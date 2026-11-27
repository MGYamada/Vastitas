"""Generate closed Lean witnesses for the protocol-10 declaration decoder."""
from fast_check import official


ROWS_PER_WORKER = 8
ORACLE = "import VastitasOracle.CertificatePackages"
DECODERS = {
    "indexed_declarations": ("Indexed.Wire.declaration", "Indexed.Source.Declaration"),
    "functions": ("Indexed.Wire.function", "Indexed.FunctionSource.Function"),
    "methods": ("Indexed.Wire.method", "Indexed.DispatchSource.Method"),
    "contributions": ("Indexed.Wire.contribution", "Indexed.DispatchSource.Contribution"),
    "resource_functions": ("Wire.function", "ResourceSource.Function"),
}


def json_object(fields, replacements, quote=official.lean_string):
    pairs = [(official.lean_string(key), replacements[key] if key in replacements else official.json_term(fields[key], quote))
             for key in sorted(fields)]
    return "(Json.mkObj [" + ", ".join(f"({key}, {value})" for key, value in pairs) + "])"


def module(imports, body):
    return f"""{imports}
set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
namespace VastitasProof.Source
open Lean VastitasKernel VastitasKernel.ResourceSource
{body}
end VastitasProof.Source
"""


def witness(name, result_type, expression):
    return f"""def {name} : {{ p : {result_type} // {expression} = .ok p }} := by
  have decoded := Eq.refl ({expression})
  conv at decoded => rhs; cbv
  exact ⟨_, decoded⟩"""


def observed_function_row(label, item):
    """Check the stripped function and its named observations in the same worker."""
    row, decoded, clean = label + "Wire", label + "Observed", label + "BodyWire"
    annotations, observed_read = label + "Annotations", label + "ObservedRead"
    value, body_read = label + "Value", label + "Read"
    observation_type = "String × List Indexed.Core.Observation"
    lines = [
        f"def {row} : Json := {official.json_term(item)}",
        f"def {decoded} : {{p : Json × ({observation_type}) // Wire.observedFunction {row} = .ok (p.1, some p.2)}} := by",
        f"  have decoded := Eq.refl (Wire.observedFunction {row})",
        "  conv at decoded => rhs; cbv",
        "  exact ⟨(_, _), decoded⟩",
        f"def {clean} := {decoded}.val.1",
        f"def {annotations} := {decoded}.val.2",
        f"theorem {observed_read} : Wire.observedFunction {row} = .ok ({clean}, some {annotations}) := {decoded}.property",
        witness(label, "Indexed.FunctionSource.Function", f"Indexed.Wire.function {clean}"),
        f"def {value} := {label}.val",
        f"theorem {body_read} : Indexed.Wire.function {clean} = .ok {value} := {label}.property",
    ]
    rules = (f"attribute [local cbv_opaque] {row} {clean} {annotations} {value}\n"
             f"attribute [local cbv_eval] {observed_read} {body_read}")
    return row, "\n".join(lines), rules


def decoded_row(label, key, item):
    if key == "functions" and "observations" in item:
        return observed_function_row(label, item)
    decoder, result_type = DECODERS[key]
    row, value, proof = label + "Wire", label + "Value", label + "Read"
    body = [f"def {row} : Json := {official.json_term(item)}",
            witness(label, result_type, f"{decoder} {row}"),
            f"def {value} := {label}.val",
            f"theorem {proof} : {decoder} {row} = .ok {value} := {label}.property"]
    rules = [proof]
    if key == "functions":
        observation = label + "Observations"
        body.append(f'theorem {observation} : {row}.getObjVal? "observations" = '
                    '.error "property not found: observations" := by with_unfolding_all rfl')
        rules.append(observation)
    # During package replay cbv uses the row's proved equation. Keeping both
    # endpoints opaque to this tactic avoids reconstructing the body a second time.
    attributes = f"attribute [local cbv_opaque] {row} {value}\nattribute [local cbv_eval] {' '.join(rules)}"
    return row, "\n".join(body), attributes


def package_modules(index, package):
    """Give long body lists checked row witnesses before assembling the original JSON."""
    name, row, result = f"SourcePackage{index}", f"packageRow{index}", f"packageResult{index}"

    def package_source(imports, attributes, wire):
        body = [*attributes, f"def {row} : Json := {wire}", witness(result, "Package", f"Wire.package {row}")]
        return name, module("\n".join(imports), "\n".join(body))

    count = sum(len(m.get(key, [])) for m in package["modules"] for key in DECODERS)
    if count <= ROWS_PER_WORKER:
        yield package_source([ORACLE], [], official.json_term(package))
        return

    imports, modules, attributes, chunk = [ORACLE], [], [], []
    for m, source in enumerate(package["modules"]):
        fields = {}
        for key in DECODERS:
            if key not in source:
                continue
            entries = []
            for i, item in enumerate(source[key]):
                entry, evidence, rules = decoded_row(f"p{index}m{m}{key}{i}", key, item)
                entries.append(entry)
                chunk.append(evidence)
                attributes.append(rules)
                if len(chunk) == ROWS_PER_WORKER:
                    part = f"{name}Rows{len(imports)}"
                    yield part, module(ORACLE, "\n".join(chunk))
                    imports.append("import " + part)
                    chunk = []
            fields[key] = ".arr #[" + ", ".join(entries) + "]"
        modules.append(json_object(source, fields))
    if chunk:
        part = f"{name}Rows{len(imports)}"
        yield part, module(ORACLE, "\n".join(chunk))
        imports.append("import " + part)
    wire = json_object(package, {"modules": ".arr #[" + ", ".join(modules) + "]"})
    yield package_source(imports, attributes, wire)


def declaration_modules(wire):
    """Decode each package once and check the identities and operators on the recovered program."""
    imports, rows, values, steps = [], [], [], []
    for i, package in enumerate(wire["packages"]):
        yield from package_modules(i, package)
        imports.append(f"import SourcePackage{i}")
        rows.append(f"packageRow{i}")
        values.append(f"packageResult{i}.val")
        steps.append(f"VastitasOracle.CertificatePackages.map_row packageResult{i}.property (")
    package_rows = ", ".join(rows)
    projected = {key: None if key in {"root_source", "expected_function_revision"} else value
                 for key, value in wire.items()}
    header = json_object(projected, {"packages": f".arr #[{package_rows}]"})
    root, file = map(official.lean_string, (wire["root"], wire["file"]))
    legacy = "true" if wire.get("legacy_geometry") is True else "false"
    mapped = "".join(steps) + "by rfl" + ")" * len(steps)
    yield "SourceFields", module("\n".join([ORACLE, *imports]), f"""def headerWire : Json := {header}
def raw : Program := {{file := {file}, root := {root}, legacyGeometry := {legacy}, packages := [{', '.join(values)}]}}
theorem fields : Wire.decodeFields headerWire = .ok raw :=
  VastitasOracle.CertificatePackages.fields_of_packages (rows := [{package_rows}])
    (by with_unfolding_all rfl) ({mapped})""")
    yield "SourceIdentities", module("import SourceFields",
        "theorem identities : (Wire.reservedIdentities raw.root raw.packages).isOk = true := by cbv")
    yield "SourceOperators", module("import SourceIdentities", """theorem operators : (Wire.operatorNames raw).isOk = true := by cbv
theorem decoded : (Wire.sourceCandidate headerWire).isOk = true :=
  VastitasOracle.CertificatePackages.candidate_of_stages fields identities operators""")

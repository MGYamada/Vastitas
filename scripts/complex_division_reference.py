"""Bit-exact *operational* reference for #855's pinned complex division graph.

This is a pure Python/reference fragment, not a CUDA wrapper or an IEEE proof.
Every scalar primitive comes from float_reference's binary32/binary64 model;
its operation-local flags are ORed in the specified left-to-right order.
The graph intentionally has no finite-extrema recovery or special-value path.
"""

from dataclasses import dataclass

import float_reference as ieee


GRAPH_ID = "cuda-scaled-rdiv-rne-gradual-no-fma-no-fallback-v1"
SCALAR = (ieee.F32, ieee.F64)

# An independent witness specification for replaying a proposed lowering/trace.
# The evaluator below is deliberately handwritten rather than generated from it.
SSA = (
    ("abs_c", "abs_bits", ("c",)),
    ("abs_d", "abs_bits", ("d",)),
    ("s", "add", ("abs_c", "abs_d")),
    ("t", "rdiv", ("one", "s")),
    ("A", "mul", ("a", "t")),
    ("B", "mul", ("b", "t")),
    ("C", "mul", ("c", "t")),
    ("D", "mul", ("d", "t")),
    ("CC", "mul", ("C", "C")),
    ("DD", "mul", ("D", "D")),
    ("v", "add", ("CC", "DD")),
    ("u", "rdiv", ("one", "v")),
    ("AC", "mul", ("A", "C")),
    ("BD", "mul", ("B", "D")),
    ("qr_sum", "add", ("AC", "BD")),
    ("qr", "mul", ("qr_sum", "u")),
    ("BC", "mul", ("B", "C")),
    ("AD", "mul", ("A", "D")),
    ("qi_diff", "sub", ("BC", "AD")),
    ("qi", "mul", ("qi_diff", "u")),
)


@dataclass(frozen=True)
class ComplexBits:
    real: ieee.F32 | ieee.F64
    imag: ieee.F32 | ieee.F64

    def __post_init__(self):
        if type(self.real) not in SCALAR or type(self.real) is not type(self.imag):
            raise TypeError("complex components must share exactly one F32/F64 format")


@dataclass(frozen=True)
class Step:
    name: str
    operation: str
    operand_bits: tuple[int, ...]
    result_bits: int
    flags: ieee.Flags
    # For rdiv the selected low-level primitive must be explicit in the trace.
    selected_primitive: str


@dataclass(frozen=True)
class GraphResult:
    value: ComplexBits
    flags: ieee.Flags
    steps: tuple[Step, ...]
    graph_id: str = GRAPH_ID


def one(kind):
    if kind is ieee.F32:
        return kind(0x3F800000)
    if kind is ieee.F64:
        return kind(0x3FF0000000000000)
    raise TypeError("only F32/CC and F64/CC are admitted")


def divide(x: ComplexBits, y: ComplexBits) -> GraphResult:
    """Execute all 20 scalar occurrences, with no branch except scalar rdiv."""
    if type(x.real) is not type(y.real):
        raise TypeError("complex division requires homogeneous precision")

    kind = type(x.real)
    flags = ieee.Flags.NONE
    steps = []

    def perform(name, operation, *args):
        nonlocal flags
        local = getattr(ieee, operation)(*args)
        selected = "mul_zero" if operation == "rdiv" and args[1].is_zero else (
            "div" if operation == "rdiv" else operation)
        steps.append(Step(name, operation, tuple(arg.bits for arg in args),
                          local.value.bits, local.flags, selected))
        flags |= local.flags
        return local.value

    a, b = x.real, x.imag
    c, d = y.real, y.imag

    # Exact SSA schedule. Do not combine these occurrences or contract to FMA.
    abs_c = perform("abs_c", "abs_bits", c)
    abs_d = perform("abs_d", "abs_bits", d)
    s = perform("s", "add", abs_c, abs_d)
    t = perform("t", "rdiv", one(kind), s)
    A = perform("A", "mul", a, t)
    B = perform("B", "mul", b, t)
    C = perform("C", "mul", c, t)
    D = perform("D", "mul", d, t)
    CC = perform("CC", "mul", C, C)
    DD = perform("DD", "mul", D, D)
    v = perform("v", "add", CC, DD)
    u = perform("u", "rdiv", one(kind), v)
    AC = perform("AC", "mul", A, C)
    BD = perform("BD", "mul", B, D)
    qr_sum = perform("qr_sum", "add", AC, BD)
    qr = perform("qr", "mul", qr_sum, u)
    BC = perform("BC", "mul", B, C)
    AD = perform("AD", "mul", A, D)
    qi_diff = perform("qi_diff", "sub", BC, AD)
    qi = perform("qi", "mul", qi_diff, u)

    return GraphResult(ComplexBits(qr, qi), flags, tuple(steps))


def reciprocal(z: ComplexBits) -> GraphResult:
    """Exactly divide (one_F,+0_F) by z; no separate reciprocal kernel."""
    kind = type(z.real)
    return divide(ComplexBits(one(kind), ieee.zero(kind=kind)), z)


def verify_trace(x: ComplexBits, y: ComplexBits, proposal: GraphResult) -> bool:
    """Independently replay SSA/dataflow, bits, flags, and actual rdiv branches.

    This checks a *pure reference witness*, not a source/IR/LLVM/CUDA program.
    An optimized implementation must still supply a separate refinement proof.
    """
    if (proposal.graph_id != GRAPH_ID or len(proposal.steps) != len(SSA)
            or type(x.real) is not type(y.real)):
        return False
    values = {"a": x.real, "b": x.imag, "c": y.real, "d": y.imag,
              "one": one(type(x.real))}
    sticky = ieee.Flags.NONE
    for step, (name, operation, sources) in zip(proposal.steps, SSA):
        if step.name != name or step.operation != operation:
            return False
        args = tuple(values[source] for source in sources)
        if step.operand_bits != tuple(arg.bits for arg in args):
            return False
        computed = getattr(ieee, operation)(*args)
        selected = "mul_zero" if operation == "rdiv" and args[1].is_zero else (
            "div" if operation == "rdiv" else operation)
        if ((step.result_bits, step.flags, step.selected_primitive)
                != (computed.value.bits, computed.flags, selected)):
            return False
        sticky |= computed.flags
        values[name] = computed.value
    return (proposal.flags == sticky and
            proposal.value == ComplexBits(values["qr"], values["qi"]))

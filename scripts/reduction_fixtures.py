"""Independent targets and illustrative candidate plans; no authoritative flags."""

from copy import deepcopy
from dataclasses import asdict

from reduction_reference import ADD, FLOAT_ADD, MATMUL, Binding, law_reference


def leaf(ident: str, revision: str = "input-v1") -> dict:
    return {"leaf": ident, "revision": revision}


def node(binding: Binding, left: dict, right: dict) -> dict:
    return {"binding": asdict(binding), "left": left, "right": right}


def plan(target: dict, tree: dict, *certificates: str) -> dict:
    # This convenience function copies a separately constructed target's ID and
    # binding. check() never uses a candidate to manufacture the target.
    return {"schema": 1, "target_id": target["id"], "binding": deepcopy(target["binding"]),
            "tree": deepcopy(tree), "evidence": [law_reference(c) for c in certificates]}


def target(binding: Binding, values: list, ids: tuple[str, ...], contract: dict,
           ident: str = "independent-request-v1") -> dict:
    return {"schema": 1, "id": ident, "binding": asdict(binding),
            "inputs": [{"id": i, "revision": "input-v1", "value": deepcopy(v)}
                       for i, v in zip(ids, values, strict=True)], "contract": deepcopy(contract)}


def matrix_target(*, permutation: bool = False, binding: Binding = MATMUL) -> dict:
    return target(binding, [[["1", "1"], ["0", "1"]],
                            [["1", "0"], ["1", "1"]],
                            [["1", "2"], ["0", "1"]]], ("A", "B", "C"),
                  {"kind": "exact", "allow_permutation": permutation}, "matrix-request-v1")


def scalar_target(binding: Binding = ADD, values: list | None = None, *, permutation: bool = False) -> dict:
    return target(binding, ["2", "3", "4"] if values is None else values, ("a", "b", "c"),
                  {"kind": "exact", "allow_permutation": permutation}, "scalar-request-v1")


def float_target(kind: str = "fixed_tree") -> dict:
    # x=2**54, y=-2**54, z=1. These are exact binary64 input bit patterns.
    contract = {"kind": kind}
    if kind == "fixed_tree":
        # The target chooses right nesting independently; the candidate must match.
        contract["tree"] = node(FLOAT_ADD, leaf("x"), node(FLOAT_ADD, leaf("y"), leaf("z")))
    elif kind == "relaxed":
        contract.update({"policy": "explicit-reassociate-v1", "error_contract": "absolute-error-at-most-one"})
    return target(FLOAT_ADD, ["4350000000000000", "c350000000000000", "3ff0000000000000"],
                  ("x", "y", "z"), contract, "binary64-request-v1")


def examples() -> dict[str, tuple[dict, dict]]:
    m = matrix_target()
    right = node(MATMUL, leaf("A"), node(MATMUL, leaf("B"), leaf("C")))
    swapped = node(MATMUL, node(MATMUL, leaf("B"), leaf("A")), leaf("C"))
    f = float_target()
    q = scalar_target(permutation=True)
    qtree = node(ADD, leaf("b"), node(ADD, leaf("a"), leaf("c")))
    p = plan(m, right, "matmul-v1-assoc")
    forged = deepcopy(p)
    forged["laws"] = ["associative", "commutative"]
    stale = deepcopy(p)
    stale["evidence"][0]["subject"]["revision"] = "v0"
    return {
        "matrix_ordered_reassociation": (m, p),
        "matrix_permutation_associativity_only": (matrix_target(permutation=True), plan(m, swapped, "matmul-v1-assoc")),
        "matrix_missing_leaf": (m, plan(m, node(MATMUL, leaf("A"), leaf("C")), "matmul-v1-assoc")),
        "matrix_duplicate_leaf": (m, plan(m, node(MATMUL, leaf("A"), node(MATMUL, leaf("B"), leaf("B"))), "matmul-v1-assoc")),
        "candidate_law_tag": (m, forged),
        "stale_evidence_revision": (m, stale),
        "commutative_exact_permutation": (q, plan(q, qtree, "qq-add-assoc", "qq-add-comm")),
        "float_fixed_right_tree": (f, plan(f, f["contract"]["tree"])),
        "float_right_tree_vs_left_fold": (float_target("left_fold_equivalent"), plan(f, f["contract"]["tree"])),
        "float_relaxed_unsupported": (float_target("relaxed"), plan(f, f["contract"]["tree"])),
    }

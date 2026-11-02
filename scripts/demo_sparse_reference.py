"""Human-readable #243 fixture observations, not #242 graph emit or timing data."""

from sparse_reference import (
    Binding, PlanInvalidated, SparseError, bind_pivot_guard, cancellation_example,
    execute_guarded, execute_spgemm, from_coo, inspect_spgemm, require_structural_bound,
)


def matrix_text(matrix):
    return "[" + ", ".join("[" + ", ".join(map(str, row)) + "]" for row in matrix.dense()) + "]"


def main():
    a, b, updated = cancellation_example()
    binding = Binding("fixture/AB")
    plan = inspect_spgemm(a, b, binding)
    print("Exact Python reference only; no checked Core, graph emit, native or GPU execution.")
    print("Counts are logical slots/products, not bytes, FLOPs or performance measurements.")
    for name, matrix in (("A", a), ("B", b), ("B'", updated)):
        print(f"{name}: structural_slots={matrix.pattern.slots}; numerical_nonzeros={matrix.numerical_nonzeros}")
    for name, right in (("AB", b), ("AB'", updated)):
        result = execute_spgemm(plan, a, right, binding)
        print(f"{name}={matrix_text(result)}; structural_slots={result.pattern.slots}; "
              f"numerical_nonzeros={result.numerical_nonzeros}; "
              f"multiplication_contributions={plan.multiplication_contributions}")
    print("structure-only plan: reused after B -> B' (same nominal pattern snapshot)")

    compacted = from_coo(2, 2, [(0, 1, 1), (1, 0, -1)], label="observed-support")
    try:
        require_structural_bound(a, b, compacted.pattern)
    except SparseError as error:
        print(f"cancellation-based omission: {error.code}")
    changed = from_coo(3, 2, [(0, 0, 1), (1, 1, 1), (2, 1, -1)], label="B", revision=1)
    try:
        execute_spgemm(plan, a, changed, binding)
    except PlanInvalidated as error:
        print(f"pattern edit: {error.code}")

    entries = [(0, 0, 1), (0, 0, -1), (0, 1, 0)]
    duplicates = from_coo(2, 2, entries, label="duplicates-and-empty-row")
    print(f"COO duplicate sum: raw_entries={len(entries)}; structural_slots={duplicates.pattern.slots}; "
          f"numerical_nonzeros={duplicates.numerical_nonzeros}; offsets={duplicates.pattern.offsets}")

    pivot_a = from_coo(2, 1, [(0, 0, 2), (1, 0, 1)], label="pivotA")
    pivot_b = from_coo(1, 1, [(0, 0, 1)], label="pivotB")
    structural = inspect_spgemm(pivot_a, pivot_b, binding)
    guarded = bind_pivot_guard(structural, pivot_a, pivot_b, binding)
    stable = pivot_a.with_values([3, 1])
    execute_guarded(guarded, stable, pivot_b, binding)
    print("first-pivot guard: reused after values change with the same selected row")
    changed = pivot_a.with_values([1, 4])
    execute_spgemm(structural, changed, pivot_b, binding)
    try:
        execute_guarded(guarded, changed, pivot_b, binding)
    except PlanInvalidated as error:
        print(f"first-pivot guard: {error.code}; structure-only plan remains reusable")


if __name__ == "__main__":
    main()

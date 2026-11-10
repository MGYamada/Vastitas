"""Run the bounded #318 reference; all reported flags are symbolic, not native."""

from fractions import Fraction as Q

import float_reference as r
import safe_float_reference as m


def describe(value):
    if isinstance(value, m.Ok):
        return f"Ok({describe(value.value)})"
    if isinstance(value, m.Err):
        return f"Err({value.error.value})"
    if isinstance(value, r.F64):
        return f"0x{value.bits:016x}"
    return repr(value)


def show(label, program):
    value, flags = program.run()
    trace = program.audit().trace
    print(f"{label}: {describe(value)}, symbolic flags={flags.name}")
    print("  internal trace:", " -> ".join(f"{e.site}:{e.operation}" for e in trace) or "empty")


def main():
    one = r.F64(0x3FF0000000000000)
    x = r.F64(0x4340000000000000)
    print("Reference execution profile:", m.EXECUTION_PROFILE)
    for z in (r.zero(), r.zero(True)):
        show("pure signed zero", m.Float.pure(z))
        show("raw 1 / zero", m.binary("div", one, z))
        show("checked 1 / zero", m.checked_div(one, z))
    show("underflow before checked failure", m.lift(m.convert(Q(1, 2**1075), site="tiny"))
         .bind(lambda b: m.checked_div(one, b, site="failure")))
    show("rounded (2**53 + 1) - 2**53", m.binary("add", x, one, site="add")
         .bind(lambda y: m.binary("sub", y, x, site="sub")))
    first = m.checked_div(one, r.zero(), site="first")
    second = m.checked_div(one, r.zero(), site="second")
    show("two checked zeros", first.bind(lambda _: second))
    print("No Lean proof, production Core integration, native flags or native refinement.")


if __name__ == "__main__":
    main()

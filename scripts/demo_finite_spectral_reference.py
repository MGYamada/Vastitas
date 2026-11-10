"""Small exact spectral-pair report; run with Python's standard library only."""

import json
from dataclasses import replace

import finite_spectral_reference as fs
from rational_polynomial_reference import Invalid


def main():
    frame = fs.Frame("spectral-demo", "QQ", "V", "e0,e1")
    zero = fs.Subject("H0", "1", frame, frame, ((0, 0), (0, 0)))
    jordan = fs.Subject("HJ", "1", frame, frame, ((0, 1), (0, 0)))
    ez, ej = fs.propose(zero), fs.propose(jordan)
    fs.verify(zero, ez)
    fs.verify(jordan, ej)
    fs.check_structure_sheaf_isomorphism(jordan, ej, ((0, 1), (1, 0)))

    rejected = {}
    for name, call in (
        ("erase_jordan", lambda: fs.verify(jordan, replace(ej, t_action=zero.h))),
        ("false_structure_sheaf", lambda: fs.check_structure_sheaf_isomorphism(zero, ez, fs.IDENTITY)),
        ("reduced_roots", lambda: fs.QuadraticAlgebra("t", fs.T)),
        ("canonical_vector", lambda: fs.check_eigenvector(zero, ez, 0, (1, 0), selection="canonical")),
    ):
        try:
            call()
        except Invalid as error:
            rejected[name] = error.code
        else:
            raise AssertionError(f"incorrect acceptance: {name}")

    k = fs.QuadraticAlgebra("sqrt2", fs.T ** 2 - 2)
    extension = fs.propose_scalar_extension(jordan, ej, k)
    extended = fs.extended_act(jordan, ej, k, extension, fs.ZERO, fs.ONE, (fs.ZERO, fs.T))
    if extended != (fs.T, fs.ZERO):
        raise AssertionError("scalar extension lost the Jordan action")
    fermi = fs.QuadraticAlgebra("z", (fs.T + 1) ** 2)
    print(json.dumps({
        "status": "external exact reference; Lean/Core/native pending",
        "same_characteristic": ez.algebra == ej.algebra,
        "characteristic": "t^2",
        "epsilon_on_zero": list(map(str, fs.act(zero, ez, fs.T, (0, 1)))),
        "epsilon_on_jordan": list(map(str, fs.act(jordan, ej, fs.T, (0, 1)))),
        "jordan_regular_comparison": [[0, 1], [1, 0]],
        "QQ_sqrt2_jordan_action": "(u,0)",
        "ssh_fermi_epsilon_nonzero": fermi.reduce(fs.T + 1) != fs.ZERO,
        "ssh_fermi_epsilon_squared_zero": fermi.reduce((fs.T + 1) ** 2) == fs.ZERO,
        "rejections": rejected,
    }, indent=2))


if __name__ == "__main__":
    main()

"""Run the finite exact SSH example and its three counterexamples; JSON output."""

import json

import ssh_toric_reference as sr


def polynomial_data(poly):
    return [{"powers_v_w_E_z": list(p), "coefficient": [c.numerator, c.denominator]}
            for p, c in poly.terms]


def matrix_data(matrix):
    return [[str(entry) for entry in row] for row in matrix]


def report():
    family = sr.ssh_bloch_family()
    params = family.specialize(v=1, w=1)
    fiber = params.target.specialize(E=0)
    other_order = family.specialize(E=0).target.specialize(v=1, w=1)
    basis = sr.require_ssh_double_point(fiber.target)
    power, f = sr.clear_z_denominator(params.target.equation)
    bad = sr.Z * f
    witness = sr.saturate_principal_z(bad)
    h_at_point = sr.specialize_matrix(sr.ssh_hamiltonian(), v=1, w=1, z=-1)
    jordan = sr.matrix2(((0, 1), (0, 0)))
    nilpotent = sr.in_double_point(sr.Z + 1)
    expected_p = sr.E ** 2 - (sr.V + sr.W * sr.Z) * (sr.V + sr.W * sr.Z_INV)
    specialized_h = sr.specialize_matrix(sr.ssh_hamiltonian(), v=1, w=1)
    kernel_dimensions = [sr.kernel_dimension2(h_at_point), sr.kernel_dimension2(jordan)]
    checks = {
        "symbolic_characteristic_polynomial": family.equation == expected_p,
        "determinant_commutes_with_parameter_specialization": (
            params.target.equation == sr.characteristic2(specialized_h)),
        "energy_and_parameter_fibers_commute": fiber.target == other_order.target,
        "epsilon_nonzero": nilpotent != sr.Dual(),
        "epsilon_squared_zero": nilpotent ** 2 == sr.Dual(),
        "z_inverse_is_minus_one_minus_epsilon": sr.DUAL_Z.inverse() == sr.Dual(-1, -1),
        "z_times_inverse_is_one": sr.DUAL_Z * sr.DUAL_Z.inverse() == sr.Dual(1),
        "fiber_equation_zero_in_quotient": sr.in_double_point(fiber.target.equation) == sr.Dual(),
        "reduced_point_loses_nonzero_epsilon": nilpotent.a == 0 and nilpotent != sr.Dual(),
        "extra_clearing_adds_z_zero_component": (
            sr.polynomial_boundary_at_z_zero(bad) == sr.ZERO
            and sr.polynomial_boundary_at_z_zero(f) == -sr.ONE),
        "principal_saturation_recovers_f": (
            sr.check_principal_z_saturation(bad, witness) and witness.generator == f),
        "same_characteristic_polynomial": (
            sr.characteristic2(h_at_point) == sr.characteristic2(jordan) == sr.E ** 2),
        "different_kernel_dimensions": kernel_dimensions == [2, 1],
    }
    return {
        "status": "external_exact_reference_only",
        "vastitas_or_lean_acceptance": False,
        "issue": "https://github.com/MGYamada/Vastitas/issues/247",
        "family": {
            "coefficient_ring": "QQ[v,w]", "ambient": "Spec(QQ[v,w][z,z^-1,E])",
            "equation": polynomial_data(family.equation),
        },
        "zero_energy_fiber_v_w_1": {
            "equation": polynomial_data(fiber.target.equation),
            "coordinate_algebra": "QQ[epsilon]/(epsilon^2), z=-1+epsilon",
            "basis": ["1", "epsilon"], "dimension_over_QQ": len(basis),
            "epsilon_multiplication": matrix_data(sr.EPSILON.multiplication_matrix()),
            "z_multiplication": matrix_data(sr.DUAL_Z.multiplication_matrix()),
            "z_inverse_multiplication": matrix_data(sr.DUAL_Z.inverse().multiplication_matrix()),
            "reduction_map": "a+b*epsilon -> a; reduced algebra QQ has dimension 1",
        },
        "boundary_counterexample": {
            "minimal_clearing_power": power, "f": polynomial_data(f),
            "extra_clearing": "z*F", "f_at_z_zero": "-1", "z_f_at_z_zero": "0 for all E",
            "saturation_scope": "one nonzero principal ideal in QQ[E,z], localized at z",
            "removed_z_power": witness.removed_power,
        },
        "jordan_counterexample": {
            "matrices": ["SSH(v=w=1,z=-1)=0", "J=[[0,1],[0,0]]"],
            "common_characteristic_polynomial": "E^2",
            "kernel_dimensions": kernel_dimensions,
        },
        "checks": checks,
    }


if __name__ == "__main__":
    result = report()
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if all(result["checks"].values()) else 1)

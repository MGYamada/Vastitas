"""Exhaustive finite regressions for #249, not universal probability proofs."""

from dataclasses import replace
from fractions import Fraction as Q
from itertools import permutations, product
import unittest

import rand_reference as r


def pair(reader=r.read_bit):
    return r.bind(reader, lambda a: r.bind(reader, lambda b: r.pure((a, b))))


def bracketings(reader=r.read_bit):
    start = r.bind(reader, lambda a: r.pure((a,)))
    append = lambda previous: r.bind(reader, lambda b: r.pure(previous + (b,)))
    return (r.bind(r.bind(start, append), append),
            r.bind(start, lambda a: r.bind(append(a), append)))


def split_pair(supply):
    partition = r.split_at(1)(supply)
    if isinstance(partition, r.Exhausted):
        return partition
    left, right = (r.read_bit(child) for child in partition.value)
    trace = partition.trace + left.trace + right.trace
    if isinstance(right, r.Exhausted):
        return replace(right, trace=trace)
    return r.Success((left.value, right.value), partition.rest, trace)


class StateTests(unittest.TestCase):
    def test_three_bit_associativity_including_complete_trace_and_rest(self):
        left, right = bracketings()
        for bits in product((0, 1), repeat=3):
            with self.subTest(bits=bits):
                supply = r.Supply.from_bits(bits)
                expected = r.Success(bits, replace(supply, position=3),
                                     tuple(r.Read(i, b, True) for i, b in enumerate(bits)))
                self.assertEqual(left(supply), expected)
                self.assertEqual(right(supply), expected)

    def test_associativity_preserves_unused_suffix(self):
        left, right = bracketings()
        for bits in product((0, 1), repeat=5):
            supply = r.Supply.from_bits(bits)
            self.assertEqual(left(supply), right(supply))
            self.assertEqual(left(supply).rest.bits[3:], bits[3:])
            self.assertEqual(left(supply).rest.remaining, 2)

    def test_state_laws_with_branching_nonzero_positions_and_shortages(self):
        f = lambda a: pair() if a else r.pure((0, 0))
        g = lambda ab: r.bind(r.read_bit, lambda c: r.pure((*ab, c)))
        for width in range(5):
            for bits in product((0, 1), repeat=width):
                for position in range(width + 1):
                    supply = replace(r.Supply.from_bits(bits), position=position)
                    for m in (r.read_bit, r.unsafe_peek_bit, r.pure(1)):
                        self.assertEqual(r.bind(m, r.pure)(supply), m(supply))
                        self.assertEqual(r.bind(r.bind(m, f), g)(supply),
                                         r.bind(m, lambda a: r.bind(f(a), g))(supply))
                    for a in (0, 1):
                        self.assertEqual(r.bind(r.pure(a), f)(supply), f(a)(supply))

    def test_shortage_is_absorbing_and_retains_consumed_prefix(self):
        supply = r.Supply.from_bits((1,))
        self.assertEqual(pair()(supply), r.Exhausted(replace(supply, position=1),
                                                   trace=(r.Read(0, 1, True),)))
        def must_not_run(_):
            self.fail("continuation ran after shortage")
        self.assertEqual(r.bind(r.read_bit, must_not_run)(r.Supply.from_bits(())),
                         r.Exhausted(r.Supply.from_bits(())))

    def test_peek_rereads_same_address_without_changing_state(self):
        supply = r.Supply.from_bits((1, 0))
        actual = pair(r.unsafe_peek_bit)(supply)
        self.assertEqual(actual.value, (1, 1))
        self.assertEqual(actual.rest, supply)
        self.assertEqual(actual.trace, (r.Read(0, 1, False),) * 2)
        self.assertEqual(pair()(supply).value, (1, 0))

    def test_malformed_supply_is_rejected(self):
        for bits, addresses, position in (
            ((2,), (0,), 0), ((True,), (0,), 0), ([0], (0,), 0),
            ((0,), (), 0), ((0, 1), (0, 0), 0), ((0,), (-1,), 0),
            ((0,), (0,), -1), ((0,), (0,), 2), ((0,), (0,), True),
        ):
            with self.subTest(bits=bits, addresses=addresses, position=position):
                with self.assertRaises(ValueError):
                    r.Supply(bits, addresses, position)


class SplitTests(unittest.TestCase):
    def test_explicit_split_partitions_only_the_unconsumed_suffix(self):
        supply = r.read_bit(r.Supply.from_bits((1, 0, 1, 1, 0))).rest
        partition = r.split_at(2)(supply)
        left, right = partition.value
        self.assertEqual(left, r.Supply((0, 1), (1, 2)))
        self.assertEqual(right, r.Supply((1, 0), (3, 4)))
        self.assertEqual(partition.trace, (r.Split((1, 2), (3, 4)),))
        self.assertEqual(partition.rest.remaining, 0)
        self.assertIsInstance(r.read_bit(partition.rest), r.Exhausted)
        for schedule in (("left", "right"), ("right", "left")):
            children = {"left": left, "right": right}
            results = {name: pair()(children[name]) for name in schedule}
            self.assertEqual(results["left"].value, (0, 1))
            self.assertEqual(results["right"].value, (1, 0))
            self.assertEqual(results["left"].rest.position, 2)
            self.assertEqual(results["right"].rest.position, 2)

    def test_empty_full_and_insufficient_partitions(self):
        supply = r.Supply.from_bits((0, 1))
        for cut in range(3):
            left, right = r.split_at(cut)(supply).value
            self.assertEqual(left.addresses + right.addresses, (0, 1))
            self.assertTrue(set(left.addresses).isdisjoint(right.addresses))
        self.assertEqual(r.split_at(3)(supply), r.Exhausted(supply, needed=3))
        empty = r.Supply.from_bits(())
        self.assertEqual(r.split_at(0)(empty).value, (empty, empty))
        for invalid in (-1, True, 1.5):
            with self.assertRaises(ValueError):
                r.split_at(invalid)

    def test_implicit_splitting_changes_addresses_and_fixed_supply_outputs(self):
        left, right = r.implicit_split_addresses()
        self.assertEqual(left, ("LL", "LR", "R"))
        self.assertEqual(right, ("L", "RL", "RR"))
        table = {**dict.fromkeys(left, 0), **dict.fromkeys(right, 1)}
        self.assertEqual(tuple(table[a] for a in left), (0, 0, 0))
        self.assertEqual(tuple(table[a] for a in right), (1, 1, 1))
        # One common six-bit probability space, not unrelated marginal fixtures.
        domain = tuple(sorted(table))
        def law(paths):
            return r.pushforward(r.uniform_bits(6), lambda bits:
                                 tuple(dict(zip(domain, bits))[a] for a in paths))
        self.assertEqual(law(left), law(right))
        self.assertEqual(law(left), r.uniform_bits(3))


class DistributionTests(unittest.TestCase):
    def test_finite_distribution_laws_with_nondyadic_weights(self):
        dist = r.FiniteDist.from_weights(((0, Q(1, 3)), (1, Q(2, 3))))
        f = lambda a: r.FiniteDist.from_weights(((a, Q(2, 5)), (a + 1, Q(3, 5))))
        g = lambda b: r.FiniteDist.from_weights(((b, Q(1, 7)), (-b, Q(6, 7))))
        self.assertEqual(r.compose_dist(dist, r.dirac), dist)
        self.assertEqual(r.compose_dist(r.dirac(1), f), f(1))
        self.assertEqual(r.compose_dist(r.compose_dist(dist, f), g),
                         r.compose_dist(dist, lambda a: r.compose_dist(f(a), g)))

    def test_fresh_consumption_matches_independent_kernel_composition(self):
        coin = r.output_law(r.read_bit, r.uniform_bits(1))
        expected = r.compose_dist(coin, lambda a:
                                 r.pushforward(coin, lambda b: (a, b)))
        self.assertEqual(expected, r.uniform_bits(2))
        self.assertEqual(r.output_law(pair(), r.uniform_bits(2)), expected)
        self.assertEqual(r.output_law(split_pair, r.uniform_bits(2)), expected)
        self.assertEqual(r.output_law(r.pure(None), r.uniform_bits(0)), r.dirac(None))

    def test_value_dependent_consumption_with_enough_fresh_bits(self):
        continuation = lambda a: (r.pure((0, 0)) if a == 0 else
                                  r.bind(r.read_bit, lambda b: r.pure((1, b))))
        actual = r.output_law(r.bind(r.read_bit, continuation), r.uniform_bits(2))
        expected = r.compose_dist(r.output_law(r.read_bit, r.uniform_bits(1)),
                                  lambda a: r.output_law(continuation(a), r.uniform_bits(1)))
        self.assertEqual(actual, expected)
        self.assertEqual(actual.mass((0, 0)), Q(1, 2))
        self.assertEqual(actual.mass((1, 0)), Q(1, 4))

    def test_same_marginal_laws_do_not_establish_the_bind_equation(self):
        coin = r.uniform_bits(1)
        self.assertEqual(r.output_law(r.unsafe_peek_bit, coin),
                         r.output_law(r.read_bit, coin))
        reread = r.output_law(pair(r.unsafe_peek_bit), coin)
        fresh = r.output_law(pair(), r.uniform_bits(2))
        self.assertEqual(dict(reread.masses), {(0, 0): Q(1, 2), (1, 1): Q(1, 2)})
        self.assertNotEqual(reread, fresh)
        equal = lambda ab: ab[0] == ab[1]
        self.assertEqual(r.pushforward(reread, equal).mass(True), Q(1))
        self.assertEqual(r.pushforward(fresh, equal).mass(True), Q(1, 2))

    def test_consumption_and_disjoint_split_do_not_certify_source_independence(self):
        correlated = r.FiniteDist.from_weights((((0, 0), Q(1, 2)), ((1, 1), Q(1, 2))))
        self.assertEqual(r.output_law(pair(), correlated), correlated)
        self.assertEqual(r.output_law(split_pair, correlated), correlated)
        self.assertNotEqual(correlated, r.uniform_bits(2))

    def test_shortage_probability_is_not_dropped_or_renormalized(self):
        program = r.bind(r.read_bit, lambda a: r.pure(None) if a == 0 else r.read_bit)
        source = r.uniform_bits(1)
        self.assertEqual(dict(r.execution_law(program, source).masses),
                         {r.Returned(None): Q(1, 2), r.Failure.SUPPLY_EXHAUSTED: Q(1, 2)})
        with self.assertRaisesRegex(ValueError, "nonzero shortage mass"):
            r.output_law(program, source)
        self.assertEqual(r.execution_law(r.read_bit, r.uniform_bits(0)),
                         r.dirac(r.Failure.SUPPLY_EXHAUSTED))

    def test_distribution_inputs_require_exact_normalized_nonnegative_mass(self):
        for entries in ((), ((0, Q(-1)),), ((0, Q(1, 2)),), ((0, 1.0),), ((0, 1),)):
            with self.subTest(entries=entries), self.assertRaises(ValueError):
                r.FiniteDist.from_weights(entries)
        self.assertEqual(r.FiniteDist.from_weights(((0, Q(1, 3)), (0, Q(2, 3)),
                                                    (1, Q(0)))), r.dirac(0))
        for width in (-1, True, 13):
            with self.assertRaises(ValueError):
                r.uniform_bits(width)

    def test_unmodeled_program_errors_are_not_classified_as_shortages(self):
        with self.assertRaises(TypeError):
            r.execution_law(lambda _: None, r.uniform_bits(0))
        def broken(_):
            raise RuntimeError("unmodeled program error")
        with self.assertRaisesRegex(RuntimeError, "unmodeled"):
            r.execution_law(broken, r.uniform_bits(0))


class AddressTests(unittest.TestCase):
    def test_one_use_keys_alone_allow_identical_address_reconstruction(self):
        address = r.LogicalAddress(7, "trajectory", 2, 0)
        first, second = r.LinearKey(address), r.LinearKey(replace(address))
        self.assertEqual(first.consume(), second.consume())
        for key in (first, second):
            with self.assertRaises(r.KeyReuse):
                key.consume()

    def test_owned_domain_rejects_duplicates_before_and_after_consumption(self):
        address = r.LogicalAddress(7, "trajectory", 2, 0)
        book = r.AddressBook((address,))
        key = book.claim(address)
        with self.assertRaises(r.DuplicateAddress):
            book.claim(replace(address))
        key.consume()
        with self.assertRaises(r.DuplicateAddress):
            book.claim(replace(address))
        with self.assertRaises(r.DuplicateAddress):
            r.AddressBook((address, replace(address)))

    def test_logical_task_assignment_survives_all_24_execution_orders(self):
        domain = tuple(r.LogicalAddress(7, "tasks", i, j) for i in range(4) for j in range(2))
        # A fixed finite table, not a seed-to-bit generator or PRNG quality test.
        table = dict(zip(domain, (1, 0, 0, 0, 1, 1, 0, 1)))
        expected = {i: tuple((a, table[a]) for a in domain if a.logical_index == i)
                    for i in range(4)}
        for order in permutations(range(4)):
            book = r.AddressBook(domain)  # Explicitly replay a new run.
            observed = {}
            for task in order:
                addresses = tuple(book.claim(r.LogicalAddress(7, "tasks", task, draw)).consume()
                                  for draw in range(2))
                observed[task] = tuple((a, table[a]) for a in addresses)
            self.assertEqual(observed, expected)

    def test_identity_dimensions_bounds_and_owned_domain(self):
        a = r.LogicalAddress(7, "tasks", 0, 0)
        domain = (a, replace(a, seed=8), replace(a, namespace="other"),
                  replace(a, logical_index=1), replace(a, draw_index=1))
        book = r.AddressBook(domain)
        self.assertEqual(tuple(book.claim(x).consume() for x in domain), domain)
        with self.assertRaisesRegex(ValueError, "outside owned domain"):
            book.claim(replace(a, logical_index=2))
        for changes in ({"logical_index": -1}, {"draw_index": r.ADDRESS_LIMIT},
                        {"logical_index": r.ADDRESS_LIMIT}, {"draw_index": True},
                        {"seed": -1}, {"namespace": ""}, {"profile": "unknown"}):
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                replace(a, **changes)
        self.assertEqual(replace(a, draw_index=r.ADDRESS_LIMIT - 1).draw_index,
                         r.ADDRESS_LIMIT - 1)


if __name__ == "__main__":
    unittest.main()

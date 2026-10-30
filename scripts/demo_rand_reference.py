"""Run: python3 scripts/demo_rand_reference.py (standard library only)."""

from fractions import Fraction as Q
from itertools import permutations, product

import rand_reference as r


def pair(reader):
    return r.bind(reader, lambda a: r.bind(reader, lambda b: r.pure((a, b))))


def main():
    print("Finite reference tests only; conditional ideal-law and Lean proofs remain pending.")
    start = r.bind(r.read_bit, lambda a: r.pure((a,)))
    append = lambda previous: r.bind(r.read_bit, lambda b: r.pure(previous + (b,)))
    left = r.bind(r.bind(start, append), append)
    right = r.bind(start, lambda a: r.bind(append(a), append))
    matches = sum(left(r.Supply.from_bits(bits)) == right(r.Supply.from_bits(bits))
                  for bits in product((0, 1), repeat=3))
    print(f"Sequential associativity (output, remaining position, trace): {matches}/8 supplies")
    print(f"Supply shortage: {pair(r.read_bit)(r.Supply.from_bits((1,)))}")

    partition = r.split_at(1)(r.Supply.from_bits((0, 1)))
    print(f"Explicit split: {partition.trace}; parent remaining={partition.rest.remaining}")
    print(f"Implicit split at bind: left/right addresses={r.implicit_split_addresses()}")
    for name, reader, width in (("fresh", r.read_bit, 2), ("reread", r.unsafe_peek_bit, 1)):
        law = r.output_law(pair(reader), r.uniform_bits(width))
        probability = r.pushforward(law, lambda ab: ab[0] == ab[1]).mass(True)
        print(f"{name}: {sorted(law.masses)}; P(equal)={probability}")
    partial = r.bind(r.read_bit, lambda a: r.pure(None) if a == 0 else r.read_bit)
    law = r.execution_law(partial, r.uniform_bits(1))
    print(f"Failure retained: success={law.mass(r.Returned(None))}, "
          f"shortage={law.mass(r.Failure.SUPPLY_EXHAUSTED)} (total={Q(1)})")

    domain = tuple(r.LogicalAddress(7, "tasks", i, 0) for i in range(4))
    table = dict(zip(domain, (1, 0, 0, 1)))  # Fixed fixture, not a PRNG.
    expected = {a.logical_index: (a, table[a]) for a in domain}
    matches = 0
    for order in permutations(range(4)):
        book = r.AddressBook(domain)  # Explicit fresh run/replay.
        observed = {}
        for task in order:
            address = book.claim(r.LogicalAddress(7, "tasks", task, 0)).consume()
            observed[task] = (address, table[address])
        matches += observed == expected
    print(f"Logical address and table output preserved: {matches}/24 schedules")
    address = domain[0]
    print("Two individually one-use keys can repeat an address:",
          r.LinearKey(address).consume() == r.LinearKey(address).consume())
    book = r.AddressBook(domain)
    book.claim(address).consume()
    try:
        book.claim(r.LogicalAddress(7, "tasks", 0, 0))
    except r.DuplicateAddress as error:
        print(f"Duplicate reconstruction rejected: {error}")


if __name__ == "__main__":
    main()

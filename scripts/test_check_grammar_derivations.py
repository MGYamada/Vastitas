"""Regressions for the derivation logic of scripts/check_grammar_derivations.py; no compiler needed."""
from pathlib import Path
import stat
import sys
import tempfile
import textwrap
import unittest

import book_grammar
import check_grammar_derivations as derivations
from check_grammar_derivations import Case, Node


GRAMMAR = book_grammar.load()


def expression(*parts):
    """An Expression node of an operator chain: operands and operators alternate, grouped to the right."""
    if len(parts) == 1:
        operand = parts[0]
        return operand if isinstance(operand, Node) else Node("Expression", [Node("PathExpression", [operand])])
    left, operator, *rest = parts
    return Node("Expression", [Node("OperatorExpression", [
        expression(left), Node("BinaryOperator", [operator]), expression(*rest)])])


class DerivationTests(unittest.TestCase):
    def test_the_derivation_is_fixed_by_the_seed(self):
        first = [case.program for case in derivations.derive_cases(GRAMMAR, 40, seed=3)[0]]
        second = [case.program for case in derivations.derive_cases(GRAMMAR, 40, seed=3)[0]]
        other = [case.program for case in derivations.derive_cases(GRAMMAR, 40, seed=4)[0]]
        self.assertEqual(first, second)
        self.assertNotEqual(first, other)

    def test_the_texts_parse_and_take_every_option_that_the_contexts_reach(self):
        cases, deriver = derivations.derive_cases(GRAMMAR)
        self.assertEqual(len(cases), derivations.COUNT)
        for case in cases:
            self.assertIsNone(GRAMMAR.parse(case.program), case.program)
        used, total = deriver.coverage(derivations.CONTEXTS)
        self.assertEqual(used, total)
        self.assertGreater(total, 700)
        reached = {node.name for case in cases for node in case.tree.nodes()}
        self.assertEqual({name for name in deriver.heights if name != "SourceFile"} - reached, set())
        # Goals come first and lie in manifest mode; the free texts take every context.
        goals = [case for case in cases if case.goal]
        self.assertTrue(goals and all(case.context.mode == "manifest" for case in goals))
        self.assertEqual({case.context for case in cases if not case.goal}, set(derivations.CONTEXTS))

    def test_free_texts_keep_the_depth_bound(self):
        toy = book_grammar.Grammar(book_grammar.read_productions(
            (book_grammar.ROOT / "docs" / book_grammar.GRAMMAR_CHAPTER).read_text().replace(
                "SourceFile -> Item*", "SourceFile -> Item*\nNest -> `(` Nest `)` | `(` `)` | Nest Nest")))
        deriver = derivations.Deriver(toy, seed=1, depth=4)

        def depth(node):
            return 1 + max((depth(child) for child in node.children if isinstance(child, Node)), default=0)

        self.assertTrue(all(depth(deriver.derive("Nest")) <= 5 for _ in range(200)))

    def test_a_goal_reaches_its_node_and_option(self):
        deriver = derivations.Deriver(GRAMMAR, seed=5)
        tree = deriver.derive("Item", goal=("node", "Fraction"))
        self.assertIn("Fraction", {node.name for node in tree.nodes()})
        key = next(key for key, (owner, _) in deriver.points.items() if owner == "PullbackMode")
        tree = deriver.derive("Item", goal=("point", key, 1))
        self.assertIn("recomputed", list(tree.leaves()))
        self.assertTrue(deriver.covered(("point", key, 1)))

    def test_except_and_token_classes_derive_their_tokens(self):
        deriver = derivations.Deriver(GRAMMAR, seed=2)
        endpoints = {" ".join(deriver.derive("Endpoint").leaves()) for _ in range(300)}
        self.assertNotIn("Base", endpoints)
        self.assertIn("Base ( QQ )", endpoints)
        for name in ("INTEGER_LITERAL", "FLOAT_LITERAL"):
            for _ in range(50):
                token = deriver.token(name)
                self.assertTrue(GRAMMAR.matches(name, token), token)

    def test_render_gives_the_place_of_each_node(self):
        tree = Node("Statement", [Node("LetStatement", ["let", "a", "=", Node("Expression", ["1"]), ";"]),
                                  Node("Tail", ["b"])])
        text, places = derivations.render(tree)
        self.assertEqual(text, "let a = 1 ;\nb")
        self.assertEqual(places[id(tree.children[1])], (2, 1))
        self.assertEqual(places[id(tree.children[0].children[3])], (1, 9))
        for context in derivations.CONTEXTS:
            program = context.program(text)
            line, column = context.position(2, 1)
            self.assertTrue(program.splitlines()[line - 1][column - 1:].startswith("b"), context)
            line, column = context.position(1, 9)
            self.assertTrue(program.splitlines()[line - 1][column - 1:].startswith("1 ;"), context)


class RuleTests(unittest.TestCase):
    def names(self, tree, mode="manifest"):
        return [rule.name for rule, _, _ in derivations.applicable(tree, mode, GRAMMAR)]

    def test_chained_comparisons(self):
        self.assertEqual(self.names(expression("a", "<", "b", "+", "c", "<", "d")), ["chained comparison"])
        self.assertEqual(self.names(expression("a", "<", "b", "&&", "c", "<", "d")), [])
        grouped = Node("Expression", [Node("GroupedExpression", ["(", expression("a", "<", "b"), ")"])])
        self.assertEqual(self.names(expression(grouped, "==", "c")), [])
        unary = Node("Expression", [Node("OperatorExpression", [Node("UnaryOperator", ["!"]),
                                                                expression("a", "<", "b")])])
        self.assertEqual(self.names(expression(unary, "<", "c")), ["chained comparison"])

    def test_type_names_are_no_families(self):
        def indexed(*leaves):
            return Node("IndexedType", [*leaves[:2], Node("IndexedArguments", list(leaves[2:-1])), leaves[-1]])

        self.assertEqual(self.names(Node("IndexedType", ["Point", "<", ">"])),
                         ["type name as the family of an indexed type"])
        self.assertEqual(self.names(indexed("Point", "<", "X", ",", "Y", ">")), [])
        self.assertEqual(self.names(indexed("Pair", "<", "Bool", ">")), ["type name as the family of an indexed type"])
        self.assertEqual(self.names(indexed("Object", "<", "a", "::", "b", ",", "c", ">")), [])
        self.assertEqual(self.names(indexed("Object", "<", "a", ",", "b", ",", ">")),
                         ["type name as the family of an indexed type"])
        self.assertEqual(self.names(indexed("Shape", "<", "X", ">")), [])

    def test_a_path_that_begins_with_a_type_name_in_flat_mode(self):
        tree = Node("Type", [Node("IndexedType", ["Nat", "::", Node("PathSegment", ["F"]), "<", ">"])])
        self.assertEqual(self.names(tree), [])
        self.assertEqual(self.names(tree, "flat"), ["path that begins with a type name in a type in flat mode",
                                                    "indexed type in flat mode"])
        other = Node("Type", [Node("IndexedType", ["x", "::", Node("PathSegment", ["F"]), "<", ">"])])
        self.assertEqual(self.names(other, "flat"), ["indexed type in flat mode"])

    def test_flat_mode_rules(self):
        path = Node("Path", [Node("PathSegment", ["a"]), "::", Node("PathSegment", ["generic"])])
        tree = Node("Item", ["pub", Node("VisibleItem", [Node("SubtypeDeclaration", ["subtype", "S", "<:", path, ";"])])])
        self.assertEqual(self.names(tree), [])
        self.assertEqual(self.names(tree, "flat"), [
            "pub in flat mode", "path in a selector, a parent or a subtype in flat mode",
            "generic as a path segment in flat mode"])
        used = Node("Item", [Node("VisibleItem", [Node("UseDeclaration", ["use", path, ";"])])])
        self.assertEqual(self.names(used, "flat"), ["item of manifest mode in flat mode",
                                                    "generic as a path segment in flat mode"])


class VerdictTests(unittest.TestCase):
    RULE = derivations.RULES[0]

    def case(self, broken=()):
        context = derivations.CONTEXTS[3]
        return Case(0, context, Node("Statement"), "", "",
                    [(rule, place, frozenset({rule.code})) for rule, place in broken])

    def test_a_derived_text_gives_no_parse_code(self):
        self.assertIsNone(derivations.verdict(self.case(), [((2, 5), "E_NAME")]))
        self.assertIsNone(derivations.verdict(self.case(), []))
        self.assertEqual(derivations.verdict(self.case(), [((2, 5), "E_TYPE"), ((3, 1), "E_UNSUPPORTED")]),
                         "the compiler gives E_UNSUPPORTED")

    def test_a_text_that_breaks_a_rule_gives_its_code(self):
        broken = [(self.RULE, (2, 9))]
        self.assertIsNone(derivations.verdict(self.case(broken), [((2, 11), "E_PARSE")]))
        # An error of another class at or before the place stops the frontend there.
        self.assertIsNone(derivations.verdict(self.case(broken), [((2, 9), "E_RESERVED")]))
        self.assertIsNone(derivations.verdict(self.case(broken), [((1, 4), "E_LIMIT")]))
        self.assertIsNone(derivations.verdict(self.case(broken), [((2, 1), "E_TYPE"), ((3, 1), "E_NAME")]))
        for found in ([((3, 1), "E_RESERVED")], [((2, 10), "E_TYPE")], [(None, "E_PROTOCOL")], []):
            self.assertIn("the text breaks the rules (chained comparison) at 2:9",
                          derivations.verdict(self.case(broken), found), found)
        self.assertEqual(derivations.verdict(self.case(broken), [((1, 1), "E_UNSUPPORTED")]),
                         "the compiler gives E_UNSUPPORTED")

    def test_a_break_may_give_the_codes_of_the_rules_of_its_type(self):
        def pair(*arguments):
            leaves = ["Pair", "<", *arguments, ">"]
            tree = Node("Type", [Node("IndexedType", [*leaves[:2], Node("IndexedArguments", leaves[2:-1]), ">"])])
            return [(rule.name, codes) for rule, _, codes in derivations.applicable(tree, "manifest", GRAMMAR)]

        self.assertEqual(pair("a"), [("type name as the family of an indexed type", {"E_PARSE", "E_TYPE"})])
        context = derivations.CONTEXTS[6]
        broken = [(derivations.RULES[6], (1, 17), frozenset({"E_PARSE", "E_TYPE"}))]
        case = Case(0, context, Node("Type"), "", "", broken)
        self.assertIsNone(derivations.verdict(case, [((1, 22), "E_TYPE")]))
        self.assertIsNone(derivations.verdict(case, [((1, 22), "E_PARSE")]))
        self.assertIsNotNone(derivations.verdict(case, [((1, 22), "E_NAME")]))

    def test_diagnostics_are_read_with_their_places(self):
        stderr = textwrap.dedent("""
            src/main.vast:3:7: E_PARSE: expected `)`
            src/main.vast:3:1: note: here
            main.vast:4:2: E_TYPE: expected Int
            Vastitas.toml:1:1: E_PROTOCOL: Fn signatures contain only scalars
            E_USAGE: unknown option
            """)
        self.assertEqual(derivations.diagnostics(stderr), [
            ((3, 7), "E_PARSE"), ((4, 2), "E_TYPE"), (None, "E_PROTOCOL"), (None, "E_USAGE")])


class RunTests(unittest.TestCase):
    def test_the_compiler_runs_on_each_mode(self):
        with tempfile.TemporaryDirectory() as directory:
            compiler = Path(directory) / "fake-vastitas"
            compiler.write_text(textwrap.dedent(f"""\
                #!{sys.executable}
                import pathlib, sys
                target = pathlib.Path(sys.argv[-1])
                sys.stderr.write(f"{{target}}:1:1: E_NAME: {{' '.join(sys.argv[1:-1])}} "
                                 f"{{sorted(p.name for p in target.parent.iterdir())}}\\n")
                """))
            compiler.chmod(compiler.stat().st_mode | stat.S_IXUSR)
            work = Path(directory) / "work"
            work.mkdir()
            flat = Case(1, derivations.CONTEXTS[1], Node("Item"), "", "fn f() -> Int { 0 }\n", [])
            manifest = Case(2, derivations.CONTEXTS[0], Node("Item"), "", "fn f() -> Int { 0 }\n", [])
            self.assertEqual(derivations.run(str(compiler), flat, work),
                             "main.vast:1:1: E_NAME: check ['main.vast']\n")
            self.assertEqual(derivations.run(str(compiler), manifest, work),
                             "Vastitas.toml:1:1: E_NAME: check --manifest-path ['Vastitas.toml', 'src']\n")
            self.assertEqual((work / "case-2/src/main.vast").read_text(), "fn f() -> Int { 0 }\n")


if __name__ == "__main__":
    unittest.main()

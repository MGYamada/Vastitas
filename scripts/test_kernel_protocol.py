"""The reader of the wire schema epoch (#533) and the scripts that use it."""

from pathlib import Path
import tempfile
import unittest

import kernel_protocol


class KernelProtocolTests(unittest.TestCase):
    def read(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "Protocol.lean"
            path.write_text(text, encoding="utf-8")
            return kernel_protocol.current_protocol(path)

    def test_reads_the_kernel_definition(self):
        source = kernel_protocol.SOURCE.read_text(encoding="utf-8")
        self.assertIn(f"{kernel_protocol.PREFIX}{kernel_protocol.CURRENT_PROTOCOL}\n", source)
        self.assertEqual(kernel_protocol.current_protocol(), kernel_protocol.CURRENT_PROTOCOL)

    def test_reads_one_decimal_definition(self):
        self.assertEqual(self.read("/-- doc -/\ndef currentProtocol : Nat := 12\n"), 12)
        self.assertEqual(self.read("def currentProtocol : Nat := 7  \n"), 7)

    def test_rejects_a_missing_repeated_or_malformed_definition(self):
        for text in ("def otherProtocol : Nat := 10\n",
                     "def currentProtocol : Nat := 10\ndef currentProtocol : Nat := 11\n",
                     "def currentProtocol : Nat := ten\n",
                     "def currentProtocol : Nat := -1\n",
                     "def currentProtocol : Nat := 1 + 9\n",
                     "  def currentProtocol : Nat := 10\n"):
            with self.subTest(text=text), self.assertRaises(ValueError):
                self.read(text)

    def test_every_reader_takes_the_kernel_epoch(self):
        import check_resource_cleanup
        import diagnostic_reference
        import doctest_result_reference
        for module in (diagnostic_reference, doctest_result_reference):
            self.assertEqual(module.PROTOCOL, kernel_protocol.CURRENT_PROTOCOL)
        self.assertEqual(check_resource_cleanup.CURRENT_PROTOCOL, kernel_protocol.CURRENT_PROTOCOL)


if __name__ == "__main__":
    unittest.main()

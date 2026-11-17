"""The wire schema epoch, read from the kernel's one definition (#533).

The kernel holds the epoch in `currentProtocol` of
`lean-kernel/VastitasKernel/Protocol.lean`. `build.rs` reads the same line for
the driver's `ir::PROTOCOL`: exactly one line `def currentProtocol : Nat := N`
with a decimal `N`. Scripts and experiment harnesses read the number here, so
that a change of the epoch reaches them without a second literal.
"""

from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "lean-kernel/VastitasKernel/Protocol.lean"
PREFIX = "def currentProtocol : Nat := "
_DECIMAL = re.compile(r"[0-9]+\Z")


def current_protocol(source=SOURCE):
    """The `N` of the one line `def currentProtocol : Nat := N` of `source`."""
    values = [line[len(PREFIX):].strip()
              for line in Path(source).read_text(encoding="utf-8").splitlines()
              if line.startswith(PREFIX)]
    if len(values) != 1 or not _DECIMAL.match(values[0]):
        raise ValueError(f"{source} must define `{PREFIX}N` exactly once, with a decimal N")
    return int(values[0])


CURRENT_PROTOCOL = current_protocol()

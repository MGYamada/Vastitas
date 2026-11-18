"""Audit emitted entry/cleanup envelopes before wrapping private fixtures.

The old IO Unit envelopes remain supported for retained evidence. Current
programs return UInt32 after cleanup; only the terminal result plumbing is
normalized for the harnesses' existing instruction audits.
"""
import re


def normalize_main(text):
    """Recognize the complete status envelope, without guessing a new shape."""
    marker = 'def main : IO UInt32 := do\n'
    if marker not in text:
        return text
    if text.count('def main :') != 1:
        raise ValueError('unexpected generated main')
    preamble, body = text.split(marker)
    lines = body.splitlines()
    if not lines or lines[0] != '  let mut status : UInt32 := 0' or lines[-1] != '  pure status':
        raise ValueError('unexpected exit-status envelope')
    # The status assignment must be the last operation in the single arena's
    # try block. The caller's cleanup and instruction audit checks that position.
    result = re.compile(
        r'    status := \(UInt32.ofNat \(Int.toNat \(Int.emod '
        r'\((VastitasGenerated\.[A-Za-z0-9_]+(?: resourceValue_[0-9]+)*)\) 256\)\)\)')
    matches = [(i, result.fullmatch(line)) for i, line in enumerate(lines[1:-1], 1)
               if re.search(r'\bstatus\b', line)]
    if len(matches) != 1 or matches[0][1] is None:
        raise ValueError('unexpected exit-status assignment')
    index, match = matches[0]
    lines[index] = f'    IO.println ({match[1]})'
    return preamble + 'def main : IO Unit := do\n' + '\n'.join(lines[1:-1]) + '\n'


def require_success(result):
    """The current public fixtures exit zero and have no display operations."""
    if (type(result.get('returncode')) is not int or result['returncode'] != 0 or result.get('stdout') != '' or
            result.get('stderr') != ''):
        raise ValueError('canonical executable did not exit successfully without output')


def require_execution(generated, result):
    """Verify current or retained results against their emitted entry contract."""
    if 'def main : IO UInt32 := do\n' in generated:
        normalize_main(generated)
        require_success(result)
    elif (generated.count('def main : IO Unit := do\n') != 1 or
          type(result.get('returncode')) is not int or result['returncode'] != 0 or
          result.get('stdout', '').strip() != '0' or result.get('stderr') != ''):
        raise ValueError('retained canonical executable did not print its checked result')


def suffix(style, arena, indent=2):
    spaces = ' ' * indent
    if style == 'finally':
        return f'{spaces}finally\n{spaces}  close {arena}\n'
    if style == 'unit-catch':
        return (f'{spaces}catch cleanupError =>\n{spaces}  close {arena}\n'
                f'{spaces}  throw cleanupError\n{spaces}close {arena}\n')
    raise ValueError('unknown cleanup style')


def split(lines, arena):
    # Verifiers pass a complete generated program; body-only callers have
    # already normalized it in split_generated.
    if 'def main : IO UInt32 := do' in lines:
        lines = normalize_main('\n'.join(lines) + '\n').splitlines()
    for style in ('finally', 'unit-catch'):
        tail = suffix(style, arena).splitlines()
        if lines[-len(tail):] == tail:
            return style, lines[:-len(tail)]
    raise ValueError('unexpected cleanup envelope')


def preserve(generated, wrapped, arena='arena', expected=2):
    """The caller separately audits the complete body; never guess a cleanup."""
    style, _ = split(generated.splitlines(), arena)
    pattern = re.compile(r'^( *)finally\n\1  close ' + re.escape(arena) + r'\n', re.MULTILINE)
    matches = list(pattern.finditer(wrapped))
    if len(matches) != expected:
        raise ValueError('unexpected wrapper cleanup coverage')
    if style == 'finally':
        return wrapped
    return pattern.sub(lambda m: suffix(style, arena, len(m[1])), wrapped)

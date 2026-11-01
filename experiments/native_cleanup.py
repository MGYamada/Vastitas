"""Preserve either exact emitted IO Unit cleanup envelope in private fixtures."""
import re


def suffix(style, arena, indent=2):
    spaces = ' ' * indent
    if style == 'finally':
        return f'{spaces}finally\n{spaces}  close {arena}\n'
    if style == 'unit-catch':
        return (f'{spaces}catch cleanupError =>\n{spaces}  close {arena}\n'
                f'{spaces}  throw cleanupError\n{spaces}close {arena}\n')
    raise ValueError('unknown cleanup style')


def split(lines, arena):
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

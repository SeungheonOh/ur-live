export type EditorEdit = {
  from: number;
  to: number;
  text: string;
  anchor: number;
  head: number;
};

// Small, local editing operations, not a formatter or an alternative Ur parser.
// Never rewrite any text outside the lines the user is editing.
export function indentationEdit(
  source: string,
  start: number,
  end: number,
  key: string,
  shift = false,
): EditorEdit | null {
  const lineStart = start === 0 ? 0 : source.lastIndexOf('\n', start - 1) + 1;
  const before = source.slice(lineStart, start);
  const indent = before.match(/^[\t ]*/)?.[0] ?? '';
  const replace = (
    from: number,
    to: number,
    text: string,
    caret = from + text.length,
  ): EditorEdit => ({ from, to, text, anchor: caret, head: caret });

  if (key === 'Tab') {
    if (start === end && !shift) {
      let column = 0;
      for (const char of before) column += char === '\t' ? 2 - (column % 2) : 1;
      return replace(start, end, ' '.repeat(2 - (column % 2)));
    }
    const lastSelected =
      end > start && source[end - 1] === '\n' ? end - 1 : end;
    const nextBreak = source.indexOf('\n', lastSelected);
    const to = nextBreak < 0 ? source.length : nextBreak;
    const lines = source.slice(lineStart, to).split('\n');
    const deltas = lines.map((line) =>
      shift ? -(line.match(/^(?:\t| {1,2})/)?.[0].length ?? 0) : 2,
    );
    const text = lines
      .map((line, i) => (shift ? line.slice(-deltas[i]) : '  ' + line))
      .join('\n');
    const mapPosition = (position: number) => {
      let offset = lineStart;
      let change = 0;
      for (let i = 0; i < lines.length; i++) {
        const delta = deltas[i];
        if (position <= offset + lines[i].length)
          return Math.max(offset + change, position + change + delta);
        change += delta;
        offset += lines[i].length + 1;
      }
      return position + change;
    };
    return {
      from: lineStart,
      to,
      text,
      anchor: mapPosition(start),
      head: mapPosition(end),
    };
  }
  if (key === 'Backspace' && start === end && before && /^[ ]+$/.test(before)) {
    return replace(start - (before.length % 2 || 2), end, '');
  }
  if (key !== 'Enter') return null;
  const after = source.slice(end).split('\n', 1)[0];
  const trimmed = before.trimEnd();
  const tag = trimmed.endsWith('/>')
    ? null
    : trimmed.match(/<([A-Za-z][\w:]*)\b[^<>]*>$/);
  const opens =
    /(?:=>|=|\b(?:let|in|struct|sig|of|then|else)|[({[])$/.test(trimmed) ||
    !!tag;
  const pair =
    (trimmed.endsWith('(') && /^\s*\)/.test(after)) ||
    (trimmed.endsWith('{') && /^\s*\}/.test(after)) ||
    (trimmed.endsWith('[') && /^\s*\]/.test(after)) ||
    (tag && after.trimStart().startsWith(`</${tag[1]}>`));
  const inner = indent + (opens ? '  ' : '');
  return replace(
    start,
    end,
    '\n' + inner + (pair ? '\n' + indent : ''),
    start + 1 + inner.length,
  );
}

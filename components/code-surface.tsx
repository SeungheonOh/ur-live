'use client';

import {
  useMemo,
  useLayoutEffect,
  useRef,
  type KeyboardEventHandler,
  type ReactNode,
} from 'react';
import { Textarea } from '@/components/ui/textarea';
import { indentationEdit } from '@/lib/editor-editing';

const keywords = new Set(
  'fun val con type datatype class signature structure struct sig end functor open let in case of if then else fn return where with rec and as export import const async await function new throw try catch finally true false null undefined'.split(
    ' ',
  ),
);
const types = new Set(
  'int float string char bool unit transaction page source signal option list'.split(
    ' ',
  ),
);

// Display-only coloring: text is never rewritten or interpreted as HTML.
// This is not the compiler lexer and cannot accept or reject Ur programs.
function colorize(source: string, language: 'ur' | 'javascript') {
  const pattern =
    language === 'ur'
      ? /\(\*[\s\S]*?(?:\*\)|$)|"(?:\\[\s\S]|[^"\\])*(?:"|$)|<\/?[A-Za-z][\w:.-]*|\b\d+(?:\.\d+)?\b|\b[A-Za-z_][\w']*/g
      : /\/\/[^\n]*|\/\*[\s\S]*?(?:\*\/|$)|"(?:\\[\s\S]|[^"\\])*(?:"|$)|'(?:\\[\s\S]|[^'\\])*(?:'|$)|\b\d+(?:\.\d+)?n?\b|\b[A-Za-z_$][\w$]*/g;
  const result: ReactNode[] = [];
  let position = 0;
  for (const match of source.matchAll(pattern)) {
    const value = match[0];
    const kind =
      value.startsWith('(*') || value.startsWith('//') || value.startsWith('/*')
        ? 'comment'
        : value.startsWith('"') || value.startsWith("'")
          ? 'string'
          : value.startsWith('<')
            ? 'tag'
            : /^\d/.test(value)
              ? 'number'
              : keywords.has(value)
                ? 'keyword'
                : types.has(value)
                  ? 'type'
                  : '';
    result.push(source.slice(position, match.index));
    result.push(
      kind ? (
        <span key={match.index} className={`syntax-${kind}`}>
          {value}
        </span>
      ) : (
        value
      ),
    );
    position = match.index + value.length;
  }
  result.push(source.slice(position));
  return result;
}

export function CodeOutput({ source }: { source: string }) {
  const colored = useMemo(() => colorize(source, 'javascript'), [source]);
  return (
    <div className="code-scroll">
      <pre className="code-text">
        <code>{colored}</code>
      </pre>
    </div>
  );
}

export function SourceEditor({
  filename,
  source,
  disabled,
  onChange,
  onKeyDown,
}: {
  filename: string;
  source: string;
  disabled: boolean;
  onChange: (value: string) => void;
  onKeyDown: KeyboardEventHandler<HTMLTextAreaElement>;
}) {
  const colorLayer = useRef<HTMLPreElement>(null);
  const gutter = useRef<HTMLPreElement>(null);
  const editor = useRef<HTMLTextAreaElement>(null);
  const pendingSelection = useRef<[number, number] | null>(null);
  const applying = useRef(false);
  const escapeTab = useRef(false);
  useLayoutEffect(() => {
    if (pendingSelection.current && editor.current) {
      editor.current.setSelectionRange(...pendingSelection.current);
      pendingSelection.current = null;
    }
    const area = editor.current;
    if (area && colorLayer.current && gutter.current) {
      colorLayer.current.style.transform = `translate(${-area.scrollLeft}px, ${-area.scrollTop}px)`;
      gutter.current.style.transform = `translateY(${-area.scrollTop}px)`;
    }
  }, [source]);
  const colored = useMemo(() => colorize(source, 'ur'), [source]);
  const lines = useMemo(
    () =>
      source
        .split('\n')
        .map((_, i) => i + 1)
        .join('\n'),
    [source],
  );
  return (
    <div className="code-surface">
      <div className="code-gutter" aria-hidden="true">
        <pre ref={gutter} className="code-text">
          {lines}
        </pre>
      </div>
      <div className="code-color-layer" aria-hidden="true">
        <pre ref={colorLayer} className="code-text">
          {colored}
          {'\n'}
        </pre>
      </div>
      <Textarea
        ref={editor}
        id={`source-${filename}`}
        aria-label={`${filename} source code`}
        aria-describedby="editor-keyboard-help"
        className="code-editor code-text"
        value={source}
        disabled={disabled}
        onChange={(event) => {
          if (!applying.current) onChange(event.target.value);
        }}
        onKeyDown={(event) => {
          onKeyDown(event);
          if (
            event.defaultPrevented ||
            event.nativeEvent.isComposing ||
            event.ctrlKey ||
            event.metaKey ||
            event.altKey
          )
            return;
          if (event.key === 'Escape') {
            escapeTab.current = true;
            return;
          }
          const leave = escapeTab.current && event.key === 'Tab';
          escapeTab.current = false;
          if (leave) return;
          const area = event.currentTarget;
          const edit = indentationEdit(
            source,
            area.selectionStart,
            area.selectionEnd,
            event.key,
            event.shiftKey,
          );
          if (!edit) return;
          event.preventDefault();
          const expected =
            source.slice(0, edit.from) + edit.text + source.slice(edit.to);
          if (expected === source) return;
          applying.current = true;
          area.setSelectionRange(edit.from, edit.to);
          // insertText keeps native undo history. setRangeText is a fallback for
          // browsers that don't provide this editing command. Never insert HTML.
          try {
            // eslint-disable-next-line @typescript-eslint/no-deprecated -- The native undo buffer has no replacement editing API; fallback below.
            document.execCommand('insertText', false, edit.text);
          } catch {}
          if (area.value !== expected) {
            area.value = source;
            area.setRangeText(edit.text, edit.from, edit.to, 'end');
          }
          applying.current = false;
          pendingSelection.current = [edit.anchor, edit.head];
          onChange(expected);
        }}
        onScroll={(event) => {
          const { scrollLeft, scrollTop } = event.currentTarget;
          if (colorLayer.current)
            colorLayer.current.style.transform = `translate(${-scrollLeft}px, ${-scrollTop}px)`;
          if (gutter.current)
            gutter.current.style.transform = `translateY(${-scrollTop}px)`;
        }}
        wrap="off"
        spellCheck={false}
        autoCapitalize="off"
        autoCorrect="off"
        autoComplete="off"
      />
    </div>
  );
}

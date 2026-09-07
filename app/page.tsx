'use client';

import { useCallback, useEffect, useRef, useState } from 'react';
import { Button } from '@/components/ui/button';
import { Textarea } from '@/components/ui/textarea';
import {
  NativeSelect,
  NativeSelectOption,
} from '@/components/ui/native-select';
import { CompilerClient, type Compilation } from '@/lib/compiler-client';
import { resultFrame } from '@/lib/result-frame';

const initialSource = `fun identity [a] (x : a) : a = x

fun main () : transaction page =
    return <xml><body>
      <h1>Hello from Ur</h1>
      <p>The answer is {[identity 42]}.</p>
    </body></xml>
`;

export default function Playground() {
  const [source, setSource] = useState(initialSource);
  const [examples, setExamples] = useState<Record<string, string>>({
    hello: initialSource,
  });
  const [selected, setSelected] = useState('hello');
  const [status, setStatus] = useState('Loading the WebAssembly compiler…');
  const [busy, setBusy] = useState(false);
  const [result, setResult] = useState<Compilation | null>(null);
  const [diagnostics, setDiagnostics] = useState('');
  const [logs, setLogs] = useState<string[]>([]);
  const [running, setRunning] = useState(false);
  const [frame, setFrame] = useState('');
  const compiler = useRef<CompilerClient | null>(null);
  const execution = useRef<Worker | null>(null);
  const iframe = useRef<HTMLIFrameElement | null>(null);
  const channel = useRef('');
  const frameReady = useRef(false);
  const frameQueue = useRef<unknown[]>([]);
  const timer = useRef<ReturnType<typeof setTimeout> | undefined>(undefined);
  const revision = useRef(0);
  const sourceRef = useRef(source);

  const stop = useCallback(() => {
    execution.current?.terminate();
    execution.current = null;
    clearTimeout(timer.current);
    setRunning(false);
  }, []);
  const showFrame = useCallback((data: unknown) => {
    if (frameReady.current)
      iframe.current?.contentWindow?.postMessage(
        { channel: channel.current, ...(data as object) },
        '*',
      );
    else frameQueue.current.push(data);
  }, []);
  const startProgram = useCallback(
    (javascript: string) => {
      stop();
      setLogs([]);
      setRunning(true);
      channel.current = crypto.randomUUID();
      frameReady.current = false;
      frameQueue.current = [];
      setFrame(resultFrame(channel.current, crypto.randomUUID()));
      const worker = new Worker('/execution-worker.mjs', { type: 'module' });
      execution.current = worker;
      timer.current = setTimeout(() => {
        stop();
        setDiagnostics('Program exceeded 10 seconds and was stopped.');
      }, 10_000);
      worker.onmessage = ({ data }) => {
        if (execution.current !== worker) return;
        if (data.type === 'result' || data.type === 'event-complete')
          clearTimeout(timer.current);
        if (data.type === 'result' || data.type === 'patch') showFrame(data);
        if (data.type === 'log')
          setLogs((current) => [...current.slice(-199), String(data.message)]);
        if (data.type === 'error') {
          setDiagnostics(data.message);
          stop();
        }
      };
      worker.onerror = (event) => {
        setDiagnostics(event.message || 'Program worker failed');
        stop();
      };
      worker.postMessage({ type: 'run', javascript });
    },
    [showFrame, stop],
  );

  const compile = useCallback(
    async (input = sourceRef.current) => {
      const version = ++revision.current;
      stop();
      setBusy(true);
      setDiagnostics('');
      setResult(null);
      setFrame('');
      try {
        compiler.current ??= new CompilerClient(setStatus);
        const compiled = await compiler.current.compile(input);
        if (version !== revision.current) return compiled;
        setResult(compiled);
        setDiagnostics(compiled.diagnostics);
        setStatus(
          `Compiled in ${Math.round(compiled.milliseconds)} ms · ${(compiled.memoryBytes / 1048576).toFixed(0)} MiB Wasm memory`,
        );
        if (compiled.ok) startProgram(compiled.javascript);
        return compiled;
      } catch (error) {
        if (version === revision.current) {
          setDiagnostics(String(error));
          compiler.current?.dispose();
          compiler.current = null;
        }
        throw error;
      } finally {
        if (version === revision.current) setBusy(false);
      }
    },
    [startProgram, stop],
  );

  useEffect(() => {
    compiler.current = new CompilerClient(setStatus);
    void fetch('/examples.json')
      .then((response) => {
        if (!response.ok) throw new Error('Examples unavailable');
        return response.json();
      })
      .then((value) => {
        if (
          value &&
          typeof value === 'object' &&
          Object.values(value).every((item) => typeof item === 'string')
        )
          setExamples(value as Record<string, string>);
      })
      .catch(() => {});
    return () => {
      compiler.current?.dispose();
      stop();
    };
  }, [stop]);

  useEffect(() => {
    const receive = ({ source: sender, data }: MessageEvent) => {
      if (
        sender !== iframe.current?.contentWindow ||
        data?.channel !== channel.current
      )
        return;
      if (data.type === 'frame-ready') {
        frameReady.current = true;
        for (const message of frameQueue.current) showFrame(message);
        frameQueue.current = [];
      }
      if (
        data.type === 'event' &&
        execution.current &&
        Number.isSafeInteger(data.handler)
      ) {
        clearTimeout(timer.current);
        timer.current = setTimeout(() => {
          stop();
          setDiagnostics('Event handler exceeded 10 seconds and was stopped.');
        }, 10_000);
        execution.current.postMessage({
          type: 'event',
          handler: data.handler,
          event: data.event,
          id: crypto.randomUUID(),
        });
      }
    };
    addEventListener('message', receive);
    return () => removeEventListener('message', receive);
  }, [showFrame, stop]);

  // Progressive enhancement: the same compile action is available to an agent
  // in browsers implementing WebMCP. No remote execution or extra privileges.
  useEffect(() => {
    const context = (
      document as unknown as {
        modelContext?: {
          registerTool: (tool: unknown, options: unknown) => unknown;
        };
      }
    ).modelContext;
    if (!context?.registerTool) return;
    const lifecycle = new AbortController();
    try {
      void Promise.resolve(
        context.registerTool(
          {
            name: 'compile_ur',
            description:
              'Replace the editor source, compile Ur locally with WebAssembly, and run its browser JavaScript.',
            inputSchema: {
              type: 'object',
              properties: { source: { type: 'string' } },
              required: ['source'],
              additionalProperties: false,
            },
            annotations: { readOnlyHint: false, untrustedContentHint: true },
            execute: async (input: unknown) => {
              if (
                !input ||
                typeof input !== 'object' ||
                typeof (input as { source?: unknown }).source !== 'string'
              )
                throw new Error('Expected Ur source text');
              const value = (input as { source: string }).source;
              sourceRef.current = value;
              setSource(value);
              setSelected('');
              const compiled = await compile(value);
              return {
                ok: compiled?.ok,
                diagnostics: compiled?.diagnostics,
                milliseconds: compiled?.milliseconds,
              };
            },
          },
          { signal: lifecycle.signal },
        ),
      ).catch(() => {});
    } catch {}
    return () => lifecycle.abort();
  }, [compile]);

  const changeSource = (value: string) => {
    sourceRef.current = value;
    setSource(value);
    setResult(null);
    setDiagnostics('');
    stop();
    setFrame('');
  };
  const cancel = () => {
    ++revision.current;
    compiler.current?.dispose();
    compiler.current = null;
    setBusy(false);
    setDiagnostics('Compilation cancelled.');
    setStatus('Ready to restart compiler');
  };
  return (
    <main className="playground">
      <header>
        <h1>Vr playground</h1>
        <p>Ur → WebAssembly compiler → JavaScript</p>
      </header>
      <div className="toolbar">
        <label htmlFor="example">Example</label>
        <NativeSelect
          id="example"
          value={selected}
          disabled={busy}
          onChange={(event) => {
            setSelected(event.target.value);
            if (examples[event.target.value])
              changeSource(examples[event.target.value]);
          }}
        >
          <NativeSelectOption value="" disabled>
            Custom program
          </NativeSelectOption>
          {Object.keys(examples).map((name) => (
            <NativeSelectOption key={name} value={name}>
              {name.replaceAll('-', ' ')}
            </NativeSelectOption>
          ))}
        </NativeSelect>
        <Button disabled={busy} onClick={() => void compile().catch(() => {})}>
          Compile &amp; run
        </Button>
        {busy && (
          <Button variant="outline" onClick={cancel}>
            Cancel compilation
          </Button>
        )}
        {running && (
          <Button variant="outline" onClick={stop}>
            Stop program
          </Button>
        )}
        <output>{busy ? 'Compiling in WebAssembly…' : status}</output>
      </div>
      <div className="workspace">
        <section>
          <h2>
            <label htmlFor="source">Ur source</label>
          </h2>
          <Textarea
            id="source"
            className="code-editor"
            value={source}
            disabled={busy}
            onChange={(event) => {
              setSelected('');
              changeSource(event.target.value);
            }}
            onKeyDown={(event) => {
              if ((event.ctrlKey || event.metaKey) && event.key === 'Enter') {
                event.preventDefault();
                if (!busy) void compile().catch(() => {});
              }
            }}
            spellCheck={false}
            autoCapitalize="off"
            autoCorrect="off"
          />
        </section>
        <section>
          <h2>JavaScript</h2>
          <pre className="output">
            {result?.javascript ||
              'Compile a program to see its generated JavaScript.'}
          </pre>
        </section>
      </div>
      {diagnostics && (
        <section aria-live="polite">
          <h2>Diagnostics</h2>
          <pre className="diagnostic">{diagnostics}</pre>
        </section>
      )}
      <section>
        <h2>Result</h2>
        {frame ? (
          <iframe
            ref={iframe}
            title="Ur program output"
            className="result result-frame"
            sandbox="allow-scripts"
            srcDoc={frame}
          />
        ) : (
          <div className="result">Your program’s output will appear here.</div>
        )}
      </section>
      {logs.length > 0 && (
        <section>
          <h2>Program log</h2>
          <pre>{logs.join('\n')}</pre>
        </section>
      )}
      <footer>
        The compiler and program run in your browser. No SQL, server requests,
        files, or native FFI. Entry point:{' '}
        <code>main : unit → transaction page</code>. Ctrl/⌘ + Enter to compile.
      </footer>
    </main>
  );
}

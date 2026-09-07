'use client';

import { useCallback, useEffect, useRef, useState } from 'react';
import { Button } from '@/components/ui/button';
import { Tabs, TabsList, TabsTrigger, TabsContent } from '@/components/ui/tabs';
import { CodeOutput } from '@/components/code-surface';
import { ProjectEditor } from '@/components/project-editor';
import {
  ResizablePanelGroup,
  ResizablePanel,
  ResizableHandle,
} from '@/components/ui/resizable';
import {
  singleFileProject,
  validateProject,
  type BrowserProject,
} from '../public/project.mjs';
import {
  Braces,
  Check,
  CircleAlert,
  Globe2,
  LoaderCircle,
  LockKeyhole,
  Maximize2,
  Minimize2,
  Play,
  Square,
  Terminal,
} from 'lucide-react';
import {
  Dialog,
  DialogContent,
  DialogDescription,
  DialogHeader,
  DialogTitle,
  DialogTrigger,
} from '@/components/ui/dialog';
import { CompilerClient, type Compilation } from '@/lib/compiler-client';
import { resultFrame } from '@/lib/result-frame';

const initialSource = `fun identity [a] (x : a) : a = x

fun main () : transaction page =
    return <xml><body>
      <h1>Hello from Ur</h1>
      <p>The answer is {[identity 42]}.</p>
    </body></xml>
`;

const demoLabels: Record<string, string> = {
  'demo-hello': 'Hello — first page',
  'demo-react': 'React — reactive text',
  'demo-sum': 'Sum — record folding',
  'demo-tc-sum': 'TcSum — numeric type classes',
  'demo-list-edit': 'ListEdit — editable linked list',
  'demo-threads': 'Threads — concurrent messages',
};

export default function Playground() {
  const [project, setProject] = useState<BrowserProject>(() =>
    singleFileProject(initialSource),
  );
  const [projectEpoch, setProjectEpoch] = useState(0);
  const [filesOpen, setFilesOpen] = useState(true);
  const [projects, setProjects] = useState<Record<string, BrowserProject>>({});
  const [vertical, setVertical] = useState(false);
  const [expanded, setExpanded] = useState(false);
  const expandedRef = useRef(false);
  const previewModeButton = useRef<HTMLButtonElement>(null);
  const [examples, setExamples] = useState<Record<string, string>>({
    hello: initialSource,
  });
  const [selected, setSelected] = useState('hello');
  const [examplesOpen, setExamplesOpen] = useState(false);
  const [status, setStatus] = useState('Loading the WebAssembly compiler…');
  const [busy, setBusy] = useState(false);
  const [result, setResult] = useState<Compilation | null>(null);
  const [diagnostics, setDiagnostics] = useState('');
  const [logs, setLogs] = useState<string[]>([]);
  const [running, setRunning] = useState(false);
  const [frame, setFrame] = useState('');
  const [outputTab, setOutputTab] = useState('javascript');
  const compiler = useRef<CompilerClient | null>(null);
  const execution = useRef<Worker | null>(null);
  const iframe = useRef<HTMLIFrameElement | null>(null);
  const channel = useRef('');
  const frameReady = useRef(false);
  const frameQueue = useRef<unknown[]>([]);
  const timer = useRef<ReturnType<typeof setTimeout> | undefined>(undefined);
  const revision = useRef(0);
  const projectRef = useRef(project);

  const exitPreview = useCallback(() => {
    if (!expandedRef.current) return;
    expandedRef.current = false;
    setExpanded(false);
    previewModeButton.current?.focus();
  }, []);
  useEffect(() => {
    const query = matchMedia('(max-width: 50rem)');
    const update = () => setVertical(query.matches);
    update();
    query.addEventListener('change', update);
    return () => query.removeEventListener('change', update);
  }, []);
  useEffect(() => {
    const keyDown = (event: KeyboardEvent) => {
      if (expanded && event.key === 'Escape') {
        event.preventDefault();
        exitPreview();
      }
    };
    document.addEventListener('keydown', keyDown);
    return () => {
      document.removeEventListener('keydown', keyDown);
    };
  }, [expanded, exitPreview]);
  useEffect(() => {
    if (expanded && outputTab !== 'preview') exitPreview();
  }, [outputTab, expanded, exitPreview]);

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
        setOutputTab('diagnostics');
      }, 10_000);
      worker.onmessage = ({ data }) => {
        if (execution.current !== worker) return;
        if (data.type === 'result' || data.type === 'event-complete')
          clearTimeout(timer.current);
        if (
          data.type === 'result' ||
          data.type === 'patch' ||
          data.type === 'control'
        )
          showFrame(data);
        if (data.type === 'log')
          setLogs((current) => [...current.slice(-199), String(data.message)]);
        if (data.type === 'error') {
          setDiagnostics(data.message);
          setOutputTab('diagnostics');
          stop();
        }
      };
      worker.onerror = (event) => {
        setDiagnostics(event.message || 'Program worker failed');
        setOutputTab('diagnostics');
        stop();
      };
      worker.postMessage({ type: 'run', javascript });
    },
    [showFrame, stop],
  );

  const compile = useCallback(
    async (input = projectRef.current) => {
      const version = ++revision.current;
      exitPreview();
      stop();
      setBusy(true);
      setDiagnostics('');
      setResult(null);
      setFrame('');
      setLogs([]);
      try {
        compiler.current ??= new CompilerClient(setStatus);
        const compiled = await compiler.current.compile(input);
        if (version !== revision.current) return compiled;
        setResult(compiled);
        setDiagnostics(compiled.diagnostics);
        setOutputTab(compiled.ok ? 'preview' : 'diagnostics');
        setStatus(
          `${compiled.ok ? 'Compiled' : 'Checked'} in ${Math.round(compiled.milliseconds)} ms · ${(compiled.memoryBytes / 1048576).toFixed(0)} MiB Wasm memory`,
        );
        if (compiled.ok) startProgram(compiled.javascript);
        return compiled;
      } catch (error) {
        if (version === revision.current) {
          setDiagnostics(String(error));
          setOutputTab('diagnostics');
          compiler.current?.dispose();
          compiler.current = null;
        }
        throw error;
      } finally {
        if (version === revision.current) setBusy(false);
      }
    },
    [startProgram, stop, exitPreview],
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
    void fetch('/projects.json')
      .then((response) => {
        if (!response.ok) throw new Error('Project examples unavailable');
        return response.json();
      })
      .then((value) => {
        if (!value || typeof value !== 'object' || Array.isArray(value))
          throw new Error('Invalid project examples');
        for (const item of Object.values(value)) validateProject(item);
        setProjects(value as Record<string, BrowserProject>);
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
      if (data.type === 'preview-exit') exitPreview();
      if (
        data.type === 'event' &&
        execution.current &&
        Number.isSafeInteger(data.handler)
      ) {
        clearTimeout(timer.current);
        timer.current = setTimeout(() => {
          stop();
          setDiagnostics('Event handler exceeded 10 seconds and was stopped.');
          setOutputTab('diagnostics');
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
  }, [showFrame, stop, exitPreview]);

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
              'Replace the editor with a single Ur source or a multi-file project, compile locally with WebAssembly, and run its browser JavaScript.',
            inputSchema: {
              type: 'object',
              properties: {
                source: { type: 'string' },
                project: {
                  type: 'object',
                  properties: {
                    files: {
                      type: 'object',
                      additionalProperties: { type: 'string' },
                    },
                    entry: { type: 'string' },
                    order: { type: 'array', items: { type: 'string' } },
                  },
                  required: ['files', 'entry', 'order'],
                  additionalProperties: false,
                },
              },
              oneOf: [{ required: ['source'] }, { required: ['project'] }],
              additionalProperties: false,
            },
            annotations: { readOnlyHint: false, untrustedContentHint: true },
            execute: async (input: unknown) => {
              if (!input || typeof input !== 'object')
                throw new Error('Expected Ur source text or a project');
              const value = input as { source?: unknown; project?: unknown };
              if ('source' in value === 'project' in value)
                throw new Error('Provide either source or project, not both');
              if ('source' in value && typeof value.source !== 'string')
                throw new Error('Expected Ur source text');
              const next = validateProject(
                typeof value.source === 'string'
                  ? singleFileProject(value.source)
                  : value.project,
              ) as BrowserProject;
              projectRef.current = next;
              setProject(next);
              setProjectEpoch((epoch) => epoch + 1);
              setSelected('');
              const compiled = await compile(next);
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

  const changeProject = (value: BrowserProject) => {
    projectRef.current = value;
    setProject(value);
    setSelected('');
    setResult(null);
    setDiagnostics('');
    setLogs([]);
    stop();
    setFrame('');
  };
  const cancel = () => {
    ++revision.current;
    compiler.current?.dispose();
    compiler.current = null;
    setBusy(false);
    setDiagnostics('Compilation cancelled.');
    setOutputTab('diagnostics');
    setStatus('Ready to restart compiler');
  };
  const exampleGroups = [
    {
      title: 'Ur/Web demos',
      names: Object.keys(examples).filter((name) => name.startsWith('demo-')),
    },
    {
      title: 'Playground examples',
      names: [
        ...new Set([...Object.keys(projects), ...Object.keys(examples)]),
      ].filter((name) => !name.startsWith('demo-')),
    },
  ];
  return (
    <main className="playground" data-preview-only={expanded || undefined}>
      <header className="topbar" inert={expanded}>
        <div className="identity">
          <span className="wordmark" aria-hidden="true">
            Vr
          </span>
          <div>
            <h1>Vr Playground</h1>
            <p>Compile and run Ur in your browser</p>
          </div>
        </div>
        <div className="topbar-actions">
          <span className="local-label">
            <LockKeyhole aria-hidden="true" /> Runs locally
          </span>
          <Dialog open={examplesOpen} onOpenChange={setExamplesOpen}>
            <DialogTrigger
              render={<Button variant="outline" />}
              disabled={busy}
            >
              Examples
            </DialogTrigger>
            <DialogContent className="examples-dialog">
              <DialogHeader>
                <DialogTitle>Examples</DialogTitle>
                <DialogDescription>
                  Opening an example replaces the current project.
                </DialogDescription>
              </DialogHeader>
              <div className="example-groups">
                {exampleGroups
                  .filter((group) => group.names.length > 0)
                  .map((group) => (
                    <section key={group.title} aria-label={group.title}>
                      <h3>{group.title}</h3>
                      <ul className="example-list">
                        {group.names.map((name) => (
                          <li key={name}>
                            <Button
                              variant="ghost"
                              className="example-choice"
                              disabled={busy}
                              aria-current={
                                selected === name ? 'true' : undefined
                              }
                              onClick={() => {
                                const next =
                                  projects[name] ??
                                  (examples[name] !== undefined
                                    ? singleFileProject(examples[name])
                                    : null);
                                if (!next || busy) return;
                                changeProject(next);
                                setProjectEpoch((epoch) => epoch + 1);
                                setSelected(name);
                                setExamplesOpen(false);
                              }}
                            >
                              <span>
                                {demoLabels[name] ?? name.replaceAll('-', ' ')}
                              </span>
                              {selected === name && (
                                <>
                                  <Check aria-hidden="true" />
                                  <span className="sr-only">
                                    Current example
                                  </span>
                                </>
                              )}
                            </Button>
                          </li>
                        ))}
                      </ul>
                    </section>
                  ))}
              </div>
            </DialogContent>
          </Dialog>
          {busy && (
            <Button variant="outline" onClick={cancel}>
              Cancel
            </Button>
          )}
          {running && (
            <Button variant="outline" onClick={stop}>
              <Square aria-hidden="true" /> Stop program
            </Button>
          )}
          <Button
            className="compile-button"
            disabled={busy}
            onClick={() => void compile().catch(() => {})}
          >
            {busy ? (
              <LoaderCircle className="spinner" aria-hidden="true" />
            ) : (
              <Play aria-hidden="true" />
            )}
            {busy ? 'Compiling…' : 'Compile & run'}
            <kbd title="Control or Command + Enter" aria-hidden="true">
              ⌘ ↵
            </kbd>
          </Button>
        </div>
      </header>
      <ResizablePanelGroup
        className="workspace"
        orientation={vertical ? 'vertical' : 'horizontal'}
        aria-label="Vr compiler workspace"
      >
        <ResizablePanel id="source-pane" defaultSize="52%" minSize="25%">
          <section
            className="source-pane"
            aria-label="Source editor"
            inert={expanded}
          >
            <ProjectEditor
              key={projectEpoch}
              project={project}
              disabled={busy}
              filesOpen={filesOpen}
              onFilesOpenChange={setFilesOpen}
              onChange={changeProject}
              onCompile={() => void compile().catch(() => {})}
            />
          </section>
        </ResizablePanel>
        <ResizableHandle
          withHandle
          className="workspace-divider"
          aria-label="Resize code and result panes"
          inert={expanded}
        />
        <ResizablePanel id="output-pane" defaultSize="48%" minSize="25%">
          <section className="output-pane" aria-label="Compiler output">
            <Tabs
              className="output-tabs"
              value={outputTab}
              onValueChange={(value) => setOutputTab(String(value))}
            >
              <header className="pane-toolbar output-toolbar" inert={expanded}>
                <TabsList
                  variant="line"
                  className="output-tab-list"
                  aria-label="Compiler and program output"
                >
                  <TabsTrigger value="javascript">JavaScript</TabsTrigger>
                  <TabsTrigger value="preview">Preview</TabsTrigger>
                  <TabsTrigger value="diagnostics">
                    Diagnostics
                    {diagnostics && (
                      <span className="tab-count tab-count-error">!</span>
                    )}
                  </TabsTrigger>
                  <TabsTrigger value="logs">
                    Log
                    {logs.length > 0 && (
                      <span className="tab-count">{logs.length}</span>
                    )}
                  </TabsTrigger>
                </TabsList>
              </header>
              <TabsContent value="javascript" className="output-panel">
                <div className="pane-meta">
                  <span>
                    <Braces aria-hidden="true" /> Generated JavaScript
                  </span>
                  <span>ES module</span>
                </div>
                {result?.javascript ? (
                  <CodeOutput source={result.javascript} />
                ) : (
                  <div className="empty-state">
                    <Braces aria-hidden="true" />
                    <h2>
                      {busy
                        ? 'Compiling your program…'
                        : 'Your source, compiled.'}
                    </h2>
                    <p>
                      {busy
                        ? 'Vr is checking and compiling the Ur source in your browser.'
                        : 'Compile an example to inspect the JavaScript emitted by Vr.'}
                    </p>
                  </div>
                )}
              </TabsContent>
              <TabsContent
                value="preview"
                className={`output-panel${expanded ? ' preview-expanded' : ''}`}
                keepMounted
              >
                <div className="pane-meta">
                  <span>
                    <Globe2 aria-hidden="true" /> Program preview
                  </span>
                  <Button
                    ref={previewModeButton}
                    variant="ghost"
                    size="sm"
                    aria-label={
                      expanded ? 'Back to editor' : 'Show preview only'
                    }
                    aria-pressed={expanded}
                    onClick={() => {
                      if (expanded) {
                        exitPreview();
                        return;
                      }
                      setExpanded(true);
                      expandedRef.current = true;
                    }}
                  >
                    {expanded ? (
                      <Minimize2 aria-hidden="true" />
                    ) : (
                      <Maximize2 aria-hidden="true" />
                    )}
                    {expanded ? 'Back to editor' : 'Preview only'}
                  </Button>
                </div>
                {frame ? (
                  <div className="preview-surface">
                    <iframe
                      ref={iframe}
                      title="Ur program output"
                      className="result-frame"
                      sandbox="allow-scripts"
                      srcDoc={frame}
                    />
                  </div>
                ) : (
                  <div className="empty-state">
                    <Play aria-hidden="true" />
                    <h2>Ready when you are.</h2>
                    <p>
                      Compile &amp; run to see your page here. Try the counter
                      example for a live, interactive result.
                    </p>
                  </div>
                )}
              </TabsContent>
              <TabsContent value="diagnostics" className="output-panel">
                <div className="pane-meta">
                  <span>
                    <CircleAlert aria-hidden="true" /> Compiler &amp; runtime
                    diagnostics
                  </span>
                </div>
                {diagnostics ? (
                  <pre className="diagnostic" role="alert">
                    {diagnostics}
                  </pre>
                ) : (
                  <div className="empty-state">
                    <Check aria-hidden="true" />
                    <h2>
                      {result?.ok ? 'No diagnostics.' : 'Nothing to report.'}
                    </h2>
                    <p>
                      {result?.ok
                        ? 'Your program passed the compiler checks.'
                        : 'Type errors and unsupported operations will appear here.'}
                    </p>
                  </div>
                )}
              </TabsContent>
              <TabsContent value="logs" className="output-panel">
                <div className="pane-meta">
                  <span>
                    <Terminal aria-hidden="true" /> Program log
                  </span>
                  <span>{logs.length} messages</span>
                </div>
                {logs.length > 0 ? (
                  <pre className="program-log">{logs.join('\n')}</pre>
                ) : (
                  <div className="empty-state">
                    <Terminal aria-hidden="true" />
                    <h2>No log messages.</h2>
                    <p>Messages from your running program will appear here.</p>
                  </div>
                )}
              </TabsContent>
            </Tabs>
            <output
              className="compiler-status"
              data-state={busy ? 'busy' : diagnostics ? 'error' : 'ready'}
              aria-live="polite"
              inert={expanded}
            >
              <span className="status-dot" aria-hidden="true" />
              {busy
                ? 'Compiling in WebAssembly…'
                : diagnostics
                  ? 'See diagnostics for details'
                  : status}
            </output>
          </section>
        </ResizablePanel>
      </ResizablePanelGroup>
    </main>
  );
}

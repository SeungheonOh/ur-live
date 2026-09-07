import {
  WASI,
  File,
  OpenFile,
  Directory,
  PreopenDirectory,
  ConsoleStdout,
} from './compiler/wasi/index.js';
import { entryModule, projectFiles } from './project.mjs';

const encoder = new TextEncoder(),
  decoder = new TextDecoder();
export const projectSource = '\n$/list\n$/option\nplayground\n';
export const projectSignature = 'val main : unit -> transaction page\n';
export function virtualTree(files) {
  const root = new Map();
  for (const [path, content] of Object.entries(files)) {
    const parts = path.split('/');
    let current = root;
    for (const name of parts.slice(0, -1)) {
      if (!current.has(name)) current.set(name, new Directory(new Map()));
      current = current.get(name).contents;
    }
    current.set(
      parts.at(-1),
      new File(encoder.encode(content), { readonly: true }),
    );
  }
  return root;
}

// One fresh command instance per compilation: no environment, inference state,
// source files, or GHC heap is reused across user programs. The compiled module
// itself may be reused. WASI sees only these memory-backed files, never the host.
export async function compileUr(module, standardFiles, source) {
  const legacy = typeof source === 'string';
  if (legacy && encoder.encode(source).length > 256 * 1024)
    throw new Error('The playground accepts at most 256 KiB of Ur source.');
  const inputs = legacy
    ? {
        'playground.urp': projectSource,
        'playground.ur': source,
        'playground.urs': projectSignature,
      }
    : projectFiles(source);
  const root = virtualTree(standardFiles);
  const output = new File([]);
  const work = virtualTree(inputs);
  work.set('program.mjs', output);
  root.set('work', new Directory(work));
  let stderr = '',
    stdout = '';
  const stderrDecoder = new TextDecoder(),
    stdoutDecoder = new TextDecoder();
  const wasi = new WASI(
    [
      'vr-browser',
      '/vr',
      '/work/playground.urp',
      '/browser-capabilities.txt',
      '/work/program.mjs',
      ...(!legacy ? [entryModule] : []),
    ],
    ['LANG=C.UTF-8', 'LC_ALL=C.UTF-8'],
    [
      new OpenFile(new File([])),
      new ConsoleStdout((data) => {
        stdout += stdoutDecoder.decode(data, { stream: true });
      }),
      new ConsoleStdout((data) => {
        stderr += stderrDecoder.decode(data, { stream: true });
      }),
      new PreopenDirectory('/', root),
    ],
    { debug: false },
  );
  const started = performance.now();
  const instance = await WebAssembly.instantiate(module, {
    wasi_snapshot_preview1: wasi.wasiImport,
  });
  const status = wasi.start(instance);
  stdout += stdoutDecoder.decode();
  stderr += stderrDecoder.decode();
  return {
    ok: status === 0,
    javascript: status === 0 ? decoder.decode(output.data) : '',
    diagnostics: stderr,
    stdout,
    milliseconds: performance.now() - started,
    memoryBytes: instance.exports.memory.buffer.byteLength,
  };
}

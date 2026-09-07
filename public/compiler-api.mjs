import {
  WASI,
  File,
  OpenFile,
  Directory,
  PreopenDirectory,
  ConsoleStdout,
} from './compiler/wasi/index.js';

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
  if (typeof source !== 'string')
    throw new TypeError('Ur source must be a string');
  if (encoder.encode(source).length > 256 * 1024)
    throw new Error('The playground accepts at most 256 KiB of Ur source.');
  const root = virtualTree(standardFiles);
  const output = new File([]);
  root.set(
    'work',
    new Directory(
      new Map([
        [
          'playground.urp',
          new File(encoder.encode(projectSource), { readonly: true }),
        ],
        ['playground.ur', new File(encoder.encode(source), { readonly: true })],
        [
          'playground.urs',
          new File(encoder.encode(projectSignature), { readonly: true }),
        ],
        ['program.mjs', output],
      ]),
    ),
  );
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

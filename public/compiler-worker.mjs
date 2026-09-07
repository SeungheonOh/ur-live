import { compileUr } from './compiler-api.mjs';

let compiler;
let files;
try {
  const [response, fileResponse] = await Promise.all([
    fetch('./compiler/vr.wasm'),
    fetch('./compiler/files.json'),
  ]);
  if (!response.ok || !fileResponse.ok)
    throw new Error(
      'Compiler assets are unavailable. Run npm run build:wasm first.',
    );
  const bytes = await response.arrayBuffer();
  [compiler, files] = await Promise.all([
    WebAssembly.compile(bytes),
    fileResponse.json(),
  ]);
  postMessage({ type: 'ready', bytes: bytes.byteLength });
} catch (error) {
  postMessage({ type: 'failure', message: String(error) });
}

self.onmessage = async ({ data }) => {
  if (data.type !== 'compile') return;
  try {
    if (!compiler || !files) throw new Error('Compiler is not ready');
    postMessage({
      type: 'compiled',
      id: data.id,
      ...(await compileUr(compiler, files, data.source)),
    });
  } catch (error) {
    postMessage({
      type: 'compiled',
      id: data.id,
      ok: false,
      javascript: '',
      diagnostics: String(error),
      milliseconds: 0,
      memoryBytes: 0,
    });
  }
};

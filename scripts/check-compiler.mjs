import assert from 'node:assert/strict';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { pathToFileURL } from 'node:url';
import { compileUr } from '../public/compiler-api.mjs';
import { getRuntime, setHost } from '../public/browser-runtime.mjs';

const wasmModule = await WebAssembly.compile(
  await readFile(new URL('../public/compiler/vr.wasm', import.meta.url)),
);
const files = JSON.parse(
  await readFile(
    new URL('../public/compiler/files.json', import.meta.url),
    'utf8',
  ),
);
const runtime = pathToFileURL(
  new URL('../public/browser-runtime.mjs', import.meta.url).pathname,
).href;
await mkdir(new URL('../.build/checks/', import.meta.url), { recursive: true });
for (const [name, expected] of [
  ['hello', 'The answer is 42.'],
  ['polymorphism', '42, 42, 41'],
  ['trees', 'The tree sums to 42.'],
  ['records', 'Scores total: 42'],
  ['modules', 'A functor produced 42'],
  ['counter', 'Count: '],
  ['strings', 'Characters: 3; bytes: 4.'],
  ['integer-boundaries', 'Wrapped: -9223372036854775808.'],
  ['type-error', null],
  ['no-sql', null],
  ['no-server', null],
  ['hello', 'The answer is 42.'],
]) {
  const source = await readFile(
    new URL(`../examples/${name}.ur`, import.meta.url),
    'utf8',
  );
  const result = await compileUr(wasmModule, files, source);
  await writeFile(
    new URL(`../.build/checks/${name}.json`, import.meta.url),
    JSON.stringify(result, null, 2),
  );
  console.log(
    name,
    result.ok,
    Math.round(result.milliseconds) + ' ms',
    Math.round(result.memoryBytes / 1048576) + ' MiB',
  );
  assert.equal(result.ok, expected !== null, result.diagnostics);
  if (!result.ok) {
    assert.match(result.diagnostics, /type|unif|int|string|not supported/i);
    continue;
  }
  const output = new URL(`../.build/checks/${name}.mjs`, import.meta.url);
  await writeFile(
    output,
    result.javascript.replace(
      "'./browser-runtime.mjs'",
      JSON.stringify(runtime),
    ),
  );
  const program = await import(output.href + '?' + Date.now());
  const patches = [];
  setHost({ patch: (id, html) => patches.push([id, html]) });
  const html = await program.main();
  console.log(html);
  assert(html.includes(expected), html);
  if (name === 'counter') {
    const handler = html.match(/data-vrp-onclick="(\d+)"/)?.[1];
    assert(handler, html);
    await getRuntime().dispatch(Number(handler), {});
    await getRuntime().dispatch(Number(handler), {});
    assert.deepEqual(
      patches.map(([, body]) => body),
      ['1', '2'],
    );
  }
  getRuntime().dispose();
}
console.log(
  'Real Ur programs compiled with WebAssembly and ran as JavaScript.',
);

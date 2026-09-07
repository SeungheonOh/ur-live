import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { resolve } from 'node:path';
import {
  compileUr,
  projectSource,
  projectSignature,
} from '../public/compiler-api.mjs';
import { supportedNames } from '../public/browser-runtime.mjs';

const wasmModule = await WebAssembly.compile(
  await readFile('public/compiler/vr.wasm'),
);
const files = JSON.parse(await readFile('public/compiler/files.json', 'utf8'));
const root = resolve('.build/cross-compile');
await mkdir(root, { recursive: true });
await writeFile(root + '/playground.urp', projectSource);
await writeFile(root + '/playground.urs', projectSignature);
await writeFile(root + '/capabilities.txt', supportedNames.join('\n'));
const results = [];
for (const name of Object.keys(
  JSON.parse(await readFile('public/examples.json', 'utf8')),
)) {
  const source = await readFile('examples/' + name + '.ur', 'utf8');
  await writeFile(root + '/playground.ur', source);
  const wasm = await compileUr(wasmModule, files, source);
  const native = spawnSync(
    resolve('.build/vr-browser-native'),
    [
      resolve('vendor/vr/vendor/urweb'),
      root + '/playground.urp',
      root + '/capabilities.txt',
      root + '/program.mjs',
    ],
    { encoding: 'utf8' },
  );
  assert.equal(
    native.status,
    wasm.ok ? 0 : 1,
    native.stderr + '\n' + wasm.diagnostics,
  );
  if (wasm.ok)
    assert.equal(
      await readFile(root + '/program.mjs', 'utf8'),
      wasm.javascript,
      name,
    );
  else
    assert.equal(
      native.stderr
        .replaceAll(root, '/work')
        .replaceAll(resolve('vendor/vr/vendor/urweb'), '/vr'),
      wasm.diagnostics,
      name,
    );
  results.push({ name, accepted: wasm.ok, identical: true });
  console.log(
    name +
      ': native and wasm ' +
      (wasm.ok ? 'JavaScript' : 'diagnostics') +
      ' identical',
  );
}
await writeFile(root + '/results.json', JSON.stringify(results, null, 2));

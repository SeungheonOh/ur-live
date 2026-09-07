// Real multi-file Ur programs through the actual compiler and JavaScript runtime.
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { dirname, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
import { compileUr } from '../public/compiler-api.mjs';
import {
  projectFiles,
  entryModule,
  validateProject,
} from '../public/project.mjs';
import {
  getRuntime,
  setHost,
  supportedNames,
} from '../public/browser-runtime.mjs';
import { indentationEdit } from '../lib/editor-editing.ts';

const compiler = await WebAssembly.compile(
  await readFile('public/compiler/vr.wasm'),
);
const library = JSON.parse(
  await readFile('public/compiler/files.json', 'utf8'),
);
const projects = JSON.parse(await readFile('public/projects.json', 'utf8'));
const base = projects['multiple-files'];
const runtime = pathToFileURL(resolve('public/browser-runtime.mjs')).href;
const results = [];

async function check(name, project, expected, exercise) {
  const compiled = await compileUr(compiler, library, project);
  assert.equal(
    compiled.ok,
    expected !== null,
    name + ': ' + compiled.diagnostics,
  );
  const root = resolve('.build/project-checks/' + name);
  await mkdir(root, { recursive: true });
  await writeFile(root + '/result.json', JSON.stringify(compiled, null, 2));
  if (process.argv.includes('--native')) {
    for (const [path, source] of Object.entries(projectFiles(project))) {
      await mkdir(dirname(root + '/' + path), { recursive: true });
      await writeFile(root + '/' + path, source);
    }
    await writeFile(root + '/capabilities.txt', supportedNames.join('\n'));
    const native = spawnSync(
      resolve('.build/vr-browser-native'),
      [
        resolve('vendor/vr/vendor/urweb'),
        root + '/playground.urp',
        root + '/capabilities.txt',
        root + '/native.mjs',
        entryModule,
      ],
      { encoding: 'utf8' },
    );
    assert.equal(
      native.status,
      compiled.ok ? 0 : 1,
      name + ': ' + native.stderr,
    );
    if (compiled.ok)
      assert.equal(
        await readFile(root + '/native.mjs', 'utf8'),
        compiled.javascript,
        name,
      );
    else
      assert.equal(
        native.stderr
          .replaceAll(root, '/work')
          .replaceAll(resolve('vendor/vr/vendor/urweb'), '/vr'),
        compiled.diagnostics,
        name,
      );
  }
  if (compiled.ok) {
    const patches = [];
    const errors = [];
    setHost({
      patch: (id, html) => patches.push([id, html]),
      error: (message) => errors.push(message),
    });
    const output = root + '/program.mjs';
    await writeFile(
      output,
      compiled.javascript.replace(
        "'./browser-runtime.mjs'",
        JSON.stringify(runtime),
      ),
    );
    const program = await import(pathToFileURL(output));
    try {
      const html = await program.main();
      assert.match(html, expected, name);
      if (exercise) await exercise(html, patches);
      assert.deepEqual(errors, []);
    } finally {
      getRuntime().dispose();
    }
  }
  results.push({
    name,
    ok: compiled.ok,
    milliseconds: compiled.milliseconds,
    nativeIdentical: process.argv.includes('--native'),
  });
  console.log(
    name +
      ': ' +
      (compiled.ok ? 'compiled and executed' : 'rejected as expected'),
  );
}

await check('modules-and-signature', base, /Math.answer is 42/);
await check('wrong-order', { ...base, order: [...base.order].reverse() }, null);
await check(
  'signature-mismatch',
  {
    ...base,
    files: {
      ...base.files,
      'math.urs': 'val answer : string\nval twice : int -> int\n',
    },
  },
  null,
);
await check(
  'signature-hides-value',
  { ...base, files: { ...base.files, 'math.urs': 'val twice : int -> int\n' } },
  null,
);
await check(
  'wrong-main-type',
  { ...base, files: { ...base.files, 'main.ur': 'val main = 42\n' } },
  null,
);
await check(
  'hidden-main',
  { ...base, files: { ...base.files, 'main.urs': '' } },
  null,
);
await check(
  'missing-main',
  { ...base, files: { ...base.files, 'main.ur': 'val answer = 42\n' } },
  null,
);
const alternate = {
  ...base,
  files: {
    ...base.files,
    'other.ur':
      'fun main () : transaction page = return <xml><body>Other entry</body></xml>\n',
  },
  order: [...base.order, 'other.ur'],
};
await check('select-first-main', alternate, /Math.answer is 42/);
await check(
  'select-second-main',
  { ...alternate, entry: 'other.ur' },
  /Other entry/,
);
await check(
  'nested-file-path',
  {
    files: Object.fromEntries(
      Object.entries(base.files).map(([path, source]) => [
        'lib/' + path,
        source,
      ]),
    ),
    entry: 'lib/main.ur',
    order: base.order.map((path) => 'lib/' + path),
  },
  /Twice seven is 14/,
);
await check(
  'edited-dependency',
  {
    ...base,
    files: {
      ...base.files,
      'math.ur': base.files['math.ur'].replace('twice 21', 'twice 25'),
    },
  },
  /Math.answer is 50/,
);
await check('fresh-project-state', base, /Math.answer is 42/);

const apply = (source, start, end, key, shift = false) => {
  const edit = indentationEdit(source, start, end, key, shift);
  assert(edit, key);
  return {
    text: source.slice(0, edit.from) + edit.text + source.slice(edit.to),
    start: edit.anchor,
    end: edit.head,
  };
};
const source = base.files['main.ur'];
const indented = apply(source, 0, source.length, 'Tab');
const unindented = apply(
  indented.text,
  indented.start,
  indented.end,
  'Tab',
  true,
);
assert.equal(unindented.text, source);
const firstLineEnd = source.indexOf('\n') + 1;
const firstLine = apply(source, 0, firstLineEnd, 'Tab');
assert.equal(firstLine.text, '  ' + source);
const endOfDeclaration = source.indexOf('\n');
const entered = apply(source, endOfDeclaration, endOfDeclaration, 'Enter');
assert.equal(entered.text.slice(endOfDeclaration, entered.start), '\n  ');
assert.equal(
  apply('    return <xml/>', 4, 4, 'Backspace').text,
  '  return <xml/>',
);
assert.equal(apply('<xml></xml>', 5, 5, 'Enter').text, '<xml>\n  \n</xml>');
assert.equal(apply('  <br/>', 7, 7, 'Enter').text, '  <br/>\n  ');
assert.equal(apply('\n' + source, 0, 0, 'Tab').text, '  \n' + source);
await check(
  'indented-program',
  { ...base, files: { ...base.files, 'main.ur': indented.text } },
  /Math.answer is 42/,
);
await check(
  'enter-in-program',
  { ...base, files: { ...base.files, 'main.ur': entered.text } },
  /Math.answer is 42/,
);

for (const path of [
  '../escape.ur',
  '/main.ur',
  'a\\b.ur',
  'bad\nfile.ur',
  'VrBrowserEntry.ur',
  'list.ur',
])
  assert.throws(() =>
    validateProject({ ...base, files: { ...base.files, [path]: '' } }),
  );
assert.throws(
  () => validateProject({ ...base, files: { ...base.files, 'Math.ur': '' } }),
  /Duplicate/,
);
assert.throws(
  () => validateProject({ ...base, order: ['main.ur', 'main.ur'] }),
  /exactly once/,
);
assert.throws(() => validateProject({ ...base, entry: 'missing.ur' }), /entry/);
assert.throws(
  () => validateProject({ ...base, files: { ...base.files, 'extra.urs': '' } }),
  /matching/,
);
assert.throws(
  () =>
    validateProject({
      ...base,
      files: { ...base.files, 'math.ur': ' '.repeat(256 * 1024) },
    }),
  /256 KiB/,
);

await check(
  'three-file-threads',
  projects['demo-threads'],
  /data-vrp-onload/,
  async (html, patches) => {
    const handler = Number(html.match(/data-vrp-onload="(\d+)"/)[1]);
    await getRuntime().dispatch(handler, {});
    await new Promise((resolve) => setTimeout(resolve, 5300));
    const labels = patches.map(([, html]) => html.split('<br>')[0]);
    for (const message of [
      'A: Message #0',
      'B: Message #100',
      'B: Message #101',
      'A: Message #1',
    ])
      assert(labels.includes(message), JSON.stringify(labels));
    assert.equal(
      labels.length,
      new Set(labels).size,
      'No duplicate reactive subscriptions',
    );
  },
);
await writeFile(
  '.build/project-checks/results.json',
  JSON.stringify(results, null, 2),
);

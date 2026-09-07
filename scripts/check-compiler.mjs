import assert from 'node:assert/strict';
import { mkdir, readFile, writeFile } from 'node:fs/promises';
import { pathToFileURL } from 'node:url';
import { compileUr } from '../public/compiler-api.mjs';
import { getRuntime, setHost } from '../public/browser-runtime.mjs';
import { checkInteractions } from './check-interactions.mjs';

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
  ['tic-tac-toe', 'X to move'],
  ['lights-out', 'Lights on: 9'],
  ['task-board', 'To do (1)'],
  ['strings', 'Characters: 3; bytes: 4.'],
  ['integer-boundaries', 'Wrapped: -9223372036854775808.'],
  ['demo-hello', 'Hello world!'],
  ['demo-react', "You didn't click it yet."],
  ['demo-react-controls', "You didn't click it yet."],
  ['demo-sum', '9'],
  ['demo-tc-sum', '9.6'],
  ['demo-list-edit', '>Add</button>'],
  ['demo-threads', 'data-vrp-onload'],
  ['type-error', null],
  ['no-sql', null],
  ['no-server', null],
  ['hello', 'The answer is 42.'],
]) {
  let source = await readFile(
    new URL(
      `../examples/${name === 'demo-react-controls' ? 'demo-react' : name}.ur`,
      import.meta.url,
    ),
    'utf8',
  );
  // Exercise the new two-way binding with real compiled Ur: the official React
  // demo, with two textboxes observing the same existing source.
  if (name === 'demo-react-controls')
    source = source.replace(
      '<dyn signal=',
      '<ctextbox source={s}/><ctextbox source={s}/><dyn signal=',
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
  const controls = [];
  const errors = [];
  setHost({
    patch: (id, html) => patches.push([id, html]),
    control: (id, value) => controls.push([id, value]),
    error: (message) => errors.push(message),
  });
  const html = await program.main();
  console.log(html);
  assert(html.includes(expected), html);
  await checkInteractions(name, html, patches);
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
  if (name === 'demo-react') {
    assert.match(html, />Click me!<\/button>/);
    const handler = Number(html.match(/data-vrp-onclick="(\d+)"/)[1]);
    await getRuntime().dispatch(handler, {});
    assert.deepEqual(
      patches.map(([, body]) => body),
      ['Now you clicked it.'],
    );
  }
  if (name === 'demo-react-controls') {
    const ids = [...html.matchAll(/data-vrp-control="(\d+)"/g)].map((match) =>
      Number(match[1]),
    );
    assert.equal(ids.length, 2);
    await getRuntime().dispatch(ids[0], { value: 'Typed <&>' });
    assert.deepEqual(
      controls,
      [[ids[1], 'Typed <&>']],
      'Update the other binding without echoing a stale input value',
    );
    controls.length = 0;
    await getRuntime().dispatch(
      Number(html.match(/data-vrp-onclick="(\d+)"/)[1]),
      {},
    );
    assert.deepEqual(
      controls,
      ids.map((id) => [id, 'Now you clicked it.']),
      'An Ur set must update both textboxes',
    );
    console.log(
      'ctextbox: shared source, no input echo, programmatic Ur updates.',
    );
  }
  if (name === 'demo-sum' || name === 'demo-tc-sum') {
    const values = html
      .replace(/<[^>]*>/g, ' ')
      .trim()
      .split(/\s+/);
    assert.deepEqual(
      values,
      name === 'demo-sum' ? ['0', '1', '9'] : ['1', '9.6'],
    );
  }
  if (name === 'demo-list-edit') {
    const id = (text, marker) =>
      Number(text.match(new RegExp(marker + '="(\\d+)"'))?.[1]);
    const dispatch = (handler, event = {}) =>
      getRuntime().dispatch(handler, event);
    const update = (slot) => patches.filter(([id]) => id === slot).at(-1)?.[1];
    const input = id(html, 'data-vrp-control');
    const add = id(html, 'data-vrp-onclick');
    const head = id(html, 'data-vrp-slot');
    await dispatch(input, { value: 'Alpha <&> λ' });
    await dispatch(add);
    const first = update(head);
    assert(first, 'Appending a row must update the visible head');
    assert.match(first, /Alpha &lt;&amp;> &#955;/);
    assert.match(first, />Change to:<\/button>/);
    const editFirst = id(first, 'data-vrp-control');
    const changeFirst = id(first, 'data-vrp-onclick');
    const firstLabel = id(first, 'data-vrp-slot');
    const tail = Number(
      [...first.matchAll(/data-vrp-slot="(\d+)"/g)].at(-1)[1],
    );
    await dispatch(editFirst, { value: 'Changed <b>first</b>' });
    await dispatch(changeFirst);
    assert.equal(update(firstLabel), 'Changed &lt;b>first&lt;/b>');
    await dispatch(input, { value: 'Beta' });
    await dispatch(add);
    const second = update(tail);
    assert(second, 'Appending another row must update the existing tail');
    assert.match(second, />Beta<\/span>/);
    await dispatch(id(second, 'data-vrp-control'), { value: 'Second edited' });
    await dispatch(id(second, 'data-vrp-onclick'));
    assert.equal(update(id(second, 'data-vrp-slot')), 'Second edited');
    await dispatch(editFirst, { value: 'First still editable' });
    await dispatch(changeFirst);
    assert.equal(update(firstLabel), 'First still editable');
    assert.deepEqual(
      controls,
      [],
      'Input events must not echo stale values back to their own textboxes',
    );
    console.log(
      'ListEdit: add two rows, edit both, preserve earlier handlers, escape user input.',
    );
  }
  if (name === 'demo-threads') {
    await getRuntime().dispatch(
      Number(html.match(/data-vrp-onload="(\d+)"/)[1]),
      {},
    );
    await new Promise((resolve) => setTimeout(resolve, 5300));
    const messages = patches.map(([, body]) => body).join('\n');
    assert.equal(
      patches.length,
      new Set(patches.map(([, body]) => body.split('<br>')[0])).size,
      'Each buffer append must emit one update, not exponentially duplicated subscriptions',
    );
    for (const message of [
      'A: Message #0',
      'B: Message #100',
      'B: Message #101',
      'A: Message #1',
    ])
      assert(messages.includes(message), 'Missing timed message: ' + message);
    console.log(
      'Threads: both original loops advanced at their 3 s / 5 s intervals.',
    );
  }
  assert.deepEqual(errors, [], 'Unexpected program error');
  getRuntime().dispose();
}
console.log(
  'Real Ur programs compiled with WebAssembly and ran as JavaScript.',
);

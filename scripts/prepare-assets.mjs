import { mkdir, readdir, readFile, writeFile, cp } from 'node:fs/promises';
import { supportedNames } from '../public/browser-runtime.mjs';

const standardRoot = new URL(
  '../vendor/vr/vendor/urweb/lib/ur/',
  import.meta.url,
);
const files = {};
for (const name of (await readdir(standardRoot)).sort()) {
  if (/\.urs?$/.test(name))
    files['vr/lib/ur/' + name] = await readFile(
      new URL(name, standardRoot),
      'utf8',
    );
}
files['browser-capabilities.txt'] = supportedNames.join('\n');
await mkdir(new URL('../public/compiler/', import.meta.url), {
  recursive: true,
});
await writeFile(
  new URL('../public/compiler/files.json', import.meta.url),
  JSON.stringify(files),
);
await cp(
  new URL('../node_modules/@bjorn3/browser_wasi_shim/dist/', import.meta.url),
  new URL('../public/compiler/wasi/', import.meta.url),
  { recursive: true },
);
await cp(
  new URL(
    '../node_modules/@bjorn3/browser_wasi_shim/LICENSE-MIT',
    import.meta.url,
  ),
  new URL('../public/compiler/wasi/LICENSE-MIT', import.meta.url),
);
console.log(`Prepared ${Object.keys(files).length} virtual compiler files.`);
const examples = {};
for (const name of [
  'hello',
  'polymorphism',
  'trees',
  'records',
  'modules',
  'counter',
  'strings',
  'integer-boundaries',
  'demo-hello',
  'demo-react',
  'demo-sum',
  'demo-tc-sum',
  'demo-list-edit',
  'demo-threads',
  'type-error',
  'no-sql',
  'no-server',
])
  examples[name] = await readFile(
    new URL(`../examples/${name}.ur`, import.meta.url),
    'utf8',
  );
await writeFile(
  new URL('../public/examples.json', import.meta.url),
  JSON.stringify(examples),
);
const projects = {
  'multiple-files': {
    files: {},
    entry: 'main.ur',
    order: ['math.ur', 'main.ur'],
  },
  'demo-threads': {
    files: {},
    entry: 'threads.ur',
    order: ['buffer.ur', 'threads.ur'],
  },
};
for (const name of ['math.ur', 'math.urs', 'main.ur'])
  projects['multiple-files'].files[name] = await readFile(
    new URL(`../examples/projects/modules/${name}`, import.meta.url),
    'utf8',
  );
for (const name of ['buffer.ur', 'buffer.urs', 'threads.ur'])
  projects['demo-threads'].files[name] =
    '(* From the Ur/Web demo collection; BSD license: /licenses/UrWeb-demos.txt. *)\n' +
    (await readFile(
      new URL(`../vendor/urweb-demos/${name}`, import.meta.url),
      'utf8',
    ));
await writeFile(
  new URL('../public/projects.json', import.meta.url),
  JSON.stringify(projects),
);
const notices = new URL('../public/licenses/', import.meta.url);
await mkdir(notices, { recursive: true });
await cp(
  new URL('../vendor/vr/LICENSE', import.meta.url),
  new URL('Vr.txt', notices),
);
await cp(
  new URL('../vendor/vr/vendor/urweb/LICENSE', import.meta.url),
  new URL('UrWeb.txt', notices),
);
const ghcDocs = new URL('../.wasm-toolchain/lib/doc/', import.meta.url);
await cp(
  new URL('../vendor/urweb-demos/LICENSE', import.meta.url),
  new URL('UrWeb-demos.txt', notices),
);
for (const compiler of await readdir(ghcDocs)) {
  if (!compiler.startsWith('wasm32-wasi-ghc-')) continue;
  const libraries = new URL(compiler + '/', ghcDocs);
  for (const library of await readdir(libraries)) {
    try {
      await cp(
        new URL(library + '/LICENSE', libraries),
        new URL('GHC-' + library + '.txt', notices),
      );
    } catch (error) {
      if (error.code !== 'ENOENT') throw error;
    }
  }
}

# Vr playground

The **real Haskell Vr compiler, compiled to WebAssembly**, running locally in
the browser. Ur programs become ordinary JavaScript functions, closures,
records, and tagged datatypes. There is no compile endpoint or server runtime.

The compiler is pinned to Vr commit `d8a9a8d` and vendored in this directory.
The original `/home/sho/fun/Vr` checkout is not a build dependency and is not
modified by this project. See [VENDORED.md](VENDORED.md).

## Run

The built playground is served at <http://127.0.0.1:63208/> on this machine.
To reproduce it from source, use Node 22.13+ and Nix:

```sh
npm ci
npm run build:wasm
npm run build
npm start
```

`build:wasm` installs a pinned GHC WebAssembly toolchain through Nix on its first
run; this is a substantial toolchain download. Later builds reuse it. The build
creates `public/compiler/vr.wasm`, the virtual standard-library files, and the
browser WASI shim. `npm run build` exports the site to **`dist/client`**; any
ordinary static HTTP host can serve that directory. `npm start` is only a local
static-file server: it rejects POST and performs no compilation or execution.

For interface development after building the compiler, use `npm run dev`.
Do not run the development server and static server on the same port together.
The final browser needs JavaScript modules, BigInt, WebAssembly, and Web Workers.

## Use

Select an example, edit its Ur source, and choose **Compile & run**, or press
Ctrl/Command+Enter. The JavaScript panel contains actual output from the Wasm
compiler, not a hand-written approximation. Its small `browser-runtime.mjs`
dependency is a browser-only library, not Node or the Vr server runtime.

Each program is a single Ur compilation unit, with this checked interface:

```ur
val main : unit -> transaction page
```

For example:

```ur
fun identity [a] (x : a) : a = x

fun main () : transaction page =
    return <xml><body>
      <p>The answer is {[identity 42]}.</p>
    </body></xml>
```

The generated module exports `main()` (returns rendered HTML) and
`mount(element)` (renders and attaches browser behavior). The playground runs
it in a second worker and displays HTML in a sandboxed iframe. Its event bridge
keeps Ur execution out of the editor's main thread, including event handlers.
**Stop program** terminates that worker. Starting a new program resets its state.

## Supported scope

- Vr's real parsing, elaboration, type checking, constraint/instance resolution,
  module/functor processing, specialization, and monomorphic lowering.
- Polymorphism, records, lists/options, recursive datatypes, pattern matching,
  higher-order functions, and inline structures/signatures/functors.
- Vendored Basis and Top, plus automatically included `List` and `Option`.
- Signed 64-bit integer operations using BigInt, supported float/string/character
  primitives, ordinary XML/HTML, and local `source`/`get`/`set`/`signal` behavior.
- The examples include a real reactive counter, Unicode byte operations,
  integer boundaries, a functor, and intentional rejected programs.

This is a **browser subset**, not full Ur/Web application hosting. The target
rejects SQL/schema declarations, cookies, RPC, server channels, native FFI,
server tasks, and unsupported Basis operations. It has no filesystem API for
Ur programs, external project-file editor, HTTP routing, or forms that submit
to server actions. Active XML blocks, dynamic class/style attributes, advanced
controls, and time APIs are not yet supported. Browser HTML is mounted inside
an existing document, so outer `html`/`body` elements become local containers.

The complete frontend remains intact; backend restrictions are separate from
type checking. This does not assert full behavioral equivalence for every
Ur/Web primitive or every possible program. Diagnostics retain the original
compiler text, which sometimes includes internal type representations.

## Execution boundaries

1. The compiler worker loads the Wasm module and pinned library sources once.
2. Every compilation gets a **fresh Wasm instance and memory-only filesystem**.
   The compiler cannot read files from the user's computer. Library and input
   files are read-only; the generated JavaScript file is writable.
3. The same native Vr pipeline produces Mono. A small browser adapter validates
   capabilities and reuses Vr's existing JavaScript expression emitter.
4. A separate, replaceable execution worker runs the generated module. The
   display iframe has an opaque origin and a network-blocking content policy.
   Only the trusted rendering/event bridge executes in that iframe.

The playground caps source at 256 KiB, compiler GHC heap at 768 MiB, Wasm linear
memory at 1 GiB, and compilation at 30 seconds. Initial program execution and
event handlers have a 10-second watchdog. These are local playground limits,
not claims of identical native Ur/Web resource accounting. Standalone exports
used outside the playground do not inherit its worker/watchdog boundaries.

## Verification

```sh
npm run check:compiler
npx tsc --noEmit
npm run build
```

`check:compiler` feeds real `.ur` files through WebAssembly using the same WASI
shim as the browser, then executes the generated JavaScript. It checks output,
counter updates, deliberate type/backend errors, and successful compilation
after a failure. No synthetic AST fixtures are used.

For a cross-target comparison, build the same adapter with native GHC 9.10:

```sh
mkdir -p .build/native
ghc --make compiler/Main.hs -icompiler -ivendor/vr/src -XGHC2021 -O1 -j4 \
  -odir .build/native -hidir .build/native -stubdir .build/native \
  -o .build/vr-browser-native
node scripts/check-cross-compile.mjs
```

All eleven included programs produced byte-identical JavaScript or identical
diagnostics between native GHC and Wasm GHC, normalizing filesystem roots in
diagnostics only. Separately, **Chromium 152** compiled actual Ur programs in a
browser worker and ran their output in another browser worker, including
counter updates `0 → 1 → 2`, Unicode, integer limits, failures, and recovery.
This is worker integration testing, not screenshot/DOM/UI interaction testing.
Browser results are retained in `.build/checks/browser-workers.json`.

To repeat the browser-worker check, open this playground in a local Chromium
instance with remote debugging enabled, then supply its loopback endpoint:

```sh
node scripts/check-browser-workers.mjs http://127.0.0.1:9222
```

The page optionally registers `compile_ur` when `document.modelContext` exists.
That WebMCP integration is progressive enhancement; it was not verified in a
WebMCP-enabled browser and is not required for manual compilation.

## Build references

- [GHC WebAssembly backend](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/wasm.html)
- [Pinned ghc-wasm-meta toolchain](https://github.com/haskell-wasm/ghc-wasm-meta/tree/fc630f0c3c3577cce0c21ae20d810c0981fe1cb2)
- [Browser WASI shim](https://github.com/bjorn3/browser_wasi_shim)

GHC is `9.10.3.20260731`; the browser shim is pinned to `0.4.2`. The toolchain
uses GHC's GMP flavour. Keep the upstream compiler/library licenses and their
source/relinking requirements in mind when redistributing a compiled bundle.
The local build copies available license notices into `public/licenses`.

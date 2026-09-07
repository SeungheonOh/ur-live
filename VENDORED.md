# Compiler source provenance

`vendor/vr` is an archive of these paths from Vr commit
`d8a9a8d` (`Rename Yr to Vr and optimize native allocation and compilation`):

- `src`
- `vendor/urweb/lib/ur`
- `vendor/urweb/LICENSE`
- `LICENSE`

The committed original compiler lives separately at `/home/sho/fun/Vr`.
This playground does not symlink or mutate its sources or build output.

The **only change to vendored Haskell source** is the export list in
`Vr.Backend.ClientJavaScript`: the browser adapter can call the existing Mono
expression emitter and its context/reachability helpers. No emitter body or
frontend/type-checking implementation was changed.

`compiler/Browser.hs` is a new target adapter. `compiler/Main.hs` invokes the
actual Vr pipeline. `compiler/Paths_vr.hs` provides the otherwise Cabal-generated
data-path helper for this direct GHC build; the entry point passes explicit
virtual filesystem paths.

`public/browser-runtime.mjs` is a separate browser-only implementation of the
supported runtime subset, using Vr's value conventions. In particular, it does
not load, polyfill, or emulate the Node/C server runtime. The new application
source is under the Vr BSD-3-Clause license in `LICENSE`; upstream Ur/Web and
toolchain components retain their respective licenses.

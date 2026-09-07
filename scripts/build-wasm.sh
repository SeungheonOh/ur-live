#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ ! -x .wasm-toolchain/bin/wasm32-wasi-ghc ]]; then
  nix --extra-experimental-features 'nix-command flakes' build \
    github:haskell-wasm/ghc-wasm-meta/fc630f0c3c3577cce0c21ae20d810c0981fe1cb2#all_9_10 \
    --out-link .wasm-toolchain
fi
mkdir -p .build/wasm public/compiler
.wasm-toolchain/bin/wasm32-wasi-ghc --make compiler/Main.hs \
  -icompiler -ivendor/vr/src -XGHC2021 -O1 -j4 \
  -odir .build/wasm -hidir .build/wasm -stubdir .build/wasm \
  -rtsopts -with-rtsopts='-A8m -M768m -K64m' \
  -optl-Wl,--max-memory=1073741824 \
  -o public/compiler/vr.wasm
node scripts/prepare-assets.mjs

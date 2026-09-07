# Official Ur/Web demo sources

Copied from https://github.com/urweb/urweb/tree/55a881ff9b50d9e5c3b2fd564f5cd44a5cc5e6bc/demo.
The upstream commit is `55a881ff9b50d9e5c3b2fd564f5cd44a5cc5e6bc`.
These are the examples linked from http://www.impredicative.com/ur/demo/.
The original source files and upstream BSD license are retained here; only
trailing blank lines are normalized by the source import.

Runnable copies live in `../../examples/demo-*.ur`. They add an attribution
comment. Threads also inlines `buffer.ur` behind its original `buffer.urs`
signature, since the playground edits a single compilation unit.

No SQL/RPC demo has been relabeled as browser-only or silently emulated.

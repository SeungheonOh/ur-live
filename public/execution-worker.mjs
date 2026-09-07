import { getRuntime, setHost } from './browser-runtime.mjs';

setHost({
  patch: (id, html) => postMessage({ type: 'patch', slot: id, html }),
  control: (id, value) => postMessage({ type: 'control', control: id, value }),
  log: (message) => postMessage({ type: 'log', message }),
  error: (message) => postMessage({ type: 'error', message }),
});
let program;
let queue = Promise.resolve();
self.onmessage = ({ data }) => {
  queue = queue
    .then(async () => {
      if (data.type === 'run') {
        if (program) throw new Error('Create a fresh worker for each program');
        const runtime = new URL('./browser-runtime.mjs', import.meta.url).href;
        const source = data.javascript.replace(
          "'./browser-runtime.mjs'",
          JSON.stringify(runtime),
        );
        const url = URL.createObjectURL(
          new Blob([source], { type: 'text/javascript' }),
        );
        try {
          program = await import(url);
          postMessage({ type: 'result', html: await program.main() });
        } finally {
          URL.revokeObjectURL(url);
        }
      } else if (data.type === 'event') {
        await getRuntime().dispatch(data.handler, data.event);
        postMessage({ type: 'event-complete', id: data.id });
      }
    })
    .catch((error) => postMessage({ type: 'error', message: String(error) }));
};

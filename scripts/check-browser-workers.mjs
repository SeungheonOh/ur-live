// Compiler/execution-worker integration in a real browser. This deliberately
// does not inspect the page DOM, take screenshots, or simulate UI clicks.
import assert from 'node:assert/strict';
import { mkdir, writeFile } from 'node:fs/promises';

const endpoint = process.argv[2];
assert(
  endpoint,
  'Provide the local Chromium debugging endpoint, e.g. http://127.0.0.1:9222',
);
const pages = await (await fetch(endpoint + '/json/list')).json();
const page = pages.find(
  (value) =>
    value.type === 'page' && value.url.startsWith('http://127.0.0.1:63208/'),
);
assert(page, 'Open the local playground in that browser first');
const socket = new WebSocket(page.webSocketDebuggerUrl);
await new Promise((resolve, reject) => {
  socket.addEventListener('open', resolve, { once: true });
  socket.addEventListener('error', reject, { once: true });
});
let next = 0;
const pending = new Map();
socket.addEventListener('message', ({ data }) => {
  const message = JSON.parse(data);
  if (message.id) {
    const action = pending.get(message.id);
    pending.delete(message.id);
    if (message.error) action.reject(new Error(message.error.message));
    else action.resolve(message.result);
  }
});
const call = (method, params) =>
  new Promise((resolve, reject) => {
    const id = ++next;
    pending.set(id, { resolve, reject });
    socket.send(JSON.stringify({ id, method, params }));
  });
const deadline = setTimeout(() => {
  console.error('Browser worker check exceeded 45 seconds');
  process.exit(1);
}, 45_000);
try {
  const result = await call('Runtime.evaluate', {
    awaitPromise: true,
    returnByValue: true,
    expression: `(async()=>{
    const examples=await(await fetch('/examples.json')).json();
    const projects=await(await fetch('/projects.json')).json();
    const compiler=new Worker('/compiler-worker.mjs',{type:'module'});
    const receive=(worker,kind)=>new Promise((resolve,reject)=>{
      const handler=({data})=>{if(data.type==='failure'||data.type==='error'){worker.removeEventListener('message',handler);reject(new Error(data.message));}else if(data.type===kind){worker.removeEventListener('message',handler);resolve(data);}};
      worker.addEventListener('message',handler);worker.addEventListener('error',event=>reject(new Error(event.message)),{once:true});
    });
    const ready=await receive(compiler,'ready');
    const results=[];
    try{
      for(const name of ['hello','modules','multiple-files','counter','strings','integer-boundaries','demo-hello','demo-react','demo-sum','demo-tc-sum','demo-list-edit','demo-threads','type-error','no-sql','no-server','hello']){
        const response=receive(compiler,'compiled');compiler.postMessage({type:'compile',id:name,source:projects[name]??{files:{'playground.ur':examples[name]},entry:'playground.ur',order:['playground.ur']}});
        const compiled=await response;
        const entry={name,ok:compiled.ok,diagnostics:compiled.diagnostics,milliseconds:compiled.milliseconds};results.push(entry);
        if(!compiled.ok)continue;
        const execution=new Worker('/execution-worker.mjs',{type:'module'});
        try{
          const output=receive(execution,'result');execution.postMessage({type:'run',javascript:compiled.javascript});entry.html=(await output).html;
          const updates=[];execution.addEventListener('message',({data})=>{if(data.type==='patch')updates.push(data);});
          const event=async(handler,event={})=>{const done=receive(execution,'event-complete');execution.postMessage({type:'event',id:crypto.randomUUID(),handler,event});await done;};
          const marker=(html,name)=>Number(html.match(new RegExp(name+'="(\\\\d+)"'))[1]);
          if(name==='demo-react'){
            await event(marker(entry.html,'data-vrp-onclick'));entry.patches=updates.map(value=>value.html);
          }
          if(name==='demo-list-edit'){
            await event(marker(entry.html,'data-vrp-control'),{value:'Browser row <&>'});
            await event(marker(entry.html,'data-vrp-onclick'));
            const row=updates.filter(value=>value.slot===marker(entry.html,'data-vrp-slot')).at(-1).html;
            await event(marker(row,'data-vrp-control'),{value:'Edited in the browser'});
            await event(marker(row,'data-vrp-onclick'));
            entry.added=row;entry.edited=updates.filter(value=>value.slot===marker(row,'data-vrp-slot')).at(-1).html;
          }
          if(name==='demo-threads'){
            await event(marker(entry.html,'data-vrp-onload'));
            await new Promise(resolve=>setTimeout(resolve,5300));entry.messages=updates.map(value=>value.html).join('\\n');entry.messageLabels=updates.map(value=>value.html.split('<br>')[0]);
          }
          if(name==='counter'){
            const handler=Number(entry.html.match(/data-vrp-onclick="(\\d+)"/)[1]);entry.patches=[];
            for(let id=1;id<=2;id++){
              const patch=receive(execution,'patch'),complete=receive(execution,'event-complete');
              execution.postMessage({type:'event',id,handler,event:{}});
              entry.patches.push((await patch).html);await complete;
            }
          }
        }finally{execution.terminate();}
      }
      return {wasmBytes:ready.bytes,results,userAgent:navigator.userAgent};
    }finally{compiler.terminate();}
  })()`,
  });
  assert.equal(
    result.exceptionDetails,
    undefined,
    JSON.stringify(result.exceptionDetails),
  );
  const value = result.result.value;
  assert(value.wasmBytes > 1_000_000);
  for (const entry of value.results) {
    const expected = !['type-error', 'no-sql', 'no-server'].includes(
      entry.name,
    );
    assert.equal(entry.ok, expected, entry.name + ': ' + entry.diagnostics);
    if (entry.name === 'hello') assert.match(entry.html, /answer is 42/);
    if (entry.name === 'modules')
      assert.match(entry.html, /functor produced 42/);
    if (entry.name === 'multiple-files')
      assert.match(entry.html, /Math.answer is 42/);
    if (entry.name === 'counter') assert.deepEqual(entry.patches, ['1', '2']);
    if (entry.name === 'strings')
      assert.match(entry.html, /Characters: 3; bytes: 4/);
    if (entry.name === 'integer-boundaries')
      assert.match(entry.html, /-9223372036854775808/);
    if (entry.name === 'demo-hello') assert.match(entry.html, /Hello world!/);
    if (entry.name === 'demo-react')
      assert.deepEqual(entry.patches, ['Now you clicked it.']);
    if (entry.name === 'demo-sum' || entry.name === 'demo-tc-sum')
      assert.deepEqual(
        entry.html
          .replace(/<[^>]*>/g, ' ')
          .trim()
          .split(/\s+/),
        entry.name === 'demo-sum' ? ['0', '1', '9'] : ['1', '9.6'],
      );
    if (entry.name === 'demo-list-edit') {
      assert.match(entry.added, /Browser row &lt;&amp;>/);
      assert.equal(entry.edited, 'Edited in the browser');
    }
    if (entry.name === 'demo-threads') {
      assert.equal(
        entry.messageLabels.length,
        new Set(entry.messageLabels).size,
        'No duplicated reactive subscriptions',
      );
      for (const message of [
        'A: Message #0',
        'B: Message #100',
        'B: Message #101',
        'A: Message #1',
      ])
        assert(entry.messages.includes(message), message);
    }
  }
  await mkdir(new URL('../.build/checks/', import.meta.url), {
    recursive: true,
  });
  await writeFile(
    new URL('../.build/checks/browser-workers.json', import.meta.url),
    JSON.stringify(value, null, 2),
  );
  console.log(JSON.stringify(value, null, 2));
} finally {
  clearTimeout(deadline);
  socket.close();
}

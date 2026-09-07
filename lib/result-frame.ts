// User HTML lives in an opaque-origin, network-blocked iframe. Ur evaluation
// stays in a terminable worker; this tiny trusted bridge only renders results
// and forwards a fixed set of browser events. No user script runs in this frame.
export function resultFrame(channel: string, nonce: string) {
  return `<!doctype html><html><head><meta charset="utf-8">
<meta http-equiv="Content-Security-Policy" content="default-src 'none'; script-src 'nonce-${nonce}'; style-src 'unsafe-inline'; img-src data:; connect-src 'none'; base-uri 'none'; form-action 'none'">
<style>body{font:16px/1.6 system-ui,sans-serif;color:#20252c;margin:16px}button,input,select{font:inherit}button{padding:3px 12px;cursor:pointer}h1{font-size:24px}pre{white-space:pre-wrap}</style></head><body>
<main id="result"></main><script nonce="${nonce}">
const channel=${JSON.stringify(channel)},root=document.getElementById('result');
const send=data=>parent.postMessage({channel,...data},'*');
addEventListener('message',({source,data})=>{
  if(source!==parent||data.channel!==channel)return;
  if(data.type==='result'){root.innerHTML=data.html;for(const node of root.querySelectorAll('[data-vrp-onload]'))send({type:'event',handler:Number(node.dataset.vrpOnload),event:{}});}
  if(data.type==='patch'){const node=root.querySelector('[data-vrp-slot="'+Number(data.slot)+'"]');if(node)node.innerHTML=data.html;}
});
for(const kind of ['click','dblclick','contextmenu','mousedown','mouseup','mousemove','mouseenter','mouseleave','keydown','keyup','keypress','change','input','focus','blur']){
  document.addEventListener(kind,event=>{
    const node=event.target.closest?.('[data-vrp-on'+kind+']');if(!node)return;
    if(kind==='click'||kind==='contextmenu')event.preventDefault();
    send({type:'event',handler:Number(node.getAttribute('data-vrp-on'+kind)),event:{
      altKey:event.altKey,ctrlKey:event.ctrlKey,metaKey:event.metaKey,shiftKey:event.shiftKey,
      clientX:event.clientX,clientY:event.clientY,button:event.button,keyCode:event.keyCode,repeat:event.repeat
    }});
  },true);
}
send({type:'frame-ready'});
</script></body></html>`;
}

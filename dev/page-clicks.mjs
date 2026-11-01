// Opens URL in headless Chrome, clicks its buttons by index, in order, and
// prints the text of the page's first <p> before and after each click,
// separated by " | ". Uses the DevTools protocol, with Node's own fetch and
// WebSocket (Node 22 or later). Chrome: $CHROME, or macOS's.
//
// usage: node dev/page-clicks.mjs URL 0,0,0,1
import { spawn } from 'node:child_process';
const [url, plan] = process.argv.slice(2);
const chrome = spawn(process.env.CHROME || '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
  ['--headless=new', '--disable-gpu', '--remote-debugging-port=9333', '--user-data-dir=' + (process.env.TMPDIR || '/tmp') + '/soma-page-clicks', '--allow-file-access-from-files', url],
  { stdio: 'ignore' });
const sleep = ms => new Promise(r => setTimeout(r, ms));
let ws;
for (let i = 0; i < 50 && !ws; i++) {
  await sleep(200);
  try {
    const pages = await (await fetch('http://127.0.0.1:9333/json')).json();
    const page = pages.find(p => p.type === 'page');
    if (page) ws = new WebSocket(page.webSocketDebuggerUrl);
  } catch {}
}
await new Promise(r => ws.addEventListener('open', r));
let id = 0; const waiting = new Map();
ws.addEventListener('message', e => { const m = JSON.parse(e.data); if (waiting.has(m.id)) { waiting.get(m.id)(m.result); waiting.delete(m.id); } });
const evaluate = expression => new Promise(r => { const n = ++id; waiting.set(n, r); ws.send(JSON.stringify({ id: n, method: 'Runtime.evaluate', params: { expression, returnByValue: true } })); }).then(r => r.result.value);
await sleep(1000);
const read = () => evaluate("(document.querySelector('p') || {}).textContent");
const seen = [await read()];
for (const b of plan.split(',').filter(x => x !== '')) {
  await evaluate(`document.querySelectorAll('button')[${b}].click()`);
  await sleep(150);
  seen.push(await read());
}
console.log(seen.join(' | '));
ws.close(); chrome.kill();

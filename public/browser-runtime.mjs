// Browser-only support for Vr's ordinary JavaScript expressions. No networking,
// Node imports, native addons, SQL, filesystem, or server transaction machinery.
const tags = new Set(
  'html head title body br span div p strong em b i tt sub sup h1 h2 h3 h4 h5 h6 li ol ul hr pre section article nav aside footer header main meter progress output details figure figcaption data mark rp rt ruby summary time wbr bdi a img button ctextbox label fieldset legend tabl tr th td thead tbody tfoot dl dt dd dyn active'.split(
    ' ',
  ),
);
const arities = {
  cdata: 1,
  htmlifyString: 1,
  htmlifyInt: 1,
  htmlifyFloat: 1,
  htmlifyBool: 1,
  intToString: 1,
  floatToString: 1,
  boolToString: 1,
  charToString: 1,
  str1: 1,
  attrifyString: 1,
  attrifyInt: 1,
  attrifyFloat: 1,
  attrifyBool: 1,
  strlen: 1,
  strlenUtf8: 1,
  strlenGe: 2,
  strcat: 2,
  strsub: 2,
  strsubUtf8: 2,
  strsuffix: 2,
  strsuffixUtf8: 2,
  substring: 3,
  strindex: 2,
  strsindex: 2,
  strchr: 2,
  strcspn: 2,
  stringToInt: 1,
  stringToInt_error: 1,
  stringToFloat: 1,
  stringToFloat_error: 1,
  stringToBool: 1,
  stringToBool_error: 1,
  stringToChar: 1,
  stringToChar_error: 1,
  ord: 1,
  chr: 1,
  floatFromInt: 1,
  ceil: 1,
  floor: 1,
  trunc: 1,
  round: 1,
  pow: 2,
  sqrt: 1,
  sin: 1,
  cos: 1,
  log: 1,
  exp: 1,
  asin: 1,
  acos: 1,
  atan: 1,
  atan2: 2,
  abs: 1,
  islower: 1,
  isupper: 1,
  isalpha: 1,
  isdigit: 1,
  isalnum: 1,
  isblank: 1,
  isspace: 1,
  isxdigit: 1,
  isprint: 1,
  tolower: 1,
  toupper: 1,
  new_client_source: 1,
  get_client_source: 1,
  set_client_source: 2,
  atom: 1,
  property: 1,
  css_url: 1,
  blessData: 1,
};
export const supportedNames = [...tags]
  .filter((name) => name !== 'active')
  .concat(Object.keys(arities), [
    'tag',
    'join',
    'return',
    'bind',
    'source',
    'get',
    'set',
    'signal',
    'debug',
    'naughtyDebug',
    'fresh',
    'not',
    'neg',
    'show_string',
    'show_int',
    'show_float',
    'show_bool',
    'show_char',
    'eq_int',
    'eq_float',
    'eq_string',
    'eq_bool',
    'eq_char',
    'lt_int',
    'lt_float',
    'lt_string',
    'lt_char',
    'le_int',
    'le_float',
    'le_string',
    'le_char',
    'plus',
    'minus',
    'times',
    'div',
    'mod',
  ]);

let host = {};
let latestRuntime;
export function setHost(value) {
  host = value;
}
export function getRuntime() {
  return latestRuntime;
}

// Vr's server runtime uses Ur/Web's six-significant-digit float formatting.
function formatFloat(value) {
  if (Number.isNaN(value)) return 'nan';
  if (value === Infinity) return 'inf';
  if (value === -Infinity) return '-inf';
  if (Object.is(value, -0)) return '-0';
  if (value === 0) return '0';
  const trim = (s) =>
    s.includes('.') ? s.replace(/0+$/, '').replace(/\.$/, '') : s;
  const exponent = Math.floor(Math.log10(Math.abs(value)));
  if (exponent < -4 || exponent >= 6) {
    const [mantissa, power] = value.toExponential(5).split('e'),
      n = Number(power);
    return `${trim(mantissa)}e${n < 0 ? '-' : '+'}${String(Math.abs(n)).padStart(2, '0')}`;
  }
  return trim(value.toFixed(Math.max(0, 5 - exponent)));
}

export function createRuntime() {
  const td = new TextDecoder();
  const encoder = new TextEncoder();
  const text = (x) =>
    x == null ? '' : x.__vrHtml === true ? x.value : String(x);
  const html = (x) => ({ __vrHtml: true, value: text(x) });
  const escape = (x) =>
    text(x)
      .replaceAll('&', '&amp;')
      .replaceAll('<', '&lt;')
      .replaceAll('>', '&gt;')
      .replaceAll('"', '&quot;')
      .replaceAll("'", '&#39;');
  const htmlify = (x) =>
    [...text(x)]
      .map((c) => {
        const n = c.codePointAt(0);
        return n >= 32 && n <= 126
          ? c === '&'
            ? '&amp;'
            : c === '<'
              ? '&lt;'
              : c
          : `&#${n};`;
      })
      .join('');
  const option = (x) =>
    x === null ? { tag: 0, payload: null } : { tag: 1, payload: x };
  const app = (f, x) => {
    if (typeof f !== 'function')
      throw new TypeError('Invalid Ur function application');
    return f(x);
  };
  const run = async (x) => await (typeof x === 'function' ? x({}) : x);
  const int64 = (n) => BigInt.asIntN(64, n);
  const equal = (a, b) =>
    a === b ||
    !!(
      a &&
      b &&
      typeof a === 'object' &&
      typeof b === 'object' &&
      Object.keys(a).length === Object.keys(b).length &&
      Object.keys(a).every((k) => Object.hasOwn(b, k) && equal(a[k], b[k]))
    );
  const binary = (op, a, b) => {
    const numeric = (x) =>
      typeof a === 'bigint' && typeof b === 'bigint' ? int64(x) : x;
    switch (op) {
      case '=':
      case '==':
      case 'eq':
        return equal(a, b);
      case '<>':
      case '!=':
      case 'neq':
        return !equal(a, b);
      case '!strcmp':
        return text(a) === text(b);
      case 'strcmp':
        return BigInt(text(a) < text(b) ? -1 : text(a) > text(b) ? 1 : 0);
      case '<':
      case 'lt':
        return a < b;
      case '<=':
      case 'le':
        return a <= b;
      case '>':
      case 'gt':
        return a > b;
      case '>=':
      case 'ge':
        return a >= b;
      case '+':
      case 'plus':
        return numeric(a + b);
      case '-':
      case 'minus':
        return numeric(a - b);
      case '*':
      case 'times':
        return numeric(a * b);
      case '/':
      case 'div':
        if (b === 0n) throw new Error('Division by zero');
        return numeric(a / b);
      case '%':
      case 'mod':
        if (b === 0n) throw new Error('Division by zero');
        return numeric(a % b);
      case '&&':
      case 'and':
        return a && b;
      case '||':
      case 'or':
        return a || b;
      case 'powl':
      case 'powf':
      case 'pow':
        return numeric(a ** b);
      default:
        throw new Error(`Unsupported operator ${op}`);
    }
  };
  const unary = (op, x) => {
    // Mono lowers negated equality (including string <>) to "!".
    if (op === 'not' || op === '!') return !x;
    if (op === '-' || op === 'neg')
      return typeof x === 'bigint' ? int64(-x) : -x;
    throw new Error(`Unsupported unary operator ${op}`);
  };
  const source = (value) => ({ value, listeners: new Set() });
  const publish = (s, value) => {
    s.value = value;
    // Subscription callbacks may remove/re-add themselves; iterate a snapshot.
    // eslint-disable-next-line unicorn/no-useless-spread
    for (const notify of [...s.listeners]) notify();
  };
  const signalReturn = (value) => ({
    read: () => value,
    subscribe: () => () => {},
  });
  const signalSource = (s) => ({
    read: () => s.value,
    subscribe: (notify) => {
      s.listeners.add(notify);
      return () => s.listeners.delete(notify);
    },
  });
  const signalBind = (s, k) => {
    let initialized = false,
      previous,
      selected;
    // Reading and subscribing must share the same continuation result. XML
    // construction registers nested dyns/controls; evaluating k twice creates
    // invisible duplicate subscriptions (exponential growth in Buffer's tail).
    // Ur values are immutable, so an unchanged outer value can reuse its inner
    // signal, which still observes its own independent source dependencies.
    const current = () => {
      const value = s.read();
      if (!initialized || !Object.is(previous, value)) {
        const next = app(k, value);
        previous = value;
        selected = next;
        initialized = true;
      }
      return selected;
    };
    return {
      read: () => current().read(),
      subscribe: (notify) => {
        let innerSignal = current();
        let inner = innerSignal.subscribe(notify);
        const outer = s.subscribe(() => {
          const next = current();
          if (next !== innerSignal) {
            inner();
            innerSignal = next;
            inner = innerSignal.subscribe(notify);
          }
          notify();
        });
        return () => {
          outer();
          inner();
        };
      },
    };
  };
  const events = new Map();
  const dynamics = new Map();
  const controls = new Map();
  const cleanups = [];
  const timers = new Set();
  let mountedRoot;
  let inputOrigin;
  let disposed = false;
  let nextId = 0;
  const eventValue = (e) => ({
    AltKey: !!e.altKey,
    CtrlKey: !!e.ctrlKey,
    MetaKey: !!e.metaKey,
    ShiftKey: !!e.shiftKey,
    Button: { tag: { 0: 0, 1: 2, 2: 1 }[e.button] ?? 0, payload: null },
    ClientX: BigInt(e.clientX ?? 0),
    ClientY: BigInt(e.clientY ?? 0),
    KeyCode: BigInt(e.keyCode ?? 0),
    Repeat: !!e.repeat,
  });
  const attribute = (name, value) =>
    value == null || value === false
      ? ''
      : ` ${name}="${escape(value === true ? '' : value)}"`;
  const makeTag = (
    classes,
    dynamicClass,
    style,
    dynamicStyle,
    attributes,
    descriptor,
    child,
  ) => {
    if (dynamicClass?.tag === 1 || dynamicStyle?.tag === 1)
      throw new Error('Dynamic class/style is not supported yet');
    const tag = descriptor.name;
    if (tag === 'dyn') {
      const signal = attributes.Signal,
        id = ++nextId;
      dynamics.set(id, signal);
      cleanups.push(
        signal.subscribe(() => {
          const body = text(signal.read());
          host.patch?.(id, body);
          const node = mountedRoot?.querySelector(`[data-vrp-slot="${id}"]`);
          if (node) node.innerHTML = body;
        }),
      );
      return html(`<span data-vrp-slot="${id}">${text(signal.read())}</span>`);
    }
    if (tag === 'active')
      throw new Error('Active XML blocks are not supported yet');
    let attrs =
      attribute('class', classes || null) + attribute('style', style || null);
    if (tag === 'ctextbox') {
      attrs += attribute('type', 'text');
      if (attributes.Source) {
        const s = attributes.Source,
          id = ++nextId;
        controls.set(id, s);
        attrs +=
          attribute('data-vrp-control', id) + attribute('value', s.value);
        const draw = () => {
          const value = text(s.value);
          // Echoing an input event through the worker could overwrite a newer
          // keystroke. Other bindings and later programmatic sets still update.
          if (id !== inputOrigin) host.control?.(id, value);
          const node = mountedRoot?.querySelector(`[data-vrp-control="${id}"]`);
          if (node && node.value !== value) node.value = value;
        };
        s.listeners.add(draw);
        cleanups.push(() => s.listeners.delete(draw));
      }
    }
    for (const [name, value] of Object.entries(attributes)) {
      if (tag === 'button' && name === 'Value') continue;
      if (
        tag === 'ctextbox' &&
        (name === 'Source' || (name === 'Value' && attributes.Source))
      )
        continue;
      if (name.startsWith('On')) {
        const id = ++nextId,
          kind = name.slice(2).toLowerCase();
        events.set(id, {
          kind,
          value,
          takesEvent: ![
            'load',
            'unload',
            'resize',
            'scroll',
            'focus',
            'blur',
            'hashchange',
            'input',
            'change',
          ].includes(kind),
        });
        attrs += attribute(`data-vrp-on${kind}`, id);
      } else if (name === 'Data') {
        for (const [key, item] of Object.entries(value ?? {}))
          attrs += attribute('data-' + key, item);
      } else attrs += attribute(name.toLowerCase(), value);
    }
    // A standalone page is mounted inside an existing document body.
    const name =
      tag === 'body' || tag === 'html'
        ? 'div'
        : tag === 'tabl'
          ? 'table'
          : tag === 'ctextbox'
            ? 'input'
            : tag;
    // Ur/Web uses a button's Value attribute as its visible, escaped label.
    const content =
      (tag === 'button' && attributes.Value !== undefined
        ? htmlify(attributes.Value)
        : '') + text(child);
    return html(
      `<${name}${attrs}>${['br', 'hr', 'img', 'wbr', 'input'].includes(name) ? '' : `${content}</${name}>`}`,
    );
  };
  const curry =
    (arity, f, args = []) =>
    (value) =>
      args.length + 1 === arity
        ? f(...args, value)
        : curry(arity, f, [...args, value]);
  const parseIntUr = (value) => {
    const s = text(value);
    if (!/^[\t\n\v\f\r ]*[+-]?[0-9]+$/.test(s)) return null;
    const n = BigInt(s),
      lo = -(1n << 63n),
      hi = (1n << 63n) - 1n;
    return n < lo ? lo : n > hi ? hi : n;
  };
  const codepoints = (value) => [...text(value)];
  const slice = (value, index, length) => {
    const s = codepoints(value),
      i = Number(index),
      n = length === undefined ? s.length - i : Number(length);
    if (
      !Number.isSafeInteger(i) ||
      !Number.isSafeInteger(n) ||
      i < 0 ||
      n < 0 ||
      i > s.length ||
      n > s.length - i
    )
      throw new Error('Substring out of bounds');
    return s.slice(i, i + n).join('');
  };
  const call = (name, args) => {
    const x = args[0],
      y = args[1];
    if (name === 'decodeBytes')
      return td.decode(
        Uint8Array.from(text(x).match(/../g) || [], (b) => parseInt(b, 16)),
      );
    if (name === 'strcat') return text(x) + text(y);
    if (name === 'cdata' || name === 'htmlifyString')
      return x?.__vrHtml ? x : html(htmlify(x));
    if (name === 'htmlifyInt') return html(text(x));
    if (name === 'htmlifyFloat') return html(formatFloat(Number(x)));
    if (name === 'htmlifyBool') return html(x ? 'True' : 'False');
    if (['intToString', 'show_string'].includes(name)) return text(x);
    if (name === 'floatToString') return formatFloat(Number(x));
    if (name === 'boolToString') return x ? 'True' : 'False';
    if (['charToString', 'str1'].includes(name))
      return String.fromCodePoint(Number(x));
    if (name.startsWith('attrify'))
      return escape(
        name === 'attrifyBool'
          ? x
            ? 'True'
            : 'False'
          : name === 'attrifyFloat'
            ? formatFloat(Number(x))
            : x,
      );
    if (name === 'strlen') return BigInt(codepoints(x).length);
    if (name === 'strlenUtf8') return BigInt(encoder.encode(text(x)).length);
    if (name === 'strlenGe') return BigInt(codepoints(x).length) >= y;
    if (name === 'substring') return slice(x, y, args[2]);
    if (name === 'strsuffix' || name === 'strsuffixUtf8') {
      if (y < 0n) throw new Error('Negative string suffix bound');
      return name === 'strsuffix'
        ? codepoints(x).slice(Number(y)).join('')
        : td.decode(encoder.encode(text(x)).subarray(Number(y)));
    }
    if (name === 'strsub') return slice(x, y, 1).codePointAt(0);
    if (name === 'strsubUtf8') {
      const bytes = encoder.encode(text(x));
      if (y < 0n || y >= BigInt(bytes.length))
        throw new Error('String byte index out of bounds');
      return bytes[Number(y)];
    }
    if (name === 'strindex' || name === 'strchr') {
      const s = codepoints(x),
        i = s.indexOf(String.fromCodePoint(Number(y)));
      return option(
        i < 0 ? null : name === 'strchr' ? s.slice(i).join('') : BigInt(i),
      );
    }
    if (name === 'strsindex') {
      const i = text(x).indexOf(text(y));
      return option(
        i < 0 ? null : BigInt(codepoints(text(x).slice(0, i)).length),
      );
    }
    if (name === 'strcspn') {
      const s = codepoints(x),
        bad = new Set(codepoints(y)),
        i = s.findIndex((c) => bad.has(c));
      return BigInt(i < 0 ? s.length : i);
    }
    if (name.startsWith('stringTo')) {
      let value = null;
      if (name.startsWith('stringToInt')) value = parseIntUr(x);
      else if (name.startsWith('stringToBool'))
        value = text(x) === 'True' ? true : text(x) === 'False' ? false : null;
      else if (name.startsWith('stringToChar'))
        value = codepoints(x).length === 1 ? text(x).codePointAt(0) : null;
      else if (name.startsWith('stringToFloat')) {
        const s = text(x);
        if (
          /^[\t\n\v\f\r ]*[+-]?(?:(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?|inf(?:inity)?|nan)$/i.test(
            s,
          )
        )
          value = /^[\t\n\v\f\r ]*[+-]?inf/i.test(s)
            ? /-/.test(s)
              ? -Infinity
              : Infinity
            : Number(s);
      }
      if (name.endsWith('_error')) {
        if (value === null)
          throw new Error(
            `Invalid ${name.replace('stringTo', '').replace('_error', '')} string`,
          );
        return value;
      }
      return option(value);
    }
    if (name === 'ord') return BigInt(x);
    if (name === 'chr') {
      if (x < 0n || x > 0x10ffffn)
        throw new Error('Invalid character codepoint');
      return Number(x);
    }
    if (name === 'floatFromInt') return Number(x);
    if (name === 'round')
      return BigInt(x < 0 ? Math.ceil(x - 0.5) : Math.floor(x + 0.5));
    if (['ceil', 'floor', 'trunc'].includes(name))
      return BigInt(Math[name](Number(x)));
    if (
      [
        'pow',
        'sqrt',
        'sin',
        'cos',
        'log',
        'exp',
        'asin',
        'acos',
        'atan',
        'atan2',
        'abs',
      ].includes(name)
    )
      return Math[name](...args.map(Number));
    const patterns = {
      islower: /^\p{Lowercase_Letter}$/u,
      isupper: /^\p{Uppercase_Letter}$/u,
      isalpha: /^\p{Alphabetic}$/u,
      isdigit: /^[0-9]$/,
      isalnum: /^[\p{Alphabetic}\p{Decimal_Number}]$/u,
      isblank: /^(?:\t|\p{Zs})$/u,
      isspace: /^\p{White_Space}$/u,
      isxdigit: /^[A-Fa-f0-9]$/,
      isprint: /^(?:[\p{L}\p{M}\p{N}\p{P}\p{S}]|\p{Zs})$/u,
    };
    if (patterns[name])
      return patterns[name].test(String.fromCodePoint(Number(x)));
    if (name === 'tolower' || name === 'toupper')
      return String.fromCodePoint(Number(x))
        [name === 'tolower' ? 'toLowerCase' : 'toUpperCase']()
        .codePointAt(0);
    if (name === 'new_client_source') return source(x);
    if (name === 'get_client_source') return x.value;
    if (name === 'set_client_source') {
      publish(x, y);
      return {};
    }
    if (name === 'blessData') {
      if (!/^[A-Za-z0-9_-]*$/.test(text(x)))
        throw new Error('Invalid data attribute');
      return x;
    }
    if (name === 'atom' || name === 'css_url' || name === 'property') {
      const pattern =
        name === 'property'
          ? /^[a-z_][a-z0-9_-]*$/
          : name === 'atom'
            ? /^[A-Za-z0-9+.#%-]*$/
            : /^[A-Za-z0-9:/._+%?&=#-]*$/;
      if (!pattern.test(text(x))) throw new Error(`Invalid CSS ${name}`);
      return x;
    }
    throw new Error(`Unsupported browser Basis.${name}`);
  };
  const basis = (name) => {
    if (tags.has(name)) return () => ({ name });
    if (name === 'tag') return curry(7, makeTag);
    if (name === 'join') return (a) => (b) => html(text(a) + text(b));
    if (name === 'return') return (value) => () => value;
    if (name === 'bind')
      return (action) => (continuation) => async () =>
        run(app(continuation, await run(action)));
    if (name === 'source') return (value) => () => source(value);
    if (name === 'get') return (s) => () => s.value;
    if (name === 'set')
      return (s) => (value) => () => {
        publish(s, value);
        return {};
      };
    if (name === 'signal') return signalSource;
    if (name === 'fresh') return () => `vrp-${++nextId}`;
    if (name === 'debug' || name === 'naughtyDebug')
      return (value) => () => {
        host.log?.(text(value));
        return {};
      };
    if (name === 'not' || name === 'neg') return (x) => unary(name, x);
    if (name.startsWith('show_'))
      return (value) =>
        call(
          {
            show_int: 'intToString',
            show_float: 'floatToString',
            show_bool: 'boolToString',
            show_char: 'charToString',
            show_string: 'show_string',
          }[name],
          [value],
        );
    if (/^(eq|lt|le)_/.test(name))
      return (a) => (b) => binary(name.split('_')[0], a, b);
    if (['plus', 'minus', 'times', 'div', 'mod'].includes(name))
      return (a) => (b) => binary(name, a, b);
    if (Object.hasOwn(arities, name))
      return curry(arities[name], (...args) => call(name, args));
    throw new Error(`Unsupported browser Basis.${name}`);
  };
  const dispatch = async (id, event = {}) => {
    const control = controls.get(Number(id));
    if (control) {
      if (typeof event.value !== 'string')
        throw new Error('Expected a textbox string');
      const previousOrigin = inputOrigin;
      inputOrigin = Number(id);
      try {
        publish(control, event.value);
      } finally {
        inputOrigin = previousOrigin;
      }
      return {};
    }
    const handler = events.get(Number(id));
    if (!handler) throw new Error('Unknown browser event handler');
    return run(
      handler.takesEvent
        ? app(handler.value, eventValue(event))
        : handler.value,
    );
  };
  const mount = (root) => {
    mountedRoot = root;
    // Delegation also covers controls/handlers inserted by later dyn updates.
    for (const kind of [
      'click',
      'dblclick',
      'contextmenu',
      'mousedown',
      'mouseup',
      'mousemove',
      'mouseenter',
      'mouseleave',
      'keydown',
      'keyup',
      'keypress',
      'change',
      'input',
      'focus',
      'blur',
    ]) {
      const listener = async (event) => {
        try {
          if (kind === 'input' || kind === 'change') {
            const control = event.target.closest?.('[data-vrp-control]');
            if (control)
              await dispatch(control.dataset.vrpControl, {
                value: control.value,
              });
          }
          const node = event.target.closest?.(`[data-vrp-on${kind}]`);
          if (node) {
            if (kind === 'click' || kind === 'contextmenu')
              event.preventDefault();
            await dispatch(node.getAttribute(`data-vrp-on${kind}`), event);
          }
        } catch (error) {
          host.error?.(String(error));
        }
      };
      root.addEventListener(kind, listener, true);
      cleanups.push(() => root.removeEventListener(kind, listener, true));
    }
    for (const node of root.querySelectorAll('[data-vrp-onload]'))
      void dispatch(node.dataset.vrpOnload, {}).catch((error) =>
        host.error?.(String(error)),
      );
  };
  latestRuntime = {
    app,
    basis,
    binary,
    call,
    equal,
    unary,
    html,
    text,
    force: (x) => x,
    concat: (a, b) =>
      a?.__vrHtml || b?.__vrHtml ? html(text(a) + text(b)) : text(a) + text(b),
    run,
    source,
    get: (s) => () => s.value,
    set: (s, x) => () => publish(s, x),
    signalReturn,
    signalSource,
    signalBind,
    closure: (f, c) => (x) => app(c.reduce(app, f), x),
    cut: (r, keys) =>
      Object.fromEntries(
        Object.entries(r).filter(([key]) => !keys.includes(key)),
      ),
    letValue: (x, k) => (x && typeof x.then === 'function' ? x.then(k) : k(x)),
    sequence: (a, k) => async () => {
      await run(a);
      return run(k());
    },
    sleep: (ms) => () =>
      new Promise((resolve) => {
        if (disposed) return;
        const timer = setTimeout(() => {
          timers.delete(timer);
          if (!disposed) resolve({});
        }, Number(ms));
        timers.add(timer);
      }),
    spawn: (action) => () => {
      run(action).catch((error) => host.error?.(String(error)));
      return {};
    },
    fail: (message) => {
      throw new Error(text(message));
    },
    matchFailure: () => {
      throw new Error('Non-exhaustive Ur pattern match');
    },
    dispatch,
    mount,
    dispose: () => {
      disposed = true;
      for (const timer of timers) clearTimeout(timer);
      timers.clear();
      for (const cleanup of cleanups) cleanup();
      events.clear();
      dynamics.clear();
      controls.clear();
      mountedRoot = undefined;
    },
  };
  return latestRuntime;
}

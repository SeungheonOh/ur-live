/** @typedef {{files: Record<string, string>, entry: string, order: string[]}} BrowserProject */

export const entryModule = 'VrBrowserEntry';
const encoder = new TextEncoder();

export function moduleName(path) {
  const name = path
    .split('/')
    .at(-1)
    .replace(/\.urs?$/, '');
  return name[0].toUpperCase() + name.slice(1);
}

export function validateFilename(path) {
  if (
    typeof path !== 'string' ||
    path.length > 180 ||
    !/^(?:[A-Za-z][A-Za-z0-9_]*\/)*[A-Za-z][A-Za-z0-9_]*\.urs?$/.test(path)
  )
    throw new Error(
      'Use an Ur filename such as main.ur, math.urs, or lib/math.ur (letters, numbers, and underscores).',
    );
  if (
    ['Basis', 'Top', 'List', 'Option', entryModule].includes(moduleName(path))
  )
    throw new Error(
      `${moduleName(path)} is reserved by the playground. Choose another module name.`,
    );
}

/** Validate a snapshot, without changing source text or guessing dependencies. */
export function validateProject(project) {
  if (
    !project ||
    typeof project !== 'object' ||
    !project.files ||
    typeof project.files !== 'object' ||
    Array.isArray(project.files)
  )
    throw new Error(
      'Expected a project containing files, an entry file, and a module order.',
    );
  const entries = Object.entries(project.files);
  if (!entries.length || entries.length > 64)
    throw new Error('A project must contain between 1 and 64 files.');
  let bytes = 0;
  const modules = new Set();
  for (const [path, source] of entries) {
    validateFilename(path);
    if (typeof source !== 'string')
      throw new Error(`${path}: expected source text.`);
    bytes += encoder.encode(source).length;
    if (path.endsWith('.ur')) {
      const name = moduleName(path);
      if (modules.has(name))
        throw new Error(
          `Duplicate Ur module ${name}. Directory names do not namespace modules.`,
        );
      modules.add(name);
    } else if (!Object.hasOwn(project.files, path.slice(0, -1))) {
      throw new Error(`${path}: add its matching .ur implementation.`);
    }
  }
  if (bytes > 256 * 1024)
    throw new Error(
      'The playground accepts at most 256 KiB of Ur source across all files.',
    );
  if (
    typeof project.entry !== 'string' ||
    !project.entry.endsWith('.ur') ||
    !Object.hasOwn(project.files, project.entry)
  )
    throw new Error('Choose an existing .ur file as the entry module.');
  if (
    !Array.isArray(project.order) ||
    project.order.length !== modules.size ||
    new Set(project.order).size !== modules.size ||
    project.order.some(
      (path) =>
        typeof path !== 'string' ||
        !path.endsWith('.ur') ||
        !Object.hasOwn(project.files, path),
    )
  )
    throw new Error(
      'The build order must list every .ur implementation exactly once.',
    );
  return project;
}

/** @returns {BrowserProject} */
export function singleFileProject(source) {
  return {
    files: { 'playground.ur': source },
    entry: 'playground.ur',
    order: ['playground.ur'],
  };
}

export function projectFiles(project) {
  validateProject(project);
  return {
    ...project.files,
    'playground.urp':
      '\n$/list\n$/option\n' +
      project.order.map((path) => path.slice(0, -3)).join('\n') +
      `\n${entryModule}\n`,
    [`${entryModule}.ur`]: `val main = ${moduleName(project.entry)}.main\n`,
    [`${entryModule}.urs`]: 'val main : unit -> transaction page\n',
  };
}

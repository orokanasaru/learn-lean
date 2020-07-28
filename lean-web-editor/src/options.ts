import { LeanJsOpts } from '@bryangingechen/lean-client-js-browser';

// const hostPrefix = process.env.COMMUNITY ? 'https://cdn.jsdelivr.net/gh/bryangingechen/lean-web-editor-dist/' : './';
// const hostPrefix = process.env.COMMUNITY ? 'https://tqft.net/lean/web-editor/' : './';
const hostPrefix = process.env.COMMUNITY
  ? 'https://bryangingechen.github.io/lean/lean-web-editor/'
  : './';

export const leanJsOpts: LeanJsOpts = {
  javascript: hostPrefix + 'lean_js_js.js',
  libraryZip: hostPrefix + 'library.zip',
  libraryMeta: hostPrefix + 'library.info.json',
  libraryOleanMap: hostPrefix + 'library.olean_map.json',
  libraryKey: 'library',
  webassemblyJs: hostPrefix + 'lean_js_wasm.js',
  webassemblyWasm: hostPrefix + 'lean_js_wasm.wasm',
  dbName: 'leanlibrary',
};

export let info = null;

fetch(leanJsOpts.libraryMeta)
  .then((res) => res.json())
  .then((j) => (info = j));

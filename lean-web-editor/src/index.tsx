import { LeanJsOpts } from '@bryangingechen/lean-client-js-browser';
import { editor } from 'monaco-editor';
import React from 'react';
import { render } from 'react-dom';
import { App } from './app';
import { registerLeanLanguage } from './langservice';

export async function leanColorize(text: string): Promise<string> {
  const colorized = await editor.colorize(text, 'lean', {});
  return colorized.replace(/&nbsp;/g, ' ');
}

export interface Position {
  line: number;
  column: number;
}

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

// tslint:disable-next-line:no-var-requires
(window as any).require(['vs/editor/editor.main'], () => {
  registerLeanLanguage(leanJsOpts);
  render(<App />, document.getElementById('root'));
});

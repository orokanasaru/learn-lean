import { editor, Uri } from 'monaco-editor';
import React from 'react';
import { HashParams, paramsToString, parseHash } from './hash-params';
import { LeanEditor } from './lean-editor';

export const defaultValue = `-- Live ${
  (self as any).WebAssembly ? 'WebAssembly' : 'JavaScript'
} version of Lean
#eval let v := lean.version in let s := lean.special_version_desc in string.join
["Lean (version ", v.1.repr, ".", v.2.1.repr, ".", v.2.2.repr, ", ",
if s ≠ "" then s ++ ", " else s, "commit ", (lean.githash.to_list.take 12).as_string, ")"]

example (m n : ℕ) : m + n = n + m :=
by simp [nat.add_comm]`;

export interface AppProps {
  showFilePicker?: boolean;
  editUrlHash?: boolean;
  initialValue?: string;
  onValueChange?: (
    edits: editor.IModelContentChangedEvent,
    value: string,
  ) => void;
  getEditHandler?: (
    cb: (edit: editor.IIdentifiedSingleEditOperation) => void,
  ) => void;
}

export function App(appProps: AppProps = {}) {
  const initUrl: URL = new URL(window.location.href);
  const params: HashParams = parseHash(initUrl.hash);

  function changeUrl(newValue: string, key: string) {
    params[key] = newValue;
    // if we just loaded a url, wipe out the code param
    if (key === 'url' || !newValue) {
      params.code = null;
    }
    history.replaceState(undefined, undefined, paramsToString(params));
  }

  function clearUrlParam() {
    params.url = null;
    history.replaceState(undefined, undefined, paramsToString(params));
  }

  const fn = Uri.file('test.lean').fsPath;

  if (window.localStorage.getItem('underline') === 'true') {
    const style = document.createElement('style');
    style.type = 'text/css';
    style.id = 'hideUnderline';
    style.appendChild(
      document.createTextNode(`.monaco-editor .greensquiggly,
    .monaco-editor .redsquiggly { background-size:0px; }`),
    );
    document.head.appendChild(style);
  }

  if (window.localStorage.getItem('docs') === 'true') {
    const style = document.createElement('style');
    style.type = 'text/css';
    style.id = 'hideDocs';
    style.appendChild(
      document.createTextNode(`.toggleDoc, .doc-header { display:none; }`),
    );
    document.head.appendChild(style);
  }

  return (
    <LeanEditor
      file={fn}
      initialValue={params.code || appProps.initialValue || defaultValue}
      onValueChange={(changes, newValue) => {
        console.log(changes);
        if (appProps.editUrlHash ?? true) {
          changeUrl(newValue, 'code');
        }

        if (appProps.onValueChange) {
          appProps.onValueChange(changes, newValue);
        }
      }}
      initialUrl={params.url}
      onUrlChange={(newValue) =>
        (appProps.editUrlHash ?? true) && changeUrl(newValue, 'url')
      }
      clearUrlParam={clearUrlParam}
      getEditHandler={appProps.getEditHandler}
    />
  );
}

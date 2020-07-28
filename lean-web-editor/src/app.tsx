import { Uri } from 'monaco-editor';
import React from 'react';
import { HashParams, paramsToString, parseHash } from './hash-params';
import { LeanEditor } from './lean-editor';

export function App() {
  const initUrl: URL = new URL(window.location.href);
  const params: HashParams = parseHash(initUrl.hash);

  function changeUrl(newValue, key) {
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
      initialValue={params.code}
      onValueChange={(newValue) => changeUrl(newValue, 'code')}
      initialUrl={params.url}
      onUrlChange={(newValue) => changeUrl(newValue, 'url')}
      clearUrlParam={clearUrlParam}
    />
  );
}

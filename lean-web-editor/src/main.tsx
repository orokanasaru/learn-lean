import React from 'react';
import { render } from 'react-dom';
import { App } from './app';
import { registerLeanLanguage } from './langservice';
import { leanJsOpts } from './options';

// tslint:disable-next-line:no-var-requires
(window as any).require(['vs/editor/editor.main'], () => {
  registerLeanLanguage(leanJsOpts);
  render(<App />, document.getElementById('root'));
});

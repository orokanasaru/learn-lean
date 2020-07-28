import { IDisposable } from 'monaco-editor';
import React from 'react';
import { currentlyRunning } from './langservice';
import { Modal } from './modal';
import { UrlForm } from './url-form';

interface PageHeaderProps {
  file: string;
  url: string;
  onSubmit: (value: string) => void;
  status: string;
  onSave: () => void;
  onLoad: (localFile: string, lastFileName: string) => void;
  clearUrlParam: () => void;
  onChecked: () => void;
}

interface PageHeaderState {
  currentlyRunning: boolean;
}

export class PageHeader extends React.Component<
  PageHeaderProps,
  PageHeaderState
> {
  private subscriptions: IDisposable[] = [];

  constructor(props: PageHeaderProps) {
    super(props);
    this.state = { currentlyRunning: true };
    this.onFile = this.onFile.bind(this);
    // this.restart = this.restart.bind(this);
  }

  componentWillMount() {
    this.updateRunning(this.props);
    this.subscriptions.push(
      currentlyRunning.updated.on((fns) => this.updateRunning(this.props)),
    );
  }

  componentWillUnmount() {
    for (const s of this.subscriptions) {
      s.dispose();
    }
    this.subscriptions = [];
  }

  componentWillReceiveProps(nextProps) {
    this.updateRunning(nextProps);
  }

  updateRunning(nextProps) {
    this.setState({
      currentlyRunning: currentlyRunning.value.indexOf(nextProps.file) !== -1,
    });
  }

  onFile(e) {
    const reader = new FileReader();
    const file = e.target.files[0];
    reader.readAsText(file);
    reader.onload = () => this.props.onLoad(reader.result as string, file.name);
    this.props.clearUrlParam();
  }

  // This doesn't work! /test.lean not found after restarting
  // restart() {
  //   // server.restart();
  //   registerLeanLanguage(leanJsOpts);
  // }

  render() {
    const isRunning = this.state.currentlyRunning ? 'busy...' : 'ready!';
    const runColor = this.state.currentlyRunning ? 'orange' : 'lightgreen';

    // TODO: add input for delayMs
    // checkbox for console spam
    // server.logMessagesToConsole = true;
    return (
      <div className='wrap-collapsible'>
        <input
          id='collapsible'
          className='toggle'
          type='checkbox'
          defaultChecked={true}
          onChange={this.props.onChecked}
        />
        <label
          style={{ background: runColor }}
          htmlFor='collapsible'
          className='lbl-toggle'
          tabIndex={0}
        >
          Lean is {isRunning}
        </label>
        <div className='collapsible-content'>
          <div className='leanheader'>
            <a href='https://leanprover.github.io'>
              <img
                className='logo'
                src='./lean_logo.svg'
                style={{
                  height: '5em',
                  margin: '1ex',
                  paddingLeft: '1em',
                  paddingRight: '1em',
                }}
              />
            </a>
            <div className='headerForms'>
              <UrlForm
                url={this.props.url}
                onSubmit={this.props.onSubmit}
                clearUrlParam={this.props.clearUrlParam}
              />
              <div
                style={{
                  // @ts-ignore
                  cssFloat: 'right',
                  margin: '1em',
                }}
              >
                <button onClick={this.props.onSave}>Save</button>
                {/* <button onClick={this.restart}>Restart server:<br/>will redownload<br/>library.zip!</button> */}
              </div>
              <label className='logo' htmlFor='lean_upload'>
                Load .lean from disk:&nbsp;
              </label>
              <input
                id='lean_upload'
                type='file'
                accept='.lean'
                onChange={this.onFile}
              />
              <div className='leanlink'>
                <Modal />
                &nbsp;
                <span className='logo'>Live in-browser version of the </span>
                <a href='https://leanprover.github.io/'>Lean theorem prover</a>
                <span className='logo'>.</span>
              </div>
              {this.props.status && (
                <span style={{ color: 'red' }}>
                  Could not fetch (error: {this.props.status})!&nbsp;
                  {this.props.status.startsWith('TypeError') && (
                    <span>
                      If you see{' '}
                      <a href='https://developer.mozilla.org/en-US/docs/Web/HTTP/CORS'>
                        cross-origin (CORS) errors
                      </a>{' '}
                      in your browser's dev console, try{' '}
                      <a href='https://cors-anywhere.herokuapp.com/'>
                        a CORS proxy
                      </a>
                      , e.g. prepend https://cors-anywhere.herokuapp.com/ to the
                      beginning of your URL.
                    </span>
                  )}
                </span>
              )}
            </div>
          </div>
        </div>
      </div>
    );
  }
}

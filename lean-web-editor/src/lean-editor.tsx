import { editor, KeyCode, Uri } from 'monaco-editor';
import React from 'react';
import { findDOMNode } from 'react-dom';
import SplitPane from 'react-split-pane';
import { InfoView } from './info-view';
import {
  checkInputCompletionChange,
  checkInputCompletionPosition,
  tabHandler,
} from './langservice';
import { PageHeader } from './page-header';
import { Position } from './position';

interface LeanEditorProps {
  file: string;
  initialValue: string;
  onValueChange?: (
    edits: editor.IModelContentChangedEvent,
    value: string,
  ) => void;
  initialUrl: string;
  onUrlChange?: (value: string) => void;
  clearUrlParam: () => void;
  getEditHandler?: (
    cb: (edit: editor.IIdentifiedSingleEditOperation) => void,
  ) => void;
  showFilePicker?: boolean;
}

interface LeanEditorState {
  cursor?: Position;
  split: 'vertical' | 'horizontal';
  url: string;
  status: string;
  size: number;
  checked: boolean;
  lastFileName: string;
}

export class LeanEditor extends React.Component<
  LeanEditorProps,
  LeanEditorState
> {
  model: editor.IModel;
  editor: editor.IStandaloneCodeEditor;

  constructor(props: LeanEditorProps) {
    super(props);
    this.state = {
      split: 'vertical',
      url: this.props.initialUrl,
      status: null,
      size: null,
      checked: true,
      lastFileName: this.props.file,
    };
    this.model = editor.createModel(
      this.props.initialValue,
      'lean',
      Uri.file(this.props.file),
    );
    this.model.updateOptions({ tabSize: 2 });
    this.model.onDidChangeContent((e) => {
      checkInputCompletionChange(e, this.editor, this.model);
      const val = this.model.getValue();
      // do not change code URL param unless user has actually typed
      // (this makes the #url=... param a little more "sticky")
      return (
        (!e.isFlush || !val) &&
        this.props.onValueChange &&
        this.props.onValueChange(e, val)
      );
    });

    this.updateDimensions = this.updateDimensions.bind(this);
    this.dragFinished = this.dragFinished.bind(this);
    this.onSubmit = this.onSubmit.bind(this);
    this.onSave = this.onSave.bind(this);
    this.onLoad = this.onLoad.bind(this);
    this.onChecked = this.onChecked.bind(this);

    if (this.props.getEditHandler) {
      this.props.getEditHandler((edit) =>
        this.editor.executeEdits('sync', [edit]),
      );
    }
  }

  componentDidMount() {
    /* TODO: factor this out */
    const ta = document.createElement('div');
    ta.style.fontSize = '1px';
    ta.style.lineHeight = '1';
    ta.innerHTML = 'a';
    document.body.appendChild(ta);
    const minimumFontSize = ta.clientHeight;
    ta.remove();
    const node = findDOMNode(this.refs.monaco) as HTMLElement;
    const options: editor.IStandaloneEditorConstructionOptions = {
      selectOnLineNumbers: true,
      roundedSelection: false,
      readOnly: false,
      theme: 'vs-dark',
      cursorStyle: 'line',
      automaticLayout: true,
      cursorBlinking: 'solid',
      model: this.model,
      minimap: { enabled: false },
      wordWrap: 'on',
      scrollBeyondLastLine: false,
      fontSize: minimumFontSize > 1 ? minimumFontSize : null,
    };
    this.editor = editor.create(node, options);
    const canTranslate = this.editor.createContextKey('canTranslate', false);
    this.editor.onDidChangeCursorPosition((e) => {
      canTranslate.set(
        checkInputCompletionPosition(e, this.editor, this.model),
      );
      this.setState({
        cursor: { line: e.position.lineNumber, column: e.position.column - 1 },
      });
    });

    this.editor.addCommand(
      KeyCode.Tab,
      () => {
        tabHandler(this.editor, this.model);
      },
      'canTranslate',
    );

    this.determineSplit();
    window.addEventListener('resize', this.updateDimensions);
  }

  componentWillUnmount() {
    this.editor.dispose();
    this.editor = undefined;
    window.removeEventListener('resize', this.updateDimensions);
  }

  componentDidUpdate() {
    // if state url is not null, fetch, then set state url to null again
    if (this.state.url) {
      fetch(this.state.url)
        .then((s) => s.text())
        .then((s) => {
          this.model.setValue(s);
          this.setState({ status: null });
        })
        .catch((e) => this.setState({ status: e.toString() }));
      this.setState({ url: null });
    }
  }

  updateDimensions() {
    this.determineSplit();
  }

  determineSplit() {
    const node = findDOMNode(this.refs.root) as HTMLElement;
    this.setState({
      split:
        node.clientHeight > 0.8 * node.clientWidth ? 'horizontal' : 'vertical',
    });
    // can we reset the pane "size" when split changes?
  }

  dragFinished(newSize) {
    this.setState({ size: newSize });
  }

  onSubmit(value) {
    const lastFileName = value
      .split('#')
      .shift()
      .split('?')
      .shift()
      .split('/')
      .pop();
    this.props.onUrlChange(value);
    this.setState({ url: value, lastFileName });
  }

  onSave() {
    const file = new Blob([this.model.getValue()], { type: 'text/plain' });
    const a = document.createElement('a');
    const url = URL.createObjectURL(file);
    a.href = url;
    a.download = this.state.lastFileName;
    document.body.appendChild(a);
    a.click();
    setTimeout(() => {
      document.body.removeChild(a);
      window.URL.revokeObjectURL(url);
    }, 0);
  }
  onLoad(fileStr, lastFileName) {
    this.model.setValue(fileStr);
    this.props.clearUrlParam();
    this.setState({ lastFileName });
  }

  onChecked() {
    this.setState({ checked: !this.state.checked });
  }

  render() {
    const infoStyle = {
      height:
        this.state.size && this.state.split === 'horizontal'
          ? `calc(95vh - ${this.state.checked ? 115 : 0}px - ${
              this.state.size
            }px)`
          : this.state.split === 'horizontal'
          ? // crude hack to set initial height if horizontal
            `calc(35vh - ${this.state.checked ? 45 : 0}px)`
          : '100%',
      width:
        this.state.size && this.state.split === 'vertical'
          ? `calc(98vw - ${this.state.size}px)`
          : this.state.split === 'vertical'
          ? '38vw'
          : '99%',
    };

    return (
      <div className='leaneditorContainer'>
        <div className='headerContainer'>
          <PageHeader
            file={this.props.file}
            url={this.props.initialUrl}
            onSubmit={this.onSubmit}
            clearUrlParam={this.props.clearUrlParam}
            status={this.state.status}
            onSave={this.onSave}
            onLoad={this.onLoad}
            onChecked={this.onChecked}
            showFilePicker={this.props.showFilePicker}
          />
        </div>
        <div className='editorContainer' ref='root'>
          <SplitPane
            split={this.state.split}
            defaultSize='60%'
            allowResize={true}
            onDragFinished={this.dragFinished}
          >
            <div ref='monaco' className='monacoContainer' />
            <div className='infoContainer' style={infoStyle}>
              <InfoView file={this.props.file} cursor={this.state.cursor} />
            </div>
          </SplitPane>
        </div>
      </div>
    );
  }
}

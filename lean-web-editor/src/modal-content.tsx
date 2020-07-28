import React from 'react';
import { createPortal } from 'react-dom';
import { server } from './langservice';
import { info, leanJsOpts } from './options';

export function ModalContent({ onClose, modalRef, onKeyDown, clickAway }) {
  const libinfo = []; // populated with info about included libraries
  if (info) {
    for (const k in info) {
      if (info.hasOwnProperty(k)) {
        const v = info[k];
        if (v.match(/^https:\/\/raw\.githubusercontent\.com/)) {
          const urlArray = v.slice(34).split('/').slice(0, 3);
          const commit = urlArray[2].slice(0, 8);
          urlArray.unshift('https://github.com');
          urlArray.splice(3, 0, 'tree');
          const url = urlArray.join('/');
          libinfo.push(
            <div
              key={libinfo.length - 1}
              className='code-block'
              style={{ fontWeight: 'normal' }}
            >
              {k} : <a href={url}>{commit}</a>
            </div>,
          );
        } else {
          libinfo.push(
            <div
              key={libinfo.length - 1}
              className='code-block'
              style={{ fontWeight: 'normal' }}
            >
              {k} : {v}
            </div>,
          );
        }
      }
    }
  }

  return createPortal(
    <aside
      className='c-modal-cover'
      tabIndex={-1}
      onClick={clickAway}
      onKeyDown={onKeyDown}
    >
      <div className='c-modal' ref={modalRef}>
        <h1>Lean web editor:</h1>
        <button className='c-modal__close' onClick={onClose} autoFocus>
          <span className='u-hide-visually'>Close</span>
          <svg className='c-modal__close-icon' viewBox='0 0 40 40'>
            <path d='M 10,10 L 30,30 M 30,10 L 10,30'></path>
          </svg>
        </button>
        <div className='c-modal__body'>
          <p>
            This page runs a WebAssembly or JavaScript version of{' '}
            <a href='https://leanprover.github.io'>Lean 3</a>, a theorem prover
            and programming language developed at{' '}
            <a href='https://research.microsoft.com/'>Microsoft Research</a>.
          </p>

          <h3>New to Lean?</h3>
          <p>
            Please note that this editor is not really meant for serious use.
            Most Lean users use the Lean VS Code or Emacs extensions to write
            proofs and programs. There are good installation guides for Lean 3
            and its standard library "mathlib"&nbsp;
            <a href='https://leanprover-community.github.io/get_started.html'>
              here
            </a>
            . The books{' '}
            <a href='https://leanprover.github.io/theorem_proving_in_lean'>
              Theorem Proving in Lean
            </a>
            &nbsp; and{' '}
            <a href='https://leanprover.github.io/logic_and_proof/'>
              Logic and Proof
            </a>{' '}
            are reasonable places to start learning Lean. For a more interactive
            approach, you might try{' '}
            <a href='http://wwwf.imperial.ac.uk/~buzzard/xena/natural_number_game/'>
              the "Natural number game"
            </a>
            . For more resources, see the&nbsp;
            <a href='https://leanprover-community.github.io/learn.html'>
              Learning Lean page
            </a>
            . If you have questions, drop by the&nbsp;
            <a href='https://leanprover.zulipchat.com/#'>
              leanprover zulip chat
            </a>
            .
          </p>

          <h3>Using this editor:</h3>
          <p>
            Type Lean code into the editor panel or load and edit a .lean file
            from the web or your computer using the input forms in the header.
            If there are errors, warnings, or info messages, they will be
            underlined in red or green in the editor and a message will be
            displayed in the info panel.
          </p>
          <p>
            You can input unicode characters by entering "\" and then typing the
            corresponding code (see below) and then either typing a space or a
            comma or hitting TAB.
          </p>
          <p>
            Here are a few common codes. Note that many other LaTeX commands
            will work as well:
            <br />
            "lam" for "λ", "to" (or "-&gt;") for "→", "l" (or "&lt;-") for "←",
            "u" for "↑", "d" for "↓", "in" for "∈", "and" for "∧", "or" for "∨",
            "x" for "×", "le" and "ge" (or "&lt;=" and "&gt;=") for "≤" and "≥",
            "&lt;" and "&gt;" for "⟨" and "⟩", "ne" for "≠", "nat" for "ℕ",
            "not" for "¬", "int" for "ℤ",
            <br />
            (For full details, see{' '}
            <a href='https://github.com/leanprover/vscode-lean/blob/master/translations.json'>
              this list
            </a>
            .)
          </p>
          <p>
            To see the type of a term, hover over it to see a popup, or place
            your cursor in the text to view the type and / or docstring in the
            info panel (on the right, or below, depending on your browser's
            aspect ratio).
          </p>
          <p>Click the colored bar to show / hide the header UI.</p>
          <p>
            Drag the separating line between the editor panel and info panels to
            adjust their relative sizes.
          </p>

          <h3>About this editor:</h3>
          <p>
            <a href='https://github.com/leanprover-community/lean-web-editor/'>
              This editor
            </a>{' '}
            is a fork of the original{' '}
            <a href='https://leanprover.github.io/live'>lean-web-editor</a> app
            (written in TypeScript+React and using the Monaco editor; see the
            original GitHub repository{' '}
            <a href='https://github.com/leanprover/lean-web-editor'>here</a>).
            This page also uses{' '}
            <a href='https://github.com/bryangingechen/lean-client-js/tree/cache'>
              a forked version
            </a>{' '}
            of the{' '}
            <a href='https://github.com/leanprover/lean-client-js'>
              lean-client-browser
            </a>{' '}
            package that caches the <code>library.zip</code> file in{' '}
            <a href='https://developer.mozilla.org/en-US/docs/Web/API/IndexedDB_API'>
              IndexedDB
            </a>
            .
          </p>
          <h3>Lean packages in library.zip:</h3>
          {libinfo}
          <h3>Settings:</h3>
          <p>
            <input
              id='showUnderlines'
              type='checkbox'
              defaultChecked={!document.getElementById('hideUnderline')}
              onChange={(e) => {
                if (
                  !e.target.checked &&
                  !document.getElementById('hideUnderline')
                ) {
                  const style = document.createElement('style');
                  style.type = 'text/css';
                  style.id = 'hideUnderline';
                  style.appendChild(
                    document.createTextNode(`.monaco-editor .greensquiggly,
              .monaco-editor .redsquiggly { background-size:0px; }`),
                  );
                  document.head.appendChild(style);
                  window.localStorage.setItem('underline', 'true');
                } else if (document.getElementById('hideUnderline')) {
                  document.getElementById('hideUnderline').remove();
                  window.localStorage.setItem('underline', 'false');
                }
              }}
            />{' '}
            <label htmlFor='showUnderlines'>
              Decorate code with squiggly underlines for errors / warnings /
              info
            </label>
          </p>
          <p>
            <input
              id='showDocs'
              type='checkbox'
              defaultChecked={!document.getElementById('hideDocs')}
              onChange={(e) => {
                if (!e.target.checked && !document.getElementById('hideDocs')) {
                  const style = document.createElement('style');
                  style.type = 'text/css';
                  style.id = 'hideDocs';
                  style.appendChild(
                    document.createTextNode(
                      `.toggleDoc, .doc-header { display:none; }`,
                    ),
                  );
                  document.head.appendChild(style);
                  window.localStorage.setItem('docs', 'true');
                } else if (document.getElementById('hideDocs')) {
                  document.getElementById('hideDocs').remove();
                  window.localStorage.setItem('dosc', 'false');
                }
              }}
            />{' '}
            <label htmlFor='showDocs'>
              Show tactic docs in info panel (regardless of whether this is
              checked, tactic docs can be viewed by hovering your cursor over
              the tactic name)
            </label>
          </p>
          <h3>Debug:</h3>
          <p>
            <input
              id='logToConsole'
              type='checkbox'
              defaultChecked={server.logMessagesToConsole}
              onChange={(e) => {
                server.logMessagesToConsole = e.target.checked;
                window.localStorage.setItem(
                  'logging',
                  e.target.checked ? 'true' : 'false',
                );
                console.log(
                  `server logging ${
                    server.logMessagesToConsole ? 'start' : 'end'
                  }ed!`,
                );
              }}
            />{' '}
            <label htmlFor='logToConsole'>Log server messages to console</label>
          </p>
          <p>
            <button
              onClick={(e) => {
                const req = indexedDB.deleteDatabase('leanlibrary');
                req.onsuccess = () => {
                  console.log('Deleted leanlibrary successfully');
                  location.reload(true);
                };
                req.onerror = () => {
                  console.log("Couldn't delete leanlibrary");
                };
                req.onblocked = () => {
                  console.log(
                    "Couldn't delete leanlibrary due to the operation being blocked",
                  );
                };
              }}
            >
              Clear library cache and refresh
            </button>
          </p>
          <p>
            <button
              onClick={() => {
                if ((self as any).WebAssembly) {
                  fetch(leanJsOpts.webassemblyJs, { cache: 'reload' })
                    .then(() =>
                      fetch(leanJsOpts.webassemblyWasm, { cache: 'reload' }),
                    )
                    .then(() => {
                      console.log('Updated JS & WASM cache successfully');
                      location.reload(true);
                    })
                    .catch((e) => console.log(e));
                } else {
                  fetch(leanJsOpts.javascript, { cache: 'reload' })
                    .then(() => {
                      console.log('Updated JS cache successfully');
                      location.reload(true);
                    })
                    .catch((e) => console.log(e));
                }
              }}
            >
              Clear JS/WASM cache and refresh
            </button>
          </p>
        </div>
      </div>
    </aside>,
    document.body,
  );
}

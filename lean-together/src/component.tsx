import {
  PrimedComponent,
  PrimedComponentFactory,
} from '@fluidframework/aqueduct';
import { IComponentHTMLView } from '@fluidframework/view-interfaces';
import { App, editor } from 'lean-web-editor';

import React from 'react';
import ReactDOM from 'react-dom';

import { ILeanTogether } from './interface';

const editKey = 'edit';

/**
 * Fluid component
 */
export class LeanTogether extends PrimedComponent
  implements ILeanTogether, IComponentHTMLView {
  public static get ComponentName() {
    return 'leantogether';
  }

  public get IComponentHTMLView() {
    return this;
  }

  /**
   * The factory defines how to create an instance of the component as well as the
   * dependencies of the component.
   */
  public static readonly factory = new PrimedComponentFactory(
    LeanTogether.ComponentName,
    LeanTogether,
    [],
    {},
  );

  /**
   * componentInitializingFirstTime is called only once, it is executed only by the first client to open the
   * component and all work will resolve before the view is presented to any user.
   *
   * This method is used to perform component setup, which can include setting an initial schema or initial values.
   */
  protected async componentInitializingFirstTime() {
    this.root.set(editKey, '');
  }

  /**
   * componentHasInitialized runs every time the component is initialized including the first time.
   */
  protected async componentHasInitialized() {
    this.root.on('valueChanged', (changed, local, op, target) => {
      if (local) {
        return;
      }

      console.log(changed, local, op, target);

      if (changed.key === editKey) {
        this.emit('diceRolled');
      }
    });
  }

  /**
   * Render the dice.
   */
  public render(div: HTMLElement) {
    ReactDOM.render(
      <App
        editUrlHash={false}
        showFilePicker={false}
        onValueChange={(edits, value) => {
          this.root.set(editKey, JSON.stringify({ edits, value }));
        }}
        initialValue={this.value.value}
      />,
      div,
    );
  }

  public get value() {
    return JSON.parse(this.root.get(editKey || '{}')) as {
      edits?: editor.IModelContentChangedEvent;
      value?: string;
    };
  }

  public readonly roll = () => {
    const rollValue = Math.floor(Math.random() * 6) + 1;
    this.root.set(editKey, rollValue);
  };
}

import {
  PrimedComponent,
  PrimedComponentFactory,
} from '@fluidframework/aqueduct';
import { IValueChanged } from '@fluidframework/map';
import { IComponentHTMLView } from '@fluidframework/view-interfaces';
import { App, leanJsOpts, registerLeanLanguage } from 'lean-web-editor';

import React from 'react';
import ReactDOM from 'react-dom';

import { ILeanTogether } from './interface';

const diceValueKey = 'diceValue';

registerLeanLanguage(leanJsOpts);

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
    this.root.set(diceValueKey, 1);
  }

  /**
   * componentHasInitialized runs every time the component is initialized including the first time.
   */
  protected async componentHasInitialized() {
    this.root.on('valueChanged', (changed: IValueChanged) => {
      if (changed.key === diceValueKey) {
        this.emit('diceRolled');
      }
    });
  }

  /**
   * Render the dice.
   */
  public render(div: HTMLElement) {
    ReactDOM.render(<App />, div);
  }

  public get value() {
    return this.root.get(diceValueKey);
  }

  public readonly roll = () => {
    const rollValue = Math.floor(Math.random() * 6) + 1;
    this.root.set(diceValueKey, rollValue);
  };
}

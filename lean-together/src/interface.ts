import { EventEmitter } from 'events';
import { editor } from 'lean-web-editor';

/**
 * Describes the public API surface for our Fluid component.
 */
export interface ILeanTogether extends EventEmitter {
  readonly value: { edits?: editor.IModelContentChangedEvent; value?: string };

  /**
   * Roll the dice.  Will cause a "diceRolled" event to be emitted.
   */
  roll: () => void;

  /**
   * The diceRolled event will fire whenever someone rolls the device, either locally or remotely.
   */
  on(event: 'diceRolled', listener: () => void): this;
}

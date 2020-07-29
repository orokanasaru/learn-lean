import { ContainerRuntimeFactoryWithDefaultComponent } from '@fluidframework/aqueduct';
import { LeanTogether } from './component';
import { registerLeanLanguage, leanJsOpts } from 'lean-web-editor';

export { LeanTogether };

const factory = new Promise<typeof LeanTogether.factory>((res) => {
  registerLeanLanguage(leanJsOpts);
  res(LeanTogether.factory);
});

/**
 * fluidExport is the entry point of the fluid package. We define our component
 * as a component that can be created in the container.
 */
export const fluidExport = new ContainerRuntimeFactoryWithDefaultComponent(
  LeanTogether.ComponentName,
  new Map([
    [LeanTogether.ComponentName, factory],
    // Add another component here to create it within the container
  ]),
);

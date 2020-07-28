import { ContainerRuntimeFactoryWithDefaultComponent } from "@fluidframework/aqueduct";
import { LeanTogether } from "./component";

export { LeanTogether };

/**
 * fluidExport is the entry point of the fluid package. We define our component
 * as a component that can be created in the container.
 */
export const fluidExport = new ContainerRuntimeFactoryWithDefaultComponent(
  LeanTogether.ComponentName,
  new Map([
    [LeanTogether.ComponentName, Promise.resolve(LeanTogether.factory)],
    // Add another component here to create it within the container
  ])
);

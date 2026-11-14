// The script's entry: window.StablePatternsDemo.mount(element, options?).
import { mount } from './widget.ts';

(window as unknown as { StablePatternsDemo: { mount: typeof mount } }).StablePatternsDemo = { mount };

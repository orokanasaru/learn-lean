import { editor } from 'monaco-editor';

export async function leanColorize(text: string): Promise<string> {
  const colorized = await editor.colorize(text, 'lean', {});
  return colorized.replace(/&nbsp;/g, ' ');
}

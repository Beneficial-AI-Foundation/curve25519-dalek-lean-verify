import * as vscode from 'vscode';
import { FunctionEntry } from './dataLoader';

export interface DecorationTypes {
  verified: vscode.TextEditorDecorationType;
  specified: vscode.TextEditorDecorationType;
  extracted: vscode.TextEditorDecorationType;
}

export function createDecorationTypes(context: vscode.ExtensionContext): DecorationTypes {
  return {
    verified: vscode.window.createTextEditorDecorationType({
      gutterIconPath: vscode.Uri.file(context.asAbsolutePath('icons/verified.svg')),
      gutterIconSize: '80%',
    }),
    specified: vscode.window.createTextEditorDecorationType({
      gutterIconPath: vscode.Uri.file(context.asAbsolutePath('icons/specified.svg')),
      gutterIconSize: '80%',
    }),
    extracted: vscode.window.createTextEditorDecorationType({
      gutterIconPath: vscode.Uri.file(context.asAbsolutePath('icons/extracted.svg')),
      gutterIconSize: '60%',
    }),
  };
}

export function updateDecorations(
  editor: vscode.TextEditor,
  entries: FunctionEntry[],
  types: DecorationTypes,
  showExtracted: boolean
): void {
  const verifiedRanges: vscode.DecorationOptions[] = [];
  const specifiedRanges: vscode.DecorationOptions[] = [];
  const extractedRanges: vscode.DecorationOptions[] = [];

  for (const entry of entries) {
    // VSCode lines are 0-indexed, JSON lines are 1-indexed
    const line = entry.startLine - 1;
    if (line < 0 || line >= editor.document.lineCount) {
      continue;
    }

    const range = new vscode.Range(line, 0, line, 0);

    if (entry.verified) {
      verifiedRanges.push({ range });
    } else if (entry.specified) {
      specifiedRanges.push({ range });
    } else if (showExtracted) {
      extractedRanges.push({ range });
    }
  }

  editor.setDecorations(types.verified, verifiedRanges);
  editor.setDecorations(types.specified, specifiedRanges);
  editor.setDecorations(types.extracted, extractedRanges);
}

export function clearDecorations(
  editor: vscode.TextEditor,
  types: DecorationTypes
): void {
  editor.setDecorations(types.verified, []);
  editor.setDecorations(types.specified, []);
  editor.setDecorations(types.extracted, []);
}

import * as vscode from 'vscode';
import { FileIndex, findEntriesForFile } from './dataLoader';

export class SpecHoverProvider implements vscode.HoverProvider {
  constructor(
    private getFileIndex: () => FileIndex,
    private workspaceRoot: string
  ) {}

  provideHover(
    document: vscode.TextDocument,
    position: vscode.Position,
    _token: vscode.CancellationToken
  ): vscode.ProviderResult<vscode.Hover> {
    const entries = findEntriesForFile(this.getFileIndex(), document.uri, this.workspaceRoot);
    if (entries.length === 0) {
      return null;
    }

    // Only respond on the first line of a function
    const line = position.line + 1; // 0-indexed to 1-indexed
    const entry = entries.find(e => e.startLine === line);
    if (!entry || !entry.specStatement) {
      return null;
    }

    const md = new vscode.MarkdownString();
    md.isTrusted = true;
    md.appendCodeblock(entry.specStatement, 'lean');

    // Link to open spec file
    if (entry.specFile) {
      const cmdArgs = encodeURIComponent(JSON.stringify(entry.specFile));
      const cmdUri = `command:aeneas-verify.openSpecFile?${cmdArgs}`;
      md.appendMarkdown(`[Open spec file](${cmdUri})`);
    }

    const hoverRange = new vscode.Range(position.line, 0, position.line, Number.MAX_SAFE_INTEGER);

    return new vscode.Hover(md, hoverRange);
  }
}


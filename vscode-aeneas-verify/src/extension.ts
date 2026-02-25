import * as vscode from 'vscode';
import * as path from 'path';
import { loadFunctions, findEntriesForFile, FileIndex } from './dataLoader';
import { createDecorationTypes, updateDecorations, DecorationTypes } from './decorationProvider';
import { SpecHoverProvider } from './hoverProvider';

let fileIndex: FileIndex = new Map();
let decorationTypes: DecorationTypes;

export function activate(context: vscode.ExtensionContext) {
  console.log('Aeneas Verify: activate() called');
  console.log(`Aeneas Verify: extension path = ${context.extensionPath}`);

  const workspaceFolder = vscode.workspace.workspaceFolders?.[0];
  if (!workspaceFolder) {
    console.log('Aeneas Verify: no workspace folder found, aborting');
    return;
  }
  const workspaceRoot = workspaceFolder.uri.fsPath;
  console.log(`Aeneas Verify: workspace root = ${workspaceRoot}`);

  // Read configuration
  const config = vscode.workspace.getConfiguration('aeneas-verify');
  const jsonRelPath = config.get<string>('jsonPath', 'functions.json');
  const jsonAbsPath = path.join(workspaceRoot, jsonRelPath);

  // Load data
  fileIndex = loadFunctions(jsonAbsPath);
  const entryCount = Array.from(fileIndex.values()).reduce((sum, arr) => sum + arr.length, 0);
  console.log(`Aeneas Verify: Loaded ${entryCount} function entries from ${jsonRelPath}`);

  // Create gutter decorations
  decorationTypes = createDecorationTypes(context);

  // Register hover provider
  const hoverProvider = new SpecHoverProvider(() => fileIndex, workspaceRoot);
  context.subscriptions.push(
    vscode.languages.registerHoverProvider('rust', hoverProvider)
  );

  // Register command: open spec file
  context.subscriptions.push(
    vscode.commands.registerCommand('aeneas-verify.openSpecFile', (specFile: string) => {
      const absPath = path.join(workspaceRoot, specFile);
      const uri = vscode.Uri.file(absPath);
      vscode.window.showTextDocument(uri);
    })
  );

  // Register command: manual reload
  context.subscriptions.push(
    vscode.commands.registerCommand('aeneas-verify.reload', () => {
      fileIndex = loadFunctions(jsonAbsPath);
      refreshActiveEditor();
      vscode.window.showInformationMessage('Aeneas Verify: Reloaded verification data');
    })
  );

  // Watch for JSON changes
  const watcher = vscode.workspace.createFileSystemWatcher(
    new vscode.RelativePattern(workspaceFolder, jsonRelPath)
  );
  watcher.onDidChange(() => {
    fileIndex = loadFunctions(jsonAbsPath);
    refreshActiveEditor();
    console.log('Aeneas Verify: Reloaded after functions.json change');
  });
  watcher.onDidCreate(() => {
    fileIndex = loadFunctions(jsonAbsPath);
    refreshActiveEditor();
  });
  context.subscriptions.push(watcher);

  // React to editor changes
  context.subscriptions.push(
    vscode.window.onDidChangeActiveTextEditor(editor => {
      if (editor) {
        decorateEditor(editor, workspaceRoot);
      }
    })
  );

  // React to configuration changes
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration(e => {
      if (e.affectsConfiguration('aeneas-verify')) {
        refreshActiveEditor();
      }
    })
  );

  // Decorate the currently active editor on startup
  if (vscode.window.activeTextEditor) {
    decorateEditor(vscode.window.activeTextEditor, workspaceRoot);
  }

  // Also decorate when visible editors change (e.g. split views)
  context.subscriptions.push(
    vscode.window.onDidChangeVisibleTextEditors(editors => {
      for (const editor of editors) {
        decorateEditor(editor, workspaceRoot);
      }
    })
  );

  function refreshActiveEditor() {
    for (const editor of vscode.window.visibleTextEditors) {
      decorateEditor(editor, workspaceRoot);
    }
  }

  function decorateEditor(editor: vscode.TextEditor, wsRoot: string) {
    console.log(`Aeneas Verify: decorateEditor called for ${editor.document.uri.fsPath} (lang=${editor.document.languageId})`);
    if (editor.document.languageId !== 'rust') {
      console.log('Aeneas Verify: skipping non-rust file');
      return;
    }

    const showExtracted = vscode.workspace
      .getConfiguration('aeneas-verify')
      .get<boolean>('showExtractedOnly', true);

    const entries = findEntriesForFile(fileIndex, editor.document.uri, wsRoot);
    console.log(`Aeneas Verify: found ${entries.length} entries for this file (showExtracted=${showExtracted})`);
    if (entries.length > 0) {
      console.log(`Aeneas Verify: first entry: ${entries[0].rustName} L${entries[0].startLine} verified=${entries[0].verified} specified=${entries[0].specified}`);
    }
    updateDecorations(editor, entries, decorationTypes, showExtracted);
  }
}

export function deactivate() {
  // Decoration types are disposed via context.subscriptions
}

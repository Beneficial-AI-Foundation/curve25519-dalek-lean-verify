import * as fs from 'fs';
import * as path from 'path';
import * as vscode from 'vscode';

export interface FunctionEntry {
  rustName: string;
  leanName: string;
  source: string;
  startLine: number;
  endLine: number;
  specified: boolean;
  verified: boolean;
  specStatement: string | null;
  specDocstring: string | null;
  specFile: string | null;
}

/** Map from source file path (as in JSON) to sorted array of function entries */
export type FileIndex = Map<string, FunctionEntry[]>;

interface RawFunctionEntry {
  rust_name: string;
  lean_name: string;
  source: string;
  lines: string;
  specified: boolean;
  verified: boolean;
  spec_statement: string | null;
  spec_docstring: string | null;
  spec_file: string | null;
  is_hidden: boolean;
  is_extraction_artifact: boolean;
}

interface RawFunctionsJson {
  functions: RawFunctionEntry[];
}

function parseLineRange(lines: string): { startLine: number; endLine: number } | null {
  const match = lines.match(/^L(\d+)-L(\d+)$/);
  if (!match) {
    return null;
  }
  return { startLine: parseInt(match[1], 10), endLine: parseInt(match[2], 10) };
}

/**
 * Load functions.json and build an index keyed by source file path.
 * Filters out hidden entries and extraction artifacts.
 */
export function loadFunctions(jsonPath: string): FileIndex {
  const index: FileIndex = new Map();

  let content: string;
  try {
    content = fs.readFileSync(jsonPath, 'utf-8');
  } catch (e) {
    vscode.window.showWarningMessage(`Aeneas Verify: Could not read ${jsonPath}`);
    return index;
  }

  let data: RawFunctionsJson;
  try {
    data = JSON.parse(content);
  } catch (e) {
    vscode.window.showWarningMessage(`Aeneas Verify: Could not parse ${jsonPath}`);
    return index;
  }

  if (!Array.isArray(data.functions)) {
    vscode.window.showWarningMessage(`Aeneas Verify: No "functions" array in ${jsonPath}`);
    return index;
  }

  for (const raw of data.functions) {
    // Skip hidden entries (impl trait blocks) and extraction artifacts (loop helpers, _body)
    if (raw.is_hidden || raw.is_extraction_artifact) {
      continue;
    }

    const range = parseLineRange(raw.lines);
    if (!range) {
      continue;
    }

    const entry: FunctionEntry = {
      rustName: raw.rust_name,
      leanName: raw.lean_name,
      source: raw.source,
      startLine: range.startLine,
      endLine: range.endLine,
      specified: raw.specified,
      verified: raw.verified,
      specStatement: raw.spec_statement,
      specDocstring: raw.spec_docstring,
      specFile: raw.spec_file,
    };

    const existing = index.get(raw.source);
    if (existing) {
      existing.push(entry);
    } else {
      index.set(raw.source, [entry]);
    }
  }

  // Sort each file's entries by start line
  for (const entries of index.values()) {
    entries.sort((a, b) => a.startLine - b.startLine);
  }

  return index;
}

/**
 * Find function entries that correspond to the given document.
 * Matches the document's path against the source field in the index.
 */
export function findEntriesForFile(
  fileIndex: FileIndex,
  documentUri: vscode.Uri,
  workspaceRoot: string
): FunctionEntry[] {
  const docPath = documentUri.fsPath;
  const relativePath = path.relative(workspaceRoot, docPath);
  // Normalize to forward slashes for cross-platform matching
  const normalized = relativePath.split(path.sep).join('/');

  // Direct lookup
  const direct = fileIndex.get(normalized);
  if (direct) {
    return direct;
  }

  // Suffix match: the JSON might use a different prefix than the workspace root
  for (const [source, entries] of fileIndex) {
    if (normalized.endsWith(source) || source.endsWith(normalized)) {
      return entries;
    }
  }

  return [];
}

/**
 * Find the specific entry whose line range contains the given line (1-indexed).
 */
export function findEntryAtLine(entries: FunctionEntry[], line: number): FunctionEntry | undefined {
  return entries.find(e => line >= e.startLine && line <= e.endLine);
}

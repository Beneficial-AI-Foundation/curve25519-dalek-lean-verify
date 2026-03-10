import fs from 'fs'
import path from 'path'

// Raw record as stored in functions.json
interface RawFunctionRecord {
  lean_name: string
  rust_name: string | null
  source: string | null
  lines: string | null
  dependencies: string[]
  nested_children: string[]
  is_relevant: boolean
  is_extraction_artifact: boolean
  is_hidden: boolean
  is_ignored: boolean
  specified: boolean
  verified: boolean
  fully_verified: boolean
  externally_verified: boolean
  spec_docstring: string | null
  spec_statement: string | null
}

// Extended record with computed fields
export interface FunctionRecord extends RawFunctionRecord {
  dependents: string[]
  rust_source: string | null
}

export interface FunctionsData {
  functions: FunctionRecord[]
}

declare const data: FunctionsData
export { data }

// Parse "L459-L473" → { start: 459, end: 473 }
function parseLines(lines: string): { start: number; end: number } | null {
  const m = lines.match(/^L(\d+)-L(\d+)$/)
  if (!m) return null
  return { start: parseInt(m[1], 10), end: parseInt(m[2], 10) }
}

// Read Rust source lines, caching file contents
function readRustSource(
  source: string,
  lines: string,
  fileCache: Map<string, string[]>
): string | null {
  const range = parseLines(lines)
  if (!range) return null

  const filePath = path.join(process.cwd(), source)

  let fileLines = fileCache.get(filePath)
  if (!fileLines) {
    try {
      const content = fs.readFileSync(filePath, 'utf-8')
      fileLines = content.split('\n')
      fileCache.set(filePath, fileLines)
    } catch {
      return null
    }
  }

  if (range.start < 1 || range.start > fileLines.length) return null
  const extracted = fileLines.slice(range.start - 1, range.end)
  return extracted.length > 0 ? extracted.join('\n') : null
}

export default {
  watch: ['../../../functions.json'],
  load(): FunctionsData {
    const functionsPath = path.join(process.cwd(), 'functions.json')
    const content = fs.readFileSync(functionsPath, 'utf-8')
    const parsed = JSON.parse(content) as { functions: RawFunctionRecord[] }

    // Build reverse dependency map
    const dependentsMap = new Map<string, string[]>()
    for (const fn of parsed.functions) {
      for (const dep of fn.dependencies) {
        if (!dependentsMap.has(dep)) {
          dependentsMap.set(dep, [])
        }
        dependentsMap.get(dep)!.push(fn.lean_name)
      }
    }

    // Read Rust source files (cached per file path)
    const fileCache = new Map<string, string[]>()

    const functions: FunctionRecord[] = parsed.functions.map(fn => ({
      ...fn,
      dependents: dependentsMap.get(fn.lean_name) ?? [],
      rust_source: fn.source && fn.lines
        ? readRustSource(fn.source, fn.lines, fileCache)
        : null
    }))

    return { functions }
  }
}

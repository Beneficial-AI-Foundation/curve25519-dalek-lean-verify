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
  specified: boolean
  verified: boolean
  fully_verified: boolean
  externally_verified: boolean
  spec_docstring: string | null
  spec_statement: string | null
  rust_source: string | null
}

// Extended record with computed dependents field
export interface FunctionRecord extends RawFunctionRecord {
  dependents: string[]  // functions that depend on this one
}

export interface FunctionsData {
  functions: FunctionRecord[]
}

declare const data: FunctionsData
export { data }

export default {
  watch: ['../../../functions.json'],
  load(): FunctionsData {
    const functionsPath = path.join(process.cwd(), 'functions.json')
    const content = fs.readFileSync(functionsPath, 'utf-8')
    const parsed = JSON.parse(content) as { functions: RawFunctionRecord[] }

    // Build reverse dependency map: for each function, who uses it?
    const dependentsMap = new Map<string, string[]>()

    for (const fn of parsed.functions) {
      for (const dep of fn.dependencies) {
        if (!dependentsMap.has(dep)) {
          dependentsMap.set(dep, [])
        }
        dependentsMap.get(dep)!.push(fn.lean_name)
      }
    }

    // Add dependents field to each function
    const functions: FunctionRecord[] = parsed.functions.map(fn => ({
      ...fn,
      dependents: dependentsMap.get(fn.lean_name) ?? []
    }))

    return { functions }
  }
}

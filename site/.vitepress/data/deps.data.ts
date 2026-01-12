import fs from 'fs'
import path from 'path'

export interface FunctionRecord {
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
  spec_docstring: string | null
  spec_statement: string | null
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
    const parsed = JSON.parse(content) as FunctionsData
    return parsed
  }
}

import fs from 'fs'
import path from 'path'

export interface FunctionDep {
  lean_name: string
  dependencies: string[]
  specified: boolean
  verified: boolean
  fully_verified: boolean
}

export interface DepsData {
  functions: FunctionDep[]
}

declare const data: DepsData
export { data }

export default {
  watch: ['../../../deps.json'],
  load(): DepsData {
    const depsPath = path.join(process.cwd(), 'deps.json')
    const content = fs.readFileSync(depsPath, 'utf-8')
    const parsed = JSON.parse(content) as DepsData
    return parsed
  }
}

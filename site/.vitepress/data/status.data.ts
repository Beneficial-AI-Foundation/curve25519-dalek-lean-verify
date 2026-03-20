import fs from 'fs'
import path from 'path'

interface FunctionRecord {
  lean_name: string
  rust_name: string | null
  source: string | null
  lines: string | null
  spec_file: string | null
  is_hidden: boolean
  is_extraction_artifact: boolean
  specified: boolean
  verified: boolean
  externally_verified: boolean
}

export interface StatusEntry {
  function: string
  source: string
  lines: string
  spec_theorem: string
  extracted: string
  verified: string
  notes: string
  'ai-proveable'?: string
}

export interface StatusData {
  entries: StatusEntry[]
  stats: {
    total: number
    extracted: number
    draft_spec: number
    specified: number
    verified: number
    externally_verified: number
    ai_proveable: number
  }
}

declare const data: StatusData
export { data }

function toStatusEntry(fn: FunctionRecord): StatusEntry {
  let verifiedStr = ''
  if (fn.verified) verifiedStr = 'verified'
  else if (fn.externally_verified) verifiedStr = 'externally verified'
  else if (fn.specified) verifiedStr = 'specified'

    return {
    function: fn.rust_name ?? fn.lean_name,
    source: fn.source ?? '',
    lines: fn.lines ?? '',
    spec_theorem: fn.spec_file ?? '',
    extracted: 'extracted',
    verified: verifiedStr,
    notes: '',
    'ai-proveable': ''
  }
}

export default {
  watch: ['../../../functions.json'],
  load(): StatusData {
    const functionsPath = path.join(process.cwd(), 'functions.json')
    const content = fs.readFileSync(functionsPath, 'utf-8')
    const parsed = JSON.parse(content) as { functions: FunctionRecord[] }

    const visible = parsed.functions.filter(
      fn => !fn.is_hidden && !fn.is_extraction_artifact
    )

    const entries = visible.map(toStatusEntry)

    const stats = {
      total: visible.length,
      extracted: visible.length,
      draft_spec: 0,
      specified: visible.filter(fn => fn.specified).length,
      verified: visible.filter(fn => fn.verified).length,
      externally_verified: visible.filter(fn => fn.externally_verified).length,
      ai_proveable: 0
    }

    return { entries, stats }
  }
}
// Shared types for the verification status site

export interface FunctionDep {
  lean_name: string
  dependencies: string[]
  specified: boolean
  verified: boolean
  fully_verified: boolean
}

export interface StatusEntry {
  function: string
  lean_name?: string
  source: string
  lines: string
  spec_theorem: string
  extracted: string
  verified: string
  notes: string
  'ai-proveable'?: string
}

export interface ProgressDataPoint {
  date: string
  timestamp: number
  total: number
  verified: number
  specified: number
  draft_spec: number
  extracted: number
  ai_proveable: number
}

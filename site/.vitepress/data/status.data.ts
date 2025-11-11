import fs from 'fs'
import path from 'path'
import { fileURLToPath } from 'url'
import { parse } from 'csv-parse/sync'

const __dirname = path.dirname(fileURLToPath(import.meta.url))

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
    ai_proveable: number
  }
}

declare const data: StatusData
export { data }

export default {
  watch: ['../../../status.csv'],
  load(): StatusData {
    // Read the CSV file from the project root
    // During build, process.cwd() is the project root
    const csvPath = path.join(process.cwd(), 'status.csv')
    const csvContent = fs.readFileSync(csvPath, 'utf-8')

    // Parse CSV
    const records = parse(csvContent, {
      columns: true,
      skip_empty_lines: true,
      trim: true,
      relax_column_count: true
    }) as StatusEntry[]

    // Calculate statistics
    const stats = {
      total: records.length,
      extracted: records.filter(r => r.extracted === 'extracted').length,
      draft_spec: records.filter(r => r.verified === 'draft spec').length,
      specified: records.filter(r => r.verified === 'specified').length,
      verified: records.filter(r => r.verified === 'verified').length,
      ai_proveable: records.filter(r => r['ai-proveable'] && r['ai-proveable'].trim() !== '').length
    }

    return {
      entries: records,
      stats
    }
  }
}
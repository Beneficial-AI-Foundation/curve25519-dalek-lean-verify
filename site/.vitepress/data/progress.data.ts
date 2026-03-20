import fs from 'fs'
import path from 'path'

export interface ProgressDataPoint {
  date: string
  timestamp: number
  total: number
  verified: number
  externally_verified: number
  specified: number
  draft_spec: number
  extracted: number
  ai_proveable: number
  ignored: number
}

export interface ProgressData {
  dataPoints: ProgressDataPoint[]
}

declare const data: ProgressData
export { data }

interface HistoryEntry {
  commit: string
  date: string
  total: number
  verified: number
  externally_verified: number
  specified: number
  extracted: number
  fully_verified: number
  ignored: number
}

export default {
  watch: ['../../../outputs/stats_history.jsonl'],
  load(): ProgressData {
    console.log('Loading progress data from stats_history.jsonl...')

    const historyPath = path.join(process.cwd(), 'outputs', 'stats_history.jsonl')
    const dataPoints: ProgressDataPoint[] = []

    if (!fs.existsSync(historyPath)) {
      console.warn('stats_history.jsonl not found, returning empty progress data')
      return { dataPoints }
    }

    const content = fs.readFileSync(historyPath, 'utf-8')
    for (const line of content.split('\n')) {
      const trimmed = line.trim()
      if (!trimmed) continue
      try {
        const entry: HistoryEntry = JSON.parse(trimmed)
        const timestamp = Math.floor(new Date(entry.date).getTime() / 1000)
        dataPoints.push({
          date: entry.date,
          timestamp,
          total: entry.total,
          verified: entry.verified,
          externally_verified: entry.externally_verified,
          specified: entry.specified,
          draft_spec: 0,
          extracted: entry.extracted,
          ai_proveable: 0,
          ignored: entry.ignored
        })
      } catch {
        continue
      }
    }

    console.log(`Loaded ${dataPoints.length} data points from stats_history.jsonl`)
    return { dataPoints }
  }
}

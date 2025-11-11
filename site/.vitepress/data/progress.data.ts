import { execSync } from 'child_process'
import { parse } from 'csv-parse/sync'

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

export interface ProgressData {
  dataPoints: ProgressDataPoint[]
}

declare const data: ProgressData
export { data }

function getCommitHistory(): Array<{ hash: string; timestamp: number }> {
  try {
    const output = execSync('git log "--format=%H|%at" --reverse', {
      encoding: 'utf-8',
      cwd: process.cwd(),
      shell: '/bin/bash'
    })

    return output
      .trim()
      .split('\n')
      .filter(line => line)
      .map(line => {
        const [hash, timestamp] = line.split('|')
        return { hash, timestamp: parseInt(timestamp) }
      })
  } catch (error) {
    console.error('Error getting commit history:', error)
    return []
  }
}

function getFileFromCommit(commitHash: string, filepath: string): string | null {
  try {
    const output = execSync(`git show ${commitHash}:${filepath}`, {
      encoding: 'utf-8',
      cwd: process.cwd()
    })
    return output
  } catch {
    return null
  }
}

function countVerificationStatus(csvContent: string | null): {
  total: number
  verified: number
  specified: number
  draft_spec: number
  extracted: number
  ai_proveable: number
} | null {
  if (!csvContent) return null

  try {
    const records = parse(csvContent, {
      columns: true,
      skip_empty_lines: true,
      trim: true,
      relax_column_count: true
    }) as StatusEntry[]

    // let total = 0
    // let verified = 0
    // let specified = 0
    // let draftSpec = 0
    // let extracted = 0

    // Calculate statistics
    // const stats = {
    let total = records.length
    let extracted = records.filter(r => r.extracted === 'extracted').length
    let draft_spec = records.filter(r => r.verified === 'draft spec').length
    let specified = records.filter(r => r.verified === 'specified').length
    let verified = records.filter(r => r.verified === 'verified').length
    let ai_proveable = records.filter(r => r['ai-proveable'] && r['ai-proveable'].trim() !== '').length
    // }

    // for (const row of records) {
    //   total++
    //   const status = (row.verified || '').trim().toLowerCase()
    //   const specTheorem = (row.spec_theorem || '').trim()
    //   const extractedStatus = (row.extracted || '').trim().toLowerCase()

    //   if (status === 'verified') {
    //     verified++
    //   } else if (status === 'specified') {
    //     specified++
    //   } else if (specTheorem) {
    //     // Has spec_theorem but not verified/specified = draft
    //     draftSpec++
    //   }

    //   if (extractedStatus === 'extracted') {
    //     extracted++
    //   }
    // }

    return { total, verified, specified, draft_spec, extracted, ai_proveable }
  } catch (error) {
    console.error('Error parsing CSV:', error)
    return null
  }
}

export default {
  watch: ['../../../.git/refs/heads/**'],
  load(): ProgressData {
    console.log('Loading progress data from git history...')

    const commits = getCommitHistory()
    const dataPoints: ProgressDataPoint[] = []

    for (const commit of commits) {
      const csvContent = getFileFromCommit(commit.hash, 'status.csv')
      const counts = countVerificationStatus(csvContent)

      if (counts) {
        dataPoints.push({
          date: new Date(commit.timestamp * 1000).toISOString(),
          timestamp: commit.timestamp,
          total: counts.total,
          verified: counts.verified,
          specified: counts.specified,
          draft_spec: counts.draft_spec,
          extracted: counts.extracted,
          ai_proveable: counts.ai_proveable
        })
      }
    }

    console.log(`Loaded ${dataPoints.length} data points from git history`)

    return { dataPoints }
  }
}

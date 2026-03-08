import { computed, type Ref } from 'vue'
import type { ProcessedGraphData, FileStats, FilteredGraphData } from '../types/graph'

/**
 * Composable for computing and accessing graph statistics.
 * Provides both global stats and per-file breakdowns.
 */
export function useGraphStats(
  processedData: Ref<ProcessedGraphData>,
  filteredData?: Ref<FilteredGraphData>
) {
  // Global stats from processed data
  const globalStats = computed(() => processedData.value.stats)

  // Per-file stats sorted by verification percentage (descending)
  const fileStatsSorted = computed<FileStats[]>(() => {
    const stats = Array.from(processedData.value.stats.bySourceFile.values())
    return stats.sort((a, b) => b.verificationPercentage - a.verificationPercentage)
  })

  // Stats for currently filtered/visible nodes
  const filteredStats = computed(() => {
    if (!filteredData) {
      return globalStats.value
    }

    const nodes = filteredData.value.nodes
    let total = 0
    let verified = 0
    let fullyVerified = 0
    let specified = 0
    let notSpecified = 0

    for (const node of nodes) {
      total++
      if (node.status === 'verified') {
        verified++
        fullyVerified++
      } else if (node.status === 'externally_verified') {
        verified++
      } else if (node.status === 'specified') {
        specified++
      } else {
        notSpecified++
      }
    }

    return {
      total,
      verified,
      fullyVerified,
      specified,
      notSpecified,
      verificationPercentage: total > 0 ? Math.round((verified / total) * 100) : 0
    }
  })

  // Get stats for a specific source file
  function getFileStats(sourceFile: string): FileStats | undefined {
    return processedData.value.stats.bySourceFile.get(sourceFile)
  }

  // Get filename from full path (for display)
  function getDisplayName(sourceFile: string): string {
    if (sourceFile === 'unknown') return 'Unknown'
    const parts = sourceFile.split('/')
    return parts[parts.length - 1]
  }

  // Summary text for global stats
  const summaryText = computed(() => {
    const s = globalStats.value
    return `${s.total} functions | ${s.verified} verified (${Math.round((s.verified / s.total) * 100)}%) | ${s.specified} specified | ${s.notSpecified} not specified`
  })

  // Summary text for filtered stats
  const filteredSummaryText = computed(() => {
    const s = filteredStats.value
    if (s.total === 0) return 'No functions visible'
    const pct = Math.round((s.verified / s.total) * 100)
    return `${s.total} functions | ${s.verified} verified (${pct}%) | ${s.specified} specified | ${s.notSpecified} not specified`
  })

  return {
    globalStats,
    fileStatsSorted,
    filteredStats,
    getFileStats,
    getDisplayName,
    summaryText,
    filteredSummaryText
  }
}

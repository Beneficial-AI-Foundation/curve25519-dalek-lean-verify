import { computed, type Ref } from 'vue'
import type { FunctionRecord } from '../data/deps.data'
import type {
  GraphNode,
  GraphEdge,
  ProcessedGraphData,
  GlobalStats,
  FileStats,
  NodeStatus
} from '../types/graph'
import { getShortLabel, getMediumLabel } from '../utils/labelUtils'

/**
 * Compute transitive dependencies through hidden functions.
 * If A depends on B (hidden) which depends on C (visible), result includes C.
 */
function computeTransitiveDependencies(
  funcName: string,
  hiddenSet: Set<string>,
  allFuncsMap: Map<string, FunctionRecord>,
  visibleSet: Set<string>,
  visited: Set<string> = new Set()
): { deps: string[]; transitiveTargets: Set<string> } {
  const deps: string[] = []
  const transitiveTargets = new Set<string>()
  const func = allFuncsMap.get(funcName)

  if (!func) return { deps, transitiveTargets }

  for (const dep of func.dependencies) {
    if (visited.has(dep)) continue
    visited.add(dep)

    if (hiddenSet.has(dep)) {
      // Hidden: recurse to find visible transitive deps
      const transitive = computeTransitiveDependencies(
        dep,
        hiddenSet,
        allFuncsMap,
        visibleSet,
        visited
      )
      deps.push(...transitive.deps)
      // Mark these as transitive targets
      transitive.deps.forEach(d => transitiveTargets.add(d))
      transitive.transitiveTargets.forEach(t => transitiveTargets.add(t))
    } else if (visibleSet.has(dep)) {
      // Visible: direct dependency
      deps.push(dep)
    }
    // Dependencies not in visibleSet are ignored (e.g., external deps)
  }

  return { deps: [...new Set(deps)], transitiveTargets }
}

/**
 * Get the verification status of a function
 */
function getNodeStatus(func: FunctionRecord): NodeStatus {
  if (func.fully_verified) return 'fully_verified'
  if (func.verified) return 'verified'
  if (func.specified) return 'specified'
  return 'none'
}

/**
 * Extract filename from full source path
 */
function getFilename(source: string | null): string {
  if (!source) return 'unknown'
  const parts = source.split('/')
  return parts[parts.length - 1]
}

/**
 * Composable for processing raw function data into graph-ready structures.
 * Handles filtering of hidden functions and extraction artifacts,
 * and computes transitive dependencies.
 */
export function useGraphData(rawFunctions: Ref<FunctionRecord[]>) {
  const processedData = computed<ProcessedGraphData>(() => {
    const functions = rawFunctions.value

    // Separate hidden and visible functions
    // Hidden includes: is_hidden=true and extraction artifacts
    const hiddenSet = new Set<string>()
    const visibleSet = new Set<string>()
    const allFuncsMap = new Map<string, FunctionRecord>()

    for (const func of functions) {
      allFuncsMap.set(func.lean_name, func)
      // Filter out hidden functions and extraction artifacts (matches status.csv criteria)
      const isFiltered = func.is_hidden || func.is_extraction_artifact
      if (isFiltered) {
        hiddenSet.add(func.lean_name)
      } else {
        visibleSet.add(func.lean_name)
      }
    }

    // Track which nodes have incoming transitive edges
    const transitiveTargetSet = new Set<string>()

    // Build nodes from visible functions with transitive dependencies
    const nodeMap = new Map<string, GraphNode>()
    const nodes: GraphNode[] = []

    for (const func of functions) {
      // Skip hidden and filtered functions
      if (hiddenSet.has(func.lean_name)) continue

      const { deps: transitiveDeps, transitiveTargets } = computeTransitiveDependencies(
        func.lean_name,
        hiddenSet,
        allFuncsMap,
        visibleSet
      )

      // Track transitive targets globally
      transitiveTargets.forEach(t => transitiveTargetSet.add(t))

      const node: GraphNode = {
        id: func.lean_name,
        label: getShortLabel(func.lean_name),
        fullLabel: getMediumLabel(func.lean_name),
        sourceFile: func.source,
        lines: func.lines,
        status: getNodeStatus(func),
        fullyVerified: func.fully_verified,
        specStatement: func.spec_statement,
        specDocstring: func.spec_docstring,
        rustName: func.rust_name,
        originalDependencies: func.dependencies,
        dependencies: transitiveDeps,
        dependents: [], // computed below
        isTransitiveTarget: false // updated below
      }

      nodes.push(node)
      nodeMap.set(func.lean_name, node)
    }

    // Compute reverse dependencies (dependents) based on transitive deps
    for (const node of nodes) {
      for (const dep of node.dependencies) {
        const targetNode = nodeMap.get(dep)
        if (targetNode) {
          targetNode.dependents.push(node.id)
        }
      }
    }

    // Mark transitive targets
    for (const nodeId of transitiveTargetSet) {
      const node = nodeMap.get(nodeId)
      if (node) {
        node.isTransitiveTarget = true
      }
    }

    // Build edges
    const edges: GraphEdge[] = []
    const edgeSet = new Set<string>() // prevent duplicates

    for (const node of nodes) {
      for (const dep of node.dependencies) {
        const edgeId = `${node.id}->${dep}`
        if (!edgeSet.has(edgeId) && nodeMap.has(dep)) {
          edgeSet.add(edgeId)

          // Check if this edge is transitive (dependency was through hidden node)
          const originalDeps = node.originalDependencies
          const isTransitive = !originalDeps.includes(dep)

          edges.push({
            id: edgeId,
            source: node.id,
            target: dep,
            isTransitive
          })
        }
      }
    }

    // Collect unique source files
    const sourceFilesSet = new Set<string>()
    for (const node of nodes) {
      if (node.sourceFile) {
        sourceFilesSet.add(node.sourceFile)
      }
    }
    const sourceFiles = Array.from(sourceFilesSet).sort()

    // Compute statistics
    const stats = computeStats(nodes, hiddenSet.size, sourceFiles)

    return {
      nodes,
      edges,
      nodeMap,
      sourceFiles,
      stats
    }
  })

  return {
    processedData
  }
}

/**
 * Compute global and per-file statistics
 */
function computeStats(
  nodes: GraphNode[],
  hiddenCount: number,
  sourceFiles: string[]
): GlobalStats {
  const bySourceFile = new Map<string, FileStats>()

  // Initialize per-file stats
  for (const file of sourceFiles) {
    bySourceFile.set(file, {
      sourceFile: file,
      total: 0,
      verified: 0,
      fullyVerified: 0,
      specified: 0,
      notSpecified: 0,
      verificationPercentage: 0
    })
  }

  // Also track "unknown" source
  bySourceFile.set('unknown', {
    sourceFile: 'unknown',
    total: 0,
    verified: 0,
    fullyVerified: 0,
    specified: 0,
    notSpecified: 0,
    verificationPercentage: 0
  })

  let total = 0
  let verified = 0
  let fullyVerified = 0
  let specified = 0
  let notSpecified = 0

  for (const node of nodes) {
    total++
    const file = node.sourceFile || 'unknown'
    const fileStats = bySourceFile.get(file)!

    fileStats.total++

    if (node.status === 'fully_verified') {
      fullyVerified++
      verified++
      fileStats.fullyVerified++
      fileStats.verified++
    } else if (node.status === 'verified') {
      verified++
      fileStats.verified++
    } else if (node.status === 'specified') {
      specified++
      fileStats.specified++
    } else {
      notSpecified++
      fileStats.notSpecified++
    }
  }

  // Compute verification percentages
  for (const [_, fileStats] of bySourceFile) {
    if (fileStats.total > 0) {
      fileStats.verificationPercentage = Math.round(
        (fileStats.verified / fileStats.total) * 100
      )
    }
  }

  // Remove empty "unknown" if no nodes have null source
  const unknownStats = bySourceFile.get('unknown')!
  if (unknownStats.total === 0) {
    bySourceFile.delete('unknown')
  }

  return {
    total,
    verified,
    fullyVerified,
    specified,
    notSpecified,
    hiddenFiltered: hiddenCount,
    bySourceFile
  }
}

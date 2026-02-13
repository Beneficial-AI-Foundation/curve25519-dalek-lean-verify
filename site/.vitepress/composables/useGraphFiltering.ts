import { computed, reactive, type Ref } from 'vue'
import type {
  ProcessedGraphData,
  FilterState,
  FilteredGraphData,
  GraphNode,
  GraphEdge,
  SubgraphMode
} from '../types/graph'

/**
 * Composable for filtering graph data by source file and extracting subgraphs.
 */
export function useGraphFiltering(
  processedData: Ref<ProcessedGraphData>,
  initialFilters?: Partial<FilterState>
) {
  // Initialize filter state with all source files enabled
  const filterState = reactive<FilterState>({
    enabledSourceFiles: new Set(processedData.value.sourceFiles),
    focusedFunction: null,
    subgraphMode: 'all',
    subgraphDepth: 2,
    ...initialFilters
  })

  // Toggle a source file on/off
  function toggleSourceFile(sourceFile: string): void {
    if (filterState.enabledSourceFiles.has(sourceFile)) {
      filterState.enabledSourceFiles.delete(sourceFile)
    } else {
      filterState.enabledSourceFiles.add(sourceFile)
    }
  }

  // Enable all source files
  function enableAllSourceFiles(): void {
    filterState.enabledSourceFiles = new Set(processedData.value.sourceFiles)
  }

  // Disable all source files
  function disableAllSourceFiles(): void {
    filterState.enabledSourceFiles = new Set()
  }

  // Set a single source file (solo mode)
  function soloSourceFile(sourceFile: string): void {
    filterState.enabledSourceFiles = new Set([sourceFile])
  }

  // Set the focused function for subgraph extraction
  function setFocusedFunction(leanName: string | null): void {
    filterState.focusedFunction = leanName
  }

  // Set the subgraph mode
  function setSubgraphMode(mode: SubgraphMode): void {
    filterState.subgraphMode = mode
  }

  // Set the subgraph depth
  function setSubgraphDepth(depth: number): void {
    filterState.subgraphDepth = Math.max(1, Math.min(10, depth))
  }

  // Extract subgraph around a function
  function extractSubgraph(
    nodeMap: Map<string, GraphNode>,
    focusedId: string,
    mode: SubgraphMode,
    depth: number
  ): Set<string> {
    const included = new Set<string>()

    if (!nodeMap.has(focusedId)) {
      return included
    }

    included.add(focusedId)

    // Collect dependencies (functions this one depends on)
    if (mode === 'dependencies' || mode === 'both') {
      collectConnected(nodeMap, focusedId, included, depth, 'dependencies')
    }

    // Collect dependents (functions that depend on this one)
    if (mode === 'dependents' || mode === 'both') {
      collectConnected(nodeMap, focusedId, included, depth, 'dependents')
    }

    return included
  }

  // Recursively collect connected nodes
  function collectConnected(
    nodeMap: Map<string, GraphNode>,
    nodeId: string,
    included: Set<string>,
    remainingDepth: number,
    direction: 'dependencies' | 'dependents'
  ): void {
    if (remainingDepth <= 0) return

    const node = nodeMap.get(nodeId)
    if (!node) return

    const connected = direction === 'dependencies' ? node.dependencies : node.dependents

    for (const connectedId of connected) {
      if (!included.has(connectedId) && nodeMap.has(connectedId)) {
        included.add(connectedId)
        collectConnected(nodeMap, connectedId, included, remainingDepth - 1, direction)
      }
    }
  }

  // Computed filtered data
  const filteredData = computed<FilteredGraphData>(() => {
    const { nodes, edges, nodeMap } = processedData.value
    const { enabledSourceFiles, focusedFunction, subgraphMode, subgraphDepth } = filterState

    let filteredNodes: GraphNode[]
    let isFiltered = false

    // Step 1: Filter by source file
    if (enabledSourceFiles.size < processedData.value.sourceFiles.length) {
      isFiltered = true
      filteredNodes = nodes.filter(node => {
        const file = node.sourceFile || 'unknown'
        return enabledSourceFiles.has(file)
      })
    } else {
      filteredNodes = [...nodes]
    }

    // Step 2: Extract subgraph if focused function is set
    if (focusedFunction && subgraphMode !== 'all') {
      isFiltered = true
      const subgraphNodeIds = extractSubgraph(
        nodeMap,
        focusedFunction,
        subgraphMode,
        subgraphDepth
      )

      // Filter to only include subgraph nodes (intersect with source file filter)
      const filteredNodeIds = new Set(filteredNodes.map(n => n.id))
      filteredNodes = filteredNodes.filter(node => subgraphNodeIds.has(node.id))
    }

    // Build set of visible node IDs for edge filtering
    const visibleNodeIds = new Set(filteredNodes.map(n => n.id))

    // Filter edges to only include those between visible nodes
    const filteredEdges = edges.filter(edge =>
      visibleNodeIds.has(edge.source) && visibleNodeIds.has(edge.target)
    )

    return {
      nodes: filteredNodes,
      edges: filteredEdges,
      isFiltered
    }
  })

  // Check if a source file is enabled
  function isSourceFileEnabled(sourceFile: string): boolean {
    return filterState.enabledSourceFiles.has(sourceFile)
  }

  // Get count of enabled source files
  const enabledCount = computed(() => filterState.enabledSourceFiles.size)
  const totalSourceFiles = computed(() => processedData.value.sourceFiles.length)

  return {
    filterState,
    filteredData,
    toggleSourceFile,
    enableAllSourceFiles,
    disableAllSourceFiles,
    soloSourceFile,
    setFocusedFunction,
    setSubgraphMode,
    setSubgraphDepth,
    isSourceFileEnabled,
    enabledCount,
    totalSourceFiles
  }
}

// Graph visualization types - framework-agnostic data structures

// ============ Node Types ============

export type NodeStatus = 'verified' | 'externally_verified' | 'specified' | 'none'

export interface GraphNode {
  id: string                      // lean_name
  label: string                   // short label (last component)
  fullLabel: string               // medium label (stripped prefix)
  sourceFile: string | null       // Rust source file path
  lines: string | null            // Line range (e.g., "L459-L473")
  status: NodeStatus
  fullyVerified: boolean
  specStatement: string | null
  specDocstring: string | null
  rustName: string | null
  rustSource: string | null         // actual Rust source code
  originalDependencies: string[]  // before transitive calculation
  dependencies: string[]          // after transitive calculation (visible deps only)
  dependents: string[]            // computed reverse deps (visible only)
  isTransitiveTarget: boolean     // has incoming transitive edges
}

export interface GraphEdge {
  id: string
  source: string
  target: string
  isTransitive: boolean           // true if created by collapsing hidden nodes
}

// ============ Grouping Types ============

export interface FileStats {
  sourceFile: string
  total: number
  verified: number
  fullyVerified: number
  specified: number
  notSpecified: number
  verificationPercentage: number
}

export interface FileGroup {
  id: string                      // unique group id
  label: string                   // display name (filename without path)
  sourceFile: string              // full source file path
  nodeIds: string[]               // lean_names of nodes in this group
  stats: FileStats
  color: string                   // border/highlight color
  collapsed: boolean              // whether group is collapsed
}

// ============ Processed Data ============

export interface ProcessedGraphData {
  nodes: GraphNode[]
  edges: GraphEdge[]
  nodeMap: Map<string, GraphNode>
  sourceFiles: string[]           // unique source files
  stats: GlobalStats
}

export interface GlobalStats {
  total: number
  verified: number
  fullyVerified: number
  specified: number
  notSpecified: number
  hiddenFiltered: number          // count of hidden functions filtered out
  bySourceFile: Map<string, FileStats>
}

// ============ Filter Types ============

export type SubgraphMode = 'all' | 'dependencies' | 'dependents' | 'both'

export interface FilterState {
  enabledSourceFiles: Set<string>
  focusedFunction: string | null
  subgraphMode: SubgraphMode
  subgraphDepth: number           // how many levels to traverse
}

export interface FilteredGraphData {
  nodes: GraphNode[]
  edges: GraphEdge[]
  isFiltered: boolean
}

// ============ Selection Types ============

export interface SelectionState {
  selectedNodes: Set<string>
  hoveredNode: string | null
  maxSelections: number
}

// ============ Style Types ============

export interface NodeStyle {
  backgroundColor: string
  borderColor: string
  borderWidth: number
  width: number
  height: number
  opacity: number
  labelVisible: boolean
}

export interface EdgeStyle {
  lineColor: string
  width: number
  opacity: number
  lineStyle: 'solid' | 'dashed'
  curveStyle: 'taxi' | 'bezier' | 'straight'
}

export interface GroupStyle {
  backgroundColor: string
  borderColor: string
  borderWidth: number
  borderStyle: 'solid' | 'dashed'
  padding: number
  labelPosition: 'top' | 'bottom'
  showStats: boolean
}

// ============ Layout Types ============

export type LayoutDirection = 'LEFT' | 'RIGHT' | 'DOWN' | 'UP'

export interface LayoutOptions {
  direction: LayoutDirection
  nodeSpacing: number
  layerSpacing: number
  groupPadding: number
  animate: boolean
}

// ============ Event Types ============

export interface NodeClickEvent {
  nodeId: string
  originalEvent: MouseEvent
  isCtrlKey: boolean
  isShiftKey: boolean
}

export interface NodeHoverEvent {
  nodeId: string | null
  position: { x: number; y: number } | null
}

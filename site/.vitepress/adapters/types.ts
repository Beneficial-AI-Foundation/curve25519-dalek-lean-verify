import type {
  GraphNode,
  GraphEdge,
  FileGroup,
  NodeStyle,
  EdgeStyle,
  GroupStyle,
  LayoutOptions,
  NodeClickEvent,
  NodeHoverEvent
} from '../types/graph'

/**
 * Interface for visualization adapters.
 * Implement this to add support for different graph libraries (Cytoscape, D3, Sigma, etc.)
 */
export interface IVisualizationAdapter {
  // ============ Lifecycle ============

  /**
   * Initialize the visualization in the given container
   */
  initialize(container: HTMLElement, options?: InitOptions): Promise<void>

  /**
   * Clean up resources
   */
  destroy(): void

  /**
   * Check if adapter is initialized
   */
  isInitialized(): boolean

  // ============ Data Management ============

  /**
   * Set the graph data (nodes and edges)
   * Replaces all existing data
   */
  setData(nodes: GraphNode[], edges: GraphEdge[]): void

  /**
   * Update specific nodes without full re-render
   */
  updateNodes(nodes: GraphNode[]): void

  /**
   * Set file grouping configuration
   */
  setGroups(groups: FileGroup[]): void

  /**
   * Show/hide group visual boxes
   */
  setGroupsVisible(visible: boolean): void

  // ============ Interaction Handlers ============

  /**
   * Register node click handler. Returns unsubscribe function.
   */
  onNodeClick(handler: (event: NodeClickEvent) => void): () => void

  /**
   * Register node hover handler. Returns unsubscribe function.
   */
  onNodeHover(handler: (event: NodeHoverEvent) => void): () => void

  /**
   * Register background click handler. Returns unsubscribe function.
   */
  onBackgroundClick(handler: () => void): () => void

  /**
   * Register group click handler. Returns unsubscribe function.
   */
  onGroupClick(handler: (groupId: string) => void): () => void

  /**
   * Register node double-click handler. Returns unsubscribe function.
   */
  onNodeDoubleClick(handler: (event: NodeClickEvent) => void): () => void

  // ============ View Control ============

  /**
   * Fit all visible elements in view
   */
  fitToView(padding?: number): void

  /**
   * Center view on specific node
   */
  centerOnNode(nodeId: string, zoom?: number): void

  /**
   * Animate to a position
   */
  animateTo(options: { center?: string; zoom?: number; duration?: number }): void

  /**
   * Get current viewport state
   */
  getViewport(): { zoom: number; pan: { x: number; y: number } }

  /**
   * Set viewport
   */
  setViewport(viewport: { zoom?: number; pan?: { x: number; y: number } }): void

  /**
   * Get node's position in screen coordinates
   */
  getNodeScreenPosition(nodeId: string): { x: number; y: number } | null

  // ============ Highlighting ============

  /**
   * Highlight nodes (selection style)
   */
  highlightNodes(nodeIds: string[]): void

  /**
   * Highlight node and its connections (hover style)
   */
  highlightConnections(nodeId: string): void

  /**
   * Fade non-relevant elements
   */
  fadeElements(excludeNodeIds: string[]): void

  /**
   * Reset all highlighting
   */
  resetHighlight(): void

  // ============ Layout ============

  /**
   * Set and run a specific layout type
   */
  setLayout(layoutType: string): Promise<void>

  /**
   * Run layout algorithm
   */
  runLayout(options?: Partial<LayoutOptions>): Promise<void>

  /**
   * Get available layout algorithms
   */
  getAvailableLayouts(): string[]

  // ============ Styling ============

  /**
   * Apply dark/light theme
   */
  setTheme(dark: boolean): void

  /**
   * Update node style
   */
  setNodeStyle(nodeId: string, style: Partial<NodeStyle>): void

  /**
   * Update edge style
   */
  setEdgeStyle(edgeId: string, style: Partial<EdgeStyle>): void

  /**
   * Update group style
   */
  setGroupStyle(groupId: string, style: Partial<GroupStyle>): void

  // ============ Export ============

  /**
   * Export as PNG
   */
  exportPNG(options?: { scale?: number; backgroundColor?: string }): Promise<Blob>

  /**
   * Export as SVG
   */
  exportSVG(): string
}

/**
 * Options for adapter initialization
 */
export interface InitOptions {
  theme: 'light' | 'dark'
  minZoom: number
  maxZoom: number
}

/**
 * Default initialization options
 */
export const defaultInitOptions: InitOptions = {
  theme: 'light',
  minZoom: 0.1,
  maxZoom: 4
}

/**
 * Factory function to create visualization adapters
 */
export type AdapterType = 'cytoscape' | 'd3' | 'sigma'

export async function createVisualizationAdapter(
  type: AdapterType
): Promise<IVisualizationAdapter> {
  switch (type) {
    case 'cytoscape':
      const { CytoscapeAdapter } = await import('./CytoscapeAdapter')
      return new CytoscapeAdapter()
    case 'd3':
      throw new Error('D3 adapter not yet implemented')
    case 'sigma':
      throw new Error('Sigma adapter not yet implemented')
    default:
      throw new Error(`Unknown adapter type: ${type}`)
  }
}

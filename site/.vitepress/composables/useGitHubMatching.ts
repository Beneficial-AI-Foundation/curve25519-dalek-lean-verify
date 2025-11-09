import type { GitHubItem } from '../data/github.data'

/**
 * Composable for matching GitHub issues/PRs to function names
 *
 * Supports matching in multiple formats:
 * - Rust path: curve25519_dalek::backend::serial::u64::field::FieldElement51::from_bytes
 * - Lean notation: curve25519_dalek.backend.serial.u64.field.FieldElement51.from_bytes
 */
export function useGitHubMatching() {
  /**
   * Check if text contains the full function path in any supported notation
   */
  function containsFullPath(text: string, funcPath: string): boolean {
    if (!text) return false

    const lowerText = text.toLowerCase()
    const normalizedPath = funcPath.toLowerCase()

    // Normalize text: replace - with _, handle both :: and / and . separators
    const normalizedText = lowerText.replace(/-/g, '_')
    const searchPath = normalizedPath.replace(/-/g, '_')

    // Create variations of the search path to match different notations:
    // 1. Rust path: crate_name::backend::serial::u64::field::FieldElement51::from_bytes
    // 2. Lean dot notation: crate_name.backend.serial.u64.field.FieldElement51.from_bytes

    const rustPath = searchPath // already in :: format
    const dotPath = searchPath.replace(/::/g, '.')

    // Check if any variation appears with word boundaries
    const patterns = [
      // Rust notation with word boundaries
      new RegExp(`(^|[^a-zA-Z0-9_:.])${escapeRegex(rustPath)}($|[^a-zA-Z0-9_:.])`, 'i'),
      // Lean dot notation with word boundaries
      new RegExp(`(^|[^a-zA-Z0-9_.])${escapeRegex(dotPath)}($|[^a-zA-Z0-9_.])`, 'i')
    ]

    return patterns.some(pattern => pattern.test(normalizedText))
  }

  /**
   * Escape special regex characters
   */
  function escapeRegex(str: string): string {
    return str.replace(/[.*+?^${}()|[\]\\]/g, '\\$&')
  }

  /**
   * Find all GitHub items (issues/PRs) that match a given function name
   * Returns an array of matching items (can be multiple)
   *
   * Requires the FULL function path to match in one of the accepted formats.
   * This prevents false positives where function names are substrings of other functions.
   */
  function findItemsForFunction(functionName: string, items: GitHubItem[]): GitHubItem[] {
    // Use the full function name (including crate prefix) for matching
    const functionPath = functionName

    // Filter items that match the function - requires full path match
    const matches = items.filter(item => {
      // Only show open issues and open PRs (exclude closed/merged)
      if (item.state !== 'open') return false

      const title = item.title || ''
      const body = item.body || ''

      // Require matching the FULL function path in any accepted format
      return containsFullPath(title, functionPath) ||
             containsFullPath(body, functionPath)
    })

    return matches
  }

  return {
    findItemsForFunction
  }
}

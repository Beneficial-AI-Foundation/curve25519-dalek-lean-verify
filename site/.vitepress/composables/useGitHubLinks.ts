/**
 * Composable for generating GitHub links
 */

const BASE_URL = 'https://github.com/Beneficial-AI-Foundation/curve25519-dalek-lean-verify/blob/master'

export function useGitHubLinks() {
  /**
   * Generate GitHub URL for Rust source file
   */
  function getSourceLink(source: string, lines: string): string {
    if (!source) return ''

    const lineMatch = lines?.match(/L(\d+)(?:-L(\d+))?/)
    if (lineMatch) {
      const start = lineMatch[1]
      const end = lineMatch[2]
      const lineFragment = end ? `#L${start}-L${end}` : `#L${start}`
      return `${BASE_URL}/${source}${lineFragment}`
    }

    return `${BASE_URL}/${source}`
  }

  /**
   * Generate GitHub URL for Lean spec file
   */
  function getSpecLink(specPath: string): string {
    if (!specPath) return ''
    return `${BASE_URL}/${specPath}`
  }

  return {
    getSourceLink,
    getSpecLink
  }
}

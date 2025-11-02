import { createContentLoader } from 'vitepress'

export interface Issue {
  number: number
  title: string
  state: 'open' | 'closed'
  labels: string[]
  url: string
  created_at: string
  updated_at: string
  assignees: string[]
  body: string
  author: string
}

declare const data: Issue[]
export { data }

export default {
  async load(): Promise<Issue[]> {
    const owner = 'Beneficial-AI-Foundation'
    const repo = 'curve25519-dalek-lean-verify'
    const apiUrl = `https://api.github.com/repos/${owner}/${repo}/issues`

    try {
      // Add authentication token if available (for higher rate limits)
      const headers: HeadersInit = {
        'Accept': 'application/vnd.github.v3+json',
        'User-Agent': 'VitePress-Site'
      }

      if (process.env.GITHUB_TOKEN) {
        headers['Authorization'] = `Bearer ${process.env.GITHUB_TOKEN}`
      }

      const response = await fetch(apiUrl, {
        headers,
        // Don't cache - always fetch fresh data
        cache: 'no-store'
      })

      if (!response.ok) {
        console.error(`GitHub API error: ${response.status} ${response.statusText}`)
        return []
      }

      const issues = await response.json()

      // Transform GitHub API response to our Issue interface
      return issues.map((issue: any) => ({
        number: issue.number,
        title: issue.title,
        state: issue.state,
        labels: issue.labels.map((label: any) => label.name),
        url: issue.html_url,
        created_at: issue.created_at,
        updated_at: issue.updated_at,
        assignees: issue.assignees.map((assignee: any) => assignee.login),
        body: issue.body || '',
        author: issue.user?.login || 'unknown'
      }))

    } catch (error) {
      console.error('Failed to fetch GitHub issues:', error)
      return []
    }
  }
}

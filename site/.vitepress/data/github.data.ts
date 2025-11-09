import { createContentLoader } from 'vitepress'

export interface GitHubUser {
  login: string
  avatar_url: string
}

export interface GitHubItem {
  number: number
  title: string
  state: 'open' | 'closed' | 'merged'
  labels: string[]
  url: string
  created_at: string
  updated_at: string
  assignees: GitHubUser[]
  body: string
  author: GitHubUser
  type: 'issue' | 'pr'
  isDraft?: boolean
}

declare const data: GitHubItem[]
export { data }

async function fetchGitHubData(url: string, headers: HeadersInit): Promise<any[]> {
  const allData: any[] = []
  let page = 1
  const perPage = 100

  while (true) {
    const paginatedUrl = `${url}${url.includes('?') ? '&' : '?'}page=${page}&per_page=${perPage}`
    const response = await fetch(paginatedUrl, { headers, cache: 'no-store' })

    if (!response.ok) {
      console.error(`GitHub API error: ${response.status} ${response.statusText}`)
      break
    }

    const data = await response.json()
    if (data.length === 0) break

    allData.push(...data)

    // Check if there are more pages
    const linkHeader = response.headers.get('Link')
    if (!linkHeader || !linkHeader.includes('rel="next"')) break

    page++
  }

  return allData
}

export default {
  async load(): Promise<GitHubItem[]> {
    const owner = 'Beneficial-AI-Foundation'
    const repo = 'curve25519-dalek-lean-verify'

    console.log('Loading GitHub issue and PR data from GitHub...')

    try {
      // Add authentication token if available (for higher rate limits)
      const headers: HeadersInit = {
        'Accept': 'application/vnd.github.v3+json',
        'User-Agent': 'VitePress-Site'
      }

      if (process.env.GITHUB_TOKEN) {
        headers['Authorization'] = `Bearer ${process.env.GITHUB_TOKEN}`
      }

      // Fetch both issues and PRs
      // Note: GitHub API /issues endpoint includes PRs, but we'll fetch them separately for clarity
      const [issuesData, prsData] = await Promise.all([
        fetchGitHubData(`https://api.github.com/repos/${owner}/${repo}/issues?state=all`, headers),
        fetchGitHubData(`https://api.github.com/repos/${owner}/${repo}/pulls?state=all`, headers)
      ])

      // Filter out PRs from issues (GitHub's /issues endpoint includes PRs)
      const issues = issuesData
        .filter((item: any) => !item.pull_request)
        .map((issue: any) => ({
          number: issue.number,
          title: issue.title,
          state: issue.state,
          labels: issue.labels.map((label: any) => label.name),
          url: issue.html_url,
          created_at: issue.created_at,
          updated_at: issue.updated_at,
          assignees: issue.assignees.map((assignee: any) => ({
            login: assignee.login,
            avatar_url: assignee.avatar_url
          })),
          body: issue.body || '',
          author: {
            login: issue.user?.login || 'unknown',
            avatar_url: issue.user?.avatar_url || ''
          },
          type: 'issue' as const
        }))

      // Process PRs
      const prs = prsData.map((pr: any) => ({
        number: pr.number,
        title: pr.title,
        state: pr.merged_at ? 'merged' : pr.state,
        labels: pr.labels.map((label: any) => label.name),
        url: pr.html_url,
        created_at: pr.created_at,
        updated_at: pr.updated_at,
        assignees: pr.assignees.map((assignee: any) => ({
          login: assignee.login,
          avatar_url: assignee.avatar_url
        })),
        body: pr.body || '',
        author: {
          login: pr.user?.login || 'unknown',
          avatar_url: pr.user?.avatar_url || ''
        },
        type: 'pr' as const,
        isDraft: pr.draft
      }))

      // Combine and sort by number (descending - most recent first)
      const allItems = [...issues, ...prs].sort((a, b) => b.number - a.number)

      console.log(`Loaded ${allItems.length} GitHub items (${issues.length} issues, ${prs.length} PRs)`)

      return allItems

    } catch (error) {
      console.error('Failed to fetch GitHub data:', error)
      return []
    }
  }
}

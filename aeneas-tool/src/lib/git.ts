import { run } from "./shell.js";

export async function clone(
  repo: string,
  dest: string,
  opts?: { commit?: string; branch?: string },
): Promise<void> {
  const cloneArgs = ["clone"];
  if (opts?.branch) cloneArgs.push("--branch", opts.branch);
  cloneArgs.push(repo, dest);
  await run("git", cloneArgs, { label: `Cloning ${repo}...` });

  if (opts?.commit) {
    await run("git", ["checkout", opts.commit], {
      cwd: dest,
      label: `Checking out ${opts.commit.substring(0, 8)}...`,
    });
  }
}

export async function fetch(dir: string): Promise<void> {
  await run("git", ["fetch", "origin"], {
    cwd: dir,
    label: "Fetching latest...",
  });
}

export async function checkout(dir: string, ref: string): Promise<void> {
  await run("git", ["checkout", ref], {
    cwd: dir,
    label: `Checking out ${ref.substring(0, 8)}...`,
  });
}

export async function lsRemoteBranches(repo: string): Promise<string[]> {
  const output = await run("git", ["ls-remote", "--heads", repo], {
    label: "Fetching branches...",
  });
  return output
    .split("\n")
    .filter(Boolean)
    .map((line) => line.replace(/.*refs\/heads\//, ""));
}

export async function log(
  dir: string,
  opts?: { count?: number; format?: string; ref?: string },
): Promise<string> {
  const args = ["log"];
  if (opts?.count) args.push(`-${opts.count}`);
  if (opts?.format) args.push(`--format=${opts.format}`);
  if (opts?.ref) args.push(opts.ref);
  return run("git", args, { cwd: dir, silent: true });
}

export interface CommitInfo {
  hash: string;
  shortHash: string;
  date: string;
  subject: string;
}

export async function commitInfo(dir: string): Promise<CommitInfo> {
  const output = await run(
    "git",
    ["log", "-1", "--format=%H%n%h%n%cd%n%s", "--date=short"],
    { cwd: dir, silent: true },
  );
  const lines = output.split("\n");
  return {
    hash: lines[0] ?? "",
    shortHash: lines[1] ?? "",
    date: lines[2] ?? "",
    subject: lines[3] ?? "",
  };
}

import { execa, type Options as ExecaOptions } from "execa";
import ora from "ora";
import fs from "node:fs";
import path from "node:path";
import { AeneasToolError } from "./errors.js";

export interface RunOptions {
  cwd?: string;
  env?: Record<string, string>;
  label?: string;
  logFile?: string;
  silent?: boolean;
}

export async function run(
  cmd: string,
  args: string[],
  opts?: RunOptions,
): Promise<string> {
  const spinner =
    opts?.label && !opts?.silent ? ora(opts.label).start() : null;

  const execaOpts: ExecaOptions = {
    cwd: opts?.cwd,
    env: opts?.env ? { ...process.env, ...opts.env } : undefined,
    reject: false,
  };

  try {
    const result = await execa(cmd, args, execaOpts);

    const output = [result.stdout, result.stderr].filter(Boolean).join("\n");

    if (opts?.logFile) {
      const logDir = path.dirname(opts.logFile);
      fs.mkdirSync(logDir, { recursive: true });
      fs.writeFileSync(opts.logFile, output, "utf-8");
    }

    if (result.exitCode !== 0) {
      spinner?.fail();
      throw new AeneasToolError(
        `Command failed: ${cmd} ${args.join(" ")}\n${result.stderr || result.stdout}`,
        { hint: opts?.logFile ? `See log: ${opts.logFile}` : undefined },
      );
    }

    spinner?.succeed();
    return String(result.stdout ?? "");
  } catch (err) {
    spinner?.fail();
    if (err instanceof AeneasToolError) throw err;
    throw new AeneasToolError(`Failed to execute: ${cmd}`, {
      cause: err as Error,
    });
  }
}

export async function runStreaming(
  cmd: string,
  args: string[],
  opts?: RunOptions,
): Promise<void> {
  const execaOpts: ExecaOptions = {
    cwd: opts?.cwd,
    env: opts?.env ? { ...process.env, ...opts.env } : undefined,
    reject: false,
    stdout: "pipe",
    stderr: "pipe",
  };

  const result = await execa(cmd, args, execaOpts);

  const output = [result.stdout, result.stderr].filter(Boolean).join("\n");

  if (opts?.logFile) {
    const logDir = path.dirname(opts.logFile);
    fs.mkdirSync(logDir, { recursive: true });
    fs.writeFileSync(opts.logFile, output, "utf-8");
  }

  // Print output to console
  if (result.stdout) process.stdout.write(result.stdout + "\n");
  if (result.stderr) process.stderr.write(result.stderr + "\n");

  if (result.exitCode !== 0) {
    throw new AeneasToolError(
      `Command failed: ${cmd} ${args.join(" ")}`,
      { hint: opts?.logFile ? `See log: ${opts.logFile}` : undefined },
    );
  }
}

export async function which(name: string): Promise<string | null> {
  try {
    const result = await execa("which", [name], { reject: false });
    return result.exitCode === 0 ? result.stdout.trim() : null;
  } catch {
    return null;
  }
}

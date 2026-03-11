import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { select } from "@inquirer/prompts";
import {
  type AeneasConfig,
  updateConfigCommit,
  findLakefileAeneasRev,
  updateLakefileRev,
} from "../config.js";
import { getAeneasDir, getAeneasRepoDir } from "../lib/paths.js";
import * as git from "../lib/git.js";
import { installCommand } from "./install.js";

export async function updateCommand(
  config: AeneasConfig,
  root: string,
): Promise<void> {
  console.log(chalk.bold("\n=== Update Aeneas ===\n"));

  // Step 1: List remote branches
  const branches = await git.lsRemoteBranches(config.aeneas.repo);

  if (branches.length === 0) {
    console.log(chalk.red("No branches found on remote"));
    return;
  }

  // Put 'main' first if it exists
  branches.sort((a, b) => {
    if (a === "main") return -1;
    if (b === "main") return 1;
    return a.localeCompare(b);
  });

  const branch = await select({
    message: "Select branch:",
    choices: branches.map((b) => ({ name: b, value: b })),
  });

  // Step 2: Fetch and show recent commits on that branch
  const repoDir = getAeneasRepoDir(root);
  const aeneasDir = getAeneasDir(root);

  // We need a local repo to view commits. Clone if not exists
  if (!fs.existsSync(repoDir)) {
    fs.mkdirSync(aeneasDir, { recursive: true });
    await git.clone(config.aeneas.repo, repoDir);
  } else {
    await git.fetch(repoDir);
  }

  // Get recent commits on the selected branch
  const logOutput = await git.log(repoDir, {
    count: 20,
    format: "%H %h %ci %s",
    ref: `origin/${branch}`,
  });

  const commits = logOutput
    .split("\n")
    .filter(Boolean)
    .map((line) => {
      const [hash, shortHash, date, _time, _tz, ...rest] = line.split(" ");
      return {
        hash,
        shortHash,
        date,
        subject: rest.join(" "),
      };
    });

  if (commits.length === 0) {
    console.log(chalk.red("No commits found on branch"));
    return;
  }

  const selectedHash = await select({
    message: "Select commit:",
    choices: commits.map((c) => ({
      name: `${c.shortHash} ${c.date} ${c.subject}`,
      value: c.hash,
    })),
  });

  // Step 3: Update config
  const configPath = path.join(root, "aeneas-config.yml");
  updateConfigCommit(configPath, selectedHash);
  console.log(chalk.green(`  ✓ Updated aeneas-config.yml to ${selectedHash.substring(0, 8)}`));

  // Step 3b: Update lakefile.toml if it has an aeneas rev
  const lakefile = findLakefileAeneasRev(root);
  if (lakefile && lakefile.currentRev !== selectedHash) {
    const updateLakefile = await select({
      message: `Update lakefile.toml rev? (currently ${lakefile.currentRev.substring(0, 8)})`,
      choices: [
        { name: "Yes", value: true },
        { name: "No", value: false },
      ],
    });
    if (updateLakefile) {
      updateLakefileRev(lakefile.filePath, selectedHash);
      console.log(chalk.green(`  ✓ Updated lakefile.toml rev to ${selectedHash.substring(0, 8)}`));
    }
  }
  console.log();

  // Step 4: Ask to install
  const doInstall = await select({
    message: "Install now?",
    choices: [
      { name: "Yes", value: true },
      { name: "No", value: false },
    ],
  });

  if (doInstall) {
    // Reload config with new commit
    config.aeneas.commit = selectedHash;
    await installCommand(config, root);
  }
}

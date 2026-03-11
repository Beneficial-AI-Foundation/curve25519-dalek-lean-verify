import fs from "node:fs";
import chalk from "chalk";
import { select } from "@inquirer/prompts";
import { type AeneasConfig } from "./config.js";
import { getAeneasRepoDir } from "./lib/paths.js";
import * as git from "./lib/git.js";
import { statusCommand } from "./commands/status.js";
import { extractCommand } from "./commands/extract.js";
import { installCommand } from "./commands/install.js";
import { updateCommand } from "./commands/update.js";

async function showHeader(
  config: AeneasConfig,
  root: string,
): Promise<void> {
  const repoDir = getAeneasRepoDir(root);
  const localInstall = fs.existsSync(repoDir);

  let shortHash = config.aeneas.commit.substring(0, 7);
  let date = "";
  let subject = "";

  if (localInstall) {
    try {
      const info = await git.commitInfo(repoDir);
      shortHash = info.shortHash;
      date = info.date;
      subject = info.subject;
      if (subject.length > 40) subject = subject.substring(0, 40) + "...";
    } catch {
      // fall back to config
    }
  }

  const source = localInstall ? ".aeneas/ (local)" : "not installed";
  const parts = [chalk.bold(`Aeneas ${shortHash}`)];
  if (date) parts.push(date);
  if (subject) parts.push(`"${subject}"`);
  parts.push(source);

  console.log(parts.join(" · "));
  console.log();
}

export async function showMenu(
  config: AeneasConfig,
  root: string,
): Promise<void> {
  while (true) {
    await showHeader(config, root);

    const action = await select({
      message: "What would you like to do?",
      choices: [
        { name: "Extract to Lean", value: "extract" },
        { name: "Install Aeneas locally", value: "install" },
        { name: "Update Aeneas", value: "update" },
        { name: "Show status", value: "status" },
        { name: "Exit", value: "exit" },
      ],
    });

    switch (action) {
      case "extract":
        await extractCommand(config, root, { dryRun: false });
        break;
      case "install":
        await installCommand(config, root);
        break;
      case "update":
        await updateCommand(config, root);
        break;
      case "status":
        await statusCommand(config, root);
        break;
      case "exit":
        return;
    }

    console.log();
  }
}

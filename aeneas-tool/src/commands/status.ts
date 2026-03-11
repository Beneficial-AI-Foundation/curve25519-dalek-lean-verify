import fs from "node:fs";
import chalk from "chalk";
import { type AeneasConfig } from "../config.js";
import { getAeneasRepoDir, findBinary } from "../lib/paths.js";
import * as git from "../lib/git.js";

export async function statusCommand(
  config: AeneasConfig,
  root: string,
): Promise<void> {
  const repoDir = getAeneasRepoDir(root);
  const localInstall = fs.existsSync(repoDir);

  let info: git.CommitInfo | null = null;
  if (localInstall) {
    try {
      info = await git.commitInfo(repoDir);
    } catch {
      // repo exists but git info unavailable
    }
  }

  const charonBin = await findBinary("charon", root);
  const aeneasBin = await findBinary("aeneas", root);

  const shortHash = info?.shortHash ?? config.aeneas.commit.substring(0, 7);
  const date = info?.date ?? "not installed";
  const subject = info?.subject
    ? `"${info.subject.length > 40 ? info.subject.substring(0, 40) + "..." : info.subject}"`
    : "";
  const source = localInstall ? ".aeneas/ (local)" : charonBin ? "PATH" : "not found";

  console.log(
    chalk.bold(`Aeneas ${shortHash}`) +
      ` · ${date}` +
      (subject ? ` · ${subject}` : "") +
      ` · ${source}`,
  );
  console.log();
  console.log(`  Config commit: ${config.aeneas.commit}`);
  console.log(`  Repo:          ${config.aeneas.repo}`);
  console.log(`  Charon:        ${charonBin ?? chalk.red("not found")}`);
  console.log(`  Aeneas:        ${aeneasBin ?? chalk.red("not found")}`);
  console.log(`  Backend:       ${config.aeneas_args.backend}`);
  console.log(`  Extract from:  ${config.charon.start_from.length} modules`);
  console.log(`  Excludes:      ${config.charon.exclude.length} patterns`);
  console.log(`  Tweaks:        ${config.tweaks.substitutions.length} substitutions`);
}

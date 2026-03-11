import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { type AeneasConfig } from "../config.js";
import { getAeneasDir, getAeneasRepoDir, findBinary } from "../lib/paths.js";
import * as git from "../lib/git.js";
import * as build from "../lib/build.js";

export async function installCommand(
  config: AeneasConfig,
  root: string,
): Promise<void> {
  console.log(chalk.bold("\n=== Installing Aeneas ===\n"));

  // Step 1: Check dependencies
  console.log(chalk.bold("Step 1: Checking dependencies..."));
  await build.checkDependencies();
  console.log(chalk.green("  ✓ All dependencies found\n"));

  // Step 2: Setup OCaml
  console.log(chalk.bold("Step 2: Setting up OCaml..."));
  const opamEnv = await build.setupOcaml();
  console.log(chalk.green("  ✓ OCaml environment ready\n"));

  // Step 3: Install OCaml deps
  console.log(chalk.bold("Step 3: Installing OCaml dependencies..."));
  await build.installOcamlDeps(opamEnv);
  console.log(chalk.green("  ✓ OCaml dependencies installed\n"));

  // Step 4: Clone/update aeneas repo
  console.log(chalk.bold("Step 4: Setting up Aeneas repository..."));
  const aeneasDir = getAeneasDir(root);
  const repoDir = getAeneasRepoDir(root);

  fs.mkdirSync(aeneasDir, { recursive: true });

  if (fs.existsSync(repoDir)) {
    console.log("  Updating existing repository...");
    await git.fetch(repoDir);
    await git.checkout(repoDir, config.aeneas.commit);
  } else {
    await git.clone(config.aeneas.repo, repoDir, {
      commit: config.aeneas.commit,
    });
  }
  console.log(chalk.green(`  ✓ Aeneas at ${config.aeneas.commit.substring(0, 8)}\n`));

  // Step 5: Setup Rust toolchain for Charon
  console.log(chalk.bold("Step 5: Setting up Rust toolchain..."));
  const charonDir = path.join(repoDir, "charon");
  await build.setupRustToolchain(charonDir);
  console.log(chalk.green("  ✓ Rust toolchain ready\n"));

  // Step 6: Build Charon
  console.log(chalk.bold("Step 6: Building Charon..."));
  await build.buildCharon(repoDir, opamEnv);
  console.log(chalk.green("  ✓ Charon built\n"));

  // Step 7: Build Aeneas
  console.log(chalk.bold("Step 7: Building Aeneas..."));
  await build.buildAeneas(repoDir, opamEnv);
  console.log(chalk.green("  ✓ Aeneas built\n"));

  // Verify
  const charonBin = await findBinary("charon", root);
  const aeneasBin = await findBinary("aeneas", root);

  if (!charonBin || !aeneasBin) {
    console.log(
      chalk.red("  ⚠ Build completed but binaries not found at expected paths"),
    );
  } else {
    console.log(chalk.bold.green("=== Installation complete! ==="));
    console.log(`  Charon: ${charonBin}`);
    console.log(`  Aeneas: ${aeneasBin}`);
  }
}

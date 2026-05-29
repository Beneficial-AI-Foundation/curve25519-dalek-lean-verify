/**
 * Run the full extraction pipeline: Charon -> Aeneas -> Tweaks.
 *
 * Charon reads start_from / exclude / opaque natively from
 * [package.metadata.charon] in curve25519-dalek/Cargo.toml (Charon PR #1104).
 * This script only passes preset, package, and cargo_args as CLI flags.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { loadConfig } from "./lib/config.js";
import { findBinary } from "./lib/paths.js";
import { runStreaming } from "./lib/shell.js";
import { applyTweaks, warnUnmatchedTweaks } from "./lib/tweaks.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Extract\n"));

  const { config, root } = loadConfig();

  // Resolve binaries
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);

  if (!charonBin) {
    throw new Error("Charon binary not found. Run 'npm run aeneas-install' first.");
  }
  if (!aeneasBin) {
    throw new Error("Aeneas binary not found. Run 'npm run aeneas-install' first.");
  }

  // Charon reads [package.metadata.charon] from ./Cargo.toml in its cwd,
  // but always outputs the LLBC to the workspace root regardless of cwd.
  const crateDir = path.join(root, config.crate.dir);
  const llbcFile = `${config.crate.name}.llbc`;
  const llbcPath = path.join(root, llbcFile); // charon outputs to workspace root
  const destDir = path.join(root, config.aeneas_args.dest);
  const logsDir = path.join(root, ".logs");

  // ── Step 1: Charon ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 1: Generating LLBC with Charon..."));

  const charonArgs: string[] = ["cargo"];

  if (config.charon.preset) charonArgs.push(`--preset=${config.charon.preset}`);

  // Running from the crate directory, so --package is not needed.
  // Cargo args (feature flags etc.) go after --
  if (config.charon.cargo_args.length > 0) {
    charonArgs.push("--", ...config.charon.cargo_args);
  }

  // Remove stale LLBC
  if (fs.existsSync(llbcPath)) {
    fs.unlinkSync(llbcPath);
  }

  fs.mkdirSync(logsDir, { recursive: true });

  await runStreaming(charonBin, charonArgs, {
    cwd: crateDir,  // read [package.metadata.charon] from crate's Cargo.toml
    logFile: path.join(logsDir, "charon.log"),
  });

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Failed to generate ${llbcFile}`);
  }
  console.log(chalk.green(`  LLBC generated: ${llbcFile}\n`));

  // ── Step 2: Aeneas ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 2: Generating Lean files with Aeneas..."));

  const aeneasArgs: string[] = [
    "-backend", "lean",  // we only ever target the Lean backend
    ...config.aeneas_args.options.map((o) => `-${o}`),
    "-dest", destDir,
    llbcPath,  // absolute path since aeneas runs from root, LLBC is in crateDir
  ];

  fs.mkdirSync(destDir, { recursive: true });

  // Aeneas may exit non-zero while still producing output (known errors like
  // "join of nested borrows not supported" or internal errors on certain
  // constructs are non-fatal for our codebase).  We check for the output
  // files explicitly rather than relying solely on the exit code.
  try {
    await runStreaming(aeneasBin, aeneasArgs, {
      cwd: root,
      logFile: path.join(logsDir, "aeneas.log"),
    });
  } catch {
    // Check if output files were generated despite the error
    const missingFiles = config.tweaks.files.filter(
      (f) => !fs.existsSync(path.join(destDir, f)),
    );
    if (missingFiles.length > 0) {
      throw new Error(
        `Aeneas failed and did not generate: ${missingFiles.join(", ")}. See .logs/aeneas.log`,
      );
    }
    console.log(chalk.yellow("  Aeneas exited with errors but output files were generated (see .logs/aeneas.log)\n"));
  }

  console.log(chalk.green(`  Lean files generated in ${config.aeneas_args.dest}/\n`));

  // ── Step 3: Tweaks ──────────────────────────────────────────────────
  if (config.tweaks.substitutions.length > 0 && config.tweaks.files.length > 0) {
    console.log(chalk.bold("Step 3: Applying tweaks..."));

    const matchedPerFile: Set<number>[] = [];
    for (const file of config.tweaks.files) {
      const filePath = path.join(destDir, file);
      if (!fs.existsSync(filePath)) {
        console.log(chalk.yellow(`  Warning: File not found, skipping: ${file}`));
        continue;
      }
      const matched = applyTweaks(filePath, config.tweaks.substitutions);
      matchedPerFile.push(matched);
      console.log(chalk.green(`  Tweaks applied to ${file} (${matched.size} substitutions matched)`));
    }
    warnUnmatchedTweaks(config.tweaks.substitutions, matchedPerFile);
    console.log();
  }

  // ── Step 4: Lean toolchain sync ─────────────────────────────────────
  syncLeanToolchain(root);

  console.log(chalk.green("Done."));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});

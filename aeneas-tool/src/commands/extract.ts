import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { type AeneasConfig } from "../config.js";
import { findBinary } from "../lib/paths.js";
import { runStreaming } from "../lib/shell.js";
import { applyTweaks } from "../lib/tweaks.js";
import { ExtractionError } from "../lib/errors.js";

export async function extractCommand(
  config: AeneasConfig,
  root: string,
  opts: { dryRun?: boolean },
): Promise<void> {
  // Resolve binaries (allow missing for dry-run)
  const charonBin = await findBinary("charon", root);
  const aeneasBin = await findBinary("aeneas", root);

  if (!opts.dryRun) {
    if (!charonBin) {
      throw new ExtractionError("Charon binary not found", {
        hint: "Run 'aeneas-tool install' first",
      });
    }
    if (!aeneasBin) {
      throw new ExtractionError("Aeneas binary not found", {
        hint: "Run 'aeneas-tool install' first",
      });
    }
  }

  const llbcFile = `${config.crate.name}.llbc`;
  const outputDir = path.join(root, config.aeneas_args.dest);
  const logsDir = path.join(root, ".logs");

  // Build charon args
  const charonArgs: string[] = ["cargo", `--preset=${config.charon.preset}`];

  for (const item of config.charon.start_from) {
    charonArgs.push("--start-from", item);
  }
  for (const item of config.charon.exclude) {
    charonArgs.push("--exclude", item);
  }
  for (const item of config.charon.opaque) {
    charonArgs.push("--opaque", item);
  }

  charonArgs.push("--", "-p", config.crate.dir, ...config.charon.cargo_args);

  // Build aeneas args
  const aeneasArgs: string[] = [
    `-backend`,
    config.aeneas_args.backend,
    ...config.aeneas_args.options.map((o) => `-${o}`),
    `-dest`,
    outputDir,
    llbcFile,
  ];

  if (opts.dryRun) {
    console.log(chalk.bold("Dry run — commands that would be executed:\n"));
    console.log(chalk.cyan("Charon:"));
    console.log(`  ${charonBin ?? "charon"} ${charonArgs.join(" ")}\n`);
    console.log(chalk.cyan("Aeneas:"));
    console.log(`  ${aeneasBin ?? "aeneas"} ${aeneasArgs.join(" ")}\n`);

    if (config.tweaks.substitutions.length > 0) {
      console.log(chalk.cyan("Tweaks:"));
      console.log(
        `  ${config.tweaks.substitutions.length} substitutions on: ${config.tweaks.files.join(", ")}\n`,
      );
    }
    return;
  }

  // Step 1: Run Charon
  console.log(chalk.bold("\nStep 1: Generating LLBC with Charon..."));

  // Remove existing LLBC
  const llbcPath = path.join(root, llbcFile);
  if (fs.existsSync(llbcPath)) {
    fs.unlinkSync(llbcPath);
  }

  fs.mkdirSync(logsDir, { recursive: true });

  await runStreaming(charonBin!, charonArgs, {
    cwd: root,
    logFile: path.join(logsDir, "charon.log"),
  });

  if (!fs.existsSync(llbcPath)) {
    throw new ExtractionError(`Failed to generate ${llbcFile}`);
  }
  console.log(chalk.green(`  ✓ LLBC generated: ${llbcFile}`));

  // Step 2: Run Aeneas
  console.log(chalk.bold("\nStep 2: Generating Lean files with Aeneas..."));

  fs.mkdirSync(outputDir, { recursive: true });

  await runStreaming(aeneasBin!, aeneasArgs, {
    cwd: root,
    logFile: path.join(logsDir, "aeneas.log"),
  });

  console.log(chalk.green(`  ✓ Lean files generated in ${config.aeneas_args.dest}/`));

  // Step 3: Apply tweaks
  if (config.tweaks.substitutions.length > 0 && config.tweaks.files.length > 0) {
    console.log(chalk.bold("\nStep 3: Applying tweaks..."));

    for (const file of config.tweaks.files) {
      const filePath = path.join(outputDir, file);
      if (!fs.existsSync(filePath)) {
        console.log(chalk.yellow(`  ⚠ File not found, skipping: ${file}`));
        continue;
      }
      applyTweaks(filePath, config.tweaks.substitutions);
      console.log(chalk.green(`  ✓ Tweaks applied to ${file}`));
    }
  }

  // Step 4: Sync lean toolchain
  syncLeanToolchain(root);

  console.log(chalk.bold.green("\n=== Extraction complete! ===\n"));
}

function syncLeanToolchain(root: string): void {
  const projectToolchain = path.join(root, "lean-toolchain");
  const aeneasToolchain = path.join(
    root,
    ".aeneas",
    "aeneas",
    "backends",
    "lean",
    "lean-toolchain",
  );

  if (!fs.existsSync(aeneasToolchain)) return;
  if (!fs.existsSync(projectToolchain)) return;

  const projectVersion = fs.readFileSync(projectToolchain, "utf-8").trim();
  const aeneasVersion = fs.readFileSync(aeneasToolchain, "utf-8").trim();

  if (projectVersion !== aeneasVersion) {
    console.log(
      chalk.bold("\nSyncing Lean toolchain:"),
      `${projectVersion} → ${aeneasVersion}`,
    );
    fs.writeFileSync(projectToolchain, aeneasVersion + "\n", "utf-8");
    console.log(chalk.green("  ✓ lean-toolchain updated"));
  }
}

import { Command } from "commander";
import chalk from "chalk";
import { loadConfig } from "./config.js";
import { AeneasToolError } from "./lib/errors.js";
import { statusCommand } from "./commands/status.js";
import { extractCommand } from "./commands/extract.js";
import { installCommand } from "./commands/install.js";
import { updateCommand } from "./commands/update.js";
import { showMenu } from "./menu.js";

const program = new Command()
  .name("aeneas-tool")
  .description("CLI tool for Aeneas extraction to Lean")
  .version("0.1.0")
  .option("-c, --config <path>", "Path to aeneas-config.yml");

program
  .command("extract")
  .description("Run extraction pipeline (charon → aeneas → tweaks)")
  .option("--dry-run", "Print commands without executing")
  .action(async (opts) => {
    const { config, root } = loadConfig(program.opts().config);
    await extractCommand(config, root, { dryRun: opts.dryRun });
  });

program
  .command("install")
  .description("Clone and build Aeneas locally in .aeneas/")
  .action(async () => {
    const { config, root } = loadConfig(program.opts().config);
    await installCommand(config, root);
  });

program
  .command("update")
  .description("Interactive branch/commit picker + rebuild")
  .action(async () => {
    const { config, root } = loadConfig(program.opts().config);
    await updateCommand(config, root);
  });

program
  .command("status")
  .description("Show current Aeneas version and install info")
  .action(async () => {
    const { config, root } = loadConfig(program.opts().config);
    await statusCommand(config, root);
  });

// Default action: interactive menu
program.action(async () => {
  const { config, root } = loadConfig(program.opts().config);
  await showMenu(config, root);
});

async function main(): Promise<void> {
  try {
    await program.parseAsync();
  } catch (err) {
    if (err instanceof AeneasToolError) {
      console.error(chalk.red(`\nError: ${err.message}`));
      if (err.hint) {
        console.error(chalk.yellow(`Hint: ${err.hint}`));
      }
      process.exit(1);
    }
    // Handle Ctrl+C gracefully
    if (
      err instanceof Error &&
      (err.message.includes("User force closed") ||
        err.message.includes("ExitPromptError"))
    ) {
      console.log("\nBye!");
      process.exit(0);
    }
    throw err;
  }
}

main();

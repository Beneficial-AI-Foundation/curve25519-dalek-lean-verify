import fs from "node:fs";
import path from "node:path";
import { run, which } from "./shell.js";
import { DependencyError } from "./errors.js";

export async function checkDependencies(): Promise<void> {
  const deps = ["git", "opam", "make"];
  const missing: string[] = [];

  for (const dep of deps) {
    if (!(await which(dep))) {
      missing.push(dep);
    }
  }

  // Check for rustup or nix
  const hasRustup = await which("rustup");
  const hasNix = await which("nix");
  if (!hasRustup && !hasNix) {
    missing.push("rustup (or nix)");
  }

  if (missing.length > 0) {
    throw new DependencyError(
      `Missing dependencies: ${missing.join(", ")}`,
      { hint: "Install the missing tools and try again" },
    );
  }
}

export async function getOpamEnv(
  switchName: string,
): Promise<Record<string, string>> {
  const output = await run(
    "opam",
    ["env", `--switch=${switchName}`, "--set-switch"],
    { silent: true },
  );

  const env: Record<string, string> = {};
  // Parse lines like: VAR='value'; export VAR;
  for (const line of output.split("\n")) {
    const match = line.match(/^(\w+)='([^']*)'; export \1;/);
    if (match) {
      env[match[1]] = match[2];
    }
  }
  return env;
}

export async function setupOcaml(): Promise<Record<string, string>> {
  const switchName = "5.2.0";

  // Check if switch exists
  const switches = await run("opam", ["switch", "list", "--short"], {
    silent: true,
  });
  const exists = switches.split("\n").some((s) => s.trim() === switchName);

  if (!exists) {
    await run("opam", ["switch", "create", switchName], {
      label: "Creating OCaml 5.2.0 switch...",
    });
  } else {
    console.log("  OCaml 5.2.0 switch already exists");
  }

  return getOpamEnv(switchName);
}

const OCAML_DEPS = [
  "ppx_deriving",
  "visitors",
  "easy_logging",
  "zarith",
  "yojson",
  "core_unix",
  "odoc",
  "ocamlgraph",
  "menhir",
  "ocamlformat",
  "unionFind",
  "domainslib",
  "progress",
];

export async function installOcamlDeps(
  env: Record<string, string>,
): Promise<void> {
  await run("opam", ["update"], {
    env,
    label: "Updating opam packages...",
  });
  await run("opam", ["install", "-y", ...OCAML_DEPS], {
    env,
    label: "Installing OCaml dependencies...",
  });
}

function parseToolchainChannel(filePath: string): string | null {
  if (!fs.existsSync(filePath)) return null;
  const content = fs.readFileSync(filePath, "utf-8");
  const match = content.match(/channel\s*=\s*"?([^"\s]+)"?/);
  return match ? match[1] : null;
}

async function installRustToolchain(toolchain: string): Promise<void> {
  await run("rustup", ["toolchain", "install", toolchain], {
    label: `Installing Rust toolchain ${toolchain}...`,
  });
  await run(
    "rustup",
    ["component", "add", "--toolchain", toolchain, "rustfmt"],
    { label: "Adding rustfmt component..." },
  );
}

export async function setupRustToolchain(charonDir: string): Promise<void> {
  const toolchain =
    parseToolchainChannel(path.join(charonDir, "charon", "rust-toolchain.toml")) ??
    parseToolchainChannel(path.join(charonDir, "charon", "rust-toolchain")) ??
    "nightly";

  await installRustToolchain(toolchain);
}

export async function buildCharon(
  aeneasDir: string,
  env: Record<string, string>,
): Promise<void> {
  await run("make", ["setup-charon"], {
    cwd: aeneasDir,
    env,
    label: "Building Charon (this may take a few minutes)...",
  });
}

export async function buildAeneas(
  aeneasDir: string,
  env: Record<string, string>,
): Promise<void> {
  await run("make", [], {
    cwd: aeneasDir,
    env,
    label: "Building Aeneas...",
  });
}

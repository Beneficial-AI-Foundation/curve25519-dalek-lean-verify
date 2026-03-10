import fs from "node:fs";
import path from "node:path";
import { run, which } from "./shell.js";
import { DependencyError, BuildError } from "./errors.js";

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

export async function setupRustToolchain(charonDir: string): Promise<void> {
  // Look for rust-toolchain.toml
  const toolchainToml = path.join(charonDir, "charon", "rust-toolchain.toml");
  const toolchainFile = path.join(charonDir, "charon", "rust-toolchain");

  let nightlyVersion: string | null = null;

  if (fs.existsSync(toolchainToml)) {
    const content = fs.readFileSync(toolchainToml, "utf-8");
    const match = content.match(/channel\s*=\s*"([^"]+)"/);
    if (match) nightlyVersion = match[1];
  } else if (fs.existsSync(toolchainFile)) {
    const content = fs.readFileSync(toolchainFile, "utf-8");
    const match = content.match(/channel\s*=\s*"([^"]+)"/);
    if (match) nightlyVersion = match[1];
  }

  if (nightlyVersion) {
    await run("rustup", ["toolchain", "install", nightlyVersion], {
      label: `Installing Rust toolchain ${nightlyVersion}...`,
    });
    await run(
      "rustup",
      ["component", "add", "--toolchain", nightlyVersion, "rustfmt"],
      { label: "Adding rustfmt component..." },
    );
  } else {
    await run("rustup", ["toolchain", "install", "nightly"], {
      label: "Installing Rust nightly (no specific version found)...",
    });
    await run(
      "rustup",
      ["component", "add", "--toolchain", "nightly", "rustfmt"],
      { label: "Adding rustfmt component..." },
    );
  }
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

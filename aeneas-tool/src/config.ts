import fs from "node:fs";
import path from "node:path";
import yaml from "js-yaml";
import { getProjectRoot } from "./lib/paths.js";
import { ConfigError } from "./lib/errors.js";

export interface AeneasConfig {
  aeneas: {
    commit: string;
    repo: string;
  };
  charon: {
    preset: string;
    cargo_args: string[];
    start_from: string[];
    exclude: string[];
    opaque: string[];
  };
  aeneas_args: {
    backend: string;
    options: string[];
    dest: string;
  };
  crate: {
    dir: string;
    name: string;
  };
  tweaks: {
    files: string[];
    substitutions: Array<{
      find: string;
      replace: string;
    }>;
  };
}

export function loadConfig(configPath?: string): {
  config: AeneasConfig;
  root: string;
} {
  let root: string;
  let filePath: string;

  if (configPath) {
    filePath = path.resolve(configPath);
    root = path.dirname(filePath);
  } else {
    root = getProjectRoot();
    filePath = path.join(root, "aeneas-config.yml");
  }

  if (!fs.existsSync(filePath)) {
    throw new ConfigError(`Config file not found: ${filePath}`);
  }

  let raw: unknown;
  try {
    raw = yaml.load(fs.readFileSync(filePath, "utf-8"));
  } catch (err) {
    throw new ConfigError("Failed to parse aeneas-config.yml", {
      cause: err as Error,
    });
  }

  if (!raw || typeof raw !== "object") {
    throw new ConfigError("aeneas-config.yml is empty or invalid");
  }

  const config = raw as AeneasConfig;

  // Validate required fields
  if (!config.aeneas?.commit) {
    throw new ConfigError("Missing required field: aeneas.commit");
  }
  if (!config.aeneas?.repo) {
    throw new ConfigError("Missing required field: aeneas.repo");
  }
  if (!config.charon?.start_from?.length) {
    throw new ConfigError("Missing required field: charon.start_from");
  }
  if (!config.aeneas_args?.backend) {
    throw new ConfigError("Missing required field: aeneas_args.backend");
  }
  if (!config.crate?.dir) {
    throw new ConfigError("Missing required field: crate.dir");
  }

  // Apply defaults
  config.charon.preset = config.charon.preset ?? "aeneas";
  config.charon.cargo_args = config.charon.cargo_args ?? [];
  config.charon.exclude = config.charon.exclude ?? [];
  config.charon.opaque = config.charon.opaque ?? [];
  config.aeneas_args.options = config.aeneas_args.options ?? [];
  config.aeneas_args.dest = config.aeneas_args.dest ?? "output";
  config.crate.name =
    config.crate.name ?? config.crate.dir.replace(/-/g, "_");
  config.tweaks = config.tweaks ?? { files: [], substitutions: [] };
  config.tweaks.files = config.tweaks.files ?? [];
  config.tweaks.substitutions = config.tweaks.substitutions ?? [];

  return { config, root };
}

export function updateConfigCommit(
  configPath: string,
  newCommit: string,
): void {
  let content = fs.readFileSync(configPath, "utf-8");
  content = content.replace(
    /^(\s*commit:\s*)["']?[a-f0-9]+["']?/m,
    `$1"${newCommit}"`,
  );
  fs.writeFileSync(configPath, content, "utf-8");
}

/**
 * Find lakefile.toml in root and check if it has an aeneas require with a rev field.
 * Returns the file path and current rev, or null if not found.
 */
export function findLakefileAeneasRev(
  root: string,
): { filePath: string; currentRev: string } | null {
  const lakefilePath = path.join(root, "lakefile.toml");
  if (!fs.existsSync(lakefilePath)) return null;

  const content = fs.readFileSync(lakefilePath, "utf-8");

  // Match a [[require]] block with name = "aeneas" and a rev field
  const match = content.match(
    /\[\[require\]\][^[]*?name\s*=\s*"aeneas"[^[]*?rev\s*=\s*"([a-f0-9]+)"/s,
  );
  if (!match) return null;

  return { filePath: lakefilePath, currentRev: match[1] };
}

export function updateLakefileRev(
  filePath: string,
  newRev: string,
): void {
  let content = fs.readFileSync(filePath, "utf-8");

  // Replace rev inside the aeneas [[require]] block
  content = content.replace(
    /(\[\[require\]\][^[]*?name\s*=\s*"aeneas"[^[]*?rev\s*=\s*")([a-f0-9]+)(")/s,
    `$1${newRev}$3`,
  );
  fs.writeFileSync(filePath, content, "utf-8");
}

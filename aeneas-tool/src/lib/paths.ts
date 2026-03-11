import path from "node:path";
import fs from "node:fs";
import { ConfigError } from "./errors.js";
import { which } from "./shell.js";

const CONFIG_FILENAME = "aeneas-config.yml";

export function getProjectRoot(from?: string): string {
  let dir = from ?? process.cwd();
  while (true) {
    if (fs.existsSync(path.join(dir, CONFIG_FILENAME))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new ConfigError(
        `Could not find ${CONFIG_FILENAME} in any parent directory`,
        { hint: `Create ${CONFIG_FILENAME} in your project root` },
      );
    }
    dir = parent;
  }
}

export function getAeneasDir(root: string): string {
  return path.join(root, ".aeneas");
}

export function getAeneasRepoDir(root: string): string {
  return path.join(getAeneasDir(root), "aeneas");
}

export async function findBinary(
  name: "charon" | "aeneas",
  root: string,
): Promise<string | null> {
  const repoDir = getAeneasRepoDir(root);

  // Check local .aeneas/ install first
  const localPaths =
    name === "charon"
      ? [path.join(repoDir, "charon", "bin", "charon")]
      : [path.join(repoDir, "bin", "aeneas")];

  for (const p of localPaths) {
    if (fs.existsSync(p)) return p;
  }

  // Fall back to PATH
  return which(name);
}

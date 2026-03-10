import fs from "node:fs";
import chalk from "chalk";

export interface Substitution {
  find?: string;
  find_regex?: string;
  replace: string;
}

/**
 * Apply substitutions to a single file.
 * Returns a Set of substitution indices that matched in this file.
 */
export function applyTweaks(
  filePath: string,
  substitutions: Substitution[],
): Set<number> {
  let content = fs.readFileSync(filePath, "utf-8");
  const matched = new Set<number>();

  for (let i = 0; i < substitutions.length; i++) {
    const sub = substitutions[i];

    if (sub.find !== undefined) {
      if (!content.includes(sub.find)) continue;
      matched.add(i);
      content = content.replaceAll(sub.find, sub.replace);
    } else if (sub.find_regex !== undefined) {
      const regex = new RegExp(sub.find_regex, "gs");
      if (!regex.test(content)) continue;
      matched.add(i);
      regex.lastIndex = 0;
      content = content.replace(regex, sub.replace);
    }
  }

  fs.writeFileSync(filePath, content, "utf-8");
  return matched;
}

/**
 * Warn about substitutions that were not found in any file.
 */
export function warnUnmatchedTweaks(
  substitutions: Substitution[],
  matchedPerFile: Set<number>[],
): void {
  const allMatched = new Set<number>();
  for (const s of matchedPerFile) {
    for (const i of s) allMatched.add(i);
  }

  const unmatched: string[] = [];
  for (let i = 0; i < substitutions.length; i++) {
    if (allMatched.has(i)) continue;
    const sub = substitutions[i];
    const pattern = sub.find ?? sub.find_regex ?? "";
    const preview =
      pattern.length > 60 ? pattern.substring(0, 60) + "..." : pattern;
    const kind = sub.find !== undefined ? "literal" : "regex";
    unmatched.push(`Substitution #${i + 1} (${kind}) not found in any file: "${preview}"`);
  }

  if (unmatched.length > 0) {
    console.log(chalk.yellow("\n  Tweak warnings:"));
    for (const w of unmatched) {
      console.log(chalk.yellow(`    ⚠ ${w}`));
    }
  }
}

import fs from "node:fs";
import chalk from "chalk";

export interface Substitution {
  find?: string;
  find_regex?: string;
  replace: string;
}

export function applyTweaks(
  filePath: string,
  substitutions: Substitution[],
): void {
  let content = fs.readFileSync(filePath, "utf-8");
  const warnings: string[] = [];

  for (let i = 0; i < substitutions.length; i++) {
    const sub = substitutions[i];

    if (sub.find !== undefined) {
      // Literal find/replace
      if (!content.includes(sub.find)) {
        const preview =
          sub.find.length > 60
            ? sub.find.substring(0, 60) + "..."
            : sub.find;
        warnings.push(
          `Substitution #${i + 1} (literal) not found: "${preview}"`,
        );
        continue;
      }
      const before = content;
      content = content.replaceAll(sub.find, sub.replace);
      const count = (before.length - content.length + sub.replace.length * countOccurrences(before, sub.find)) / (sub.find.length);
      // Simpler: just count how many times it was replaced
      void count;
    } else if (sub.find_regex !== undefined) {
      // Regex find/replace
      const regex = new RegExp(sub.find_regex, "gs");
      if (!regex.test(content)) {
        const preview =
          sub.find_regex.length > 60
            ? sub.find_regex.substring(0, 60) + "..."
            : sub.find_regex;
        warnings.push(
          `Substitution #${i + 1} (regex) not found: "${preview}"`,
        );
        continue;
      }
      // Reset lastIndex after test
      regex.lastIndex = 0;
      content = content.replace(regex, sub.replace);
    }
  }

  fs.writeFileSync(filePath, content, "utf-8");

  if (warnings.length > 0) {
    console.log(chalk.yellow(`\n  Warnings for ${filePath}:`));
    for (const w of warnings) {
      console.log(chalk.yellow(`    ⚠ ${w}`));
    }
  }
}

function countOccurrences(str: string, sub: string): number {
  let count = 0;
  let pos = 0;
  while ((pos = str.indexOf(sub, pos)) !== -1) {
    count++;
    pos += sub.length;
  }
  return count;
}

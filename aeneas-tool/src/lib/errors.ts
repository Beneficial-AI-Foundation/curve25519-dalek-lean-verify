export class AeneasToolError extends Error {
  public hint?: string;

  constructor(message: string, options?: { cause?: Error; hint?: string }) {
    super(message, { cause: options?.cause });
    this.name = "AeneasToolError";
    this.hint = options?.hint;
  }
}

export class DependencyError extends AeneasToolError {
  constructor(message: string, options?: { cause?: Error; hint?: string }) {
    super(message, options);
    this.name = "DependencyError";
  }
}

export class ConfigError extends AeneasToolError {
  constructor(message: string, options?: { cause?: Error; hint?: string }) {
    super(message, options);
    this.name = "ConfigError";
  }
}

export class ExtractionError extends AeneasToolError {
  constructor(message: string, options?: { cause?: Error; hint?: string }) {
    super(message, options);
    this.name = "ExtractionError";
  }
}

import Foundation

// MARK: - Process Environment

/// Provides a minimal, sanitized environment for subprocess execution.
/// Avoids inheriting secrets, DYLD_* variables, or other sensitive parent environment.
enum ProcessEnvironment {
    /// Returns a minimal environment suitable for subprocess execution.
    /// Only includes PATH, HOME, TMPDIR, LANG, LC_ALL, and USER from the parent.
    static func minimal() -> [String: String] {
        let parentEnv = ProcessInfo.processInfo.environment
        var env: [String: String] = [:]
        let allowedKeys = ["PATH", "HOME", "TMPDIR", "LANG", "LC_ALL", "USER"]
        for key in allowedKeys {
            if let value = parentEnv[key] {
                env[key] = value
            }
        }
        // Ensure PATH has a reasonable fallback
        if env["PATH"] == nil {
            env["PATH"] = "/usr/local/bin:/usr/bin:/bin"
        }
        return env
    }
}

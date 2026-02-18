import Foundation
import os

/// Centralized logger factory to ensure consistent subsystem across the app.
enum Log {
    static let subsystem = Bundle.main.bundleIdentifier ?? "com.tlastudio.app"

    static func logger(category: String) -> Logger {
        Logger(subsystem: subsystem, category: category)
    }
}

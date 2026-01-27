import Foundation
import AppKit
import UserNotifications

// MARK: - Completion Notifier

/// Sends macOS notifications when long-running operations complete
final class CompletionNotifier {

    // MARK: - Singleton

    static let shared = CompletionNotifier()

    // MARK: - Properties

    private var isAuthorized = false

    // MARK: - Initialization

    private init() {
        requestAuthorization()
    }

    // MARK: - Authorization

    private func requestAuthorization() {
        UNUserNotificationCenter.current().requestAuthorization(options: [.alert, .sound]) { [weak self] granted, error in
            self?.isAuthorized = granted
            if let error = error {
                print("Notification authorization error: \(error)")
            }
        }
    }

    // MARK: - Public API

    /// Notify that TLC model checking has completed
    func notifyTLCComplete(success: Bool, moduleName: String, statesGenerated: Int?, duration: TimeInterval) {
        guard isAuthorized else { return }
        guard !NSApp.isActive else { return } // Don't notify if app is in foreground

        let content = UNMutableNotificationContent()
        content.title = success ? "Model Check Passed" : "Model Check Failed"

        var bodyParts: [String] = [moduleName]
        if let states = statesGenerated {
            bodyParts.append("\(formatNumber(states)) states")
        }
        bodyParts.append(formatDuration(duration))

        content.body = bodyParts.joined(separator: " - ")
        content.sound = success ? .default : UNNotificationSound.defaultCritical

        scheduleNotification(content: content, identifier: "tlc-complete")
    }

    /// Notify that TLAPM proof checking has completed
    func notifyProofComplete(success: Bool, moduleName: String, proved: Int, failed: Int, duration: TimeInterval) {
        guard isAuthorized else { return }
        guard !NSApp.isActive else { return }

        let content = UNMutableNotificationContent()

        if success {
            content.title = "All Proofs Verified"
            content.body = "\(moduleName) - \(proved) obligations proved in \(formatDuration(duration))"
        } else {
            content.title = "Proof Check Failed"
            content.body = "\(moduleName) - \(failed) failed, \(proved) proved in \(formatDuration(duration))"
        }

        content.sound = success ? .default : UNNotificationSound.defaultCritical

        scheduleNotification(content: content, identifier: "proof-complete")
    }

    /// Notify that PlusCal translation has completed
    func notifyPlusCalComplete(success: Bool, moduleName: String) {
        guard isAuthorized else { return }
        guard !NSApp.isActive else { return }

        let content = UNMutableNotificationContent()
        content.title = success ? "PlusCal Translation Complete" : "PlusCal Translation Failed"
        content.body = moduleName
        content.sound = .default

        scheduleNotification(content: content, identifier: "pluscal-complete")
    }

    // MARK: - Private Helpers

    private func scheduleNotification(content: UNMutableNotificationContent, identifier: String) {
        let request = UNNotificationRequest(
            identifier: identifier,
            content: content,
            trigger: nil // Deliver immediately
        )

        UNUserNotificationCenter.current().add(request) { error in
            if let error = error {
                print("Failed to schedule notification: \(error)")
            }
        }
    }

    private func formatDuration(_ duration: TimeInterval) -> String {
        if duration < 1 {
            return String(format: "%.0fms", duration * 1000)
        } else if duration < 60 {
            return String(format: "%.1fs", duration)
        } else if duration < 3600 {
            let minutes = Int(duration / 60)
            let seconds = Int(duration.truncatingRemainder(dividingBy: 60))
            return "\(minutes)m \(seconds)s"
        } else {
            let hours = Int(duration / 3600)
            let minutes = Int((duration.truncatingRemainder(dividingBy: 3600)) / 60)
            return "\(hours)h \(minutes)m"
        }
    }

    private func formatNumber(_ number: Int) -> String {
        let formatter = NumberFormatter()
        formatter.numberStyle = .decimal
        return formatter.string(from: NSNumber(value: number)) ?? "\(number)"
    }
}

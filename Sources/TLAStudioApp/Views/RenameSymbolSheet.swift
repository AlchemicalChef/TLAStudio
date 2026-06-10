import SwiftUI

/// Sheet for renaming a symbol across the current document: live validation,
/// non-blocking collision warnings, occurrence count.
struct RenameSymbolSheet: View {
    let plan: RenameService.Plan
    let symbols: [TLASymbol]
    let moduleName: String
    let onRename: (String) -> Void

    @Environment(\.dismiss) private var dismiss
    @State private var newName: String

    init(
        plan: RenameService.Plan,
        symbols: [TLASymbol],
        moduleName: String,
        onRename: @escaping (String) -> Void
    ) {
        self.plan = plan
        self.symbols = symbols
        self.moduleName = moduleName
        self.onRename = onRename
        self._newName = State(initialValue: plan.originalName)
    }

    private var validationError: TLAIdentifierValidator.ValidationError? {
        TLAIdentifierValidator.validate(newName, original: plan.originalName)
    }

    var body: some View {
        VStack(alignment: .leading, spacing: 10) {
            Text("Rename '\(plan.originalName)'")
                .font(.headline)

            TextField("New name", text: $newName)
                .textFieldStyle(.roundedBorder)
                .font(.system(.body, design: .monospaced))
                .onSubmit(confirm)

            if let error = validationError, error != .unchanged {
                Label(error.message, systemImage: "xmark.circle")
                    .font(.caption)
                    .foregroundColor(.red)
            }

            warnings

            Text("Renames \(plan.occurrences.count) occurrence\(plan.occurrences.count == 1 ? "" : "s") in module \(moduleName) (matches by name — same-named nested bindings rename too)")
                .font(.caption)
                .foregroundColor(.secondary)
                .fixedSize(horizontal: false, vertical: true)

            HStack {
                Spacer()
                Button("Cancel") { dismiss() }
                    .keyboardShortcut(.cancelAction)
                Button("Rename", action: confirm)
                    .keyboardShortcut(.defaultAction)
                    .disabled(validationError != nil)
            }
        }
        .padding(16)
        .frame(width: 420)
    }

    @ViewBuilder
    private var warnings: some View {
        if validationError == nil {
            if let collision = RenameService.collision(newName: newName, in: symbols) {
                warningLabel("A \(kindName(collision.kind)) named '\(newName)' already exists in this module")
            }
            if RenameService.shadowsBuiltin(newName) {
                warningLabel("'\(newName)' shadows a TLA+ builtin or standard-library operator")
            }
        }
        if let external = plan.externalDefinition {
            warningLabel("Defined in module \(external.moduleName) (\(external.fileURL.lastPathComponent)) — only this document will be changed")
        }
        if plan.originalName == moduleName {
            warningLabel("Renaming the module: the file name must match the module name for TLC")
        }
    }

    private func warningLabel(_ text: String) -> some View {
        Label(text, systemImage: "exclamationmark.triangle")
            .font(.caption)
            .foregroundColor(.orange)
            .fixedSize(horizontal: false, vertical: true)
    }

    private func confirm() {
        guard validationError == nil else { return }
        onRename(newName)
        dismiss()
    }

    private func kindName(_ kind: TLASymbolKind) -> String {
        switch kind {
        case .module: return "module"
        case .operator: return "operator"
        case .variable: return "variable"
        case .constant: return "constant"
        case .theorem: return "theorem"
        case .definition: return "definition"
        case .instance: return "instance"
        case .assumption: return "assumption"
        }
    }
}

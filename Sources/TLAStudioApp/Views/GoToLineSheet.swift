import SwiftUI

// MARK: - Go to Line Sheet

/// A sheet that allows the user to navigate to a specific line number
struct GoToLineSheet: View {
    @Binding var isPresented: Bool
    @State private var lineNumberText: String = ""
    @FocusState private var isTextFieldFocused: Bool

    let totalLines: Int
    let onNavigate: (Int) -> Void

    var body: some View {
        VStack(spacing: 16) {
            // Header
            Text("Go to Line")
                .font(.headline)

            // Line number input
            HStack {
                Text("Line:")
                    .foregroundColor(.secondary)

                TextField("1-\(totalLines)", text: $lineNumberText)
                    .textFieldStyle(.roundedBorder)
                    .frame(width: 120)
                    .focused($isTextFieldFocused)
                    .onSubmit { navigate() }
                    .onChange(of: lineNumberText) { _, newValue in
                        // Filter to only allow digits
                        let filtered = newValue.filter { $0.isNumber }
                        if filtered != newValue {
                            lineNumberText = filtered
                        }
                    }
            }

            // Valid range hint
            if !lineNumberText.isEmpty, let lineNum = Int(lineNumberText) {
                if lineNum < 1 || lineNum > totalLines {
                    Text("Line number must be between 1 and \(totalLines)")
                        .font(.caption)
                        .foregroundColor(.red)
                }
            }

            // Buttons
            HStack(spacing: 12) {
                Button("Cancel") {
                    isPresented = false
                }
                .keyboardShortcut(.cancelAction)

                Button("Go") {
                    navigate()
                }
                .keyboardShortcut(.defaultAction)
                .disabled(!isValidLineNumber)
            }
        }
        .padding(20)
        .frame(minWidth: 250)
        .onAppear {
            isTextFieldFocused = true
        }
    }

    // MARK: - Private

    private var isValidLineNumber: Bool {
        guard let lineNum = Int(lineNumberText) else { return false }
        return lineNum >= 1 && lineNum <= totalLines
    }

    private func navigate() {
        guard let lineNum = Int(lineNumberText),
              lineNum >= 1, lineNum <= totalLines else {
            return
        }

        onNavigate(lineNum)
        isPresented = false
    }
}

// MARK: - Preview

#if DEBUG
struct GoToLineSheet_Previews: PreviewProvider {
    static var previews: some View {
        GoToLineSheet(
            isPresented: .constant(true),
            totalLines: 150
        ) { lineNumber in
            print("Navigate to line \(lineNumber)")
        }
    }
}
#endif

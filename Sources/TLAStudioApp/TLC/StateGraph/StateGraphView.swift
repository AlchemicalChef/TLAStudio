import SwiftUI
import WebKit

// MARK: - State Graph View

/// SwiftUI view for displaying error trace as an interactive graph
struct StateGraphView: View {
    let trace: ErrorTrace

    @State private var configuration = DOTGenerator.Configuration()
    @State private var graphData: Data?
    @State private var isLoading = false
    @State private var error: Error?
    @State private var graphvizAvailable: Bool?
    @State private var showExportSheet = false
    @State private var currentRenderTask: Task<Void, Never>?

    var body: some View {
        VStack(spacing: 0) {
            // Toolbar
            toolbar

            Divider()

            // Content
            content
        }
        .task {
            await checkGraphvizAndRender()
        }
        .sheet(isPresented: $showExportSheet) {
            ExportGraphSheet(trace: trace, configuration: configuration)
        }
        .onDisappear {
            // Cancel any pending render when view disappears
            currentRenderTask?.cancel()
        }
    }

    // MARK: - Toolbar

    var toolbar: some View {
        HStack {
            // Direction picker
            Picker("Direction", selection: $configuration.direction) {
                ForEach(DOTGenerator.Configuration.Direction.allCases, id: \.self) { direction in
                    Text(direction.displayName).tag(direction)
                }
            }
            .pickerStyle(.menu)
            .frame(width: 150)
            .onChange(of: configuration.direction) { _, _ in
                startNewRenderTask()
            }

            // Show variables toggle
            Toggle("Variables", isOn: $configuration.showVariables)
                .toggleStyle(.checkbox)
                .onChange(of: configuration.showVariables) { _, _ in
                    startNewRenderTask()
                }

            Spacer()

            // Refresh button
            Button {
                startNewRenderTask()
            } label: {
                Image(systemName: "arrow.clockwise")
            }
            .help("Refresh Graph")
            .disabled(isLoading)

            // Export button
            Button {
                showExportSheet = true
            } label: {
                Image(systemName: "square.and.arrow.up")
            }
            .help("Export Graph")
            .disabled(graphData == nil)
        }
        .padding(8)
        .background(Color(NSColor.controlBackgroundColor))
    }

    // MARK: - Content

    @ViewBuilder
    var content: some View {
        if let available = graphvizAvailable {
            if !available {
                graphvizNotInstalledView
            } else if isLoading {
                loadingView
            } else if let error = error {
                errorView(error)
            } else if let data = graphData {
                SVGWebView(svgData: data)
            } else {
                loadingView
            }
        } else {
            loadingView
        }
    }

    var loadingView: some View {
        VStack(spacing: 16) {
            ProgressView()
            Text("Rendering graph...")
                .foregroundColor(.secondary)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    func errorView(_ error: Error) -> some View {
        VStack(spacing: 16) {
            Image(systemName: "exclamationmark.triangle")
                .font(.largeTitle)
                .foregroundColor(.orange)

            Text("Failed to render graph")
                .font(.headline)

            Text(error.localizedDescription)
                .font(.callout)
                .foregroundColor(.secondary)
                .multilineTextAlignment(.center)
                .padding(.horizontal)

            Button("Try Again") {
                startNewRenderTask()
            }
            .buttonStyle(.bordered)
        }
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    var graphvizNotInstalledView: some View {
        VStack(spacing: 16) {
            Image(systemName: "exclamationmark.triangle")
                .font(.system(size: 48))
                .foregroundColor(.orange)

            Text("Graphviz Not Installed")
                .font(.headline)

            Text(GraphvizProcessManager.installationInstructions)
                .font(.system(.body, design: .monospaced))
                .foregroundColor(.secondary)
                .multilineTextAlignment(.leading)
                .padding()
                .background(Color(NSColor.textBackgroundColor))
                .cornerRadius(8)

            HStack {
                Button("Copy Install Command") {
                    NSPasteboard.general.clearContents()
                    NSPasteboard.general.setString("brew install graphviz", forType: .string)
                }
                .buttonStyle(.bordered)

                Button("Check Again") {
                    Task { await checkGraphvizAndRender() }
                }
                .buttonStyle(.borderedProminent)
            }
        }
        .padding()
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    // MARK: - Actions

    /// Cancel any existing render task and start a new one
    private func startNewRenderTask() {
        currentRenderTask?.cancel()
        currentRenderTask = Task {
            await renderGraph()
        }
    }

    private func checkGraphvizAndRender() async {
        let available = await GraphvizProcessManager.shared.isGraphvizAvailable
        await MainActor.run {
            graphvizAvailable = available
        }

        if available {
            await renderGraph()
        }
    }

    private func renderGraph() async {
        await MainActor.run {
            isLoading = true
            error = nil
        }

        do {
            let data = try await GraphvizProcessManager.shared.render(
                trace: trace,
                format: .svg,
                configuration: configuration
            )

            // Check if task was cancelled before updating UI
            guard !Task.isCancelled else { return }

            await MainActor.run {
                self.graphData = data
                self.isLoading = false
            }
        } catch {
            // Check if task was cancelled before updating UI with error
            guard !Task.isCancelled else { return }

            await MainActor.run {
                self.error = error
                self.isLoading = false
            }
        }
    }
}

// MARK: - SVG Web View

/// NSViewRepresentable wrapper for WKWebView to display SVG
struct SVGWebView: NSViewRepresentable {
    let svgData: Data

    func makeNSView(context: Context) -> WKWebView {
        let configuration = WKWebViewConfiguration()
        configuration.preferences.setValue(true, forKey: "developerExtrasEnabled")

        let webView = WKWebView(frame: .zero, configuration: configuration)
        webView.setValue(false, forKey: "drawsBackground")
        return webView
    }

    func updateNSView(_ webView: WKWebView, context: Context) {
        guard let svgString = String(data: svgData, encoding: .utf8) else { return }

        // Wrap SVG in HTML with zoom controls
        let html = """
        <!DOCTYPE html>
        <html>
        <head>
            <meta charset="utf-8">
            <style>
                * { margin: 0; padding: 0; box-sizing: border-box; }
                html, body {
                    width: 100%;
                    height: 100%;
                    overflow: auto;
                    background: transparent;
                }
                .container {
                    display: flex;
                    justify-content: center;
                    align-items: flex-start;
                    min-height: 100%;
                    padding: 20px;
                }
                svg {
                    max-width: 100%;
                    height: auto;
                }
            </style>
        </head>
        <body>
            <div class="container">
                \(svgString)
            </div>
            <script>
                // Enable zoom with mouse wheel
                let scale = 1;
                const container = document.querySelector('.container');
                const svg = document.querySelector('svg');

                document.addEventListener('wheel', (e) => {
                    if (e.ctrlKey || e.metaKey) {
                        e.preventDefault();
                        scale += e.deltaY * -0.001;
                        scale = Math.min(Math.max(0.25, scale), 4);
                        if (svg) {
                            svg.style.transform = `scale(${scale})`;
                            svg.style.transformOrigin = 'center top';
                        }
                    }
                }, { passive: false });
            </script>
        </body>
        </html>
        """

        webView.loadHTMLString(html, baseURL: nil)
    }
}

// MARK: - Export Sheet

struct ExportGraphSheet: View {
    let trace: ErrorTrace
    let configuration: DOTGenerator.Configuration

    @Environment(\.dismiss) private var dismiss
    @State private var selectedFormat: GraphExportFormat = .svg
    @State private var isExporting = false
    @State private var exportError: Error?

    var body: some View {
        VStack(spacing: 20) {
            Text("Export Graph")
                .font(.headline)

            // Format picker
            Picker("Format", selection: $selectedFormat) {
                ForEach(GraphExportFormat.allCases, id: \.self) { format in
                    Text(format.displayName).tag(format)
                }
            }
            .pickerStyle(.radioGroup)

            if let error = exportError {
                Text(error.localizedDescription)
                    .foregroundColor(.red)
                    .font(.caption)
            }

            HStack {
                Button("Cancel") {
                    dismiss()
                }
                .keyboardShortcut(.escape)

                Spacer()

                Button("Export") {
                    Task { await exportGraph() }
                }
                .buttonStyle(.borderedProminent)
                .disabled(isExporting)
                .keyboardShortcut(.return)
            }
        }
        .padding()
        .frame(width: 300)
    }

    private func exportGraph() async {
        isExporting = true
        exportError = nil

        do {
            let data = try await GraphvizProcessManager.shared.render(
                trace: trace,
                format: selectedFormat,
                configuration: configuration
            )

            await MainActor.run {
                let panel = NSSavePanel()
                panel.allowedContentTypes = [.init(filenameExtension: selectedFormat.fileExtension) ?? .data]
                panel.nameFieldStringValue = "error_trace.\(selectedFormat.fileExtension)"

                if panel.runModal() == .OK, let url = panel.url {
                    do {
                        try data.write(to: url)
                        dismiss()
                    } catch {
                        exportError = error
                    }
                }
                isExporting = false
            }
        } catch {
            await MainActor.run {
                exportError = error
                isExporting = false
            }
        }
    }
}

// MARK: - Preview

#Preview {
    StateGraphView(trace: ErrorTrace(
        type: .invariantViolation,
        message: "Invariant TypeOK is violated",
        states: [
            TraceState(id: 0, action: nil, variables: ["x": .int(0), "y": .int(0)]),
            TraceState(id: 1, action: "Increment", variables: ["x": .int(1), "y": .int(0)]),
            TraceState(id: 2, action: "Decrement", variables: ["x": .int(1), "y": .int(-1)])
        ]
    ))
    .frame(width: 600, height: 400)
}

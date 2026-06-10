import XCTest
@testable import TLAStudioApp

/// Dot fixtures are verbatim captures from `tlc2.TLC -dump dot,actionlabels`
/// (TLC 2.20) against generated simulation modules.
final class SimulationOutputParsersTests: XCTestCase {

    // MARK: - Dot parsing

    func testParsesOriginAndLabeledSuccessors() {
        let dot = """
        strict digraph DiskGraph {
        node [shape=box,style=rounded]
        nodesep=0.35;
        subgraph cluster_graph {
        color="white";
        -1878848071080891435 [label="/\\\\ tlaStudioSimDepth = 0\\n/\\\\ x = 1\\n/\\\\ y = <<0>>",style = filled]
        -1878848071080891435 -> 9145219575526230694 [label="TLAStudioSimAction1",color="black",fontcolor="black"];
        9145219575526230694 [label="/\\\\ tlaStudioSimDepth = 1\\n/\\\\ x = 2\\n/\\\\ y = <<0>>",tooltip="…"];
        -1878848071080891435 -> 2423904052029680317 [label="TLAStudioSimAction2",color="black",fontcolor="black"];
        2423904052029680317 [label="/\\\\ tlaStudioSimDepth = 1\\n/\\\\ x = 1\\n/\\\\ y = <<0, 1>>",tooltip="…"];
        {rank = same; -1878848071080891435;}
        }
        }
        """

        let graph = SimulationDotParser.parse(
            dotText: dot,
            actionLabels: ["TLAStudioSimAction1": "Inc", "TLAStudioSimAction2": "Push"]
        )

        XCTAssertEqual(graph.origins.count, 1)
        XCTAssertFalse(graph.truncated)
        let origin = graph.origins[0]
        XCTAssertEqual(origin.variableNames, ["x", "y"])   // depth variable stripped
        XCTAssertEqual(origin.rawValue(of: "x"), "1")
        XCTAssertEqual(origin.rawValue(of: "y"), "<<0>>")

        XCTAssertEqual(graph.successors.count, 2)
        XCTAssertEqual(graph.successors[0].actionLabel, "Inc")
        XCTAssertEqual(graph.successors[0].state.rawValue(of: "x"), "2")
        XCTAssertEqual(graph.successors[1].actionLabel, "Push")
        XCTAssertEqual(graph.successors[1].state.rawValue(of: "y"), "<<0, 1>>")
    }

    func testUnescapesQuotedStringValues() {
        // A TLA+ string value with embedded quotes/backslashes, dot-escaped.
        let dot = #"""
        strict digraph DiskGraph {
        4696961472418532141 [label="/\\ tlaStudioSimDepth = 0\n/\\ s = \"say \\\"hi\\\" \\\\ there\"",style = filled]
        }
        """#

        let graph = SimulationDotParser.parse(dotText: dot, actionLabels: [:])
        XCTAssertEqual(graph.origins.count, 1)
        XCTAssertEqual(
            graph.origins[0].rawValue(of: "s"),
            #""say \"hi\" \\ there""#
        )
    }

    func testInitOnlyDumpHasNoSuccessors() {
        let dot = """
        strict digraph DiskGraph {
        1 [label="/\\\\ tlaStudioSimDepth = 0\\n/\\\\ x = 0",style = filled]
        2 [label="/\\\\ tlaStudioSimDepth = 0\\n/\\\\ x = 1",style = filled]
        }
        """
        let graph = SimulationDotParser.parse(dotText: dot, actionLabels: [:])
        XCTAssertEqual(graph.origins.count, 2)
        XCTAssertTrue(graph.successors.isEmpty)
    }

    func testIgnoresMalformedLines() {
        let graph = SimulationDotParser.parse(
            dotText: "digraph {\nnonsense\n}\n",
            actionLabels: [:]
        )
        XCTAssertTrue(graph.origins.isEmpty)
        XCTAssertTrue(graph.successors.isEmpty)
    }

    func testDuplicateEdgesAreDeduplicated() {
        let dot = """
        strict digraph DiskGraph {
        1 [label="/\\\\ tlaStudioSimDepth = 0\\n/\\\\ x = 0",style = filled]
        1 -> 2 [label="TLAStudioSimAction1",color="black"];
        1 -> 2 [label="TLAStudioSimAction1",color="black"];
        2 [label="/\\\\ tlaStudioSimDepth = 1\\n/\\\\ x = 1"];
        }
        """
        let graph = SimulationDotParser.parse(dotText: dot, actionLabels: [:])
        XCTAssertEqual(graph.successors.count, 1)
    }

    // MARK: - Eval parsing

    func testEvalParserExtractsValueBetweenMarkers() {
        let output = """
        Computing initial states...
        "TLASTUDIO_EVAL_BEGIN"
        11
        "TLASTUDIO_EVAL_END"
        Finished computing initial states: 1 distinct state generated.
        """
        XCTAssertEqual(SimulationEvalParser.parse(output: output), .success("11"))
    }

    func testEvalParserReportsTLCErrorWhenMarkersMissing() {
        let output = """
        Computing initial states...
        "TLASTUDIO_EVAL_BEGIN"
        Error: The first argument of Head should be a nonempty sequence, but instead it is:
        <<>>
        The error occurred when TLC was evaluating the nested
        """
        guard case .failure(.tlcFailed(let message)) = SimulationEvalParser.parse(output: output) else {
            return XCTFail("Expected tlcFailed")
        }
        XCTAssertTrue(message.contains("first argument of Head"))
        XCTAssertTrue(message.contains("<<>>"))
        XCTAssertFalse(message.contains("The error occurred"))
    }

    func testEvalParserHandlesAbsentOutput() {
        guard case .failure = SimulationEvalParser.parse(output: "") else {
            return XCTFail("Expected failure for empty output")
        }
    }

    // MARK: - Error extraction

    func testErrorExtractorReturnsNilWithoutErrors() {
        XCTAssertNil(SimulationTLCErrorExtractor.extract(from: "Model checking completed."))
    }

    func testErrorExtractorCollectsBlock() {
        let output = """
        Starting...
        Error: Invariant TypeOK is violated.
        The behavior up to this point is:
        State 1: x = 1
        """
        let message = SimulationTLCErrorExtractor.extract(from: output)
        XCTAssertEqual(message?.hasPrefix("Error: Invariant TypeOK"), true)
    }
}

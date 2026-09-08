# Preserved report-assembly encoding failure

The first report-generation invocation used the bundled Python executable with `-B evidence/prepare_final_report.py` from the workspace. The execution tool returned native shell exit code 1, chunk `cf6f8d`, and measured wall time 0.3362448 seconds. Its displayed diagnostic was a `UnicodeDecodeError` in the report-template `read_text()` call: the Windows `cp1252` decoder could not decode byte `0x9d` at position 8106. The original invocation was made directly through the execution tool; separate native start/end timestamps were not collected for that first presentation-only invocation.

The unchanged script is preserved as `prepare_final_report.encoding-failure.py`. Before repair, the same invocation was repeated under the bounded native logger, producing `report-assembly-encoding-failure.command.json`, separate raw stdout/stderr, and the combined display log. That actual repeated failure returned 1 and preserves the same diagnostic with complete timestamps. It is not relabelled as the initial invocation.

The repair explicitly decodes the UTF-8 Markdown template and JSON inputs as UTF-8. The report was also updated to disclose this failure. No mathematical source, proof, statement, dependency, checker, axiom allowlist or completed mathematical check was changed. The instrumented retry is recorded separately as `report-assembly-retry`.

The bounded runner's generic nonzero-process label reads `FAILED CHECK`; the semantic classification here is an incomplete report-generation step caused by text decoding, not a rejected Lean proof or kernel replay. The completed retry resolves that presentation-tool problem. The prior Git HEAD probe's expected exit 128 is separately explained in the report.

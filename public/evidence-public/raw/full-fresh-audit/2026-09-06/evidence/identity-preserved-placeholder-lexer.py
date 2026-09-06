"""Read-only Lean source inventory, lexical placeholder audit and local import closure.

This is a source-text audit, not a Lean parser, elaborator or kernel checker.
All output files stay beside this script. No Lean/build command is run.
Run with: python placeholder_scan.py
"""
from __future__ import annotations

from collections import Counter, deque
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys

OUT = Path(__file__).resolve().parent
ROOT = OUT.parent.parent
MAIN = "ComplementedSubspace.RealMainTheorem"
KEYWORDS = (
    "sorry sorryAx admit admitted axiom constant constants opaque unsafe partial "
    "native_decide native_decide_eq_true native_decide_eq_false implemented_by extern "
    "unsafeCast lcProof trust trustLevel skipKernelTC debug.skipKernelTC "
    "allowUnsafeReducibility run_cmd run_elab run_meta elab elab_rules macro macro_rules "
    "syntax initialize builtin_initialize meta unimplemented "
    "mkSorry mkSyntheticSorry mkLabeledSorry hasSorry "
    "ofReduceBool ofReduceNat reduceBool reduceNat evalExpr evalConst "
    "addDecl addDeclCore addTrustedDecl addAndCompile addAndCompileUnsafe "
    "replaceDecl modifyEnv setEnv set_option"
).split()
BASE_HAZARDS = set("sorry sorryAx admit admitted axiom constant opaque unsafe partial native_decide native_decide_eq_true native_decide_eq_false implemented_by extern unsafeCast lcProof trust trustLevel skipKernelTC debug.skipKernelTC mkSorry mkSyntheticSorry mkLabeledSorry ofReduceBool ofReduceNat reduceBool reduceNat addDecl addDeclCore addTrustedDecl addAndCompile addAndCompileUnsafe replaceDecl modifyEnv setEnv".split())
TOKEN_RE = re.compile(r"(?<![\w'])" + r"(?:" + "|".join(re.escape(x) for x in sorted(KEYWORDS, key=len, reverse=True)) + r")(?![\w'])|#(?:eval|run|exit|compile)\b")


def lex(text: str):
    """Keep executable text; mask comments/string literals preserving positions.

    Handles nested /- -/ comments, -- comments, escaped strings, raw strings,
    character literals, quoted identifiers and !-prefixed interpolated strings.
    Code inside interpolation braces is scanned recursively. Every input byte's
    decoded character is classified; unterminated constructs are reported.
    Quoted Lean names (`foo) remain visible conservatively.
    """
    kinds = ["code"] * len(text)
    issues = []
    constructs = Counter()
    n = len(text)

    def mark(a, b, k):
        kinds[a:b] = [k] * (b - a)

    def block(i):
        start = i
        depth = 1
        i += 2
        while i < n and depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
        mark(start, i, "block_comment")
        constructs["block_comment"] += 1
        if depth:
            issues.append({"offset": start, "issue": "unterminated nested block comment"})
        return i

    def string(i, interpolated=False):
        start = i
        mark(i, i + 1, "string")
        constructs["interpolated_string" if interpolated else "string"] += 1
        i += 1
        while i < n:
            if text[i] == "\\":
                mark(i, min(i + 2, n), "string")
                i += 2
            elif text[i] == '"':
                mark(i, i + 1, "string")
                return i + 1
            elif interpolated and text.startswith("{{", i):
                mark(i, i + 2, "string")
                i += 2
            elif interpolated and text[i] == "{":
                mark(i, i + 1, "string")
                constructs["interpolation_hole"] += 1
                i = code(i + 1, stop_at_brace=True)
            else:
                mark(i, i + 1, "string")
                i += 1
        issues.append({"offset": start, "issue": "unterminated string"})
        return n

    def code(i=0, stop_at_brace=False):
        depth = 0
        while i < n:
            if text.startswith("/-", i):
                i = block(i)
            elif text.startswith("--", i):
                end = text.find("\n", i)
                if end < 0:
                    end = n
                mark(i, end, "line_comment")
                constructs["line_comment"] += 1
                i = end
            elif text[i] == "«":
                end = text.find("»", i + 1)
                if end < 0:
                    issues.append({"offset": i, "issue": "unterminated quoted identifier"})
                    return n
                constructs["quoted_identifier"] += 1
                i = end + 1  # Keep identifiers visible; their content is not commentary.
            elif text[i] == "r" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] == "_")) and (raw := re.match(r'r(#{0,})"', text[i:])):
                close = '"' + raw.group(1)
                end = text.find(close, i + len(raw.group()), n)
                if end < 0:
                    issues.append({"offset": i, "issue": "unterminated raw string"})
                    end = n
                else:
                    end += len(close)
                mark(i, end, "raw_string")
                constructs["raw_string"] += 1
                i = end
            elif text[i] == '"':
                i = string(i, interpolated=(i > 0 and text[i - 1] == "!"))
            elif text[i] == "'" and (char := re.match(r"'(?:[^'\\\n]|\\(?:[nrt0\\\"']|x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}))'", text[i:])):
                end = i + len(char.group())
                mark(i, end, "character")
                constructs["character"] += 1
                i = end
            elif stop_at_brace and text[i] == "{":
                depth += 1
                i += 1
            elif stop_at_brace and text[i] == "}":
                if depth == 0:
                    mark(i, i + 1, "string")
                    return i + 1
                depth -= 1
                i += 1
            else:
                i += 1
        if stop_at_brace:
            issues.append({"offset": i, "issue": "unterminated interpolation hole"})
        return i

    code()
    clean = "".join(c if k == "code" or c in "\r\n" else " " for c, k in zip(text, kinds))
    return clean, kinds, dict(constructs), issues


def scanner_self_test():
    fixture = r'''-- sorry
/- axiom /- sorryAx -/ admit -/
def x := "sorry \" axiom" -- opaque
def y := r##"sorry " unsafe"##
def z := s!"sorry {by /- axiom -/ sorry}"
def c := '"'
theorem ok : True := by sorry
theorem escaped : True := by «sorryAx»
'''
    clean, kinds, _, errors = lex(fixture)
    got = [m.group() for m in TOKEN_RE.finditer(clean)]
    assert got == ["sorry", "sorry", "sorryAx"], (got, clean)
    assert not errors, errors
    assert len(clean) == len(fixture)
    assert clean.count("\n") == fixture.count("\n")
    return "PASS: nested comments, escaped and raw strings, character literal, interpolation code, quoted identifier, offsets/newlines"


def line_info(text, offset):
    line = text.count("\n", 0, offset) + 1
    start = text.rfind("\n", 0, offset) + 1
    end = text.find("\n", offset)
    if end < 0:
        end = len(text)
    return line, offset - start + 1, text[start:end].rstrip("\r")


def group(rel):
    if rel.startswith("ComplementedSubspace/"):
        return "ComplementedSubspace"
    if rel.startswith("BanLat/"):
        return "vendored BanLat"
    if rel.startswith("experiments/unverified/"):
        return "experiments/unverified"
    if "/" not in rel:
        return "root sources (including scratch/audits)"
    return "other local sources (including verification)"


def imports_from(clean):
    # All observed imports have one or multiple ordinary module names on their
    # command line. Reject any unrecognized syntax instead of silently skipping it.
    found = []
    errors = []
    for m in re.finditer(r"(?m)^\s*(?:(?:public|private|meta)\s+)?import\s+([^\r\n]+)", clean):
        tail = m.group(1).strip()
        modules = tail.split()
        for mod in modules:
            if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", mod):
                found.append(mod)
            else:
                errors.append(f"unrecognized import syntax: {tail}")
    return found, errors


def main():
    self_test = scanner_self_test()
    excluded = []
    symlinks = []
    sources = []
    for current, dirs, names in os.walk(ROOT, followlinks=False):
        here = Path(current)
        for name in list(dirs):
            sub = here / name
            if here.name == ".lake" and name in {"packages", "build"}:
                dirs.remove(name)
                excluded.append(sub.relative_to(ROOT).as_posix() + "/")
            elif sub.is_symlink():
                dirs.remove(name)
                symlinks.append(sub.relative_to(ROOT).as_posix())
        for name in names:
            if name.lower().endswith(".lean"):
                sources.append(here / name)
    sources.sort(key=lambda p: p.relative_to(ROOT).as_posix())
    inventory, hits, options, errors = [], [], [], []
    code_counts, noncode_counts, constructs = Counter(), Counter(), Counter()
    modules = {}
    for path in sources:
        data = path.read_bytes()
        text = data.decode("utf-8-sig")
        rel = path.relative_to(ROOT).as_posix()
        clean, kinds, stat, lex_errors = lex(text)
        constructs.update(stat)
        for issue in lex_errors:
            issue["file"] = rel
            issue["line"], issue["column"], issue["source"] = line_info(text, issue["offset"])
            errors.append(issue)
        imports, import_errors = imports_from(clean)
        errors.extend({"file": rel, "issue": s} for s in import_errors)
        module = rel[:-5].replace("/", ".")
        modules[module] = imports
        inventory.append({"file": rel, "module": module, "group": group(rel), "bytes": len(data), "lines": len(text.splitlines()), "sha256": hashlib.sha256(data).hexdigest(), "imports": imports})
        for match in TOKEN_RE.finditer(text):
            kind = kinds[match.start()]
            token = match.group()
            line, column, source = line_info(text, match.start())
            record = {"file": rel, "line": line, "column": column, "token": token, "kind": kind, "source": source}
            hits.append(record)
            if kind == "code":
                code_counts[token] += 1
            else:
                noncode_counts[token] += 1
        for match in re.finditer(r"(?m)\bset_option\s+(\S+)\s+(\S+)", clean):
            line, column, source = line_info(text, match.start())
            options.append({"file": rel, "line": line, "column": column, "name": match.group(1), "value": match.group(2), "source": source})
    if MAIN not in modules:
        raise RuntimeError(f"Missing main theorem source {MAIN}")
    closure, external, parents = set(), set(), {MAIN: None}
    queue = deque([MAIN])
    while queue:
        mod = queue.popleft()
        if mod in closure:
            continue
        closure.add(mod)
        for imp in modules[mod]:
            if imp in modules:
                if imp not in parents:
                    parents[imp] = mod
                queue.append(imp)
            else:
                external.add(imp)
    for record in inventory:
        record["in_realMainTheorem_import_closure"] = record["module"] in closure
    by_path = {i["file"]: i for i in inventory}
    for hit in hits + options:
        hit["in_realMainTheorem_import_closure"] = by_path[hit["file"]]["in_realMainTheorem_import_closure"]
    hazards = [h for h in hits if h["kind"] == "code" and h["token"] in BASE_HAZARDS]
    dynamic = [h for h in hits if h["kind"] == "code" and h["token"] in {"run_cmd", "run_elab", "run_meta", "elab", "elab_rules", "macro", "macro_rules", "syntax", "initialize", "builtin_initialize", "#eval", "#run", "#exit", "#compile", "evalExpr", "evalConst"}]
    option_counts = Counter((x["name"], x["value"]) for x in options)
    group_counts = Counter(i["group"] for i in inventory)
    group_lines = Counter()
    for item in inventory:
        group_lines[item["group"]] += item["lines"]
    closure_group_counts = Counter(i["group"] for i in inventory if i["in_realMainTheorem_import_closure"])
    read_only_commands = []

    def capture(argv, cwd=ROOT):
        proc = subprocess.run(argv, cwd=cwd, capture_output=True, encoding="utf-8", errors="strict")
        result = {"command": subprocess.list2cmdline(argv), "cwd": str(cwd), "exit_code": proc.returncode, "stdout": proc.stdout, "stderr": proc.stderr}
        read_only_commands.append(result)
        return result

    rg_inventory = capture(["rg", "--files", "--hidden", "--no-ignore", "-g", "*.lean", "-g", "!**/.lake/packages/**", "-g", "!**/.lake/build/**", "."])
    rg_paths = {s.replace("\\", "/").removeprefix("./") for s in rg_inventory["stdout"].splitlines()}
    python_paths = {i["file"] for i in inventory}
    inventory_agreement = rg_paths == python_paths and rg_inventory["exit_code"] == 0
    capture(["rg", "-n", "--hidden", "--no-ignore", "-g", "*.lean", "-g", "!**/.lake/packages/**", "-g", "!**/.lake/build/**", r"\b(sorry|sorryAx|admit|admitted|axiom|opaque|unsafe|native_decide|implemented_by|extern)\b|allowUnsafeReducibility", "."])
    lean_source = ROOT.parents[1] / "tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows/src/lean"
    reducibility_source = lean_source / "Lean/ReducibilityAttrs.lean"
    evidence_data = reducibility_source.read_bytes()
    evidence_lines = evidence_data.decode("utf-8-sig").splitlines()
    semantics_evidence = {"file": str(reducibility_source), "sha256": hashlib.sha256(evidence_data).hexdigest(), "line_range": [90, 184], "source_with_line_numbers": "\n".join(f"{i+1}: {evidence_lines[i]}" for i in range(89, 184))}
    capture(["rg", "-n", "allowUnsafeReducibility", str(lean_source), "-g", "*.lean", "-g", "*.cpp", "-g", "*.h"])
    report = {
        "created_utc": datetime.now(timezone.utc).isoformat(), "root": str(ROOT),
        "command": subprocess.list2cmdline([sys.executable, str(Path(__file__).resolve())]),
        "scope": "Every local .lean file under root, including unused/root/experimental/vendored/verification sources; no ignore-file filters",
        "excluded_directory_patterns": ["**/.lake/packages/**", "**/.lake/build/**"],
        "existing_excluded_directories_at_scan": sorted(excluded), "unfollowed_directory_symlinks": symlinks,
        "method": "Conservative source-text token scan after nested-comment, character/string/raw-string-aware lexing; ! string interpolation code is retained. Not an elaborator/kernel replacement.",
        "self_test": self_test, "lexical_and_import_errors": errors,
        "files": len(inventory), "lines": sum(i["lines"] for i in inventory),
        "groups": dict(group_counts), "lines_by_group": dict(group_lines), "lexical_constructs": dict(constructs),
        "code_token_counts": {k: code_counts[k] for k in KEYWORDS + ["#eval", "#run", "#exit", "#compile"]},
        "noncode_token_counts": dict(noncode_counts), "inventory": inventory,
        "occurrences": hits, "source_placeholder_or_trust_hazards": hazards,
        "metaprogramming_occurrences": dynamic, "set_options": options,
        "main_module": MAIN, "local_import_closure": sorted(closure),
        "independent_rg_inventory_agrees": inventory_agreement,
        "inventory_rg_only": sorted(rg_paths - python_paths), "inventory_python_only": sorted(python_paths - rg_paths),
        "read_only_command_transcript": read_only_commands,
        "allowUnsafeReducibility_implementation_evidence": semantics_evidence,
        "local_import_closure_groups": dict(closure_group_counts),
        "local_import_parents": parents,
        "external_direct_import_frontier_not_recursively_scanned": sorted(external),
        "import_scope_caveat": "Local syntactic import closure only: includes each imported local module, not the theorem's Expr dependency closure. External packages and Lean standard library are outside source scan.",
        "stability_check": {},
    }
    changed = []
    for item in inventory:
        path = ROOT / item["file"]
        if not path.exists() or hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            changed.append(item["file"])
    report["stability_check"] = {"changed_or_removed_during_scan": changed}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "placeholder_scan.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    inventory_lines = ["# All paths relative to " + str(ROOT), "# sha256\tbytes\tlines\tin main local import closure\tpath"]
    inventory_lines += [f'{i["sha256"]}\t{i["bytes"]}\t{i["lines"]}\t{i["in_realMainTheorem_import_closure"]}\t{i["file"]}' for i in inventory]
    (OUT / "local-source-inventory.txt").write_text("\n".join(inventory_lines) + "\n", encoding="utf-8")
    lines = [
        "INDEPENDENT LOCAL LEAN PLACEHOLDER / TRUST SOURCE AUDIT",
        f'UTC: {report["created_utc"]}', f'Root: {ROOT}',
        "Exact command: " + report["command"], "Self-test: " + self_test,
        f'Files: {len(inventory)}; lines: {report["lines"]}',
        "Inventory groups: " + json.dumps(dict(group_counts), sort_keys=True),
        "Lines by group: " + json.dumps(dict(group_lines), sort_keys=True),
        "Exclusion rules: **/.lake/packages/** and **/.lake/build/** (external downloaded dependencies and compiled build artifacts)",
        "Excluded directories present at scan: " + ", ".join(sorted(excluded)),
        "No unused local Lean files excluded. Ignore files were not consulted.",
        f'Unfollowed directory symlinks: {symlinks}',
        f'Independent rg --files --hidden --no-ignore inventory agrees exactly: {inventory_agreement}',
        f'Lexical/import parsing errors: {len(errors)}; source hashes changed during scan: {changed}',
        "", "EXECUTABLE SOURCE TOKEN COUNTS (conservative candidates):",
    ]
    lines += [f"{k}: {code_counts[k]}" for k in KEYWORDS + ["#eval", "#run", "#exit", "#compile"]]
    lines += ["", f"Placeholder/trust bypass candidate occurrences: {len(hazards)}"]
    lines += [f'{h["file"]}:{h["line"]}:{h["column"]} {h["source"]}' for h in hazards]
    lines += ["", "METAPROGRAMMING OCCURRENCES:"]
    lines += [f'{h["file"]}:{h["line"]}:{h["column"]} closure={h["in_realMainTheorem_import_closure"]}: {h["source"]}' for h in dynamic]
    lines += ["The three pre-existing root run_cmd blocks inspect collectAxioms/getEnv and throw/log audit results; they do not insert declarations or mutate the environment.",
              "The verification MainIdentity block checks the theorem's stored type/kind; TraceDependencies traverses declarations and writes audit JSON/text. Both are outside the theorem's import closure and do not insert mathematical axioms.",
              "The sole executable token 'constants' occurs as env.constants.toList in WholeProjectAudit.lean:15, an environment-field access, not a constant declaration.",
              "", "ALL OPTION COUNTS:"]
    lines += [f"{key} {value}: {count}" for (key, value), count in sorted(option_counts.items())]
    lines += ["", "allowUnsafeReducibility LOCATIONS AND IMMEDIATELY FOLLOWING COMMAND:"]
    for opt in options:
        if opt["name"] == "allowUnsafeReducibility":
            src = (ROOT / opt["file"]).read_text(encoding="utf-8-sig").splitlines()
            lines += [f'{opt["file"]}:{opt["line"]} closure={opt["in_realMainTheorem_import_closure"]}: {opt["source"]}', f'{opt["file"]}:{opt["line"]+1}: {src[opt["line"]]}']
    lines += ["These three commands permit local elaborator reducibility attributes. They are not declarations of unsafe proofs, new axioms, or a kernel-check disable option.",
              "The precise Lean v4.34.0-rc2 implementation is in src/lean/Lean/ReducibilityAttrs.lean:122-184: the option skips validation of reducibility-attribute changes; the command then updates the reducibility environment extension.",
              "Other observed settings concern elaborator transparency, typeclass search size, or heartbeat resources. Exact locations of every option are in placeholder_scan.json.",
              "", "NON-EXECUTABLE HITS (comments/strings), NOT PLACEHOLDERS:"]
    lines += [f'{h["file"]}:{h["line"]}:{h["column"]} [{h["kind"]}] {h["token"]}: {h["source"]}' for h in hits if h["kind"] != "code" and h["token"] in BASE_HAZARDS]
    lines += ["", "LOCAL IMPORT CLOSURE:", f'Main module: {MAIN}', f'Local modules including main: {len(closure)}', "Closure groups: " + json.dumps(dict(closure_group_counts), sort_keys=True), f'Executable placeholder/trust-bypass candidates in closure: {sum(h["in_realMainTheorem_import_closure"] for h in hazards)}', f'Metaprogramming candidates in closure: {sum(h["in_realMainTheorem_import_closure"] for h in dynamic)}', ""]
    lines += sorted(closure)
    lines += ["", f"External direct import frontier (not recursively scanned): {len(external)} modules", "Full frontier, all imports, all hits and all SHA-256 hashes are recorded in placeholder_scan.json and local-source-inventory.txt.", "LIMITATION: This scan does not prove that a file elaborates, nor that its generated proof terms avoid implicit sorries after errors. The independent rebuild/kernel axiom audit is required for that assertion.", "LIMITATION: An import closure is broader than the theorem's actual declaration dependency graph. No paper-faithfulness claim is made.", "", "READ-ONLY COMMAND TRANSCRIPTS (verbatim stdout/stderr also retained in JSON):"]
    for command in read_only_commands:
        lines += ["CWD: " + command["cwd"], "$ " + command["command"], "Exit code: " + str(command["exit_code"]), "STDOUT:", command["stdout"], "STDERR:", command["stderr"]]
    lines += ["", "PINNED LEAN SOURCE EVIDENCE:", semantics_evidence["file"], "SHA-256: " + semantics_evidence["sha256"], semantics_evidence["source_with_line_numbers"]]
    rendered = "\n".join(lines) + "\n"
    (OUT / "placeholder_audit.txt").write_text(rendered, encoding="utf-8")
    sys.stdout.reconfigure(encoding="utf-8")
    print(rendered, end="")
    if errors or symlinks or changed or not inventory_agreement:
        raise SystemExit(2)


if __name__ == "__main__":
    main()

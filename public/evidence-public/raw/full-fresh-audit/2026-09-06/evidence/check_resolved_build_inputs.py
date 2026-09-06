#!/usr/bin/env python3
"""Read-only Windows check of pinned Lake setup input paths; writes separate reports."""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import sys


BASE = Path("WORKSPACE")
DEFAULT_REPRODUCTION = BASE / "output/full_fresh_audit_2026-09-06_102854/reproduction"
DEFAULT_TOOLCHAIN = BASE / "tmp/lean_library_definition_audit_2026-09-05/lean-4.34.0-rc2-windows"
FORMAT_KEYS = {"name", "package", "isModule", "imports", "importArts", "dynlibs", "plugins", "options"}
REQUIRED_KEYS = {"name", "package", "isModule", "importArts", "dynlibs", "plugins", "options"}


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def key(path):
    return os.path.normcase(os.path.abspath(str(path)))


def within(path, root):
    try:
        return os.path.commonpath([key(path), key(root)]) == key(root)
    except ValueError:
        return False


def sha256_bytes(data):
    return hashlib.sha256(data).hexdigest()


def sha256_file(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def no_duplicate_keys(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError(f"Duplicate JSON object key: {name!r}")
        result[name] = value
    return result


class Audit:
    def __init__(self, args, module_stream):
        self.args = args
        self.module_stream = module_stream
        self.roots = {
            "reproduction": Path(os.path.abspath(args.reproduction)),
            "pinned_toolchain": Path(os.path.abspath(args.toolchain)),
        }
        self.findings = []
        self.path_records = []
        self.path_ids = {}
        self.modules = []
        self.package_directories = []
        self.counts = Counter()

    def finding(self, status, code, **details):
        self.findings.append({"status": status, "code": code, **details})

    def incomplete(self, code, **details):
        self.finding("NOT COMPLETED", code, **details)

    def inspect_path(self, raw, expected_file=True):
        """Resolve once per distinct spelling; inventory keeps original and resolved paths."""
        cache_key = (raw, expected_file)
        if cache_key in self.path_ids:
            return self.path_ids[cache_key]
        ident = len(self.path_records)
        self.path_ids[cache_key] = ident
        record = {"id": ident, "rawPath": raw, "expectedFile": expected_file}
        self.path_records.append(record)
        path = Path(raw)
        if not raw or not path.is_absolute() or not path.drive:
            record["status"] = "NOT COMPLETED"
            self.incomplete("non_absolute_input_path", pathId=ident, rawPath=raw,
                            reason="Compiler working-directory semantics are not guessed.")
            return ident
        try:
            resolved = path.resolve(strict=False)
            record["resolvedPath"] = str(resolved)
            lexical = [name for name, root in self.roots.items() if within(path, root)]
            owners = [name for name, root in self.roots.items() if within(resolved, root)]
            record["lexicalAllowedRoots"] = lexical
            record["resolvedAllowedRoots"] = owners
            record["resolutionChangesPath"] = key(path) != key(resolved)
            if not owners:
                record["status"] = "FAILED CHECK"
                self.finding("FAILED CHECK", "resolved_input_escape", pathId=ident,
                             rawPath=raw, resolvedPath=str(resolved))
                return ident
            if not lexical:
                record["status"] = "FAILED CHECK"
                self.finding("FAILED CHECK", "input_spelling_outside_allowed_roots", pathId=ident,
                             rawPath=raw, resolvedPath=str(resolved))
                return ident
            strict = path.resolve(strict=True)
            if key(strict) != key(resolved):
                record["status"] = "NOT COMPLETED"
                self.incomplete("path_changed_during_resolution", pathId=ident)
                return ident
            correct_type = strict.is_file() if expected_file else strict.is_dir()
            record["existsAsExpectedType"] = correct_type
            if not correct_type:
                record["status"] = "NOT COMPLETED"
                self.incomplete("input_wrong_file_type", pathId=ident)
            else:
                record["status"] = "PASS"
                record["allowedRoot"] = owners[0]
        except (OSError, RuntimeError, ValueError) as exc:
            record["status"] = "NOT COMPLETED"
            self.incomplete("input_missing_or_unresolvable", pathId=ident, error=str(exc))
        return ident

    def add_reference(self, module, raw, field, imported=None):
        if not isinstance(raw, str):
            self.incomplete("non_string_path", setupFile=module["setupFile"], field=field,
                            value=raw)
            return
        ident = self.inspect_path(raw)
        module["references"].append({"field": field, "importedModule": imported, "pathId": ident})
        self.counts["inputReferences"] += 1
        self.counts[field.split("[", 1)[0]] += 1

    def read_setup(self, path, package_dir):
        setup_id = self.inspect_path(str(path))
        if self.path_records[setup_id]["status"] != "PASS":
            return
        module = {"setupFile": str(path), "packageDirectory": str(package_dir),
                  "setupPathId": setup_id, "references": []}
        try:
            self.read_setup_content(path, module)
        finally:
            # Keep the complete map on disk, but at most one module's references in memory.
            json.dump(module, self.module_stream, ensure_ascii=False, separators=(",", ":"))
            self.module_stream.write("\n")
            self.module_stream.flush()
            reference_count = len(module.pop("references"))
            module["referenceCount"] = reference_count
            self.modules.append(module)

    def read_setup_content(self, path, module):
        try:
            before = path.stat()
            data = path.read_bytes()
            after = path.stat()
            module["setupSha256"] = sha256_bytes(data)
            module["setupBytes"] = len(data)
            if (before.st_size, before.st_mtime_ns) != (after.st_size, after.st_mtime_ns):
                self.incomplete("setup_changed_during_read", setupFile=str(path))
            content = json.loads(data.decode("utf-8-sig"), object_pairs_hook=no_duplicate_keys)
        except (OSError, UnicodeError, ValueError) as exc:
            self.incomplete("setup_unreadable_or_invalid_json", setupFile=str(path), error=str(exc))
            return
        if not isinstance(content, dict):
            self.incomplete("setup_not_object", setupFile=str(path))
            return
        missing = sorted(REQUIRED_KEYS - content.keys())
        unknown = sorted(content.keys() - FORMAT_KEYS)
        if missing or unknown:
            self.incomplete("unsupported_setup_fields", setupFile=str(path), missing=missing, unknown=unknown)
        name = content.get("name")
        package = content.get("package")
        module.update({"name": name, "package": package, "isModule": content.get("isModule")})
        if not isinstance(name, str) or not name:
            self.incomplete("invalid_module_name", setupFile=str(path))
        if package is not None and not isinstance(package, str):
            self.incomplete("invalid_package_name", setupFile=str(path))
        if not isinstance(content.get("isModule"), bool) or not isinstance(content.get("options"), dict):
            self.incomplete("unsupported_setup_metadata", setupFile=str(path))
        if "imports" in content and content["imports"] is not None and not isinstance(content["imports"], list):
            self.incomplete("unsupported_imports_metadata", setupFile=str(path))
        arts = content.get("importArts")
        if not isinstance(arts, dict):
            self.incomplete("unsupported_importArts", setupFile=str(path))
        else:
            module["importArtifactModuleCount"] = len(arts)
            for imported, arrays in arts.items():
                if not isinstance(arrays, list) or not all(isinstance(group, list) for group in arrays):
                    self.incomplete("unsupported_import_artifact_shape", setupFile=str(path), importedModule=imported)
                    continue
                # Pinned Lean/Setup.lean uses Array (Array FilePath), including variable lengths.
                for group_i, group in enumerate(arrays):
                    for part_i, raw in enumerate(group):
                        self.add_reference(module, raw, f"importArts[{group_i}][{part_i}]", imported)
        dynlibs = content.get("dynlibs")
        if not isinstance(dynlibs, list):
            self.incomplete("unsupported_dynlibs", setupFile=str(path))
        else:
            for i, raw in enumerate(dynlibs):
                self.add_reference(module, raw, f"dynlibs[{i}]")
        plugins = content.get("plugins")
        if not isinstance(plugins, list):
            self.incomplete("unsupported_plugins", setupFile=str(path))
        else:
            for i, plugin in enumerate(plugins):
                if isinstance(plugin, str):
                    raw = plugin
                elif isinstance(plugin, dict) and "path" in plugin:
                    if set(plugin) - {"path", "initFn"}:
                        self.incomplete("unknown_plugin_fields", setupFile=str(path), pluginIndex=i,
                                        unknown=sorted(set(plugin) - {"path", "initFn"}))
                    if plugin.get("initFn") is not None and not isinstance(plugin["initFn"], str):
                        self.incomplete("unsupported_plugin_initFn", setupFile=str(path), pluginIndex=i)
                    raw = plugin["path"]
                else:
                    self.incomplete("unsupported_plugin", setupFile=str(path), pluginIndex=i, value=plugin)
                    continue
                self.add_reference(module, raw, f"plugins[{i}]")

    def scan_ir(self, package_dir):
        ir = package_dir / ".lake/build/ir"
        row = {"packageDirectory": str(package_dir), "irDirectory": str(ir), "present": ir.exists()}
        self.package_directories.append(row)
        if not ir.exists():
            return  # Unused dependency packages need not have build output.
        ident = self.inspect_path(str(ir), expected_file=False)
        if self.path_records[ident]["status"] != "PASS":
            return
        count = 0
        def walk_error(exc):
            self.incomplete("setup_directory_unreadable", directory=str(ir), error=str(exc))
        for current, dirs, files in os.walk(ir, followlinks=False, onerror=walk_error):
            for dirname in list(dirs):
                child = Path(current) / dirname
                try:
                    if child.is_symlink() or child.is_junction():
                        link_id = self.inspect_path(str(child), expected_file=False)
                        self.incomplete("linked_setup_subdirectory_not_traversed", directory=str(child), pathId=link_id)
                        dirs.remove(dirname)
                except OSError as exc:
                    self.incomplete("setup_directory_type_unknown", directory=str(child), error=str(exc))
                    dirs.remove(dirname)
            dirs.sort()
            for filename in sorted(files):
                if filename.endswith(".setup.json"):
                    count += 1
                    self.read_setup(Path(current) / filename, package_dir)
        row["setupFileCount"] = count

    def run(self):
        if os.name != "nt" or not hasattr(Path, "is_junction"):
            self.incomplete("unsupported_platform", reason="Requires Windows Python 3.12+ for native junction resolution.")
            return
        for name, root in self.roots.items():
            try:
                resolved = root.resolve(strict=True)
                if not root.is_dir():
                    self.incomplete("allowed_root_not_directory", root=name, path=str(root))
                if key(resolved) != key(root):
                    self.finding("FAILED CHECK", "allowed_root_redirected", root=name,
                                 configuredPath=str(root), resolvedPath=str(resolved))
            except (OSError, RuntimeError) as exc:
                self.incomplete("allowed_root_unavailable", root=name, error=str(exc))
        if self.findings:
            return
        reproduction = self.roots["reproduction"]
        manifest_path = reproduction / "lake-manifest.json"
        try:
            manifest_bytes = manifest_path.read_bytes()
            self.manifest_sha256 = sha256_bytes(manifest_bytes)
            manifest = json.loads(manifest_bytes.decode("utf-8-sig"), object_pairs_hook=no_duplicate_keys)
            if manifest.get("packagesDir") != ".lake/packages":
                self.incomplete("unsupported_manifest_packagesDir", actual=manifest.get("packagesDir"))
                return
            packages = manifest["packages"]
            if not isinstance(packages, list):
                raise ValueError("packages must be an array")
            expected = set()
            for package in packages:
                name = package.get("name")
                if not isinstance(name, str) or not name or "/" in name or "\\" in name or name in {".", ".."}:
                    raise ValueError("Invalid package name")
                if package.get("type") != "git" or package.get("subDir") not in (None, ""):
                    self.incomplete("unsupported_manifest_package_location", package=package)
                expected.add(name)
        except (OSError, UnicodeError, ValueError, KeyError, AttributeError) as exc:
            self.incomplete("manifest_unreadable_or_unsupported", error=str(exc))
            return
        self.scan_ir(reproduction)
        packages_dir = reproduction / ".lake/packages"
        packages_id = self.inspect_path(str(packages_dir), expected_file=False)
        if self.path_records[packages_id]["status"] != "PASS":
            return
        actual = set()
        for package_dir in sorted(packages_dir.iterdir()):
            if package_dir.is_dir():
                actual.add(package_dir.name)
                package_id = self.inspect_path(str(package_dir), expected_file=False)
                if self.path_records[package_id]["status"] == "PASS":
                    self.scan_ir(package_dir)
        if expected != actual:
            self.incomplete("manifest_package_directory_mismatch", missing=sorted(expected - actual), extra=sorted(actual - expected))
        names = [row.get("name") for row in self.modules]
        if not self.modules:
            self.incomplete("no_setup_files")
        required = [row for row in self.modules if row.get("name") == self.args.required_module
                    and key(row["packageDirectory"]) == key(reproduction)]
        if len(required) != 1:
            self.incomplete("required_root_module_setup_missing_or_ambiguous", module=self.args.required_module,
                            matches=len(required))
        duplicates = {name: count for name, count in Counter(n for n in names if isinstance(n, str)).items() if count > 1}
        if duplicates:
            self.incomplete("duplicate_setup_module_names", modules=duplicates)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--reproduction", type=Path, default=DEFAULT_REPRODUCTION)
    parser.add_argument("--toolchain", type=Path, default=DEFAULT_TOOLCHAIN)
    parser.add_argument("--required-module", default="ComplementedSubspace")
    parser.add_argument("--output-dir", type=Path, required=True,
                        help="New report directory outside both inspected roots; never overwrites evidence.")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    if any(within(output, root.resolve()) for root in (args.reproduction, args.toolchain)):
        parser.error("--output-dir must be outside the reproduction and toolchain")
    # Refuse existing nonempty output so an earlier result cannot survive an interrupted retry.
    if output.exists() and any(output.iterdir()):
        parser.error("--output-dir must be new or empty")
    output.mkdir(parents=True, exist_ok=True)
    start = utc_now()
    # Flush each completed setup record. Closing the stream also preserves partial evidence on error.
    with (output / "module_map.jsonl").open("w", encoding="utf-8", newline="\n") as stream:
        audit = Audit(args, stream)
        try:
            audit.run()
        except Exception as exc:
            audit.incomplete("unexpected_checker_error", error=f"{type(exc).__name__}: {exc}")
    statuses = {finding["status"] for finding in audit.findings}
    status = "FAILED CHECK" if "FAILED CHECK" in statuses else "NOT COMPLETED" if statuses else "PASS"
    exit_code = {"PASS": 0, "FAILED CHECK": 1, "NOT COMPLETED": 2}[status]
    def write_json(name, value):
        with (output / name).open("w", encoding="utf-8", newline="\n") as stream:
            json.dump(value, stream, indent=2, ensure_ascii=False)
            stream.write("\n")
    write_json("findings.json", audit.findings)
    write_json("paths.json", audit.path_records)
    write_json("module_summaries.json", audit.modules)
    summary = {
        "status": status, "exitCode": exit_code, "startedUtc": start, "finishedUtc": utc_now(),
        "command": [sys.executable, str(Path(__file__).resolve()), *sys.argv[1:]],
        "pythonVersion": sys.version, "platform": sys.platform,
        "checkerSha256": sha256_bytes(Path(__file__).read_bytes()),
        "allowedRoots": {name: str(path) for name, path in audit.roots.items()},
        "requiredModule": args.required_module, "manifestSha256": getattr(audit, "manifest_sha256", None),
        "setupFileCount": len(audit.modules), "uniquePathCount": len(audit.path_records),
        "referenceCounts": dict(audit.counts), "findingsByStatus": dict(Counter(f["status"] for f in audit.findings)),
        "uniquePathsByStatus": dict(Counter(p["status"] for p in audit.path_records)),
        "uniquePathsByAllowedRoot": dict(Counter(p.get("allowedRoot", "unconfirmed") for p in audit.path_records)),
        "packageDirectories": audit.package_directories,
        "scope": "Every discovered setup JSON in root and manifest-layout package .lake/build/ir trees; explicit importArts, dynlibs and plugins paths only.",
        "limits": [
            "This is a post-build filesystem observation, not interception of compiler file reads.",
            "Setup files can omit toolchain imports resolved by the compiler; environment/replay evidence remains necessary.",
            "Containment does not prove artifact freshness, pin correctness, build success or full import-closure compilation.",
            "Artifact contents and native library transitive loader dependencies are not audited by this helper.",
            "Input files must remain quiescent; setup content hashes and timestamps detect only changes during each read.",
        ],
        "files": ["findings.json", "paths.json", "module_map.jsonl", "module_summaries.json"],
    }
    summary["reportSha256"] = {name: sha256_file(output / name) for name in summary["files"]}
    write_json("summary.json", summary)
    (output / "README.md").write_text(
        f"# Resolved build input check\n\nStatus: **{status}** (exit {exit_code}).\n\n"
        f"Inspected {len(audit.modules)} setup files and {audit.counts['inputReferences']} explicit input references.\n\n"
        "`summary.json` records the exact invocation, roots, counts, limits and report hashes. "
        "`findings.json` retains every finding. `paths.json` retains raw/resolved paths and containment outcomes. "
        "`module_map.jsonl` maps every setup hash/module/reference to path IDs in `paths.json`. "
        "`module_summaries.json` contains the small per-module summaries and reference counts.\n\n"
        "PASS covers only this path-containment observation; the source-build, source-hash, environment, "
        "pin and fresh-replay checks remain separate.\n", encoding="utf-8")
    print(json.dumps({"status": status, "exitCode": exit_code, "outputDirectory": str(output),
                      "setupFileCount": len(audit.modules), "findingCount": len(audit.findings)}))
    return exit_code


if __name__ == "__main__":
    raise SystemExit(main())

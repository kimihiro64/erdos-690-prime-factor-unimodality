"""Bounded Linux telemetry; partial runs never constitute proof acceptance."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tarfile
import time

BASE = "5097ece9126d2536e395143f739ac8cf68ab199b"
PIN = "68d5ca9db226849b41a6fff59d796ff19d0a8840"
REPO = "kimihiro64/erdos-690-prime-factor-unimodality"
EDITS = [
    {
        "relative": "src/main.rs",
        "before": "    let (export_file, skipped_axioms) = cfg.to_export_file()?;\n    // Check the environment\n    export_file.check_all_declars();",
        "after": "    let profile_started = std::time::Instant::now();\n    eprintln!(\"NANODA_PARSE_START\");\n    let (export_file, skipped_axioms) = cfg.to_export_file()?;\n    eprintln!(\"NANODA_PARSE_DONE seconds={} declarations={}\", profile_started.elapsed().as_secs_f64(), export_file.declars.len());\n    // Check the environment\n    let profile_check_started = std::time::Instant::now();\n    export_file.check_all_declars();\n    eprintln!(\"NANODA_CHECK_DONE seconds={}\", profile_check_started.elapsed().as_secs_f64());"
    },
    {
        "relative": "src/parser.rs",
        "before": "        parser.line_num += 1;\n        line_buffer.clear();",
        "after": "        parser.line_num += 1;\n        if parser.line_num % 1_000_000 == 0 {\n            eprintln!(\"NANODA_PARSE_LINES lines={} expressions={}\", parser.line_num, parser.dag.exprs.len());\n        }\n        line_buffer.clear();"
    },
    {
        "relative": "src/parser.rs",
        "before": "    let name_cache = parser.dag.mk_name_cache();",
        "after": "    eprintln!(\"NANODA_INPUT_DONE lines={} expressions={} declarations={}\", parser.line_num, parser.dag.exprs.len(), parser.declars.len());\n    let profile_name_cache_started = std::time::Instant::now();\n    let name_cache = parser.dag.mk_name_cache();\n    eprintln!(\"NANODA_NAME_CACHE_DONE seconds={}\", profile_name_cache_started.elapsed().as_secs_f64());"
    },
    {
        "relative": "src/tc.rs",
        "before": "    pub(crate) fn check_all_declars_serial(&self) {\n        for declar in self.declars.values() {\n            self.check_declar(declar);\n        }\n    }",
        "after": "    pub(crate) fn check_all_declars_serial(&self) {\n        for (index, declar) in self.declars.values().enumerate() {\n            let profile_name_idx = declar.info().name.idx;\n            eprintln!(\"NANODA_DECL_START index={} name_id={}\", index, profile_name_idx);\n            let profile_started = std::time::Instant::now();\n            self.check_declar(declar);\n            eprintln!(\"NANODA_DECL_END index={} name_id={} seconds={}\", index, profile_name_idx, profile_started.elapsed().as_secs_f64());\n        }\n    }"
    }
]
AXIOMS = ["propext", "Quot.sound", "Classical.choice"]


def digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def save(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def restore(root: Path) -> None:
    archives = list((root / "download").rglob("*.tar.gz"))
    assert len(archives) == 1
    dest = root / "checkpoint"
    dest.mkdir()
    expected = {"manifest.json", "challenge.export", "challenge.sha256",
                "comparator.bin", "configuration.sha256",
                "solution.export", "solution.sha256"}
    with tarfile.open(archives[0], "r:gz") as archive:
        members = archive.getmembers()
        assert len(members) == len(expected)
        assert {m.name for m in members} == expected
        assert all(m.isfile() and Path(m.name).name == m.name for m in members)
        assert sum(m.size for m in members) < 3_000_000_000
        for member in members:
            stream = archive.extractfile(member)
            assert stream is not None
            with stream, (dest / member.name).open("wb") as output:
                shutil.copyfileobj(stream, output)
    manifest = json.loads((dest / "manifest.json").read_text(encoding="utf-8"))
    assert manifest["schema"] == 1
    assert manifest["identity"] == {
        "commit": BASE, "repository": REPO, "run_id": "40707217629"}
    assert set(manifest["files"]) == expected - {"manifest.json"}
    for name, record in manifest["files"].items():
        path = dest / name
        assert path.stat().st_size == record["bytes"]
        assert digest(path) == record["sha256"]
    assert digest(dest / "solution.export") == (
        "f3bcc9f0af8a6da9972b1a8567d53cf83d5ade166da17a26dbbc5ea95d2d18aa")
    assert digest(dest / "comparator.bin") == (
        "ecbe8d4c440ceee14245da29f12354ccdd34f012d2f19898f332997cd0336718")
    (dest / "comparator.bin").chmod(0o755)
    small = root / "prefix"
    small.mkdir()
    copied = 0
    with (dest / "solution.export").open("rb") as source:
        with (small / "solution.export").open("wb") as output:
            for line in source:
                output.write(line)
                copied += len(line)
                if copied >= 1_000_000 and "thm" in json.loads(line):
                    break
    assert 1_000_000 <= copied < 20_000_000
    save(root / "results" / "input.json", {
        "manifest": manifest, "prefix_bytes": copied,
        "purpose": "Dependency prefix tests IO only, not submission acceptance."})


def instrument(root: Path) -> None:
    source_root = root / "nanoda"
    git = shutil.which("git")
    assert git and Path(git).is_file()
    assert subprocess.check_output(
        [git, "-C", str(source_root), "rev-parse", "HEAD"],
        text=True).strip() == PIN
    inventory = subprocess.check_output(
        [git, "-C", str(source_root), "ls-files"], text=True).splitlines()
    report = []
    for relative in dict.fromkeys(edit["relative"] for edit in EDITS):
        assert inventory.count(relative) == 1
        path = source_root / relative
        assert path.is_file()
        original = path.read_text(encoding="utf-8")
        changed = original
        relevant = [e for e in EDITS if e["relative"] == relative]
        for edit in relevant:
            assert changed.count(edit["before"]) == 1
            changed = changed.replace(edit["before"], edit["after"])
        recovered = changed
        for edit in reversed(relevant):
            assert recovered.count(edit["after"]) == 1
            recovered = recovered.replace(edit["after"], edit["before"])
        assert recovered == original
        path.write_text(changed, encoding="utf-8", newline="\n")
        report.append({"path": relative, "checker_recovery_exact": True,
                       "original_sha256": hashlib.sha256(
                           original.encode()).hexdigest()})
    save(root / "results" / "instrumentation.json", report)


def proc_info(pid: int) -> dict | None:
    try:
        folder = Path("/proc") / str(pid)
        raw = (folder / "stat").read_text()
        fields = raw[raw.rfind(")") + 2:].split()
        selected = {}
        for line in (folder / "status").read_text().splitlines():
            key = line.split(":", 1)[0]
            if key in {"VmRSS", "VmHWM", "VmSwap", "Threads"}:
                selected[key] = line.split(":", 1)[1].strip()
        try:
            exe = os.readlink(folder / "exe")
        except OSError:
            exe = ""
        return {"pid": pid, "ppid": int(fields[1]), "state": fields[0],
                "start_ticks": int(fields[19]), "exe": exe,
                "cpu_seconds": (int(fields[11]) + int(fields[12])) /
                               os.sysconf("SC_CLK_TCK"),
                "major_faults": int(fields[9]),
                "wchan": (folder / "wchan").read_text().strip(), **selected}
    except (OSError, ValueError, IndexError):
        return None


def descendants(leader: int) -> list[dict]:
    records = {}
    for folder in Path("/proc").iterdir():
        if folder.name.isdecimal():
            record = proc_info(int(folder.name))
            if record:
                records[record["pid"]] = record
    included = {leader}
    while True:
        grown = included | {pid for pid, r in records.items()
                            if r["ppid"] in included}
        if grown == included:
            return [records[p] for p in sorted(included) if p in records]
        included = grown


def host_info() -> dict:
    result = {}
    for relative in ("meminfo", "pressure/cpu", "pressure/memory", "pressure/io"):
        path = Path("/proc") / relative
        if path.is_file():
            result[relative] = path.read_text()
    result["vmstat"] = [
        line for line in Path("/proc/vmstat").read_text().splitlines()
        if line.startswith(("pswpin ", "pswpout ", "pgmajfault ", "oom_kill "))]
    return result


def last_event(path: Path) -> list[str]:
    with path.open("rb") as stream:
        stream.seek(max(0, path.stat().st_size - 4096))
        return stream.read().decode("utf-8", errors="replace").splitlines()[-1:]


def stack_limit() -> None:
    import resource
    wanted = 256 * 1024 * 1024
    _, hard = resource.getrlimit(resource.RLIMIT_STACK)
    assert hard == resource.RLIM_INFINITY or hard >= wanted
    resource.setrlimit(resource.RLIMIT_STACK, (wanted, hard))


def run_case(root: Path, repo: Path, name: str, source: Path,
             pipeline: bool, seconds: int) -> None:
    results = root / "results"
    env = os.environ.copy()
    wrapper = repo / "scripts/landrun-wrapper.sh"
    nanoda = root / "nanoda/target/release/nanoda_bin"
    landrun = root / "bin/landrun"
    comparator = root / "checkpoint/comparator.bin"
    assert all(p.is_file() for p in (wrapper, nanoda, landrun, comparator))
    env.update(COMPARATOR_NANODA=str(nanoda), COMPARATOR_LANDRUN=str(wrapper),
               PALOMAR_LANDRUN_BIN=str(landrun), COMPARATOR_STAGE_DIR=str(source))
    if pipeline:
        command = [str(comparator), str(repo / "comparator.json"), "nanoda"]
    else:
        config = results / (name + ".config.json")
        save(config, {"export_file_path": str(source / "solution.export"),
                      "use_stdin": False, "permitted_axioms": AXIOMS,
                      "unpermitted_axiom_hard_error": True,
                      "nat_extension": True, "string_extension": True})
        command = [str(wrapper), "--best-effort", "--ro", "/", "--rw", "/dev",
                   "-ldd", "-add-exec", "--ro", str(config), str(nanoda),
                   str(config)]
    stderr_path = results / (name + ".stderr")
    started = time.monotonic()
    timed_out = False
    owned = {}
    process = None
    identity = None
    with (results / (name + ".stdout")).open("wb") as output:
        with stderr_path.open("wb") as error:
            with (results / (name + ".samples.jsonl")).open(
                    "w", encoding="utf-8") as samples:
                try:
                    process = subprocess.Popen(
                        command, env=env, stdout=output, stderr=error,
                        start_new_session=True, preexec_fn=stack_limit)
                    identity = proc_info(process.pid)
                    assert identity is not None
                    while True:
                        records = descendants(process.pid)
                        owned.update((r["pid"], r) for r in records)
                        elapsed = time.monotonic() - started
                        samples.write(json.dumps({
                            "elapsed": elapsed, "processes": records,
                            "host": host_info(),
                            "last_event": last_event(stderr_path)}) + "\n")
                        samples.flush()
                        if process.poll() is not None:
                            break
                        if elapsed >= seconds:
                            timed_out = True
                            break
                        time.sleep(min(10, seconds - elapsed))
                finally:
                    if process is not None:
                        live = proc_info(process.pid)
                        if (identity and live
                                and live["start_ticks"] == identity["start_ticks"]
                                and os.getpgid(process.pid) == process.pid):
                            try:
                                os.killpg(process.pid, signal.SIGTERM)
                            except ProcessLookupError:
                                pass
                        try:
                            process.wait(timeout=5)
                        except subprocess.TimeoutExpired:
                            os.killpg(process.pid, signal.SIGKILL)
                            process.wait(timeout=5)
                        for pid, record in owned.items():
                            live = proc_info(pid)
                            if (live and live["start_ticks"] == record["start_ticks"]
                                    and live["exe"] == record["exe"]
                                    and live["state"] != "Z"):
                                os.kill(pid, signal.SIGKILL)
                        time.sleep(0.2)
                        residual = [
                            pid for pid, record in owned.items()
                            if (live := proc_info(pid))
                            and live["start_ticks"] == record["start_ticks"]
                            and live["state"] != "Z"]
                        assert not residual, residual
    summary = {"case": name, "seconds_cap": seconds,
               "wall_seconds": time.monotonic() - started,
               "timed_out": timed_out, "exit_code": process.returncode,
               "submission_acceptance": False}
    save(results / (name + ".summary.json"), summary)
    print(json.dumps(summary), flush=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["restore", "instrument", "profile",
                                        "validate"])
    parser.add_argument("--root", type=Path, required=True)
    args = parser.parse_args()
    root = args.root.resolve()
    repo = Path(__file__).resolve().parents[1]
    if args.mode == "validate":
        assert len(EDITS) == 4
        for relative in dict.fromkeys(e["relative"] for e in EDITS):
            entries = [e for e in EDITS if e["relative"] == relative]
            probe = "\n".join(e["before"] for e in entries)
            original = probe
            for edit in entries:
                assert probe.count(edit["before"]) == 1
                probe = probe.replace(edit["before"], edit["after"])
            for edit in reversed(entries):
                assert probe.count(edit["after"]) == 1
                probe = probe.replace(edit["after"], edit["before"])
            assert probe == original
        import yaml
        workflow = yaml.safe_load(
            (repo / ".github/workflows/nanoda-diagnostic.yml").read_text(
                encoding="utf-8"))
        trigger = workflow.get("on", workflow.get(True))
        assert trigger == {"push": {"branches": ["diagnostics/nanoda-runtime"]}}
        assert workflow["jobs"]["profile"]["timeout-minutes"] == 20
        assert len(workflow["jobs"]) == 1
        print("Instrumentation recovery and bounded workflow checks passed.")
        return
    assert sys.platform == "linux"
    (root / "results").mkdir(parents=True, exist_ok=True)
    if args.mode == "restore":
        restore(root)
    elif args.mode == "instrument":
        instrument(root)
    else:
        save(root / "results/host.json", host_info())
        for label, folder, pipeline, cap in [
            ("prefix-stdin", "prefix", True, 45),
            ("prefix-file", "prefix", False, 45),
            ("full-stdin", "checkpoint", True, 180),
            ("full-file", "checkpoint", False, 180),
        ]:
            run_case(root, repo, label, root / folder, pipeline, cap)


if __name__ == "__main__":
    main()

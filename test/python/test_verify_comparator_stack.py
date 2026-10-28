"""Exercise the actual verifier launcher's inherited Linux stack limit."""

import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

pytestmark = pytest.mark.skipif(sys.platform != "linux", reason="Linux process resource limits")
ROOT = Path(__file__).resolve().parents[2]


def executable(path: Path, source: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(source, encoding="utf-8")
    path.chmod(0o755)


@pytest.mark.parametrize(("phase", "exit_code"), [("nanoda", 0), ("nanoda", 17), ("kernel", 0)])
def test_verifier_scopes_and_inherits_main_thread_stack(
    tmp_path: Path, phase: str, exit_code: int
) -> None:
    import resource

    bash = shutil.which("bash")
    assert bash is not None
    for command in ("python3", "sha256sum", "stdbuf"):
        assert shutil.which(command) is not None, command

    project = tmp_path / "project"
    script = project / "scripts/verify-comparator.sh"
    script.parent.mkdir(parents=True)
    script.write_text((ROOT / "scripts/verify-comparator.sh").read_text(encoding="utf-8"))
    cache = project / ".cache/palomar-comparator"
    exports = cache / "exports"
    exports.mkdir(parents=True)
    report = tmp_path / "stack.json"
    probe = tmp_path / "probe.py"
    probe.write_text(
        "import json, resource, sys\n"
        "from pathlib import Path\n"
        "Path(sys.argv[1]).write_text(json.dumps(resource.getrlimit(resource.RLIMIT_STACK)))\n"
        "raise SystemExit(int(sys.argv[2]))\n"
    )
    config = project / "comparator.json"
    config.write_text(
        json.dumps(
            {
                "enable_nanoda": True,
                "definition_names": [],
                "probe": str(probe),
                "report": str(report),
                "exit_code": exit_code,
            }
        )
    )
    for name, target in (
        ("configuration", config),
        ("challenge", exports / "challenge.export"),
        ("solution", exports / "solution.export"),
    ):
        if target != config:
            target.write_text("fixture\n")
        digest = hashlib.sha256(target.read_bytes()).hexdigest()
        (exports / f"{name}.sha256").write_text(f"{digest}  {target}\n")

    tools = tmp_path / "bin"
    for name in ("cargo", "git", "go"):
        executable(tools / name, "#!/bin/sh\nexit 91\n")
    executable(tools / "lake", '#!/bin/sh\n[ "$1" = env ] || exit 92\nshift\nexec "$@"\n')
    executable(
        cache / "comparator/.lake/build/bin/comparator",
        "#!/usr/bin/env python3\n"
        "import json, subprocess, sys\n"
        "from pathlib import Path\n"
        "config = json.loads(Path(sys.argv[1]).read_text())\n"
        "result = subprocess.run(\n"
        "    [sys.executable, config['probe'], config['report'], str(config['exit_code'])],\n"
        "    env={}, check=False,\n"
        ")\n"
        "raise SystemExit(result.returncode)\n",
    )
    environment = os.environ.copy()
    environment["PATH"] = str(tools) + os.pathsep + environment["PATH"]
    environment.pop("PALOMAR_COMPARATOR_CACHE", None)
    inherited_soft, inherited_hard = resource.getrlimit(resource.RLIMIT_STACK)
    result = subprocess.run(
        [bash, str(script), phase],
        cwd=project,
        env=environment,
        capture_output=True,
        text=True,
        check=False,
        timeout=30,
    )
    assert result.returncode == exit_code, result.stdout + result.stderr
    soft, hard = json.loads(report.read_text())
    assert soft == (256 * 1024 * 1024 if phase == "nanoda" else inherited_soft)
    assert hard == inherited_hard
    if phase == "nanoda":
        assert "NanoDa main-thread stack limit: 262144 KiB" in result.stdout
    else:
        assert "NanoDa main-thread stack limit:" not in result.stdout
    assert resource.getrlimit(resource.RLIMIT_STACK) == (inherited_soft, inherited_hard)

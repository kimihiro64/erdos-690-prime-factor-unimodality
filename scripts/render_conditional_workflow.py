"""Release the single-theta proof after one shared conditional build job.

Lightweight checks and licensing are copied verbatim from ci.yml. The Lean
job restores a complete proof when available, otherwise resumes serial durable
checkpoints without repeating a prefix in separate jobs. Comparator, API docs and late Lean lint are
deliberately omitted, not reported as having passed.
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path
from textwrap import dedent

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = Path(".github/workflows/conditional-dusart.yml")
CHECKOUT = "actions/checkout@3d3c42e5aac5ba805825da76410c181273ba90b1"
LEAN = "leanprover/lean-action@38fbc41a8c28c4cbaec22d7f7de508ec2e7c0dd9"
UPLOAD = "actions/upload-artifact@043fb46d1a93c77aae656e7c1c64a875d1fc6a0a"
DOWNLOAD = "actions/download-artifact@3e5f45b2cfb9172054b4087a40e8e0b5a5461e7c"
GATE = "${{ vars.CONDITIONAL_CI_BUILDS == 'enabled' }}"


def original_jobs(root: Path) -> dict[str, str]:
    source = (root / ".github/workflows/ci.yml").read_text().split("jobs:\n", 1)[1]
    starts = list(re.finditer(r"^  ([\w-]+):\n", source, re.M))
    return {
        match[1]: source[
            match.start() : starts[i + 1].start() if i + 1 < len(starts) else len(source)
        ].rstrip()
        + "\n"
        for i, match in enumerate(starts)
    }


def step(text: str) -> str:
    return "".join(
        "      " + line + "\n" if line else "\n" for line in dedent(text).strip().splitlines()
    )


def checkout() -> str:
    return step(f"""\
        - uses: {CHECKOUT}
          with:
            persist-credentials: false
            fetch-depth: 0
        """)


def lean() -> str:
    return step(f"""\
        - uses: {LEAN}
          with:
            build: false
            test: false
            lint: false
            use-mathlib-cache: true
        - name: Apply reviewed compatibility ports
          run: |
            python3 scripts/patch_pnt_compat.py
            python3 scripts/patch_primecert_compat.py
        """)


def upload(name: str, path: str, *, always: bool = False) -> str:
    return step(f"""\
        - uses: {UPLOAD}
          if: {"always()" if always else "success()"}
          with:
            name: {name}
            path: {path}
            include-hidden-files: true
            if-no-files-found: {"ignore" if always else "error"}
            retention-days: 14
        """)


def download(name: str, path: str) -> str:
    return step(f"""\
        - uses: {DOWNLOAD}
          with:
            name: {name}
            path: {path}
        """)


def job(name: str, title: str, needs: str, minutes: int = 360, *, write: bool = False) -> str:
    return (
        f"  {name}:\n    name: {title}\n    if: {GATE}\n    needs: [{needs}]\n"
        f"    runs-on: ubuntu-latest\n    timeout-minutes: {minutes}\n"
        + ("    permissions:\n      contents: write\n      actions: read\n" if write else "")
        + "    steps:\n"
        + checkout()
    )


def build_stage(name: str, title: str, needs: str, stage: str, restores: tuple[str, ...]) -> str:
    text = job(name, title, needs, write=True) + lean()
    for artifact in restores:
        text += download(artifact, ".lake/build")
    text += step(f"""\
        - name: Restore the complete proof and validate once, or resume missing checkpoints
          env:
            GH_TOKEN: ${{{{ github.token }}}}
          shell: bash
          run: |
            set -euo pipefail
            mkdir -p .research
            python3 -m scripts.conditional_dusart_ci --stage {stage} --minutes 280 2>&1 |
              tee .research/conditional-{stage}.log
        """)
    text += upload(
        f"conditional-{stage}-diagnostics", f".research/conditional-{stage}.log", always=True
    )
    return text


def render(root: Path) -> str:
    base = original_jobs(root)
    jobs = {
        name: base[name].replace("vars.DUSART_CI_BUILDS", "vars.CONDITIONAL_CI_BUILDS")
        for name in (
            "release_version",
            "metadata-and-boundary",
            "release-licensing",
            "python",
            "sandbox",
            "submission-link",
        )
    }
    jobs["release_version"] = jobs["release_version"].replace(
        'tag="v$version"', 'tag="v$version-conditional.${GITHUB_SHA:0:12}"'
    )
    jobs["build"] = (
        build_stage(
            "build",
            "Restore and validate the conditional proof once",
            "release_version, metadata-and-boundary, python",
            "build",
            (),
        )
        + step("""\
        - name: Package the full compiled conditional dependency closure
          run: |
            python3 -m scripts.conditional_release_bundle \\
              --receipt .research/conditional-audit.json --commit "$GITHUB_SHA" \\
              --output .research/conditional-build-release
        """)
        + upload("conditional-proof-audit", ".research/conditional-audit.json")
        + upload("conditional-build-release", ".research/conditional-build-release")
    )
    jobs["paper"] = (
        job("paper", "Build separate conditional research paper", "build", 30)
        + download("conditional-proof-audit", ".research/paper-audit")
        + step("""\
        - name: Install paper toolchain
          run: |
            sudo apt-get update
            sudo apt-get install --yes --no-install-recommends \\
              lmodern poppler-utils texlive-latex-base texlive-latex-recommended
        - name: Generate, build and inspect the conditional paper
          run: |
            python3 -m scripts.conditional_paper \\
              --receipt .research/paper-audit/conditional-audit.json --commit "$GITHUB_SHA" \\
              --output .research/conditional-paper
        """)
        + upload("conditional-research-paper", ".research/conditional-paper")
    )
    jobs["release"] = job(
        "release",
        "Publish conditional release",
        "release_version, metadata-and-boundary, "
        "release-licensing, python, sandbox, build, paper, submission-link",
        45,
        write=True,
    ).replace(
        f"    if: {GATE}",
        "    if: >-\n      vars.CONDITIONAL_CI_BUILDS == 'enabled' &&\n"
        "      needs.release_version.outputs.release_ready == 'true' &&\n"
        "      github.ref == 'refs/heads/main' &&\n"
        "      (github.event_name == 'push' || github.event_name == 'workflow_dispatch')",
    )
    for name, directory in (
        ("conditional-build-release", "build"),
        ("conditional-research-paper", "paper"),
    ):
        jobs["release"] += download(name, f".research/conditional-release-inputs/{directory}")
    jobs["release"] += step("""\
        - name: Validate, package, and publish the exact conditional artifacts
          env:
            GH_TOKEN: ${{ github.token }}
            RELEASE_TAG: ${{ needs.release_version.outputs.tag }}
          run: |
            python3 -m scripts.publish_conditional_release \\
              --inputs .research/conditional-release-inputs --commit "$GITHUB_SHA" \\
              --output .research/conditional-release-assets
        """)
    header = """name: Conditional all-k proof

# Generated by scripts/render_conditional_workflow.py.
# No Comparator, API documentation or post-build Lean lint job.
on:
  push:
    branches: [main]
  pull_request:
  workflow_dispatch:

permissions:
  contents: read
  actions: read

concurrency:
  group: >-
    ${{ github.ref == 'refs/heads/main' && 'conditional-dusart-checkpoints' ||
        format('conditional-dusart-checkpoints-{0}', github.ref) }}
  cancel-in-progress: false

jobs:
"""
    omitted = {"comparator", "docs", "lean-foundations", "certificate-prebuild", "analytic-tail"}
    order = [name for name in base if name not in omitted]
    if set(order) != set(jobs):
        raise ValueError("original CI stages changed: review the conditional mirror")
    return header + "\n".join(jobs[name] for name in order)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    expected = render(ROOT)
    if args.check:
        if (ROOT / OUTPUT).read_text() != expected:
            raise SystemExit("conditional workflow is stale; run its renderer")
    else:
        (ROOT / OUTPUT).write_text(expected)


if __name__ == "__main__":
    main()

#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$repository_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"
export_dir="$cache_root/exports"
phase="${1:-all}"
if [[ $# -gt 1 ]]; then
  echo "error: expected at most one Comparator phase" >&2
  exit 1
fi
case "$phase" in
  all|prepare|export-challenge|export-solution|match-axioms|match|axioms|nanoda|kernel) ;;
  *) echo "error: unknown Comparator phase: $phase" >&2; exit 1 ;;
esac

comparator_commit=68a064109f01c08f47c8edc9f51d6a2bbffaa188
lean4export_repository=https://github.com/leanprover/lean4export.git
lean4export_commit=076e8e57707e813375e8f9da8bf989799ace9680
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3 sha256sum stdbuf; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  fi
done

python3 - "$repository_root/comparator.json" <<'PY'
import json
import pathlib
import sys

config_path = pathlib.Path(sys.argv[1])
try:
    config = json.loads(config_path.read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {config_path}: {error}", file=sys.stderr)
    raise SystemExit(1)

if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    print(
        f"error: {config_path}: enable_nanoda must be exactly true; "
        "the NanoDa replay is required",
        file=sys.stderr,
    )
    raise SystemExit(1)
if config.get("definition_names", []) != []:
    print("error: fixed Challenge definitions cannot be definition holes", file=sys.stderr)
    raise SystemExit(1)
PY

run_phase() (
  local selected=$1
  test -x /usr/bin/time
  test -s "$export_dir/configuration.sha256"
  sha256sum -c "$export_dir/configuration.sha256"
  case "$selected" in
    export-solution)
      sha256sum -c "$export_dir/challenge.sha256"
      ;;
    match-axioms|match|axioms|nanoda|kernel)
      sha256sum -c "$export_dir/challenge.sha256"
      sha256sum -c "$export_dir/solution.sha256"
      ;;
  esac
  if [[ "$selected" == nanoda ]]; then
    # NanoDa checks on Rust's main thread; RUST_MIN_STACK only affects workers.
    # Set an inherited OS limit, scoped to this phase, without changing the checker.
    ulimit -S -s 262144
    echo "NanoDa main-thread stack limit: $(ulimit -S -s) KiB"
  fi
  echo "Comparator phase: $selected"
  PALOMAR_LANDRUN_BIN="$bin_dir/landrun" \
  COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
  COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
  COMPARATOR_LANDRUN="$repository_root/scripts/landrun-wrapper.sh" \
  COMPARATOR_STAGE_DIR="$export_dir" \
    /usr/bin/time -v stdbuf -oL -eL lake env \
      "$comparator_dir/.lake/build/bin/comparator" comparator.json "$selected"
  case "$selected" in
    export-challenge)
      sha256sum "$export_dir/challenge.export" > "$export_dir/challenge.sha256"
      ;;
    export-solution)
      sha256sum "$export_dir/solution.export" > "$export_dir/solution.sha256"
      ;;
  esac
)

if [[ "$phase" != prepare && "$phase" != all ]]; then
  cd "$repository_root"
  run_phase "$phase"
  exit 0
fi

mkdir -p "$cache_root" "$bin_dir" "$export_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    mkdir -p "$destination"
    git -C "$destination" init --quiet
    git -C "$destination" remote add origin "$repository"
  else
    git -C "$destination" remote set-url origin "$repository"
  fi
  if [ "$(git -C "$destination" remote get-url origin)" != "$repository" ]; then
    echo "error: cached dependency $destination has the wrong origin" >&2
    exit 1
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
  if [ "$(git -C "$destination" rev-parse HEAD)" != "$commit" ]; then
    echo "error: cached dependency $destination did not resolve to $commit" >&2
    exit 1
  fi
}

checkout_exact "$lean4export_repository" "$lean4export_dir" "$lean4export_commit"

if [ ! -f "$lean4export_dir/lean-toolchain" ]; then
  echo "error: pinned lean4export revision $lean4export_commit has no lean-toolchain file" >&2
  echo "select a lean4export revision that declares its Lean toolchain" >&2
  exit 1
fi

project_toolchain=$(tr -d '[:space:]' < "$repository_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$lean4export_toolchain" != "leanprover/lean4:v4.34.0" ]; then
  echo "error: pinned upstream lean4export revision declares" >&2
  echo "$lean4export_toolchain instead of reviewed toolchain leanprover/lean4:v4.34.0" >&2
  exit 1
fi
if [ "$project_toolchain" != "leanprover/lean4:v4.34.0" ]; then
  echo "error: project toolchain $project_toolchain is not the reviewed" >&2
  echo "Lean stable release leanprover/lean4:v4.34.0" >&2
  echo "review lean4export, Comparator and NanoDa compatibility before changing it" >&2
  exit 1
fi

checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"

python3 "$repository_root/scripts/patch_comparator_stages.py" "$comparator_dir"
(cd "$comparator_dir" && lake build comparator)
# Build the matching upstream v4.34.0 source unchanged with the project's exact
# toolchain so the exporter can read this repository's .olean format; no fork
# or source patch is involved.
(cd "$lean4export_dir" && ELAN_TOOLCHAIN="$project_toolchain" lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$repository_root"
# Consume the committed dependency lock; updating it invalidates restored proof objects.
git diff --exit-code HEAD -- lake-manifest.json
lake exe cache get
# Check only the advertised roots, retaining the unconditional imported closure.
# A library-wide build also selects historical conditional and certificate routes.
lake build +Challenge +Solution
git diff --exit-code HEAD -- lake-manifest.json
sha256sum \
  "$repository_root/comparator.json" \
  "$repository_root/lake-manifest.json" \
  "$repository_root/lean-toolchain" \
  "$repository_root/scripts/patch_comparator_stages.py" \
  "$comparator_dir/Main.lean" \
  "$comparator_dir/.lake/build/bin/comparator" > "$export_dir/configuration.sha256"

if [[ "$phase" == all ]]; then
  for selected in export-challenge export-solution match-axioms nanoda kernel; do
    run_phase "$selected"
  done
fi

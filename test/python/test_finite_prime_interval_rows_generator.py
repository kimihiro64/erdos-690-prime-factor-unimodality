from pathlib import Path

from scripts.generate_finite_prime_interval_rows import main


def test_finite_prime_interval_rows_low_generation_is_sharded(tmp_path, monkeypatch):
    repo = Path(__file__).resolve().parents[2]
    monkeypatch.setattr(
        "sys.argv",
        [
            "generate_finite_prime_interval_rows.py",
            "--repo",
            str(repo),
            "--output-dir",
            str(tmp_path),
        ],
    )
    (tmp_path / "LowPart99.lean").write_text("stale generated shard")

    main()

    manifest = (tmp_path / "LowManifest.lean").read_text()
    count = int(manifest.split(":=")[1].strip())
    assert count > 0

    facade = (tmp_path / "Low.lean").read_text()
    assert f"LowPart{count:02d}" in facade

    for part in range(1, count + 1):
        path = tmp_path / f"LowPart{part:02d}.lean"
        assert path.exists()
        assert path.stat().st_size <= 10_000
        if part == 1:
            expected = "LowBase"
        else:
            expected = f"LowPart{part - 1:02d}"
        assert f".{expected}\n" in path.read_text()

    assert not list(tmp_path.glob(f"LowPart{count + 1:02d}.lean"))
    assert not (tmp_path / "LowPart99.lean").exists()

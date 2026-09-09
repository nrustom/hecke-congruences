"""Test safe pruning of temporary recursive maps, without production data."""
from pathlib import Path
import tempfile
from run_p3_ideal_source_data import prune_module_cache

with tempfile.TemporaryDirectory() as name:
    root = Path(name)
    (root / "degree_2_plus.gz").write_bytes(b"a"*8)
    (root / "degree_3206_minus.gz").write_bytes(b"b"*8)
    (root / "degree_4000_plus.gz").write_bytes(b"c"*8)
    final = root / "degree_2.npz"
    final.write_bytes(b"do not delete")
    assert prune_module_cache(root, 5000) == 16
    assert not (root / "degree_2_plus.gz").exists()
    assert (root / "degree_3206_minus.gz").exists()
    assert prune_module_cache(root, 5000, maximum_bytes=8) == 8
    assert final.read_bytes() == b"do not delete"
    assert prune_module_cache(root, 7290) == 0
    assert final.exists()
print("Optional map-cache eviction tests passed")

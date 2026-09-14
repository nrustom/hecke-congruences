"""One-time Sage export of the exact mod49 notebook relations; no verification."""
import hashlib
import json
from pathlib import Path
from p7_mod49 import p7_mod49_nim_relation_spec

ROOT = Path(__file__).resolve().parents[1]


def export():
    """Write the fixed modulo-49 degree, orientation and polynomial specifications for native replay."""
    for exponent, stage in ((2, 'G_mod49'), (3, 'Q_selectors_mod343')):
        specifications = {str(r): p7_mod49_nim_relation_spec(r, 0, exponent)
                          for r in range(0, 42, 2)}
        # Check that the producer's residue lookup is exactly the notebook's.
        for r in range(0, 42, 2):
            for q in range(6):
                assert specifications[str((r+14*q) % 42)] == p7_mod49_nim_relation_spec(r, q, exponent)
        plan = dict(schema='hecke.native-witness-plan.v1', prime=7, exponent=exponent,
                    classification_modulus=49, coefficient_period=42, orientation_shift=14,
                    degree_bound=7**exponent*6 + 7**(exponent-1)*8,
                    low_orientation_bound=7**(exponent-1)*8, dependency_period=14,
                    source_directory=f'source_data/p7_mod49_transfer_maps/{stage}',
                    allow_missing_lower_orientations=False,
                    relation_specifications=specifications,
                    exported_from='p7_mod49.p7_mod49_nim_relation_spec',
                    relation_data_sha256=hashlib.sha256((ROOT/'p7_mod49_relation_data.json').read_bytes()).hexdigest())
        path = ROOT/f'relations/p7_mod49_{stage}_native.json'
        if path.exists():
            if json.loads(path.read_text()) != plan:
                raise RuntimeError(f'refusing to overwrite a different plan: {path}')
        else:
            path.write_text(json.dumps(plan, indent=2)+'\n')
        total = plan['low_orientation_bound']//2 + (plan['degree_bound']-plan['low_orientation_bound'])//2*6
        print(f'{stage}: {total} cases; {len(specifications["0"]["relations"])} relations per case; {path}')


if __name__ == '__main__':
    export()

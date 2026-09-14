"""Export notebook polynomials and losslessly decode its old source bundle.

No source construction or identity verification occurs here. The original
bundle is preserved. The notebook's existing loader decodes its scaled rows.
"""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import numpy as np
from sage.all import *
from sage.repl.preparse import preparse
from load_source_data import load_source_data
from verify_hecke_relations import relation_spec

ROOT = Path(__file__).resolve().parents[1]


def export():
    """Write the fixed modulo-256 degree, orientation and polynomial specifications for native replay."""
    notebook = json.loads((ROOT / 'classification_mod_256.ipynb').read_text())
    ns = dict(globals())
    with contextlib.redirect_stdout(io.StringIO()):
        exec(preparse(''.join(notebook['cells'][3]['source'])), ns)
    P = PolynomialRing(Integers(256), names=('T3','T5','Z'))
    T3,T5,Z = P.gens()
    specs = {}
    for r in ns['degree_residues']:
        specs[str(r)] = relation_spec(
            [('T5', ns['F5'][r](T5), 8), ('T3_full_domain', Z, 0),
             ('T3_terminal', ns['F3'][r](Z), 1)],
            hecke_operators={'T3': 3, 'T5': 5},
            divisions={'Z': (ns['Q3'][r](T3), 7)},
            witness_semantics='independent_monomials', max_howell_dimension=4096)
    original = ROOT / 'source_data/p2_mod256_T3_T5_all_degrees.npz'
    digest = hashlib.sha256(original.read_bytes()).hexdigest()
    directory = ROOT / 'source_data/p2_mod256_native'
    directory.mkdir(exist_ok=True)
    for d in range(0, 640, 2):
        data = load_source_data(Integers(256), d, 0, original)
        meta = dict(prime=2, exponent=8, degree=d, orientations=[0],
                    source_scope='manin', ideal=None, construction='archived',
                    hecke_indices=[3,5], original_bundle_sha256=digest)
        arrays = dict(source_data_version=np.array([3], dtype=np.uint8),
                      metadata_json=np.frombuffer(json.dumps(meta).encode(), dtype=np.uint8),
                      q0_order_exponents=np.array(data['coordinates']['surviving_exponents'], dtype=np.uint8))
        for ell in (3,5):
            matrix = data['archived_hecke_matrices'][ell]['normalized_matrix']
            arrays[f'q0_T{ell}'] = np.array(matrix.list(), dtype=np.uint16).reshape(matrix.dimensions())
        path = directory / f'degree_{d}.npz'
        if path.exists():
            with np.load(path, allow_pickle=False) as old:
                assert set(old.files) == set(arrays) and all(np.array_equal(old[k],v) for k,v in arrays.items())
        else:
            with path.open('xb') as stream:
                np.savez_compressed(stream, **arrays)
        with np.load(path, allow_pickle=False) as saved:
            assert all(np.array_equal(saved[k],v) for k,v in arrays.items())
    plan = dict(schema='hecke.native-witness-plan.v1', prime=2, exponent=8,
                classification_modulus=256, coefficient_period=128, orientation_shift=0,
                degree_bound=640, low_orientation_bound=0, dependency_period=2,
                degree_residue_modulus=2, degree_residues=[0],
                verification_mode='whole_compact_source', source_scope='manin',
                source_directory='source_data/p2_mod256_native', relation_specifications=specs,
                exported_from='classification_mod_256.ipynb', original_bundle_sha256=digest)
    assert hashlib.sha256(original.read_bytes()).hexdigest() == digest
    path = ROOT / 'relations/p2_mod256_T3_T5_native.json'
    if path.exists() and json.loads(path.read_text()) != plan:
        raise RuntimeError('refusing to overwrite a different plan')
    path.write_text(json.dumps(plan, indent=2)+'\n')
    print('Exported 320 unsigned sources and the T3,T5 specifications; original preserved.')


if __name__ == '__main__':
    export()

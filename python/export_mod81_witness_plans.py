"""Export exact specifications by intercepting the notebook's verifier calls.

Only setup/definition cells are executed, never the verification loops or scan.
Run from the repository root with Sage Python; queued arithmetic is pure Nim.
"""
import contextlib
import io
import json
from pathlib import Path
from sage.all import *
from sage.repl.preparse import preparse

ROOT = Path(__file__).resolve().parents[1]


def export():
    """Write the fixed modulo-81 degree, orientation and polynomial specifications for native replay."""
    notebook = json.loads((ROOT / 'classification_mod_81.ipynb').read_text())
    ns = dict(globals())
    with contextlib.redirect_stdout(io.StringIO()):
        for index in (1, 3, 5, 9, 10, 13):
            exec(preparse(''.join(notebook['cells'][index]['source'])), ns)
    class Captured(Exception):
        """Signal that the notebook specification has been captured without executing the verification loop."""
        pass
    def capture(spec, *args, **kwargs):
        """Capture the requested native specification instead of running a source verification."""
        raise Captured(spec)
    ns['verify_hecke_relations_nim'] = capture
    ns['get_source_data'] = lambda *a: {'source_scope': 'ideal_image'}
    ns['load_source_data'] = lambda *a: {'source_scope': 'manin'}
    stages = [
        ('T7_mod81', 4, 270, [0, 2, 4], 'manin', 'p3_T7_mod81', 'verify_common_T7_case'),
        ('nonzero_mod243', 5, 810, [0, 4], 'manin', 'p3_nonzero_T2_T7_mod243', 'verify_Q_case'),
        ('zero_ideal_mod2187', 7, 7290, [2], 'ideal_image', 'p3_ideal_9_T2_mod2187', 'verify_A_B_case'),
    ]
    for stage, m, bound, residues, scope, archive, function in stages:
        specs = {}
        for r in range(0, 54, 2):
            if r % 6 not in residues:
                continue
            for q in (0, 1):
                try:
                    ns[function](r, q)
                except Captured as result:
                    spec = result.args[0]
                else:
                    raise RuntimeError('notebook verifier was not intercepted')
                if q == 0:
                    specs[str(r)] = spec
                else:
                    assert specs[str(r)] == spec
        plan = dict(schema='hecke.native-witness-plan.v1', prime=3, exponent=m,
                    classification_modulus=81, coefficient_period=54, orientation_shift=0,
                    degree_bound=bound, low_orientation_bound=0, dependency_period=6,
                    degree_residue_modulus=6, degree_residues=residues,
                    verification_mode='whole_compact_source', source_scope=scope,
                    source_directory='source_data/' + archive,
                    relation_specifications=specs,
                    exported_from='classification_mod_81.ipynb: ' + function)
        path = ROOT / f'relations/p3_mod81_{stage}_native.json'
        if path.exists() and json.loads(path.read_text()) != plan:
            raise RuntimeError(f'refusing to overwrite a different plan: {path}')
        path.write_text(json.dumps(plan, indent=2) + '\n')
        degrees = [d for d in range(0, bound, 2) if d % 6 in residues]
        assert all((ROOT / plan['source_directory'] / f'degree_{d}.npz').is_file() for d in degrees)
        print(stage, len(degrees)*2, 'cases')


if __name__ == '__main__':
    export()

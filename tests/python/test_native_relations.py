"""Sage/native cross-checks; build the native verifier before running this file."""
import json
import os
from pathlib import Path
import subprocess
import sys
from itertools import product

from sage.all import Integers, PolynomialRing, ZZ
from hecke_congruences import (
    prepare_source_data, load_ideal_source_data, relation_spec,
    verify_hecke_relations_nim, verify_ordinary_identities,
    verify_divided_identities,
)
from staged_circuit import verify_staged_polynomial

ROOT = Path(__file__).resolve().parents[2]
BINARY = ROOT/'nim/.verify-hecke-relations-build/verify_hecke_relations'


def native_scalar(t, F, divisions, p=3, m=2, coordinate_moduli=(9,), b=2,
                  semantics='independent_monomials', limit=4096):
    """Run a rank-one exact arithmetic test without any modular-symbol assumptions."""
    spec = relation_spec([('test', F, b)], {'T': 2}, divisions,
                         witness_semantics=semantics, max_howell_dimension=limit)
    request = {'relations': spec, 'source': {
        'schema': 'hecke.mixed-source.v1', 'prime': p, 'exponent': m,
        'coordinate_moduli': list(coordinate_moduli), 'operators': {'T': [[t]]},
        'operators_are_oriented': True, 'metadata': {'source_scope': 'synthetic'},
    }}
    env = os.environ.copy()
    env['LD_LIBRARY_PATH'] = str(Path(sys.prefix)/'lib')+':'+env.get('LD_LIBRARY_PATH', '')
    result = subprocess.run([str(BINARY), '-'], input=json.dumps(request),
                            text=True, capture_output=True, env=env, check=False)
    report = json.loads(result.stdout)
    assert result.returncode in (0,1,3), (result.stderr,report)
    return report


def test_exhaustive_nested_witnesses():
    """Compare nested native division tests with exhaustive choices of intermediate elements on a small source."""
    R = Integers(9)
    S = PolynomialRing(R, names=('T','A','D'))
    T,A,D = S.gens()
    for n in (3,9):
        for t,c in product(range(n), repeat=2):
            expected = any((t-3*y)%n == 0 and (y-3*z)%n == 0 and (z-c)%n == 0
                           for y,z in product(range(n), repeat=2))
            report = native_scalar(t,D-c,{'A':(T,1),'D':(A,1)},coordinate_moduli=(n,))
            assert report['passed'] == expected, (n,t,c,report)
    report = native_scalar(0,D-1,{'A':(T,1),'D':(A,1)},limit=1)
    assert report['passed'] is None and report['state']=='inconclusive'


def test_paper_polynomial_semantics():
    """Enumerate independent chains for A and A^2, including their terminal sum."""
    R = Integers(9)
    S = PolynomialRing(R, names=('T','A'))
    T,A = S.gens()
    for t,c in product(range(9), repeat=2):
        first = [y for y in range(9) if (t-3*y)%9==0]
        second = [z for y in first for z in range(9) if (t*y-3*z)%9==0]
        expected = any((y+z-c)%9==0 for y in first for z in second)
        report = native_scalar(t,A**2+A-c,{'A':(T,1)})
        assert report['passed']==expected, (t,c,report)


def test_local_kernel_choices():
    """A terminal correction may use the entire torsion kernel, not a global map.

    Existing exhaustive nested and independent-chain tests also compare this
    fast path against enumeration, including impossible presentations.
    """
    S = PolynomialRing(Integers(9), names=('T', 'A'))
    T, A = S.gens()
    report = native_scalar(0, A-1, {'A': (T, 1)},
                           coordinate_moduli=(3,), b=1, limit=1)
    assert report['passed'] is True
    assert report['relations'][0]['verification_route'] == 'local_kernel_witness_replay'


def test_sources_and_ordinary_joint_relations():
    """Compare fresh Sage and fresh Nim for signed, unsigned, and ideal sources."""
    for p,m,d,n in ((2,3,10,3),(3,2,22,7),(5,2,10,2)):
        R=Integers(p**m)
        S=PolynomialRing(R, names=('T','U'))
        T,U=S.gens()
        spec=relation_spec([('joint',T-U, m)], {'T':n,'U':n})
        for q in range(p-1):
            for ideal in (None,{'scalar':p,'generators':[[[1,[1]]]]}):
                data=prepare_source_data(R,d,q,hecke_indices=(n,),ideal=ideal)
                sage=verify_hecke_relations_nim(spec,data)
                config={'prime':p,'exponent':m,'degree':d,'orientation':q,'recursive':False}
                if ideal is not None:config['ideal']=ideal
                native=verify_hecke_relations_nim(spec,compute=config)
                assert sage['passed'] and native['passed']
                assert sorted(sage['coordinate_moduli'])==sorted(native['coordinate_moduli'])
                del config['recursive']
                recursive=verify_hecke_relations_nim(spec,compute=config)
                assert recursive['passed']
                assert sorted(sage['coordinate_moduli'])==sorted(recursive['coordinate_moduli'])
        # Direct unsigned quotient also available for odd primes.
        unsigned=verify_hecke_relations_nim(spec,compute={
            'prime':p,'exponent':m,'degree':d,'orientation':0,'sign':0})
        assert unsigned['passed']


def test_mod27_torsion_and_zero_module():
    """Check native replay on a torsion source modulo 27 and on the zero module."""
    R=Integers(27)
    S=PolynomialRing(R, names=('T','U','A'))
    T,U,A=S.gens()
    for d in (0,12,22):
        c={0:1,12:7,22:4}[d]
        for q in (0,1):
            data=prepare_source_data(R,d,q)
            spec=relation_spec([('ordinary',U-(1+7**(d+1)),3),('divided',A**2-c,2)],
                               {'T':2,'U':7},{'A':(T,1)},witness_semantics='common_chain')
            result=verify_hecke_relations_nim(spec,data)
            P=PolynomialRing(R,'X'); X=P.gen()
            ordinary=verify_ordinary_identities(X-(1+7**(d+1)),7,data)
            divided=verify_divided_identities(X**2-c,X,2,1,2,data)
            assert result['passed']==(ordinary['passed'] and divided['passed'])


def test_archived_nested_ideal_relations():
    """Check all h-types and both orientations against the Sage circuit solver."""
    R=Integers(2187)
    S=PolynomialRing(R, names=('T','A','D'))
    T,A,D=S.gens()
    C=A**3-A
    cases=[(2,1-A**2,((0,2),(0,1),(0,1))),
           (8,1-A**2,((0,2),(1,2),(1,2))),
           (14,2+5*A,((0,2),(0,2),(0,1))),
           (32,2+A**2,((0,2),(0,1),(0,1)))]
    for d,h,allowed in cases:
        divisions={'A':(T,2),'D':(C**2+3*h*C,2)}
        Fs=[('Frobenius',(D**3-D)**2,1)]
        for s in range(3):
            u,v=allowed[s]
            Fs.append((f'branch{s}',(1-(A-s)**2)**6*(D-u)**2*(D-v)**2,1))
        for q in (0,1):
            data=load_ideal_source_data(R,d,q,ROOT/f'source_data/p3_ideal_9_T2_mod2187/degree_{d}.npz')
            report=verify_hecke_relations_nim(relation_spec(Fs,{'T':2},divisions),data)
            assert report['passed'],report
            Tdata=data['archived_hecke_matrices'][2]
            for name,F,b in Fs:
                sage=verify_staged_polynomial(F,{'T':(-1)**q*Tdata['normalized_matrix']},
                    divisions,Tdata['coordinate_moduli'],3,b=b)
                assert sage['passed']


def test_error_paths_and_prescribed_inputs():
    """Check invalid requests and the requirement that prescribed inputs remain fixed."""
    R=Integers(27)
    S=PolynomialRing(R,names=('T','A'))
    T,A=S.gens()
    data=prepare_source_data(R,12,0,hecke_indices=(2,))
    spec=relation_spec([('impossible_constant',S(1),3)],{'T':2},{'A':(T,1)})
    assert verify_hecke_relations_nim(spec,data)['passed'] is False
    spec['relations'][0]['input_polynomial']=[]  # Gamma_0 inputs, not the zero module
    assert verify_hecke_relations_nim(spec,data)['passed'] is True
    spec['relations'][0]['polynomial']=[[1,[0,1]],[-1,[0,0]]]
    assert verify_hecke_relations_nim(spec,data)['passed'] is True
    spec['coefficient_modulus']=9
    try:
        verify_hecke_relations_nim(spec,data)
    except RuntimeError as error:
        assert 'different coefficient rings' in str(error)
    else:
        raise AssertionError('wrong coefficient ring was accepted')


def test_recursive_verification():
    """Compare recursive full-domain proofs with whole-source verification.

    Includes odd signs, unsplit modules, nonprincipal/zero ideals, joint
    numerators, nested relations, failure, and prescribed inputs.
    """
    successes = 0
    savings = 0
    fallbacks = 0
    for p,m,d,ell in ((3,2,22,7), (3,2,28,7), (2,3,18,5), (5,1,22,2)):
        R=Integers(p**m)
        S=PolynomialRing(R,names=('T','U','A','D'))
        T,U,A,D=S.gens()
        second = (7 if ell==2 else 2) if p!=2 else 3
        bindings={'T':ell,'U':second}
        specs = [
            relation_spec([('ordinary',T-(1+ell**(d+1)),m)],bindings,
                          {'A':(T,1),'D':(A,1)}),
            relation_spec([('zero',S(0),m)],bindings,{'A':(T,1),'D':(A,1)}),
            relation_spec([('false',S(1),1)],bindings,{'A':(T,1),'D':(A,1)}),
            relation_spec([('joint_division',A**2-A,1)],bindings,
                          {'A':(p*(T+U),1),'D':(A,1)}),
            relation_spec([('nested',D**2-D,1)],bindings,
                          {'A':(p*T,1),'D':(p*A,1)}),
        ]
        specs[-1]['relations'][0]['input_polynomial']=[[1,[1,0,0,0]]]
        for q in (range(2) if p!=2 else range(1)):
            for ideal in (None,{}, {'scalar':p,'generators':[[[1,[1,0]]],[[1,[0,1]]]]}):
                config=dict(prime=p,exponent=m,degree=d,orientation=q)
                if ideal is not None:config['ideal']=ideal
                for spec in specs:
                    full=verify_hecke_relations_nim(spec,
                        compute={**config,'recursive_verification':False},executable=BINARY)
                    rec=verify_hecke_relations_nim(spec,compute=config,executable=BINARY)
                    assert rec['state']==full['state'],(config,spec,rec,full)
                    assert rec['verification_scope']=='whole_source'
                    assert rec['all_weight_propagation_proved'] is False
                    assert rec['transfer_and_span_checked'] is True
                    assert rec['verified_presentation']==spec
                    successes += rec['state']=='passed'
                    savings += rec['checked_input_count']<rec['rank']
                    fallbacks += rec['recursive_route']=='whole_source_fallback'
                    assert all(x['transfer_checked'] for x in rec['recursive_dependencies'])
    assert successes and savings and fallbacks

    # Full-domain tests at terminal depth zero and dyadic a<=d<b direct bases.
    R=Integers(8); S=PolynomialRing(R,names=('T','A'));T,A=S.gens()
    spec=relation_spec([('domain',A,0)],{'T':3},{'A':(2*T,1)})
    for d in (0,8,10,18):
        rec=verify_hecke_relations_nim(spec,compute=dict(prime=ZZ(2),exponent=ZZ(3),
            degree=ZZ(d),orientation=ZZ(0),recursive_verification=True),executable=BINARY)
        assert rec['passed'] is True
    for changes in ({'degree':20},{'orientation':1},{'sign':1},{'recursive':False}):
        try:
            verify_hecke_relations_nim(spec,compute=dict(prime=2,exponent=3,
                degree=18,orientation=0,recursive_verification=True) | changes,
                executable=BINARY)
        except RuntimeError:
            pass
        else:
            raise AssertionError(('invalid recursive parameters accepted',changes))
    S=PolynomialRing(Integers(2),'T'); T=S.gen()
    spec=relation_spec([('zero',0*T,1)],{'T':3})
    rec=verify_hecke_relations_nim(spec,compute=dict(prime=2,exponent=1,
        degree=4,orientation=0),executable=BINARY)
    assert rec['recursive_route']=='direct_base'


def test_recursive_archived_actions():
    """Reuse compact sources without replacing recursive verification by replay."""
    from p7_mod49 import p7_mod49_nim_relation_spec
    from verify_hecke_relations import _recursive_archived_sources

    config = dict(prime=7, exponent=2, degree=56, orientation=1)
    spec = p7_mod49_nim_relation_spec(56, 1, 2)
    fresh = verify_hecke_relations_nim(spec, compute=config, timeout=30)
    archived = dict(config, archive_directory=str(
        ROOT/'source_data/p7_mod49_recursive/G_mod49'))
    reused = verify_hecke_relations_nim(spec, compute=archived, timeout=30)
    assert fresh['passed'] and reused['passed']
    assert fresh['recursive_trace'] == reused['recursive_trace']
    assert reused['archived_actions_reused']
    assert reused['transfer_and_span_checked']
    assert reused['source_archives']

    # Wrong cyclic coordinates must be rejected, not used as a new basis.
    records = _recursive_archived_sources(archived, spec)
    records[0]['exponents'][0] = 3-records[0]['exponents'][0]
    try:
        verify_hecke_relations_nim(spec, compute=dict(config, archived_sources=records))
    except RuntimeError as error:
        assert 'cyclic coordinates disagree' in str(error)
    else:
        raise AssertionError('mismatched archived coordinates accepted')

    # Exercise a modulo-343 transfer independently of expensive selector solving.
    S = PolynomialRing(Integers(343), names=('T', 'U'))
    zero = relation_spec([('map check', S.zero(), 1)], {'T':3, 'U':29})
    report = verify_hecke_relations_nim(zero, compute=dict(
        prime=7, exponent=3, degree=392, orientation=0,
        archive_directory=str(ROOT/'source_data/p7_mod49_recursive/Q_selectors_mod343')),
        timeout=30)
    assert report['passed'] and report['transfer_and_span_checked']
    assert report['recursive_route'] == 'inherited_images_and_complement'


def test_literal_source_sandwiches():
    """Compare E B E, with an extra initial E, against exhaustive Z/9 outputs."""
    from verify_hecke_relations import NimRelationVerifier
    names = ['T', 'V', 'B', 'E', 'J']

    def term(c, variable=None):
        """Encode one sparse polynomial term in the variable order used by the test."""
        exponents = [0]*len(names)
        if variable is not None:
            exponents[names.index(variable)] = 1
        return [str(c), exponents]

    with NimRelationVerifier() as session:
        for t, c in product(range(9), range(3)):
            def V(x):
                """Enumerate outputs of the first division relation at this test input."""
                return {y for y in range(9) if (t*x-3*y) % 9 == 0}
            def B(x):
                """Enumerate the sum of the first division relation and the identity at this input."""
                return {(y+x) % 9 for y in V(x)}
            def J(x):
                """Enumerate the literal selector composition, retaining both selector copies."""
                return {z for y in V(x) for b in B(y) for z in V(b)}
            expected = any((z-c*x) % 9 == 0 for x in V(1) for z in J(x))
            spec = {
                'schema': 'hecke.relations.v1', 'coefficient_modulus': 9,
                'variables': names, 'hecke_operators': {'T': 2},
                'divisions': [{'variable': 'V', 'numerator': [term(1, 'T')], 'power': 1}],
                'presentations': [
                    {'variable': 'B', 'polynomial': [term(1, 'V'), term(1)]},
                    {'variable': 'E', 'polynomial': [term(1, 'V')]},
                    {'variable': 'J', 'factors': ['E', 'B', 'E']},
                ],
                'relations': [{'name': 'sandwich', 'polynomial': [term(1, 'J'), term(-c)],
                               'input_presentation': 'E', 'terminal_power': 2}],
                'witness_semantics': 'independent_monomials',
            }
            report = session.verify_request({'relations': spec, 'source': {
                'schema': 'hecke.mixed-source.v1', 'prime': 3, 'exponent': 2,
                'coordinate_moduli': [9], 'operators': {'T': [[t]]},
                'operators_are_oriented': True, 'metadata': {'source_scope': 'synthetic'},
            }}, timeout=10)
            assert report['passed'] == expected, (t, c, report)


def test_source_preparation_cache():
    """Cache preparation, not mathematical claims; no classification scan."""
    from unittest.mock import patch
    from verify_hecke_relations import (
        NimRelationVerifier, _SourcePreparationCache, _recursive_archived_sources,
        _archive_stamp,
    )
    S = PolynomialRing(Integers(343), names=('T', 'U'))
    spec = relation_spec([('zero', S.zero(), 1)], {'T': 3, 'U': 29})
    config = dict(prime=7, exponent=3, degree=48, orientation=0,
                  archive_directory=str(ROOT/'source_data/p7_mod49_transfer_maps/Q_selectors_mod343'))
    cache = _SourcePreparationCache()
    first = _recursive_archived_sources(config, spec, cache)
    second = _recursive_archived_sources(config, spec, cache)
    assert first == second and cache.misses == 1 and cache.hits == 1
    second[0]['actions']['3'][0][0] += 1
    assert _recursive_archived_sources(config, spec, cache) == first
    # Simulate a changed file timestamp without touching any production data.
    def changed_stamp(path):
        """Change the simulated archive identifier to test invalidation of a cached source."""
        stamp = _archive_stamp(path)
        return (*stamp[:-1], stamp[-1]+1)
    with patch('verify_hecke_relations._archive_stamp', changed_stamp):
        assert _recursive_archived_sources(config, spec, cache) == first
    assert cache.misses == 2
    tiny = _SourcePreparationCache(1)
    tiny.put('oversized', {'example': 1})
    assert tiny.bytes == 0
    cache.clear()
    assert cache.bytes == 0 and not cache.entries

    # Only a zero identity: test real stored transfer compatibility and reuse.
    config['degree'] = 400
    with NimRelationVerifier() as session:
        for repeated in (False, True):
            report = verify_hecke_relations_nim(spec, compute=config,
                                               session=session, timeout=20)
            assert report['passed'] and report['transfer_and_span_checked']
            assert report['archived_maps_reused']
            assert report['verification_cache_hit'] == repeated
            if repeated:
                assert report['source_preparation_cache']['hits'] >= 2
                assert report['prepared_source_cache_hits'] >= 2
        config['orientation'] = 2
        oriented = verify_hecke_relations_nim(spec, compute=config,
                                             session=session, timeout=20)
        assert oriented['passed'] and not oriented['verification_cache_hit']
        assert oriented['prepared_source_cache_hits'] >= 2


def test_mod125_session_and_parameters():
    """Small real-source smoke test and cache binding, not a full classification scan."""
    from p5_mod125 import (load_mod125_parameters, mod125_relation_spec,
                          mod125_possible_signatures, load_mod125_strong_representatives)
    from verify_hecke_relations import NimRelationVerifier, _recursive_archived_sources
    rows = load_mod125_parameters()
    possible = mod125_possible_signatures(rows)
    assert sum(map(len, possible.values())) == 1100
    signatures = load_mod125_strong_representatives(ROOT/'strong_signatures/p5_m3')
    observed = {r: set() for r in possible}
    for k, a, b in signatures:
        observed[k % 100].add((a, b))
    assert possible == observed
    spec = mod125_relation_spec(rows[12])
    config = dict(prime=5, exponent=4, degree=12, orientation=0,
                  archive_directory=str(ROOT/'source_data/p5_mod625_recursive'))
    records = _recursive_archived_sources(config, spec)
    del config['archive_directory']
    config['archived_sources'] = records
    with NimRelationVerifier() as session:
        for repeated in (False, True):
            report = session.verify_request({'relations': spec, 'compute': config}, timeout=30)
            assert report['passed'] and report['verification_cache_hit'] == repeated
        # Change an action without changing the claimed file hash: the actual
        # archived content is included in the in-memory verification key.
        for i in range(len(records[0]['actions']['2'])):
            records[0]['actions']['2'][i][i] += 1
        changed = session.verify_request({'relations': spec, 'compute': config}, timeout=30)
        assert not changed['verification_cache_hit'] and changed['state'] == 'failed'


def test_compact_witness_packets():
    """Real torsion example, fresh replay, and rejection of corrupted choices."""
    import gzip
    import tempfile
    from p5_mod125 import load_mod125_parameters, mod125_relation_spec
    from verify_hecke_relations import NimRelationVerifier, verify_hecke_relations_nim
    spec = mod125_relation_spec(load_mod125_parameters()[26])
    config = dict(prime=5, exponent=4, degree=26, orientation=0,
                  archive_directory=str(ROOT/'source_data/p5_mod625_recursive'))
    with tempfile.TemporaryDirectory(prefix='compact-witness-test-') as folder:
        produced = verify_hecke_relations_nim(spec, compute=config,
            witness_directory=folder, timeout=60)
        assert produced['passed']
        with NimRelationVerifier() as session:
            replayed = verify_hecke_relations_nim(spec, compute=config,
                witness_directory=folder, witness_mode='replay', session=session, timeout=60)
            assert replayed['passed']
            assert all(r['witness_file_reused'] for r in replayed['relations'])
        changed = False
        for path in Path(folder).glob('*.json.gz'):
            packet = json.loads(gzip.decompress(path.read_bytes()))
            if packet.get('recipe') or packet['choices']:
                packet.pop('recipe', None)
                packet['choices'] = []
                path.write_bytes(gzip.compress(json.dumps(packet).encode()))
                changed = True
                break
        assert changed, 'test must exercise noncanonical choices'
        try:
            verify_hecke_relations_nim(spec, compute=config,
                witness_directory=folder, witness_mode='replay', timeout=60)
        except RuntimeError as error:
            assert 'saved witness equations' in str(error)
        else:
            raise AssertionError('corrupted witness accepted')
    # Never silently run discovery when a replay packet is absent.
    with tempfile.TemporaryDirectory(prefix='missing-witness-test-') as folder:
        try:
            verify_hecke_relations_nim(spec, compute=config,
                witness_directory=folder, witness_mode='replay', timeout=60)
        except RuntimeError as error:
            assert 'missing witness packet' in str(error)
        else:
            raise AssertionError('missing packet accepted')


def test_structured_division_choices():
    """Previously capped real cases pass by exact replay, with the solver disabled."""
    import gzip
    import tempfile
    from p5_mod125 import load_mod125_parameters, mod125_relation_spec
    from verify_hecke_relations import NimRelationVerifier
    rows = load_mod125_parameters()
    for degree in (26, 130, 250, 270):
        spec = mod125_relation_spec(rows[degree % 100])
        config = dict(prime=5, exponent=4, degree=degree, orientation=0,
                      archive_directory=str(ROOT/'source_data/p5_mod625_recursive'),
                      allow_missing_lower_orientations=True)
        with tempfile.TemporaryDirectory(prefix='structured-choices-test-') as folder:
            produced = verify_hecke_relations_nim(spec, compute=config,
                witness_directory=folder, witness_solver_limit=1, timeout=60)
            assert produced['passed'], produced
            routes = [r['verification_route'] for r in produced['relations']]
            assert 'structured_witness_replay' in routes
            assert all(route in ('ordinary_polynomial', 'explicit_witness_replay',
                                 'structured_witness_replay') for route in routes)
            assert len(produced['relations']) == 8
            with NimRelationVerifier() as session:
                replayed = verify_hecke_relations_nim(spec, compute=config,
                    witness_directory=folder, witness_mode='replay',
                    session=session, timeout=60)
                assert replayed['passed']
            # A packet is not accepted merely because discovery reported success.
            # Deliberately break a recipe division equation on a free factor.
            changed = False
            for path in Path(folder).glob('*.json.gz'):
                packet = json.loads(gzip.decompress(path.read_bytes()))
                if packet.get('recipe'):
                    orders = produced['coordinate_moduli']
                    index = orders.index(625)
                    entries = packet['recipe']['outputs'][0]['entries']
                    slot = index*len(orders)+index
                    entries[slot] = (entries[slot]+1) % 625
                    path.write_bytes(gzip.compress(json.dumps(packet).encode()))
                    changed = True
                    break
            assert changed
            try:
                verify_hecke_relations_nim(spec, compute=config,
                    witness_directory=folder, witness_mode='replay', timeout=60)
            except RuntimeError as error:
                assert 'recipe division' in str(error)
            else:
                raise AssertionError('invalid structured division choice accepted')


def test_streamed_legacy_packets_and_memory_budget():
    """Replay v1 corrections across row batches; reject duplicates; cap solves."""
    import gzip
    import tempfile
    from verify_hecke_relations import NimRelationVerifier
    n = 17  # more than one replay batch
    request = {
        'relations': {
            'schema': 'hecke.relations.v1', 'coefficient_modulus': 9,
            'variables': ['T', 'Z'],
            'divisions': [{'variable': 'Z', 'numerator': [[1, [1, 0]]], 'power': 1}],
            'relations': [{'name': 'test', 'polynomial': [[1, [0, 1]], [6, [0, 0]]],
                           'terminal_power': 2}],
        },
        'source': {'schema': 'hecke.mixed-source.v1', 'prime': 3, 'exponent': 2,
                   'coordinate_moduli': [9]*n, 'operators': {'T': [[0]*n for _ in range(n)]},
                   'operators_are_oriented': True, 'metadata': {'source_scope': 'synthetic'}},
    }
    with tempfile.TemporaryDirectory(prefix='streamed-witness-test-') as folder:
        request.update(witness_directory=folder, witness_mode='produce')
        with NimRelationVerifier() as session:
            report = session.verify_request(request)
        assert report['passed'], report
        path = next(Path(folder).glob('*.json.gz'))
        packet = json.loads(gzip.decompress(path.read_bytes()))
        assert len(packet['choices']) == n
        packet['schema'] = 'hecke.compact-relation-witness.v1'
        packet['choices'].reverse()  # legacy packets need not be sorted
        path.write_bytes(gzip.compress(json.dumps(packet).encode()))
        request['witness_mode'] = 'replay'
        with NimRelationVerifier() as session:
            assert session.verify_request(request)['passed']
        packet['choices'].append(packet['choices'][0])
        path.write_bytes(gzip.compress(json.dumps(packet).encode()))
        try:
            with NimRelationVerifier() as session:
                session.verify_request(request)
        except RuntimeError as error:
            assert 'duplicate' in str(error)
        else:
            raise AssertionError('duplicate legacy correction accepted')
    request.pop('witness_directory')
    request.pop('witness_mode')
    request['witness_memory_limit_mb'] = 1
    request['relations']['relations'][0]['polynomial'] = [[1, [0, 200]], [8, [0, 0]]]
    with NimRelationVerifier() as session:
        limited = session.verify_request(request)
    assert limited['state'] == 'inconclusive' and limited['passed'] is None, limited
    assert limited['relations'][0]['verification_route'] == 'howell_memory_limit', limited


def test_native_source_archive_loader():
    """Nim-loaded recursive sources produce packets the Sage loader can replay."""
    import tempfile
    from verify_hecke_relations import NimRelationVerifier, verify_hecke_relations_nim
    S = PolynomialRing(Integers(625), names=('T',))
    T = S.gen()
    spec = relation_spec([('zero', T-T, 1)], {'T': 2})
    with tempfile.TemporaryDirectory(prefix='native-archive-test-') as folder:
        for d, q in ((750, 0), (750, 1), (1600, 0), (3248, 1)):
            config = dict(prime=5, exponent=4, degree=d, orientation=q,
                archive_directory=str(ROOT/'source_data/p5_mod625_recursive'),
                allow_missing_lower_orientations=True)
            with NimRelationVerifier() as session:
                native = session.verify_request(dict(relations=spec, compute=dict(config),
                    witness_directory=folder, witness_mode='produce'), timeout=60)
            assert native['state'] == 'passed', native
            replay = verify_hecke_relations_nim(spec, compute=config,
                witness_directory=folder, witness_mode='replay', timeout=60)
            assert replay['state'] == 'passed', replay
            assert native['source_archives'] == replay['source_archives']


def test_supplementary_sources_and_witnesses():
    """Replay read-only packets and check transfers to supplementary signs."""
    import tempfile
    import hashlib
    import gzip
    S = PolynomialRing(Integers(625), names=('T',))
    T = S.gen()
    spec = relation_spec([('zero', T-T, 1)], {'T': 2})
    def run(request):
        """Run this test request with the specified supplementary source and intermediate-element archives."""
        child = subprocess.run([str(BINARY), '-'], input=json.dumps(request),
            text=True, capture_output=True, timeout=120)
        result = json.loads(child.stdout)
        assert child.returncode in (0, 1, 2, 3), (child.stderr, result)
        return result
    config = dict(prime=5, exponent=4, degree=2500, orientation=1,
        archive_directory=str(ROOT/'source_data/p5_mod625_recursive'),
        allow_missing_lower_orientations=True)
    old = run(dict(relations=spec, compute=config))
    assert old['state']=='passed' and old['recursive_route']=='whole_source_fallback', old
    config = dict(config, supplementary_archive_directories=[
        str(ROOT/'source_data/p5_mod625_lower_minus')])
    with tempfile.TemporaryDirectory(prefix='supplementary-replay-') as folder:
        primary, extra = Path(folder)/'primary', Path(folder)/'extra'
        primary.mkdir(); extra.mkdir()
        produced = run(dict(relations=spec, compute=config,
            witness_directory=str(extra), witness_mode='produce'))
        assert produced['state']=='passed', produced
        assert produced['recursive_route']=='inherited_images_and_complement'
        assert produced['transfer_and_span_checked']
        assert all(x['state']=='passed' and x['transfer_checked']
                   for x in produced['recursive_dependencies'])
        packets = {p: hashlib.sha256(p.read_bytes()).hexdigest()
                   for p in extra.glob('*.json.gz')}
        request = dict(relations=spec, compute=config,
            witness_directory=str(primary), witness_read_directories=[str(extra)],
            witness_mode='replay')
        replay = run(request)
        assert replay['state']=='passed', replay
        assert all(x['witness_file_reused'] for x in replay['relations'])
        assert not list(primary.iterdir())
        assert packets == {p: hashlib.sha256(p.read_bytes()).hexdigest() for p in packets}
        target = Path(replay['relations'][0]['witness_file'])
        packet = json.loads(gzip.decompress(target.read_bytes()))
        packet['binding'] = 'incorrect'
        target.write_bytes(gzip.compress(json.dumps(packet).encode()))
        assert run(request)['state']=='error', 'corrupt supplementary packet accepted'
        # A malformed primary archive must not be hidden by a valid fallback.
        (primary/'degree_2500.npz').write_bytes(b'invalid ZIP')
        bad = dict(config, archive_directory=str(primary),
            supplementary_archive_directories=[str(ROOT/'source_data/p5_mod625_recursive')])
        assert run(dict(relations=spec, compute=bad))['state']=='error'


def test_persistent_verification_checkpoints():
    """Fresh-process hits, transitive invalidation, and audit replay bypass."""
    import tempfile
    import shutil
    import gzip
    import time
    S=PolynomialRing(Integers(625), names=('T',))
    T=S.gen()
    spec=relation_spec([('zero', T-T, 1)], {'T': 2})
    def run(request, executable=None):
        """Run the checkpoint test request and collect the native report."""
        start=time.monotonic()
        child=subprocess.run([str(executable or BINARY), '-'], input=json.dumps(request),
            text=True,capture_output=True,timeout=120)
        result=json.loads(child.stdout)
        assert child.returncode in (0,1,2,3), (child.stderr,result)
        return result,time.monotonic()-start
    with tempfile.TemporaryDirectory(prefix='persistent-verification-') as folder:
        folder=Path(folder)
        primary,extra,packets,checkpoints=[folder/x for x in ('primary','extra','packets','checkpoints')]
        for path in (primary,extra,packets,checkpoints):path.mkdir()
        for d in (10,760):shutil.copyfile(ROOT/f'source_data/p5_mod625_recursive/degree_{d}.npz',primary/f'degree_{d}.npz')
        shutil.copyfile(ROOT/'source_data/p5_mod625_lower_minus/degree_10.npz',extra/'degree_10.npz')
        request=dict(relations=spec,witness_directory=str(packets),witness_mode='produce',
            checkpoint_directory=str(checkpoints),compute=dict(prime=5,exponent=4,degree=760,
                orientation=0,archive_directory=str(primary),
                supplementary_archive_directories=[str(extra)],allow_missing_lower_orientations=True))
        first,t1=run(request)
        assert first['state']=='passed' and not first['persistent_checkpoint_hit'], first
        second,t2=run(request)
        assert second['state']=='passed' and second['persistent_checkpoint_hit'], second
        variant=folder/'verifier-variant'
        shutil.copy2(BINARY,variant)
        with variant.open('ab') as f:f.write(b'changed executable identity')
        assert not run(request,variant)[0]['persistent_checkpoint_hit']
        audit,_=run(dict(request,witness_mode='replay'))
        assert audit['state']=='passed' and not audit.get('persistent_checkpoint_hit'), audit
        # Alter a lower source file without changing its valid module data.
        with (extra/'degree_10.npz').open('ab') as f:f.write(b'checkpoint invalidation test')
        changed,_=run(request)
        assert changed['state']=='passed' and not changed['persistent_checkpoint_hit'], changed
        assert run(request)[0]['persistent_checkpoint_hit']
        # The optional source was absent when the previous pass was checked.
        shutil.copyfile(primary/'degree_760.npz',extra/'degree_760.npz')
        assert not run(request)[0]['persistent_checkpoint_hit']
        assert run(request)[0]['persistent_checkpoint_hit']
        # Specification and orientation are part of the identity of a proof.
        altered=json.loads(json.dumps(request))
        altered['relations']['relations'][0]['name']='other_zero'
        assert not run(altered)[0]['persistent_checkpoint_hit']
        invalid=dict(request,relations=relation_spec([('not_zero',S(1),1)],{'T':2}))
        assert run(invalid)[0]['state']=='failed'
        different=json.loads(json.dumps(request))
        different['compute']['orientation']=2
        assert not run(different)[0]['persistent_checkpoint_hit']
        # A corrupt checkpoint is discarded and regenerated by verification.
        for path in checkpoints.glob('*.json.gz'):path.write_bytes(b'corrupt cache')
        assert not run(request)[0]['persistent_checkpoint_hit']
        # Corrupt a TRANSITIVE witness: unchanged root cache must not hide it.
        for path in packets.glob('*.json.gz'):
            packet=json.loads(gzip.decompress(path.read_bytes()))
            if packet['source']['degree']==10 and packet['source']['orientation']==1 and packet['relation']=='zero':
                packet['binding']='incorrect'
                path.write_bytes(gzip.compress(json.dumps(packet).encode()))
                break
        else:raise AssertionError('missing lower packet for negative test')
        bad,_=run(request)
        assert bad['state']=='error', bad
        print(f'Checkpoint smoke: first={t1:.3f}s restart={t2:.3f}s; negative tests passed')


def test_mod49_success_gate():
    """Check that incomplete or failed predecessor records cannot release the modulo-49 job."""
    from queue_mod49_witnesses import predecessor_succeeded, stage_succeeded
    good=dict(schema='hecke.mod125-witness-production-status.v2',state='completed',
        working_modulus=625,classification_modulus=125,completed_count=5375,
        total_cases=5375,all_requested_witnesses_produced=True,failed=[],active=[])
    assert predecessor_succeeded(good,False)
    assert not predecessor_succeeded(good,True)
    for changed in ({'state':'running'},{'state':'stopped'},{'state':'failed'},
                    {'completed_count':5374},{'failed':[{'error':'x'}]},
                    {'active':[{'degree':2}]},{'all_requested_witnesses_produced':False},
                    {'working_modulus':343}):
        assert not predecessor_succeeded(good|changed,False)
    assert stage_succeeded(good,5375)
    assert not stage_succeeded(good|{'state':'inconclusive'},5375)


def _parallel_test_case(d, q, session=None):
    """Small requests checking session ownership, ordering and event delivery."""
    S = PolynomialRing(Integers(9), names=('T',))
    T = S.gen()
    request = {'relations': relation_spec([('zero', T-T, 1)], {'T': 2}),
               'source': {'schema': 'hecke.mixed-source.v1', 'prime': 3,
                          'exponent': 2, 'coordinate_moduli': [9],
                          'operators': {'T': [[3]]}, 'operators_are_oriented': True,
                          'metadata': {'degree': d, 'orientation': q}}}
    report = session.verify_request(request, timeout=10)
    return dict(report, degree=d, orientation=q, worker_pid=os.getpid(),
                native_pid=session._process.pid)


def test_parallel_sessions_and_progress():
    """Check isolation of parallel verifier sessions and their progress reports."""
    from contextlib import closing
    from verify_hecke_relations import parallel_relation_cases
    cases = [(d, q) for d in range(0, 42, 2) for q in (0, 1)]
    events = []
    with closing(parallel_relation_cases(_parallel_test_case, cases,
            dependency_period=14, workers=4, on_progress=events.append)) as stream:
        results = list(stream)
    assert len(results) == len(cases) and all(r['passed'] for r in results)
    assert len({r['worker_pid'] for r in results}) == 4
    for residue in range(0, 14, 2):
        chain = [r for r in results if r['degree'] % 14 == residue]
        assert len({r['worker_pid'] for r in chain}) == 1
        assert [(r['degree'], r['orientation']) for r in chain] == sorted(
            (r['degree'], r['orientation']) for r in chain)
    assert any(e.get('relation') == 'zero' for e in events)
    # Closing a partially consumed iterator must leave no native child behind.
    with closing(parallel_relation_cases(_parallel_test_case, cases,
            dependency_period=14, workers=1)) as stream:
        first = next(stream)
    for pid in (first['worker_pid'], first['native_pid']):
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            pass
        else:
            raise AssertionError(f'worker or native child still exists: {pid}')


if __name__=='__main__':
    os.chdir(ROOT)
    for test in (test_exhaustive_nested_witnesses,test_paper_polynomial_semantics,
                 test_sources_and_ordinary_joint_relations,test_mod27_torsion_and_zero_module,
                 test_archived_nested_ideal_relations,test_error_paths_and_prescribed_inputs,
                 test_recursive_verification,test_recursive_archived_actions,
                 test_literal_source_sandwiches,test_source_preparation_cache,
                 test_mod125_session_and_parameters,test_compact_witness_packets,
                 test_native_source_archive_loader,test_structured_division_choices,
                 test_supplementary_sources_and_witnesses,
                 test_persistent_verification_checkpoints,
                 test_mod49_success_gate,
                 test_streamed_legacy_packets_and_memory_budget,
                 test_parallel_sessions_and_progress):
        test()
        print(test.__name__, 'passed',flush=True)

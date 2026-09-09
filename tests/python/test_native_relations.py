"""Sage/native cross-checks; build the native verifier before running this file."""
import json
import os
from pathlib import Path
import subprocess
import sys
from itertools import product

from sage.all import Integers, PolynomialRing
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
                config={'prime':p,'exponent':m,'degree':d,'orientation':q}
                if ideal is not None:config['ideal']=ideal
                native=verify_hecke_relations_nim(spec,compute=config)
                assert sage['passed'] and native['passed']
                assert sorted(sage['coordinate_moduli'])==sorted(native['coordinate_moduli'])
                config['recursive']=True
                recursive=verify_hecke_relations_nim(spec,compute=config)
                assert recursive['passed']
                assert sorted(sage['coordinate_moduli'])==sorted(recursive['coordinate_moduli'])
        # Direct unsigned quotient also available for odd primes.
        unsigned=verify_hecke_relations_nim(spec,compute={
            'prime':p,'exponent':m,'degree':d,'orientation':0,'sign':0})
        assert unsigned['passed']


def test_mod27_torsion_and_zero_module():
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


if __name__=='__main__':
    os.chdir(ROOT)
    for test in (test_exhaustive_nested_witnesses,test_paper_polynomial_semantics,
                 test_sources_and_ordinary_joint_relations,test_mod27_torsion_and_zero_module,
                 test_archived_nested_ideal_relations,test_error_paths_and_prescribed_inputs):
        test()
        print(test.__name__, 'passed',flush=True)

"""Exact recursive/direct/ideal replay; optionally cross-check the Nim producer.

Set HECKE_SOURCE_EXECUTABLE to a separately compiled compute_source_data.
All generated files live in a temporary directory, never in source_data/.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
import numpy as np
from sage.all import ZZ, Integers, PolynomialRing, matrix, diagonal_matrix, identity_matrix
from hecke_action import RecursiveContext
from manin_quotient import direct_manin_presentation, direct_signed_manin_presentation
from modular_matrix import row_basis, chain_ring_coordinates
from modular_polynomial import evaluate_polynomial
from mixed_endomorphisms import image_coordinates, mixed_matrix_is_zero
from compute_source_data import prepare_source_data
from load_source_data import load_source_data, load_ideal_source_data
from identity_verification import (verify_ordinary_identities, verify_divided_identities,
                                   _hecke_matrix_on_source)


class SourceArchitectureTests(unittest.TestCase):
    """Regression checks for the shared direct, recursive and ideal-image source interfaces."""
    def test_recursive_default_and_lazy_actions(self):
        """Check that recursion is the default and Hecke actions are constructed only when requested."""
        for p,m,d,ns in ((2,3,18,(3,5)),(3,2,28,(2,7)),(5,1,22,(2,19))):
            R=Integers(p**m)
            ctx=RecursiveContext(R,ns)
            for q in range(1 if p==2 else 2):
                data=prepare_source_data(R,d,q)
                self.assertEqual(data['construction'],'recursive')
                M=data['recursive_module']
                self.assertTrue(M.recursive)
                direct=ctx.direct_module(d,0 if p==2 else (-1)**q)
                forward=M.lifts*direct.reduction
                moduli=tuple(p**e for e in direct.exponents)
                for n in ns:
                    T=_hecke_matrix_on_source(n,data,True)['normalized_matrix']
                    self.assertTrue(mixed_matrix_is_zero(T*forward-forward*direct.actions[n],moduli))
                    self.assertIs(T,_hecke_matrix_on_source(n,data,False)['normalized_matrix'])
                    self.assertIs(M,data['recursive_module'])
                legacy=prepare_source_data(R,d,q,recursive=False)
                self.assertIsNotNone(legacy['presentation'])
                self.assertEqual(legacy['construction'],'direct')

    def test_high_precision_direct_is_lazy(self):
        """Check that high-precision direct construction does not eagerly compute all Hecke actions."""
        ctx = RecursiveContext(Integers(3**15),(2,7),retain_lifts=False)
        self.assertIsNone(ctx.A)
        data = prepare_source_data(ctx.R,12,0,hecke_indices=(2,7),
            ideal={'scalar':9},context=ctx,audit=True)
        self.assertTrue(data['coordinates']['surviving_indices'])
        self.assertIsNone(ctx.A)

    def test_recursive_maps(self):
        """Check the stored recursive transfer maps and source conventions."""
        for p,m,ns in [(2,1,(3,5)),(2,2,(3,5)),(3,1,(2,7)),(3,2,(2,7)),(5,1,(2,19)),(7,1,(3,29))]:
            R = Integers(p**m)
            ctx = RecursiveContext(R,ns)
            for d in sorted(set([0,ctx.b-2,ctx.b,ctx.a,ctx.a+ctx.b-2])):
                if d % 2:
                    continue
                for sign in ([0] if p==2 else [1,-1]):
                    with self.subTest(p=p,m=m,d=d,sign=sign):
                        a = ctx.direct_module(d,sign)
                        b = ctx.build_modular_symbols_recursive(d,sign)
                        self.assertEqual(sorted(a.exponents),sorted(b.exponents))
                        am, bm = [p**e for e in a.exponents], [p**e for e in b.exponents]
                        f,g = a.lifts*b.reduction, b.lifts*a.reduction
                        self.assertTrue(mixed_matrix_is_zero(f*g-identity_matrix(R,len(am)),am))
                        self.assertTrue(mixed_matrix_is_zero(g*f-identity_matrix(R,len(bm)),bm))
                        P = direct_manin_presentation(d,R) if sign==0 else direct_signed_manin_presentation(d,R,sign)
                        self.assertTrue(mixed_matrix_is_zero(P['B_mod']*b.reduction,bm))
                        for n in ns:
                            self.assertTrue(mixed_matrix_is_zero(a.actions[n]*f-f*b.actions[n],bm))
                ctx.splits.clear()

    def test_images_without_scalar_and_internal_precision(self):
        """Check ideals without a scalar generator and the precision retained in their image modules."""
        for p in (2,3,5,7):
            R = Integers(p**2)
            B = diagonal_matrix(R,[p,0])
            T = diagonal_matrix(R,[1,p])
            for G in (matrix(R,0,2),T,identity_matrix(R,2),matrix(R,[[0,p]])):
                for s in (0,1,p,p**2):
                    H = image_coordinates(B,G,{1:T},s,audit=True)
                    expected = row_basis(B.stack(G).stack(s*identity_matrix(R,2)))
                    self.assertEqual(row_basis(B.stack(H['inclusion'])),expected)
        R = Integers(27)
        X = PolynomialRing(R,'X').gen()
        data = prepare_source_data(R,12,0,hecke_indices=[2],ideal={'scalar':9},audit=True)
        self.assertEqual(data['source_scope'],'ideal_image')
        self.assertTrue(verify_ordinary_identities(0*X,2,data)['passed'])
        self.assertTrue(verify_divided_identities(X,0*X,2,1,1,data)['passed'])
        # On a source with an order-9 factor, 3*y=0 and y+x in 3*M
        # cannot hold for a generator x of that factor.
        data = prepare_source_data(R,12,0,hecke_indices=[2],ideal={'scalar':3},audit=True)
        if data['coordinates']['surviving_indices']:
            self.assertFalse(verify_divided_identities(X+1,0*X,2,1,1,data)['passed'])

    @unittest.skipUnless(os.environ.get('HECKE_SOURCE_EXECUTABLE'), 'Nim executable not supplied')
    def test_nim_archives_by_independent_monomial_replay(self):
        """Check native archives against independently computed monomial images."""
        exe = os.environ['HECKE_SOURCE_EXECUTABLE']
        with tempfile.TemporaryDirectory(prefix='hecke-source-test-') as directory:
            directory = Path(directory)
            counter = 0
            cases = [(2,1,4,(3,5)),(2,2,8,(3,5)),(3,15,12,(2,7)),(3,3,22,(2,7)),
                     (3,3,88,(2,7)),(5,1,22,(2,19)),(7,1,48,(3,29))]
            ideals = [None,{}, {'scalar':1}, {'scalar':3},
                      {'generators':[[[1,[1,0]],[-1,[0,0]]]]},
                      {'generators':[[[1,[1,0]]],[[1,[0,1]],[-2,[0,0]]]]}]
            for p,m,d,ns in cases:
                R = Integers(p**m)
                ctx = RecursiveContext(R,ns)
                for recursive in (False,True):
                    for ideal in ideals:
                        counter += 1
                        path = directory/f'case_{counter}.npz'
                        args = [exe,'--prime',str(p),'--exponent',str(m),'--degree',str(d),
                                '--hecke',','.join(map(str,ns)),'--compact','--audit',
                                '--replay-maps','--output',str(path)]
                        if not recursive:args.append('--direct')
                        if ideal is not None:
                            spec = directory/'ideal.json'
                            spec.write_text(json.dumps(ideal))
                            args.extend(['--ideal',str(spec)])
                        subprocess.run(args,check=True,stdout=subprocess.DEVNULL)
                        for q in range(1 if p==2 else p-1 if ideal is not None else 2):
                            load = load_source_data if ideal is None else load_ideal_source_data
                            data = load(R,d,q,path)
                            self.assertEqual(data['source_metadata']['construction'],
                                             'recursive' if recursive else 'direct')
                            if ideal is not None:
                                with self.assertRaises(ValueError):
                                    load_source_data(R,d,q,path)
                                fresh = prepare_source_data(R,d,q,hecke_indices=ns,
                                    ideal=ideal,recursive=recursive,context=ctx,audit=True)
                                self.assertEqual(sorted(fresh['coordinates']['surviving_exponents']),
                                                 sorted(data['coordinates']['surviving_exponents']))
                            a = ctx.direct_module(d,0 if p==2 else (-1)**q)
                            am = tuple(p**e for e in a.exponents)
                            with np.load(path,allow_pickle=False) as bundle:
                                rows = bundle[f'q{q}_mixed_to_monomials']
                                lifts = matrix(R,*rows.shape,[int(v) for v in rows.flat])
                            inclusion = lifts*a.reduction
                            B = diagonal_matrix(R,am)
                            self.assertTrue(mixed_matrix_is_zero(
                                diagonal_matrix(R,data['coordinates']['coordinate_moduli'])*inclusion,am))
                            if ideal is None:
                                expected = row_basis(identity_matrix(R,len(am)))
                            else:
                                twisted = [R(n)**(q*ctx.t)*a.actions[n] for n in ns]
                                G = matrix(R,0,len(am))
                                for F in ideal.get('generators',[]):G=G.stack(evaluate_polynomial(F,twisted))
                                expected = row_basis(B.stack(G).stack(R(ideal.get('scalar',0))*identity_matrix(R,len(am))))
                            self.assertEqual(row_basis(B.stack(inclusion)),expected)
                            # Independent image cardinality, not just equality of image spans.
                            coker = chain_ring_coordinates(expected)
                            image_length = sum(a.exponents)-sum(coker['surviving_exponents'])
                            self.assertEqual(sum(data['coordinates']['surviving_exponents']),image_length)
                            for n in ns:
                                T = data['archived_hecke_matrices'][n]['normalized_matrix']
                                self.assertTrue(mixed_matrix_is_zero(T*inclusion-inclusion*a.actions[n],am))


if __name__ == '__main__':
    unittest.main()

"""Run with Sage's Python and PYTHONPATH=python; no archive is required."""
from itertools import product
from sage.all import Integers, PolynomialRing, matrix
from staged_circuit import verify_staged_polynomial


def test_nested_scalar_circuit_against_exhaustive_search():
    """Include solutions missed by canonical division and true failures."""
    R = Integers(9)
    S = PolynomialRing(R, names=('T', 'A', 'D'))
    T, A, D = S.gens()
    for target in (3, 9):
        for t, c in product(range(target), repeat=2):
            expected = any(
                (t - 3*y) % target == 0
                and (y - 3*z) % target == 0
                and (z-c) % target == 0
                for y, z in product(range(target), repeat=2)
            )
            report = verify_staged_polynomial(
                D-c, {'T': matrix(R, 1, 1, [t])},
                {'A': (T, 1), 'D': (A, 1)}, (target,), 3, b=2,
            )
            assert report['passed'] == expected, (target, t, c, report)


def test_mixed_module_terminal_is_inside_the_module():
    """3M kills the order-three coordinate, regardless of ambient modulus."""
    R = Integers(27)
    S = PolynomialRing(R, names=('T', 'A'))
    T, A = S.gens()
    report = verify_staged_polynomial(
        S(1), {'T': matrix(R, 2, 2, [0,0,0,0])},
        {'A': (T, 1)}, (27,3), 3, b=1,
    )
    assert report['passed'] is False


def test_fallback_does_not_fix_canonical_division():
    R = Integers(9)
    S = PolynomialRing(R, names=('T', 'A', 'D'))
    T, A, D = S.gens()
    args = (D-1, {'T': matrix(R,1,1,[0])},
            {'A': (T,1), 'D': (A,1)}, (9,), 3)
    assert verify_staged_polynomial(*args, b=2, howell_fallback=False)['passed'] is None
    report = verify_staged_polynomial(*args, b=2)
    assert report['passed'] and report['verification_route'] == 'simultaneous_howell'


def test_joint_mixed_circuit_against_exhaustive_search():
    R = Integers(9)
    S = PolynomialRing(R, names=('T', 'A', 'D'))
    T, A, D = S.gens()
    action = matrix(R, 2, 2, [3,1,3,0])
    mods = (9,3)
    elements = list(product(range(9), range(3)))
    for c in range(3):
        expected = True
        for x in ((1,0), (0,1)):
            tx = [sum(x[i]*int(action[i,j]) for i in range(2)) for j in range(2)]
            exists = any(
                all((tx[j]-3*y[j]) % mods[j] == 0
                    and (y[j]-3*z[j]) % mods[j] == 0
                    and (z[j]+y[j]-c*x[j]) % 3 == 0
                    for j in range(2))
                for y, z in product(elements, repeat=2)
            )
            expected = expected and exists
        report = verify_staged_polynomial(
            D+A-c, {'T': action}, {'A': (T,1), 'D': (A,1)}, mods, 3,
        )
        assert report['passed'] == expected, (c, report)


if __name__ == '__main__':
    test_nested_scalar_circuit_against_exhaustive_search()
    test_mixed_module_terminal_is_inside_the_module()
    test_fallback_does_not_fix_canonical_division()
    test_joint_mixed_circuit_against_exhaustive_search()
    print('Staged circuit tests passed')

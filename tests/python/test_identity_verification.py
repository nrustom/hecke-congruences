"""Regression tests for staged witnesses; run with Sage's Python."""

import unittest

import numpy as np
from sage.all import ZZ, Integers, PolynomialRing, matrix, zero_matrix

import identity_verification as iv
import p7_mod49 as p7


def scalar_source(p, m, degree, order, operators):
    """Construct the one-coordinate source used to test division relations over a finite chain ring."""
    return {
        "p": ZZ(p), "m": ZZ(m), "q": ZZ(0), "d": ZZ(degree),
        "sign": 1, "period": ZZ(p**(m - 1) * (p - 1)),
        "coefficient_ring": Integers(p**m),
        "coordinates": {"surviving_indices": (0,)},
        "archived_hecke_matrices": {
            ZZ(n): {
                "normalized_matrix": matrix(ZZ, 1, 1, [value]),
                "coordinate_moduli": (ZZ(p**order),),
            }
            for n, value in operators.items()
        },
    }


def term(w3=0, w29=0, j=0, coefficient=1):
    """Encode one sparse polynomial term in the variable order used by the test."""
    return {
        "W3_power": w3, "W29_power": w29,
        "J_power": j, "coefficient": coefficient,
    }


class StagedWitnessTests(unittest.TestCase):
    """Regression checks for common-chain realizations of presented division relations."""
    def test_impossible_terminal_equation_is_rejected_by_public_verifier(self):
        """Check that the public verifier rejects an inconsistent terminal equation."""
        data = scalar_source(3, 2, 2, 2, {2: 0})
        X = PolynomialRing(data["coefficient_ring"], "X").gen()
        result = iv.verify_divided_identities(X + 1, X, 2, 1, 1, data)
        self.assertEqual(result["verification_route"], "howell_staged_witness_fallback")
        # 3*x1=0 forces x1=0 modulo 3, so 1+x1 cannot be in 3M.
        self.assertFalse(result["passed"])

    def test_solvable_witnesses_and_terminal_depth_zero(self):
        """Check solvable division equations, including the full-domain test at terminal depth zero."""
        R = Integers(27)
        X = PolynomialRing(R, "X").gen()
        self.assertTrue(iv._staged_witnesses_exist(
            matrix(R, 1, 1, [3]), X - 1, (27,), 3, 1, 2,
        ))
        self.assertTrue(iv._staged_witnesses_exist(
            zero_matrix(R, 1, 1), X + 1, (27,), 3, 1, 0,
        ))


class SelectorWitnessTests(unittest.TestCase):
    """Regression checks for fixed selector inputs and permitted torsion corrections."""
    def test_fixed_starting_vector_cannot_be_corrected(self):
        """Check that kernel choices cannot change a prescribed initial element."""
        source = p7._Source((1,))
        root = p7._generators(source)
        zero = np.zeros_like(root)
        # The first equation would be 7*x1=1 in Z/7Z.
        self.assertFalse(p7._relation_holds(
            source, root, (zero, zero, root), (2, 1, 1), [term(j=3)],
        ))

    def test_a_previous_divided_witness_can_be_corrected(self):
        """Check that an earlier division output may change by an element of its kernel."""
        source = p7._Source((1, 2))
        root = np.array([[6 * 49, 7]], dtype=np.int64)
        numerator = p7._encode_operator(source, matrix(ZZ, [[1, 0], [1, 7]]))
        zero = np.zeros_like(numerator)
        # In ordinary coordinates, x0=x1=(6,1), x2=(0,1) is a
        # valid chain. The canonical first quotient (0,1) needs correction.
        result = p7._monomial(
            source, root, (zero, zero, numerator), (2, 1, 1), (0, 0, 2),
        )
        np.testing.assert_array_equal(result, [[0, 7]])

    def test_terminal_freedom_uses_the_actual_last_division(self):
        """Check that terminal corrections use only the last division in the ordered monomial."""
        source = p7._Source((2,))
        root = p7._generators(source)
        zero = np.zeros_like(root)
        # For A=0 and F=J+1, 7*x1=0 prevents x1=-1 modulo 7;
        # 49*x1=0 permits x1=-1 and hence a zero terminal value.
        for exponent, expected in ((1, False), (2, True)):
            with self.subTest(exponent=exponent):
                self.assertEqual(p7._relation_holds(
                    source, root, (zero, zero, zero), (2, 1, exponent),
                    [term(j=1), term()],
                ), expected)

    def test_last_w3_division_allows_order_49_torsion(self):
        """Check the order-49 kernel freedom available after a division by 49."""
        source = p7._Source((2,))
        root = p7._generators(source)
        zero = np.zeros_like(root)
        # W29 is applied first and W3 last; the last 49-division can
        # absorb the constant term on Z/49Z.
        self.assertTrue(p7._relation_holds(
            source, root, (zero, zero, zero), (2, 1, 1),
            [term(w3=1, w29=1), term()],
        ))

    def test_stored_graph_polynomial_rejects_impossible_raw_digit(self):
        """Check that the recorded graph polynomial rejects an inadmissible digit."""
        data = scalar_source(7, 3, 40, 2, {3: 1, 29: 2})
        # The default loader must find the relation table at the repo root.
        relations = p7.p7_mod49_relation_polynomials()
        result = p7.verify_p7_mod49_selector_identities(data, relations)
        self.assertFalse(result["passed"])
        branch = next(b for b in result["branches"] if b["centre"] == 1)
        graph = next(r for r in branch["relations"] if r["label"] == "k0_c1_V_graph")
        # V-3 cannot vanish modulo 7 when its raw numerator T29-2 is zero.
        self.assertFalse(graph["passed"])


if __name__ == "__main__":
    unittest.main()

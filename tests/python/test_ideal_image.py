"""Independent enumeration tests: run with sage -python tests/python/test_ideal_image.py."""
from itertools import product
from sage.all import Integers, matrix, diagonal_matrix, zero_matrix
from mixed_endomorphisms import ideal_image, image_submodule


def row_span(B):
    n = int(B.base_ring().characteristic())
    return {tuple(sum(c[i] * int(B[i, j]) for i in range(B.nrows())) % n
                  for j in range(B.ncols()))
            for c in product(range(n), repeat=B.nrows())}


for modulus in (4, 9):
    R = Integers(modulus)
    p = 2 if modulus == 4 else 3
    # Genuine mixed torsion: Z/p + Z/p^2.
    B = diagonal_matrix(R, [p, 0])
    for entries in product(range(modulus), repeat=2):
        G = matrix(R, 1, 2, entries)
        H = image_submodule(B, G)
        span = row_span(B.stack(G))
        for x in product(range(modulus), repeat=2):
            assert (x in H) == (x in span)
        assert H.is_zero() == (span == row_span(B))
        assert H.is_full() == (len(span) == modulus**2)
    T = diagonal_matrix(R, [1, p])
    H = ideal_image(B, [T], p=p, a=1)
    assert (1, p) in H and (0, 1) not in H
    assert ideal_image(B, [], p=p, a=0).is_full()
    assert ideal_image(B, [], p=p, a=2).is_zero()
    bad = matrix(R, [[0, 1], [0, 0]])
    try:
        ideal_image(B, [bad], p=p, a=1)
    except ValueError:
        pass
    else:
        raise AssertionError("invalid descent accepted")
    empty = zero_matrix(R, 0, 0)
    H = ideal_image(empty, [], p=p, a=1)
    assert H.is_full() and H.is_zero() and () in H
print("Ideal-image exhaustive membership, torsion, descent and empty-module tests passed")

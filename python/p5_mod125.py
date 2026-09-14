"""The specified modulo-125 presentations, at working precision 625.

Polynomial aliases and literal products of relations are deliberately distinct:
E_l B E_l is not replaced by E_l B on a torsion source.
"""
import json
import hashlib
from pathlib import Path

from sage.all import GF, ZZ, Integers, PolynomialRing, prod


def load_mod125_parameters(path=None):
    """Read the fifty integer parameter rows, indexed by coefficient degree."""
    if path is None:
        path = Path(__file__).resolve().parents[1]/'p5_mod125_relation_data.json'
    data = json.loads(Path(path).read_text())
    if (data['schema'] != 'hecke.p5-mod125-parameters.v1'
            or data['working_modulus'] != 625
            or data['classification_modulus'] != 125):
        raise ValueError('unexpected modulo-125 parameter file')
    rows = {row['r']: row for row in data['parameters']}
    if len(data['parameters']) != 50 or set(rows) != set(range(0, 100, 2)):
        raise ValueError('expected all fifty even residues modulo 100')
    for row in rows.values():
        lam = row['v0'] % 5
        u0 = ((row['v0']**5-row['v0'])//5) % 5
        if (row['alpha']+row['beta']*lam+row['gamma']*lam**2-2*u0) % 5:
            raise ValueError('A_r(lambda) != 2*u0 modulo 5')
    return rows


def mod125_polynomials(row):
    """Return expanded integer polynomials; lift P only AFTER powering over F5."""
    ring = PolynomialRing(ZZ, 'X')
    X = ring.gen()
    finite_ring = PolynomialRing(GF(5), 'Y')
    Y = finite_ring.gen()
    A = row['alpha']+row['beta']*X+row['gamma']*X**2
    N = (X**5-X)**2-5*A*(X**5-X)
    E = {ell: (1-(X-ell)**4)**5 for ell in range(5)}
    lam = row['v0'] % 5
    u0 = ((row['v0']**5-row['v0'])//5) % 5
    allowed = {lam, (lam+2) % 5, (lam-2) % 5}
    R, P = {}, {}
    for ell in range(5):
        R[ell] = (finite_ring.one() if ell not in allowed else
                  Y+u0**2 if ell == lam else
                  prod(Y-t**2+GF(5)(A(ell))*t for t in range(5)))
        P[ell] = ring([ZZ(c) for c in (R[ell]**4).list()])
    return {'A': A, 'N': N, 'E': E, 'R': R, 'P': P}


def mod125_relation_spec(row, max_howell_dimension=4096):
    """Eight checks: ordinary, V-domain, B-domain, and five source sandwiches."""
    names = ['T2', 'T19', 'V', 'B']
    for ell in range(5):
        names.extend((f'E{ell}', f'J{ell}'))
    ring = PolynomialRing(Integers(625), names=names)
    variables = dict(zip(names, ring.gens()))
    T2, T19, V, B = (variables[name] for name in names[:4])
    polys = mod125_polynomials(row)

    def terms(F):
        """Encode the expanded polynomial with integer coefficient lifts and the prescribed variable order."""
        return [[str(ZZ(c)), [int(e) for e in powers]]
                for powers, c in ring(F).dict().items()]

    relations = [
        {'name': 'ordinary_joint', 'polynomial': terms(
            T2**2-row['h0']-row['h1']*T19-row['h2']*T19**2),
         'terminal_power': 3},
        {'name': 'V_full_domain', 'polynomial': terms(V), 'terminal_power': 0},
        {'name': 'B_full_domain', 'polynomial': terms(B), 'terminal_power': 0},
    ]
    presentations = []
    for ell in range(5):
        E, J = f'E{ell}', f'J{ell}'
        presentations.extend((
            {'variable': E, 'polynomial': terms(polys['E'][ell](V))},
            {'variable': J, 'factors': [E, 'B', E]},
        ))
        relations.append({
            'name': f'selector_{ell}',
            'polynomial': terms(polys['P'][ell](variables[J])),
            'input_presentation': E, 'terminal_power': 1,
        })
    return {
        'schema': 'hecke.relations.v1', 'coefficient_modulus': 625,
        'variables': names, 'hecke_operators': {'T2': 2, 'T19': 19},
        'divisions': [
            {'variable': 'V', 'numerator': terms(T19), 'power': 1},
            {'variable': 'B', 'numerator': terms(polys['N'](V)), 'power': 2},
        ],
        'presentations': presentations, 'relations': relations,
        'witness_semantics': 'independent_monomials',
        'max_howell_dimension': int(max_howell_dimension),
    }


def mod125_possible_signatures(rows):
    """The 22 allowed (a2,a19) pairs per WEIGHT residue, not degree residue."""
    result = {}
    for r, row in rows.items():
        lam = row['v0'] % 5
        values = {row['v0']}
        values.update((lam+offset) % 5+5*j for offset in (-2, 2) for j in range(5))
        pairs = set()
        for t in values:
            rhs = (row['h0']+5*row['h1']*t+25*row['h2']*t**2) % 125
            roots = [a for a in range(125) if (a*a-rhs) % 125 == 0]
            if len(roots) != 2 or any(a % 5 == 0 for a in roots):
                raise ValueError('expected two unit roots for each allowed t')
            pairs.update((a, 5*t) for a in roots)
        if len(pairs) != 22:
            raise ValueError('expected 22 pairs')
        result[(r+2) % 100] = pairs
    return result


def load_mod125_strong_representatives(directory):
    """Bind saved representatives to sealed weight/orbit/place records.

    This audits the saved scan; it does not recompute eigenforms or replay
    number-field reductions. Those remain the strong-signature producer's
    mathematical inputs, independently of the source-relation verification.
    """
    directory = Path(directory)
    summary = json.loads((directory/'summary.json').read_text())
    if (summary['schema'] != 'hecke.strong-signature-summary.v1'
            or summary['prime'] != 5 or summary['exponent'] != 3
            or summary['hecke_indices'] != [2, 19]):
        raise ValueError('expected the modulo-125 T2,T19 scan')
    loaded, signatures = {}, []
    for item in summary['rational_signatures']:
        weight = item['weight']
        filename = f'weight_{weight}.json'
        if item['weight_file'] != filename or item['weight_residue'] != weight % 100:
            raise ValueError('invalid strong representative binding')
        if weight not in loaded:
            data = json.loads((directory/filename).read_text())
            payload = {key: value for key, value in data.items() if key != 'payload_sha1'}
            digest = hashlib.sha1(json.dumps(payload, ensure_ascii=False,
                                            separators=(',', ':')).encode()).hexdigest()
            if digest.upper() != data['payload_sha1'].upper():
                raise ValueError(f'payload seal mismatch: {filename}')
            if (data['weight'] != weight or data['prime'] != 5
                    or data['exponent'] != 3 or data['hecke_indices'] != [2, 19]
                    or data['level'] != 1 or not data['cuspidal']
                    or not data['finite_weight_complete']):
                raise ValueError(f'inconsistent strong weight record: {filename}')
            loaded[weight] = data
        orbits = [orbit for orbit in loaded[weight]['orbits'] if orbit['orbit'] == item['orbit']]
        if len(orbits) != 1:
            raise ValueError('missing/duplicate strong orbit')
        packets = [packet for packet in orbits[0]['local_packets'] if packet['place'] == item['place']]
        if len(packets) != 1:
            raise ValueError('missing/duplicate local place')
        packet = packets[0]
        pair = tuple(map(int, item['eigenvalue_residues']))
        if (tuple(map(int, packet['rational_signature'])) != pair
                or len(pair) != 2 or any(a < 0 or a >= 125 for a in pair)
                or packet['krw_ideal_exponent'] != 2*packet['ramification_index']+1
                or not packet.get('krw_reduction_replayed', False)):
            raise ValueError('strong signature disagrees with the local record')
        signatures.append((weight, *pair))
    return signatures

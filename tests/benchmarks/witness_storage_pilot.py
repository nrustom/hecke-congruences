"""Bounded storage experiment, not a production or all-weight certificate.

Compile the same shared-chain presentation as Nim; export only noncanonical
division choices. A separate replay reconstructs every ordinary output and
checks every equation. Simultaneous solving is restricted to small systems.
Run with Sage and PYTHONPATH=python. Existing source archives are read-only.
"""
import argparse
import gzip
import hashlib
import json
import math
import time
from pathlib import Path

import numpy as np
from sage.all import GF, matrix
from p7_mod49 import p7_mod49_nim_relation_spec
from p5_mod125 import load_mod125_parameters, mod125_relation_spec
from functools import lru_cache

ROOT = Path(__file__).resolve().parents[2]


def digest(value):
    """Return the SHA-256 identifier of the canonically serialized input record."""
    return hashlib.sha256(json.dumps(value, sort_keys=True,
        separators=(',', ':')).encode()).hexdigest()


@lru_cache(None)
def case_spec(p,m,d,q):
    """Return the fixed polynomial presentation for the selected benchmark case."""
    if p==7:
        return p7_mod49_nim_relation_spec(d,q,m)
    if p==5 and m==4:
        return mod125_relation_spec(load_mod125_parameters()[(d+50*q)%100])
    raise ValueError('pilot supports p7 modulo 49/343 and p5 modulo 625')


@lru_cache(None)
def dependencies_available(p,m,d,q):
    """Match the notebook's missing-low-orientation whole-source fallback.

    This is an availability check, NOT verification of the lower relations.
    The p5 archive below degree 750 contains only the plus source.
    """
    a,b=p**m*(p-1),p**(m-1)*(p+1)
    if d<b:
        return not (p==5 and q%2)
    return (dependencies_available(p,m,d-b,(q+1)%(p-1)) and
            (d<a or dependencies_available(p,m,d-a,q)))


def compile_circuit(spec, relation):
    """Expand the presentation into its intermediate linear equations for this storage benchmark."""
    names = spec['variables']
    definitions = {n: {'ordinary': int(v)} for n, v in spec['hecke_operators'].items()}
    for item in spec.get('divisions', []):
        definitions[item['variable']] = dict(power=item['power'], polynomial=item['numerator'])
    for item in spec.get('presentations', []):
        definitions[item['variable']] = dict(item, power=0)
    steps, cache = [], {}

    def polynomial(terms, initial):
        """Expand monomials in the prescribed order and collect their intermediate outputs."""
        collected = {}
        for coefficient, powers in terms:
            node = initial
            for name, power in reversed(list(zip(names, powers))):
                for _ in range(power):
                    node = apply(name, node)
            collected[node] = (collected.get(node, 0) + int(coefficient)) % spec['coefficient_modulus']
        return [(node, c) for node, c in collected.items() if c]

    def apply(name, initial):
        """Append one ordinary or division application, reusing common intermediate outputs."""
        if (name, initial) in cache:
            return cache[name, initial]
        definition = definitions[name]
        if 'factors' in definition:
            node = initial
            for factor in reversed(definition['factors']):
                node = apply(factor, node)
        else:
            if 'ordinary' in definition:
                step = dict(operator=definition['ordinary'], input=initial)
            else:
                step = dict(power=definition['power'], terms=polynomial(definition['polynomial'], initial))
            steps.append(step)
            node = len(steps)
        cache[name, initial] = node
        return node

    initial = apply(relation['input_presentation'], 0) if 'input_presentation' in relation else 0
    steps.append(dict(power=relation['terminal_power'],
                      terms=polynomial(relation['polynomial'], initial)))
    return steps


def solve_modular(A, B, p, modulus):
    """Solve A*X=B using minimum-valuation pivots over Z/p^m; no saturation.

    Column permutations track unknowns; row operations also act on B.
    Each pivot divides the remaining block, so choosing free variables zero
    and back-substituting gives a solution whenever one exists.
    """
    original_A, original_B = A.copy(), B.copy()
    A, B = A.copy() % modulus, B.copy() % modulus
    rows, cols = A.shape
    permutation = np.arange(cols)
    valuations = np.full(modulus, 100, dtype=np.int64)
    for x in range(1, modulus):
        value, v = x, 0
        while value % p == 0:
            value //= p
            v += 1
        valuations[x] = v
    rank = 0
    for k in range(min(rows, cols)):
        block = valuations[A[k:, k:]]
        position = int(block.argmin())
        if block.flat[position] == 100:
            break
        i, j = np.unravel_index(position, block.shape)
        i, j = int(i)+k, int(j)+k
        A[[k, i]], B[[k, i]] = A[[i, k]], B[[i, k]]
        A[:, [k, j]] = A[:, [j, k]]
        permutation[[k, j]] = permutation[[j, k]]
        pivot = p**int(valuations[A[k, k]])
        unit_inverse = pow(int(A[k, k])//pivot, -1, modulus)
        A[k] = A[k]*unit_inverse % modulus
        B[k] = B[k]*unit_inverse % modulus
        if np.any(B[k] % pivot):
            return None
        factors = A[k+1:, k]//pivot
        A[k+1:, k:] = (A[k+1:, k:] - factors[:, None]*A[k, k:]) % modulus
        B[k+1:] = (B[k+1:] - factors[:, None]*B[k]) % modulus
        rank += 1
    if np.any(B[rank:]):
        return None
    X = np.zeros((cols, B.shape[1]), dtype=np.int64)
    for k in reversed(range(rank)):
        rhs = (B[k] - A[k, k+1:] @ X[k+1:]) % modulus
        if np.any(rhs % A[k, k]):
            return None
        X[k] = rhs//A[k, k]
    result = np.zeros_like(X)
    result[permutation] = X
    assert not np.any((original_A @ result - original_B) % modulus)
    return result


def simultaneous(steps, inputs, actions, mods, p, modulus, limit):
    """Solve the common-chain linear system for the prescribed inputs within the size limit.

    Return the intermediate choices and status; the caller replays the equations.
    """
    n = len(mods)
    nodes = [i for i, s in enumerate(steps, 1) if 'operator' not in s]
    size = len(nodes)*n
    if size > limit:
        return None, 'resource_limit'
    positions = {node: i for i, node in enumerate(nodes)}
    system = np.zeros((size, size), dtype=np.int64)
    rhs = np.zeros((len(inputs), size), dtype=np.int64)
    Id = np.eye(n, dtype=np.int64)
    for col, node in enumerate(nodes):
        step = steps[node-1]
        sl = slice(col*n, (col+1)*n)
        system[sl, sl] = p**step['power']*Id
        for current, coefficient in step['terms']:
            action = Id
            while current and 'operator' in steps[current-1]:
                previous = steps[current-1]
                action = actions[previous['operator']] @ action % modulus
                current = previous['input']
            if current:
                row = positions[current]
                system[row*n:(row+1)*n, sl] -= coefficient*action
            else:
                rhs[:, sl] += coefficient*(inputs @ action % modulus)
    scale = modulus//np.tile(mods, len(nodes))
    solution = solve_modular((system.T % modulus)*scale[:, None] % modulus,
                            (rhs.T % modulus)*scale[:, None] % modulus, p, modulus)
    if solution is None:
        return None, 'no_shared_solution'
    return {node: solution[col*n:(col+1)*n].T % mods
            for col, node in enumerate(nodes)}, 'simultaneous'


def replay(steps, inputs, actions, mods, p, choices=None, solved=None):
    """Without solved, use only recorded corrections; check each equation.

    Keys are (node, input row, target coordinate). Terminal rho is reconstructed
    canonically and is never stored. Ordinary outputs are never stored.
    """
    values = [inputs % mods]
    uses=[0]*(len(steps)+1)
    for step in steps:
        for source in ([step['input']] if 'operator' in step else [node for node,c in step['terms']]):
            uses[source]+=1
    exported, used = [], set()
    choices = {} if choices is None else choices
    by_node={}
    for (node,i,j),c in choices.items():
        if node<1 or node>=len(steps) or i<0 or i>=len(inputs) or j<0 or j>=len(mods):
            raise ValueError('correction index outside the circuit')
        by_node.setdefault(node,[]).append((i,j,c))
    raw_vector_bytes, choice_slots = 0, 0
    for node, step in enumerate(steps, 1):
        if 'operator' in step:
            value = values[step['input']] @ actions[step['operator']] % mods
        else:
            rhs = np.zeros_like(inputs)
            for source, coefficient in step['terms']:
                rhs = (rhs + coefficient*values[source]) % mods
            divisor = p**step['power']
            kernel = np.minimum(divisor, mods)
            if np.any(rhs % kernel):
                return None
            canonical = rhs//divisor
            value = canonical.copy()
            if step['power'] and node != len(steps):
                stride = mods//kernel
                if solved is not None:
                    correction = (solved[node] - canonical) % mods
                    assert not np.any(correction % stride)
                    correction //= stride
                else:
                    correction = np.zeros_like(inputs)
                    for i,j,c in by_node.get(node,()):
                        correction[i,j]=c
                        used.add((node,i,j))
                if np.any(correction < 0) or np.any(correction >= kernel):
                    raise ValueError('correction outside its kernel coordinate')
                value = (canonical + stride*correction) % mods
                exported.extend([node, int(i), int(j), int(correction[i,j])]
                                for i,j in zip(*np.nonzero(correction)))
                raw_vector_bytes += inputs.size*(1 if max(mods, default=1)<256 else 2)
                choice_slots += inputs.size
            if np.any((divisor*value - rhs) % mods):
                raise ValueError('division equation failed')
        values.append(value)
        for source in ([step['input']] if 'operator' in step else [node for node,c in step['terms']]):
            uses[source]-=1
            if uses[source]==0:
                values[source]=None
    if set(choices) != used:
        raise ValueError('unconsumed corrections')
    return dict(corrections=exported, raw_vector_bytes=raw_vector_bytes,
                choice_slots=choice_slots)


def source_case(m, d, q, p=7):
    """Load the signed source and oriented Hecke operators for one benchmark case."""
    if p==7:
        folder = 'G_mod49' if m==2 else 'Q_selectors_mod343'
        directory=ROOT/'source_data/p7_mod49_transfer_maps'/folder
    else:
        directory=ROOT/'source_data/p5_mod625_recursive'
    path=directory/f'degree_{d}.npz'
    with np.load(path, allow_pickle=False) as z:
        key = f'q{q%2}'
        mods = p**z[key+'_order_exponents'].astype(np.int64)
        n = len(mods)
        actions = {ell: z[key+f'_T{ell}'].astype(np.int64)*pow(ell,q*p**(m-1),p**m) % mods
                   for ell in ((3,29) if p==7 else (2,19))}
        selected = []
        if z[key+'_recursive'][0] and dependencies_available(p,m,d,q):
            inherited = np.concatenate([z[key+'_transfer_a'], z[key+'_transfer_b']], axis=0)
            complement = z[key+'_complement_images'].astype(np.int64)
            # Choose rows completing the inherited image over F7, as in Nim.
            joined = np.concatenate([inherited,complement],axis=0)
            pivots = matrix(GF(p),joined.shape[0],n,joined.reshape(-1).tolist()).transpose().pivots()
            selected = [int(i)-len(inherited) for i in pivots if i>=len(inherited)]
            inputs = complement[selected].reshape(len(selected),n)
        else:
            inputs = np.eye(n,dtype=np.int64)
    return path, mods, actions, inputs, selected


def input_scope(p,m,d,q):
    """Return the whole-source or selected-input mode recorded by this benchmark."""
    if d<p**(m-1)*(p+1):return 'whole_source'
    return 'recursive_supplement' if dependencies_available(p,m,d,q) else 'whole_source_fallback'


def prescribed_inputs(spec, relation, inputs, actions, mods):
    """Construct the specified initial rows, retaining the ordinary input selector when present."""
    if 'input_polynomial' not in relation:
        return inputs.copy()
    result = np.zeros_like(inputs)
    for coefficient, powers in relation['input_polynomial']:
        value = inputs.copy()
        for name, e in reversed(list(zip(spec['variables'], powers))):
            if e and name not in spec['hecke_operators']:
                raise ValueError('nonordinary prescribed input')
            for _ in range(e):
                value = value @ actions[spec['hecke_operators'][name]] % mods
        result = (result + int(coefficient)*value) % mods
    return result


def replay_packet(filename):
    """Reload only source data and the packet; never invoke the witness solver."""
    packet = json.loads(gzip.decompress(Path(filename).read_bytes()))
    if packet['schema'] != 'hecke.compact-witness-pilot.v1':
        raise ValueError('unexpected witness schema')
    m,d,q = (packet[k] for k in ('exponent','degree','orientation'))
    p=packet['prime']
    spec = case_spec(p,m,d,q)
    path, mods, actions, inputs, selected = source_case(m,d,q,p)
    assert packet['shared_chains'] is True
    assert packet['source_path']==str(path.relative_to(ROOT))
    assert packet['source_sha256']==hashlib.sha256(path.read_bytes()).hexdigest()
    assert packet['specification_sha256']==digest(spec)
    assert packet['supplementary_indices']==selected
    definitions = {r['name']:r for r in spec['relations']}
    seen = set()
    for record in packet['relations']:
        name=record['name']
        assert name not in seen
        seen.add(name)
        relation=definitions[name]
        steps=compile_circuit(spec,relation)
        assert record['circuit_sha256']==digest(steps)
        corrections={tuple(item[:3]):item[3] for item in record['corrections']}
        assert len(corrections)==len(record['corrections'])
        initial=prescribed_inputs(spec,relation,inputs,actions,mods)
        if replay(steps,initial,actions,mods,p,choices=corrections) is None:
            raise ValueError('recorded choices fail a division or terminal equation')
    if packet.get('complete',False):
        assert seen==set(definitions)
    return dict(degree=d,orientation=q,exponent=m,relations=len(seen),
                complete=seen==set(definitions), inputs=len(inputs),
                input_scope=input_scope(p,m,d,q),
                all_weight_propagation_proved=False)


def run_case(m, d, q, output, limit, p=7):
    """Measure construction, storage and replay of the recorded elements for one fixed case."""
    started = time.monotonic()
    spec = case_spec(p,m,d,q)
    path, mods, actions, inputs, selected = source_case(m,d,q,p)
    packet = dict(schema='hecke.compact-witness-pilot.v1', prime=p, exponent=m,
        degree=d, orientation=q, source_path=str(path.relative_to(ROOT)),
        source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        specification_sha256=digest(spec), shared_chains=True,
        input_scope=input_scope(p,m,d,q),
        supplementary_indices=selected, relations=[])
    stats = dict(degree=d,orientation=q,exponent=m,rank=len(mods),inputs=len(inputs),
                 greedy=0,solved=0,unresolved=[],raw_vector_bytes=0,choice_slots=0,
                 nonzero_corrections=0,replay_seconds=0)
    for relation in spec['relations']:
        # Prescribed input polynomials in p7 use ordinary variables only.
        initial = prescribed_inputs(spec,relation,inputs,actions,mods)
        steps = compile_circuit(spec,relation)
        witness = replay(steps,initial,actions,mods,p)
        if witness is None:
            solved, route = simultaneous(steps,initial,actions,mods,p,p**m,limit)
            if solved is None:
                stats['unresolved'].append([relation['name'],route])
                continue
            witness = replay(steps,initial,actions,mods,p,solved=solved)
            assert witness is not None
            stats['solved'] += 1
        else:
            stats['greedy'] += 1
        corrections = {tuple(item[:3]): item[3] for item in witness['corrections']}
        before = time.monotonic()
        checked = replay(steps,initial,actions,mods,p,choices=corrections)
        assert checked is not None and checked['corrections']==witness['corrections']
        stats['replay_seconds'] += time.monotonic()-before
        packet['relations'].append(dict(name=relation['name'],circuit_sha256=digest(steps),
                                       corrections=witness['corrections']))
        for key in ('raw_vector_bytes','choice_slots'):
            stats[key] += witness[key]
        stats['nonzero_corrections'] += len(corrections)
    packet['complete']=not stats['unresolved']
    encoded=gzip.compress(json.dumps(packet,separators=(',',':')).encode(),mtime=0)
    output.mkdir(parents=True,exist_ok=True)
    target=output/f'm{m}_degree_{d}_q{q}.json.gz'
    target.write_bytes(encoded)
    # Read-back check: an archive must preserve every bound and correction.
    assert json.loads(gzip.decompress(target.read_bytes()))==packet
    stats.update(archive_bytes=len(encoded),elapsed_seconds=time.monotonic()-started,
                 complete=not stats['unresolved'])
    print(json.dumps(stats),flush=True)
    return stats


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--cases',help='comma separated m:degree:q')
    parser.add_argument('--prime',type=int,choices=(5,7),default=7)
    parser.add_argument('--replay',type=Path,nargs='+',help='replay saved pilot packets, with no solver')
    parser.add_argument('--max-solver-dimension',type=int,default=1100)
    parser.add_argument('--output',type=Path,default=ROOT/'verification_data/mod49_pilot')
    args=parser.parse_args()
    if args.replay:
        for filename in args.replay:
            started=time.monotonic()
            print(dict(replay_packet(filename),seconds=time.monotonic()-started),flush=True)
        raise SystemExit(0)
    if not args.cases:
        parser.error('supply --cases or --replay')
    results=[run_case(*map(int,case.split(':')),args.output,args.max_solver_dimension,args.prime)
             for case in args.cases.split(',')]
    summary=args.output/'summary.json'
    previous=json.loads(summary.read_text()) if summary.exists() else []
    combined={(r['exponent'],r['degree'],r['orientation']):r for r in previous+results}
    summary.write_text(json.dumps(list(combined.values()),indent=2)+'\n')

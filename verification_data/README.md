# Auxiliary elements for equation replay

`mod125/` contains the production packets for the eight modulo-125 source
checks at working modulus 625. The existing Manin source archives are not
duplicated or modified. `mod125_pilot/` and `mod49_pilot/` are earlier bounded
format experiments, not inputs to the production replayer.

The production supervisor, its four workers, archive loading, solution
extraction and equation replay are compiled Nim. It does not launch Python,
Sage, Singular or a notebook. FLINT, GMP, zlib and OpenSSL are native library
dependencies. The existing FLINT library directory may happen to reside in
the Sage/Conda installation; no Sage code is executed.

`relations/p5_mod125_native.json` freezes the exact fifty polynomial
specifications already exported by the notebook front end. This is data, not
a new derivation of the identities. The source archives are read directly as
unsigned C-order NPZ arrays, with CRC, SHA-256, metadata and shape checks.
The same native recursive transfer/spanning checks still apply.

Each compressed packet stores only the nonzero choices added to canonical
outputs of division equations in the cyclic source module. Ordinary steps,
polynomial aliases and the terminal auxiliary element are reconstructed.
The oriented actions, cyclic orders, tested input rows, and literal relation
specification determine the packet binding. No division in a torsion module
is justified by cancellation, and no global divided endomorphism is assumed.

Production first tries canonical choices, then reusable divided endomorphisms
with a bounded search through diagonal torsion-kernel corrections. These are
sufficient choices, not an assumption that division is unique. Every nested
numerator is reconstructed after a choice changes, and the literal polynomial
and composition equations are replayed. This path is reported as
`structured_witness_replay`. Unsuccessful structured choices are inconclusive;
the common-chain simultaneous solve and, where permitted, independent
monomial chains remain the fallback. Each accepted solution undergoes one
complete equation replay, which also encodes its compact kernel corrections.
Production does not repeat that replay or immediately decompress the newly
written packet. Gzip write/close errors are checked and publication is atomic;
every later load still checks the binding and replays all equations.
Source validation is performed once per uncached source verification, and
successful lower-degree results are reused only with matching specification,
orientation and archive-dependency fingerprints. The required transfer and
spanning checks are unchanged. Resource-limit outcomes are not counterexamples and
are not recorded as passed. Per-relation successes survive an interrupted or
inconclusive degree.

## Running and monitoring

From the repository root:

```bash
bash run_mod125_witnesses.sh start 4
bash run_mod125_witnesses.sh status
bash run_mod125_witnesses.sh stop
bash run_mod125_witnesses.sh resume 4
```

Four persistent native sessions own ascending degree chains modulo 250, so
both Dickson degree shifts preserve worker ownership. Low degrees are
processed first. A failed/inconclusive case stops new scheduling; other
active cases may finish. The systemd service owns all descendant processes.
Production stops if less than 10 GiB of disk space remains. Existing packets
are replayed on resume; saved reports alone are never accepted as proofs.
Consequently `completed_count` counts cases checked in the current launch,
whereas `packet_count` includes previously saved packets and lower recursive
dependencies. Heartbeats show liveness, not completion of a mathematical step.

The production extraction cap is 8,192 simultaneous coordinates. This is a
resource setting, not an identity coefficient or certificate hypothesis;
the polynomial specification retains its original 4,096 verifier default.
Changing the extraction cap does not invalidate already produced packets.
The structured fast path does not increase this cap. Regression tests at
degrees 26, 130, 250 and 270 pass all eight checks even with the simultaneous
solver capped at one coordinate, and separately replay their saved choices.

## Later notebook replay

The existing `verify_hecke_relations_nim` call accepts two optional keywords:

```python
report = verify_hecke_relations_nim(
    native_relations[relation_residue],
    compute=compute,
    session=session,
    witness_directory="verification_data/mod125/packets",
    witness_mode="replay",
)
```

Use the same source data and relation specifications (including the solver
limit recorded in the manifest). Replay mode never invokes witness discovery:
missing or invalid packets raise errors. The recursive transfer, spanning
and lower-degree checks are still performed. An empty supplementary source
check does not by itself prove the whole-source assertion. Sources remain
trusted archived Hecke actions, as in the original notebook.

The notebooks have not been switched to these packets automatically. Until
the run has complete coverage, full replay can encounter missing packets.
Neither packet production nor a bounded source verification alone asserts
an all-weight classification theorem.

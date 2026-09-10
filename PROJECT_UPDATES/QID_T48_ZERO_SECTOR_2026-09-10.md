# QI-D T48 zero-sector boundary Lean certificate — 2026-09-10

## Source authority

Current QIprojects head at final promotion audit:

`6080f36ddd7a3c85015416b793e0562caf685e5a`

Canonical source:

`QI-D/code/certify_E6_F4_endpoint_locus_reduction.py`

Current source blob:

`d99c94652fb29a51eb919a0cc746021a2fa4e20a`

The T48 endpoint-locus verifier is unchanged across the QIprojects drift that occurred during Lean validation. It certifies, for each of four central-D4 E6 facets, `Tr(F_aa)=1/3`, `support_W(D4)(F_tt)=2/3`, active counts `24,20,16,14`, and therefore the sharp zero-sector boundary value `1`.

## Lean implementation

Module:

`FormalResearch/QID/E6F4ZeroSectorBoundary.lean`

The module reuses the existing exact 192-element even signed-permutation model `allD4` from `D4DoublyStochasticCertificate` and checks an explicit source-to-standard basis change. It proves/checks:

- the displayed basis change determinant, inverse, and pullback Gram identity;
- conjugacy of the four source zero-root D4 simple reflections to the standard D4 signed-permutation generators;
- exact transformation of all four source `F_tt` blocks to the standard-coordinate normals used for finite enumeration;
- `Tr(F_aa)=1/3` for all four facets;
- zero support violations above `2/3` over all 192 D4 elements;
- exact active counts `24,20,16,14`;
- attainment of `2/3` for every facet;
- the pointwise finite zero-sector bound `1/3+2/3<=1` and its attainment.

## Verification

An initial implementation run failed only because `native_decide` was invoked on goals with a free `k : Fin 4`. No source value or certificate identity failed. The proofs were repaired by making the four finite cases explicit with `fin_cases k`.

Module-green repaired run:

`34441664322`

Exact promoted Lean-content head after importing the module into `FormalResearch.lean`:

`46aa00dbb7b76c74a4204eb1d6f35d7a79aef0e1`

Aggregate validation run:

`34441876733`

That run passed:

1. placeholder rejection;
2. `lake build FormalResearch.QID.E6F4ZeroSectorBoundary`;
3. full `lake build FormalResearch`.

The temporary validation workflow was removed after this successful run. No theorem/module bytes changed after the exact promoted content head above.

## Scope boundary

This is the exact finite T48 **zero-sector boundary certificate** only. It does not formalize the full E6 restricted-root enumeration, the identification of the three multiplicity-eight triality modules, the PSD/rank outer endpoint locus, or the missing common-F4/triality compatibility for interior endpoints.

In particular it does **not** prove compact-E6 simultaneous Weyl convexity. The unresolved interior problem remains source-side T49 (or its current successor after any later source-side task reorganization).

## Concurrent source drift note

During this validation QIprojects also strengthened `QI-D/code/certify_E6_A2_phase_envelope.py` beyond the source version used for reasoner PR #18 by adding explicit regressions showing that the linear guard `d>=|a|` is not redundant. This does not invalidate the T48 module above, whose source blob is unchanged, but the E6 quartic Lean status should be reconciled separately before claiming full source-current coverage of that reduction.

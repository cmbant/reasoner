# QI-D E6/F4 A2 linear-guard reconciliation — 2026-09-10

## Why this follow-up exists

Reasoner PR #18 formalized the exact tangent-half-angle / quartic algebra from the then-current T33 source. QIprojects later strengthened `QI-D/code/certify_E6_A2_phase_envelope.py` by adding exact regressions showing that the linear/sign condition `d >= |a|` is load-bearing: quartic nonnegativity alone is not equivalent to the original phase-envelope bound.

This follow-up makes the Lean certificate source-current without changing the earlier theorem boundary.

## Source authority

QIprojects audit pin:

`6080f36ddd7a3c85015416b793e0562caf685e5a`

Canonical verifier:

`QI-D/code/certify_E6_A2_phase_envelope.py`

Source blob:

`fad4403997347c90b8301cdf691d140253dd2935`

The current exact criterion keeps two separate pieces:

1. `d >= |a|`;
2. nonnegativity of the circle defect / cleared quartic, including the `t=infinity` point.

The source includes both a degenerate and a nondegenerate exact regression where the quartic branch accepts but `d >= |a|` fails and the original bound is false.

## Lean update

Updated module:

`FormalResearch/QID/E6A2PhaseEnvelopeQuartic.lean`

Exact Lean-content commit:

`0468a2ee1ee8402b52935d32ec599ce4ffd3a894`

The module now defines the rational source guard

`e6A2LinearGuard ar ai d := 0 <= d ∧ ar^2 + ai^2 <= d^2`

and checks its equivalence to the source verifier's boolean arithmetic. It also formalizes the two new source regressions:

- degenerate `a=b=c=0`, `d=-1`: quartic `(1+t^2)^2 >= 0`, nonnegative infinity defect, but guard false;
- nondegenerate `a=b=c=1/100`, `d=-1/2`: quartic `(2401 t^4 + 4994 t^2 + 2597)/10000 > 0`, infinity defect `2401/10000`, but guard false.

Thus Lean now proves explicitly that quartic/infinity nonnegativity cannot replace the linear guard.

## Verification

GitHub Actions run:

`34444000316`

The run passed:

1. placeholder rejection;
2. `lake build FormalResearch.QID.E6A2PhaseEnvelopeQuartic`;
3. full `lake build FormalResearch`.

The temporary validation workflow was removed after the run. No theorem/module bytes changed after exact content commit `0468a2ee...`.

## Scope boundary

Lean still does **not** prove the analytic maximization `max_v Re(z v)=|z|` or derive the complete phase-envelope iff statement from it. It also does not identify every genuine compact-F4 endpoint coefficient tuple or prove uniform quartic positivity on that locus.

Therefore this remains an exact algebraic certificate/reconciliation only, not a proof of compact-E6 simultaneous Weyl convexity.

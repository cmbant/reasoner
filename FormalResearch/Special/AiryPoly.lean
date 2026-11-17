module

public import FormalResearch.Special.AiryPolyAlg
public import FormalResearch.Special.AiryPolyAsym
public import FormalResearch.Special.AiryPolySector
public import FormalResearch.Special.AiryPolyCircle
public import FormalResearch.Special.AiryPolyHB
public import FormalResearch.Special.AiryPolyZeros
public import FormalResearch.Special.AiryPolyQuad
public import FormalResearch.Special.AiryPolyWeights
public import FormalResearch.Special.AiryPolySample
public import FormalResearch.Special.AiryPolyApplications

/-!
# The Airy quadrature for `N = P·Ai + Q·Ai'` with real polynomial `P`, `Q` (Hermite-Biehler extensions): umbrella

Survey row T4 of the Airy/soft-edge programme: `general_theorems.tex` Lemma 1.0′ (E2$_N$) and `SOFT_EDGE_THEOREMS.md` Lemmas 4.4, 4.6
(Blaschke-extension Airy summation), the input (HB) of `SE5_FIVE_LEVEL_AIRY.md` and Theorem 4.7.  It extends the constant-coefficient chain
`AiryCft2Combo*`, `AiryCftQNC*` to polynomial `P`, `Q`.  Notation: `N = P Ai + Q Ai'`, `M = P Bi + Q Bi'`, `D = P (P+Q') - Q (P'+zQ)`,
`N M' - N' M = D/π`; *Hermite-Biehler* (`AiryPQHB`): all roots of `Q + iP` in the open lower half plane.

* `AiryPolyAlg`: complex evaluation of real polynomials, `N, M, N', M', D`, Wronskian, numerator bound `‖M - iN‖² e ≤ 4(3‖a‖(1+r)^{-1/4} + 5‖b‖(1+r)^{1/4})²`;
* `AiryPolyAsym`: leading-term bounds on `‖u‖ ≥ T`; the **dominance dichotomy** `16‖Q(u)‖√‖u‖ ≤ ‖P(u)‖` or `16‖P(u)‖ ≤ ‖Q(u)‖√‖u‖`;
* `AiryPolySector`, `AiryPolyCircle`: **(i) good circles** for every pair `(P, Q) ≠ 0` (`airyPQ_good_circle`, `airyPQ_good_circle_kappa`): `N ≠ 0` and
  `|N|² ≥ c r^{2κ} e`, `|M/N ∓ i| e ≤ 168√π` on circles `|u| = r ∈ [k, k+1]`;
* `AiryPolyHB`, `AiryPolyZeros`: **(ii) Hermite-Biehler step**: Herglotz inequality, positive Wronskian, zeros of `N` real, simple, `D > 0`
  (`airyPQ_zero_im`, `airyPQ_zero_weight_pos`), finitely many in discs, at most one zero per gap of `Ai` beyond the real roots of `Q` (`airyPQ_injOn_far`; existence of a zero in each gap is not formalised);
* `AiryPolyQuad`, `AiryPolyWeights`, `AiryPolySample`: **(iii) quadrature**: limit form for every `(P, Q)` with simple zeros
  (`airyPQ_tendsto_of_simple`), weights `D/N'² ≍ |t|^{-1/2}`, sampling bound, and the unconditional `∫ f = Σ f D/N'²` (`airyPQ_hasSum_unc`);
* `AiryPolyApplications`: constant pairs, Lemma 4.4 (`airyPQ_lemma44_hasSum`), and the positivity step of Theorems 4.5/4.7
  (`airyPQ_nonneg_zeros_vanish`).

Not formalised: `Q = 0` (that is `Ai` itself, the existing `airyQ_*`), the Prüfer-angle monotonicity `Λ' = D/(P²+Q²)`, the converse of
Theorem 4.7 (the extremal assembly, forward direction, is in `AiryThm47`), explicit `k₀`.
-/

module

public import FormalResearch.SignUncertainty.BinetVertical
public import FormalResearch.SignUncertainty.BinetSmall

/-!
# `ct:dual-id` (1): Binet decay along vertical lines, extension and small-`τ` expansion

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:dual-id`, part (1).

**Scope.**  For `c ≥ 2`, with `B_c(ζ) = B_Bin(c(1-ζ)) - B_Bin(c)` (`binetDiff`):
* `(ct:binet-decay)`: `|∂_τ^r B_c(iτ)| ≤ C_r / (c (1+|τ|)^{r+1})` for every integer `r ≥ 1`, `C_r` independent of `c`
  (here `C_r = r! 4^r`, valid for every `c > 0`);
* `τ ↦ B_c(iτ)` extends holomorphically to `{Im τ > -1}`;
* `(ct:binet-small)`: `B_c(iτ) = iτ/(12 c (1-iτ)) + O(c^{-3}|τ|)` on `|τ| ≤ 1/2` (here with the explicit
  constant `8`, valid for every `c > 0` and every real `τ`).

**Proved** (new route: `B_Bin^{(r)}(w) = (-1)^r (r+1)! ∫₀^∞ P₂(s)(s+w)^{-(r+2)} ds` with the periodic
`P₂(s) = {s}(1-{s})/2`, instead of the integrations by parts of the paper; the remainder `B_Bin(w) - 1/(12w)`
needs two more periodic antiderivatives `P₃, P₄`).  See `BinetP2`, `BinetFubini`, `BinetDecay`,
`BinetVertical`, `BinetSmall`.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

open FormalResearch.Asymptotics FormalResearch.SignUncertainty.BinetDecay

/-- **`ct:dual-id` (1)** of `constant_terms_lower.tex` (Binet decay on vertical lines, holomorphic extension
to `Im τ > -1`, small-`τ` expansion), for every `c ≥ 2`. -/
theorem ct_dual_id_part1 :
    (∀ r : ℕ, 1 ≤ r → ∃ C : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ τ : ℝ,
      ‖iteratedDeriv r (fun τ : ℝ => binetDiff c (Complex.I * (τ : ℂ))) τ‖ ≤
        C / (c * (1 + |τ|) ^ (r + 1))) ∧
    (∀ c : ℝ, 2 ≤ c →
      DifferentiableOn ℂ (fun τ : ℂ => binetDiff c (Complex.I * τ)) {τ : ℂ | -1 < τ.im}) ∧
    (∃ C : ℝ, ∀ c : ℝ, 2 ≤ c → ∀ τ : ℝ, |τ| ≤ 1 / 2 →
      ‖binetDiff c (Complex.I * (τ : ℂ)) -
          Complex.I * (τ : ℂ) / (12 * (c : ℂ) * (1 - Complex.I * (τ : ℂ)))‖ ≤ C * |τ| / c ^ 3) := by
  refine ⟨fun r hr => ⟨(r.factorial : ℝ) * 4 ^ r, fun c hc τ => ?_⟩, fun c hc => ?_, ⟨8, fun c hc τ _ => ?_⟩⟩
  · exact binetDiff_vertical_decay (by linarith) hr τ
  · exact differentiableOn_binetDiff_vertical (by linarith)
  · exact binetDiff_small (by linarith) τ

/-- info: 'FormalResearch.SignUncertainty.ct_dual_id_part1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_dual_id_part1

end FormalResearch.SignUncertainty

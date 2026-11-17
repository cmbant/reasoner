module

public import FormalResearch.Special.AiryCftSignEqualityDiv
public import FormalResearch.Special.AiryCftQUniform
public import FormalResearch.Special.AiryGoodCircles

/-!
# Theorem B at `u₁ = a₁`: `H` is `β + (u - a₁)(q₀ + q₁ u)` (Liouville on the good circles)

CFT `AIRY_POISSON.md` §4, Theorem B′ step 4 and Proof 1 ("`f/Ai²` is `O(r^{N'+1/2})` on good circles with `N' = 1/2`, so a polynomial"):
let `f` be entire with the class bound `‖f(u)‖ ≤ C (1+|u|)^ν e(u)`, `f ∈ L¹(ℝ)`, and `H` entire with `(u - a₁) f(u) = H(u) Ai(u)²`
(`airy_eq_div`).  Then (**proved**, `airy_eq_affine`) there are `q₀, q₁ ∈ ℂ` with

`H(u) = H(a₁) + (u - a₁)(q₀ + q₁ u)`  for all `u`.

Proof: `airyQ_mem_half` (`𝒢_N ⊂ 𝒢_{1/2}`) gives `‖f‖ ≤ C'(1+|u|)^{1/2} e`; on the good circles of `good_circle_exists`
(`‖Ai‖² ≥ (25π)⁻¹(1+r)^{-1/2} e`) this yields `‖H(u)‖ ≤ 25π C' (r + |a₁|)(1+r)`; then `Q = dslope H a₁` has `‖Q‖ ≤ C''(1+r)` on those circles
(large `r`) and is affine by `FormalResearch.EntireDiv.entire_affine_of_circle_bound`.

(The note writes `f/Ai² = P + β/(u - a₁)` with `P` of degree `≤ 1`; here `H = (u - a₁) f/Ai² = β + (u - a₁)(q₀ + q₁u)`, the same
statement.  Its bound on good circles is `|f/Ai²| ≲ r^{N'+1/2} = r`.)
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **`‖H‖` on good circles.**  If `(u - a₁) f(u) = H(u) Ai(u)²` and `‖f u‖ ≤ C' (1+|u|)^{1/2} e(u)`, then on a circle where
`‖Ai‖² ≥ (25π)⁻¹ (1+r)^{-1/2} e`, `‖H u‖ ≤ 25π C' (r + |a₁|)(1 + r)`. -/
lemma airy_eq_H_bound {f H : ℂ → ℂ} {C' : ℝ}
    (hfb : ∀ u : ℂ, ‖f u‖ ≤ C' * (1 + ‖u‖) ^ (1 / 2 : ℝ) * airyEnv u)
    (hH : ∀ u : ℂ, (u - (airyZero 1 : ℂ)) * f u = H u * airyAiC u ^ 2) {r : ℝ} (hr : 0 ≤ r)
    (hgood : ∀ u : ℂ, ‖u‖ = r → 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2)
    {u : ℂ} (hu : ‖u‖ = r) : ‖H u‖ ≤ 25 * π * C' * (r + |airyZero 1|) * (1 + r) := by
  have hpi := Real.pi_pos
  set t : ℝ := (1 + r) ^ (1 / 2 : ℝ) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  have htt : t * t = 1 + r := by
    rw [ht, ← Real.rpow_add (by linarith)]; norm_num
  have hneg : (1 + r) ^ (-(1 / 2) : ℝ) = t⁻¹ := by
    rw [Real.rpow_neg (by linarith)]
  set e : ℝ := airyEnv u with he
  have hepos : 0 < e := airyEnv_pos u
  have hg := hgood u hu
  rw [hneg] at hg
  set c : ℝ := 1 / (25 * π) * t⁻¹ * e with hc
  have hcpos : 0 < c := by positivity
  have h1 := hH u
  have hnorm : ‖u - (airyZero 1 : ℂ)‖ * ‖f u‖ = ‖H u‖ * ‖airyAiC u‖ ^ 2 := by
    have := congrArg norm h1
    rwa [norm_mul, norm_mul, norm_pow] at this
  have hu1 : ‖u - (airyZero 1 : ℂ)‖ ≤ r + |airyZero 1| := by
    calc ‖u - (airyZero 1 : ℂ)‖ ≤ ‖u‖ + ‖(airyZero 1 : ℂ)‖ := norm_sub_le _ _
      _ = r + |airyZero 1| := by rw [hu, Complex.norm_real, Real.norm_eq_abs]
  have hf1 : ‖f u‖ ≤ C' * t * e := by
    have := hfb u
    rw [hu] at this
    exact this
  have h2 : ‖H u‖ * c ≤ (r + |airyZero 1|) * (C' * t * e) := by
    calc ‖H u‖ * c ≤ ‖H u‖ * ‖airyAiC u‖ ^ 2 := by gcongr
      _ = ‖u - (airyZero 1 : ℂ)‖ * ‖f u‖ := hnorm.symm
      _ ≤ (r + |airyZero 1|) * (C' * t * e) := by
          gcongr
  have h3 : ‖H u‖ ≤ (r + |airyZero 1|) * (C' * t * e) / c := (le_div_iff₀ hcpos).2 h2
  have h4 : (r + |airyZero 1|) * (C' * t * e) / c = 25 * π * C' * (r + |airyZero 1|) * (t * t) := by
    rw [hc]; field_simp
  rw [h4, htt] at h3
  exact h3

/-- **`H = β + (u - a₁)(q₀ + q₁ u)`.** -/
theorem airy_eq_affine {f H : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hHd : Differentiable ℂ H)
    (hH : ∀ u : ℂ, (u - (airyZero 1 : ℂ)) * f u = H u * airyAiC u ^ 2) :
    ∃ q₀ q₁ : ℂ, ∀ u : ℂ, H u = H (airyZero 1 : ℂ) + (u - (airyZero 1 : ℂ)) * (q₀ + q₁ * u) := by
  have hpi := Real.pi_pos
  obtain ⟨C', hC', hfb⟩ := airyQ_mem_half hf hfi hC hb
  set a : ℝ := airyZero 1 with ha
  set B : ℝ := ‖H (a : ℂ)‖ with hB
  set Q : ℂ → ℂ := dslope H (a : ℂ) with hQ
  have dQ : Differentiable ℂ Q := EntireDiv.differentiable_dslope_entire hHd _
  have hCnn : 0 ≤ 100 * π * C' + 2 * B := by positivity
  have hcirc : ∀ R : ℝ, ∃ r : ℝ, R ≤ r ∧ ∀ u : ℂ, ‖u‖ = r → ‖Q u‖ ≤ (100 * π * C' + 2 * B) * (1 + r) := by
    intro R
    set k : ℕ := ⌈max R (10 + 2 * |a|)⌉₊ with hk
    have hkR : max R (10 + 2 * |a|) ≤ k := Nat.le_ceil _
    have h10 : (10 : ℝ) ≤ k := by
      have := le_max_right R (10 + 2 * |a|)
      have := abs_nonneg a
      linarith
    obtain ⟨r, hr1, hr2, hgood⟩ := good_circle_exists k (by exact_mod_cast h10)
    refine ⟨r, (le_max_left _ _).trans (hkR.trans hr1), fun u hu => ?_⟩
    have hr2a : 2 * |a| + 10 ≤ r := by
      have := le_max_right R (10 + 2 * |a|); linarith
    have hra := abs_nonneg a
    have hrpos : 0 < r := by linarith
    have hHb := airy_eq_H_bound hfb hH hrpos.le hgood hu
    have hne : u ≠ (a : ℂ) := by
      intro h
      rw [h, Complex.norm_real, Real.norm_eq_abs] at hu
      linarith
    have hden : r / 2 ≤ ‖u - (a : ℂ)‖ := by
      have : r - |a| ≤ ‖u - (a : ℂ)‖ := by
        have := norm_sub_norm_le u (a : ℂ)
        rw [hu, Complex.norm_real, Real.norm_eq_abs] at this
        exact this
      linarith
    have hdenpos : 0 < ‖u - (a : ℂ)‖ := by linarith
    have hQu : Q u = (H u - H (a : ℂ)) / (u - (a : ℂ)) := by
      rw [hQ, dslope_of_ne _ hne, slope_def_field]
    rw [hQu, norm_div]
    rw [div_le_iff₀ hdenpos]
    have hnum : ‖H u - H (a : ℂ)‖ ≤ 25 * π * C' * (r + |a|) * (1 + r) + B := by
      calc ‖H u - H (a : ℂ)‖ ≤ ‖H u‖ + ‖H (a : ℂ)‖ := norm_sub_le _ _
        _ ≤ _ := by rw [← hB]; linarith
    have hnum2 : 25 * π * C' * (r + |a|) * (1 + r) ≤ 50 * π * C' * r * (1 + r) := by
      have : (r + |a|) ≤ 2 * r := by linarith
      have h0 : 0 ≤ 25 * π * C' * (1 + r) := by positivity
      calc 25 * π * C' * (r + |a|) * (1 + r) = (25 * π * C' * (1 + r)) * (r + |a|) := by ring
        _ ≤ (25 * π * C' * (1 + r)) * (2 * r) := by gcongr
        _ = 50 * π * C' * r * (1 + r) := by ring
    have hB0 : 0 ≤ B := norm_nonneg _
    calc ‖H u - H (a : ℂ)‖ ≤ 50 * π * C' * r * (1 + r) + B := hnum.trans (by linarith)
      _ ≤ (100 * π * C' + 2 * B) * (1 + r) * (r / 2) := by
          have h1 : 0 ≤ 100 * π * C' * (1 + r) * (r / 2) := by positivity
          have : B ≤ B * r := by nlinarith
          nlinarith [mul_nonneg hB0 hrpos.le, mul_nonneg (mul_nonneg hpi.le hC') hrpos.le]
      _ ≤ (100 * π * C' + 2 * B) * (1 + r) * ‖u - (a : ℂ)‖ := by gcongr
  obtain ⟨q₀, q₁, hq⟩ := EntireDiv.entire_affine_of_circle_bound dQ hCnn hcirc
  refine ⟨q₀, q₁, fun u => ?_⟩
  have e1 : (u - (a : ℂ)) • Q u = H u - H (a : ℂ) := sub_smul_dslope H (a : ℂ) u
  simp only [smul_eq_mul] at e1
  rw [hq u] at e1
  linear_combination -e1

/-- info: 'FormalResearch.Special.airy_eq_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_eq_affine

end FormalResearch.Special

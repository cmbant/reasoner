module

public import FormalResearch.SignUncertainty.CtOscIBP
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Pointwise bounds for the double-integration-by-parts integrand

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu` Step 4, Pieces 2 and 3 (the four terms
`|B''|/|Φ'|², |B'Φ''|/|Φ'|³, |BΦ'''|/|Φ'|³, |B|(Φ'')²/|Φ'|⁴`).  **Proved.**

With `σ(τ) = τ²/(1+τ²)`, amplitude bounds `‖B^{(k)}‖ ≤ K τ^{1/2-k}/(1+τ)`, `|ϕ''| ≤ C₀ σ/τ`, `|ϕ'''| ≤ C₀/(1+τ)²`, and a
lower bound `|ϕ'| ≥ p` with `γ σ ≤ p`, all four terms are `≤ K' τ^{-3/2}/((1+τ)p²)`.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty.CtOsc

/-- `σ(τ) = τ²/(1+τ²)`. -/
noncomputable def sg (τ : ℝ) : ℝ := τ ^ 2 / (1 + τ ^ 2)

lemma sg_nonneg (τ : ℝ) : 0 ≤ sg τ := by unfold sg; positivity

lemma sg_le_one (τ : ℝ) : sg τ ≤ 1 := by
  unfold sg; rw [div_le_one (by positivity)]; linarith [sq_nonneg τ]

lemma sg_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : sg a ≤ sg b := by
  unfold sg
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : a ^ 2 ≤ b ^ 2 := by nlinarith
  nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg (sq_nonneg a) (sq_nonneg b)]

lemma sq_div_sq_le_sg (τ : ℝ) (hτ : 0 < τ) : τ ^ 2 / (1 + τ) ^ 2 ≤ sg τ := by
  unfold sg
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg τ, mul_nonneg (sq_nonneg τ) hτ.le]

/-- The weight `τ^{-3/2}/(1+τ)`. -/
noncomputable def wt (τ : ℝ) : ℝ := τ ^ (-3 / 2 : ℝ) / (1 + τ)

lemma wt_pos {τ : ℝ} (hτ : 0 < τ) : 0 < wt τ := by unfold wt; positivity

lemma rpow_half_eq {τ : ℝ} (hτ : 0 < τ) : τ ^ (1 / 2 : ℝ) = τ ^ 2 * τ ^ (-3 / 2 : ℝ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add hτ]; norm_num

lemma rpow_neg_half_eq {τ : ℝ} (hτ : 0 < τ) : τ ^ (-1 / 2 : ℝ) = τ * τ ^ (-3 / 2 : ℝ) := by
  rw [← Real.rpow_one_add' hτ.le (by norm_num)]; norm_num

lemma Q_real {KB C0 u τ s p γ : ℝ} (hτ : 0 < τ) (hp : 0 < p) (hγ : 0 < γ) (hC0 : 0 ≤ C0) (hKB : 0 ≤ KB)
    (hu : 0 ≤ u) (hs0 : 0 ≤ s) (hsp : s ≤ p / γ) (hτs : τ ^ 2 / (1 + τ) ^ 2 ≤ s) :
    KB * u / p ^ 2 + 3 * (KB * τ * u) * (C0 * (s / τ)) / p ^ 3 + (KB * τ ^ 2 * u) * (C0 / (1 + τ) ^ 2) / p ^ 3 +
      3 * (KB * τ ^ 2 * u) * (C0 * (s / τ)) ^ 2 / p ^ 4 ≤
      KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * u / p ^ 2 := by
  have hKu : 0 ≤ KB * u := mul_nonneg hKB hu
  have hsγ : s ≤ p / γ := hsp
  have e2 : 3 * (KB * τ * u) * (C0 * (s / τ)) / p ^ 3 = 3 * (KB * u) * C0 * (s / p) / p ^ 2 := by
    field_simp
  have e3 : (KB * τ ^ 2 * u) * (C0 / (1 + τ) ^ 2) / p ^ 3 =
      (KB * u) * C0 * (τ ^ 2 / (1 + τ) ^ 2 / p) / p ^ 2 := by
    field_simp
  have e4 : 3 * (KB * τ ^ 2 * u) * (C0 * (s / τ)) ^ 2 / p ^ 4 = 3 * (KB * u) * C0 ^ 2 * (s / p) ^ 2 / p ^ 2 := by
    field_simp
  have hq : s / p ≤ 1 / γ := by
    rw [div_le_iff₀ hp]
    calc s ≤ p / γ := hsγ
      _ = 1 / γ * p := by ring
  have hq0 : 0 ≤ s / p := by positivity
  have hq3 : τ ^ 2 / (1 + τ) ^ 2 / p ≤ 1 / γ :=
    (div_le_div_of_nonneg_right hτs hp.le).trans hq
  have hq30 : 0 ≤ τ ^ 2 / (1 + τ) ^ 2 / p := by positivity
  have hp2 : 0 < p ^ 2 := by positivity
  rw [e2, e3, e4]
  have a2 : 3 * (KB * u) * C0 * (s / p) / p ^ 2 ≤ 3 * (KB * u) * C0 * (1 / γ) / p ^ 2 := by
    gcongr
  have a3 : (KB * u) * C0 * (τ ^ 2 / (1 + τ) ^ 2 / p) / p ^ 2 ≤ (KB * u) * C0 * (1 / γ) / p ^ 2 := by
    gcongr
  have a4 : 3 * (KB * u) * C0 ^ 2 * (s / p) ^ 2 / p ^ 2 ≤ 3 * (KB * u) * C0 ^ 2 * (1 / γ) ^ 2 / p ^ 2 := by
    gcongr
  have : KB * u / p ^ 2 + 3 * (KB * u) * C0 * (1 / γ) / p ^ 2 + (KB * u) * C0 * (1 / γ) / p ^ 2 +
      3 * (KB * u) * C0 ^ 2 * (1 / γ) ^ 2 / p ^ 2 = KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * u / p ^ 2 := by
    field_simp
    ring
  linarith [a2, a3, a4]

/-- The four terms of `Q`. -/
lemma Q_pt {τ p γ C0 KB : ℝ} (hτ : 0 < τ) (hp : 0 < p) (hγ : 0 < γ) (hC0 : 0 ≤ C0) (hKB : 0 ≤ KB)
    (hσ : γ * sg τ ≤ p)
    {ϕ1 ϕ2 ϕ3 : ℝ → ℝ} {B B1 B2 : ℝ → ℂ}
    (h1 : p ≤ |ϕ1 τ|) (h2 : |ϕ2 τ| ≤ C0 * (sg τ / τ)) (h3 : |ϕ3 τ| ≤ C0 / (1 + τ) ^ 2)
    (hB : ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ)) (hB1 : ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ))
    (hB2 : ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ)) :
    ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 τ‖ ≤
      KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) * wt τ / p ^ 2 := by
  have hu := wt_pos hτ
  set u := wt τ with hu_def
  have e0 : KB * τ ^ (1 / 2 : ℝ) / (1 + τ) = KB * τ ^ 2 * u := by
    rw [rpow_half_eq hτ, hu_def]; unfold wt; ring
  have e1 : KB * τ ^ (-1 / 2 : ℝ) / (1 + τ) = KB * τ * u := by
    rw [rpow_neg_half_eq hτ, hu_def]; unfold wt; ring
  have e2 : KB * τ ^ (-3 / 2 : ℝ) / (1 + τ) = KB * u := by
    rw [hu_def]; unfold wt; ring
  rw [e0] at hB; rw [e1] at hB1; rw [e2] at hB2
  have hsgp : sg τ ≤ p / γ := by rw [le_div_iff₀ hγ]; linarith
  have hsg0 := sg_nonneg τ
  set x := |ϕ1 τ| with hx
  have hxp : 0 < x := lt_of_lt_of_le hp h1
  have hn1 : ‖(ϕ1 τ : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖(ϕ2 τ : ℂ)‖ = |ϕ2 τ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hn3 : ‖(ϕ3 τ : ℂ)‖ = |ϕ3 τ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖ibpQ B B1 B2 ϕ1 ϕ2 ϕ3 τ‖ ≤ ‖B2 τ‖ / x ^ 2 + 3 * ‖B1 τ‖ * |ϕ2 τ| / x ^ 3 +
      ‖B τ‖ * |ϕ3 τ| / x ^ 3 + 3 * ‖B τ‖ * |ϕ2 τ| ^ 2 / x ^ 4 := by
    unfold ibpQ
    have t1 : ‖B2 τ / (ϕ1 τ : ℂ) ^ 2‖ = ‖B2 τ‖ / x ^ 2 := by rw [norm_div, norm_pow, hn1]
    have t2 : ‖3 * B1 τ * (ϕ2 τ : ℂ) / (ϕ1 τ : ℂ) ^ 3‖ = 3 * ‖B1 τ‖ * |ϕ2 τ| / x ^ 3 := by
      rw [norm_div, norm_pow, hn1, norm_mul, norm_mul, hn2]; simp
    have t3 : ‖B τ * (ϕ3 τ : ℂ) / (ϕ1 τ : ℂ) ^ 3‖ = ‖B τ‖ * |ϕ3 τ| / x ^ 3 := by
      rw [norm_div, norm_pow, hn1, norm_mul, hn3]
    have t4 : ‖3 * B τ * (ϕ2 τ : ℂ) ^ 2 / (ϕ1 τ : ℂ) ^ 4‖ = 3 * ‖B τ‖ * |ϕ2 τ| ^ 2 / x ^ 4 := by
      rw [norm_div, norm_pow, hn1, norm_mul, norm_mul, norm_pow, hn2]; simp
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (le_of_eq t1) (le_of_eq t2))) (le_of_eq t3))) (le_of_eq t4)
  have hτs : τ ^ 2 / (1 + τ) ^ 2 ≤ sg τ := sq_div_sq_le_sg τ hτ
  have hKBu : 0 ≤ KB * u := mul_nonneg hKB hu.le
  have hC2 : 0 ≤ C0 * (sg τ / τ) := by positivity
  have hxp_le : ∀ k : ℕ, p ^ k ≤ x ^ k := fun k => pow_le_pow_left₀ hp.le h1 k
  have b1 : ‖B2 τ‖ / x ^ 2 ≤ KB * u / p ^ 2 :=
    div_le_div₀ hKBu hB2 (by positivity) (hxp_le 2)
  have b2 : 3 * ‖B1 τ‖ * |ϕ2 τ| / x ^ 3 ≤ 3 * (KB * τ * u) * (C0 * (sg τ / τ)) / p ^ 3 := by
    refine div_le_div₀ (by positivity) ?_ (by positivity) (hxp_le 3)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB1 (by norm_num)) h2 (abs_nonneg _) (by positivity)
  have b3 : ‖B τ‖ * |ϕ3 τ| / x ^ 3 ≤ (KB * τ ^ 2 * u) * (C0 / (1 + τ) ^ 2) / p ^ 3 := by
    refine div_le_div₀ (by positivity) ?_ (by positivity) (hxp_le 3)
    exact mul_le_mul hB h3 (abs_nonneg _) (by positivity)
  have b4 : 3 * ‖B τ‖ * |ϕ2 τ| ^ 2 / x ^ 4 ≤ 3 * (KB * τ ^ 2 * u) * (C0 * (sg τ / τ)) ^ 2 / p ^ 4 := by
    refine div_le_div₀ (by positivity) ?_ (by positivity) (hxp_le 4)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) (pow_le_pow_left₀ (abs_nonneg _) h2 2)
      (by positivity) (by positivity)
  have hQ := Q_real (KB := KB) (C0 := C0) (u := u) (τ := τ) (s := sg τ) (p := p) (γ := γ) hτ hp hγ hC0 hKB hu.le hsg0 hsgp hτs
  linarith [hnorm, b1, b2, b3, b4, hQ]

/-- The first-order term `H = (B/ϕ')'`. -/
lemma H_pt {τ p γ C0 KB : ℝ} (hτ : 0 < τ) (hp : 0 < p) (hγ : 0 < γ) (hC0 : 0 ≤ C0) (hKB : 0 ≤ KB)
    (hσ : γ * sg τ ≤ p)
    {ϕ1 ϕ2 : ℝ → ℝ} {B B1 : ℝ → ℂ}
    (h1 : p ≤ |ϕ1 τ|) (h2 : |ϕ2 τ| ≤ C0 * (sg τ / τ))
    (hB : ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ)) (hB1 : ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ)) :
    ‖ibpH B B1 ϕ1 ϕ2 τ‖ ≤ KB * (1 + C0 / γ) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := by
  have hsgp : sg τ ≤ p / γ := by rw [le_div_iff₀ hγ]; linarith
  have hsg0 := sg_nonneg τ
  set x := |ϕ1 τ| with hx
  have hxp : 0 < x := lt_of_lt_of_le hp h1
  have hn1 : ‖(ϕ1 τ : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖(ϕ2 τ : ℂ)‖ = |ϕ2 τ| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have hnorm : ‖ibpH B B1 ϕ1 ϕ2 τ‖ ≤ ‖B1 τ‖ / x + ‖B τ‖ * |ϕ2 τ| / x ^ 2 := by
    unfold ibpH
    have t1 : ‖B1 τ * (ϕ1 τ : ℂ) / (ϕ1 τ : ℂ) ^ 2‖ = ‖B1 τ‖ / x := by
      rw [norm_div, norm_pow, hn1, norm_mul, hn1]; field_simp
    have t2 : ‖B τ * (ϕ2 τ : ℂ) / (ϕ1 τ : ℂ) ^ 2‖ = ‖B τ‖ * |ϕ2 τ| / x ^ 2 := by
      rw [norm_div, norm_pow, hn1, norm_mul, hn2]
    have : B1 τ * (ϕ1 τ : ℂ) - B τ * (ϕ2 τ : ℂ) = B1 τ * (ϕ1 τ : ℂ) - B τ * (ϕ2 τ : ℂ) := rfl
    rw [sub_div]
    exact (norm_sub_le _ _).trans (add_le_add (le_of_eq t1) (le_of_eq t2))
  have hw : 0 ≤ τ ^ (-1 / 2 : ℝ) / (1 + τ) := by positivity
  have c1 : ‖B1 τ‖ / x ≤ KB * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := by
    refine div_le_div₀ (by positivity) ?_ hp h1
    calc ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ) := hB1
      _ = KB * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by ring
  have c2 : ‖B τ‖ * |ϕ2 τ| / x ^ 2 ≤ KB * (C0 / γ) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := by
    have e : KB * τ ^ (1 / 2 : ℝ) / (1 + τ) * (C0 * (sg τ / τ)) =
        KB * C0 * sg τ * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by
      have : τ ^ (1 / 2 : ℝ) = τ ^ (-1 / 2 : ℝ) * τ := by
        rw [← Real.rpow_add_one hτ.ne']; norm_num
      rw [this]; field_simp
    have step : ‖B τ‖ * |ϕ2 τ| / x ^ 2 ≤ KB * C0 * sg τ * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p ^ 2 := by
      rw [← e]
      refine div_le_div₀ (by positivity) (mul_le_mul hB h2 (abs_nonneg _) (by positivity)) (by positivity)
        (pow_le_pow_left₀ hp.le h1 2)
    refine step.trans ?_
    have hq : sg τ / p ≤ 1 / γ := by
      rw [div_le_iff₀ hp]
      calc sg τ ≤ p / γ := hsgp
        _ = 1 / γ * p := by ring
    have : KB * C0 * sg τ * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p ^ 2 =
        KB * C0 * (sg τ / p) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := by field_simp
    rw [this]
    have h0 : 0 ≤ KB * C0 * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) := by positivity
    calc KB * C0 * (sg τ / p) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p
        = (KB * C0 * (τ ^ (-1 / 2 : ℝ) / (1 + τ))) * (sg τ / p) / p := by ring
      _ ≤ (KB * C0 * (τ ^ (-1 / 2 : ℝ) / (1 + τ))) * (1 / γ) / p := by gcongr
      _ = KB * (C0 / γ) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := by ring
  calc ‖ibpH B B1 ϕ1 ϕ2 τ‖ ≤ _ := hnorm
    _ ≤ KB * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p + KB * (C0 / γ) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := add_le_add c1 c2
    _ = KB * (1 + C0 / γ) * (τ ^ (-1 / 2 : ℝ) / (1 + τ)) / p := by ring

end FormalResearch.SignUncertainty.CtOsc

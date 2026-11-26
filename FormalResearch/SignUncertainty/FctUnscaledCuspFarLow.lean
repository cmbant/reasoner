/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctUnscaledCuspFarLowAux

/-!
# `fct:unscaled-cusp`, regime `u ≥ 1`: the low piece `[(cu)^{-1}, t₀/2]` (F2a), pointwise and endpoint estimates

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, Lemma `fct:unscaled-cusp`, third estimate.

With `K = C_a M (e^η + 8/η²)`, `E(x) = e^{-ηx/2}`, `B_j = K x^{1/2-j} E`, `P₁ = c g(x)` where `g = u/2` for `x ≤ γ` and
`g = g_m` for `x > γ` (`γ = min(t_*, t₀/2)`), `P₂ = cκ₃/x`, `P₃ = cC₂`, the majorant expression `ibpF` is dominated by
`Ψ(x) = K c^{-2} [(A₁ + A₂ ε) x^{-3/2} + C₂ (R₁ + R₂ ε) x^{1/2} e^{-ηx/4}]`, `ε = e^{-ηγ/4}`
(`far_pt_le`); `far_alpha_end`, `far_beta_end` bound the endpoint terms at `y²` and at `t₀/2`.

Class: proved.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty.FctUnscaledCusp

open FormalResearch.SignUncertainty FormalResearch.SignUncertainty.FctCuspEdge

/-- `A(g) = g^{-2} + 3κ₃ g^{-3} + 3κ₃² g^{-4}`. -/
noncomputable def cuspFarA (g k3 : ℝ) : ℝ := (g ^ 2)⁻¹ + 3 * k3 * (g ^ 3)⁻¹ + 3 * k3 ^ 2 * (g ^ 4)⁻¹

lemma cuspFarA_nonneg {g k3 : ℝ} (hg : 0 < g) (hk : 0 ≤ k3) : 0 ≤ cuspFarA g k3 := by
  unfold cuspFarA; positivity

/-- The floor `g_m = min (G₂, 1/2)` of the gap. -/
noncomputable def cuspGm (κ₁ κ₂ : ℝ) : ℝ := min (cuspG2 κ₁ κ₂) (1 / 2)

section Low

variable {𝔪 : ℝ → ℝ} {κ₁ κ₂ C₂ C₀ η Ca M : ℝ} {a : ℝ → ℂ}

lemma cuspGm_pos (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) : 0 < cuspGm κ₁ κ₂ := lt_min (cuspG2_pos h) (by norm_num)

lemma cuspGm_le_half (κ₁ κ₂ : ℝ) : cuspGm κ₁ κ₂ ≤ 1 / 2 := min_le_right _ _

lemma cuspGm_le_G2 (κ₁ κ₂ : ℝ) : cuspGm κ₁ κ₂ ≤ cuspG2 κ₁ κ₂ := min_le_left _ _

/-- `‖a'' x‖ ≤ K x^{-3/2} e^{-ηx/2}` on `x > 0`. -/
lemma CuspAmpPos.amp2 (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca) (hM : 0 ≤ M) {x : ℝ} (hx : 0 < x) :
    ‖deriv (deriv a) x‖ ≤ Ca * M * ampC η * (x ^ (-(3 : ℝ) / 2) * Real.exp (-(η / 2) * x)) := by
  have := ha.jet_le hη hCa hM (j := 2) (by norm_num) hx
  rw [iteratedDeriv_two_eq] at this
  unfold ampB at this
  have e : (1 : ℝ) / 2 - ((2 : ℕ) : ℝ) = -(3 : ℝ) / 2 := by norm_num
  rw [e] at this
  exact this

/-- Algebra of the pointwise domination, case `x ≤ γ`. -/
lemma far_pt_alg1 {T E E' ε X Z A1 A2 R1 R2 C2 : ℝ} (hT : 0 ≤ T) (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hC2 : 0 ≤ C2) (hε : 0 ≤ ε) (hE' : 0 ≤ E')
    (h1 : E ≤ 1) (h2 : E ≤ E') :
    T * (E * (A1 * X + C2 * R1 * Z)) ≤ T * ((A1 + A2 * ε) * X + C2 * (R1 + R2 * ε) * (Z * E')) := by
  refine mul_le_mul_of_nonneg_left ?_ hT
  have p1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hA1 hX)
  have p2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg (mul_nonneg hC2 hR1) hZ)
  have q1 : 0 ≤ A2 * ε * X := by positivity
  have q2 : 0 ≤ C2 * R2 * ε * (Z * E') := by positivity
  nlinarith [p1, p2, q1, q2]

/-- Algebra of the pointwise domination, case `x > γ`. -/
lemma far_pt_alg2 {T E E' ε X Z A1 A2 R1 R2 C2 : ℝ} (hT : 0 ≤ T) (hX : 0 ≤ X) (hZ : 0 ≤ Z) (hA1 : 0 ≤ A1)
    (hA2 : 0 ≤ A2) (hR1 : 0 ≤ R1) (hR2 : 0 ≤ R2) (hC2 : 0 ≤ C2) (hE' : 0 ≤ E')
    (h1 : E ≤ ε) (h2 : E ≤ ε * E') :
    T * (E * (A2 * X + C2 * R2 * Z)) ≤ T * ((A1 + A2 * ε) * X + C2 * (R1 + R2 * ε) * (Z * E')) := by
  refine mul_le_mul_of_nonneg_left ?_ hT
  have p1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hA2 hX)
  have p2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg (mul_nonneg hC2 hR2) hZ)
  have q1 : 0 ≤ A1 * X := by positivity
  have q2 : 0 ≤ C2 * R1 * (Z * E') := by positivity
  nlinarith [p1, p2, q1, q2]

/-- The pointwise domination `ibpF ≤ Ψ` (cases `x ≤ γ`, `x > γ`). -/
lemma far_pt_le {K c κ₃ C2 u gm γ x : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hk3 : 0 ≤ κ₃) (hC2 : 0 ≤ C2) (hu : 0 < u)
    (hgm : 0 < gm) (hη : 0 < η) (hx : 0 < x) :
    ibpF (K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x))) (K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
        (K * (x ^ (-(3 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
        (c * (if x ≤ γ then u / 2 else gm)) (c * κ₃ / x) (c * C2) ≤
      K * (c ^ 2)⁻¹ * ((cuspFarA (u / 2) κ₃ + cuspFarA gm κ₃ * Real.exp (-(η / 4) * γ)) * x ^ (-(3 : ℝ) / 2) +
        C2 * (((u / 2) ^ 3)⁻¹ + (gm ^ 3)⁻¹ * Real.exp (-(η / 4) * γ)) *
          (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x))) := by
  have hX : 0 ≤ x ^ (-(3 : ℝ) / 2) := Real.rpow_nonneg hx.le _
  have hZ : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx.le _
  have hE0 : 0 < Real.exp (-(η / 2) * x) := Real.exp_pos _
  have hE1 : Real.exp (-(η / 2) * x) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE2 : Real.exp (-(η / 2) * x) ≤ Real.exp (-(η / 4) * x) := Real.exp_le_exp.2 (by nlinarith)
  have hε0 : 0 < Real.exp (-(η / 4) * γ) := Real.exp_pos _
  have hE' : 0 < Real.exp (-(η / 4) * x) := Real.exp_pos _
  have hA1 : 0 ≤ cuspFarA (u / 2) κ₃ := cuspFarA_nonneg (by positivity) hk3
  have hA2 : 0 ≤ cuspFarA gm κ₃ := cuspFarA_nonneg hgm hk3
  have hR1 : 0 ≤ ((u / 2) ^ 3)⁻¹ := by positivity
  have hR2 : 0 ≤ (gm ^ 3)⁻¹ := by positivity
  have hT : 0 ≤ K * (c ^ 2)⁻¹ := by positivity
  have hrep : ∀ g : ℝ, 0 < g → ibpF (K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
      (K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x))) (K * (x ^ (-(3 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
      (c * g) (c * κ₃ / x) (c * C2) =
      (K * (c ^ 2)⁻¹) * (Real.exp (-(η / 2) * x) * (cuspFarA g κ₃ * x ^ (-(3 : ℝ) / 2) +
        C2 * (g ^ 3)⁻¹ * x ^ ((1 : ℝ) / 2))) := by
    intro g hg
    rw [ibpF_far_eq hx hc hg]; unfold cuspFarA; ring
  by_cases hxγ : x ≤ γ
  · simp only [hxγ, ↓reduceIte]
    rw [hrep _ (by positivity)]
    have := far_pt_alg1 hT hX hZ hA1 hA2 hR1 hR2 hC2 hε0.le hE'.le hE1 hE2
    refine this.trans (le_of_eq ?_)
    ring
  · simp only [hxγ, ↓reduceIte]
    rw [hrep _ hgm]
    push Not at hxγ
    have hEε : Real.exp (-(η / 2) * x) ≤ Real.exp (-(η / 4) * γ) := Real.exp_le_exp.2 (by nlinarith)
    have hEε' : Real.exp (-(η / 2) * x) ≤ Real.exp (-(η / 4) * γ) * Real.exp (-(η / 4) * x) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by nlinarith)
    have := far_pt_alg2 hT hX hZ hA1 hA2 hR1 hR2 hC2 hE'.le hEε hEε'
    refine this.trans (le_of_eq ?_)
    ring

/-- `(1+x) e^{-ηx/2} ≤ (1 + 4/η) e^{-ηx/4}`. -/
lemma exp_poly1 {η x : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    (1 + x) * Real.exp (-(η / 2) * x) ≤ (1 + 4 / η) * Real.exp (-(η / 4) * x) := by
  have h1 := one_add_mul_exp_le (z := η / 4) (x := x) (by positivity) hx
  have e : Real.exp (-(η / 2) * x) = Real.exp (-(η / 4) * x) * Real.exp (-(η / 4) * x) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : 1 + 1 / (η / 4) = 1 + 4 / η := by field_simp
  rw [e2] at h1
  have := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-(η / 4) * x)).le
  calc (1 + x) * Real.exp (-(η / 2) * x) = ((1 + x) * Real.exp (-(η / 4) * x)) * Real.exp (-(η / 4) * x) := by
        rw [e]; ring
    _ ≤ _ := by simpa [mul_comm, mul_assoc, mul_left_comm] using this

/-- `(1+x)² e^{-ηx/2} ≤ (1 + 8/η)² e^{-ηx/4}`. -/
lemma exp_poly2 {η x : ℝ} (hη : 0 < η) (hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-(η / 2) * x) ≤ (1 + 8 / η) ^ 2 * Real.exp (-(η / 4) * x) := by
  have h1 := one_add_mul_exp_le (z := η / 8) (x := x) (by positivity) hx
  have e : Real.exp (-(η / 2) * x) =
      Real.exp (-(η / 8) * x) * Real.exp (-(η / 8) * x) * Real.exp (-(η / 4) * x) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have e2 : 1 + 1 / (η / 8) = 1 + 8 / η := by field_simp
  rw [e2] at h1
  have h0 : 0 ≤ (1 + x) * Real.exp (-(η / 8) * x) := by positivity
  have h3 := mul_self_le_mul_self h0 h1
  calc (1 + x) ^ 2 * Real.exp (-(η / 2) * x) =
      ((1 + x) * Real.exp (-(η / 8) * x)) * ((1 + x) * Real.exp (-(η / 8) * x)) * Real.exp (-(η / 4) * x) := by
        rw [e]; ring
    _ ≤ ((1 + 8 / η) * (1 + 8 / η)) * Real.exp (-(η / 4) * x) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = _ := by ring

/-- The constant of the endpoint term at `t₀/2`. -/
noncomputable def cuspFarD2 (η κ₃ gm : ℝ) : ℝ :=
  (1 + 2 * κ₃) * ((1 + 4 / η) * (1 / gm + 1 / gm ^ 2) + 2 * κ₃ ^ 2 * (1 + 8 / η) ^ 2 / gm ^ 3)

/-- The endpoint term at `β = t₀/2`: `≤ (K/c) D₂ e^{-ηβ/4}`. -/
lemma far_beta_end {K c gm κ₃ β η p1 : ℝ} (hK : 0 ≤ K) (hc : 1 ≤ c) (hgm : 0 < gm) (hk3 : 0 ≤ κ₃) (hβ : 0 < β)
    (hβ2 : 1 ≤ 2 * κ₃ * β ^ 2) (hη : 0 < η) (hp1 : c * gm ≤ p1) :
    ibpEnd (K * (β ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * β))) (K * (β ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * β)))
        p1 (c * κ₃ / β) ≤ K / c * (cuspFarD2 η κ₃ gm * Real.exp (-(η / 4) * β)) := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hE0 : 0 < Real.exp (-(η / 2) * β) := Real.exp_pos _
  have hs0 : β ^ ((1 : ℝ) / 2) ≤ 1 + β := rpow_half_le_one_add hβ
  have hinv : β⁻¹ ≤ 2 * κ₃ * β := by
    rw [inv_eq_one_div, div_le_iff₀ hβ]; nlinarith
  have hs1 : β ^ (-(1 : ℝ) / 2) ≤ (1 + 2 * κ₃) * (1 + β) := by
    have := rpow_neg_half_le_one_add hβ
    nlinarith [mul_nonneg hk3 hβ.le]
  have hs0' : β ^ ((1 : ℝ) / 2) ≤ (1 + 2 * κ₃) * (1 + β) := by
    nlinarith [mul_nonneg hk3 hβ.le, mul_nonneg hk3 hk3]
  set W : ℝ := (1 + 2 * κ₃) * (1 + β) with hW
  have hW0 : 0 < W := by positivity
  set Eβ : ℝ := Real.exp (-(η / 2) * β) with hEβ
  have hp2 : c * κ₃ / β ≤ 2 * c * κ₃ ^ 2 * (1 + β) := by
    have : c * κ₃ / β = c * κ₃ * β⁻¹ := by rw [div_eq_mul_inv]
    rw [this]
    have h1 : c * κ₃ * β⁻¹ ≤ c * κ₃ * (2 * κ₃ * β) := mul_le_mul_of_nonneg_left hinv (by positivity)
    nlinarith [mul_nonneg (mul_nonneg hc0.le (mul_nonneg hk3 hk3)) hβ.le, mul_nonneg hc0.le (mul_nonneg hk3 hk3)]
  have hcg : 0 < c * gm := by positivity
  have hb0 : 0 ≤ K * (β ^ ((1 : ℝ) / 2) * Eβ) := by positivity
  have hb1 : 0 ≤ K * (β ^ (-(1 : ℝ) / 2) * Eβ) := by positivity
  have hp2' : 0 ≤ c * κ₃ / β := by positivity
  refine (ibpEnd_mono hcg hp1 hb0 hb1 hp2').trans ?_
  have hmon : ibpEnd (K * (β ^ ((1 : ℝ) / 2) * Eβ)) (K * (β ^ (-(1 : ℝ) / 2) * Eβ)) (c * gm) (c * κ₃ / β) ≤
      ibpEnd (K * (W * Eβ)) (K * (W * Eβ)) (c * gm) (2 * c * κ₃ ^ 2 * (1 + β)) := by
    unfold ibpEnd
    have a0 : K * (β ^ ((1 : ℝ) / 2) * Eβ) ≤ K * (W * Eβ) := by gcongr
    have a1 : K * (β ^ (-(1 : ℝ) / 2) * Eβ) ≤ K * (W * Eβ) := by gcongr
    have a2 := hp2
    have z0 : 0 ≤ K * (W * Eβ) := by positivity
    have e1 : K * (β ^ ((1 : ℝ) / 2) * Eβ) / (c * gm) ≤ K * (W * Eβ) / (c * gm) := by gcongr
    have e2 : K * (β ^ (-(1 : ℝ) / 2) * Eβ) / (c * gm) ≤ K * (W * Eβ) / (c * gm) := by gcongr
    have e3 : K * (β ^ ((1 : ℝ) / 2) * Eβ) * (c * κ₃ / β) / (c * gm) ^ 2 ≤
        K * (W * Eβ) * (2 * c * κ₃ ^ 2 * (1 + β)) / (c * gm) ^ 2 := by
      have : 0 ≤ c * κ₃ / β := hp2'
      calc K * (β ^ ((1 : ℝ) / 2) * Eβ) * (c * κ₃ / β) / (c * gm) ^ 2
          ≤ K * (W * Eβ) * (c * κ₃ / β) / (c * gm) ^ 2 := by gcongr
        _ ≤ _ := by gcongr
    have e4 : (K * (β ^ (-(1 : ℝ) / 2) * Eβ) / (c * gm) + K * (β ^ ((1 : ℝ) / 2) * Eβ) * (c * κ₃ / β) / (c * gm) ^ 2) /
        (c * gm) ≤ (K * (W * Eβ) / (c * gm) + K * (W * Eβ) * (2 * c * κ₃ ^ 2 * (1 + β)) / (c * gm) ^ 2) / (c * gm) := by
      gcongr
    linarith
  refine hmon.trans ?_
  have heq : ibpEnd (K * (W * Eβ)) (K * (W * Eβ)) (c * gm) (2 * c * κ₃ ^ 2 * (1 + β)) =
      K / c * (W * Eβ * (1 / gm + 1 / (c * gm ^ 2)) + 2 * κ₃ ^ 2 * (1 + β) * W * Eβ / (c * gm ^ 3)) := by
    unfold ibpEnd; field_simp; ring
  rw [heq]
  have hcc : 1 / (c * gm ^ 2) ≤ 1 / gm ^ 2 :=
    one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_left (by positivity) hc)
  have hcc2 : 1 / (c * gm ^ 3) ≤ 1 / gm ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (le_mul_of_one_le_left (by positivity) hc)
  have hP1 := exp_poly1 hη hβ.le
  have hP2 := exp_poly2 hη hβ.le
  have hKc : 0 ≤ K / c := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hKc
  have t1 : W * Eβ = (1 + 2 * κ₃) * ((1 + β) * Eβ) := by rw [hW]; ring
  have t2 : 2 * κ₃ ^ 2 * (1 + β) * W * Eβ = 2 * κ₃ ^ 2 * (1 + 2 * κ₃) * ((1 + β) ^ 2 * Eβ) := by rw [hW]; ring
  have t3 : 2 * κ₃ ^ 2 * (1 + β) * W * Eβ / (c * gm ^ 3) ≤ 2 * κ₃ ^ 2 * (1 + β) * W * Eβ * (1 / gm ^ 3) := by
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left hcc2 (by positivity)
  have u1 : W * Eβ * (1 / gm + 1 / (c * gm ^ 2)) ≤ W * Eβ * (1 / gm + 1 / gm ^ 2) := by
    gcongr
  refine (add_le_add u1 t3).trans ?_
  unfold cuspFarD2
  rw [t1, t2]
  have v1 : (1 + 2 * κ₃) * ((1 + β) * Eβ) * (1 / gm + 1 / gm ^ 2) ≤
      (1 + 2 * κ₃) * ((1 + 4 / η) * Real.exp (-(η / 4) * β)) * (1 / gm + 1 / gm ^ 2) := by gcongr
  have v2 : 2 * κ₃ ^ 2 * (1 + 2 * κ₃) * ((1 + β) ^ 2 * Eβ) * (1 / gm ^ 3) ≤
      2 * κ₃ ^ 2 * (1 + 2 * κ₃) * ((1 + 8 / η) ^ 2 * Real.exp (-(η / 4) * β)) * (1 / gm ^ 3) := by gcongr
  calc _ ≤ (1 + 2 * κ₃) * ((1 + 4 / η) * Real.exp (-(η / 4) * β)) * (1 / gm + 1 / gm ^ 2) +
        2 * κ₃ ^ 2 * (1 + 2 * κ₃) * ((1 + 8 / η) ^ 2 * Real.exp (-(η / 4) * β)) * (1 / gm ^ 3) := add_le_add v1 v2
    _ = _ := by ring

/-- The endpoint term at `α = y²` (`y² c u = 1`): `≤ K y³ (6 + 8κ₃)`. -/
lemma far_alpha_end {K c u y κ₃ η : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (hu : 1 ≤ u) (hyc : y ^ 2 * (c * u) = 1)
    (hk3 : 0 ≤ κ₃) (hη : 0 < η) :
    ibpEnd (K * ((y ^ 2) ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * y ^ 2)))
        (K * ((y ^ 2) ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * y ^ 2))) (c * (u / 2)) (c * κ₃ / y ^ 2) ≤
      K * y ^ 3 * (6 + 8 * κ₃) := by
  have hu0 : 0 < u := by linarith
  have hc : c = (y ^ 2 * u)⁻¹ := by
    field_simp; nlinarith [hyc]
  rw [rpow_sq_half hy, rpow_sq_neg_half hy]
  have hE0 : 0 < Real.exp (-(η / 2) * y ^ 2) := Real.exp_pos _
  have hE1 : Real.exp (-(η / 2) * y ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg y])
  generalize Real.exp (-(η / 2) * y ^ 2) = E at hE0 hE1 ⊢
  have heq : ibpEnd (K * (y * E)) (K * (y⁻¹ * E)) (c * (u / 2)) (c * κ₃ / y ^ 2) =
      K * E * y ^ 3 * (6 + 8 * κ₃ / u) := by
    subst hc
    unfold ibpEnd
    field_simp
    ring
  rw [heq]
  have h1 : 8 * κ₃ / u ≤ 8 * κ₃ := by
    rw [div_le_iff₀ hu0]; nlinarith
  have h2 : 0 ≤ K * y ^ 3 := by positivity
  have h3 : K * E * y ^ 3 = E * (K * y ^ 3) := by ring
  rw [h3]
  calc E * (K * y ^ 3) * (6 + 8 * κ₃ / u) ≤ 1 * (K * y ^ 3) * (6 + 8 * κ₃) := by gcongr
    _ = _ := by ring

lemma cuspFarA_u2_le {u κ₃ : ℝ} (hu : 1 ≤ u) (hk3 : 0 ≤ κ₃) :
    u ^ 2 * cuspFarA (u / 2) κ₃ ≤ 4 + 24 * κ₃ + 48 * κ₃ ^ 2 := by
  have hu0 : 0 < u := by linarith
  have e : u ^ 2 * cuspFarA (u / 2) κ₃ = 4 + 24 * κ₃ / u + 48 * κ₃ ^ 2 / u ^ 2 := by
    unfold cuspFarA; field_simp; ring
  rw [e]
  have h1 : 24 * κ₃ / u ≤ 24 * κ₃ := by rw [div_le_iff₀ hu0]; nlinarith
  have h2 : 48 * κ₃ ^ 2 / u ^ 2 ≤ 48 * κ₃ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg κ₃, mul_nonneg (sq_nonneg κ₃) (sub_nonneg.2 hu)]
  linarith

lemma far_R1_le {u : ℝ} (hu : 1 ≤ u) : u ^ 2 * ((u / 2) ^ 3)⁻¹ ≤ 8 := by
  have hu0 : 0 < u := by linarith
  have e : u ^ 2 * ((u / 2) ^ 3)⁻¹ = 8 / u := by field_simp; norm_num
  rw [e, div_le_iff₀ hu0]; nlinarith

/-- The real-variable algebra of the bound for `∫ Ψ`. -/
lemma far_psi_alg {K y u c κ₃ C2 ε Γ A2 R2 : ℝ} (hK : 0 ≤ K) (hy : 0 < y) (hy1 : y ≤ 1) (hu : 1 ≤ u)
    (hyc : y ^ 2 * (c * u) = 1) (hk3 : 0 ≤ κ₃) (hC2 : 0 ≤ C2) (hε : 0 ≤ ε) (hΓ : 0 ≤ Γ)
    (hR2 : 0 ≤ R2) :
    K * (c ^ 2)⁻¹ * (cuspFarA (u / 2) κ₃ + A2 * ε) * (2 * y⁻¹) +
        K * (c ^ 2)⁻¹ * C2 * (((u / 2) ^ 3)⁻¹ + R2 * ε) * Γ ≤
      K * y ^ 3 * (2 * (4 + 24 * κ₃ + 48 * κ₃ ^ 2) + 2 * A2 * (u ^ 2 * ε) + C2 * Γ * (8 + R2 * (u ^ 2 * ε))) := by
  have hu0 : 0 < u := by linarith
  have hc : c = (y ^ 2 * u)⁻¹ := by
    field_simp; nlinarith [hyc]
  have hc2 : (c ^ 2)⁻¹ = y ^ 4 * u ^ 2 := by
    rw [hc]; field_simp
  rw [hc2]
  have hA1 := cuspFarA_u2_le hu hk3
  have hR1 := far_R1_le hu
  have hN : 0 ≤ u ^ 2 * ε := by positivity
  have hy4 : y ^ 4 ≤ y ^ 3 := by
    have : y ^ 4 = y ^ 3 * y := by ring
    rw [this]; nlinarith [pow_pos hy 3]
  have e1 : K * (y ^ 4 * u ^ 2) * (cuspFarA (u / 2) κ₃ + A2 * ε) * (2 * y⁻¹) =
      2 * K * y ^ 3 * (u ^ 2 * cuspFarA (u / 2) κ₃ + A2 * (u ^ 2 * ε)) := by
    field_simp
  have e2 : K * (y ^ 4 * u ^ 2) * C2 * (((u / 2) ^ 3)⁻¹ + R2 * ε) * Γ =
      K * y ^ 4 * C2 * Γ * (u ^ 2 * ((u / 2) ^ 3)⁻¹ + R2 * (u ^ 2 * ε)) := by
    ring
  rw [e1, e2]
  have s1 : 2 * K * y ^ 3 * (u ^ 2 * cuspFarA (u / 2) κ₃ + A2 * (u ^ 2 * ε)) ≤
      2 * K * y ^ 3 * ((4 + 24 * κ₃ + 48 * κ₃ ^ 2) + A2 * (u ^ 2 * ε)) := by gcongr
  have s2 : K * y ^ 4 * C2 * Γ * (u ^ 2 * ((u / 2) ^ 3)⁻¹ + R2 * (u ^ 2 * ε)) ≤
      K * y ^ 3 * C2 * Γ * (8 + R2 * (u ^ 2 * ε)) := by
    have hKC : 0 ≤ K * C2 * Γ := by positivity
    have : K * y ^ 4 * C2 * Γ = y ^ 4 * (K * C2 * Γ) := by ring
    have : K * y ^ 3 * C2 * Γ = y ^ 3 * (K * C2 * Γ) := by ring
    calc K * y ^ 4 * C2 * Γ * (u ^ 2 * ((u / 2) ^ 3)⁻¹ + R2 * (u ^ 2 * ε))
        ≤ K * y ^ 4 * C2 * Γ * (8 + R2 * (u ^ 2 * ε)) := by gcongr
      _ ≤ K * y ^ 3 * C2 * Γ * (8 + R2 * (u ^ 2 * ε)) := by
        have h8 : 0 ≤ 8 + R2 * (u ^ 2 * ε) := by positivity
        have := mul_le_mul_of_nonneg_right hy4 (mul_nonneg hKC h8)
        nlinarith [this]
  nlinarith [s1, s2]

/-- The dominating function is interval integrable and its integral is bounded. -/
lemma far_psi_int {T P C2 R y β η : ℝ} (hT : 0 ≤ T) (hP : 0 ≤ P) (hC2 : 0 ≤ C2) (hR : 0 ≤ R) (hy : 0 < y)
    (hyβ : y ^ 2 ≤ β) (hη : 0 < η) :
    IntervalIntegrable (fun x : ℝ => T * (P * x ^ (-(3 : ℝ) / 2) +
      C2 * R * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x)))) volume (y ^ 2) β ∧
    ∫ x in y ^ 2..β, T * (P * x ^ (-(3 : ℝ) / 2) + C2 * R * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x))) ≤
      T * P * (2 * y⁻¹) + T * C2 * R * cuspGamB η := by
  have hα : 0 < y ^ 2 := by positivity
  have hnot0 : (0 : ℝ) ∉ uIcc (y ^ 2) β := by
    rw [uIcc_of_le hyβ]; intro hm; exact absurd hm.1 (not_le.2 hα)
  have Ii1 : IntervalIntegrable (fun x : ℝ => x ^ (-(3 : ℝ) / 2)) volume (y ^ 2) β :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hnot0)
  have Ii2 : IntervalIntegrable (fun x : ℝ => x ^ ((1 : ℝ) / 2)) volume (y ^ 2) β :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hEc : Continuous fun x : ℝ => Real.exp (-(η / 4) * x) := by fun_prop
  have Ii3 : IntervalIntegrable (fun x : ℝ => x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x)) volume (y ^ 2) β :=
    Ii2.mul_continuousOn hEc.continuousOn
  have hfun : (fun x : ℝ => T * (P * x ^ (-(3 : ℝ) / 2) +
      C2 * R * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x)))) =
      fun x => (T * P) * x ^ (-(3 : ℝ) / 2) + (T * C2 * R) * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x)) := by
    funext x; ring
  rw [hfun]
  refine ⟨(Ii1.const_mul _).add (Ii3.const_mul _), ?_⟩
  rw [intervalIntegral.integral_add (Ii1.const_mul _) (Ii3.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have h1 := integral_rpow_neg_three_half_le hα hyβ
  have h2 := integral_sqrt_exp_le hη hα hyβ
  rw [Real.sqrt_sq hy.le] at h1
  have := mul_le_mul_of_nonneg_left h1 (mul_nonneg hT hP)
  have := mul_le_mul_of_nonneg_left h2 (mul_nonneg (mul_nonneg hT hC2) hR)
  nlinarith

/-- The constants of the low piece: `D₀ = 6 + 8κ₃ + 2(4+24κ₃+48κ₃²) + 8 C₂ Γ'`, `D₁ = 2 A(g_m) + C₂ Γ' g_m^{-3}`. -/
noncomputable def cuspFarD0 (η κ₃ C2 : ℝ) : ℝ := 6 + 8 * κ₃ + 2 * (4 + 24 * κ₃ + 48 * κ₃ ^ 2) + 8 * C2 * cuspGamB η

noncomputable def cuspFarD1 (η κ₃ C2 gm : ℝ) : ℝ := 2 * cuspFarA gm κ₃ + C2 * cuspGamB η * (gm ^ 3)⁻¹

/-- **The low piece** `[y², t₀/2]`, `y² c u = 1`, for `u ≥ 1`, `c ≥ 1`:
`‖∫_{y²}^{t₀/2} e^{icφ} a‖ ≤ K y³ (D₀ + D₁ u² e^{-ηγ/4}) + (K/c) D₂ e^{-ηt₀/8}`, where `γ ≤ min(t_*, t₀/2)`,
`y² ≤ γ`, `𝔪 t_* = u/2`. -/
lemma cuspFar_low (h : CuspPhase 𝔪 κ₁ κ₂ C₂ C₀) (ha : CuspAmpPos η Ca M a) (hη : 0 < η) (hCa : 0 ≤ Ca)
    (hM : 0 ≤ M) {c u t₀ ts γ y : ℝ} (hc : 1 ≤ c) (hu : 1 ≤ u) (ht₀ : 0 < t₀) (hv : 𝔪 t₀ = u)
    (hts : 𝔪 ts = u / 2) (hγs : γ ≤ ts) (hγb : γ ≤ t₀ / 2) (hy : 0 < y) (hyγ : y ^ 2 ≤ γ)
    (hyc : y ^ 2 * (c * u) = 1) :
    ‖∫ x in y ^ 2..(t₀ / 2), Complex.exp (Complex.I * ((c * cuspPhase 𝔪 u x : ℝ) : ℂ)) * a x‖ ≤
      Ca * M * ampC η * y ^ 3 * (cuspFarD0 η (cuspK3 κ₂) C₂ + cuspFarD1 η (cuspK3 κ₂) C₂ (cuspGm κ₁ κ₂) *
        (u ^ 2 * Real.exp (-(η / 4) * γ))) +
      Ca * M * ampC η / c * (cuspFarD2 η (cuspK3 κ₂) (cuspGm κ₁ κ₂) * Real.exp (-(η / 8) * t₀)) := by
  have hκ3 := h.κ₃_pos
  have hgm := cuspGm_pos h
  have hgmh := cuspGm_le_half κ₁ κ₂
  have hC2 : 0 ≤ C₂ := (abs_nonneg _).trans (h.deriv2_bound 0)
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  have hu0 : 0 < u := by linarith
  have hK0 := cuspK_nonneg hη hCa hM
  have hγ0 : 0 ≤ γ := (sq_nonneg y).trans hyγ
  set K : ℝ := Ca * M * ampC η with hK
  set κ₃ : ℝ := cuspK3 κ₂ with hκ₃
  set gm : ℝ := cuspGm κ₁ κ₂ with hgmdef
  have hy1 : y ≤ 1 := by
    have : y ^ 2 ≤ 1 := by nlinarith [mul_le_mul hc hu zero_le_one hc0.le]
    nlinarith
  have hαβ : y ^ 2 ≤ t₀ / 2 := hyγ.trans hγb
  have hα : 0 < y ^ 2 := by positivity
  have hgmu : gm ≤ u / 2 := by linarith
  have hβ : 0 < t₀ / 2 := by positivity
  have hβ2 : 1 ≤ 2 * κ₃ * (t₀ / 2) ^ 2 := by
    have := h.two_le_sq ht₀ hv hu
    nlinarith
  have hΓ := cuspGamB_nonneg η
  -- the amplitude and phase hypotheses
  have hP1 : ∀ x ∈ Icc (y ^ 2) (t₀ / 2), 0 < c * (if x ≤ γ then u / 2 else gm) ∧
      c * (if x ≤ γ then u / 2 else gm) ≤ c * |u - 𝔪 x| := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    by_cases hxγ : x ≤ γ
    · simp only [hxγ, ↓reduceIte]
      refine ⟨by positivity, mul_le_mul_of_nonneg_left ?_ hc0.le⟩
      have h1 : 𝔪 x ≤ 𝔪 ts := h.mono hx0.le (hxγ.trans hγs)
      rw [abs_of_pos (by linarith)]
      linarith
    · simp only [hxγ, ↓reduceIte]
      refine ⟨by positivity, mul_le_mul_of_nonneg_left ?_ hc0.le⟩
      have h1 := h.far_half_gap ht₀ hv hu hx0.le hx.2
      have h2 := cuspGm_le_G2 κ₁ κ₂
      rw [abs_of_pos (by linarith [cuspG2_pos h])]
      linarith
  have hP2 : ∀ x ∈ Icc (y ^ 2) (t₀ / 2), c * deriv 𝔪 x ≤ c * κ₃ / x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have h1 := h.deriv_le_w hx0
    unfold cuspW at h1
    have h2 : x / (1 + x ^ 2) ≤ 1 / x := by
      rw [div_le_div_iff₀ (by positivity) hx0]; nlinarith
    have h3 : deriv 𝔪 x ≤ κ₃ * (1 / x) := h1.trans (mul_le_mul_of_nonneg_left h2 hκ3.le)
    calc c * deriv 𝔪 x ≤ c * (κ₃ * (1 / x)) := mul_le_mul_of_nonneg_left h3 hc0.le
      _ = c * κ₃ / x := by ring
  have hpsi := far_psi_int (T := K * (c ^ 2)⁻¹) (P := cuspFarA (u / 2) κ₃ + cuspFarA gm κ₃ * Real.exp (-(η / 4) * γ))
    (C2 := C₂) (R := ((u / 2) ^ 3)⁻¹ + (gm ^ 3)⁻¹ * Real.exp (-(η / 4) * γ)) (η := η) (y := y) (β := t₀ / 2)
    (by positivity) (by have := cuspFarA_nonneg (show 0 < u / 2 by positivity) hκ3.le
                        have := cuspFarA_nonneg hgm hκ3.le
                        positivity) hC2 (by positivity) hy hαβ hη
  have hib := cusp_ibp_two_psi h ha hc0 hα hαβ (u := u)
    (B0 := fun x => K * (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (B1 := fun x => K * (x ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (B2 := fun x => K * (x ^ (-(3 : ℝ) / 2) * Real.exp (-(η / 2) * x)))
    (P1 := fun x => c * (if x ≤ γ then u / 2 else gm)) (P2 := fun x => c * κ₃ / x) (P3 := fun _ => c * C₂)
    (Ψ := fun x : ℝ => K * (c ^ 2)⁻¹ * ((cuspFarA (u / 2) κ₃ + cuspFarA gm κ₃ * Real.exp (-(η / 4) * γ)) *
        x ^ (-(3 : ℝ) / 2) + C₂ * (((u / 2) ^ 3)⁻¹ + (gm ^ 3)⁻¹ * Real.exp (-(η / 4) * γ)) *
          (x ^ ((1 : ℝ) / 2) * Real.exp (-(η / 4) * x))))
    (fun x hx => ha.amp0 hη hCa hM (lt_of_lt_of_le hα hx.1))
    (fun x hx => ha.amp1 hη hCa hM (lt_of_lt_of_le hα hx.1))
    (fun x hx => ha.amp2 hη hCa hM (lt_of_lt_of_le hα hx.1)) hP1 hP2 (fun x _ => le_rfl)
    (fun x hx => far_pt_le hK0 hc0 hκ3.le hC2 hu0 hgm hη (lt_of_lt_of_le hα hx.1))
    (by simpa [mul_assoc] using hpsi.1)
  refine hib.trans ?_
  -- endpoint at `t₀/2`
  have hbeta : ibpEnd (K * ((t₀ / 2) ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * (t₀ / 2))))
      (K * ((t₀ / 2) ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * (t₀ / 2))))
      (c * (if t₀ / 2 ≤ γ then u / 2 else gm)) (c * κ₃ / (t₀ / 2)) ≤
      K / c * (cuspFarD2 η κ₃ gm * Real.exp (-(η / 4) * (t₀ / 2))) := by
    refine far_beta_end hK0 hc hgm hκ3.le hβ hβ2 hη ?_
    by_cases hb : t₀ / 2 ≤ γ
    · simp only [hb, ↓reduceIte]; nlinarith
    · simp only [hb, ↓reduceIte]; exact le_rfl
  have halpha : ibpEnd (K * ((y ^ 2) ^ ((1 : ℝ) / 2) * Real.exp (-(η / 2) * y ^ 2)))
      (K * ((y ^ 2) ^ (-(1 : ℝ) / 2) * Real.exp (-(η / 2) * y ^ 2)))
      (c * (if y ^ 2 ≤ γ then u / 2 else gm)) (c * κ₃ / y ^ 2) ≤ K * y ^ 3 * (6 + 8 * κ₃) := by
    simp only [hyγ, ↓reduceIte]
    exact far_alpha_end hK0 hy hu hyc hκ3.le hη
  have hint := hpsi.2
  have halg := far_psi_alg (K := K) (y := y) (u := u) (c := c) (κ₃ := κ₃) (C2 := C₂)
    (ε := Real.exp (-(η / 4) * γ)) (Γ := cuspGamB η) (A2 := cuspFarA gm κ₃) (R2 := (gm ^ 3)⁻¹) hK0 hy hy1 hu hyc
    hκ3.le hC2 (Real.exp_pos _).le hΓ (by positivity)
  have hexp : Real.exp (-(η / 4) * (t₀ / 2)) = Real.exp (-(η / 8) * t₀) := by congr 1; ring
  rw [hexp] at hbeta
  unfold cuspFarD0 cuspFarD1
  linarith [hbeta, halpha, hint, halg]

end Low

end FormalResearch.SignUncertainty.FctUnscaledCusp

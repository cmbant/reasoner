/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctChart

/-!
# The abstract phase-perturbation data and the chart (F2a, `fct:comp-cfu`, Steps 1-3)

`CfuTheta` is the hypothesis structure whose fields are the bounds that `fct:comp-D` will provide (the rescaled `Θ_X`, and the
smooth remainders `m̃`, `θ̃`, all `C^18` with bounds `M`).  `CfuTheta.r` is the resulting phase perturbation on the parameter
box `OmT t` of `(ℓ, λ, α)`, `cfuR_jc` its `C^18` bound `C₀ t²` (`t = c^{-1/4}`), and `cfu_chart` the chart of `cfu_chart_core`
with all `C^16` bounds `≤ C t² = C c^{-1/2}`.

Class: proved under the explicit hypothesis `CfuTheta` (satisfiable: all-zero instance; the genuine instance needs `fct:comp-D`
and the Whitney extension, not yet formalised).
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace FormalResearch.SignUncertainty

section Theta

/-- Hypothesis structure for the phase perturbation of `fct:comp-cfu`.  The five functions `Θ_X`
(`X ∈ {0b, 0m, 1b, 1m, α}`, `fct:Theta-split`) are the rescaled, flattened `ϑ`-components supplied by `fct:comp-D`
(`ϑ̂_X(x) = σ_X⁻¹ ϑ_X(τ₁ x)`, `Θ_X(z) = ϑ̂_X(√z)/z^{11/2}`, with `‖Θ_X‖_{C^k([0,5])} ≤ C_k` from `(fct:thhat)`), extended
(Whitney) to `(-1, 6)`; `m̃`, `θ̃` are the smooth remainders of the phase (`P_λ(x;ℓ) = ℓ x - π²/36 x³ + τ₁² x⁵ m̃(τ₁² x²) -
c⁻¹ x³ θ̃(τ₁² x²) + λ ε_D x^{11} Θ(x²)`).  All are `C^18` on `(-1, 6)` with all derivatives of order `≤ 18` bounded by `M`
(independent of `c` and `K₄`).

Satisfiability: the structure is satisfiable (all functions zero), and the genuine instance needs `fct:comp-D`
(`ϑ_X` with `C^{47}` bounds `(fct:th-inner)`, `(fct:th1-inner)`) and the Whitney extension of the `Θ_X` from `[0,5]` to `(-1, 6)`;
neither is formalised yet, so the bounds `M` here are hypotheses, not consequences. -/
structure CfuTheta where
  mt : ℝ → ℝ
  θt : ℝ → ℝ
  Θ0b : ℝ → ℝ
  Θ0m : ℝ → ℝ
  Θ1b : ℝ → ℝ
  Θ1m : ℝ → ℝ
  Θα : ℝ → ℝ
  M : ℝ
  hM : 0 ≤ M
  jc_mt : JC 18 (Ioo (-1 : ℝ) 6) mt M
  jc_θt : JC 18 (Ioo (-1 : ℝ) 6) θt M
  jc_Θ0b : JC 18 (Ioo (-1 : ℝ) 6) Θ0b M
  jc_Θ0m : JC 18 (Ioo (-1 : ℝ) 6) Θ0m M
  jc_Θ1b : JC 18 (Ioo (-1 : ℝ) 6) Θ1b M
  jc_Θ1m : JC 18 (Ioo (-1 : ℝ) 6) Θ1m M
  jc_Θα : JC 18 (Ioo (-1 : ℝ) 6) Θα M

/-- `Θ(z; α) = Θ_{0b} + K₄ τ₁² Θ_{0m} + c⁻¹ τ₁⁻³ Θ_{1b} + K₄ c⁻¹ τ₁⁻¹ Θ_{1m} + α Θ_α`, written in `t = τ₁ = c^{-1/4}`
(`c⁻¹ = t⁴`). -/
noncomputable def CfuTheta.Th (T : CfuTheta) (t K4 α z : ℝ) : ℝ :=
  T.Θ0b z + K4 * t ^ 2 * T.Θ0m z + t * T.Θ1b z + K4 * t ^ 3 * T.Θ1m z + α * T.Θα z

/-- The perturbation `r(ℓ,λ,α; z) = τ₁² z² m̃(τ₁² z) - c⁻¹ z θ̃(τ₁² z) + λ ε_D z⁵ Θ(z; α)` of the scaled phase
(`ε_D = c⁻¹τ₁⁻¹ = t³`, `c⁻¹ = t⁴`, `τ₁² = t²`). -/
noncomputable def CfuTheta.r (T : CfuTheta) (t K4 : ℝ) (q : (ℝ × ℝ × ℝ) × ℝ) : ℝ :=
  t ^ 2 * (q.2 ^ 2 * T.mt (t ^ 2 * q.2)) - t ^ 4 * (q.2 * T.θt (t ^ 2 * q.2)) +
    q.1.2.1 * (t ^ 3 * (q.2 ^ 5 * T.Th t K4 q.1.2.2 q.2))

/-- The parameter box `(ℓ, λ, α) ∈ (-1/10, 27/10) × (-1/10, 11/10) × (-2t², 2t²)` (open neighbourhood of the paper's
`[0, 2.6] × [0, 1] × [-c^{-1/2}, c^{-1/2}]`, `t² = c^{-1/2}`). -/
noncomputable def OmT (t : ℝ) : Set (ℝ × ℝ × ℝ) :=
  Ioo (-(1 / 10) : ℝ) (27 / 10) ×ˢ (Ioo (-(1 / 10) : ℝ) (11 / 10) ×ˢ Ioo (-(2 * t ^ 2) : ℝ) (2 * t ^ 2))

lemma OmT_open (t : ℝ) : IsOpen (OmT t) := isOpen_Ioo.prod (isOpen_Ioo.prod isOpen_Ioo)

lemma norm_le_one_of_norm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (L : X →L[ℝ] ℝ)
    (h : ∀ x, ‖L x‖ ≤ ‖x‖) : ‖L‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simpa using h x

/-- The coordinates `λ, α` of a point `((ℓ,λ,α), z)`. -/
noncomputable def coordLam : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) ℝ))

noncomputable def coordAlp : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
    (ContinuousLinearMap.fst ℝ (ℝ × ℝ × ℝ) ℝ))

lemma coordLam_apply (q : (ℝ × ℝ × ℝ) × ℝ) : coordLam q = q.1.2.1 := rfl
lemma coordAlp_apply (q : (ℝ × ℝ × ℝ) × ℝ) : coordAlp q = q.1.2.2 := rfl

lemma coordLam_norm : ‖coordLam‖ ≤ 1 :=
  norm_le_one_of_norm_le _ fun q => by
    rw [coordLam_apply]
    exact (norm_fst_le _).trans ((norm_snd_le _).trans (by simpa using norm_fst_le q))

lemma coordAlp_norm : ‖coordAlp‖ ≤ 1 :=
  norm_le_one_of_norm_le _ fun q => by
    rw [coordAlp_apply]
    exact (norm_snd_le _).trans ((norm_snd_le _).trans (by simpa using norm_fst_le q))

lemma cfuR_jc (M : ℝ) (hM : 0 ≤ M) : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (T : CfuTheta), T.M = M → ∀ {t K4 : ℝ}, 0 < t → t ≤ 1 →
    0 ≤ K4 → K4 * t ^ 2 ≤ 1 → JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (T.r t K4) (C0 * t ^ 2) := by
  set bm : ℝ := (Nat.factorial 18 : ℝ) * M with hbm
  set b1 : ℝ := 2 ^ 18 * 6 * 6 with hb1
  set b1m : ℝ := 2 ^ 18 * b1 * bm with hb1m
  set b2 : ℝ := 2 ^ 18 * 6 * bm with hb2
  set b4 : ℝ := 2 ^ 18 * b1 * b1 with hb4
  set b5 : ℝ := 2 ^ 18 * b4 * 6 with hb5
  set bΘ : ℝ := bm + bm + bm + bm + 2 ^ 18 * 2 * bm with hbΘ
  refine ⟨b1m + b2 + 2 ^ 18 * 2 * (2 ^ 18 * b5 * bΘ), by positivity, ?_⟩
  intro T hTM t K4 ht0 ht1 hK0 hK
  subst hTM
  have hbm0 : 0 ≤ bm := by positivity
  have hU : IsOpen (OmT t ×ˢ Ioo (-1 : ℝ) 6) := (OmT_open t).prod isOpen_Ioo
  have hUd : UniqueDiffOn ℝ (OmT t ×ˢ Ioo (-1 : ℝ) 6) := hU.uniqueDiffOn
  have hI : UniqueDiffOn ℝ (Ioo (-1 : ℝ) 6) := isOpen_Ioo.uniqueDiffOn
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have ht2p : 0 < t ^ 2 := by positivity
  have ht3 : t ^ 3 ≤ t ^ 2 := by nlinarith
  have ht4 : t ^ 4 ≤ t ^ 2 := by nlinarith
  have hz : JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (fun q : (ℝ × ℝ × ℝ) × ℝ => q.2) 6 :=
    JC.snd hUd (by norm_num) fun q hq => by
      have := hq.2
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
  have hzz := JC.mul hUd (by norm_num) (by norm_num) hz hz
  -- the scaling `z ↦ t² z`
  set L2 : ((ℝ × ℝ × ℝ) × ℝ) →L[ℝ] ℝ := (t ^ 2) • ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) ℝ with hL2
  have hL2n : ‖L2‖ ≤ 1 := by
    refine norm_le_one_of_norm_le _ fun x => ?_
    simp only [hL2, smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul, norm_mul,
      Real.norm_eq_abs]
    rw [abs_of_pos ht2p]
    calc t ^ 2 * |x.2| ≤ 1 * ‖x‖ := by
          gcongr
          exact (by simpa [Real.norm_eq_abs] using norm_snd_le x)
      _ = ‖x‖ := one_mul _
  have hst2 : MapsTo L2 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (Ioo (-1 : ℝ) 6) := by
    intro x hx
    have h := hx.2
    simp only [hL2, smul_apply, ContinuousLinearMap.coe_snd', smul_eq_mul]
    constructor <;> nlinarith [h.1, h.2]
  have hst1 : MapsTo (ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) ℝ) (OmT t ×ˢ Ioo (-1 : ℝ) 6) (Ioo (-1 : ℝ) 6) :=
    fun x hx => hx.2
  have hn1 : ‖ContinuousLinearMap.snd ℝ (ℝ × ℝ × ℝ) ℝ‖ ≤ 1 := norm_snd_le_one _ _
  have hmt : JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (fun q => T.mt (t ^ 2 * q.2)) bm := by
    have := JC.comp_clm hUd hI L2 hL2n T.hM T.jc_mt hst2
    exact this.congr fun x _ => by simp [hL2]
  have hθ : JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (fun q => T.θt (t ^ 2 * q.2)) bm := by
    have := JC.comp_clm hUd hI L2 hL2n T.hM T.jc_θt hst2
    exact this.congr fun x _ => by simp [hL2]
  have hΘ : ∀ {Θ : ℝ → ℝ}, JC 18 (Ioo (-1 : ℝ) 6) Θ T.M →
      JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (fun q => Θ q.2) bm := by
    intro Θ hΘ
    have := JC.comp_clm hUd hI _ hn1 T.hM hΘ hst1
    exact this.congr fun x _ => by simp
  have hlam : JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.1) 2 :=
    JC.clm hUd coordLam (coordLam_norm.trans (by norm_num)) fun x hx => by
      have := hx.1.2.1
      rw [coordLam_apply, Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have hal : JC 18 (OmT t ×ˢ Ioo (-1 : ℝ) 6) (fun q : (ℝ × ℝ × ℝ) × ℝ => q.1.2.2) 2 :=
    JC.clm hUd coordAlp (coordAlp_norm.trans (by norm_num)) fun x hx => by
      have := hx.1.2.2
      rw [coordAlp_apply, Real.norm_eq_abs, abs_le]; constructor <;> linarith [this.1, this.2]
  have hA0 := hΘ T.jc_Θ0b
  have hA1 := (hΘ T.jc_Θ0m).const_smul hUd (K4 * t ^ 2)
  have hA2 := (hΘ T.jc_Θ1b).const_smul hUd t
  have hA3 := (hΘ T.jc_Θ1m).const_smul hUd (K4 * t ^ 3)
  have hA4 := JC.mul hUd (by norm_num) hbm0 hal (hΘ T.jc_Θα)
  have hK3 : K4 * t ^ 3 ≤ 1 := by nlinarith
  have hA1' := hA1.mono (b' := bm) (by
    rw [abs_of_nonneg (by positivity)]; exact mul_le_of_le_one_left hbm0 hK)
  have hA2' := hA2.mono (b' := bm) (by
    rw [abs_of_pos ht0]; exact mul_le_of_le_one_left hbm0 ht1)
  have hA3' := hA3.mono (b' := bm) (by
    rw [abs_of_nonneg (by positivity)]; exact mul_le_of_le_one_left hbm0 hK3)
  have hTh := (((hA0.add hUd hA1').add hUd hA2').add hUd hA3').add hUd hA4
  have hz2 := hzz
  have hz4 := JC.mul hUd (by positivity) (by positivity) hz2 hz2
  have hz5 := JC.mul hUd (by positivity) (by norm_num) hz4 hz
  have hzΘ := JC.mul hUd (by positivity) (by positivity) hz5 hTh
  have ht3c := hzΘ.const_smul hUd (t ^ 3)
  have hl3 := JC.mul hUd (by norm_num) (by positivity) hlam ht3c
  have hm1 := JC.mul hUd (by positivity) hbm0 hzz hmt
  have hm1c := hm1.const_smul hUd (t ^ 2)
  have hθ1 := JC.mul hUd (by norm_num) hbm0 hz hθ
  have hθ1c := hθ1.const_smul hUd (t ^ 4)
  have hfin := (hm1c.sub hUd hθ1c).add hUd hl3
  refine (hfin.congr fun q _ => ?_).mono ?_
  · simp only [CfuTheta.r, CfuTheta.Th, smul_eq_mul]
    ring
  · rw [abs_of_pos ht2p, abs_of_pos (by positivity : 0 < t ^ 4), abs_of_pos (by positivity : 0 < t ^ 3)]
    have e1 : t ^ 2 * b1m ≤ b1m * t ^ 2 := by nlinarith
    have hb2' : 0 ≤ b2 := by positivity
    have hq : 0 ≤ 2 ^ 18 * 2 * (2 ^ 18 * b5 * bΘ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ht4 hb2', mul_le_mul_of_nonneg_left ht3 hq]

/-- The conclusions of `cfu_chart_core` for given objects. -/
def ChartOut {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (cB cd cR cD cZ cV : ℝ) (Ω : Set P)
    (r : P × ℝ → ℝ) (ℓ : P → ℝ) (ε : ℝ) (B d : P → ℝ) (R Z : P × ℝ → ℝ) : Prop :=
  JC 16 Ω (fun p => B p - 12 / Real.pi ^ 2 * ℓ p) (cB * ε) ∧
  (∀ p ∈ Ω, B p ∈ Ioo (-1 : ℝ) 6 ∧ Real.pi ^ 2 / 12 * B p - ℓ p - rhoF r (p, B p) = 0) ∧
  JC 16 Ω (fun p => d p - dStar) (cd * ε) ∧
  (∀ p ∈ Ω, 0 < d p ∧ d p ^ 3 = Real.pi ^ 2 / 12 - 3 * fderiv ℝ r (p, B p) (0, 1)) ∧
  JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) R (cR * ε) ∧
  (∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, |R q| < 1 / 50 ∧
    hadH r B q + R q * (d q.1 ^ 2 + d q.1 * q.2 * R q + 1 / 3 * q.2 * (q.2 - B q.1) * R q ^ 2) = 0) ∧
  JC 16 (Ω ×ˢ Ioo (-1 : ℝ) 6) (fun q => Dfun B d R q - dStar) (cD * ε) ∧
  JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => Z y - (dStar ^ 2)⁻¹ * y.2) (cZ * ε) ∧
  (∀ y ∈ Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10), Z y ∈ Ioo (-1 : ℝ) 6 ∧
    Z y * Dfun B d R (y.1, Z y) ^ 2 = y.2) ∧
  JC 16 (Ω ×ˢ Ioo (-(1 / 5) : ℝ) (36 / 10)) (fun y => (Dfun B d R (y.1, Z y))⁻¹ - dStar⁻¹) (cV * ε) ∧
  (∀ q ∈ Ω ×ˢ Ioo (-1 : ℝ) 6, ℓ q.1 - Real.pi ^ 2 / 36 * q.2 + r q =
    d q.1 ^ 2 * B q.1 * Dfun B d R q - q.2 * Dfun B d R q ^ 3 / 3)

/-- **The scalar cubic chart of `fct:comp-cfu`** (Steps 2-3), for the phase perturbation `r = T.r t K₄` built from the abstract
`C^18` data `T : CfuTheta` (`t = τ₁ = c^{-1/4}`, `K₄ t² ≤ 1` is `c ≥ K₄²`), on the parameter box `OmT t` of `(ℓ, λ, α)`, for `t` small
enough (`c ≥ c₀`, independent of `K₄`): the objects of `cfu_chart_core` exist with `C^16` jet bounds `≤ C t² = C c^{-1/2}`; in
particular `‖V - τ_*‖_{16} ≤ C c^{-1/2}`. -/
theorem cfu_chart (M : ℝ) (hM : 0 ≤ M) : ∃ (C0 cB cd cR cD cZ cV t0 : ℝ), 0 ≤ C0 ∧ 0 ≤ cB ∧ 0 ≤ cd ∧ 0 ≤ cR ∧ 0 ≤ cD ∧
    0 ≤ cZ ∧ 0 ≤ cV ∧ 0 < t0 ∧ ∀ (T : CfuTheta), T.M = M → ∀ {t K4 : ℝ}, 0 < t → t ≤ t0 → 0 ≤ K4 → K4 * t ^ 2 ≤ 1 →
    ∃ (B d : ℝ × ℝ × ℝ → ℝ) (R Z : (ℝ × ℝ × ℝ) × ℝ → ℝ),
      ChartOut cB cd cR cD cZ cV (OmT t) (T.r t K4) (fun p => p.1) (C0 * t ^ 2) B d R Z := by
  obtain ⟨C0, hC0, hr⟩ := cfuR_jc M hM
  obtain ⟨cB, cd, cR, cD, cZ, cV, hcB, hcd, hcR, hcD, hcZ, hcV, ε0, hε0, hcore⟩ := cfu_chart_core (P := ℝ × ℝ × ℝ)
  refine ⟨C0, cB, cd, cR, cD, cZ, cV, min 1 (Real.sqrt (ε0 / (C0 + 1))), hC0, hcB, hcd, hcR, hcD, hcZ, hcV,
    lt_min one_pos (Real.sqrt_pos.mpr (by positivity)), ?_⟩
  intro T hTM t K4 ht0 ht1 hK0 hK
  have ht1' : t ≤ 1 := ht1.trans (min_le_left _ _)
  have ht2 : t ≤ Real.sqrt (ε0 / (C0 + 1)) := ht1.trans (min_le_right _ _)
  have hεt : C0 * t ^ 2 ≤ ε0 := by
    have h1 : t ^ 2 ≤ ε0 / (C0 + 1) := by
      calc t ^ 2 ≤ Real.sqrt (ε0 / (C0 + 1)) ^ 2 := by gcongr
        _ = ε0 / (C0 + 1) := Real.sq_sqrt (by positivity)
    calc C0 * t ^ 2 ≤ (C0 + 1) * (ε0 / (C0 + 1)) := by
          gcongr
          linarith
      _ = ε0 := by field_simp
  have hℓ : JC 16 (OmT t) (fun p : ℝ × ℝ × ℝ => p.1) 3 :=
    JC.clm (OmT_open t).uniqueDiffOn (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ))
      ((norm_fst_le_one _ _).trans (by norm_num)) fun p hp => by
        have := hp.1
        simp only [ContinuousLinearMap.coe_fst', Real.norm_eq_abs, abs_le]
        constructor <;> linarith [this.1, this.2]
  exact hcore (OmT_open t) (by positivity) hεt (hr T hTM ht0 ht1' hK0 hK) hℓ
    (fun p hp => ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩)

end Theta

/-- info: 'FormalResearch.SignUncertainty.cfuR_jc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cfuR_jc

/-- info: 'FormalResearch.SignUncertainty.cfu_chart' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cfu_chart

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.MellinLiftTail

/-!
# `uct:admiss`, the lift of a general strip multiplier

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`, Lemma T.7 (`mat:T7`) (a), (b) and the definition `(mat:lift)` / `(uct:mellin-inv-gen)`:
for a multiplier `W̃` on the closed strip `0 ≤ Re ζ ≤ 1` and `c ≥ 2` the lift is
`f_W(Δ) = (2πi)⁻¹ ∫_{Re z = x₀} (2π)^{-z} Γ(z) e^{cℋ(1-z/c)} W̃(1 - z/c) Δ^{-z} dz`.

* `StripM1`: hypotheses (M1) (holomorphic, continuous, real-symmetric, decay `(1+|τ|)^{-2}`);
* `admissPhi`: the multiplier `Φ_W(z) = G(z) W̃(1 - z/c)`, `G(z) = (2π)^{-z} Γ(z) e^{cℋ(1-z/c)}`;
* `admissG_norm_le_*`: `G` is bounded on `|Im z| ≥ 1` (right half by `K₀`, left half by the reflection `ℋ(1-ζ) = ℋ(ζ)` and the Gamma ratio);
* `admissPhi_mellinLiftData`: `Φ_W` satisfies the hypotheses of the Mellin hub (`MellinLiftData`), hence `f_W` is independent of the line,
  real and continuous on `(0, ∞)`;
* `admiss_vert_rep`: the vertical representation `(f_W ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ + iτ, ξ) W̃(σ + iτ) dτ`, `0 ≤ σ < 1` (`mat:T7`(b)).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- `G(z) = (2π)^{-z} Γ(z) e^{cℋ(1 - z/c)}`, the symbol-free factor of the lift `(mat:lift)`. -/
noncomputable def admissG (c : ℝ) (z : ℂ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c))

/-- The Mellin multiplier `Φ_W(z) = G(z) W̃(1 - z/c)` of the lift of a strip multiplier `W̃`. -/
noncomputable def admissPhi (c : ℝ) (W : ℂ → ℂ) (z : ℂ) : ℂ := admissG c z * W (1 - z / c)

/-- The lift `f_W` of `(uct:mellin-inv-gen)` on `(0, ∞)`, along the line `Re z = c/2` (the line is irrelevant, see
`admissPhi_mellinLiftData` and `MellinLiftData.mellinInv_indep`). -/
noncomputable def admissLift (c : ℝ) (W : ℂ → ℂ) : ℝ → ℝ := liftFun (admissPhi c W) (c / 2)

/-- The lift with its origin value `f_W(0) = W̃(1)`. -/
noncomputable def admissF (c : ℝ) (W : ℂ → ℂ) (Δ : ℝ) : ℝ :=
  if Δ = 0 then (W 1).re else admissLift c W Δ

/-- Hypothesis (W1) of `mat:T7` (Lemma T.7) on `W : ℂ → ℂ` (only its values on `0 ≤ Re ζ ≤ 1` matter),
with decay exponent `1/2 + η` (`η > 0`). -/
structure StripW1 (η : ℝ) (W : ℂ → ℂ) : Prop where
  hol : DifferentiableOn ℂ W {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1}
  cont : ContinuousOn W {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}
  real : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W (starRingEnd ℂ ζ) = starRingEnd ℂ (W ζ)
  bound : ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖W ζ‖ ≤ C * (1 + |ζ.im|) ^ (-(1 / 2 + η))

/-- Hypothesis (M1) of `uct:admiss` on `W̃ : ℂ → ℂ` (only its values on `0 ≤ Re ζ ≤ 1` matter). -/
structure StripM1 (W : ℂ → ℂ) : Prop where
  hol : DifferentiableOn ℂ W {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1}
  cont : ContinuousOn W {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}
  real : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W (starRingEnd ℂ ζ) = starRingEnd ℂ (W ζ)
  bound : ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖W ζ‖ ≤ C * (1 + |ζ.im|) ^ (-(2 : ℝ))

lemma StripM1.toStripW1 {W : ℂ → ℂ} (hW : StripM1 W) : StripW1 (3 / 2) W where
  hol := hW.hol
  cont := hW.cont
  real := hW.real
  bound := by
    obtain ⟨C, hC⟩ := hW.bound
    refine ⟨C, fun ζ h0 h1 => ?_⟩
    convert hC ζ h0 h1 using 2
    norm_num

/-- Reflection `ζ ↦ 1 - ζ` preserves `(W1)`. -/
lemma StripW1.reflect {η : ℝ} {W : ℂ → ℂ} (hW : StripW1 η W) :
    StripW1 η (fun ζ => W (1 - ζ)) where
  hol := hW.hol.comp ((differentiableOn_const 1).sub differentiableOn_id) fun ζ hζ =>
    ⟨by simp [hζ.2], by simp [hζ.1]⟩
  cont := hW.cont.comp (continuousOn_const.sub continuousOn_id) fun ζ hζ =>
    ⟨by simp [hζ.2], by simp [hζ.1]⟩
  real ζ h0 h1 := by
    have hconj : (1 : ℂ) - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) := by simp
    rw [hconj]
    exact hW.real (1 - ζ) (by simp [h1]) (by simp [h0])
  bound := by
    obtain ⟨C, hC⟩ := hW.bound
    refine ⟨C, fun ζ h0 h1 => ?_⟩
    have hb := hC (1 - ζ) (by simp [h1]) (by simp [h0])
    simpa [abs_neg] using hb

/-- Reflection `ζ ↦ 1 - ζ` preserves `(M1)`. -/
lemma StripM1.reflect {W : ℂ → ℂ} (hW : StripM1 W) :
    StripM1 (fun ζ => W (1 - ζ)) where
  hol := hW.hol.comp ((differentiableOn_const 1).sub differentiableOn_id) fun ζ hζ =>
    ⟨by simp [hζ.2], by simp [hζ.1]⟩
  cont := hW.cont.comp (continuousOn_const.sub continuousOn_id) fun ζ hζ =>
    ⟨by simp [hζ.2], by simp [hζ.1]⟩
  real ζ h0 h1 := by
    have hconj : (1 : ℂ) - starRingEnd ℂ ζ = starRingEnd ℂ (1 - ζ) := by simp
    rw [hconj]
    exact hW.real (1 - ζ) (by simp [h1]) (by simp [h0])
  bound := by
    obtain ⟨C, hC⟩ := hW.bound
    refine ⟨C, fun ζ h0 h1 => ?_⟩
    have hb := hC (1 - ζ) (by simp [h1]) (by simp [h0])
    simpa [abs_neg] using hb

section G

variable {c : ℝ}

theorem admissG_eq (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re ≤ c) :
    admissG c z = ((2 * Real.pi : ℝ) : ℂ) ^ (-z) *
      (Complex.Gamma (c : ℂ) * mellinK0 c (1 - z / c) (liftXi c)) := by
  unfold admissG
  rw [mul_assoc (((2 * Real.pi : ℝ) : ℂ) ^ (-z)), gamma_exp_stripH_eq hc hz0 hz1]

theorem admissG_differentiableOn (hc : 0 < c) :
    DifferentiableOn ℂ (admissG c) {z : ℂ | 0 < z.re ∧ z.re < c} := by
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hb : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : DifferentiableOn ℂ (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) {z : ℂ | 0 < z.re ∧ z.re < c} :=
    fun z _ => ((differentiableAt_id.neg).const_cpow (Or.inl hb)).differentiableWithinAt
  have h2 : DifferentiableOn ℂ (fun z : ℂ => mellinK0 c (1 - z / c) (liftXi c)) {z : ℂ | 0 < z.re ∧ z.re < c} := by
    refine (differentiableOn_mellinK0 hc (liftXi c)).comp
      (((differentiableOn_const _).sub (differentiableOn_id.div_const _))) fun z hz => ?_
    show |(1 - z / (c : ℂ)).re| < 1
    rw [re_one_sub_div hc]
    have h0 : 0 < z.re / c := by have := hz.1; positivity
    have h1' : z.re / c < 1 := (div_lt_one hc).mpr hz.2
    rw [abs_lt]; constructor <;> linarith
  refine (h1.mul (h2.const_mul (Complex.Gamma (c : ℂ)))).congr fun z hz => ?_
  exact admissG_eq hc hz.1 hz.2.le

theorem admissG_continuousOn_edge (hc : 0 < c) :
    ContinuousOn (admissG c) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  have hb : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    exact_mod_cast this.ne'
  have h1 : ContinuousOn (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) ^ (-z)) {z : ℂ | 0 < z.re ∧ z.re ≤ c} :=
    (Continuous.const_cpow continuous_neg (Or.inl hb)).continuousOn
  have h2 : ContinuousOn (fun z : ℂ => mellinK0 c (1 - z / c) (liftXi c)) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
    refine ((differentiableOn_mellinK0 hc (liftXi c)).continuousOn).comp
      ((continuousOn_const.sub (continuousOn_id.div_const _))) fun z hz => ?_
    show |(1 - z / (c : ℂ)).re| < 1
    rw [re_one_sub_div hc]
    have h0 : 0 < z.re / c := by have := hz.1; positivity
    have h1' : z.re / c ≤ 1 := (div_le_one hc).mpr hz.2
    rw [abs_lt]; constructor <;> linarith
  refine (h1.mul ((continuousOn_const (c := Complex.Gamma (c : ℂ))).mul h2)).congr fun z hz => ?_
  exact admissG_eq hc hz.1 hz.2

theorem admissG_conj (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c) :
    admissG c (starRingEnd ℂ z) = starRingEnd ℂ (admissG c z) := by
  have hcz0 : 0 < (starRingEnd ℂ z).re := by simpa using hz0
  have hcz1 : (starRingEnd ℂ z).re < c := by simpa using hz1
  rw [admissG_eq hc hcz0 hcz1.le, admissG_eq hc hz0 hz1.le]
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  simp only [map_mul]
  have e1 : ((2 * Real.pi : ℝ) : ℂ) ^ (-(starRingEnd ℂ z)) = starRingEnd ℂ (((2 * Real.pi : ℝ) : ℂ) ^ (-z)) := by
    have hargs : (((2 * Real.pi : ℝ) : ℂ)).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg hr.le]; exact Real.pi_ne_zero.symm
    have := Complex.cpow_conj (((2 * Real.pi : ℝ) : ℂ)) (-z) hargs
    rw [Complex.conj_ofReal] at this
    rw [show -(starRingEnd ℂ z) = starRingEnd ℂ (-z) by simp, this]
  have e2 : mellinK0 c (1 - starRingEnd ℂ z / c) (liftXi c) = starRingEnd ℂ (mellinK0 c (1 - z / c) (liftXi c)) := by
    have hb0 : 0 < (1 - z / (c : ℂ)).re := by
      rw [re_one_sub_div hc]; have := (div_lt_one hc).mpr hz1; linarith
    have hb1 : (1 - z / (c : ℂ)).re < 1 := by
      rw [re_one_sub_div hc]; have : 0 < z.re / c := by positivity
      linarith
    have := mellinK0_conj (c := c) (liftXi_pos hc) hb0 hb1
    rw [← this]
    congr 1
    simp [Complex.conj_ofReal]
  have e3 : Complex.Gamma (c : ℂ) = starRingEnd ℂ (Complex.Gamma (c : ℂ)) := by
    rw [← Complex.Gamma_conj, Complex.conj_ofReal]
  rw [e1, e2]
  conv_lhs => rw [e3]

lemma norm_one_sub_cpow_neg_half_le {s τ : ℝ} (hs : s ≤ 1 / 2) :
    ‖(1 - ((s : ℂ) + (τ : ℂ) * Complex.I)) ^ (-(1 / 2 : ℂ))‖ ≤ 2 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by
  set ζ : ℂ := (s : ℂ) + (τ : ℂ) * Complex.I with hζ
  have hre : (1 - ζ).re = 1 - s := by simp [hζ]
  have him : (1 - ζ).im = -τ := by simp [hζ]
  have h1ζ : (1 - ζ) ≠ 0 := fun h => by
    have := congrArg Complex.re h; rw [hre] at this; simp at this; linarith
  have hsq : (1 + |τ|) ^ 2 / 8 ≤ ‖1 - ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith [sq_abs τ, sq_nonneg (|τ| - 1), sq_nonneg (1 - s - 1 / 2)]
  have hnorm_ge : (1 + |τ|) / 4 ≤ ‖1 - ζ‖ := by
    have h1 : ((1 + |τ|) / 4) ^ 2 ≤ ‖1 - ζ‖ ^ 2 := by nlinarith [sq_nonneg (1 + |τ|)]
    nlinarith [norm_nonneg (1 - ζ), show (0 : ℝ) ≤ (1 + |τ|) / 4 by positivity]
  rw [Complex.norm_cpow_of_ne_zero h1ζ]
  simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.div_ofNat_im,
    Complex.one_im, neg_zero, zero_div, mul_zero, Real.exp_zero, div_one]
  calc ‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) ≤ ((1 + |τ|) / 4) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hnorm_ge (by norm_num)
    _ = 2 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
          div_inv_eq_mul, mul_comm]
        have h4 : (4 : ℝ) ^ (1 / 2 : ℝ) = 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        rw [h4]

/-- Decay of `K₀` on `Re ζ ∈ [0, 1/2]`: `‖K₀(s + iτ, ξ)‖ ≤ K (1 + |τ|)^{-1/2}` (`mat:Gbound`). -/
lemma norm_mellinK0_half_strip_decay {c ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s τ : ℝ, 0 ≤ s → s ≤ 1 / 2 →
      ‖mellinK0 c ((s : ℂ) + (τ : ℂ) * Complex.I) ξ‖ ≤ K * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by
  set L := Real.log (Real.pi ^ 2 * ξ) with hL
  set K : ℝ := 2 * Real.exp (1 / (4 * c)) * Real.exp (c * (1 / 18 + |L| / 2)) with hK
  have hK1 : 2 ≤ K := by
    have h1 : 1 ≤ Real.exp (1 / (4 * c)) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ Real.exp (c * (1 / 18 + |L| / 2)) := Real.one_le_exp (by positivity)
    rw [hK]; nlinarith
  refine ⟨K, by linarith, fun s τ hs0 hs2 => ?_⟩
  rcases hs0.eq_or_lt with rfl | hs
  · have h0 := (norm_mellinK0_imag_le hc hξ τ).2
    have e : ((0 : ℝ) : ℂ) + (τ : ℂ) * Complex.I = (τ : ℂ) * Complex.I := by simp
    rw [e]
    have hq : (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ 2 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := by
      have h1 : (1 + |τ|) ^ 2 * 2⁻¹ ≤ 1 + τ ^ 2 := by nlinarith [sq_abs τ, sq_nonneg (|τ| - 1)]
      have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num : -(1 / 4 : ℝ) ≤ 0)
      have h3 : ((1 + |τ|) ^ 2 * 2⁻¹) ^ (-(1 / 4 : ℝ)) = (1 + |τ|) ^ (-(1 / 2 : ℝ)) * 2 ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by positivity) (by norm_num), Real.inv_rpow (by norm_num),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num
      have h4 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
        calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := Real.rpow_one 2
      rw [h3] at h2
      calc (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) ≤ (1 + |τ|) ^ (-(1 / 2 : ℝ)) * 2 ^ (1 / 4 : ℝ) := h2
        _ ≤ (1 + |τ|) ^ (-(1 / 2 : ℝ)) * 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = 2 * (1 + |τ|) ^ (-(1 / 2 : ℝ)) := mul_comm _ _
    exact h0.trans (hq.trans (mul_le_mul_of_nonneg_right hK1 (by positivity)))
  · have hnonneg : ∀ t : ℝ, 0 ≤ t →
        ‖mellinK0 c ((s : ℂ) + (t : ℂ) * Complex.I) ξ‖ ≤ K * (1 + |t|) ^ (-(1 / 2 : ℝ)) := by
      intro t ht
      set ζ : ℂ := (s : ℂ) + (t : ℂ) * Complex.I with hζ
      have hre : ζ.re = s := by simp [hζ]
      have hs1 : s < 1 := by linarith
      have hpow := norm_one_sub_cpow_neg_half_le (s := s) (τ := t) hs2
      have hbin : ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ)‖ ≤ Real.exp (1 / (4 * c)) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
        have := FormalResearch.Asymptotics.binetDiff_norm_le hc (ζ := ζ) (by rw [hre]; exact hs1)
        refine this.trans ?_
        rw [hre]
        have h : 1 / (1 - s) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        calc 1 / (12 * c) * (1 / (1 - s) + 1) ≤ 1 / (12 * c) * (2 + 1) := by gcongr
          _ = 1 / (4 * c) := by field_simp; ring
      have hphi := mellinPhi_re_vertical (σ := s) (ξ := ξ) (τ := t) hs hs1 hξ
      have hφ0 := re_mellinPhi_real_le hs hs2 hξ
      have hU : 0 ≤ vertUpsilon s t := by
        rcases eq_or_lt_of_le ht with rfl | htpos
        · simp [vertUpsilon]
        · have hge := integral_im_stripG_ge hs hs2 htpos
          have hl := lobeU_nonneg t
          unfold lobeU at hl
          rw [abs_of_pos htpos] at hl
          have h0 : 0 ≤ 2 * (3 / 56 : ℝ) * s * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)) := by positivity
          have hv : 2 * (3 / 56 : ℝ) * s * ((1 / 2 : ℝ) * min (t ^ 2) 1 + max 0 (Real.log t)) ≤ vertUpsilon s t := by
            simpa [vertUpsilon, mul_assoc] using hge
          linarith
      have hexpphi : ‖Complex.exp ((c : ℂ) * mellinPhi ζ ξ)‖ ≤ Real.exp (c * (1 / 18 + |L| / 2)) := by
        rw [Complex.norm_exp]
        refine Real.exp_le_exp.mpr ?_
        rw [Complex.re_ofReal_mul]
        have h1 : (mellinPhi ζ ξ).re = (mellinPhi (s : ℂ) ξ).re - vertUpsilon s t := by
          have := hphi; rw [Complex.sub_re] at this; linarith
        rw [h1]
        have h3 : s ^ 3 ≤ (1 / 2) ^ 3 := pow_le_pow_left₀ hs.le hs2 3
        have h4 : s * L ≤ |L| / 2 := by
          calc s * L ≤ s * |L| := mul_le_mul_of_nonneg_left (le_abs_self L) hs.le
            _ ≤ (1 / 2) * |L| := mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
            _ = |L| / 2 := by ring
        have h5 : (mellinPhi (s : ℂ) ξ).re - vertUpsilon s t ≤ 1 / 18 + |L| / 2 := by
          rw [← hL] at hφ0; linarith
        exact mul_le_mul_of_nonneg_left h5 hc.le
      unfold mellinK0
      rw [norm_mul, norm_mul]
      calc ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ)‖ *
            ‖Complex.exp ((c : ℂ) * mellinPhi ζ ξ)‖
          ≤ (2 * (1 + |t|) ^ (-(1 / 2 : ℝ))) * Real.exp (1 / (4 * c)) * Real.exp (c * (1 / 18 + |L| / 2)) := by
            gcongr
        _ = K * (1 + |t|) ^ (-(1 / 2 : ℝ)) := by rw [hK]; ring
    rcases le_total 0 τ with hτ | hτ
    · exact hnonneg τ hτ
    · have hconj : (s : ℂ) + (τ : ℂ) * Complex.I =
          starRingEnd ℂ ((s : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) := by
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
      have hre : ((s : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I).re = s := by simp
      rw [hconj, mellinK0_conj hξ (by rw [hre]; exact hs) (by rw [hre]; linarith), Complex.norm_conj]
      simpa [abs_neg] using hnonneg (-τ) (neg_nonneg.mpr hτ)

/-- `‖G(z)‖ ≤ B (1 + |Im z|)^{-1/2}` on `c/2 ≤ Re z ≤ c` (`mat:Gbound`, right half). -/
theorem admissG_bound_right_decay (hc : 1 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c →
      ‖admissG c z‖ ≤ B * (1 + |z.im|) ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨K, hK0, hK⟩ := norm_mellinK0_half_strip_decay hc0 (liftXi_pos hc0)
  refine ⟨‖Complex.Gamma (c : ℂ)‖ * K * c ^ (1 / 2 : ℝ), by positivity, fun z hz1 hz2 => ?_⟩
  have hz0 : 0 < z.re := by linarith
  rw [admissG_eq hc0 hz0 hz2, norm_mul, norm_mul]
  have hr : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpw : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith)
  have hKz : ‖mellinK0 c (1 - z / c) (liftXi c)‖ ≤ K * (1 + |z.im| / c) ^ (-(1 / 2 : ℝ)) := by
    have e : (1 - z / (c : ℂ)) = ((1 - z.re / c : ℝ) : ℂ) + ((-(z.im / c) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_ofReal]
    rw [e]
    have h1 := hK (1 - z.re / c) (-(z.im / c))
      (by have := (div_le_one hc0).mpr hz2; linarith)
      (by have : 1 / 2 ≤ z.re / c := by rw [le_div_iff₀ hc0]; linarith
          linarith)
    simpa [abs_neg, abs_div, abs_of_pos hc0] using h1
  have hc_rpow : (1 + |z.im| / c) ^ (-(1 / 2 : ℝ)) ≤ c ^ (1 / 2 : ℝ) * (1 + |z.im|) ^ (-(1 / 2 : ℝ)) := by
    have h1' : (1 + |z.im|) / c ≤ 1 + |z.im| / c := by
      rw [add_div]; have : 1 / c ≤ 1 := (div_le_one hc0).mpr hc; linarith
    calc (1 + |z.im| / c) ^ (-(1 / 2 : ℝ)) ≤ ((1 + |z.im|) / c) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1' (by norm_num)
      _ = c ^ (1 / 2 : ℝ) * (1 + |z.im|) ^ (-(1 / 2 : ℝ)) := by
          rw [Real.div_rpow (by positivity) hc0.le, Real.rpow_neg hc0.le, div_inv_eq_mul, mul_comm]
  calc ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ * (‖Complex.Gamma (c : ℂ)‖ * ‖mellinK0 c (1 - z / c) (liftXi c)‖)
      ≤ 1 * (‖Complex.Gamma (c : ℂ)‖ * (K * (c ^ (1 / 2 : ℝ) * (1 + |z.im|) ^ (-(1 / 2 : ℝ))))) := by
        gcongr
        exact hKz.trans (mul_le_mul_of_nonneg_left hc_rpow hK0)
    _ = _ := by ring

/-- `G` is bounded on `c/2 ≤ Re z ≤ c`. -/
theorem admissG_bound_right (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c → ‖admissG c z‖ ≤ B := by
  obtain ⟨K, hK0, hK⟩ := norm_K0_half_strip_le hc
  refine ⟨‖Complex.Gamma (c : ℂ)‖ * K, by positivity, fun z hz1 hz2 => ?_⟩
  have hz0 : 0 < z.re := by linarith
  rw [admissG_eq hc hz0 hz2, norm_mul, norm_mul]
  have hr : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hpw : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos hr (by linarith)
  have hKz : ‖mellinK0 c (1 - z / c) (liftXi c)‖ ≤ K := by
    have e : (1 - z / (c : ℂ)) = ((1 - z.re / c : ℝ) : ℂ) + ((-(z.im / c) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [Complex.div_re, Complex.div_im, Complex.normSq_ofReal]
    rw [e]
    exact hK _ _ (by have := (div_le_one hc).mpr hz2; linarith)
      (by have : 1 / 2 ≤ z.re / c := by rw [le_div_iff₀ hc]; linarith
          linarith)
  calc ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ * (‖Complex.Gamma (c : ℂ)‖ * ‖mellinK0 c (1 - z / c) (liftXi c)‖)
      ≤ 1 * (‖Complex.Gamma (c : ℂ)‖ * K) := by gcongr
    _ = _ := one_mul _

/-- The reflection `G(z) · (2π)^{-(c-z)} Γ(c-z) = G(c-z) · (2π)^{-z} Γ(z)` (`ℋ(1-ζ) = ℋ(ζ)`). -/
theorem admissG_reflect (hc : 0 < c) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c) :
    admissG c z * (((2 * Real.pi : ℝ) : ℂ) ^ (-((c : ℂ) - z)) * Complex.Gamma ((c : ℂ) - z)) =
      admissG c ((c : ℂ) - z) * (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hre0 : 0 < (z / (c : ℂ)).re := by
    rw [Complex.div_ofReal_re]; positivity
  have hre1 : (z / (c : ℂ)).re < 1 := by
    rw [Complex.div_ofReal_re]; exact (div_lt_one hc).mpr hz1
  have e2 : stripH (1 - z / c) = stripH (z / c) := stripH_one_sub hre0 hre1
  have e1 : 1 - ((c : ℂ) - z) / c = z / c := by field_simp; ring
  unfold admissG
  rw [e1, e2]
  ring

/-- `‖G(z)‖ ≤ B (1 + |Im z|)^{-1/2}` on `0 < Re z < c/2`, `|Im z| ≥ 1` (`mat:Gbound`, left half). -/
theorem admissG_bound_left_decay (hc : 1 ≤ c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 < z.re → z.re < c / 2 → 1 ≤ |z.im| →
      ‖admissG c z‖ ≤ B * (1 + |z.im|) ^ (-(1 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨BR, hBR0, hBR⟩ := admissG_bound_right_decay hc
  set D : ℝ := Real.exp (2 * ((c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2)) with hD
  have hD0 : 0 < D := Real.exp_pos _
  refine ⟨BR * ((2 * Real.pi) ^ c * D), by positivity, fun z hz0 hz2 hy => ?_⟩
  have hzc : z.re < c := by linarith
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hr1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hz0' : 0 < ((c : ℂ) - z).re := by simp; exact hzc
  have hrefl := admissG_reflect hc0 hz0 hzc
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hGc : Complex.Gamma ((c : ℂ) - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0'
  have hn1 : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ = (2 * Real.pi) ^ (-z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
  have hn2 : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-((c : ℂ) - z))‖ = (2 * Real.pi) ^ (-(c - z.re)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
  have hratio := norm_Gamma_ratio_le (c := c) (x1 := z.re) (y := z.im) hz0 (by linarith) hy
  have hzre : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  have hcz : (((c - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I) = (c : ℂ) - z := by
    apply Complex.ext <;> simp
  rw [hzre, hcz] at hratio
  have hy0 : |z.im| ^ (2 * z.re - c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hB : ‖admissG c ((c : ℂ) - z)‖ ≤ BR * (1 + |z.im|) ^ (-(1 / 2 : ℝ)) := by
    have := hBR ((c : ℂ) - z) (by simp; linarith) (by simp; linarith)
    simpa [abs_neg] using this
  have hnorm := congrArg norm hrefl
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hn1, hn2] at hnorm
  have hGn : 0 < ‖Complex.Gamma ((c : ℂ) - z)‖ := norm_pos_iff.mpr hGc
  have hp1 : 0 < (2 * Real.pi) ^ (-(c - z.re)) := Real.rpow_pos_of_pos hr _
  have hprod : (2 * Real.pi) ^ (-z.re) / (2 * Real.pi) ^ (-(c - z.re)) = (2 * Real.pi) ^ (c - 2 * z.re) := by
    rw [← Real.rpow_sub hr]; congr 1; ring
  have hpow_le : (2 * Real.pi) ^ (c - 2 * z.re) ≤ (2 * Real.pi) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  have hGeq : ‖admissG c z‖ = ‖admissG c ((c : ℂ) - z)‖ * ((2 * Real.pi) ^ (c - 2 * z.re) *
      (‖Complex.Gamma z‖ / ‖Complex.Gamma ((c : ℂ) - z)‖)) := by
    rw [← hprod]
    field_simp
    linarith [hnorm]
  rw [hGeq]
  calc ‖admissG c ((c : ℂ) - z)‖ * ((2 * Real.pi) ^ (c - 2 * z.re) * (‖Complex.Gamma z‖ / ‖Complex.Gamma ((c : ℂ) - z)‖))
      ≤ (BR * (1 + |z.im|) ^ (-(1 / 2 : ℝ))) * ((2 * Real.pi) ^ c * (D * 1)) := by
        refine mul_le_mul hB (mul_le_mul hpow_le (hratio.trans (mul_le_mul_of_nonneg_left hy0 hD0.le))
          (by positivity) (by positivity)) (by positivity) (by positivity)
    _ = _ := by ring

theorem admissG_bound_left (hc : 0 < c) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 < z.re → z.re < c / 2 → 1 ≤ |z.im| → ‖admissG c z‖ ≤ B := by
  obtain ⟨BR, hBR0, hBR⟩ := admissG_bound_right hc
  set D : ℝ := Real.exp (2 * ((c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2)) with hD
  have hD0 : 0 < D := Real.exp_pos _
  refine ⟨BR * ((2 * Real.pi) ^ c * D), by positivity, fun z hz0 hz2 hy => ?_⟩
  have hzc : z.re < c := by linarith
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hr1 : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hz0' : 0 < ((c : ℂ) - z).re := by simp; exact hzc
  have hrefl := admissG_reflect hc hz0 hzc
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hGc : Complex.Gamma ((c : ℂ) - z) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0'
  have hn1 : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-z)‖ = (2 * Real.pi) ^ (-z.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
  have hn2 : ‖((2 * Real.pi : ℝ) : ℂ) ^ (-((c : ℂ) - z))‖ = (2 * Real.pi) ^ (-(c - z.re)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hr]; simp
  have hratio := norm_Gamma_ratio_le (c := c) (x1 := z.re) (y := z.im) hz0 (by linarith) hy
  have hzre : (z.re : ℂ) + (z.im : ℂ) * Complex.I = z := Complex.re_add_im z
  have hcz : (((c - z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I) = (c : ℂ) - z := by
    apply Complex.ext <;> simp
  rw [hzre, hcz] at hratio
  have hy0 : |z.im| ^ (2 * z.re - c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hB := hBR ((c : ℂ) - z) (by simp; linarith) (by simp; linarith)
  have hnorm := congrArg norm hrefl
  rw [norm_mul, norm_mul, norm_mul, norm_mul, hn1, hn2] at hnorm
  have hGn : 0 < ‖Complex.Gamma ((c : ℂ) - z)‖ := norm_pos_iff.mpr hGc
  have hp1 : 0 < (2 * Real.pi) ^ (-(c - z.re)) := Real.rpow_pos_of_pos hr _
  have hprod : (2 * Real.pi) ^ (-z.re) / (2 * Real.pi) ^ (-(c - z.re)) = (2 * Real.pi) ^ (c - 2 * z.re) := by
    rw [← Real.rpow_sub hr]; congr 1; ring
  have hpow_le : (2 * Real.pi) ^ (c - 2 * z.re) ≤ (2 * Real.pi) ^ c :=
    Real.rpow_le_rpow_of_exponent_le hr1 (by linarith)
  -- `‖G z‖ = ‖G (c - z)‖ · (2π)^{c - 2x} · ‖Γ z‖ / ‖Γ (c - z)‖`
  have hGeq : ‖admissG c z‖ = ‖admissG c ((c : ℂ) - z)‖ * ((2 * Real.pi) ^ (c - 2 * z.re) *
      (‖Complex.Gamma z‖ / ‖Complex.Gamma ((c : ℂ) - z)‖)) := by
    rw [← hprod]
    field_simp
    linarith [hnorm]
  rw [hGeq]
  calc ‖admissG c ((c : ℂ) - z)‖ * ((2 * Real.pi) ^ (c - 2 * z.re) * (‖Complex.Gamma z‖ / ‖Complex.Gamma ((c : ℂ) - z)‖))
      ≤ BR * ((2 * Real.pi) ^ c * (D * 1)) := by
        refine mul_le_mul hB (mul_le_mul hpow_le (hratio.trans (mul_le_mul_of_nonneg_left hy0 hD0.le))
          (by positivity) (by positivity)) (by positivity) hBR0
    _ = _ := by ring

end G

section Phi

variable {c : ℝ} {W : ℂ → ℂ}

lemma re_arg_mem {z : ℂ} (hc : 0 < c) (hz0 : 0 < z.re) (hz1 : z.re ≤ c) :
    0 ≤ (1 - z / (c : ℂ)).re ∧ (1 - z / (c : ℂ)).re < 1 := by
  rw [re_one_sub_div hc]
  have : z.re / c ≤ 1 := (div_le_one hc).mpr hz1
  have : 0 < z.re / c := by positivity
  constructor <;> linarith

lemma norm_W_arg_le_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 < z.re → z.re ≤ c →
      ‖W (1 - z / (c : ℂ))‖ ≤ B * (1 + |z.im|) ^ (-(1 / 2 + η)) := by
  obtain ⟨C, hC⟩ := hW.bound
  have hc0 : 0 < c := by linarith
  refine ⟨|C| * c ^ (1 / 2 + η), by positivity, fun z hz0 hz1 => ?_⟩
  obtain ⟨h0, h1⟩ := re_arg_mem hc0 hz0 hz1
  have hb := hC _ h0 h1.le
  have him : |(1 - z / (c : ℂ)).im| = |z.im| / c := by
    simp [Complex.div_im, Complex.normSq_ofReal, abs_div, abs_of_pos hc0]
    field_simp
  rw [him] at hb
  have h2 : (1 + |z.im| / c) ^ (-(1 / 2 + η)) ≤ c ^ (1 / 2 + η) * (1 + |z.im|) ^ (-(1 / 2 + η)) := by
    have h1' : (1 + |z.im|) / c ≤ 1 + |z.im| / c := by
      rw [add_div]; have : 1 / c ≤ 1 := (div_le_one hc0).mpr hc
      linarith
    calc (1 + |z.im| / c) ^ (-(1 / 2 + η)) ≤ ((1 + |z.im|) / c) ^ (-(1 / 2 + η)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1' (by linarith)
      _ = c ^ (1 / 2 + η) * (1 + |z.im|) ^ (-(1 / 2 + η)) := by
          rw [Real.div_rpow (by positivity) hc0.le, Real.rpow_neg hc0.le, div_inv_eq_mul, mul_comm]
  calc ‖W (1 - z / (c : ℂ))‖ ≤ C * (1 + |z.im| / c) ^ (-(1 / 2 + η)) := hb
    _ ≤ |C| * (1 + |z.im| / c) ^ (-(1 / 2 + η)) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (c ^ (1 / 2 + η) * (1 + |z.im|) ^ (-(1 / 2 + η))) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = _ := by ring

lemma norm_W_arg_le (hc : 1 ≤ c) (hW : StripM1 W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 < z.re → z.re ≤ c → ‖W (1 - z / (c : ℂ))‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨B, hB0, hB⟩ := norm_W_arg_le_of_W1 hc (by norm_num : (0 : ℝ) < 3 / 2) hW.toStripW1
  refine ⟨B, hB0, fun z hz0 hz1 => ?_⟩
  convert hB z hz0 hz1 using 2
  norm_num

theorem admissPhi_differentiableOn_of_W1 {η : ℝ} (hc : 0 < c) (hW : StripW1 η W) :
    DifferentiableOn ℂ (admissPhi c W) {z : ℂ | 0 < z.re ∧ z.re < c} := by
  refine (admissG_differentiableOn hc).mul ?_
  refine hW.hol.comp ((differentiableOn_const _).sub (differentiableOn_id.div_const _)) fun z hz => ?_
  obtain ⟨h0, h1⟩ := re_arg_mem hc hz.1 hz.2.le
  have : (1 - z / (c : ℂ)).re ≠ 0 := by
    rw [re_one_sub_div hc]
    have : z.re / c < 1 := (div_lt_one hc).mpr hz.2
    linarith
  exact ⟨lt_of_le_of_ne h0 (Ne.symm this), h1⟩

theorem admissPhi_differentiableOn (hc : 0 < c) (hW : StripM1 W) :
    DifferentiableOn ℂ (admissPhi c W) {z : ℂ | 0 < z.re ∧ z.re < c} :=
  admissPhi_differentiableOn_of_W1 hc hW.toStripW1

theorem admissPhi_continuousOn_edge_of_W1 {η : ℝ} (hc : 0 < c) (hW : StripW1 η W) :
    ContinuousOn (admissPhi c W) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  refine (admissG_continuousOn_edge hc).mul ?_
  refine hW.cont.comp ((continuousOn_const.sub (continuousOn_id.div_const _))) fun z hz => ?_
  obtain ⟨h0, h1⟩ := re_arg_mem hc hz.1 hz.2
  exact ⟨h0, h1.le⟩

theorem admissPhi_continuousOn_edge (hc : 0 < c) (hW : StripM1 W) :
    ContinuousOn (admissPhi c W) {z : ℂ | 0 < z.re ∧ z.re ≤ c} :=
  admissPhi_continuousOn_edge_of_W1 hc hW.toStripW1

/-- Bound of `Φ_W` on `c/2 ≤ Re z ≤ c` under `(W1)` (`mat:T7`). -/
theorem admissPhi_bound_right_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W) :
    ∃ B : ℝ, ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c → ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(1 + η)) := by
  obtain ⟨BG, hBG0, hBG⟩ := admissG_bound_right_decay hc
  obtain ⟨BW, hBW0, hBW⟩ := norm_W_arg_le_of_W1 hc hη hW
  refine ⟨BG * BW, fun z hz1 hz2 => ?_⟩
  have hz0 : 0 < z.re := by linarith
  unfold admissPhi
  rw [norm_mul]
  have hadd : (1 + |z.im|) ^ (-(1 / 2 : ℝ)) * (1 + |z.im|) ^ (-(1 / 2 + η)) = (1 + |z.im|) ^ (-(1 + η)) := by
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc ‖admissG c z‖ * ‖W (1 - z / (c : ℂ))‖
      ≤ (BG * (1 + |z.im|) ^ (-(1 / 2 : ℝ))) * (BW * (1 + |z.im|) ^ (-(1 / 2 + η))) :=
        mul_le_mul (hBG z hz1 hz2) (hBW z hz0 hz2) (norm_nonneg _) (by positivity)
    _ = BG * BW * ((1 + |z.im|) ^ (-(1 / 2 : ℝ)) * (1 + |z.im|) ^ (-(1 / 2 + η))) := by ring
    _ = _ := by rw [hadd]

/-- Bound of `Φ_W` on `c/2 ≤ Re z ≤ c`. -/
theorem admissPhi_bound_right (hc : 1 ≤ c) (hW : StripM1 W) :
    ∃ B : ℝ, ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c → ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨B, hB⟩ := admissPhi_bound_right_of_W1 hc (by norm_num : (0 : ℝ) < 3 / 2) hW.toStripW1
  refine ⟨|B|, fun z hz1 hz2 => ?_⟩
  have h1 := hB z hz1 hz2
  have h2 : (1 + |z.im|) ^ (-(1 + (3 / 2 : ℝ))) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by norm_num)
  calc ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(1 + (3 / 2 : ℝ))) := h1
    _ ≤ |B| * (1 + |z.im|) ^ (-(1 + (3 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    _ ≤ |B| * (1 + |z.im|) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)

/-- Bound of `Φ_W` on `0 < Re z < c/2`, `|Im z| ≥ 1`, under `(W1)` (`mat:T7`). -/
theorem admissPhi_bound_left_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W) :
    ∃ B : ℝ, ∀ z : ℂ, 0 < z.re → z.re < c / 2 → 1 ≤ |z.im| →
      ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(1 + η)) := by
  obtain ⟨BG, hBG0, hBG⟩ := admissG_bound_left_decay hc
  obtain ⟨BW, hBW0, hBW⟩ := norm_W_arg_le_of_W1 hc hη hW
  refine ⟨BG * BW, fun z hz0 hz2 hy => ?_⟩
  unfold admissPhi
  rw [norm_mul]
  have hadd : (1 + |z.im|) ^ (-(1 / 2 : ℝ)) * (1 + |z.im|) ^ (-(1 / 2 + η)) = (1 + |z.im|) ^ (-(1 + η)) := by
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  calc ‖admissG c z‖ * ‖W (1 - z / (c : ℂ))‖
      ≤ (BG * (1 + |z.im|) ^ (-(1 / 2 : ℝ))) * (BW * (1 + |z.im|) ^ (-(1 / 2 + η))) :=
        mul_le_mul (hBG z hz0 hz2 hy) (hBW z hz0 (by linarith)) (norm_nonneg _) (by positivity)
    _ = BG * BW * ((1 + |z.im|) ^ (-(1 / 2 : ℝ)) * (1 + |z.im|) ^ (-(1 / 2 + η))) := by ring
    _ = _ := by rw [hadd]

/-- Bound of `Φ_W` on `0 < Re z < c/2`, `|Im z| ≥ 1`, uniform up to the line `Re z = 0`. -/
theorem admissPhi_bound_left (hc : 1 ≤ c) (hW : StripM1 W) :
    ∃ B : ℝ, ∀ z : ℂ, 0 < z.re → z.re < c / 2 → 1 ≤ |z.im| →
      ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨B, hB⟩ := admissPhi_bound_left_of_W1 hc (by norm_num : (0 : ℝ) < 3 / 2) hW.toStripW1
  refine ⟨|B|, fun z hz0 hz2 hy => ?_⟩
  have h1 := hB z hz0 hz2 hy
  have h2 : (1 + |z.im|) ^ (-(1 + (3 / 2 : ℝ))) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg z.im]) (by norm_num)
  calc ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(1 + (3 / 2 : ℝ))) := h1
    _ ≤ |B| * (1 + |z.im|) ^ (-(1 + (3 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    _ ≤ |B| * (1 + |z.im|) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)

/-- **`Φ_W` satisfies the hypotheses of the Mellin hub** under `(W1)` (`c ≥ 1`, `η > 0`). -/
theorem admissPhi_mellinLiftData_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W) :
    MellinLiftData c (admissPhi c W) where
  hol := admissPhi_differentiableOn_of_W1 (by linarith) hW
  decay := by
    intro a b ha hab hb
    have hc0 : 0 < c := by linarith
    obtain ⟨M, hM⟩ := exists_bound_rect (admissPhi_differentiableOn_of_W1 hc0 hW).continuousOn ha hab hb
    obtain ⟨BR, hBR⟩ := admissPhi_bound_right_of_W1 hc hη hW
    obtain ⟨BL, hBL⟩ := admissPhi_bound_left_of_W1 hc hη hW
    refine ⟨1 + η, by linarith, 2 ^ (1 + η) * |M| + |BR| + |BL|, fun z hz1 hz2 => ?_⟩
    have hw0 : 0 ≤ (1 + |z.im|) ^ (-(1 + η)) := by positivity
    rcases le_total |z.im| 1 with hy | hy
    · have h1 := hM z hz1 hz2 hy
      have h4 : (2 : ℝ) ^ (-(1 + η)) ≤ (1 + |z.im|) ^ (-(1 + η)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg z.im]) (by linarith) (by linarith)
      have h2p : (2 : ℝ) ^ (1 + η) * (2 : ℝ) ^ (-(1 + η)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have hMle : |M| ≤ 2 ^ (1 + η) * |M| * (1 + |z.im|) ^ (-(1 + η)) := by
        calc |M| = 2 ^ (1 + η) * |M| * (2 : ℝ) ^ (-(1 + η)) := by
              rw [mul_right_comm, h2p, one_mul]
          _ ≤ 2 ^ (1 + η) * |M| * (1 + |z.im|) ^ (-(1 + η)) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
      have := le_abs_self M
      nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
    · rcases le_or_gt (c / 2) z.re with hr | hr
      · have h1 := hBR z hr (hz2.trans hb.le)
        have : BR * (1 + |z.im|) ^ (-(1 + η)) ≤ |BR| * (1 + |z.im|) ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hw0
        have : 0 ≤ 2 ^ (1 + η) * |M| * (1 + |z.im|) ^ (-(1 + η)) := by positivity
        nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
      · have h1 := hBL z (by linarith) hr hy
        have : BL * (1 + |z.im|) ^ (-(1 + η)) ≤ |BL| * (1 + |z.im|) ^ (-(1 + η)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hw0
        have : 0 ≤ 2 ^ (1 + η) * |M| * (1 + |z.im|) ^ (-(1 + η)) := by positivity
        nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
  real := by
    intro z hz0 hz1
    have hc0 : 0 < c := by linarith
    unfold admissPhi
    rw [map_mul, admissG_conj hc0 hz0 hz1]
    congr 1
    obtain ⟨h0, h1⟩ := re_arg_mem hc0 hz0 hz1.le
    have : (1 - starRingEnd ℂ z / (c : ℂ)) = starRingEnd ℂ (1 - z / (c : ℂ)) := by
      simp [Complex.conj_ofReal]
    rw [this]
    exact hW.real _ h0 h1.le

/-- **`Φ_W` satisfies the hypotheses of the Mellin hub** (`c ≥ 1`). -/
theorem admissPhi_mellinLiftData (hc : 1 ≤ c) (hW : StripM1 W) : MellinLiftData c (admissPhi c W) :=
  admissPhi_mellinLiftData_of_W1 hc (by norm_num) hW.toStripW1

end Phi

section Vert

variable {c : ℝ} {W : ℂ → ℂ}

/-- The lift along `Re z = c` equals the lift along `Re z = c/2` under `(W1)` (`mat:T7`). -/
theorem mellinInv_admissPhi_edge_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W)
    {Δ : ℝ} (hΔ : 0 < Δ) :
    mellinInv c (admissPhi c W) Δ = mellinInv (c / 2) (admissPhi c W) Δ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨B0, hB0⟩ := admissPhi_bound_right_of_W1 hc hη hW
  have hB : ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c → ‖admissPhi c W z‖ ≤ |B0| * (1 + |z.im|) ^ (-(1 + η)) :=
    fun z h1 h2 => (hB0 z h1 h2).trans (mul_le_mul_of_nonneg_right (le_abs_self B0) (by positivity))
  have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  set H : ℂ → ℂ := fun z => (Δ : ℂ) ^ (-z) • admissPhi c W z with hH
  have hcont : ContinuousOn H {w : ℂ | c / 2 ≤ w.re ∧ w.re ≤ c} :=
    (Continuous.const_cpow continuous_neg (Or.inl hΔ0)).continuousOn.smul
      ((admissPhi_continuousOn_edge_of_W1 hc0 hW).mono fun w hw => ⟨by linarith [hw.1], hw.2⟩)
  have hd : DifferentiableOn ℂ H {w : ℂ | c / 2 < w.re ∧ w.re < c} :=
    DifferentiableOn.smul (fun w _ => ((differentiableAt_id.neg).const_cpow (Or.inl hΔ0)).differentiableWithinAt)
      ((admissPhi_differentiableOn_of_W1 hc0 hW).mono fun w hw => ⟨by linarith [hw.1], hw.2⟩)
  have key := CohnElkies.strip_shift (H := H) (a := c / 2) (b := c) (by linarith) hcont hd
    (integrable_weight_rpow (by linarith : 1 < 1 + η) ((Δ ^ (-(c / 2)) + Δ ^ (-c)) * |B0|))
    (fun w hw1 hw2 => by
      have h1 := hB w hw1 hw2
      have h2 := rpow_neg_le_sum hΔ hw1 hw2
      simp only [hH, norm_smul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
      simp only [Complex.neg_re]
      calc Δ ^ (-w.re) * ‖admissPhi c W w‖ ≤ (Δ ^ (-(c / 2)) + Δ ^ (-c)) * (|B0| * (1 + |w.im|) ^ (-(1 + η))) :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring)
    (tendsto_weight_rpow_atTop (by linarith) _) (tendsto_weight_rpow_atBot (by linarith) _)
  unfold mellinInv
  congr 1

/-- The lift along `Re z = c` equals the lift along `Re z = c/2` (the contour shift to the edge). -/
theorem mellinInv_admissPhi_edge (hc : 1 ≤ c) (hW : StripM1 W) {Δ : ℝ} (hΔ : 0 < Δ) :
    mellinInv c (admissPhi c W) Δ = mellinInv (c / 2) (admissPhi c W) Δ :=
  mellinInv_admissPhi_edge_of_W1 hc (by norm_num) hW.toStripW1 hΔ


/-- The integrand of the inverse Mellin integral in kernel form (cf. `edge_integrand_eq`, here on any line `0 < Re z ≤ c`). -/
theorem admiss_integrand_eq (hc : 0 < c) {ξ : ℝ} (hξ : 0 < ξ) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re ≤ c) :
    ((c * ξ : ℝ) : ℂ) ^ (-z) • admissPhi c W z =
      (Complex.Gamma (c : ℂ) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ))) *
        (mellinK0 c (1 - z / c) ξ * W (1 - z / c)) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  obtain ⟨hζ0, hζ1⟩ := re_arg_mem hc hz0 hz1
  have key := mellin_strip_kernel_eq hc hξ hζ0 hζ1
  have e1 : (c : ℂ) * (1 - (1 - z / (c : ℂ))) = z := by field_simp; ring
  have e0 : (c : ℂ) * (1 - z / c) = (c : ℂ) - z := by field_simp
  rw [e1, e0] at key
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hD : (0 : ℝ) < c * ξ := by positivity
  have hP : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hDn : ((c * ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hTeq : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * ((c * ξ : ℝ) : ℂ) := by push_cast; ring
  have hTkey : (2 * (Real.pi : ℂ) * c * ξ : ℂ) = ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) := by push_cast; ring
  rw [hTkey] at key
  have hT : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ≠ 0 := by rw [hTeq]; exact mul_ne_zero hP hDn
  have hGc : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hc)
  have hTz : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-z) =
      ((2 * Real.pi : ℝ) : ℂ) ^ (-z) * ((c * ξ : ℝ) : ℂ) ^ (-z) := by
    rw [hTeq, Complex.mul_cpow_ofReal_nonneg hr.le hD.le]
  have hTadd : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ)) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ ((c : ℂ) - z) =
      ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-z) := by
    rw [← Complex.cpow_add _ _ hT]; congr 1; ring
  unfold admissPhi admissG
  rw [← key, smul_eq_mul]
  calc ((c * ξ : ℝ) : ℂ) ^ (-z) * (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c))
      = (((2 * Real.pi : ℝ) : ℂ) ^ (-z) * ((c * ξ : ℝ) : ℂ) ^ (-z)) * Complex.Gamma z * Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c) := by ring
    _ = ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ)) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ ((c : ℂ) - z) * Complex.Gamma z *
          Complex.exp ((c : ℂ) * stripH (1 - z / c)) * W (1 - z / c) := by rw [hTadd, ← hTz]
    _ = _ := by field_simp

/-- Absolute integrability of the vertical-line integrand `K₀(σ + iτ, ξ) W(σ + iτ)` under `(W1)` (`mat:T7` (b)). -/
theorem admiss_vert_integrable_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {ξ : ℝ} (hξ : 0 < ξ) :
    Integrable (fun τ : ℝ => mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I)) := by
  have hc0 : 0 < c := by linarith
  have hΦ := admissPhi_mellinLiftData_of_W1 hc hη hW
  have hΔ : 0 < c * ξ := mul_pos hc0 hξ
  set x : ℝ := c * (1 - σ) with hxdef
  have hx0 : 0 < x := mul_pos hc0 (by linarith)
  have hxc : x ≤ c := by rw [hxdef]; nlinarith
  have hcont : Continuous (fun τ : ℝ => mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
      W ((σ : ℂ) + (τ : ℂ) * Complex.I)) := by
    have hK : Continuous (fun τ : ℝ => mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ) :=
      (differentiableOn_mellinK0 hc0 ξ).continuousOn.comp_continuous (by fun_prop) fun τ => by
        show |((σ : ℂ) + (τ : ℂ) * Complex.I).re| < 1
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
          Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
        rw [abs_of_nonneg hσ0]; exact hσ1
    have hWc : Continuous (fun τ : ℝ => W ((σ : ℂ) + (τ : ℂ) * Complex.I)) :=
      hW.cont.comp_continuous (by fun_prop) fun τ => by simp [hσ0, hσ1.le]
    exact hK.mul hWc
  rcases hσ0.eq_or_lt with rfl | hσpos
  · obtain ⟨K, hK0, hK⟩ := norm_mellinK0_half_strip_decay hc0 hξ
    obtain ⟨C, hC⟩ := hW.bound
    refine (integrable_weight_rpow (by linarith : 1 < 1 + η) (K * |C|)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun τ => ?_)
    rw [norm_mul]
    have hk := hK 0 τ le_rfl (by norm_num)
    have hw := hC ((0 : ℝ) + (τ : ℂ) * Complex.I) (by simp) (by simp)
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hw
    have hadd : (1 + |τ|) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(1 / 2 + η)) = (1 + |τ|) ^ (-(1 + η)) := by
      rw [← Real.rpow_add (by positivity)]; congr 1; ring
    calc ‖mellinK0 c ((0 : ℝ) + (τ : ℂ) * Complex.I) ξ‖ * ‖W ((0 : ℝ) + (τ : ℂ) * Complex.I)‖
        ≤ (K * (1 + |τ|) ^ (-(1 / 2 : ℝ))) * (|C| * (1 + |τ|) ^ (-(1 / 2 + η))) := by
          refine mul_le_mul hk (hw.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)))
            (norm_nonneg _) (by positivity)
      _ = K * |C| * ((1 + |τ|) ^ (-(1 / 2 : ℝ)) * (1 + |τ|) ^ (-(1 / 2 + η))) := by ring
      _ = _ := by rw [hadd]
  · have hlt : x < c := by rw [hxdef]; nlinarith
    have hI := hΦ.integrable_line_cpow hx0 hlt hΔ
    have hcomp := hI.comp_mul_left' (R := -c) (by linarith)
    set αc : ℂ := Complex.Gamma (c : ℂ) * ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ^ (-(c : ℂ)) with hαc
    have hαne : αc ≠ 0 := by
      have hG : Complex.Gamma (c : ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hc0)
      have hT : ((2 * Real.pi * (c * ξ) : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (show (0 : ℝ) < 2 * Real.pi * (c * ξ) by positivity).ne'
      exact mul_ne_zero hG (fun h => hT ((Complex.cpow_eq_zero_iff _ _).mp h).1)
    have hscaled := hcomp.const_mul αc⁻¹
    refine hscaled.congr (ae_of_all _ fun τ => ?_)
    have hre : ((x : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I).re = x := by simp
    have heq := admiss_integrand_eq (W := W) hc0 hξ (z := (x : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)
      (by rw [hre]; exact hx0) (by rw [hre]; exact hxc)
    have harg : 1 - ((x : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I) / c = (σ : ℂ) + (τ : ℂ) * Complex.I := by
      have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
      rw [hxdef]; push_cast; field_simp; ring
    rw [harg] at heq
    dsimp only
    rw [heq, ← hαc, inv_mul_cancel_left₀ hαne]

/-- **Vertical representation** (`mat:T7` (b)) under `(W1)`: for `0 ≤ σ < 1` and `ξ > 0`,
`(f_W ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ + iτ, ξ) W(σ + iτ) dτ`. -/
theorem admiss_vert_rep_of_W1 {η : ℝ} (hc : 1 ≤ c) (hη : 0 < η) (hW : StripW1 η W)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {ξ : ℝ} (hξ : 0 < ξ) :
    (((hankelRho0 c (c * ξ) * admissLift c W (c * ξ) : ℝ)) : ℂ) =
      ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
        ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hΦ := admissPhi_mellinLiftData_of_W1 hc hη hW
  have hΔ : 0 < c * ξ := mul_pos hc0 hξ
  set Δ := c * ξ with hΔdef
  set x : ℝ := c * (1 - σ) with hxdef
  have hx0 : 0 < x := mul_pos hc0 (by linarith)
  have hxc : x ≤ c := by rw [hxdef]; nlinarith
  have e1 : (admissLift c W Δ : ℂ) = mellinInv x (admissPhi c W) Δ := by
    by_cases hσ : 0 < σ
    · have hlt : x < c := by rw [hxdef]; nlinarith
      exact ofReal_liftFun hΦ (x₀ := c / 2) (x := x) (by linarith) (by linarith) hx0 hlt hΔ
    · have hσ' : σ = 0 := le_antisymm (not_lt.mp hσ) hσ0
      have hx : x = c := by rw [hxdef, hσ']; ring
      rw [hx, mellinInv_admissPhi_edge_of_W1 hc hη hW hΔ]
      exact ofReal_liftFun hΦ (x₀ := c / 2) (x := c / 2) (by linarith) (by linarith) (by linarith) (by linarith) hΔ
  set G : ℝ → ℂ := fun y => mellinK0 c (1 - ((x : ℂ) + (y : ℂ) * Complex.I) / c) ξ *
    W (1 - ((x : ℂ) + (y : ℂ) * Complex.I) / c) with hG
  have e2 : mellinInv x (admissPhi c W) Δ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((Complex.Gamma (c : ℂ) * ((2 * Real.pi * Δ : ℝ) : ℂ) ^ (-(c : ℂ))) * ∫ y : ℝ, G y) := by
    unfold mellinInv
    rw [Complex.real_smul]
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
    exact admiss_integrand_eq hc0 hξ (by rw [hre]; exact hx0) (by rw [hre]; exact hxc)
  have e3 : ∫ y : ℝ, G y = (c : ℂ) * ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
      W ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
    have h := Measure.integral_comp_mul_left G (-c)
    have hpt : ∀ τ : ℝ, G (-c * τ) = mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ *
        W ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
      intro τ
      have : 1 - ((x : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I) / c = (σ : ℂ) + (τ : ℂ) * Complex.I := by
        have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
        rw [hxdef]; push_cast; field_simp; ring
      simp only [hG, this]
    simp_rw [hpt] at h
    have habs : |(-c)⁻¹| = c⁻¹ := by rw [abs_inv, abs_neg, abs_of_pos hc0]
    rw [habs, Complex.real_smul] at h
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    push_cast at h
    rw [h]; field_simp
  have hΓ : (Real.Gamma c : ℂ) = Complex.Gamma (c : ℂ) := (Complex.Gamma_ofReal c).symm
  have hGpos : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc0
  have hr : (0 : ℝ) < 2 * Real.pi := by positivity
  have hT : ((2 * Real.pi * Δ : ℝ) : ℂ) ^ (-(c : ℂ)) = (((2 * Real.pi * Δ) ^ (-c) : ℝ) : ℂ) := by
    rw [show -(c : ℂ) = ((-c : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cpow (by positivity)]
  have hconst : (2 * Real.pi) ^ c / Real.Gamma c * Δ ^ (c - 1) * (1 / (2 * Real.pi)) *
      (Real.Gamma c * (2 * Real.pi * Δ) ^ (-c)) * c = 1 / (2 * Real.pi * ξ) := by
    have h1 : (2 * Real.pi) ^ c * (2 * Real.pi) ^ (-c) = 1 := by rw [← Real.rpow_add hr]; simp
    have h2 : Δ ^ c * Δ ^ (-c) = 1 := by rw [← Real.rpow_add hΔ]; simp
    rw [Real.mul_rpow hr.le hΔ.le, Real.rpow_sub_one hΔ.ne']
    have hΔξ : Δ = c * ξ := hΔdef
    have hG0 : Real.Gamma c ≠ 0 := hGpos.ne'
    have : (2 * Real.pi) ^ c / Real.Gamma c * (Δ ^ c / Δ) * (1 / (2 * Real.pi)) *
        (Real.Gamma c * ((2 * Real.pi) ^ (-c) * Δ ^ (-c))) * c =
        ((2 * Real.pi) ^ c * (2 * Real.pi) ^ (-c)) * (Δ ^ c * Δ ^ (-c)) * c / (Δ * (2 * Real.pi)) := by
      field_simp
    rw [this, h1, h2, hΔξ]
    field_simp
  rw [show ((hankelRho0 c Δ * admissLift c W Δ : ℝ) : ℂ) = (hankelRho0 c Δ : ℂ) * (admissLift c W Δ : ℂ) by push_cast; ring,
    e1, e2, e3, hT]
  unfold hankelRho0
  have hc13 : ((((2 * Real.pi) ^ c / Real.Gamma c * Δ ^ (c - 1) : ℝ)) : ℂ) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Complex.Gamma (c : ℂ) * (((2 * Real.pi * Δ) ^ (-c) : ℝ) : ℂ)) * (c : ℂ))) =
      ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) := by
    rw [← hconst]; push_cast; rw [← hΓ]; ring
  set J := ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I)
  calc _ = (((2 * Real.pi) ^ c / Real.Gamma c * Δ ^ (c - 1) : ℝ) : ℂ) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Complex.Gamma (c : ℂ) * (((2 * Real.pi * Δ) ^ (-c) : ℝ) : ℂ)) * ((c : ℂ) * J))) := by
        push_cast; ring_nf
    _ = ((((2 * Real.pi) ^ c / Real.Gamma c * Δ ^ (c - 1) : ℝ)) : ℂ) *
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * ((Complex.Gamma (c : ℂ) * (((2 * Real.pi * Δ) ^ (-c) : ℝ) : ℂ)) * (c : ℂ))) * J := by ring
    _ = _ := by rw [hc13]

/-- **Vertical representation** (`uct:vert-rep`, `mat:T7`(b)): for `0 ≤ σ < 1` and `ξ > 0`,
`(f_W ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ + iτ, ξ) W̃(σ + iτ) dτ`. -/
theorem admiss_vert_rep (hc : 1 ≤ c) (hW : StripM1 W) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {ξ : ℝ} (hξ : 0 < ξ) :
    (((hankelRho0 c (c * ξ) * admissLift c W (c * ξ) : ℝ)) : ℂ) =
      ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
        ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I) :=
  admiss_vert_rep_of_W1 hc (by norm_num) hW.toStripW1 hσ0 hσ1 hξ

end Vert

/-- info: 'FormalResearch.SignUncertainty.admissPhi_mellinLiftData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admissPhi_mellinLiftData

/-- info: 'FormalResearch.SignUncertainty.mellinInv_admissPhi_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinInv_admissPhi_edge

/-- info: 'FormalResearch.SignUncertainty.admiss_vert_rep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms admiss_vert_rep

end FormalResearch.SignUncertainty

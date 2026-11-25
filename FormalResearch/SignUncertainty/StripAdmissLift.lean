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

/-- Hypothesis (M1) of `uct:admiss` on `W̃ : ℂ → ℂ` (only its values on `0 ≤ Re ζ ≤ 1` matter). -/
structure StripM1 (W : ℂ → ℂ) : Prop where
  hol : DifferentiableOn ℂ W {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1}
  cont : ContinuousOn W {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1}
  real : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → W (starRingEnd ℂ ζ) = starRingEnd ℂ (W ζ)
  bound : ∃ C : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖W ζ‖ ≤ C * (1 + |ζ.im|) ^ (-(2 : ℝ))

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

theorem admissG_bound_left (hc : 0 < c) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, a ≤ z.re → z.re < c / 2 → 1 ≤ |z.im| → ‖admissG c z‖ ≤ B := by
  obtain ⟨BR, hBR0, hBR⟩ := admissG_bound_right hc
  set D : ℝ := Real.exp (2 * ((c + 1 / 2) * c ^ 2 / 2 + c ^ 3 / 3 + 2)) with hD
  have hD0 : 0 < D := Real.exp_pos _
  refine ⟨BR * ((2 * Real.pi) ^ c * D), by positivity, fun z hz1 hz2 hy => ?_⟩
  have hz0 : 0 < z.re := by linarith
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

lemma norm_W_arg_le (hc : 1 ≤ c) (hW : StripM1 W) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : ℂ, 0 < z.re → z.re ≤ c → ‖W (1 - z / (c : ℂ))‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := hW.bound
  have hc0 : 0 < c := by linarith
  refine ⟨|C| * c ^ 2, by positivity, fun z hz0 hz1 => ?_⟩
  obtain ⟨h0, h1⟩ := re_arg_mem hc0 hz0 hz1
  have hb := hC _ h0 h1.le
  have him : |(1 - z / (c : ℂ)).im| = |z.im| / c := by
    simp [Complex.div_im, Complex.normSq_ofReal, abs_div, abs_of_pos hc0]
    field_simp
  rw [him] at hb
  have h2 : (1 + |z.im| / c) ^ (-(2 : ℝ)) ≤ c ^ 2 * (1 + |z.im|) ^ (-(2 : ℝ)) := by
    have h1' : (1 + |z.im|) / c ≤ 1 + |z.im| / c := by
      rw [add_div]; have : 1 / c ≤ 1 := (div_le_one hc0).mpr hc
      linarith
    calc (1 + |z.im| / c) ^ (-(2 : ℝ)) ≤ ((1 + |z.im|) / c) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) h1' (by norm_num)
      _ = c ^ 2 * (1 + |z.im|) ^ (-(2 : ℝ)) := by
          rw [Real.div_rpow (by positivity) hc0.le, Real.rpow_neg hc0.le, div_inv_eq_mul]
          rw [Real.rpow_two]; ring
  calc ‖W (1 - z / (c : ℂ))‖ ≤ C * (1 + |z.im| / c) ^ (-(2 : ℝ)) := hb
    _ ≤ |C| * (1 + |z.im| / c) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (c ^ 2 * (1 + |z.im|) ^ (-(2 : ℝ))) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = _ := by ring

theorem admissPhi_differentiableOn (hc : 0 < c) (hW : StripM1 W) :
    DifferentiableOn ℂ (admissPhi c W) {z : ℂ | 0 < z.re ∧ z.re < c} := by
  refine (admissG_differentiableOn hc).mul ?_
  refine hW.hol.comp ((differentiableOn_const _).sub (differentiableOn_id.div_const _)) fun z hz => ?_
  obtain ⟨h0, h1⟩ := re_arg_mem hc hz.1 hz.2.le
  have : (1 - z / (c : ℂ)).re ≠ 0 := by
    rw [re_one_sub_div hc]
    have : z.re / c < 1 := (div_lt_one hc).mpr hz.2
    linarith
  exact ⟨lt_of_le_of_ne h0 (Ne.symm this), h1⟩

theorem admissPhi_continuousOn_edge (hc : 0 < c) (hW : StripM1 W) :
    ContinuousOn (admissPhi c W) {z : ℂ | 0 < z.re ∧ z.re ≤ c} := by
  refine (admissG_continuousOn_edge hc).mul ?_
  refine hW.cont.comp ((continuousOn_const.sub (continuousOn_id.div_const _))) fun z hz => ?_
  obtain ⟨h0, h1⟩ := re_arg_mem hc hz.1 hz.2
  exact ⟨h0, h1.le⟩

/-- Bound of `Φ_W` on `c/2 ≤ Re z ≤ c`. -/
theorem admissPhi_bound_right (hc : 1 ≤ c) (hW : StripM1 W) :
    ∃ B : ℝ, ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c → ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨BG, hBG0, hBG⟩ := admissG_bound_right hc0
  obtain ⟨BW, hBW0, hBW⟩ := norm_W_arg_le hc hW
  refine ⟨BG * BW, fun z hz1 hz2 => ?_⟩
  have hz0 : 0 < z.re := by linarith
  unfold admissPhi
  rw [norm_mul]
  calc ‖admissG c z‖ * ‖W (1 - z / (c : ℂ))‖ ≤ BG * (BW * (1 + |z.im|) ^ (-(2 : ℝ))) :=
        mul_le_mul (hBG z hz1 hz2) (hBW z hz0 hz2) (norm_nonneg _) hBG0
    _ = _ := by ring

/-- Bound of `Φ_W` on `a ≤ Re z < c/2`, `|Im z| ≥ 1`. -/
theorem admissPhi_bound_left (hc : 1 ≤ c) (hW : StripM1 W) {a : ℝ} (ha : 0 < a) :
    ∃ B : ℝ, ∀ z : ℂ, a ≤ z.re → z.re < c / 2 → 1 ≤ |z.im| →
      ‖admissPhi c W z‖ ≤ B * (1 + |z.im|) ^ (-(2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  obtain ⟨BG, hBG0, hBG⟩ := admissG_bound_left hc0 ha
  obtain ⟨BW, hBW0, hBW⟩ := norm_W_arg_le hc hW
  refine ⟨BG * BW, fun z hz1 hz2 hy => ?_⟩
  have hz0 : 0 < z.re := by linarith
  unfold admissPhi
  rw [norm_mul]
  calc ‖admissG c z‖ * ‖W (1 - z / (c : ℂ))‖ ≤ BG * (BW * (1 + |z.im|) ^ (-(2 : ℝ))) :=
        mul_le_mul (hBG z hz1 hz2 hy) (hBW z hz0 (by linarith)) (norm_nonneg _) hBG0
    _ = _ := by ring

/-- **`Φ_W` satisfies the hypotheses of the Mellin hub** (`c ≥ 1`). -/
theorem admissPhi_mellinLiftData (hc : 1 ≤ c) (hW : StripM1 W) : MellinLiftData c (admissPhi c W) where
  hol := admissPhi_differentiableOn (by linarith) hW
  decay := by
    intro a b ha hab hb
    have hc0 : 0 < c := by linarith
    obtain ⟨M, hM⟩ := exists_bound_rect (admissPhi_differentiableOn hc0 hW).continuousOn ha hab hb
    obtain ⟨BR, hBR⟩ := admissPhi_bound_right hc hW
    obtain ⟨BL, hBL⟩ := admissPhi_bound_left hc hW ha
    refine ⟨4 * |M| + |BR| + |BL|, fun z hz1 hz2 => ?_⟩
    have hw0 : 0 ≤ (1 + |z.im|) ^ (-(2 : ℝ)) := by positivity
    rcases le_total |z.im| 1 with hy | hy
    · have h1 := hM z hz1 hz2 hy
      have h4 : (1 / 4 : ℝ) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) := by
        have : (2 : ℝ) ^ (-(2 : ℝ)) ≤ (1 + |z.im|) ^ (-(2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg z.im]) (by linarith) (by norm_num)
        have e : (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 := by
          rw [Real.rpow_neg (by norm_num)]; norm_num
        rwa [e] at this
      have := le_abs_self M
      nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
    · rcases le_or_gt (c / 2) z.re with hr | hr
      · have h1 := hBR z hr (hz2.trans hb.le)
        have : BR * (1 + |z.im|) ^ (-(2 : ℝ)) ≤ |BR| * (1 + |z.im|) ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hw0
        nlinarith [abs_nonneg M, abs_nonneg BR, abs_nonneg BL]
      · have h1 := hBL z hz1 hr hy
        have : BL * (1 + |z.im|) ^ (-(2 : ℝ)) ≤ |BL| * (1 + |z.im|) ^ (-(2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hw0
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

end Phi

section Vert

variable {c : ℝ} {W : ℂ → ℂ}

/-- The lift along `Re z = c` equals the lift along `Re z = c/2` (the contour shift to the edge). -/
theorem mellinInv_admissPhi_edge (hc : 1 ≤ c) (hW : StripM1 W) {Δ : ℝ} (hΔ : 0 < Δ) :
    mellinInv c (admissPhi c W) Δ = mellinInv (c / 2) (admissPhi c W) Δ := by
  have hc0 : 0 < c := by linarith
  obtain ⟨B0, hB0⟩ := admissPhi_bound_right hc hW
  have hB : ∀ z : ℂ, c / 2 ≤ z.re → z.re ≤ c → ‖admissPhi c W z‖ ≤ |B0| * (1 + |z.im|) ^ (-(2 : ℝ)) :=
    fun z h1 h2 => (hB0 z h1 h2).trans (mul_le_mul_of_nonneg_right (le_abs_self B0) (by positivity))
  have hΔ0 : (Δ : ℂ) ≠ 0 := by exact_mod_cast hΔ.ne'
  set H : ℂ → ℂ := fun z => (Δ : ℂ) ^ (-z) • admissPhi c W z with hH
  have hcont : ContinuousOn H {w : ℂ | c / 2 ≤ w.re ∧ w.re ≤ c} :=
    (Continuous.const_cpow continuous_neg (Or.inl hΔ0)).continuousOn.smul
      ((admissPhi_continuousOn_edge hc0 hW).mono fun w hw => ⟨by linarith [hw.1], hw.2⟩)
  have hd : DifferentiableOn ℂ H {w : ℂ | c / 2 < w.re ∧ w.re < c} :=
    DifferentiableOn.smul (fun w _ => ((differentiableAt_id.neg).const_cpow (Or.inl hΔ0)).differentiableWithinAt)
      ((admissPhi_differentiableOn hc0 hW).mono fun w hw => ⟨by linarith [hw.1], hw.2⟩)
  have key := CohnElkies.strip_shift (H := H) (a := c / 2) (b := c) (by linarith) hcont hd
    (integrable_weight_two ((Δ ^ (-(c / 2)) + Δ ^ (-c)) * |B0|))
    (fun w hw1 hw2 => by
      have h1 := hB w hw1 hw2
      have h2 := rpow_neg_le_sum hΔ hw1 hw2
      simp only [hH, norm_smul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hΔ]
      simp only [Complex.neg_re]
      calc Δ ^ (-w.re) * ‖admissPhi c W w‖ ≤ (Δ ^ (-(c / 2)) + Δ ^ (-c)) * (|B0| * (1 + |w.im|) ^ (-(2 : ℝ))) :=
            mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
        _ = _ := by ring)
    (tendsto_weight_two_atTop _) (tendsto_weight_two_atBot _)
  unfold mellinInv
  congr 1


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

/-- **Vertical representation** (`uct:vert-rep`, `mat:T7`(b)): for `0 ≤ σ < 1` and `ξ > 0`,
`(f_W ρ₀)(cξ) = (2πξ)⁻¹ ∫ K₀(σ + iτ, ξ) W̃(σ + iτ) dτ`. -/
theorem admiss_vert_rep (hc : 1 ≤ c) (hW : StripM1 W) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) {ξ : ℝ} (hξ : 0 < ξ) :
    (((hankelRho0 c (c * ξ) * admissLift c W (c * ξ) : ℝ)) : ℂ) =
      ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
        ∫ τ : ℝ, mellinK0 c ((σ : ℂ) + (τ : ℂ) * Complex.I) ξ * W ((σ : ℂ) + (τ : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hΦ := admissPhi_mellinLiftData hc hW
  have hΔ : 0 < c * ξ := mul_pos hc0 hξ
  set Δ := c * ξ with hΔdef
  set x : ℝ := c * (1 - σ) with hxdef
  have hx0 : 0 < x := mul_pos hc0 (by linarith)
  have hxc : x ≤ c := by rw [hxdef]; nlinarith
  -- the lift along `Re z = x`
  have e1 : (admissLift c W Δ : ℂ) = mellinInv x (admissPhi c W) Δ := by
    by_cases hσ : 0 < σ
    · have hlt : x < c := by rw [hxdef]; nlinarith
      exact ofReal_liftFun hΦ (x₀ := c / 2) (x := x) (by linarith) (by linarith) hx0 hlt hΔ
    · have hσ' : σ = 0 := le_antisymm (not_lt.mp hσ) hσ0
      have hx : x = c := by rw [hxdef, hσ']; ring
      rw [hx, mellinInv_admissPhi_edge hc hW hΔ]
      exact ofReal_liftFun hΦ (x₀ := c / 2) (x := c / 2) (by linarith) (by linarith) (by linarith) (by linarith) hΔ
  -- the integrand
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
  -- constants
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

end Vert

end FormalResearch.SignUncertainty

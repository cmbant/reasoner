module

public import FormalResearch.ModularBootstrap.FiveTerm.OuterS4b

/-!
# FIVE-S, S3 (step 1a): `ΔΦ_δ` is holomorphic on the whole open strip `0 < Im b < 1`

Extends `outerS4b` (which proved holomorphy on the middle band `|Im b - 1/2| < 1/4`) to the full open strip
`imStrip = {b : ℂ | 0 < b.im ∧ b.im < 1}` for `δ ∈ (0, 1/4)`, with locally uniform bounds on
`stripEps ε = {b : ℂ | ε < b.im ∧ b.im < 1 - ε}` (`0 < ε < 1/2`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

/-- The sub-strip `ε < Im b < 1 - ε`. -/
def stripEps (ε : ℝ) : Set ℂ := {b : ℂ | ε < b.im ∧ b.im < 1 - ε}

lemma isOpen_stripEps (ε : ℝ) : IsOpen (stripEps ε) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter (isOpen_lt Complex.continuous_im continuous_const)

lemma stripEps_subset_imStrip {ε : ℝ} (hε : 0 < ε) : stripEps ε ⊆ imStrip := fun _ hb =>
  ⟨by linarith [hb.1], by linarith [hb.2]⟩

private lemma sin_ge_sin_eps {θ α : ℝ} (hα0 : 0 < α)
    (h1 : α < θ) (h2 : θ < π - α) : Real.sin α ≤ Real.sin θ := by
  have hpi := Real.pi_pos
  rcases le_total θ (π / 2) with h | h
  · exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, h⟩ h1.le
  · rw [← Real.sin_pi_sub θ]
    exact Real.strictMonoOn_sin.monotoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)

lemma norm_sinh_ge_of_stripEps {ε y : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {b : ℂ} (hb : b ∈ stripEps ε) :
    Real.sin (π * ε) ≤ ‖Complex.sinh ((π : ℂ) * (b - y))‖ ∧
    Real.sin (π * ε) ≤ ‖Complex.sinh ((π : ℂ) * (b + y))‖ := by
  have hpi := Real.pi_pos
  have hs : Real.sin (π * ε) ≤ Real.sin (π * b.im) :=
    sin_ge_sin_eps (by positivity) (by nlinarith [hb.1]) (by nlinarith [hb.2])
  have hs0 : 0 < Real.sin (π * ε) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have key : ∀ w : ℂ, w.im = π * b.im → Real.sin (π * ε) ≤ ‖Complex.sinh w‖ := by
    intro w hw
    have h1 := norm_sinh_sq w
    rw [hw] at h1
    have hsin : Real.sin (π * ε) ^ 2 ≤ Real.sin (π * b.im) ^ 2 :=
      pow_le_pow_left₀ hs0.le hs 2
    have hn := norm_nonneg (Complex.sinh w)
    nlinarith [sq_nonneg (Real.sinh w.re)]
  exact ⟨key _ (by simp), key _ (by simp)⟩

lemma norm_phiYDeriv_le_of_stripEps {ε y : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {b : ℂ} (hb : b ∈ stripEps ε) :
    ‖phiYDeriv y b‖ ≤ 2 * π / Real.sin (π * ε) := by
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sin (π * ε) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  obtain ⟨a1, a2⟩ := norm_sinh_ge_of_stripEps hε0 hε1 hb (y := y)
  unfold phiYDeriv
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  have h1 : ‖1 / Complex.sinh ((π : ℂ) * (b - y))‖ ≤ 1 / Real.sin (π * ε) := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left zero_le_one hs0 a1
  have h2 : ‖1 / Complex.sinh ((π : ℂ) * (b + y))‖ ≤ 1 / Real.sin (π * ε) := by
    rw [norm_div, norm_one]
    exact div_le_div_of_nonneg_left zero_le_one hs0 a2
  have h3 := norm_add_le (1 / Complex.sinh ((π : ℂ) * (b - y))) (1 / Complex.sinh ((π : ℂ) * (b + y)))
  calc π * ‖1 / Complex.sinh ((π : ℂ) * (b - y)) + 1 / Complex.sinh ((π : ℂ) * (b + y))‖
      ≤ π * (1 / Real.sin (π * ε) + 1 / Real.sin (π * ε)) :=
        mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) hpi.le
    _ = 2 * π / Real.sin (π * ε) := by ring

lemma norm_phiY_le_of_stripEps {ε y : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {b : ℂ} (hb : b ∈ stripEps ε) :
    ‖phiY y b‖ ≤ 2 * (-Real.log (Real.sin (π * ε / 2))) + π := by
  have hbs := stripEps_subset_imStrip hε0 hb
  rw [phiY_eq hbs]
  have hpi := Real.pi_pos
  set s := Real.sin (π * ε / 2) with hsdef
  have hs0 : 0 < s := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
  have hs1 : s ≤ 1 := Real.sin_le_one _
  have key : ∀ w : ℂ, w.im = π * b.im / 2 → s ≤ ‖Complex.tanh w‖ ∧ ‖Complex.tanh w‖ ≤ s⁻¹ := by
    intro w hw
    have hv1 : s ≤ Real.sin w.im := by
      rw [hw]
      exact Real.strictMonoOn_sin.monotoneOn ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        ⟨by nlinarith [hb.1, Real.pi_pos], by nlinarith [hb.2, Real.pi_pos]⟩ (by nlinarith [hb.1])
    have hv2 : s ≤ Real.cos w.im := by
      rw [← Real.sin_pi_div_two_sub, hw]
      exact Real.strictMonoOn_sin.monotoneOn ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
        ⟨by nlinarith [hb.2, Real.pi_pos], by nlinarith [hb.1, Real.pi_pos]⟩ (by nlinarith [hb.2])
    have h2 := norm_tanh_sq w
    set S := Real.sinh w.re ^ 2
    have hS0 : 0 ≤ S := sq_nonneg _
    have hp : s ^ 2 ≤ Real.sin w.im ^ 2 := pow_le_pow_left₀ hs0.le hv1 2
    have hq : s ^ 2 ≤ Real.cos w.im ^ 2 := pow_le_pow_left₀ hs0.le hv2 2
    have hc1 : Real.cos w.im ^ 2 ≤ 1 := Real.cos_sq_le_one _
    have hs1' : Real.sin w.im ^ 2 ≤ 1 := Real.sin_sq_le_one _
    have hd : 0 < S + Real.cos w.im ^ 2 := by linarith [sq_pos_of_pos hs0]
    have hs2_le1 : s ^ 2 ≤ 1 := pow_le_one₀ hs0.le hs1
    have hn := norm_nonneg (Complex.tanh w)
    have lo : s ^ 2 ≤ ‖Complex.tanh w‖ ^ 2 := by
      rw [h2, le_div_iff₀ hd]
      have : s ^ 2 * S ≤ S := mul_le_of_le_one_left hS0 hs2_le1
      have : s ^ 2 * Real.cos w.im ^ 2 ≤ s ^ 2 := mul_le_of_le_one_right (sq_nonneg s) hc1
      linarith
    have hi : ‖Complex.tanh w‖ ^ 2 ≤ s⁻¹ ^ 2 := by
      rw [h2, div_le_iff₀ hd, inv_pow]
      have hA : S ≤ (s ^ 2)⁻¹ * S := le_mul_of_one_le_left hS0 ((one_le_inv₀ (sq_pos_of_pos hs0)).mpr hs2_le1)
      have hB : Real.sin w.im ^ 2 ≤ (s ^ 2)⁻¹ * Real.cos w.im ^ 2 := by
        rw [inv_mul_eq_div, le_div_iff₀ (sq_pos_of_pos hs0)]
        nlinarith
      nlinarith
    constructor
    · exact le_of_pow_le_pow_left₀ (by norm_num) hn lo
    · exact le_of_pow_le_pow_left₀ (by norm_num) (inv_nonneg.mpr hs0.le) hi
  obtain ⟨l1, u1⟩ := key _ (im_w₁ y b)
  obtain ⟨l2, u2⟩ := key _ (im_w₂ y b)
  have hT1 : s ^ 2 ≤ ‖-(Tcx y b)‖ := by
    rw [norm_neg]; unfold Tcx; rw [norm_mul, sq]
    exact mul_le_mul l1 l2 hs0.le (norm_nonneg _)
  have hT2 : ‖-(Tcx y b)‖ ≤ (s ^ 2)⁻¹ := by
    rw [norm_neg]; unfold Tcx; rw [norm_mul, sq, mul_inv]
    exact mul_le_mul u1 u2 (norm_nonneg _) (inv_nonneg.mpr hs0.le)
  have hs2p : 0 < s ^ 2 := sq_pos_of_pos hs0
  have hlog : |Real.log ‖-(Tcx y b)‖| ≤ 2 * (-Real.log s) := by
    rw [abs_le]
    have hlog_eq : Real.log (s ^ 2) = 2 * Real.log s := Real.log_pow s 2
    constructor
    · have := Real.log_le_log hs2p hT1
      linarith
    · have := Real.log_le_log (lt_of_lt_of_le hs2p hT1) hT2
      rw [Real.log_inv] at this
      linarith
  have harg := Complex.abs_arg_le_pi (-(Tcx y b))
  calc ‖Complex.log (-(Tcx y b))‖
      = ‖((Real.log ‖-(Tcx y b)‖ : ℝ) : ℂ) + ((Complex.arg (-(Tcx y b)) : ℝ) : ℂ) * Complex.I‖ := rfl
    _ ≤ ‖((Real.log ‖-(Tcx y b)‖ : ℝ) : ℂ)‖ + ‖((Complex.arg (-(Tcx y b)) : ℝ) : ℂ) * Complex.I‖ := norm_add_le _ _
    _ ≤ 2 * (-Real.log s) + π := by
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
      linarith

/-- Differentiation under the integral on `stripEps ε`. -/
lemma hasDerivAt_DeltaPhi_stripEps {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) {b : ℂ} (hb : b ∈ stripEps ε) :
    HasDerivAt (DeltaPhi δ)
      ((1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv y b) b := by
  have hg := integrableOn_dphi_deriv hδ0 hδ1
  set K0 := 2 * (-Real.log (Real.sin (π * ε / 2))) + π
  set K1 := 2 * π / Real.sin (π * ε)
  have hgc : AEStronglyMeasurable (fun y => ((deriv (dphi δ) y : ℝ) : ℂ)) (volume.restrict (Ioi xiStar)) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hg.aestronglyMeasurable
  have hnorm : ∀ (Q : ℝ → ℂ) (K : ℝ), (∀ y, ‖Q y‖ ≤ K) →
      ∀ y, ‖((deriv (dphi δ) y : ℝ) : ℂ) * Q y‖ ≤ ‖deriv (dphi δ) y‖ * K := by
    intro Q K hQ y
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (hQ y) (norm_nonneg _)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun y => ‖deriv (dphi δ) y‖ * K1)
    (F := fun z y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y z)
    (F' := fun z y => ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv y z)
    (μ := volume.restrict (Ioi xiStar)) (s := stripEps ε)
    ((isOpen_stripEps ε).mem_nhds hb) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact hd.const_mul (1 / (π : ℂ))
  · have hev : ∀ᶠ z in 𝓝 b, z ∈ stripEps ε := (isOpen_stripEps ε).mem_nhds hb
    exact hev.mono fun z hz => hgc.mul (continuous_phiY_y (stripEps_subset_imStrip hε0 hz)).aestronglyMeasurable
  · exact Integrable.mono' (hg.norm.mul_const K0)
      (hgc.mul (continuous_phiY_y (stripEps_subset_imStrip hε0 hb)).aestronglyMeasurable)
      (ae_of_all _ (hnorm (fun y => phiY y b) K0 (fun y => norm_phiY_le_of_stripEps hε0 hε1 hb)))
  · exact hgc.mul (continuous_phiYDeriv_y (stripEps_subset_imStrip hε0 hb)).aestronglyMeasurable
  · exact ae_of_all _ fun y z hz => hnorm (fun y => phiYDeriv y z) K1
      (fun y => norm_phiYDeriv_le_of_stripEps hε0 hε1 hz) y
  · exact hg.norm.mul_const K1
  · exact ae_of_all _ fun y z hz => (hasDerivAt_phiY (stripEps_subset_imStrip hε0 hz)).const_mul _

/-- **`ΔΦ_δ` on the whole open strip `0 < Im b < 1`** (`cts:smooth-env` (2)):
for `δ ∈ (0, 1/4)`, `DeltaPhi δ` is holomorphic on `imStrip` with derivative
`(1/π) ∫_{ξ_*}^∞ δφ_δ'(y) φ_y'(b) dy`. -/
theorem hasDerivAt_DeltaPhi_imStrip {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    {b : ℂ} (hb : b ∈ imStrip) :
    HasDerivAt (DeltaPhi δ)
      ((1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiYDeriv y b) b := by
  set ε := min (b.im / 2) ((1 - b.im) / 2)
  have hε0 : 0 < ε := lt_min (by linarith [hb.1]) (by linarith [hb.2])
  have hε1 : ε < 1 / 2 := by
    have : ε ≤ (b.im / 2 + (1 - b.im) / 2) / 2 := by
      have h1 : ε ≤ b.im / 2 := min_le_left _ _
      have h2 : ε ≤ (1 - b.im) / 2 := min_le_right _ _
      linarith
    linarith
  have hbε : b ∈ stripEps ε := ⟨by linarith [min_le_left (b.im / 2) ((1 - b.im) / 2), hb.1],
    by linarith [min_le_right (b.im / 2) ((1 - b.im) / 2), hb.2]⟩
  exact hasDerivAt_DeltaPhi_stripEps hδ0 hδ1 hε0 hε1 hbε

/-- **`ΔΦ_δ` is holomorphic on `0 < Im b < 1`** (`cts:smooth-env` (2)). -/
theorem differentiableOn_DeltaPhi_imStrip {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) :
    DifferentiableOn ℂ (DeltaPhi δ) imStrip := fun _ hb =>
  (hasDerivAt_DeltaPhi_imStrip hδ0 hδ1 hb).differentiableAt.differentiableWithinAt

/-- Locally uniform bound on `ΔΦ_δ` and `ΔΦ_δ'` on `ε < Im b < 1 - ε`. -/
theorem norm_DeltaPhi_le_of_stripEps {δ ε : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ stripEps ε, ‖DeltaPhi δ b‖ ≤ C ∧ ‖deriv (DeltaPhi δ) b‖ ≤ C := by
  have hg := integrableOn_dphi_deriv hδ0 hδ1
  set I := ∫ y in Ioi xiStar, ‖deriv (dphi δ) y‖
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _
  set K0 := 2 * (-Real.log (Real.sin (π * ε / 2))) + π
  set K1 := 2 * π / Real.sin (π * ε)
  have hK0 : 0 ≤ K0 := by
    have hpi := Real.pi_pos
    have hs0 : 0 < Real.sin (π * ε / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    have hs1 : Real.sin (π * ε / 2) ≤ 1 := Real.sin_le_one _
    have : Real.log (Real.sin (π * ε / 2)) ≤ 0 := Real.log_nonpos hs0.le hs1
    linarith
  have hK1 : 0 ≤ K1 := by
    have hpi := Real.pi_pos
    have hs0 : 0 < Real.sin (π * ε) := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    positivity
  refine ⟨I * (K0 + K1) / π + 1, by positivity, fun b hb => ?_⟩
  have hpi := Real.pi_pos
  constructor
  · show ‖(1 / (π : ℂ)) * ∫ y in Ioi xiStar, ((deriv (dphi δ) y : ℝ) : ℂ) * phiY y b‖ ≤ _
    rw [norm_inv_pi_mul, div_le_iff₀ hpi]
    have h1 := norm_int_le hg (Q := fun y => phiY y b) (K := K0)
      (fun y => norm_phiY_le_of_stripEps hε0 hε1 hb)
    have h2 : I * K0 ≤ I * (K0 + K1) := mul_le_mul_of_nonneg_left (by linarith) hI0
    have h3 : (I * (K0 + K1) / π + 1) * π = I * (K0 + K1) + π := by field_simp
    linarith
  · rw [(hasDerivAt_DeltaPhi_stripEps hδ0 hδ1 hε0 hε1 hb).deriv]
    rw [norm_inv_pi_mul, div_le_iff₀ hpi]
    have h1 := norm_int_le hg (Q := fun y => phiYDeriv y b) (K := K1)
      (fun y => norm_phiYDeriv_le_of_stripEps hε0 hε1 hb)
    have h2 : I * K1 ≤ I * (K0 + K1) := mul_le_mul_of_nonneg_left (by linarith) hI0
    have h3 : (I * (K0 + K1) / π + 1) * π = I * (K0 + K1) + π := by field_simp
    linarith

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.hasDerivAt_DeltaPhi_imStrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_DeltaPhi_imStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.differentiableOn_DeltaPhi_imStrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_DeltaPhi_imStrip

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.OuterStrip.norm_DeltaPhi_le_of_stripEps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_DeltaPhi_le_of_stripEps

end FormalResearch.ModularBootstrap.FiveTerm.OuterStrip

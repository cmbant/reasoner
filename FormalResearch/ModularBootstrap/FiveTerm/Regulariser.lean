module

public import FormalResearch.ModularBootstrap.FiveTerm.CombMinimum

/-!
# The regulariser `m_ε = √((1-z)/(1-(1-ε)z))` (FIVE-0; `ctu:common-functional` (3))

Source: `CFT/modular_bootstrap/paper/constant_term_universality.tex`, Lemma ctu.2a (3).

`mEps ε z = exp(½(log(1-z) - log(1-(1-ε)z)))` (principal logarithms, so `m_ε = √((1-z)/(1-(1-ε)z))` on
`closure Ω ∖ {1}`).  This file proves the elementary properties needed to put `m_ε F_*` in `H_adm`:
`mEps_sq` (`m_ε² = (1-z)/(1-(1-ε)z)`), `re_mEps_pos`, holomorphy on the unit disc, continuity on
`closure Ω ∖ {1}`, real symmetry on `Ω`, the bound `‖m_ε‖² ≤ 2/ε` on `closure Ω ∖ {1}`, and the jet
`m_ε = 1 - (ε/2) z + O(z²)` (`mEps_jet`).  All proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `m_ε(z) = √((1-z)/(1-(1-ε)z))`, via principal logarithms. -/
noncomputable def mEps (ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((1 / 2 : ℂ) * (Complex.log (1 - z) - Complex.log (1 - ((1 - ε : ℝ) : ℂ) * z)))

section

variable {ε : ℝ}

/-- A generic jet: a function holomorphic on the unit disc has a second-order Taylor bound at `0`. -/
lemma jet_of_diff {h : ℂ → ℂ} (hd : DifferentiableOn ℂ h (ball (0 : ℂ) 1)) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → ‖h z - h 0 - deriv h 0 * z‖ ≤ C * ‖z‖ ^ 2 := by
  have hgd : DifferentiableOn ℂ (dslope h 0) (ball (0 : ℂ) 1) :=
    (Complex.differentiableOn_dslope (isOpen_ball.mem_nhds (mem_ball_self one_pos))).mpr hd
  have hcd : ContDiffAt ℂ 1 (dslope h 0) 0 :=
    (hgd.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))
  obtain ⟨K, t, ht, hK⟩ := hcd.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp ht
  refine ⟨K, r, hr, fun z hz => ?_⟩
  by_cases hz0 : z = 0
  · subst hz0; simp
  have hzt : z ∈ t := hrt (by simpa using hz)
  have h0t : (0 : ℂ) ∈ t := hrt (by simpa using hr)
  have hL := hK.norm_sub_le hzt h0t
  have e1 : dslope h 0 z = (h z - h 0) / z := by
    rw [dslope_of_ne _ hz0, slope_def_field, sub_zero]
  have e2 : dslope h 0 0 = deriv h 0 := dslope_same _ _
  have e3 : h z - h 0 - deriv h 0 * z = z * (dslope h 0 z - dslope h 0 0) := by
    rw [e1, e2]; field_simp
  rw [e3, norm_mul]
  have : ‖dslope h 0 z - dslope h 0 0‖ ≤ K * ‖z‖ := by
    simpa [dist_eq_norm] using hL
  calc ‖z‖ * ‖dslope h 0 z - dslope h 0 0‖ ≤ ‖z‖ * (K * ‖z‖) := by gcongr
    _ = K * ‖z‖ ^ 2 := by ring

lemma re_one_sub_pos {z : ℂ} (h1 : ‖z‖ ≤ 1) (hz1 : z ≠ 1) : 0 < (1 - z).re := by
  have h2 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith only [this, h1, norm_nonneg z]
  rw [Complex.sub_re, Complex.one_re]
  by_contra hcon
  have hre : 1 ≤ z.re := by linarith only [not_lt.mp hcon]
  have : z.im = 0 := by nlinarith only [h2, hre, sq_nonneg z.im]
  have hre1 : z.re = 1 := by nlinarith only [h2, hre, sq_nonneg z.im]
  exact hz1 (Complex.ext (by simpa using hre1) (by simpa using this))

lemma re_one_sub_mul_ge {z : ℂ} (h1 : ‖z‖ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ε ≤ (1 - ((1 - ε : ℝ) : ℂ) * z).re := by
  have hre : z.re ≤ 1 := le_trans (Complex.re_le_norm z) h1
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  nlinarith only [hre, hε0, hε1]

lemma one_sub_mem_slitPlane {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    1 - z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl (re_one_sub_pos hz hz1))

lemma one_sub_mul_mem_slitPlane {z : ℂ} (hz : ‖z‖ ≤ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    1 - ((1 - ε : ℝ) : ℂ) * z ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (lt_of_lt_of_le hε0 (re_one_sub_mul_ge hz hε0 hε1)))

lemma mEps_sq {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    mEps ε z ^ 2 = (1 - z) / (1 - ((1 - ε : ℝ) : ℂ) * z) := by
  have h1 : 1 - z ≠ 0 := (Complex.slitPlane_ne_zero (one_sub_mem_slitPlane hz hz1))
  have h2 : 1 - ((1 - ε : ℝ) : ℂ) * z ≠ 0 :=
    Complex.slitPlane_ne_zero (one_sub_mul_mem_slitPlane hz hε0 hε1)
  unfold mEps
  rw [← Complex.exp_nat_mul]
  push_cast
  rw [show (2 : ℂ) * (1 / 2 * (Complex.log (1 - z) - Complex.log (1 - ((1 : ℂ) - (ε : ℂ)) * z))) =
      Complex.log (1 - z) - Complex.log (1 - ((1 : ℂ) - (ε : ℂ)) * z) by ring]
  rw [Complex.exp_sub, Complex.exp_log h1]
  rw [Complex.exp_log (by simpa using h2)]

/-- `Re m_ε > 0` at points of `closure Ω ∖ {1}`. -/
lemma re_mEps_pos {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < (mEps ε z).re := by
  unfold mEps
  rw [Complex.exp_re]
  refine mul_pos (Real.exp_pos _) ?_
  have ha1 : |Complex.arg (1 - z)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (re_one_sub_pos hz hz1))
  have ha2 : |Complex.arg (1 - ((1 - ε : ℝ) : ℂ) * z)| < π / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (lt_of_lt_of_le hε0 (re_one_sub_mul_ge hz hε0 hε1)))
  have him : ((1 / 2 : ℂ) * (Complex.log (1 - z) - Complex.log (1 - ((1 - ε : ℝ) : ℂ) * z))).im =
      (Complex.arg (1 - z) - Complex.arg (1 - ((1 - ε : ℝ) : ℂ) * z)) / 2 := by
    simp [Complex.log_im]
    ring
  rw [him]
  apply Real.cos_pos_of_mem_Ioo
  rw [abs_lt] at ha1 ha2
  constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]

lemma differentiableAt_mEps {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    DifferentiableAt ℂ (mEps ε) z := by
  unfold mEps
  have h1 : DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 - w)) z :=
    DifferentiableAt.clog (by fun_prop) (one_sub_mem_slitPlane hz hz1)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => Complex.log (1 - ((1 - ε : ℝ) : ℂ) * w)) z :=
    DifferentiableAt.clog (by fun_prop) (one_sub_mul_mem_slitPlane hz hε0 hε1)
  exact ((h1.sub h2).const_mul _).cexp

lemma differentiableOn_mEps_ball (hε0 : 0 < ε) (hε1 : ε < 1) :
    DifferentiableOn ℂ (mEps ε) (ball (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa using hz
  have hz1 : z ≠ 1 := by intro h; rw [h] at hz'; simp at hz'
  exact (differentiableAt_mEps hz'.le hz1 hε0 hε1).differentiableWithinAt

lemma continuousOn_mEps (hε0 : 0 < ε) (hε1 : ε < 1) :
    ContinuousOn (mEps ε) (closure halfDisc \ {1}) := fun _ hz =>
  (differentiableAt_mEps (norm_closure_halfDisc_le hz.1) hz.2 hε0 hε1).continuousAt.continuousWithinAt

lemma mEps_conj {z : ℂ} (hz : z ∈ halfDisc) (hε0 : 0 < ε) (hε1 : ε < 1) :
    mEps ε (starRingEnd ℂ z) = starRingEnd ℂ (mEps ε z) := by
  have hz1 : ‖z‖ ≤ 1 := hz.1.le
  have hzn : z ≠ 1 := by intro h; rw [h] at hz; simp [halfDisc] at hz
  have a1 : (1 - z).arg ≠ π := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (re_one_sub_pos hz1 hzn))
    intro h; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
  have a2 : (1 - ((1 - ε : ℝ) : ℂ) * z).arg ≠ π := by
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr
      (Or.inl (lt_of_lt_of_le hε0 (re_one_sub_mul_ge hz1 hε0 hε1)))
    intro h; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]
  unfold mEps
  have e1 : (1 : ℂ) - starRingEnd ℂ z = starRingEnd ℂ (1 - z) := by simp
  have e2 : (1 : ℂ) - ((1 - ε : ℝ) : ℂ) * starRingEnd ℂ z =
      starRingEnd ℂ (1 - ((1 - ε : ℝ) : ℂ) * z) := by simp
  rw [e1, e2, Complex.log_conj _ a1, Complex.log_conj _ a2, ← Complex.exp_conj]
  simp [map_sub, map_mul, map_inv₀, map_ofNat]

/-- `‖m_ε‖² ≤ 2/ε` on `closure Ω ∖ {1}`. -/
lemma norm_mEps_sq_le {z : ℂ} (hz : z ∈ closure halfDisc) (hz1 : z ≠ 1) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ‖mEps ε z‖ ^ 2 ≤ 2 / ε := by
  have h1 := norm_closure_halfDisc_le hz
  have hsq := mEps_sq h1 hz1 hε0 hε1
  have h2 : ε ≤ ‖1 - ((1 - ε : ℝ) : ℂ) * z‖ :=
    le_trans (re_one_sub_mul_ge h1 hε0 hε1) (Complex.re_le_norm _)
  have h3 : ‖1 - z‖ ≤ 2 := by
    calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  rw [← norm_pow, hsq, norm_div, div_le_div_iff₀ (lt_of_lt_of_le hε0 h2) hε0]
  nlinarith only [h2, h3, hε0, norm_nonneg (1 - z)]

lemma mEps_zero (ε : ℝ) : mEps ε 0 = 1 := by simp [mEps]

lemma deriv_mEps_zero : deriv (mEps ε) 0 = ((-(ε / 2) : ℝ) : ℂ) := by
  have hd1 : HasDerivAt (fun w : ℂ => Complex.log (1 - w)) (-1 / (1 - 0)) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_sub (1 : ℂ)
    exact h1.clog (by simp)
  have hd2 : HasDerivAt (fun w : ℂ => Complex.log (1 - ((1 - ε : ℝ) : ℂ) * w))
      (-(((1 - ε : ℝ) : ℂ)) / (1 - ((1 - ε : ℝ) : ℂ) * 0)) 0 := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - ((1 - ε : ℝ) : ℂ) * w) (-((1 - ε : ℝ) : ℂ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul ((1 - ε : ℝ) : ℂ)).const_sub (1 : ℂ)
    exact h1.clog (by simp)
  have hd : HasDerivAt (mEps ε) (1 * ((1 / 2 : ℂ) * (-1 / (1 - 0) - (-(((1 - ε : ℝ) : ℂ)) / (1 - ((1 - ε : ℝ) : ℂ) * 0))))) 0 := by
    unfold mEps
    have := (((hd1.sub hd2).const_mul (1 / 2 : ℂ))).cexp
    simpa using this
  rw [hd.deriv]
  push_cast
  ring

/-- The jet `m_ε = 1 - (ε/2) z + O(z²)`. -/
lemma mEps_jet (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ C r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r →
      ‖mEps ε z - 1 - ((-(ε / 2) : ℝ) : ℂ) * z‖ ≤ C * ‖z‖ ^ 2 := by
  obtain ⟨C, r, hr, h⟩ := jet_of_diff (differentiableOn_mEps_ball hε0 hε1)
  refine ⟨C, r, hr, fun z hz => ?_⟩
  have := h z hz
  rwa [mEps_zero, deriv_mEps_zero] at this

end

end FormalResearch.ModularBootstrap.FiveTerm

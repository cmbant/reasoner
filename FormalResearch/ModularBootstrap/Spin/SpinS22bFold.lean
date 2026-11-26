module

public import FormalResearch.ModularBootstrap.Spin.SpinS22bPartA
public import FormalResearch.ModularBootstrap.PoissonJensen.LemmaPJAssembly
public import Mathlib.Analysis.Complex.Liouville

/-!
# Lemma S2.2′ (`spinnotes:S22b`), Parts (b) and (c): slit-strip fold estimate

Proves Parts (b) and (c) of **Lemma S2.2′** (`spinning_foundations.tex`, lines 250–302) and
assembles `theorem spinS22b : SpinS22b` (with `k = 1`, `κ = (4/9) √(2π)`, and explicit
`C, δ₀, n₀`) from `spinS22b_partA`, `spinS22b_log_master`, and `lemmaE_real`.
-/

@[expose] public section

open Real Complex MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Spin

open PoissonJensen

/-! ### Section 1: Damped rescaled diagonal continuation `H(w)` on `{|Im w| ≤ 1/2}` -/

/-- Rescaled diagonal continuation `g(w) = D_a G(σ w + λ d, σ w - λ d)` on `{|Im w| ≤ 1/2}`,
where `σ ∈ {-1, 1}` orients `ξ` to `[0, b_*)`. -/
private noncomputable def spinDiagC (a : ℝ) (Φ : ℝ × ℝ → ℝ) (σ d : ℝ) (w : ℂ) : ℂ :=
  spinDaC a Φ ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ))
    ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ))

/-- Damped rescaled diagonal continuation `H(w) = ((w + I) ^ 4)⁻¹ * spinDiagC a Φ σ d w`.
The polynomial damping factor `((w + I) ^ 4)⁻¹` is holomorphic and nonvanishing on
`{|Im w| ≤ 1/2}` and absorbs the `(1 + 4 (Re b_L)²)(1 + 4 (Re b_R)²)` growth from `norm_spinDaC_le`,
yielding a uniform constant bound on `{|Im w| ≤ 1/2}` independent of `a, n, d, Φ, w`. -/
private noncomputable def spinDampedDiag (a : ℝ) (Φ : ℝ × ℝ → ℝ) (σ d : ℝ) (w : ℂ) : ℂ :=
  ((w + I) ^ 4)⁻¹ * spinDiagC a Φ σ d w

private lemma add_I_ne_zero_of_im_le {w : ℂ} (hw : |w.im| ≤ 1 / 2) : w + I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  have := (abs_le.mp hw).1
  linarith

private lemma norm_inv_add_I_pow_four_le {w : ℂ} (hw : |w.im| ≤ 1 / 2) :
    ‖((w + I) ^ 4)⁻¹‖ ≤ 16 / (1 + w.re ^ 2) ^ 2 := by
  have h1 : (1 / 2 : ℝ) ≤ w.im + 1 := by linarith [(abs_le.mp hw).1]
  have hsq : (1 / 4 : ℝ) * (1 + w.re ^ 2) ≤ ‖w + I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.I_re, add_zero, Complex.add_im, Complex.I_im]
    nlinarith
  have hpos1 : 0 < (1 / 4 : ℝ) * (1 + w.re ^ 2) := by positivity
  have hpow : ((1 / 4 : ℝ) * (1 + w.re ^ 2)) ^ 2 ≤ (‖w + I‖ ^ 2) ^ 2 :=
    pow_le_pow_left₀ hpos1.le hsq 2
  have hpow4 : (1 / 16 : ℝ) * (1 + w.re ^ 2) ^ 2 ≤ ‖w + I‖ ^ 4 := by
    calc (1 / 16 : ℝ) * (1 + w.re ^ 2) ^ 2 = ((1 / 4 : ℝ) * (1 + w.re ^ 2)) ^ 2 := by ring
      _ ≤ (‖w + I‖ ^ 2) ^ 2 := hpow
      _ = ‖w + I‖ ^ 4 := by ring
  rw [norm_inv, norm_pow]
  have hpos4 : 0 < (1 / 16 : ℝ) * (1 + w.re ^ 2) ^ 2 := by positivity
  calc (‖w + I‖ ^ 4)⁻¹ ≤ ((1 / 16 : ℝ) * (1 + w.re ^ 2) ^ 2)⁻¹ :=
        inv_anti₀ hpos4 hpow4
    _ = 16 / (1 + w.re ^ 2) ^ 2 := by field_simp

private lemma norm_spinDampedDiag_le {a : ℝ} (ha : 39 / 12 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) (hM2 : spinM2 a Φ = 1)
    {σ d : ℝ} (hσ : |σ| = 1) (hd : |d| ≤ 3 * spinBStar a / 4)
    {w : ℂ} (hw : |w.im| ≤ 1 / 2) :
    ‖spinDampedDiag a Φ σ d w‖ ≤ 17424 := by
  have ha2 : 2 ≤ a := by linarith
  have hγ_pos : 0 < spinGamma a := by
    unfold spinGamma; exact Real.sqrt_pos.mpr (by linarith [(div_lt_one (by linarith : 0 < a)).mpr (by linarith : 2 < a)])
  have hlam_mul_d : |spinLambda a * d| ≤ 5 / 4 := by
    have hγ_ge : (0.6 : ℝ) ≤ spinGamma a := by
      unfold spinGamma
      have hdiv : 2 / a ≤ 2 / (39 / 12 : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha
      calc (0.6 : ℝ) = Real.sqrt (0.6 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt (by linarith)
    have hlam_le : spinLambda a ≤ 5 / 3 := by
      unfold spinLambda
      rw [inv_le_comm₀ hγ_pos (by norm_num)]
      linarith
    have hb_le : spinBStar a ≤ 1 := by
      unfold spinBStar
      have hγ_le1 : spinGamma a ≤ 1 := by
        unfold spinGamma
        calc Real.sqrt (1 - 2 / a) ≤ Real.sqrt 1 :=
              Real.sqrt_le_sqrt (by linarith [div_pos two_pos (by linarith : 0 < a)])
          _ = 1 := Real.sqrt_one
      nlinarith [xiStar_lt_one, xiStar_pos]
    have hlam_pos : 0 < spinLambda a := by unfold spinLambda; positivity
    rw [abs_mul, abs_of_pos hlam_pos]
    nlinarith [abs_nonneg d]
  have him_add : |((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).im| ≤ 1 / 2 := by
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    rw [abs_mul, hσ, one_mul]; exact hw
  have him_sub : |((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).im| ≤ 1 / 2 := by
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, sub_zero]
    rw [abs_mul, hσ, one_mul]; exact hw
  have hre_bound : ∀ sgn : ℝ, |sgn| = 1 →
      1 + 4 * (σ * w.re + sgn * (spinLambda a * d)) ^ 2 ≤ 33 * (1 + w.re ^ 2) := by
    intro sgn hsgn
    have h1 : (σ * w.re + sgn * (spinLambda a * d)) ^ 2 ≤
        2 * (σ * w.re) ^ 2 + 2 * (sgn * (spinLambda a * d)) ^ 2 := by
      nlinarith [sq_nonneg (σ * w.re - sgn * (spinLambda a * d))]
    have h2 : (σ * w.re) ^ 2 = w.re ^ 2 := by
      rw [mul_pow, ← sq_abs σ, hσ]; ring
    have h3 : (sgn * (spinLambda a * d)) ^ 2 ≤ 2 := by
      rw [mul_pow, ← sq_abs sgn, hsgn, one_pow, one_mul, ← sq_abs (spinLambda a * d)]
      nlinarith [abs_nonneg (spinLambda a * d)]
    nlinarith
  have hda := norm_spinDaC_le ha2 hΦ him_add him_sub
  rw [hM2, mul_one] at hda
  have hre1 : ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).re = σ * w.re + 1 * (spinLambda a * d) := by
    simp [Complex.mul_re]
  have hre2 : ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).re = σ * w.re + (-1) * (spinLambda a * d) := by
    simp [Complex.mul_re]; ring
  have hb1 : 1 + 4 * ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ 33 * (1 + w.re ^ 2) := by
    rw [hre1]; exact hre_bound 1 (by norm_num)
  have hb2 : 1 + 4 * ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ 33 * (1 + w.re ^ 2) := by
    rw [hre2]; exact hre_bound (-1) (by norm_num)
  have hg_le : ‖spinDiagC a Φ σ d w‖ ≤ 1089 * (1 + w.re ^ 2) ^ 2 := by
    unfold spinDiagC
    calc ‖spinDaC a Φ _ _‖
        ≤ (1 + 4 * ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).re ^ 2) *
            (1 + 4 * ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).re ^ 2) := hda
      _ ≤ (33 * (1 + w.re ^ 2)) * (33 * (1 + w.re ^ 2)) :=
          mul_le_mul hb1 hb2 (by positivity) (by positivity)
      _ = 1089 * (1 + w.re ^ 2) ^ 2 := by ring
  unfold spinDampedDiag
  rw [norm_mul]
  calc ‖((w + I) ^ 4)⁻¹‖ * ‖spinDiagC a Φ σ d w‖
      ≤ (16 / (1 + w.re ^ 2) ^ 2) * (1089 * (1 + w.re ^ 2) ^ 2) :=
        mul_le_mul (norm_inv_add_I_pow_four_le hw) hg_le (norm_nonneg _) (by positivity)
    _ = 17424 := by
        have hne : (1 + w.re ^ 2) ^ 2 ≠ 0 := by positivity
        field_simp [hne]; ring

private lemma continuousOn_spinDiagC {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {σ d : ℝ} (hσ : |σ| = 1) :
    ContinuousOn (spinDiagC a Φ σ d) {w : ℂ | |w.im| ≤ 1 / 2} := by
  intro w₀ hw₀
  let S_loc : Set ℂ := {w : ℂ | |w.im| ≤ 1 / 2} ∩ closedBall w₀ 1
  have hS_nhds : S_loc ∈ 𝓝[{w : ℂ | |w.im| ≤ 1 / 2}] w₀ :=
    inter_mem_nhdsWithin _ (closedBall_mem_nhds w₀ zero_lt_one)
  suffices hcont : ContinuousOn (spinDiagC a Φ σ d) S_loc from
    (hcont.continuousWithinAt ⟨hw₀, mem_closedBall_self zero_le_one⟩).mono_of_mem_nhdsWithin hS_nhds
  let R : ℝ := |w₀.re| + 1 + |spinLambda a * d|
  let M_loc : ℝ := (1 + 4 * R ^ 2) ^ 2
  have hfun : spinDiagC a Φ σ d = fun w =>
      -(∫ p : ℝ × ℝ, (Φ p : ℂ) *
        spinWa a p.1 ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)) *
        spinWa a p.2 ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ))) := by
    ext w; unfold spinDiagC; exact spinDaC_eq_spinWa a Φ _ _
  rw [hfun]
  refine ContinuousOn.neg ?_
  refine continuousOn_of_dominated (bound := fun p : ℝ × ℝ =>
      M_loc * (|Φ p| * spinV1 a p.1 * spinV1 a p.2)) ?_ ?_ (hΦ.int_M2.const_mul M_loc) ?_
  · intro w _
    have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have h2 : Continuous (fun p : ℝ × ℝ =>
        spinWa a p.1 ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ))) := by unfold spinWa; fun_prop
    have h3 : Continuous (fun p : ℝ × ℝ =>
        spinWa a p.2 ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ))) := by unfold spinWa; fun_prop
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  · intro w hw
    refine Eventually.of_forall fun p => ?_
    have him1 : |((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).im| ≤ 1 / 2 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      rw [abs_mul, hσ, one_mul]; exact hw.1
    have him2 : |((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).im| ≤ 1 / 2 := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero]
      rw [abs_mul, hσ, one_mul]; exact hw.1
    have hw_re : |w.re| ≤ |w₀.re| + 1 := by
      have hdist : |w.re - w₀.re| ≤ 1 := by
        have := (Complex.abs_re_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw.2)
        simpa using this
      linarith [abs_sub_abs_le_abs_sub w.re w₀.re]
    have hre1 : |((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).re| ≤ R := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      calc |σ * w.re + spinLambda a * d| ≤ |σ * w.re| + |spinLambda a * d| := abs_add_le _ _
        _ = |w.re| + |spinLambda a * d| := by rw [abs_mul, hσ, one_mul]
        _ ≤ R := by dsimp [R]; linarith
    have hre2 : |((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).re| ≤ R := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      calc |σ * w.re - spinLambda a * d| ≤ |σ * w.re| + |spinLambda a * d| := abs_sub _ _
        _ = |w.re| + |spinLambda a * d| := by rw [abs_mul, hσ, one_mul]
        _ ≤ R := by dsimp [R]; linarith
    have hb1 : 1 + 4 * ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ 1 + 4 * R ^ 2 := by
      have : ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
      linarith
    have hb2 : 1 + 4 * ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ 1 + 4 * R ^ 2 := by
      have : ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
      linarith
    have hw1 := (norm_spinWa_le ha p.1 him1).trans (mul_le_mul_of_nonneg_right hb1 (spinV1_nonneg ha p.1))
    have hw2 := (norm_spinWa_le ha p.2 him2).trans (mul_le_mul_of_nonneg_right hb2 (spinV1_nonneg ha p.2))
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |Φ p| * ‖spinWa a p.1 _‖ * ‖spinWa a p.2 _‖
        ≤ |Φ p| * ((1 + 4 * R ^ 2) * spinV1 a p.1) * ((1 + 4 * R ^ 2) * spinV1 a p.2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2 (norm_nonneg _)
            (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (spinV1_nonneg ha p.1)))
      _ = M_loc * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by dsimp [M_loc]; ring
  · refine Eventually.of_forall fun p => ?_
    have hcont_p : Continuous (fun w : ℂ => (Φ p : ℂ) *
        spinWa a p.1 ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)) *
        spinWa a p.2 ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ))) := by
      unfold spinWa; fun_prop
    exact hcont_p.continuousOn

private lemma differentiableOn_spinDiagC {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {σ d : ℝ} (hσ : |σ| = 1) :
    DifferentiableOn ℂ (spinDiagC a Φ σ d) {w : ℂ | |w.im| < 1 / 2} := by
  intro w₀ hw₀
  have hw₀_im : |w₀.im| < 1 / 2 := hw₀
  set ε : ℝ := (1 / 2 - |w₀.im|) / 4
  have hε_pos : 0 < ε := by dsimp [ε]; linarith
  let R : ℝ := |w₀.re| + 1 + |spinLambda a * d|
  let M_loc : ℝ := (1 + 4 * R ^ 2) ^ 2
  let F : ℂ → ℝ × ℝ → ℂ := fun w p =>
    (Φ p : ℂ) * spinWa a p.1 ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ)) *
      spinWa a p.2 ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ))
  have hF_diff : ∀ p : ℝ × ℝ, Differentiable ℂ (fun w => F w p) := by
    intro p; dsimp [F]; unfold spinWa; fun_prop
  have hF_bd_closed : ∀ p : ℝ × ℝ, ∀ z ∈ closedBall w₀ (2 * ε),
      ‖F z p‖ ≤ M_loc * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    intro p z hz
    have hdist : ‖z - w₀‖ ≤ 2 * ε := mem_closedBall_iff_norm.mp hz
    have h2ε_le : 2 * ε ≤ 1 / 2 - |w₀.im| := by dsimp [ε]; linarith
    have h2ε_le1 : 2 * ε ≤ 1 := by dsimp [ε]; linarith [abs_nonneg w₀.im]
    have hz_im : |z.im| ≤ 1 / 2 := by
      have him : |z.im - w₀.im| ≤ 2 * ε := by
        simpa using (Complex.abs_im_le_norm (z - w₀)).trans hdist
      linarith [abs_sub_abs_le_abs_sub z.im w₀.im]
    have hz_re : |z.re| ≤ |w₀.re| + 1 := by
      have hre : |z.re - w₀.re| ≤ 1 := by
        simpa using (Complex.abs_re_le_norm (z - w₀)).trans (hdist.trans h2ε_le1)
      linarith [abs_sub_abs_le_abs_sub z.re w₀.re]
    have him1 : |((σ : ℂ) * z + ((spinLambda a * d : ℝ) : ℂ)).im| ≤ 1 / 2 := by
      simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero]
      rw [abs_mul, hσ, one_mul]; exact hz_im
    have him2 : |((σ : ℂ) * z - ((spinLambda a * d : ℝ) : ℂ)).im| ≤ 1 / 2 := by
      simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, sub_zero]
      rw [abs_mul, hσ, one_mul]; exact hz_im
    have hre1 : |((σ : ℂ) * z + ((spinLambda a * d : ℝ) : ℂ)).re| ≤ R := by
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      calc |σ * z.re + spinLambda a * d| ≤ |σ * z.re| + |spinLambda a * d| := abs_add_le _ _
        _ = |z.re| + |spinLambda a * d| := by rw [abs_mul, hσ, one_mul]
        _ ≤ R := by dsimp [R]; linarith
    have hre2 : |((σ : ℂ) * z - ((spinLambda a * d : ℝ) : ℂ)).re| ≤ R := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      calc |σ * z.re - spinLambda a * d| ≤ |σ * z.re| + |spinLambda a * d| := abs_sub _ _
        _ = |z.re| + |spinLambda a * d| := by rw [abs_mul, hσ, one_mul]
        _ ≤ R := by dsimp [R]; linarith
    have hb1 : 1 + 4 * ((σ : ℂ) * z + ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ 1 + 4 * R ^ 2 := by
      have : ((σ : ℂ) * z + ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre1 2
      linarith
    have hb2 : 1 + 4 * ((σ : ℂ) * z - ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ 1 + 4 * R ^ 2 := by
      have : ((σ : ℂ) * z - ((spinLambda a * d : ℝ) : ℂ)).re ^ 2 ≤ R ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hre2 2
      linarith
    have hw1 := (norm_spinWa_le ha p.1 him1).trans (mul_le_mul_of_nonneg_right hb1 (spinV1_nonneg ha p.1))
    have hw2 := (norm_spinWa_le ha p.2 him2).trans (mul_le_mul_of_nonneg_right hb2 (spinV1_nonneg ha p.2))
    dsimp [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |Φ p| * ‖spinWa a p.1 _‖ * ‖spinWa a p.2 _‖
        ≤ |Φ p| * ((1 + 4 * R ^ 2) * spinV1 a p.1) * ((1 + 4 * R ^ 2) * spinV1 a p.2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)) hw2 (norm_nonneg _)
            (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (spinV1_nonneg ha p.1)))
      _ = M_loc * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by dsimp [M_loc]; ring
  have hderiv_bd : ∀ p : ℝ × ℝ, ∀ w ∈ ball w₀ ε,
      ‖deriv (fun z => F z p) w‖ ≤ (M_loc / ε) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
    intro p w hw
    have hsphere : ∀ z ∈ sphere w ε,
        ‖F z p‖ ≤ M_loc * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by
      intro z hz
      refine hF_bd_closed p z ?_
      rw [mem_closedBall]
      have h1 : dist z w = ε := mem_sphere.mp hz
      have h2 : dist w w₀ < ε := mem_ball.mp hw
      calc dist z w₀ ≤ dist z w + dist w w₀ := dist_triangle z w w₀
        _ ≤ 2 * ε := by linarith
    have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε_pos
      (hF_diff p).diffContOnCl hsphere
    calc ‖deriv (fun z => F z p) w‖
        ≤ M_loc * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) / ε := hC
      _ = (M_loc / ε) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2) := by ring
  have hmeas_F : ∀ w : ℂ, AEStronglyMeasurable (F w) volume := by
    intro w
    have h1 : Continuous (fun p : ℝ × ℝ => (Φ p : ℂ)) := Complex.continuous_ofReal.comp hΦ.cont
    have h2 : Continuous (fun p : ℝ × ℝ =>
        spinWa a p.1 ((σ : ℂ) * w + ((spinLambda a * d : ℝ) : ℂ))) := by unfold spinWa; fun_prop
    have h3 : Continuous (fun p : ℝ × ℝ =>
        spinWa a p.2 ((σ : ℂ) * w - ((spinLambda a * d : ℝ) : ℂ))) := by unfold spinWa; fun_prop
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have hint_w₀ : Integrable (F w₀) volume := by
    refine (hΦ.int_M2.const_mul M_loc).mono' (hmeas_F w₀) (Eventually.of_forall fun p => ?_)
    exact hF_bd_closed p w₀ (mem_closedBall_self (by positivity))
  have hmeas_F' : AEStronglyMeasurable (fun p : ℝ × ℝ => deriv (fun z => F z p) w₀) volume := by
    have hseq : ∀ n : ℕ, AEStronglyMeasurable
        (fun p : ℝ × ℝ => (((n + 1 : ℕ) : ℂ) : ℂ) *
          (F (w₀ + (((n + 1 : ℕ) : ℂ)⁻¹)) p - F w₀ p)) volume :=
      fun n => ((hmeas_F _).sub (hmeas_F _)).const_mul _
    refine aestronglyMeasurable_of_tendsto_ae atTop hseq (Eventually.of_forall fun p => ?_)
    have hhd := (hF_diff p w₀).hasDerivAt
    have ht : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℂ)⁻¹)) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have hR : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        have hC := (Complex.continuous_ofReal.tendsto 0).comp hR
        rw [Complex.ofReal_zero] at hC
        exact hC.congr fun n => by simp [Function.comp_apply]
      · exact Eventually.of_forall fun n => inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    have hsl := (hasDerivAt_iff_tendsto_slope_zero.mp hhd).comp ht
    refine hsl.congr fun n => ?_
    simp [smul_eq_mul]
  have hdiff_int := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := fun w p => deriv (fun z => F z p) w)
    (bound := fun p => (M_loc / ε) * (|Φ p| * spinV1 a p.1 * spinV1 a p.2))
    (ball_mem_nhds w₀ hε_pos)
    (Eventually.of_forall fun w => hmeas_F w)
    hint_w₀
    hmeas_F'
    (Eventually.of_forall fun p w hw => hderiv_bd p w hw)
    (hΦ.int_M2.const_mul (M_loc / ε))
    (Eventually.of_forall fun p w _ => (hF_diff p w).hasDerivAt)
  have hfun : spinDiagC a Φ σ d = fun w => -(∫ p : ℝ × ℝ, F w p) := by
    ext w; unfold spinDiagC; exact spinDaC_eq_spinWa a Φ _ _
  rw [hfun]
  exact hdiff_int.2.neg.differentiableAt.differentiableWithinAt

private lemma continuousOn_spinDampedDiag {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {σ d : ℝ} (hσ : |σ| = 1) :
    ContinuousOn (spinDampedDiag a Φ σ d) {w : ℂ | |w.im| ≤ 1 / 2} := by
  unfold spinDampedDiag
  have h1 : ContinuousOn (fun w : ℂ => ((w + I) ^ 4)⁻¹) {w : ℂ | |w.im| ≤ 1 / 2} := by
    refine ContinuousOn.inv₀ ?_ fun w hw => pow_ne_zero 4 (add_I_ne_zero_of_im_le hw)
    fun_prop
  exact h1.mul (continuousOn_spinDiagC ha hΦ hσ)

private lemma differentiableOn_spinDampedDiag {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {σ d : ℝ} (hσ : |σ| = 1) :
    DifferentiableOn ℂ (spinDampedDiag a Φ σ d) {w : ℂ | |w.im| < 1 / 2} := by
  unfold spinDampedDiag
  have h1 : DifferentiableOn ℂ (fun w : ℂ => ((w + I) ^ 4)⁻¹) {w : ℂ | |w.im| < 1 / 2} := by
    intro w hw
    have hne : (w + I) ^ 4 ≠ 0 := pow_ne_zero 4 (add_I_ne_zero_of_im_le hw.le)
    exact ((((differentiableAt_id.add (differentiableAt_const I)).pow 4).inv hne)).differentiableWithinAt
  exact h1.mul (differentiableOn_spinDiagC ha hΦ hσ)

private lemma spinDiagC_ofReal {a : ℝ} (ha : 2 < a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (σ d t : ℝ) :
    spinDiagC a Φ σ d (t : ℂ) =
      ((spinDeltaA a Φ (spinGamma a * (σ * t) + d) (spinGamma a * (σ * t) - d) : ℝ) : ℂ) := by
  unfold spinDiagC
  have h1 : (σ : ℂ) * (t : ℂ) + ((spinLambda a * d : ℝ) : ℂ) =
      ((σ * t + spinLambda a * d : ℝ) : ℂ) := by push_cast; ring
  have h2 : (σ : ℂ) * (t : ℂ) - ((spinLambda a * d : ℝ) : ℂ) =
      ((σ * t - spinLambda a * d : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, spinDaC_eq_spinDa ha.le hΦ]
  congr 1
  unfold spinDeltaA
  have hγ_pos : 0 < spinGamma a := by
    unfold spinGamma; exact Real.sqrt_pos.mpr (by linarith [(div_lt_one (by linarith : 0 < a)).mpr ha])
  have hlam_gam : spinLambda a * spinGamma a = 1 := by
    unfold spinLambda; exact inv_mul_cancel₀ hγ_pos.ne'
  have hL : spinLambda a * (spinGamma a * (σ * t) + d) = σ * t + spinLambda a * d := by
    calc spinLambda a * (spinGamma a * (σ * t) + d)
        = (spinLambda a * spinGamma a) * (σ * t) + spinLambda a * d := by ring
      _ = σ * t + spinLambda a * d := by rw [hlam_gam, one_mul]
  have hR : spinLambda a * (spinGamma a * (σ * t) - d) = σ * t - spinLambda a * d := by
    calc spinLambda a * (spinGamma a * (σ * t) - d)
        = (spinLambda a * spinGamma a) * (σ * t) - spinLambda a * d := by ring
      _ = σ * t - spinLambda a * d := by rw [hlam_gam, one_mul]
  rw [hL, hR]

private lemma spinDampedDiag_bdy_ne_zero_ae {a : ℝ} (ha : 2 ≤ a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ) {σ d x : ℝ} (hσ : |σ| = 1)
    (hx_ne : spinDampedDiag a Φ σ d (x : ℂ) ≠ 0) :
    ∀ᵐ s ∂(volume.restrict slitPreimage),
      spinDampedDiag a Φ σ d (slitBoundaryMap s : ℂ) ≠ 0 := by
  let U : Set ℂ := {w : ℂ | |w.im| < 1 / 2}
  have hU_open : IsOpen U := isOpen_lt Complex.continuous_im.abs continuous_const
  have hU_conv : Convex ℝ U := by
    have heq : U = Complex.imCLM ⁻¹' Ioo (-(1 / 2)) (1 / 2) := by
      ext b; simp [U, Complex.imCLM_apply, abs_lt]
    rw [heq]
    exact (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap
  have han : AnalyticOnNhd ℂ (spinDampedDiag a Φ σ d) U :=
    (differentiableOn_spinDampedDiag ha hΦ hσ).analyticOnNhd hU_open
  have hx_mem : (x : ℂ) ∈ U := by simp [U]
  have hz_re_cnt : {r : ℝ | spinDampedDiag a Φ σ d (r : ℂ) = 0}.Countable := by
    have heq : {r : ℝ | spinDampedDiag a Φ σ d (r : ℂ) = 0} =
        ⋃ n : ℕ, {r : ℝ | r ∈ Icc (-(n : ℝ)) n ∧ spinDampedDiag a Φ σ d (r : ℂ) = 0} := by
      ext r; simp only [Set.mem_ofPred_eq, mem_iUnion, mem_Icc]
      constructor
      · intro hr
        obtain ⟨n, hn⟩ := exists_nat_gt |r|
        exact ⟨n, ⟨by linarith [(abs_le.mp hn.le).1], by linarith [(abs_le.mp hn.le).2]⟩, hr⟩
      · rintro ⟨_, _, hr⟩; exact hr
    rw [heq]
    refine Set.countable_iUnion fun n => Set.Finite.countable ?_
    let K : Set ℂ := ((↑) : ℝ → ℂ) '' Icc (-(n : ℝ)) n
    have hK_comp : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
    have hK_sub : K ⊆ U := by rintro _ ⟨r, _, rfl⟩; simp [U]
    have hfin_C : {z ∈ K | spinDampedDiag a Φ σ d z = 0}.Finite := by
      by_contra hinf
      have hinf' : {z ∈ K | spinDampedDiag a Φ σ d z = 0}.Infinite := hinf
      obtain ⟨z₀, hz₀K, hz₀acc⟩ := hinf'.exists_accPt_of_subset_isCompact hK_comp (fun _ h => h.1)
      have hz₀U : z₀ ∈ U := hK_sub hz₀K
      have hfreq : ∃ᶠ z in 𝓝[≠] z₀, spinDampedDiag a Φ σ d z = 0 := by
        rw [accPt_iff_frequently] at hz₀acc
        rw [frequently_nhdsWithin_iff]
        exact hz₀acc.mono fun z hz => ⟨hz.2.2, hz.1⟩
      have heq0 := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hU_conv.isPreconnected
        hz₀U hfreq
      exact hx_ne (heq0 hx_mem)
    refine Set.Finite.of_finite_image (hfin_C.subset ?_) (Complex.ofReal_injective.injOn)
    rintro _ ⟨r, ⟨hrI, hr0⟩, rfl⟩
    exact ⟨⟨r, hrI, rfl⟩, hr0⟩
  have hpre_cnt : {s : ℝ | s ∈ slitPreimage ∧ spinDampedDiag a Φ σ d (slitBoundaryMap s : ℂ) = 0}.Countable := by
    have heq : {s : ℝ | s ∈ slitPreimage ∧ spinDampedDiag a Φ σ d (slitBoundaryMap s : ℂ) = 0} =
        ⋃ r ∈ {r : ℝ | spinDampedDiag a Φ σ d (r : ℂ) = 0},
          {s : ℝ | s ∈ slitPreimage ∧ slitBoundaryMap s = r} := by
      ext s; simp only [Set.mem_ofPred_eq, mem_iUnion, exists_prop]
      exact ⟨fun ⟨hs, h0⟩ => ⟨slitBoundaryMap s, h0, hs, rfl⟩,
        fun ⟨r, hr0, hs, hsr⟩ => ⟨hs, hsr ▸ hr0⟩⟩
    rw [heq]
    exact hz_re_cnt.biUnion fun r _ => (slitBoundaryMap_preimage_finite r).countable
  change ∀ᵐ s ∂(volume.restrict (Ioo (-1 : ℝ) 0 ∪ Ioi 1)),
    spinDampedDiag a Φ σ d (slitBoundaryMap s : ℂ) ≠ 0
  rw [ae_restrict_iff' (measurableSet_Ioo.union measurableSet_Ioi)]
  have hnull : volume {s : ℝ | s ∈ slitPreimage ∧ spinDampedDiag a Φ σ d (slitBoundaryMap s : ℂ) = 0} = 0 :=
    hpre_cnt.measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hnull] with s hs hmem hzero
  exact hs ⟨hmem, hzero⟩

/-! ### Section 2: Master logarithmic fold bound via upper half-plane Poisson–Jensen -/

private lemma slitMass_pos' {x y : ℝ} (hy : 0 < y) : 0 < slitMass x y := by
  have hIoo_pos : 0 < ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x y σ := by
    refine (setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
      (integrable_poissonKernel x hy).integrableOn).mpr ?_
    have hsupp : Function.support (poissonKernel x y) ∩ Ioo (-1 : ℝ) 0 = Ioo (-1) 0 := by
      ext σ; simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
      intro _; exact (poissonKernel_pos (x := x) hy σ).ne'
    rw [hsupp, Real.volume_Ioo]; norm_num
  have hle : ∫ σ in Ioo (-1 : ℝ) 0, poissonKernel x y σ ≤ slitMass x y := by
    unfold slitMass slitPreimage
    exact setIntegral_mono_set (integrable_poissonKernel x hy).integrableOn
      (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
      (ae_of_all _ fun σ hσ => Set.subset_union_left hσ)
  linarith

private lemma slitMass_le_one'' {x y : ℝ} (hy : 0 < y) : slitMass x y ≤ 1 := by
  unfold slitMass
  calc ∫ σ in slitPreimage, poissonKernel x y σ
      ≤ ∫ σ : ℝ, poissonKernel x y σ :=
        setIntegral_le_integral (integrable_poissonKernel x hy)
          (Eventually.of_forall fun σ => poissonKernel_nonneg hy.le σ)
    _ = 1 := integral_poissonKernel x hy

private lemma one_sub_slitMass_eq_edgeMass'' {x y : ℝ} (hy : 0 < y) :
    1 - slitMass x y = ∫ σ in edgePreimage, poissonKernel x y σ := by
  have hint := integrable_poissonKernel x hy
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]; intro σ h1 h2
    rcases h1 with h1 | (h1 : 1 < σ) <;> rcases h2 with (h2 : σ < -1) | h2
    · linarith [h1.1]
    · linarith [h1.2, h2.1]
    · linarith
    · linarith [h2.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    refine Filter.eventuallyEqSet_iff'.2 ?_
    change ∀ᵐ σ ∂volume, (σ ∈ slitPreimage ∪ edgePreimage) = (σ ∈ (univ : Set ℝ))
    rw [ae_iff]
    refine measure_mono_null (fun σ hσ => ?_) hnull
    by_contra hnot; apply hσ; apply propext
    simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_or_gt_of_ne hnot.1 with hm | hm
    · exact Or.inr (Or.inl hm)
    · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
      · exact Or.inl (Or.inl ⟨hm, h0⟩)
      · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inr h1)
  have htot : slitMass x y + ∫ σ in edgePreimage, poissonKernel x y σ = 1 := by
    unfold slitMass
    rw [← setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
        hint.integrableOn hint.integrableOn,
      setIntegral_congr_set hunion_ae, setIntegral_univ]
    exact integral_poissonKernel x hy
  linarith

private lemma log_integral_jensen_slitPreimage' {x y : ℝ} (hy : 0 < y)
    {f : ℝ → ℝ} (hf_pos : ∀ᵐ σ ∂(volume.restrict slitPreimage), 0 < f σ)
    (hf_int : IntegrableOn (fun σ => f σ * poissonKernel x y σ) slitPreimage)
    (hlog_int : IntegrableOn (fun σ => Real.log (f σ) * poissonKernel x y σ) slitPreimage)
    {B : ℝ} (hB_pos : 0 < B)
    (hI_le : ∫ σ in slitPreimage, f σ * poissonKernel x y σ ≤ B) :
    ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
      slitMass x y * Real.log B + (1 - slitMass x y) := by
  have hm_pos : 0 < slitMass x y := slitMass_pos' hy
  have hm_le : slitMass x y ≤ 1 := slitMass_le_one'' hy
  -- Pointwise `log(f σ) ≤ log B + f σ / B - 1`
  have hpt : ∀ᵐ σ ∂(volume.restrict slitPreimage),
      Real.log (f σ) * poissonKernel x y σ ≤
        (Real.log B - 1) * poissonKernel x y σ + B⁻¹ * (f σ * poissonKernel x y σ) := by
    filter_upwards [hf_pos] with σ hσ
    have hlog : Real.log (f σ / B) ≤ f σ / B - 1 := Real.log_le_sub_one_of_pos (div_pos hσ hB_pos)
    rw [Real.log_div hσ.ne' hB_pos.ne', div_eq_inv_mul] at hlog
    have hP0 := poissonKernel_nonneg (x := x) hy.le σ
    have hmul := mul_le_mul_of_nonneg_right (by linarith : Real.log (f σ) ≤ Real.log B - 1 + B⁻¹ * f σ) hP0
    linarith
  have hrhs_int : IntegrableOn
      (fun σ => (Real.log B - 1) * poissonKernel x y σ + B⁻¹ * (f σ * poissonKernel x y σ))
      slitPreimage :=
    ((integrable_poissonKernel x hy).integrableOn.const_mul _).add (hf_int.const_mul _)
  have hmono := integral_mono_ae hlog_int hrhs_int hpt
  rw [integral_add ((integrable_poissonKernel x hy).integrableOn.const_mul _) (hf_int.const_mul _),
    integral_const_mul, integral_const_mul] at hmono
  change ∫ σ in slitPreimage, Real.log (f σ) * poissonKernel x y σ ≤
    (Real.log B - 1) * slitMass x y + B⁻¹ * ∫ σ in slitPreimage, f σ * poissonKernel x y σ at hmono
  have hBinv : B⁻¹ * ∫ σ in slitPreimage, f σ * poissonKernel x y σ ≤ 1 := by
    calc B⁻¹ * ∫ σ in slitPreimage, f σ * poissonKernel x y σ
        ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left hI_le (inv_nonneg.mpr hB_pos.le)
      _ = 1 := inv_mul_cancel₀ hB_pos.ne'
  linarith

private lemma abs_slitBoundaryMap_ge_xiStar' {σ : ℝ} (hσ : σ ∈ slitPreimage) :
    xiStar ≤ |slitBoundaryMap σ| := by
  rcases hσ with hIoo | hIoi
  · exact (xiStar_le_slitBoundaryMap hIoo).trans (le_abs_self _)
  · have := slitBoundaryMap_le_neg_xiStar hIoi
    linarith [neg_abs_le (slitBoundaryMap σ)]

set_option maxHeartbeats 400000 in
/-- Master logarithmic slit-strip fold estimate (`spinning_foundations.tex`, proof of Lemma S2.2′):
there exists an absolute constant `C_log > 0` such that for all `c ≥ 40` (`n = c - 1`,
`a = n / 12`, `b_* = γ_a ξ_*`, `D = 3 b_* / 4`), every `Φ ∈ \overline{\mathcal A}_{\rm spin}`
with `M_2[Φ] = 1`, every `|ξ| < b_*`, `|d| ≤ D` with `Δ_a G(ξ + d, ξ - d) ≠ 0`, and assuming
the slit integrand at `d` is integrable:
`log(a e^{n L(ξ)} |Δ_a G(ξ + d, ξ - d)|) ≤ -(8/9) √(2π) n δ^{3/2} + log(1 + S_d) + log(δ⁻¹) + (1 - m_x) log a + C_log`,
where `δ = b_* - |ξ|`, `x = |ξ| / γ_a`, and `m_x = realSliceData.slitMassAt x`. -/
theorem spinS22b_log_master :
    ∃ C_log : ℝ, 0 < C_log ∧
      ∀ {c : ℝ}, 40 ≤ c →
        let n := c - 1
        let a := n / 12
        let bStar := spinBStar a
        let D := 3 * bStar / 4
        ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
          ∀ ξ d : ℝ, |ξ| < bStar → |d| ≤ D →
            IntegrableOn (fun s : ℝ =>
              a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|)
              {s : ℝ | bStar ≤ |s|} →
            spinDeltaA a Φ (ξ + d) (ξ - d) ≠ 0 →
            let δ := bStar - |ξ|
            let x := |ξ| / spinGamma a
            Real.log (a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)|) ≤
              -((8 / 9 : ℝ) * Real.sqrt (2 * π)) * n * δ ^ ((3 : ℝ) / 2) +
                Real.log (1 + spinSlitIntegral a Φ d) + Real.log (δ⁻¹) +
                (1 - realSliceData.slitMassAt x) * Real.log a + C_log := by
  obtain ⟨_, C_S, hS_real⟩ := lemmaS_real realSliceData.hC_e realSliceData.hc_y realSliceData.hC_y
    realSliceData.re_bound realSliceData.im_lower realSliceData.im_upper
  let C_log : ℝ := max 1 (2 * Real.log 2 + Real.log 17424 + Real.log 4 + 1 + C_S)
  refine ⟨C_log, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro c hc n a bStar D Φ hΦ hM2 ξ d hξ hd hS_int hne δ x
  have hn_ge : 39 ≤ n := by dsimp [n]; linarith
  have ha_ge : 39 / 12 ≤ a := by dsimp [a, n]; linarith
  have ha2 : 2 < a := by linarith
  have ha0 : 0 < a := by linarith
  have h12a : 12 * a = n := by dsimp [a]; ring
  have hγ_pos : 0 < spinGamma a := by
    unfold spinGamma; exact Real.sqrt_pos.mpr (by linarith [(div_lt_one ha0).mpr ha2])
  have hγ_lt1 : spinGamma a < 1 := by
    unfold spinGamma
    calc Real.sqrt (1 - 2 / a) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (by linarith [(div_lt_one ha0).mpr ha2]) (by linarith [div_pos two_pos ha0])
      _ = 1 := Real.sqrt_one
  have hγ_ge : (0.6 : ℝ) ≤ spinGamma a := by
    unfold spinGamma
    have hdiv : 2 / a ≤ 2 / (39 / 12 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha_ge
    calc (0.6 : ℝ) = Real.sqrt (0.6 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt (by linarith)
  -- Orientation `σ ∈ {-1, 1}` so that `γ * (σ * x) = ξ`
  set σ : ℝ := if 0 ≤ ξ then 1 else -1
  have hσ_abs : |σ| = 1 := by
    dsimp [σ]; split_ifs <;> norm_num
  have hγσx : spinGamma a * (σ * x) = ξ := by
    dsimp [x, σ]
    have h1 : spinGamma a * (|ξ| / spinGamma a) = |ξ| := mul_div_cancel₀ _ hγ_pos.ne'
    split_ifs with h
    · rw [one_mul, h1, abs_of_nonneg h]
    · push Not at h
      rw [show (-1 : ℝ) * (|ξ| / spinGamma a) = -(|ξ| / spinGamma a) by ring,
        mul_neg, h1, abs_of_neg h, neg_neg]
  have hx_mem : x ∈ Ico 0 xiStar := by
    refine ⟨div_nonneg (abs_nonneg _) hγ_pos.le, ?_⟩
    rw [div_lt_iff₀ hγ_pos]
    simpa [bStar, spinBStar, mul_comm] using hξ
  have hδ_std : xiStar - x = δ / spinGamma a := by
    dsimp [δ, x, bStar, spinBStar]
    field_simp [hγ_pos.ne']
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  have hδ_std_mem : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx_mem.2, by linarith [hx_mem.1]⟩
  -- Upper half-plane preimage `z₀ = x₀ + i y₀` of `x`
  set x₀ : ℝ := realSliceData.xUHP (xiStar - x)
  set y₀ : ℝ := realSliceData.yUHP (xiStar - x)
  set z₀ : ℂ := (x₀ : ℂ) + (y₀ : ℂ) * I
  have hp_pre := realSliceData_preimage hδ_std_mem
  have hy₀_pos : 0 < y₀ := hp_pre.1
  have hconfB_z₀ : confB z₀ = (x : ℂ) := by simpa [z₀, x₀, y₀, sub_sub_cancel] using hp_pre.2
  have hz₀_im : 0 < z₀.im := by simpa [z₀] using hy₀_pos
  have hz₀_re : z₀.re = x₀ := by simp [z₀]
  set m : ℝ := slitMass x₀ y₀
  have hm_eq : m = realSliceData.slitMassAt x := rfl
  have hm_pos : 0 < m := slitMass_pos' hy₀_pos
  have hm_le : m ≤ 1 := slitMass_le_one'' hy₀_pos
  -- Set up `F(z) = H(confB z)` on `{0 < z.im}` with `M = 17424`
  let H : ℂ → ℂ := spinDampedDiag a Φ σ d
  let F : ℂ → ℂ := fun z => H (confB z)
  let F_bdy : ℝ → ℂ := fun s => H (confB (s : ℂ))
  have hF_diff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} := by
    intro z hz
    have hcb := confB_mem_slitStrip hz
    have hc_diff : DifferentiableAt ℂ confB z := (hasDerivAt_confB hz).differentiableAt
    have hH_diff : DifferentiableAt ℂ H (confB z) :=
      (differentiableOn_spinDampedDiag ha2.le hΦ hσ_abs).differentiableAt
        ((isOpen_lt Complex.continuous_im.abs continuous_const).mem_nhds hcb.1)
    exact (hH_diff.comp z hc_diff).differentiableWithinAt
  have hF_bd : ∀ z : ℂ, 0 < z.im → ‖F z‖ ≤ 17424 := fun z hz =>
    norm_spinDampedDiag_le ha_ge hΦ hM2 hσ_abs hd (confB_mem_slitStrip hz).1.le
  have hconfB_im_real : ∀ s : ℝ, s ∉ ({-1, 0, 1} : Set ℝ) → |(confB (s : ℂ)).im| ≤ 1 / 2 := by
    intro s hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_trichotomy s (-1) with hm | rfl | hm1
    · rw [confB_real_im_of_lt_neg_one hm]; norm_num
    · exact absurd rfl hnot.1
    · rcases lt_trichotomy s 0 with h0 | rfl | h0
      · rw [confB_real_im_of_mem_Ioo_neg_one_zero ⟨hm1, h0⟩]; norm_num
      · exact absurd rfl hnot.2.1
      · rcases lt_trichotomy s 1 with h1 | rfl | h1
        · rw [confB_real_im_of_mem_Ioo_zero_one ⟨h0, h1⟩]; norm_num
        · exact absurd rfl hnot.2.2
        · rw [confB_real_im_of_one_lt h1]; norm_num
  have hF_bdy : ∀ᵐ s : ℝ ∂volume, Tendsto F (𝓝[{z : ℂ | 0 < z.im}] (s : ℂ)) (𝓝 (F_bdy s)) := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    filter_upwards [compl_mem_ae_iff.mpr hnull] with s hnot
    have hnot' : s ∉ ({-1, 0, 1} : Set ℝ) := hnot
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot'
    have htend_B : Tendsto confB (𝓝[{z : ℂ | 0 < z.im}] (s : ℂ))
        (𝓝[{b : ℂ | |b.im| ≤ 1 / 2}] (confB (s : ℂ))) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (confB_continuousWithinAt_real hnot'.2.1 hnot'.2.2 hnot'.1).tendsto.mono_left
          (nhdsWithin_mono _ fun z (hz : 0 < z.im) => hz.le)
      · filter_upwards [self_mem_nhdsWithin] with z hz
        exact (confB_mem_slitStrip hz).1.le
    exact ((continuousOn_spinDampedDiag ha2.le hΦ hσ_abs).continuousWithinAt
      (hconfB_im_real s hnot)).tendsto.comp htend_B
  have hFz₀_val : F z₀ = (((x : ℂ) + I) ^ 4)⁻¹ * ((spinDeltaA a Φ (ξ + d) (ξ - d) : ℝ) : ℂ) := by
    dsimp [F, H, spinDampedDiag]
    rw [hconfB_z₀, spinDiagC_ofReal ha2 hΦ σ d x, hγσx]
  have hxI_ne : ((x : ℂ) + I) ^ 4 ≠ 0 := pow_ne_zero 4 (add_I_ne_zero_of_im_le (by simp))
  have hFz₀_ne : F z₀ ≠ 0 := by
    rw [hFz₀_val]
    exact mul_ne_zero (inv_ne_zero hxI_ne) (Complex.ofReal_ne_zero.mpr hne)
  obtain ⟨hPJ_int, hPJ_le⟩ :=
    halfPlane_poissonJensen (by norm_num : (0 : ℝ) < 17424) hF_diff hF_bd hF_bdy hz₀_im hFz₀_ne
  rw [hz₀_re, show z₀.im = y₀ by simp [z₀] ] at hPJ_int hPJ_le
  -- Lower bound LHS: `log ‖F z₀‖ ≥ log |Δ_a G(ξ + d, ξ - d)| - 2 log 2`
  have hlhs_lb : Real.log |spinDeltaA a Φ (ξ + d) (ξ - d)| - 2 * Real.log 2 ≤ Real.log ‖F z₀‖ := by
    have hnorm_xI : ‖(x : ℂ) + I‖ ^ 2 = x ^ 2 + 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; simp [sq]
    have hnorm4 : ‖((x : ℂ) + I) ^ 4‖ = (x ^ 2 + 1) ^ 2 := by
      rw [norm_pow, show ‖(x : ℂ) + I‖ ^ 4 = (‖(x : ℂ) + I‖ ^ 2) ^ 2 by ring, hnorm_xI]
    have hx_le1 : x ^ 2 + 1 ≤ 2 := by
      have : x < 1 := hx_mem.2.trans xiStar_lt_one
      nlinarith [hx_mem.1]
    have hlog_xI : Real.log ((x ^ 2 + 1) ^ 2) ≤ 2 * Real.log 2 := by
      rw [Real.log_pow, Nat.cast_ofNat]
      gcongr
    rw [hFz₀_val, norm_mul, norm_inv, hnorm4, Complex.norm_real, Real.norm_eq_abs,
      Real.log_mul (inv_ne_zero (by positivity)) (abs_ne_zero.mpr hne), Real.log_inv]
    linarith
  -- Split RHS integral into `slitPreimage` and `edgePreimage`
  have hdisj : Disjoint slitPreimage edgePreimage := by
    rw [Set.disjoint_left]; intro s h1 h2
    rcases h1 with h1 | (h1 : 1 < s) <;> rcases h2 with (h2 : s < -1) | h2
    · linarith [h1.1]
    · linarith [h1.2, h2.1]
    · linarith
    · linarith [h2.2]
  have hunion_ae : (slitPreimage ∪ edgePreimage : Set ℝ) =ᵐ[volume] univ := by
    have hnull : volume ({-1, 0, 1} : Set ℝ) = 0 := ({-1, 0, 1} : Set ℝ).toFinite.measure_zero volume
    refine Filter.eventuallyEqSet_iff'.2 ?_
    change ∀ᵐ s ∂volume, (s ∈ slitPreimage ∪ edgePreimage) = (s ∈ (univ : Set ℝ))
    rw [ae_iff]
    refine measure_mono_null (fun s hs => ?_) hnull
    by_contra hnot; apply hs; apply propext
    simp only [mem_union, slitPreimage, edgePreimage, mem_Ioo, mem_Ioi, mem_Iio, mem_univ, iff_true]
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
    rcases lt_or_gt_of_ne hnot.1 with hm | hm
    · exact Or.inr (Or.inl hm)
    · rcases lt_or_gt_of_ne hnot.2.1 with h0 | h0
      · exact Or.inl (Or.inl ⟨hm, h0⟩)
      · rcases lt_or_gt_of_ne hnot.2.2 with h1 | h1
        · exact Or.inr (Or.inr ⟨h0, h1⟩)
        · exact Or.inl (Or.inr h1)
  have hsplit_eq : ∫ s : ℝ, Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s =
      (∫ s in slitPreimage, Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s) +
        (∫ s in edgePreimage, Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s) := by
    rw [← setIntegral_univ, ← setIntegral_congr_set hunion_ae]
    exact setIntegral_union hdisj (measurableSet_Iio.union measurableSet_Ioo)
      hPJ_int.integrableOn hPJ_int.integrableOn
  -- 1. Edge bound: `≤ Real.log 17424`
  have hedge_le : ∫ s in edgePreimage, Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s ≤ Real.log 17424 := by
    have hpk_edge : IntegrableOn (fun s => Real.log 17424 * poissonKernel x₀ y₀ s) edgePreimage :=
      (integrable_poissonKernel x₀ hy₀_pos).integrableOn.const_mul _
    have hpt_edge : ∀ s ∈ edgePreimage,
        Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s ≤ Real.log 17424 * poissonKernel x₀ y₀ s := by
      intro s hs
      have hnot : s ∉ ({-1, 0, 1} : Set ℝ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        rcases hs with (hlt : s < -1) | ⟨h0, h1⟩ <;> exact ⟨by linarith, by linarith, by linarith⟩
      have hbd := norm_spinDampedDiag_le ha_ge hΦ hM2 hσ_abs hd (hconfB_im_real s hnot)
      have hlog_le : Real.log ‖F_bdy s‖ ≤ Real.log 17424 := by
        by_cases h0 : ‖F_bdy s‖ = 0
        · rw [h0, Real.log_zero]; exact Real.log_nonneg (by norm_num)
        · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) hbd
      exact mul_le_mul_of_nonneg_right hlog_le (poissonKernel_nonneg hy₀_pos.le s)
    have hmono := setIntegral_mono_on hPJ_int.integrableOn hpk_edge
      (measurableSet_Iio.union measurableSet_Ioo) hpt_edge
    rw [integral_const_mul, ← one_sub_slitMass_eq_edgeMass'' hy₀_pos] at hmono
    have hln_nn : 0 ≤ Real.log 17424 := Real.log_nonneg (by norm_num)
    calc ∫ s in edgePreimage, Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s
        ≤ Real.log 17424 * (1 - m) := hmono
      _ ≤ Real.log 17424 * 1 := mul_le_mul_of_nonneg_left (by linarith) hln_nn
      _ = Real.log 17424 := mul_one _
  -- 2. Slit bound via `setIntegral_slitPreimage_div_slitDensity` and Jensen
  have hslit_confB : ∀ s ∈ slitPreimage, confB (s : ℂ) = (slitBoundaryMap s : ℂ) := by
    intro s hs
    rcases hs with hIoo | hIoi
    · exact Complex.ext (confB_real_re hIoo.2.ne (by linarith [hIoo.2]) hIoo.1.ne')
        (confB_real_im_of_mem_Ioo_neg_one_zero hIoo)
    · have hgt : 1 < s := hIoi
      exact Complex.ext (confB_real_re (by linarith) hgt.ne' (by linarith))
        (confB_real_im_of_one_lt hgt)
  -- Symmetrized slit majorant `φ(t)` on `Ioi xiStar`
  let φ : ℝ → ℝ := fun t =>
    a * Real.exp (n * spinGamma a * slitL t) *
      (|spinDeltaA a Φ (spinGamma a * t + d) (spinGamma a * t - d)| +
       |spinDeltaA a Φ (-(spinGamma a * t) + d) (-(spinGamma a * t) - d)|)
  have hφ_cont : Continuous φ := by
    have hG_cont : ∀ c₁ c₂ : ℝ, Continuous (fun t : ℝ =>
        spinG a Φ (c₁ * t + c₂) (c₁ * t - c₂)) := by
      intro c₁ c₂; unfold spinG
      exact hΦ.cont.comp ((continuous_const.mul ((continuous_const.mul continuous_id).add continuous_const)).prodMk
        (continuous_const.mul ((continuous_const.mul continuous_id).sub continuous_const)))
    have hDa_cont : ∀ sgn : ℝ, Continuous (fun t : ℝ =>
        spinDeltaA a Φ (sgn * (spinGamma a * t) + d) (sgn * (spinGamma a * t) - d)) := by
      intro sgn
      have hterm : ∀ cL cR : ℝ, Continuous (fun t : ℝ =>
          spinG a Φ (cL * (sgn * (spinGamma a * t) + d)) (cR * (sgn * (spinGamma a * t) - d))) := by
        intro cL cR; unfold spinG
        exact hΦ.cont.comp ((continuous_const.mul (continuous_const.mul
          ((continuous_const.mul (continuous_const.mul continuous_id)).add continuous_const))).prodMk
          (continuous_const.mul (continuous_const.mul
            ((continuous_const.mul (continuous_const.mul continuous_id)).sub continuous_const))))
      have heq_da : (fun t : ℝ =>
          spinDeltaA a Φ (sgn * (spinGamma a * t) + d) (sgn * (spinGamma a * t) - d)) =
          fun t =>
            spinG a Φ (spinLambda a * (sgn * (spinGamma a * t) + d))
              (spinLambda a * (sgn * (spinGamma a * t) - d)) -
            spinG a Φ ((spinGamma a * spinLambda a) * (sgn * (spinGamma a * t) + d))
              (spinLambda a * (sgn * (spinGamma a * t) - d)) -
            spinG a Φ (spinLambda a * (sgn * (spinGamma a * t) + d))
              ((spinGamma a * spinLambda a) * (sgn * (spinGamma a * t) - d)) +
            spinG a Φ ((spinGamma a * spinLambda a) * (sgn * (spinGamma a * t) + d))
              ((spinGamma a * spinLambda a) * (sgn * (spinGamma a * t) - d)) := by
        ext t; unfold spinDeltaA spinDa; rw [mul_assoc, mul_assoc]
      rw [heq_da]
      exact (((hterm _ _).sub (hterm _ _)).sub (hterm _ _)).add (hterm _ _)
    have hL_cont : Continuous slitL := by unfold slitL; fun_prop
    have h1 := hDa_cont 1
    have h2 := hDa_cont (-1)
    have heq : φ = fun t => a * Real.exp (n * spinGamma a * slitL t) *
        (|spinDeltaA a Φ (1 * (spinGamma a * t) + d) (1 * (spinGamma a * t) - d)| +
         |spinDeltaA a Φ (-1 * (spinGamma a * t) + d) (-1 * (spinGamma a * t) - d)|) := by
      ext t; dsimp [φ]; ring_nf
    rw [heq]
    exact (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hL_cont))).mul
      (h1.abs.add h2.abs)
  -- Relate `∫_{Ioi xiStar} φ t dt` to `spinSlitIntegral a Φ d`
  have hφ_int_and_eq : IntegrableOn φ (Ioi xiStar) ∧
      ∫ t in Ioi xiStar, φ t = (spinGamma a)⁻¹ * spinSlitIntegral a Φ d := by
    let g_slit : ℝ → ℝ := fun s =>
      a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|
    have hS_pos_int : IntegrableOn g_slit (Ioi bStar) :=
      hS_int.mono_set fun s (hs : bStar < s) => by
        change bStar ≤ |s|
        have hb0 : 0 ≤ bStar := by unfold bStar spinBStar; positivity [xiStar_pos]
        rw [abs_of_pos (hb0.trans_lt hs)]; exact hs.le
    have hS_neg_int : IntegrableOn g_slit (Iio (-bStar)) :=
      hS_int.mono_set fun s (hs : s < -bStar) => by
        change bStar ≤ |s|
        have hb0 : 0 ≤ bStar := by unfold bStar spinBStar; positivity [xiStar_pos]
        rw [abs_of_neg (by linarith)]; linarith
    -- Change of variables `s = γ t` on `Ioi xiStar`
    have hpre_pos : (fun t : ℝ => spinGamma a * t) ⁻¹' Ioi bStar = Ioi xiStar := by
      ext t; simp only [mem_preimage, mem_Ioi, bStar, spinBStar]
      constructor <;> intro h <;> nlinarith
    have hpre_neg : (fun t : ℝ => (-spinGamma a) * t) ⁻¹' Iio (-bStar) = Ioi xiStar := by
      ext t; simp only [mem_preimage, mem_Iio, mem_Ioi, bStar, spinBStar]
      constructor <;> intro h <;> nlinarith
    have hind_pos : (fun t => (Ioi bStar).indicator g_slit (spinGamma a * t)) =
        (Ioi xiStar).indicator (fun t => g_slit (spinGamma a * t)) := by
      ext t; by_cases ht : t ∈ Ioi xiStar
      · have hgt : spinGamma a * t ∈ Ioi bStar := by rw [← hpre_pos] at ht; exact ht
        rw [indicator_of_mem hgt, indicator_of_mem ht]
      · have hgt : spinGamma a * t ∉ Ioi bStar := fun h => ht (by rw [← hpre_pos]; exact h)
        rw [indicator_of_notMem hgt, indicator_of_notMem ht]
    have hind_neg : (fun t => (Iio (-bStar)).indicator g_slit ((-spinGamma a) * t)) =
        (Ioi xiStar).indicator (fun t => g_slit (-(spinGamma a * t))) := by
      ext t; by_cases ht : t ∈ Ioi xiStar
      · have hgt : (-spinGamma a) * t ∈ Iio (-bStar) := by rw [← hpre_neg] at ht; exact ht
        rw [indicator_of_mem hgt, indicator_of_mem ht, neg_mul]
      · have hgt : (-spinGamma a) * t ∉ Iio (-bStar) := fun h => ht (by rw [← hpre_neg]; exact h)
        rw [indicator_of_notMem hgt, indicator_of_notMem ht]
    have hpos_int : IntegrableOn (fun t : ℝ => g_slit (spinGamma a * t)) (Ioi xiStar) := by
      have h1 := ((integrable_indicator_iff measurableSet_Ioi).mpr hS_pos_int).comp_mul_left' hγ_pos.ne'
      rw [hind_pos] at h1
      exact (integrable_indicator_iff measurableSet_Ioi).mp h1
    have hneg_int : IntegrableOn (fun t : ℝ => g_slit (-(spinGamma a * t))) (Ioi xiStar) := by
      have h1 := ((integrable_indicator_iff measurableSet_Iio).mpr hS_neg_int).comp_mul_left'
        (neg_ne_zero.mpr hγ_pos.ne')
      rw [hind_neg] at h1
      exact (integrable_indicator_iff measurableSet_Ioi).mp h1
    have hφ_eq_sum : ∀ t ∈ Ioi xiStar, φ t = g_slit (spinGamma a * t) + g_slit (-(spinGamma a * t)) := by
      intro t ht
      have ht_pos : 0 < t := xiStar_pos.trans ht
      have hL1 : 12 * a * spinL (spinGamma a * t) = n * spinGamma a * slitL t := by
        rw [h12a]; unfold spinL slitL
        rw [abs_of_pos (mul_pos hγ_pos ht_pos), abs_of_pos ht_pos]; ring
      have hL2 : 12 * a * spinL (-(spinGamma a * t)) = n * spinGamma a * slitL t := by
        rw [h12a]; unfold spinL slitL
        rw [abs_neg, abs_of_pos (mul_pos hγ_pos ht_pos), abs_of_pos ht_pos]; ring
      dsimp [φ, g_slit]; rw [hL1, hL2]; ring
    have hφ_int : IntegrableOn φ (Ioi xiStar) :=
      (hpos_int.add hneg_int).congr_fun (fun t ht => (hφ_eq_sum t ht).symm) measurableSet_Ioi
    refine ⟨hφ_int, ?_⟩
    have hIpos : ∫ t in Ioi xiStar, g_slit (spinGamma a * t) =
        (spinGamma a)⁻¹ * ∫ s in Ioi bStar, g_slit s := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
        ← hind_pos, Measure.integral_comp_mul_left (fun s => (Ioi bStar).indicator g_slit s) (spinGamma a),
        abs_of_pos (inv_pos.mpr hγ_pos), smul_eq_mul]
    have hIneg : ∫ t in Ioi xiStar, g_slit (-(spinGamma a * t)) =
        (spinGamma a)⁻¹ * ∫ s in Iio (-bStar), g_slit s := by
      rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Iio,
        ← hind_neg, Measure.integral_comp_mul_left (fun s => (Iio (-bStar)).indicator g_slit s) (-spinGamma a),
        inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hγ_pos), smul_eq_mul]
    have hS_split : spinSlitIntegral a Φ d =
        (∫ s in Ioi bStar, g_slit s) + (∫ s in Iio (-bStar), g_slit s) := by
      unfold spinSlitIntegral
      have hnull : volume ({bStar, -bStar} : Set ℝ) = 0 :=
        ({bStar, -bStar} : Set ℝ).toFinite.measure_zero volume
      have hae_set : ({s : ℝ | bStar ≤ |s|} : Set ℝ) =ᵐ[volume] Ioi bStar ∪ Iio (-bStar) := by
        refine Filter.eventuallyEqSet_iff'.2 ?_
        change ∀ᵐ s ∂volume, (bStar ≤ |s|) = (s ∈ Ioi bStar ∪ Iio (-bStar))
        rw [ae_iff]
        refine measure_mono_null (fun s hs => ?_) hnull
        by_contra hnot; apply hs; apply propext
        simp only [mem_union, mem_Ioi, mem_Iio]
        simp only [mem_insert_iff, mem_singleton_iff, not_or] at hnot
        have hb0 : 0 < bStar := by unfold bStar spinBStar; positivity [xiStar_pos]
        rcases le_total 0 s with h0 | h0
        · rw [abs_of_nonneg h0]
          constructor
          · intro h; left; exact lt_of_le_of_ne h (Ne.symm hnot.1)
          · rintro (h | h)
            · exact h.le
            · linarith
        · rw [abs_of_nonpos h0]
          constructor
          · intro h; right; exact lt_of_le_of_ne (by linarith) hnot.2
          · rintro (h | h)
            · linarith
            · linarith
      have hdisj' : Disjoint (Ioi bStar) (Iio (-bStar)) := by
        rw [Set.disjoint_left]; intro s h1 h2
        have hb0 : 0 < bStar := by unfold bStar spinBStar; positivity [xiStar_pos]
        linarith [show bStar < s from h1, show s < -bStar from h2]
      rw [setIntegral_congr_set hae_set,
        setIntegral_union hdisj' measurableSet_Iio hS_pos_int hS_neg_int]
    rw [setIntegral_congr_fun measurableSet_Ioi hφ_eq_sum, integral_add hpos_int hneg_int,
      hIpos, hIneg, hS_split]
    ring
  -- Pull back `φ` to `slitPreimage`
  have hφ_nn : ∀ t ∈ Ioi xiStar, 0 ≤ φ t := fun t _ => by dsimp [φ]; positivity
  obtain ⟨hpull_int, hpull_eq⟩ :=
    setIntegral_slitPreimage_div_slitDensity (x := x₀) hy₀_pos hφ_cont.measurable hφ_nn hφ_int_and_eq.1
  -- Define `f s := a * exp(n γ slitL(slitBoundaryMap s)) * ‖F_bdy s‖ / slitDensity x₀ y₀ s`
  let f : ℝ → ℝ := fun s =>
    (a * Real.exp (n * spinGamma a * slitL (slitBoundaryMap s)) * ‖F_bdy s‖) /
      slitDensity x₀ y₀ s
  have hf_le_φ : ∀ s ∈ slitPreimage,
      a * Real.exp (n * spinGamma a * slitL (slitBoundaryMap s)) * ‖F_bdy s‖ ≤
        φ |slitBoundaryMap s| := by
    intro s hs
    have hFbdy_eq : ‖F_bdy s‖ ≤
        |spinDeltaA a Φ (spinGamma a * (σ * slitBoundaryMap s) + d)
          (spinGamma a * (σ * slitBoundaryMap s) - d)| := by
      dsimp [F_bdy, H, spinDampedDiag]
      rw [hslit_confB s hs, spinDiagC_ofReal ha2 hΦ σ d (slitBoundaryMap s), norm_mul,
        Complex.norm_real, Real.norm_eq_abs]
      have hinv_le1 : ‖(((slitBoundaryMap s : ℂ) + I) ^ 4)⁻¹‖ ≤ 1 := by
        rw [norm_inv, norm_pow]
        have h1 : 1 ≤ ‖(slitBoundaryMap s : ℂ) + I‖ := by
          have him : ((slitBoundaryMap s : ℂ) + I).im = 1 := by simp
          simpa [him] using Complex.abs_im_le_norm ((slitBoundaryMap s : ℂ) + I)
        exact inv_le_one_of_one_le₀ (one_le_pow₀ h1)
      calc ‖(((slitBoundaryMap s : ℂ) + I) ^ 4)⁻¹‖ *
              |spinDeltaA a Φ (spinGamma a * (σ * slitBoundaryMap s) + d)
                (spinGamma a * (σ * slitBoundaryMap s) - d)|
          ≤ 1 * |spinDeltaA a Φ (spinGamma a * (σ * slitBoundaryMap s) + d)
                (spinGamma a * (σ * slitBoundaryMap s) - d)| :=
            mul_le_mul_of_nonneg_right hinv_le1 (abs_nonneg _)
        _ = _ := one_mul _
    have hsum_ge : |spinDeltaA a Φ (spinGamma a * (σ * slitBoundaryMap s) + d)
          (spinGamma a * (σ * slitBoundaryMap s) - d)| ≤
        |spinDeltaA a Φ (spinGamma a * |slitBoundaryMap s| + d)
          (spinGamma a * |slitBoundaryMap s| - d)| +
        |spinDeltaA a Φ (-(spinGamma a * |slitBoundaryMap s|) + d)
          (-(spinGamma a * |slitBoundaryMap s|) - d)| := by
      have hcases : σ * slitBoundaryMap s = |slitBoundaryMap s| ∨
          σ * slitBoundaryMap s = -|slitBoundaryMap s| := by
        rcases eq_or_eq_neg_of_abs_eq hσ_abs with h1 | h1 <;>
          rcases le_total 0 (slitBoundaryMap s) with h2 | h2
        · left; rw [h1, one_mul, abs_of_nonneg h2]
        · right; rw [h1, one_mul, abs_of_nonpos h2, neg_neg]
        · right; rw [h1, neg_one_mul, abs_of_nonneg h2]
        · left; rw [h1, neg_one_mul, abs_of_nonpos h2]
      rcases hcases with h | h
      · rw [h]; linarith [abs_nonneg (spinDeltaA a Φ (-(spinGamma a * |slitBoundaryMap s|) + d)
          (-(spinGamma a * |slitBoundaryMap s|) - d))]
      · rw [h, mul_neg]; linarith [abs_nonneg (spinDeltaA a Φ (spinGamma a * |slitBoundaryMap s| + d)
          (spinGamma a * |slitBoundaryMap s| - d))]
    have hL_abs : slitL |slitBoundaryMap s| = slitL (slitBoundaryMap s) := by
      unfold slitL; rw [abs_abs]
    dsimp [φ]; rw [hL_abs]
    exact mul_le_mul_of_nonneg_left (hFbdy_eq.trans hsum_ge) (by positivity)
  have hf_pull_int : IntegrableOn (fun s => f s * poissonKernel x₀ y₀ s) slitPreimage := by
    have hmeas_f : AEStronglyMeasurable (fun s => f s * poissonKernel x₀ y₀ s)
        (volume.restrict slitPreimage) := by
      have h1 : Measurable (fun s : ℝ => a * Real.exp (n * spinGamma a * slitL (slitBoundaryMap s))) :=
        measurable_const.mul (Real.measurable_exp.comp
          (measurable_const.mul ((by unfold slitL; fun_prop : Continuous slitL).measurable.comp
            measurable_slitBoundaryMap)))
      have h2 : AEStronglyMeasurable (fun s : ℝ => ‖F_bdy s‖) (volume.restrict slitPreimage) := by
        have hcont : ContinuousOn (fun s : ℝ => ‖H (s : ℂ)‖) univ :=
          ((continuousOn_spinDampedDiag ha2.le hΦ hσ_abs).norm.comp Complex.continuous_ofReal.continuousOn
            (fun s _ => by simp))
        have hm : Measurable (fun s : ℝ => ‖H (slitBoundaryMap s : ℂ)‖) :=
          (continuousOn_univ.mp hcont).measurable.comp measurable_slitBoundaryMap
        refine hm.aestronglyMeasurable.congr ?_
        filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with s hs
        dsimp [F_bdy]; rw [hslit_confB s hs]
      have h3 : Measurable (slitDensity x₀ y₀) := by
        unfold slitDensity
        exact Measurable.ite measurableSet_Iio
          (by unfold rightSlitDensity poissonKernel slitInv invJacobian; fun_prop)
          (by unfold leftSlitDensity poissonKernel leftSlitInv invJacobian; fun_prop)
      have hdiv : AEStronglyMeasurable (fun s : ℝ =>
          (a * Real.exp (n * spinGamma a * slitL (slitBoundaryMap s)) * ‖F_bdy s‖) *
            (slitDensity x₀ y₀ s)⁻¹) (volume.restrict slitPreimage) :=
        (h1.aestronglyMeasurable.mul h2).mul h3.inv.aestronglyMeasurable
      exact (hdiv.congr (Eventually.of_forall fun s => by simp [f, div_eq_mul_inv])).mul
        (continuous_poissonKernel x₀ hy₀_pos).measurable.aestronglyMeasurable
    refine hpull_int.mono' hmeas_f ?_
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi),
      slitDensity_pos_ae (x := x₀) hy₀_pos] with s hs hω
    have hP0 := poissonKernel_nonneg (x := x₀) hy₀_pos.le s
    have hf_nn : 0 ≤ f s := div_nonneg (by positivity) hω.le
    rw [Real.norm_of_nonneg (mul_nonneg hf_nn hP0)]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hf_le_φ s hs) hω.le) hP0
  have hf_pull_le : ∫ s in slitPreimage, f s * poissonKernel x₀ y₀ s ≤
      4 * (1 + spinSlitIntegral a Φ d) := by
    have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
      unfold spinSlitIntegral
      exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet
        fun s _ => by positivity
    have hmono : ∫ s in slitPreimage, f s * poissonKernel x₀ y₀ s ≤
        ∫ s in slitPreimage, (φ |slitBoundaryMap s| / slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s := by
      refine integral_mono_ae hf_pull_int hpull_int ?_
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi),
        slitDensity_pos_ae (x := x₀) hy₀_pos] with s hs hω
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hf_le_φ s hs) hω.le)
        (poissonKernel_nonneg hy₀_pos.le s)
    have hγinv_le : (spinGamma a)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hγ_pos zero_lt_two]; linarith
    calc ∫ s in slitPreimage, f s * poissonKernel x₀ y₀ s
        ≤ 2 * ∫ t in Ioi xiStar, φ t := hmono.trans hpull_eq.le
      _ = 2 * ((spinGamma a)⁻¹ * spinSlitIntegral a Φ d) := by rw [hφ_int_and_eq.2]
      _ ≤ 2 * (2 * spinSlitIntegral a Φ d) := by gcongr
      _ ≤ 4 * (1 + spinSlitIntegral a Φ d) := by linarith
  -- Positivity a.e. of `f` on `slitPreimage` and `log f` decomposition
  have hH_ne : H (x : ℂ) ≠ 0 := by
    simpa [F, hconfB_z₀] using hFz₀_ne
  have hFbdy_ne_ae : ∀ᵐ s ∂(volume.restrict slitPreimage), F_bdy s ≠ 0 := by
    filter_upwards [spinDampedDiag_bdy_ne_zero_ae ha2.le hΦ hσ_abs hH_ne,
      ae_restrict_mem (measurableSet_Ioo.union measurableSet_Ioi)] with s hs hmem
    dsimp [F_bdy]; rwa [hslit_confB s hmem]
  have hf_pos_ae : ∀ᵐ s ∂(volume.restrict slitPreimage), 0 < f s := by
    filter_upwards [hFbdy_ne_ae, slitDensity_pos_ae (x := x₀) hy₀_pos] with s hF hω
    exact div_pos (mul_pos (mul_pos ha0 (Real.exp_pos _)) (norm_pos_iff.mpr hF)) hω
  have hident := identification_integrand_integrable x₀ hy₀_pos
  have hpk_int : IntegrableOn (poissonKernel x₀ y₀) slitPreimage :=
    (integrable_poissonKernel x₀ hy₀_pos).integrableOn
  have hlogω_int : IntegrableOn (fun s => Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s)
      slitPreimage :=
    (integrableOn_poisson_mul_log_slitDensity x₀ hy₀_pos).congr_fun
      (fun s _ => by dsimp only; ring) (measurableSet_Ioo.union measurableSet_Ioi)
  have hlogF_slit_int : IntegrableOn (fun s => Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s)
      slitPreimage := hPJ_int.integrableOn
  have hlogf_eq_ae : ∀ᵐ s ∂(volume.restrict slitPreimage),
      Real.log (f s) * poissonKernel x₀ y₀ s =
        Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s -
          Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s +
          Real.log a * poissonKernel x₀ y₀ s +
          (n * spinGamma a) * (slitL (slitBoundaryMap s) * poissonKernel x₀ y₀ s) := by
    filter_upwards [hFbdy_ne_ae, slitDensity_pos_ae (x := x₀) hy₀_pos] with s hF hω
    have hFn : 0 < ‖F_bdy s‖ := norm_pos_iff.mpr hF
    dsimp [f]
    rw [Real.log_div (mul_pos (mul_pos ha0 (Real.exp_pos _)) hFn).ne' hω.ne',
      Real.log_mul (mul_pos ha0 (Real.exp_pos _)).ne' hFn.ne',
      Real.log_mul ha0.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hlogf_int : IntegrableOn (fun s => Real.log (f s) * poissonKernel x₀ y₀ s) slitPreimage :=
    ((((hlogF_slit_int.sub hlogω_int).add (hpk_int.const_mul (Real.log a))).add
      (hident.const_mul (n * spinGamma a)))).congr (hlogf_eq_ae.mono fun _ h => h.symm)
  -- Apply Jensen on `slitPreimage`
  have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
    unfold spinSlitIntegral
    exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet
      fun s _ => by positivity
  have hjensen := log_integral_jensen_slitPreimage' hy₀_pos hf_pos_ae hf_pull_int hlogf_int
    (by linarith : 0 < 4 * (1 + spinSlitIntegral a Φ d)) hf_pull_le
  have hjensen_bd : ∫ s in slitPreimage, Real.log (f s) * poissonKernel x₀ y₀ s ≤
      Real.log (1 + spinSlitIntegral a Φ d) + Real.log 4 + 1 := by
    have hlog4 : Real.log (4 * (1 + spinSlitIntegral a Φ d)) =
        Real.log 4 + Real.log (1 + spinSlitIntegral a Φ d) :=
      Real.log_mul (by norm_num) (by linarith)
    have hlog_nn : 0 ≤ Real.log (4 * (1 + spinSlitIntegral a Φ d)) :=
      Real.log_nonneg (by linarith)
    have hm1 : m * Real.log (4 * (1 + spinSlitIntegral a Φ d)) ≤
        Real.log (4 * (1 + spinSlitIntegral a Φ d)) := by
      calc m * Real.log (4 * (1 + spinSlitIntegral a Φ d))
          ≤ 1 * Real.log (4 * (1 + spinSlitIntegral a Φ d)) := mul_le_mul_of_nonneg_right hm_le hlog_nn
        _ = Real.log (4 * (1 + spinSlitIntegral a Φ d)) := one_mul _
    linarith [hjensen, hlog4, hm1]
  -- Decompose `∫ log ‖F_bdy‖ dω` on `slitPreimage`
  have hdecomp : ∫ s in slitPreimage, Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s =
      (∫ s in slitPreimage, Real.log (f s) * poissonKernel x₀ y₀ s) +
        (∫ s in slitPreimage, Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s) -
        Real.log a * m -
        (n * spinGamma a) * ∫ s in slitPreimage, slitL (slitBoundaryMap s) * poissonKernel x₀ y₀ s := by
    have h1 : IntegrableOn (fun s => Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s -
        Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s) slitPreimage :=
      hlogF_slit_int.sub hlogω_int
    have h2 : IntegrableOn (fun s => Real.log ‖F_bdy s‖ * poissonKernel x₀ y₀ s -
        Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s +
        Real.log a * poissonKernel x₀ y₀ s) slitPreimage :=
      h1.add (hpk_int.const_mul (Real.log a))
    have hInt := integral_congr_ae hlogf_eq_ae
    rw [integral_add h2 (hident.const_mul (n * spinGamma a)),
      integral_add h1 (hpk_int.const_mul (Real.log a)),
      integral_sub hlogF_slit_int hlogω_int,
      integral_const_mul, integral_const_mul] at hInt
    change _ = _ - _ + Real.log a * m + _ at hInt
    linarith
  -- Entropy term
  have hent_le : ∫ s in slitPreimage, Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s ≤
      Real.log (δ⁻¹) + C_S := by
    have h1 : ∫ s in slitPreimage, Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s ≤
        slitEntropy x₀ y₀ := by
      calc ∫ s in slitPreimage, Real.log (slitDensity x₀ y₀ s) * poissonKernel x₀ y₀ s
          = ∫ s in slitPreimage, poissonKernel x₀ y₀ s * Real.log (slitDensity x₀ y₀ s) :=
            integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
        _ ≤ slitEntropy x₀ y₀ := setIntegral_poisson_mul_log_slitDensity_le_entropy x₀ hy₀_pos
    have h2 := hS_real (xiStar - x) hδ_std_mem
    have h3 : Real.log (1 / (xiStar - x)) ≤ Real.log (δ⁻¹) := by
      rw [hδ_std, one_div, inv_div]
      refine Real.log_le_log (div_pos hγ_pos hδ_pos) ?_
      rw [div_eq_mul_inv]
      exact mul_le_of_le_one_left (inv_nonneg.mpr hδ_pos.le) hγ_lt1.le
    linarith [h1, h2.1, h2.2, h3]
  -- Harmonic majorant & cubic fold deficit term
  have hharm : -∫ s in slitPreimage, slitL (slitBoundaryMap s) * poissonKernel x₀ y₀ s =
      majorantReal x := (harmonicMajorantIdentification x hx_mem).symm
  have hdeficit : n * spinL ξ + n * spinGamma a * majorantReal x ≤
      -((8 / 9 : ℝ) * Real.sqrt (2 * π)) * n * δ ^ ((3 : ℝ) / 2) := by
    have hLξ : spinL ξ = spinGamma a * ((2 * π / 3) * x) := by
      unfold spinL
      have hx_eq : |ξ| = spinGamma a * x := by dsimp [x]; field_simp [hγ_pos.ne']
      rw [hx_eq]; ring
    have hg := majorantReal_g_deficit hx_mem
    have hsd := slitDeficit_ge_exact hδ_std_mem.1.le hδ_std_mem.2
    have hpow : (xiStar - x) ^ ((3 : ℝ) / 2) = δ ^ ((3 : ℝ) / 2) / spinGamma a ^ ((3 : ℝ) / 2) := by
      rw [hδ_std, Real.div_rpow hδ_pos.le hγ_pos.le]
    have hγ_pow : spinGamma a * (δ ^ ((3 : ℝ) / 2) / spinGamma a ^ ((3 : ℝ) / 2)) ≥
        δ ^ ((3 : ℝ) / 2) := by
      have h1 : spinGamma a ^ ((3 : ℝ) / 2) ≤ spinGamma a := by
        calc spinGamma a ^ ((3 : ℝ) / 2) ≤ spinGamma a ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_ge hγ_pos hγ_lt1.le (by norm_num)
          _ = spinGamma a := Real.rpow_one _
      have h2 : 1 ≤ spinGamma a / spinGamma a ^ ((3 : ℝ) / 2) :=
        (one_le_div (Real.rpow_pos_of_pos hγ_pos _)).mpr h1
      calc δ ^ ((3 : ℝ) / 2) = (1 : ℝ) * δ ^ ((3 : ℝ) / 2) := (one_mul _).symm
        _ ≤ (spinGamma a / spinGamma a ^ ((3 : ℝ) / 2)) * δ ^ ((3 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hδ_pos.le _)
        _ = spinGamma a * (δ ^ ((3 : ℝ) / 2) / spinGamma a ^ ((3 : ℝ) / 2)) := by ring
    have hmul1 : spinGamma a * ((2 * π / 3) * x + majorantReal x) ≤
        -((8 / 9 : ℝ) * Real.sqrt (2 * π)) * δ ^ ((3 : ℝ) / 2) := by
      have hsub : (2 * π / 3) * x + majorantReal x ≤
          -((8 / 9 : ℝ) * Real.sqrt (2 * π)) * (xiStar - x) ^ ((3 : ℝ) / 2) := by linarith
      calc spinGamma a * ((2 * π / 3) * x + majorantReal x)
          ≤ spinGamma a * (-((8 / 9 : ℝ) * Real.sqrt (2 * π)) * (xiStar - x) ^ ((3 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hsub hγ_pos.le
        _ = -((8 / 9 : ℝ) * Real.sqrt (2 * π)) *
              (spinGamma a * (δ ^ ((3 : ℝ) / 2) / spinGamma a ^ ((3 : ℝ) / 2))) := by rw [hpow]; ring
        _ ≤ -((8 / 9 : ℝ) * Real.sqrt (2 * π)) * δ ^ ((3 : ℝ) / 2) := by
            have hκ0 : 0 ≤ (8 / 9 : ℝ) * Real.sqrt (2 * π) := by positivity
            nlinarith
    have hmul2 := mul_le_mul_of_nonneg_left hmul1 (by linarith : 0 ≤ n)
    rw [hLξ]; linarith
  -- Assemble final log inequality
  have hlhs_expand : Real.log (a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)|) =
      Real.log a + n * spinL ξ + Real.log |spinDeltaA a Φ (ξ + d) (ξ - d)| := by
    rw [Real.log_mul (mul_pos ha0 (Real.exp_pos _)).ne' (abs_ne_zero.mpr hne),
      Real.log_mul ha0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hC_ge : 2 * Real.log 2 + Real.log 17424 + Real.log 4 + 1 + C_S ≤ C_log := le_max_right _ _
  have hcomb : Real.log |spinDeltaA a Φ (ξ + d) (ξ - d)| ≤
      2 * Real.log 2 + Real.log 17424 + Real.log (1 + spinSlitIntegral a Φ d) + Real.log 4 + 1 +
        Real.log (δ⁻¹) + C_S - Real.log a * m + n * spinGamma a * majorantReal x := by
    have hharm' : -(n * spinGamma a) * ∫ s in slitPreimage, slitL (slitBoundaryMap s) * poissonKernel x₀ y₀ s =
        n * spinGamma a * majorantReal x := by
      calc -(n * spinGamma a) * ∫ s in slitPreimage, slitL (slitBoundaryMap s) * poissonKernel x₀ y₀ s
          = (n * spinGamma a) * (-∫ s in slitPreimage, slitL (slitBoundaryMap s) * poissonKernel x₀ y₀ s) := by ring
        _ = n * spinGamma a * majorantReal x := by rw [hharm]
    linarith [hlhs_lb, hPJ_le, hsplit_eq, hedge_le, hdecomp, hjensen_bd, hent_le, hharm']
  rw [hlhs_expand, ← hm_eq]
  linarith [hcomb, hdeficit, hC_ge]

/-! ### Section 3: Full assembly of `SpinS22b` (`spinnotes:S22b`) -/

/-- **Lemma S2.2′ (`spinnotes:S22b`)**:
discharges Parts (a), (b) (with `k = 1`), and (c) (with `k = 0`) completely from `spinS22`,
`spinS22b_partA`, `spinS22b_log_master`, and `lemmaE_real`. -/
theorem spinS22b : SpinS22b := by
  obtain ⟨C_log, hC_log_pos, hmaster⟩ := spinS22b_log_master
  obtain ⟨C_E, hCE_pos, hE_real⟩ := lemmaE_real realSliceData.hC_e realSliceData.hc_y
    realSliceData.hC_y realSliceData.re_bound realSliceData.im_lower realSliceData.im_upper
  let κ₀ : ℝ := (8 / 9 : ℝ) * Real.sqrt (2 * π)
  have hκ₀_pos : 0 < κ₀ := by dsimp [κ₀]; positivity
  let κ : ℝ := κ₀ / 2
  have hκ_pos : 0 < κ := by dsimp [κ]; positivity
  let C : ℝ := max (2 * spinSlitConst0⁻¹) (Real.exp C_log)
  have hC_pos : 0 < C := lt_of_lt_of_le (Real.exp_pos C_log) (le_max_right _ _)
  -- Choose `n₀ ≥ 39` large enough that `2 * C_E * log n ≤ κ * n^{1/3}` for `n ≥ n₀`:
  -- since `log n = 6 * log(n^{1/6}) ≤ 6 * n^{1/6}`, it suffices that `12 * C_E / κ ≤ n^{1/6}`,
  -- i.e. `n ≥ (12 * C_E / κ) ^ 6`.
  let n₀ : ℝ := max 39 ((12 * C_E / κ + 1) ^ 6)
  have hn₀_ge : 39 ≤ n₀ := le_max_left _ _
  refine ⟨1, C, κ, 1, n₀, by norm_num, hC_pos, hκ_pos, by norm_num, hn₀_ge, ?_⟩
  intro c hc n a ε bStar D Φ hΦ hM2
  have hc40 : 40 ≤ c := by linarith
  have hn_ge39 : 39 ≤ n := by dsimp [n]; linarith
  have hn_pos : 0 < n := by linarith
  have ha_ge : 39 / 12 ≤ a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have ha_le_n : a ≤ n := by dsimp [a]; linarith
  have ha_ge1 : 1 ≤ a := by linarith
  have hγ_pos : 0 < spinGamma a := by
    unfold spinGamma; exact Real.sqrt_pos.mpr (by linarith [(div_lt_one ha0).mpr (by linarith : 2 < a)])
  have hγ_ge : (0.6 : ℝ) ≤ spinGamma a := by
    unfold spinGamma
    have hdiv : 2 / a ≤ 2 / (39 / 12 : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha_ge
    calc (0.6 : ℝ) = Real.sqrt (0.6 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt (by linarith)
  -- Part (a)
  obtain ⟨hS_int_D, hS_le_D, hS_ae_D⟩ := spinS22b_partA hc40 hΦ hM2
  refine ⟨⟨hS_int_D, hS_le_D.trans (le_max_left _ _), hS_ae_D⟩, ?_, ?_⟩
  · -- Part (b) with `k = 1`
    intro ξ d hξ hd hS_int δ
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
      unfold spinSlitIntegral
      exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet
        fun s _ => by positivity
    by_cases h0 : spinDeltaA a Φ (ξ + d) (ξ - d) = 0
    · rw [h0, abs_zero, mul_zero]; positivity
    · have hlog := hmaster hc40 hΦ hM2 ξ d hξ hd hS_int h0
      set x := |ξ| / spinGamma a
      have hx_mem : x ∈ Ico 0 xiStar := by
        refine ⟨div_nonneg (abs_nonneg _) hγ_pos.le, ?_⟩
        rw [div_lt_iff₀ hγ_pos]
        simpa [bStar, spinBStar, mul_comm] using hξ
      have hm_nn : 0 ≤ realSliceData.slitMassAt x := by
        have hδ_std : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx_mem.2, by linarith [hx_mem.1]⟩
        exact (slitMass_pos' (realSliceData_preimage hδ_std).1).le
      have h1m_le1 : 1 - realSliceData.slitMassAt x ≤ 1 := by linarith
      have hlog_a_nn : 0 ≤ Real.log a := Real.log_nonneg ha_ge1
      have hlog_a_le : (1 - realSliceData.slitMassAt x) * Real.log a ≤ Real.log n := by
        calc (1 - realSliceData.slitMassAt x) * Real.log a
            ≤ 1 * Real.log a := mul_le_mul_of_nonneg_right h1m_le1 hlog_a_nn
          _ = Real.log a := one_mul _
          _ ≤ Real.log n := Real.log_le_log ha0 ha_le_n
      have hκ_le : -κ₀ * n * δ ^ ((3 : ℝ) / 2) ≤ -κ * n * δ ^ ((3 : ℝ) / 2) := by
        have : 0 ≤ n * δ ^ ((3 : ℝ) / 2) := mul_nonneg hn_pos.le (Real.rpow_nonneg hδ_pos.le _)
        dsimp [κ]; nlinarith
      have hlog_rhs :
          Real.log (a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)|) ≤
          Real.log (C * n ^ (1 : ℝ) * (1 + spinSlitIntegral a Φ d) * δ⁻¹ *
            Real.exp (-κ * n * δ ^ (3 / 2 : ℝ))) := by
        rw [Real.rpow_one,
          Real.log_mul (by positivity) (Real.exp_pos _).ne',
          Real.log_mul (by positivity) (inv_ne_zero hδ_pos.ne'),
          Real.log_mul (by positivity) (by linarith : 0 < 1 + spinSlitIntegral a Φ d).ne',
          Real.log_mul hC_pos.ne' hn_pos.ne',
          Real.log_exp]
        have hClog : C_log ≤ Real.log C := by
          rw [← Real.log_exp C_log]
          exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
        dsimp [κ₀] at hκ_le
        linarith [hlog, hlog_a_le, hκ_le, hClog]
      have hlhs_pos : 0 < a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| :=
        mul_pos (mul_pos ha0 (Real.exp_pos _)) (abs_pos.mpr h0)
      exact (Real.log_le_log_iff hlhs_pos (by positivity)).mp hlog_rhs
  · -- Part (c) with `k = 0`
    intro R hR ξ d hξ hd hS_int δ hδ_lo _hδ_hi
    have hδ_pos : 0 < δ := by dsimp [δ]; linarith
    have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
      unfold spinSlitIntegral
      exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet
        fun s _ => by positivity
    by_cases h0 : spinDeltaA a Φ (ξ + d) (ξ - d) = 0
    · rw [h0, abs_zero, mul_zero]; positivity
    · have hlog := hmaster hc40 hΦ hM2 ξ d hξ hd hS_int h0
      set x := |ξ| / spinGamma a
      have hx_mem : x ∈ Ico 0 xiStar := by
        refine ⟨div_nonneg (abs_nonneg _) hγ_pos.le, ?_⟩
        rw [div_lt_iff₀ hγ_pos]
        simpa [bStar, spinBStar, mul_comm] using hξ
      have hδ_std_eq : xiStar - x = δ / spinGamma a := by
        dsimp [δ, x, bStar, spinBStar]; field_simp [hγ_pos.ne']
      have hδ_std_mem : xiStar - x ∈ Ioc 0 xiStar := ⟨sub_pos.mpr hx_mem.2, by linarith [hx_mem.1]⟩
      -- Bound `(1 - m) * log a ≤ 2 * C_E * √δ * log n ≤ κ * n * δ^{3/2}`
      have h1m_le : 1 - realSliceData.slitMassAt x ≤ 2 * C_E * Real.sqrt δ := by
        have hE : 1 - realSliceData.slitMassAt x ≤ C_E * Real.sqrt (xiStar - x) :=
          hE_real (xiStar - x) hδ_std_mem
        have hsqrt_eq : Real.sqrt (xiStar - x) = Real.sqrt δ / Real.sqrt (spinGamma a) := by
          rw [hδ_std_eq, Real.sqrt_div hδ_pos.le]
        have hsqrt_γ : (1 / 2 : ℝ) ≤ Real.sqrt (spinGamma a) := by
          calc (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
            _ ≤ Real.sqrt (spinGamma a) := Real.sqrt_le_sqrt (by linarith)
        have hdiv_le : Real.sqrt δ / Real.sqrt (spinGamma a) ≤ 2 * Real.sqrt δ := by
          rw [div_le_iff₀ (Real.sqrt_pos.mpr hγ_pos)]
          nlinarith [Real.sqrt_nonneg δ]
        calc 1 - realSliceData.slitMassAt x
            ≤ C_E * Real.sqrt (xiStar - x) := hE
          _ = C_E * (Real.sqrt δ / Real.sqrt (spinGamma a)) := by rw [hsqrt_eq]
          _ ≤ C_E * (2 * Real.sqrt δ) := mul_le_mul_of_nonneg_left hdiv_le hCE_pos.le
          _ = 2 * C_E * Real.sqrt δ := by ring
      have hlog_n_le : 2 * C_E * Real.log n ≤ κ * n ^ ((1 : ℝ) / 3) := by
        have hn_ge_pow : (12 * C_E / κ + 1) ^ 6 ≤ n := (le_max_right _ _).trans (by dsimp [n]; linarith)
        have hn6_ge : 12 * C_E / κ + 1 ≤ n ^ ((1 : ℝ) / 6) := by
          have h1 := Real.rpow_le_rpow (by positivity) hn_ge_pow (by norm_num : (0 : ℝ) ≤ 1 / 6)
          rw [← Real.rpow_natCast (12 * C_E / κ + 1) 6, ← Real.rpow_mul (by positivity)] at h1
          simpa using h1
        have hlog_le : Real.log n ≤ 6 * n ^ ((1 : ℝ) / 6) := by
          have h1 : Real.log (n ^ ((1 : ℝ) / 6)) ≤ n ^ ((1 : ℝ) / 6) :=
            (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hn_pos _)).trans (by linarith)
          rw [Real.log_rpow hn_pos] at h1
          linarith
        have hn13 : n ^ ((1 : ℝ) / 6) * n ^ ((1 : ℝ) / 6) = n ^ ((1 : ℝ) / 3) := by
          rw [← Real.rpow_add hn_pos]; norm_num
        have h12 : 12 * C_E ≤ κ * n ^ ((1 : ℝ) / 6) := by
          have := (div_le_iff₀ hκ_pos).mp (by linarith : 12 * C_E / κ ≤ n ^ ((1 : ℝ) / 6))
          linarith
        calc 2 * C_E * Real.log n
            ≤ 2 * C_E * (6 * n ^ ((1 : ℝ) / 6)) :=
              mul_le_mul_of_nonneg_left hlog_le (by positivity)
          _ = (12 * C_E) * n ^ ((1 : ℝ) / 6) := by ring
          _ ≤ (κ * n ^ ((1 : ℝ) / 6)) * n ^ ((1 : ℝ) / 6) :=
              mul_le_mul_of_nonneg_right h12 (Real.rpow_nonneg hn_pos.le _)
          _ = κ * (n ^ ((1 : ℝ) / 6) * n ^ ((1 : ℝ) / 6)) := by ring
          _ = κ * n ^ ((1 : ℝ) / 3) := by rw [hn13]
      have hnδ_ge : n ^ ((1 : ℝ) / 3) ≤ n * δ := by
        have h1 : n ^ (-(2 / 3 : ℝ)) ≤ δ := (by nlinarith [Real.rpow_pos_of_pos hn_pos (-(2 / 3 : ℝ))] :
          n ^ (-(2 / 3 : ℝ)) ≤ R * n ^ (-(2 / 3 : ℝ))).trans hδ_lo
        calc n ^ ((1 : ℝ) / 3) = n ^ (1 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by
              rw [← Real.rpow_add hn_pos]; norm_num
          _ = n * n ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
          _ ≤ n * δ := mul_le_mul_of_nonneg_left h1 hn_pos.le
      have hδ32 : Real.sqrt δ * δ = δ ^ ((3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow]
        calc δ ^ ((1 : ℝ) / 2) * δ = δ ^ ((1 : ℝ) / 2) * δ ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = δ ^ ((1 : ℝ) / 2 + 1) := (Real.rpow_add hδ_pos _ _).symm
          _ = δ ^ ((3 : ℝ) / 2) := by norm_num
      have habsorb : (1 - realSliceData.slitMassAt x) * Real.log a ≤
          κ * n * δ ^ ((3 : ℝ) / 2) := by
        have hlog_a_le : Real.log a ≤ Real.log n := Real.log_le_log ha0 ha_le_n
        have hlog_a_nn : 0 ≤ Real.log a := Real.log_nonneg ha_ge1
        calc (1 - realSliceData.slitMassAt x) * Real.log a
            ≤ (2 * C_E * Real.sqrt δ) * Real.log n :=
              mul_le_mul h1m_le hlog_a_le hlog_a_nn (by positivity)
          _ = Real.sqrt δ * (2 * C_E * Real.log n) := by ring
          _ ≤ Real.sqrt δ * (κ * n ^ ((1 : ℝ) / 3)) :=
              mul_le_mul_of_nonneg_left hlog_n_le (Real.sqrt_nonneg _)
          _ ≤ Real.sqrt δ * (κ * (n * δ)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnδ_ge hκ_pos.le) (Real.sqrt_nonneg _)
          _ = κ * n * (Real.sqrt δ * δ) := by ring
          _ = κ * n * δ ^ ((3 : ℝ) / 2) := by rw [hδ32]
      have hlog_rhs :
          Real.log (a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)|) ≤
          Real.log (C * (1 + spinSlitIntegral a Φ d) * δ⁻¹ *
            Real.exp (-κ * n * δ ^ (3 / 2 : ℝ))) := by
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne',
          Real.log_mul (by positivity) (inv_ne_zero hδ_pos.ne'),
          Real.log_mul hC_pos.ne' (by linarith),
          Real.log_exp]
        have hClog : C_log ≤ Real.log C := by
          rw [← Real.log_exp C_log]
          exact Real.log_le_log (Real.exp_pos _) (le_max_right _ _)
        have hκ_split : -κ₀ * n * δ ^ ((3 : ℝ) / 2) + κ * n * δ ^ ((3 : ℝ) / 2) =
            -κ * n * δ ^ ((3 : ℝ) / 2) := by dsimp [κ]; ring
        dsimp [κ₀] at hκ_split
        linarith [hlog, habsorb, hClog, hκ_split]
      have hlhs_pos : 0 < a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| :=
        mul_pos (mul_pos ha0 (Real.exp_pos _)) (abs_pos.mpr h0)
      exact (Real.log_le_log_iff hlhs_pos (by positivity)).mp hlog_rhs

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS22b_log_master' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS22b_log_master

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS22b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS22b

end FormalResearch.ModularBootstrap.Spin

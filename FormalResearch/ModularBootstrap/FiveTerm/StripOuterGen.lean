module

public import FormalResearch.SignUncertainty.CtOuterBoundary
public import FormalResearch.SignUncertainty.CtOuterGen

/-!
# The strip Schwarz integral of an even real-analytic amplitude (FIVE-0 slice 1; `cts:involution` (1))

Generalisation of Paper I's `CtOuterEdge`/`CtOuterBoundary` (`SignUncertainty`, specific to `uR`) to an arbitrary
amplitude `a` of exponential growth, new copies only (Paper I is not edited); the generic Paper I parts
(`genH`, `hasDerivAt_genH`, `nearJ`, `logPart`, `differentiableOn_nearJ`, `kernel_norm_le_far`, ...) are imported.

`Amp a`: `a` continuous, even, `|a t| ≤ M e^{|t|}`, and real-analytic (local holomorphic extension at every `y₀`).
For such `a`, with `H = genH a` (`∫ a(t)/sin(π(ζ - it)) dt`, holomorphic on `S = {0 < Re ζ < 1}`):

* `genH_eq_contHA`: near every edge point `i y₀`, `H` is the restriction of a function holomorphic on a ball;
* `hbarA` (the `limUnder` boundary extension) is continuous on `closure S`, equals `H` on `S`, is real-symmetric,
  invariant under `ζ ↦ 1 - ζ`, and `Re hbarA(i y) = Re hbarA(1 + i y) = a y`.

All proved unconditionally.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.ModularBootstrap.FiveTerm.StripOuter

/-- Amplitudes admissible for the strip Schwarz integral. -/
structure Amp (a : ℝ → ℝ) : Prop where
  cont : Continuous a
  even : ∀ t, a (-t) = a t
  bdd : ExpBdd a
  loc : ∀ y₀ : ℝ, ∃ R : ℝ, 0 < R ∧ ∃ v : ℂ → ℂ, DifferentiableOn ℂ v (ball (y₀ : ℂ) R) ∧
    ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (a t : ℂ)

section

variable {a : ℝ → ℝ}

lemma integrable_genH_integrand (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ strip) :
    Integrable fun t : ℝ => (a t : ℂ) * kern0 ζ t := by
  obtain ⟨r, hr, C, _, _, hb⟩ := kern_ball_bound hζ
  exact integrable_amp_mul_kern ha.cont ha.bdd (continuous_kern0 hζ) (C := C)
    (fun t => (hb ζ (mem_ball_self hr) t).1)

lemma genH_eq_integral (a : ℝ → ℝ) (ζ : ℂ) :
    genH a ζ = ∫ t : ℝ, (a t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) := by
  unfold genH kern0
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp [div_eq_mul_inv]

lemma integrable_integrandA (ha : Amp a) {ζ : ℂ} (hζ : ζ ∈ strip) :
    Integrable fun t : ℝ => (a t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) := by
  refine (integrable_genH_integrand ha hζ).congr (Eventually.of_forall fun t => ?_)
  simp [kern0, div_eq_mul_inv]

lemma differentiableOn_genH (ha : Amp a) : DifferentiableOn ℂ (genH a) strip := fun _w hw =>
  (hasDerivAt_genH ha.cont ha.bdd hw).differentiableAt.differentiableWithinAt

/-- Parity `H(1 - ζ) = H(ζ)` for even `a`. -/
lemma genH_one_sub (ha : Amp a) (ζ : ℂ) : genH a (1 - ζ) = genH a ζ := by
  unfold genH
  have key : ∀ t : ℝ, kern0 (1 - ζ) t = kern0 ζ (-t) := by
    intro t
    unfold kern0
    have : (π : ℂ) * (1 - ζ - Complex.I * t) = π - π * (ζ - Complex.I * ((-t : ℝ) : ℂ)) := by
      push_cast; ring
    rw [this, Complex.sin_pi_sub]
  have h1 : ∫ t : ℝ, (a t : ℂ) * kern0 (1 - ζ) t = ∫ t : ℝ, (a (-t) : ℂ) * kern0 ζ (-t) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [key, ha.even]
  rw [h1]
  exact integral_neg_eq_self (fun t : ℝ => (a t : ℂ) * kern0 ζ t) volume

/-- Real symmetry `H(ζ̄) = conj H(ζ)` for even `a`. -/
lemma genH_conj (ha : Amp a) (ζ : ℂ) : genH a (starRingEnd ℂ ζ) = starRingEnd ℂ (genH a ζ) := by
  unfold genH
  have key : ∀ t : ℝ, kern0 (starRingEnd ℂ ζ) t = starRingEnd ℂ (kern0 ζ (-t)) := by
    intro t
    unfold kern0
    have : (π : ℂ) * (starRingEnd ℂ ζ - Complex.I * t) =
        starRingEnd ℂ ((π : ℂ) * (ζ - Complex.I * ((-t : ℝ) : ℂ))) := by
      simp only [map_mul, map_sub, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [this, Complex.sin_conj]
    simp
  have h1 : ∫ t : ℝ, (a t : ℂ) * kern0 (starRingEnd ℂ ζ) t =
      ∫ t : ℝ, starRingEnd ℂ ((a (-t) : ℂ) * kern0 ζ (-t)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [key, ha.even, map_mul, Complex.conj_ofReal]
  rw [h1, integral_conj]
  congr 1
  exact integral_neg_eq_self (fun t : ℝ => (a t : ℂ) * kern0 ζ t) volume

/-! ### The far part -/

noncomputable def farPartA (a : ℝ → ℝ) (lo hi : ℝ) (ζ : ℂ) : ℂ :=
  ∫ t in (Icc lo hi)ᶜ, (a t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))

lemma differentiableOn_farPartA (ha : Amp a) {y₀ δ : ℝ} (hδ : 0 < δ) :
    DifferentiableOn ℂ (farPartA a (y₀ - δ) (y₀ + δ)) (ball (Complex.I * (y₀ : ℂ)) δ) := by
  obtain ⟨M, hM0, hM⟩ := ExpBdd_nonneg_const ha.bdd
  have hne : ∀ ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ, ∀ t ∈ (Icc (y₀ - δ) (y₀ + δ))ᶜ,
      Complex.sin (π * (ζ - Complex.I * t)) ≠ 0 := by
    intro ζ hζ t ht h
    have h1 := norm_sin_arg_sq ζ t
    rw [h, norm_zero] at h1
    have h2 := im_ball_close hζ
    have h3 := abs_sub_gt_of_notMem hδ ht
    have hne : ζ.im - t ≠ 0 := by
      intro h0
      have : |t - y₀| ≤ |ζ.im - y₀| := by
        have : t - y₀ = ζ.im - y₀ := by linarith
        rw [this]
      linarith
    have : Real.sinh (π * (ζ.im - t)) ≠ 0 := Real.sinh_eq_zero.not.mpr (mul_ne_zero Real.pi_pos.ne' hne)
    nlinarith [sq_nonneg (Real.sin (π * ζ.re)), pow_pos (abs_pos.mpr this) 2, sq_abs (Real.sinh (π * (ζ.im - t)))]
  unfold farPartA
  refine differentiableOn_integral_param (μ := volume.restrict (Icc (y₀ - δ) (y₀ + δ))ᶜ)
    (Φ := fun w t => (a t : ℂ) / Complex.sin (π * (w - Complex.I * t))) isOpen_ball ?_ ?_ ?_
  · intro w hw
    have : ContinuousOn (fun t : ℝ => (a t : ℂ) / Complex.sin (π * (w - Complex.I * t)))
        (Icc (y₀ - δ) (y₀ + δ))ᶜ := by
      refine ContinuousOn.div (Complex.continuous_ofReal.comp ha.cont).continuousOn
        (by fun_prop) (fun t ht => hne w hw t ht)
    exact this.aestronglyMeasurable measurableSet_Icc.compl
  · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht w hw
    exact ((differentiableAt_const (a t : ℂ)).div
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.sin (π * (w - Complex.I * t))) w)
      (hne w hw t ht)).differentiableWithinAt
  · intro ζ₀ hζ₀
    have h0 := im_ball_close hζ₀
    set m : ℝ := (δ - |ζ₀.im - y₀|) / 2 with hm
    have hmpos : 0 < m := by rw [hm]; linarith
    set σ : ℝ := 2 / (1 - Real.exp (-(2 * π * m))) with hσ
    have hq : 0 < 1 - Real.exp (-(2 * π * m)) := by
      have : Real.exp (-(2 * π * m)) < 1 := Real.exp_lt_one_iff.mpr (by have := Real.pi_pos; nlinarith)
      linarith
    have hσpos : 0 < σ := by positivity
    have hπ1 : 0 < π - 1 := by linarith [Real.pi_gt_three]
    refine ⟨min m 1, lt_min hmpos one_pos, fun t => M * σ *
      Real.exp (π * (|ζ₀.im| + 1)) * Real.exp (-(π - 1) * |t|), ?_, ?_⟩
    · exact ((integrable_exp_neg_abs' hπ1).const_mul (M * σ * Real.exp (π * (|ζ₀.im| + 1)))).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht w hw
      have him : |w.im - ζ₀.im| < min m 1 := by
        have := Complex.abs_im_le_norm (w - ζ₀)
        rw [mem_ball, dist_eq_norm] at hw
        simp only [Complex.sub_im] at this
        linarith
      have hy : |w.im| ≤ |ζ₀.im| + 1 := by
        calc |w.im| = |(w.im - ζ₀.im) + ζ₀.im| := by ring_nf
          _ ≤ |w.im - ζ₀.im| + |ζ₀.im| := abs_add_le _ _
          _ ≤ _ := by linarith [min_le_right m 1]
      have hgap : m ≤ |w.im - t| := by
        have h3 := abs_sub_gt_of_notMem hδ ht
        have : |t - y₀| ≤ |t - w.im| + |w.im - y₀| := by
          calc |t - y₀| = |(t - w.im) + (w.im - y₀)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        have h4 : |w.im - y₀| ≤ |w.im - ζ₀.im| + |ζ₀.im - y₀| := by
          calc |w.im - y₀| = |(w.im - ζ₀.im) + (ζ₀.im - y₀)| := by ring_nf
            _ ≤ _ := abs_add_le _ _
        rw [abs_sub_comm t w.im] at this
        linarith [min_le_left m 1]
      have hk := kernel_norm_le_far (ζ := w) t hmpos hgap
      have hexp : Real.exp (-(π * |w.im - t|)) ≤ Real.exp (π * (|ζ₀.im| + 1)) * Real.exp (-(π * |t|)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have : |t| ≤ |w.im - t| + |w.im| := by
          calc |t| = |w.im - (w.im - t)| := by ring_nf
            _ ≤ |w.im| + |w.im - t| := abs_sub _ _
            _ = _ := by ring
        nlinarith [Real.pi_pos]
      have hu : ‖(a t : ℂ)‖ ≤ M * Real.exp |t| := by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact hM t
      rw [norm_div, div_eq_mul_inv, ← norm_inv]
      have h1 : ‖(Complex.sin (π * (w - Complex.I * t)))⁻¹‖ ≤
          σ * (Real.exp (π * (|ζ₀.im| + 1)) * Real.exp (-(π * |t|))) :=
        hk.trans (mul_le_mul_of_nonneg_left hexp hσpos.le)
      have hee : Real.exp |t| * Real.exp (-(π * |t|)) = Real.exp (-(π - 1) * |t|) := by
        rw [← Real.exp_add]; congr 1; ring
      calc ‖(a t : ℂ)‖ * ‖(Complex.sin (π * (w - Complex.I * t)))⁻¹‖
          ≤ (M * Real.exp |t|) * (σ * (Real.exp (π * (|ζ₀.im| + 1)) *
              Real.exp (-(π * |t|)))) :=
            mul_le_mul hu h1 (norm_nonneg _) (by positivity)
        _ = M * σ * Real.exp (π * (|ζ₀.im| + 1)) * (Real.exp |t| * Real.exp (-(π * |t|))) := by ring
        _ = _ := by rw [hee]

/-- The explicit continuation `H = far + i (near + (1/π) v(w) logPart)` with `w = -iζ`. -/
noncomputable def contHA (a : ℝ → ℝ) (v : ℂ → ℂ) (y₀ δ : ℝ) (ζ : ℂ) : ℂ :=
  farPartA a (y₀ - δ) (y₀ + δ) ζ + Complex.I * (nearJ v (y₀ - δ) (y₀ + δ) (wOf ζ) +
    (1 / (π : ℂ)) * v (wOf ζ) * logPart (y₀ - δ) (y₀ + δ) (wOf ζ))

theorem differentiableOn_contHA (ha : Amp a) {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hδR : δ < R) (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R)) :
    DifferentiableOn ℂ (contHA a v y₀ δ) (ball (Complex.I * (y₀ : ℂ)) δ) := by
  have hw : ∀ ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ, wOf ζ ∈ ball (y₀ : ℂ) δ := fun ζ hζ => wOf_mem_ball hζ
  have hwd := differentiable_wOf
  have h1 := differentiableOn_nearJ hδ2 hδR hv
  have h2 : DifferentiableOn ℂ (fun ζ => v (wOf ζ)) (ball (Complex.I * (y₀ : ℂ)) δ) :=
    (hv.mono (ball_subset_ball hδR.le)).comp hwd.differentiableOn hw
  have h3 := (differentiableOn_logPart (y₀ := y₀) (δ := δ)).comp hwd.differentiableOn hw
  exact (differentiableOn_farPartA ha hδ).add
    (((h1.comp hwd.differentiableOn hw).add ((differentiableOn_const _).mul h2 |>.mul h3)).const_mul _)

lemma integrand_eqA {ζ : ℂ} (hζ : ζ ∈ strip) {t : ℝ} {v : ℂ → ℂ} (hvt : v (t : ℂ) = (a t : ℂ)) :
    (a t : ℂ) / Complex.sin (π * (ζ - Complex.I * t)) =
      Complex.I * ((1 / (π : ℂ)) * dslope v (t : ℂ) (wOf ζ) + v (t : ℂ) * kappaFn ((t : ℂ) - wOf ζ)
        + (1 / (π : ℂ)) * v (wOf ζ) * (1 / ((t : ℂ) - wOf ζ))) := by
  have hs : (t : ℂ) - wOf ζ ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, wOf_im, Complex.zero_im] at this
    have := hζ.1
    linarith
  have hd : dslope v (t : ℂ) (wOf ζ) = ((t : ℂ) - wOf ζ)⁻¹ * (v (t : ℂ) - v (wOf ζ)) := by
    rw [dslope_symm v (t : ℂ) (wOf ζ), dslope_of_ne v (sub_ne_zero.mp hs), slope_def_module, smul_eq_mul]
  rw [sin_arg_eq, hd, ← hvt]
  unfold kappaFn
  simp only [div_eq_mul_inv, one_mul, mul_inv, inv_neg, Complex.inv_I]
  ring

/-- **Local holomorphic continuation of `genH a` across the edge `Re ζ = 0`.** -/
theorem genH_eq_contHA (ha : Amp a) {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ2 : δ ≤ 1 / 2)
    (hδR : δ < R) (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R))
    (hvu : ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (a t : ℂ)) {ζ : ℂ} (hζ : ζ ∈ strip)
    (hζb : ζ ∈ ball (Complex.I * (y₀ : ℂ)) δ) : genH a ζ = contHA a v y₀ δ ζ := by
  have hwζ := wOf_mem_ball hζb
  have himw : (wOf ζ).im < 0 := by rw [wOf_im]; linarith [hζ.1]
  have hδ : 0 < δ := by
    have := mem_ball.mp hζb
    rw [dist_eq_norm] at this
    exact lt_of_le_of_lt (norm_nonneg _) this
  have hint := integrable_integrandA ha hζ
  have hsplit := integral_add_compl (measurableSet_Icc (a := y₀ - δ) (b := y₀ + δ)) hint
  rw [genH_eq_integral]
  unfold contHA farPartA
  rw [← hsplit, add_comm]
  refine congrArg₂ (· + ·) rfl ?_
  have hcont1 := continuousOn_nearIntegrand hδ2 hδR hv hwζ
  have hcont2 : ContinuousOn (fun t : ℝ => 1 / ((t : ℂ) - wOf ζ)) (Icc (y₀ - δ) (y₀ + δ)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun t _ h => ?_)
    have := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at this
    linarith
  have hi1 : IntegrableOn (fun t : ℝ => (1 / (π : ℂ)) * dslope v (t : ℂ) (wOf ζ) +
      v (t : ℂ) * kappaFn ((t : ℂ) - wOf ζ)) (Icc (y₀ - δ) (y₀ + δ)) :=
    hcont1.integrableOn_Icc
  have hi2 : IntegrableOn (fun t : ℝ => (1 / (π : ℂ)) * v (wOf ζ) * (1 / ((t : ℂ) - wOf ζ)))
      (Icc (y₀ - δ) (y₀ + δ)) :=
    (continuousOn_const.mul hcont2).integrableOn_Icc
  calc ∫ t in Icc (y₀ - δ) (y₀ + δ), (a t : ℂ) / Complex.sin (π * (ζ - Complex.I * t))
      = ∫ t in Icc (y₀ - δ) (y₀ + δ), Complex.I * (((1 / (π : ℂ)) * dslope v (t : ℂ) (wOf ζ) +
          v (t : ℂ) * kappaFn ((t : ℂ) - wOf ζ)) +
          (1 / (π : ℂ)) * v (wOf ζ) * (1 / ((t : ℂ) - wOf ζ))) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
        have htR : |t - y₀| < R := by
          have : |t - y₀| ≤ δ := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
          linarith
        have := integrand_eqA hζ (hvu t htR)
        simpa [add_assoc] using this
    _ = Complex.I * (nearJ v (y₀ - δ) (y₀ + δ) (wOf ζ) +
          (1 / (π : ℂ)) * v (wOf ζ) * logPart (y₀ - δ) (y₀ + δ) (wOf ζ)) := by
        rw [integral_const_mul, integral_add hi1 hi2, integral_const_mul]
        unfold nearJ
        rw [integral_inv_sub (by linarith) himw]

lemma farPartA_center_re (a' : ℝ → ℝ) (lo hi y₀ : ℝ) :
    (farPartA a' lo hi (Complex.I * (y₀ : ℂ))).re = 0 := by
  unfold farPartA
  have : ∀ t : ℝ, (a' t : ℂ) / Complex.sin (π * (Complex.I * (y₀ : ℂ) - Complex.I * t)) =
      Complex.I * ((a' t / Real.sinh (π * (t - y₀)) : ℝ) : ℂ) := by
    intro t
    rw [sin_arg_eq, wOf_center]
    have : Complex.sinh (π * ((t : ℂ) - y₀)) = ((Real.sinh (π * (t - y₀)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sinh]; push_cast; ring_nf
    rw [this]
    push_cast
    simp only [div_eq_mul_inv, mul_inv, inv_neg, Complex.inv_I]
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_complex_ofReal]
  simp

lemma nearJ_center_imA {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R))
    (hvu : ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (a t : ℂ)) :
    (nearJ v (y₀ - δ) (y₀ + δ) (y₀ : ℂ)).im = 0 := by
  unfold nearJ
  have hw : (y₀ : ℂ) ∈ ball (y₀ : ℂ) δ := mem_ball_self hδ
  have hint : IntegrableOn (fun t : ℝ => (1 / (π : ℂ)) * dslope v (t : ℂ) (y₀ : ℂ) +
      v (t : ℂ) * kappaFn ((t : ℂ) - y₀)) (Icc (y₀ - δ) (y₀ + δ)) :=
    (continuousOn_nearIntegrand hδ2 hδR hv hw).integrableOn_Icc
  have h1 := integral_im (μ := volume.restrict (Icc (y₀ - δ) (y₀ + δ))) hint
  simp only [RCLike.im_to_complex] at h1
  rw [← h1]
  refine integral_eq_zero_of_ae ?_
  have hne : ∀ᵐ t ∂(volume.restrict (Icc (y₀ - δ) (y₀ + δ))), t ≠ y₀ := by
    have : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ y₀ := by
      simpa using (Set.countable_singleton y₀).ae_notMem volume
    exact ae_restrict_of_ae this
  filter_upwards [hne, ae_restrict_mem measurableSet_Icc] with t ht htI
  have htR : |t - y₀| < R := by
    have : |t - y₀| ≤ δ := abs_le.mpr ⟨by linarith [htI.1], by linarith [htI.2]⟩
    linarith
  have hy : |y₀ - y₀| < R := by simp; linarith
  have e1 := hvu t htR
  have e2 := hvu y₀ hy
  have hne' : (t : ℂ) ≠ (y₀ : ℂ) := by exact_mod_cast ht
  have hd : dslope v (t : ℂ) (y₀ : ℂ) = ((t : ℂ) - y₀)⁻¹ * (v (t : ℂ) - v (y₀ : ℂ)) := by
    rw [dslope_symm v (t : ℂ) (y₀ : ℂ), dslope_of_ne v hne', slope_def_module, smul_eq_mul]
  rw [hd, e1, e2]
  unfold kappaFn
  have : ((1 / (π : ℂ)) * (((t : ℂ) - y₀)⁻¹ * ((a t : ℂ) - (a y₀ : ℂ))) +
      (a t : ℂ) * (1 / Complex.sinh (π * ((t : ℂ) - y₀)) - 1 / (π * ((t : ℂ) - y₀)))) =
      (((1 / π) * ((t - y₀)⁻¹ * (a t - a y₀)) + a t * (1 / Real.sinh (π * (t - y₀)) -
        1 / (π * (t - y₀))) : ℝ) : ℂ) := by
    push_cast
    ring_nf
  rw [this]
  exact Complex.ofReal_im _

/-- The boundary real part: `Re H(i y₀) = a(y₀)`. -/
theorem re_contHA_center {y₀ δ R : ℝ} {v : ℂ → ℂ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (hδR : δ < R)
    (hv : DifferentiableOn ℂ v (ball (y₀ : ℂ) R))
    (hvu : ∀ t : ℝ, |t - y₀| < R → v (t : ℂ) = (a t : ℂ)) :
    (contHA a v y₀ δ (Complex.I * (y₀ : ℂ))).re = a y₀ := by
  unfold contHA
  rw [wOf_center, logPart_center y₀ δ]
  have hy : |y₀ - y₀| < R := by simp; linarith
  have e2 := hvu y₀ hy
  have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
  have hnear := nearJ_center_imA hδ hδ2 hδR hv hvu
  have : Complex.I * (nearJ v (y₀ - δ) (y₀ + δ) (y₀ : ℂ) +
      1 / (π : ℂ) * v (y₀ : ℂ) * (-(Complex.I * π))) =
      Complex.I * nearJ v (y₀ - δ) (y₀ + δ) (y₀ : ℂ) + (a y₀ : ℂ) := by
    rw [e2]; field_simp; ring_nf; simp
  rw [this, Complex.add_re, Complex.add_re, farPartA_center_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, hnear]
  simp

end

end FormalResearch.ModularBootstrap.FiveTerm.StripOuter

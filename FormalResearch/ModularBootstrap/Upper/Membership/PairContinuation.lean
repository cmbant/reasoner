module

public import FormalResearch.ModularBootstrap.WeightAxioms.HankelContinuation
public import Mathlib.Analysis.Complex.Liouville

/-!
# Strip continuity and holomorphy of the Hankel continuation of a kernel-integrable profile

`WeightAxioms.continuousOn_hankelContinuationW` and `differentiableOn_hankelContinuationW` are stated
for members of the test class.  The vacuum step of `FW-M` (`fw:FWM` item 3) and of `K7` (`cmb:K7`,
"Vacuum") applies the same argument to the *transform* `ĥ₀` (and to `h₀`) separately, where only

`∫₀^∞ |ψ(t)| K_{c'/12}^{(w)}(t) dt < ∞`   and continuity of `ψ` on `[0, ∞)`

are available ("each with a kernel bounded by `e^{c' L}` against an integrand bounded by `C e^{-πx}`").
This module proves the strip statements under exactly these two hypotheses:

* `continuousOn_hankelContinuationW_of_integrable`: continuity on `{|Im b| ≤ 1/2}`;
* `differentiableOn_hankelContinuationW_of_integrable`: holomorphy on `{|Im b| < 1/2}`.

Holomorphy uses the Cauchy estimate on a small circle inside the strip for the entire family
`b ↦ K_{-c' b²/3}^{(w)}(t)`, instead of the power-series bounds of the test-class proof.
All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms

section Continuation

variable {w : ℕ} {c' : ℝ} {ψ : ℝ → ℝ}

lemma aestronglyMeasurable_kernelIntegrand (hψ : ContinuousOn ψ (Ici 0)) (b : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => (ψ t : ℂ) * kernelKC w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ))
      (volume.restrict (Ioi 0)) :=
  ((Complex.continuous_ofReal.comp_continuousOn (hψ.mono Ioi_subset_Ici_self)).mul
    ((kernelKC_entire_t w _).continuous.comp Complex.continuous_ofReal).continuousOn
      ).aestronglyMeasurable measurableSet_Ioi

lemma norm_kernelIntegrand_le (hw : 1 ≤ w) (hc' : 0 < c') {t : ℝ} (ht : 0 ≤ t) {b : ℂ}
    (hb : |b.im| ≤ 1 / 2) :
    ‖(ψ t : ℂ) * kernelKC w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)‖ ≤
      |ψ t| * kernelK w (c' / 12) t := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_kernelKC_strip_le w hw hc' ht hb) (abs_nonneg _)

/-- The Hankel continuation of a kernel-integrable profile is continuous on the closed strip. -/
theorem continuousOn_hankelContinuationW_of_integrable (hw : 1 ≤ w) (hc' : 0 < c')
    (hψ : ContinuousOn ψ (Ici 0))
    (hint : IntegrableOn (fun t : ℝ => |ψ t| * kernelK w (c' / 12) t) (Ioi 0)) :
    ContinuousOn (hankelContinuationW w c' ψ) {b : ℂ | |b.im| ≤ 1 / 2} := by
  intro b₀ hb₀
  unfold hankelContinuationW
  refine ContinuousWithinAt.mul continuousWithinAt_const ?_
  refine continuousWithinAt_of_dominated
    (bound := fun t => |ψ t| * kernelK w (c' / 12) t) ?_ ?_ hint ?_
  · exact Eventually.of_forall fun b => aestronglyMeasurable_kernelIntegrand hψ b
  · rw [eventually_nhdsWithin_iff]
    refine Eventually.of_forall fun b hb =>
      (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    exact norm_kernelIntegrand_le hw hc' (mem_Ioi.mp ht).le hb
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t _ => ?_)
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : Continuous fun b : ℂ => kernelKC w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ) :=
      (kernelKC_entire_alpha w (t : ℂ)).continuous.comp (by fun_prop)
    exact (continuous_const.mul h1).continuousAt

/-- The Hankel continuation of a kernel-integrable profile is holomorphic on the open strip. -/
theorem differentiableOn_hankelContinuationW_of_integrable (hw : 1 ≤ w) (hc' : 0 < c')
    (hψ : ContinuousOn ψ (Ici 0))
    (hint : IntegrableOn (fun t : ℝ => |ψ t| * kernelK w (c' / 12) t) (Ioi 0)) :
    DifferentiableOn ℂ (hankelContinuationW w c' ψ) {b : ℂ | |b.im| < 1 / 2} := by
  intro b₀ hb₀
  have hb₀' : |b₀.im| < 1 / 2 := hb₀
  refine DifferentiableAt.differentiableWithinAt ?_
  set δ : ℝ := (1 / 2 - |b₀.im|) / 2 with hδ
  have hδ_pos : 0 < δ := by rw [hδ]; linarith
  let S : ℂ → ℂ := besselSC (w - 1)
  have hS : Differentiable ℂ S := besselSC_entire (w - 1)
  have hS' : Continuous (deriv S) := (hS.contDiff (n := 1)).continuous_deriv le_rfl
  let zf : ℂ → ℝ → ℂ := fun b t => 4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * b ^ 2 / 3) * (t : ℂ)
  let F : ℂ → ℝ → ℂ := fun b t => (ψ t : ℂ) * kernelKC w (-(c' : ℂ) * b ^ 2 / 3) (t : ℂ)
  let F' : ℂ → ℝ → ℂ := fun b t =>
    (ψ t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (w - 1) *
      (deriv S (zf b t) * (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (2 * b) / 3) * (t : ℂ))))
  have hF_eq : ∀ b t, F b t = (ψ t : ℂ) * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (w - 1) *
      S (zf b t)) := fun b t => by simp only [F, kernelKC, S, zf]
  have h_hasDeriv : ∀ (t : ℝ) (b : ℂ), HasDerivAt (fun b => F b t) (F' b t) b := by
    intro t b
    have hz : HasDerivAt (fun b : ℂ => zf b t)
        (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (2 * b) / 3) * (t : ℂ)) b := by
      have h1 := ((((hasDerivAt_pow 2 b).const_mul (-(c' : ℂ))).div_const 3).const_mul
        (4 * (Real.pi : ℂ) ^ 2)).mul_const (t : ℂ)
      refine h1.congr_deriv ?_
      simp only [Nat.cast_ofNat]; ring
    have h2 : HasDerivAt (fun b : ℂ => S (zf b t))
        (deriv S (zf b t) * (4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (2 * b) / 3) * (t : ℂ))) b :=
      (hS (zf b t)).hasDerivAt.comp b hz
    have h3 := (h2.const_mul ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (w - 1))).const_mul (ψ t : ℂ)
    have hfun : (fun b => F b t) = fun b : ℂ => (ψ t : ℂ) *
        ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ (w - 1) * S (zf b t)) := funext fun b => hF_eq b t
    rw [hfun]
    exact h3
  have hball_strip : ∀ b ∈ ball b₀ δ, ∀ z ∈ sphere b δ, |z.im| ≤ 1 / 2 := by
    intro b hb z hz
    have h1 : ‖b - b₀‖ < δ := dist_eq_norm b b₀ ▸ mem_ball.mp hb
    have h2 : ‖z - b‖ = δ := dist_eq_norm z b ▸ mem_sphere.mp hz
    have hz1 : |z.im - b₀.im| ≤ ‖z - b₀‖ := by
      simpa [Complex.sub_im] using Complex.abs_im_le_norm (z - b₀)
    have h3 : ‖z - b₀‖ ≤ ‖z - b‖ + ‖b - b₀‖ := by
      calc ‖z - b₀‖ = ‖(z - b) + (b - b₀)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    calc |z.im| = |(z.im - b₀.im) + b₀.im| := by ring_nf
      _ ≤ |z.im - b₀.im| + |b₀.im| := abs_add_le _ _
      _ ≤ 2 * δ + |b₀.im| := by linarith
      _ = 1 / 2 := by rw [hδ]; ring
  have hF'_meas : AEStronglyMeasurable (F' b₀) (volume.restrict (Ioi 0)) := by
    have hcont : ContinuousOn (F' b₀) (Ioi 0) := by
      refine (Complex.continuous_ofReal.comp_continuousOn (hψ.mono Ioi_subset_Ici_self)).mul ?_
      refine Continuous.continuousOn ?_
      have hzc : Continuous fun t : ℝ => zf b₀ t := by simp only [zf]; fun_prop
      have hpow : Continuous fun t : ℝ => (2 * (Real.pi : ℂ) * (t : ℂ)) ^ (w - 1) := by fun_prop
      have hD : Continuous fun t : ℝ => deriv S (zf b₀ t) := hS'.comp hzc
      have hlin : Continuous fun t : ℝ =>
          4 * (Real.pi : ℂ) ^ 2 * (-(c' : ℂ) * (2 * b₀) / 3) * (t : ℂ) := by fun_prop
      exact hpow.mul (hD.mul hlin)
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have h_bound : ∀ᵐ t ∂(volume.restrict (Ioi 0)), ∀ b ∈ ball b₀ δ,
      ‖F' b t‖ ≤ (|ψ t| * kernelK w (c' / 12) t) / δ := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht b hb => ?_)
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hdiff : Differentiable ℂ (fun b => F b t) := fun b => (h_hasDeriv t b).differentiableAt
    have hC : ∀ z ∈ sphere b δ, ‖F z t‖ ≤ |ψ t| * kernelK w (c' / 12) t := fun z hz =>
      norm_kernelIntegrand_le hw hc' ht0 (hball_strip b hb z hz)
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ_pos hdiff.diffContOnCl hC
    rwa [(h_hasDeriv t b).deriv] at this
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds b₀ hδ_pos)
    (Eventually.of_forall fun b => aestronglyMeasurable_kernelIntegrand hψ b)
    (by
      refine hint.mono' (aestronglyMeasurable_kernelIntegrand hψ b₀)
        ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
      exact norm_kernelIntegrand_le hw hc' (mem_Ioi.mp ht).le (le_of_lt hb₀'))
    hF'_meas h_bound (hint.div_const δ)
    (Eventually.of_forall fun t b _ => h_hasDeriv t b)).2
  unfold hankelContinuationW
  exact (hd.const_mul (-2 * (Real.pi : ℂ))).differentiableAt

end Continuation

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.continuousOn_hankelContinuationW_of_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuousOn_hankelContinuationW_of_integrable

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.differentiableOn_hankelContinuationW_of_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms differentiableOn_hankelContinuationW_of_integrable

end FormalResearch.ModularBootstrap.Upper.Membership

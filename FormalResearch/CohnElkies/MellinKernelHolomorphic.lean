module

public import FormalResearch.CohnElkies.MellinKernel
public import FormalResearch.CohnElkies.ComplexEdgePhase

/-!
# Holomorphy of the Mellin-strip kernel on the strip `|Re ζ| < 1`

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1co:O5`(1) (the contour shift of
`I_main` to `Re w = 1` needs `K₀(ε w, ξ)` holomorphic on `0 < Re w < ε⁻¹`).

* `differentiableAt_stripS0Tilde`: `S̃₀(ζ) = ∫₀¹ g(s ζ) ζ ds` is holomorphic on `|Re ζ| < 1` (differentiation
  under the integral; `g = stripG` is holomorphic there by `differentiableOn_stripG`);
* `differentiableOn_mellinK0`: `ζ ↦ K₀(ζ, ξ)` is holomorphic on `|Re ζ| < 1`.

Status: proved, unconditional.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory Metric
open scoped Real

namespace FormalResearch.CohnElkies

lemma continuousOn_deriv_stripG : ContinuousOn (deriv stripG) edgeStrip :=
  (differentiableOn_stripG.analyticOnNhd isOpen_edgeStrip).deriv.continuousOn

/-- `S̃₀` is holomorphic on the strip `|Re ζ| < 1`. -/
lemma differentiableAt_stripS0Tilde {ζ₀ : ℂ} (h : |ζ₀.re| < 1) : DifferentiableAt ℂ stripS0Tilde ζ₀ := by
  set r : ℝ := (1 - |ζ₀.re|) / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hball : ∀ ζ ∈ closedBall ζ₀ r, |ζ.re| < 1 := fun ζ hζ => by
    have h1 : ‖ζ - ζ₀‖ ≤ r := by simpa [dist_eq_norm] using mem_closedBall.mp hζ
    have h2 : |ζ.re - ζ₀.re| ≤ r := (Complex.abs_re_le_norm _).trans (by simpa using h1)
    have h3 : |ζ.re| ≤ |ζ₀.re| + r := by
      calc |ζ.re| = |ζ₀.re + (ζ.re - ζ₀.re)| := by ring_nf
        _ ≤ |ζ₀.re| + |ζ.re - ζ₀.re| := abs_add_le _ _
        _ ≤ _ := by linarith
    rw [hrdef] at h3; linarith
  set K : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' (Icc (0 : ℝ) 1 ×ˢ closedBall ζ₀ r) with hK
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall _ _)).image (by fun_prop)
  have hKs : K ⊆ edgeStrip := by
    rintro _ ⟨⟨s, ζ⟩, ⟨hs, hζ⟩, rfl⟩
    simp only [edgeStrip, mem_setOf_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [abs_mul, abs_of_nonneg hs.1]
    have := hball ζ hζ
    nlinarith [abs_nonneg ζ.re, hs.2]
  obtain ⟨MG, hMG⟩ := hKc.exists_bound_of_continuousOn (continuousOn_stripG.mono hKs)
  obtain ⟨MG', hMG'⟩ := hKc.exists_bound_of_continuousOn (continuousOn_deriv_stripG.mono hKs)
  have hmemK : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall ζ₀ r, (t : ℂ) * x ∈ K := fun t ht x hx =>
    ⟨(t, x), ⟨ht, hx⟩, rfl⟩
  have hnx : ∀ x ∈ ball ζ₀ r, ‖x‖ ≤ ‖ζ₀‖ + r := fun x hx => by
    have : ‖x - ζ₀‖ < r := by simpa [dist_eq_norm] using mem_ball.mp hx
    calc ‖x‖ = ‖ζ₀ + (x - ζ₀)‖ := by ring_nf
      _ ≤ ‖ζ₀‖ + ‖x - ζ₀‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  have hcontG : ∀ x ∈ closedBall ζ₀ r, ContinuousOn (fun t : ℝ => stripG ((t : ℂ) * x)) (Icc 0 1) := fun x hx =>
    continuousOn_stripG.comp (by fun_prop) fun t ht => hKs (hmemK t ht x hx)
  have hcontG' : ∀ x ∈ closedBall ζ₀ r, ContinuousOn (fun t : ℝ => deriv stripG ((t : ℂ) * x)) (Icc 0 1) := fun x hx =>
    continuousOn_deriv_stripG.comp (by fun_prop) fun t ht => hKs (hmemK t ht x hx)
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (a := 0) (b := 1) (μ := volume)
    (F := fun (x : ℂ) (t : ℝ) => stripG ((t : ℂ) * x) * x)
    (F' := fun (x : ℂ) (t : ℝ) => deriv stripG ((t : ℂ) * x) * (t : ℂ) * x + stripG ((t : ℂ) * x))
    (x₀ := ζ₀) (s := ball ζ₀ r) (bound := fun _ => MG' * (‖ζ₀‖ + r) + MG) (ball_mem_nhds ζ₀ hr)
    ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · exact key.2.differentiableAt
  · refine Filter.eventually_of_mem (ball_mem_nhds ζ₀ hr) fun x hx => ?_
    have := ((hcontG x (ball_subset_closedBall hx)).mul (continuousOn_const (c := x)))
    rw [uIoc_of_le zero_le_one]
    exact (this.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · have := ((hcontG ζ₀ (mem_closedBall_self hr.le)).mul (continuousOn_const (c := ζ₀)))
    exact (this.mono (by rw [uIcc_of_le zero_le_one])).intervalIntegrable
  · have h1 := ((hcontG' ζ₀ (mem_closedBall_self hr.le)).mul (by fun_prop : ContinuousOn (fun t : ℝ => (t : ℂ)) (Icc 0 1))).mul
      (continuousOn_const (c := ζ₀))
    have h2 := (h1.add (hcontG ζ₀ (mem_closedBall_self hr.le)))
    rw [uIoc_of_le zero_le_one]
    exact (h2.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc := ball_subset_closedBall hx
    have hG := hMG _ (hmemK t ht' x hxc)
    have hG' := hMG' _ (hmemK t ht' x hxc)
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
    have hx' := hnx x hx
    calc ‖deriv stripG ((t : ℂ) * x) * (t : ℂ) * x + stripG ((t : ℂ) * x)‖
        ≤ ‖deriv stripG ((t : ℂ) * x)‖ * ‖(t : ℂ)‖ * ‖x‖ + ‖stripG ((t : ℂ) * x)‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul, norm_mul]
      _ ≤ MG' * 1 * (‖ζ₀‖ + r) + MG := by
          have : 0 ≤ MG' := (norm_nonneg _).trans hG'
          gcongr
      _ = _ := by ring
  · refine Filter.Eventually.of_forall fun t ht x hx => ?_
    rw [uIoc_of_le zero_le_one] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc := ball_subset_closedBall hx
    have hmem : (t : ℂ) * x ∈ edgeStrip := hKs (hmemK t ht' x hxc)
    have hG : HasDerivAt stripG (deriv stripG ((t : ℂ) * x)) ((t : ℂ) * x) :=
      ((differentiableOn_stripG.differentiableAt (isOpen_edgeStrip.mem_nhds hmem))).hasDerivAt
    have h1 : HasDerivAt (fun y : ℂ => (t : ℂ) * y) (t : ℂ) x := by
      simpa using (hasDerivAt_id x).const_mul (t : ℂ)
    have hc2 : HasDerivAt (fun y : ℂ => stripG ((t : ℂ) * y)) (deriv stripG ((t : ℂ) * x) * (t : ℂ)) x := hG.comp x h1
    have := hc2.fun_mul (hasDerivAt_id x)
    simpa using this

lemma differentiableOn_stripS0Tilde : DifferentiableOn ℂ stripS0Tilde edgeStrip := fun ζ hζ =>
  (differentiableAt_stripS0Tilde hζ).differentiableWithinAt

/-- **The Mellin-strip kernel `K₀(·, ξ)` is holomorphic on `|Re ζ| < 1`.** -/
theorem differentiableOn_mellinK0 {c : ℝ} (hc : 0 < c) (ξ : ℝ) :
    DifferentiableOn ℂ (fun ζ : ℂ => mellinK0 c ζ ξ) edgeStrip := by
  intro ζ hζ
  have hζ' : |ζ.re| < 1 := hζ
  have hre : 0 < (1 - ζ).re := by simp; linarith [(abs_lt.mp hζ').2]
  have hat : DifferentiableAt ℂ (fun ζ : ℂ => mellinK0 c ζ ξ) ζ := by
    unfold mellinK0 mellinPhi
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => (1 - ζ) ^ (-(1 / 2 : ℂ))) ζ :=
      (differentiableAt_const _ |>.sub differentiableAt_id).cpow (differentiableAt_const _)
        (Complex.mem_slitPlane_iff.mpr (Or.inl hre))
    have hbin : DifferentiableAt ℂ (fun ζ : ℂ => FormalResearch.Asymptotics.binetDiff c ζ) ζ := by
      unfold FormalResearch.Asymptotics.binetDiff
      have hw : 0 < ((c : ℂ) * (1 - ζ)).re := by simp at hre ⊢; exact mul_pos hc (sub_pos.mpr hre)
      have hd := (FormalResearch.Asymptotics.binetRem_differentiableOn ((c : ℂ) * (1 - ζ)) hw).differentiableAt
        (isOpen_lt continuous_const Complex.continuous_re |>.mem_nhds hw)
      have hlin : DifferentiableAt ℂ (fun ζ : ℂ => (c : ℂ) * (1 - ζ)) ζ :=
        (differentiableAt_const _).mul ((differentiableAt_const _).sub differentiableAt_id)
      exact (hd.comp ζ hlin).sub (differentiableAt_const _)
    have hS := differentiableAt_stripS0Tilde hζ'
    have hph : DifferentiableAt ℂ (fun ζ : ℂ => stripS0Tilde ζ + ζ * Complex.log (Real.pi ^ 2 * ξ)) ζ :=
      hS.add (differentiableAt_id.mul (differentiableAt_const _))
    exact (h1.mul (hbin.cexp)).mul ((differentiableAt_const _).mul hph).cexp
  exact hat.differentiableWithinAt

/-- info: 'FormalResearch.CohnElkies.differentiableAt_stripS0Tilde' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms differentiableAt_stripS0Tilde
/-- info: 'FormalResearch.CohnElkies.differentiableOn_mellinK0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms differentiableOn_mellinK0

end FormalResearch.CohnElkies

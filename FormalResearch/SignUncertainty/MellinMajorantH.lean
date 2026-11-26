module

public import FormalResearch.Special.ComplexStirlingBinet
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The phase `ℋ` of the Mellin majorant on a neighbourhood of the closed strip (`gt:7.4(2)`)

`fourier_mellin.tex`, `gt:7.4(2)`: `ℋ(ζ) = ∫_0^ζ log R(z) dz`, `R(z) = (1-z) tan(πz/2)/z =
Γ((1+z)/2) Γ((3-z)/2) / (Γ((2+z)/2) Γ((2-z)/2))`. Here the holomorphic logarithm of `R` on `-1 < Re z < 2`
is `hLog z`, the combination of four copies of the Binet branch `binetLogGamma` of `log Γ`; the symmetry
`R(1-z) = 1/R(z)` is then the exact identity `hLog (1-z) = - hLog z` (no branch bookkeeping).

* `hLog`, `hLog_one_sub`: the holomorphic log of `R` and its symmetry (`exp_hLog` is in `MellinMajorantHId`).
* `hInt ζ = ∫_0^1 ζ hLog(s ζ) ds` (`ℋ`), `hasDerivAt_hInt`: `ℋ' = hLog` on `-1 < Re ζ < 2`.
* `hInt_one`, `hInt_one_sub`: `ℋ(1) = 0` and `ℋ(1-ζ) = ℋ(ζ)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.Special.ComplexStirling

/-- The open strip `-1 < Re z < 2` carrying the holomorphic logarithm of `R`. -/
def hStrip : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < 2}

lemma isOpen_hStrip : IsOpen hStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma convex_hStrip : Convex ℝ hStrip :=
  (convex_halfSpace_re_gt (-1)).inter (convex_halfSpace_re_lt 2)

lemma zero_mem_hStrip : (0 : ℂ) ∈ hStrip := by simp [hStrip]

lemma mem_hStrip_one_sub {z : ℂ} : 1 - z ∈ hStrip ↔ z ∈ hStrip := by
  simp only [hStrip, mem_ofPred_eq, Complex.sub_re, Complex.one_re]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The holomorphic logarithm of `R(z) = Γ((1+z)/2) Γ((3-z)/2) / (Γ((2+z)/2) Γ((2-z)/2))`. -/
noncomputable def hLog (z : ℂ) : ℂ :=
  binetLogGamma ((1 + z) / 2) + binetLogGamma ((3 - z) / 2) -
    binetLogGamma ((2 + z) / 2) - binetLogGamma ((2 - z) / 2)

/-- The derivative of `hLog`. -/
noncomputable def hLogDeriv (z : ℂ) : ℂ :=
  Complex.digamma ((1 + z) / 2) * (1 / 2) + Complex.digamma ((3 - z) / 2) * (-(1 / 2)) -
    Complex.digamma ((2 + z) / 2) * (1 / 2) - Complex.digamma ((2 - z) / 2) * (-(1 / 2))

lemma hLog_one_sub (z : ℂ) : hLog (1 - z) = -hLog z := by
  unfold hLog
  have e1 : (1 + (1 - z)) / 2 = (2 - z) / 2 := by ring
  have e2 : (3 - (1 - z)) / 2 = (2 + z) / 2 := by ring
  have e3 : (2 + (1 - z)) / 2 = (3 - z) / 2 := by ring
  have e4 : (2 - (1 - z)) / 2 = (1 + z) / 2 := by ring
  rw [e1, e2, e3, e4]
  ring

lemma hasDerivAt_hLog {z : ℂ} (hz : z ∈ hStrip) : HasDerivAt hLog (hLogDeriv z) z := by
  obtain ⟨h1, h2⟩ := hz
  have hd : ∀ (a b : ℂ), 0 < ((a + b * z) / 2).re → HasDerivAt (fun w : ℂ => binetLogGamma ((a + b * w) / 2))
      (Complex.digamma ((a + b * z) / 2) * (b / 2)) z := by
    intro a b hre
    have h : HasDerivAt (fun w : ℂ => (a + b * w) / 2) (b / 2) z := by
      simpa using ((hasDerivAt_const z a).add ((hasDerivAt_id z).const_mul b)).div_const 2
    exact (hasDerivAt_binetLogGamma hre).comp z h
  have d1 := hd 1 1 (by simp; linarith)
  have d2 := hd 3 (-1) (by simp; linarith)
  have d3 := hd 2 1 (by simp; linarith)
  have d4 := hd 2 (-1) (by simp; linarith)
  have := ((d1.add d2).sub d3).sub d4
  convert this using 1
  · ext w; simp [hLog]; ring_nf
  · simp [hLogDeriv]; ring_nf


lemma continuousOn_hLog : ContinuousOn hLog hStrip := fun _ hz =>
  (hasDerivAt_hLog hz).continuousAt.continuousWithinAt

lemma continuousOn_hLogDeriv : ContinuousOn hLogDeriv hStrip := by
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨h1, h2⟩ := hz
  have hdig : ∀ (a b : ℂ), 0 < ((a + b * z) / 2).re →
      ContinuousAt (fun w : ℂ => Complex.digamma ((a + b * w) / 2)) z := by
    intro a b hre
    exact ContinuousAt.comp (f := fun w : ℂ => (a + b * w) / 2) (g := Complex.digamma)
      (hasDerivAt_digamma_binet hre).continuousAt (by fun_prop)
  have d1 := hdig 1 1 (by simp; linarith)
  have d2 := hdig 3 (-1) (by simp; linarith)
  have d3 := hdig 2 1 (by simp; linarith)
  have d4 := hdig 2 (-1) (by simp; linarith)
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at d1 d2 d3 d4
  exact (((d1.mul_const (1 / 2 : ℂ)).add (d2.mul_const (-(1 / 2) : ℂ))).sub
    (d3.mul_const (1 / 2 : ℂ))).sub (d4.mul_const (-(1 / 2) : ℂ))

/-- `ℋ(ζ) = ∫_0^ζ hLog = ∫_0^1 ζ hLog(s ζ) ds`. -/
noncomputable def hInt (ζ : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, ζ * hLog ((s : ℂ) * ζ)

lemma smul_mem_hStrip {ζ : ℂ} (hζ : ζ ∈ hStrip) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (s : ℂ) * ζ ∈ hStrip := by
  have := convex_hStrip zero_mem_hStrip hζ (sub_nonneg.mpr hs.2) hs.1 (by ring)
  simpa [Complex.real_smul] using this

/-- `ℋ' = hLog` on the strip `-1 < Re ζ < 2`. -/
theorem hasDerivAt_hInt {ζ0 : ℂ} (hζ0 : ζ0 ∈ hStrip) : HasDerivAt hInt (hLog ζ0) ζ0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_hStrip ζ0 hζ0
  set ρ : ℝ := r / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  have hcb : Metric.closedBall ζ0 ρ ⊆ hStrip := fun z hz =>
    hball (Metric.closedBall_subset_ball (by rw [hρ]; linarith) hz)
  have hb : Metric.ball ζ0 ρ ⊆ hStrip := Metric.ball_subset_closedBall.trans hcb
  let K : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' (Icc (0 : ℝ) 1 ×ˢ Metric.closedBall ζ0 ρ)
  have hKc : IsCompact K :=
    (isCompact_Icc.prod (isCompact_closedBall ζ0 ρ)).image (by fun_prop)
  have hKs : K ⊆ hStrip := by
    rintro _ ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
    exact smul_mem_hStrip (hcb hz) hs
  obtain ⟨B1, hB1⟩ := hKc.exists_bound_of_continuousOn (continuousOn_hLog.mono hKs)
  obtain ⟨B2, hB2⟩ := hKc.exists_bound_of_continuousOn (continuousOn_hLogDeriv.mono hKs)
  let F : ℂ → ℝ → ℂ := fun ζ s => ζ * hLog ((s : ℂ) * ζ)
  let F' : ℂ → ℝ → ℂ := fun ζ s => hLog ((s : ℂ) * ζ) + ζ * (hLogDeriv ((s : ℂ) * ζ) * (s : ℂ))
  have hmeasF : ∀ ζ ∈ hStrip, AEStronglyMeasurable (F ζ) (volume.restrict (Ι (0 : ℝ) 1)) := by
    intro ζ hζ
    rw [Set.uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine continuousOn_const.mul ?_
    exact (continuousOn_hLog.comp (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ).continuousOn
      fun s hs => smul_mem_hStrip hζ ⟨hs.1.le, hs.2⟩)
  have hmeasF' : AEStronglyMeasurable (F' ζ0) (volume.restrict (Ι (0 : ℝ) 1)) := by
    rw [Set.uIoc_of_le zero_le_one]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    have hc : ContinuousOn (fun s : ℝ => (s : ℂ) * ζ0) (Icc (0 : ℝ) 1) :=
      (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ0).continuousOn
    have h1 := continuousOn_hLog.comp hc fun s hs => smul_mem_hStrip hζ0 hs
    have h2 := continuousOn_hLogDeriv.comp hc fun s hs => smul_mem_hStrip hζ0 hs
    exact (h1.add (continuousOn_const.mul (h2.mul Complex.continuous_ofReal.continuousOn))).mono
      Ioc_subset_Icc_self
  have hFint : IntervalIntegrable (F ζ0) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    have hc : ContinuousOn (F ζ0) (Icc (0 : ℝ) 1) :=
      continuousOn_const.mul (continuousOn_hLog.comp
        (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ0).continuousOn
        fun s hs => smul_mem_hStrip hζ0 hs)
    exact (hc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F')
    (x₀ := ζ0) (s := Metric.ball ζ0 ρ) (a := 0) (b := 1) (μ := volume)
    (bound := fun _ => B1 + (‖ζ0‖ + ρ) * B2) (Metric.ball_mem_nhds ζ0 hρ0)
    (Filter.eventually_of_mem (Metric.ball_mem_nhds ζ0 hρ0) fun ζ hζ => hmeasF ζ (hb hζ))
    hFint hmeasF' ?_ intervalIntegrable_const ?_
  · have hderiv : ∫ s in (0 : ℝ)..1, F' ζ0 s = hLog ζ0 := by
      have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (s : ℂ) * hLog ((s : ℂ) * ζ0))
          (hLog ((s : ℂ) * ζ0) + (s : ℂ) * (hLogDeriv ((s : ℂ) * ζ0) * ζ0)) s := by
        intro s hs
        rw [uIcc_of_le zero_le_one] at hs
        have hmem := smul_mem_hStrip hζ0 hs
        have hinner : HasDerivAt (fun w : ℂ => w * ζ0) ζ0 (s : ℂ) := by
          simpa using (hasDerivAt_id (s : ℂ)).mul_const ζ0
        have h1 := (hasDerivAt_hLog hmem).comp (s : ℂ) hinner
        have h2 := (hasDerivAt_id (s : ℂ)).mul h1
        have h3 := h2.comp_ofReal
        exact h3.congr_deriv (by simp [Function.comp])
      have hint : IntervalIntegrable (fun s : ℝ => hLog ((s : ℂ) * ζ0) + (s : ℂ) *
          (hLogDeriv ((s : ℂ) * ζ0) * ζ0)) volume 0 1 := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        have hc : ContinuousOn (fun s : ℝ => (s : ℂ) * ζ0) (Icc (0 : ℝ) 1) :=
          (by fun_prop : Continuous fun s : ℝ => (s : ℂ) * ζ0).continuousOn
        have h1 := continuousOn_hLog.comp hc fun s hs => smul_mem_hStrip hζ0 hs
        have h2 := continuousOn_hLogDeriv.comp hc fun s hs => smul_mem_hStrip hζ0 hs
        exact ((h1.add (Complex.continuous_ofReal.continuousOn.mul
          (h2.mul continuousOn_const))).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
      simp only [Complex.ofReal_one, one_mul, Complex.ofReal_zero, zero_mul, sub_zero] at this
      rw [← this]
      refine intervalIntegral.integral_congr fun s _ => ?_
      simp only [F']
      ring
    rw [hderiv] at h
    exact h.2
  · refine Eventually.of_forall fun s hs ζ hζ => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hmemK : (s : ℂ) * ζ ∈ K := ⟨(s, ζ), ⟨hs', Metric.ball_subset_closedBall hζ⟩, rfl⟩
    simp only [F']
    calc ‖hLog ((s : ℂ) * ζ) + ζ * (hLogDeriv ((s : ℂ) * ζ) * (s : ℂ))‖
        ≤ ‖hLog ((s : ℂ) * ζ)‖ + ‖ζ‖ * (‖hLogDeriv ((s : ℂ) * ζ)‖ * ‖(s : ℂ)‖) := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ B1 + (‖ζ0‖ + ρ) * B2 := by
          have hζn : ‖ζ‖ ≤ ‖ζ0‖ + ρ := by
            have := norm_le_of_mem_closedBall (Metric.ball_subset_closedBall hζ)
            have h2 := norm_sub_le_norm_sub_add_norm_sub ζ ζ0 0
            simp only [sub_zero] at h2
            rw [mem_ball_iff_norm] at hζ
            linarith [norm_sub_rev ζ ζ0]
          have hsn : ‖(s : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]; exact hs'.2
          have hb2 := hB2 _ hmemK
          have hb1 := hB1 _ hmemK
          have h0 : 0 ≤ ‖hLogDeriv ((s : ℂ) * ζ)‖ := norm_nonneg _
          have hB2' : 0 ≤ B2 := le_trans (norm_nonneg _) hb2
          calc ‖hLog ((s : ℂ) * ζ)‖ + ‖ζ‖ * (‖hLogDeriv ((s : ℂ) * ζ)‖ * ‖(s : ℂ)‖)
              ≤ B1 + (‖ζ0‖ + ρ) * (B2 * 1) := by
                gcongr
            _ = _ := by ring
  · refine Eventually.of_forall fun s hs ζ hζ => ?_
    rw [Set.uIoc_of_le zero_le_one] at hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2⟩
    have hmem := smul_mem_hStrip (hb hζ) hs'
    have hinner : HasDerivAt (fun w : ℂ => (s : ℂ) * w) (s : ℂ) ζ := by
      simpa using (hasDerivAt_id ζ).const_mul (s : ℂ)
    have h1 := (hasDerivAt_hLog hmem).comp ζ hinner
    have h2 := (hasDerivAt_id ζ).mul h1
    refine h2.congr_deriv ?_
    simp only [F', Function.comp, id]
    ring


lemma hInt_zero : hInt 0 = 0 := by simp [hInt]

/-- `ℋ(1) = 0`: `∫_0^1 log R = 0` by the antisymmetry `hLog (1 - x) = - hLog x`. -/
theorem hInt_one : hInt 1 = 0 := by
  have h1 : hInt 1 = ∫ s in (0 : ℝ)..1, hLog (s : ℂ) := by simp [hInt]
  have h2 : ∫ s in (0 : ℝ)..1, hLog (s : ℂ) = ∫ s in (0 : ℝ)..1, hLog ((1 - s : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun s : ℝ => hLog (s : ℂ)) 1]
    simp
  have h3 : ∫ s in (0 : ℝ)..1, hLog ((1 - s : ℝ) : ℂ) = -∫ s in (0 : ℝ)..1, hLog (s : ℂ) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun s _ => ?_
    push_cast
    exact hLog_one_sub _
  have h4 := h2.trans h3
  rw [h1]
  linear_combination (1 / 2 : ℂ) * h4

/-- `ℋ(1 - ζ) = ℋ(ζ)` on `-1 < Re ζ < 2`. -/
theorem hInt_one_sub {ζ : ℂ} (hζ : ζ ∈ hStrip) : hInt (1 - ζ) = hInt ζ := by
  set g : ℂ → ℂ := fun z => hInt (1 - z) - hInt z with hg
  have hgd : ∀ z ∈ hStrip, HasDerivAt g 0 z := by
    intro z hz
    have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub 1
    have h2 := (hasDerivAt_hInt (mem_hStrip_one_sub.mpr hz)).comp z h1
    have h3 := h2.sub (hasDerivAt_hInt hz)
    refine h3.congr_deriv ?_
    rw [hLog_one_sub]
    ring
  have hconst := isOpen_hStrip.is_const_of_deriv_eq_zero convex_hStrip.isPreconnected
    (fun x hx => (hgd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hgd x hx).deriv) hζ zero_mem_hStrip
  have h0 : g 0 = 0 := by simp [hg, hInt_one, hInt_zero]
  have := hconst.trans h0
  simpa [hg, sub_eq_zero] using this

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_hInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_hInt

/-- info: 'FormalResearch.SignUncertainty.hInt_one_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hInt_one_sub

end FormalResearch.SignUncertainty

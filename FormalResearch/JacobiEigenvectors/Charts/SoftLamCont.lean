module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.Charts.PCExact
public import FormalResearch.JacobiEigenvectors.Charts.PCSmooth
public import FormalResearch.JacobiEigenvectors.Charts.PCPositive
public import FormalResearch.JacobiEigenvectors.Charts.PCEnvelopeAssembled
public import FormalResearch.JacobiEigenvectors.Charts.SoftParabolicCylinder
public import FormalResearch.JacobiEigenvectors.Engine.Casoratian

/-!
# Paper J, charts (WP1a): continuity of `λ_L` across `a = 0` (`SoftEdgeChart.lamL_cont`)

Source: Paper J `app_thmA.tex` Step 6 ("`λ_L` is real, continuous and non-vanishing in `X`").
Between `a ≤ 0` and `a > 0`, the second branch `pcMinus · 1 z` changes its scalar normalisation:
* for `a ≤ 0`: `pcMinus 1 a z = -√(π/2) κ_bal(a)⁻¹ pcV a (-z)` (`= -2^{-1/2} π^{1/4} pcU 0 z` at `a = 0`);
* for `a > 0`: `pcMinus 1 a z = -κ_bal(a) pcU a z` (`→ -2^{-1/4} pcU 0 z` as `a → 0⁺`).
These two scalar multiples do NOT agree at `a = 0` (`2^{-1/2} π^{1/4} ≠ 2^{-1/4}`), yet inside the quotient
`λ_L = cas A ψ_W (φ_2^{(2)}) j₁ / cas A (φ_2^{(1)} / κ_bal a) (φ_2^{(2)}) j₁`
any nonzero scalar factor on `φ_2^{(2)}` cancels between numerator and denominator!
Replacing `pcMinus 1 a z` by the continuous renormalised branch `pcBranch1Cont a z` (defined by
`-√π pcV a (-z)` for `a ≤ 0` and `-pcU a z` for `a > 0`, which join continuously at `a = 0` by
`pc_reflect_V 0 z`) exhibits `λ_L` as a quotient of two continuous functions with nonvanishing denominator.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Engine

/-- Branch 1 of `pcMinus`, rescaled by a positive `a`-dependent scalar so it is continuous across `a = 0`:
for `a ≤ 0`, `-√π * pcV a (-z)`; for `a > 0`, `-pcU a z`. -/
def pcBranch1Cont (a z : ℝ) : ℝ :=
  if a ≤ 0 then -(Real.sqrt Real.pi * pcV a (-z)) else -pcU a z

/-- The positive scalar relating `pcMinus pcU pcV a 1 z = pcBranch1Scale a * pcBranch1Cont a z`. -/
def pcBranch1Scale (a : ℝ) : ℝ :=
  if a ≤ 0 then Real.sqrt (Real.pi / 2) / (kappaBal a * Real.sqrt Real.pi) else kappaBal a

lemma pcBranch1Scale_pos (a : ℝ) : 0 < pcBranch1Scale a := by
  unfold pcBranch1Scale
  split_ifs
  · exact div_pos (Real.sqrt_pos.mpr (by positivity))
      (mul_pos (kappaBal_pos a) (Real.sqrt_pos.mpr Real.pi_pos))
  · exact kappaBal_pos a

lemma pcMinus_one_eq_scale (a z : ℝ) :
    pcMinus pcU pcV a 1 z = pcBranch1Scale a * pcBranch1Cont a z := by
  unfold pcMinus pcBranch1Scale pcBranch1Cont
  split_ifs with ha
  · unfold vt
    have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hk : kappaBal a ≠ 0 := (kappaBal_pos a).ne'
    field_simp [hpi, hk]
  · ring

lemma pcBranch1Cont_zero (z : ℝ) :
    -(Real.sqrt Real.pi * pcV 0 (-z)) = -pcU 0 z := by
  have h := pc_reflect_V 0 z
  simp only [mul_zero, Real.cos_zero, Real.sin_zero, sub_zero, zero_mul, add_zero] at h
  have hG : Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  rw [h, hG]
  have hpi : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp [hpi]

private lemma continuous_if_fst_le {f g : ℝ × ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h0 : ∀ z, f (0, z) = g (0, z)) :
    Continuous (fun p : ℝ × ℝ => if p.1 ≤ 0 then f p else g p) := by
  let S1 : Set (ℝ × ℝ) := {p | p.1 ≤ 0}
  let S2 : Set (ℝ × ℝ) := {p | 0 ≤ p.1}
  have hS1 : IsClosed S1 := isClosed_le continuous_fst continuous_const
  have hS2 : IsClosed S2 := isClosed_le continuous_const continuous_fst
  have hu : S1 ∪ S2 = Set.univ := by
    ext p; simp only [Set.mem_union, Set.mem_univ, iff_true]; exact le_total p.1 0
  rw [← continuousOn_univ, ← hu]
  refine ContinuousOn.union_of_isClosed ?_ ?_ hS1 hS2
  · refine hf.continuousOn.congr fun p hp => ?_
    have hp' : p.1 ≤ 0 := hp
    simp [hp']
  · refine hg.continuousOn.congr fun p hp => ?_
    have hp' : 0 ≤ p.1 := hp
    rcases eq_or_lt_of_le hp' with h | h
    · have : p = (0, p.2) := Prod.ext h.symm rfl
      rw [this, ite_eq_left (le_refl _), h0]
    · simp [not_le.mpr h]

lemma continuous_pcBranch1Cont : Continuous (fun p : ℝ × ℝ => pcBranch1Cont p.1 p.2) := by
  have hc1 : Continuous (fun p : ℝ × ℝ => -(Real.sqrt Real.pi * pcV p.1 (-p.2))) :=
    ((pcSmoothFacts.cont_V.comp (continuous_fst.prodMk continuous_snd.neg)).const_mul _).neg
  have hc2 : Continuous (fun p : ℝ × ℝ => -pcU p.1 p.2) := pcSmoothFacts.cont_U.neg
  exact (continuous_if_fst_le hc1 hc2 pcBranch1Cont_zero).congr fun p => rfl

/-- Continuous `z`-derivative of `pcBranch1Cont a` across `a = 0`. -/
lemma continuous_deriv_pcBranch1Cont :
    Continuous (fun p : ℝ × ℝ => deriv (pcBranch1Cont p.1) p.2) := by
  have hderiv_neg : ∀ a z, deriv (fun w => -(Real.sqrt Real.pi * pcV a (-w))) z =
      Real.sqrt Real.pi * deriv (pcV a) (-z) := fun a z => by
    have hd : HasDerivAt (fun w : ℝ => -(Real.sqrt Real.pi * pcV a (-w)))
        (-(Real.sqrt Real.pi * (pcVD a (-z) * (-1)))) z :=
      ((hasDerivAt_pcV a (-z)).comp z (hasDerivAt_neg z)).const_mul _ |>.neg
    rw [hd.deriv, deriv_pcV]; ring
  have hderiv_pos : ∀ a z, deriv (fun w => -pcU a w) z = -deriv (pcU a) z := fun a z => by
    exact (hasDerivAt_pcU a z).neg.deriv.trans (by rw [deriv_pcU])
  have hdeq : ∀ p : ℝ × ℝ, deriv (pcBranch1Cont p.1) p.2 =
      if p.1 ≤ 0 then Real.sqrt Real.pi * deriv (pcV p.1) (-p.2) else -deriv (pcU p.1) p.2 := by
    intro ⟨a, z⟩
    dsimp only
    by_cases ha : a ≤ 0
    · simp only [ha, ↓reduceIte]
      have hfn : pcBranch1Cont a = fun w => -(Real.sqrt Real.pi * pcV a (-w)) :=
        funext fun w => by simp [pcBranch1Cont, ha]
      rw [hfn, hderiv_neg]
    · simp only [ha, ↓reduceIte]
      have hfn : pcBranch1Cont a = fun w => -pcU a w := funext fun w => by simp [pcBranch1Cont, ha]
      rw [hfn, hderiv_pos]
  have hz0 : ∀ z, Real.sqrt Real.pi * deriv (pcV 0) (-z) = -deriv (pcU 0) z := fun z => by
    have hfn : (fun w => -(Real.sqrt Real.pi * pcV 0 (-w))) = fun w => -pcU 0 w :=
      funext pcBranch1Cont_zero
    have h1 := congrFun (congrArg deriv hfn) z
    rwa [hderiv_neg, hderiv_pos] at h1
  have hc1 : Continuous (fun p : ℝ × ℝ => Real.sqrt Real.pi * deriv (pcV p.1) (-p.2)) :=
    (cont_pcVD.comp (continuous_fst.prodMk continuous_snd.neg)).const_mul _
  have hc2 : Continuous (fun p : ℝ × ℝ => -deriv (pcU p.1) p.2) := cont_pcUD.neg
  exact (continuous_if_fst_le hc1 hc2 hz0).congr fun p => (hdeq p).symm

/-- **Quotient continuity of `λ_L` across `a = 0`**: if `ψ_W, φ_1/κ_bal` are continuous in `X`,
`φ_2` is built from `pcMinus pcU pcV a 1` (with continuous coefficients `A, B, ζ, a`), `j₁` is
fixed and the denominator Casoratian is nonvanishing on `I`, then `λ_L` is `ContinuousOn` `I`. -/
theorem lamL_continuousOn_of_coeff {I : Set ℝ} {A ψW φ1 φA φB ζ a : ℝ → ℤ → ℝ} {h : ℝ} (_hh : 0 < h)
    (j1 : ℤ)
    (hAc : ContinuousOn (fun X => A X j1) I)
    (hψW0 : ContinuousOn (fun X => ψW X j1) I) (hψW1 : ContinuousOn (fun X => ψW X (j1 + 1)) I)
    (hφ10 : ContinuousOn (fun X => φ1 X j1) I) (hφ11 : ContinuousOn (fun X => φ1 X (j1 + 1)) I)
    (hφA0 : ContinuousOn (fun X => φA X j1) I) (hφA1 : ContinuousOn (fun X => φA X (j1 + 1)) I)
    (hφB0 : ContinuousOn (fun X => φB X j1) I) (hφB1 : ContinuousOn (fun X => φB X (j1 + 1)) I)
    (hζ0 : ContinuousOn (fun X => ζ X j1) I) (hζ1 : ContinuousOn (fun X => ζ X (j1 + 1)) I)
    (ha : ContinuousOn (fun X => a X 0) I)
    (hden : ∀ X ∈ I,
      cas (A X) (φ1 X) (fun n => φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h))) j1 ≠ 0) :
    ContinuousOn (fun X =>
      cas (A X) (ψW X) (fun n => φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h))) j1 /
      cas (A X) (φ1 X) (fun n => φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h))) j1) I := by
  let ψC : ℝ → ℤ → ℝ := fun X n =>
    φA X n * pcBranch1Cont (a X 0) (ζ X n / Real.sqrt h) +
      h * φB X n * (Real.sqrt h * deriv (pcBranch1Cont (a X 0)) (ζ X n / Real.sqrt h))
  have hscale : ∀ X n,
      φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h)) =
      pcBranch1Scale (a X 0) * ψC X n := by
    intro X n
    have hfun : pcMinus pcU pcV (a X 0) 1 = fun z => pcBranch1Scale (a X 0) * pcBranch1Cont (a X 0) z :=
      funext fun z => pcMinus_one_eq_scale (a X 0) z
    have hdiff : DifferentiableAt ℝ (pcBranch1Cont (a X 0)) (ζ X n / Real.sqrt h) := by
      by_cases h0 : a X 0 ≤ 0
      · have hfn : pcBranch1Cont (a X 0) = fun w => -(Real.sqrt Real.pi * pcV (a X 0) (-w)) :=
          funext fun w => by simp [pcBranch1Cont, h0]
        rw [hfn]
        exact (((hasDerivAt_pcV (a X 0) _).comp _ (hasDerivAt_neg _)).const_mul _).neg.differentiableAt
      · have hfn : pcBranch1Cont (a X 0) = fun w => -pcU (a X 0) w :=
          funext fun w => by simp [pcBranch1Cont, h0]
        rw [hfn]
        exact (hasDerivAt_pcU (a X 0) _).neg.differentiableAt
    rw [pcMinus_one_eq_scale, hfun, deriv_const_mul _ hdiff]
    dsimp [ψC]; ring
  have hcas_eq : ∀ (ψ : ℝ → ℤ → ℝ) (X : ℝ),
      cas (A X) (ψ X) (fun n => φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h))) j1 =
      pcBranch1Scale (a X 0) * cas (A X) (ψ X) (ψC X) j1 := fun ψ X => by
    simp only [cas, hscale]
    ring
  have hq_eq : ∀ X,
      cas (A X) (ψW X) (fun n => φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h))) j1 /
      cas (A X) (φ1 X) (fun n => φA X n * pcMinus pcU pcV (a X 0) 1 (ζ X n / Real.sqrt h) +
        h * φB X n * (Real.sqrt h * deriv (pcMinus pcU pcV (a X 0) 1) (ζ X n / Real.sqrt h))) j1 =
      cas (A X) (ψW X) (ψC X) j1 / cas (A X) (φ1 X) (ψC X) j1 := fun X => by
    rw [hcas_eq ψW X, hcas_eq φ1 X, mul_div_mul_left _ _ (pcBranch1Scale_pos (a X 0)).ne']
  have hcB1_0 : ContinuousOn (fun X => pcBranch1Cont (a X 0) (ζ X j1 / Real.sqrt h)) I :=
    continuous_pcBranch1Cont.comp_continuousOn (ha.prodMk (hζ0.div_const _))
  have hcB1_1 : ContinuousOn (fun X => pcBranch1Cont (a X 0) (ζ X (j1 + 1) / Real.sqrt h)) I :=
    continuous_pcBranch1Cont.comp_continuousOn (ha.prodMk (hζ1.div_const _))
  have hcBd_0 : ContinuousOn (fun X => deriv (pcBranch1Cont (a X 0)) (ζ X j1 / Real.sqrt h)) I :=
    continuous_deriv_pcBranch1Cont.comp_continuousOn (ha.prodMk (hζ0.div_const _))
  have hcBd_1 : ContinuousOn (fun X => deriv (pcBranch1Cont (a X 0)) (ζ X (j1 + 1) / Real.sqrt h)) I :=
    continuous_deriv_pcBranch1Cont.comp_continuousOn (ha.prodMk (hζ1.div_const _))
  have hψC0 : ContinuousOn (fun X => ψC X j1) I :=
    (hφA0.mul hcB1_0).add ((continuousOn_const.mul hφB0).mul (continuousOn_const.mul hcBd_0))
  have hψC1 : ContinuousOn (fun X => ψC X (j1 + 1)) I :=
    (hφA1.mul hcB1_1).add ((continuousOn_const.mul hφB1).mul (continuousOn_const.mul hcBd_1))
  have hnum : ContinuousOn (fun X => cas (A X) (ψW X) (ψC X) j1) I := by
    unfold cas
    exact hAc.mul ((hψW1.mul hψC0).sub (hψW0.mul hψC1))
  have hdenC : ContinuousOn (fun X => cas (A X) (φ1 X) (ψC X) j1) I := by
    unfold cas
    exact hAc.mul ((hφ11.mul hψC0).sub (hφ10.mul hψC1))
  refine ContinuousOn.congr (hnum.div hdenC fun X hX => ?_) (fun X _ => hq_eq X)
  have h0 := hden X hX
  rw [hcas_eq φ1 X] at h0
  exact right_ne_zero_of_mul h0

/-- info: 'FormalResearch.JacobiEigenvectors.Charts.lamL_continuousOn_of_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.Charts.lamL_continuousOn_of_coeff

end FormalResearch.JacobiEigenvectors.Charts

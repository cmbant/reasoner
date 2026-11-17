module

public import FormalResearch.Special.LatticeSaw

/-!
# Integration by parts against the sawtooth antiderivative

For `φ = Ψ τ₀'` the identity
`∫_{-X}^{X} [Ψ' sawH(t₀) + Ψ ({t₀} - ½) t₀'] = [Ψ sawH(t₀)]_{-X}^{X}`
(fundamental theorem of calculus for `Ψ·sawH∘t₀`, differentiable off the finite set `t₀⁻¹(ℤ)`),
so that `∫ φ ({t₀} - ½) = [Ψ sawH(t₀)] - ∫ Ψ' sawH(t₀)`.  This replaces the conditionally convergent
Fourier series of the sawtooth in the paper's proof of `lem:latticesum` (i).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K : ℝ}

lemma continuousOn_deriv_re (h : CalPhase τ0 X y0 m M K) :
    ContinuousOn (fun s : ℝ => (deriv τ0 (s : ℂ)).re) (Icc (-(X + 1)) (X + 1)) := by
  intro z hz
  have hw : InWin X y0 (z : ℂ) := inWin_real (abs_le.mpr hz) h.hy0.le
  have h1 : ContinuousAt (deriv τ0) (z : ℂ) := (h.ddiff _ hw).continuousAt
  have h2 : ContinuousAt (fun s : ℝ => deriv τ0 (s : ℂ)) z :=
    h1.comp (f := fun s : ℝ => (s : ℂ)) Complex.continuous_ofReal.continuousAt
  exact (Complex.continuous_re.continuousAt.comp h2).continuousWithinAt

lemma countable_levels (h : CalPhase τ0 X y0 m M K) :
    {s : ℝ | s ∈ Icc (-X) X ∧ ∃ n : ℤ, realPhase τ0 s = n}.Countable := by
  have hinj : InjOn (realPhase τ0) {s : ℝ | s ∈ Icc (-X) X ∧ ∃ n : ℤ, realPhase τ0 s = n} := by
    intro x hx y hy hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact absurd hxy (h.realPhase_strictMono (abs_le.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩)
        (abs_le.mpr ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩) hlt).ne
    · exact heq
    · exact absurd hxy (h.realPhase_strictMono (abs_le.mpr ⟨by linarith [hy.1.1], by linarith [hy.1.2]⟩)
        (abs_le.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩) hgt).ne'
  refine MapsTo.countable_of_injOn (f := realPhase τ0) (t := range ((↑) : ℤ → ℝ)) ?_ hinj
    (countable_range _)
  intro s hs
  obtain ⟨n, hn⟩ := hs.2
  exact ⟨n, hn.symm⟩

/-- The real derivative `t₀' = Re τ₀'`. -/
noncomputable def realDeriv (τ0 : ℂ → ℂ) (s : ℝ) : ℝ := (deriv τ0 (s : ℂ)).re

/-- **Integration by parts** with `sawH` (the fundamental theorem of calculus off the finite set
`t₀⁻¹(ℤ)`). -/
theorem ibp_identity (h : CalPhase τ0 X y0 m M K) {Ψ : ℂ → ℂ} {CΨ : ℝ}
    (hΨ : ∀ s, InWin X y0 s → DifferentiableAt ℂ Ψ s)
    (hΨ' : ∀ s, InWin X y0 s → DifferentiableAt ℂ (deriv Ψ) s)
    (hb : ∀ s : ℝ, |s| ≤ X → ‖Ψ s‖ ≤ CΨ) :
    ∫ s in (-X)..X, (deriv Ψ (s : ℂ) * ((sawH (realPhase τ0 s) : ℝ) : ℂ) +
      Ψ s * (((Int.fract (realPhase τ0 s) - 1 / 2) * realDeriv τ0 s : ℝ) : ℂ)) =
    Ψ X * ((sawH (realPhase τ0 X) : ℝ) : ℂ) - Ψ (-X : ℝ) * ((sawH (realPhase τ0 (-X)) : ℝ) : ℂ) := by
  have hX := h.hX
  have hwin : ∀ s : ℝ, |s| ≤ X → InWin X y0 (s : ℂ) := fun s hs =>
    inWin_real (hs.trans (by linarith)) h.hy0.le
  have hsub : Icc (-X) X ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc (by linarith) (by linarith)
  have hIcc : ∀ s ∈ Icc (-X) X, |s| ≤ X := fun s hs => abs_le.mpr hs
  -- continuity pieces
  have hΨc : ContinuousOn (fun s : ℝ => Ψ (s : ℂ)) (Icc (-X) X) := fun s hs =>
    (((hΨ _ (hwin s (hIcc s hs))).continuousAt).comp (f := fun s : ℝ => (s : ℂ))
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hΨ'c : ContinuousOn (fun s : ℝ => deriv Ψ (s : ℂ)) (Icc (-X) X) := fun s hs =>
    (((hΨ' _ (hwin s (hIcc s hs))).continuousAt).comp (f := fun s : ℝ => (s : ℂ))
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have ht0c : ContinuousOn (realPhase τ0) (Icc (-X) X) := h.continuousOn_realPhase.mono hsub
  have hHc : ContinuousOn (fun s => sawH (realPhase τ0 s)) (Icc (-X) X) :=
    continuous_sawH.comp_continuousOn ht0c
  have hdc : ContinuousOn (realDeriv τ0) (Icc (-X) X) := h.continuousOn_deriv_re.mono hsub
  -- the function g and its derivative
  set g : ℝ → ℂ := fun s => Ψ s * ((sawH (realPhase τ0 s) : ℝ) : ℂ) with hg
  set g' : ℝ → ℂ := fun s => deriv Ψ (s : ℂ) * ((sawH (realPhase τ0 s) : ℝ) : ℂ) +
      Ψ s * (((Int.fract (realPhase τ0 s) - 1 / 2) * realDeriv τ0 s : ℝ) : ℂ) with hg'
  have hgc : ContinuousOn g (Icc (-X) X) :=
    hΨc.mul (Complex.continuous_ofReal.comp_continuousOn hHc)
  have hderiv : ∀ s ∈ Ioo (-X) X \ {s : ℝ | s ∈ Icc (-X) X ∧ ∃ n : ℤ, realPhase τ0 s = n},
      HasDerivAt g (g' s) s := by
    intro s ⟨hs, hns⟩
    have hsI : s ∈ Icc (-X) X := ⟨hs.1.le, hs.2.le⟩
    have hnoint : ∀ n : ℤ, realPhase τ0 s ≠ n := fun n hn => hns ⟨hsI, n, hn⟩
    have hd1 : HasDerivAt (fun y : ℝ => Ψ (y : ℂ)) (deriv Ψ (s : ℂ)) s :=
      (hΨ _ (hwin s (hIcc s hsI))).hasDerivAt.comp_ofReal
    have hd2 : HasDerivAt (fun y => sawH (realPhase τ0 y)) ((Int.fract (realPhase τ0 s) - 1 / 2) *
        realDeriv τ0 s) s :=
      (hasDerivAt_sawH hnoint).comp s (h.hasDerivAt_real (abs_le.mpr (hsub hsI)))
    have hd3 := hd2.ofReal_comp
    exact hd1.mul hd3
  have hint : IntervalIntegrable g' volume (-X) X := by
    have hA : IntervalIntegrable (fun s : ℝ => deriv Ψ (s : ℂ) * ((sawH (realPhase τ0 s) : ℝ) : ℂ))
        volume (-X) X :=
      (hΨ'c.mul (Complex.continuous_ofReal.comp_continuousOn hHc)).intervalIntegrable_of_Icc
        (by linarith)
    have hBm : AEStronglyMeasurable (fun s : ℝ => Ψ s *
        (((Int.fract (realPhase τ0 s) - 1 / 2) * realDeriv τ0 s : ℝ) : ℂ))
        (volume.restrict (Icc (-X) X)) := by
      refine (hΨc.aestronglyMeasurable measurableSet_Icc).mul ?_
      refine (Complex.measurable_ofReal.comp_aemeasurable ?_).aestronglyMeasurable
      exact ((measurable_fract.comp_aemeasurable (ht0c.aemeasurable measurableSet_Icc)).sub_const
        (1 / 2 : ℝ)).mul (hdc.aemeasurable measurableSet_Icc)
    have hB : IntegrableOn (fun s : ℝ => Ψ s *
        (((Int.fract (realPhase τ0 s) - 1 / 2) * realDeriv τ0 s : ℝ) : ℂ)) (Icc (-X) X) := by
      show Integrable _ (volume.restrict (Icc (-X) X))
      refine Integrable.of_bound hBm (CΨ * (1 / 2 * M)) ?_
      refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
      have hs' := hIcc s hs
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      have h1 : |Int.fract (realPhase τ0 s) - 1 / 2| ≤ 1 / 2 := by
        have := Int.fract_nonneg (realPhase τ0 s); have := Int.fract_lt_one (realPhase τ0 s)
        rw [abs_le]; constructor <;> linarith
      have h2 : |realDeriv τ0 s| ≤ M := by
        have a1 := h.ge (s : ℂ) (hwin s hs')
        have a2 := h.le s (hs'.trans (by linarith))
        unfold realDeriv
        rw [abs_of_nonneg (by linarith [h.hm])]; exact a2
      have h3 := hb s hs'
      have h4 : 0 ≤ CΨ := (norm_nonneg _).trans h3
      have h5 : |Int.fract (realPhase τ0 s) - 1 / 2| * |realDeriv τ0 s| ≤ 1 / 2 * M :=
        mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      exact mul_le_mul h3 h5 (by positivity) h4
    exact hA.add ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mpr hB)
  have := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le g g' (by linarith : -X ≤ X)
    h.countable_levels hgc hderiv hint
  exact this

end CalPhase

end FormalResearch.Special.Lattice

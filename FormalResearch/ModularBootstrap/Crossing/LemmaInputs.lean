module

public import FormalResearch.ModularBootstrap.Crossing.Setup
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit

/-!
# The two analytic estimates of the Virasoro strip argument: `Lemma PJ` and `Lemma G`

Definitions of the uniform estimates over the concrete Virasoro test class
`TestClass virasoroProblem (c' / 12)` that the strip argument of `Crossing.Bridge` uses:

* `LemmaPJInput rs c_PJ C_PJ U`: **unproved analytic hypothesis**, Lemma `PJ` (`vlo:PJ`), the strip
  Poisson--Jensen bound on `x ∈ [0, xiStar)`.  It is the only analytic input of Theorem `A`
  (`Crossing.VirasoroStripInput.hPJ`).
* `LemmaGapInput fg`: Lemma `G` (`vlo:Gap`), the fixed-gap deep-lobe concentration at `x₀ = 0.05`.
  It is a *consequence* of `LemmaPJInput` (`Integration.lemmaGapInput_of_lemmaPJInput`,
  `Crossing.GapFromPJ`), not an input.
* `cardyNorm_pos_of_nonzero`: a nonzero test function has `M[g] > 0`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Crossing

open FormalResearch.ModularBootstrap

/-- **Unproved analytic input (`Lemma PJ`, `lower_o1_two_edge.tex`, `vlo:PJ`):**
Uniform slit-strip Poisson--Jensen estimate on `x ∈ [0, xiStar)` over all nonzero concrete
Virasoro tests `g ∈ TestClass virasoroProblem (c' / 12)` for `c' ≥ c_PJ`.
Not proved in this module. -/
def LemmaPJInput (rs : RealSliceData) (c_PJ C_PJ : ℝ) (U : ℝ → ℝ) : Prop :=
  ∀ {c' : ℝ}, c_PJ ≤ c' → ∀ {g : ℝ → ℝ},
    TestClass virasoroProblem (c' / 12) g →
    0 < virasoroProblem.cardyNorm (c' / 12) g →
    ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
      Real.log |g (c' * x ^ 2 / 3)| ≤
        c' * U x + Real.log (virasoroProblem.cardyNorm (c' / 12) g) - (1 / 2 : ℝ) * Real.log c' +
          (5 / 2 : ℝ) * (1 - rs.slitMassAt x) * Real.log c' + rs.slitEntropyAt x + C_PJ

/-- **Lemma `G`** (`lower_o1_two_edge.tex`, `vlo:Gap` at `x₀ = 0.05`), a consequence of Lemma `PJ`
(`Integration.lemmaGapInput_of_lemmaPJInput`):
uniform fixed-gap exponential concentration of `|g| V` on `[0, c' · 0.05² / 3]` over all
concrete Virasoro tests `g ∈ TestClass virasoroProblem (c' / 12)` for `c' ≥ fg.c_deep`. -/
def LemmaGapInput (fg : FixedGapInput) : Prop :=
  ∀ {c' : ℝ}, fg.c_deep ≤ c' → ∀ {g : ℝ → ℝ},
    TestClass virasoroProblem (c' / 12) g →
    ∫ t in (0 : ℝ)..(c' * (0.05 : ℝ) ^ 2 / 3), |g t| * virasoroProblem.cardyV (c' / 12) t ≤
      fg.C_deep * Real.exp (-fg.κ_deep * c') * virasoroProblem.cardyNorm (c' / 12) g

lemma cardyNorm_pos_of_nonzero {a : ℝ} (ha : virasoroProblem.totalShift ≤ a)
    {g : ℝ → ℝ} (hg : TestClass virasoroProblem a g) (hnonzero : ∃ t ≥ 0, g t ≠ 0) :
    0 < virasoroProblem.cardyNorm a g := by
  unfold FixedWeightProblem.cardyNorm
  have hint : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) := hg.int_cardy
  have hcont : ContinuousOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) :=
    (hg.cont.abs.mul (continuous_cardyV virasoroProblem a).continuousOn).mono Ioi_subset_Ici_self
  have hnn : 0 ≤ ∫ t in Ioi 0, |g t| * virasoroProblem.cardyV a t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha (Set.mem_Ioi.mp ht).le)
  rcases hnn.eq_or_lt with heq | hlt
  · exfalso
    have hzero_ae : (fun t => |g t| * virasoroProblem.cardyV a t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).mp heq.symm
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha (Set.mem_Ioi.mp ht).le)
    have hpos_ae : ∀ t ∈ Ioi (0 : ℝ), |g t| * virasoroProblem.cardyV a t = 0 := by
      intro t ht
      by_contra hne
      have hpos : 0 < |g t| * virasoroProblem.cardyV a t :=
        lt_of_le_of_ne (mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg ha ht.le))
          (Ne.symm hne)
      obtain ⟨r, hr_pos, hr_lt⟩ := Metric.continuousAt_iff.mp
        (hcont.continuousAt (Ioi_mem_nhds ht))
        ((|g t| * virasoroProblem.cardyV a t) / 2) (half_pos hpos)
      have hopen : (Metric.ball t r ∩ Ioi (0 : ℝ)).Nonempty := ⟨t, Metric.mem_ball_self hr_pos, ht⟩
      have hmeas_pos : 0 < (volume.restrict (Ioi (0 : ℝ))) (Metric.ball t r ∩ Ioi (0 : ℝ)) := by
        rw [Measure.restrict_apply (measurableSet_ball.inter measurableSet_Ioi), Set.inter_assoc,
          Set.inter_self]
        exact (Metric.isOpen_ball.inter isOpen_Ioi).measure_pos _ hopen
      have hsub_null : Metric.ball t r ∩ Ioi (0 : ℝ) ⊆
          {s | |g s| * virasoroProblem.cardyV a s ≠ 0} := by
        intro s hs hzero
        have hdist := hr_lt (Metric.mem_ball.mp hs.1)
        rw [hzero, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hpos] at hdist
        linarith
      have hnull : (volume.restrict (Ioi (0 : ℝ))) (Metric.ball t r ∩ Ioi (0 : ℝ)) = 0 :=
        measure_mono_null hsub_null (ae_iff.mp hzero_ae)
      exact hmeas_pos.ne' hnull
    have hg_pos : ∀ t : ℝ, 0 < t → g t = 0 := fun t ht => by
      have hmul := hpos_ae t ht
      rcases mul_eq_zero.mp hmul with h1 | h2
      · exact abs_eq_zero.mp h1
      · exfalso
        exact (virasoroProblem.cardyV_pos ha ht).ne' h2
    have hg_zero_at_0 : g 0 = 0 := by
      have htend : Tendsto g (𝓝[>] 0) (𝓝 (g 0)) :=
        (hg.cont 0 (le_refl 0)).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
      exact tendsto_nhds_unique htend (tendsto_const_nhds.congr' (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        exact (hg_pos t ht).symm))
    obtain ⟨t₀, ht₀, hne⟩ := hnonzero
    rcases eq_or_lt_of_le ht₀ with rfl | ht₀_pos
    · exact hne hg_zero_at_0
    · exact hne (hg_pos t₀ ht₀_pos)
  · exact hlt

end FormalResearch.ModularBootstrap.Crossing

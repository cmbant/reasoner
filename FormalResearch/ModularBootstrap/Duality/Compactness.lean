module

public import FormalResearch.ModularBootstrap.Duality.Coordinates

/-!
# Exact solutions of the crossing equations by weak compactness (Theorem E(b), (c))

For `T₀ ≤ T < T_V` the atomic approximate solutions of `MomentProblem` are pushed to finite measures
on `[0, 1]` (the compactification of `[T₀, ∞]`), and the finite-intersection property of the weakly
compact set `{μ : mass ≤ C₀, ∫ ζ_T dμ = 0}` yields a *limit measure* satisfying all the equations
`∫ Ξ_β/w_* dμ = ∫ Ξ_β ρ_C dt` exactly.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real NNReal BoundedContinuousFunction

namespace FormalResearch.ModularBootstrap.Duality

open FormalResearch.ModularBootstrap.Crossing

/-- The finite atomic measure `Σ_k c_k δ_{s(t_k)}` on `[0, 1]`. -/
noncomputable def atomMeasure (T₀ : ℝ) {N : ℕ} (t c : Fin N → ℝ) : Measure Ecoord :=
  ∑ k, (c k).toNNReal • Measure.dirac (toE T₀ (t k))

instance atomMeasure_finite (T₀ : ℝ) {N : ℕ} (t c : Fin N → ℝ) :
    IsFiniteMeasure (atomMeasure T₀ t c) := by
  unfold atomMeasure
  infer_instance

lemma integral_atomMeasure (T₀ : ℝ) {N : ℕ} (t c : Fin N → ℝ) (hc : ∀ k, 0 ≤ c k)
    (g : Ecoord →ᵇ ℝ) :
    ∫ x, g x ∂(atomMeasure T₀ t c) = ∑ k, c k * g (toE T₀ (t k)) := by
  unfold atomMeasure
  rw [integral_finsetSum_measure (fun k _ => g.integrable _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_smul_nnreal_measure, integral_dirac, NNReal.smul_def, smul_eq_mul,
    Real.coe_toNNReal _ (hc k)]

lemma atomMeasure_real_univ (T₀ : ℝ) {N : ℕ} (t c : Fin N → ℝ) (hc : ∀ k, 0 ≤ c k) :
    (atomMeasure T₀ t c).real univ = ∑ k, c k := by
  have := integral_atomMeasure T₀ t c hc (BoundedContinuousFunction.const _ 1)
  simpa using this

/-- Real-valued mass of a finite measure. -/
lemma finiteMeasure_mass_coe (μ : FiniteMeasure Ecoord) :
    (μ.mass : ℝ) = (μ : Measure Ecoord).real univ := by
  rw [Measure.real, ← FiniteMeasure.ennreal_mass, ENNReal.coe_toReal]

/-- The weakly compact set of measures of mass `≤ C` vanishing on `{ζ > 0}`. -/
def Kset (C : ℝ≥0) (ζ : Ecoord →ᵇ ℝ) : Set (FiniteMeasure Ecoord) :=
  {μ | μ.mass ≤ C ∧ ∫ x, ζ x ∂(μ : Measure Ecoord) = 0}

lemma isClosed_Kset (C : ℝ≥0) (ζ : Ecoord →ᵇ ℝ) : IsClosed (Kset C ζ) := by
  refine IsClosed.inter ?_ ?_
  · exact isClosed_Iic.preimage FiniteMeasure.continuous_mass
  · exact isClosed_eq (continuous_integral_finiteMeasure ζ) continuous_const

lemma isCompact_Kset (C : ℝ≥0) (ζ : Ecoord →ᵇ ℝ) : IsCompact (Kset C ζ) :=
  (isCompact_setOfPred_finiteMeasure_le_of_compactSpace Ecoord C).of_isClosed_subset
    (isClosed_Kset C ζ) (fun _ hμ => hμ.1)

/-- **Theorem E(a)+(b), exactness on `[0,1]`.** For `T₀ ≤ T < T_V` there is a finite measure `μ`
on `[0, 1]` with mass `≤ C₀`, `∫ ζ_T dμ = 0` (support in `[T, ∞]`), and
`∫ Ξ_β/w_* dμ = ∫ Ξ_β ρ_C dt` for every `β > 0`. -/
theorem exists_measure_exact {cTilde β₀ T₀ T : ℝ} (S : DualSetup cTilde β₀ T₀) (hT₀T : T₀ ≤ T)
    (hTV : T < virasoroProblem.T_V cTilde) :
    ∃ μ : FiniteMeasure Ecoord, (μ.mass : ℝ) ≤ dualC0 (cTilde / 12) β₀ ∧
      ∫ x, zetaB T₀ T x ∂(μ : Measure Ecoord) = 0 ∧
      ∀ (β : ℝ) (hβ : 0 < β),
        ∫ x, FtildeB (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀) (by linarith [S.ha]) S.hβ₀ S.hT₀pos hβ x
          ∂(μ : Measure Ecoord) = crossingRHS (cTilde / 12) β := by
  have ha0 : 0 < cTilde / 12 := by linarith [S.ha]
  have hC0 : 0 < dualC0 (cTilde / 12) β₀ := dualC0_pos S.ha S.hβ₀ S.hβ₀2
  set C : ℝ≥0 := (dualC0 (cTilde / 12) β₀).toNNReal with hC
  have hCcoe : (C : ℝ) = dualC0 (cTilde / 12) β₀ := Real.coe_toNNReal _ hC0.le
  obtain ⟨μ, hμK, hμ⟩ := exists_exact_of_approx (isCompact_Kset C (zetaB T₀ T))
    (isClosed_Kset C (zetaB T₀ T))
    (J := {β : ℝ // 0 < β})
    (fun j => FtildeB (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀) ha0 S.hβ₀ S.hT₀pos j.2)
    (fun j => crossingRHS (cTilde / 12) j.1) (fun u n => by
      obtain ⟨N, t, c, ht, hc, hs, hd⟩ := exists_atomic_approx S hT₀T hTV
        (u.image Subtype.val) (fun β hβ => by
          obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hβ; exact j.2)
        (by positivity : (0 : ℝ) < 1 / (n + 1))
      let μ : FiniteMeasure Ecoord := ⟨atomMeasure T₀ t c, inferInstance⟩
      have hint := integral_atomMeasure T₀ t c hc
      refine ⟨μ, ⟨?_, ?_⟩, fun j hj => ?_⟩
      · show (μ.mass : ℝ) ≤ C
        rw [finiteMeasure_mass_coe, hCcoe]
        show (atomMeasure T₀ t c).real univ ≤ _
        rw [atomMeasure_real_univ T₀ t c hc]; exact hs
      · show ∫ x, zetaB T₀ T x ∂(atomMeasure T₀ t c) = 0
        rw [hint]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [zetaB_toE hT₀T (ht k), mul_zero]
      · show |∫ x, _ ∂(atomMeasure T₀ t c) - _| ≤ _
        rw [hint]
        have := hd j.1 (Finset.mem_image.2 ⟨j, hj, rfl⟩)
        refine le_of_lt ?_
        convert this using 3
        refine Finset.sum_congr rfl fun k _ => ?_
        have e : (FtildeB (a := cTilde / 12) (β₀ := β₀) (T₀ := T₀) ha0 S.hβ₀ S.hT₀pos j.2)
            (toE T₀ (t k)) = Ftilde (cTilde / 12) β₀ T₀ j.1 (toE T₀ (t k)) := rfl
        rw [e, Ftilde_toE _ _ _ _ (hT₀T.trans (ht k))])
  refine ⟨μ, ?_, hμK.2, fun β hβ => hμ ⟨β, hβ⟩⟩
  have := hμK.1
  rw [← hCcoe]; exact_mod_cast this

/-- info: 'FormalResearch.ModularBootstrap.Duality.exists_measure_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Duality.exists_measure_exact

end FormalResearch.ModularBootstrap.Duality

module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Complex-smooth dependence of a segment integral on a complex parameter

Support for the CFU chart of `ct:cfu` (`constant_terms_lower.tex`, Step 2/3).  **Proved.**
`contDiffAt_segInt`: if `F(u, w)` is `C^∞` over `ℂ` in `(u, w) ∈ E × ℂ` near `{u₀} × [0,1]`, then `u ↦ ∫₀¹ F(u, t) dt` is `C^∞` over `ℂ`
at `u₀`.  (Mathlib's `ContDiffOn.parametric_integral` needs the integration variable in a `ℂ`-space; we push Lebesgue measure forward to `ℂ`.)
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Interval

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem contDiffAt_segInt_nat {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → ℂ → ℂ} {u0 : E}
    (n : ℕ) (hF : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℂ ((n : ℕ∞) : WithTop ℕ∞) (fun p : E × ℂ => F p.1 p.2) (u0, (t : ℂ))) :
    ContDiffAt ℂ ((n : ℕ∞) : WithTop ℕ∞) (fun u => ∫ t in (0 : ℝ)..1, F u (t : ℂ)) u0 := by
  set K : Set ℂ := Complex.ofReal '' Icc (0 : ℝ) 1 with hK
  have hKc : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  set O : Set (E × ℂ) := {p | ContDiffAt ℂ ((n : ℕ∞) : WithTop ℕ∞) (fun p : E × ℂ => F p.1 p.2) p} with hO
  have hOo : IsOpen O := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    exact (hp.eventually (by simp)).mono fun q hq => hq
  have hsub : ({u0} : Set E) ×ˢ K ⊆ O := by
    rintro ⟨u, w⟩ ⟨hu, hw⟩
    obtain ⟨t, ht, rfl⟩ := hw
    rw [mem_singleton_iff] at hu
    subst hu
    exact hF t ht
  obtain ⟨U, V, hUo, hVo, hu0, hKV, hUV⟩ := generalized_tube_lemma isCompact_singleton hKc hOo hsub
  have hu0' : u0 ∈ U := hu0 rfl
  set μ : Measure ℂ := Measure.map Complex.ofReal (volume : Measure ℝ) with hμ
  have hemb : MeasurableEmbedding Complex.ofReal := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hμK : μ K ≠ ⊤ := by
    rw [hμ, hemb.map_apply, hK, Set.preimage_image_eq _ Complex.ofReal_injective, Real.volume_Icc]
    simp
  have hcd : ContDiffOn ℂ (n : ℕ∞) (fun p : E × ℂ => F p.1 p.2) (U ×ˢ K) := by
    intro p hp
    exact (hUV (⟨hp.1, hKV hp.2⟩ : p ∈ U ×ˢ V)).contDiffWithinAt
  have hint := ContDiffOn.parametric_integral (𝕜 := ℂ) (μ := μ) (f := F) hUo hKc (s₀ := K) (n := (n : ℕ∞))
    subset_rfl hcd hμK
  have hat : ContDiffAt ℂ ((n : ℕ∞) : WithTop ℕ∞) (fun x => ∫ a in K, F x a ∂μ) u0 :=
    hint.contDiffAt (hUo.mem_nhds hu0')
  have heq : (fun x => ∫ a in K, F x a ∂μ) = fun u => ∫ t in (0 : ℝ)..1, F u (t : ℂ) := by
    funext x
    rw [hμ, hemb.setIntegral_map, hK, Set.preimage_image_eq _ Complex.ofReal_injective,
      intervalIntegral.integral_of_le zero_le_one, integral_Icc_eq_integral_Ioc]
  rw [heq] at hat
  exact hat

theorem contDiffAt_segInt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : E → ℂ → ℂ} {u0 : E}
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℂ ∞' (fun p : E × ℂ => F p.1 p.2) (u0, (t : ℂ))) :
    ContDiffAt ℂ ∞' (fun u => ∫ t in (0 : ℝ)..1, F u (t : ℂ)) u0 := by
  rw [contDiffAt_infty]
  intro n
  exact contDiffAt_segInt_nat n fun t ht => (contDiffAt_infty.mp (hF t ht)) n

end FormalResearch.SignUncertainty.CtChart

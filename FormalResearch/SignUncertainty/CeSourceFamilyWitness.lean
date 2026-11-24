module

public import FormalResearch.SignUncertainty.CeLiftSign

/-!
# Non-vacuity of `CeSourceFamily` (M6)

`ceSourceFamily_nonvacuous`: the source family `S_c = ε g₁` (`ε = c^{-1/3}`, `g₁ = ceG1 a₁`, mass exactly `ε`) satisfies every field of
`CeSourceFamily`, given `O6Bricks 4` (needed for the field `dual`, through `O6Est`).  So the input of `ceLift_physical` is satisfiable.  This
witness is not the convolution source `S_c` of `ceo:conv` (the instance for `convSource` is the open item (a) of the M6 plan).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma airySeedU2_zero_zero (b : ℝ) : airySeedU2 0 b 0 = fun u => b * ceG1 (airyZero 1) u := by
  funext u; simp [airySeedU2]

/-- **Non-vacuity of `CeSourceFamily`**: `S_c = ε g₁` satisfies it, given `O6Bricks 4`. -/
theorem ceSourceFamily_nonvacuous (h : O6Bricks 4) :
    CeSourceFamily (fun c u => airySeedU2 0 (liftEps c) 0 u) := by
  obtain ⟨g0, hg0, hE⟩ := h
  have E := hE 1 zero_le_one
  refine ⟨fun {c} _ => hasU2_airySeedU2 0 _ 0, ⟨1, 1, one_pos, one_pos, fun {c} hc => ?_⟩,
    fun {K c} hK hc hcK => convTailData_of_oneLevel (by norm_num) 0 (liftEps c) 0 hK hc hcK, fun K hK => ?_, ?_⟩
  · have hint : ∫ u : ℝ, airySeedU2 0 (liftEps c) 0 u = liftEps c := by
      rw [airySeedU2_zero_zero, integral_const_mul, ceG1_integral_eq_one, mul_one]
    show 1 * liftEps c ≤ ∫ u : ℝ, airySeedU2 0 (liftEps c) 0 u ∧ ∫ u : ℝ, airySeedU2 0 (liftEps c) 0 u ≤ 1 * liftEps c
    rw [hint]; exact ⟨by rw [one_mul], by rw [one_mul]⟩
  · obtain ⟨Ce, hCe, he⟩ := liftSymbol_edge_bound (m := 4) (by norm_num) 1 zero_le_one
    refine ⟨Ce, hCe.le, fun {c} hc hc8 => ?_⟩
    have hc0 : 0 < c := by linarith
    have hb : |liftEps c| ≤ 1 := by
      rw [abs_of_pos (liftEps_pos hc0)]; exact liftEps_le_one (by linarith)
    have h1 := he (a := 0) (b := liftEps c) (c₀ := 0) (by simp) hb (by simp) (K := K) (c := c) hK (by linarith)
    have hK4 : K ^ (-((4 : ℕ) : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hK (by norm_num)
    refine h1.trans ?_
    have hp : 0 ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
    calc Ce * K ^ (-((4 : ℕ) : ℝ)) * c ^ (-(5 / 6 : ℝ)) ≤ Ce * 1 * c ^ (-(5 / 6 : ℝ)) := by gcongr
      _ = Ce * c ^ (-(5 / 6 : ℝ)) := by ring
  · have e : (fun (_ : ℝ) (c u : ℝ) => -airySeedU2 0 (liftEps c) 0 u) =
        fun _ c => airySeedU2 ((fun _ => (0 : ℝ)) c) ((fun c => -liftEps c) c) ((fun _ => (0 : ℝ)) c) := by
      funext K c u; simp [airySeedU2]
    show O6DualEst 4 (fun (_ : ℝ) (c u : ℝ) => -airySeedU2 0 (liftEps c) 0 u)
    rw [e]
    refine o6DualEst_of_oneLevel_family E (a := fun _ => 0) (b := fun c => -liftEps c) (c₀ := fun _ => 0)
      (fun _ _ => by simp) (fun c hc => ?_) (fun _ _ => by simp)
    have hc0 : 0 < c := by linarith
    simp only [abs_neg]
    rw [abs_of_pos (liftEps_pos hc0)]; exact liftEps_le_one (by linarith)

/-- info: 'FormalResearch.SignUncertainty.ceSourceFamily_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceSourceFamily_nonvacuous

end FormalResearch.SignUncertainty

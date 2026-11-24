module

public import FormalResearch.ModularBootstrap.FixedWeightBand.BootstrapClarkMain
public import FormalResearch.ModularBootstrap.TwoLevel.A2StarCurve

/-!
# Theorem `W1'(2)`: the Two-Level Lower `O(1)` Bound at Every Fixed-Weight Problem

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Theorem `W1'` part (2) (`wone:genlower`), the case
`(P, Q) = (cos α, -sin α)`, `m₀ = 2`, of Theorem `FT-L.FW` (`wone:ftlfw`) with the prescribed level
`t₁ = ξ̄ c' + A₁ c'^{1/3} + r`, `|r| ≤ R_off`, and `virasoro_two_level.tex`, Theorem 2.1 (`gt:2.1`) for `A_2^*`.

* `theorem_W1prime_two`: for every fixed-weight problem `prob` (`(H_w)`, hence Virasoro, `N = 1`, `W_N`, ...),
  `R_off ≥ 0` and compact `J ⊂ (-∞, A_opt)` there are `c₂, D₂` such that for every `A₁ ∈ J`, `c' ≥ c₂`, and
  every weakly feasible `g` at `(c'/12, T₂)` (`g ≥ 0` on `[T₂, ∞)`) with `g(t₁) ≥ 0` at some
  `|t₁ - (ξ̄ c' + A₁ c'^{1/3})| ≤ R_off` (`t₁` depends on `g`): `T₂ ≥ ξ̄ c' + A_2^*(A₁) c'^{1/3} - D₂`;
* `theorem_W1prime_two_fixed`: the fixed-`A₁` form.

Proof: Theorem FT-2E with fixed Hermite--Biehler data (`ft_twoEdge_lower_hb_explicit`) over the instance
`twoEdgeInstance_of_YVForClark` for `K = {-A/c_* : A ∈ J}`; the constants are uniform because the instance
parameters `P`, `W_top`, `C₁` are common to `K` and the remainder of FT-2E depends on `u_* = z₂(α(u₁))` only through
`|u_*| ≤ |a₂|`.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.TwoEdgeBootstrap Crossing FormalResearch.ModularBootstrap.FoldTip
  FormalResearch.ModularBootstrap.FixedWeightBand FormalResearch.SignUncertainty

/-- **Theorem `W1'(2)`** (`wone:genlower`(2)), uniform for `A₁` in a compact subset of `(-∞, A_opt)`: the two-level
lower bound `T₂ ≥ ξ̄ c' + A_2^*(A₁) c'^{1/3} - D₂` for every weakly feasible `g` at `(c'/12, T₂)` that is nonnegative
at some `t₁` with `|t₁ - (ξ̄ c' + A₁ c'^{1/3})| ≤ R_off`. -/
theorem theorem_W1prime_two (prob : FixedWeightProblem) {R_off : ℝ} (hR_off : 0 ≤ R_off)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Iio Aopt) :
    ∃ c₂ D₂ : ℝ, ∀ A₁ ∈ J, ∀ c' : ℝ, c₂ ≤ c' → ∀ (T₂ : ℝ) (g : ℝ → ℝ) (t₁ : ℝ),
      |t₁ - (xiBar * c' + A₁ * c' ^ (1 / 3 : ℝ))| ≤ R_off → 0 ≤ g t₁ →
      prob.IsWeaklyFeasible (c' / 12) T₂ g →
      xiBar * c' + A2star A₁ * c' ^ (1 / 3 : ℝ) - D₂ ≤ T₂ := by
  obtain ⟨Q⟩ := LemmaQData.nonempty prob
  have hcS := cStar_pos
  have hYV := Q.yvInputUniformSecond_of_scaleCompat Q.bvChoice_pos Q.bvChoice_le Q.bvChoice_scaleCompat
  set K : Set ℝ := (fun A : ℝ => -A / cStar) '' J with hK_def
  have hKc : IsCompact K := hJ.image (by fun_prop)
  have hKsub : K ⊆ Ioi (airyZero 1) := by
    rintro _ ⟨A, hA, rfl⟩
    exact mem_gap_one_of_lt_Aopt (hJsub hA)
  obtain ⟨P, Ws, C₁, hWs, hC1_Q, hC1, hU, hinst⟩ :=
    twoEdgeInstance_of_YVForClark Q Q.bvChoice_pos Q.bvChoice_le hYV hKc hKsub hR_off
  set m : ℝ := min P.δ_star (min P.η_0 1) with hm_def
  set D₂ : ℝ := tebK0HB P Ws / (foldChartOfLemmaQ Q).β +
    (foldChartOfLemmaQ Q).Cξ * (|airyZero 2| + m) ^ 2 with hD₂_def
  refine ⟨C₁, D₂, fun A₁ hA₁ c' hc' T₂ g t₁ ht₁ hgt₁ hg => ?_⟩
  have hu₁K : -A₁ / cStar ∈ K := ⟨A₁, hA₁, rfl⟩
  have hA₁_lt : A₁ < Aopt := hJsub hA₁
  have hu₁ : airyZero 1 < -A₁ / cStar := mem_gap_one_of_lt_Aopt hA₁_lt
  obtain ⟨hcov, hviol⟩ := hinst _ hu₁K
  obtain ⟨hz2_lo, hz2_hi⟩ := airyZero_two_lt_clarkNode_two hu₁
  have hz2_neg : clarkNode (clarkAngle (-A₁ / cStar)) 2 < 0 := by
    linarith [airyZero_one.2]
  have hA_eq : -cStar * (-A₁ / cStar) = A₁ := by field_simp
  have hfeas : TwoLevelFeasible prob (-cStar * (-A₁ / cStar)) R_off c' T₂ := by
    rw [hA_eq]; exact ⟨g, t₁, ht₁, hgt₁, hg⟩
  have h := ft_twoEdge_lower_hb_explicit (foldChartOfLemmaQ Q) P hz2_neg hC1
    (fun C hC => hU C hC _ hu₁K) hcov hviol c' hc' T₂ hfeas
  have hβ : (foldChartOfLemmaQ Q).β = 1 / cStar := rfl
  have hslope : (|clarkNode (clarkAngle (-A₁ / cStar)) 2| / (foldChartOfLemmaQ Q).β) =
      A2star A₁ := by
    rw [hβ]; unfold A2star; field_simp
  have hKm : twoEdgeKminus (foldChartOfLemmaQ Q) (clarkNode (clarkAngle (-A₁ / cStar)) 2)
      (tebK0HB P Ws) m ≤ D₂ := by
    unfold twoEdgeKminus
    have habs : |clarkNode (clarkAngle (-A₁ / cStar)) 2| ≤ |airyZero 2| := by
      rw [abs_of_neg hz2_neg, abs_of_neg (by linarith [airyZero_two.2] : airyZero 2 < 0)]
      linarith
    have hm_nn : 0 ≤ m := le_min P.hδ_star.le (le_min P.hη0.le zero_le_one)
    have hCξ := (foldChartOfLemmaQ Q).hCξ
    have : (|clarkNode (clarkAngle (-A₁ / cStar)) 2| + m) ^ 2 ≤ (|airyZero 2| + m) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    rw [hD₂_def]
    gcongr
  have hξ : (foldChartOfLemmaQ Q).ξs = xiBar := rfl
  rw [hξ, hslope] at h
  linarith

/-- The fixed-`A₁` form of `theorem_W1prime_two` (`wone:genlower`(2) as stated: constants depending on `A₁` and
`R_off`). -/
theorem theorem_W1prime_two_fixed (prob : FixedWeightProblem) {A₁ R_off : ℝ} (hA₁ : A₁ < Aopt)
    (hR_off : 0 ≤ R_off) :
    ∃ c₂ D₂ : ℝ, ∀ c' : ℝ, c₂ ≤ c' → ∀ (T₂ : ℝ) (g : ℝ → ℝ) (t₁ : ℝ),
      |t₁ - (xiBar * c' + A₁ * c' ^ (1 / 3 : ℝ))| ≤ R_off → 0 ≤ g t₁ →
      prob.IsWeaklyFeasible (c' / 12) T₂ g →
      xiBar * c' + A2star A₁ * c' ^ (1 / 3 : ℝ) - D₂ ≤ T₂ := by
  obtain ⟨c₂, D₂, h⟩ := theorem_W1prime_two prob hR_off (J := {A₁}) isCompact_singleton
    (by simpa using hA₁)
  exact ⟨c₂, D₂, fun c' hc' => h A₁ rfl c' hc'⟩

end FormalResearch.ModularBootstrap.TwoLevel

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_W1prime_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.theorem_W1prime_two

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.theorem_W1prime_two_fixed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.theorem_W1prime_two_fixed

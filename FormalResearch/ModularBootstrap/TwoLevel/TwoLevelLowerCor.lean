module

public import FormalResearch.ModularBootstrap.TwoLevel.TwoLevelLower
public import FormalResearch.ModularBootstrap.TwoLevel.TheoremTwoOne
public import FormalResearch.ModularBootstrap.FixedWeightBand.N1Lower

/-!
# Corollaries of Theorem `W1'(2)`: the `-O(1)` Remainder of Theorem 2.1 and `n1:T5(2)`

Source: `CFT/modular_bootstrap/paper/virasoro_two_level.tex`, Theorem 2.1 (`gt:2.1`) with the remainder
`-O_{A₁,R_off}(1)` from `wone:genlower`(2); `CFT/modular_bootstrap/paper/n1_super_virasoro.tex`, Theorem 5(2) (`n1:T5`(2)).

* `concrete_two_level_lower_O1`: for every fixed-weight problem, the least threshold `τ(g)` of a weakly feasible test `g`
  that is nonnegative at some `t₁` with `|t₁ - (ξ̄ c' + A₁ c'^{1/3})| ≤ R_off` satisfies
  `(τ(g) - ξ̄ c')/c'^{1/3} ≥ A_2^*(A₁) - D₂ c'^{-1/3}`, uniformly for `A₁` in a compact subset of `(-∞, A_opt)`;
* `concrete_two_level_theorem_O1`: the sequence form, the `-O(1)` strengthening of `concrete_two_level_theorem`: along a
  filter with `c'_n → ∞` and `|t_*(n) - (ξ̄ c'_n + A₁ c'_n^{1/3})| ≤ R_off`, eventually
  `A_2^*(A₁) - D c_n'^{-1/3} ≤ (τ(g_n) - ξ̄ c'_n)/c_n'^{1/3}`;
* `n1_two_level_lower`: `n1:T5`(2), lower half, at `n1SuperVirasoroProblem` (`c̃ = c - 3/2`):
  `T₂ ≥ ξ̄ c̃ + A_2^*(A₁) c̃^{1/3} - C_-`.
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special Crossing FormalResearch.ModularBootstrap.TipFront

/-- **Theorem 2.1 with the `-O(1)` remainder, single test** (`gt:2.1` with `wone:genlower`(2)): uniform for `A₁` in a
compact subset of `(-∞, A_opt)`, the least threshold of a weakly feasible test that is nonnegative at some
`t₁` with `|t₁ - (ξ̄ c' + A₁ c'^{1/3})| ≤ R_off` satisfies
`A_2^*(A₁) - D₂ c'^{-1/3} ≤ (τ(g) - ξ̄ c')/c'^{1/3}`. -/
theorem concrete_two_level_lower_O1 (prob : FixedWeightProblem) {R_off : ℝ} (hR_off : 0 ≤ R_off)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Iio Aopt) :
    ∃ c₂ D₂ : ℝ, ∀ A₁ ∈ J, ∀ c' : ℝ, c₂ ≤ c' → ∀ (g : ℝ → ℝ) (t₁ : ℝ),
      |t₁ - (xiBar * c' + A₁ * c' ^ (1 / 3 : ℝ))| ≤ R_off → 0 ≤ g t₁ →
      (∃ T : ℝ, prob.IsWeaklyFeasible (c' / 12) T g) →
      A2star A₁ - D₂ * c' ^ (-(1 / 3 : ℝ)) ≤ (leastThreshold g - xiBar * c') / c' ^ (1 / 3 : ℝ) := by
  obtain ⟨c₂, D₂, h⟩ := theorem_W1prime_two prob hR_off hJ hJsub
  refine ⟨max c₂ 1, D₂, fun A₁ hA₁ c' hc' g t₁ ht₁ hgt₁ ⟨T, hwf⟩ => ?_⟩
  have hc'1 : 1 ≤ c' := (le_max_right _ _).trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hp : 0 < c' ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'_pos _
  have hτ : prob.IsWeaklyFeasible (c' / 12) (leastThreshold g) g :=
    ⟨hwf.1, hwf.2.1, hwf.2.2.1, leastThreshold_tail hwf.1.cont hwf.2.2.2⟩
  have h1 := h A₁ hA₁ c' ((le_max_left _ _).trans hc') (leastThreshold g) g t₁ ht₁ hgt₁ hτ
  have hmul : c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc'_pos, neg_add_cancel, Real.rpow_zero]
  rw [le_div_iff₀ hp]
  have : (A2star A₁ - D₂ * c' ^ (-(1 / 3 : ℝ))) * c' ^ (1 / 3 : ℝ) =
      A2star A₁ * c' ^ (1 / 3 : ℝ) - D₂ := by
    calc (A2star A₁ - D₂ * c' ^ (-(1 / 3 : ℝ))) * c' ^ (1 / 3 : ℝ)
        = A2star A₁ * c' ^ (1 / 3 : ℝ) - D₂ * (c' ^ (-(1 / 3 : ℝ)) * c' ^ (1 / 3 : ℝ)) := by ring
      _ = _ := by rw [hmul, mul_one]
  rw [this]
  linarith

/-- **Theorem 2.1 with the `-O(1)` remainder** (`virasoro_two_level.tex`, `gt:2.1`, strengthening
`concrete_two_level_theorem`): along `c'_n → ∞` with a pinned first level `g_n(t_*(n)) ≥ 0`,
`|t_*(n) - (ξ̄ c'_n + A₁ c_n'^{1/3})| ≤ R_off`, there is `D` with eventually
`A_2^*(A₁) - D c_n'^{-1/3} ≤ (τ(g_n) - ξ̄ c'_n)/c_n'^{1/3}`; in particular
`A_2^*(A₁) ≤ liminf (τ(g_n) - ξ̄ c'_n)/c_n'^{1/3}`. -/
theorem concrete_two_level_theorem_O1 (prob : FixedWeightProblem)
    {ι : Type*} {p : Filter ι} {c' : ι → ℝ} (hc' : Tendsto c' p atTop) (g : ι → ℝ → ℝ)
    (hg : ∀ᶠ n in p, ∃ T : ℝ, prob.IsWeaklyFeasible (c' n / 12) T (g n))
    {A₁ R_off : ℝ} (hA₁ : A₁ < Aopt) (hR_off : 0 ≤ R_off) (tstar : ι → ℝ)
    (hts : ∀ᶠ n in p, |tstar n - (xiBar * c' n + A₁ * (c' n) ^ (1 / 3 : ℝ))| ≤ R_off)
    (hpin : ∀ᶠ n in p, 0 ≤ g n (tstar n)) :
    ∃ D : ℝ, ∀ᶠ n in p,
      A2star A₁ - D * (c' n) ^ (-(1 / 3 : ℝ)) ≤
        (leastThreshold (g n) - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) := by
  obtain ⟨c₂, D, h⟩ := concrete_two_level_lower_O1 prob hR_off (J := {A₁}) isCompact_singleton
    (by simpa using hA₁)
  refine ⟨D, ?_⟩
  filter_upwards [hc'.eventually (eventually_ge_atTop c₂), hg, hts, hpin] with n hn hgn htn hpn
  exact h A₁ rfl (c' n) hn (g n) (tstar n) htn hpn hgn

/-- **`n1:T5`(2), lower half** (`n1_super_virasoro.tex`): for the `𝒩 = 1` NS problem
(`w = 1`, `Q = (1 - q^{1/2})²`, `c̃ = c - 3/2`), every `A₁ < A_opt` and `R_off ≥ 0`: there are `c₂, C_-` such that
every weakly feasible `g` at `(c̃/12, T₂)` that is nonnegative at some `t₁` with
`|t₁ - (ξ̄ c̃ + A₁ c̃^{1/3})| ≤ R_off` has `T₂ ≥ ξ̄ c̃ + A_2^*(A₁) c̃^{1/3} - C_-`, for `c̃ ≥ c₂`. -/
theorem n1_two_level_lower {A₁ R_off : ℝ} (hA₁ : A₁ < Aopt) (hR_off : 0 ≤ R_off) :
    ∃ c₂ C_minus : ℝ, ∀ cTilde : ℝ, c₂ ≤ cTilde → ∀ (T₂ : ℝ) (g : ℝ → ℝ) (t₁ : ℝ),
      |t₁ - (xiBar * cTilde + A₁ * cTilde ^ (1 / 3 : ℝ))| ≤ R_off → 0 ≤ g t₁ →
      n1SuperVirasoroProblem.IsWeaklyFeasible (cTilde / 12) T₂ g →
      xiBar * cTilde + A2star A₁ * cTilde ^ (1 / 3 : ℝ) - C_minus ≤ T₂ :=
  theorem_W1prime_two_fixed n1SuperVirasoroProblem hA₁ hR_off

end FormalResearch.ModularBootstrap.TwoLevel

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_lower_O1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_lower_O1

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_theorem_O1' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.concrete_two_level_theorem_O1

/--
info: 'FormalResearch.ModularBootstrap.TwoLevel.n1_two_level_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.TwoLevel.n1_two_level_lower

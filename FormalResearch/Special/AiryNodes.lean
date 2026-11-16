module

public import FormalResearch.Special.AiryBridge
public import FormalResearch.Special.AiryPositive
public import FormalResearch.Special.AiryPruferLift
public import FormalResearch.Special.SturmAiryNodes

/-!
# The Prüfer angle of `Ai` and the nodes of `cos α·Ai − sin α·Ai'` (Clark nodes)

Specialises the generic Prüfer layer (`SturmAiryNodes`, `AiryPruferLift`) to `y = Ai`, `y' = Ai'`
via `isSol_airyAi`.

* `airy_exists_prufer`: there is a `C¹` Prüfer lift `θ` of `(Ai, Ai')`, `Ai = r sin θ`, `Ai' = r cos θ`,
  `r > 0`, normalised so that `θ 0 = arg (Ai'(0) + i Ai(0)) ∈ (π/2, π)` (`Ai(0) > 0`, `Ai'(0) < 0`), and
  `θ` is strictly increasing on `(-∞, 0]`.
* `airy_zero_iff_level`: `Ai x = 0 ↔ ∃ k : ℤ, θ x = k π`; with `θ 0 ∈ (0, π)` the zeros of `Ai` in
  `(-∞, 0]` are the points `a_{k+1}` at the levels `θ = -kπ`, `k ≥ 0` (the largest zero `a₁` at `θ = 0`),
  and `airy_zeros_ncard`: `#{zeros in (a, 0]} = -⌊θ(a)/π⌋` for `a ≤ 0`.
* `airy_node_exists_unique`: for every `α` and `m ≤ ⌊(θ 0 - α)/π⌋` the function `cos α·Ai − sin α·Ai'`
  has exactly one zero `x ≤ 0` at the level `θ = α + mπ` (the Clark nodes of `Ai` for the boundary
  parameter `α`).

Not formalised: the node counts for `x > 0` (there `θ ∈ (π/2, π)` stays bounded, so for `α ∈ (θ(0), π)`
the level `α + 0·π` is also reached on `x > 0`, which is outside the half-line statements), asymptotics
of `θ(-v)` (`~ (2/3) v^{3/2}`), and the values `a_k`.
-/

@[expose] public section

namespace FormalResearch.Special

open Set SturmAiry

/-- The Prüfer lift of `(Ai, Ai')`, normalised at `0`, with `θ 0 ∈ (π/2, π)` and increasing on
`(-∞, 0]`. -/
theorem airy_exists_prufer :
    ∃ θ : ℝ → ℝ, IsPruferLift (fun x => x) airyAi airyAi' θ ∧ Real.pi / 2 < θ 0 ∧ θ 0 < Real.pi ∧
      StrictMonoOn θ (Iic 0) := by
  obtain ⟨θ, hθ, h0⟩ := isSol_airyAi.exists_isPruferLift continuous_id
    ⟨0, (airyAi_pos le_rfl).ne'⟩ 0
  have hre : ((airyAi' 0 : ℂ) + (airyAi 0 : ℂ) * Complex.I).re < 0 := by
    simpa using airyAi'_neg le_rfl
  have him : 0 < ((airyAi' 0 : ℂ) + (airyAi 0 : ℂ) * Complex.I).im := by
    simpa using airyAi_pos le_rfl
  refine ⟨θ, hθ, ?_, ?_, ?_⟩
  · rw [h0]
    by_contra hle
    have hle' := not_lt.mp hle
    have := Complex.arg_lt_pi_div_two_iff.mp (lt_of_le_of_ne hle' ?_)
    · rcases this with h | h | h
      · exact absurd h (not_lt.mpr hre.le)
      · exact absurd h (not_lt.mpr him.le)
      · rw [h] at hre; simp at hre
    · intro heq
      -- arg = π/2 forces re = 0
      have := Complex.arg_eq_pi_div_two_iff.mp heq
      exact absurd this.1 hre.ne
  · rw [h0]
    exact lt_of_le_of_ne (Complex.arg_le_pi _) (fun heq => by
      have := Complex.arg_eq_pi_iff.mp heq
      exact absurd this.2 him.ne')
  · exact hθ.strictMonoOn_of_neg (convex_Iic 0)
      (by rw [interior_Iic]; exact fun x hx => hx)

/-- `Ai x = 0` exactly at the levels `θ = kπ`. -/
theorem airy_zero_iff_level {θ : ℝ → ℝ} (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ) (x : ℝ) :
    airyAi x = 0 ↔ ∃ k : ℤ, θ x = k * Real.pi :=
  hθ.zero_iff_exists_int x

/-- Zero count of `Ai` on `(a, 0]`: with the normalisation `θ 0 ∈ (0, π)` the number of zeros of `Ai` in
`(a, 0]` is `-⌊θ(a)/π⌋`. -/
theorem airy_zeros_ncard {θ : ℝ → ℝ} (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ)
    (h0 : 0 < θ 0) (h1 : θ 0 < Real.pi) {a : ℝ} (ha : a ≤ 0) :
    (({x | x ∈ Ioc a 0 ∧ airyAi x = 0}).ncard : ℤ) = -⌊θ a / Real.pi⌋ := by
  have hfl : ⌊θ 0 / Real.pi⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨by positivity, (div_lt_one Real.pi_pos).2 h1⟩
  rw [hθ.zeros_ncard ha, hfl]; ring

/-- The Clark nodes of `Ai` on `(-∞, 0]`: for every `α` and every integer `m` with `α + mπ ≤ θ 0`
the function `cos α·Ai − sin α·Ai'` has exactly one zero `x ≤ 0` at the level `θ x = α + mπ`. -/
theorem airy_node_exists_unique {θ : ℝ → ℝ} (hθ : IsPruferLift (fun x => x) airyAi airyAi' θ)
    {α : ℝ} {m : ℤ} (hm : α + m * Real.pi ≤ θ 0) :
    ∃! x, x ≤ 0 ∧ θ x = α + m * Real.pi ∧ combo α airyAi airyAi' x = 0 :=
  airy_exists_unique_combo_zero_Iic_level hθ le_rfl hm

/-- info: 'FormalResearch.Special.airy_exists_prufer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_exists_prufer

/-- info: 'FormalResearch.Special.airy_zero_iff_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_zero_iff_level

/-- info: 'FormalResearch.Special.airy_zeros_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_zeros_ncard

/-- info: 'FormalResearch.Special.airy_node_exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_node_exists_unique

end FormalResearch.Special

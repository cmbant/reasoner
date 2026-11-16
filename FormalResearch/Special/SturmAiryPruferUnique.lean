module

public import FormalResearch.Special.AiryPruferLift
public import FormalResearch.Special.SturmAiryInterlace
public import FormalResearch.Special.SturmAiryLevels

/-!
# Prüfer lifts: uniqueness mod `2π`, the polar form of `cos α · y - sin α · y'`, simple zeros

Conventions as in `AiryPruferLift`: a Prüfer lift `θ` of a solution `(y, y')` of `y'' = q y` satisfies
`y = r sin θ`, `y' = r cos θ` with `r > 0`.

* `IsPruferLift.exists_int_eq_add`: **uniqueness mod `2π`**.  Two Prüfer lifts `θ₁, θ₂` of the same
  `(y, y')` differ by a constant `2πk`, `k ∈ ℤ`; conversely `θ + 2πk` is again a lift
  (`IsPruferLift.add_int_mul_two_pi`).  (Pointwise the difference lies in `2πℤ` because `(r, θ)` are
  polar data of the same nonzero vector; a continuous function with values in `2πℤ` is constant.)
  So `θ` is canonical up to `2πℤ`; the floor differences `⌊(θ b - α)/π⌋ - ⌊(θ a - α)/π⌋` used below are
  insensitive to the choice.
* `IsPruferLift.combo_eq`: `u_α := cos α · y - sin α · y' = r sin (θ - α)` with `r > 0`; hence
  `IsPruferLift.combo_eq_zero_iff`: `u_α x = 0 ↔ ∃ k : ℤ, θ x = α + kπ` (an iff, proved).
* `IsSol.contDiff_combo`: `u_α` is `C¹` (`u_α` is **not** a solution of `y'' = q y`).
* `IsSol.deriv_combo_ne_zero_of_zero`: at a zero `x₀` of `u_α` with `cos² α - q(x₀) sin² α ≠ 0`
  (in particular whenever `q x₀ < 0`, `IsSol.deriv_combo_ne_zero_of_zero_of_neg`) one has
  `u_α' x₀ ≠ 0`: **the zeros of `u_α` are simple** wherever `q < 0`.  The identities
  `sin α · u_α' = (cos² α - q sin² α) y` and `cos α · u_α' = (cos² α - q sin² α) y'` at a zero are
  the whole proof.  (No sign statement for `u_α'` is made.)

Not formalised: simplicity of the zeros of `u_α` at points where `cos² α = q(x₀) sin² α` (there it can
fail), sign of `u_α'` at the zeros.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special.SturmAiry

variable {q y y' : ℝ → ℝ}

/-! ### A continuous function with values in `2πℤ` is constant -/

private theorem const_of_lattice {d : ℝ → ℝ} (hd : Continuous d)
    (hn : ∀ x, ∃ n : ℤ, d x = n * (2 * Real.pi)) (x₁ x₂ : ℝ) : d x₁ = d x₂ := by
  have key : ∀ x y : ℝ, ∀ nx ny : ℤ, d x = nx * (2 * Real.pi) → d y = ny * (2 * Real.pi) →
      nx < ny → False := by
    intro x y nx ny hx hy hlt
    have h1 : (nx : ℝ) + 1 ≤ ny := by exact_mod_cast hlt
    have hv : d x + Real.pi ∈ uIcc (d x) (d y) := by
      refine Set.mem_uIcc.2 (Or.inl ⟨by linarith [Real.pi_pos], ?_⟩)
      rw [hy]
      nlinarith [mul_nonneg (sub_nonneg.2 h1) Real.pi_pos.le, Real.pi_pos]
    obtain ⟨z, -, hz⟩ := intermediate_value_uIcc (a := x) (b := y) hd.continuousOn hv
    obtain ⟨m, hm⟩ := hn z
    have h2 : (2 * (m : ℝ) - 2 * nx - 1) * Real.pi = 0 := by
      rw [hm, hx] at hz; linarith
    have h3 : (2 * (m : ℝ) - 2 * nx - 1) = 0 := (mul_eq_zero.1 h2).resolve_right Real.pi_ne_zero
    have h4 : (2 * m - 2 * nx - 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  by_contra hne
  obtain ⟨n₁, h₁⟩ := hn x₁
  obtain ⟨n₂, h₂⟩ := hn x₂
  rcases lt_trichotomy n₁ n₂ with h | h | h
  · exact key x₁ x₂ n₁ n₂ h₁ h₂ h
  · exact hne (by rw [h₁, h₂, h])
  · exact key x₂ x₁ n₂ n₁ h₂ h₁ h

namespace IsPruferLift

variable {θ θ₁ θ₂ : ℝ → ℝ}

/-- **Uniqueness of the Prüfer lift mod `2π`.**  If `θ₁, θ₂` are Prüfer lifts of the same
solution `(y, y')` then `θ₂ = θ₁ + 2πk` for a fixed integer `k`. -/
theorem exists_int_eq_add (h1 : IsPruferLift q y y' θ₁) (h2 : IsPruferLift q y y' θ₂) :
    ∃ k : ℤ, ∀ x, θ₂ x = θ₁ x + k * (2 * Real.pi) := by
  obtain ⟨r₁, hr₁, hy₁, hy'₁⟩ := h1.exists_r
  obtain ⟨r₂, hr₂, hy₂, hy'₂⟩ := h2.exists_r
  have hnorm : ∀ (r t : ℝ), (r * Real.sin t) ^ 2 + (r * Real.cos t) ^ 2 = r ^ 2 := fun r t => by
    rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one]
  have hpt : ∀ x, ∃ n : ℤ, θ₂ x - θ₁ x = n * (2 * Real.pi) := by
    intro x
    have hsq : r₁ x ^ 2 = r₂ x ^ 2 := by
      rw [← hnorm (r₁ x) (θ₁ x), ← hy₁ x, ← hy'₁ x, hy₂ x, hy'₂ x, hnorm]
    have hr : r₁ x = r₂ x := (sq_eq_sq₀ (hr₁ x).le (hr₂ x).le).1 hsq
    have hs : Real.sin (θ₂ x) = Real.sin (θ₁ x) := by
      have := (hy₁ x).symm.trans (hy₂ x)
      rw [hr] at this
      exact (mul_left_cancel₀ (hr₂ x).ne' this).symm
    have hc : Real.cos (θ₂ x) = Real.cos (θ₁ x) := by
      have := (hy'₁ x).symm.trans (hy'₂ x)
      rw [hr] at this
      exact (mul_left_cancel₀ (hr₂ x).ne' this).symm
    have h1' : Real.cos (θ₂ x - θ₁ x) = 1 := by
      rw [Real.cos_sub, hs, hc]
      nlinarith [Real.sin_sq_add_cos_sq (θ₁ x)]
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 h1'
    exact ⟨n, hn.symm⟩
  have hd : Continuous fun x => θ₂ x - θ₁ x := h2.continuous.sub h1.continuous
  obtain ⟨k, hk⟩ := hpt 0
  refine ⟨k, fun x => ?_⟩
  have := const_of_lattice hd hpt x 0
  linarith

/-- Adding `2πk` to a Prüfer lift gives a Prüfer lift. -/
theorem add_int_mul_two_pi (hθ : IsPruferLift q y y' θ) (k : ℤ) :
    IsPruferLift q y y' (fun x => θ x + k * (2 * Real.pi)) := by
  obtain ⟨r, hr, hy, hy'⟩ := hθ.exists_r
  refine ⟨⟨r, hr, fun x => ?_, fun x => ?_⟩, fun x => ?_⟩
  · rw [Real.sin_add_int_mul_two_pi]; exact hy x
  · rw [Real.cos_add_int_mul_two_pi]; exact hy' x
  · have := (hθ.hasDerivAt x).add_const ((k : ℝ) * (2 * Real.pi))
    rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]
    exact this

/-- **Polar form of `u_α`.**  `cos α · y - sin α · y' = r sin (θ - α)` with `r > 0`. -/
theorem combo_eq (hθ : IsPruferLift q y y' θ) (α : ℝ) :
    ∃ r : ℝ → ℝ, (∀ x, 0 < r x) ∧ ∀ x, combo α y y' x = r x * Real.sin (θ x - α) := by
  obtain ⟨r, hr, hy, hy'⟩ := hθ.exists_r
  refine ⟨r, hr, fun x => ?_⟩
  unfold combo
  rw [hy x, hy' x, Real.sin_sub]
  ring

/-- The zeros of `u_α = cos α · y - sin α · y'` are exactly the points where the Prüfer angle lies in
`α + πℤ`. -/
theorem combo_eq_zero_iff (hθ : IsPruferLift q y y' θ) (α x : ℝ) :
    combo α y y' x = 0 ↔ ∃ k : ℤ, θ x = α + k * Real.pi := by
  obtain ⟨r, hr, h⟩ := hθ.combo_eq α
  rw [h x, mul_eq_zero, Real.sin_eq_zero_iff]
  constructor
  · rintro (h0 | ⟨k, hk⟩)
    · exact absurd h0 (hr x).ne'
    · exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact Or.inr ⟨k, by linarith⟩

/-- `AtLevel θ α` is the zero set of `u_α` (the form used by the counting lemmas). -/
theorem combo_eq_zero_iff_atLevel (hθ : IsPruferLift q y y' θ) (α x : ℝ) :
    combo α y y' x = 0 ↔ AtLevel θ α x :=
  hθ.combo_eq_zero_iff α x

end IsPruferLift

namespace IsSol

/-- `u_α = cos α · y - sin α · y'` is `C¹` when `q` is continuous. -/
theorem contDiff_combo (hq : Continuous q) (h : IsSol q y y') (α : ℝ) :
    ContDiff ℝ 1 (combo α y y') := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun x => (h.hasDerivAt_combo α x).differentiableAt, ?_⟩
  have : deriv (combo α y y') =
      fun x => Real.cos α * y' x - Real.sin α * (q x * y x) :=
    funext fun x => (h.hasDerivAt_combo α x).deriv
  rw [this]
  have := h.continuous
  have := h.continuous'
  fun_prop

/-- **Zeros of `u_α` are simple** wherever `cos² α - q(x₀) sin² α ≠ 0`:
`u_α x₀ = 0 → u_α' x₀ ≠ 0` for a nontrivial solution. -/
theorem deriv_combo_ne_zero_of_zero (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0)
    {α x₀ : ℝ} (hz : combo α y y' x₀ = 0)
    (hc : Real.cos α ^ 2 - q x₀ * Real.sin α ^ 2 ≠ 0) :
    Real.cos α * y' x₀ - Real.sin α * (q x₀ * y x₀) ≠ 0 := by
  intro h0
  unfold combo at hz
  have e1 : Real.sin α * (Real.cos α * y' x₀ - Real.sin α * (q x₀ * y x₀)) =
      (Real.cos α ^ 2 - q x₀ * Real.sin α ^ 2) * y x₀ := by
    linear_combination (-Real.cos α) * hz
  have e2 : Real.cos α * (Real.cos α * y' x₀ - Real.sin α * (q x₀ * y x₀)) =
      (Real.cos α ^ 2 - q x₀ * Real.sin α ^ 2) * y' x₀ := by
    linear_combination (-(q x₀) * Real.sin α) * hz
  rw [h0, mul_zero] at e1 e2
  have h1 : y x₀ = 0 := (mul_eq_zero.1 e1.symm).resolve_left hc
  have h2 : y' x₀ = 0 := (mul_eq_zero.1 e2.symm).resolve_left hc
  rcases h.data_ne_zero hq hy x₀ with h3 | h3
  · exact h3 h1
  · exact h3 h2

/-- If `q x₀ < 0`, then `cos² α - q(x₀) sin² α > 0` for every `α`. -/
theorem cos_sq_sub_pos {q₀ : ℝ} (hq : q₀ < 0) (α : ℝ) : 0 < Real.cos α ^ 2 - q₀ * Real.sin α ^ 2 := by
  by_cases hs : Real.sin α = 0
  · have := Real.sin_sq_add_cos_sq α
    rw [hs] at this ⊢
    nlinarith
  · have hs2 : 0 < Real.sin α ^ 2 := by positivity
    nlinarith [sq_nonneg (Real.cos α), mul_pos (neg_pos.2 hq) hs2]

/-- **Zeros of `u_α` are simple where `q < 0`** (for `q x = x`: on the negative axis). -/
theorem deriv_combo_ne_zero_of_zero_of_neg (hq : Continuous q) (h : IsSol q y y')
    (hy : ∃ x, y x ≠ 0) {α x₀ : ℝ} (hz : combo α y y' x₀ = 0) (hneg : q x₀ < 0) :
    deriv (combo α y y') x₀ ≠ 0 := by
  rw [(h.hasDerivAt_combo α x₀).deriv]
  exact h.deriv_combo_ne_zero_of_zero hq hy hz (cos_sq_sub_pos hneg α).ne'

end IsSol

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.exists_int_eq_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.exists_int_eq_add

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.add_int_mul_two_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.add_int_mul_two_pi

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.combo_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.combo_eq

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.combo_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.combo_eq_zero_iff

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.contDiff_combo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.contDiff_combo

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.deriv_combo_ne_zero_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.deriv_combo_ne_zero_of_zero

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.deriv_combo_ne_zero_of_zero_of_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.deriv_combo_ne_zero_of_zero_of_neg

end FormalResearch.Special.SturmAiry

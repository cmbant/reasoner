module

public import FormalResearch.Special.SturmAiryZeros

/-!
# Interlacing of the zeros of `cos α · y - sin α · y'` with those of `y`

For a nontrivial real solution `y` of `y'' = q y` and an angle `α`, put
`u_α = cos α · y - sin α · y'` (for `y = Ai` these are the functions whose zeros are the Clark nodes
of the Airy de Branges space).  `u_α` is **not** a solution of `y'' = q y`; the interlacing is
the generalised Wronskian argument `exists_unique_zero_of_sep` with `f' g - f g' = ∓ sin α (y'² - q y²)`.

On an interval where `q < 0` (for `q x = x`: the negative half-line), and `sin α ≠ 0`:

* `IsSol.exists_unique_zero_combo_between` : between two consecutive zeros `a < b` of `y` there is
  exactly one zero of `u_α`;
* `IsSol.exists_unique_zero_between_combo`: between two consecutive zeros of `u_α` there is exactly
  one zero of `y`.

Hence the two zero sets strictly interlace on `{q < 0}`.  Not formalised: the statement where `q`
changes sign (it is false in general for `q > 0`: there `y` has at most one zero), or the position of
the first node (for `y = Ai` the labelling of all nodes, the first included, is `Special.AiryClarkLabel`) (the zeros of `u_α` being simple, and the interlacing in counting form with the
position of the nodes through the Prüfer angle, are in `SturmAiryPruferUnique`, `SturmAiryNodes`).
-/

@[expose] public section

open Set

namespace FormalResearch.Special.SturmAiry

variable {q y y' : ℝ → ℝ}

/-- `u_α = cos α · y - sin α · y'`. -/
noncomputable def combo (α : ℝ) (y y' : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.cos α * y x - Real.sin α * y' x

namespace IsSol

theorem hasDerivAt_combo (α : ℝ) (h : IsSol q y y') (x : ℝ) :
    HasDerivAt (combo α y y')
      (Real.cos α * y' x - Real.sin α * (q x * y x)) x :=
  ((h.hasDerivAt x).const_mul (Real.cos α)).sub ((h.hasDerivAt' x).const_mul (Real.sin α))

/-- On `{q < 0}` the quantity `y'² - q y²` of a nontrivial solution is positive. -/
theorem sq_sub_pos (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0) {x : ℝ}
    (hqx : q x < 0) : 0 < y' x ^ 2 - q x * y x ^ 2 := by
  rcases h.data_ne_zero hq hy x with h1 | h1
  · have : 0 < y x ^ 2 := by positivity
    nlinarith [sq_nonneg (y' x), mul_pos (neg_pos.2 hqx) this]
  · have : 0 < y' x ^ 2 := by positivity
    nlinarith [mul_nonneg (neg_nonneg.2 hqx.le) (sq_nonneg (y x))]

/-- Between consecutive zeros `a < b` of a nontrivial solution `y`, on an interval where `q < 0`,
exactly one zero of `cos α · y - sin α · y'` (`sin α ≠ 0`). -/
theorem exists_unique_zero_combo_between (hq : Continuous q) (h : IsSol q y y')
    (hy : ∃ x, y x ≠ 0) {α : ℝ} (hα : Real.sin α ≠ 0) {a b : ℝ} (hab : a < b) (ha : y a = 0)
    (hb : y b = 0) (hne : ∀ x ∈ Ioo a b, y x ≠ 0) (hneg : ∀ x ∈ Icc a b, q x < 0) :
    ∃! c, c ∈ Ioo a b ∧ combo α y y' c = 0 := by
  refine exists_unique_zero_of_sep h.hasDerivAt (h.hasDerivAt_combo α) hab ha hb hne ?_
  intro x hx hx0
  have := h.sq_sub_pos hq hy (hneg x hx)
  have e : y' x * combo α y y' x - y x * (Real.cos α * y' x - Real.sin α * (q x * y x)) =
      -Real.sin α * (y' x ^ 2 - q x * y x ^ 2) := by
    unfold combo; ring
  rw [e] at hx0
  exact (mul_ne_zero (neg_ne_zero.2 hα) this.ne') hx0

/-- Between consecutive zeros `a < b` of `cos α · y - sin α · y'` (`sin α ≠ 0`), on an interval
where `q < 0`, exactly one zero of the nontrivial solution `y`. -/
theorem exists_unique_zero_between_combo (hq : Continuous q) (h : IsSol q y y')
    (hy : ∃ x, y x ≠ 0) {α : ℝ} (hα : Real.sin α ≠ 0) {a b : ℝ} (hab : a < b)
    (ha : combo α y y' a = 0) (hb : combo α y y' b = 0)
    (hne : ∀ x ∈ Ioo a b, combo α y y' x ≠ 0) (hneg : ∀ x ∈ Icc a b, q x < 0) :
    ∃! c, c ∈ Ioo a b ∧ y c = 0 := by
  refine exists_unique_zero_of_sep (h.hasDerivAt_combo α) h.hasDerivAt hab ha hb hne ?_
  intro x hx hx0
  have := h.sq_sub_pos hq hy (hneg x hx)
  have e : (Real.cos α * y' x - Real.sin α * (q x * y x)) * y x - combo α y y' x * y' x =
      Real.sin α * (y' x ^ 2 - q x * y x ^ 2) := by
    unfold combo; ring
  rw [e] at hx0
  exact (mul_ne_zero hα this.ne') hx0

end IsSol

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_unique_zero_combo_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_unique_zero_combo_between

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_unique_zero_between_combo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_unique_zero_between_combo

end FormalResearch.Special.SturmAiry

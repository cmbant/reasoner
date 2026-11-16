module

public import FormalResearch.Special.AiryPruferZeros
public import FormalResearch.Special.SturmAiryPruferUnique

/-!
# Zeros of `cos α · y - sin α · y'` located through the Prüfer angle (`q < 0`)

Let `(y, y')` solve `y'' = q y`, `θ` a Prüfer lift (`y = r sin θ`, `y' = r cos θ`,
`θ' = cos² θ - q sin² θ`) and `u_α = cos α · y - sin α · y' = r sin (θ - α)`
(`SturmAiryPruferUnique`).  The zeros of `u_α` are the points where `θ ∈ α + πℤ`
(`IsPruferLift.combo_eq_zero_iff`).  On an interval where `q < 0`, `θ' > 0`, so `θ` is strictly
increasing there (`IsPruferLift.strictMonoOn_of_neg`) and the zeros of `u_α` are read off from the
levels of `θ`.  For the Airy equation `q x = x` the interval is the negative half-line, and the
zeros of `u_α` in the case `y = Ai` are the Clark nodes.

* `IsPruferLift.combo_zeros_ncard`, `combo_zeros_finite`: **zero count** — if `q < 0` on `(a, b)`,
  `a ≤ b`, then `#{x ∈ (a, b] : u_α x = 0} = ⌊(θ b - α)/π⌋ - ⌊(θ a - α)/π⌋` (for `α = 0` this is
  `zeros_ncard` of `AiryPruferZeros`, under the extra hypothesis `q < 0`; the existing statement
  needs none).
* `IsPruferLift.consecutive_combo_zeros_gap`: consecutive zeros `a < b` of `u_α` (nothing between)
  have `θ b = θ a + π`.
* **Interlacing in counting form** (`IsPruferLift.exists_unique_combo_zero_between_combo_zeros`,
  `..._Ioo`, `IsSol.exists_unique_combo_zero_between_combo_zeros`): between consecutive zeros
  `a < b` of `u_α` (on `(a, b)`: `q < 0`), for every `α'` exactly one zero of `u_α'` lies in
  `(a, b]`, and it lies in `(a, b)` when `sin (α' - α) ≠ 0` (if
  `α' - α ∈ πℤ` it is `b`).  For `α = 0` (`u_0 = y`) this is the interlacing of the zeros of `y` with those
  of `u_α'` (`IsSol.exists_unique_combo_zero_between_zeros`); with `sin α ≠ 0` it reproves
  `IsSol.exists_unique_zero_combo_between` (that one needs `q < 0` on the closed interval).  Any
  two such `u_α, u_α'` interlace (for `0 < α' - α < π` the order is `z_m^α < z_m^α' < z_{m+1}^α`,
  `IsPruferLift.between_combo_zeros`).
* `Levels.lt_iff_of_levels`, `IsPruferLift.node_between`: **position of the `m`-th node relative to
  the zeros of `y`**: if `jπ < α < (j+1)π` then the zero of `u_α` at level `θ = α + mπ` lies strictly
  between the zeros of `y` at levels `(m+j)π` and `(m+j+1)π`, and `y`'s zero at level `kπ` is to the
  left of it iff `k ≤ m + j`.  (`α ∈ (0, π)` is `j = 0`: node `m` is in `(z_m, z_{m+1})`;
  `α ∈ (-π, 0)` is `j = -1`: node `m` is in `(z_{m-1}, z_m)`.)
* `IsPruferLift.exists_unique_le_level`, `IsPruferLift.exists_unique_combo_zero_Iic_level`: for `q < 0`
  on `(-∞, b)` with `θ` unbounded below on `(-∞, b]`, every level `L ≤ θ b` is attained exactly once on
  `(-∞, b]`; so the zeros of `u_α` in `(-∞, b]` are `x_m`, `θ x_m = α + mπ`, `m ≤ ⌊(θ b - α)/π⌋`, one for
  each such `m` (`IsPruferLift.exists_floor_of_combo_zero`), increasing in `m`.
  `IsPruferLift.exists_le_of_le_neg_one` gives the unboundedness from `q ≤ -1` on `(-∞, b₁]`, and
  `airy_exists_unique_combo_zero_Iic_level` is the case `q x = x`, `b ≤ 0`.

Hypotheses and not formalised: everything needs `q < 0` on the interval in question (for `q > 0` the
statements are false: a nontrivial solution has at most one zero there); no "iff" is claimed for the
count beyond the displayed formula.  The identification of `θ b` for `y = Ai` (where the first node
sits relative to the largest zero of `Ai`) needs the behaviour of `Ai` on the positive axis and is not
part of this generic layer.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special.SturmAiry

variable {q y y' : ℝ → ℝ}

namespace Levels

variable {g : ℝ → ℝ}

/-- **Position of nodes relative to zeros** (pure monotonicity statement): if `g` is strictly
increasing on `D`, `jπ < α < (j+1)π`, `g x = kπ`, `g x' = α + mπ` (`x, x' ∈ D`), then
`x < x' ↔ k ≤ m + j`. -/
theorem lt_iff_of_levels {D : Set ℝ} (hm : StrictMonoOn g D) {x x' : ℝ} (hx : x ∈ D) (hx' : x' ∈ D)
    {α : ℝ} {j k m : ℤ} (hα1 : j * Real.pi < α) (hα2 : α < (j + 1) * Real.pi)
    (hk : g x = k * Real.pi) (hm' : g x' = α + m * Real.pi) : x < x' ↔ k ≤ m + j := by
  rw [← hm.lt_iff_lt hx hx', hk, hm']
  constructor
  · intro h
    by_contra hc
    have h1 : ((m : ℝ) + j + 1) ≤ k := by exact_mod_cast (by omega : m + j + 1 ≤ k)
    have := mul_le_mul_of_nonneg_right h1 Real.pi_pos.le
    nlinarith
  · intro h
    have h1 : (k : ℝ) ≤ m + j := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right h1 Real.pi_pos.le
    nlinarith

end Levels

namespace IsPruferLift

variable {θ : ℝ → ℝ} {a b : ℝ}

/-- **`θ' > 0` where `q < 0`**: on a convex set `D` with `q < 0` on its interior, the Prüfer angle is
strictly increasing. -/
theorem strictMonoOn_of_neg (hθ : IsPruferLift q y y' θ) {D : Set ℝ} (hD : Convex ℝ D)
    (hq : ∀ x ∈ interior D, q x < 0) : StrictMonoOn θ D := by
  refine strictMonoOn_of_deriv_pos hD hθ.continuous.continuousOn ?_
  intro x hx
  rw [(hθ.hasDerivAt x).deriv]
  exact IsSol.cos_sq_sub_pos (hq x hx) (θ x)

theorem strictMonoOn_Icc_of_neg (hθ : IsPruferLift q y y' θ) (hneg : ∀ x ∈ Ioo a b, q x < 0) :
    StrictMonoOn θ (Icc a b) :=
  hθ.strictMonoOn_of_neg (convex_Icc a b) (by rw [interior_Icc]; exact hneg)

/-- **Zero count of `u_α` through the Prüfer angle.**  If `q < 0` on `(a, b)` and `a ≤ b`, then
`#{x ∈ (a, b] : cos α · y x - sin α · y' x = 0} = ⌊(θ b - α)/π⌋ - ⌊(θ a - α)/π⌋`. -/
theorem combo_zeros_ncard (hθ : IsPruferLift q y y' θ) (hab : a ≤ b)
    (hneg : ∀ x ∈ Ioo a b, q x < 0) (α : ℝ) :
    (({x | x ∈ Ioc a b ∧ combo α y y' x = 0}).ncard : ℤ) =
      ⌊(θ b - α) / Real.pi⌋ - ⌊(θ a - α) / Real.pi⌋ := by
  have hset : {x | x ∈ Ioc a b ∧ combo α y y' x = 0} = {x | x ∈ Ioc a b ∧ AtLevel θ α x} :=
    Set.ext fun x => and_congr_right fun _ => hθ.combo_eq_zero_iff_atLevel α x
  rw [hset]
  exact Levels.ncard_levels hab hθ.continuous.continuousOn (hθ.strictMonoOn_Icc_of_neg hneg) α

/-- The zeros of `u_α` in `(a, b]` form a finite set when `q < 0` on `(a, b)`. -/
theorem combo_zeros_finite (hθ : IsPruferLift q y y' θ) (hab : a ≤ b)
    (hneg : ∀ x ∈ Ioo a b, q x < 0) (α : ℝ) :
    {x | x ∈ Ioc a b ∧ combo α y y' x = 0}.Finite := by
  have hset : {x | x ∈ Ioc a b ∧ combo α y y' x = 0} = {x | x ∈ Ioc a b ∧ AtLevel θ α x} :=
    Set.ext fun x => and_congr_right fun _ => hθ.combo_eq_zero_iff_atLevel α x
  rw [hset]
  exact Levels.finite_levels hab (hθ.strictMonoOn_Icc_of_neg hneg) α

/-- Consecutive zeros `a < b` of `u_α` (none strictly between, `q < 0` on `(a, b)`) are one
half-turn apart: `θ b = θ a + π`. -/
theorem consecutive_combo_zeros_gap (hθ : IsPruferLift q y y' θ) {α : ℝ} (hab : a < b)
    (hneg : ∀ x ∈ Ioo a b, q x < 0) (ha : combo α y y' a = 0) (hb : combo α y y' b = 0)
    (hne : ∀ x ∈ Ioo a b, combo α y y' x ≠ 0) : θ b = θ a + Real.pi := by
  obtain ⟨k, hk⟩ := (hθ.combo_eq_zero_iff α a).1 ha
  obtain ⟨k', hk'⟩ := (hθ.combo_eq_zero_iff α b).1 hb
  have hne' : ∀ x ∈ Ioo a b, ¬ AtLevel θ α x := fun x hx hl =>
    hne x hx ((hθ.combo_eq_zero_iff α x).2 hl)
  have := Levels.level_succ hab hθ.continuous.continuousOn (hθ.strictMonoOn_Icc_of_neg hneg) hk hk'
    hne'
  rw [hk, hk', this]
  push_cast
  ring

/-- **Interlacing, counting form.**  Let `a < b` be consecutive zeros of `u_α` and `q < 0` on
`(a, b)`.  Then for every `α'` there is exactly one zero of `u_α'` in `(a, b]`. -/
theorem exists_unique_combo_zero_between_combo_zeros (hθ : IsPruferLift q y y' θ) {α α' : ℝ}
    (hab : a < b) (hneg : ∀ x ∈ Ioo a b, q x < 0) (ha : combo α y y' a = 0)
    (hb : combo α y y' b = 0) (hne : ∀ x ∈ Ioo a b, combo α y y' x ≠ 0) :
    ∃! x, x ∈ Ioc a b ∧ combo α' y y' x = 0 := by
  have hw := hθ.consecutive_combo_zeros_gap hab hneg ha hb hne
  exact (existsUnique_congr fun x => and_congr_right fun _ => hθ.combo_eq_zero_iff_atLevel α' x).2
    (Levels.exists_unique_window hab.le hθ.continuous.continuousOn
      (hθ.strictMonoOn_Icc_of_neg hneg) hw α')

/-- As `exists_unique_combo_zero_between_combo_zeros`, the zero of `u_α'` lies in the open interval
`(a, b)` when `sin (α' - α) ≠ 0` (in particular for `0 < α' - α < π`). -/
theorem exists_unique_combo_zero_between_combo_zeros_Ioo (hθ : IsPruferLift q y y' θ) {α α' : ℝ}
    (hab : a < b) (hneg : ∀ x ∈ Ioo a b, q x < 0) (ha : combo α y y' a = 0)
    (hb : combo α y y' b = 0) (hne : ∀ x ∈ Ioo a b, combo α y y' x ≠ 0)
    (hα : Real.sin (α' - α) ≠ 0) : ∃! x, x ∈ Ioo a b ∧ combo α' y y' x = 0 := by
  have hw := hθ.consecutive_combo_zeros_gap hab hneg ha hb hne
  have hnb : ¬ AtLevel θ α' b := by
    rintro ⟨m, hm⟩
    obtain ⟨k', hk'⟩ := (hθ.combo_eq_zero_iff α b).1 hb
    apply hα
    have : α' - α = ((k' - m : ℤ) : ℝ) * Real.pi := by push_cast; linarith
    rw [this]
    exact Real.sin_int_mul_pi _
  exact (existsUnique_congr fun x => and_congr_right fun _ => hθ.combo_eq_zero_iff_atLevel α' x).2
    (Levels.exists_unique_window_Ioo hab.le hθ.continuous.continuousOn
      (hθ.strictMonoOn_Icc_of_neg hneg) hw α' hnb)

/-- **Order of the nodes of `u_α` and `u_α'`** (`α < α' < α + π`): with `θ x₀ = α + mπ`,
`θ x₁ = α' + mπ`, `θ x₂ = α + (m+1)π` for points of a set `D` where `θ` is strictly increasing, one has
`x₀ < x₁ < x₂`. -/
theorem between_combo_zeros {D : Set ℝ} {θ : ℝ → ℝ} (hm : StrictMonoOn θ D) {x₀ x₁ x₂ : ℝ}
    (h₀ : x₀ ∈ D) (h₁ : x₁ ∈ D) (h₂ : x₂ ∈ D) {α α' : ℝ} {m : ℤ} (hlt : α < α')
    (hlt' : α' < α + Real.pi) (e₀ : θ x₀ = α + m * Real.pi) (e₁ : θ x₁ = α' + m * Real.pi)
    (e₂ : θ x₂ = α + (m + 1) * Real.pi) : x₀ < x₁ ∧ x₁ < x₂ := by
  refine ⟨(hm.lt_iff_lt h₀ h₁).1 (by rw [e₀, e₁]; linarith),
    (hm.lt_iff_lt h₁ h₂).1 (by rw [e₁, e₂]; linarith)⟩

/-- **The node `m` of `u_α` between zeros of `y`** (`jπ < α < (j+1)π`): points `x₀, x₁, x₂` of a set
`D` on which `θ` is strictly increasing, with `θ x₀ = (m+j)π`, `θ x₁ = α + mπ`, `θ x₂ = (m+j+1)π`
(so `y x₀ = y x₂ = 0 = u_α x₁`) satisfy `x₀ < x₁ < x₂`. -/
theorem node_between {D : Set ℝ} {θ : ℝ → ℝ} (hm : StrictMonoOn θ D) {x₀ x₁ x₂ : ℝ}
    (h₀ : x₀ ∈ D) (h₁ : x₁ ∈ D) (h₂ : x₂ ∈ D) {α : ℝ} {j m : ℤ} (hα1 : j * Real.pi < α)
    (hα2 : α < (j + 1) * Real.pi) (e₀ : θ x₀ = ((m : ℝ) + j) * Real.pi)
    (e₁ : θ x₁ = α + m * Real.pi) (e₂ : θ x₂ = ((m : ℝ) + j + 1) * Real.pi) :
    x₀ < x₁ ∧ x₁ < x₂ := by
  refine ⟨(hm.lt_iff_lt h₀ h₁).1 (by rw [e₀, e₁]; nlinarith),
    (hm.lt_iff_lt h₁ h₂).1 (by rw [e₁, e₂]; nlinarith)⟩

/-! ### Zeros of `u_α` on a half-line `(-∞, b]` -/

/-- On `(-∞, b]` with `q < 0` on `(-∞, b)` and `θ` unbounded below, every level `L ≤ θ b` is
attained exactly once. -/
theorem exists_unique_le_level (hθ : IsPruferLift q y y' θ) (hneg : ∀ x ∈ Iio b, q x < 0)
    (hunb : ∀ L, ∃ a ≤ b, θ a ≤ L) {L : ℝ} (hL : L ≤ θ b) : ∃! x, x ≤ b ∧ θ x = L := by
  have hm : StrictMonoOn θ (Iic b) :=
    hθ.strictMonoOn_of_neg (convex_Iic b) (by rw [interior_Iic]; exact hneg)
  obtain ⟨a, hab, ha⟩ := hunb L
  obtain ⟨x, hx, hxL⟩ := intermediate_value_Icc hab hθ.continuous.continuousOn
    (show L ∈ Icc (θ a) (θ b) from ⟨ha, hL⟩)
  exact ⟨x, ⟨hx.2, hxL⟩, fun z hz => hm.injOn hz.1 hx.2 (hz.2.trans hxL.symm)⟩

/-- **The `m`-th zero of `u_α` to the left of `b`.**  Under the hypotheses of `exists_unique_le_level`,
for every integer `m` with `α + mπ ≤ θ b` there is exactly one `x ≤ b` with `θ x = α + mπ`, and
it is a zero of `u_α`. -/
theorem exists_unique_combo_zero_Iic_level (hθ : IsPruferLift q y y' θ)
    (hneg : ∀ x ∈ Iio b, q x < 0) (hunb : ∀ L, ∃ a ≤ b, θ a ≤ L) {α : ℝ} {m : ℤ}
    (hm : α + m * Real.pi ≤ θ b) :
    ∃! x, x ≤ b ∧ θ x = α + m * Real.pi ∧ combo α y y' x = 0 := by
  obtain ⟨x, ⟨hx, hxL⟩, hu⟩ := hθ.exists_unique_le_level hneg hunb hm
  refine ⟨x, ⟨hx, hxL, (hθ.combo_eq_zero_iff α x).2 ⟨m, hxL⟩⟩, fun z hz => hu z ⟨hz.1, hz.2.1⟩⟩

/-- Every zero `x ≤ b` of `u_α` has `θ x = α + mπ` with `m ≤ ⌊(θ b - α)/π⌋`, when `q < 0` on
`(-∞, b)`. -/
theorem exists_floor_of_combo_zero (hθ : IsPruferLift q y y' θ) (hneg : ∀ x ∈ Iio b, q x < 0)
    {α x : ℝ} (hx : x ≤ b) (hz : combo α y y' x = 0) :
    ∃ m : ℤ, θ x = α + m * Real.pi ∧ m ≤ ⌊(θ b - α) / Real.pi⌋ := by
  have hm : StrictMonoOn θ (Iic b) :=
    hθ.strictMonoOn_of_neg (convex_Iic b) (by rw [interior_Iic]; exact hneg)
  obtain ⟨m, hm'⟩ := (hθ.combo_eq_zero_iff α x).1 hz
  refine ⟨m, hm', Int.le_floor.2 ((le_div_iff₀ Real.pi_pos).2 ?_)⟩
  have := hm.monotoneOn hx (le_refl b) hx
  linarith

/-- If `q ≤ -1` on `(-∞, b₁]`, `θ` is unbounded below there. -/
theorem exists_le_of_le_neg_one (hθ : IsPruferLift q y y' θ) {b₁ : ℝ} (hq : ∀ x ≤ b₁, q x ≤ -1)
    (L : ℝ) : ∃ a ≤ b₁, θ a ≤ L := by
  set t := |θ b₁ - L| with ht
  have ht0 : 0 ≤ t := abs_nonneg _
  refine ⟨b₁ - t, by linarith, ?_⟩
  have := hθ.sub_ge_of_le_neg_one (a := b₁ - t) (b := b₁) (by linarith) (fun x hx => hq x hx.2)
  have h2 := le_abs_self (θ b₁ - L)
  linarith

end IsPruferLift

namespace IsSol

variable {q y y' : ℝ → ℝ}

/-- **Interlacing of `u_α'` with the consecutive zeros of `u_α`** (no Prüfer angle in the statement):
for a nontrivial solution, `a < b` consecutive zeros of `cos α · y - sin α · y'` with `q < 0` on
`(a, b)`, and any `α'`, exactly one zero of `cos α' · y - sin α' · y'` in `(a, b]`; in `(a, b)` when
`sin (α' - α) ≠ 0`. -/
theorem exists_unique_combo_zero_between_combo_zeros (hq : Continuous q) (h : IsSol q y y')
    (hy : ∃ x, y x ≠ 0) {α α' a b : ℝ} (hab : a < b) (hneg : ∀ x ∈ Ioo a b, q x < 0)
    (ha : combo α y y' a = 0) (hb : combo α y y' b = 0)
    (hne : ∀ x ∈ Ioo a b, combo α y y' x ≠ 0) :
    (∃! x, x ∈ Ioc a b ∧ combo α' y y' x = 0) ∧
      (Real.sin (α' - α) ≠ 0 → ∃! x, x ∈ Ioo a b ∧ combo α' y y' x = 0) := by
  obtain ⟨θ, hθ, -⟩ := h.exists_isPruferLift hq hy 0
  exact ⟨hθ.exists_unique_combo_zero_between_combo_zeros hab hneg ha hb hne,
    fun hα => hθ.exists_unique_combo_zero_between_combo_zeros_Ioo hab hneg ha hb hne hα⟩

/-- **Interlacing with the zeros of `y`**: `a < b` consecutive zeros of the nontrivial solution `y`,
`q < 0` on `(a, b)`: exactly one zero of `cos α · y - sin α · y'` in `(a, b]`, in `(a, b)` when
`sin α ≠ 0` (this reproves `exists_unique_zero_combo_between`, with `q < 0` only on `(a, b)`). -/
theorem exists_unique_combo_zero_between_zeros (hq : Continuous q) (h : IsSol q y y')
    (hy : ∃ x, y x ≠ 0) {α a b : ℝ} (hab : a < b) (hneg : ∀ x ∈ Ioo a b, q x < 0)
    (ha : y a = 0) (hb : y b = 0) (hne : ∀ x ∈ Ioo a b, y x ≠ 0) :
    (∃! x, x ∈ Ioc a b ∧ combo α y y' x = 0) ∧
      (Real.sin α ≠ 0 → ∃! x, x ∈ Ioo a b ∧ combo α y y' x = 0) := by
  have e : ∀ x, combo 0 y y' x = y x := fun x => by simp [combo]
  have := h.exists_unique_combo_zero_between_combo_zeros hq hy (α := 0) (α' := α) hab hneg
    (by rw [e]; exact ha) (by rw [e]; exact hb) (fun x hx => by rw [e]; exact hne x hx)
  simpa using this

end IsSol

/-- **Nodes of `u_α` on the negative half-line of the Airy equation.**  For `y'' = x y`, a Prüfer lift
`θ` of a nontrivial solution, `b ≤ 0`, and every integer `m` with `α + mπ ≤ θ b`, there is exactly one
`x ≤ b` with `θ x = α + mπ`, and it is a zero of `cos α · y - sin α · y'`. -/
theorem airy_exists_unique_combo_zero_Iic_level {y y' θ : ℝ → ℝ}
    (hθ : IsPruferLift (fun x => x) y y' θ) {b : ℝ} (hb : b ≤ 0) {α : ℝ} {m : ℤ}
    (hm : α + m * Real.pi ≤ θ b) :
    ∃! x, x ≤ b ∧ θ x = α + m * Real.pi ∧ combo α y y' x = 0 := by
  have hneg : ∀ x ∈ Iio b, (fun x : ℝ => x) x < 0 := fun x hx => lt_of_lt_of_le hx hb
  have hmono : StrictMonoOn θ (Iic 0) :=
    hθ.strictMonoOn_of_neg (convex_Iic 0) (by rw [interior_Iic]; exact fun x hx => hx)
  refine hθ.exists_unique_combo_zero_Iic_level hneg (fun L => ?_) hm
  obtain ⟨a, ha, haL⟩ := hθ.exists_le_of_le_neg_one (b₁ := -1) (fun x hx => hx) L
  refine ⟨min a b, min_le_right _ _, le_trans ?_ haL⟩
  exact hmono.monotoneOn (show min a b ≤ 0 from (min_le_right _ _).trans hb)
    (show a ≤ 0 by linarith) (min_le_left _ _)

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.combo_zeros_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.combo_zeros_ncard

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.consecutive_combo_zeros_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.consecutive_combo_zeros_gap

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_unique_combo_zero_between_combo_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_unique_combo_zero_between_combo_zeros

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_unique_combo_zero_between_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_unique_combo_zero_between_zeros

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.node_between' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.node_between

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.between_combo_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.between_combo_zeros

/-- info: 'FormalResearch.Special.SturmAiry.Levels.lt_iff_of_levels' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.Levels.lt_iff_of_levels

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.exists_floor_of_combo_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.exists_floor_of_combo_zero

/-- info: 'FormalResearch.Special.SturmAiry.airy_exists_unique_combo_zero_Iic_level' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.airy_exists_unique_combo_zero_Iic_level

end FormalResearch.Special.SturmAiry

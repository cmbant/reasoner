module

public import Mathlib

/-!
# Sturm theory for `y'' = q y`: uniqueness, simple zeros, separation of zeros

Real solutions of the linear equation `y'' = q(x) y` on `ℝ`, with `q` continuous, in the form that
applies to `y = Ai`, `Bi` (take `q x = x`) and to any real combination of them.  Nothing here depends
on a definition of the Airy functions.

A solution is a pair `(y, y')` of real functions with `HasDerivAt y (y' x) x` and
`HasDerivAt y' (q x * y x) x` at every `x` (`IsSol`); `IsSol.of_deriv` turns a `C²` function with
`(deriv (deriv y)) x = q x * y x` into this form.

## Contents (all proved, no hypotheses beyond those displayed)

* `IsSol.eq_zero_of_zero_data`: uniqueness, `y a = y' a = 0 → y ≡ 0` (Grönwall on `y² + y'²`);
  hence a nontrivial solution has `(y x, y' x) ≠ (0, 0)` for every `x` (`IsSol.data_ne_zero`).
* `IsSol.wr_eq`: the Wronskian `y w' - y' w` of two solutions is constant;
  `IsSol.eq_smul_of_wr_eq_zero`: if it vanishes and `y` is nontrivial then `w = c y`
  (so, for `y` nontrivial, `wr ≠ 0` is exactly linear independence, one direction being trivial).
* `IsSol.deriv_ne_zero_of_zero` (zeros are simple), `IsSol.eventually_ne_of_zero` (isolated),
  `IsSol.finite_zeros_Icc` (finitely many zeros on a compact interval).
* `exists_unique_zero_of_sep`: the generic Rolle argument for the ratio of two functions whose
  generalised Wronskian does not vanish; `IsSol.sturm_separation`: **Sturm separation** — between
  two consecutive zeros `x₁ < x₂` of a solution `y` there is exactly one zero of every solution `w`
  with nonzero Wronskian with `y` (`IsSol.exists_zero_of_wr_ne_zero`: at least one between any two
  zeros of `y`).
* `IsSol.hasDerivAt_div` / `IsSol.hasDerivAt_logDeriv`: the ratio `w / y` has derivative
  `wr / y²`, and the real Riccati equation `(y'/y)' = q - (y'/y)²` where `y ≠ 0`.

Not formalised here: solutions on a proper interval only (everything is for `ℝ`-global solutions,
which is what `Ai`, `Bi` are), the complex (Herglotz) Riccati equation.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special.SturmAiry

/-- `(y, y')` is a real solution of `y'' = q y` on `ℝ`: `y' = dy/dx` and `y'' = q y` everywhere. -/
structure IsSol (q y y' : ℝ → ℝ) : Prop where
  hasDerivAt : ∀ x, HasDerivAt y (y' x) x
  hasDerivAt' : ∀ x, HasDerivAt y' (q x * y x) x

variable {q y y' w w' : ℝ → ℝ}

namespace IsSol

/-- A `C²` function with `y'' = q y` is a solution (with `y' = deriv y`). -/
theorem of_deriv (hy : Differentiable ℝ y) (hy' : Differentiable ℝ (deriv y))
    (h : ∀ x, deriv (deriv y) x = q x * y x) : IsSol q y (deriv y) where
  hasDerivAt x := (hy x).hasDerivAt
  hasDerivAt' x := by simpa [h x] using (hy' x).hasDerivAt

theorem continuous (h : IsSol q y y') : Continuous y :=
  continuous_iff_continuousAt.2 fun x => (h.hasDerivAt x).continuousAt

theorem continuous' (h : IsSol q y y') : Continuous y' :=
  continuous_iff_continuousAt.2 fun x => (h.hasDerivAt' x).continuousAt

theorem neg (h : IsSol q y y') : IsSol q (fun x => -y x) (fun x => -y' x) where
  hasDerivAt x := (h.hasDerivAt x).neg
  hasDerivAt' x := (h.hasDerivAt' x).neg.congr_deriv (by ring)

theorem const_mul (c : ℝ) (h : IsSol q y y') : IsSol q (fun x => c * y x) (fun x => c * y' x) where
  hasDerivAt x := (h.hasDerivAt x).const_mul c
  hasDerivAt' x := ((h.hasDerivAt' x).const_mul c).congr_deriv (by ring)

theorem sub (h : IsSol q y y') (h2 : IsSol q w w') :
    IsSol q (fun x => w x - y x) (fun x => w' x - y' x) where
  hasDerivAt x := (h2.hasDerivAt x).sub (h.hasDerivAt x)
  hasDerivAt' x := ((h2.hasDerivAt' x).sub (h.hasDerivAt' x)).congr_deriv (by ring)

/-- Time reversal. -/
theorem reflect (h : IsSol q y y') :
    IsSol (fun x => q (-x)) (fun x => y (-x)) (fun x => -y' (-x)) where
  hasDerivAt x := ((h.hasDerivAt (-x)).scomp x (hasDerivAt_neg x)).congr_deriv (by simp)
  hasDerivAt' x := ((h.hasDerivAt' (-x)).scomp x (hasDerivAt_neg x)).neg.congr_deriv (by simp)

/-- Forward half of uniqueness (Grönwall on `y² + y'²`). -/
private theorem eq_zero_forward (hq : Continuous q) (h : IsSol q y y') {a b : ℝ} (hab : a ≤ b)
    (hy : y a = 0) (hy' : y' a = 0) : ∀ x ∈ Icc a b, y x = 0 ∧ y' x = 0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hq.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC a ⟨le_rfl, hab⟩)
  have hE : ∀ x, HasDerivAt (fun x => y x ^ 2 + y' x ^ 2)
      (2 * y x * y' x + 2 * y' x * (q x * y x)) x := by
    intro x
    have := ((h.hasDerivAt x).pow 2).add ((h.hasDerivAt' x).pow 2)
    convert this using 1
    simp only [Nat.cast_ofNat]
    ring
  have key := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := 1 + C) (a := a) (b := b)
    (f := fun x => y x ^ 2 + y' x ^ 2)
    (f' := fun x => 2 * y x * y' x + 2 * y' x * (q x * y x))
    (fun x _ => (hE x).continuousAt.continuousWithinAt)
    (fun x _ => (hE x).hasDerivWithinAt) (by simp [hy, hy']) (by
      intro x hx
      have hqx : |q x| ≤ C := by simpa using hC x ⟨hx.1, hx.2.le⟩
      have h1 : |1 + q x| ≤ 1 + C := (abs_add_le _ _).trans (by simpa using hqx)
      have h2 : |2 * (y x * y' x)| ≤ y x ^ 2 + y' x ^ 2 := by
        rw [abs_le]; constructor <;> nlinarith [sq_nonneg (y x + y' x), sq_nonneg (y x - y' x)]
      have h3 : 2 * y x * y' x + 2 * y' x * (q x * y x) = (1 + q x) * (2 * (y x * y' x)) := by
        ring
      rw [Real.norm_eq_abs, Real.norm_eq_abs, h3, abs_mul,
        abs_of_nonneg (add_nonneg (sq_nonneg (y x)) (sq_nonneg (y' x)))]
      exact mul_le_mul h1 h2 (abs_nonneg _) (by linarith))
  intro x hx
  have := key x hx
  constructor <;> nlinarith [sq_nonneg (y x), sq_nonneg (y' x)]

/-- **Uniqueness** for `y'' = q y` with `q` continuous: zero Cauchy data at one point forces
`y ≡ 0` (and `y' ≡ 0`). -/
theorem eq_zero_of_zero_data (hq : Continuous q) (h : IsSol q y y') {a : ℝ} (hy : y a = 0)
    (hy' : y' a = 0) (x : ℝ) : y x = 0 ∧ y' x = 0 := by
  rcases le_total a x with hax | hxa
  · exact eq_zero_forward hq h hax hy hy' x ⟨hax, le_rfl⟩
  · have hq' : Continuous fun x => q (-x) := hq.comp continuous_neg
    have := eq_zero_forward hq' h.reflect (a := -a) (b := -x) (by linarith) (by simpa using hy)
      (by simpa using hy') (-x) ⟨by linarith, le_rfl⟩
    simpa using this

/-- A nontrivial solution has nonzero Cauchy data `(y x, y' x)` at every point. -/
theorem data_ne_zero (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0) (a : ℝ) :
    y a ≠ 0 ∨ y' a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx⟩ := hy
  exact hx (eq_zero_of_zero_data hq h hcon.1 hcon.2 x).1

/-- **Zeros are simple**: at a zero of a nontrivial solution, `y' ≠ 0`. -/
theorem deriv_ne_zero_of_zero (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0) {a : ℝ}
    (ha : y a = 0) : y' a ≠ 0 := by
  rcases data_ne_zero hq h hy a with h1 | h1
  · exact absurd ha h1
  · exact h1

/-- **Zeros are isolated.** -/
theorem eventually_ne_of_zero (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0) {a : ℝ}
    (ha : y a = 0) : ∀ᶠ x in 𝓝[≠] a, y x ≠ 0 := by
  have := (h.hasDerivAt a).eventually_ne (c := 0) (deriv_ne_zero_of_zero hq h hy ha)
  exact this

/-- A nontrivial solution has only finitely many zeros on a compact interval. -/
theorem finite_zeros_Icc (hq : Continuous q) (h : IsSol q y y') (hy : ∃ x, y x ≠ 0) (a b : ℝ) :
    {x | x ∈ Icc a b ∧ y x = 0}.Finite := by
  have hcl : IsClosed {x | x ∈ Icc a b ∧ y x = 0} :=
    isClosed_Icc.inter (isClosed_eq h.continuous continuous_const)
  have hc : IsCompact {x | x ∈ Icc a b ∧ y x = 0} :=
    isCompact_Icc.of_isClosed_subset hcl (fun x hx => hx.1)
  refine hc.finite ?_
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  have h1 := eventually_ne_of_zero hq h hy hx.2
  rw [← Filter.empty_mem_iff_bot, mem_inf_principal]
  filter_upwards [h1] with z hz hzs using absurd hzs.2 hz

/-! ### Wronskian -/

/-- The Wronskian `y w' - y' w`. -/
def wr (y y' w w' : ℝ → ℝ) (x : ℝ) : ℝ := y x * w' x - y' x * w x

theorem hasDerivAt_wr (h1 : IsSol q y y') (h2 : IsSol q w w') (x : ℝ) :
    HasDerivAt (wr y y' w w') 0 x := by
  have := ((h1.hasDerivAt x).mul (h2.hasDerivAt' x)).sub
    ((h1.hasDerivAt' x).mul (h2.hasDerivAt x))
  exact this.congr_deriv (by ring)

/-- The Wronskian of two solutions of the same equation is constant. -/
theorem wr_eq (h1 : IsSol q y y') (h2 : IsSol q w w') (x t : ℝ) :
    wr y y' w w' x = wr y y' w w' t :=
  is_const_of_deriv_eq_zero (fun x => (hasDerivAt_wr h1 h2 x).differentiableAt)
    (fun x => (hasDerivAt_wr h1 h2 x).deriv) x t

/-- If the Wronskian of `y` (nontrivial) and `w` vanishes, `w` is a multiple of `y`.  Together with
`wr_eq` this shows `wr ≠ 0 ↔ y, w linearly independent` (given `y` nontrivial). -/
theorem eq_smul_of_wr_eq_zero (hq : Continuous q) (h1 : IsSol q y y') (h2 : IsSol q w w')
    (hy : ∃ x, y x ≠ 0) {a : ℝ} (hW : wr y y' w w' a = 0) :
    ∃ c : ℝ, ∀ x, w x = c * y x ∧ w' x = c * y' x := by
  unfold wr at hW
  have hc : ∃ c : ℝ, w a = c * y a ∧ w' a = c * y' a := by
    rcases data_ne_zero hq h1 hy a with h | h
    · exact ⟨w a / y a, by field_simp, by field_simp; linarith⟩
    · exact ⟨w' a / y' a, by field_simp; linarith, by field_simp⟩
  obtain ⟨c, hc1, hc2⟩ := hc
  refine ⟨c, fun x => ?_⟩
  have := eq_zero_of_zero_data hq (h2.sub (h1.const_mul c)) (a := a) (by simp [hc1])
    (by simp [hc2]) x
  constructor <;> linarith [this.1, this.2]

end IsSol

/-! ### Rolle argument for the ratio of two functions -/

/-- **Rolle for a ratio.** If `g` has no zero on `[a, b]` and `f a = f b = 0`, the generalised
Wronskian `f' g - f g'` vanishes somewhere in `(a, b)`. -/
theorem exists_wr_eq_zero_of_ratio {f f' g g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) {a b : ℝ} (hab : a < b) (hfa : f a = 0) (hfb : f b = 0)
    (hg0 : ∀ x ∈ Icc a b, g x ≠ 0) : ∃ c ∈ Ioo a b, f' c * g c - f c * g' c = 0 := by
  have hd : ∀ x ∈ Icc a b, HasDerivAt (fun t => f t / g t)
      ((f' x * g x - f x * g' x) / g x ^ 2) x := fun x hx => (hf x).div (hg x) (hg0 x hx)
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (by simp [hfa, hfb])
    (fun x hx => hd x (Ioo_subset_Icc_self hx))
  refine ⟨c, hc, ?_⟩
  have := hg0 c (Ioo_subset_Icc_self hc)
  exact (div_eq_zero_iff.1 hc0).resolve_right (pow_ne_zero 2 this)

/-- **Generic Sturm separation.**  Let `f` have consecutive zeros `a < b` and let the generalised
Wronskian `f' g - f g'` be nonzero on `[a, b]`.  Then `g` has exactly one zero in `(a, b)`. -/
theorem exists_unique_zero_of_sep {f f' g g' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hg : ∀ x, HasDerivAt g (g' x) x) {a b : ℝ} (hab : a < b) (hfa : f a = 0) (hfb : f b = 0)
    (hfne : ∀ x ∈ Ioo a b, f x ≠ 0) (hW : ∀ x ∈ Icc a b, f' x * g x - f x * g' x ≠ 0) :
    ∃! c, c ∈ Ioo a b ∧ g c = 0 := by
  have hgab : ∀ x ∈ Icc a b, f x = 0 → g x ≠ 0 := by
    intro x hx hfx hgx
    exact hW x hx (by simp [hfx, hgx])
  have hno : ∀ c1 c2, a < c1 → c1 < c2 → c2 < b → g c1 = 0 → g c2 = 0 → False := by
    intro c1 c2 h1 h12 h2 hg1 hg2
    obtain ⟨c, hc, hc0⟩ := exists_wr_eq_zero_of_ratio hg hf h12 hg1 hg2
      (fun x hx => hfne x ⟨h1.trans_le hx.1, hx.2.trans_lt h2⟩)
    exact hW c ⟨(h1.trans hc.1).le, (hc.2.trans h2).le⟩ (by linarith)
  refine existsUnique_of_exists_of_unique ?_ ?_
  · by_contra hcon
    push Not at hcon
    have hg0 : ∀ x ∈ Icc a b, g x ≠ 0 := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · exact hgab x hx (h ▸ hfa)
      rcases eq_or_lt_of_le hx.2 with h' | h'
      · exact hgab x hx (h' ▸ hfb)
      exact hcon x ⟨h, h'⟩
    obtain ⟨c, hc, hc0⟩ := exists_wr_eq_zero_of_ratio hf hg hab hfa hfb hg0
    exact hW c (Ioo_subset_Icc_self hc) hc0
  · rintro c1 c2 ⟨h1, hg1⟩ ⟨h2, hg2⟩
    rcases lt_trichotomy c1 c2 with h | h | h
    · exact (hno c1 c2 h1.1 h h2.2 hg1 hg2).elim
    · exact h
    · exact (hno c2 c1 h2.1 h h1.2 hg2 hg1).elim

namespace IsSol

/-- **Sturm separation theorem.**  Let `y`, `w` be solutions of `y'' = q y` with nonzero
Wronskian (linearly independent), and `x₁ < x₂` consecutive zeros of `y`.  Then `w` has exactly one
zero in `(x₁, x₂)`.  (Applied with the roles exchanged: between consecutive zeros of `w` lies
exactly one zero of `y`; so the zeros of `y` and `w` interlace strictly.) -/
theorem sturm_separation (h1 : IsSol q y y') (h2 : IsSol q w w') {t : ℝ}
    (hW : wr y y' w w' t ≠ 0) {x₁ x₂ : ℝ} (h12 : x₁ < x₂) (hz1 : y x₁ = 0) (hz2 : y x₂ = 0)
    (hno : ∀ x ∈ Ioo x₁ x₂, y x ≠ 0) : ∃! c, c ∈ Ioo x₁ x₂ ∧ w c = 0 := by
  refine exists_unique_zero_of_sep h1.hasDerivAt h2.hasDerivAt h12 hz1 hz2 hno ?_
  intro x _ hx
  apply hW
  rw [wr_eq h1 h2 t x]
  unfold wr
  linarith

/-- Between any two zeros of `y` there is a zero of every linearly independent solution `w`. -/
theorem exists_zero_of_wr_ne_zero (h1 : IsSol q y y') (h2 : IsSol q w w') {t : ℝ}
    (hW : wr y y' w w' t ≠ 0) {x₁ x₂ : ℝ} (h12 : x₁ < x₂) (hz1 : y x₁ = 0) (hz2 : y x₂ = 0) :
    ∃ c ∈ Ioo x₁ x₂, w c = 0 := by
  by_contra hcon
  push Not at hcon
  have hg0 : ∀ x ∈ Icc x₁ x₂, w x ≠ 0 := by
    intro x hx hwx
    rcases eq_or_lt_of_le hx.1 with h | h
    · rw [← h] at hwx
      exact hW ((wr_eq h1 h2 t x₁).trans (by simp [wr, hz1, hwx]))
    rcases eq_or_lt_of_le hx.2 with h' | h'
    · rw [h'] at hwx
      exact hW ((wr_eq h1 h2 t x₂).trans (by simp [wr, hz2, hwx]))
    exact hcon x ⟨h, h'⟩ hwx
  obtain ⟨c, hc, hc0⟩ := exists_wr_eq_zero_of_ratio h1.hasDerivAt h2.hasDerivAt h12 hz1 hz2 hg0
  apply hW
  rw [wr_eq h1 h2 t c]
  unfold wr
  linarith

/-! ### Ratio and Riccati equation -/

/-- `(w / y)' = wr / y²` where `y ≠ 0`. -/
theorem hasDerivAt_div (h1 : IsSol q y y') (h2 : IsSol q w w') {x : ℝ} (hx : y x ≠ 0) :
    HasDerivAt (fun t => w t / y t) (wr y y' w w' x / y x ^ 2) x := by
  have := (h2.hasDerivAt x).div (h1.hasDerivAt x) hx
  convert this using 1
  unfold wr
  ring

/-- **Real Riccati equation.**  Where `y ≠ 0`, `u = y'/y` satisfies `u' = q - u²`. -/
theorem hasDerivAt_logDeriv (h : IsSol q y y') {x : ℝ} (hx : y x ≠ 0) :
    HasDerivAt (fun t => y' t / y t) (q x - (y' x / y x) ^ 2) x := by
  have := (h.hasDerivAt' x).div (h.hasDerivAt x) hx
  convert this using 1
  field_simp

end IsSol

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.eq_zero_of_zero_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.eq_zero_of_zero_data

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.deriv_ne_zero_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.deriv_ne_zero_of_zero

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.finite_zeros_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.finite_zeros_Icc

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.eq_smul_of_wr_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.eq_smul_of_wr_eq_zero

/-- info: 'FormalResearch.Special.SturmAiry.exists_unique_zero_of_sep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.exists_unique_zero_of_sep

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.sturm_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.sturm_separation

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.exists_zero_of_wr_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.exists_zero_of_wr_ne_zero

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.hasDerivAt_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.hasDerivAt_logDeriv

/-- info: 'FormalResearch.Special.SturmAiry.IsSol.wr_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsSol.wr_eq

end FormalResearch.Special.SturmAiry

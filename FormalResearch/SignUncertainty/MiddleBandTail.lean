module

public import FormalResearch.SignUncertainty.MiddleBandPointwise

/-!
# Two integrations by parts on a half-line `[α, ∞)` (`GT.2a`, more 3)

The outer reference piece has amplitude with `|a^{(r)}(x)| ≤ B x^{-5/2-r}` for `x ≥ α`, zero for
`x < α`, and cubic phase `ψ(x) = a0 x - π² x³/36` with `|ψ'| ≥ q x²`. `cubic_two_ibp_power` needs
the amplitude compactly supported, so the half-line statement is obtained by truncation.

* `cubic_two_ibp_power_tail`: `∃ K ≥ 0, ∀ a a0 α B q, hypotheses → ‖∫ a e^{iψ}‖ ≤ (1 + K) · (2/15) α^{-15/2} B C`
  with `C = 1/q² + π²/(2q³) + π²/(6q³) + π⁴/(12q⁴)`. The quantifier order matters: `K` (built from a fixed
  smooth bump, `K = 4K₁ + 4K₂`) is chosen before `a, a0, α, B, q`, so it is an absolute constant. The sharp
  constant `K = 0` of `cubic_two_ibp_power` is not claimed. Classes: proved. GT.2a needs only a constant
  independent of the parameters `ε, S, κ₀`, which this gives.
* `cubic_two_ibp_power_tail_neg`: the mirror statement on `(-∞, -α]` (same `K`), by `x ↦ -x` and complex
  conjugation. Classes: proved.
* Truncation: `a_R(x) = θ(x/R) a(x)` with a fixed bump `θ` (`θ = 1` on `[0, 1]`, `θ = 0` on `[2, ∞)`).
  On `[α, 2R]`, `|a_R^{(r)}| ≤ (1 + K) B x^{-5/2-r}` (the Leibniz terms carry `θ'(x/R)/R ≤ 2K₁/x`,
  `θ''(x/R)/R² ≤ 4K₂/x²`). `cubic_two_ibp_power` gives the bound for `a_R`, and dominated convergence
  (dominating function `B x^{-5/2} 1_{[α,∞)}`) gives `∫ a_R e^{iψ} → ∫ a e^{iψ}` as `R → ∞`.

Mathlib ingredients (not restated results): `ContDiffBump`, `Continuous.bounded_above_of_compact_support`,
`tendsto_integral_filter_of_dominated_convergence`, and the product rule `HasDerivAt.mul`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### Derivatives of a real function times a complex function -/

/-- Product rule for `(g : ℂ) · a` with `g` real. Classes: proved (`HasDerivAt.mul`). -/
lemma mbt_hasDerivAt_mul {g : ℝ → ℝ} {a : ℝ → ℂ} (hg : Differentiable ℝ g)
    (ha : Differentiable ℝ a) (x : ℝ) :
    HasDerivAt (fun y => (g y : ℂ) * a y) (((deriv g x : ℝ) : ℂ) * a x + (g x : ℂ) * deriv a x) x :=
  (hg x).hasDerivAt.ofReal_comp.mul (ha x).hasDerivAt

/-- Second derivative of `(g : ℂ) · a`, with `g, a` of class `C²`. Classes: proved. -/
lemma mbt_deriv2_mul {g : ℝ → ℝ} {a : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (ha : ContDiff ℝ 2 a) (x : ℝ) :
    deriv (deriv (fun y => (g y : ℂ) * a y)) x =
      ((deriv (deriv g) x : ℝ) : ℂ) * a x + 2 * ((deriv g x : ℝ) : ℂ) * deriv a x + (g x : ℂ) * deriv (deriv a) x := by
  have hgD : Differentiable ℝ g := hg.differentiable (by norm_num)
  have haD : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hdgC : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hdaC : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdgD : Differentiable ℝ (deriv g) := hdgC.differentiable (by norm_num)
  have hdaD : Differentiable ℝ (deriv a) := hdaC.differentiable (by norm_num)
  have hfun : deriv (fun y => (g y : ℂ) * a y) =
      fun y => ((deriv g y : ℝ) : ℂ) * a y + (g y : ℂ) * deriv a y :=
    funext fun y => (mbt_hasDerivAt_mul hgD haD y).deriv
  rw [hfun]
  have hA := mbt_hasDerivAt_mul hdgD haD x
  have hB := mbt_hasDerivAt_mul hgD hdaD x
  refine (hA.add hB).deriv.trans ?_
  ring

/-- Chain rule for a dilation: `d/dy f(y/R) = f'(y/R) / R`. Classes: proved. -/
lemma mbt_hasDerivAt_scale {f : ℝ → ℝ} (hf : Differentiable ℝ f) (R x : ℝ) :
    HasDerivAt (fun y => f (y / R)) (deriv f (x / R) * (1 / R)) x := by
  have h1 : HasDerivAt (fun y : ℝ => y / R) (1 / R) x := (hasDerivAt_id' x).div_const R
  exact (hf (x / R)).hasDerivAt.comp x h1

/-! ### Norm bounds for the three terms -/

/-- Triangle inequality for `c A + t B'` with real `c, t`. Classes: proved. -/
lemma mbt_norm_two {c t : ℝ} {A B' : ℂ} :
    ‖(c : ℂ) * A + (t : ℂ) * B'‖ ≤ |c| * ‖A‖ + |t| * ‖B'‖ := by
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]

/-- Triangle inequality for `c₂ A + 2 c₁ A₁ + t A₂` with real `c₂, c₁, t`. Classes: proved. -/
lemma mbt_norm_three {c1 c2 t : ℝ} {A A1 A2 : ℂ} :
    ‖(c2 : ℂ) * A + 2 * (c1 : ℂ) * A1 + (t : ℂ) * A2‖ ≤
      |c2| * ‖A‖ + 2 * |c1| * ‖A1‖ + |t| * ‖A2‖ := by
  have h1 := norm_add_le ((c2 : ℂ) * A + 2 * (c1 : ℂ) * A1) ((t : ℂ) * A2)
  have h2 := norm_add_le ((c2 : ℂ) * A) (2 * (c1 : ℂ) * A1)
  have e1 : ‖(c2 : ℂ) * A‖ = |c2| * ‖A‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have e2 : ‖2 * (c1 : ℂ) * A1‖ = 2 * |c1| * ‖A1‖ := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_two]
  have e3 : ‖(t : ℂ) * A2‖ = |t| * ‖A2‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  linarith

/-! ### The fixed bump -/

/-- A fixed smooth cutoff: `θ : ℝ → [0,1]` of class `C³`, `θ = 1` on `[0, 1]`, `θ = 0` on `[2, ∞)`,
compact support, and absolute bounds `K₁, K₂` on `|θ'|, |θ''|`. Classes: proved (from `ContDiffBump`
and boundedness of continuous compactly supported functions). -/
lemma mbt_bump_exists : ∃ th : ℝ → ℝ, ContDiff ℝ 3 th ∧ Continuous th ∧
    (∀ t, 0 ≤ th t ∧ th t ≤ 1) ∧ (∀ t, 0 ≤ t → t ≤ 1 → th t = 1) ∧ (∀ t, 2 ≤ t → th t = 0) ∧
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ (∀ t, |deriv th t| ≤ K1) ∧ (∀ t, |deriv (deriv th) t| ≤ K2) := by
  let bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hc3 : ContDiff ℝ 3 bump := bump.contDiff
  have hcs : HasCompactSupport bump := bump.hasCompactSupport
  have hc2' : ContDiff ℝ (2 + 1) bump := hc3
  have hd1 : ContDiff ℝ 2 (deriv bump) := hc2'.deriv'
  have hd1c : Continuous (deriv bump) := hd1.continuous
  have hd2 : ContDiff ℝ 1 (deriv (deriv bump)) := hd1.deriv'
  have hd2c : Continuous (deriv (deriv bump)) := hd2.continuous
  obtain ⟨K1, hK1⟩ := hd1c.bounded_above_of_compact_support hcs.deriv
  obtain ⟨K2, hK2⟩ := hd2c.bounded_above_of_compact_support hcs.deriv.deriv
  have hK1n : 0 ≤ K1 := le_trans (norm_nonneg _) (hK1 0)
  have hK2n : 0 ≤ K2 := le_trans (norm_nonneg _) (hK2 0)
  refine ⟨bump, hc3, bump.continuous, fun t => ⟨bump.nonneg, bump.le_one⟩, ?_, ?_, K1, K2,
    hK1n, hK2n, fun t => ?_, fun t => ?_⟩
  · intro t h0 h1
    exact bump.one_of_mem_closedBall (by
      rw [Metric.mem_closedBall, Real.dist_0_eq_abs, abs_of_nonneg h0]
      exact h1)
  · intro t h2
    exact bump.zero_of_le_dist (by
      rw [Real.dist_0_eq_abs, abs_of_nonneg (by linarith)]
      exact h2)
  · rw [← Real.norm_eq_abs]; exact hK1 t
  · rw [← Real.norm_eq_abs]; exact hK2 t

/-! ### Bounds for the truncated amplitude -/

/-- Power identities: `x^{-7/2} = x^{-5/2} x⁻¹` and `x^{-9/2} = x^{-5/2} x⁻¹ x⁻¹` for `x > 0`.
Classes: proved. -/
lemma mbt_rpow_shift {x : ℝ} (hx : 0 < x) :
    x ^ (-(7 / 2 : ℝ)) = x ^ (-(5 / 2 : ℝ)) * x⁻¹ ∧
      x ^ (-(9 / 2 : ℝ)) = x ^ (-(5 / 2 : ℝ)) * x⁻¹ * x⁻¹ := by
  constructor
  · rw [show (-(7 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-1) by norm_num, Real.rpow_add hx, Real.rpow_neg_one]
  · rw [show (-(9 / 2 : ℝ)) = -(5 / 2 : ℝ) + (-1) + (-1) by norm_num, Real.rpow_add hx,
      Real.rpow_add hx, Real.rpow_neg_one]

/-- Derivative bounds for the truncated amplitude `θ(·/R) a` on `[α, 2R]`. Classes: proved. -/
lemma mbt_cutoff_bounds {a : ℝ → ℂ} {th : ℝ → ℝ} {α B K1 K2 R : ℝ} (hth : ContDiff ℝ 3 th)
    (hth01 : ∀ t, 0 ≤ th t ∧ th t ≤ 1) (hK1 : ∀ t, |deriv th t| ≤ K1)
    (hK2 : ∀ t, |deriv (deriv th) t| ≤ K2) (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2)
    (ha : ContDiff ℝ 2 a) (hα : 0 < α) (hB : 0 ≤ B) (hR : 0 < R)
    (hb0 : ∀ x, α ≤ x → ‖a x‖ ≤ B * x ^ (-(5 / 2 : ℝ)))
    (hb1 : ∀ x, α ≤ x → ‖deriv a x‖ ≤ B * x ^ (-(7 / 2 : ℝ)))
    (hb2 : ∀ x, α ≤ x → ‖deriv (deriv a) x‖ ≤ B * x ^ (-(9 / 2 : ℝ)))
    (x : ℝ) (hx : α ≤ x) (hxR : x ≤ 2 * R) :
    ‖deriv (fun y => (th (y / R) : ℂ) * a y) x‖ ≤ (1 + 2 * K1) * B * x ^ (-(7 / 2 : ℝ)) ∧
      ‖deriv (deriv (fun y => (th (y / R) : ℂ) * a y)) x‖ ≤
        (1 + 4 * K1 + 4 * K2) * B * x ^ (-(9 / 2 : ℝ)) := by
  have hx0 : 0 < x := lt_of_lt_of_le hα hx
  have hthD : Differentiable ℝ th := hth.differentiable (by norm_num)
  have hth' : ContDiff ℝ (2 + 1) th := hth
  have hdthC : ContDiff ℝ 2 (deriv th) := hth'.deriv'
  have hdthD : Differentiable ℝ (deriv th) := hdthC.differentiable (by norm_num)
  have hg2 : ContDiff ℝ 2 (fun y => th (y / R)) :=
    (hth.of_le (by norm_num)).comp (by fun_prop : ContDiff ℝ 2 (fun y : ℝ => y / R))
  have hgD : Differentiable ℝ (fun y => th (y / R)) := hg2.differentiable (by norm_num)
  have haD : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hgx : ∀ y, deriv (fun y => th (y / R)) y = deriv th (y / R) * (1 / R) :=
    fun y => (mbt_hasDerivAt_scale hthD R y).deriv
  have hdg : deriv (fun y => th (y / R)) = fun y => deriv th (y / R) * (1 / R) := funext hgx
  have hdg2 : ∀ y, deriv (deriv (fun y => th (y / R))) y =
      deriv (deriv th) (y / R) * (1 / R) * (1 / R) := by
    intro y
    rw [hdg]
    exact ((mbt_hasDerivAt_scale hdthD R y).mul_const (1 / R)).deriv
  -- the two derivatives of the truncated amplitude
  have e1 : deriv (fun y => (th (y / R) : ℂ) * a y) x =
      ((deriv th (x / R) * (1 / R) : ℝ) : ℂ) * a x + (th (x / R) : ℂ) * deriv a x := by
    rw [(mbt_hasDerivAt_mul hgD haD x).deriv, hgx x]
  have e2 : deriv (deriv (fun y => (th (y / R) : ℂ) * a y)) x =
      ((deriv (deriv th) (x / R) * (1 / R) * (1 / R) : ℝ) : ℂ) * a x
        + 2 * ((deriv th (x / R) * (1 / R) : ℝ) : ℂ) * deriv a x
        + (th (x / R) : ℂ) * deriv (deriv a) x := by
    rw [mbt_deriv2_mul hg2 ha x, hgx x, hdg2 x]
  -- size of `1/R` and `1/R²` on `[α, 2R]`
  have hu : 1 / R ≤ 2 * x⁻¹ := by
    have h : 2 * x⁻¹ = 2 / x := by ring
    rw [h, div_le_div_iff₀ hR hx0]
    linarith
  have hR1 : 0 ≤ 1 / R := (one_div_pos.2 hR).le
  obtain ⟨hP1, hP2⟩ := mbt_rpow_shift hx0
  have hu0 : 0 ≤ x⁻¹ := inv_nonneg.2 hx0.le
  have hP : 0 ≤ x ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hth_x := hth01 (x / R)
  have ht1 : |th (x / R)| ≤ 1 := by rw [abs_of_nonneg hth_x.1]; exact hth_x.2
  have hc1 : |deriv th (x / R) * (1 / R)| ≤ K1 * (2 * x⁻¹) := by
    rw [abs_mul, abs_of_nonneg hR1]
    exact mul_le_mul (hK1 _) hu hR1 hK1n
  have hc2 : |deriv (deriv th) (x / R) * (1 / R) * (1 / R)| ≤ K2 * (2 * x⁻¹) * (2 * x⁻¹) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hR1]
    exact mul_le_mul (mul_le_mul (hK2 _) hu hR1 hK2n) hu hR1
      (mul_nonneg hK2n (mul_nonneg (by norm_num) hu0))
  constructor
  · rw [e1]
    refine (mbt_norm_two).trans ?_
    have hA := hb0 x hx
    have hA1 := hb1 x hx
    have t1 : |deriv th (x / R) * (1 / R)| * ‖a x‖ ≤ (K1 * (2 * x⁻¹)) * (B * x ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul hc1 hA (norm_nonneg _) (mul_nonneg hK1n (mul_nonneg (by norm_num) hu0))
    have t2 : |th (x / R)| * ‖deriv a x‖ ≤ 1 * (B * x ^ (-(7 / 2 : ℝ))) :=
      mul_le_mul ht1 hA1 (norm_nonneg _) zero_le_one
    have hK : (1 + 2 * K1) * B * x ^ (-(7 / 2 : ℝ)) ≤ (1 + 4 * K1 + 4 * K2) * B * x ^ (-(7 / 2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
      exact mul_le_mul_of_nonneg_right (by linarith) hB
    have hsum : (K1 * (2 * x⁻¹)) * (B * x ^ (-(5 / 2 : ℝ))) + 1 * (B * x ^ (-(7 / 2 : ℝ)))
        = (1 + 2 * K1) * B * x ^ (-(7 / 2 : ℝ)) := by
      rw [hP1]; ring
    linarith
  · rw [e2]
    refine (mbt_norm_three).trans ?_
    have hA := hb0 x hx
    have hA1 := hb1 x hx
    have hA2 := hb2 x hx
    have t1 : |deriv (deriv th) (x / R) * (1 / R) * (1 / R)| * ‖a x‖ ≤
        (K2 * (2 * x⁻¹) * (2 * x⁻¹)) * (B * x ^ (-(5 / 2 : ℝ))) :=
      mul_le_mul hc2 hA (norm_nonneg _) (mul_nonneg (mul_nonneg hK2n (mul_nonneg (by norm_num) hu0))
        (mul_nonneg (by norm_num) hu0))
    have t2 : 2 * |deriv th (x / R) * (1 / R)| * ‖deriv a x‖ ≤
        2 * (K1 * (2 * x⁻¹)) * (B * (x ^ (-(5 / 2 : ℝ)) * x⁻¹)) := by
      apply mul_le_mul (by linarith [hc1]) (by rw [hP1] at hA1; exact hA1) (norm_nonneg _)
      exact mul_nonneg (by norm_num) (mul_nonneg hK1n (mul_nonneg (by norm_num) hu0))
    have t3 : |th (x / R)| * ‖deriv (deriv a) x‖ ≤ 1 * (B * (x ^ (-(5 / 2 : ℝ)) * x⁻¹ * x⁻¹)) := by
      rw [← hP2]
      exact mul_le_mul ht1 hA2 (norm_nonneg _) zero_le_one
    have hK : (1 + 4 * K1 + 4 * K2) * B * x ^ (-(9 / 2 : ℝ)) =
        (K2 * (2 * x⁻¹) * (2 * x⁻¹)) * (B * x ^ (-(5 / 2 : ℝ)))
          + 2 * (K1 * (2 * x⁻¹)) * (B * (x ^ (-(5 / 2 : ℝ)) * x⁻¹))
          + 1 * (B * (x ^ (-(5 / 2 : ℝ)) * x⁻¹ * x⁻¹)) := by
      rw [hP2]; ring
    linarith

/-! ### The half-line bound -/

/-- Two integrations by parts on `[α, ∞)` (`GT.2a`, outer reference piece). There is an absolute
constant `K ≥ 0` (it depends on nothing but the fixed bump, and is chosen *before* `a, a0, α, B, q`,
as the quantifier order records) such that for every amplitude `a ∈ C²` vanishing on `(-∞, α)` with
`|a^{(r)}(x)| ≤ B x^{-5/2-r}` (`r = 0, 1, 2`) and every `q > 0` with `|ψ'(x)| ≥ q x²` on `[α, ∞)`,
`ψ(x) = a0 x - π² x³/36`:
`‖∫ a e^{iψ}‖ ≤ (1 + K) · (2/15) α^{-15/2} B (1/q² + π²/(2q³) + π²/(6q³) + π⁴/(12q⁴))`.
The sharp constant (`K = 0`) of `cubic_two_ibp_power` is not claimed; the factor `1 + K` comes from the
Leibniz terms of the truncation. Classes: proved (truncation and dominated convergence; `K = 4K₁ + 4K₂`
for the first two derivative bounds of the fixed `ContDiffBump`, not made numerically explicit). -/
theorem cubic_two_ibp_power_tail : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a : ℝ → ℂ) (a0 α B q : ℝ), 0 < α → 0 ≤ B → 0 < q → ContDiff ℝ 2 a →
    (∀ x, x < α → a x = 0) →
    (∀ x ≥ α, ‖a x‖ ≤ B * x ^ (-(5 / 2 : ℝ))) →
    (∀ x ≥ α, ‖deriv a x‖ ≤ B * x ^ (-(7 / 2 : ℝ))) →
    (∀ x ≥ α, ‖deriv (deriv a) x‖ ≤ B * x ^ (-(9 / 2 : ℝ))) →
    (∀ x ≥ α, q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|) →
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      (1 + K) * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4))) := by
  obtain ⟨th, hth, hthc, hth01, hth1, hth0, K1, K2, hK1n, hK2n, hK1, hK2⟩ := mbt_bump_exists
  refine ⟨4 * K1 + 4 * K2, by linarith, ?_⟩
  intro a a0 α B q hα hB hq ha hsupp hb0 hb1 hb2 hp
  -- the amplitude bound for each truncation, with the constant `(1 + 4K₁ + 4K₂) B`
  have hbound : ∀ R : ℝ, α ≤ R →
      ‖∫ x, (th (x / R) : ℂ) * a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖
        ≤ (2 / 15) * α ^ (-(15 / 2 : ℝ)) * ((1 + 4 * K1 + 4 * K2) * B) * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
          + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le hα hR
    have hthR : ContDiff ℝ 2 (fun y => th (y / R)) :=
      (hth.of_le (by norm_num)).comp (by fun_prop : ContDiff ℝ 2 (fun y : ℝ => y / R))
    have hAR : ContDiff ℝ 2 (fun x => (th (x / R) : ℂ) * a x) :=
      (Complex.ofRealCLM.contDiff.comp hthR).mul ha
    have hsuppR : ∀ x, x ∉ Set.Icc α (2 * R) → (th (x / R) : ℂ) * a x = 0 := by
      intro x hx
      by_cases h1 : x < α
      · simp [hsupp x h1]
      · have h2 : 2 * R < x := lt_of_not_ge fun hc => hx ⟨not_lt.1 h1, hc⟩
        have h3 : 2 ≤ x / R := (le_div_iff₀ hRpos).2 (by linarith)
        simp [hth0 _ h3]
    have hB'0 : 0 ≤ (1 + 4 * K1 + 4 * K2) * B :=
      mul_nonneg (by linarith) hB
    have hBle : B ≤ (1 + 4 * K1 + 4 * K2) * B := le_mul_of_one_le_left hB (by linarith)
    have hA0 : ∀ x ∈ Set.Icc α (2 * R),
        ‖(th (x / R) : ℂ) * a x‖ ≤ (1 + 4 * K1 + 4 * K2) * B * x ^ (-(5 / 2 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
      have hth_n : ‖(th (x / R) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hth01 _).1]
        exact (hth01 _).2
      rw [norm_mul]
      have h1 : ‖(th (x / R) : ℂ)‖ * ‖a x‖ ≤ ‖a x‖ := mul_le_of_le_one_left (norm_nonneg _) hth_n
      have h2 : B * x ^ (-(5 / 2 : ℝ)) ≤ (1 + 4 * K1 + 4 * K2) * B * x ^ (-(5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right hBle (Real.rpow_nonneg hx0.le _)
      linarith [hb0 x hx.1]
    have hA1 : ∀ x ∈ Set.Icc α (2 * R),
        ‖deriv (fun y => (th (y / R) : ℂ) * a y) x‖ ≤
          (1 + 4 * K1 + 4 * K2) * B * x ^ (-(7 / 2 : ℝ)) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
      refine (mbt_cutoff_bounds hth hth01 hK1 hK2 hK1n hK2n ha hα hB hRpos hb0 hb1 hb2 x hx.1 hx.2).1.trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
      exact mul_le_mul_of_nonneg_right (by linarith) hB
    have hA2 : ∀ x ∈ Set.Icc α (2 * R),
        ‖deriv (deriv (fun y => (th (y / R) : ℂ) * a y)) x‖ ≤
          (1 + 4 * K1 + 4 * K2) * B * x ^ (-(9 / 2 : ℝ)) := fun x hx =>
      (mbt_cutoff_bounds hth hth01 hK1 hK2 hK1n hK2n ha hα hB hRpos hb0 hb1 hb2 x hx.1 hx.2).2
    have hbR := cubic_two_ibp_power (a := fun x => (th (x / R) : ℂ) * a x) (a0 := a0) (α := α)
      (β := 2 * R) (B := (1 + 4 * K1 + 4 * K2) * B) (q := q) hα (by linarith) hB'0 hq hAR hsuppR
      hA0 hA1 hA2 (fun x hx => hp x hx.1)
    exact hbR
  -- dominated convergence: the truncations converge to `a e^{iψ}`
  have hlim : Filter.Tendsto (fun R : ℝ => ∫ x, (th (x / R) : ℂ) * a x *
      Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))) Filter.atTop
      (𝓝 (∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ)))) := by
    have hbI : IntegrableOn (fun y : ℝ => B * y ^ (-(5 / 2 : ℝ))) (Set.Ici α) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by norm_num) hα) B
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Set.indicator (Set.Ici α) (fun y => B * y ^ (-(5 / 2 : ℝ))) x) ?_ ?_
      (hbI.integrable_indicator measurableSet_Ici) ?_
    · refine Filter.Eventually.of_forall (fun R => ?_)
      have hθc : Continuous (fun x : ℝ => (th (x / R) : ℂ)) :=
        Complex.continuous_ofReal.comp (hthc.comp (continuous_id.div_const R))
      exact Continuous.aestronglyMeasurable ((hθc.mul ha.continuous).mul
        (Complex.continuous_exp.comp (continuous_const.mul
          (Complex.continuous_ofReal.comp (by fun_prop)))))
    · refine Filter.Eventually.of_forall (fun R => ae_of_all _ (fun x => ?_))
      by_cases hx : x < α
      · have h0 : a x = 0 := hsupp x hx
        have hxn : x ∉ Set.Ici α := fun h => absurd (Set.mem_Ici.1 h) (not_le.2 hx)
        simp [h0, hxn]
      · have hx' : α ≤ x := not_lt.1 hx
        have hthn : ‖(th (x / R) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hth01 _).1]
          exact (hth01 _).2
        rw [Set.indicator_of_mem (Set.mem_Ici.2 hx'), norm_mul, norm_mul,
          Complex.norm_exp_I_mul_ofReal, mul_one]
        exact (mul_le_of_le_one_left (norm_nonneg _) hthn).trans (hb0 x hx')
    · refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : x < α
      · have h0 : a x = 0 := hsupp x hx
        simp only [h0, zero_mul, mul_zero]
        exact tendsto_const_nhds
      · have hx' : α ≤ x := not_lt.1 hx
        have hpos : 0 < x := lt_of_lt_of_le hα hx'
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.eventually_ge_atTop x] with R hR
        have hRpos : 0 < R := lt_of_lt_of_le hpos hR
        have h1 : th (x / R) = 1 :=
          hth1 _ (div_nonneg hpos.le hRpos.le) ((div_le_one hRpos).2 hR)
        rw [h1]
        simp
  have hnorm := hlim.norm
  refine le_of_tendsto hnorm (Filter.eventually_atTop.2 ⟨α, fun R hR => ?_⟩)
  exact (hbound R hR).trans (le_of_eq (by ring))

/-! ### The mirror half-line `(-∞, -α]` -/

/-- Derivative of the reflected conjugate `y ↦ conj (f (-y))`. Classes: proved. -/
lemma mbt_deriv_reflect {f : ℝ → ℂ} (hf : Differentiable ℝ f) (y : ℝ) :
    deriv (fun y => star (f (-y))) y = -star (deriv f (-y)) := by
  have h1 : HasDerivAt (fun y : ℝ => f (-y)) (-deriv f (-y)) y := by
    have h0 : HasDerivAt (fun y : ℝ => f (-y)) ((-1 : ℝ) • deriv f (-y)) y :=
      (hf (-y)).hasDerivAt.scomp y (hasDerivAt_neg y)
    rwa [neg_smul, one_smul] at h0
  have h2 := h1.star
  rw [h2.deriv, star_neg]

/-- Mirror of `cubic_two_ibp_power_tail`: with the same absolute `K`, the bound holds for an amplitude
vanishing on `(-α, ∞)` with `|a^{(r)}(x)| ≤ B (-x)^{-5/2-r}` on `x ≤ -α` and `q x² ≤ |ψ'(x)|` there.
The reflection `x ↦ -x` sends `∫ a e^{iψ}` to the complex conjugate of `∫ b e^{iψ}` with
`b(y) = conj (a (-y))` (same `a0`). Classes: proved (from `cubic_two_ibp_power_tail`). -/
theorem cubic_two_ibp_power_tail_neg : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (a : ℝ → ℂ) (a0 α B q : ℝ), 0 < α → 0 ≤ B → 0 < q → ContDiff ℝ 2 a →
    (∀ x, -α < x → a x = 0) →
    (∀ x ≤ -α, ‖a x‖ ≤ B * (-x) ^ (-(5 / 2 : ℝ))) →
    (∀ x ≤ -α, ‖deriv a x‖ ≤ B * (-x) ^ (-(7 / 2 : ℝ))) →
    (∀ x ≤ -α, ‖deriv (deriv a) x‖ ≤ B * (-x) ^ (-(9 / 2 : ℝ))) →
    (∀ x ≤ -α, q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|) →
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      (1 + K) * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4))) := by
  obtain ⟨K, hK0, hK⟩ := cubic_two_ibp_power_tail
  refine ⟨K, hK0, ?_⟩
  intro a a0 α B q hα hB hq ha hsupp hb0 hb1 hb2 hp
  set b : ℝ → ℂ := fun y => star (a (-y)) with hb
  have haD : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hda : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdaD : Differentiable ℝ (deriv a) := hda.differentiable (by norm_num)
  have hbC : ContDiff ℝ 2 b :=
    (Complex.conjCLE.contDiff.comp (ha.comp contDiff_neg) : ContDiff ℝ 2 (fun y => Complex.conjCLE (a (-y))))
  have hd1 : ∀ y, deriv b y = -star (deriv a (-y)) := fun y => mbt_deriv_reflect haD y
  have hd1' : deriv b = fun y => -star (deriv a (-y)) := funext hd1
  have hd2 : ∀ y, deriv (deriv b) y = star (deriv (deriv a) (-y)) := by
    intro y
    rw [hd1']
    have := mbt_deriv_reflect hdaD y
    have h3 : deriv (fun y => -star (deriv a (-y))) y = -deriv (fun y => star (deriv a (-y))) y := by
      rw [deriv.fun_neg]
    rw [h3, this, neg_neg]
  have hmain := hK b a0 α B q hα hB hq hbC
    (fun x hx => by simp [hb, hsupp (-x) (by linarith)])
    (fun x hx => by
      have := hb0 (-x) (by linarith)
      simpa [hb, neg_neg] using this)
    (fun x hx => by
      have := hb1 (-x) (by linarith)
      rw [hd1]; simpa [norm_neg, neg_neg] using this)
    (fun x hx => by
      have := hb2 (-x) (by linarith)
      rw [hd2]; simpa [neg_neg] using this)
    (fun x hx => by
      have := hp (-x) (by linarith)
      simpa [neg_sq] using this)
  -- reflect the integral
  have hrefl : ∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ)) =
      star (∫ y, b y * Complex.exp (Complex.I * ((a0 * y - Real.pi ^ 2 / 36 * y ^ 3 : ℝ) : ℂ))) := by
    rw [← integral_neg_eq_self, RCLike.star_def, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hexp : Complex.exp (Complex.I * ((a0 * -y - Real.pi ^ 2 / 36 * (-y) ^ 3 : ℝ) : ℂ)) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * ((a0 * y - Real.pi ^ 2 / 36 * y ^ 3 : ℝ) : ℂ))) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1
      push_cast
      ring
    simp only [hb, RCLike.star_def, map_mul, Complex.conj_conj, hexp]
  rw [hrefl, norm_star]
  exact hmain

/-! `#print axioms` guards. -/

/-- info: 'FormalResearch.SignUncertainty.mbt_bump_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbt_bump_exists

/-- info: 'FormalResearch.SignUncertainty.mbt_cutoff_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbt_cutoff_bounds

/-- info: 'FormalResearch.SignUncertainty.mbt_deriv_reflect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbt_deriv_reflect

/-- info: 'FormalResearch.SignUncertainty.cubic_two_ibp_power_tail_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_two_ibp_power_tail_neg

/-- info: 'FormalResearch.SignUncertainty.cubic_two_ibp_power_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_two_ibp_power_tail

end FormalResearch.SignUncertainty

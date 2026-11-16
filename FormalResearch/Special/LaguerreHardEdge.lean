module

public import FormalResearch.Special.JacobiMehlerHeine
public import FormalResearch.Racah.P2ThreeJOperator

/-!
# The Laguerre recurrence behind the hard-edge factor (Weyl P2, `rem:Laguerre`)

Two exact statements, both elementary.

* `laguerre_recurrence`: the orthonormal Laguerre Jacobi recurrence at spectral parameter zero,
  `√(n(n+p)) Ξ_{n-1} + √((n+1)(n+p+1)) Ξ_{n+1} = (2n+p+1) Ξ_n`, has the solution
  `Ξ_n = √((n+1)_p) = √(Γ(n+p+1)/n!)` (`laguerreRegular`), including its `n = 0` row (the first coefficient
  vanishes), for every real `p > -1`; this solution is unique up to scale by the forward recurrence
  (positive coefficients), which is not formalised; for natural `p`
  this is `√` of the Pochhammer symbol (`laguerreRegular_nat`).
* `ah3_*_tendsto`: the leading part, as `h → 0⁺`, of the exact magnetic difference equation
  `eq:3jdiff` near the upper edge at the grid point `x = 1 - h (p+1+2n)`: with
  `a_h(y) = √([(1-y)²-h²p²][(1+y)²-h²q²])` (`eq:ah3`, `p = |M-σ|`, `q = |M+σ|`) the rescaled
  coefficients `a_h(x±h)/(4h)` and `2(1-x²)/(4h)` tend to `√(n(n+p))`, `√((n+1)(n+p+1))` and
  `2n+p+1`, the Laguerre coefficients (and the term `2h²[…]Φ`, which is `O(h)` after division by `4h`, drops).

Not formalised: the identification of `Φ(1 - h y) = h^{p/2} Ξ(y; h)` with the physical `3j` symbol,
the passage from the coefficient limits to the asymptotics of the solution, the `6j` (Racah
`c`-lattice) version, and the `[1 + O(N⁻²)]` edge ratio of `prop:LaguerreEdge` and
`thm:6jhardedge`.
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.Special

/-- The solution `Ξ_n = √((n+1)_p) = √(Γ(n+p+1)/Γ(n+1))` of the Laguerre recurrence (including its `n = 0` row). -/
noncomputable def laguerreRegular (p : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (Real.Gamma ((n : ℝ) + p + 1) / Real.Gamma ((n : ℝ) + 1))

/-- For natural `p`, `Ξ_n = √((n+1)_p)` with the Pochhammer symbol. -/
lemma laguerreRegular_nat (p n : ℕ) :
    laguerreRegular p n = Real.sqrt ((ascPochhammer ℝ p).eval ((n : ℝ) + 1)) := by
  unfold laguerreRegular
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have := gamma_add_nat_eq _ hn p
  rw [show (n : ℝ) + p + 1 = ((n : ℝ) + 1) + p by ring, this]
  congr 1
  have := Real.Gamma_pos_of_pos hn
  field_simp

lemma laguerreRegular_sq (p : ℝ) (hp : -1 < p) (n : ℕ) :
    laguerreRegular p n ^ 2 = Real.Gamma ((n : ℝ) + p + 1) / Real.Gamma ((n : ℝ) + 1) := by
  unfold laguerreRegular
  have h1 : 0 < Real.Gamma ((n : ℝ) + p + 1) :=
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  have h2 : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  exact Real.sq_sqrt (by positivity)

lemma laguerreRegular_pos (p : ℝ) (hp : -1 < p) (n : ℕ) : 0 < laguerreRegular p n := by
  unfold laguerreRegular
  have h1 : 0 < Real.Gamma ((n : ℝ) + p + 1) :=
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  have h2 : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  exact Real.sqrt_pos.2 (by positivity)

/-- Ratio of consecutive terms: `Ξ_{n+1}² = (n+p+1)/(n+1) · Ξ_n²`. -/
lemma laguerreRegular_succ_sq (p : ℝ) (hp : -1 < p) (n : ℕ) :
    laguerreRegular p (n + 1) ^ 2 = ((n : ℝ) + p + 1) / ((n : ℝ) + 1) * laguerreRegular p n ^ 2 := by
  rw [laguerreRegular_sq p hp, laguerreRegular_sq p hp]
  have h1 : 0 < Real.Gamma ((n : ℝ) + p + 1) :=
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith)
  have h2 : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp1 : (0 : ℝ) < (n : ℝ) + p + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  rw [show (((n + 1 : ℕ) : ℝ) + p + 1) = ((n : ℝ) + p + 1) + 1 by push_cast; ring,
    show (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 1) + 1 by push_cast; ring,
    Real.Gamma_add_one hp1.ne', Real.Gamma_add_one hn1.ne']
  field_simp

/-- **The Laguerre recurrence** (`rem:Laguerre`, `eq:Lagrec`): for every real `p > -1`,
`√(n(n+p)) Ξ_{n-1} + √((n+1)(n+p+1)) Ξ_{n+1} = (2n+p+1) Ξ_n` with `Ξ_n = √((n+1)_p)`; for `n = 0`
the first coefficient vanishes. -/
theorem laguerre_recurrence (p : ℝ) (hp : -1 < p) (n : ℕ) :
    Real.sqrt ((n : ℝ) * (n + p)) * laguerreRegular p (n - 1) +
      Real.sqrt (((n : ℝ) + 1) * (n + p + 1)) * laguerreRegular p (n + 1) =
        (2 * n + p + 1) * laguerreRegular p n := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hp1 : (0 : ℝ) < (n : ℝ) + p + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _; linarith
  set a := laguerreRegular p n with ha
  have ha0 : 0 < a := laguerreRegular_pos p hp n
  -- the upper neighbour
  have hup : Real.sqrt (((n : ℝ) + 1) * (n + p + 1)) * laguerreRegular p (n + 1) =
      ((n : ℝ) + p + 1) * a := by
    have h2 : laguerreRegular p (n + 1) =
        Real.sqrt (((n : ℝ) + p + 1) / ((n : ℝ) + 1)) * a := by
      rw [← Real.sqrt_sq (laguerreRegular_pos p hp (n + 1)).le,
        laguerreRegular_succ_sq p hp, Real.sqrt_mul (div_nonneg hp1.le hn1.le), Real.sqrt_sq ha0.le]
    rw [h2, ← mul_assoc, ← Real.sqrt_mul (by positivity)]
    have : ((n : ℝ) + 1) * ((n : ℝ) + p + 1) * (((n : ℝ) + p + 1) / ((n : ℝ) + 1)) =
        ((n : ℝ) + p + 1) ^ 2 := by field_simp
    rw [show ((n : ℝ) + 1) * ((n : ℝ) + p + 1) = ((n : ℝ) + 1) * ((n : ℝ) + p + 1) from rfl, this,
      Real.sqrt_sq hp1.le]
  rcases n with _ | m
  · simp only [Nat.cast_zero, zero_mul, Real.sqrt_zero, zero_add, mul_zero] at hup ⊢
    simpa using hup
  · -- the lower neighbour: `Ξ_m² = (m+1)/(m+1+p) Ξ_{m+1}²`
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hmp : (0 : ℝ) < (m : ℝ) + p + 1 := by
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg _; linarith
    have h3 := laguerreRegular_succ_sq p hp m
    have h4 : laguerreRegular p m =
        Real.sqrt (((m : ℝ) + 1) / ((m : ℝ) + p + 1)) * a := by
      rw [← Real.sqrt_sq (laguerreRegular_pos p hp m).le]
      have : laguerreRegular p m ^ 2 = ((m : ℝ) + 1) / ((m : ℝ) + p + 1) * a ^ 2 := by
        rw [ha, h3]; field_simp
      rw [this, Real.sqrt_mul (div_nonneg hm.le hmp.le), Real.sqrt_sq ha0.le]
    have hlow : Real.sqrt (((m + 1 : ℕ) : ℝ) * ((m + 1 : ℕ) + p)) * laguerreRegular p (m + 1 - 1) =
        ((m + 1 : ℕ) : ℝ) * a := by
      rw [Nat.add_sub_cancel, h4]
      push_cast
      rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg hm.le (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1 + p))]
      have : (((m : ℝ) + 1) * ((m : ℝ) + 1 + p)) * (((m : ℝ) + 1) / ((m : ℝ) + p + 1)) =
          ((m : ℝ) + 1) ^ 2 := by field_simp; ring
      rw [this, Real.sqrt_sq hm.le]
    rw [hlow, hup]
    push_cast
    ring

/-! ### The leading part of the magnetic difference equation near the edge -/

/-- `a_h(y) = √([(1-y)² - h²p²][(1+y)² - h²q²])`, `eq:ah3` of Weyl P2 with `p = |M-σ|`, `q = |M+σ|`
(only the squares `(σ∓M)²` enter). -/
noncomputable def ah3 (p q h y : ℝ) : ℝ :=
  Real.sqrt (((1 - y) ^ 2 - h ^ 2 * p ^ 2) * ((1 + y) ^ 2 - h ^ 2 * q ^ 2))

/-- `ah3` is the `aH` of `FormalResearch.Racah` (the coefficient of the exact difference equation
`eq:3jdiff`, `Dop`) for `p = |M-σ|`, `q = |M+σ|`. -/
theorem ah3_eq_aH (M σ h y : ℝ) :
    ah3 |M - σ| |M + σ| h y = FormalResearch.Racah.aH M σ h y := by
  unfold ah3 FormalResearch.Racah.aH
  rw [sq_abs, sq_abs]
  congr 2 <;> ring

/-- The `n`-th grid point from the upper edge, `x = 1 - h (p + 1 + 2n)`. -/
def edgePoint (p h : ℝ) (n : ℕ) : ℝ := 1 - h * (p + 1 + 2 * n)

/-- Coefficient of `Ξ_{n-1}` (the neighbour `x_n + h`): `a_h(x_n + h)/(4h) → √(n(n+p))` as `h → 0⁺`. -/
theorem ah3_upper_tendsto (p q : ℝ) (n : ℕ) :
    Tendsto (fun h : ℝ => ah3 p q h (edgePoint p h n + h) / (4 * h)) (𝓝[>] 0)
      (𝓝 (Real.sqrt ((n : ℝ) * (n + p)))) := by
  have hc : Continuous fun h : ℝ => Real.sqrt ((n : ℝ) * (n + p) *
      ((2 - h * (p + 2 * n)) ^ 2 - h ^ 2 * q ^ 2)) / 2 := by fun_prop
  have h0 := hc.tendsto 0
  have e : Real.sqrt ((n : ℝ) * (n + p) * ((2 - 0 * (p + 2 * n)) ^ 2 - 0 ^ 2 * q ^ 2)) / 2 =
      Real.sqrt ((n : ℝ) * (n + p)) := by
    have : (n : ℝ) * (n + p) * ((2 - 0 * (p + 2 * n)) ^ 2 - 0 ^ 2 * q ^ 2) =
        ((n : ℝ) * (n + p)) * 2 ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  rw [e] at h0
  refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh : 0 < h := hh
  unfold ah3 edgePoint
  have : ((1 - (1 - h * (p + 1 + 2 * n) + h)) ^ 2 - h ^ 2 * p ^ 2) *
      ((1 + (1 - h * (p + 1 + 2 * n) + h)) ^ 2 - h ^ 2 * q ^ 2) =
      h ^ 2 * (4 * ((n : ℝ) * (n + p) * ((2 - h * (p + 2 * n)) ^ 2 - h ^ 2 * q ^ 2))) := by
    ring
  rw [this]
  generalize (n : ℝ) * (n + p) * ((2 - h * (p + 2 * n)) ^ 2 - h ^ 2 * q ^ 2) = Y
  have k1 : Real.sqrt (h ^ 2 * (4 * Y)) = h * (2 * Real.sqrt Y) := by
    rw [Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [k1]
  field_simp
  ring

/-- Coefficient of `Ξ_{n+1}` (the neighbour `x_n - h`): `a_h(x_n - h)/(4h) → √((n+1)(n+p+1))` as `h → 0⁺` (`p ≥ -1`). -/
theorem ah3_lower_tendsto (p q : ℝ) (hp : -1 ≤ p) (n : ℕ) :
    Tendsto (fun h : ℝ => ah3 p q h (edgePoint p h n - h) / (4 * h)) (𝓝[>] 0)
      (𝓝 (Real.sqrt (((n : ℝ) + 1) * (n + p + 1)))) := by
  have hc : Continuous fun h : ℝ => Real.sqrt (((n : ℝ) + 1) * (n + p + 1) *
      ((2 - h * (p + 2 * n + 2)) ^ 2 - h ^ 2 * q ^ 2)) / 2 := by fun_prop
  have h0 := hc.tendsto 0
  have hnn : (0 : ℝ) ≤ ((n : ℝ) + 1) * (n + p + 1) := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    exact mul_nonneg (by linarith) (by linarith)
  have e : Real.sqrt (((n : ℝ) + 1) * (n + p + 1) *
      ((2 - 0 * (p + 2 * n + 2)) ^ 2 - 0 ^ 2 * q ^ 2)) / 2 =
      Real.sqrt (((n : ℝ) + 1) * (n + p + 1)) := by
    have : ((n : ℝ) + 1) * (n + p + 1) * ((2 - 0 * (p + 2 * n + 2)) ^ 2 - 0 ^ 2 * q ^ 2) =
        (((n : ℝ) + 1) * (n + p + 1)) * 2 ^ 2 := by ring
    rw [this, Real.sqrt_mul hnn, Real.sqrt_sq (by norm_num)]
    ring
  rw [e] at h0
  refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh : 0 < h := hh
  unfold ah3 edgePoint
  have : ((1 - (1 - h * (p + 1 + 2 * n) - h)) ^ 2 - h ^ 2 * p ^ 2) *
      ((1 + (1 - h * (p + 1 + 2 * n) - h)) ^ 2 - h ^ 2 * q ^ 2) =
      h ^ 2 * (4 * (((n : ℝ) + 1) * (n + p + 1) *
        ((2 - h * (p + 2 * n + 2)) ^ 2 - h ^ 2 * q ^ 2))) := by
    ring
  rw [this]
  generalize ((n : ℝ) + 1) * (n + p + 1) * ((2 - h * (p + 2 * n + 2)) ^ 2 - h ^ 2 * q ^ 2) = Y
  have k1 : Real.sqrt (h ^ 2 * (4 * Y)) = h * (2 * Real.sqrt Y) := by
    rw [Real.sqrt_mul (sq_nonneg h), Real.sqrt_sq hh.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [k1]
  field_simp
  ring

/-- Diagonal coefficient: `2(1-x_n²)/(4h) → 2n+p+1` as `h → 0⁺`. -/
theorem diag_tendsto (p : ℝ) (n : ℕ) :
    Tendsto (fun h : ℝ => 2 * (1 - edgePoint p h n ^ 2) / (4 * h)) (𝓝[>] 0)
      (𝓝 (2 * n + p + 1)) := by
  have hc : Continuous fun h : ℝ => (p + 1 + 2 * n) * (2 - h * (p + 1 + 2 * n)) / 2 := by
    fun_prop
  have h0 := hc.tendsto 0
  have e : (p + 1 + 2 * (n : ℝ)) * (2 - 0 * (p + 1 + 2 * n)) / 2 = 2 * n + p + 1 := by ring
  rw [e] at h0
  refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh : 0 < h := hh
  unfold edgePoint
  field_simp
  ring

/-- **Laguerre limit of the edge difference equation.** Along the edge points `x_n = 1 - h(p+1+2n)`,
the leading part of `eq:3jdiff` divided by `4h`, applied to the solution
`Ξ_n = √((n+1)_p)` (`p > -1`), tends to `0` as `h → 0⁺`:
`a_h(x_n+h)/(4h) Ξ_{n-1} + a_h(x_n-h)/(4h) Ξ_{n+1} - 2(1-x_n²)/(4h) Ξ_n → 0`
(the term `2h²[2L(L+1)-M²-σ²+1]Φ/(4h) = O(h)` is dropped; `n - 1` is truncated at `n = 0`,
where the coefficient `√(n(n+p))` vanishes). -/
theorem laguerre_limit_edge_equation (p q : ℝ) (hp : -1 < p) (n : ℕ) :
    Tendsto (fun h : ℝ => ah3 p q h (edgePoint p h n + h) / (4 * h) * laguerreRegular p (n - 1) +
      ah3 p q h (edgePoint p h n - h) / (4 * h) * laguerreRegular p (n + 1) -
        2 * (1 - edgePoint p h n ^ 2) / (4 * h) * laguerreRegular p n) (𝓝[>] 0) (𝓝 0) := by
  have h1 := (ah3_upper_tendsto p q n).mul_const (laguerreRegular p (n - 1))
  have h2 := (ah3_lower_tendsto p q hp.le n).mul_const (laguerreRegular p (n + 1))
  have h3 := (diag_tendsto p n).mul_const (laguerreRegular p n)
  have := (h1.add h2).sub h3
  have e := laguerre_recurrence p hp n
  rwa [e, sub_self] at this

/-! ### Axiom check -/

/-- info: 'FormalResearch.Special.laguerre_recurrence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.laguerre_recurrence

/-- info: 'FormalResearch.Special.laguerre_limit_edge_equation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.laguerre_limit_edge_equation

/-- info: 'FormalResearch.Special.laguerreRegular_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.laguerreRegular_nat

/-- info: 'FormalResearch.Special.ah3_eq_aH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ah3_eq_aH

/-- info: 'FormalResearch.Special.ah3_upper_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ah3_upper_tendsto

/-- info: 'FormalResearch.Special.ah3_lower_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ah3_lower_tendsto

/-- info: 'FormalResearch.Special.diag_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.diag_tendsto

end FormalResearch.Special

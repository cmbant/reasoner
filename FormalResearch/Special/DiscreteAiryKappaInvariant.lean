module

public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# The adiabatic invariant of a three-term recurrence (Airy-free; plan K1, step M-c)

For a real solution `Y` of the Jacobi rows `a (k+1) Y (k+1) + a k Y (k-1) = c k Y k` put

`F_k = a_k (Y_k² + Y_{k-1}²) - c_k Y_k Y_{k-1}`   (`kiF`).

**Exact identity** (`kiF_step`, using the row `k` only):

`F_{k+1} - F_k = (a_{k+1} - a_k)(Y_k² + Y_{k-1} Y_{k+1}) + (c_k - c_{k+1}) Y_k Y_{k+1}`.

So `F` changes only through *differences of the coefficients*; this is the discrete energy/Liouville invariant
(for frozen `a, c` it is the exactly conserved quadratic form `Y_k² + Y_{k-1}² - 2u Y_k Y_{k-1}`, `u = c/(2a)`).  In the
region `2 a_k - |c_k| ≥ m₀ > 0` (the oscillatory band `|u| < 1`) `F_k ≥ (m₀/2)(Y_k² + Y_{k-1}²)` is positive definite,
and the identity gives `|F_{k+1} - F_k| ≤ ε_k F_k` with `ε_k ≍ |Δa| + |Δc|`.

* `kiF_step`: the identity; `kiF_lower`, `kiF_upper`: `(m₀/2) S_k ≤ F_k ≤ 2 a_k S_k`, `S_k = Y_k² + Y_{k-1}²`;
  `ki_next_sq`: `Y_{k+1}² ≤ B S_k` if `c_k² + a_k² ≤ B a_{k+1}²`; `ki_step_bound`: `|F_{k+1} - F_k| ≤ ε_k F_k`.
* `ki_invariant` (**comparison over a band**): for `n` steps `k₀ → k₀ + n` with the stated hypotheses and
  `E = Σ ε`: `F_{k₀+n} ≤ e^{E} F_{k₀}` and `F_{k₀} ≤ e^{2E} F_{k₀+n}`.  No oscillatory averaging and no turning-point
  input is used: `E` is `Σ(|Δa| + |Δc|)` over the band, which is `O(1)` whenever the coefficients vary on the
  macroscopic scale (`O(h)` per step) plus a summable `O(k⁻²)` part (the Hahn left end, `DiscreteAiryKappaLeft`).
* `ki_pair_le`, `ki_pair_ge`: the two-sided pair bounds `S_k ≤ (2 a_{k₁}/(m₀/2)) e^{2E}`-type consequences stated for
  one pair of endpoints (used for the a priori bound on the left of the Airy window).

**Claim class: proved.**  Pure real algebra plus an induction; no numerical constant.  Numerics (mpmath 30 digits, scratch,
not a Lean claim): identity residual `< 10⁻³⁰` on the actual Hahn `3j` chain (`M = σ = 1, N = 342, x = 1/2`; `M = 2, σ = 1,
N = 150, x = 1/3`); `max F/min F` over the whole left region `k ≤ (q_* - 0.1) N` is `1.6`, resp. `1.4`.

**Not formalised.**  A sharper (two-sided, `1 + o(1)`) invariance of the energy: this module bounds `F` between constant
multiples, which is what the a priori bound needs; the asymptotically exact amplitude needs the oscillatory averaging
of the `O(h)` terms.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The adiabatic invariant `F_k = a_k (Y_k² + Y_{k-1}²) - c_k Y_k Y_{k-1}` (see the module docstring). -/
def kiF (a c Y : ℤ → ℝ) (k : ℤ) : ℝ := a k * (Y k ^ 2 + Y (k - 1) ^ 2) - c k * Y k * Y (k - 1)

/-- **The exact step identity** for the invariant (uses the row `k`). -/
lemma kiF_step {a c Y : ℤ → ℝ} {k : ℤ} (h : jac a c Y k = 0) :
    kiF a c Y (k + 1) - kiF a c Y k =
      (a (k + 1) - a k) * (Y k ^ 2 + Y (k - 1) * Y (k + 1)) + (c k - c (k + 1)) * (Y k * Y (k + 1)) := by
  unfold kiF; unfold jac at h
  simp only [add_sub_cancel_right]
  linear_combination (Y (k + 1) - Y (k - 1)) * h

lemma ki_cross_le (c y z : ℝ) : c * y * z ≤ |c| * ((y ^ 2 + z ^ 2) / 2) := by
  rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · nlinarith [sq_nonneg (y - z), sq_nonneg (y + z)]
  · nlinarith [sq_nonneg (y - z), sq_nonneg (y + z)]

lemma ki_cross_ge (c y z : ℝ) : -(|c| * ((y ^ 2 + z ^ 2) / 2)) ≤ c * y * z := by
  rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
  · nlinarith [sq_nonneg (y - z), sq_nonneg (y + z)]
  · nlinarith [sq_nonneg (y - z), sq_nonneg (y + z)]

/-- Positive definiteness: `(m₀/2)(Y_k² + Y_{k-1}²) ≤ F_k` when `2 a_k - |c_k| ≥ m₀`. -/
lemma kiF_lower {a c Y : ℤ → ℝ} {k : ℤ} {m0 : ℝ} (hm : m0 ≤ 2 * a k - |c k|) :
    m0 / 2 * (Y k ^ 2 + Y (k - 1) ^ 2) ≤ kiF a c Y k := by
  unfold kiF
  have h := ki_cross_le (c k) (Y k) (Y (k - 1))
  nlinarith [sq_nonneg (Y k), sq_nonneg (Y (k - 1)), mul_le_mul_of_nonneg_right hm
    (add_nonneg (sq_nonneg (Y k)) (sq_nonneg (Y (k - 1))))]

/-- Upper bound `F_k ≤ 2 a_k (Y_k² + Y_{k-1}²)` when `|c_k| ≤ 2 a_k`. -/
lemma kiF_upper {a c Y : ℤ → ℝ} {k : ℤ} (hm : |c k| ≤ 2 * a k) :
    kiF a c Y k ≤ 2 * a k * (Y k ^ 2 + Y (k - 1) ^ 2) := by
  unfold kiF
  have h := ki_cross_ge (c k) (Y k) (Y (k - 1))
  have := mul_le_mul_of_nonneg_right hm (add_nonneg (sq_nonneg (Y k)) (sq_nonneg (Y (k - 1))))
  nlinarith [sq_nonneg (Y k), sq_nonneg (Y (k - 1))]

/-- The next site is controlled by the pair: `Y_{k+1}² ≤ B (Y_k² + Y_{k-1}²)` if `c_k² + a_k² ≤ B a_{k+1}²`. -/
lemma ki_next_sq {a c Y : ℤ → ℝ} {k : ℤ} {B : ℝ} (h : jac a c Y k = 0) (ha : 0 < a (k + 1))
    (hB : c k ^ 2 + a k ^ 2 ≤ B * a (k + 1) ^ 2) :
    Y (k + 1) ^ 2 ≤ B * (Y k ^ 2 + Y (k - 1) ^ 2) := by
  unfold jac at h
  have e : a (k + 1) * Y (k + 1) = c k * Y k - a k * Y (k - 1) := by linarith
  have h1 : (a (k + 1) * Y (k + 1)) ^ 2 ≤ (c k ^ 2 + a k ^ 2) * (Y k ^ 2 + Y (k - 1) ^ 2) := by
    rw [e]
    nlinarith [sq_nonneg (c k * Y (k - 1) + a k * Y k)]
  have h2 : (a (k + 1) * Y (k + 1)) ^ 2 ≤ B * a (k + 1) ^ 2 * (Y k ^ 2 + Y (k - 1) ^ 2) :=
    h1.trans (mul_le_mul_of_nonneg_right hB (by positivity))
  have h3 : a (k + 1) ^ 2 * Y (k + 1) ^ 2 ≤ a (k + 1) ^ 2 * (B * (Y k ^ 2 + Y (k - 1) ^ 2)) := by
    nlinarith [h2]
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- **One step**: `|F_{k+1} - F_k| ≤ ε F_k` once `2(1+B)(|Δa| + |Δc|) ≤ m₀ ε`. -/
lemma ki_step_bound {a c Y : ℤ → ℝ} {k : ℤ} {m0 B ε : ℝ} (hm0 : 0 < m0) (h : jac a c Y k = 0)
    (ha : 0 < a (k + 1)) (hm : m0 ≤ 2 * a k - |c k|) (hB : c k ^ 2 + a k ^ 2 ≤ B * a (k + 1) ^ 2)
    (hε : 2 * (1 + B) * (|a (k + 1) - a k| + |c (k + 1) - c k|) ≤ m0 * ε) :
    |kiF a c Y (k + 1) - kiF a c Y k| ≤ ε * kiF a c Y k := by
  have hnext := ki_next_sq h ha hB
  have hlow := kiF_lower (Y := Y) (a := a) (c := c) hm
  have hB0 : 0 ≤ B := by
    by_contra hneg
    push Not at hneg
    have : B * a (k + 1) ^ 2 < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
    nlinarith [sq_nonneg (c k), sq_nonneg (a k)]
  rw [kiF_step h]
  set S := Y k ^ 2 + Y (k - 1) ^ 2 with hS
  set Da := |a (k + 1) - a k| with hDa
  set Dc := |c (k + 1) - c k| with hDc
  have hS0 : 0 ≤ S := by positivity
  have t1 : |Y k ^ 2 + Y (k - 1) * Y (k + 1)| ≤ S + Y (k + 1) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Y (k - 1) + Y (k + 1)), sq_nonneg (Y (k - 1) - Y (k + 1)),
      sq_nonneg (Y k), sq_nonneg (Y (k - 1)), sq_nonneg (Y (k + 1))]
  have t2 : |Y k * Y (k + 1)| ≤ S + Y (k + 1) ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Y k + Y (k + 1)), sq_nonneg (Y k - Y (k + 1)),
      sq_nonneg (Y k), sq_nonneg (Y (k - 1)), sq_nonneg (Y (k + 1))]
  have t3 : S + Y (k + 1) ^ 2 ≤ (1 + B) * S := by nlinarith [hnext]
  have e1 : |c k - c (k + 1)| = Dc := by rw [hDc, abs_sub_comm]
  calc |(a (k + 1) - a k) * (Y k ^ 2 + Y (k - 1) * Y (k + 1)) + (c k - c (k + 1)) * (Y k * Y (k + 1))|
      ≤ |(a (k + 1) - a k) * (Y k ^ 2 + Y (k - 1) * Y (k + 1))| +
        |(c k - c (k + 1)) * (Y k * Y (k + 1))| := abs_add_le _ _
    _ = Da * |Y k ^ 2 + Y (k - 1) * Y (k + 1)| + Dc * |Y k * Y (k + 1)| := by
        rw [abs_mul, abs_mul, e1]
    _ ≤ Da * ((1 + B) * S) + Dc * ((1 + B) * S) := by
        gcongr
        · exact t1.trans t3
        · exact t2.trans t3
    _ = (1 + B) * (Da + Dc) * S := by ring
    _ ≤ ε * kiF a c Y k := by
        have h1 : (1 + B) * (Da + Dc) * S * 2 ≤ m0 * ε * S := by
          have := mul_le_mul_of_nonneg_right hε hS0
          nlinarith [this]
        have h2 : m0 * ε * S ≤ 2 * (ε * kiF a c Y k) := by
          have hε0 : 0 ≤ ε := by
            by_contra hneg
            push Not at hneg
            have h3 : 0 ≤ (1 + B) * (Da + Dc) := by positivity
            nlinarith [mul_pos hm0 (neg_pos.2 hneg)]
          nlinarith [mul_le_mul_of_nonneg_left hlow hε0]
        nlinarith

/-- One-step comparison: `F_{k+1} ≤ e^{ε} F_k` and `F_k ≤ e^{2ε} F_{k+1}` for `0 ≤ ε ≤ 1/2`. -/
lemma ki_step_exp {F G ε : ℝ} (hF : 0 ≤ F) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 2) (h : |G - F| ≤ ε * F) :
    G ≤ Real.exp ε * F ∧ F ≤ Real.exp (2 * ε) * G := by
  have h1 := (abs_le.1 h)
  have e1 : 1 + ε ≤ Real.exp ε := by linarith [Real.add_one_le_exp ε]
  have e2 : 1 + 2 * ε ≤ Real.exp (2 * ε) := by linarith [Real.add_one_le_exp (2 * ε)]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right e1 hF]
  · have hG : (1 - ε) * F ≤ G := by nlinarith [h1.1]
    have : F ≤ (1 + 2 * ε) * ((1 - ε) * F) := by nlinarith [mul_nonneg hε0 hF, mul_nonneg hε0 (mul_nonneg hε0 hF)]
    have h3 : (1 + 2 * ε) * ((1 - ε) * F) ≤ Real.exp (2 * ε) * G := by
      calc (1 + 2 * ε) * ((1 - ε) * F) ≤ (1 + 2 * ε) * G :=
            mul_le_mul_of_nonneg_left hG (by linarith)
        _ ≤ Real.exp (2 * ε) * G := by
            have hG0 : 0 ≤ G := le_trans (by nlinarith [mul_nonneg hε0 hF]) hG
            exact mul_le_mul_of_nonneg_right e2 hG0
    linarith

/-- **Comparison of the invariant over a band** (see the module docstring).  Steps `k₀ → k₀ + n`; hypotheses:
rows `jac = 0`, `a > 0`, margin `2 a_k - |c_k| ≥ m₀ > 0`, `c_k² + a_k² ≤ B a_{k+1}²`, and
`2(1+B)(|Δa_k| + |Δc_k|) ≤ m₀ ε_k` with `0 ≤ ε_k ≤ 1/2`.  Then, with `E = Σ ε_k`,
`F_{k₀+n} ≤ e^{E} F_{k₀}` and `F_{k₀} ≤ e^{2E} F_{k₀+n}`. -/
theorem ki_invariant {a c Y ε : ℤ → ℝ} {k0 : ℤ} {m0 B : ℝ} (hm0 : 0 < m0) (n : ℕ)
    (hrow : ∀ i : ℕ, i < n → jac a c Y (k0 + (i : ℤ)) = 0)
    (ha : ∀ i : ℕ, i ≤ n → 0 < a (k0 + (i : ℤ)))
    (hmarg : ∀ i : ℕ, i < n → m0 ≤ 2 * a (k0 + (i : ℤ)) - |c (k0 + (i : ℤ))|)
    (hB : ∀ i : ℕ, i < n → c (k0 + (i : ℤ)) ^ 2 + a (k0 + (i : ℤ)) ^ 2 ≤ B * a (k0 + (i : ℤ) + 1) ^ 2)
    (hε : ∀ i : ℕ, i < n → 2 * (1 + B) * (|a (k0 + (i : ℤ) + 1) - a (k0 + (i : ℤ))| +
        |c (k0 + (i : ℤ) + 1) - c (k0 + (i : ℤ))|) ≤ m0 * ε (k0 + (i : ℤ)))
    (hε0 : ∀ i : ℕ, i < n → 0 ≤ ε (k0 + (i : ℤ))) (hε1 : ∀ i : ℕ, i < n → ε (k0 + (i : ℤ)) ≤ 1 / 2) :
    kiF a c Y (k0 + (n : ℤ)) ≤ Real.exp (∑ i ∈ range n, ε (k0 + (i : ℤ))) * kiF a c Y k0 ∧
      kiF a c Y k0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) * kiF a c Y (k0 + (n : ℤ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i hi => hrow i (by omega)) (fun i hi => ha i (by omega))
      (fun i hi => hmarg i (by omega)) (fun i hi => hB i (by omega)) (fun i hi => hε i (by omega))
      (fun i hi => hε0 i (by omega)) (fun i hi => hε1 i (by omega))
    have hk : k0 + ((n + 1 : ℕ) : ℤ) = k0 + (n : ℤ) + 1 := by push_cast; ring
    have hrown := hrow n (by omega)
    have han1 : 0 < a (k0 + (n : ℤ) + 1) := by
      have := ha (n + 1) le_rfl
      rwa [show k0 + ((n + 1 : ℕ) : ℤ) = k0 + (n : ℤ) + 1 by push_cast; ring] at this
    have hstep := ki_step_bound (a := a) (c := c) (Y := Y) hm0 hrown han1 (hmarg n (by omega)) (hB n (by omega))
      (hε n (by omega))
    have hFn : 0 ≤ kiF a c Y (k0 + (n : ℤ)) := by
      have := kiF_lower (a := a) (c := c) (Y := Y) (hmarg n (by omega))
      nlinarith [sq_nonneg (Y (k0 + (n : ℤ))), sq_nonneg (Y (k0 + (n : ℤ) - 1))]
    obtain ⟨s1, s2⟩ := ki_step_exp hFn (hε0 n (by omega)) (hε1 n (by omega)) hstep
    rw [hk, Finset.sum_range_succ, Real.exp_add, mul_add, Real.exp_add]
    constructor
    · calc kiF a c Y (k0 + (n : ℤ) + 1) ≤ Real.exp (ε (k0 + (n : ℤ))) * kiF a c Y (k0 + (n : ℤ)) := s1
        _ ≤ Real.exp (ε (k0 + (n : ℤ))) * (Real.exp (∑ i ∈ range n, ε (k0 + (i : ℤ))) * kiF a c Y k0) :=
            mul_le_mul_of_nonneg_left ih'.1 (Real.exp_pos _).le
        _ = _ := by ring
    · have hE0 : 0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) := (Real.exp_pos _).le
      calc kiF a c Y k0 ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) * kiF a c Y (k0 + (n : ℤ)) := ih'.2
        _ ≤ Real.exp (2 * ∑ i ∈ range n, ε (k0 + (i : ℤ))) *
            (Real.exp (2 * ε (k0 + (n : ℤ))) * kiF a c Y (k0 + (n : ℤ) + 1)) :=
            mul_le_mul_of_nonneg_left s2 hE0
        _ = _ := by ring

/-- info: 'FormalResearch.Special.ki_invariant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ki_invariant

end FormalResearch.Special

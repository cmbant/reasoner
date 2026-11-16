module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-!
# Discrete Jacobi calculus I: Casoratian, Green function, second solution

The Airy-free calculus for second-order three-term (Jacobi) recurrences on `ℤ`-intervals that underlies the
discrete-to-Airy limit of the Weyl/W1 papers (the Volterra and comparison parts are in
`DiscreteJacobiCalculusVolterra` and `DiscreteJacobiCalculusComparison`).

Conventions.  Sequences are `ℤ → ℝ` (a `ℤ`-index avoids truncated subtraction in `k - 1`; a chain on `ℕ` is
used by extending by anything outside its range, all statements being about explicit `Icc` windows).  The *row
operator* is
`jac a c y k = a (k+1) * y (k+1) + a k * y (k-1) - c k * y k`
(P3 natural gauge `x Y_k = A_{k+1}Y_{k+1} + B_kY_k + A_kY_{k-1}` with `c = x - B`; the W1 form
`a_{n-1}u_{n-1} + (b_n - E)u_n + a_nu_{n+1} = 0` has `a (k+1) = a_k^{W1}`).  A *solution on `Icc lo N`* is a
sequence with `jac a c y k = 0` for `k ∈ Icc lo N`; the row `k` involves the sites `k-1, k, k+1`.

Statements (all **proved**, exact identities, no asymptotics; mpmath 40-digit sanity run on random positive
`a`, random `c` of the identities `cas_sub`, `green_final`, `cas_secondSol`, `jac_secondSol` and the reduction of
order identity of the Volterra part: all residuals `< 1e-38`):

* `cas a f g k = a (k+1) (f k g (k+1) - f (k+1) g k)` and the Lagrange identity
  `cas_sub : cas k - cas (k-1) = f k * jac g k - g k * jac f k`; hence `cas_eq_of_sol`: the Casoratian of two
  solutions on `Icc lo N` is constant on `Icc (lo-1) N`.  (The paper's Casoratian
  `𝒲 = a(f_{1,k+1} f_{2,k} - f_{1,k} f_{2,k+1})`, A:1130, equals `cas a f2 f1 = - cas a f1 f2`.)
* `eq_zero_of_two_values`: a solution vanishing at two adjacent sites vanishes on the whole window (needs
  `a ≠ 0`); `eq_of_final_values`: uniqueness of the final-value problem.
* `green_final` (A:1130, `prop:airy2-exact`): for solutions `f1 f2` with `W = cas a f1 f2 ≠ 0` the final-value
  Green function `e k = Σ_{i ∈ (k, N]} (f1 k f2 i - f2 k f1 i) r i / W` satisfies `jac e = r` on `Icc lo N` and
  `e N = e (N+1) = 0`.
* `redSum`, `secondSol`: the exact second solution `f2 = f1 · Σ_{i<k} 1/(a f1 f1)` of a solution `f1` without
  zeros has `cas a f1 f2 = 1` (`cas_secondSol`) and solves the recurrence (`jac_secondSol`); it needs no
  second input function (in the Airy lane it replaces the Bi-type solution on the recessive side);
  `green_final_secondSol` is the corresponding explicit Green function with `W = 1`.

**Not formalised** here: anything asymptotic (this module carries no `O(h)` and no constants other than the
exact ones displayed); the existence/boundedness of the sums in `ℕ`-indexed chains with a hard edge.
-/

@[expose] public section

open Finset

namespace FormalResearch.DiscreteAiry

/-- The Jacobi row operator `a (k+1) y (k+1) + a k y (k-1) - c k y k` (a solution has `jac a c y k = 0`). -/
def jac (a c y : ℤ → ℝ) (k : ℤ) : ℝ := a (k + 1) * y (k + 1) + a k * y (k - 1) - c k * y k

/-- The Casoratian `a (k+1) (f k g (k+1) - f (k+1) g k)` of two sequences across the bond `(k, k+1)`. -/
def cas (a f g : ℤ → ℝ) (k : ℤ) : ℝ := a (k + 1) * (f k * g (k + 1) - f (k + 1) * g k)

lemma cas_self (a f : ℤ → ℝ) (k : ℤ) : cas a f f k = 0 := by unfold cas; ring

lemma cas_comm (a f g : ℤ → ℝ) (k : ℤ) : cas a g f k = - cas a f g k := by simp [cas]; ring

lemma cas_add_right (a f g h : ℤ → ℝ) (k : ℤ) :
    cas a f (fun i => g i + h i) k = cas a f g k + cas a f h k := by simp [cas]; ring

lemma cas_smul_right (a f g : ℤ → ℝ) (t : ℝ) (k : ℤ) :
    cas a f (fun i => t * g i) k = t * cas a f g k := by simp [cas]; ring

/-- **Lagrange identity**: `cas a f g k - cas a f g (k-1) = f k * jac g k - g k * jac f k`. -/
theorem cas_sub (a c f g : ℤ → ℝ) (k : ℤ) :
    cas a f g k - cas a f g (k - 1) = f k * jac a c g k - g k * jac a c f k := by
  simp only [cas, jac, sub_add_cancel]; ring

/-- The Casoratian of two solutions on `Icc lo N` is constant on `Icc (lo-1) N`. -/
theorem cas_eq_of_sol (a c f g : ℤ → ℝ) (lo N : ℤ) (hf : ∀ k ∈ Icc lo N, jac a c f k = 0)
    (hg : ∀ k ∈ Icc lo N, jac a c g k = 0) :
    ∀ k ∈ Icc (lo - 1) N, cas a f g k = cas a f g N := by
  have key : ∀ n : ℕ, ∀ k : ℤ, k + n = N → lo - 1 ≤ k → cas a f g k = cas a f g N := by
    intro n
    induction n with
    | zero => intro k hk _; have : k = N := by omega
              rw [this]
    | succ n ih =>
      intro k hk hlo
      have h1 : cas a f g (k + 1) = cas a f g N := ih (k + 1) (by omega) (by omega)
      have h2 := cas_sub a c f g (k + 1)
      rw [hf (k + 1) (by simp only [mem_Icc]; omega), hg (k + 1) (by simp only [mem_Icc]; omega)] at h2
      simp only [add_sub_cancel_right, mul_zero, sub_zero] at h2
      linarith
  intro k hk
  rw [mem_Icc] at hk
  exact key (N - k).toNat k (by omega) hk.1

/-- Uniqueness from two adjacent values: a solution on `Icc lo N` (with `a k ≠ 0` for `k ∈ Icc lo (N+1)`)
which vanishes at two adjacent sites `k₀, k₀+1` of `Icc (lo-1) (N+1)` vanishes on all of `Icc (lo-1) (N+1)`. -/
theorem eq_zero_of_two_values (a c y : ℤ → ℝ) (lo N k₀ : ℤ) (hrow : ∀ k ∈ Icc lo N, jac a c y k = 0)
    (ha : ∀ k ∈ Icc lo (N + 1), a k ≠ 0) (hk₀ : k₀ ∈ Icc (lo - 1) N) (h0 : y k₀ = 0)
    (h1 : y (k₀ + 1) = 0) : ∀ k ∈ Icc (lo - 1) (N + 1), y k = 0 := by
  rw [mem_Icc] at hk₀
  -- forward
  have fwd : ∀ n : ℕ, k₀ + n + 1 ≤ N + 1 → y (k₀ + n) = 0 ∧ y (k₀ + n + 1) = 0 := by
    intro n
    induction n with
    | zero => intro _; simpa using ⟨h0, h1⟩
    | succ n ih =>
      intro hn
      obtain ⟨e0, e1⟩ := ih (by omega)
      refine ⟨by push_cast; rw [← add_assoc]; exact e1, ?_⟩
      have hr := hrow (k₀ + n + 1) (by simp only [mem_Icc]; omega)
      have hne := ha (k₀ + n + 1 + 1) (by simp only [mem_Icc]; omega)
      simp only [jac] at hr
      have : y (k₀ + n + 1 + 1) = 0 := by
        have e0' : y (k₀ + n + 1 - 1) = 0 := by simpa using e0
        rw [e1, e0'] at hr
        have : a (k₀ + n + 1 + 1) * y (k₀ + n + 1 + 1) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hne
      push_cast
      simpa [add_assoc] using this
  -- backward
  have bwd : ∀ n : ℕ, lo - 1 ≤ k₀ - n → y (k₀ - n) = 0 ∧ y (k₀ - n + 1) = 0 := by
    intro n
    induction n with
    | zero => intro _; simpa using ⟨h0, h1⟩
    | succ n ih =>
      intro hn
      obtain ⟨e0, e1⟩ := ih (by omega)
      have hr := hrow (k₀ - n) (by simp only [mem_Icc]; omega)
      have hne := ha (k₀ - n) (by simp only [mem_Icc]; omega)
      simp only [jac] at hr
      have h3 : y (k₀ - n - 1) = 0 := by
        rw [e1, e0] at hr
        have : a (k₀ - n) * y (k₀ - n - 1) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left hne
      have e4 : k₀ - ((n + 1 : ℕ) : ℤ) + 1 = k₀ - n := by push_cast; ring
      have e5 : k₀ - ((n + 1 : ℕ) : ℤ) = k₀ - n - 1 := by push_cast; ring
      rw [e4, e5]
      exact ⟨h3, e0⟩
  intro k hk
  rw [mem_Icc] at hk
  by_cases hkk : k₀ ≤ k
  · rcases eq_or_lt_of_le hkk with h | h
    · rw [← h]; exact h0
    · have := (fwd (k - 1 - k₀).toNat (by omega)).2
      have hh : k₀ + ((k - 1 - k₀).toNat : ℤ) + 1 = k := by omega
      rw [hh] at this; exact this
  · have := (bwd (k₀ - k).toNat (by omega)).1
    have hh : k₀ - ((k₀ - k).toNat : ℤ) = k := by omega
    rw [hh] at this; exact this

/-- Final-value uniqueness: two solutions of `jac y = r` on `Icc lo N` with equal values at the last two
sites `N, N+1` agree on `Icc (lo-1) (N+1)` (if `a k ≠ 0` on `Icc lo (N+1)` and `lo ≤ N`). -/
theorem eq_of_final_values (a c y z r : ℤ → ℝ) (lo N : ℤ) (hlo : lo ≤ N)
    (hy : ∀ k ∈ Icc lo N, jac a c y k = r k) (hz : ∀ k ∈ Icc lo N, jac a c z k = r k)
    (ha : ∀ k ∈ Icc lo (N + 1), a k ≠ 0) (hN : y N = z N) (hN1 : y (N + 1) = z (N + 1)) :
    ∀ k ∈ Icc (lo - 1) (N + 1), y k = z k := by
  have hrow : ∀ k ∈ Icc lo N, jac a c (fun i => y i - z i) k = 0 := by
    intro k hk
    have := hy k hk; have := hz k hk
    simp only [jac] at *; linarith
  have := eq_zero_of_two_values a c (fun i => y i - z i) lo N N hrow ha
    (by simp only [mem_Icc]; omega) (by simp [hN]) (by simp [hN1])
  intro k hk
  have := this k hk
  simpa [sub_eq_zero] using this

/-- **Final-value Green function** (`A:1130`, proof of `prop:airy2-exact`).  `e k` sums over the lattice sites
`i ∈ (k, N]`. -/
noncomputable def greenFinal (f1 f2 r : ℤ → ℝ) (W : ℝ) (N k : ℤ) : ℝ :=
  ∑ i ∈ Ioc k N, (f1 k * f2 i - f2 k * f1 i) * r i / W

lemma greenFinal_eq_zero_of_le (f1 f2 r : ℤ → ℝ) (W : ℝ) (N k : ℤ) (hk : N ≤ k) :
    greenFinal f1 f2 r W N k = 0 := by
  unfold greenFinal
  rw [Ioc_eq_empty (by omega)]; simp

/-- Let `f1, f2` be solutions on `Icc lo N` with `W = cas a f1 f2 N ≠ 0` (the common value of the Casoratian).
Then `e = greenFinal f1 f2 r W N` solves `jac a c e k = r k` for `k ∈ Icc lo N`, with final data
`e N = e (N+1) = 0`. -/
theorem green_final (a c f1 f2 r : ℤ → ℝ) (lo N : ℤ) (hf1 : ∀ k ∈ Icc lo N, jac a c f1 k = 0)
    (hf2 : ∀ k ∈ Icc lo N, jac a c f2 k = 0) (W : ℝ) (hW : cas a f1 f2 N = W) (hW0 : W ≠ 0) :
    (∀ k ∈ Icc lo N, jac a c (greenFinal f1 f2 r W N) k = r k) ∧
      greenFinal f1 f2 r W N N = 0 ∧ greenFinal f1 f2 r W N (N + 1) = 0 := by
  refine ⟨?_, greenFinal_eq_zero_of_le _ _ _ _ _ _ le_rfl,
    greenFinal_eq_zero_of_le _ _ _ _ _ _ (by omega)⟩
  intro k hk
  rw [mem_Icc] at hk
  have hcas : cas a f1 f2 (k - 1) = W := by
    rw [← hW]; exact cas_eq_of_sol a c f1 f2 lo N hf1 hf2 (k - 1) (by simp only [mem_Icc]; omega)
  -- the three values of `e` in terms of sums over `Ioc k N`
  set G : ℤ → ℤ → ℝ := fun j i => (f1 j * f2 i - f2 j * f1 i) * r i / W with hG
  have e0 : greenFinal f1 f2 r W N k = ∑ i ∈ Ioc k N, G k i := rfl
  have ep : greenFinal f1 f2 r W N (k + 1) = ∑ i ∈ Ioc k N, G (k + 1) i := by
    unfold greenFinal
    by_cases hkN : k < N
    · have : Ioc k N = insert (k + 1) (Ioc (k + 1) N) := by ext i; simp only [mem_Ioc, mem_insert]; omega
      rw [this, Finset.sum_insert (by simp)]
      have hz : f1 (k + 1) * f2 (k + 1) - f2 (k + 1) * f1 (k + 1) = 0 := by ring
      simp [hG, hz]
    · have : k = N := by omega
      subst this
      simp
  have em : greenFinal f1 f2 r W N (k - 1) = G (k - 1) k + ∑ i ∈ Ioc k N, G (k - 1) i := by
    unfold greenFinal
    have : Ioc (k - 1) N = insert k (Ioc k N) := by ext i; simp only [mem_Ioc, mem_insert]; omega
    rw [this, Finset.sum_insert (by simp)]
  have hsum : a (k + 1) * (∑ i ∈ Ioc k N, G (k + 1) i) + a k * (∑ i ∈ Ioc k N, G (k - 1) i)
      - c k * (∑ i ∈ Ioc k N, G k i) = 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_eq_zero
    intro i _
    have h1 := hf1 k (by simp only [mem_Icc]; omega)
    have h2 := hf2 k (by simp only [mem_Icc]; omega)
    simp only [jac] at h1 h2
    simp only [hG]
    field_simp
    linear_combination (f2 i * r i) * h1 - (f1 i * r i) * h2
  have hbd : a k * G (k - 1) k = r k := by
    simp only [cas, sub_add_cancel] at hcas
    simp only [hG]
    field_simp
    linear_combination (r k) * hcas
  simp only [jac]
  rw [ep, em, e0]
  linear_combination hsum + hbd

/-- Triangle-inequality bound for the Green function (the form used in `prop:airy2-exact`):
`|e k| ≤ Σ_{i ∈ (k,N]} (|f1 k||f2 i| + |f2 k||f1 i|) |r i| / |W|`. -/
theorem abs_greenFinal_le (f1 f2 r : ℤ → ℝ) (W : ℝ) (N k : ℤ) :
    |greenFinal f1 f2 r W N k| ≤
      ∑ i ∈ Ioc k N, (|f1 k| * |f2 i| + |f2 k| * |f1 i|) * |r i| / |W| := by
  unfold greenFinal
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_div, abs_mul]
  gcongr
  exact (abs_sub _ _).trans (by rw [abs_mul, abs_mul])

/-- The reduction-of-order sum `T k = Σ_{i ∈ [m, k)} 1 / (a (i+1) f1 i f1 (i+1))`. -/
noncomputable def redSum (a f1 : ℤ → ℝ) (m k : ℤ) : ℝ := ∑ i ∈ Ico m k, 1 / (a (i + 1) * f1 i * f1 (i + 1))

/-- The exact second solution `f2 k = f1 k * Σ_{i ∈ [m, k)} 1/(a (i+1) f1 i f1 (i+1))`
(reduction of order, `ψ = f1`, `1 + σ = T`). -/
noncomputable def secondSol (a f1 : ℤ → ℝ) (m k : ℤ) : ℝ := f1 k * redSum a f1 m k

lemma redSum_succ (a f1 : ℤ → ℝ) (m k : ℤ) (hk : m ≤ k) :
    redSum a f1 m (k + 1) = redSum a f1 m k + 1 / (a (k + 1) * f1 k * f1 (k + 1)) := by
  unfold redSum
  have : Ico m (k + 1) = insert k (Ico m k) := by ext i; simp only [mem_Ico, mem_insert]; omega
  rw [this, Finset.sum_insert (by simp)]; ring

/-- **Casoratian of the second solution** is identically `1`: `cas a f1 (secondSol a f1 m) k = 1`
for `k ≥ m` whenever `a (k+1) ≠ 0`, `f1 k ≠ 0`, `f1 (k+1) ≠ 0`. -/
theorem cas_secondSol (a f1 : ℤ → ℝ) (m k : ℤ) (hk : m ≤ k) (ha : a (k + 1) ≠ 0) (h0 : f1 k ≠ 0)
    (h1 : f1 (k + 1) ≠ 0) : cas a f1 (secondSol a f1 m) k = 1 := by
  unfold cas secondSol
  rw [redSum_succ a f1 m k hk]
  field_simp
  ring

/-- `secondSol` solves the recurrence at row `k` (`m + 1 ≤ k`) whenever `f1` does and `f1`, `a` have no zero
at the sites involved. -/
theorem jac_secondSol (a c f1 : ℤ → ℝ) (m k : ℤ) (hk : m + 1 ≤ k) (ha : a (k + 1) ≠ 0) (ha' : a k ≠ 0)
    (h0 : f1 (k - 1) ≠ 0) (h1 : f1 k ≠ 0) (h2 : f1 (k + 1) ≠ 0) (hrow : jac a c f1 k = 0) :
    jac a c (secondSol a f1 m) k = 0 := by
  have c1 := cas_secondSol a f1 m k (by omega) ha h1 h2
  have c0 := cas_secondSol a f1 m (k - 1) (by omega) (by simpa using ha') h0 (by simpa using h1)
  have := cas_sub a c f1 (secondSol a f1 m) k
  rw [c1, c0, hrow] at this
  have : f1 k * jac a c (secondSol a f1 m) k = 0 := by linarith
  exact (mul_eq_zero.mp this).resolve_left h1

/-- Explicit final-value Green function without any second input function: if `f1` solves the recurrence on
`Icc (m+1) N` and has no zero on `Icc m (N+1)`, `a ≠ 0` on `Icc (m+1) (N+1)`, then
`e k = Σ_{i ∈ (k, N]} f1 k f1 i (T i - T k) r i` (`T = redSum a f1 m`) solves `jac e = r` on `Icc (m+1) N`
with `e N = e (N+1) = 0`. -/
theorem green_final_secondSol (a c f1 r : ℤ → ℝ) (m N : ℤ) (hrow : ∀ k ∈ Icc (m + 1) N, jac a c f1 k = 0)
    (hf : ∀ k ∈ Icc m (N + 1), f1 k ≠ 0) (ha : ∀ k ∈ Icc (m + 1) (N + 1), a k ≠ 0) :
    (∀ k ∈ Icc (m + 1) N, jac a c (greenFinal f1 (secondSol a f1 m) r 1 N) k = r k) ∧
      greenFinal f1 (secondSol a f1 m) r 1 N N = 0 ∧
      greenFinal f1 (secondSol a f1 m) r 1 N (N + 1) = 0 := by
  by_cases hN : m + 1 ≤ N
  · apply green_final a c f1 (secondSol a f1 m) r (m + 1) N hrow
    · intro k hk
      rw [mem_Icc] at hk
      exact jac_secondSol a c f1 m k hk.1 (ha (k + 1) (by simp only [mem_Icc]; omega))
        (ha k (by simp only [mem_Icc]; omega)) (hf (k - 1) (by simp only [mem_Icc]; omega))
        (hf k (by simp only [mem_Icc]; omega)) (hf (k + 1) (by simp only [mem_Icc]; omega))
        (hrow k (by simp only [mem_Icc]; omega))
    · exact cas_secondSol a f1 m N (by omega) (ha (N + 1) (by simp only [mem_Icc]; omega))
        (hf N (by simp only [mem_Icc]; omega)) (hf (N + 1) (by simp only [mem_Icc]; omega))
    · exact one_ne_zero
  · refine ⟨fun k hk => ?_, greenFinal_eq_zero_of_le _ _ _ _ _ _ le_rfl,
      greenFinal_eq_zero_of_le _ _ _ _ _ _ (by omega)⟩
    rw [mem_Icc] at hk; omega

/-- info: 'FormalResearch.DiscreteAiry.cas_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.cas_sub

/-- info: 'FormalResearch.DiscreteAiry.cas_eq_of_sol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.cas_eq_of_sol

/-- info: 'FormalResearch.DiscreteAiry.eq_zero_of_two_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.eq_zero_of_two_values

/-- info: 'FormalResearch.DiscreteAiry.eq_of_final_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.eq_of_final_values

/-- info: 'FormalResearch.DiscreteAiry.green_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.green_final

/-- info: 'FormalResearch.DiscreteAiry.abs_greenFinal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.abs_greenFinal_le

/-- info: 'FormalResearch.DiscreteAiry.cas_secondSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.cas_secondSol

/-- info: 'FormalResearch.DiscreteAiry.jac_secondSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.jac_secondSol

/-- info: 'FormalResearch.DiscreteAiry.green_final_secondSol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.green_final_secondSol

end FormalResearch.DiscreteAiry

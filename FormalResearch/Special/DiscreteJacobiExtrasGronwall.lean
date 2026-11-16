module

public import FormalResearch.Special.DiscreteJacobiCalculus
public import Mathlib.Analysis.ODE.DiscreteGronwall

/-!
# Discrete Jacobi calculus VI: scaled two-vector discrete Grönwall bound for a three-term recurrence

Airy-free wrapper of Mathlib's `discrete_gronwall` (`Mathlib/Analysis/ODE/DiscreteGronwall.lean`) for the
*bounded oscillatory window* (plan M6 of the discrete-to-Airy programme: `discrete_airy_window`).

**Setting.**  A solution of `y_{k+1} = p_k y_k + q_k y_{k-1} + s_k` is followed with the scaled state
`v_k = (y_k, (y_k - y_{k-1})/δ)` and the `ℓ¹` size `stateSize y δ k = |y k| + |y k - y (k-1)| / δ`.  The
per-step matrix is `[[1 + σ_k, -δ q_k], [σ_k/δ, -q_k]]` with `σ_k = p_k + q_k - 1`; its `ℓ¹` operator norm is
`≤ 1 + Lδ` as soon as `|σ_k| ≤ Sg δ²` and `|q_k| ≤ 1 + Qq δ` (`L = 1 + 2 Sg + 2 Qq`, `0 < δ ≤ 1`).

Statements (all **proved**; uncommitted mpmath/python sanity runs: the one-step inequality on an Airy-like recurrence
`a = 1`, `c = 2 + δ²X`, `|X| ≤ 3`, `δ ∈ {0.2, 0.05}` with random defects (ratio of the two sides `≤ 0.85`), and
the final bound of `jacobi_difference_bound` on 300 random coefficient sequences obeying its hypotheses
(`δ ∈ {0.3, 0.1, 0.03}`, ratio of the two sides `≤ 0.96`)):

* `step_bound`: the one-step inequality `U_{k+1} ≤ (1 + Lδ) U_k + (1 + 1/δ)|s_k|` (pure real arithmetic);
* `three_term_bound` (the Grönwall step, via `discrete_gronwall`): after `n` steps
  `U(k0 + n) ≤ (U k0 + ∑_{i<n} (1 + 1/δ)|s (k0 + i)|) · exp (L δ n)`;
* `jacobi_difference_bound` (**the form used for the window**): for `d` with `jac a c d k = r k` on `Ico k0 K`
  (a difference of two solutions with right-hand sides `r1, r2` has `r = r1 - r2`: `jacobi_solutions_bound`),
  `a ≥ m > 0`, the *near-hyperbolic* hypothesis `|c k - a k - a (k+1)| ≤ Sg' δ²` (in the Airy lane
  `δ = h^{1/3}` and `c - a_k - a_{k+1} = O(h^{2/3}(1 + |X|))`, so `Sg' ~ A0` on `|X| ≤ A0`), the smoothness
  `|a (k+1) - a k| ≤ Qq' δ²` and `|r k| ≤ ρ`:
  `|d k| + |d k - d (k-1)|/δ ≤ (|d k0| + |d k0 - d (k0-1)|/δ + 2 (K-k0) ρ / (δ m)) · exp (L δ (K-k0))`,
  `L = 1 + 2 (Sg' + Qq')/m`;
* `jacobi_difference_bound_down`, `jacobi_solutions_bound_down`: the same marching **downward** from the two top
  sites `K, K+1` to `J` (the direction of the window `X ∈ [-A0, -1]`, since `X_k` increases with `k`), by the
  reflection `jac_reflect`.

**How plan M6 uses it.**  Let `f` be an exact solution and `ψ` the parametrix, `d = f - κψ`, so that
`jac a c d = -κ jac a c ψ =: r` with `|r| ≤ ρ = |κ| C h² sup ψ` (hypothesis `hdef` of M4), `δ = h^{1/3}`.  If at the
two top sites `d` is `ε`-small in the scaled sense, then on the `K - J ≲ A0 h^{-1/3}` steps down to `X = -A0` one
gets `|d k| ≤ (ε' + 2 (K-J) ρ/(δ m)) exp (L δ (K-J))`: the inhomogeneous term is
`h^{-1/3} · h² / h^{1/3} = h^{4/3}` and `exp (L δ (K-J)) = exp (L A0')` with `L ≈ 1 + 2 Sg'/m` and `Sg' ≈ A0` on the Airy window, i.e. `e^{O(A0²)}`: harmless
for a statement quantified over `A0`, but not the `e^{C A0}` of the plan.

**Why the structural hypotheses.**  Crude bounds `|c| ≤ C0`, `a ∈ [a_min, a_max]` do *not* suffice: for
`c = 2.5 a` the recurrence `y_{k+1} = 2.5 y_k - y_{k-1}` has multipliers `2, 1/2` and `2^n` growth over the
`n ~ δ^{-1}` steps of the window.  The theorem needs the near-hyperbolic structure `c_k - a_k - a_{k+1} = O(δ²)`
(i.e. `σ = O(δ²)`), which holds precisely in a bounded `X`-window.

The application is `discrete_airy_window` (`AiryWindowMain`), with `hdef`, `hdefW` as hypotheses.

**Not formalised** here: the verification of those hypotheses (the defect bound on the whole window, the sizes of `ψ`, the
near-hyperbolic constants for the Hahn/Racah or W1 coefficients), the sharper form with `exp (L δ (n - i))` inside the
sum (the stated form has `exp (L δ n)` outside the sum, weaker by the factor `exp (L δ i)` on the `i`-th
perturbation; the same order for the window), and a lower bound (reverse Grönwall).
-/

@[expose] public section

open Finset Real

namespace FormalResearch.DiscreteAiry

/-- The scaled `ℓ¹` size `|y k| + |y k - y (k-1)| / δ` of the state `v_k = (y_k, (y_k - y_{k-1})/δ)`. -/
noncomputable def stateSize (y : ℤ → ℝ) (δ : ℝ) (k : ℤ) : ℝ := |y k| + |y k - y (k - 1)| / δ

lemma stateSize_nonneg (y : ℤ → ℝ) (δ : ℝ) (hδ : 0 < δ) (k : ℤ) : 0 ≤ stateSize y δ k := by
  unfold stateSize; positivity

/-- **One step** of the scaled two-vector recurrence: if `y2 = p y1 + q y0 + s`, `|p + q - 1| ≤ Sg δ²` and
`|q| ≤ 1 + Qq δ` (`0 < δ ≤ 1`) then
`|y2| + |y2 - y1|/δ ≤ (1 + (1 + 2Sg + 2Q) δ) (|y1| + |y1 - y0|/δ) + (1 + 1/δ)|s|`. -/
theorem step_bound (y0 y1 y2 p q s δ Sg Qq : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hSg : 0 ≤ Sg) (hQ : 0 ≤ Qq)
    (hrec : y2 = p * y1 + q * y0 + s) (hσ : |p + q - 1| ≤ Sg * δ ^ 2) (hq : |q| ≤ 1 + Qq * δ) :
    |y2| + |y2 - y1| / δ ≤ (1 + (1 + 2 * Sg + 2 * Qq) * δ) * (|y1| + |y1 - y0| / δ) + (1 + 1 / δ) * |s| := by
  set w := (y1 - y0) / δ with hw
  set σ := p + q - 1 with hσdef
  have hy0 : y0 = y1 - δ * w := by rw [hw]; field_simp; ring
  have e2 : y2 = (1 + σ) * y1 - q * δ * w + s := by rw [hrec, hy0, hσdef]; ring
  have e21 : y2 - y1 = σ * y1 - q * δ * w + s := by rw [e2]; ring
  have hwabs : |y1 - y0| / δ = |w| := by rw [hw, abs_div, abs_of_pos hδ]
  rw [hwabs]
  have b1 : |y2| ≤ (1 + |σ|) * |y1| + δ * |q| * |w| + |s| := by
    rw [e2]
    calc |(1 + σ) * y1 - q * δ * w + s| ≤ |(1 + σ) * y1 - q * δ * w| + |s| := abs_add_le _ _
      _ ≤ |(1 + σ) * y1| + |q * δ * w| + |s| := by gcongr; exact abs_sub _ _
      _ ≤ (1 + |σ|) * |y1| + δ * |q| * |w| + |s| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hδ]
          have : |1 + σ| ≤ 1 + |σ| := by
            calc |1 + σ| ≤ |(1 : ℝ)| + |σ| := abs_add_le _ _
              _ = 1 + |σ| := by simp
          have := mul_le_mul_of_nonneg_right this (abs_nonneg y1)
          nlinarith [abs_nonneg q, abs_nonneg w]
  have b2 : |y2 - y1| ≤ |σ| * |y1| + δ * |q| * |w| + |s| := by
    rw [e21]
    calc |σ * y1 - q * δ * w + s| ≤ |σ * y1 - q * δ * w| + |s| := abs_add_le _ _
      _ ≤ |σ * y1| + |q * δ * w| + |s| := by gcongr; exact abs_sub _ _
      _ = |σ| * |y1| + δ * |q| * |w| + |s| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_pos hδ]; ring
  have b2' : |y2 - y1| / δ ≤ |σ| / δ * |y1| + |q| * |w| + |s| / δ := by
    rw [div_le_iff₀ hδ]
    have : (|σ| / δ * |y1| + |q| * |w| + |s| / δ) * δ = |σ| * |y1| + δ * |q| * |w| + |s| := by
      field_simp
    rw [this]; exact b2
  have hσδ : |σ| / δ ≤ Sg * δ := by
    rw [div_le_iff₀ hδ]; nlinarith
  have hσ2 : |σ| ≤ Sg * δ := by nlinarith [abs_nonneg σ]
  have hq2 : |q| * (1 + δ) ≤ 1 + (1 + 2 * Qq) * δ := by
    have := mul_le_mul_of_nonneg_right hq (by linarith : (0 : ℝ) ≤ 1 + δ)
    have h5 : Qq * δ ^ 2 ≤ Qq * δ := mul_le_mul_of_nonneg_left (by nlinarith) hQ
    nlinarith
  have hy1 : (1 + |σ| + |σ| / δ) ≤ 1 + (1 + 2 * Sg + 2 * Qq) * δ := by nlinarith
  have hs1 : |s| / δ = 1 / δ * |s| := by ring
  have hsum : |y2| + |y2 - y1| / δ ≤ (1 + |σ| + |σ| / δ) * |y1| + |q| * (1 + δ) * |w| + (1 + 1 / δ) * |s| := by
    nlinarith [b1, b2', hs1]
  have h3 : (1 + |σ| + |σ| / δ) * |y1| ≤ (1 + (1 + 2 * Sg + 2 * Qq) * δ) * |y1| :=
    mul_le_mul_of_nonneg_right hy1 (abs_nonneg _)
  have h4 : |q| * (1 + δ) * |w| ≤ (1 + (1 + 2 * Sg + 2 * Qq) * δ) * |w| := by
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    nlinarith
  nlinarith

/-- **Grönwall step along a window** (`discrete_gronwall` for the scaled state).  Rows `k0, …, K-1` of
`y (k+1) = p k y k + q k y (k-1) + s k` with `|p k + q k - 1| ≤ Sg δ²`, `|q k| ≤ 1 + Qq δ`:
for `k0 + n ≤ K`,
`stateSize y δ (k0 + n) ≤ (stateSize y δ k0 + ∑_{i<n} (1 + 1/δ)|s (k0+i)|) · exp ((1 + 2Sg + 2Q) δ n)`. -/
theorem three_term_bound (y p q s : ℤ → ℝ) (δ Sg Qq : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hSg : 0 ≤ Sg) (hQ : 0 ≤ Qq)
    (k0 K : ℤ) (hrec : ∀ k ∈ Ico k0 K, y (k + 1) = p k * y k + q k * y (k - 1) + s k)
    (hσ : ∀ k ∈ Ico k0 K, |p k + q k - 1| ≤ Sg * δ ^ 2) (hq : ∀ k ∈ Ico k0 K, |q k| ≤ 1 + Qq * δ)
    (n : ℕ) (hn : k0 + n ≤ K) :
    stateSize y δ (k0 + n) ≤
      (stateSize y δ k0 + ∑ i ∈ range n, (1 + 1 / δ) * |s (k0 + i)|) * exp ((1 + 2 * Sg + 2 * Qq) * δ * n) := by
  set M : ℕ := (K - k0).toNat with hM
  set L : ℝ := 1 + 2 * Sg + 2 * Qq with hL
  have hL0 : 0 ≤ L := by rw [hL]; linarith
  -- the sequence frozen after `M` steps
  let u : ℕ → ℝ := fun m => stateSize y δ (k0 + (min m M : ℕ))
  let b : ℕ → ℝ := fun m => (1 + 1 / δ) * |s (k0 + m)|
  have hu : ∀ m ≥ 0, u (m + 1) ≤ (1 + L * δ) * u m + b m := by
    intro m _
    by_cases hm : m < M
    · have h1 : min (m + 1) M = m + 1 := by omega
      have h2 : min m M = m := by omega
      simp only [u, h1, h2]
      have hk : k0 + (m : ℤ) ∈ Ico k0 K := by simp only [mem_Ico]; omega
      have := step_bound (y (k0 + m - 1)) (y (k0 + m)) (y (k0 + m + 1)) (p (k0 + m)) (q (k0 + m))
        (s (k0 + m)) δ Sg Qq hδ hδ1 hSg hQ (hrec _ hk) (hσ _ hk) (hq _ hk)
      have e : k0 + ((m + 1 : ℕ) : ℤ) = k0 + m + 1 := by push_cast; ring
      simp only [stateSize, e, add_sub_cancel_right] at this ⊢
      simpa [b] using this
    · have h1 : min (m + 1) M = M := by omega
      have h2 : min m M = M := by omega
      simp only [u, h1, h2]
      have := stateSize_nonneg y δ hδ (k0 + (M : ℤ))
      have hb : 0 ≤ b m := by simp only [b]; positivity
      nlinarith [mul_nonneg (mul_nonneg hL0 hδ.le) this]
  have hc : ∀ m ≥ 0, 0 ≤ L * δ := fun _ _ => by positivity
  have hb : ∀ m ≥ 0, 0 ≤ b m := fun m _ => by simp only [b]; positivity
  have hu0 : 0 ≤ u 0 := by simp only [u]; exact stateSize_nonneg y δ hδ _
  have key := discrete_gronwall (u := u) (b := b) (c := fun _ => L * δ) (n₀ := 0) hu0 hu hc hb
    (n := n) (Nat.zero_le n)
  have hnM : n ≤ M := by omega
  have e1 : u n = stateSize y δ (k0 + n) := by simp only [u, min_eq_left hnM]
  have e0 : u 0 = stateSize y δ k0 := by simp [u]
  rw [e1, e0] at key
  have hs : ∑ k ∈ Ico 0 n, b k = ∑ i ∈ range n, (1 + 1 / δ) * |s (k0 + i)| := by
    rw [← range_eq_Ico]
  have hs2 : ∑ i ∈ Ico 0 n, (fun _ : ℕ => L * δ) i = L * δ * n := by
    rw [sum_const, Nat.card_Ico]; simp [mul_comm]
  rw [hs, hs2] at key
  have : L * δ * n = (1 + 2 * Sg + 2 * Qq) * δ * n := by rw [hL]
  rwa [this] at key

/-- The reflection `y'(m) = y (-m)`, `a'(m) = a (1-m)`, `c'(m) = c (-m)` carries rows to rows:
`jac a' c' y' m = jac a c y (-m)`. -/
lemma jac_reflect (a c y : ℤ → ℝ) (m : ℤ) :
    jac (fun i => a (1 - i)) (fun i => c (-i)) (fun i => y (-i)) m = jac a c y (-m) := by
  have e1 : 1 - (m + 1) = -m := by ring
  have e2 : -(m + 1) = -m - 1 := by ring
  have e3 : -(m - 1) = -m + 1 := by ring
  have e4 : 1 - m = -m + 1 := by ring
  simp only [jac, e1, e2, e3, e4]; ring

lemma jac_sub (a c y z : ℤ → ℝ) (k : ℤ) :
    jac a c (fun i => y i - z i) k = jac a c y k - jac a c z k := by
  simp only [jac]; ring

/-- **Bounded-window difference bound** (upward).  `d` with `jac a c d k = r k` on `Ico k0 K`; `a ≥ m > 0` on
`Icc k0 K`; `|c k - a k - a (k+1)| ≤ Sg' δ²` and `|a (k+1) - a k| ≤ Qq' δ²` on `Ico k0 K`; `|r k| ≤ ρ`;
`0 < δ ≤ 1`.  Then for `k ∈ Icc k0 K`,
`|d k| + |d k - d (k-1)|/δ ≤ (|d k0| + |d k0 - d (k0-1)|/δ + 2 (K-k0) ρ/(δ m)) · exp (L δ (K-k0))`,
`L = 1 + 2 (Sg' + Qq')/m`. -/
theorem jacobi_difference_bound (a c d r : ℤ → ℝ) (δ m Sg' Qq' ρ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hSg : 0 ≤ Sg') (hQ : 0 ≤ Qq') (hρ : 0 ≤ ρ) (k0 K : ℤ)
    (hrow : ∀ k ∈ Ico k0 K, jac a c d k = r k) (ha : ∀ k ∈ Icc k0 K, m ≤ a k)
    (hc : ∀ k ∈ Ico k0 K, |c k - a k - a (k + 1)| ≤ Sg' * δ ^ 2)
    (ha' : ∀ k ∈ Ico k0 K, |a (k + 1) - a k| ≤ Qq' * δ ^ 2) (hr : ∀ k ∈ Ico k0 K, |r k| ≤ ρ) :
    ∀ k ∈ Icc k0 K, |d k| + |d k - d (k - 1)| / δ ≤
      (|d k0| + |d k0 - d (k0 - 1)| / δ + 2 * ((K - k0 : ℤ) : ℝ) * ρ / (δ * m)) *
        exp ((1 + 2 * (Sg' + Qq') / m) * δ * ((K - k0 : ℤ) : ℝ)) := by
  intro k hk
  rw [mem_Icc] at hk
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = k0 + n := ⟨(k - k0).toNat, by omega⟩
  have hakp : ∀ k ∈ Ico k0 K, m ≤ a k ∧ m ≤ a (k + 1) := fun k hk => by
    simp only [mem_Ico] at hk
    exact ⟨ha k (by simp only [mem_Icc]; omega), ha (k + 1) (by simp only [mem_Icc]; omega)⟩
  have hδ2 : δ ^ 2 ≤ δ := by nlinarith
  have key := three_term_bound d (fun k => c k / a (k + 1)) (fun k => -a k / a (k + 1))
    (fun k => r k / a (k + 1)) δ (Sg' / m) (Qq' / m) hδ hδ1 (by positivity) (by positivity) k0 K
    (fun k hk => by
      obtain ⟨h1, h2⟩ := hakp k hk
      have hp : a (k + 1) ≠ 0 := by linarith
      have := hrow k hk
      simp only [jac] at this
      field_simp
      linarith)
    (fun k hk => by
      obtain ⟨h1, h2⟩ := hakp k hk
      have hp : 0 < a (k + 1) := by linarith
      have e : c k / a (k + 1) + -a k / a (k + 1) - 1 = (c k - a k - a (k + 1)) / a (k + 1) := by
        field_simp
        ring
      rw [e, abs_div, abs_of_pos hp, div_le_iff₀ hp]
      have := hc k hk
      calc |c k - a k - a (k + 1)| ≤ Sg' * δ ^ 2 := this
        _ ≤ Sg' / m * δ ^ 2 * a (k + 1) := by
          have : Sg' * δ ^ 2 = Sg' / m * δ ^ 2 * m := by field_simp
          rw [this]
          gcongr)
    (fun k hk => by
      obtain ⟨h1, h2⟩ := hakp k hk
      have hp : 0 < a (k + 1) := by linarith
      have h0 : 0 < a k := by linarith
      rw [abs_div, abs_neg, abs_of_pos h0, abs_of_pos hp, div_le_iff₀ hp]
      have := (abs_le.mp (ha' k hk)).1
      have hh : Qq' * δ ^ 2 ≤ Qq' / m * δ * a (k + 1) := by
        have e : Qq' * δ ^ 2 = Qq' / m * δ * (δ * m) := by field_simp
        rw [e]
        have : δ * m ≤ a (k + 1) := by nlinarith
        gcongr
      nlinarith)
    n (by omega)
  have hk' : k = k0 + n := hn
  subst hk'
  refine key.trans ?_
  have hnK : (n : ℝ) ≤ ((K - k0 : ℤ) : ℝ) := by exact_mod_cast (by omega : (n : ℤ) ≤ K - k0)
  have hsum : ∑ i ∈ range n, (1 + 1 / δ) * |r (k0 + i) / a (k0 + i + 1)| ≤
      ((K - k0 : ℤ) : ℝ) * (2 * ρ / (δ * m)) := by
    have hterm : ∀ i ∈ range n, (1 + 1 / δ) * |r (k0 + i) / a (k0 + i + 1)| ≤ 2 * ρ / (δ * m) := by
      intro i hi
      rw [mem_range] at hi
      have hk : k0 + (i : ℤ) ∈ Ico k0 K := by simp only [mem_Ico]; omega
      obtain ⟨h1, h2⟩ := hakp _ hk
      have hp : 0 < a (k0 + i + 1) := by linarith
      rw [abs_div, abs_of_pos hp]
      have hr' := hr _ hk
      have h1δ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
      calc (1 + 1 / δ) * (|r (k0 + i)| / a (k0 + i + 1)) ≤ (2 * (1 / δ)) * (ρ / m) := by
            have : |r (k0 + i)| / a (k0 + i + 1) ≤ ρ / m := by
              calc |r (k0 + i)| / a (k0 + i + 1) ≤ ρ / a (k0 + i + 1) := by gcongr
                _ ≤ ρ / m := by gcongr
            have h3 : 1 + 1 / δ ≤ 2 * (1 / δ) := by linarith
            have h4 : 0 ≤ |r (k0 + i)| / a (k0 + i + 1) := by positivity
            calc (1 + 1 / δ) * (|r (k0 + i)| / a (k0 + i + 1))
                ≤ (2 * (1 / δ)) * (|r (k0 + i)| / a (k0 + i + 1)) := by gcongr
              _ ≤ (2 * (1 / δ)) * (ρ / m) := by gcongr
        _ = 2 * ρ / (δ * m) := by field_simp
    calc _ ≤ ∑ i ∈ range n, 2 * ρ / (δ * m) := sum_le_sum hterm
      _ = n * (2 * ρ / (δ * m)) := by simp
      _ ≤ _ := by gcongr
  have hL : 0 ≤ (1 + 2 * (Sg' + Qq') / m) * δ := by positivity
  have hexp : exp ((1 + 2 * (Sg' / m) + 2 * (Qq' / m)) * δ * n) ≤
      exp ((1 + 2 * (Sg' + Qq') / m) * δ * ((K - k0 : ℤ) : ℝ)) := by
    apply exp_le_exp.mpr
    have e : (1 + 2 * (Sg' / m) + 2 * (Qq' / m)) = 1 + 2 * (Sg' + Qq') / m := by ring
    rw [e]; gcongr
  have hnn : 0 ≤ stateSize d δ k0 + ∑ i ∈ range n, (1 + 1 / δ) * |r (k0 + i) / a (k0 + i + 1)| := by
    have := stateSize_nonneg d δ hδ k0
    have : 0 ≤ ∑ i ∈ range n, (1 + 1 / δ) * |r (k0 + i) / a (k0 + i + 1)| := by positivity
    linarith
  calc _ ≤ (stateSize d δ k0 + ∑ i ∈ range n, (1 + 1 / δ) * |r (k0 + i) / a (k0 + i + 1)|) *
        exp ((1 + 2 * (Sg' + Qq') / m) * δ * ((K - k0 : ℤ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hexp hnn
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        simp only [stateSize]
        have : 2 * ((K - k0 : ℤ) : ℝ) * ρ / (δ * m) = ((K - k0 : ℤ) : ℝ) * (2 * ρ / (δ * m)) := by ring
        rw [this]
        linarith

/-- **Bounded-window difference bound, downward** (the direction of the window `X ∈ [-A0, -1]`, `X_k`
increasing with `k`): `d` with `jac a c d k = r k` on `Ioc J K`, `a ≥ m` on `Icc (J+1) (K+1)`, the same defect
hypotheses on `Ioc J K`.  Marching from the two top sites `K, K+1` down to `J`: for `k ∈ Icc J K`,
`|d k| + |d k - d (k+1)|/δ ≤ (|d K| + |d K - d (K+1)|/δ + 2 (K-J) ρ/(δ m)) · exp (L δ (K-J))`. -/
theorem jacobi_difference_bound_down (a c d r : ℤ → ℝ) (δ m Sg' Qq' ρ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hSg : 0 ≤ Sg') (hQ : 0 ≤ Qq') (hρ : 0 ≤ ρ) (J K : ℤ)
    (hrow : ∀ k ∈ Ioc J K, jac a c d k = r k) (ha : ∀ k ∈ Icc (J + 1) (K + 1), m ≤ a k)
    (hc : ∀ k ∈ Ioc J K, |c k - a k - a (k + 1)| ≤ Sg' * δ ^ 2)
    (ha' : ∀ k ∈ Ioc J K, |a (k + 1) - a k| ≤ Qq' * δ ^ 2) (hr : ∀ k ∈ Ioc J K, |r k| ≤ ρ) :
    ∀ k ∈ Icc J K, |d k| + |d k - d (k + 1)| / δ ≤
      (|d K| + |d K - d (K + 1)| / δ + 2 * ((K - J : ℤ) : ℝ) * ρ / (δ * m)) *
        exp ((1 + 2 * (Sg' + Qq') / m) * δ * ((K - J : ℤ) : ℝ)) := by
  intro k hk
  rw [mem_Icc] at hk
  have key := jacobi_difference_bound (fun i => a (1 - i)) (fun i => c (-i)) (fun i => d (-i))
    (fun i => r (-i)) δ m Sg' Qq' ρ hδ hδ1 hm hSg hQ hρ (-K) (-J)
    (fun i hi => by
      rw [mem_Ico] at hi
      rw [jac_reflect]
      exact hrow (-i) (by simp only [mem_Ioc]; omega))
    (fun i hi => by
      rw [mem_Icc] at hi
      exact ha (1 - i) (by simp only [mem_Icc]; omega))
    (fun i hi => by
      rw [mem_Ico] at hi
      have h := hc (-i) (by simp only [mem_Ioc]; omega)
      have e1 : 1 - (i + 1) = -i := by ring
      have e2 : -i + 1 = 1 - i := by ring
      rw [e2] at h
      show |c (-i) - a (1 - i) - a (1 - (i + 1))| ≤ _
      rw [e1, show c (-i) - a (1 - i) - a (-i) = c (-i) - a (-i) - a (1 - i) by ring]; exact h)
    (fun i hi => by
      rw [mem_Ico] at hi
      have h := ha' (-i) (by simp only [mem_Ioc]; omega)
      have e1 : 1 - (i + 1) = -i := by ring
      have e2 : -i + 1 = 1 - i := by ring
      rw [e2] at h
      show |a (1 - (i + 1)) - a (1 - i)| ≤ _
      rw [e1, abs_sub_comm]; exact h)
    (fun i hi => by
      rw [mem_Ico] at hi
      exact hr (-i) (by simp only [mem_Ioc]; omega)) (-k) (by simp only [mem_Icc]; omega)
  have e0 : -(-k) = k := by ring
  have e1 : -(-k - 1) = k + 1 := by ring
  have e2 : -(-K) = K := by ring
  have e3 : -(-K - 1) = K + 1 := by ring
  have e4 : (-J - -K : ℤ) = K - J := by ring
  simp only [e0, e1, e2, e3, e4] at key
  exact key

/-- **Two exact solutions with different right-hand sides** (upward): `jac a c y k = r1 k`,
`jac a c z k = r2 k` on `Ico k0 K`, `|r1 - r2| ≤ ρ`: the difference `d = y - z` satisfies
`jacobi_difference_bound` (initial data in the first term), so in particular
`|y k - z k| ≤ (|d k0| + |d k0 - d (k0-1)|/δ + 2 (K-k0) ρ/(δ m)) exp (L δ (K-k0))`. -/
theorem jacobi_solutions_bound (a c y z r1 r2 : ℤ → ℝ) (δ m Sg' Qq' ρ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hSg : 0 ≤ Sg') (hQ : 0 ≤ Qq') (hρ : 0 ≤ ρ) (k0 K : ℤ)
    (hy : ∀ k ∈ Ico k0 K, jac a c y k = r1 k) (hz : ∀ k ∈ Ico k0 K, jac a c z k = r2 k)
    (ha : ∀ k ∈ Icc k0 K, m ≤ a k)
    (hc : ∀ k ∈ Ico k0 K, |c k - a k - a (k + 1)| ≤ Sg' * δ ^ 2)
    (ha' : ∀ k ∈ Ico k0 K, |a (k + 1) - a k| ≤ Qq' * δ ^ 2) (hr : ∀ k ∈ Ico k0 K, |r1 k - r2 k| ≤ ρ) :
    ∀ k ∈ Icc k0 K, |y k - z k| ≤
      (|y k0 - z k0| + |(y k0 - z k0) - (y (k0 - 1) - z (k0 - 1))| / δ + 2 * ((K - k0 : ℤ) : ℝ) * ρ / (δ * m)) *
        exp ((1 + 2 * (Sg' + Qq') / m) * δ * ((K - k0 : ℤ) : ℝ)) := by
  intro k hk
  have := jacobi_difference_bound a c (fun i => y i - z i) (fun i => r1 i - r2 i) δ m Sg' Qq' ρ hδ hδ1 hm
    hSg hQ hρ k0 K (fun k hk => by rw [jac_sub, hy k hk, hz k hk]) ha hc ha' hr k hk
  beta_reduce at this
  exact le_trans (by linarith [div_nonneg (abs_nonneg ((y k - z k) - (y (k - 1) - z (k - 1)))) hδ.le]) this

/-- Downward version of `jacobi_solutions_bound` (marching from the sites `K, K+1` down to `J`). -/
theorem jacobi_solutions_bound_down (a c y z r1 r2 : ℤ → ℝ) (δ m Sg' Qq' ρ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hm : 0 < m) (hSg : 0 ≤ Sg') (hQ : 0 ≤ Qq') (hρ : 0 ≤ ρ) (J K : ℤ)
    (hy : ∀ k ∈ Ioc J K, jac a c y k = r1 k) (hz : ∀ k ∈ Ioc J K, jac a c z k = r2 k)
    (ha : ∀ k ∈ Icc (J + 1) (K + 1), m ≤ a k)
    (hc : ∀ k ∈ Ioc J K, |c k - a k - a (k + 1)| ≤ Sg' * δ ^ 2)
    (ha' : ∀ k ∈ Ioc J K, |a (k + 1) - a k| ≤ Qq' * δ ^ 2) (hr : ∀ k ∈ Ioc J K, |r1 k - r2 k| ≤ ρ) :
    ∀ k ∈ Icc J K, |y k - z k| ≤
      (|y K - z K| + |(y K - z K) - (y (K + 1) - z (K + 1))| / δ + 2 * ((K - J : ℤ) : ℝ) * ρ / (δ * m)) *
        exp ((1 + 2 * (Sg' + Qq') / m) * δ * ((K - J : ℤ) : ℝ)) := by
  intro k hk
  have := jacobi_difference_bound_down a c (fun i => y i - z i) (fun i => r1 i - r2 i) δ m Sg' Qq' ρ hδ hδ1
    hm hSg hQ hρ J K (fun k hk => by rw [jac_sub, hy k hk, hz k hk]) ha hc ha' hr k hk
  beta_reduce at this
  exact le_trans (by linarith [div_nonneg (abs_nonneg ((y k - z k) - (y (k + 1) - z (k + 1)))) hδ.le]) this

/-- info: 'FormalResearch.DiscreteAiry.step_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.step_bound

/-- info: 'FormalResearch.DiscreteAiry.three_term_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.three_term_bound

/-- info: 'FormalResearch.DiscreteAiry.jacobi_difference_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.jacobi_difference_bound

/-- info: 'FormalResearch.DiscreteAiry.jacobi_difference_bound_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.jacobi_difference_bound_down

/-- info: 'FormalResearch.DiscreteAiry.jacobi_solutions_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.jacobi_solutions_bound

/-- info: 'FormalResearch.DiscreteAiry.jacobi_solutions_bound_down' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.jacobi_solutions_bound_down

end FormalResearch.DiscreteAiry

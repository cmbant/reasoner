module

public import FormalResearch.Special.DiscreteJacobiCalculusComparison
public import FormalResearch.Racah.P3JacobiComparison

/-!
# Discrete Jacobi calculus V: the hard-edge bridge `ℕ → ℤ` and the recessive-selection input

Airy-free glue between the `ℕ`-indexed hard-edge chain of Weyl P3 (`Racah.P3.backward_ratio`,
`prop:forbidden-decay`, A:1337-1349) and the `ℤ`-sequence calculus of `DiscreteJacobiCalculus{,Comparison}`
(`jac`, `cas`, `recessive_selection`).  Read against A:1105-1131 and A:1160: the physical solution `Y` of the
chain with `A_{N+1} = 0` is `κ f1 + μ f2` (`exists_combination`), and the *selection* `|μ| ≤ C |κ| |f1/f2|`
(`recessive_selection`) needs `|Y k1| ≤ |Y k0|` at two nodes: this is supplied by the backward ratio with
`y = 1` (exact hyperbolicity `A_i + A_{i+1} ≤ c_i`).

Statements (all **proved**; the ratio inequality itself is `backward_ratio`, nothing is re-derived; a mpmath
sanity run on a random hard-edge chain checked `|Y_{i+1}| ≤ |Y_i|` and the sign of `Y_i Y_N`):

* `backward_ratio_int`: `backward_ratio` for `ℤ`-sequences `a c y` with window `Icc j N`, `1 ≤ j ≤ N`,
  `a > 0` on `Icc j N`, `a (N+1) = 0`, `y N ≠ 0`, constant-ratio supersolution
  `a (k+1) r + a k / r ≤ c k`, and `jac a c y k = 0` on `Icc j N`: for `k ∈ Icc (j-1) N`,
  `y k * y N > 0` and `|y (k+1)| ≤ r |y k|` for `k < N`.
* `natExt`, `natExt_natCast`, `jac_natExt`: extension `ℕ → ℤ` (`natExt f k = f k.toNat`; the values at
  negative `k` are irrelevant for the windows used, which sit in `k ≥ j - 1 ≥ 0`), with
  `jac (natExt A) (natExt c) (natExt Y) i = A_{i+1}Y_{i+1} + A_iY_{i-1} - c_iY_i` for `i ≥ 1`.
* `hardEdge_toInt`: the `ℕ` hard-edge hypotheses of `backward_ratio` give the `ℤ` ones: `a > 0` on `Icc j N`,
  `a (N+1) = 0`, the rows on `Icc j N`; and `hardEdge_window`: the rows on the **reduced window**
  `Icc j (N-1)` together with `a ≠ 0` on `Icc j N`, which is the form to which `eq_zero_of_two_values`,
  `green_final`, `exists_combination`, `existsUnique_final_solution` apply.
  (Why the window stops at `N - 1`: the Casoratian across the bond `(N, N+1)` is `a (N+1) (…) = 0` because of
  the hard edge, so the hard-edge solution space is one-dimensional; the rows `j..N-1`, with final data
  `(y (N-1), y N)` and `a ≠ 0` up to `N`, form an ordinary final-value window.  Row `N` is the boundary
  condition `a N y (N-1) = c N y N`.)
* `hardEdge_abs_le_pow`, `hardEdge_abs_antitone`: `|y k1| ≤ r^(k1-k0) |y k0|` for `j-1 ≤ k0 ≤ k1 ≤ N`, and for
  `r = 1` (exact hyperbolicity `a (k+1) + a k ≤ c k`) `|y k1| ≤ |y k0|`; `hardEdge_ne_zero`.
* `recessive_selection_hardEdge`: for a hard-edge solution `y` with exact hyperbolicity and `y = κ f1 + μ f2` at
  two nodes `j-1 ≤ k0 ≤ k1 ≤ N` (`f1` non-increasing in modulus, `f2` growing by `λ > 1`), the hypothesis `hmono`
  of `recessive_selection` is discharged: `|μ| ≤ (2/(λ-1)) |κ| |f1 k0|/|f2 k0|`, and `κ ≠ 0`
  (`kappa_ne_zero_hardEdge`).  `recessive_selection_hardEdge_nat` is the same for `ℕ`-indexed data `A c Y`.

**Not formalised** here: the Airy-side inputs (`f1`, `f2`, the growth `λ = 3` of `Bi`, the exact solution
`f1` near the parametrix), the bound `|Ŷ| ≤ C N^m` at the end, and the exact hyperbolicity of the Hahn/Racah
chains (that is `Racah.P3.exact_hyperbolicity_hahn_racah`).
-/

@[expose] public section

open Finset

namespace FormalResearch.DiscreteAiry

/-- **Hard-edge backward ratio for `ℤ`-sequences** (`Racah.P3.backward_ratio` in the calculus' conventions).
Window `Icc j N` with `1 ≤ j ≤ N`; `a > 0` on `Icc j N`, `a (N+1) = 0` (hard edge: the forward term of the
last row vanishes), `y N ≠ 0`, constant-ratio supersolution `a (k+1) r + a k / r ≤ c k` (`r > 0`) and
`jac a c y k = 0` on `Icc j N`.  Then for `k ∈ Icc (j-1) N`: `y k * y N > 0` and, for `k < N`,
`|y (k+1)| ≤ r |y k|`. -/
theorem backward_ratio_int (a c y : ℤ → ℝ) (j N : ℤ) (r : ℝ) (hr : 0 < r) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ha : ∀ k ∈ Icc j N, 0 < a k) (hend : a (N + 1) = 0)
    (hsup : ∀ k ∈ Icc j N, a (k + 1) * r + a k / r ≤ c k)
    (hrow : ∀ k ∈ Icc j N, jac a c y k = 0) (hyN : y N ≠ 0) :
    ∀ k ∈ Icc (j - 1) N, 0 < y k * y N ∧ (k < N → |y (k + 1)| ≤ r * |y k|) := by
  have hjc : ((j.toNat : ℕ) : ℤ) = j := by omega
  have hNc : ((N.toNat : ℕ) : ℤ) = N := by omega
  have key := FormalResearch.Racah.P3.backward_ratio (fun n : ℕ => a n) (fun n : ℕ => c n)
    (fun n : ℕ => y n) j.toNat N.toNat r hr (by omega) (by omega)
    (fun i h1 h2 => ha i (by simp only [mem_Icc]; omega))
    (by simp only [Nat.cast_add, Nat.cast_one]; rw [hNc]; exact hend)
    (fun i h1 h2 => by
      have := hsup i (by simp only [mem_Icc]; omega)
      simpa using this)
    (fun i h1 h2 => by
      have h := hrow i (by simp only [mem_Icc]; omega)
      simp only [jac] at h
      have e : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
      simp only [Nat.cast_add, Nat.cast_one, e]
      linarith)
    (by simpa [hNc] using hyN)
  intro k hk
  rw [mem_Icc] at hk
  have hk0 : (k.toNat : ℤ) = k := by omega
  have := key k.toNat (by omega) (by omega)
  simp only [hk0, hNc] at this
  refine ⟨this.1, fun hkN => ?_⟩
  have h2 := this.2 (by omega)
  simpa [hk0] using h2

/-- Extension of an `ℕ`-sequence to `ℤ` (`k ↦ f k.toNat`; negative sites carry `f 0`, irrelevant for the
windows `k ≥ j - 1 ≥ 0` used here). -/
def natExt (f : ℕ → ℝ) : ℤ → ℝ := fun k => f k.toNat

lemma natExt_natCast (f : ℕ → ℝ) (n : ℕ) : natExt f (n : ℤ) = f n := by simp [natExt]

/-- The `ℤ` row operator of the extensions is the `ℕ` row `A_{i+1}Y_{i+1} + A_iY_{i-1} - c_iY_i` (`i ≥ 1`). -/
lemma jac_natExt (A c Y : ℕ → ℝ) (i : ℕ) (hi : 1 ≤ i) :
    jac (natExt A) (natExt c) (natExt Y) (i : ℤ) = A (i + 1) * Y (i + 1) + A i * Y (i - 1) - c i * Y i := by
  have e : (((i : ℤ) - 1).toNat : ℕ) = i - 1 := by omega
  simp [jac, natExt, e]

/-- **The `ℕ` hard-edge hypotheses of `backward_ratio` give the `ℤ` ones** for `natExt`: `a > 0` on `Icc j N`,
`a (N+1) = 0`, and the rows on `Icc j N`. -/
theorem hardEdge_toInt (A c Y : ℕ → ℝ) (j N : ℕ) (hj : 1 ≤ j)
    (hA : ∀ i, j ≤ i → i ≤ N → 0 < A i) (hend : A (N + 1) = 0)
    (hrow : ∀ i, j ≤ i → i ≤ N → A (i + 1) * Y (i + 1) + A i * Y (i - 1) = c i * Y i) :
    (∀ k ∈ Icc (j : ℤ) N, 0 < natExt A k) ∧ natExt A ((N : ℤ) + 1) = 0 ∧
      (∀ k ∈ Icc (j : ℤ) N, jac (natExt A) (natExt c) (natExt Y) k = 0) := by
  refine ⟨fun k hk => ?_, ?_, fun k hk => ?_⟩
  · rw [mem_Icc] at hk
    have : (k.toNat : ℤ) = k := by omega
    simp only [natExt]; exact hA _ (by omega) (by omega)
  · have : ((N : ℤ) + 1).toNat = N + 1 := by omega
    simp [natExt, this, hend]
  · rw [mem_Icc] at hk
    obtain ⟨i, rfl⟩ : ∃ i : ℕ, k = i := ⟨k.toNat, by omega⟩
    rw [jac_natExt A c Y i (by omega)]
    have := hrow i (by omega) (by omega)
    linarith

/-- **The reduced window** of a hard-edge chain: rows `Icc j (N-1)` of the `ℤ`-extension vanish and
`a ≠ 0` on `Icc j ((N-1)+1) = Icc j N` (`N ≥ j + 1`), which is the hypothesis format of
`eq_zero_of_two_values`, `eq_of_final_values`, `green_final`, `exists_combination` with last row `N - 1`. -/
theorem hardEdge_window (A c Y : ℕ → ℝ) (j N : ℕ) (hj : 1 ≤ j)
    (hA : ∀ i, j ≤ i → i ≤ N → 0 < A i) (hend : A (N + 1) = 0)
    (hrow : ∀ i, j ≤ i → i ≤ N → A (i + 1) * Y (i + 1) + A i * Y (i - 1) = c i * Y i) :
    (∀ k ∈ Icc (j : ℤ) ((N : ℤ) - 1), jac (natExt A) (natExt c) (natExt Y) k = 0) ∧
      (∀ k ∈ Icc (j : ℤ) (((N : ℤ) - 1) + 1), natExt A k ≠ 0) := by
  obtain ⟨h1, -, h3⟩ := hardEdge_toInt A c Y j N hj hA hend hrow
  refine ⟨fun k hk => h3 k (by simp only [mem_Icc] at hk ⊢; omega), fun k hk => ?_⟩
  exact (h1 k (by simp only [mem_Icc] at hk ⊢; omega)).ne'

/-- Iterated ratio bound: `|y k1| ≤ r^(k1-k0) |y k0|` for `j-1 ≤ k0 ≤ k1 ≤ N`. -/
theorem hardEdge_abs_le_pow (a c y : ℤ → ℝ) (j N : ℤ) (r : ℝ) (hr : 0 < r) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ha : ∀ k ∈ Icc j N, 0 < a k) (hend : a (N + 1) = 0)
    (hsup : ∀ k ∈ Icc j N, a (k + 1) * r + a k / r ≤ c k)
    (hrow : ∀ k ∈ Icc j N, jac a c y k = 0) (hyN : y N ≠ 0) (k0 k1 : ℤ) (h0 : j - 1 ≤ k0)
    (h01 : k0 ≤ k1) (h1 : k1 ≤ N) : |y k1| ≤ r ^ (k1 - k0).toNat * |y k0| := by
  have H := backward_ratio_int a c y j N r hr hj hjN ha hend hsup hrow hyN
  have key : ∀ n : ℕ, k0 + n ≤ N → |y (k0 + n)| ≤ r ^ n * |y k0| := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      have h2 := ih (by omega)
      have h3 := (H (k0 + n) (by simp only [mem_Icc]; omega)).2 (by omega)
      have e : k0 + ((n + 1 : ℕ) : ℤ) = k0 + n + 1 := by push_cast; ring
      rw [e, pow_succ]
      calc |y (k0 + n + 1)| ≤ r * |y (k0 + n)| := h3
        _ ≤ r * (r ^ n * |y k0|) := by gcongr
        _ = _ := by ring
  have := key (k1 - k0).toNat (by omega)
  have e : k0 + ((k1 - k0).toNat : ℤ) = k1 := by omega
  rwa [e] at this

/-- **Monotone decay of `|y|` from exact hyperbolicity** (`r = 1`: `a (k+1) + a k ≤ c k`):
`|y k1| ≤ |y k0|` for `j - 1 ≤ k0 ≤ k1 ≤ N`; this is the hypothesis `hmono` of `recessive_selection`. -/
theorem hardEdge_abs_antitone (a c y : ℤ → ℝ) (j N : ℤ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ha : ∀ k ∈ Icc j N, 0 < a k) (hend : a (N + 1) = 0)
    (hhyp : ∀ k ∈ Icc j N, a (k + 1) + a k ≤ c k)
    (hrow : ∀ k ∈ Icc j N, jac a c y k = 0) (hyN : y N ≠ 0) (k0 k1 : ℤ) (h0 : j - 1 ≤ k0)
    (h01 : k0 ≤ k1) (h1 : k1 ≤ N) : |y k1| ≤ |y k0| := by
  have := hardEdge_abs_le_pow a c y j N 1 one_pos hj hjN ha hend
    (fun k hk => by simpa using hhyp k hk) hrow hyN k0 k1 h0 h01 h1
  simpa using this

/-- Under the hard-edge hypotheses `y k ≠ 0` on `Icc (j-1) N` (all `y k` have the sign of `y N`). -/
theorem hardEdge_ne_zero (a c y : ℤ → ℝ) (j N : ℤ) (r : ℝ) (hr : 0 < r) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ha : ∀ k ∈ Icc j N, 0 < a k) (hend : a (N + 1) = 0)
    (hsup : ∀ k ∈ Icc j N, a (k + 1) * r + a k / r ≤ c k)
    (hrow : ∀ k ∈ Icc j N, jac a c y k = 0) (hyN : y N ≠ 0) (k : ℤ) (hk : k ∈ Icc (j - 1) N) :
    y k ≠ 0 := by
  have := (backward_ratio_int a c y j N r hr hj hjN ha hend hsup hrow hyN k hk).1
  intro h; rw [h] at this; simp at this

/-- **Recessive selection for a hard-edge solution** (A:1160): the exact hyperbolicity supplies `hmono`.
`y` a hard-edge solution (`a > 0` on `Icc j N`, `a (N+1) = 0`, `a (k+1) + a k ≤ c k`, `y N ≠ 0`) with
`y = κ f1 + μ f2` at `k0 ≤ k1` in `Icc (j-1) N`, `|f1 k1| ≤ |f1 k0|`, `λ |f2 k0| ≤ |f2 k1|`, `λ > 1`,
`f2 k0 ≠ 0`: `|μ| ≤ (2/(λ-1)) |κ| (|f1 k0| / |f2 k0|)`. -/
theorem recessive_selection_hardEdge (a c y f1 f2 : ℤ → ℝ) (j N : ℤ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ha : ∀ k ∈ Icc j N, 0 < a k) (hend : a (N + 1) = 0)
    (hhyp : ∀ k ∈ Icc j N, a (k + 1) + a k ≤ c k)
    (hrow : ∀ k ∈ Icc j N, jac a c y k = 0) (hyN : y N ≠ 0) (κ μ lam : ℝ) (k0 k1 : ℤ)
    (h0 : j - 1 ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ N)
    (e0 : y k0 = κ * f1 k0 + μ * f2 k0) (e1 : y k1 = κ * f1 k1 + μ * f2 k1)
    (hlam : 1 < lam) (hgrow : lam * |f2 k0| ≤ |f2 k1|) (hdec : |f1 k1| ≤ |f1 k0|)
    (hpos : 0 < |f2 k0|) :
    |μ| ≤ 2 / (lam - 1) * (|κ| * (|f1 k0| / |f2 k0|)) :=
  recessive_selection f1 f2 y κ μ lam k0 k1 e0 e1
    (hardEdge_abs_antitone a c y j N hj hjN ha hend hhyp hrow hyN k0 k1 h0 h01 h1) hlam hgrow hdec hpos

/-- In the same situation `κ ≠ 0` (the physical solution has a nonzero recessive component), since
`y k0 ≠ 0` by the sign statement of the backward ratio. -/
theorem kappa_ne_zero_hardEdge (a c y f1 f2 : ℤ → ℝ) (j N : ℤ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (ha : ∀ k ∈ Icc j N, 0 < a k) (hend : a (N + 1) = 0)
    (hhyp : ∀ k ∈ Icc j N, a (k + 1) + a k ≤ c k)
    (hrow : ∀ k ∈ Icc j N, jac a c y k = 0) (hyN : y N ≠ 0) (κ μ lam : ℝ) (k0 k1 : ℤ)
    (h0 : j - 1 ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ N)
    (e0 : y k0 = κ * f1 k0 + μ * f2 k0) (e1 : y k1 = κ * f1 k1 + μ * f2 k1)
    (hlam : 1 < lam) (hgrow : lam * |f2 k0| ≤ |f2 k1|) (hpos : 0 < |f2 k0|) : κ ≠ 0 :=
  kappa_ne_zero f1 f2 y κ μ lam k0 k1 e0 e1
    (hardEdge_abs_antitone a c y j N hj hjN ha hend hhyp hrow hyN k0 k1 h0 h01 h1) hlam hgrow hpos
    (hardEdge_ne_zero a c y j N 1 one_pos hj hjN ha hend (fun k hk => by simpa using hhyp k hk) hrow hyN k0
      (by simp only [mem_Icc]; omega))

/-- `recessive_selection_hardEdge` for the `ℕ`-indexed hard-edge chain `A c Y` of P3 (hypotheses exactly those
of `Racah.P3.backward_ratio` with `y = 1`, i.e. exact hyperbolicity `A_i + A_{i+1} ≤ c_i`), the solution being
`natExt Y`. -/
theorem recessive_selection_hardEdge_nat (A c Y : ℕ → ℝ) (j N : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N)
    (hA : ∀ i, j ≤ i → i ≤ N → 0 < A i) (hend : A (N + 1) = 0)
    (hhyp : ∀ i, j ≤ i → i ≤ N → A i + A (i + 1) ≤ c i)
    (hrow : ∀ i, j ≤ i → i ≤ N → A (i + 1) * Y (i + 1) + A i * Y (i - 1) = c i * Y i)
    (hYN : Y N ≠ 0) (f1 f2 : ℤ → ℝ) (κ μ lam : ℝ) (k0 k1 : ℤ)
    (h0 : (j : ℤ) - 1 ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ N)
    (e0 : natExt Y k0 = κ * f1 k0 + μ * f2 k0) (e1 : natExt Y k1 = κ * f1 k1 + μ * f2 k1)
    (hlam : 1 < lam) (hgrow : lam * |f2 k0| ≤ |f2 k1|) (hdec : |f1 k1| ≤ |f1 k0|)
    (hpos : 0 < |f2 k0|) :
    |μ| ≤ 2 / (lam - 1) * (|κ| * (|f1 k0| / |f2 k0|)) := by
  obtain ⟨h1', h2', h3'⟩ := hardEdge_toInt A c Y j N hj hA hend hrow
  refine recessive_selection_hardEdge (natExt A) (natExt c) (natExt Y) f1 f2 j N (by exact_mod_cast hj)
    (by exact_mod_cast hjN) h1' h2' (fun k hk => ?_) h3' (by simpa [natExt] using hYN) κ μ lam k0 k1 h0
    h01 h1 e0 e1 hlam hgrow hdec hpos
  rw [mem_Icc] at hk
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, k = i := ⟨k.toNat, by omega⟩
  have e : ((i : ℤ) + 1).toNat = i + 1 := by omega
  have := hhyp i (by omega) (by omega)
  simp only [natExt, e, Int.toNat_natCast]
  linarith

/-- info: 'FormalResearch.DiscreteAiry.backward_ratio_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.backward_ratio_int

/-- info: 'FormalResearch.DiscreteAiry.hardEdge_toInt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.hardEdge_toInt

/-- info: 'FormalResearch.DiscreteAiry.hardEdge_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.hardEdge_window

/-- info: 'FormalResearch.DiscreteAiry.hardEdge_abs_antitone' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.hardEdge_abs_antitone

/-- info: 'FormalResearch.DiscreteAiry.recessive_selection_hardEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.recessive_selection_hardEdge

/-- info: 'FormalResearch.DiscreteAiry.kappa_ne_zero_hardEdge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.kappa_ne_zero_hardEdge

/-- info: 'FormalResearch.DiscreteAiry.recessive_selection_hardEdge_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.recessive_selection_hardEdge_nat

end FormalResearch.DiscreteAiry

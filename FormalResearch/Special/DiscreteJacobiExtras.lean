module

public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# Discrete Jacobi calculus IV: existence of final-value solutions

Airy-free gap-filler for the discrete-to-Airy chain (M5/M6 of the D2A plan).  `DiscreteJacobiCalculus` proves
*uniqueness* of the final-value problem (`eq_of_final_values`); this module proves the matching **existence**
by backward recursion, so that "the exact solution `f1` with `f1 = ψ` at the last two sites" (A:1105,
`lem:airy2-recessive`; W1 est:291) is available without a second input function.

The row `k`,
`a (k+1) y (k+1) + a k y (k-1) - c k y k = r k`,
is solved for `y (k-1)`; this needs `a k ≠ 0`, and `k` runs from `N` down to `lo`, so the only nonvanishing
hypothesis is **`a k ≠ 0` for `k ∈ Icc lo N`** (the coefficient `a (N+1)` multiplies the *prescribed* value
`y (N+1)` and may vanish; for uniqueness one needs `a ≠ 0` on `Icc lo (N+1)`, see `existsUnique_final_solution`).

Statements (all **proved**, exact; mpmath 30-digit sanity run of the backward recursion on random data with
residual `4e-31`):

* `finalSol a c r u v N`: the explicit backward-recursive sequence (`finalSol .. N = u`, `finalSol .. (N+1) = v`);
* `exists_final_solution`: for `a k ≠ 0` on `Icc lo N` there is `y` with `jac a c y k = r k` on `Icc lo N`,
  `y N = u`, `y (N+1) = v` (the explicit `finalSol`);
* `exists_final_solution_hom`: the homogeneous case (`r = 0`): a solution with *chosen final data*
  (the "recessive-style" solution `f1` with `f1 = ψ` at the last two sites: take `u = ψ N`, `v = ψ (N+1)`);
* `existsUnique_final_solution`: with `a ≠ 0` on `Icc lo (N+1)` (and `lo ≤ N`) the solution is unique on
  `Icc (lo-1) (N+1)`; and `exists_exact_near`: `f` with `jac f = 0` and `f = ψ` at `N, N+1`, together with the
  identification `f = ψ + e` where `e` solves `jac e = - jac ψ` with vanishing final data (the shape used in
  `prop:airy2-exact`, A:1130).

**Not formalised** here: any positivity/size information on the constructed solution (that is the content of
the Volterra bound `volterra_contract` and of the hard-edge comparison `DiscreteJacobiExtrasHardEdge`), and the
existence for `ℕ`-indexed chains beyond what the `ℤ`-window statements give.
-/

@[expose] public section

open Finset

namespace FormalResearch.DiscreteAiry

/-- The backward recursion in the index `n = N + 1 - k`:
`w 0 = v`, `w 1 = u`, `w (n+2) = (r (N-n) - a (N-n+1) w n + c (N-n) w (n+1)) / a (N-n)`. -/
noncomputable def backSeq (a c r : ℤ → ℝ) (u v : ℝ) (N : ℤ) : ℕ → ℝ
  | 0 => v
  | 1 => u
  | (n + 2) => (r (N - n) - a (N - n + 1) * backSeq a c r u v N n
      + c (N - n) * backSeq a c r u v N (n + 1)) / a (N - n)

/-- **The final-value solution**: `finalSol a c r u v N k = backSeq .. (N+1-k)` for `k ≤ N+1` (and `0` above). -/
noncomputable def finalSol (a c r : ℤ → ℝ) (u v : ℝ) (N : ℤ) (k : ℤ) : ℝ :=
  if k ≤ N + 1 then backSeq a c r u v N (N + 1 - k).toNat else 0

lemma finalSol_succ_site (a c r : ℤ → ℝ) (u v : ℝ) (N k : ℤ) (hk : k ≤ N + 1) :
    finalSol a c r u v N k = backSeq a c r u v N (N + 1 - k).toNat := by
  simp [finalSol, hk]

lemma finalSol_N1 (a c r : ℤ → ℝ) (u v : ℝ) (N : ℤ) : finalSol a c r u v N (N + 1) = v := by
  simp [finalSol, backSeq]

lemma finalSol_N (a c r : ℤ → ℝ) (u v : ℝ) (N : ℤ) : finalSol a c r u v N N = u := by
  simp [finalSol, backSeq]

/-- The row `k ≤ N` of `finalSol` holds whenever `a k ≠ 0`. -/
theorem jac_finalSol (a c r : ℤ → ℝ) (u v : ℝ) (N k : ℤ) (hk : k ≤ N) (hak : a k ≠ 0) :
    jac a c (finalSol a c r u v N) k = r k := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, k = N - n := ⟨(N - k).toNat, by omega⟩
  have e1 : finalSol a c r u v N (k + 1) = backSeq a c r u v N n := by
    rw [finalSol_succ_site _ _ _ _ _ _ _ (by omega)]
    congr 1; omega
  have e0 : finalSol a c r u v N k = backSeq a c r u v N (n + 1) := by
    rw [finalSol_succ_site _ _ _ _ _ _ _ (by omega)]
    congr 1; omega
  have em : finalSol a c r u v N (k - 1) = backSeq a c r u v N (n + 2) := by
    rw [finalSol_succ_site _ _ _ _ _ _ _ (by omega)]
    congr 1; omega
  simp only [jac]
  rw [e1, e0, em, backSeq]
  subst hn
  field_simp
  ring

/-- **Existence of final-value solutions** (backward recursion).  If `a k ≠ 0` for `k ∈ Icc lo N` there is a
sequence `y` with `jac a c y k = r k` for `k ∈ Icc lo N` and the prescribed final values `y N = u`,
`y (N+1) = v`. -/
theorem exists_final_solution (a c r : ℤ → ℝ) (lo N : ℤ) (u v : ℝ) (ha : ∀ k ∈ Icc lo N, a k ≠ 0) :
    ∃ y : ℤ → ℝ, (∀ k ∈ Icc lo N, jac a c y k = r k) ∧ y N = u ∧ y (N + 1) = v :=
  ⟨finalSol a c r u v N, fun k hk => by
    rw [mem_Icc] at hk
    exact jac_finalSol a c r u v N k hk.2 (ha k (mem_Icc.mpr hk)),
    finalSol_N .., finalSol_N1 ..⟩

/-- Homogeneous case: a solution of `jac a c f = 0` on `Icc lo N` with **chosen final data** `f N = u`,
`f (N+1) = v` (the exact "recessive-style" solution `f1` of `lem:airy2-recessive`, once `u, v` are the values of
the parametrix at the last two sites). -/
theorem exists_final_solution_hom (a c : ℤ → ℝ) (lo N : ℤ) (u v : ℝ) (ha : ∀ k ∈ Icc lo N, a k ≠ 0) :
    ∃ f : ℤ → ℝ, (∀ k ∈ Icc lo N, jac a c f k = 0) ∧ f N = u ∧ f (N + 1) = v :=
  exists_final_solution a c (fun _ => 0) lo N u v ha

/-- Existence and uniqueness: for `lo ≤ N` and `a ≠ 0` on `Icc lo (N+1)` the final-value problem has a solution
on `Icc (lo-1) (N+1)` and any two solutions agree there. -/
theorem existsUnique_final_solution (a c r : ℤ → ℝ) (lo N : ℤ) (hlo : lo ≤ N) (u v : ℝ)
    (ha : ∀ k ∈ Icc lo (N + 1), a k ≠ 0) :
    ∃ y : ℤ → ℝ, (∀ k ∈ Icc lo N, jac a c y k = r k) ∧ y N = u ∧ y (N + 1) = v ∧
      ∀ z : ℤ → ℝ, (∀ k ∈ Icc lo N, jac a c z k = r k) → z N = u → z (N + 1) = v →
        ∀ k ∈ Icc (lo - 1) (N + 1), z k = y k := by
  obtain ⟨y, hy, hyN, hyN1⟩ := exists_final_solution a c r lo N u v
    (fun k hk => ha k (by simp only [mem_Icc] at hk ⊢; omega))
  refine ⟨y, hy, hyN, hyN1, fun z hz hzN hzN1 k hk => ?_⟩
  exact eq_of_final_values a c z y r lo N hlo hz hy ha (by rw [hzN, hyN]) (by rw [hzN1, hyN1]) k hk

/-- **Exact solution with prescribed final data and its defect form** (the shape of `prop:airy2-exact`):
for any sequence `ψ`, there is an exact solution `f` of `jac a c f = 0` on `Icc lo N` with `f = ψ` at
`N, N+1`, and `f - ψ` solves `jac e = - jac ψ` on `Icc lo N` with vanishing final data. -/
theorem exists_exact_near (a c ψ : ℤ → ℝ) (lo N : ℤ) (ha : ∀ k ∈ Icc lo N, a k ≠ 0) :
    ∃ f : ℤ → ℝ, (∀ k ∈ Icc lo N, jac a c f k = 0) ∧ f N = ψ N ∧ f (N + 1) = ψ (N + 1) ∧
      (∀ k ∈ Icc lo N, jac a c (fun i => f i - ψ i) k = - jac a c ψ k) ∧
      (fun i => f i - ψ i) N = 0 ∧ (fun i => f i - ψ i) (N + 1) = 0 := by
  obtain ⟨f, hf, hfN, hfN1⟩ := exists_final_solution_hom a c lo N (ψ N) (ψ (N + 1)) ha
  refine ⟨f, hf, hfN, hfN1, fun k hk => ?_, by simp [hfN], by simp [hfN1]⟩
  have := hf k hk
  simp only [jac] at this ⊢
  linarith

/-- info: 'FormalResearch.DiscreteAiry.exists_final_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.exists_final_solution

/-- info: 'FormalResearch.DiscreteAiry.exists_final_solution_hom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.exists_final_solution_hom

/-- info: 'FormalResearch.DiscreteAiry.existsUnique_final_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.existsUnique_final_solution

/-- info: 'FormalResearch.DiscreteAiry.exists_exact_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.exists_exact_near

end FormalResearch.DiscreteAiry

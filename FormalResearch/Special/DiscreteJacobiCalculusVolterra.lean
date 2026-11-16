module

public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# Discrete Jacobi calculus II: reduction of order, final-value Volterra form, contraction

Source: Weyl/P3 appendices `lem:airy2-recessive`(i) (A:1105-1135) and the same step in W1
`app:airy` (est:255-282).  Everything here is exact, with explicit constants, and Airy-free.

Let `ψ` be a nowhere-zero comparison sequence (the paper has `ψ > 0`, which is not needed) and `y = ψ (1 + σ)`.
With `D k = a (k+1) ψ k ψ (k+1) (σ (k+1) - σ k)`:

* `reduction_identity`: `D k - D (k-1) = ψ k * jac y k - ψ k * (1 + σ k) * jac ψ k` (for any `y`, `σ` related by
  `y = ψ(1+σ)` at `k-1, k, k+1`); for a solution `y` this is `D k - D (k-1) = - ψ k * jac ψ k * (1 + σ k)`
  (A:1114-1118).
* `volterra_final`: if `y` solves rows `m+1..N` and `σ N = σ (N+1) = 0` (`y = ψ` at the last two sites), then
  `σ k = - Σ_{i ∈ (k, N]} K k i (1 + σ i)` with the kernel
  `K k i = jac ψ i * Σ_{j ∈ [k, i)} ψ i / (a (j+1) ψ j ψ (j+1))` (A:1119, `volterraK`).
* `contraction_sup`: a sup-norm contraction lemma on finite windows (`|σ k| ≤ R + Σ_i |κ k i| |σ i|`, row sums
  `≤ q < 1` ⇒ `|σ| ≤ R/(1-q)`).
* `reduction_of_order_bound`: combined, `Σ_i |K k i| ≤ q < 1` for all `k` ⇒ `|σ| ≤ q/(1-q)`, i.e.
  `|y k - ψ k| ≤ q/(1-q) |ψ k|` (the abstract content of `lem:airy2-recessive`(i); the estimates
  `|K| ≤ C h^{5/3}(1+X⁺)^{-1/2}` giving `q ≤ C h` are Airy-specific and live elsewhere).

**Not formalised** here: the existence direction (a solution `σ` of the Volterra equation gives a solution
`y`; it is not needed for the bound; note that the existence of the exact final-value solution `y` by backward
recursion, given `a ≠ 0`, is not stated here either), and every Airy-specific
bound on `K`.
-/

@[expose] public section

open Finset

namespace FormalResearch.DiscreteAiry

/-- The reduction-of-order flux `D k = a (k+1) ψ k ψ (k+1) (σ (k+1) - σ k)`. -/
def redD (a ψ σ : ℤ → ℝ) (k : ℤ) : ℝ := a (k + 1) * ψ k * ψ (k + 1) * (σ (k + 1) - σ k)

/-- **Reduction of order identity** (A:1114): if `y = ψ (1+σ)` at `k-1, k, k+1`, then
`D k - D (k-1) = ψ k * jac y k - ψ k * (1 + σ k) * jac ψ k`. -/
theorem reduction_identity (a c ψ σ y : ℤ → ℝ) (k : ℤ) (h0 : y (k - 1) = ψ (k - 1) * (1 + σ (k - 1)))
    (h1 : y k = ψ k * (1 + σ k)) (h2 : y (k + 1) = ψ (k + 1) * (1 + σ (k + 1))) :
    redD a ψ σ k - redD a ψ σ (k - 1) = ψ k * jac a c y k - ψ k * (1 + σ k) * jac a c ψ k := by
  simp only [redD, jac, sub_add_cancel, h0, h1, h2]; ring

/-- The final-value Volterra kernel `K k i = jac ψ i * Σ_{j ∈ [k,i)} ψ i / (a (j+1) ψ j ψ (j+1))`. -/
noncomputable def volterraK (a c ψ : ℤ → ℝ) (k i : ℤ) : ℝ :=
  jac a c ψ i * ∑ j ∈ Ico k i, ψ i / (a (j + 1) * ψ j * ψ (j + 1))

/-- Downward induction on an integer window. -/
lemma int_down_induction {P : ℤ → Prop} (m N : ℤ) (hN : P N) (step : ∀ k, m < k → k ≤ N → P k → P (k - 1)) :
    ∀ k, m ≤ k → k ≤ N → P k := by
  have key : ∀ n : ℕ, ∀ k : ℤ, k + n = N → m ≤ k → P k := by
    intro n
    induction n with
    | zero => intro k hk _; have : k = N := by omega
              rw [this]; exact hN
    | succ n ih =>
      intro k hk hm
      have := step (k + 1) (by omega) (by omega) (ih (k + 1) (by omega) (by omega))
      simpa using this
  intro k hk hkN
  exact key (N - k).toNat k (by omega) hk

/-- **Final-value Volterra form** (A:1119).  Let `ψ` be nonzero on `Icc m (N+1)`, `a ≠ 0` on
`Icc (m+1) (N+1)`, `y` a solution of rows `m+1..N`, `y = ψ (1 + σ)` on `Icc m (N+1)` and `σ N = σ (N+1) = 0`.
Then for every `k ∈ Icc m (N+1)`: `σ k = - Σ_{i ∈ (k, N]} K k i (1 + σ i)`. -/
theorem volterra_final (a c ψ σ y : ℤ → ℝ) (m N : ℤ) (hψ : ∀ k ∈ Icc m (N + 1), ψ k ≠ 0)
    (ha : ∀ k ∈ Icc (m + 1) (N + 1), a k ≠ 0) (hrow : ∀ k ∈ Icc (m + 1) N, jac a c y k = 0)
    (hy : ∀ k ∈ Icc m (N + 1), y k = ψ k * (1 + σ k)) (hσN : σ N = 0) (hσN1 : σ (N + 1) = 0) :
    ∀ k ∈ Icc m (N + 1), σ k = - ∑ i ∈ Ioc k N, volterraK a c ψ k i * (1 + σ i) := by
  by_cases hmN : m ≤ N + 1
  swap
  · intro k hk; rw [mem_Icc] at hk; omega
  -- step 1: flux formula
  have hD : ∀ k, m ≤ k → k ≤ N → redD a ψ σ k = ∑ i ∈ Ioc k N, ψ i * jac a c ψ i * (1 + σ i) := by
    apply int_down_induction (P := fun k => redD a ψ σ k = ∑ i ∈ Ioc k N, ψ i * jac a c ψ i * (1 + σ i))
    · simp [redD, hσN, hσN1]
    · intro k hmk hkN hk
      have hid := reduction_identity a c ψ σ y k
        (hy (k - 1) (by simp only [mem_Icc]; omega)) (hy k (by simp only [mem_Icc]; omega))
        (hy (k + 1) (by simp only [mem_Icc]; omega))
      rw [hrow k (by simp only [mem_Icc]; omega)] at hid
      have hI : Ioc (k - 1) N = insert k (Ioc k N) := by
        ext i; simp only [mem_Ioc, mem_insert]; omega
      rw [hI, Finset.sum_insert (by simp), ← hk]
      simp only [mul_zero] at hid
      linarith
  intro k hk
  rw [mem_Icc] at hk
  -- step 2: sum over the flux
  apply int_down_induction (P := fun k => σ k = - ∑ i ∈ Ioc k N, volterraK a c ψ k i * (1 + σ i)) m (N + 1)
    _ _ k hk.1 hk.2
  · simp [hσN1]
  · intro k hmk hkN hk
    by_cases hkN1 : k = N + 1
    · subst hkN1
      simp [hσN]
    have hk1 : k - 1 ∈ Icc m N := by simp only [mem_Icc]; omega
    rw [mem_Icc] at hk1
    have hDk := hD (k - 1) hk1.1 hk1.2
    have hak : a k ≠ 0 := ha k (by simp only [mem_Icc]; omega)
    have hp0 : ψ (k - 1) ≠ 0 := hψ _ (by simp only [mem_Icc]; omega)
    have hp1 : ψ k ≠ 0 := hψ _ (by simp only [mem_Icc]; omega)
    have hdiff : σ (k - 1) = σ k - redD a ψ σ (k - 1) / (a k * ψ (k - 1) * ψ k) := by
      simp only [redD, sub_add_cancel]
      field_simp
      ring
    have hI : Ioc (k - 1) N = insert k (Ioc k N) := by
      ext i; simp only [mem_Ioc, mem_insert]; omega
    have hKk : volterraK a c ψ k k = 0 := by simp [volterraK]
    have hKs : ∀ i ∈ Ioc (k - 1) N, volterraK a c ψ (k - 1) i =
        volterraK a c ψ k i + jac a c ψ i * (ψ i / (a k * ψ (k - 1) * ψ k)) := by
      intro i hi
      rw [mem_Ioc] at hi
      have hJ : Ico (k - 1) i = insert (k - 1) (Ico k i) := by
        ext j; simp only [mem_Ico, mem_insert]; omega
      unfold volterraK
      rw [hJ, Finset.sum_insert (by simp)]
      simp only [sub_add_cancel]
      ring
    have hKsum : ∑ i ∈ Ioc (k - 1) N, volterraK a c ψ k i * (1 + σ i) =
        ∑ i ∈ Ioc k N, volterraK a c ψ k i * (1 + σ i) := by
      rw [hI, Finset.sum_insert (by simp), hKk]; ring
    have hmain : ∑ i ∈ Ioc (k - 1) N, volterraK a c ψ (k - 1) i * (1 + σ i) =
        ∑ i ∈ Ioc (k - 1) N, volterraK a c ψ k i * (1 + σ i) +
          (∑ i ∈ Ioc (k - 1) N, ψ i * jac a c ψ i * (1 + σ i)) / (a k * ψ (k - 1) * ψ k) := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hKs i hi]
      field_simp
    rw [hmain, hKsum, hdiff, hDk, hk]
    ring

/-- `Σ_i |K k i| ≤ q < 1` window contraction in sup-norm form: if `|σ k| ≤ R + Σ_{i ∈ T k} |κ k i| |σ i|` on
the finite set `s`, `T k ⊆ s` and the row sums `Σ_{i ∈ T k} |κ k i| ≤ q < 1`, then `|σ k| ≤ R / (1 - q)`. -/
theorem contraction_sup (s : Finset ℤ) (T : ℤ → Finset ℤ) (κ : ℤ → ℤ → ℝ) (σ : ℤ → ℝ) (R q : ℝ)
    (hq : q < 1) (hT : ∀ k ∈ s, T k ⊆ s) (hκ : ∀ k ∈ s, ∑ i ∈ T k, |κ k i| ≤ q)
    (hσ : ∀ k ∈ s, |σ k| ≤ R + ∑ i ∈ T k, |κ k i| * |σ i|) : ∀ k ∈ s, |σ k| ≤ R / (1 - q) := by
  intro k hk
  have hne : s.Nonempty := ⟨k, hk⟩
  obtain ⟨k0, hk0, hmax⟩ := Finset.exists_max_image s (fun i => |σ i|) hne
  have hM : 0 ≤ |σ k0| := abs_nonneg _
  have h1 : |σ k0| ≤ R + q * |σ k0| := by
    refine (hσ k0 hk0).trans ?_
    have : ∑ i ∈ T k0, |κ k0 i| * |σ i| ≤ ∑ i ∈ T k0, |κ k0 i| * |σ k0| :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmax i (hT k0 hk0 hi)) (abs_nonneg _))
    rw [← Finset.sum_mul] at this
    have := mul_le_mul_of_nonneg_right (hκ k0 hk0) hM
    linarith
  have h2 : |σ k0| ≤ R / (1 - q) := by
    rw [le_div_iff₀ (by linarith)]; nlinarith
  exact (hmax k hk).trans h2

/-- **Abstract `lem:airy2-recessive`(i)**: if `Σ_{i ∈ (k,N]} |K k i| ≤ q < 1` for `k ∈ Icc m N` (`K = volterraK`),
then (for `0 ≤ q`) the relative error `σ` of the exact solution `y = ψ(1+σ)` (equal to `ψ` at `N, N+1`) is bounded by
`q / (1 - q)`: `|y k - ψ k| ≤ q/(1-q) |ψ k|` on `Icc m (N+1)`. -/
theorem reduction_of_order_bound (a c ψ σ y : ℤ → ℝ) (m N : ℤ) (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1)
    (hψ : ∀ k ∈ Icc m (N + 1), ψ k ≠ 0) (ha : ∀ k ∈ Icc (m + 1) (N + 1), a k ≠ 0)
    (hrow : ∀ k ∈ Icc (m + 1) N, jac a c y k = 0) (hy : ∀ k ∈ Icc m (N + 1), y k = ψ k * (1 + σ k))
    (hσN : σ N = 0) (hσN1 : σ (N + 1) = 0)
    (hK : ∀ k ∈ Icc m N, ∑ i ∈ Ioc k N, |volterraK a c ψ k i| ≤ q) :
    ∀ k ∈ Icc m (N + 1), |σ k| ≤ q / (1 - q) ∧ |y k - ψ k| ≤ q / (1 - q) * |ψ k| := by
  have hV := volterra_final a c ψ σ y m N hψ ha hrow hy hσN hσN1
  have hsup : ∀ k ∈ Icc m N, |σ k| ≤ q / (1 - q) := by
    apply contraction_sup (Icc m N) (fun k => Ioc k N) (volterraK a c ψ) σ q q hq
    · intro k hk; rw [mem_Icc] at hk; intro i hi; rw [mem_Ioc] at hi; simp only [mem_Icc]; omega
    · exact hK
    · intro k hk
      have hk' : k ∈ Icc m (N + 1) := by rw [mem_Icc] at hk ⊢; omega
      have h := hV k hk'
      have : σ k = - ∑ i ∈ Ioc k N, (volterraK a c ψ k i + volterraK a c ψ k i * σ i) := by
        rw [h]; congr 1; apply Finset.sum_congr rfl; intros; ring
      rw [this, Finset.sum_add_distrib, abs_neg]
      refine (abs_add_le _ _).trans ?_
      have e1 : |∑ i ∈ Ioc k N, volterraK a c ψ k i| ≤ q :=
        (Finset.abs_sum_le_sum_abs _ _).trans (hK k hk)
      have e2 : |∑ i ∈ Ioc k N, volterraK a c ψ k i * σ i| ≤ ∑ i ∈ Ioc k N, |volterraK a c ψ k i| * |σ i| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl (fun i _ => abs_mul _ _)
      linarith
  have hq0' : 0 ≤ q / (1 - q) := div_nonneg hq0 (by linarith)
  intro k hk
  rw [mem_Icc] at hk
  have hs : |σ k| ≤ q / (1 - q) := by
    by_cases hkN : k ≤ N
    · exact hsup k (by simp only [mem_Icc]; omega)
    · have : k = N + 1 := by omega
      subst this; rw [hσN1]; simpa using hq0'
  refine ⟨hs, ?_⟩
  have : y k - ψ k = ψ k * σ k := by rw [hy k (by simp only [mem_Icc]; omega)]; ring
  rw [this, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hs (abs_nonneg _) |>.trans (le_of_eq (by ring))

/-- info: 'FormalResearch.DiscreteAiry.reduction_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.reduction_identity

/-- info: 'FormalResearch.DiscreteAiry.volterra_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.volterra_final

/-- info: 'FormalResearch.DiscreteAiry.contraction_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.contraction_sup

/-- info: 'FormalResearch.DiscreteAiry.reduction_of_order_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.DiscreteAiry.reduction_of_order_bound

end FormalResearch.DiscreteAiry

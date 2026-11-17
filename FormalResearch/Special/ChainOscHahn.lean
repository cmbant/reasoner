module

public import FormalResearch.Special.ChainOscNodal
public import FormalResearch.Special.DiscreteAiryLimitChains3j

/-!
# Chain oscillation, part 3: the physical `3j` chain is a Jacobi eigenvector with `K - 1 - n` nodes

For integers `M, σ` with `kmin = max |M| |σ| ≥ 1` and `N = kmin + m + 1` (so the physical chain
lives on `k = kmin, …, N - 1`, `K = m + 1` sites), the natural-gauge `3j` chain
`Ŷ_k = hahn3jY M σ N x_n k` at the lattice node `x_n = xLat M σ N n` (`n ≤ m`) is an eigenvector of the
`(m+1) × (m+1)` Jacobi matrix with links `A_k = hrAk 1 0 M σ (1/N) k` (positive for `kmin < k < N`)
and diagonal `B_k = hrB`, with eigenvalue `x_n` (`hahn_class_chain`, whose end rows `A_kmin = 0`,
`A_N = 0` make the truncation exact).  The `m + 1` lattice nodes are distinct eigenvalues
(`Ŷ ≠ 0` by the Gauss weight identity `gaussWeight_3j`), hence they are the whole spectrum, in
ascending order, and by the nodal Sturm theorem (`cho_eigen_ascending`):

* `cho_hahn_nodes` : the number of nodes of `Ŷ_{kmin}, …, Ŷ_{N-1}` at `x_n` is exactly `m - n`
  (the number of sign changes, an interior zero counting as one).

The chain is *not* gauge twisted (`τ = +1`, `u ≡ 1`), and the statement holds for every node, also
`x_n < 0` (the `τ = -1` chain of the bulk theorems is `(-1)^k Ŷ_k`, whose sign changes are the
non-changes of `Ŷ`; its count is `kmin`-free but not stated here).

Sanity check (not part of the proof): mpmath, 30 digits, the matrix with these `A_k`, `B_k` for
`(M, σ, N) = (1,0,9), (2,1,12), (1,-1,10), (2,-2,11), (3,1,14)`: all eigenvalues equal `xLat n` to `1e-30`
and the `n`-th eigenvector has exactly `m - n` sign changes for every `n`.

Claim class: proved.  Not formalised: `kmin = 0` (`M = σ = 0`; the row `k = 0` is not part of
`hahn_class_chain`), the half-integer lattice and the Racah (`6j`) chain, and the comparison of the
node count with the Airy phase (identification of the Bohr-Sommerfeld integer with the zero index).
-/

@[expose] public section

namespace FormalResearch.Special

open FormalResearch.Jacobi FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry Finset Matrix

/-- A strictly increasing list contained in a strictly increasing list of the same length coincides. -/
theorem cho_index_id (m : ℕ) (θ x : ℕ → ℝ) (hθ : ∀ i j, i < j → j ≤ m → θ i < θ j)
    (hx : ∀ i j, i < j → j ≤ m → x i < x j)
    (hmem : ∀ i, i ≤ m → ∃ l, l ≤ m ∧ θ l = x i) : ∀ i, i ≤ m → θ i = x i := by
  choose! f hf1 hf2 using hmem
  have hmono : ∀ i j, i < j → j ≤ m → f i < f j := by
    intro i j hij hj
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have := hθ _ _ hlt (hf1 i (by omega)); rw [hf2 i (by omega), hf2 j hj] at this
      have := hx _ _ hij hj; linarith
    · have h1 := hf2 i (by omega); have h2 := hf2 j hj
      rw [heq] at h2; have := hx _ _ hij hj; linarith
  have hge : ∀ i, i ≤ m → i ≤ f i := by
    intro i
    induction i with
    | zero => intro _; omega
    | succ i ih =>
      intro hi
      have := ih (by omega); have := hmono i (i + 1) (by omega) hi; omega
  have hle : ∀ d i, i + d ≤ m → f i + d ≤ f (i + d) := by
    intro d
    induction d with
    | zero => intro i _; simp
    | succ d ih =>
      intro i hi
      have h1 := ih i (by omega)
      have h2 := hmono (i + d) (i + d + 1) (by omega) (by omega)
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [e]; omega
  intro i hi
  have h1 := hle (m - i) i (by omega)
  have h2 := hf1 (i + (m - i)) (by omega)
  have h3 := hge i hi
  have hfi : f i = i := by omega
  rw [← hf2 i hi, hfi]

section Hahn

variable (M σ N : ℤ)

/-- The off-diagonal of the chain's Jacobi matrix: `a_i = A_{kmin+i+1}` joins the sites `i, i+1`. -/
noncomputable def cho_aJ (i : ℕ) : ℝ :=
  hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) (max |M| |σ| + (i : ℤ) + 1)

/-- The diagonal of the chain's Jacobi matrix: `b_i = B_{kmin+i}`. -/
noncomputable def cho_bJ (i : ℕ) : ℝ :=
  hrB (Real.sqrt (1 * 0)) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) ((max |M| |σ| + (i : ℤ) : ℤ) : ℝ)

variable {M σ N}

theorem cho_aJ_pos {m : ℕ} (hlo : 1 ≤ max |M| |σ|) (hm : N = max |M| |σ| + m + 1) {i : ℕ}
    (hi : i < m) : 0 < cho_aJ M σ N i := by
  unfold cho_aJ hrAk
  set k : ℤ := max |M| |σ| + (i : ℤ) + 1 with hk
  have hkM : |M| < k := by have := le_max_left |M| |σ|; omega
  have hkS : |σ| < k := by have := le_max_right |M| |σ|; omega
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : (1 : ℤ) ≤ k)
  have hkN : (k : ℝ) < N := by exact_mod_cast (by omega : k < N)
  have hk0 : (0 : ℝ) < k := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hMr : (M : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    have : |(M : ℝ)| < k := by exact_mod_cast hkM
    nlinarith [sq_abs (M : ℝ), abs_nonneg (M : ℝ)]
  have hSr : (σ : ℝ) ^ 2 < (k : ℝ) ^ 2 := by
    have : |(σ : ℝ)| < k := by exact_mod_cast hkS
    nlinarith [sq_abs (σ : ℝ), abs_nonneg (σ : ℝ)]
  have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have r1 : 0 < 1 - (M : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_one hk2]; exact hMr
  have r2 : 0 < 1 - (σ : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
    rw [sub_pos, div_lt_one hk2]; exact hSr
  have r3 : 0 < 1 - 1 / (4 * (k : ℝ) ^ 2) := by
    have : 1 / (4 * (k : ℝ) ^ 2) < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hrr : 0 < rr (M : ℝ) (σ : ℝ) (k : ℝ) := by
    unfold rr; exact Real.sqrt_pos.2 (div_pos (mul_pos r1 r2) r3)
  have het : 0 < etilde 1 0 (((k : ℝ) * (1 / (N : ℝ))) ^ 2) := by
    rw [etilde_hahn]
    apply Real.sqrt_pos.2
    have : (k : ℝ) * (1 / (N : ℝ)) < 1 := by
      rw [mul_one_div, div_lt_one hN0]; exact hkN
    have h0 : 0 ≤ (k : ℝ) * (1 / (N : ℝ)) := by positivity
    nlinarith
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hrr) het

/-- The chain vector on the sites `kmin, …, N - 1`. -/
noncomputable def cho_vec (M σ N : ℤ) (x : ℚ) (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => hahn3jY M σ N x (max |M| |σ| + ((i : ℕ) : ℤ))

theorem cho_vec_ext {m : ℕ} (hm : N = max |M| |σ| + m + 1) (x : ℚ) {i : ℕ} (hi : i ≤ m + 1) :
    extVec (cho_vec M σ N x m) i = hahn3jY M σ N x (max |M| |σ| + (i : ℤ)) := by
  rcases Nat.lt_or_ge i (m + 1) with h | h
  · rw [extVec_of_lt _ h]; rfl
  · have : i = m + 1 := by omega
    subst this
    rw [extVec_of_ge _ le_rfl]
    symm
    apply hahn_chain_support
    intro ⟨_, _, h3⟩
    push_cast at h3
    omega

/-- **The `3j` chain is a Jacobi eigenvector**: `J v = x v`. -/
theorem cho_hahn_eigen {m : ℕ} (hlo : 1 ≤ max |M| |σ|) (hm : N = max |M| |σ| + m + 1) (x : ℚ) :
    jacobiMatrix (m + 1) (cho_bJ M σ N) (cho_aJ M σ N) *ᵥ cho_vec M σ N x m =
      (x : ℝ) • cho_vec M σ N x m := by
  funext i
  rw [jacobiMatrix_mulVec, Pi.smul_apply, smul_eq_mul]
  have hN0 : 0 < N := by omega
  have hrow := hahn_class_chain M σ N x hN0 (max |M| |σ| + ((i : ℕ) : ℤ)) (by omega)
  unfold jac at hrow
  unfold jacRow
  have h1 := cho_vec_ext hm x (i := (i : ℕ) + 1) (by omega)
  have h0 := cho_vec_ext hm x (i := (i : ℕ)) (by omega)
  have e3 : max |M| |σ| + (((i : ℕ) + 1 : ℕ) : ℤ) = max |M| |σ| + ((i : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e3] at h1
  rw [h1, h0]
  have hv : cho_vec M σ N x m i = hahn3jY M σ N x (max |M| |σ| + ((i : ℕ) : ℤ)) := rfl
  rw [hv]
  unfold hrCk at hrow
  unfold cho_bJ cho_aJ
  by_cases hi0 : (i : ℕ) = 0
  · rw [hi0] at hrow ⊢
    have hend := hahn_end_lower M σ (1 / (N : ℝ)) hlo
    simp only [Nat.cast_zero, add_zero] at hrow ⊢
    rw [hend] at hrow
    simp only [↓reduceIte]
    linear_combination hrow
  · have hi1 := cho_vec_ext hm x (i := (i : ℕ) - 1) (by omega)
    have e : max |M| |σ| + (((i : ℕ) - 1 : ℕ) : ℤ) = max |M| |σ| + ((i : ℕ) : ℤ) - 1 := by omega
    rw [e] at hi1
    have e2 : max |M| |σ| + (((i : ℕ) - 1 : ℕ) : ℤ) + 1 = max |M| |σ| + ((i : ℕ) : ℤ) := by omega
    simp only [hi0, ↓reduceIte]
    rw [hi1, e2]
    linear_combination hrow


theorem cho_hahn_specAdm {m : ℕ} (hm : N = max |M| |σ| + m + 1) :
    SpecAdm (M : ℚ) (σ : ℚ) (N : ℚ) := by
  have h := (hahn_tri_iff (max |M| |σ|) M σ N).2 ⟨le_max_left _ _, le_max_right _ _, by omega⟩
  have e : ((max |M| |σ| : ℤ) : ℚ) = max |(M : ℚ)| |(σ : ℚ)| := by push_cast; rfl
  rw [e] at h
  exact h

/-- The chain vector at a lattice node is nonzero (Gauss weight identity `gaussWeight_3j`). -/
theorem cho_vec_ne_zero {m : ℕ} (hlo : 1 ≤ max |M| |σ|) (hm : N = max |M| |σ| + m + 1) {n : ℕ}
    (hn : n ≤ m) : cho_vec M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) m ≠ 0 := by
  intro h0
  have hA := cho_hahn_specAdm hm
  have hN : (0 : ℚ) < N := by have : (0 : ℤ) < N := by omega
                              exact_mod_cast this
  have e : ((max |M| |σ| : ℤ) : ℚ) = max |(M : ℚ)| |(σ : ℚ)| := by push_cast; rfl
  have hK : (((m + 1 : ℕ)) : ℚ) = N - max |(M : ℚ)| |(σ : ℚ)| := by
    rw [← e]
    have : ((m + 1 : ℕ) : ℤ) = N - max |M| |σ| := by push_cast; omega
    exact_mod_cast this
  have hg := (gaussWeight_3j hA hN hK (n := n) (by omega)).1
  unfold lambdaSq3j at hg
  have hz : ∑ i ∈ Finset.range (m + 1), (2 * ((max |(M : ℚ)| |(σ : ℚ)| + i : ℚ) : ℝ) + 1) *
      PhiX (max |(M : ℚ)| |(σ : ℚ)| + i) (M : ℚ) (σ : ℚ) (N : ℚ) (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hy := congrFun h0 ⟨i, hi'⟩
    simp only [cho_vec, Pi.zero_apply, hahn3jY] at hy
    have hpos : 0 < Real.sqrt (2 * (((max |M| |σ| + (i : ℤ) : ℤ) : ℚ) : ℝ) + 1) := by
      apply Real.sqrt_pos.2
      have : (0 : ℝ) ≤ (((max |M| |σ| + (i : ℤ) : ℤ) : ℚ) : ℝ) := by
        have : (0 : ℤ) ≤ max |M| |σ| + (i : ℤ) := by omega
        exact_mod_cast this
      linarith
    have hP := (mul_eq_zero.mp hy).resolve_left hpos.ne'
    have ec : (((max |M| |σ| + (i : ℤ) : ℤ)) : ℚ) = max |(M : ℚ)| |(σ : ℚ)| + i := by
      push_cast; rfl
    rw [ec] at hP
    rw [hP]; ring
  rw [hz] at hg
  have : (0 : ℝ) < ((N : ℚ) : ℝ) := by exact_mod_cast hN
  linarith

theorem cho_xLat_lt {N : ℤ} (hN : 0 < N) (M σ : ℤ) {i j : ℕ} (hij : i < j) :
    ((xLat (M : ℚ) (σ : ℚ) (N : ℚ) i : ℚ) : ℝ) < ((xLat (M : ℚ) (σ : ℚ) (N : ℚ) j : ℚ) : ℝ) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hij' : (i : ℝ) < j := by exact_mod_cast hij
  unfold xLat
  push_cast
  have : 2 * (i : ℝ) / N < 2 * (j : ℝ) / N := by
    apply div_lt_div_of_pos_right _ hN'; linarith
  linarith

/-- **Node count of the `3j` chain.**  For integers `M, σ` with `1 ≤ kmin = max |M| |σ|` and
`N = kmin + m + 1`, at the `n`-th lattice node `x_n = xLat M σ N n` (`n ≤ m`) the natural-gauge chain
`Ŷ_{kmin}, …, Ŷ_{N-1}` has exactly `m - n` nodes (sign changes; an interior zero counts as one). -/
theorem cho_hahn_nodes {m : ℕ} (hlo : 1 ≤ max |M| |σ|) (hm : N = max |M| |σ| + m + 1) {n : ℕ}
    (hn : n ≤ m) :
    cho_nodal (fun i : ℕ => hahn3jY M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) n) (max |M| |σ| + (i : ℤ))) m =
      m - n := by
  have hN0 : 0 < N := by omega
  obtain ⟨θ, hθ, hE, hnod⟩ := cho_eigen_ascending (b := cho_bJ M σ N) (a := cho_aJ M σ N) m
    (fun j hj => cho_aJ_pos hlo hm hj)
  have hmem : ∀ i, i ≤ m → ∃ l, l ≤ m ∧ θ l = ((xLat (M : ℚ) (σ : ℚ) (N : ℚ) i : ℚ) : ℝ) := by
    intro i hi
    rw [← hE]
    exact ⟨cho_vec M σ N (xLat (M : ℚ) (σ : ℚ) (N : ℚ) i) m, cho_vec_ne_zero hlo hm hi,
      cho_hahn_eigen hlo hm _⟩
  have hid := cho_index_id m θ (fun i => ((xLat (M : ℚ) (σ : ℚ) (N : ℚ) i : ℚ) : ℝ)) hθ
    (fun i j hij _ => cho_xLat_lt hN0 M σ hij) hmem n hn
  have h := hnod n hn _ (cho_vec_ne_zero hlo hm hn) (by rw [hid]; exact cho_hahn_eigen hlo hm _)
  rw [← h]
  unfold cho_nodal
  congr 1
  · apply congrArg
    apply filter_congr
    intro i hi
    have hi' := mem_range.mp hi
    rw [cho_vec_ext hm _ (by omega), cho_vec_ext hm _ (by omega)]
  · apply congrArg
    apply filter_congr
    intro i hi
    have hi' := mem_range.mp hi
    rw [cho_vec_ext hm _ (by omega)]

/-- info: 'FormalResearch.Special.cho_hahn_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cho_hahn_nodes

end Hahn

end FormalResearch.Special

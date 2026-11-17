module

public import FormalResearch.Special.RacahWindowTail
public import FormalResearch.Special.ChainOscNodal
public import FormalResearch.Special.ChainOscHahn

/-!
# Racah window, part 7: the physical `6j` chain is a Jacobi eigenvector with `c - c_min` nodes (integer data)

The Racah counterpart of `ChainOscHahn` (`cho_hahn_nodes`).  For a finite Racah system with integer labels `a, b, m, n` and `kmin = max |m| |n| ≥ 1`, `kmax = kmin + D' = min(2b+m, 2a+n)`,
the natural-gauge chains `Ŷ^{(c)}_k = racah6jY a b c m n k`, `k = kmin, …, kmax`, for the `D' + 1` lattice points `c = c_min + l` are eigenvectors, with the *same* `(D'+1) × (D'+1)` Jacobi matrix
(links `A_{kmin+i+1} = hrAk`, diagonal `B_{kmin+i} = hrB`, positive: `rw_aJ_pos`, `hr_Ak_pos`; the end rows `A_{kmin} = 0`, `A_{kmax+1} = 0`, `Ŷ_{kmax+1} = 0` make the truncation exact), for the
eigenvalues `x_l = cosA A B (c_l + 1/2)`, strictly decreasing in `l`, nonzero by the Gauss mass `rd_sum`.  These are `D' + 1` distinct eigenvalues of a `(D'+1)`-dimensional matrix, hence the whole
spectrum, and the nodal Sturm theorem (`cho_eigen_ascending`) gives:

* **`rw_chain_nodes`**: the chain at `c = c_min + l` has exactly `l` nodes (sign changes, an interior zero counting as one): the largest eigenvalue (`l = 0`) has none.

**Claim class: proved** (axiom guard pinned).  Numerics (mpmath, 40 digits, exact `6j` symbols from the Racah sum): the total number of nodes of the chain is `c - c_min` for all the chains
listed in `RacahWindowIndex` (`k = 5, …, 101`).  **Not formalised:** `kmin = 0`, half-integer data.  The twisted chain `(-1)^k Ŷ_k` (`τ = -1`) is `RacahWindowNodesNeg`.
-/

@[expose] public section

open Finset FormalResearch.Jacobi FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry Matrix
open scoped Real

namespace FormalResearch.Special

section Nodes

variable (P Q : ℝ) (m n : ℤ) (h : ℝ)

/-- The off-diagonal of the chain's Jacobi matrix: `a_i = A_{kmin+i+1}`. -/
noncomputable def rw_aJ (i : ℕ) : ℝ := hrAk P Q (m : ℝ) (n : ℝ) h (max |m| |n| + (i : ℤ) + 1)

/-- The diagonal of the chain's Jacobi matrix: `b_i = B_{kmin+i}`. -/
noncomputable def rw_bJ (i : ℕ) : ℝ := hrB (Real.sqrt (P * Q)) (m : ℝ) (n : ℝ) h (((max |m| |n| + (i : ℤ) : ℤ) : ℝ))

variable {P Q m n h}

/-- The chain vector on the sites `kmin, …, kmax`. -/
noncomputable def rw_vec (a b c m n : ℤ) (D' : ℕ) : Fin (D' + 1) → ℝ :=
  fun i => racah6jY a b c m n (max |m| |n| + ((i : ℕ) : ℤ))

lemma rw_vec_ext {a b c m n : ℤ} {D' : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') {i : ℕ} (hi : i ≤ D' + 1) :
    extVec (rw_vec a b c m n D') i = racah6jY a b c m n (max |m| |n| + (i : ℤ)) := by
  rcases Nat.lt_or_ge i (D' + 1) with h | h
  · rw [extVec_of_lt _ h]; rfl
  · have : i = D' + 1 := by omega
    subst this
    rw [extVec_of_ge _ le_rfl]
    symm
    apply racah_chain_support
    intro ⟨_, _, h3, h4⟩
    have hD := rw_D_eq a b m n hsys
    push_cast at h3 h4
    have : min (2 * b + m) (2 * a + n) < max |m| |n| + ((D' : ℤ) + 1) := by omega
    have h5 := le_min h3 h4
    omega

/-- Links are positive on `i < D'`, for every `h > 0`. -/
theorem rw_aJ_pos {α β h : ℝ} (hα : 0 < α) (hβ : 0 < β) {a b m n : ℤ} {D' : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D')
    (hh : 0 < h) (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) (hlo : 1 ≤ max |m| |n|)
    {i : ℕ} (hi : i < D') :
    0 < rw_aJ (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) m n h i := by
  have hD := rw_D_eq a b m n hsys
  set K : ℤ := max |m| |n| with hKdef
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = min (2 * b + m) (2 * a + n) :=
    ⟨(min (2 * b + m) (2 * a + n)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hedge := rw_hedge hα hβ a b m n hkmax hAh hBh hh
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = K + (i : ℤ) + 1 := ⟨(K + (i : ℤ) + 1).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hjK : (K : ℝ) < (j : ℝ) := by
    have : K < (j : ℤ) := by omega
    exact_mod_cast this
  have hm : |(m : ℝ)| ≤ (K : ℝ) := by
    have : |m| ≤ K := le_max_left _ _
    have h' : ((|m| : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
    simpa using h'
  have hn : |(n : ℝ)| ≤ (K : ℝ) := by
    have : |n| ≤ K := le_max_right _ _
    have h' : ((|n| : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
    simpa using h'
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hlo
  have := hr_Ak_pos (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (a := (m : ℝ)) (b := (n : ℝ)) (by positivity) (by positivity) hh
    (i := j) (kmax := kmax) (by omega) (by linarith) (by
      have : |(m : ℝ)| < j := lt_of_le_of_lt hm hjK
      have := pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
      rwa [sq_abs] at this) (by
      have : |(n : ℝ)| < j := lt_of_le_of_lt hn hjK
      have := pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
      rwa [sq_abs] at this) hedge.1
  unfold rw_aJ
  rw [← hj]
  exact this

/-- **The `6j` chain is a Jacobi eigenvector**: `J v = x v` with `x = cosA A B C`. -/
theorem rw_eigen {a b c m n : ℤ} {D' : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') {h : ℝ} (hh : 0 < h)
    (hA : 0 < wA (a : ℚ) (n : ℚ)) (hB : 0 < wB (b : ℚ) (m : ℚ)) (hlo : 1 ≤ max |m| |n|) :
    jacobiMatrix (D' + 1)
        (rw_bJ (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) m n h)
        (rw_aJ (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) m n h) *ᵥ rw_vec a b c m n D' =
      (cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ))) • rw_vec a b c m n D' := by
  funext i
  rw [jacobiMatrix_mulVec, Pi.smul_apply, smul_eq_mul]
  have hrow := racah_class_chain a b c m n h hh hA hB (max |m| |n| + ((i : ℕ) : ℤ)) (by omega)
  unfold jac at hrow
  unfold jacRow
  have h1 := rw_vec_ext (c := c) hsys (i := (i : ℕ) + 1) (by omega)
  have h0 := rw_vec_ext (c := c) hsys (i := (i : ℕ)) (by omega)
  have e3 : max |m| |n| + (((i : ℕ) + 1 : ℕ) : ℤ) = max |m| |n| + ((i : ℕ) : ℤ) + 1 := by push_cast; ring
  rw [e3] at h1
  rw [h1, h0]
  have hv : rw_vec a b c m n D' i = racah6jY a b c m n (max |m| |n| + ((i : ℕ) : ℤ)) := rfl
  rw [hv]
  unfold hrCk at hrow
  unfold rw_bJ rw_aJ
  by_cases hi0 : (i : ℕ) = 0
  · rw [hi0] at hrow ⊢
    have hend := hrAk_lower_zero (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) h m n hlo
    simp only [Nat.cast_zero, add_zero] at hrow ⊢
    rw [hend] at hrow
    simp only [↓reduceIte]
    linear_combination hrow
  · have hi1 := rw_vec_ext (c := c) hsys (i := (i : ℕ) - 1) (by omega)
    have e : max |m| |n| + (((i : ℕ) - 1 : ℕ) : ℤ) = max |m| |n| + ((i : ℕ) : ℤ) - 1 := by omega
    rw [e] at hi1
    have e2 : max |m| |n| + (((i : ℕ) - 1 : ℕ) : ℤ) + 1 = max |m| |n| + ((i : ℕ) : ℤ) := by omega
    simp only [hi0, ↓reduceIte]
    rw [hi1, e2]
    linear_combination hrow

/-- The chain vector at a lattice point is nonzero (Gauss mass `rd_sum`). -/
theorem rw_vec_ne_zero {α β h : ℝ} (hα : 0 < α) (hβ : 0 < β) {a b c m n : ℤ} {D' : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') (i : Fin (D' + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) :
    rw_vec a b c m n D' ≠ 0 := by
  intro h0
  obtain ⟨hA, hB, hC⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  have hD := rw_D_eq a b m n hsys
  have hmass := rd_sum a b c m n hsys i hc
  have hpos : 0 < 4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) := by positivity
  rw [← hmass] at hpos
  have hz : ∑ k ∈ Finset.Ico (max |m| |n|) (min (2 * b + m) (2 * a + n) + 1), racah6jY a b c m n k ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨t, ht⟩ : ∃ t : ℕ, (t : ℤ) = k - max |m| |n| := ⟨(k - max |m| |n|).toNat, Int.toNat_of_nonneg (by omega)⟩
    have := congrFun h0 ⟨t, by omega⟩
    simp only [rw_vec, Pi.zero_apply] at this
    have e : max |m| |n| + (t : ℤ) = k := by omega
    rw [e] at this
    rw [this]; ring
  rw [hz] at hpos
  exact lt_irrefl _ hpos

end Nodes


/-- `cosA A B C` is strictly decreasing in `C > 0`. -/
lemma rw_cosA_lt {A B C C' : ℝ} (hA : 0 < A) (hB : 0 < B) (hC' : 0 < C') (hlt : C' < C) :
    cosA A B C < cosA A B C' := by
  unfold cosA
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  nlinarith

/-- **Node count of the `6j` chain.**  For a finite Racah system with integer labels, `kmin = max |m| |n| ≥ 1` and `h > 0`, the natural-gauge chain at `c = c_min + l`
(`l = i`, `c = cPt i`) has exactly `i` nodes (sign changes `Ŷ_k Ŷ_{k+1} < 0`; an interior zero counts as one). -/
theorem rw_chain_nodes {a b c m n : ℤ} {D' : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') (i : Fin (D' + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) {h : ℝ} (hh : 0 < h) (hlo : 1 ≤ max |m| |n|) :
    cho_nodal (fun s : ℕ => racah6jY a b c m n (max |m| |n| + (s : ℤ))) D' = (i : ℕ) := by
  have hne : cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) ≤ cMax (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) := by
    have h1 := hsys.dim
    have : (0 : ℚ) ≤ (D' : ℚ) := Nat.cast_nonneg _
    linarith
  obtain ⟨hA, hB⟩ := AB_pos hne
  set A : ℝ := wA (a : ℚ) (n : ℚ) with hAdef
  set B : ℝ := wB (b : ℚ) (m : ℚ) with hBdef
  have hα : 0 < A * h := mul_pos hA hh
  have hβ : 0 < B * h := mul_pos hB hh
  set cMinZ : ℤ := max |a - b| |b + m - a - n| with hcMinZ
  have hcZ : ∀ (l : ℕ) (hl : l < D' + 1), ((cMinZ + (l : ℤ) : ℤ) : ℚ) =
      cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) (D := D') (⟨l, hl⟩ : Fin (D' + 1)) := by
    intro l hl
    unfold cPt cMin
    simp only [hcMinZ]
    push_cast
    rfl
  -- the spectrum
  set P : ℝ := 1 / (4 * (A * h) ^ 2) with hP
  set Q : ℝ := 1 / (4 * (B * h) ^ 2) with hQ
  obtain ⟨θ, hθ, hE, hnod⟩ := cho_eigen_ascending (b := rw_bJ P Q m n h) (a := rw_aJ P Q m n h) D'
    (fun j hj => rw_aJ_pos hα hβ hsys hh rfl rfl hlo hj)
  -- the lattice eigenvalues, ascending in `l`
  set cl : ℕ → ℤ := fun l => cMinZ + ((D' - l : ℕ) : ℤ) with hcl
  have hclFin : ∀ l, l ≤ D' → (cl l : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) (D := D') (⟨D' - l, by omega⟩ : Fin (D' + 1)) :=
    fun l hl => hcZ (D' - l) (by omega)
  set xs : ℕ → ℝ := fun l => cosA A B (wC ((cl l : ℤ) : ℚ)) with hxs
  have hCpos : ∀ l, l ≤ D' → 0 < wC ((cl l : ℤ) : ℚ) := by
    intro l hl
    have := cPt_nonneg (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) (D := D') (⟨D' - l, by omega⟩ : Fin (D' + 1))
    rw [← hclFin l hl] at this
    unfold wC
    have : (0 : ℝ) ≤ (((cl l : ℤ) : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  have hxs_lt : ∀ l l' : ℕ, l < l' → l' ≤ D' → xs l < xs l' := by
    intro l l' hll hl'
    apply rw_cosA_lt hA hB (hCpos l' hl')
    unfold wC
    have : cl l' < cl l := by simp only [hcl]; omega
    have : ((cl l' : ℤ) : ℝ) < ((cl l : ℤ) : ℝ) := by exact_mod_cast this
    have e1 : (((cl l' : ℤ) : ℚ) : ℝ) = ((cl l' : ℤ) : ℝ) := by simp
    have e2 : (((cl l : ℤ) : ℚ) : ℝ) = ((cl l : ℤ) : ℝ) := by simp
    rw [e1, e2]; linarith
  have hmem : ∀ l, l ≤ D' → ∃ t, t ≤ D' ∧ θ t = xs l := by
    intro l hl
    rw [← hE]
    exact ⟨rw_vec a b (cl l) m n D', rw_vec_ne_zero hα hβ hsys ⟨D' - l, by omega⟩ (hclFin l hl) hh rfl rfl,
      rw_eigen hsys hh hA hB hlo⟩
  have hid := cho_index_id D' θ xs hθ (fun l l' hll hl' => hxs_lt l l' hll hl') hmem
  -- the given point
  have hiD : (i : ℕ) ≤ D' := by have := i.2; omega
  have hcc : c = cl (D' - (i : ℕ)) := by
    have h1 : ((c : ℤ) : ℚ) = ((cMinZ + ((i : ℕ) : ℤ) : ℤ) : ℚ) := by
      rw [hc]; unfold cPt cMin; simp only [hcMinZ]; push_cast; rfl
    have h2 : c = cMinZ + ((i : ℕ) : ℤ) := by exact_mod_cast h1
    rw [h2]; simp only [hcl]; omega
  have hl : D' - (i : ℕ) ≤ D' := by omega
  have hvne := rw_vec_ne_zero hα hβ hsys i hc hh rfl rfl
  have hev := rw_eigen (c := c) hsys hh hA hB hlo
  have hθl : θ (D' - (i : ℕ)) = cosA A B (wC (c : ℚ)) := by
    rw [hid _ hl]; simp only [hxs, hcc]
  have key := hnod (D' - (i : ℕ)) hl _ hvne (by rw [hθl]; exact hev)
  have e : D' - (D' - (i : ℕ)) = (i : ℕ) := by omega
  rw [e] at key
  rw [← key]
  unfold cho_nodal
  congr 1
  · apply congrArg
    apply filter_congr
    intro t ht
    have ht' := mem_range.mp ht
    rw [rw_vec_ext (c := c) hsys (by omega), rw_vec_ext (c := c) hsys (by omega)]
  · apply congrArg
    apply filter_congr
    intro t ht
    have ht' := mem_range.mp ht
    rw [rw_vec_ext (c := c) hsys (by omega)]

/-- info: 'FormalResearch.Special.rw_chain_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rw_chain_nodes

end FormalResearch.Special

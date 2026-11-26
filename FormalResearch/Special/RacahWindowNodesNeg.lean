module

public import FormalResearch.Special.RacahWindowNodes

/-!
# Racah window, part 9: the twisted `6j` chain has `D' - l` nodes (`τ = -1`, integer data)

The twisted chain `Y_k = (-1)^k Ŷ_k` (`rwY (fun j => (-1) ^ j)`) satisfies `J~ Y = -x Y`, where `J~` is the Jacobi matrix with *the same positive links* `rw_aJ` and the *negated* diagonal `-rw_bJ`
(`rw_eigen`, the sign pattern `Y_{k±1}/Y_k` flips).  The lattice eigenvalues `-x_l` (`x_l = cosA A B (c_l + 1/2)`, `c_l = c_min + l`) are now *increasing* in `l`, so the nodal Sturm theorem
(`cho_eigen_ascending`) puts the chain at `c = c_min + l` at the position `l` of the ascending spectrum, i.e. with `D' - l` nodes.

* **`rw_chain_nodes_neg`**: the twisted chain at `c = c_min + l` has exactly `D' - l` nodes (sign changes of `Y_k Y_{k+1}`, an interior zero counting as one).  (`rw_chain_nodes` is the statement `l` for `Ŷ` itself.)

**Claim class: proved** (axiom guard pinned).  **Not formalised:** `kmin = 0`, half-integer data.
-/

@[expose] public section

open Finset FormalResearch.Jacobi FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry Matrix
open scoped Real

namespace FormalResearch.Special

/-- The twisted chain vector on the sites `kmin, …, kmax`. -/
noncomputable def rw_wvec (a b c m n : ℤ) (D' : ℕ) : Fin (D' + 1) → ℝ :=
  fun i => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + ((i : ℕ) : ℤ))

lemma rwn_sign_succ (K : ℤ) (j : ℕ) : (-1 : ℝ) ^ (K + ((j + 1 : ℕ) : ℤ)) = -(-1 : ℝ) ^ (K + (j : ℤ)) := by
  have : K + ((j + 1 : ℕ) : ℤ) = K + (j : ℤ) + 1 := by push_cast; ring
  rw [this, zpow_add_one₀ (by norm_num)]; ring

lemma rw_wvec_ext {a b c m n : ℤ} {D' : ℕ} (i : ℕ) :
    extVec (rw_wvec a b c m n D') i = (-1 : ℝ) ^ (max |m| |n| + (i : ℤ)) * extVec (rw_vec a b c m n D') i := by
  rcases Nat.lt_or_ge i (D' + 1) with h | h
  · rw [extVec_of_lt _ h, extVec_of_lt _ h]; rfl
  · rw [extVec_of_ge _ h, extVec_of_ge _ h, mul_zero]

/-- **The twisted `6j` chain is an eigenvector of `J~`** (links `rw_aJ`, diagonal `-rw_bJ`) for the eigenvalue `-x`. -/
theorem rw_eigen_neg {a b c m n : ℤ} {D' : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') {h : ℝ} (hh : 0 < h)
    (hA : 0 < wA (a : ℚ) (n : ℚ)) (hB : 0 < wB (b : ℚ) (m : ℚ)) (hlo : 1 ≤ max |m| |n|) :
    jacobiMatrix (D' + 1)
        (fun i => -rw_bJ (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) m n h i)
        (rw_aJ (1 / (4 * (wA (a : ℚ) (n : ℚ) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) (m : ℚ) * h) ^ 2)) m n h) *ᵥ rw_wvec a b c m n D' =
      (-(cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)))) • rw_wvec a b c m n D' := by
  funext i
  have hrow := congrFun (rw_eigen (c := c) hsys hh hA hB hlo) i
  rw [jacobiMatrix_mulVec, Pi.smul_apply, smul_eq_mul] at hrow
  rw [jacobiMatrix_mulVec, Pi.smul_apply, smul_eq_mul]
  unfold jacRow at hrow ⊢
  have hwi : rw_wvec a b c m n D' i = extVec (rw_wvec a b c m n D') (i : ℕ) := (extVec_of_lt _ i.2).symm
  have hvi : rw_vec a b c m n D' i = extVec (rw_vec a b c m n D') (i : ℕ) := (extVec_of_lt _ i.2).symm
  rw [hwi]; rw [hvi] at hrow
  generalize (i : ℕ) = s at hrow hwi hvi ⊢
  have F0 := rw_wvec_ext (a := a) (b := b) (c := c) (m := m) (n := n) (D' := D') s
  have F1 := rw_wvec_ext (a := a) (b := b) (c := c) (m := m) (n := n) (D' := D') (s + 1)
  rw [rwn_sign_succ] at F1
  rw [F0, F1]
  by_cases hi0 : s = 0
  · rw [ite_eq_left hi0] at hrow ⊢
    linear_combination (-(-1 : ℝ) ^ (max |m| |n| + (s : ℤ))) * hrow
  · rw [ite_eq_right hi0] at hrow ⊢
    have F2 := rw_wvec_ext (a := a) (b := b) (c := c) (m := m) (n := n) (D' := D') (s - 1)
    have e : (-1 : ℝ) ^ (max |m| |n| + ((s - 1 : ℕ) : ℤ)) = -(-1 : ℝ) ^ (max |m| |n| + (s : ℤ)) := by
      have := rwn_sign_succ (max |m| |n|) (s - 1)
      rw [show s - 1 + 1 = s by omega] at this
      linarith
    rw [F2, e]
    linear_combination (-(-1 : ℝ) ^ (max |m| |n| + (s : ℤ))) * hrow

/-- **Node count of the twisted `6j` chain** (`τ = -1`): at `c = c_min + l` the chain `(-1)^k Ŷ_k` has exactly `D' - l` nodes. -/
theorem rw_chain_nodes_neg {a b c m n : ℤ} {D' : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') (i : Fin (D' + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) {h : ℝ} (hh : 0 < h) (hlo : 1 ≤ max |m| |n|) :
    cho_nodal (fun s : ℕ => rwY (fun j => (-1 : ℝ) ^ j) a b c m n (max |m| |n| + (s : ℤ))) D' = D' - (i : ℕ) := by
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
  set P : ℝ := 1 / (4 * (A * h) ^ 2) with hP
  set Q : ℝ := 1 / (4 * (B * h) ^ 2) with hQ
  obtain ⟨θ, hθ, hE, hnod⟩ := cho_eigen_ascending (b := fun i => -rw_bJ P Q m n h i) (a := rw_aJ P Q m n h) D'
    (fun j hj => rw_aJ_pos hα hβ hsys hh rfl rfl hlo hj)
  set cl : ℕ → ℤ := fun l => cMinZ + (l : ℤ) with hcl
  have hclFin : ∀ l (hl : l ≤ D'), (cl l : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) (D := D') (⟨l, by omega⟩ : Fin (D' + 1)) :=
    fun l hl => hcZ l (by omega)
  set xs : ℕ → ℝ := fun l => -cosA A B (wC ((cl l : ℤ) : ℚ)) with hxs
  have hCpos : ∀ l, l ≤ D' → 0 < wC ((cl l : ℤ) : ℚ) := by
    intro l hl
    have := cPt_nonneg (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) (D := D') (⟨l, by omega⟩ : Fin (D' + 1))
    rw [← hclFin l hl] at this
    unfold wC
    have : (0 : ℝ) ≤ (((cl l : ℤ) : ℚ) : ℝ) := by exact_mod_cast this
    linarith
  have hxs_lt : ∀ l l' : ℕ, l < l' → l' ≤ D' → xs l < xs l' := by
    intro l l' hll hl'
    have key : cosA A B (wC ((cl l' : ℤ) : ℚ)) < cosA A B (wC ((cl l : ℤ) : ℚ)) := by
      apply rw_cosA_lt hA hB (hCpos l (by omega))
      unfold wC
      have : cl l < cl l' := by simp only [hcl]; omega
      have : ((cl l : ℤ) : ℝ) < ((cl l' : ℤ) : ℝ) := by exact_mod_cast this
      have e1 : (((cl l' : ℤ) : ℚ) : ℝ) = ((cl l' : ℤ) : ℝ) := by simp
      have e2 : (((cl l : ℤ) : ℚ) : ℝ) = ((cl l : ℤ) : ℝ) := by simp
      rw [e1, e2]; linarith
    simp only [hxs]; linarith
  have hmem : ∀ l, l ≤ D' → ∃ t, t ≤ D' ∧ θ t = xs l := by
    intro l hl
    rw [← hE]
    refine ⟨rw_wvec a b (cl l) m n D', ?_, rw_eigen_neg hsys hh hA hB hlo⟩
    intro h0
    apply rw_vec_ne_zero hα hβ hsys ⟨l, by omega⟩ (hclFin l hl) hh rfl rfl
    funext j
    have := congrFun h0 j
    have hs : (-1 : ℝ) ^ (max |m| |n| + ((j : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    simp only [rw_wvec, rwY, Pi.zero_apply] at this
    simp only [rw_vec, Pi.zero_apply]
    exact (mul_eq_zero.1 this).resolve_left hs
  have hid := cho_index_id D' θ xs hθ (fun l l' hll hl' => hxs_lt l l' hll hl') hmem
  have hiD : (i : ℕ) ≤ D' := by have := i.2; omega
  have hcc : c = cl (i : ℕ) := by
    have h1 : ((c : ℤ) : ℚ) = ((cMinZ + ((i : ℕ) : ℤ) : ℤ) : ℚ) := by
      rw [hc]; unfold cPt cMin; simp only [hcMinZ]; push_cast; rfl
    exact_mod_cast h1
  have hvne : rw_wvec a b c m n D' ≠ 0 := by
    intro h0
    apply rw_vec_ne_zero hα hβ hsys i hc hh rfl rfl
    funext j
    have := congrFun h0 j
    have hs : (-1 : ℝ) ^ (max |m| |n| + ((j : ℕ) : ℤ)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    simp only [rw_wvec, rwY, Pi.zero_apply] at this
    simp only [rw_vec, Pi.zero_apply]
    exact (mul_eq_zero.1 this).resolve_left hs
  have hev := rw_eigen_neg (c := c) hsys hh hA hB hlo
  have hθl : θ (i : ℕ) = -cosA A B (wC (c : ℚ)) := by
    rw [hid _ hiD]; simp only [hxs, hcc]
  have key := hnod (i : ℕ) hiD _ hvne (by rw [hθl]; exact hev)
  rw [← key]
  unfold cho_nodal
  congr 1
  · apply congrArg
    apply filter_congr
    intro t ht
    have ht' := mem_range.mp ht
    rw [rw_wvec_ext, rw_wvec_ext, extVec_of_lt _ (by omega), extVec_of_lt _ (by omega)]
    rfl
  · apply congrArg
    apply filter_congr
    intro t ht
    have ht' := mem_range.mp ht
    rw [rw_wvec_ext, extVec_of_lt _ (by omega)]
    simp only [rw_vec, rwY]

/-- info: 'FormalResearch.Special.rw_chain_nodes_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rw_chain_nodes_neg

end FormalResearch.Special

module

public import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlat
public import FormalResearch.FourQubitEntropy.PaperECriticalZeroOrbits

/-!
# Signed permutations of the magic diagonal are local unitaries

Helper for `prop:fqe-two-flat-rigidity` (identification with the cluster-to-Bell family).  In the magic
basis a local unitary on qubits `1,2` and one on qubits `3,4` act by `X ↦ O₁ X O₂ᵀ` with `O₁, O₂ ∈ SO(4)`
(`LU_of_normal_form`).  A signed permutation matrix `sp σ ε` (`ε_l = ±1`) is orthogonal with
determinant `sgn σ · ∏ ε_l`, hence in `SO(4)` when that is `1`.  Taking `O₁ = sp σ a`, `O₂ = sp σ b`
gives `LUEquiv (Gv v) (Gv v')` for `v'_{σ l} = a_l b_l v_l`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

abbrev Ix := Fin 2 × Fin 2

/-- The signed permutation matrix `e_l ↦ ε_l e_{σ l}`. -/
def sp (σ : Equiv.Perm Ix) (ε : Ix → ℝ) : RMat4 := Matrix.of fun k l => if k = σ l then ε l else 0

theorem sp_eq (σ : Equiv.Perm Ix) (ε : Ix → ℝ) :
    sp σ ε = (σ.symm.toPEquiv.toMatrix : RMat4) * Matrix.diagonal ε := by
  ext k l
  simp [sp, Matrix.mul_apply, Matrix.diagonal_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  by_cases h : k = σ l
  · subst h; simp
  · have : l ≠ σ.symm k := fun h' => h (by rw [h']; simp)
    simp [h, this]
    intro h'; exact absurd h'.symm this

theorem sp_orth (σ : Equiv.Perm Ix) (ε : Ix → ℝ) (hε : ∀ l, ε l ^ 2 = 1) :
    (sp σ ε)ᵀ * sp σ ε = 1 := by
  ext l m
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sp, Matrix.of_apply, Matrix.one_apply]
  by_cases h : l = m
  · subst h
    simp [← pow_two, hε]
  · have : σ l ≠ σ m := fun h' => h (σ.injective h')
    simp only [h, ite_false]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = σ l
    · have : k ≠ σ m := fun h' => this (hk.symm.trans h')
      have e1 : (if k = σ l then ε l else 0) = ε l := by simp [hk]
      have e2 : (if k = σ m then ε m else 0) = 0 := by simp [this]
      rw [e1, e2]; simp
    · have e1 : (if k = σ l then ε l else 0) = 0 := by simp [hk]
      rw [e1]; simp

theorem sp_det (σ : Equiv.Perm Ix) (ε : Ix → ℝ) :
    (sp σ ε).det = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ l, ε l := by
  rw [sp_eq, Matrix.det_mul, Matrix.det_permutation, Matrix.det_diagonal, Equiv.Perm.sign_symm]

theorem sp_diag (σ : Equiv.Perm Ix) (a b : Ix → ℝ) (v : Ix → ℂ) :
    rc (sp σ a) * Matrix.diagonal v * (rc (sp σ b))ᵀ =
      Matrix.diagonal (fun k => ((a (σ.symm k) * b (σ.symm k) : ℝ) : ℂ) * v (σ.symm k)) := by
  ext k m
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, rc_apply,
    sp, Matrix.of_apply]
  rw [Finset.sum_eq_single (σ.symm k)]
  · by_cases hkm : k = m
    · subst hkm; simp; ring
    · have : m ≠ σ (σ.symm k) := by simpa using Ne.symm hkm
      have e : (if m = σ (σ.symm k) then b (σ.symm k) else 0) = 0 := by simp [Ne.symm hkm]
      simp only [e]; simp [hkm]
  · intro x _ hx
    have : k ≠ σ x := fun h => hx (by rw [h]; simp)
    simp [this]
  · simp

/-- **Signed permutations of the magic diagonal are local unitaries.** -/
theorem LU_signedPerm (σ : Equiv.Perm Ix) (a b : Ix → ℝ) (ha : ∀ l, a l ^ 2 = 1) (hb : ∀ l, b l ^ 2 = 1)
    (hda : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ l, a l = 1) (hdb : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ l, b l = 1)
    (v : Ix → ℂ) :
    LUEquiv (Gv v) (Gv (fun k => ((a (σ.symm k) * b (σ.symm k) : ℝ) : ℂ) * v (σ.symm k))) := by
  refine LU_of_normal_form _ (sp σ a) (sp σ b) v (sp_orth σ a ha) (sp_orth σ b hb)
    (by rw [sp_det]; exact hda) (by rw [sp_det]; exact hdb) ?_
  rw [coord_Gv, sp_diag]

theorem exists_perm_two (i j a b : Ix) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ σ : Equiv.Perm Ix, σ i = a ∧ σ j = b := by
  refine ⟨(Equiv.swap i a).trans (Equiv.swap ((Equiv.swap i a) j) b), ?_, ?_⟩
  · have h1 : (Equiv.swap i a) i = a := Equiv.swap_apply_left _ _
    have h2 : (Equiv.swap i a) j ≠ a := by
      intro h; exact hij (((Equiv.swap i a).injective (h.trans h1.symm)).symm)
    simp only [Equiv.trans_apply, h1]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h2) hab
  · simp only [Equiv.trans_apply]
    exact Equiv.swap_apply_left _ _

theorem exists_third (i j : Ix) : ∃ k, k ≠ i ∧ k ≠ j := by
  revert i j; decide

/-- The cluster-to-Bell normal-form vector `(x, i y, 0, 0)`. -/
noncomputable def qfVec (x y : ℝ) : Ix → ℂ := fun k =>
  if k = (0, 0) then (x : ℂ) else if k = (0, 1) then Complex.I * (y : ℂ) else 0

/-- The vector `c (x e_i + s i y e_j)`. -/
noncomputable def pairVec (i j : Ix) (c : ℂ) (x y s : ℝ) : Ix → ℂ := fun k =>
  if k = i then c * (x : ℂ) else if k = j then c * (s : ℂ) * Complex.I * (y : ℂ) else 0

theorem sign_sq (σ : Equiv.Perm Ix) : (((Equiv.Perm.sign σ : ℤ) : ℝ)) ^ 2 = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

/-- Any `c (x e_i + s i y e_j)` (`i ≠ j`, `|c| = 1`, `s = ±1`) is locally unitarily equivalent to
`G(x, i y, 0, 0)`. -/
theorem LU_pair (i j : Ix) (hij : i ≠ j) (c : ℂ) (hc : (starRingEnd ℂ) c * c = 1) (x y s : ℝ)
    (hs : s ^ 2 = 1) : LUEquiv (Gv (qfVec x y)) (Gv (pairVec i j c x y s)) := by
  obtain ⟨σ, hσi, hσj⟩ := exists_perm_two i j (0, 0) (0, 1) hij (by decide)
  obtain ⟨k0, hk0i, hk0j⟩ := exists_third i j
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = ((Equiv.Perm.sign σ : ℤ) : ℝ) := ⟨_, rfl⟩
  have hg2 : g ^ 2 = 1 := by rw [hg]; exact sign_sq σ
  obtain ⟨a, ha⟩ : ∃ a : Ix → ℝ, a = fun l => if l = i then g else 1 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Ix → ℝ, b = fun l => a l * ((if l = j then s else 1) * (if l = k0 then s else 1)) :=
    ⟨_, rfl⟩
  have ha2 : ∀ l, a l ^ 2 = 1 := fun l => by by_cases h : l = i <;> simp [ha, h, hg2]
  have hb2 : ∀ l, b l ^ 2 = 1 := fun l => by
    simp only [hb, mul_pow, ha2 l, one_mul]
    by_cases h1 : l = j <;> by_cases h2 : l = k0 <;> simp [h1, h2, hs]
  have hda : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ l, a l = 1 := by
    rw [← hg]
    simp only [ha, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    linear_combination hg2
  have hdb : ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ l, b l = 1 := by
    rw [← hg]
    simp only [hb, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true, ha]
    linear_combination (s ^ 2) * hg2 + hs
  have key := LU_signedPerm σ a b ha2 hb2 hda hdb (pairVec i j c x y s)
  have hg2c : (g : ℂ) ^ 2 = 1 := by exact_mod_cast hg2
  have hsc : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs
  have ai : a i = g := by simp [ha]
  have bi : b i = g := by simp [hb, ha, hij, hk0i.symm]
  have aj : a j = 1 := by simp [ha, hij.symm]
  have bj : b j = s := by simp [hb, aj, hk0j.symm]
  have hv' : (fun k => ((a (σ.symm k) * b (σ.symm k) : ℝ) : ℂ) * pairVec i j c x y s (σ.symm k)) =
      fun k => c * qfVec x y k := by
    funext k
    have hk : k = σ (σ.symm k) := by simp
    by_cases hli : σ.symm k = i
    · have hk' : k = (0, 0) := by rw [hk, hli, hσi]
      rw [hli, ai, bi, hk']
      simp [pairVec, qfVec]
      linear_combination (c * x) * hg2c
    · by_cases hlj : σ.symm k = j
      · have hk' : k = (0, 1) := by rw [hk, hlj, hσj]
        rw [hlj, aj, bj, hk']
        simp [pairVec, qfVec, hij.symm]
        linear_combination (c * Complex.I * y) * hsc
      · have h1 : k ≠ (0, 0) := fun h => hli (by rw [h, ← hσi]; simp)
        have h2 : k ≠ (0, 1) := fun h => hlj (by rw [h, ← hσj]; simp)
        simp [pairVec, qfVec, hli, hlj, h1, h2]
  rw [hv'] at key
  have e1 : Gv (fun k => c * qfVec x y k) = fun p q r t => c * Gv (qfVec x y) p q r t := Gv_smul c _
  rw [e1] at key
  exact (LUEquiv_scalar hc (Gv (qfVec x y))).symm.trans key.symm

end FormalResearch.FourQubitEntropy.PaperECritical

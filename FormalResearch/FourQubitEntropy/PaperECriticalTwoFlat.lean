import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlatCore
import FormalResearch.FourQubitEntropy.PaperECriticalZeroOrbits

/-!
# Two-flat rigidity on critical states (`prop:fqe-two-flat-rigidity`)

Paper E, `renyi_uncapped_reduction.tex`. The paper states `(TF)` for every unit pure state, with an extra
term `W₁/4` (`Δ_k ≥ W₁/4 + 2 e₂(other three entries) ≥ W₁/4 + (λ₃ + λ₄)²`, from
`prop:fqe-spectral-spinflip`); this file proves the critical specialization `W₁ = 0` (`hW : blochSq ψ = 0`),
which is the case with the normal form `G(v)`, and the Schmidt-rank-two consequence for every unit state.
The `W₁/4` term for noncritical states is not formalized. For a unit critical state `ψ` (`blochSq ψ = 0`) with
normal form `ψ ≃ G(v)` (`critical_iff_LU_Gv`), the three cut spectra are `|v_k|²`, `|(wp v)_k|²`,
`|(wm v)_k|²` for the cuts `12|34`, `13|24`, `14|23` (`wp`, `wm` are the real Hadamard-type
changes of coordinates of `PaperECriticalCuts.lean`), and the purity identity at criticality reads
`2 P = 2 + |Σ v_k²|²`.

* `two_flat_rigidity`: for each cut `c` and each `i` with `λ_i ≥ 1/2`,
  `2 e₂(other three entries) ≤ (sum of the other two cut purities) - 1/2`, which is `(TF)`
  (first inequality; `e₂` is written `(Σ_{j≠i} λ_j)² - Σ_{j≠i} λ_j²` = `2 e₂`);
* `two_flat_rank`: if two cuts (`12|34`, `13|24`) are maximally mixed (purity `1/4`) the
  remaining cut spectrum has at least two zero entries (Schmidt rank at most two). That one
  maximally mixed cut forces criticality is `blochSq_zero_of_cutPurity12`.

Proved, axiom-free. The second inequality of `(TF)` is the scalar `two_flat_second` and the sharpness
of the first (opposite phases) is `tau_equality` (both in `PaperECriticalTwoFlatCore.lean`). NOT
formalised: the identification of the rank-two critical states with the cluster-to-Bell family
`(eq:fqe-quadratic-family)` and the resulting Rényi-envelope statement.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- Purities `tr R²` of the three balanced cuts. -/
noncomputable def cutPurity12 (ψ : Psi) : ℝ := (Matrix.trace (red12 ψ * red12 ψ)).re
noncomputable def cutPurity13 (ψ : Psi) : ℝ := (Matrix.trace (red13 ψ * red13 ψ)).re
noncomputable def cutPurity14 (ψ : Psi) : ℝ := (Matrix.trace (red14 ψ * red14 ψ)).re

theorem purity_eq_cuts (ψ : Psi) : purity ψ = cutPurity12 ψ + cutPurity13 ψ + cutPurity14 ψ := rfl

theorem cutPurities_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) :
    cutPurity12 ψ = cutPurity12 φ ∧ cutPurity13 ψ = cutPurity13 φ ∧ cutPurity14 ψ = cutPurity14 φ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · unfold cutPurity12; rw [red12_localApply hc hd, trace_conj_two (kron_unitary ha hb)]
  · unfold cutPurity13; rw [red13_localApply hb hd, trace_conj_two (kron_unitary ha hc)]
  · unfold cutPurity14; rw [red14_localApply hc hb, trace_conj_two (kron_unitary ha hd)]

theorem Gv_cutPurities (v : Fin 2 × Fin 2 → ℂ) :
    cutPurity12 (Gv v) = ∑ k, Complex.normSq (v k) ^ 2 ∧
    cutPurity13 (Gv v) = ∑ k, Complex.normSq (wp v k) ^ 2 ∧
    cutPurity14 (Gv v) = ∑ k, Complex.normSq (wm v k) ^ 2 := by
  refine ⟨red12_pow_two _ v (zmat_Gv v), ?_, ?_⟩
  · unfold cutPurity13; rw [red13_eq_swap]; exact red12_pow_two _ (wp v) (zmat_swap23_Gv v)
  · unfold cutPurity14; rw [red14_eq_swap]; exact red12_pow_two _ (wm v) (zmat_swap24_Gv v)

/-! ### Orthogonality of the cut coordinates -/

theorem wp_sq_sum (v : Fin 2 × Fin 2 → ℂ) : ∑ k, wp v k ^ 2 = ∑ k, v k ^ 2 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, wp]; ring

theorem wm_sq_sum (v : Fin 2 × Fin 2 → ℂ) : ∑ k, wm v k ^ 2 = ∑ k, v k ^ 2 := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, wm]; ring

theorem wp_normSq_sum (v : Fin 2 × Fin 2 → ℂ) :
    ∑ k, Complex.normSq (wp v k) = ∑ k, Complex.normSq (v k) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, wp, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

theorem wm_normSq_sum (v : Fin 2 × Fin 2 → ℂ) :
    ∑ k, Complex.normSq (wm v k) = ∑ k, Complex.normSq (v k) := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, wm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

/-- The purity identity at criticality in normal-form coordinates: `2 P = 2 + |Σ v_k²|²`. -/
theorem Gv_purity_tau (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (v k) = 1) :
    2 * purity (Gv v) = 2 + Complex.normSq (∑ k, v k ^ 2) := by
  have h := purity_identity_exact (Gv v)
  have hW : blochSq (Gv v) = 0 := blochSq_zero_of_LU_Gv v (Gv v) (LUEquiv.refl _)
  have hτ : spinFlipForm (Gv v) = ∑ k, v k ^ 2 := by
    rw [spinFlip_coord, coord_Gv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    simp [Matrix.trace, pow_two]
  rw [(Gv_n v).trans hn, hW, hτ] at h
  linarith

/-- Rest-of-spectrum cross term `(Σ_{j≠i} λ_j)² - Σ_{j≠i} λ_j²` (`= 2 e₂` of the other entries). -/
noncomputable def crossCost (w : Fin 2 × Fin 2 → ℂ) (i : Fin 2 × Fin 2) : ℝ :=
  (∑ j ∈ Finset.univ.erase i, Complex.normSq (w j)) ^ 2 -
    ∑ j ∈ Finset.univ.erase i, Complex.normSq (w j) ^ 2

/-- `(TF)` for the three cuts of `G(v)` (unit `v`). -/
theorem two_flat_Gv (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (v k) = 1) :
    (∀ i, 1 / 2 ≤ Complex.normSq (v i) →
        crossCost v i ≤ cutPurity13 (Gv v) + cutPurity14 (Gv v) - 1 / 2) ∧
    (∀ i, 1 / 2 ≤ Complex.normSq (wp v i) →
        crossCost (wp v) i ≤ cutPurity12 (Gv v) + cutPurity14 (Gv v) - 1 / 2) ∧
    (∀ i, 1 / 2 ≤ Complex.normSq (wm v i) →
        crossCost (wm v) i ≤ cutPurity12 (Gv v) + cutPurity13 (Gv v) - 1 / 2) := by
  have hP := Gv_purity_tau v hn
  obtain ⟨c12, c13, c14⟩ := Gv_cutPurities v
  have hsum : purity (Gv v) = cutPurity12 (Gv v) + cutPurity13 (Gv v) + cutPurity14 (Gv v) := rfl
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · have := two_flat_core v hn (purity (Gv v)) hP i hi
    unfold crossCost; rw [c12] at hsum; linarith
  · have hn' : ∑ k, Complex.normSq (wp v k) = 1 := (wp_normSq_sum v).trans hn
    have := two_flat_core (wp v) hn' (purity (Gv v)) (by rw [wp_sq_sum]; exact hP) i hi
    unfold crossCost; rw [c13] at hsum; linarith
  · have hn' : ∑ k, Complex.normSq (wm v k) = 1 := (wm_normSq_sum v).trans hn
    have := two_flat_core (wm v) hn' (purity (Gv v)) (by rw [wm_sq_sum]; exact hP) i hi
    unfold crossCost; rw [c14] at hsum; linarith

/-- **`prop:fqe-two-flat-rigidity`, bound `(TF)` (first inequality) at `W₁ = 0`** for a unit critical state:
in a normal form `ψ ≃ G(v)`, the cut spectra are `|v|²`, `|wp v|²`, `|wm v|²` and each cut whose top
eigenvalue is `≥ 1/2` pays `2 e₂(other three eigenvalues)` in the other two cut purities. -/
theorem two_flat_rigidity (ψ : Psi) (hn : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    ∃ v : Fin 2 × Fin 2 → ℂ, LUEquiv (Gv v) ψ ∧ ∑ k, Complex.normSq (v k) = 1 ∧
      cutPurity12 ψ = ∑ k, Complex.normSq (v k) ^ 2 ∧
      cutPurity13 ψ = ∑ k, Complex.normSq (wp v k) ^ 2 ∧
      cutPurity14 ψ = ∑ k, Complex.normSq (wm v k) ^ 2 ∧
      (∀ i, 1 / 2 ≤ Complex.normSq (v i) →
        crossCost v i ≤ cutPurity13 ψ + cutPurity14 ψ - 1 / 2) ∧
      (∀ i, 1 / 2 ≤ Complex.normSq (wp v i) →
        crossCost (wp v) i ≤ cutPurity12 ψ + cutPurity14 ψ - 1 / 2) ∧
      (∀ i, 1 / 2 ≤ Complex.normSq (wm v i) →
        crossCost (wm v) i ≤ cutPurity12 ψ + cutPurity13 ψ - 1 / 2) := by
  obtain ⟨v, hv⟩ := critical_LU_Gv ψ hW
  have hnv : ∑ k, Complex.normSq (v k) = 1 := by
    rw [← Gv_n, ← normSqPsi_LUEquiv hv]; exact hn
  obtain ⟨e12, e13, e14⟩ := cutPurities_LUEquiv hv
  obtain ⟨c12, c13, c14⟩ := Gv_cutPurities v
  obtain ⟨t1, t2, t3⟩ := two_flat_Gv v hnv
  refine ⟨v, hv, hnv, by rw [e12, c12], by rw [e13, c13], by rw [e14, c14], ?_, ?_, ?_⟩
  · intro i hi; rw [e13, e14]; exact t1 i hi
  · intro i hi; rw [e12, e14]; exact t2 i hi
  · intro i hi; rw [e12, e13]; exact t3 i hi


/-! ### One maximally mixed cut forces criticality -/

open scoped ComplexOrder in
/-- A unit vector whose `12|34` cut has purity `1/4` (so `ρ₁₂ = I/4`) has all one-qubit marginals
maximally mixed. -/
theorem blochSq_zero_of_cutPurity12 (ψ : Psi) (hn : normSqPsi ψ = 1) (h : cutPurity12 ψ = 1 / 4) :
    blochSq ψ = 0 := by
  have hH := red12_herm ψ
  have ht : Matrix.trace (red12 ψ) = 1 := by rw [trace_red12, hn]; simp
  have ht2 : Matrix.trace (red12 ψ * red12 ψ) = 1 / 4 := by
    rw [trace_sq_real hH]; unfold cutPurity12 at h; rw [h]; norm_num
  set R := red12 ψ with hR
  have hA : (R - (1 / 4 : ℂ) • (1 : Mat4))ᴴ = R - (1 / 4 : ℂ) • 1 := by
    rw [Matrix.conjTranspose_sub, hH.eq, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  have h0 : Matrix.trace ((R - (1 / 4 : ℂ) • (1 : Mat4))ᴴ * (R - (1 / 4 : ℂ) • 1)) = 0 := by
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_one, ht, ht2, smul_eq_mul]
    norm_num
  have hR14 : R = (1 / 4 : ℂ) • (1 : Mat4) :=
    sub_eq_zero.mp (Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h0)
  have hHl : Hl ψ = (1 / 4 : ℂ) • (1 : Mat4) := by
    unfold Hl
    rw [coord_mul_conjTranspose, ← red12_zmat, ← hR, hR14, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, magicB_unitary]
  have hHr : Hr ψ = (1 / 4 : ℂ) • (1 : Mat4) := by
    unfold Hr Hl at *
    have h1 : magicCoord (zmat ψ) * ((4 : ℂ) • (magicCoord (zmat ψ))ᴴ) = 1 := by
      rw [Matrix.mul_smul, hHl, smul_smul]; norm_num
    have h2 := mul_eq_one_comm.mp h1
    rw [Matrix.smul_mul] at h2
    have : (magicCoord (zmat ψ))ᴴ * magicCoord (zmat ψ) = (1 / 4 : ℂ) • ((4 : ℂ) • ((magicCoord (zmat ψ))ᴴ * magicCoord (zmat ψ))) := by
      rw [smul_smul]; norm_num
    rw [this, h2]
  refine (blochSq_eq_zero_iff ψ).mpr ⟨fun j k => ?_, fun j k => ?_⟩
  · rw [hHl]; by_cases hjk : j = k <;> simp [Matrix.one_apply, hjk]
  · rw [hHr]; by_cases hjk : j = k <;> simp [Matrix.one_apply, hjk]

/-- Existence of a maximal entry: some `i` with `λ_i ≥ 1/2` when the purity `Σ λ² ≥ 1/2`. -/
theorem exists_big_entry (w : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (w k) = 1)
    (hp : 1 / 2 ≤ ∑ k, Complex.normSq (w k) ^ 2) : ∃ i, 1 / 2 ≤ Complex.normSq (w i) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun k => Complex.normSq (w k))
    ⟨(0, 0), Finset.mem_univ _⟩
  refine ⟨i, ?_⟩
  have : ∑ k, Complex.normSq (w k) ^ 2 ≤ Complex.normSq (w i) := by
    calc ∑ k, Complex.normSq (w k) ^ 2 ≤ ∑ k, Complex.normSq (w i) * Complex.normSq (w k) :=
          Finset.sum_le_sum fun k hk => by
            rw [pow_two]; exact mul_le_mul_of_nonneg_right (hi k hk) (Complex.normSq_nonneg _)
      _ = Complex.normSq (w i) := by rw [← Finset.mul_sum, hn, mul_one]
  linarith

theorem exists_three_others : ∀ i : Fin 2 × Fin 2, ∃ j k l : Fin 2 × Fin 2,
    j ≠ i ∧ k ≠ i ∧ l ≠ i ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l := by decide

theorem univ_erase_eq (i j k l : Fin 2 × Fin 2) (hj : j ≠ i) (hk : k ≠ i) (hl : l ≠ i) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) : Finset.univ.erase i = {j, k, l} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [*]
  · rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    rw [Finset.card_insert_of_notMem (by simp [hjk, hjl]),
      Finset.card_insert_of_notMem (by simp [hkl])]
    simp

theorem crossCost_eq (w : Fin 2 × Fin 2 → ℂ) (i j k l : Fin 2 × Fin 2) (hj : j ≠ i) (hk : k ≠ i)
    (hl : l ≠ i) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    crossCost w i = 2 * (Complex.normSq (w j) * Complex.normSq (w k) +
      Complex.normSq (w j) * Complex.normSq (w l) + Complex.normSq (w k) * Complex.normSq (w l)) := by
  unfold crossCost
  rw [univ_erase_eq i j k l hj hk hl hjk hjl hkl, Finset.sum_insert (by simp [hjk, hjl]),
    Finset.sum_insert (by simp [hkl]), Finset.sum_singleton, Finset.sum_insert (by simp [hjk, hjl]),
    Finset.sum_insert (by simp [hkl]), Finset.sum_singleton]
  ring

/-- **`prop:fqe-two-flat-rigidity`, consequence**: for a unit state with two maximally mixed
balanced cuts (`12|34`, `13|24` of purity `1/4`), the third cut `14|23` has at least two zero
spectrum entries in the normal form, i.e. Schmidt rank at most two. -/
theorem two_flat_rank (ψ : Psi) (hn : normSqPsi ψ = 1) (h12 : cutPurity12 ψ = 1 / 4)
    (h13 : cutPurity13 ψ = 1 / 4) :
    ∃ v : Fin 2 × Fin 2 → ℂ, LUEquiv (Gv v) ψ ∧ ∑ k, Complex.normSq (v k) = 1 ∧
      ∃ a b, a ≠ b ∧ wm v a = 0 ∧ wm v b = 0 := by
  have hW := blochSq_zero_of_cutPurity12 ψ hn h12
  obtain ⟨v, hv, hnv, c12, c13, c14, -, -, t3⟩ := two_flat_rigidity ψ hn hW
  refine ⟨v, hv, hnv, ?_⟩
  have hP := Gv_purity_tau v hnv
  have hsum : purity (Gv v) = cutPurity12 (Gv v) + cutPurity13 (Gv v) + cutPurity14 (Gv v) := rfl
  obtain ⟨e12, e13, e14⟩ := cutPurities_LUEquiv hv
  have hτ := Complex.normSq_nonneg (∑ k, v k ^ 2)
  have hp14 : 1 / 2 ≤ ∑ k, Complex.normSq (wm v k) ^ 2 := by
    rw [← c14, e14]; rw [e12] at h12; rw [e13] at h13; linarith
  have hn' : ∑ k, Complex.normSq (wm v k) = 1 := (wm_normSq_sum v).trans hnv
  obtain ⟨i, hi⟩ := exists_big_entry (wm v) hn' hp14
  have hcost := t3 i hi
  rw [h12, h13] at hcost
  obtain ⟨j, k, l, hj, hk, hl, hjk, hjl, hkl⟩ := exists_three_others i
  rw [crossCost_eq (wm v) i j k l hj hk hl hjk hjl hkl] at hcost
  have a1 := Complex.normSq_nonneg (wm v j)
  have a2 := Complex.normSq_nonneg (wm v k)
  have a3 := Complex.normSq_nonneg (wm v l)
  have p1 : Complex.normSq (wm v j) * Complex.normSq (wm v k) = 0 := by
    nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]
  have p2 : Complex.normSq (wm v j) * Complex.normSq (wm v l) = 0 := by
    nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]
  have p3 : Complex.normSq (wm v k) * Complex.normSq (wm v l) = 0 := by
    nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]
  have z : ∀ x : Fin 2 × Fin 2, Complex.normSq (wm v x) = 0 → wm v x = 0 := fun x hx =>
    Complex.normSq_eq_zero.mp hx
  by_cases hj0 : Complex.normSq (wm v j) = 0
  · rcases mul_eq_zero.mp p3 with h | h
    · exact ⟨j, k, hjk, z j hj0, z k h⟩
    · exact ⟨j, l, hjl, z j hj0, z l h⟩
  · exact ⟨k, l, hkl, z k ((mul_eq_zero.mp p1).resolve_left hj0), z l ((mul_eq_zero.mp p2).resolve_left hj0)⟩

end FormalResearch.FourQubitEntropy.PaperECritical

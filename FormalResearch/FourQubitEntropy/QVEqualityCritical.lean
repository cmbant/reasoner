module

public import FormalResearch.FourQubitEntropy.QVEqualityBridge
public import FormalResearch.FourQubitEntropy.RenyiFullState

/-!
# Critical states: cut spectra in `(m, n)` coordinates and the profile `prop:fqe-critical-variance`

Paper E, `renyi_compatibility.tex`, `prop:fqe-critical-variance` (RF) for pure four-qubit states with `P = 1`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull
open FormalResearch.FourQubitEntropy.PaperECritical

/-! ### Spectra up to a permutation -/

theorem exists_perm_of_multiset_eq {α : Type*} [Fintype α] [DecidableEq α] {l l' : α → ℝ}
    (h : Multiset.map l Finset.univ.val = Multiset.map l' Finset.univ.val) :
    ∃ e : Equiv.Perm α, ∀ i, l i = l' (e i) := by
  classical
  have hc : ∀ c : ℝ, Fintype.card {a // l a = c} = Fintype.card {a // l' a = c} := by
    intro c
    have := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at this
    simp only [Fintype.card_subtype]
    simpa [Finset.card, Finset.filter_val, eq_comm] using this
  let e := Equiv.ofFiberEquiv (f := l) (g := l') (fun c => Fintype.equivOfCardEq (hc c))
  exact ⟨e, fun i => (Equiv.ofFiberEquiv_map _ i).symm⟩

/-- `l` is a rearrangement of `l'`. -/
def SpecEquiv (l l' : Fin 4 → ℝ) : Prop := ∃ e : Equiv.Perm (Fin 4), ∀ i, l i = l' (e i)

theorem SpecEquiv.isHsPerm {l l' : Fin 4 → ℝ} (h : SpecEquiv l l') (h' : IsHsPerm l') : IsHsPerm l := by
  obtain ⟨e, he⟩ := h
  obtain ⟨σ, hσ⟩ := h'
  exact ⟨e.trans σ, fun i => by rw [he i, hσ]; rfl⟩

theorem SpecEquiv.uniformFour {l l' : Fin 4 → ℝ} (h : SpecEquiv l l') (h' : UniformFour l') :
    UniformFour l := by
  obtain ⟨e, he⟩ := h
  intro i; rw [he i]; exact h' _

theorem SpecEquiv.uniformTwo {l l' : Fin 4 → ℝ} (h : SpecEquiv l l') (h' : UniformTwo l') :
    UniformTwo l := by
  obtain ⟨e, he⟩ := h
  obtain ⟨i, j, hij, hi, hj, hk⟩ := h'
  refine ⟨e.symm i, e.symm j, fun h => hij (e.symm.injective h), ?_, ?_, fun k hk1 hk2 => ?_⟩
  · rw [he]; simpa using hi
  · rw [he]; simpa using hj
  · rw [he]
    apply hk
    · intro h; apply hk1; rw [← h]; simp
    · intro h; apply hk2; rw [← h]; simp

/-! ### Cut spectra of `G(v)` and of its local-unitary images -/

theorem eig_congr {A B : Mat4} (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A = B) :
    hA.eigenvalues = hB.eigenvalues := by subst h; rfl

/-- Explicit reindexing `Fin 4 ≃ Fin 2 × Fin 2` with `0 ↦ (0,0)`, `1 ↦ (0,1)`, `2 ↦ (1,0)`, `3 ↦ (1,1)`. -/
def eqv : Fin 4 ≃ Fin 2 × Fin 2 where
  toFun := ![(0, 0), (0, 1), (1, 0), (1, 1)]
  invFun := fun p => ![![0, 1], ![2, 3]] p.1 p.2
  left_inv := by decide
  right_inv := by decide

theorem listing12_of_diag (v : Fin 2 × Fin 2 → ℂ) (lam : Fin 4 → ℝ)
    (hl : ∀ k, lam k = Complex.normSq (v (eqv k))) :
    IsSpectrumListing (red12_herm (Gv v)) lam := by
  refine listing_of_diag (Gv v) v (zmat_Gv v) lam ?_
  have : lam = (fun k => Complex.normSq (v k)) ∘ eqv := funext hl
  rw [this, map_univ_val_equiv eqv (fun k => Complex.normSq (v k))]

theorem listing13_of_diag (v : Fin 2 × Fin 2 → ℂ) (lam : Fin 4 → ℝ)
    (hl : ∀ k, lam k = Complex.normSq (wp v (eqv k))) :
    IsSpectrumListing (red13_herm (Gv v)) lam := by
  unfold IsSpectrumListing
  rw [eig_congr (red13_herm (Gv v)) (red12_herm (Gv (wp v))) (by rw [red13_eq_swap, swap23_Gv])]
  exact listing12_of_diag (wp v) lam hl

theorem listing14_of_diag (v : Fin 2 × Fin 2 → ℂ) (lam : Fin 4 → ℝ)
    (hl : ∀ k, lam k = Complex.normSq (wm v (eqv k))) :
    IsSpectrumListing (red14_herm (Gv v)) lam := by
  unfold IsSpectrumListing
  rw [eig_congr (red14_herm (Gv v)) (red12_herm (Gv (wm v))) (by rw [red14_eq_swap, swap24_Gv])]
  exact listing12_of_diag (wm v) lam hl

theorem listing12_LU {φ ψ : Psi} (h : LUEquiv φ ψ) {lam : Fin 4 → ℝ}
    (hl : IsSpectrumListing (red12_herm φ) lam) : IsSpectrumListing (red12_herm ψ) lam := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  unfold IsSpectrumListing at hl ⊢
  rw [eigMultiset_conj (red12_herm φ) _ (kron_unitary ha hb) (red12_localApply hc hd φ)]
  exact hl

theorem listing13_LU {φ ψ : Psi} (h : LUEquiv φ ψ) {lam : Fin 4 → ℝ}
    (hl : IsSpectrumListing (red13_herm φ) lam) : IsSpectrumListing (red13_herm ψ) lam := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  unfold IsSpectrumListing at hl ⊢
  rw [eigMultiset_conj (red13_herm φ) _ (kron_unitary ha hc) (red13_localApply hb hd φ)]
  exact hl

theorem listing14_LU {φ ψ : Psi} (h : LUEquiv φ ψ) {lam : Fin 4 → ℝ}
    (hl : IsSpectrumListing (red14_herm φ) lam) : IsSpectrumListing (red14_herm ψ) lam := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  unfold IsSpectrumListing at hl ⊢
  rw [eigMultiset_conj (red14_herm φ) _ (kron_unitary ha hd) (red14_localApply hc hb φ)]
  exact hl

/-- A listing of the cut spectrum gives a rearrangement of `cutSpec₂ ψ`. -/
theorem specEquiv_cutSpec₂ (ψ : Psi) {lam : Fin 4 → ℝ} (h : IsSpectrumListing (red12_herm ψ) lam) :
    SpecEquiv (cutSpec₂ ψ) lam := by
  apply exists_perm_of_multiset_eq
  unfold cutSpec₂ spec4
  rw [map_univ_val_equiv cutEquiv.symm (red12_herm ψ).eigenvalues]
  exact h.symm

theorem specEquiv_cutSpec₃ (ψ : Psi) {lam : Fin 4 → ℝ} (h : IsSpectrumListing (red13_herm ψ) lam) :
    SpecEquiv (cutSpec₃ ψ) lam := by
  apply exists_perm_of_multiset_eq
  unfold cutSpec₃ spec4
  rw [map_univ_val_equiv cutEquiv.symm (red13_herm ψ).eigenvalues]
  exact h.symm

theorem specEquiv_cutSpec₄ (ψ : Psi) {lam : Fin 4 → ℝ} (h : IsSpectrumListing (red14_herm ψ) lam) :
    SpecEquiv (cutSpec₄ ψ) lam := by
  apply exists_perm_of_multiset_eq
  unfold cutSpec₄ spec4
  rw [map_univ_val_equiv cutEquiv.symm (red14_herm ψ).eigenvalues]
  exact h.symm

/-! ### The cut vectors in real coordinates -/

theorem normSq_wp_eq (v : Fin 2 × Fin 2 → ℂ) (k : Fin 4) :
    Complex.normSq (wp v (eqv k)) =
      Hp (fun i => (v (eqv i)).re) k ^ 2 + Hp (fun i => (v (eqv i)).im) k ^ 2 := by
  fin_cases k <;>
  simp [eqv, wp, Hp, Complex.normSq_apply, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

theorem normSq_wm_eq (v : Fin 2 × Fin 2 → ℂ) (k : Fin 4) :
    Complex.normSq (wm v (eqv k)) =
      Hm (fun i => (v (eqv i)).re) k ^ 2 + Hm (fun i => (v (eqv i)).im) k ^ 2 := by
  fin_cases k <;>
  simp [eqv, wm, Hm, Complex.normSq_apply, Complex.div_ofNat_re, Complex.div_ofNat_im] <;> ring

/-! ### `G(v)` with `Σ v_k² = 0`: the `(m, n)` coordinates -/

/-- **The critical bridge for `G(v)`.**  For `Σ |v_k|² = 1`, `Σ v_k² = 0` there are unit `m, n ∈ ℝ³` whose
cut spectra `spc0, spc1, spc2` list the three cut spectra of `G(v)`. -/
theorem gv_cut_data (v : Fin 2 × Fin 2 → ℂ) (hn : ∑ k, Complex.normSq (v k) = 1)
    (hτ : ∑ k, v k ^ 2 = 0) :
    ∃ m n : Fin 3 → ℝ, m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1 ∧ n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 ∧
      IsSpectrumListing (red12_herm (Gv v)) (spc0 m n) ∧
      IsSpectrumListing (red13_herm (Gv v)) (spc1 m n) ∧
      IsSpectrumListing (red14_herm (Gv v)) (spc2 m n) := by
  set a : Fin 4 → ℝ := fun i => (v (eqv i)).re with ha
  set b : Fin 4 → ℝ := fun i => (v (eqv i)).im with hb
  have hre := congrArg Complex.re hτ
  have him := congrArg Complex.im hτ
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.add_re, Complex.add_im, pow_two,
    Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hre him
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply] at hn
  have hA : a 0 ^ 2 + a 1 ^ 2 + a 2 ^ 2 + a 3 ^ 2 = 1 / 2 := by
    simp [ha, eqv]; nlinarith
  have hB : b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 1 / 2 := by
    simp [hb, eqv]; nlinarith
  have hC : a 0 * b 0 + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 = 0 := by
    simp [ha, hb, eqv]; nlinarith
  have nn : ∀ k, Complex.normSq (v (eqv k)) = a k ^ 2 + b k ^ 2 := fun k => by
    rw [Complex.normSq_apply]; simp only [ha, hb]; ring
  refine ⟨mOf a b, nOf a b, mOf_unit a b hA hB hC, nOf_unit a b hA hB hC, ?_, ?_, ?_⟩
  · exact listing12_of_diag v _ (fun k => by rw [nn, bridge_cut0 a b hA hB hC])
  · refine listing13_of_diag v _ (fun k => ?_)
    rw [normSq_wp_eq, ← bridge_cut1 a b hA hB hC]
  · refine listing14_of_diag v _ (fun k => ?_)
    rw [normSq_wm_eq, ← bridge_cut2 a b hA hB hC]

/-- **Critical states in `(m, n)` coordinates.**  A unit pure four-qubit state with `P = 1` has cut spectra
which are rearrangements of `spc0, spc1, spc2` of unit vectors `m, n ∈ ℝ³`. -/
theorem critical_cut_data (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1) :
    ∃ m n : Fin 3 → ℝ, m 0 ^ 2 + m 1 ^ 2 + m 2 ^ 2 = 1 ∧ n 0 ^ 2 + n 1 ^ 2 + n 2 ^ 2 = 1 ∧
      SpecEquiv (cutSpec₂ ψ) (spc0 m n) ∧ SpecEquiv (cutSpec₃ ψ) (spc1 m n) ∧
      SpecEquiv (cutSpec₄ ψ) (spc2 m n) := by
  obtain ⟨hW, -⟩ := purity_one_forces ψ hn hP
  obtain ⟨v, hv⟩ := critical_LU_Gv ψ hW
  have hnv : ∑ k, Complex.normSq (v k) = 1 := by
    rw [← Gv_n, ← normSqPsi_LUEquiv hv]; exact hn
  have hPv : purity ψ = purity (Gv v) := by
    obtain ⟨e12, e13, e14⟩ := cutPurities_LUEquiv hv
    rw [purity_eq_cuts ψ, purity_eq_cuts (Gv v), e12, e13, e14]
  have hτ0 : ∑ k, v k ^ 2 = 0 := by
    have := Gv_purity_tau v hnv
    rw [← hPv, hP] at this
    have h0 : Complex.normSq (∑ k, v k ^ 2) = 0 := by linarith
    exact Complex.normSq_eq_zero.mp h0
  obtain ⟨m, n, hm, hn', l12, l13, l14⟩ := gv_cut_data v hnv hτ0
  exact ⟨m, n, hm, hn', specEquiv_cutSpec₂ ψ (listing12_LU hv l12),
    specEquiv_cutSpec₃ ψ (listing13_LU hv l13), specEquiv_cutSpec₄ ψ (listing14_LU hv l14)⟩

end FormalResearch.FourQubitEntropy.QVEquality

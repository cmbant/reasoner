module

public import FormalResearch.FourQubitEntropy.PaperECriticalSexticLU
public import FormalResearch.FourQubitEntropy.Rigidity
public import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlat
public import FormalResearch.FourQubitEntropy.RenyiRankTwoSharp

/-!
# Invariance of the cut spectra under local unitaries and qubit exchanges

Helper for the Rényi consequence of `prop:fqe-two-flat-rigidity`.  If `R' = K R Kᴴ` with `Kᴴ K = 1`,
the eigenvalue multisets of the Hermitian matrices `R, R'` agree (equal characteristic polynomials), so
every spectral sum `cutSum f` agrees.  Consequently `meanRenyi q` and `meanEntropy` are invariant under
`LUEquiv` and under the exchanges `swap23`, `swap24` of qubits (which permute the three cuts through
qubit `1`).
-/

@[expose] public section


set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

theorem eigMultiset_conj {R R' K : Mat4} (hR : R.IsHermitian) (hR' : R'.IsHermitian)
    (hK : Kᴴ * K = 1) (h : R' = K * R * Kᴴ) :
    Multiset.map hR'.eigenvalues Finset.univ.val = Multiset.map hR.eigenvalues Finset.univ.val := by
  have hc : R'.charpoly = R.charpoly := by
    rw [h, Matrix.mul_assoc, Matrix.charpoly_mul_comm, Matrix.mul_assoc, hK, Matrix.mul_one]
  have h1 := hR'.roots_charpoly_eq_eigenvalues
  have h2 := hR.roots_charpoly_eq_eigenvalues
  rw [hc, h2] at h1
  have e1 : Multiset.map (RCLike.ofReal ∘ hR'.eigenvalues) Finset.univ.val =
      Multiset.map Complex.ofReal (Multiset.map hR'.eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  have e2 : Multiset.map (RCLike.ofReal ∘ hR.eigenvalues) Finset.univ.val =
      Multiset.map Complex.ofReal (Multiset.map hR.eigenvalues Finset.univ.val) := by
    rw [Multiset.map_map]; rfl
  rw [e1, e2] at h1
  exact (Multiset.map_injective Complex.ofReal_injective h1).symm

theorem cutSum_eq_of_multiset (f : ℝ → ℝ) {R R' : Mat4} (hR : R.IsHermitian) (hR' : R'.IsHermitian)
    (h : Multiset.map hR'.eigenvalues Finset.univ.val = Multiset.map hR.eigenvalues Finset.univ.val) :
    cutSum f hR' = cutSum f hR := by
  unfold cutSum
  have e : ∀ {S : Mat4} (hS : S.IsHermitian),
      ∑ i, f (hS.eigenvalues i) = (Multiset.map f (Multiset.map hS.eigenvalues Finset.univ.val)).sum := by
    intro S hS; rw [Multiset.map_map]; rfl
  rw [e hR', e hR, h]

theorem cutSum_conj (f : ℝ → ℝ) {R R' K : Mat4} (hR : R.IsHermitian) (hR' : R'.IsHermitian)
    (hK : Kᴴ * K = 1) (h : R' = K * R * Kᴴ) : cutSum f hR' = cutSum f hR :=
  cutSum_eq_of_multiset f hR hR' (eigMultiset_conj hR hR' hK h)

theorem cutSum_congr (f : ℝ → ℝ) {R R' : Mat4} (hR : R.IsHermitian) (hR' : R'.IsHermitian)
    (h : R = R') : cutSum f hR = cutSum f hR' := by
  subst h; rfl

/-- The three cut sums of a local-unitary image agree with those of the original. -/
theorem cutSums_LU (f : ℝ → ℝ) {φ ψ : Psi} (h : LUEquiv φ ψ) :
    cutSum f (red12_herm ψ) = cutSum f (red12_herm φ) ∧
    cutSum f (red13_herm ψ) = cutSum f (red13_herm φ) ∧
    cutSum f (red14_herm ψ) = cutSum f (red14_herm φ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  refine ⟨cutSum_conj f _ _ (kron_unitary ha hb) (red12_localApply hc hd φ),
    cutSum_conj f _ _ (kron_unitary ha hc) (PaperECritical.red13_localApply hb hd φ),
    cutSum_conj f _ _ (kron_unitary ha hd) (PaperECritical.red14_localApply hc hb φ)⟩

theorem renyiCut_eq_cutSum (q : ℝ) {R : Mat4} (hR : R.IsHermitian) :
    renyiCut q hR = Real.logb 2 (cutSum (fun x => x ^ q) hR) / (1 - q) := rfl

theorem vnEntropy_eq_cutSum {R : Mat4} (hR : R.IsHermitian) :
    vnEntropy hR = cutSum Real.negMulLog hR / Real.log 2 := rfl

theorem meanRenyi_LU (q : ℝ) {φ ψ : Psi} (h : LUEquiv φ ψ) : meanRenyi q ψ = meanRenyi q φ := by
  obtain ⟨e1, e2, e3⟩ := cutSums_LU (fun x => x ^ q) h
  unfold meanRenyi
  rw [renyiCut_eq_cutSum, renyiCut_eq_cutSum, renyiCut_eq_cutSum, renyiCut_eq_cutSum,
    renyiCut_eq_cutSum, renyiCut_eq_cutSum, e1, e2, e3]

theorem meanEntropy_LU {φ ψ : Psi} (h : LUEquiv φ ψ) : meanEntropy ψ = meanEntropy φ := by
  obtain ⟨e1, e2, e3⟩ := cutSums_LU Real.negMulLog h
  unfold meanEntropy
  rw [vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, vnEntropy_eq_cutSum,
    vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, e1, e2, e3]

/-! ### Qubit exchanges -/

theorem meanRenyi_swap24 (q : ℝ) (ψ : Psi) : meanRenyi q (swap24 ψ) = meanRenyi q ψ := by
  unfold meanRenyi
  rw [renyiCut_eq_cutSum, renyiCut_eq_cutSum, renyiCut_eq_cutSum, renyiCut_eq_cutSum,
    renyiCut_eq_cutSum, renyiCut_eq_cutSum,
    cutSum_congr _ (red12_herm (swap24 ψ)) (red14_herm ψ) (red12_swap24 ψ),
    cutSum_congr _ (red13_herm (swap24 ψ)) (red13_herm ψ) (red13_swap24 ψ),
    cutSum_congr _ (red14_herm (swap24 ψ)) (red12_herm ψ) (red14_swap24 ψ)]
  ring

theorem meanRenyi_swap23 (q : ℝ) (ψ : Psi) : meanRenyi q (swap23 ψ) = meanRenyi q ψ := by
  unfold meanRenyi
  rw [renyiCut_eq_cutSum, renyiCut_eq_cutSum, renyiCut_eq_cutSum, renyiCut_eq_cutSum,
    renyiCut_eq_cutSum, renyiCut_eq_cutSum,
    cutSum_congr _ (red12_herm (swap23 ψ)) (red13_herm ψ) (red12_swap23 ψ),
    cutSum_congr _ (red13_herm (swap23 ψ)) (red12_herm ψ) (red13_swap23 ψ),
    cutSum_congr _ (red14_herm (swap23 ψ)) (red14_herm ψ) (red14_swap23 ψ)]
  ring

theorem meanEntropy_swap24 (ψ : Psi) : meanEntropy (swap24 ψ) = meanEntropy ψ := by
  unfold meanEntropy
  rw [vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, vnEntropy_eq_cutSum,
    vnEntropy_eq_cutSum, vnEntropy_eq_cutSum,
    cutSum_congr _ (red12_herm (swap24 ψ)) (red14_herm ψ) (red12_swap24 ψ),
    cutSum_congr _ (red13_herm (swap24 ψ)) (red13_herm ψ) (red13_swap24 ψ),
    cutSum_congr _ (red14_herm (swap24 ψ)) (red12_herm ψ) (red14_swap24 ψ)]
  ring

theorem meanEntropy_swap23 (ψ : Psi) : meanEntropy (swap23 ψ) = meanEntropy ψ := by
  unfold meanEntropy
  rw [vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, vnEntropy_eq_cutSum, vnEntropy_eq_cutSum,
    vnEntropy_eq_cutSum, vnEntropy_eq_cutSum,
    cutSum_congr _ (red12_herm (swap23 ψ)) (red13_herm ψ) (red12_swap23 ψ),
    cutSum_congr _ (red13_herm (swap23 ψ)) (red12_herm ψ) (red13_swap23 ψ),
    cutSum_congr _ (red14_herm (swap23 ψ)) (red14_herm ψ) (red14_swap23 ψ)]
  ring

end FormalResearch.FourQubitEntropy

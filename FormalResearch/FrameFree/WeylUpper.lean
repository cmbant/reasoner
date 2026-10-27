import FormalResearch.FrameFree.WeylRealisation
import FormalResearch.FrameFree.WeylVertex

open scoped ComplexConjugate Matrix Kronecker
open FormalResearch.FourQubitEntropy

namespace FormalResearch.FrameFree.WeylUpper

/-- The entries of `a ∈ SU(2)`: `ā₀₀ = a₁₁`, `ā₁₀ = -a₀₁`. -/
theorem su2_entries {a : Op1} (h : SU2 a) : conj (a 0 0) = a 1 1 ∧ conj (a 1 0) = - a 0 1 := by
  have hadj : aᴴ = a.adjugate := by
    have h1 : a * a.adjugate = 1 := by rw [Matrix.mul_adjugate, h.2]; simp
    calc aᴴ = aᴴ * (a * a.adjugate) := by rw [h1, Matrix.mul_one]
      _ = (aᴴ * a) * a.adjugate := by rw [Matrix.mul_assoc]
      _ = a.adjugate := by rw [h.1, Matrix.one_mul]
  have e1 := congrFun (congrFun hadj 0) 0
  have e2 := congrFun (congrFun hadj 0) 1
  simp [Matrix.conjTranspose_apply, Matrix.adjugate_fin_two] at e1 e2
  exact ⟨e1, by simpa using e2⟩

theorem eps_conj_eps {a : Op1} (h : SU2 a) : eps2 * a.map conj * eps2 = -a := by
  obtain ⟨h1, h2⟩ := su2_entries h
  have h1' : conj (a 1 1) = a 0 0 := by rw [← h1, Complex.conj_conj]
  have h2' : conj (a 0 1) = - a 1 0 := by
    have := congrArg conj h2
    rw [Complex.conj_conj, map_neg] at this
    linear_combination this
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [eps2, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, h1, h2, h1', h2']

theorem E4_conj_kron {a b : Op1} (ha : SU2 a) (hb : SU2 b) :
    E4 * (kron a b).map conj * E4 = kron a b := by
  have hk : (kron a b).map conj = (a.map conj) ⊗ₖ (b.map conj) := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩; simp [kron, Matrix.kroneckerMap_apply]
  unfold E4 kron at *
  rw [hk, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, eps_conj_eps ha, eps_conj_eps hb]
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  simp [Matrix.kroneckerMap_apply]

theorem E4_mul_magicB : E4 * magicB = magicB.map conj := by
  calc E4 * magicB = (magicB.map conj * magicBᵀ) * (E4 * magicB) := by
        rw [magicBbar_mul, Matrix.one_mul]
    _ = magicB.map conj * (magicBᵀ * E4 * magicB) := by simp only [Matrix.mul_assoc]
    _ = magicB.map conj := by rw [magicB_E4, Matrix.mul_one]

theorem E4_conjTranspose : E4ᴴ = E4 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [E4, kron, eps2, Matrix.kroneckerMap_apply, Matrix.conjTranspose_apply]

theorem magicBT_eq : magicBᵀ = magicBᴴ * E4 := by
  have h := congrArg Matrix.conjTranspose E4_mul_magicB
  rw [Matrix.conjTranspose_mul, E4_conjTranspose] at h
  rw [h]
  ext i j; simp [Matrix.conjTranspose_apply]

/-- For `a, b ∈ SU(2)` the matrix `Bᴴ (a ⊗ b) B` of the rotation in magic coordinates is real. -/
theorem magic_real {a b : Op1} (ha : SU2 a) (hb : SU2 b) :
    (magicBᴴ * kron a b * magicB).map conj = magicBᴴ * kron a b * magicB := by
  have h1 : (magicBᴴ).map conj = magicBᴴ * E4 := by rw [← magicBT_eq]; ext i j; simp [Matrix.conjTranspose_apply]
  rw [Matrix.map_mul (f := starRingEnd ℂ), Matrix.map_mul (f := starRingEnd ℂ), h1, ← E4_mul_magicB]
  calc magicBᴴ * E4 * (kron a b).map conj * (E4 * magicB)
      = magicBᴴ * (E4 * (kron a b).map conj * E4) * magicB := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [E4_conj_kron ha hb]

theorem cmat_injective : Function.Injective cmat :=
  Matrix.map_injective Complex.ofReal_injective

theorem cmat_transpose (P : Matrix Pair Pair ℝ) : cmat Pᵀ = (cmat P)ᴴ := by
  ext i j; simp [cmat, Matrix.conjTranspose_apply]

theorem det_cmat (P : Matrix Pair Pair ℝ) : (cmat P).det = (P.det : ℂ) := by
  have := RingHom.map_det Complex.ofRealHom P
  exact this.symm

theorem det_kron {a b : Op1} (ha : SU2 a) (hb : SU2 b) : (kron a b).det = 1 := by
  unfold kron
  rw [Matrix.det_kronecker, ha.2, hb.2]; simp

/-- **Local `SU(2)` rotations are real `SO(4)` rotations in magic coordinates.** -/
theorem exists_real_rep {a b : Op1} (ha : SU2 a) (hb : SU2 b) :
    ∃ P : Matrix Pair Pair ℝ, kron a b * magicB = magicB * cmat P ∧ Pᵀ * P = 1 ∧ P.det = 1 := by
  set M : Mat4 := magicBᴴ * kron a b * magicB with hM
  have hreal := magic_real ha hb
  set P : Matrix Pair Pair ℝ := Matrix.of fun i j => (M i j).re with hP
  have hPM : cmat P = M := by
    ext i j
    have him : (M i j).im = 0 := by
      have := congrFun (congrFun hreal i) j
      simpa [Matrix.map_apply, Complex.conj_eq_iff_im] using this
    apply Complex.ext <;> simp [cmat, hP, him]
  refine ⟨P, ?_, ?_, ?_⟩
  · rw [hPM, hM]
    calc kron a b * magicB = (magicB * magicBᴴ) * kron a b * magicB := by
          rw [magicB_unitary', Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]
  · apply cmat_injective
    rw [cmat_one, cmat_mul, cmat_transpose, hPM, hM]
    have hK := kron_unitary ha.1 hb.1
    calc (magicBᴴ * kron a b * magicB)ᴴ * (magicBᴴ * kron a b * magicB)
        = magicBᴴ * (kron a b)ᴴ * (magicB * magicBᴴ) * kron a b * magicB := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = magicBᴴ * ((kron a b)ᴴ * kron a b) * magicB := by
          rw [magicB_unitary']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [hK, Matrix.mul_one, magicB_unitary]
  · have h1 : (P.det : ℂ) = 1 := by
      rw [← det_cmat, hPM, hM, Matrix.det_mul, Matrix.det_mul, det_kron ha hb, mul_one,
        ← Matrix.det_mul, magicB_unitary]
      simp
    exact_mod_cast h1

/-! ### Reduction to a statement about pairs of `SO(4)` matrices -/

/-- `SO(4)` as real `4×4` matrices (indexed by `Fin 4`). -/
def SO4 (A : Matrix (Fin 4) (Fin 4) ℝ) : Prop := Aᵀ * A = 1 ∧ A.det = 1

/-- Reindexing `Pair → Fin 4`. -/
def reidx (P : Matrix Pair Pair ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  P.submatrix pairEquiv.symm pairEquiv.symm

theorem reidx_SO4 {P : Matrix Pair Pair ℝ} (h1 : Pᵀ * P = 1) (h2 : P.det = 1) : SO4 (reidx P) := by
  refine ⟨?_, ?_⟩
  · have : (reidx P)ᵀ * reidx P = (Pᵀ * P).submatrix pairEquiv.symm pairEquiv.symm := by
      unfold reidx
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    rw [this, h1]
    ext i j; simp [Matrix.one_apply]
  · unfold reidx
    rw [Matrix.det_submatrix_equiv_self, h2]

/-- The Hadamard pairing `∑ᵢⱼ xᵢ (A∘B)ᵢⱼ yⱼ`. -/
def hadPair (x y : Fin 4 → ℂ) (A B : Matrix (Fin 4) (Fin 4) ℝ) : ℂ :=
  ∑ i, ∑ j, x i * ((A i j : ℂ) * (B i j : ℂ)) * y j

/-- The Weyl-vertex pairing `∑ₖ xₖ (±1)ₖ y_{σ k}` for `w = (σ, e) ∈ W(D₄)`. -/
def weylPair (x y : Fin 4 → ℂ) (w : SP) : ℂ := ∑ k, x k * (sg (w.2 k) : ℂ) * y (w.1 k)

/-- **The missing real-matrix inequality** (`QI-A`, `thm:D4hadamard` in the form needed for
`cor:D4weylvertex`): for `A, B ∈ SO(4)` and complex vectors `x, y`, the Hadamard pairing
`x ⊤ (A∘B) y` is dominated by its largest value over the `192` even signed permutations. -/
def HadamardWeylBound : Prop :=
  ∀ (x y : Fin 4 → ℂ) (A B : Matrix (Fin 4) (Fin 4) ℝ), SO4 A → SO4 B →
    ∃ w ∈ weylSet, ‖hadPair x y A B‖ ≤ ‖weylPair x y w‖

theorem ip_local_so4 (d d' : Fin 4 → ℂ) {a b c e : Op1} (ha : SU2 a) (hb : SU2 b) (hc : SU2 c)
    (he : SU2 e) :
    ∃ A B : Matrix (Fin 4) (Fin 4) ℝ, SO4 A ∧ SO4 B ∧
      ip (psiMag d) (localApply a b c e (psiMag d')) = hadPair (fun k => conj (d k)) d' A B := by
  obtain ⟨P, hP, hP1, hP2⟩ := exists_real_rep ha hb
  obtain ⟨Q, hQ, hQ1, hQ2⟩ := exists_real_rep hc he
  refine ⟨reidx P, reidx Q, reidx_SO4 hP1 hP2, reidx_SO4 hQ1 hQ2, ?_⟩
  unfold psiMag
  rw [ip_local _ _ a b c e P Q hP hQ]
  unfold hadPair
  rw [← Equiv.sum_comp pairEquiv.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Equiv.sum_comp pairEquiv.symm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.apply_symm_apply, reidx, Matrix.submatrix_apply]
  ring

/-- The two-vector Weyl-vertex value `max_{w ∈ W(D₄)} |⟨d, w d'⟩|²`. -/
noncomputable def FKmag2 (d d' : Fin 4 → ℂ) : ℝ :=
  weylSet.sup' ⟨_, one_mem_weylSet⟩ fun w =>
    Complex.normSq (weylPair (fun k => conj (d k)) d' w)

theorem le_FKmag2 (d d' : Fin 4 → ℂ) {w : SP} (hw : w ∈ weylSet) :
    Complex.normSq (weylPair (fun k => conj (d k)) d' w) ≤ FKmag2 d d' :=
  Finset.le_sup' (fun w => Complex.normSq (weylPair (fun k => conj (d k)) d' w)) hw

theorem FKmag2_le_rotOverlap (d d' : Fin 4 → ℂ) :
    FKmag2 d d' ≤ rotOverlap (psiMag d) (psiMag d') := by
  unfold FKmag2
  refine Finset.sup'_le _ _ fun w hw => ?_
  have hw' := hw
  unfold weylSet at hw'
  rw [Finset.mem_filter] at hw'
  have hs : ∀ k, sg (w.2 k) = 1 ∨ sg (w.2 k) = -1 := by
    intro k; cases h : w.2 k <;> simp [sg]
  exact weyl_le_rotOverlap w.1 (fun k => sg (w.2 k)) hs hw'.2 d d'

/-- **Upper bound, conditional on the real-matrix inequality.** -/
theorem rotOverlap_le_FKmag2 (H : HadamardWeylBound) (d d' : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (psiMag d') ≤ FKmag2 d d' := by
  unfold rotOverlap
  refine csSup_le ⟨_, 1, 1, 1, 1, SU2.one, SU2.one, SU2.one, SU2.one, rfl⟩ ?_
  rintro x ⟨a, b, c, e, ha, hb, hc, he, rfl⟩
  obtain ⟨A, B, hA, hB, hip⟩ := ip_local_so4 d d' ha hb hc he
  obtain ⟨w, hw, hle⟩ := H (fun k => conj (d k)) d' A B hA hB
  rw [hip]
  refine le_trans ?_ (le_FKmag2 d d' hw)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- **Weyl-vertex formula (two-vector form), conditional on `HadamardWeylBound`.** -/
theorem rotOverlap_eq_FKmag2 (H : HadamardWeylBound) (d d' : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (psiMag d') = FKmag2 d d' :=
  le_antisymm (rotOverlap_le_FKmag2 H d d') (FKmag2_le_rotOverlap d d')

theorem FKmag2_conj (d : Fin 4 → ℂ) : FKmag2 d (fun k => conj (d k)) = FKmag d := by
  unfold FKmag2 FKmag
  refine Finset.sup'_congr _ rfl fun w _ => ?_
  rw [← Complex.normSq_conj]
  congr 1
  simp only [weylPair, weylVal, map_sum, map_mul, Complex.conj_conj, map_intCast]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **`thm:weyl` upper bound (conditional on `HadamardWeylBound`)**: the rotation overlap of
`ψ_d` with its time reverse is at most `FKmag d`. -/
theorem rotOverlap_conj_le_FKmag (H : HadamardWeylBound) (d : Fin 4 → ℂ) :
    rotOverlap (psiMag d) (Psi.conj (psiMag d)) ≤ FKmag d := by
  rw [conj_psiMag, ← FKmag2_conj]
  exact rotOverlap_le_FKmag2 H d _

end FormalResearch.FrameFree.WeylUpper

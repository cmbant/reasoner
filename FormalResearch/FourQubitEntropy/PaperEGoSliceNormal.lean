module

public import FormalResearch.FourQubitEntropy.PaperEGoSliceStat
public import FormalResearch.FourQubitEntropy.PaperEGoSliceFrame
public import FormalResearch.FourQubitEntropy.PaperEGoSliceMain

/-!
# `thm:fqe-global-overlap`, layer (b)/(c): the 19-coordinate normal slice

`SliceNormalForm` is proved (`sliceNormalForm`): every unit state has, in its LU class up to conjugation
and phase, a representative `sState v` on the 19-coordinate slice at which `Z_*` is a closest point.

* `exists_frame` (layer (a), `PaperEGoSliceFrame`) gives a closest-point frame `φ`;
* `stationary_of_frame` (layer (c), `PaperEGoSliceStat`) gives the ten linear relations of
  `eq:fqe-slice-stationary` for its magic coordinates `√3 X + i Y`;
* the symmetric matrix `Sym(X_jk) + 2 Y_jk` (`jk = 1..3`) is diagonalised by a simultaneous lower rotation
  `diag(1, R)`, `R ∈ SO(3)` (`exists_so3_diag`, the spectral theorem), realised by a local unitary fixing
  `Z_*` (`frame_rotate`), after which the relations and the diagonality give the 19 coordinates
  (`slice_of_rel`).
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

abbrev M3R := Matrix (Fin 3) (Fin 3) ℝ

/-! ### The spectral theorem in `SO(3)` -/

theorem det_orth3 {R : M3R} (hR : Rᵀ * R = 1) : R.det = 1 ∨ R.det = -1 := by
  have h := congrArg Matrix.det hR
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have : (R.det - 1) * (R.det + 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linarith
  · right; linarith

theorem exists_so3_diag (S : M3R) (hS : Sᵀ = S) :
    ∃ R : M3R, Rᵀ * R = 1 ∧ R.det = 1 ∧ ∀ i j, i ≠ j → (R * S * Rᵀ) i j = 0 := by
  have hH : S.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]; exact hS
  set U : M3R := ((hH.eigenvectorUnitary : Matrix.unitaryGroup (Fin 3) ℝ) : M3R) with hU
  have hUU : U * Uᵀ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.1 hH.eigenvectorUnitary.2
    simpa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hUtU : Uᵀ * U = 1 := mul_eq_one_comm.1 hUU
  have hD : Uᵀ * S * U = Matrix.diagonal (fun i => hH.eigenvalues i) := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    simpa [Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hoff : ∀ i j, i ≠ j → (Uᵀ * S * U) i j = 0 := by
    intro i j hij
    rw [hD]; simp [Matrix.diagonal_apply, hij]
  rcases det_orth3 hUtU with hd | hd
  · refine ⟨Uᵀ, by simpa using hUU, by rw [Matrix.det_transpose]; exact hd, fun i j hij => ?_⟩
    simpa using hoff i j hij
  · set F : M3R := Matrix.diagonal ![-1, 1, 1] with hF
    have hFF : F * F = 1 := by
      rw [hF, Matrix.diagonal_mul_diagonal]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    have hFt : Fᵀ = F := Matrix.diagonal_transpose _
    have hFd : F.det = -1 := by rw [hF, Matrix.det_diagonal]; simp [Fin.prod_univ_three]
    refine ⟨(U * F)ᵀ, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_transpose, Matrix.transpose_mul, hFt]
      calc U * F * (F * Uᵀ) = U * (F * F) * Uᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hFF, Matrix.mul_one, hUU]
    · rw [Matrix.det_transpose, Matrix.det_mul, hd, hFd]; norm_num
    · intro i j hij
      rw [Matrix.transpose_transpose, Matrix.transpose_mul, hFt]
      have e : F * Uᵀ * S * (U * F) = F * (Uᵀ * S * U) * F := by simp only [Matrix.mul_assoc]
      rw [e, hF]
      simp [Matrix.mul_diagonal, Matrix.diagonal_mul, hoff i j hij]


/-! ### The lower rotation `diag(1, R)` -/

/-- `diag(1, R)` for `R : 3 × 3`. -/
def lift4 (R : M3R) : M4R :=
  !![1, 0, 0, 0;
     0, R 0 0, R 0 1, R 0 2;
     0, R 1 0, R 1 1, R 1 2;
     0, R 2 0, R 2 1, R 2 2]

theorem RtR_entries {R : M3R} (hR : Rᵀ * R = 1) (a b : Fin 3) :
    ∑ k, R k a * R k b = if a = b then 1 else 0 := by
  have := congrFun (congrFun hR a) b
  simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] using this

theorem lift4_orth {R : M3R} (hR : Rᵀ * R = 1) : (lift4 R)ᵀ * lift4 R = 1 := by
  have e := RtR_entries hR
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [lift4, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> linarith

theorem lift4_00' (R : M3R) : lift4 R 0 0 = 1 := by simp [lift4]

theorem lift4_0s (R : M3R) (i : Fin 3) : lift4 R 0 i.succ = 0 := by
  fin_cases i <;> simp [lift4]

theorem lift4_det (R : M3R) : (lift4 R).det = R.det := by
  have hsub : (lift4 R).submatrix Fin.succ Fin.succ = R := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [lift4]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [lift4_00', lift4_0s, Fin.val_zero, pow_zero, one_mul, mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero, Fin.succAbove_zero, hsub]

theorem lift4_trace {R : M3R} (hR : Rᵀ * R = 1) (M : M4R) :
    (lift4 R * M * (lift4 R)ᵀ) 1 1 + (lift4 R * M * (lift4 R)ᵀ) 2 2 + (lift4 R * M * (lift4 R)ᵀ) 3 3
      = M 1 1 + M 2 2 + M 3 3 := by
  have e := RtR_entries hR
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e20 := e 2 0
  have e21 := e 2 1
  have e22 := e 2 2
  simp [Fin.sum_univ_three] at e00 e01 e02 e10 e11 e12 e20 e21 e22
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  simp [lift4]
  linear_combination (M 1 1) * e00 + (M 1 2) * e01 + (M 1 3) * e02 + (M 2 1) * e10 +
    (M 2 2) * e11 + (M 2 3) * e12 + (M 3 1) * e20 + (M 3 2) * e21 + (M 3 3) * e22

theorem lift4_00 (R : M3R) (M : M4R) : (lift4 R * M * (lift4 R)ᵀ) 0 0 = M 0 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
  simp [lift4]

/-! ### Overlap with `Z_*` in coordinates -/

theorem ip_Zs_of_coord {φ : Psi} {X Y : M4R} (hφ : CoordIs φ X Y) :
    ip (Gv (etaV 0)) φ = ∑ k : Fin 4, (starRingEnd ℂ) (etaC 0 k) * ZcG X Y k k := by
  rw [ip_Gv_coord, ← sum_pairG (fun k => (starRingEnd ℂ) (etaC 0 k) * ZcG X Y k k)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [hφ p p]
  rfl

theorem Dfun_rot {R : M3R} (hR : Rᵀ * R = 1) (X Y : M4R) :
    ∑ k : Fin 4, (starRingEnd ℂ) (etaC 0 k) *
        ZcG (lift4 R * X * (lift4 R)ᵀ) (lift4 R * Y * (lift4 R)ᵀ) k k =
      ∑ k : Fin 4, (starRingEnd ℂ) (etaC 0 k) * ZcG X Y k k := by
  have tX := lift4_trace hR X
  have tY := lift4_trace hR Y
  have h00X := lift4_00 R X
  have h00Y := lift4_00 R Y
  have c1 : ∀ k : Fin 4, k ≠ 0 → (starRingEnd ℂ) (etaC 0 k) =
      -(Complex.I * ((1 / Real.sqrt 6 : ℝ) : ℂ)) := by
    intro k hk
    rw [etaC0_pos k hk, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
  simp only [Fin.sum_univ_four, c1 1 (by decide), c1 2 (by decide), c1 3 (by decide)]
  simp only [ZcG]
  rw [h00X, h00Y]
  have e1 := congrArg (fun x : ℝ => ((Real.sqrt 3 * x : ℝ) : ℂ)) tX
  have e2 := congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) tY
  beta_reduce at e1 e2
  generalize ((1 / Real.sqrt 6 : ℝ) : ℂ) = κ
  push_cast at e1 e2 ⊢
  linear_combination (-(Complex.I * κ)) * (e1 + Complex.I * e2)

theorem frame_rotate {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    {R : M3R} (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    ∃ φ' : Psi, LUEquiv φ φ' ∧ IsFrame φ' h ∧
      CoordIs φ' (lift4 R * X * (lift4 R)ᵀ) (lift4 R * Y * (lift4 R)ᵀ) := by
  have hP : (toR (lift4 R))ᵀ * toR (lift4 R) = 1 := by
    rw [← toR_transpose, ← toR_mul, lift4_orth hR, toR_one]
  have hdP : (toR (lift4 R)).det = 1 := by rw [toR_det, lift4_det, hdet]
  obtain ⟨φ', hLU, hcoord⟩ := exists_LU_rotate hP hdP hP hdP (e := 1) (by simp) φ
  have hCI : CoordIs φ' (lift4 R * X * (lift4 R)ᵀ) (lift4 R * Y * (lift4 R)ᵀ) := by
    intro p q
    rw [hcoord]
    have hentry : ∀ i j : Fin 4, (∑ b : Fin 4, (∑ a : Fin 4, ((lift4 R) i a : ℂ) * ZcG X Y a b) *
        ((lift4 R) j b : ℂ)) =
        ZcG (lift4 R * X * (lift4 R)ᵀ) (lift4 R * Y * (lift4 R)ᵀ) i j := by
      intro i j
      simp only [ZcG, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_four]
      push_cast
      ring
    rw [← hentry]
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, rc_apply, one_smul,
      toR_apply]
    rw [← sum_pairG (fun j => (∑ a : Fin 4, ((lift4 R) (pairIdx p) a : ℂ) * ZcG X Y a j) *
      ((lift4 R) (pairIdx q) j : ℂ))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← sum_pairG (fun a => ((lift4 R) (pairIdx p) a : ℂ) * ZcG X Y a (pairIdx b))]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hφ a b]
  refine ⟨φ', hLU, ⟨?_, hf.2.1, ?_, ?_⟩, hCI⟩
  · rw [normSqPsi_LUEquiv hLU, hf.1]
  · rw [ip_Zs_of_coord hCI, Dfun_rot hR, ← ip_Zs_of_coord hφ]
    exact hf.2.2.1
  · intro χ hχ
    have := le_Phi (show normSqPsi φ' = 1 by rw [normSqPsi_LUEquiv hLU, hf.1]) hχ
    rw [Phi_LUEquiv hLU hf.1, hf.Phi_eq] at this
    rw [ip_comm χ φ', Complex.normSq_conj]
    exact this

/-! ### From the relations to the 19 coordinates -/

theorem slice_of_rel {X Y : M4R} (hs : Stationary X Y)
    (hd12 : (X 1 2 + X 2 1) / 2 + 2 * Y 1 2 = 0) (hd13 : (X 1 3 + X 3 1) / 2 + 2 * Y 1 3 = 0)
    (hd23 : (X 2 3 + X 3 2) / 2 + 2 * Y 2 3 = 0) :
    ∃ v : SV, sX v = X ∧ sY v = Y := by
  obtain ⟨r1, l1, l2, l3, m1, m2, m3, s12, s13, s23⟩ := hs
  refine ⟨![X 0 0, X 1 1, X 2 2, X 3 3, Y 1 1 - X 0 0, Y 2 2 - X 0 0, Y 3 3 - X 0 0,
    (X 1 2 + X 2 1) / 2, (X 1 3 + X 3 1) / 2, (X 2 3 + X 3 2) / 2,
    (X 1 2 - X 2 1) / 2, (X 1 3 - X 3 1) / 2, (X 2 3 - X 3 2) / 2,
    X 0 1, X 0 2, X 0 3, Y 0 1, Y 0 2, Y 0 3], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sX] <;> linarith
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [sY] <;> linarith


/-! ### The normal form -/

theorem exists_slice_frame {φ : Psi} {h : ℝ} (hf : IsFrame φ h) :
    ∃ v : SV, IsFrame (sState v) h ∧ LUEquiv φ (sState v) := by
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
  set X : M4R := Matrix.of fun i j =>
    (magicCoord (zmat φ) (pairEquiv.symm i) (pairEquiv.symm j)).re / Real.sqrt 3 with hX
  set Y : M4R := Matrix.of fun i j =>
    (magicCoord (zmat φ) (pairEquiv.symm i) (pairEquiv.symm j)).im with hY
  have hφ : CoordIs φ X Y := by
    intro p q
    have e : Real.sqrt 3 * ((magicCoord (zmat φ) p q).re / Real.sqrt 3) =
        (magicCoord (zmat φ) p q).re := by field_simp
    have hp : pairEquiv.symm (pairIdx p) = p := pairEquiv.symm_apply_apply p
    have hq : pairEquiv.symm (pairIdx q) = q := pairEquiv.symm_apply_apply q
    simp only [hX, hY, ZcG, Matrix.of_apply, hp, hq, e]
    apply Complex.ext <;> simp
  have st := stationary_of_frame hf hφ
  set S2 : M3R := Matrix.of fun i j =>
    (X i.succ j.succ + X j.succ i.succ) / 2 + 2 * Y i.succ j.succ with hS2
  have hsym : S2ᵀ = S2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hS2] <;> linarith [st.s12, st.s13, st.s23]
  obtain ⟨R, hR, hdet, hdiag⟩ := exists_so3_diag S2 hsym
  obtain ⟨φ', hLU, hf', hφ'⟩ := frame_rotate hf hφ hR hdet
  have st' := stationary_of_frame hf' hφ'
  have hrel : ∀ i j : Fin 3,
      ((lift4 R * X * (lift4 R)ᵀ) i.succ j.succ + (lift4 R * X * (lift4 R)ᵀ) j.succ i.succ) / 2 +
        2 * (lift4 R * Y * (lift4 R)ᵀ) i.succ j.succ = (R * S2 * Rᵀ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      (simp only [hS2, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
        Fin.sum_univ_four, Fin.sum_univ_three]
       simp [lift4]
       try ring)
  have hd12 := hdiag 0 1 (by decide)
  have hd13 := hdiag 0 2 (by decide)
  have hd23 := hdiag 1 2 (by decide)
  rw [← hrel 0 1] at hd12
  rw [← hrel 0 2] at hd13
  rw [← hrel 1 2] at hd23
  obtain ⟨v, hvX, hvY⟩ := slice_of_rel st' hd12 hd13 hd23
  have hsv : sState v = φ' := by
    have hc : magicCoord (zmat φ') = sZ v := by
      ext p q
      rw [hφ' p q, ← hvX, ← hvY]
      rfl
    unfold sState
    rw [← hc, ← zmat_eq_coord (zmat φ')]
    rfl
  refine ⟨v, ?_, ?_⟩
  · rw [hsv]; exact hf'
  · rw [hsv]; exact hLU

/-- **`SliceNormalForm` is a theorem.** -/
theorem sliceNormalForm : SliceNormalForm := by
  intro ψ hψ
  obtain ⟨φ, h, hf, hq, hP⟩ := exists_frame hψ
  obtain ⟨v, hfv, hLU⟩ := exists_slice_frame hf
  exact ⟨v, h, hfv, by rw [sexticQ_LUEquiv hLU, hq], hP⟩

/-- `GOSliceCertificate` and the two remaining hypotheses (`SliceQIdentity`, `FrameHess`) give
`thm:fqe-global-overlap`; the normal-slice coverage is proved. -/
theorem globalOverlap_of_slice_hess (cert : GOSliceCertificate) (hQ : SliceQIdentity)
    (hH : FrameHess) : ∀ ψ : Psi, normSqPsi ψ = 1 → GlobalOverlap ψ :=
  globalOverlap_of_slice_conditional cert hQ sliceNormalForm hH

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.sliceNormalForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sliceNormalForm

/-- info: 'FormalResearch.FourQubitEntropy.GO.globalOverlap_of_slice_hess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalOverlap_of_slice_hess

end

end FormalResearch.FourQubitEntropy.GO

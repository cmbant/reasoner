module

public import FormalResearch.FourQubitEntropy.QVFrame.Atoms

/-!
# T3: the homogenised defect `𝔇` as a quadratic form in `z^{⊗6}`

`𝔇 = 294 N²P² + 144 T² + 144 N⁶ - 408 N P T - 411 N⁴ P + 288 N³ T - 6 N² U`
(`= 𝔉² + 5 N² P² - 3 N⁴ P - 6 N² U`) with `P = Σ_c tr R_c²`, `T = Σ_c tr R_c³`, `U = Σ_c (tr R_c²)²`,
`c` over the cuts `{01|23}, {02|13}, {03|12}`.

`rhsOp` is the integer operator `K_RHS = Σ_i coef_i ⊗_q Π_{σ_{i,q}}` over the 37 permutation invariants of
`routeD/rhs.py` (the index set `RhsIdx = Fin 7 × Fin 3 × Fin 3` carries the shapes
`N⁶, N⁴P, N³T, N²U, N²P², T², NPT` and the cuts; entries with coefficient `0` are padding), and

`defectD_eq_qf : 𝔇(z) = ⟨z^{⊗6}, K_RHS z^{⊗6}⟩`.

The proof uses only: `tr R_c^k` is the invariant of a cyclic copy permutation on the cut (`atom2`, `atom3`),
`N` is a spare copy (`invG_one`) and products of invariants are invariants of block sums (`invG_bsum`).
It does not depend on the certificate data.
-/

@[expose] public section


open scoped ComplexConjugate
open scoped Matrix
open Finset

namespace FormalResearch.FourQubitEntropy.QVFrame

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.QVBlock

/-- `Σ_c |z_c|² = N`. -/
theorem sum_conj_mul (z : Psi) : ∑ c : Site, conj (zf z c) * zf z c = (normSqPsi z : ℂ) := by
  rw [sum_fin_four]
  unfold normSqPsi
  push_cast
  simp only [zf, Complex.normSq_eq_conj_mul_self]
  rfl

theorem invG_one' (n : ℕ) (z : Psi) :
    invG (Fin n) (fun _ => 1) (zf z) = (normSqPsi z : ℂ) ^ n := by
  rw [invG_one, Fintype.card_fin, sum_conj_mul]

/-- The cut masks `{0,1}, {0,2}, {0,3}`. -/
def cutM (c : Fin 3) : Fin 4 → Bool := cutMask (cutIdx c)

/-- Index set of the 37 permutation invariants: (shape, cut, cut'), shapes
`0: N⁶, 1: N⁴P, 2: N³T, 3: N²U, 4: N²P², 5: T², 6: NPT` (unused `(c,c')` have coefficient `0`). -/
abbrev RhsIdx := Fin 7 × Fin 3 × Fin 3

/-- The slot permutation of the qubits for each invariant (`routeD/rhs.py`: cycles `(0 1)`, `(0 1 2)` etc. acting on the
qubits of the cut, in consecutive blocks of slots). -/
def rhsPerm (i : RhsIdx) : Fin 4 → Equiv.Perm (Fin 6) :=
  ![(fun _ => 1),
    (bsum (cutPerm 2 (cutM i.2.1)) (fun _ => (1 : Equiv.Perm (Fin 4))) : Fin 4 → Equiv.Perm (Fin 6)),
    (bsum (cutPerm 3 (cutM i.2.1)) (fun _ => (1 : Equiv.Perm (Fin 3))) : Fin 4 → Equiv.Perm (Fin 6)),
    (bsum (cutPerm 2 (cutM i.2.1)) (bsum (cutPerm 2 (cutM i.2.1)) (fun _ => (1 : Equiv.Perm (Fin 2))))
      : Fin 4 → Equiv.Perm (Fin 6)),
    (bsum (cutPerm 2 (cutM i.2.1)) (bsum (cutPerm 2 (cutM i.2.2)) (fun _ => (1 : Equiv.Perm (Fin 2))))
      : Fin 4 → Equiv.Perm (Fin 6)),
    (bsum (cutPerm 3 (cutM i.2.1)) (cutPerm 3 (cutM i.2.2)) : Fin 4 → Equiv.Perm (Fin 6)),
    (bsum (cutPerm 2 (cutM i.2.1)) (bsum (cutPerm 3 (cutM i.2.2)) (fun _ => (1 : Equiv.Perm (Fin 1))))
      : Fin 4 → Equiv.Perm (Fin 6))] i.1

/-- The integer coefficients of the expansion of `𝔇`. -/
def rhsCoef (i : RhsIdx) : ℤ :=
  ![if i.2.1 = 0 ∧ i.2.2 = 0 then 144 else 0,
    if i.2.2 = 0 then -411 else 0,
    if i.2.2 = 0 then 288 else 0,
    if i.2.2 = 0 then -6 else 0,
    294, 144, -408] i.1

/-- `K_RHS = Σ_i coef_i ⊗_q Π_{σ_{i,q}}`, a sum of per-qubit Kronecker products of slot permutations. -/
def rhsOp : Matrix (Cfg 6) (Cfg 6) ℤ :=
  ∑ i : RhsIdx, rhsCoef i • kronPi (fun q => (slotPerm ℤ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℤ))

section shapes
variable (z : Psi)

/-- `tr R_c²` and `tr R_c³` as complex numbers. -/
noncomputable def A2 (z : Psi) (c : Fin 3) : ℂ := Matrix.trace (redC c z * redC c z)
noncomputable def A3 (z : Psi) (c : Fin 3) : ℂ := Matrix.trace (redC c z * redC c z * redC c z)

theorem shape1 (c : Fin 3) :
    invG (Fin (2 + 4)) (bsum (cutPerm 2 (cutM c)) (fun _ => (1 : Equiv.Perm (Fin 4)))) (zf z) =
      A2 z c * (normSqPsi z : ℂ) ^ 4 := by
  rw [invG_bsum, invG_one']; unfold cutM; rw [atom2]; rfl

theorem shape2 (c : Fin 3) :
    invG (Fin (3 + 3)) (bsum (cutPerm 3 (cutM c)) (fun _ => (1 : Equiv.Perm (Fin 3)))) (zf z) =
      A3 z c * (normSqPsi z : ℂ) ^ 3 := by
  rw [invG_bsum, invG_one']; unfold cutM; rw [atom3]; rfl

theorem shape4 (c c' : Fin 3) :
    invG (Fin (2 + (2 + 2))) (bsum (cutPerm 2 (cutM c))
      (bsum (cutPerm 2 (cutM c')) (fun _ => (1 : Equiv.Perm (Fin 2))))) (zf z) =
      A2 z c * (A2 z c' * (normSqPsi z : ℂ) ^ 2) := by
  rw [invG_bsum, invG_bsum, invG_one']; unfold cutM; rw [atom2, atom2]; rfl

theorem shape5 (c c' : Fin 3) :
    invG (Fin (3 + 3)) (bsum (cutPerm 3 (cutM c)) (cutPerm 3 (cutM c'))) (zf z) =
      A3 z c * A3 z c' := by
  rw [invG_bsum]; unfold cutM; rw [atom3, atom3]; rfl

theorem shape6 (c c' : Fin 3) :
    invG (Fin (2 + (3 + 1))) (bsum (cutPerm 2 (cutM c))
      (bsum (cutPerm 3 (cutM c')) (fun _ => (1 : Equiv.Perm (Fin 1))))) (zf z) =
      A2 z c * (A3 z c' * (normSqPsi z : ℂ) ^ 1) := by
  rw [invG_bsum, invG_bsum, invG_one']; unfold cutM; rw [atom2, atom3]; rfl

end shapes

/-- The value of the invariant of `rhsPerm i`: a product of the atoms. -/
noncomputable def rhsVal (i : RhsIdx) (z : Psi) : ℂ :=
  ![(normSqPsi z : ℂ) ^ 6, A2 z i.2.1 * (normSqPsi z : ℂ) ^ 4, A3 z i.2.1 * (normSqPsi z : ℂ) ^ 3,
    A2 z i.2.1 * (A2 z i.2.1 * (normSqPsi z : ℂ) ^ 2),
    A2 z i.2.1 * (A2 z i.2.2 * (normSqPsi z : ℂ) ^ 2), A3 z i.2.1 * A3 z i.2.2,
    A2 z i.2.1 * (A3 z i.2.2 * (normSqPsi z : ℂ) ^ 1)] i.1

theorem invG_rhsPerm (i : RhsIdx) (z : Psi) : invG (Fin 6) (rhsPerm i) (zf z) = rhsVal i z := by
  obtain ⟨k, c, c'⟩ := i
  fin_cases k
  · exact invG_one' 6 z
  · exact shape1 z c
  · exact shape2 z c
  · exact shape4 z c c
  · exact shape4 z c c'
  · exact shape5 z c c'
  · exact shape6 z c c'

theorem slotPerm_apply' {R : Type*} [Zero R] [One R] {n : ℕ} (π : Equiv.Perm (Fin n)) (a c : Wd n) :
    (slotPerm R π : Matrix (Wd n) (Wd n) R) a c = if a = slotAct π c then 1 else 0 := rfl

theorem kronSlot_map {n : ℕ} (s : Fin 4 → Equiv.Perm (Fin n)) :
    (kronPi (fun q => (slotPerm ℤ (s q) : Matrix (Wd n) (Wd n) ℤ))).map (Int.castRingHom ℂ) =
      kronPi (fun q => (slotPerm ℂ (s q) : Matrix (Wd n) (Wd n) ℂ)) := by
  ext α β
  simp only [Matrix.map_apply, kronPi_apply, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  show (Int.castRingHom ℂ) (slotPerm ℤ (s q) (α q) (β q)) = slotPerm ℂ (s q) (α q) (β q)
  simp only [slotPerm_apply']
  split_ifs <;> simp

theorem rhsOp_qf (z : Psi) :
    qf (copyPower (fun c => conj (zf z c)) 6) (rhsOp.map (Int.castRingHom ℂ)) (copyPower (zf z) 6) =
      ∑ i : RhsIdx, (rhsCoef i : ℂ) * rhsVal i z := by
  have hmap : rhsOp.map (Int.castRingHom ℂ) =
      ∑ i : RhsIdx, (rhsCoef i : ℂ) • kronPi (fun q => (slotPerm ℂ (rhsPerm i q) : Matrix (Wd 6) (Wd 6) ℂ)) := by
    unfold rhsOp
    have h1 : ∀ (s : Finset RhsIdx) (A : RhsIdx → Matrix (Cfg 6) (Cfg 6) ℤ),
        (∑ i ∈ s, A i).map (Int.castRingHom ℂ) = ∑ i ∈ s, (A i).map (Int.castRingHom ℂ) := by
      intro s A
      ext α β
      simp [Matrix.sum_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← kronSlot_map]
    ext α β
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast]
  rw [hmap, qf_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [qf_smul, qf_slot, invG_rhsPerm]

theorem redC0 (z : Psi) : redC 0 z = red12 z := rfl
theorem redC1 (z : Psi) : redC 1 z = red13 z := rfl
theorem redC2 (z : Psi) : redC 2 z = red14 z := rfl

/-- The cut quantities as complex numbers. -/
theorem purity_cast (z : Psi) : (purity z : ℂ) = A2 z 0 + A2 z 1 + A2 z 2 := by
  have h12 := trace_sq_real (red12_herm z)
  have h13 := trace_sq_real (red13_herm z)
  have h14 := trace_sq_real (red14_herm z)
  simp only [purity, A2, redC0, redC1, redC2]
  push_cast
  rw [← h12, ← h13, ← h14]

theorem cubic_cast (z : Psi) : (cubicMoment z : ℂ) = A3 z 0 + A3 z 1 + A3 z 2 := by
  have h12 := trace_cube_real (red12_herm z)
  have h13 := trace_cube_real (red13_herm z)
  have h14 := trace_cube_real (red14_herm z)
  simp only [cubicMoment, A3, redC0, redC1, redC2]
  push_cast
  rw [← h12, ← h13, ← h14]

theorem sumSq_cast (z : Psi) : (QVCert.sumSqCuts z : ℂ) = A2 z 0 ^ 2 + A2 z 1 ^ 2 + A2 z 2 ^ 2 := by
  have h12 := trace_sq_real (red12_herm z)
  have h13 := trace_sq_real (red13_herm z)
  have h14 := trace_sq_real (red14_herm z)
  simp only [QVCert.sumSqCuts, QVCert.trCut12, QVCert.trCut13, QVCert.trCut14, A2, redC0, redC1, redC2]
  push_cast
  rw [← h12, ← h13, ← h14]

/-- **T3.** `𝔇(z) = ⟨z^{⊗6}, K_RHS z^{⊗6}⟩` (Hermitian form, `K_RHS = rhsOp`). -/
theorem defectD_eq_qf (z : Psi) :
    (QVCert.defectD z : ℂ) =
      qf (copyPower (fun c => conj (zf z c)) 6) (rhsOp.map (Int.castRingHom ℂ)) (copyPower (zf z) 6) := by
  rw [rhsOp_qf]
  unfold QVCert.defectD sexticF
  push_cast
  rw [purity_cast, cubic_cast, sumSq_cast]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero, rhsCoef, rhsVal]
  simp
  ring

end FormalResearch.FourQubitEntropy.QVFrame

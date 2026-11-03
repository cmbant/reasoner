module

public import FormalResearch.FourQubitEntropy.PaperEGoSlice

/-!
# `thm:fqe-global-overlap`, layer (b)/(d): orbit membership and the real height inequality

For a unit frame `φ` (closest point `Z_*`, height `h`), every `e · P Z_* Qᵀ` with `P, Q` real orthogonal
`4 × 4` (either determinant) and `|e| = 1` is the magic-coordinate matrix of an element of the HS orbit
union `𝓜` (`orbit_mem4`; the reflections use `diag(1,-1,-1,-1) Z_* = conj Z_*`).  Hence
`Re ⟨χ, φ⟩ ≤ h` for all of them, which in real form on the slice is `height_ineq`:

`c (3 A₀₀ + Σ_{k≥1} B_kk) + 3 s (B₀₀ - Σ_{k≥1} A_kk) ≤ h₀`, with `A = Pᵀ X Q`, `B = Pᵀ Y Q`,
`c² + 3 s² = 1`.

Every first-order, Procrustes and lower-frame constraint of the normal slice is an instance of it.
No hypotheses (kernel-checked, standard axioms only).
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-! ### Indexing `Fin 2 × Fin 2` by `Fin 4` -/

theorem pairIdx_bij : Function.Bijective pairIdx := by
  constructor
  · intro p q h
    rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [pairIdx] at h ⊢
  · intro j
    fin_cases j
    · exact ⟨(0, 0), by simp [pairIdx]⟩
    · exact ⟨(0, 1), by simp [pairIdx]⟩
    · exact ⟨(1, 0), by simp [pairIdx]⟩
    · exact ⟨(1, 1), by simp [pairIdx]⟩

def pairEquiv : Fin 2 × Fin 2 ≃ Fin 4 := Equiv.ofBijective pairIdx pairIdx_bij

@[simp] theorem pairEquiv_apply (p : Fin 2 × Fin 2) : pairEquiv p = pairIdx p := rfl

theorem sum_pairG {M : Type*} [AddCommMonoid M] (f : Fin 4 → M) :
    ∑ k : Fin 2 × Fin 2, f (pairIdx k) = ∑ j, f j :=
  Equiv.sum_comp pairEquiv f

/-- A real `4 × 4` matrix indexed by `Fin 4`, transported to `Fin 2 × Fin 2`. -/
def toR (M : Matrix (Fin 4) (Fin 4) ℝ) : RMat4 := M.submatrix pairEquiv pairEquiv

theorem toR_apply (M : Matrix (Fin 4) (Fin 4) ℝ) (p q : Fin 2 × Fin 2) :
    toR M p q = M (pairIdx p) (pairIdx q) := rfl

theorem toR_mul (M N : Matrix (Fin 4) (Fin 4) ℝ) : toR (M * N) = toR M * toR N := by
  unfold toR
  rw [Matrix.submatrix_mul_equiv M N pairEquiv pairEquiv pairEquiv]

theorem toR_transpose (M : Matrix (Fin 4) (Fin 4) ℝ) : toR Mᵀ = (toR M)ᵀ := by
  unfold toR; rw [Matrix.transpose_submatrix]

theorem toR_one : toR (1 : Matrix (Fin 4) (Fin 4) ℝ) = 1 := by
  unfold toR; exact Matrix.submatrix_one_equiv pairEquiv

theorem toR_det (M : Matrix (Fin 4) (Fin 4) ℝ) : (toR M).det = M.det :=
  Matrix.det_submatrix_equiv_self pairEquiv M

/-! ### Overlaps in magic coordinates -/

/-- `⟨a, b⟩ = tr (X_aᴴ X_b)` in magic coordinates. -/
theorem ip_coord (a b : Psi) :
    ip a b = ∑ p, ∑ q, (starRingEnd ℂ) (magicCoord (zmat a) p q) * magicCoord (zmat b) p q := by
  rw [ip_eq_trace]
  conv_lhs => rw [zmat_eq_coord (zmat a), zmat_eq_coord (zmat b)]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, transpose_conjTranspose]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  set Xa := magicCoord (zmat a)
  set Xb := magicCoord (zmat b)
  have key : magicB.map star * (Xaᴴ * magicBᴴ) * (magicB * Xb * magicBᵀ) =
      magicB.map star * (Xaᴴ * Xb) * magicBᵀ := by
    calc _ = magicB.map star * Xaᴴ * (magicBᴴ * magicB) * Xb * magicBᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hBB' : magicBᵀ * magicB.map star = 1 := hBB
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def,
    Fintype.sum_prod_type]
  ring

theorem InOrbit_of_LU {a b : Psi} (h : InOrbit a) (hab : LUEquiv a b) : InOrbit b := by
  rcases h with h | h
  · exact Or.inl (h.trans hab)
  · exact Or.inr (h.trans hab)

/-! ### Orbit membership of `e · P Z_* Qᵀ` -/

/-- The sign matrix `diag(1,-1,-1,-1)` (`Fin 4`). -/
def Dm : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![1, -1, -1, -1]

theorem Dm_mul_self : Dm * Dm = 1 := by
  unfold Dm; rw [Matrix.diagonal_mul_diagonal]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

theorem Dm_transpose : Dmᵀ = Dm := by unfold Dm; exact Matrix.diagonal_transpose _

theorem Dm_det : Dm.det = -1 := by
  unfold Dm; rw [Matrix.det_diagonal]; simp [Fin.prod_univ_four]

/-- For orthogonal `P`, `det P = ±1`. -/
theorem det_orth {P : Matrix (Fin 4) (Fin 4) ℝ} (hP : Pᵀ * P = 1) : P.det = 1 ∨ P.det = -1 := by
  have h := congrArg Matrix.det hP
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have : (P.det - 1) * (P.det + 1) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linarith
  · right; linarith

theorem orth_mul_Dm {P : Matrix (Fin 4) (Fin 4) ℝ} (hP : Pᵀ * P = 1) : (P * Dm)ᵀ * (P * Dm) = 1 := by
  rw [Matrix.transpose_mul, Dm_transpose]
  calc Dm * Pᵀ * (P * Dm) = Dm * (Pᵀ * P) * Dm := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hP, Matrix.mul_one, Dm_mul_self]

theorem det_mul_Dm {P : Matrix (Fin 4) (Fin 4) ℝ} (hd : P.det = -1) : (P * Dm).det = 1 := by
  rw [Matrix.det_mul, hd, Dm_det]; norm_num

def sgn4 (k : Fin 4) : ℝ := if k = 0 then 1 else -1

theorem sgn4_sq (k : Fin 4) : sgn4 k * sgn4 k = 1 := by
  by_cases h : k = 0 <;> simp [sgn4, h]

theorem etaC_seven (j : Fin 4) : etaC 7 j = (sgn4 j : ℂ) * etaC 0 j := by
  have e0 : epsOf 0 = ![0, 1, 1, 1] := rfl
  have e7 : epsOf 7 = ![0, -1, -1, -1] := rfl
  have i0 : idxI 0 = 0 := rfl
  have i7 : idxI 7 = 0 := rfl
  unfold etaC
  rw [i0, i7, e0, e7]
  fin_cases j <;> simp [sgn4] <;> ring

theorem orbit_core (a : Fin 32) (P Q : RMat4) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (hdP : P.det = 1) (hdQ : Q.det = 1) (e : ℂ) (he : Complex.normSq e = 1) :
    ∃ χ : Psi, InOrbit χ ∧
      magicCoord (zmat χ) = rc P * (e • Matrix.diagonal (etaV a)) * (rc Q)ᵀ := by
  obtain ⟨ψ'', hLU, hcoord⟩ := exists_LU_rotate hP hdP hQ hdQ he (Gv (etaV a))
  refine ⟨ψ'', InOrbit_of_LU (orbit_etaV a) hLU, ?_⟩
  rw [hcoord, coord_of_eq (zmat_Gv (etaV a))]

/-- The entries of `rc P (e • diag d) (rc Q)ᵀ`. -/
theorem coord_entry (P Q : RMat4) (e : ℂ) (d : Fin 2 × Fin 2 → ℂ) (p q : Fin 2 × Fin 2) :
    (rc P * (e • Matrix.diagonal d) * (rc Q)ᵀ) p q =
      e * ∑ r, (P p r : ℂ) * d r * (Q q r : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.diagonal_apply, rc_apply,
    Matrix.transpose_apply, smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_eq_single r]
  · simp only [ite_true]; ring
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ r) h

theorem etaV_zero_eq (k : Fin 2 × Fin 2) : etaV 0 k = etaC 0 (pairIdx k) := rfl

theorem orbit_mem4 (P Q : Matrix (Fin 4) (Fin 4) ℝ) (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    (e : ℂ) (he : Complex.normSq e = 1) :
    ∃ χ : Psi, InOrbit χ ∧ ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
      e * ∑ k : Fin 4, (P (pairIdx p) k : ℂ) * etaC 0 k * (Q (pairIdx q) k : ℂ) := by
  have hDm : ∀ (A : Matrix (Fin 4) (Fin 4) ℝ) i k, (A * Dm) i k = A i k * sgn4 k := by
    intro A i k
    unfold Dm
    rw [Matrix.mul_diagonal]
    fin_cases k <;> simp [sgn4]
  have orth : ∀ A : Matrix (Fin 4) (Fin 4) ℝ, Aᵀ * A = 1 → (toR A)ᵀ * toR A = 1 := by
    intro A hA; rw [← toR_transpose, ← toR_mul, hA, toR_one]
  -- the common conclusion from `orbit_core`
  have fin : ∀ (a : Fin 32) (P' Q' : Matrix (Fin 4) (Fin 4) ℝ), P'ᵀ * P' = 1 → Q'ᵀ * Q' = 1 →
      P'.det = 1 → Q'.det = 1 →
      ∃ χ : Psi, InOrbit χ ∧ ∀ p q : Fin 2 × Fin 2, magicCoord (zmat χ) p q =
        e * ∑ k : Fin 4, (P' (pairIdx p) k : ℂ) * etaC a k * (Q' (pairIdx q) k : ℂ) := by
    intro a P' Q' hP' hQ' hdP hdQ
    obtain ⟨χ, hχ, hc⟩ := orbit_core a (toR P') (toR Q') (orth _ hP') (orth _ hQ')
      (by rw [toR_det]; exact hdP) (by rw [toR_det]; exact hdQ) e he
    refine ⟨χ, hχ, fun p q => ?_⟩
    rw [hc, coord_entry]
    congr 1
  rcases det_orth hP with hdP | hdP <;> rcases det_orth hQ with hdQ | hdQ
  · exact fin 0 P Q hP hQ hdP hdQ
  · obtain ⟨χ, hχ, hc⟩ := fin 7 P (Q * Dm) hP (orth_mul_Dm hQ) hdP (det_mul_Dm hdQ)
    refine ⟨χ, hχ, fun p q => ?_⟩
    rw [hc p q]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDm, etaC_seven]
    have h2 : ((sgn4 k : ℝ) : ℂ) * ((sgn4 k : ℝ) : ℂ) = 1 := by exact_mod_cast sgn4_sq k
    push_cast
    linear_combination (↑(P (pairIdx p) k) * etaC 0 k * ↑(Q (pairIdx q) k)) * h2
  · obtain ⟨χ, hχ, hc⟩ := fin 7 (P * Dm) Q (orth_mul_Dm hP) hQ (det_mul_Dm hdP) hdQ
    refine ⟨χ, hχ, fun p q => ?_⟩
    rw [hc p q]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDm, etaC_seven]
    have h2 : ((sgn4 k : ℝ) : ℂ) * ((sgn4 k : ℝ) : ℂ) = 1 := by exact_mod_cast sgn4_sq k
    push_cast
    linear_combination (↑(P (pairIdx p) k) * etaC 0 k * ↑(Q (pairIdx q) k)) * h2
  · obtain ⟨χ, hχ, hc⟩ := fin 0 (P * Dm) (Q * Dm) (orth_mul_Dm hP) (orth_mul_Dm hQ)
      (det_mul_Dm hdP) (det_mul_Dm hdQ)
    refine ⟨χ, hχ, fun p q => ?_⟩
    rw [hc p q]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hDm, hDm]
    have h2 : ((sgn4 k : ℝ) : ℂ) * ((sgn4 k : ℝ) : ℂ) = 1 := by exact_mod_cast sgn4_sq k
    push_cast
    linear_combination (↑(P (pairIdx p) k) * etaC 0 k * ↑(Q (pairIdx q) k)) * h2

/-! ### The height inequality -/

theorem IsFrame.re_le {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {χ : Psi} (hχ : InOrbit χ) :
    (ip χ φ).re ≤ h := by
  obtain ⟨-, h0, -, hle⟩ := hf
  have h1 := hle χ hχ
  have h2 : (ip χ φ).re ^ 2 ≤ h ^ 2 := by
    have := Complex.normSq_apply (ip χ φ)
    nlinarith [sq_nonneg (ip χ φ).im]
  exact abs_le_of_sq_le_sq' h2 h0 |>.2

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.orbit_mem4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orbit_mem4

end

end FormalResearch.FourQubitEntropy.GO

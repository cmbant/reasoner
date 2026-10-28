import FormalResearch.FourQubitEntropy.PaperECriticalMomentMap
import FormalResearch.FourQubitEntropy.Classify
import FormalResearch.FourQubitEntropy.Marginals

/-!
# `SO(4)` is realised by local unitaries in the magic basis

`Real4 G` says that the real `4×4` matrix `G` is the magic-basis matrix `Bᴴ (a ⊗ b) B` of a local
unitary `a ⊗ b` on qubits `1, 2`. The set of such `G` is closed under products and transposes, a
realised orthogonal `G` has `det G = 1` (`Real4.det_eq_one`, via `E4_conj`), and every `O ∈ SO(4)`
is realised (`Real4.of_SO`). The surjectivity is proved from the Lie-algebra identities
`L_x1, L_y1, L_z1` (`Bᴴ (σ ⊗ 1) B = i A_σ`): the elements `x₀ + i(x₁σ_x + x₂σ_y + x₃σ_z)` of
`SU(2)` act transitively on the unit sphere, and the stabiliser of the singlet coordinate is
handled by the existing `euler4`. No hypotheses, no `native_decide`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- `G` is realised in the magic basis by a local unitary `a ⊗ b`. -/
def Real4 (G : RMat4) : Prop :=
  ∃ a b : Op1, aᴴ * a = 1 ∧ bᴴ * b = 1 ∧ magicBᴴ * kron a b * magicB = G.map Complex.ofReal

theorem Real4.one : Real4 1 := by
  refine ⟨1, 1, by simp, by simp, ?_⟩
  have : (1 : RMat4).map Complex.ofReal = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [kron_one, this, Matrix.mul_one, magicB_unitary]

theorem Real4.mul {G H : RMat4} (hG : Real4 G) (hH : Real4 H) : Real4 (G * H) := by
  obtain ⟨a, b, ha, hb, hG⟩ := hG
  obtain ⟨c, d, hc, hd, hH⟩ := hH
  refine ⟨a * c, b * d, ?_, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc cᴴ * aᴴ * (a * c) = cᴴ * (aᴴ * a) * c := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [ha, Matrix.mul_one, hc]
  · rw [Matrix.conjTranspose_mul]
    calc dᴴ * bᴴ * (b * d) = dᴴ * (bᴴ * b) * d := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb, Matrix.mul_one, hd]
  · have e : (G * H).map Complex.ofReal = G.map Complex.ofReal * H.map Complex.ofReal := by
      ext i j; simp [Matrix.mul_apply]
    rw [e, ← hG, ← hH, ← kron_mul]
    calc magicBᴴ * (kron a b * kron c d) * magicB
        = magicBᴴ * kron a b * (magicB * magicBᴴ) * kron c d * magicB := by
          rw [magicB_unitary']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem Real4.transpose {G : RMat4} (hG : Real4 G) : Real4 Gᵀ := by
  obtain ⟨a, b, ha, hb, h⟩ := hG
  refine ⟨aᴴ, bᴴ, ?_, ?_, ?_⟩
  · simpa using mul_eq_one_comm.mp ha
  · simpa using mul_eq_one_comm.mp hb
  · have : kron aᴴ bᴴ = (kron a b)ᴴ := by
      unfold kron; rw [Matrix.conjTranspose_kronecker]
    rw [this]
    have h2 := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at h2
    rw [Matrix.mul_assoc, h2]
    ext i j; simp [Matrix.conjTranspose_apply]

theorem Real4.of_Rlz {G : RMat4} (h : Rlz G) : Real4 G := by
  obtain ⟨⟨c, hc, hcG⟩, -, -⟩ := h
  exact ⟨c, c, hc, hc, hcG⟩


theorem E4_eq_B : E4 = magicB.map (starRingEnd ℂ) * magicBᴴ := by
  have h := congrArg (fun M => magicB.map (starRingEnd ℂ) * M * magicBᴴ) magicB_E4
  beta_reduce at h
  have e : magicB.map (starRingEnd ℂ) * (magicBᵀ * E4 * magicB) * magicBᴴ =
      (magicB.map (starRingEnd ℂ) * magicBᵀ) * E4 * (magicB * magicBᴴ) := by
    simp only [Matrix.mul_assoc]
  rw [e, magicBbar_mul, magicB_unitary', Matrix.one_mul, Matrix.mul_one, Matrix.mul_one] at h
  exact h

theorem E4_ne : (E4 (0, 0) (1, 1)) ≠ 0 := by
  simp [E4, kron, eps2, Matrix.kroneckerMap_apply]

/-- A realised orthogonal matrix has `det = 1`. -/
theorem Real4.det_eq_one {G : RMat4} (hG : Real4 G) (hO : Gᵀ * G = 1) : G.det = 1 := by
  obtain ⟨a, b, ha, hb, h⟩ := hG
  set G' := G.map Complex.ofReal with hG'
  have hK : kron a b = magicB * G' * magicBᴴ := by
    rw [← h]
    calc kron a b = (magicB * magicBᴴ) * kron a b * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hGG : G'ᵀ * G' = 1 := by
    have : (Gᵀ * G).map Complex.ofReal = (1 : RMat4).map Complex.ofReal := by rw [hO]
    ext i j
    have := congrFun (congrFun this i) j
    simpa [hG', Matrix.mul_apply, Matrix.one_apply, apply_ite] using this
  have hT : (magicBᴴ)ᵀ = magicB.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hd : (kron a b)ᵀ * E4 * kron a b = E4 := by
    rw [hK, Matrix.transpose_mul, Matrix.transpose_mul, hT]
    calc _ = magicB.map (starRingEnd ℂ) * G'ᵀ * (magicBᵀ * E4 * magicB) * G' * magicBᴴ := by
          simp only [Matrix.mul_assoc]
      _ = E4 := by rw [magicB_E4, Matrix.mul_one, Matrix.mul_assoc _ G'ᵀ G', hGG,
            Matrix.mul_one, E4_eq_B]
  have hd2 := E4_conj a b
  rw [hd] at hd2
  have e1 := congrFun (congrFun hd2 (0, 0)) (1, 1)
  simp only [Matrix.smul_apply, smul_eq_mul] at e1
  have hdd : a.det * b.det = 1 := by
    have h0 := E4_ne
    have : (a.det * b.det - 1) * E4 (0, 0) (1, 1) = 0 := by linear_combination -e1
    rcases mul_eq_zero.mp this with h | h
    · linear_combination h
    · exact absurd h h0
  have hdet : G'.det = (a.det * b.det) ^ 2 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul] at this
    have hB : magicBᴴ.det * magicB.det = 1 := by
      rw [← Matrix.det_mul, magicB_unitary, Matrix.det_one]
    unfold kron at this
    rw [Matrix.det_kronecker] at this
    simp only [Fintype.card_fin] at this
    calc G'.det = magicBᴴ.det * (a.det ^ 2 * b.det ^ 2) * magicB.det := by rw [← this]
      _ = (a.det * b.det) ^ 2 := by linear_combination (a.det ^ 2 * b.det ^ 2) * hB
  rw [hdd] at hdet
  have : (G.det : ℂ) = 1 := by
    have e : G'.det = (G.det : ℂ) := (RingHom.map_det Complex.ofRealHom G).symm
    rw [e] at hdet
    simpa using hdet
  exact_mod_cast this


/-! ### Left multiplication by `SU(2)` elements `x₀ + i (x₁ σ_x + x₂ σ_y + x₃ σ_z)` -/

/-- The unit quaternion `x₀ + i (x₁ σ_x + x₂ σ_y + x₃ σ_z)` as a `2×2` matrix. -/
noncomputable def aq (x0 x1 x2 x3 : ℝ) : Op1 :=
  (x0 : ℂ) • (1 : Op1) + (Complex.I * x1) • pauliX + (Complex.I * x2) • pauliY +
    (Complex.I * x3) • pauliZ

/-- Its magic-basis matrix `x₀ 1 - x₁ A_{x1} - x₂ A_{y1} - x₃ A_{z1}`. -/
def Rq (x0 x1 x2 x3 : ℝ) : RMat4 := x0 • (1 : RMat4) - x1 • A_x1 - x2 • A_y1 - x3 • A_z1

theorem aq_unitary {x0 x1 x2 x3 : ℝ} (h : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) :
    (aq x0 x1 x2 x3)ᴴ * aq x0 x1 x2 x3 = 1 := by
  have hC : (x0 : ℂ) ^ 2 + (x1 : ℂ) ^ 2 + (x2 : ℂ) ^ 2 + (x3 : ℂ) ^ 2 = 1 := by exact_mod_cast h
  have hI4 : Complex.I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [aq, pauliX, pauliY, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  all_goals (try ring_nf)
  all_goals (try simp only [Complex.I_sq, hI4])
  all_goals (try ring_nf)
  all_goals (first | done | linear_combination hC)


theorem Rq_real {x0 x1 x2 x3 : ℝ} (h : x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 = 1) :
    Real4 (Rq x0 x1 x2 x3) := by
  refine ⟨aq x0 x1 x2 x3, 1, aq_unitary h, by simp, ?_⟩
  have e : kron (aq x0 x1 x2 x3) 1 = (x0 : ℂ) • (1 : Mat4) + (Complex.I * x1) • kron pauliX 1 +
      (Complex.I * x2) • kron pauliY 1 + (Complex.I * x3) • kron pauliZ 1 := by
    unfold kron aq
    simp only [Matrix.add_kronecker, Matrix.smul_kronecker, Matrix.one_kronecker_one]
  rw [e]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    magicB_unitary, L_x1, L_y1, L_z1]
  ext i j
  simp only [Rq, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.sub_apply,
    smul_eq_mul, Matrix.one_apply]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  by_cases hij : i = j
  · subst hij
    simp
    linear_combination ((x1 : ℂ) * (A_x1 i i : ℂ) + (x2 : ℂ) * (A_y1 i i : ℂ) + (x3 : ℂ) * (A_z1 i i : ℂ)) * hI
  simp [hij]
  linear_combination ((x1 : ℂ) * (A_x1 i j : ℂ) + (x2 : ℂ) * (A_y1 i j : ℂ) + (x3 : ℂ) * (A_z1 i j : ℂ)) * hI


/-- A realised matrix is orthogonal. -/
theorem Real4.orth {G : RMat4} (hG : Real4 G) : Gᵀ * G = 1 := by
  obtain ⟨a, b, ha, hb, h⟩ := hG
  have hK := kron_unitary ha hb
  have h2 : (G.map Complex.ofReal)ᴴ * G.map Complex.ofReal = 1 := by
    rw [← h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = magicBᴴ * (kron a b)ᴴ * (magicB * magicBᴴ) * kron a b * magicB := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [magicB_unitary', Matrix.mul_one]
          calc magicBᴴ * (kron a b)ᴴ * kron a b * magicB
              = magicBᴴ * ((kron a b)ᴴ * kron a b) * magicB := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hK, Matrix.mul_one, magicB_unitary]
  ext i j
  have := congrFun (congrFun h2 i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, apply_ite] using
    congrArg Complex.re this

theorem Real4.orth' {G : RMat4} (hG : Real4 G) : G * Gᵀ = 1 := by
  have := (Real4.transpose hG).orth
  simpa using this

theorem Real4.det {G : RMat4} (hG : Real4 G) : G.det = 1 := hG.det_eq_one hG.orth

/-- **Transitivity**: every unit vector `w` is the singlet column of a realised matrix. -/
theorem exists_real4_column (w : Fin 2 × Fin 2 → ℝ) (hw : ∑ j, w j ^ 2 = 1) :
    ∃ R : RMat4, Real4 R ∧ ∀ j, R j sing = w j := by
  have hw' : w (0, 0) ^ 2 + w (0, 1) ^ 2 + w (1, 0) ^ 2 + w (1, 1) ^ 2 = 1 := by
    simpa [Fintype.sum_prod_type, Fin.sum_univ_two, add_assoc] using hw
  refine ⟨Rq (w (1, 0)) (-w (1, 1)) (-w (0, 0)) (w (0, 1)), Rq_real (by nlinarith), ?_⟩
  intro j
  obtain ⟨j1, j2⟩ := j
  fin_cases j1 <;> fin_cases j2 <;> simp [Rq, A_x1, A_y1, A_z1, Eu, sing]


theorem det_Fd : Fd.det = -1 := by
  have : Fd = Matrix.diagonal (fun i => if i = ((1 : Fin 2), (1 : Fin 2)) then (-1 : ℝ) else 1) := by
    ext ⟨i1, i2⟩ ⟨j1, j2⟩
    fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [Fd, Matrix.diagonal_apply]
  rw [this, Matrix.det_diagonal]
  simp [Fintype.prod_prod_type, Fin.prod_univ_two]

/-- **`SO(4)` is realised by `SU(2) × SU(2)`**: every `O ∈ SO(4)` is the magic-basis matrix
`Bᴴ (a ⊗ b) B` of a local unitary `a ⊗ b` (proved). -/
theorem Real4.of_SO {O : RMat4} (hO : Oᵀ * O = 1) (hdet : O.det = 1) : Real4 O := by
  have hO' : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  set w : Fin 2 × Fin 2 → ℝ := fun j => O j sing with hw
  have hw1 : ∑ j, w j ^ 2 = 1 := by
    have := congrFun (congrFun hO sing) sing
    simpa [Matrix.mul_apply, pow_two, hw] using this
  obtain ⟨R, hR, hRw⟩ := exists_real4_column w hw1
  have hRo := hR.orth
  have hRo' := hR.orth'
  set Q := Rᵀ * O with hQ
  have hQ1 : Q * Qᵀ = 1 := by
    rw [hQ, Matrix.transpose_mul, Matrix.transpose_transpose]
    calc Rᵀ * O * (Oᵀ * R) = Rᵀ * (O * Oᵀ) * R := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hO', Matrix.mul_one, hRo]
  have hQ2 : Qᵀ * Q = 1 := mul_eq_one_comm.mp hQ1
  have hcol : ∀ i, Q i sing = if i = sing then 1 else 0 := by
    intro i
    have e : Q i sing = (Rᵀ * R) i sing := by
      simp only [hQ, Matrix.mul_apply, Matrix.transpose_apply]
      exact Finset.sum_congr rfl (fun k _ => by rw [hRw k])
    rw [e, hRo, Matrix.one_apply]
  have hrow : ∀ j, Q sing j = if j = sing then 1 else 0 := by
    intro j
    have e : Q sing j = (Qᵀ * Q) j sing := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol]
      simp [Finset.sum_ite_eq']
    rw [e, hQ2, Matrix.one_apply]
  have h11 : Q sing sing = 1 := by simpa using hcol sing
  have hs1 : Q * Prm = Prm := by
    ext i j
    simp only [Prm, Matrix.mul_diagonal, Matrix.diagonal_apply]
    by_cases hj : j = sing
    · subst hj
      by_cases hi : i = sing
      · subst hi; simp [h11]
      · simp [hi, hcol i, Ne.symm hi]
    · simp [hj]
      intro h1; subst h1; exact fun h => hj h
  have hs2 : Prm * Q = Prm := by
    ext i j
    simp only [Prm, Matrix.diagonal_mul, Matrix.diagonal_apply]
    by_cases hi : i = sing
    · subst hi
      by_cases hj : j = sing
      · subst hj; simp [h11]
      · simp [hj, hrow j, Ne.symm hj]
    · simp [hi]
  obtain ⟨G, hG, hGQ⟩ := euler4 Q hQ1 hQ2 hs1 hs2
  have hG' := Real4.of_Rlz hG
  have hdQ : Q.det = 1 := by
    rw [hQ, Matrix.det_mul, Matrix.det_transpose, hR.det, hdet, one_mul]
  rcases hGQ with h | h
  · have hQG : Q = Gᵀ := by
      calc Q = (Gᵀ * G) * Q := by rw [hG'.orth, Matrix.one_mul]
        _ = Gᵀ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
    have hOR : O = R * Q := by
      rw [hQ, ← Matrix.mul_assoc, hRo', Matrix.one_mul]
    rw [hOR, hQG]
    exact hR.mul hG'.transpose
  · exfalso
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, hG'.det, hdQ, det_Fd] at this
    norm_num at this

end FormalResearch.FourQubitEntropy.PaperECritical

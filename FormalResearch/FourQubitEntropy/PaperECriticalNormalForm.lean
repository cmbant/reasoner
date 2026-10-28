import FormalResearch.FourQubitEntropy.PaperECriticalBloch
import FormalResearch.FourQubitEntropy.PaperECriticalRealGram
import FormalResearch.FourQubitEntropy.PaperECriticalRealize

/-!
# Critical normal form, (1) ⇔ (2) ⇔ (3) of `thm:fqe-critical-normal-form`

For `ψ : Psi` with `X = magicCoord (zmat ψ)` (so `zmat ψ = B X Bᵀ` in the magic basis):

1. `blochSq ψ = 0` (all four one-qubit marginals are `I/2` up to normalisation);
2. `X Xᴴ` and `Xᴴ X` are real matrices;
3. `X = O₁ diag(v) O₂ᵀ` with `O₁, O₂ ∈ SO(4)` (real orthogonal, determinant `1`) and `v ∈ ℂ⁴`.

All three are proved equivalent with no hypotheses and no `native_decide`:
`(1) ⇔ (2)` is `blochSq_eq_zero_iff` (`lem:fqe-moment-map`), `(2) ⇒ (3)` is `real_gram_square_SO`
(`lem:fqe-real-gram`, square case) and `(3) ⇒ (2)` is `real_gram_of_normal_form`.

The equivalence with (4), local-unitary equivalence to `G(v)`, needs the realisation of `SO(4)` by
`SU(2) × SU(2)` and is not part of this file.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- `thm:fqe-critical-normal-form`, (2) ⇒ (3) (proved). -/
theorem normal_form_of_real_gram (ψ : Psi) (h : ∀ j k, (Hl ψ j k).im = 0 ∧ (Hr ψ j k).im = 0) :
    ∃ (O₁ O₂ : RMat4) (v : Fin 2 × Fin 2 → ℂ), O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧ O₁.det = 1 ∧
      O₂.det = 1 ∧ magicCoord (zmat ψ) = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ :=
  real_gram_square_SO (0, 0) (magicCoord (zmat ψ)) (fun i j => (h i j).1) (fun i j => (h i j).2)

/-- `thm:fqe-critical-normal-form`, (3) ⇒ (2) (proved). -/
theorem real_gram_of_normal_form' (ψ : Psi) (O₁ O₂ : RMat4) (v : Fin 2 × Fin 2 → ℂ)
    (h1 : O₁ᵀ * O₁ = 1) (h2 : O₂ᵀ * O₂ = 1)
    (hX : magicCoord (zmat ψ) = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) :
    (∀ j k, (Hl ψ j k).im = 0) ∧ (∀ j k, (Hr ψ j k).im = 0) := by
  have := real_gram_of_normal_form O₁ O₂ v h1 h2
  unfold Hl Hr
  rw [hX]; exact this

/-- **`thm:fqe-critical-normal-form`, (1) ⇔ (2) ⇔ (3)** (proved, no hypotheses): the four one-qubit
marginals of `ψ` are maximally mixed iff its magic-basis coordinate matrix is
`O₁ diag(v) O₂ᵀ` with `O₁, O₂ ∈ SO(4)`. -/
theorem critical_normal_form (ψ : Psi) :
    blochSq ψ = 0 ↔
      ∃ (O₁ O₂ : RMat4) (v : Fin 2 × Fin 2 → ℂ), O₁ᵀ * O₁ = 1 ∧ O₂ᵀ * O₂ = 1 ∧ O₁.det = 1 ∧
        O₂.det = 1 ∧ magicCoord (zmat ψ) = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ := by
  rw [blochSq_eq_zero_iff]
  constructor
  · rintro ⟨hl, hr⟩
    exact normal_form_of_real_gram ψ fun j k => ⟨hl j k, hr j k⟩
  · rintro ⟨O₁, O₂, v, h1, h2, -, -, hX⟩
    exact real_gram_of_normal_form' ψ O₁ O₂ v h1 h2 hX


/-- The vector `G(v)` with magic-basis coordinate matrix `diag(v)`, i.e. `Σ_k v_k |m_k⟩|m_k⟩`-type
normal form (`zmat = B diag(v) Bᵀ`). -/
noncomputable def Gv (v : Fin 2 × Fin 2 → ℂ) : Psi := ofZmat (magicB * Matrix.diagonal v * magicBᵀ)

theorem coord_Gv (v : Fin 2 × Fin 2 → ℂ) : magicCoord (zmat (Gv v)) = Matrix.diagonal v := by
  unfold Gv; rw [zmat_ofZmat]; exact coord_of_eq rfl

/-- A real orthogonal normal form is a local unitary image of `G(v)`: if
`X = O₁ diag(v) O₂ᵀ` with `O₁, O₂ ∈ SO(4)` then `ψ = (a ⊗ b ⊗ c ⊗ d) G(v)`. -/
theorem LU_of_normal_form (ψ : Psi) (O₁ O₂ : RMat4) (v : Fin 2 × Fin 2 → ℂ)
    (h1 : O₁ᵀ * O₁ = 1) (h2 : O₂ᵀ * O₂ = 1) (d1 : O₁.det = 1) (d2 : O₂.det = 1)
    (hX : magicCoord (zmat ψ) = rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) : LUEquiv (Gv v) ψ := by
  obtain ⟨a, b, ha, hb, hab⟩ := Real4.of_SO h1 d1
  obtain ⟨c, d, hc, hd, hcd⟩ := Real4.of_SO h2 d2
  refine ⟨a, b, c, d, ha, hb, hc, hd, ?_⟩
  have hK1 : kron a b = magicB * rc O₁ * magicBᴴ := by
    have : rc O₁ = O₁.map Complex.ofReal := rfl
    rw [this, ← hab]
    calc kron a b = (magicB * magicBᴴ) * kron a b * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hK2 : kron c d = magicB * rc O₂ * magicBᴴ := by
    have : rc O₂ = O₂.map Complex.ofReal := rfl
    rw [this, ← hcd]
    calc kron c d = (magicB * magicBᴴ) * kron c d * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hT : (magicBᴴ)ᵀ = magicB.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  have hz : zmat (localApply a b c d (Gv v)) = zmat ψ := by
    rw [zmat_localApply, hK1, hK2, Matrix.transpose_mul, Matrix.transpose_mul, hT]
    have hz0 : zmat (Gv v) = magicB * Matrix.diagonal v * magicBᵀ := by unfold Gv; rw [zmat_ofZmat]
    rw [hz0, zmat_eq_coord (zmat ψ), hX]
    calc _ = magicB * rc O₁ * (magicBᴴ * magicB) * Matrix.diagonal v *
          (magicBᵀ * magicB.map (starRingEnd ℂ)) * (rc O₂)ᵀ * magicBᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary, hBB]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  calc localApply a b c d (Gv v) = ofZmat (zmat (localApply a b c d (Gv v))) := rfl
    _ = ofZmat (zmat ψ) := by rw [hz]
    _ = ψ := rfl

/-- **`thm:fqe-critical-normal-form`, (1) ⇒ (4)** (proved): a four-qubit vector with all one-qubit
marginals maximally mixed is local-unitarily equivalent to some `G(v)`. -/
theorem critical_LU_Gv (ψ : Psi) (h : blochSq ψ = 0) : ∃ v : Fin 2 × Fin 2 → ℂ, LUEquiv (Gv v) ψ := by
  obtain ⟨O₁, O₂, v, h1, h2, d1, d2, hX⟩ := (critical_normal_form ψ).mp h
  exact ⟨v, LU_of_normal_form ψ O₁ O₂ v h1 h2 d1 d2 hX⟩


/-! ### The converse (4) ⇒ (1): local unitaries are real up to a phase in the magic basis -/

/-- A unitary `U` with `Uᵀ U = d • 1` is a unimodular phase times a real orthogonal matrix. -/
theorem exists_phase_real (U : Mat4) (hU : Uᴴ * U = 1) (d : ℂ) (hd : Uᵀ * U = d • 1) :
    ∃ (s : ℂ) (O : RMat4), s * (starRingEnd ℂ) s = 1 ∧ Oᵀ * O = 1 ∧ U = s • rc O := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.mp hU
  have hUb : Uᵀ * U.map (starRingEnd ℂ) = 1 := unitary_transpose_mul hU
  have hdd : d * (starRingEnd ℂ) d = 1 := by
    have h1 : (Uᵀ * U) * (Uᵀ * U)ᴴ = 1 := by
      rw [Matrix.conjTranspose_mul, transpose_conjTranspose]
      calc Uᵀ * U * (Uᴴ * U.map star) = Uᵀ * (U * Uᴴ) * U.map star := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU', Matrix.mul_one]; exact hUb
    rw [hd] at h1
    have h2 := congrFun (congrFun h1 (0, 0)) (0, 0)
    rw [mul_comm]
    simpa [Matrix.smul_apply, Matrix.conjTranspose_smul, Matrix.one_apply] using h2
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq d (n := 2) (by norm_num)
  have hsd : s * s = d := by rw [← hs]; ring
  have hss : s * (starRingEnd ℂ) s = 1 := by
    have h1 : (s * (starRingEnd ℂ) s) ^ 2 = 1 := by
      calc (s * (starRingEnd ℂ) s) ^ 2 = (s * s) * (starRingEnd ℂ) (s * s) := by
            rw [map_mul]; ring
        _ = 1 := by rw [hsd, hdd]
    have h2 : s * (starRingEnd ℂ) s = (Complex.normSq s : ℂ) := by
      rw [Complex.mul_conj]
    rw [h2] at h1 ⊢
    have h3 : Complex.normSq s ^ 2 = 1 := by exact_mod_cast h1
    have h4 : 0 ≤ Complex.normSq s := Complex.normSq_nonneg s
    have : Complex.normSq s = 1 := by nlinarith
    rw [this]; simp
  set O' : Mat4 := (starRingEnd ℂ) s • U with hO'
  have hsbar : (starRingEnd ℂ) s * s = 1 := by rw [mul_comm]; exact hss
  have h1 : O'ᴴ * O' = 1 := by
    rw [hO', Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hU]
    simp [hss]
  have h2 : O'ᵀ * O' = 1 := by
    rw [hO', Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd, smul_smul]
    have : (starRingEnd ℂ) s * (starRingEnd ℂ) s * d = 1 := by
      rw [← hsd]
      calc (starRingEnd ℂ) s * (starRingEnd ℂ) s * (s * s)
          = ((starRingEnd ℂ) s * s) * ((starRingEnd ℂ) s * s) := by ring
        _ = 1 := by rw [hsbar]; ring
    rw [this, one_smul]
  have hT : O'ᵀ = O'ᴴ := by
    have h3 : O' * O'ᴴ = 1 := mul_eq_one_comm.mp h1
    calc O'ᵀ = O'ᵀ * (O' * O'ᴴ) := by rw [h3, Matrix.mul_one]
      _ = (O'ᵀ * O') * O'ᴴ := by rw [Matrix.mul_assoc]
      _ = O'ᴴ := by rw [h2, Matrix.one_mul]
  have hreal : ∀ i j, O' i j = ((O' i j).re : ℂ) := by
    intro i j
    have := congrFun (congrFun hT j) i
    simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply, Complex.star_def] at this
    exact (Complex.conj_eq_iff_re.mp this.symm).symm
  set O : RMat4 := Matrix.of fun i j => (O' i j).re with hO
  have hrc : rc O = O' := by ext i j; rw [rc_apply]; exact (hreal i j).symm
  refine ⟨s, O, hss, ?_, ?_⟩
  · have : rc (Oᵀ * O) = rc 1 := by
      rw [map_mul, ← rc_transpose, hrc]
      rw [hT, h1]; exact (map_one rc).symm
    ext i j
    have := congrFun (congrFun this i) j
    simpa [rc_apply, Matrix.one_apply, apply_ite] using congrArg Complex.re this
  · rw [hrc, hO', smul_smul, hss, one_smul]


theorem magic_local_transpose (a b : Op1) :
    (magicBᴴ * kron a b * magicB)ᵀ * (magicBᴴ * kron a b * magicB) = (a.det * b.det) • (1 : Mat4) := by
  have hT : (magicBᴴ)ᵀ = magicB.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hT]
  calc _ = magicBᵀ * ((kron a b)ᵀ * (magicB.map (starRingEnd ℂ) * magicBᴴ) * kron a b) * magicB := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [← E4_eq_B, E4_conj, Matrix.mul_smul, Matrix.smul_mul, magicB_E4]

/-- **`thm:fqe-critical-normal-form`, (4) ⇒ (1)** (proved): every local-unitary image of `G(v)` has
all one-qubit marginals maximally mixed. -/
theorem blochSq_zero_of_LU_Gv (v : Fin 2 × Fin 2 → ℂ) (ψ : Psi) (h : LUEquiv (Gv v) ψ) :
    blochSq ψ = 0 := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  have hU1 : (magicBᴴ * kron a b * magicB)ᴴ * (magicBᴴ * kron a b * magicB) = 1 := by
    have hK := kron_unitary ha hb
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = magicBᴴ * (kron a b)ᴴ * (magicB * magicBᴴ) * kron a b * magicB := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [magicB_unitary', Matrix.mul_one]
          calc magicBᴴ * (kron a b)ᴴ * kron a b * magicB
              = magicBᴴ * ((kron a b)ᴴ * kron a b) * magicB := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hK, Matrix.mul_one, magicB_unitary]
  have hU2 : (magicBᴴ * kron c d * magicB)ᴴ * (magicBᴴ * kron c d * magicB) = 1 := by
    have hK := kron_unitary hc hd
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = magicBᴴ * (kron c d)ᴴ * (magicB * magicBᴴ) * kron c d * magicB := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [magicB_unitary', Matrix.mul_one]
          calc magicBᴴ * (kron c d)ᴴ * kron c d * magicB
              = magicBᴴ * ((kron c d)ᴴ * kron c d) * magicB := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hK, Matrix.mul_one, magicB_unitary]
  obtain ⟨s1, O1, hs1, hO1, hU1e⟩ := exists_phase_real _ hU1 _ (magic_local_transpose a b)
  obtain ⟨s2, O2, hs2, hO2, hU2e⟩ := exists_phase_real _ hU2 _ (magic_local_transpose c d)
  have hK1 : kron a b = magicB * (magicBᴴ * kron a b * magicB) * magicBᴴ := by
    calc kron a b = (magicB * magicBᴴ) * kron a b * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hK2 : kron c d = magicB * (magicBᴴ * kron c d * magicB) * magicBᴴ := by
    calc kron c d = (magicB * magicBᴴ) * kron c d * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  set U1 := magicBᴴ * kron a b * magicB with hU1def
  set U2 := magicBᴴ * kron c d * magicB with hU2def
  have hT : (magicBᴴ)ᵀ = magicB.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  have hX : magicCoord (zmat (localApply a b c d (Gv v))) = U1 * Matrix.diagonal v * U2ᵀ := by
    rw [zmat_localApply]
    have hz0 : zmat (Gv v) = magicB * Matrix.diagonal v * magicBᵀ := by unfold Gv; rw [zmat_ofZmat]
    rw [hz0]
    unfold magicCoord
    conv_lhs => rw [hK1, hK2, Matrix.transpose_mul, Matrix.transpose_mul, hT]
    calc _ = (magicBᴴ * magicB) * U1 * (magicBᴴ * magicB) * Matrix.diagonal v *
          (magicBᵀ * magicB.map (starRingEnd ℂ)) * U2ᵀ * (magicBᵀ * magicB.map (starRingEnd ℂ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary, hBB]; simp only [Matrix.mul_one, Matrix.one_mul]
  have hX' : magicCoord (zmat (localApply a b c d (Gv v))) =
      rc O1 * Matrix.diagonal (fun k => s1 * s2 * v k) * (rc O2)ᵀ := by
    rw [hX, hU1e, hU2e, Matrix.transpose_smul]
    have : Matrix.diagonal (fun k => s1 * s2 * v k) = (s1 * s2) • Matrix.diagonal v := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [this]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [smul_smul, mul_comm]
  have := real_gram_of_normal_form' _ O1 O2 _ hO1 hO2 hX'
  exact (blochSq_eq_zero_iff _).mpr this


/-- **`thm:fqe-critical-normal-form`, (1) ⇔ (4)** (proved, no hypotheses): `blochSq ψ = 0` iff `ψ` is
local-unitarily equivalent to some `G(v)`. -/
theorem critical_iff_LU_Gv (ψ : Psi) : blochSq ψ = 0 ↔ ∃ v : Fin 2 × Fin 2 → ℂ, LUEquiv (Gv v) ψ :=
  ⟨critical_LU_Gv ψ, fun ⟨v, h⟩ => blochSq_zero_of_LU_Gv v ψ h⟩

end FormalResearch.FourQubitEntropy.PaperECritical

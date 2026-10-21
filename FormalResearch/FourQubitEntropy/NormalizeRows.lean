import FormalResearch.FourQubitEntropy.TopVector

/-!
# A local unitary on qubits `1,2` sending the top vector to the singlet
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

/-- The rank-one matrix `u u†`. -/
def projVec (u : Fin 2 × Fin 2 → ℂ) : Mat4 := Matrix.of fun i j => u i * (starRingEnd ℂ) (u j)

/-- The singlet `m₃ = (|01⟩ - |10⟩)/√2`. -/
noncomputable def sv : Fin 2 × Fin 2 → ℂ := fun p => magicB p sing

/-- The target cut matrix `1/6 + (1/3) |m₃⟩⟨m₃|`. -/
noncomputable def Gs : Mat4 := (1 / 6 : ℂ) • 1 + (1 / 3 : ℂ) • projVec sv

theorem sv_apply (a b : Fin 2) : sv (a, b) = rt * eps2 a b := by
  fin_cases a <;> fin_cases b <;> simp [sv, magicB, sing, eps2]

theorem eps2_mul_transpose : eps2 * eps2ᵀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eps2, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

theorem eps2_transpose_conj : (eps2ᵀ)ᴴ = eps2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eps2, Matrix.conjTranspose_apply]

theorem kron_mulVec (a b : Op1) (u : Fin 2 × Fin 2 → ℂ) (p q : Fin 2) :
    (kron a b *ᵥ u) (p, q) = ∑ p', ∑ q', a p p' * b q q' * u (p', q') := by
  simp [Matrix.mulVec, dotProduct, kron, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]

/-- A top vector with maximally mixed first-qubit marginal is the image of the singlet under a
unitary on the first qubit. -/
theorem normalize_rows (φ : Psi)
    (hq : (red12 φ - (1 / 6 : ℂ) • 1) * (red12 φ - (1 / 2 : ℂ) • 1) = 0)
    (htr : (Matrix.trace (red12 φ)).re = 1)
    (hmarg : ∀ a a', ∑ b, red12 φ (a, b) (a', b) = if a = a' then 1 / 2 else 0) :
    ∃ a : Op1, aᴴ * a = 1 ∧ red12 (rowLU (kron aᴴ 1) φ) = Gs := by
  obtain ⟨u, hu, hRu⟩ := exists_top_vec (red12_herm φ) hq htr
  -- the matrix of `u` as a `2×2` matrix
  set U : Op1 := Matrix.of fun a b => u (a, b) with hU
  have hUU : U * Uᴴ = (1 / 2 : ℂ) • 1 := by
    ext a a'
    have := hmarg a a'
    simp only [hRu, Fin.sum_univ_two] at this
    simp only [hU, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.one_apply, Matrix.star_eq_conjTranspose]
    by_cases h : a = a'
    · subst h; simp at this ⊢; linear_combination 3 * this
    · simp [h] at this ⊢; linear_combination 3 * this
  have hrt := rt_mul_rt
  have hrtc : (starRingEnd ℂ) rt = rt := rt_conj
  set c : ℂ := 2 * rt with hc
  have hcc : c * c = 2 := by rw [hc]; linear_combination 4 * hrt
  have hcs : (starRingEnd ℂ) c = c := by rw [hc, map_mul, hrtc, map_ofNat]
  -- `U†U = 1/2`
  have hUtU : Uᴴ * U = (1 / 2 : ℂ) • 1 := by
    have hW : (c • U) * (c • U)ᴴ = 1 := by
      rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hUU, smul_smul]
      show (c * (star c) * (1 / 2)) • (1 : Op1) = 1
      have : star c = c := hcs
      rw [this, hcc]; norm_num
    have hW' := mul_eq_one_comm.mp hW
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul] at hW'
    have hs : star c * c = 2 := by
      have : star c = c := hcs
      rw [this, hcc]
    rw [hs] at hW'
    have := congrArg (fun M => (1 / 2 : ℂ) • M) hW'
    simp only [smul_smul] at this
    rw [show (1 / 2 : ℂ) * 2 = 1 by norm_num, one_smul] at this
    rw [this]
  set a1 : Op1 := c • (U * eps2ᵀ) with ha1
  have ha1ha : a1ᴴ * a1 = 1 := by
    rw [ha1, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, eps2_transpose_conj,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : star c * c = 2 := by
      have : star c = c := hcs
      rw [this, hcc]
    rw [this]
    calc (2 : ℂ) • (eps2 * Uᴴ * (U * eps2ᵀ)) = (2 : ℂ) • (eps2 * (Uᴴ * U) * eps2ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hUtU, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, smul_smul, eps2_mul_transpose]
          norm_num
  have haU : a1ᴴ * U = rt • eps2 := by
    rw [ha1, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, eps2_transpose_conj,
      Matrix.smul_mul]
    have hcs' : star c = c := hcs
    rw [hcs']
    calc c • (eps2 * Uᴴ * U) = c • (eps2 * (Uᴴ * U)) := by rw [Matrix.mul_assoc]
      _ = rt • eps2 := by
          rw [hUtU, Matrix.mul_smul, Matrix.mul_one, smul_smul, hc]
          congr 1; ring
  refine ⟨a1, ha1ha, ?_⟩
  -- the vector identity `K u = m₃`
  have hKu : kron a1ᴴ 1 *ᵥ u = sv := by
    funext ⟨p, q⟩
    rw [kron_mulVec, sv_apply]
    have := congrFun (congrFun haU p) q
    simp only [Matrix.mul_apply, hU, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two] at this ⊢
    fin_cases q <;> simp [Matrix.one_apply] <;> simpa using this
  have hKun : (kron a1ᴴ 1)ᴴ * kron a1ᴴ 1 = 1 := by
    have : (a1ᴴ)ᴴ * a1ᴴ = 1 := by
      rw [Matrix.conjTranspose_conjTranspose]; exact mul_eq_one_comm.mp ha1ha
    have h1 : (1 : Op1)ᴴ * 1 = 1 := by simp
    exact kron_unitary this h1
  have hKK : kron a1ᴴ 1 * (kron a1ᴴ 1)ᴴ = 1 := mul_eq_one_comm.mpr hKun
  have hR : red12 φ = (1 / 6 : ℂ) • 1 + (1 / 3 : ℂ) • projVec u := by
    ext i j; simp [hRu, projVec, Matrix.one_apply]
  have hproj : ∀ (K : Mat4) (v : Fin 2 × Fin 2 → ℂ), K * projVec v * Kᴴ = projVec (K *ᵥ v) := by
    intro K v
    ext i j
    have e1 : (K * projVec v * Kᴴ) i j
        = ∑ l, ∑ k, K i k * (v k * (starRingEnd ℂ) (v l)) * (starRingEnd ℂ) (K j l) := by
      simp only [Matrix.mul_apply, projVec, Matrix.of_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
      rfl
    have e2 : projVec (K *ᵥ v) i j
        = ∑ k, ∑ l, K i k * (v k * (starRingEnd ℂ) (v l)) * (starRingEnd ℂ) (K j l) := by
      simp only [projVec, Matrix.of_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e1, e2, Finset.sum_comm]
  rw [red12_rowLU, hR]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hKK,
    hproj, hKu]
  rfl

end FormalResearch.FourQubitEntropy

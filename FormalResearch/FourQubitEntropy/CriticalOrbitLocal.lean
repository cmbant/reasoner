import FormalResearch.FourQubitEntropy.CriticalOrbitPhi
import FormalResearch.FourQubitEntropy.PaperECriticalRealGram

/-!
# Critical-orbit stability: local unitaries in the magic basis

A local unitary image `(a ⊗ b ⊗ c ⊗ d) G(w)` has magic coordinates `rc O₁ · diag(s w) · (rc O₂)ᵀ`
with `O₁, O₂` real orthogonal and `|s| = 1` (`coord_localApply`), so its overlap with `G(v)` is
`s ∑_{i,k} conj(v_i) w_k O₁_{ik} O₂_{ik}` (`ip_Gv_localApply`): the reduction of
`eq:fqe-signed-diagonal-overlap`.
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- `⟨G(v), χ⟩ = ∑_i conj(v_i) X_{ii}` where `X` is the magic coordinate matrix of `χ`. -/
theorem ip_Gv_coord (v : V) (χ : Psi) :
    ip (Gv v) χ = ∑ i, (starRingEnd ℂ) (v i) * magicCoord (zmat χ) i i := by
  rw [ip_eq_trace, zmat_Gv]
  conv_lhs => rw [zmat_eq_coord (zmat χ)]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, transpose_conjTranspose,
    Matrix.diagonal_conjTranspose]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  set X := magicCoord (zmat χ) with hX
  have key : magicB.map star * (Matrix.diagonal (star v) * magicBᴴ) *
      (magicB * X * magicBᵀ) = magicB.map star * (Matrix.diagonal (star v) * X) * magicBᵀ := by
    calc _ = magicB.map star * Matrix.diagonal (star v) * (magicBᴴ * magicB) * X * magicBᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hBB' : magicBᵀ * magicB.map star = 1 := hBB
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB', Matrix.one_mul]
  simp [Matrix.trace, Matrix.diagonal_mul, Complex.star_def]

theorem magic_local_real (a b : Op1) (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) :
    ∃ (s : ℂ) (O : RMat4), s * (starRingEnd ℂ) s = 1 ∧ Oᵀ * O = 1 ∧
      magicBᴴ * kron a b * magicB = s • rc O := by
  have hK := kron_unitary ha hb
  have hU1 : (magicBᴴ * kron a b * magicB)ᴴ * (magicBᴴ * kron a b * magicB) = 1 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc _ = magicBᴴ * (kron a b)ᴴ * (magicB * magicBᴴ) * kron a b * magicB := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [magicB_unitary', Matrix.mul_one]
          calc magicBᴴ * (kron a b)ᴴ * kron a b * magicB
              = magicBᴴ * ((kron a b)ᴴ * kron a b) * magicB := by simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hK, Matrix.mul_one, magicB_unitary]
  exact exists_phase_real _ hU1 _ (magic_local_transpose a b)

/-- Magic coordinates of a local unitary image of `G(w)`. -/
theorem coord_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (hd : dᴴ * d = 1) (w : V) :
    ∃ (s : ℂ) (O1 O2 : RMat4), Complex.normSq s = 1 ∧ O1ᵀ * O1 = 1 ∧ O2ᵀ * O2 = 1 ∧
      magicCoord (zmat (localApply a b c d (Gv w))) =
        rc O1 * Matrix.diagonal (fun k => s * w k) * (rc O2)ᵀ := by
  obtain ⟨s1, O1, hs1, hO1, hU1e⟩ := magic_local_real a b ha hb
  obtain ⟨s2, O2, hs2, hO2, hU2e⟩ := magic_local_real c d hc hd
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
  have hX : magicCoord (zmat (localApply a b c d (Gv w))) = U1 * Matrix.diagonal w * U2ᵀ := by
    rw [zmat_localApply]
    have hz0 : zmat (Gv w) = magicB * Matrix.diagonal w * magicBᵀ := by unfold Gv; rw [zmat_ofZmat]
    rw [hz0]
    unfold magicCoord
    conv_lhs => rw [hK1, hK2, Matrix.transpose_mul, Matrix.transpose_mul, hT]
    calc _ = (magicBᴴ * magicB) * U1 * (magicBᴴ * magicB) * Matrix.diagonal w *
          (magicBᵀ * magicB.map (starRingEnd ℂ)) * U2ᵀ * (magicBᵀ * magicB.map (starRingEnd ℂ)) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [magicB_unitary, hBB]; simp only [Matrix.mul_one, Matrix.one_mul]
  refine ⟨s1 * s2, O1, O2, ?_, hO1, hO2, ?_⟩
  · have : (s1 * s2) * (starRingEnd ℂ) (s1 * s2) = 1 := by
      rw [map_mul]; calc _ = (s1 * (starRingEnd ℂ) s1) * (s2 * (starRingEnd ℂ) s2) := by ring
        _ = 1 := by rw [hs1, hs2]; simp
    rw [Complex.mul_conj] at this
    exact_mod_cast this
  · rw [hX, hU1e, hU2e, Matrix.transpose_smul]
    have : Matrix.diagonal (fun k => s1 * s2 * w k) = (s1 * s2) • Matrix.diagonal w := by
      ext i j; by_cases hij : i = j <;> simp [Matrix.diagonal_apply, hij]
    rw [this]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [smul_smul, mul_comm]

/-- The overlap of `G(v)` with a local unitary image of `G(w)`:
`s ∑_{i,k} conj(v_i) w_k O₁_{ik} O₂_{ik}`. -/
theorem ip_Gv_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (hd : dᴴ * d = 1) (v w : V) :
    ∃ (s : ℂ) (O1 O2 : RMat4), Complex.normSq s = 1 ∧ O1ᵀ * O1 = 1 ∧ O2ᵀ * O2 = 1 ∧
      ip (Gv v) (localApply a b c d (Gv w)) =
        s * ∑ i, ∑ k, (starRingEnd ℂ) (v i) * w k * ((O1 i k * O2 i k : ℝ) : ℂ) := by
  obtain ⟨s, O1, O2, hs, hO1, hO2, hX⟩ := coord_localApply ha hb hc hd w
  refine ⟨s, O1, O2, hs, hO1, hO2, ?_⟩
  rw [ip_Gv_coord, hX, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply, rc_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  push_cast; ring

end FormalResearch.FourQubitEntropy.CO

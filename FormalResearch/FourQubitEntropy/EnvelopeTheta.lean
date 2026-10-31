import FormalResearch.FourQubitEntropy.EnvelopePermClass
import FormalResearch.FourQubitEntropy.EnvelopeEquality

/-!
# The Bloch correlation matrix `Θ` of a critical normal vector (`prop:fqe-critical-envelope`)

For `v : Fin 2 × Fin 2 → ℂ` let `φ = Σ_k v_k m_k` (`critPhi`, `m_k` the magic basis, `magicB`) and
`Θ_{αβ} = ⟨φ|σ_α ⊗ σ_β|φ⟩` (`critTheta`, `σ = (σ_x, σ_y, σ_z)`); `critBloch v` is the local Bloch
vector `⟨φ|1 ⊗ σ_β|φ⟩` of the second qubit. With `n = Σ|v_k|²` (`nV`) and `τ = |Σ v_k²|²` (`tauV`),
all identities below are polynomial identities in the real and imaginary parts of `v`:

* `critTheta_gram`: `Θᵀ Θ = τ I + b bᵀ` (so `Θ` has singular values `(1, κ, κ)` for unit `v`);
* `critBloch_dot`: `|b|² = n² - τ`; `critTheta_det`: `det Θ = -n τ`;
* `sexticF_Gv_perm`: `F(G(v)) = n³/2 + (7/4) τ n + (9/4) perm Θ` — the closed form of
  `eq:fqe-critical-envelope` (`F = 1/2 + 7τ/4 + 9 perm Θ / 4` for unit `v`).
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

open FormalResearch.FourQubitEntropy.PaperECritical

/-- The auxiliary two-qubit vector `φ = Σ_k v_k m_k` of a critical normal vector `v`. -/
noncomputable def critPhi (v : Fin 2 × Fin 2 → ℂ) : Fin 2 × Fin 2 → ℂ := magicB.mulVec v

/-- The Pauli matrices `(σ_x, σ_y, σ_z)`. -/
def pauli3 : Fin 3 → Op1 := ![pauliX, pauliY, pauliZ]

/-- Bloch correlation matrix `Θ_{αβ} = ⟨φ|σ_α ⊗ σ_β|φ⟩`. -/
noncomputable def critTheta (v : Fin 2 × Fin 2 → ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun α β => (star (critPhi v) ⬝ᵥ (kron (pauli3 α) (pauli3 β)).mulVec (critPhi v)).re

/-- Local Bloch vector of the second qubit of `φ`, `b_β = ⟨φ|1 ⊗ σ_β|φ⟩`. -/
noncomputable def critBloch (v : Fin 2 × Fin 2 → ℂ) : Fin 3 → ℝ :=
  fun β => (star (critPhi v) ⬝ᵥ (kron 1 (pauli3 β)).mulVec (critPhi v)).re

theorem rt_re_eq : rt.re = (Real.sqrt 2)⁻¹ := by unfold rt; exact Complex.ofReal_re _
theorem rt_im_eq : rt.im = 0 := by unfold rt; exact Complex.ofReal_im _
theorem rt_re_sq : rt.re ^ 2 = 1 / 2 := by
  rw [rt_re_eq, inv_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- `Re (v̄_j v_k)`. -/
def pq (v : Fin 2 × Fin 2 → ℂ) (j k : Fin 2 × Fin 2) : ℝ :=
  (v j).re * (v k).re + (v j).im * (v k).im

set_option maxHeartbeats 2000000 in
theorem critTheta_eq (v : Fin 2 × Fin 2 → ℂ) : critTheta v = !![
    pq v (0,0) (0,0) + pq v (0,1) (0,1) - pq v (1,0) (1,0) - pq v (1,1) (1,1),
    -2 * (pq v (0,0) (1,1) + pq v (0,1) (1,0)),
    -2 * pq v (0,0) (1,0) + 2 * pq v (0,1) (1,1);
    -2 * pq v (0,0) (1,1) + 2 * pq v (0,1) (1,0),
    -pq v (0,0) (0,0) + pq v (0,1) (0,1) - pq v (1,0) (1,0) + pq v (1,1) (1,1),
    2 * pq v (0,0) (0,1) + 2 * pq v (1,0) (1,1);
    2 * pq v (0,0) (1,0) + 2 * pq v (0,1) (1,1),
    2 * pq v (0,0) (0,1) - 2 * pq v (1,0) (1,1),
    pq v (0,0) (0,0) - pq v (0,1) (0,1) - pq v (1,0) (1,0) + pq v (1,1) (1,1)] := by
  ext α β
  fin_cases α <;> fin_cases β <;>
  · simp [critTheta, critPhi, pauli3, kron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, magicB, pauliX, pauliY, pauliZ, Matrix.kroneckerMap_apply, pq, rt_im_eq]
    ring_nf
    simp only [rt_re_sq]
    ring


/-- `Im (v̄_j v_k)`. -/
def qq (v : Fin 2 × Fin 2 → ℂ) (j k : Fin 2 × Fin 2) : ℝ :=
  (v j).re * (v k).im - (v j).im * (v k).re

set_option maxHeartbeats 2000000 in
theorem critBloch_eq (v : Fin 2 × Fin 2 → ℂ) : critBloch v = ![
    -2 * qq v (0,0) (0,1) - 2 * qq v (1,0) (1,1),
    2 * qq v (0,0) (1,0) - 2 * qq v (0,1) (1,1),
    -2 * qq v (0,0) (1,1) - 2 * qq v (0,1) (1,0)] := by
  funext β
  fin_cases β <;>
  · simp [critBloch, critPhi, pauli3, kron, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, magicB, pauliX, pauliY, pauliZ, Matrix.kroneckerMap_apply, qq, rt_im_eq]
    ring_nf
    simp only [rt_re_sq]
    ring

/-- `τ = |Σ_k v_k²|²`. -/
noncomputable def tauV (v : Fin 2 × Fin 2 → ℂ) : ℝ := Complex.normSq (∑ k, v k ^ 2)

/-- `n = Σ_k |v_k|²`. -/
noncomputable def nV (v : Fin 2 × Fin 2 → ℂ) : ℝ := ∑ k, Complex.normSq (v k)

theorem tauV_expand (v : Fin 2 × Fin 2 → ℂ) : tauV v =
    ((v (0,0)).re ^ 2 - (v (0,0)).im ^ 2 + ((v (0,1)).re ^ 2 - (v (0,1)).im ^ 2)
      + ((v (1,0)).re ^ 2 - (v (1,0)).im ^ 2) + ((v (1,1)).re ^ 2 - (v (1,1)).im ^ 2)) ^ 2
    + (2 * ((v (0,0)).re * (v (0,0)).im + (v (0,1)).re * (v (0,1)).im + (v (1,0)).re * (v (1,0)).im
      + (v (1,1)).re * (v (1,1)).im)) ^ 2 := by
  simp [tauV, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply, pow_two]
  ring

theorem nV_expand (v : Fin 2 × Fin 2 → ℂ) : nV v =
    (v (0,0)).re ^ 2 + (v (0,0)).im ^ 2 + ((v (0,1)).re ^ 2 + (v (0,1)).im ^ 2)
      + ((v (1,0)).re ^ 2 + (v (1,0)).im ^ 2) + ((v (1,1)).re ^ 2 + (v (1,1)).im ^ 2) := by
  simp [nV, Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply, pow_two]
  ring

theorem critTheta_gram (v : Fin 2 × Fin 2 → ℂ) :
    (critTheta v)ᵀ * critTheta v = tauV v • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      + Matrix.vecMulVec (critBloch v) (critBloch v) := by
  rw [critTheta_eq, critBloch_eq, tauV_expand]
  ext i j
  fin_cases i <;> fin_cases j <;>
  · simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec_apply, Matrix.one_apply, pq, qq]
    ring

theorem critBloch_dot (v : Fin 2 × Fin 2 → ℂ) : critBloch v ⬝ᵥ critBloch v = nV v ^ 2 - tauV v := by
  rw [critBloch_eq, nV_expand, tauV_expand]
  simp [dotProduct, Fin.sum_univ_three, qq]
  ring

theorem critTheta_det (v : Fin 2 × Fin 2 → ℂ) : (critTheta v).det = -(nV v * tauV v) := by
  rw [critTheta_eq, nV_expand, tauV_expand]
  simp [Matrix.det_fin_three, pq]
  ring


theorem perm3_critTheta (v : Fin 2 × Fin 2 → ℂ) : perm3 (critTheta v) =
    (pq v (0,0) (0,0) + pq v (0,1) (0,1) - pq v (1,0) (1,0) - pq v (1,1) (1,1)) *
      (-pq v (0,0) (0,0) + pq v (0,1) (0,1) - pq v (1,0) (1,0) + pq v (1,1) (1,1)) *
      (pq v (0,0) (0,0) - pq v (0,1) (0,1) - pq v (1,0) (1,0) + pq v (1,1) (1,1)) +
    (pq v (0,0) (0,0) + pq v (0,1) (0,1) - pq v (1,0) (1,0) - pq v (1,1) (1,1)) *
      (2 * pq v (0,0) (0,1) + 2 * pq v (1,0) (1,1)) *
      (2 * pq v (0,0) (0,1) - 2 * pq v (1,0) (1,1)) +
    (-2 * (pq v (0,0) (1,1) + pq v (0,1) (1,0))) *
      (-2 * pq v (0,0) (1,1) + 2 * pq v (0,1) (1,0)) *
      (pq v (0,0) (0,0) - pq v (0,1) (0,1) - pq v (1,0) (1,0) + pq v (1,1) (1,1)) +
    (-2 * (pq v (0,0) (1,1) + pq v (0,1) (1,0))) *
      (2 * pq v (0,0) (0,1) + 2 * pq v (1,0) (1,1)) *
      (2 * pq v (0,0) (1,0) + 2 * pq v (0,1) (1,1)) +
    (-2 * pq v (0,0) (1,0) + 2 * pq v (0,1) (1,1)) *
      (-2 * pq v (0,0) (1,1) + 2 * pq v (0,1) (1,0)) *
      (2 * pq v (0,0) (0,1) - 2 * pq v (1,0) (1,1)) +
    (-2 * pq v (0,0) (1,0) + 2 * pq v (0,1) (1,1)) *
      (-pq v (0,0) (0,0) + pq v (0,1) (0,1) - pq v (1,0) (1,0) + pq v (1,1) (1,1)) *
      (2 * pq v (0,0) (1,0) + 2 * pq v (0,1) (1,1)) := by
  rw [critTheta_eq]
  simp [perm3]

set_option maxHeartbeats 8000000 in
theorem sexticF_Gv_perm (v : Fin 2 × Fin 2 → ℂ) :
    sexticF (Gv v) = nV v ^ 3 / 2 + 7 / 4 * tauV v * nV v + 9 / 4 * perm3 (critTheta v) := by
  rw [sexticF_Gv, perm3_critTheta, nV_expand, tauV_expand]
  simp only [Zsum, Zterm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat, pow_two, pq]
  ring

end FormalResearch.FourQubitEntropy

import FormalResearch.FourQubitEntropy.LocalUnitary

/-!
# Local-unitary images of `M₄` and `conj M₄` attain the bound
-/

open scoped ComplexConjugate Matrix ComplexOrder Kronecker

namespace FormalResearch.FourQubitEntropy

theorem trace_red12_rowLU (K : Mat4) (hK : Kᴴ * K = 1) (ψ : Psi) :
    Matrix.trace (red12 (rowLU K ψ)) = Matrix.trace (red12 ψ) := by
  rw [red12_rowLU, Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, hK, Matrix.mul_one]

theorem normSqPsi_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1)
    (hc : cᴴ * c = 1) (hd : dᴴ * d = 1) (ψ : Psi) :
    normSqPsi (localApply a b c d ψ) = normSqPsi ψ := by
  have h := trace_red12_rowLU (kron a b) (kron_unitary ha hb) ψ
  unfold localApply
  have h2 := congrArg Complex.re
    ((congrArg Matrix.trace (red12_colLU (kron c d) (kron_unitary hc hd) (rowLU (kron a b) ψ))))
  rw [trace_red12, trace_red12] at h2
  rw [trace_red12, trace_red12] at h
  have := congrArg Complex.re h
  simp at h2 this
  linarith

/-- The cut `12|34` matrix transforms by conjugation. -/
theorem red12_localApply {a b c d : Op1} (hc : cᴴ * c = 1) (hd : dᴴ * d = 1) (ψ : Psi) :
    red12 (localApply a b c d ψ) = kron a b * red12 ψ * (kron a b)ᴴ := by
  unfold localApply
  rw [red12_colLU _ (kron_unitary hc hd), red12_rowLU]

theorem quadratic_conj {R : Mat4} {K : Mat4} (hK : Kᴴ * K = 1)
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) :
    (K * R * Kᴴ - (1 / 6 : ℂ) • 1) * (K * R * Kᴴ - (1 / 2 : ℂ) • 1) = 0 := by
  have hK' : K * Kᴴ = 1 := mul_eq_one_comm.mp hK
  have e : ∀ c : ℂ, K * R * Kᴴ - c • (1 : Mat4) = K * (R - c • 1) * Kᴴ := by
    intro c
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hK']
  rw [e, e]
  calc K * (R - (1 / 6 : ℂ) • 1) * Kᴴ * (K * (R - (1 / 2 : ℂ) • 1) * Kᴴ)
      = K * ((R - (1 / 6 : ℂ) • 1) * (Kᴴ * K) * (R - (1 / 2 : ℂ) • 1)) * Kᴴ := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hK, Matrix.mul_one, h]; simp

/-- A unit vector all of whose three cut matrices satisfy the quadratic attains the bound. -/
theorem meanEntropy_of_quadratics (ψ : Psi) (hψ : normSqPsi ψ = 1)
    (q12 : (red12 ψ - (1 / 6 : ℂ) • 1) * (red12 ψ - (1 / 2 : ℂ) • 1) = 0)
    (q13 : (red13 ψ - (1 / 6 : ℂ) • 1) * (red13 ψ - (1 / 2 : ℂ) • 1) = 0)
    (q14 : (red14 ψ - (1 / 6 : ℂ) • 1) * (red14 ψ - (1 / 2 : ℂ) • 1) = 0) :
    meanEntropy ψ = 1 + Real.log 3 / (2 * Real.log 2) := by
  have l2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have t12 : (Matrix.trace (red12 ψ)).re = 1 := by rw [trace_red12, hψ]; simp
  have t13 : (Matrix.trace (red13 ψ)).re = 1 := by rw [trace_red13, hψ]; simp
  have t14 : (Matrix.trace (red14 ψ)).re = 1 := by rw [trace_red14, hψ]; simp
  unfold meanEntropy vnEntropy
  rw [entropy_sum_of_quadratic _ q12 t12, entropy_sum_of_quadratic _ q13 t13,
    entropy_sum_of_quadratic _ q14 t14]
  field_simp
  ring

theorem red12_conj (ψ : Psi) : red12 ψ.conj = (red12 ψ).map (starRingEnd ℂ) := by
  ext i j
  simp [red12, Psi.conj, map_sum, mul_comm]

theorem red13_conj (ψ : Psi) : red13 ψ.conj = (red13 ψ).map (starRingEnd ℂ) := by
  ext i j
  simp [red13, Psi.conj, map_sum, mul_comm]

theorem red14_conj (ψ : Psi) : red14 ψ.conj = (red14 ψ).map (starRingEnd ℂ) := by
  ext i j
  simp [red14, Psi.conj, map_sum, mul_comm]

theorem quadratic_map_star {R : Mat4}
    (h : (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0) :
    (R.map (starRingEnd ℂ) - (1 / 6 : ℂ) • 1) * (R.map (starRingEnd ℂ) - (1 / 2 : ℂ) • 1) = 0 := by
  have e : ∀ c : ℂ, (starRingEnd ℂ) c = c →
      R.map (starRingEnd ℂ) - c • (1 : Mat4) = (R - c • 1).map (starRingEnd ℂ) := by
    intro c hc
    ext i j
    by_cases hij : i = j
    · subst hij; simp [hc]
    · simp [hij]
  have h6 : (starRingEnd ℂ) (1 / 6 : ℂ) = 1 / 6 := by
    rw [show (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) by push_cast; ring]; exact Complex.conj_ofReal _
  have h2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]; exact Complex.conj_ofReal _
  rw [e _ h6, e _ h2]
  have hm := map_mul (starRingEnd ℂ).mapMatrix (R - (1 / 6 : ℂ) • 1) (R - (1 / 2 : ℂ) • 1)
  simp only [RingHom.mapMatrix_apply] at hm
  rw [← hm, h]
  simp

/-- The three cut conditions of a vector, bundled. -/
structure CutQuadratics (φ : Psi) : Prop where
  q12 : (red12 φ - (1 / 6 : ℂ) • 1) * (red12 φ - (1 / 2 : ℂ) • 1) = 0
  q13 : (red13 φ - (1 / 6 : ℂ) • 1) * (red13 φ - (1 / 2 : ℂ) • 1) = 0
  q14 : (red14 φ - (1 / 6 : ℂ) • 1) * (red14 φ - (1 / 2 : ℂ) • 1) = 0

theorem CutQuadratics.localApply {φ : Psi} (h : CutQuadratics φ) {a b c d : Op1}
    (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1) (hd : dᴴ * d = 1) :
    CutQuadratics (localApply a b c d φ) where
  q12 := by
    rw [red12_localApply hc hd]
    exact quadratic_conj (kron_unitary ha hb) h.q12
  q13 := by
    have e : swap23 (_root_.FormalResearch.FourQubitEntropy.localApply a b c d φ)
        = _root_.FormalResearch.FourQubitEntropy.localApply a c b d (swap23 φ) :=
      swap23_localApply a c b d φ
    rw [red13_eq_swap, e, red12_localApply hb hd, ← red13_eq_swap]
    exact quadratic_conj (kron_unitary ha hc) h.q13
  q14 := by
    have e : swap24 (_root_.FormalResearch.FourQubitEntropy.localApply a b c d φ)
        = _root_.FormalResearch.FourQubitEntropy.localApply a d c b (swap24 φ) :=
      swap24_localApply a d c b φ
    rw [red14_eq_swap, e, red12_localApply hc hb, ← red14_eq_swap]
    exact quadratic_conj (kron_unitary ha hd) h.q14

theorem CutQuadratics.conj {φ : Psi} (h : CutQuadratics φ) : CutQuadratics φ.conj where
  q12 := by rw [red12_conj]; exact quadratic_map_star h.q12
  q13 := by rw [red13_conj]; exact quadratic_map_star h.q13
  q14 := by rw [red14_conj]; exact quadratic_map_star h.q14

theorem M4_cutQuadratics : CutQuadratics M4 := ⟨red12_M4, red13_M4, red14_M4⟩

theorem normSqPsi_conj (ψ : Psi) : normSqPsi ψ.conj = normSqPsi ψ := by
  simp [normSqPsi, Psi.conj]

/-- A local-unitary image of a vector with the cut quadratics attains the entropy bound. -/
theorem meanEntropy_of_LU {φ ψ : Psi} (hφ : normSqPsi φ = 1) (hq : CutQuadratics φ)
    (h : LUEquiv φ ψ) : meanEntropy ψ = 1 + Real.log 3 / (2 * Real.log 2) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  have hq' := hq.localApply ha hb hc hd
  exact meanEntropy_of_quadratics _ (by rw [normSqPsi_localApply ha hb hc hd, hφ])
    hq'.q12 hq'.q13 hq'.q14

end FormalResearch.FourQubitEntropy

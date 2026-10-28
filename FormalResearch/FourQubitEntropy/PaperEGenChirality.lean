import FormalResearch.FourQubitEntropy.Rigidity

/-!
# `M₄` and `conj M₄` are not related by any local operators (even filters)

Paper E, introduction (`four_qubit_entropy.tex`) and the end of Appendix `sec:fqe-sextic`
(`sextic_identity.tex`, the paragraph after `prop:fqe-moment-zeros`): the two maximising LU orbits
are distinct, "even under invertible local filters", by the ratio of flattening determinants.

Let `D₁ⱼ(ψ)` be the determinant of the `1j|\\hat{1j}` flattening (`flatDet12`, `flatDet13`, `flatDet14`,
qubit indices in increasing order). For *any* four one-qubit operators `a, b, c, d`
(`det (A ⊗ B) = det A² det B²` for `2 × 2` matrices) all three determinants of `a ⊗ b ⊗ c ⊗ d ψ` are
those of `ψ` times the same factor `(det a det b det c det d)²` (`flatDet_localApply_*`), so
`D₁₃(φ) D₁₂(ψ) = D₁₃(ψ) D₁₂(φ)` whenever `φ = (a⊗b⊗c⊗d) ψ` (`flatDet_cross`).

For `M₄`: `D₁₂ = (ω - ω²)/36` and `D₁₃ = (1 - ω²)/36`, the ratio `D₁₃/D₁₂ = (1 - i√3)/2` is not real
(`M4_flatDet12`, `M4_flatDet13`), whereas conjugation conjugates it. Hence

* `no_local_operator_M4_conj`: there are no `a b c d : Op1` (invertible or not) with
  `(a⊗b⊗c⊗d) M₄ = conj M₄`;
* `not_LUEquiv_M4_conj`: `M₄` and `conj M₄` are not local-unitarily equivalent (the first proof of
  LU-inequivalence is Lyons–Walck–Blanda, Prop. 7; this elementary argument also covers filters).

Proved, no hypothesis; `#print axioms` lists `propext`, `Classical.choice`, `Quot.sound` only
(nothing here uses the sextic identity).
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

namespace Chirality

/-- The bijection `Fin 4 ≃ Fin 2 × Fin 2` in the order `00, 01, 10, 11`. -/
noncomputable def e4 : Fin 4 ≃ Fin 2 × Fin 2 :=
  Equiv.ofBijective
    (![((0 : Fin 2), (0 : Fin 2)), (0, 1), (1, 0), (1, 1)] : Fin 4 → Fin 2 × Fin 2) (by decide)

theorem det_mat4_aux (Z : Mat4) : Z.det = (Matrix.of fun i j : Fin 4 => Z (e4 i) (e4 j)).det := by
  rw [← Matrix.det_reindex_self e4.symm Z]
  rfl

/-- Laplace expansion of the determinant of a `4 × 4` matrix indexed by pairs of bits. -/
theorem det_mat4 (Z : Mat4) : Z.det =
    Z (0,0) (0,0) * (Z (0,1) (0,1) * (Z (1,0) (1,0) * Z (1,1) (1,1) - Z (1,0) (1,1) * Z (1,1) (1,0))
       - Z (0,1) (1,0) * (Z (1,0) (0,1) * Z (1,1) (1,1) - Z (1,0) (1,1) * Z (1,1) (0,1))
       + Z (0,1) (1,1) * (Z (1,0) (0,1) * Z (1,1) (1,0) - Z (1,0) (1,0) * Z (1,1) (0,1)))
    - Z (0,0) (0,1) * (Z (0,1) (0,0) * (Z (1,0) (1,0) * Z (1,1) (1,1) - Z (1,0) (1,1) * Z (1,1) (1,0))
       - Z (0,1) (1,0) * (Z (1,0) (0,0) * Z (1,1) (1,1) - Z (1,0) (1,1) * Z (1,1) (0,0))
       + Z (0,1) (1,1) * (Z (1,0) (0,0) * Z (1,1) (1,0) - Z (1,0) (1,0) * Z (1,1) (0,0)))
    + Z (0,0) (1,0) * (Z (0,1) (0,0) * (Z (1,0) (0,1) * Z (1,1) (1,1) - Z (1,0) (1,1) * Z (1,1) (0,1))
       - Z (0,1) (0,1) * (Z (1,0) (0,0) * Z (1,1) (1,1) - Z (1,0) (1,1) * Z (1,1) (0,0))
       + Z (0,1) (1,1) * (Z (1,0) (0,0) * Z (1,1) (0,1) - Z (1,0) (0,1) * Z (1,1) (0,0)))
    - Z (0,0) (1,1) * (Z (0,1) (0,0) * (Z (1,0) (0,1) * Z (1,1) (1,0) - Z (1,0) (1,0) * Z (1,1) (0,1))
       - Z (0,1) (0,1) * (Z (1,0) (0,0) * Z (1,1) (1,0) - Z (1,0) (1,0) * Z (1,1) (0,0))
       + Z (0,1) (1,0) * (Z (1,0) (0,0) * Z (1,1) (0,1) - Z (1,0) (0,1) * Z (1,1) (0,0))) := by
  rw [det_mat4_aux, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Fin.succAbove, Matrix.det_succ_row_zero, e4]
  ring

end Chirality

open Chirality

/-- Determinant of the `12|34` flattening. -/
noncomputable def flatDet12 (ψ : Psi) : ℂ := (zmat ψ).det
/-- Determinant of the `13|24` flattening. -/
noncomputable def flatDet13 (ψ : Psi) : ℂ := (zmat (swap23 ψ)).det
/-- Determinant of the `14|23` flattening. -/
noncomputable def flatDet14 (ψ : Psi) : ℂ := (zmat (swap24 ψ)).det

theorem det_zmat_localApply (a b c d : Op1) (ψ : Psi) :
    (zmat (localApply a b c d ψ)).det = (a.det * b.det * c.det * d.det) ^ 2 * (zmat ψ).det := by
  rw [zmat_localApply, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  unfold kron
  rw [Matrix.det_kronecker, Matrix.det_kronecker]
  simp only [Fintype.card_fin]
  ring

theorem flatDet_localApply_12 (a b c d : Op1) (ψ : Psi) :
    flatDet12 (localApply a b c d ψ) = (a.det * b.det * c.det * d.det) ^ 2 * flatDet12 ψ :=
  det_zmat_localApply a b c d ψ

theorem flatDet_localApply_13 (a b c d : Op1) (ψ : Psi) :
    flatDet13 (localApply a b c d ψ) = (a.det * b.det * c.det * d.det) ^ 2 * flatDet13 ψ := by
  unfold flatDet13
  have h' : swap23 (localApply a b c d ψ) = localApply a c b d (swap23 ψ) := by
    have := swap23_localApply a c b d ψ
    exact this
  rw [h', det_zmat_localApply]
  ring

theorem flatDet_localApply_14 (a b c d : Op1) (ψ : Psi) :
    flatDet14 (localApply a b c d ψ) = (a.det * b.det * c.det * d.det) ^ 2 * flatDet14 ψ := by
  unfold flatDet14
  have h' : swap24 (localApply a b c d ψ) = localApply a d c b (swap24 ψ) := by
    have := swap24_localApply a d c b ψ
    exact this
  rw [h', det_zmat_localApply]
  ring

/-- **The cross relation.** Local operators multiply all three flattening determinants by the same
factor, so `D₁₃(φ) D₁₂(ψ) = D₁₃(ψ) D₁₂(φ)` and likewise for `D₁₄`. -/
theorem flatDet_cross (a b c d : Op1) (ψ : Psi) :
    flatDet13 (localApply a b c d ψ) * flatDet12 ψ = flatDet13 ψ * flatDet12 (localApply a b c d ψ) ∧
    flatDet14 (localApply a b c d ψ) * flatDet12 ψ = flatDet14 ψ * flatDet12 (localApply a b c d ψ) := by
  rw [flatDet_localApply_13, flatDet_localApply_12, flatDet_localApply_14]
  constructor <;> ring

theorem flatDet12_conj (ψ : Psi) : flatDet12 ψ.conj = conj (flatDet12 ψ) := by
  unfold flatDet12
  have : zmat ψ.conj = (starRingEnd ℂ).mapMatrix (zmat ψ) := by
    ext i j; simp [zmat, Psi.conj]
  rw [this, ← RingHom.map_det]

theorem flatDet13_conj (ψ : Psi) : flatDet13 ψ.conj = conj (flatDet13 ψ) := by
  unfold flatDet13
  have : zmat (swap23 ψ.conj) = (starRingEnd ℂ).mapMatrix (zmat (swap23 ψ)) := by
    ext i j; simp [zmat, Psi.conj, swap23]
  rw [this, ← RingHom.map_det]

theorem flatDet14_conj (ψ : Psi) : flatDet14 ψ.conj = conj (flatDet14 ψ) := by
  unfold flatDet14
  have : zmat (swap24 ψ.conj) = (starRingEnd ℂ).mapMatrix (zmat (swap24 ψ)) := by
    ext i j; simp [zmat, Psi.conj, swap24]
  rw [this, ← RingHom.map_det]

/-- `D₁₂(M₄) = (1/√6)⁴ (ω - ω²)`. -/
theorem M4_flatDet12 : flatDet12 M4 = (((1 / Real.sqrt 6 : ℝ) : ℂ)) ^ 4 * (omega - omega ^ 2) := by
  unfold flatDet12
  rw [det_mat4]
  simp [zmat, M4]
  rw [conj_omega]
  ring_nf
  rw [omega_pow4]
  ring

/-- `D₁₃(M₄) = (1/√6)⁴ (1 - ω²)`. -/
theorem M4_flatDet13 : flatDet13 M4 = (((1 / Real.sqrt 6 : ℝ) : ℂ)) ^ 4 * (1 - omega ^ 2) := by
  unfold flatDet13
  rw [det_mat4]
  simp [zmat, M4, swap23]
  rw [conj_omega]
  ring_nf
  have h6 : omega ^ 6 = 1 := by
    rw [show omega ^ 6 = (omega ^ 3) ^ 2 by ring, omega_pow3]; norm_num
  rw [h6]
  ring

/-- The two determinants of `M₄` have a non-real ratio: `conj D₁₃ · D₁₂ ≠ D₁₃ · conj D₁₂`. -/
theorem M4_flatDet_ratio_ne :
    conj (flatDet13 M4) * flatDet12 M4 ≠ flatDet13 M4 * conj (flatDet12 M4) := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hc : 0 < (1 / Real.sqrt 6 : ℝ) ^ 4 := by positivity
  rw [M4_flatDet12, M4_flatDet13]
  simp only [map_mul, map_sub, map_pow, map_one, conj_omega, Complex.conj_ofReal]
  have h4 : (omega ^ 2) ^ 2 = omega := by rw [← pow_mul]; exact omega_pow4
  rw [h4]
  intro h
  have him := congrArg Complex.im h
  have e1 : ((1 / Real.sqrt 6 : ℝ) : ℂ) ^ 4 = (((1 / Real.sqrt 6 : ℝ) ^ 4 : ℝ) : ℂ) := by push_cast; rfl
  rw [e1] at him
  generalize (1 / Real.sqrt 6 : ℝ) ^ 4 = c at hc him
  simp [omega, pow_two, Complex.mul_im, Complex.mul_re] at him
  nlinarith [mul_pos hc hc, mul_pos (mul_pos hc hc) hs]

/-- **No local operators relate `M₄` and `conj M₄`.** There are no one-qubit operators `a, b, c, d`
(unitary, invertible or not) with `(a⊗b⊗c⊗d) M₄ = conj M₄`. -/
theorem no_local_operator_M4_conj (a b c d : Op1) : localApply a b c d M4 ≠ Psi.conj M4 := by
  intro h
  have hx := (flatDet_cross a b c d M4).1
  rw [h, flatDet13_conj, flatDet12_conj] at hx
  exact M4_flatDet_ratio_ne hx

/-- `M₄` and `conj M₄` are not local-unitarily equivalent (even under invertible local filters, by
`no_local_operator_M4_conj`): the two maximising LU orbits of `thm:fqe-entropy-max` are distinct. -/
theorem not_LUEquiv_M4_conj : ¬ LUEquiv M4 (Psi.conj M4) := by
  rintro ⟨a, b, c, d, -, -, -, -, h⟩
  exact no_local_operator_M4_conj a b c d h

theorem not_LUEquiv_conj_M4 : ¬ LUEquiv (Psi.conj M4) M4 := fun h => not_LUEquiv_M4_conj h.symm

end FormalResearch.FourQubitEntropy

import FormalResearch.FourQubitEntropy.Rotations
import FormalResearch.FourQubitEntropy.Euler3

/-!
# Realising rotations of the magic basis by local unitaries

A real orthogonal matrix fixing the singlet coordinate is brought to `1` or to `diag(1,1,1,-1)` by
rotations that are realised by `c ⊗ c`, `c ∈ SU(2)`.
-/

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy

/-- A real matrix realised in the magic basis by `c ⊗ c` and fixing the singlet coordinate. -/
def Rlz (G : RMat4) : Prop :=
  (∃ c : Op1, cᴴ * c = 1 ∧ magicBᴴ * kron c c * magicB = G.map Complex.ofReal) ∧
    G * Prm = Prm ∧ Prm * G = Prm

theorem Rlz.one : Rlz 1 := by
  refine ⟨⟨1, by simp, ?_⟩, by simp, by simp⟩
  rw [kron_one]
  have : (1 : RMat4).map Complex.ofReal = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  rw [this, Matrix.mul_one, magicB_unitary]

theorem Rlz.mul {G H : RMat4} (hG : Rlz G) (hH : Rlz H) : Rlz (G * H) := by
  obtain ⟨⟨c, hc, hcG⟩, hG1, hG2⟩ := hG
  obtain ⟨⟨d, hd, hdH⟩, hH1, hH2⟩ := hH
  refine ⟨⟨c * d, ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul]
    calc dᴴ * cᴴ * (c * d) = dᴴ * (cᴴ * c) * d := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hc, Matrix.mul_one, hd]
  · have e : (G * H).map Complex.ofReal = G.map Complex.ofReal * H.map Complex.ofReal := by
      ext i j; simp [Matrix.mul_apply]
    rw [e, ← hcG, ← hdH, ← kron_mul]
    calc magicBᴴ * (kron c c * kron d d) * magicB
        = magicBᴴ * kron c c * (magicB * magicBᴴ) * kron d d * magicB := by
          rw [magicB_unitary']; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.mul_assoc, hH1, hG1]
  · rw [← Matrix.mul_assoc, hG2, hH2]

theorem rlz_rotX {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) : Rlz (rotX p q) := by
  obtain ⟨a, b, hab, rfl, rfl⟩ := half_angle p q h
  refine ⟨⟨cx a b, cx_unitary hab, magic_cx hab⟩, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Prm, rotX, Matrix.mul_diagonal, sing]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Prm, rotX, Matrix.diagonal_mul, sing]

theorem rlz_rotY {p q : ℝ} (h : p ^ 2 + q ^ 2 = 1) : Rlz (rotY p q) := by
  obtain ⟨a, b, hab, rfl, rfl⟩ := half_angle p q h
  refine ⟨⟨cy a b, cy_unitary hab, magic_cy hab⟩, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Prm, rotY, Matrix.mul_diagonal, sing]
  · ext i j
    fin_cases i <;> fin_cases j <;>
    simp [Prm, rotY, Matrix.diagonal_mul, sing]

/-! ### Lifting the `3×3` reduction -/

/-- The coordinates `m₁, m₂, m₄` as indices. -/
def ι3 : Fin 3 → Fin 2 × Fin 2 := ![(0, 0), (0, 1), (1, 1)]

/-- Inverse of `ι3` away from the singlet. -/
def κ3 : Fin 2 × Fin 2 → Fin 3
  | (0, 0) => 0
  | (0, 1) => 1
  | (1, 1) => 2
  | (1, 0) => 0

/-- Embed a `3×3` matrix, acting trivially on the singlet coordinate. -/
def lift3 (M : Matrix (Fin 3) (Fin 3) ℝ) : RMat4 := Matrix.of fun i j =>
  if i = sing ∨ j = sing then (if i = j then 1 else 0) else M (κ3 i) (κ3 j)

theorem lift3_mul (M N : Matrix (Fin 3) (Fin 3) ℝ) : lift3 (M * N) = lift3 M * lift3 N := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, sing, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Fin.sum_univ_three]

theorem lift3_one : lift3 (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, sing, Matrix.one_apply]

theorem lift3_transpose (M : Matrix (Fin 3) (Fin 3) ℝ) : lift3 Mᵀ = (lift3 M)ᵀ := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, sing, eq_comm]

theorem lift3_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) : lift3 M (ι3 a) (ι3 b) = M a b := by
  fin_cases a <;> fin_cases b <;> simp [lift3, κ3, ι3, sing]

theorem lift3_X3 (p q : ℝ) : lift3 (X3 p q) = rotX p q := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, sing, X3, rotX]

theorem lift3_Y3 (p q : ℝ) : lift3 (Y3 p q) = rotY p q := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, sing, Y3, rotY]

/-- The reflection of the `m₄` coordinate. -/
def Fd : RMat4 := Matrix.of fun i j =>
  match i, j with
  | (0, 0), (0, 0) => 1
  | (0, 1), (0, 1) => 1
  | (1, 0), (1, 0) => 1
  | (1, 1), (1, 1) => -1
  | _, _ => 0

theorem lift3_F3 : lift3 F3 = Fd := by
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, sing, F3, Fd]

/-- A real matrix fixing the singlet coordinate is the lift of its `3×3` block. -/
theorem eq_lift3 (Q : RMat4) (hs1 : Q * Prm = Prm) (hs2 : Prm * Q = Prm) :
    Q = lift3 (Matrix.of fun a b => Q (ι3 a) (ι3 b)) := by
  have c1 : ∀ i, Q i sing = if i = sing then 1 else 0 := by
    intro i
    have := congrFun (congrFun hs1 i) sing
    by_cases hi : i = sing
    · subst hi; simpa [Prm, Matrix.mul_diagonal, Matrix.diagonal_apply] using this
    · simpa [Prm, Matrix.mul_diagonal, Matrix.diagonal_apply, hi] using this
  have c2 : ∀ j, Q sing j = if j = sing then 1 else 0 := by
    intro j
    have := congrFun (congrFun hs2 sing) j
    by_cases hj : j = sing
    · subst hj; simpa [Prm, Matrix.diagonal_mul, Matrix.diagonal_apply] using this
    · simpa [Prm, Matrix.diagonal_mul, Matrix.diagonal_apply, hj, Ne.symm hj] using this
  ext ⟨i1, i2⟩ ⟨j1, j2⟩
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
  simp [lift3, κ3, ι3, sing] <;> first | exact c1 _ | exact c2 _ | skip

theorem lift3_injective {M N : Matrix (Fin 3) (Fin 3) ℝ} (h : lift3 M = lift3 N) : M = N := by
  ext a b
  have := congrFun (congrFun h (ι3 a)) (ι3 b)
  simpa [lift3_apply] using this

/-- **Reduction of a rotation fixing the singlet.** -/
theorem euler4 (Q : RMat4) (h1 : Q * Qᵀ = 1) (h2 : Qᵀ * Q = 1) (hs1 : Q * Prm = Prm)
    (hs2 : Prm * Q = Prm) : ∃ G : RMat4, Rlz G ∧ (G * Q = 1 ∨ G * Q = Fd) := by
  set Q3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun a b => Q (ι3 a) (ι3 b) with hQ3
  have hQ : Q = lift3 Q3 := eq_lift3 Q hs1 hs2
  have o1 : Q3 * Q3ᵀ = 1 := by
    apply lift3_injective
    rw [lift3_mul, lift3_transpose, lift3_one, ← hQ]; exact h1
  have o2 : Q3ᵀ * Q3 = 1 := by
    apply lift3_injective
    rw [lift3_mul, lift3_transpose, lift3_one, ← hQ]; exact h2
  obtain ⟨p1, q1, p2, q2, p3, q3, n1, n2, n3, hcase⟩ := euler3 Q3 o1 o2
  refine ⟨rotY p3 q3 * rotX p2 q2 * rotY p1 q1,
    ((rlz_rotY n3).mul (rlz_rotX n2)).mul (rlz_rotY n1), ?_⟩
  have e : rotY p3 q3 * rotX p2 q2 * rotY p1 q1 * Q
      = lift3 (Y3 p3 q3 * X3 p2 q2 * Y3 p1 q1 * Q3) := by
    rw [lift3_mul, lift3_mul, lift3_mul, lift3_Y3, lift3_Y3, lift3_X3, ← hQ]
  rw [e]
  rcases hcase with h | h
  · left; rw [h, lift3_one]
  · right; rw [h, lift3_F3]

end FormalResearch.FourQubitEntropy

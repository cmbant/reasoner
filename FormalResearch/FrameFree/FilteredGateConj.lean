import FormalResearch.FrameFree.FilteredGateEcho


/-!
# Filtered-gate law: conjugation of Pauli products by the Cartan gate

`A_conj`: `U (σ_a ⊗ 1) U† = C_bC_c σ_a⊗1 + S_bS_c 1⊗σ_a - S_bC_c σ_c⊗σ_b + C_bS_c σ_b⊗σ_c`
with `C_k = cos 2c_k`, `S_k = sin 2c_k`.  `S_gauge`: for symmetric `K = a + bσ_x + dσ_z`,
`U (ς ⊗ K) U = ς ⊗ m + m' ⊗ ς` with `ς = σ_y` (operator-Schmidt rank two).
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

theorem I_cube : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, Complex.I_sq]; ring

theorem I_four : Complex.I ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num

theorem A_formula (a : Fin 3) (θ φ : ℝ) :
    Uk θ (a + 1) * Uk φ (a + 2) * kr (sig a.succ) 1 =
      ((Real.cos θ * Real.cos φ : ℝ) : ℂ) • kr (sig a.succ) 1 +
      ((Real.sin θ * Real.sin φ : ℝ) : ℂ) • kr 1 (sig a.succ) -
      ((Real.sin θ * Real.cos φ : ℝ) : ℂ) • kr (sig (a + 2).succ) (sig (a + 1).succ) +
      ((Real.cos θ * Real.sin φ : ℝ) : ℂ) • kr (sig (a + 1).succ) (sig (a + 2).succ) := by
  fin_cases a <;> ext ⟨i, k⟩ ⟨j, l⟩ <;> fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Uk, Pm, sig, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, kr_apply,
      Matrix.one_apply] <;> ring_nf <;> simp only [Complex.I_sq, I_cube, I_four] <;> ring

theorem conj_Uk_gen (X : M4) (hX : X * X = 1) (s : ℝ) (hs1 : s = 1 ∨ s = -1) (j : Fin 3)
    (hs : X * Pm j * X = (s : ℂ) • Pm j) (θ : ℝ) : X * Uk θ j * X = Uk (s * θ) j := by
  unfold Uk
  have e : X * ((Real.cos θ : ℂ) • (1 : M4) - (Complex.I * (Real.sin θ : ℂ)) • Pm j) * X
      = (Real.cos θ : ℂ) • (X * X) - (Complex.I * (Real.sin θ : ℂ)) • (X * Pm j * X) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [e, hX, hs]
  rcases hs1 with h | h <;> rw [h] <;> simp [smul_smul]

theorem Ug_neg (c : Fin 3 → ℝ) : (Ug c)ᴴ = Ug (fun k => -c k) := by
  rw [Ug_conjTranspose]
  unfold Ug
  have h01 := (Uk_comm (-c 0) (-c 1) 0 1).eq
  have h02 := (Uk_comm (-c 0) (-c 2) 0 2).eq
  have h12 := (Uk_comm (-c 1) (-c 2) 1 2).eq
  simp only
  calc Uk (-c 2) 2 * Uk (-c 1) 1 * Uk (-c 0) 0
      = Uk (-c 2) 2 * (Uk (-c 1) 1 * Uk (-c 0) 0) := by simp only [Matrix.mul_assoc]
    _ = Uk (-c 2) 2 * (Uk (-c 0) 0 * Uk (-c 1) 1) := by rw [← h01]
    _ = (Uk (-c 2) 2 * Uk (-c 0) 0) * Uk (-c 1) 1 := by simp only [Matrix.mul_assoc]
    _ = (Uk (-c 0) 0 * Uk (-c 2) 2) * Uk (-c 1) 1 := by rw [← h02]
    _ = Uk (-c 0) 0 * (Uk (-c 2) 2 * Uk (-c 1) 1) := by simp only [Matrix.mul_assoc]
    _ = Uk (-c 0) 0 * (Uk (-c 1) 1 * Uk (-c 2) 2) := by rw [← h12]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem UXUg (X : M4) (hX : X * X = 1) (s : Fin 3 → ℝ) (hs1 : ∀ k, s k = 1 ∨ s k = -1)
    (hs : ∀ k, X * Pm k * X = (s k : ℂ) • Pm k) (c d : Fin 3 → ℝ) :
    Ug c * X * Ug d = Uk (c 0 + s 0 * d 0) 0 * Uk (c 1 + s 1 * d 1) 1 * Uk (c 2 + s 2 * d 2) 2 * X := by
  have e1 : Ug c * X * Ug d = Ug c * (X * Ug d * X) * X := by
    calc Ug c * X * Ug d = Ug c * X * Ug d * (X * X) := by rw [hX, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : X * Ug d * X = Uk (s 0 * d 0) 0 * Uk (s 1 * d 1) 1 * Uk (s 2 * d 2) 2 := by
    unfold Ug
    rw [conj3 _ _ _ _ hX, conj_Uk_gen X hX _ (hs1 0) 0 (hs 0), conj_Uk_gen X hX _ (hs1 1) 1 (hs 1),
      conj_Uk_gen X hX _ (hs1 2) 2 (hs 2)]
  rw [e1, e2]
  unfold Ug
  rw [prod3 _ _ _ _ _ _ (Uk_comm _ _ _ _) (Uk_comm _ _ _ _) (Uk_comm _ _ _ _), Uk_mul, Uk_mul, Uk_mul]

theorem kr_sig_one_sq (a : Fin 3) : kr (sig a.succ) 1 * kr (sig a.succ) 1 = 1 := by
  rw [kr_mul, sig_sq, Matrix.one_mul, kr_one]

theorem kr_sig_one_Pm (a k : Fin 3) :
    kr (sig a.succ) 1 * Pm k * kr (sig a.succ) 1 = (esg a k : ℂ) • Pm k := by
  unfold Pm esg
  rw [kr_mul, kr_mul, Matrix.mul_one, Matrix.one_mul, sig_conj_same a k]
  by_cases h : a = k
  · simp [h]
  · simp [h, kr_neg_left]

theorem esg_pm (a k : Fin 3) : esg a k = 1 ∨ esg a k = -1 := by
  unfold esg; split_ifs <;> simp

theorem A_conj (c : Fin 3 → ℝ) (a : Fin 3) :
    Ug c * kr (sig a.succ) 1 * (Ug c)ᴴ =
      ((Real.cos (2 * c (a + 1)) * Real.cos (2 * c (a + 2)) : ℝ) : ℂ) • kr (sig a.succ) 1 +
      ((Real.sin (2 * c (a + 1)) * Real.sin (2 * c (a + 2)) : ℝ) : ℂ) • kr 1 (sig a.succ) -
      ((Real.sin (2 * c (a + 1)) * Real.cos (2 * c (a + 2)) : ℝ) : ℂ) • kr (sig (a + 2).succ) (sig (a + 1).succ) +
      ((Real.cos (2 * c (a + 1)) * Real.sin (2 * c (a + 2)) : ℝ) : ℂ) • kr (sig (a + 1).succ) (sig (a + 2).succ) := by
  rw [Ug_neg, UXUg _ (kr_sig_one_sq a) (esg a) (esg_pm a) (kr_sig_one_Pm a)]
  rw [← A_formula a (2 * c (a + 1)) (2 * c (a + 2))]
  fin_cases a
  · simp [esg, Uk_zero, ← two_mul]
  · simp [esg, Uk_zero, ← two_mul]
    rw [(Uk_comm _ _ 0 2).eq]
  · simp [esg, Uk_zero, ← two_mul]

theorem kr_sig_sq (p q : Fin 3) :
    kr (sig p.succ) (sig q.succ) * kr (sig p.succ) (sig q.succ) = 1 := by
  rw [kr_mul, sig_sq, sig_sq, kr_one]

theorem kr_sig_Pm (p q k : Fin 3) :
    kr (sig p.succ) (sig q.succ) * Pm k * kr (sig p.succ) (sig q.succ) =
      ((esg p k * esg q k : ℝ) : ℂ) • Pm k := by
  unfold Pm
  rw [kr_mul, kr_mul, sig_conj_same, sig_conj_same, kr_smul_left, kr_smul_right, smul_smul]
  unfold esg
  split_ifs <;> simp

theorem Uk_mul_X (θ : ℝ) (j : Fin 3) (X : M4) :
    Uk θ j * X = (Real.cos θ : ℂ) • X - (Complex.I * (Real.sin θ : ℂ)) • (Pm j * X) := by
  unfold Uk
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul]

theorem S_one (c : Fin 3 → ℝ) :
    Ug c * kr (sig 2) 1 * Ug c =
      (Real.cos (2 * c 1) : ℂ) • kr (sig 2) 1 -
        (Complex.I * (Real.sin (2 * c 1) : ℂ)) • kr 1 (sig 2) := by
  have h := UXUg (kr (sig (1 : Fin 3).succ) 1) (kr_sig_one_sq 1) (esg 1) (esg_pm 1)
    (kr_sig_one_Pm 1) c c
  have e : Uk (c 0 + esg 1 0 * c 0) 0 * Uk (c 1 + esg 1 1 * c 1) 1 * Uk (c 2 + esg 1 2 * c 2) 2 =
      Uk (2 * c 1) 1 := by
    simp [esg, Uk_zero, two_mul]
  rw [e] at h
  have h1 : (1 : Fin 3).succ = 2 := rfl
  rw [h1] at h
  rw [h, Uk_mul_X]
  have : Pm 1 * kr (sig 2) 1 = kr 1 (sig 2) := by
    unfold Pm
    rw [kr_mul]
    show kr (sig 2 * sig 2) (sig 2 * 1) = _
    rw [sig_sq, Matrix.mul_one]
  rw [this]

theorem S_x (c : Fin 3 → ℝ) :
    Ug c * kr (sig 2) (sig 1) * Ug c =
      (Real.cos (2 * c 2) : ℂ) • kr (sig 2) (sig 1) -
        (Complex.I * (Real.sin (2 * c 2) : ℂ)) • kr (sig 1) (sig 2) := by
  have h := UXUg (kr (sig (1 : Fin 3).succ) (sig (0 : Fin 3).succ)) (kr_sig_sq 1 0)
    (fun k => esg 1 k * esg 0 k)
    (fun k => by rcases esg_pm 1 k with h | h <;> rcases esg_pm 0 k with h' | h' <;> simp [h, h'])
    (kr_sig_Pm 1 0) c c
  have e : Uk (c 0 + (esg 1 0 * esg 0 0) * c 0) 0 * Uk (c 1 + (esg 1 1 * esg 0 1) * c 1) 1 *
      Uk (c 2 + (esg 1 2 * esg 0 2) * c 2) 2 = Uk (2 * c 2) 2 := by
    simp [esg, Uk_zero, two_mul]
  rw [e] at h
  have h1 : (1 : Fin 3).succ = 2 := rfl
  have h0 : (0 : Fin 3).succ = 1 := rfl
  rw [h1, h0] at h
  rw [h, Uk_mul_X]
  have : Pm 2 * kr (sig 2) (sig 1) = kr (sig 1) (sig 2) := by
    unfold Pm
    rw [kr_mul]
    show kr (sig 3 * sig 2) (sig 3 * sig 1) = _
    ext ⟨i, k⟩ ⟨j, l⟩
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp [kr_apply, sig, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this]

theorem S_z (c : Fin 3 → ℝ) :
    Ug c * kr (sig 2) (sig 3) * Ug c =
      (Real.cos (2 * c 0) : ℂ) • kr (sig 2) (sig 3) -
        (Complex.I * (Real.sin (2 * c 0) : ℂ)) • kr (sig 3) (sig 2) := by
  have h := UXUg (kr (sig (1 : Fin 3).succ) (sig (2 : Fin 3).succ)) (kr_sig_sq 1 2)
    (fun k => esg 1 k * esg 2 k)
    (fun k => by rcases esg_pm 1 k with h | h <;> rcases esg_pm 2 k with h' | h' <;> simp [h, h'])
    (kr_sig_Pm 1 2) c c
  have e : Uk (c 0 + (esg 1 0 * esg 2 0) * c 0) 0 * Uk (c 1 + (esg 1 1 * esg 2 1) * c 1) 1 *
      Uk (c 2 + (esg 1 2 * esg 2 2) * c 2) 2 = Uk (2 * c 0) 0 := by
    simp [esg, Uk_zero, two_mul]
  rw [e] at h
  have h1 : (1 : Fin 3).succ = 2 := rfl
  have h0 : (2 : Fin 3).succ = 3 := rfl
  rw [h1, h0] at h
  rw [h, Uk_mul_X]
  have : Pm 0 * kr (sig 2) (sig 3) = kr (sig 3) (sig 2) := by
    unfold Pm
    rw [kr_mul]
    show kr (sig 1 * sig 2) (sig 1 * sig 3) = _
    ext ⟨i, k⟩ ⟨j, l⟩
    fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
      simp [kr_apply, sig, Matrix.mul_apply, Fin.sum_univ_two]
  rw [this]

/-- Symmetric `K = a 1 + b σ_x + d σ_z`. -/
noncomputable def Ksym (a b d : ℂ) : M2 := a • (1 : M2) + b • sig 1 + d • sig 3

theorem S_gauge (c : Fin 3 → ℝ) (a b d : ℂ) :
    Ug c * kr (sig 2) (Ksym a b d) * Ug c =
      kr (sig 2) (Ksym (a * (Real.cos (2 * c 1) : ℂ)) (b * (Real.cos (2 * c 2) : ℂ))
        (d * (Real.cos (2 * c 0) : ℂ))) +
      kr (Ksym (-(Complex.I * a * (Real.sin (2 * c 1) : ℂ)))
        (-(Complex.I * b * (Real.sin (2 * c 2) : ℂ)))
        (-(Complex.I * d * (Real.sin (2 * c 0) : ℂ)))) (sig 2) := by
  have e : kr (sig 2) (Ksym a b d) =
      a • kr (sig 2) 1 + b • kr (sig 2) (sig 1) + d • kr (sig 2) (sig 3) := by
    unfold Ksym
    simp only [kr_add_right, kr_smul_right]
  rw [e]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [S_one, S_x, S_z]
  unfold Ksym
  simp only [kr_add_right, kr_add_left, kr_smul_right, kr_smul_left]
  module

end FormalResearch.FrameFree.FTG

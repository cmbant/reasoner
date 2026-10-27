import FormalResearch.FrameFree.FilteredGateBasic

/-!
# Filtered-gate law: the Pauli echoes

For `U = U_c` the Pauli echoes `(A,B,C) = (1, σ_j, σ_j)` and `(σ_j, 1, σ_j)` at `W = 1` give
`|Tr[U(A⊗B)U(W⊗C)]|² = (1 ± cos 4c_j) · 2‖(A⊗B)U(W⊗C)‖_F²`, with `‖·‖_F² = 4`.
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

/-- `1 ⊗ σ_j`. -/
def Lm (j : Fin 3) : M4 := kr 1 (sig j.succ)

/-- Sign `+1` if `j = k`, else `-1`. -/
def esg (j k : Fin 3) : ℝ := if j = k then 1 else -1

theorem Lm_sq (j : Fin 3) : Lm j * Lm j = 1 := by
  unfold Lm; rw [kr_mul, Matrix.one_mul, sig_sq, kr_one]

theorem Lm_conj_Pm (j k : Fin 3) : Lm j * Pm k * Lm j = (esg j k : ℂ) • Pm k := by
  unfold Lm Pm esg
  rw [kr_mul, kr_mul, Matrix.one_mul, Matrix.mul_one, sig_conj_same j k]
  by_cases h : j = k
  · simp [h]
  · simp [h, kr_neg_right]

theorem Lm_conj_Uk (j k : Fin 3) (θ : ℝ) : Lm j * Uk θ k * Lm j = Uk (esg j k * θ) k := by
  have hL := Lm_sq j
  unfold Uk
  have e : Lm j * ((Real.cos θ : ℂ) • (1 : M4) - (Complex.I * (Real.sin θ : ℂ)) • Pm k) * Lm j
      = (Real.cos θ : ℂ) • (Lm j * Lm j) - (Complex.I * (Real.sin θ : ℂ)) • (Lm j * Pm k * Lm j) := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  rw [e, hL, Lm_conj_Pm]
  have hs : esg j k = 1 ∨ esg j k = -1 := by unfold esg; split_ifs <;> simp
  rcases hs with h | h <;> rw [h] <;> simp [smul_smul]

theorem conj3 (L X Y Z : M4) (hL : L * L = 1) :
    L * (X * Y * Z) * L = (L * X * L) * (L * Y * L) * (L * Z * L) := by
  rw [show (L * X * L) * (L * Y * L) * (L * Z * L) = L * X * (L * L) * Y * (L * L) * Z * L by
    simp only [Matrix.mul_assoc], hL]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

theorem Lm_conj_Ug (j : Fin 3) (c : Fin 3 → ℝ) :
    Lm j * Ug c * Lm j =
      Uk (esg j 0 * c 0) 0 * Uk (esg j 1 * c 1) 1 * Uk (esg j 2 * c 2) 2 := by
  unfold Ug
  rw [conj3 _ _ _ _ (Lm_sq j), Lm_conj_Uk, Lm_conj_Uk, Lm_conj_Uk]

theorem Pm_comm_Uk (j k : Fin 3) (θ : ℝ) : Commute (Pm j) (Uk θ k) := by
  unfold Uk
  exact Commute.sub_right ((Commute.one_right _).smul_right _) ((show Commute (Pm j) (Pm k) from Pm_comm j k).smul_right _)

theorem Pm_comm_Ug (j : Fin 3) (c : Fin 3 → ℝ) : Commute (Pm j) (Ug c) := by
  unfold Ug
  exact ((Pm_comm_Uk j 0 _).mul_right (Pm_comm_Uk j 1 _)).mul_right (Pm_comm_Uk j 2 _)

theorem Ug_mul_echo (j : Fin 3) (c : Fin 3 → ℝ) :
    Ug c * (Lm j * Ug c * Lm j) = Uk (2 * c j) j := by
  rw [Lm_conj_Ug]
  unfold Ug
  rw [prod3 _ _ _ _ _ _ (Uk_comm _ _ _ _) (Uk_comm _ _ _ _) (Uk_comm _ _ _ _), Uk_mul, Uk_mul, Uk_mul]
  fin_cases j <;> simp [esg, Uk_zero, two_mul]

theorem Uk_trace (θ : ℝ) (j : Fin 3) : (Uk θ j).trace = 4 * (Real.cos θ : ℂ) := by
  unfold Uk
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Pm_trace]
  simp [Matrix.trace_one]
  ring

theorem Pm_Uk_trace (θ : ℝ) (j : Fin 3) :
    (Pm j * Uk θ j).trace = -(4 * Complex.I * (Real.sin θ : ℂ)) := by
  unfold Uk
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Pm_sq, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Pm_trace]
  simp [Matrix.trace_one]
  ring

theorem fro2_unitary (M : M4) (h : Mᴴ * M = 1) : fro2 M = 4 := by
  have := fro2_one
  unfold fro2 at this ⊢
  simpa [h] using this

theorem Lm_herm (j : Fin 3) : (Lm j)ᴴ = Lm j := by
  unfold Lm; rw [kr_conjTranspose, Matrix.conjTranspose_one, sig_herm]

/-- The filtered gate `(A ⊗ B) U (W ⊗ C)`. -/
noncomputable def gm (c : Fin 3 → ℝ) (A B W C : M2) : M4 := kr A B * Ug c * kr W C

/-- The overlap `Tr[U (A ⊗ B) U (W ⊗ C)]`. -/
noncomputable def ov (c : Fin 3 → ℝ) (A B W C : M2) : ℂ := (Ug c * gm c A B W C).trace

/-- The sharp constant `δ = max_j |cos 4c_j|`. -/
noncomputable def dl (c : Fin 3 → ℝ) : ℝ :=
  max (max |Real.cos (4 * c 0)| |Real.cos (4 * c 1)|) |Real.cos (4 * c 2)|

theorem le_dl (c : Fin 3 → ℝ) (k : Fin 3) : |Real.cos (4 * c k)| ≤ dl c := by
  unfold dl; fin_cases k <;> simp

theorem exists_dl (c : Fin 3 → ℝ) : ∃ k : Fin 3, |Real.cos (4 * c k)| = dl c := by
  unfold dl
  rcases max_choice (max |Real.cos (4 * c 0)| |Real.cos (4 * c 1)|) |Real.cos (4 * c 2)| with h | h
  · rcases max_choice |Real.cos (4 * c 0)| |Real.cos (4 * c 1)| with h' | h'
    · exact ⟨0, by rw [h, h']⟩
    · exact ⟨1, by rw [h, h']⟩
  · exact ⟨2, by rw [h]⟩

theorem echo_plus (c : Fin 3 → ℝ) (j : Fin 3) :
    fro2 (gm c 1 (sig j.succ) 1 (sig j.succ)) = 4 ∧
    ‖ov c 1 (sig j.succ) 1 (sig j.succ)‖ ^ 2 =
      (1 + Real.cos (4 * c j)) * (2 * fro2 (gm c 1 (sig j.succ) 1 (sig j.succ))) := by
  have hg : gm c 1 (sig j.succ) 1 (sig j.succ) = Lm j * Ug c * Lm j := rfl
  have h4 : fro2 (gm c 1 (sig j.succ) 1 (sig j.succ)) = 4 := by
    rw [hg, fro2_mul_unitary_right _ _ (by rw [Lm_herm, Lm_sq]), fro2_mul_unitary_left _ _ (by
      rw [Lm_herm, Lm_sq])]
    exact fro2_unitary _ (Ug_conjT_mul c)
  refine ⟨h4, ?_⟩
  unfold ov
  rw [h4, hg, Ug_mul_echo, Uk_trace]
  have e : (4 * (Real.cos (2 * c j) : ℂ)) = ((4 * Real.cos (2 * c j) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h : Real.cos (4 * c j) = 2 * Real.cos (2 * c j) ^ 2 - 1 := by
    rw [show 4 * c j = 2 * (2 * c j) by ring, Real.cos_two_mul]
  rw [h]; ring

theorem echo_minus (c : Fin 3 → ℝ) (j : Fin 3) :
    fro2 (gm c (sig j.succ) 1 1 (sig j.succ)) = 4 ∧
    ‖ov c (sig j.succ) 1 1 (sig j.succ)‖ ^ 2 =
      (1 - Real.cos (4 * c j)) * (2 * fro2 (gm c (sig j.succ) 1 1 (sig j.succ))) := by
  have hP : Pm j * Lm j = kr (sig j.succ) 1 := by
    unfold Pm Lm; rw [kr_mul, Matrix.mul_one, sig_sq]
  have hg : gm c (sig j.succ) 1 1 (sig j.succ) = Pm j * (Lm j * Ug c * Lm j) := by
    unfold gm
    rw [← hP]
    show Pm j * Lm j * Ug c * Lm j = _
    simp only [Matrix.mul_assoc]
  have hPu : Pm j * (Pm j)ᴴ = 1 := by rw [Pm_herm, Pm_sq]
  have hPu' : (Pm j)ᴴ * Pm j = 1 := by rw [Pm_herm, Pm_sq]
  have h4 : fro2 (gm c (sig j.succ) 1 1 (sig j.succ)) = 4 := by
    rw [hg, fro2_mul_unitary_left _ _ hPu', fro2_mul_unitary_right _ _ (by rw [Lm_herm, Lm_sq]),
      fro2_mul_unitary_left _ _ (by rw [Lm_herm, Lm_sq])]
    exact fro2_unitary _ (Ug_conjT_mul c)
  refine ⟨h4, ?_⟩
  unfold ov
  rw [h4, hg, ← Matrix.mul_assoc, (Pm_comm_Ug j c).eq.symm, Matrix.mul_assoc, Ug_mul_echo,
    Pm_Uk_trace]
  have e : -(4 * Complex.I * (Real.sin (2 * c j) : ℂ)) = Complex.I * ((-(4 * Real.sin (2 * c j)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h : Real.cos (4 * c j) = 1 - 2 * Real.sin (2 * c j) ^ 2 := by
    rw [show 4 * c j = 2 * (2 * c j) by ring, Real.cos_two_mul, Real.cos_sq']; ring
  rw [h]; ring

/-- The bound `1 + δ` is attained by a Pauli echo at `W = 1`. -/
theorem echo_attain (c : Fin 3 → ℝ) :
    ∃ A B C : M2, fro2 (gm c A B 1 C) = 4 ∧
      ‖ov c A B 1 C‖ ^ 2 = (1 + dl c) * (2 * fro2 (gm c A B 1 C)) := by
  obtain ⟨k, hk⟩ := exists_dl c
  by_cases h : 0 ≤ Real.cos (4 * c k)
  · obtain ⟨h1, h2⟩ := echo_plus c k
    refine ⟨1, sig k.succ, sig k.succ, h1, ?_⟩
    rw [h2, ← hk, abs_of_nonneg h]
  · obtain ⟨h1, h2⟩ := echo_minus c k
    refine ⟨sig k.succ, 1, sig k.succ, h1, ?_⟩
    rw [h2, ← hk, abs_of_neg (not_le.mp h)]
    ring

end FormalResearch.FrameFree.FTG

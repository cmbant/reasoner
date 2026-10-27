import FormalResearch.FrameFree.FilteredGateCore


/-!
# Filtered-gate law: reduction to `sin 4c_k ≥ 0`

`Law c` is the filtered-gate law at `c`.  Conjugating by `1 ⊗ σ_j` replaces `c` by
`(esg j k · c_k)_k` (`Law_flip`), and entrywise conjugation replaces `c` by `-c` (`Law_neg`).  These
generate all sign changes `c_k ↦ ±c_k`, so every `c` reduces to one with `sin 4c_k ≥ 0` for all `k`,
where `core_good` applies (`Law_all`).
-/

open scoped Matrix Kronecker ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG

/-- The filtered-gate law at a fixed Cartan vector `c`. -/
def Law (c : Fin 3 → ℝ) : Prop :=
  ∀ A B C W : M2, Wᴴ * W = 1 →
    ‖(Ug c * kr A B * Ug c * kr W C).trace‖ ^ 2 ≤ 2 * (1 + dl c) * fro2 (kr A B * Ug c * kr W C)

theorem fro2_eq (N : M4) : fro2 N = ∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, Complex.normSq (N y x) := by
  have h : Matrix.trace (Nᴴ * N) =
      ((∑ x : Fin 2 × Fin 2, ∑ y : Fin 2 × Fin 2, Complex.normSq (N y x) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.star_def, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  unfold fro2
  rw [h, Complex.ofReal_re]

theorem fro2_conj (N : M4) : fro2 (N.map conj) = fro2 N := by
  simp [fro2_eq, Matrix.map_apply]

theorem tr_conj (N : M4) : (N.map conj).trace = conj N.trace := by
  simp [Matrix.trace, map_sum]

theorem abs_cos4_esg (j k : Fin 3) (x : ℝ) :
    |Real.cos (4 * (esg j k * x))| = |Real.cos (4 * x)| := by
  rcases esg_pm j k with h | h <;> rw [h]
  · simp
  · rw [show 4 * (-1 * x) = -(4 * x) by ring, Real.cos_neg]

theorem dl_flip (j : Fin 3) (c : Fin 3 → ℝ) : dl (fun k => esg j k * c k) = dl c := by
  unfold dl; simp only [abs_cos4_esg]

theorem dl_neg (c : Fin 3 → ℝ) : dl (fun k => -c k) = dl c := by
  unfold dl; simp only [mul_neg, Real.cos_neg]

theorem Law_flip (j : Fin 3) (c : Fin 3 → ℝ) (h : Law c) : Law (fun k => esg j k * c k) := by
  intro A B C W hW
  have hL : Lm j * Lm j = 1 := Lm_sq j
  have hLh : (Lm j)ᴴ * Lm j = 1 := by rw [Lm_herm, hL]
  have hLh' : Lm j * (Lm j)ᴴ = 1 := by rw [Lm_herm, hL]
  have hU : Ug (fun k => esg j k * c k) = Lm j * Ug c * Lm j := (Lm_conj_Ug j c).symm
  set σ := sig j.succ
  have hF : Lm j * kr A B * Lm j = kr A (σ * B * σ) := by
    unfold Lm; rw [kr_mul, kr_mul, Matrix.one_mul, Matrix.mul_one]
  have hG : Lm j * kr W C * Lm j = kr W (σ * C * σ) := by
    unfold Lm; rw [kr_mul, kr_mul, Matrix.one_mul, Matrix.mul_one]
  have h1 := h A (σ * B * σ) (σ * C * σ) W hW
  have e1 : (Ug (fun k => esg j k * c k) * kr A B * Ug (fun k => esg j k * c k) * kr W C).trace =
      (Ug c * kr A (σ * B * σ) * Ug c * kr W (σ * C * σ)).trace := by
    rw [← hF, ← hG, hU]
    have : Lm j * Ug c * Lm j * kr A B * (Lm j * Ug c * Lm j) * kr W C =
        Lm j * (Ug c * (Lm j * kr A B * Lm j) * Ug c * (Lm j * kr W C)) := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc, hL, Matrix.mul_one]
  have e2 : fro2 (kr A B * Ug (fun k => esg j k * c k) * kr W C) =
      fro2 (kr A (σ * B * σ) * Ug c * kr W (σ * C * σ)) := by
    rw [← hF, ← hG, hU]
    have : Lm j * kr A B * Lm j * Ug c * (Lm j * kr W C * Lm j) =
        Lm j * (kr A B * (Lm j * Ug c * Lm j) * kr W C) * Lm j := by
      simp only [Matrix.mul_assoc]
    rw [this, fro2_mul_unitary_right _ _ hLh', fro2_mul_unitary_left _ _ hLh]
  rw [e1, e2, dl_flip]
  exact h1

theorem Pm_conj (j : Fin 3) : (Pm j).map conj = Pm j := by
  unfold Pm
  rw [kr_conj]
  fin_cases j <;> ext ⟨i, k⟩ ⟨i', k'⟩ <;> fin_cases i <;> fin_cases k <;> fin_cases i' <;>
    fin_cases k' <;> simp [kr_apply, sig]

theorem Uk_conj (θ : ℝ) (j : Fin 3) : (Uk θ j).map conj = Uk (-θ) j := by
  unfold Uk
  ext x y
  have h := congrFun (congrFun (Pm_conj j) x) y
  simp only [Matrix.map_apply] at h ⊢
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul, h,
    Complex.conj_I, Complex.conj_ofReal, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]

theorem Ug_conj (c : Fin 3 → ℝ) : (Ug c).map conj = Ug (fun k => -c k) := by
  unfold Ug
  simp only [Matrix.map_mul, Uk_conj]

theorem Wb_Wb (M : M2) : Wb (Wb M) = M := by
  ext i j; simp [Wb]

theorem map_conj_eq_Wb (M : M2) : M.map conj = Wb M := rfl

theorem Law_neg (c : Fin 3 → ℝ) (h : Law c) : Law (fun k => -c k) := by
  intro A B C W hW
  have hW' : (Wb W)ᴴ * Wb W = 1 := (Wb_unit W hW).2.1
  have h1 := h (Wb A) (Wb B) (Wb C) (Wb W) hW'
  have k1 : Ug (fun k => -c k) * kr A B * Ug (fun k => -c k) * kr W C =
      (Ug c * kr (Wb A) (Wb B) * Ug c * kr (Wb W) (Wb C)).map conj := by
    rw [← Ug_conj]
    simp only [Matrix.map_mul, kr_conj]
    simp only [map_conj_eq_Wb, Wb_Wb]
  have k2 : kr A B * Ug (fun k => -c k) * kr W C =
      (kr (Wb A) (Wb B) * Ug c * kr (Wb W) (Wb C)).map conj := by
    rw [← Ug_conj]
    simp only [Matrix.map_mul, kr_conj]
    simp only [map_conj_eq_Wb, Wb_Wb]
  rw [k1, k2, tr_conj, fro2_conj, dl_neg]
  simpa using h1

theorem Law_of_flip (j : Fin 3) (c : Fin 3 → ℝ) (h : Law (fun k => esg j k * c k)) : Law c := by
  have := Law_flip j _ h
  have e : (fun k => esg j k * (esg j k * c k)) = c := by
    funext k; rcases esg_pm j k with h | h <;> rw [h] <;> ring
  rwa [e] at this

theorem Law_of_neg (c : Fin 3 → ℝ) (h : Law (fun k => -c k)) : Law c := by
  have := Law_neg _ h
  simpa using this

theorem sin4_esg (j k : Fin 3) (x : ℝ) : Real.sin (4 * (esg j k * x)) = esg j k * Real.sin (4 * x) := by
  rcases esg_pm j k with h | h <;> rw [h]
  · simp
  · rw [show 4 * (-1 * x) = -(4 * x) by ring, Real.sin_neg]; ring

theorem sin4_neg (x : ℝ) : Real.sin (4 * -x) = -Real.sin (4 * x) := by
  rw [mul_neg, Real.sin_neg]

/-- The filtered-gate law for every Cartan vector `c`. -/
theorem Law_all (c : Fin 3 → ℝ) : Law c := by
  have g := fun (c : Fin 3 → ℝ) (hg : ∀ k, 0 ≤ Real.sin (4 * c k)) =>
    (fun A B C W hW => core_good c hg A B C W hW : Law c)
  rcases le_or_gt 0 (Real.sin (4 * c 0)) with h0 | h0 <;>
  rcases le_or_gt 0 (Real.sin (4 * c 1)) with h1 | h1 <;>
  rcases le_or_gt 0 (Real.sin (4 * c 2)) with h2 | h2
  · exact g c (fun k => by fin_cases k <;> assumption)
  · refine Law_of_neg c (Law_of_flip 2 _ (g _ fun k => ?_))
    simp only [sin4_esg, sin4_neg]
    fin_cases k <;> simp [esg] <;> linarith
  · refine Law_of_neg c (Law_of_flip 1 _ (g _ fun k => ?_))
    simp only [sin4_esg, sin4_neg]
    fin_cases k <;> simp [esg] <;> linarith
  · refine Law_of_flip 0 c (g _ fun k => ?_)
    simp only [sin4_esg]
    fin_cases k <;> simp [esg] <;> linarith
  · refine Law_of_neg c (Law_of_flip 0 _ (g _ fun k => ?_))
    simp only [sin4_esg, sin4_neg]
    fin_cases k <;> simp [esg] <;> linarith
  · refine Law_of_flip 1 c (g _ fun k => ?_)
    simp only [sin4_esg]
    fin_cases k <;> simp [esg] <;> linarith
  · refine Law_of_flip 2 c (g _ fun k => ?_)
    simp only [sin4_esg]
    fin_cases k <;> simp [esg] <;> linarith
  · refine Law_of_neg c (g _ fun k => ?_)
    simp only [sin4_neg]
    fin_cases k <;> simp <;> linarith

end FormalResearch.FrameFree.FTG

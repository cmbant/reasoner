module

public import FormalResearch.FourQubitEntropy.PaperEGoSliceGen

/-!
# `thm:fqe-global-overlap`, layer (c): first-order stationarity at a closest point

For a frame `φ` with magic coordinates `√3 X + i Y` (`CoordIs`), the height inequality `height_ineqG`
along one-parameter families of plane rotations (`rotM`, with `c² + σ² = 1`) and along the phase
`(c, s)` with `c² + 3 s² = 1` gives the ten linear relations of `eq:fqe-slice-stationary`
(`Stationary`, `stationary_of_frame`):

`Y₀₀ = Σ_j X_jj`, `Y_0j = 3 X_j0`, `Y_j0 = 3 X_0j`, `Y_jk = Y_kj` (`1 ≤ j < k ≤ 3`).

Elementary: each rotation gives `σ a + (c - 1) b ≤ 0` for all `c² + σ² = 1`, and `lin_zero` forces `a = 0`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-- The plane rotation in the `(i, j)` plane: `c` on the two diagonal entries, `σ` at `(i,j)`,
`-σ` at `(j,i)`. -/
def rotM (i j : Fin 4) (c σ : ℝ) : M4R := Matrix.of fun a b =>
  if a = i ∧ b = i then c else if a = j ∧ b = j then c else if a = i ∧ b = j then σ
  else if a = j ∧ b = i then -σ else if a = b then 1 else 0

theorem rotM_orth (i j : Fin 4) (hij : i ≠ j) (c σ : ℝ) (h : c ^ 2 + σ ^ 2 = 1) :
    (rotM i j c σ)ᵀ * rotM i j c σ = 1 := by
  fin_cases i <;> fin_cases j <;> (try simp at hij) <;>
    (ext a b
     fin_cases a <;> fin_cases b <;>
       simp [rotM, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> nlinarith [h])

/-- If `t a - t² b ≤ 0` for all `t`, then `a = 0`. -/
theorem lin_zero_core {a b : ℝ} (h : ∀ t : ℝ, t * a - t ^ 2 * b ≤ 0) : a = 0 := by
  by_contra ha
  have hD : 0 < |b| + 1 := by positivity
  have h1 := h (a / (|b| + 1))
  have e : a / (|b| + 1) * a - (a / (|b| + 1)) ^ 2 * b = a ^ 2 * ((|b| + 1) - b) / (|b| + 1) ^ 2 := by
    field_simp
  rw [e] at h1
  have h2 : 0 < a ^ 2 := by positivity
  have h3 : 0 < (|b| + 1) - b := by linarith [le_abs_self b]
  have h4 : 0 < a ^ 2 * ((|b| + 1) - b) / (|b| + 1) ^ 2 := by positivity
  linarith

/-- Rotation form: `σ a + (c - 1) b ≤ 0` whenever `c² + σ² = 1` forces `a = 0`. -/
theorem lin_zero_rot {a b : ℝ} (h : ∀ c σ : ℝ, c ^ 2 + σ ^ 2 = 1 → σ * a + (c - 1) * b ≤ 0) :
    a = 0 := by
  refine lin_zero_core (b := b) fun t => ?_
  have hp : 0 < 1 + t ^ 2 := by positivity
  have h1 := h ((1 - t ^ 2) / (1 + t ^ 2)) (2 * t / (1 + t ^ 2)) (by field_simp; ring)
  have e : 2 * t / (1 + t ^ 2) * a + ((1 - t ^ 2) / (1 + t ^ 2) - 1) * b =
      (2 * (t * a - t ^ 2 * b)) / (1 + t ^ 2) := by field_simp; ring
  rw [e] at h1
  have := (div_nonpos_iff.1 h1)
  rcases this with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · linarith
  · linarith

/-- Phase form: `3 s a + (c - 1) b ≤ 0` whenever `c² + 3 s² = 1` forces `a = 0`. -/
theorem lin_zero_phase {a b : ℝ} (h : ∀ c s : ℝ, c ^ 2 + 3 * s ^ 2 = 1 → 3 * s * a + (c - 1) * b ≤ 0) :
    a = 0 := by
  refine lin_zero_core (b := b) fun t => ?_
  have hp : 0 < 1 + 3 * t ^ 2 := by positivity
  have h1 := h ((1 - 3 * t ^ 2) / (1 + 3 * t ^ 2)) (2 * t / (1 + 3 * t ^ 2)) (by field_simp; ring)
  have e : 3 * (2 * t / (1 + 3 * t ^ 2)) * a + ((1 - 3 * t ^ 2) / (1 + 3 * t ^ 2) - 1) * b =
      (6 * (t * a - t ^ 2 * b)) / (1 + 3 * t ^ 2) := by field_simp; ring
  rw [e] at h1
  have := (div_nonpos_iff.1 h1)
  rcases this with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · linarith
  · linarith

/-- The ten stationarity relations of `eq:fqe-slice-stationary`. -/
structure Stationary (X Y : M4R) : Prop where
  r1 : Y 0 0 = X 1 1 + X 2 2 + X 3 3
  l1 : Y 0 1 = 3 * X 1 0
  l2 : Y 0 2 = 3 * X 2 0
  l3 : Y 0 3 = 3 * X 3 0
  m1 : Y 1 0 = 3 * X 0 1
  m2 : Y 2 0 = 3 * X 0 2
  m3 : Y 3 0 = 3 * X 0 3
  s12 : Y 1 2 = Y 2 1
  s13 : Y 1 3 = Y 3 1
  s23 : Y 2 3 = Y 3 2

theorem stat_family {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    (P Q : ℝ → ℝ → M4R) (hP : ∀ c σ : ℝ, c ^ 2 + σ ^ 2 = 1 → (P c σ)ᵀ * P c σ = 1)
    (hQ : ∀ c σ : ℝ, c ^ 2 + σ ^ 2 = 1 → (Q c σ)ᵀ * Q c σ = 1) (a b : ℝ)
    (hform : ∀ c σ : ℝ, (1 * (3 * ((P c σ)ᵀ * X * Q c σ) 0 0 +
        ∑ k : Fin 3, ((P c σ)ᵀ * Y * Q c σ) k.succ k.succ) +
        3 * 0 * (((P c σ)ᵀ * Y * Q c σ) 0 0 -
          ∑ k : Fin 3, ((P c σ)ᵀ * X * Q c σ) k.succ k.succ)) - hgt X Y =
        σ * a + (c - 1) * b) : a = 0 := by
  refine lin_zero_rot (b := b) fun c σ hcs => ?_
  have hI := height_ineqG hf hφ (P c σ) (Q c σ) (hP c σ hcs) (hQ c σ hcs) 1 0 (by norm_num)
  have := hform c σ
  linarith

theorem one_orth (c σ : ℝ) (h : c ^ 2 + σ ^ 2 = 1) : (1 : M4R)ᵀ * 1 = 1 := by simp

theorem stat_phase {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y) :
    Y 0 0 = X 1 1 + X 2 2 + X 3 3 := by
  have : Y 0 0 - (X 1 1 + X 2 2 + X 3 3) = 0 := by
    refine lin_zero_phase (b := hgt X Y) fun c s hcs => ?_
    have hI := height_ineqG hf hφ 1 1 (by simp) (by simp) c s hcs
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Fin.sum_univ_three,
      Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      show ((2 : Fin 3).succ : Fin 4) = 3 from rfl] at hI
    simp only [hgt, Fin.sum_univ_three, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
      show ((2 : Fin 3).succ : Fin 4) = 3 from rfl] at hI ⊢
    nlinarith [hI]
  linarith

theorem stat_left {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    (j : Fin 4) (hj : 0 ≠ j)
    (hform : ∀ c σ : ℝ, (1 * (3 * ((rotM 0 j c σ)ᵀ * X * (1 : M4R)) 0 0 +
        ∑ k : Fin 3, ((rotM 0 j c σ)ᵀ * Y * (1 : M4R)) k.succ k.succ) +
        3 * 0 * (((rotM 0 j c σ)ᵀ * Y * (1 : M4R)) 0 0 -
          ∑ k : Fin 3, ((rotM 0 j c σ)ᵀ * X * (1 : M4R)) k.succ k.succ)) - hgt X Y =
        σ * (Y 0 j - 3 * X j 0) + (c - 1) * (3 * X 0 0 + Y j j)) :
    Y 0 j = 3 * X j 0 := by
  have := stat_family hf hφ (fun c σ => rotM 0 j c σ) (fun _ _ => 1)
    (fun c σ hcs => rotM_orth 0 j hj c σ hcs) (fun c σ hcs => by simp) _ _ hform
  linarith

theorem stat_right {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    (j : Fin 4) (hj : 0 ≠ j)
    (hform : ∀ c σ : ℝ, (1 * (3 * ((1 : M4R)ᵀ * X * rotM 0 j c σ) 0 0 +
        ∑ k : Fin 3, ((1 : M4R)ᵀ * Y * rotM 0 j c σ) k.succ k.succ) +
        3 * 0 * (((1 : M4R)ᵀ * Y * rotM 0 j c σ) 0 0 -
          ∑ k : Fin 3, ((1 : M4R)ᵀ * X * rotM 0 j c σ) k.succ k.succ)) - hgt X Y =
        σ * (Y j 0 - 3 * X 0 j) + (c - 1) * (3 * X 0 0 + Y j j)) :
    Y j 0 = 3 * X 0 j := by
  have := stat_family hf hφ (fun _ _ => 1) (fun c σ => rotM 0 j c σ)
    (fun c σ hcs => by simp) (fun c σ hcs => rotM_orth 0 j hj c σ hcs) _ _ hform
  linarith

theorem stat_lower {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R} (hφ : CoordIs φ X Y)
    (j k : Fin 4) (hjk : j ≠ k)
    (hform : ∀ c σ : ℝ, (1 * (3 * ((rotM j k c σ)ᵀ * X * (1 : M4R)) 0 0 +
        ∑ l : Fin 3, ((rotM j k c σ)ᵀ * Y * (1 : M4R)) l.succ l.succ) +
        3 * 0 * (((rotM j k c σ)ᵀ * Y * (1 : M4R)) 0 0 -
          ∑ l : Fin 3, ((rotM j k c σ)ᵀ * X * (1 : M4R)) l.succ l.succ)) - hgt X Y =
        σ * (Y j k - Y k j) + (c - 1) * (Y j j + Y k k)) :
    Y j k = Y k j := by
  have := stat_family hf hφ (fun c σ => rotM j k c σ) (fun _ _ => 1)
    (fun c σ hcs => rotM_orth j k hjk c σ hcs) (fun c σ hcs => by simp) _ _ hform
  linarith

/-- **First-order stationarity** (`eq:fqe-slice-stationary`): the ten linear relations at a frame. -/
theorem stationary_of_frame {φ : Psi} {h : ℝ} (hf : IsFrame φ h) {X Y : M4R}
    (hφ : CoordIs φ X Y) : Stationary X Y := by
  have lf : ∀ j : Fin 4, 0 ≠ j → (∀ c σ : ℝ, (1 * (3 * ((rotM 0 j c σ)ᵀ * X * (1 : M4R)) 0 0 +
        ∑ k : Fin 3, ((rotM 0 j c σ)ᵀ * Y * (1 : M4R)) k.succ k.succ) +
        3 * 0 * (((rotM 0 j c σ)ᵀ * Y * (1 : M4R)) 0 0 -
          ∑ k : Fin 3, ((rotM 0 j c σ)ᵀ * X * (1 : M4R)) k.succ k.succ)) - hgt X Y =
        σ * (Y 0 j - 3 * X j 0) + (c - 1) * (3 * X 0 0 + Y j j)) → Y 0 j = 3 * X j 0 :=
    fun j hj hform => stat_left hf hφ j hj hform
  refine ⟨stat_phase hf hφ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine lf 1 (by decide) fun c σ => ?_
    simp only [Matrix.mul_one]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine lf 2 (by decide) fun c σ => ?_
    simp only [Matrix.mul_one]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine lf 3 (by decide) fun c σ => ?_
    simp only [Matrix.mul_one]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine stat_right hf hφ 1 (by decide) fun c σ => ?_
    simp only [Matrix.transpose_one, Matrix.one_mul]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine stat_right hf hφ 2 (by decide) fun c σ => ?_
    simp only [Matrix.transpose_one, Matrix.one_mul]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine stat_right hf hφ 3 (by decide) fun c σ => ?_
    simp only [Matrix.transpose_one, Matrix.one_mul]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine stat_lower hf hφ 1 2 (by decide) fun c σ => ?_
    simp only [Matrix.mul_one]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine stat_lower hf hφ 1 3 (by decide) fun c σ => ?_
    simp only [Matrix.mul_one]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring
  · refine stat_lower hf hφ 2 3 (by decide) fun c σ => ?_
    simp only [Matrix.mul_one]
    simp [rotM, hgt, Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    ring

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.stationary_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stationary_of_frame

end

end FormalResearch.FourQubitEntropy.GO

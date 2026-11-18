module

public import Mathlib
public import FormalResearch.JB.JBDefs

/-!
# Paper J, Theorem B reduction: gluing of two carriers across a fixed seam (`lem:thb-glue`)

Source: Paper J, `/home/user/scratch/paperJ2/thmB.tex`, Lemma `lem:thb-glue`, equation `eq:thb-T1`.

* `jb_glue` (`τ = +1`) and `jb_glue_rev` (`τ = -1`): rows `Fin R`, any finite column type; the constants of
  `eq:thb-T1` are verbatim.  Both reduce to the abstract `jb_glue_core` (only `‖W‖ ≤ ω_max‖Y‖ + ‖E‖`
  for `W = (ω_n Y_{n+τ,k})` is used) and the weighted-shift bound `norm_wShift_le`
  (`‖S Y‖ ≤ ω_max ‖Y‖`, partial isometry `selMat σ` composed with a diagonal).
* Statement differences from the paper: none in the constants; `h ≥ 0` is explicit; the lemma is stated on
  `Fin R × κ` (the consecutive row set `I` re-indexed) and `τ = -1` is proved with a second partial shift
  instead of `Fin.rev` re-indexing.  Not formalised: nothing from the lemma.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix
open scoped Matrix.Norms.L2Operator

section Shift

variable {ι ι' κ : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] [Fintype κ]

/-- The 0/1 selection matrix of a partial map `σ : ι → Option ι'`. -/
def selMat (σ : ι → Option ι') : Matrix ι ι' ℝ := Matrix.of fun n m => if σ n = some m then 1 else 0

omit [Fintype ι] in
theorem selMat_mul_transpose (σ : ι → Option ι') (hσ : ∀ n n' m, σ n = some m → σ n' = some m → n = n') :
    selMat σ * (selMat σ)ᵀ = diagonal fun n => if (σ n).isSome then (1 : ℝ) else 0 := by
  ext n n'
  simp only [selMat, mul_apply, transpose_apply, of_apply, diagonal_apply]
  by_cases hnn : n = n'
  · subst hnn
    rcases h : σ n with _ | a
    · simp
    · simp
  · simp only [hnn, ite_false]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases h1 : σ n = some m
    · by_cases h2 : σ n' = some m
      · exact absurd (hσ n n' m h1 h2) hnn
      · simp [h2]
    · simp [h1]

theorem norm_selMat_le (σ : ι → Option ι') (hσ : ∀ n n' m, σ n = some m → σ n' = some m → n = n') :
    ‖selMat σ‖ ≤ 1 := by
  have h1 : ‖(selMat σ)ᵀ‖ * ‖(selMat σ)ᵀ‖ ≤ 1 := by
    have := l2_opNorm_conjTranspose_mul_self (selMat σ)ᵀ
    rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose, selMat_mul_transpose σ hσ] at this
    rw [← this]
    exact FormalResearch.MatrixAnalysis.jop_norm_proj_le (fun n => (σ n).isSome = true)
      |>.trans' (le_of_eq (by congr 1))
  have h2 : ‖(selMat σ)ᵀ‖ ≤ 1 := by nlinarith [norm_nonneg (selMat σ)ᵀ]
  have := l2_opNorm_conjTranspose (selMat σ)ᵀ
  rw [conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
  rw [this]; exact h2

/-- The weighted partial shift `(S Y)_{nk} = ω_n Y_{σ n, k}` (and `0` where `σ n = none`). -/
def wShift (ω : ι → ℝ) (σ : ι → Option ι') (Y : Matrix ι' κ ℝ) : Matrix ι κ ℝ :=
  Matrix.of fun n k => match σ n with
    | some m => ω n * Y m k
    | none => 0

omit [Fintype κ] in
theorem wShift_eq (ω : ι → ℝ) (σ : ι → Option ι') (Y : Matrix ι' κ ℝ) :
    wShift ω σ Y = diagonal ω * (selMat σ * Y) := by
  ext n k
  rw [diagonal_mul, mul_apply]
  simp only [wShift, selMat, of_apply]
  rcases h : σ n with _ | a
  · simp
  · simp [Finset.sum_ite_eq]

variable [DecidableEq κ]

/-- **Weighted shift bound**: `‖S Y‖ ≤ ω_max ‖Y‖` (a partial isometry composed with a diagonal). -/
theorem norm_wShift_le (ω : ι → ℝ) (σ : ι → Option ι')
    (hσ : ∀ n n' m, σ n = some m → σ n' = some m → n = n') {ωmax : ℝ} (h0 : 0 ≤ ωmax)
    (hω : ∀ n, |ω n| ≤ ωmax) (Y : Matrix ι' κ ℝ) : ‖wShift ω σ Y‖ ≤ ωmax * ‖Y‖ := by
  rw [wShift_eq]
  calc ‖diagonal ω * (selMat σ * Y)‖ ≤ ‖(diagonal ω : Matrix ι ι ℝ)‖ * ‖selMat σ * Y‖ :=
        l2_opNorm_mul _ _
    _ ≤ ωmax * (1 * ‖Y‖) := by
        refine mul_le_mul (FormalResearch.MatrixAnalysis.jop_norm_diagonal_le ω h0 hω)
          ((l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (norm_selMat_le σ hσ)
            (norm_nonneg _))) (norm_nonneg _) h0
    _ = ωmax * ‖Y‖ := by ring

end Shift

section Core

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The effective coefficient `α = A − h B t₁₁ / t₁₂` of `lem:thb-glue` (entrywise). -/
noncomputable def jbAlpha (A B t11 t12 : Matrix ι κ ℝ) (h : ℝ) : Matrix ι κ ℝ :=
  Matrix.of fun n k => A n k - h * B n k * t11 n k / t12 n k

/-- Abstract form of `lem:thb-glue`: `W` is the matrix `(ω_n Y_{n+τ,k})` (shift plus exterior row);
all that is used about it is `‖W‖ ≤ ω_max ‖Y‖ + ‖E‖`. -/
theorem jb_glue_core (Y Yt F A B t11 t12 W E : Matrix ι κ ℝ) {h K ωmax : ℝ}
    (hT : ∀ n k, W n k = t11 n k * Y n k + t12 n k * Yt n k)
    (hF : F = A ⊙ Y + h • (B ⊙ Yt))
    (hW : ‖W‖ ≤ ωmax * ‖Y‖ + ‖E‖)
    (ht12 : ∀ n k, t12 n k ≠ 0) (hα : ∀ n k, jbAlpha A B t11 t12 h n k ≠ 0)
    (hS1 : IsSchurBdd (Matrix.of fun n k => 1 / jbAlpha A B t11 t12 h n k) K)
    (hS2 : IsSchurBdd (Matrix.of fun n k => B n k / (t12 n k * jbAlpha A B t11 t12 h n k)) K)
    (hS3 : IsSchurBdd (Matrix.of fun n k => 1 / t12 n k) K)
    (hS4 : IsSchurBdd (Matrix.of fun n k => t11 n k / t12 n k) K)
    (hh : 0 ≤ h) (hK : h * K * ωmax < 1) :
    ‖Y‖ ≤ K * (‖F‖ + h * ‖E‖) / (1 - h * K * ωmax) ∧
      ‖Yt‖ ≤ K * ((ωmax + 1) * ‖Y‖ + ‖E‖) := by
  have hK0 : 0 ≤ K := hS1.1
  -- Yt = (1/t12) ⊙ W − (t11/t12) ⊙ Y
  have hYt : Yt = (Matrix.of fun n k => 1 / t12 n k) ⊙ W -
      (Matrix.of fun n k => t11 n k / t12 n k) ⊙ Y := by
    ext n k
    have := ht12 n k
    simp only [Matrix.sub_apply, hadamard_apply, of_apply]
    rw [hT n k]; field_simp; ring
  -- Y = (1/α) ⊙ F − h (B/(t12 α)) ⊙ W
  have hY : Y = (Matrix.of fun n k => 1 / jbAlpha A B t11 t12 h n k) ⊙ F -
      h • ((Matrix.of fun n k => B n k / (t12 n k * jbAlpha A B t11 t12 h n k)) ⊙ W) := by
    ext n k
    have h1 := ht12 n k
    have h2 := hα n k
    have h3 : Yt n k = (W n k - t11 n k * Y n k) / t12 n k := by
      rw [hT n k]; field_simp; ring
    simp only [Matrix.sub_apply, Matrix.smul_apply, hadamard_apply, of_apply, hF, Matrix.add_apply, smul_eq_mul, h3]
    simp only [jbAlpha, of_apply] at h2 ⊢
    have h2' : A n k * t12 n k - h * B n k * t11 n k ≠ 0 := by
      intro hz; apply h2; field_simp; linarith
    field_simp
    ring
  have hden : 0 < 1 - h * K * ωmax := by linarith
  have e1 : ‖Y‖ ≤ K * ‖F‖ + h * (K * ‖W‖) := by
    calc ‖Y‖ ≤ ‖(Matrix.of fun n k => 1 / jbAlpha A B t11 t12 h n k) ⊙ F‖ +
          ‖h • ((Matrix.of fun n k => B n k / (t12 n k * jbAlpha A B t11 t12 h n k)) ⊙ W)‖ := by
          conv_lhs => rw [hY]
          exact norm_sub_le _ _
      _ ≤ K * ‖F‖ + h * (K * ‖W‖) := by
          refine add_le_add (hS1.2 F) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
          exact mul_le_mul_of_nonneg_left (hS2.2 W) hh
  have e2 : K * ‖W‖ ≤ K * (ωmax * ‖Y‖ + ‖E‖) := mul_le_mul_of_nonneg_left hW hK0
  have hmain : ‖Y‖ * (1 - h * K * ωmax) ≤ K * (‖F‖ + h * ‖E‖) := by
    nlinarith [mul_le_mul_of_nonneg_left e2 hh]
  refine ⟨(le_div_iff₀ hden).2 hmain, ?_⟩
  calc ‖Yt‖ ≤ ‖(Matrix.of fun n k => 1 / t12 n k) ⊙ W‖ +
        ‖(Matrix.of fun n k => t11 n k / t12 n k) ⊙ Y‖ := by
        conv_lhs => rw [hYt]
        exact norm_sub_le _ _
    _ ≤ K * ‖W‖ + K * ‖Y‖ := add_le_add (hS3.2 W) (hS4.2 Y)
    _ ≤ K * (ωmax * ‖Y‖ + ‖E‖) + K * ‖Y‖ := by linarith
    _ = K * ((ωmax + 1) * ‖Y‖ + ‖E‖) := by ring

end Core

section Fin

variable {R : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Upward partial shift `n ↦ n + 1` (`τ = +1`). -/
def shiftUp (R : ℕ) : Fin R → Option (Fin R) := fun n => if hn : n.val + 1 < R then some ⟨n.val + 1, hn⟩ else none

/-- Downward partial shift `n ↦ n - 1` (`τ = -1`). -/
def shiftDown (R : ℕ) : Fin R → Option (Fin R) :=
  fun n => if hn : 0 < n.val then some ⟨n.val - 1, by omega⟩ else none

theorem shiftUp_inj (n n' m : Fin R) : shiftUp R n = some m → shiftUp R n' = some m → n = n' := by
  intro h1 h2
  unfold shiftUp at h1 h2
  split_ifs at h1 h2 with a b
  have := congrArg Fin.val (Option.some.inj h1)
  have := congrArg Fin.val (Option.some.inj h2)
  apply Fin.ext; simp at *; omega

theorem shiftDown_inj (n n' m : Fin R) : shiftDown R n = some m → shiftDown R n' = some m → n = n' := by
  intro h1 h2
  unfold shiftDown at h1 h2
  split_ifs at h1 h2 with a b
  have := congrArg Fin.val (Option.some.inj h1)
  have := congrArg Fin.val (Option.some.inj h2)
  apply Fin.ext; simp at *; omega

/-- `‖W‖ ≤ ω_max ‖Y‖ + ‖E‖` for `W = S Y + E` (shared by both directions). -/
theorem norm_shift_add_le (σ : Fin R → Option (Fin R))
    (hσ : ∀ n n' m, σ n = some m → σ n' = some m → n = n') (ω : Fin R → ℝ) {ωmax : ℝ}
    (hω : ∀ n, 0 < ω n ∧ ω n ≤ ωmax) (Y E : Matrix (Fin R) κ ℝ) :
    ‖wShift ω σ Y + E‖ ≤ ωmax * ‖Y‖ + ‖E‖ := by
  refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
  by_cases h0 : 0 ≤ ωmax
  · exact norm_wShift_le ω σ hσ h0 (fun n => by
      rw [abs_of_pos (hω n).1]; exact (hω n).2) Y
  · have hR : IsEmpty (Fin R) := by
      refine ⟨fun n => h0 (((hω n).1).le.trans (hω n).2)⟩
    have e1 : wShift ω σ Y = 0 := Subsingleton.elim _ _
    have e2 : Y = 0 := Subsingleton.elim _ _
    rw [e1, e2]; simp

/-- Row shift with exterior row, `τ = +1`: `Y_{n+1,k}` for `n + 1 < R`, else the given exterior row. -/
def Ysh (yext : κ → ℝ) (Y : Matrix (Fin R) κ ℝ) (n : Fin R) (k : κ) : ℝ :=
  if hn : n.val + 1 < R then Y ⟨n.val + 1, hn⟩ k else yext k

/-- Row shift with exterior row, `τ = -1`: `Y_{n-1,k}` for `n ≥ 1`, else the given exterior row. -/
def YshRev (yext : κ → ℝ) (Y : Matrix (Fin R) κ ℝ) (n : Fin R) (k : κ) : ℝ :=
  if hn : 0 < n.val then Y ⟨n.val - 1, by omega⟩ k else yext k

/-- The exterior-row matrix `E` for `τ = +1`: supported on the last row `R-1`, equal to `ω_{R-1} y_ext`. -/
def extRow (ω : Fin R → ℝ) (yext : κ → ℝ) : Matrix (Fin R) κ ℝ :=
  Matrix.of fun n k => if n.val + 1 = R then ω n * yext k else 0

/-- The exterior-row matrix `E` for `τ = -1`: supported on row `0`, equal to `ω_0 y_ext`. -/
def extRowRev (ω : Fin R → ℝ) (yext : κ → ℝ) : Matrix (Fin R) κ ℝ :=
  Matrix.of fun n k => if n.val = 0 then ω n * yext k else 0

theorem shift_add_ext (ω : Fin R → ℝ) (yext : κ → ℝ) (Y : Matrix (Fin R) κ ℝ) :
    Matrix.of (fun n k => ω n * Ysh yext Y n k) = wShift ω (shiftUp R) Y + extRow ω yext := by
  ext n k
  simp only [Ysh, wShift, shiftUp, extRow, of_apply, Matrix.add_apply]
  by_cases h : n.val + 1 < R
  · simp [h, show ¬ (n.val + 1 = R) by omega]
  · simp [h, show (n.val + 1 = R) by omega]

theorem shiftRev_add_ext (ω : Fin R → ℝ) (yext : κ → ℝ) (Y : Matrix (Fin R) κ ℝ) :
    Matrix.of (fun n k => ω n * YshRev yext Y n k) = wShift ω (shiftDown R) Y + extRowRev ω yext := by
  ext n k
  simp only [YshRev, wShift, shiftDown, extRowRev, of_apply, Matrix.add_apply]
  by_cases h : 0 < n.val
  · simp [h, show ¬ (n.val = 0) by omega]
  · simp [h, show (n.val = 0) by omega]

/-- **Gluing of two carriers across a fixed seam** (Paper J, `lem:thb-glue`, equation `eq:thb-T1`),
direction `τ = +1`.  Rows `Fin R`, arbitrary finite column type; `Y, Ỹ, F` are `R × κ` matrices,
`yext` the given exterior row `n_ext = R`, `E` (`extRow`) the matrix supported on row `R - 1` with entries
`ω_{R-1} yext_k`.  If `ω_n Y_{n+1,k} = t₁₁ Y_{nk} + t₁₂ Ỹ_{nk}` (with `Y_{R,k} = yext_k`),
`F = A ∘ Y + h B ∘ Ỹ`, `t₁₂` and `α = A − h B t₁₁/t₁₂` have no zero entry, the four multipliers
`1/α, B/(t₁₂ α), 1/t₁₂, t₁₁/t₁₂` have Schur bound `K` and `h K ω_max < 1`, then
`‖Y‖ ≤ K(‖F‖ + h‖E‖)/(1 − hKω_max)` and `‖Ỹ‖ ≤ K((ω_max + 1)‖Y‖ + ‖E‖)`.
Constants are the paper's, verbatim.  Differences: `h ≥ 0` is made explicit (the paper's `h` is a
positive step); `Ỹ` is written `Yt`.  Covers the whole lemma for `τ = +1`; the paper's "consecutive set `I`" is
`Fin R` (consecutive blocks are re-indexed).  Direction `τ = -1` is `jb_glue_rev`. -/
theorem jb_glue (Y Yt F A B t11 t12 : Matrix (Fin R) κ ℝ) (ω : Fin R → ℝ) (yext : κ → ℝ)
    {h K ωmax : ℝ}
    (hω : ∀ n, 0 < ω n ∧ ω n ≤ ωmax)
    (hT : ∀ n k, ω n * Ysh yext Y n k = t11 n k * Y n k + t12 n k * Yt n k)
    (hF : F = A ⊙ Y + h • (B ⊙ Yt))
    (ht12 : ∀ n k, t12 n k ≠ 0) (hα : ∀ n k, jbAlpha A B t11 t12 h n k ≠ 0)
    (hS1 : IsSchurBdd (Matrix.of fun n k => 1 / jbAlpha A B t11 t12 h n k) K)
    (hS2 : IsSchurBdd (Matrix.of fun n k => B n k / (t12 n k * jbAlpha A B t11 t12 h n k)) K)
    (hS3 : IsSchurBdd (Matrix.of fun n k => 1 / t12 n k) K)
    (hS4 : IsSchurBdd (Matrix.of fun n k => t11 n k / t12 n k) K)
    (hh : 0 ≤ h) (hK : h * K * ωmax < 1) :
    ‖Y‖ ≤ K * (‖F‖ + h * ‖extRow ω yext‖) / (1 - h * K * ωmax) ∧
      ‖Yt‖ ≤ K * ((ωmax + 1) * ‖Y‖ + ‖extRow ω yext‖) :=
  jb_glue_core Y Yt F A B t11 t12 (Matrix.of fun n k => ω n * Ysh yext Y n k) (extRow ω yext)
    hT hF (by rw [shift_add_ext]; exact norm_shift_add_le _ shiftUp_inj ω hω Y _)
    ht12 hα hS1 hS2 hS3 hS4 hh hK

/-- **Gluing of two carriers across a fixed seam** (Paper J, `lem:thb-glue`), direction `τ = -1`:
`ω_n Y_{n-1,k} = t₁₁ Y_{nk} + t₁₂ Ỹ_{nk}` with the exterior row `yext` above row `0` and `E` (`extRowRev`)
supported on row `0`.  Same conclusion and constants as `jb_glue`.  Proved directly with the downward
shift (the same abstract core `jb_glue_core`), not by `Fin.rev` re-indexing; the two are equivalent by
the row reversal `n ↦ R-1-n`, which is not needed. -/
theorem jb_glue_rev (Y Yt F A B t11 t12 : Matrix (Fin R) κ ℝ) (ω : Fin R → ℝ) (yext : κ → ℝ)
    {h K ωmax : ℝ}
    (hω : ∀ n, 0 < ω n ∧ ω n ≤ ωmax)
    (hT : ∀ n k, ω n * YshRev yext Y n k = t11 n k * Y n k + t12 n k * Yt n k)
    (hF : F = A ⊙ Y + h • (B ⊙ Yt))
    (ht12 : ∀ n k, t12 n k ≠ 0) (hα : ∀ n k, jbAlpha A B t11 t12 h n k ≠ 0)
    (hS1 : IsSchurBdd (Matrix.of fun n k => 1 / jbAlpha A B t11 t12 h n k) K)
    (hS2 : IsSchurBdd (Matrix.of fun n k => B n k / (t12 n k * jbAlpha A B t11 t12 h n k)) K)
    (hS3 : IsSchurBdd (Matrix.of fun n k => 1 / t12 n k) K)
    (hS4 : IsSchurBdd (Matrix.of fun n k => t11 n k / t12 n k) K)
    (hh : 0 ≤ h) (hK : h * K * ωmax < 1) :
    ‖Y‖ ≤ K * (‖F‖ + h * ‖extRowRev ω yext‖) / (1 - h * K * ωmax) ∧
      ‖Yt‖ ≤ K * ((ωmax + 1) * ‖Y‖ + ‖extRowRev ω yext‖) :=
  jb_glue_core Y Yt F A B t11 t12 (Matrix.of fun n k => ω n * YshRev yext Y n k) (extRowRev ω yext)
    hT hF (by rw [shiftRev_add_ext]; exact norm_shift_add_le _ shiftDown_inj ω hω Y _)
    ht12 hα hS1 hS2 hS3 hS4 hh hK

/-- info: 'FormalResearch.JB.jb_glue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_glue

/-- info: 'FormalResearch.JB.jb_glue_rev' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JB.jb_glue_rev

/-- Non-vacuity: the hypotheses of `jb_glue` are satisfiable (one row, one column, `Y = 1`, `Ỹ = 0`,
`t₁₁ = 0`, `t₁₂ = 1`, `A = 1`, `B = 0`, `h = 0`, `ω = 1`, exterior row `0`), and the conclusion holds. -/
example : ‖(Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ))‖ ≤
    1 * (‖(Matrix.of fun (_ : Fin 1) (_ : Fin 1) => (1 : ℝ))‖ + 0 * ‖extRow (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))‖)
      / (1 - 0 * 1 * 1) := by
  have := (jb_glue (R := 1) (κ := Fin 1) (Matrix.of fun _ _ => (1 : ℝ)) 0
    (Matrix.of fun _ _ => (1 : ℝ)) (Matrix.of fun _ _ => (1 : ℝ)) 0 0 (Matrix.of fun _ _ => (1 : ℝ))
    (fun _ => 1) (fun _ => 0) (h := 0) (K := 1) (ωmax := 1)
    (fun _ => ⟨one_pos, le_rfl⟩) (by intro n k; simp [Ysh])
    (by ext n k; simp) (by intro n k; simp)
    (by intro n k; simp [jbAlpha])
    (by simpa [jbAlpha] using isSchurBdd_one (ι := Fin 1) (κ := Fin 1))
    (by simpa [jbAlpha] using (isSchurBdd_const (ι := Fin 1) (κ := Fin 1) 0).mono (by norm_num : |(0:ℝ)| ≤ 1))
    (by simpa using isSchurBdd_one (ι := Fin 1) (κ := Fin 1))
    (by simpa using (isSchurBdd_const (ι := Fin 1) (κ := Fin 1) 0).mono (by norm_num : |(0:ℝ)| ≤ 1))
    le_rfl (by norm_num)).1
  simpa using this

end Fin

end FormalResearch.JB

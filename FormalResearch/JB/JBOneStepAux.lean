module

public import Mathlib
public import FormalResearch.JB.JBDefs
public import FormalResearch.JB.JBGlue
public import FormalResearch.JB.JBOneStepDef
public import FormalResearch.MatrixAnalysis.MaskedFrobenius

/-!
# Paper J, Theorem B reduction: auxiliary lemmas for the one-step criterion

Elementary facts used by the proof of `OneStepReduction` (`thm:thb-onestep`, Steps 1-5):

* `jbL2` calculus (`jbL2_le_mul`, `jbL2_comp_le`);
* operator norm from column norms (`opNorm_le_of_cols`), single entries (`abs_apply_le_norm`),
  Schur bounds on entries (`IsSchurBdd.abs_le`);
* zero-padded submatrices `pad f g M = S_f M S_gᵀ` (`norm_pad_le`: coordinate projections and
  embeddings do not increase the operator norm);
* the scalar inequality `h log(1/h) ≤ 1`.
-/

@[expose] public section

namespace FormalResearch.JB

open Matrix FormalResearch.MatrixAnalysis
open scoped Matrix.Norms.L2Operator

section L2

variable {ι : Type*}

theorem jbL2_nonneg (S : Finset ι) (v : ι → ℝ) : 0 ≤ jbL2 S v := Real.sqrt_nonneg _

theorem jbL2_le_mul (S : Finset ι) (a b : ι → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n ∈ S, |a n| ≤ c * |b n|) : jbL2 S a ≤ c * jbL2 S b := by
  unfold jbL2
  have e : c * √(∑ n ∈ S, b n ^ 2) = √(c ^ 2 * ∑ n ∈ S, b n ^ 2) := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  rw [e]
  apply Real.sqrt_le_sqrt
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have h1 := h n hn
  calc a n ^ 2 = |a n| ^ 2 := (sq_abs _).symm
    _ ≤ (c * |b n|) ^ 2 := by gcongr
    _ = c ^ 2 * b n ^ 2 := by rw [mul_pow, sq_abs]

theorem jbL2_comp_le {ι' : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (f : ι → ι')
    (hf : Function.Injective f) [Fintype ι'] (v : ι' → ℝ) :
    jbL2 S (fun n => v (f n)) ≤ jbL2 Finset.univ v := by
  classical
  unfold jbL2
  apply Real.sqrt_le_sqrt
  calc ∑ n ∈ S, v (f n) ^ 2 = ∑ i ∈ S.image f, v i ^ 2 :=
        (Finset.sum_image (g := f) (f := fun i => v i ^ 2) (fun a _ b _ h => hf h)).symm
    _ ≤ ∑ i, v i ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

/-- `ℓ²` norm of a vector restricted to a subset is at most the full norm. -/
theorem jbL2_le_univ [Fintype ι] (S : Finset ι) (v : ι → ℝ) : jbL2 S v ≤ jbL2 Finset.univ v := by
  unfold jbL2
  apply Real.sqrt_le_sqrt
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)

end L2

section Norms

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Every entry is bounded by the operator norm. -/
theorem abs_apply_le_norm (M : Matrix ι κ ℝ) (i : ι) (j : κ) : |M i j| ≤ ‖M‖ := by
  have h := l2_opNorm_mulVec M (EuclideanSpace.single j (1 : ℝ))
  have h1 : ‖(EuclideanSpace.single j (1 : ℝ))‖ = 1 := by simp
  rw [h1, mul_one] at h
  refine le_trans ?_ h
  have := PiLp.norm_apply_le ((EuclideanSpace.equiv ι ℝ).symm (M *ᵥ (EuclideanSpace.single j (1 : ℝ))))  i
  refine le_trans ?_ this
  simp [Matrix.mulVec, dotProduct]

theorem norm_single_le (n : ι) (k : κ) : ‖(Matrix.single n k (1 : ℝ))‖ ≤ 1 := by
  refine (l2_opNorm_le_sqrt_frobSq _).trans ?_
  have : frobSq (Matrix.single n k (1 : ℝ)) = 1 := by
    unfold frobSq
    rw [Finset.sum_eq_single n]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj; simp [Matrix.single_apply, hj.symm]
      · simp
    · intro i _ hi; simp [Matrix.single_apply, hi.symm]
    · simp
  rw [this]; simp

/-- A Schur bound controls every entry. -/
theorem IsSchurBdd.abs_le {Φ : Matrix ι κ ℝ} {K : ℝ} (h : IsSchurBdd Φ K) (n : ι) (k : κ) :
    |Φ n k| ≤ K := by
  have h1 := h.apply_le (Matrix.single n k (1 : ℝ))
  have h2 := abs_apply_le_norm (Φ ⊙ Matrix.single n k (1 : ℝ)) n k
  have h3 : (Φ ⊙ Matrix.single n k (1 : ℝ)) n k = Φ n k := by simp [Matrix.hadamard_apply]
  rw [h3] at h2
  have h4 := norm_single_le n k
  have := h.nonneg
  nlinarith [norm_nonneg (Matrix.single n k (1 : ℝ))]

end Norms

section Cols

/-- Operator norm from column norms: `‖M‖ ≤ √D · c` when every column has `ℓ²` norm `≤ c`. -/
theorem opNorm_le_of_cols {D : ℕ} (M : Matrix (Fin D) (Fin D) ℝ) {c : ℝ}
    (h : ∀ j, jbL2 Finset.univ (fun i => M i j) ≤ c) : ‖M‖ ≤ √(D : ℝ) * c := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    have : frobSq M = 0 := by simp [frobSq]
    have h0 := l2_opNorm_le_sqrt_frobSq M
    rw [this] at h0
    simpa using h0
  · have hc : 0 ≤ c := (jbL2_nonneg _ _).trans (h ⟨0, hD⟩)
    refine (l2_opNorm_le_sqrt_frobSq M).trans ?_
    have e : √(D : ℝ) * c = √((D : ℝ) * c ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc]
    rw [e]
    apply Real.sqrt_le_sqrt
    unfold frobSq
    rw [Finset.sum_comm]
    calc ∑ j, ∑ i, M i j ^ 2 ≤ ∑ _j : Fin D, c ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact (Real.sqrt_le_iff.mp (h j)).2
      _ = (D : ℝ) * c ^ 2 := by simp

end Cols

section Pad

variable {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] [DecidableEq ι]
  [DecidableEq ι'] [DecidableEq κ] [DecidableEq κ']

/-- Zero-padded re-indexing along partial maps `f : ι → Option ι'`, `g : κ → Option κ'`. -/
def pad (f : ι → Option ι') (g : κ → Option κ') (M : Matrix ι' κ' ℝ) : Matrix ι κ ℝ :=
  Matrix.of fun i k => match f i, g k with
    | some a, some b => M a b
    | _, _ => 0

theorem pad_eq (f : ι → Option ι') (g : κ → Option κ') (M : Matrix ι' κ' ℝ) :
    pad f g M = selMat f * M * (selMat g)ᵀ := by
  ext i k
  simp only [pad, of_apply, Matrix.mul_apply, selMat, transpose_apply]
  rcases hf : f i with _ | a <;> rcases hg : g k with _ | b <;> simp [hf, hg]

/-- Coordinate projections and embeddings do not increase the operator norm. -/
theorem norm_pad_le (f : ι → Option ι') (g : κ → Option κ')
    (hf : ∀ n n' m, f n = some m → f n' = some m → n = n')
    (hg : ∀ n n' m, g n = some m → g n' = some m → n = n') (M : Matrix ι' κ' ℝ) :
    ‖pad f g M‖ ≤ ‖M‖ := by
  rw [pad_eq]
  calc ‖selMat f * M * (selMat g)ᵀ‖ ≤ ‖selMat f * M‖ * ‖(selMat g)ᵀ‖ := l2_opNorm_mul _ _
    _ ≤ (‖selMat f‖ * ‖M‖) * ‖selMat g‖ := by
        gcongr
        · exact l2_opNorm_mul _ _
        · have := l2_opNorm_conjTranspose (selMat g)
          rw [conjTranspose_eq_transpose_of_trivial] at this
          exact this.le
    _ ≤ (1 * ‖M‖) * 1 := by
        gcongr
        · exact norm_selMat_le f hf
        · exact norm_selMat_le g hg
    _ = ‖M‖ := by ring

end Pad

section Scalar

/-- `h log(1/h) ≤ 1` for `h > 0` (indeed `log(1/h) ≤ 1/h - 1`). -/
theorem mul_log_inv_le_one {h : ℝ} (hh : 0 < h) : h * Real.log (1 / h) ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 / h by positivity)
  have e : h * (1 / h - 1) = 1 - h := by field_simp
  nlinarith

end Scalar

end FormalResearch.JB

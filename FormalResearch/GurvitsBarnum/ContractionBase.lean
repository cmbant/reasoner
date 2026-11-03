module

public import Mathlib

/-!
# Gurvits–Barnum: positive maps, vector bounds and the normal-contraction lemma (L1, L2)

Source: L. Gurvits and H. Barnum, *Largest separable balls around the maximally mixed bipartite
quantum state*, Phys. Rev. A 66, 062311 (2002); plan lemmas L1, L2.

* `IsPositiveMap φ`: `φ` sends positive semidefinite matrices to positive semidefinite matrices.
* `Contr.Bdd c A`: the vector form `‖⟨u, A w⟩‖ ≤ c ‖u‖ ‖w‖` of the operator-norm bound `‖A‖ ≤ c`.
* `Contr.bdd_map_of_decomp` (L2 core): a unital positive map sends `Σ zⱼ Pⱼ`
  (`Pⱼ ≥ 0`, `Σ Pⱼ = 1`, `|zⱼ| ≤ 1`) to a contraction.
-/

@[expose] public section


namespace FormalResearch.GurvitsBarnum

open Matrix ComplexOrder
open scoped MatrixOrder

/-- A positive linear map between matrix algebras: it maps PSD matrices to PSD matrices. -/
def IsPositiveMap {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    (φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ) : Prop :=
  ∀ P, P.PosSemidef → (φ P).PosSemidef

namespace Contr

section vec

variable {m : Type*} [Fintype m]

/-- The Euclidean norm of a vector `m → ℂ`. -/
noncomputable def vn (u : m → ℂ) : ℝ := ‖(WithLp.toLp 2 u : EuclideanSpace ℂ m)‖

theorem vn_nonneg (u : m → ℂ) : 0 ≤ vn u := norm_nonneg _

theorem vn_sq (u : m → ℂ) : vn u ^ 2 = (star u ⬝ᵥ u).re := by
  have h := @inner_self_eq_norm_sq_to_K ℂ _ _ _ _ (WithLp.toLp 2 u : EuclideanSpace ℂ m)
  rw [EuclideanSpace.inner_toLp_toLp] at h
  rw [vn, dotProduct_comm]
  have := congrArg Complex.re h
  exact_mod_cast this.symm

theorem norm_dot_le (u v : m → ℂ) : ‖star u ⬝ᵥ v‖ ≤ vn u * vn v := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 u : EuclideanSpace ℂ m) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] at h
  exact h

theorem vn_smul (c : ℂ) (u : m → ℂ) : vn (c • u) = ‖c‖ * vn u := by
  simp [vn, ← norm_smul]

theorem vn_add_le (u v : m → ℂ) : vn (u + v) ≤ vn u + vn v := by
  simpa [vn] using norm_add_le (WithLp.toLp 2 u : EuclideanSpace ℂ m) (WithLp.toLp 2 v)

theorem star_dot_self_eq (v : m → ℂ) : star v ⬝ᵥ v = ((vn v ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [vn_sq]
  · simp only [dotProduct, Complex.im_sum, Complex.ofReal_im]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp [Complex.mul_im]
    ring

/-- The vector form of `‖A‖ ≤ c`: `‖⟨u, A w⟩‖ ≤ c ‖u‖ ‖w‖`. -/
def Bdd (c : ℝ) (A : Matrix m m ℂ) : Prop :=
  ∀ u w : m → ℂ, ‖star u ⬝ᵥ (A *ᵥ w)‖ ≤ c * vn u * vn w

theorem quad_conjTranspose_mul (A : Matrix m m ℂ) (w : m → ℂ) :
    star (A *ᵥ w) ⬝ᵥ (A *ᵥ w) = star w ⬝ᵥ ((Aᴴ * A) *ᵥ w) := by
  rw [star_mulVec, ← mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, dotProduct_mulVec]

theorem vn_mulVec_sq (A : Matrix m m ℂ) (w : m → ℂ) :
    vn (A *ᵥ w) ^ 2 = (star w ⬝ᵥ ((Aᴴ * A) *ᵥ w)).re := by
  rw [vn_sq, quad_conjTranspose_mul]

variable [DecidableEq m]

theorem quad_psd_re (c : ℝ) (A : Matrix m m ℂ) (w : m → ℂ) :
    (star w ⬝ᵥ ((((c ^ 2 : ℝ) • (1 : Matrix m m ℂ)) - Aᴴ * A) *ᵥ w)).re
      = c ^ 2 * vn w ^ 2 - vn (A *ᵥ w) ^ 2 := by
  rw [vn_mulVec_sq, vn_sq, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul]
  simp only [Complex.sub_re, Complex.smul_re, smul_eq_mul]

theorem bdd_of_psd {c : ℝ} (hc : 0 ≤ c) {A : Matrix m m ℂ}
    (h : (((c ^ 2 : ℝ) • (1 : Matrix m m ℂ)) - Aᴴ * A).PosSemidef) : Bdd c A := by
  intro u w
  have h1 : vn (A *ᵥ w) ≤ c * vn w := by
    have := (Complex.nonneg_iff.1 (h.dotProduct_mulVec_nonneg w)).1
    rw [quad_psd_re] at this
    have h2 : vn (A *ᵥ w) ^ 2 ≤ (c * vn w) ^ 2 := by nlinarith
    exact le_of_sq_le_sq h2 (mul_nonneg hc (vn_nonneg _))
  calc ‖star u ⬝ᵥ (A *ᵥ w)‖ ≤ vn u * vn (A *ᵥ w) := norm_dot_le _ _
    _ ≤ vn u * (c * vn w) := mul_le_mul_of_nonneg_left h1 (vn_nonneg _)
    _ = c * vn u * vn w := by ring

theorem psd_of_bdd {c : ℝ} (hc : 0 ≤ c) {A : Matrix m m ℂ} (h : Bdd c A) :
    (((c ^ 2 : ℝ) • (1 : Matrix m m ℂ)) - Aᴴ * A).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun w => ?_⟩
  · simp [IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_mul]
  · have h1 : vn (A *ᵥ w) ≤ c * vn w := by
      have h2 := h (A *ᵥ w) w
      have h3 : ‖star (A *ᵥ w) ⬝ᵥ (A *ᵥ w)‖ = vn (A *ᵥ w) ^ 2 := by
        rw [star_dot_self_eq, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      rw [h3] at h2
      by_cases h0 : vn (A *ᵥ w) = 0
      · rw [h0]; exact mul_nonneg hc (vn_nonneg _)
      · have hp : 0 < vn (A *ᵥ w) := lt_of_le_of_ne (vn_nonneg _) (Ne.symm h0)
        nlinarith
    have hre : (0 : ℝ) ≤ c ^ 2 * vn w ^ 2 - vn (A *ᵥ w) ^ 2 := by nlinarith [vn_nonneg w, vn_nonneg (A *ᵥ w)]
    have him : (star w ⬝ᵥ ((((c ^ 2 : ℝ) • (1 : Matrix m m ℂ)) - Aᴴ * A) *ᵥ w)) =
        ((c ^ 2 * vn w ^ 2 - vn (A *ᵥ w) ^ 2 : ℝ) : ℂ) := by
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul,
        ← quad_conjTranspose_mul, star_dot_self_eq, star_dot_self_eq]
      push_cast
      simp
    rw [him]
    exact_mod_cast hre

omit [DecidableEq m] in
theorem Bdd.half_add {c : ℝ} {A B : Matrix m m ℂ} (hA : Bdd c A) (hB : Bdd c B) :
    Bdd c ((1 / 2 : ℂ) • (A + B)) := by
  intro u w
  rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, smul_eq_mul, norm_mul]
  have := norm_add_le (star u ⬝ᵥ (A *ᵥ w)) (star u ⬝ᵥ (B *ᵥ w))
  have h1 := hA u w
  have h2 := hB u w
  have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  rw [this]
  nlinarith

omit [DecidableEq m] in
theorem Bdd.add {c c' : ℝ} {A B : Matrix m m ℂ} (hA : Bdd c A) (hB : Bdd c' B) :
    Bdd (c + c') (A + B) := by
  intro u w
  rw [add_mulVec, dotProduct_add]
  have := norm_add_le (star u ⬝ᵥ (A *ᵥ w)) (star u ⬝ᵥ (B *ᵥ w))
  have h1 := hA u w
  have h2 := hB u w
  nlinarith

omit [DecidableEq m] in
theorem Bdd.neg {c : ℝ} {A : Matrix m m ℂ} (hA : Bdd c A) : Bdd c (-A) := by
  intro u w
  rw [neg_mulVec, dotProduct_neg, norm_neg]
  exact hA u w

theorem bdd_smul_one {t : ℝ} (ht : 0 ≤ t) : Bdd t ((t : ℂ) • (1 : Matrix m m ℂ)) := by
  intro u w
  rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ht]
  have := norm_dot_le u w
  nlinarith

omit [DecidableEq m] in
theorem Bdd.mono {c c' : ℝ} {A : Matrix m m ℂ} (h : Bdd c A) (hc : c ≤ c') : Bdd c' A := by
  intro u w
  have := h u w
  have h3 : 0 ≤ vn u * vn w := mul_nonneg (vn_nonneg _) (vn_nonneg _)
  nlinarith

omit [DecidableEq m] in
/-- `Bdd` is closed in the constant. -/
theorem bdd_of_forall_pos {c : ℝ} {A : Matrix m m ℂ} (h : ∀ ε : ℝ, 0 < ε → Bdd (c + ε) A) :
    Bdd c A := by
  intro u w
  have hp : 0 ≤ vn u * vn w := mul_nonneg (vn_nonneg _) (vn_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := h (ε / (vn u * vn w + 1)) (by positivity) u w
  have h2 : ε / (vn u * vn w + 1) * (vn u * vn w) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

omit [DecidableEq m] in
theorem bdd_smul {c : ℝ} (r : ℝ) (hr : 0 ≤ r) {A : Matrix m m ℂ} (h : Bdd c A) :
    Bdd (r * c) ((r : ℂ) • A) := by
  intro u w
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hr]
  have := h u w
  nlinarith

theorem exists_eq_conjTranspose_mul_self {Q : Matrix m m ℂ} (hQ : Q.PosSemidef) :
    ∃ R : Matrix m m ℂ, Q = Rᴴ * R := by
  refine ⟨CFC.sqrt Q, ?_⟩
  have hR : (CFC.sqrt Q).PosSemidef := (CFC.sqrt_nonneg Q).posSemidef
  rw [hR.isHermitian.eq]
  exact (CFC.sqrt_mul_sqrt_self Q hQ.nonneg).symm

omit [DecidableEq m] in
theorem norm_dot_mulVec_le {Q R : Matrix m m ℂ} (hQ : Q = Rᴴ * R) (u v : m → ℂ) :
    ‖star u ⬝ᵥ (Q *ᵥ v)‖ ≤ vn (R *ᵥ u) * vn (R *ᵥ v) := by
  have : star u ⬝ᵥ (Q *ᵥ v) = star (R *ᵥ u) ⬝ᵥ (R *ᵥ v) := by
    rw [hQ, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  rw [this]
  exact norm_dot_le _ _

end vec

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]

/-- **L2 core.** A unital positive map sends `Σ zⱼ Pⱼ` (`Pⱼ ≥ 0`, `Σ Pⱼ = 1`, `|zⱼ| ≤ 1`) to a
contraction. -/
theorem bdd_map_of_decomp {ι : Type*} [Fintype ι] (φ : Matrix n n ℂ →ₗ[ℂ] Matrix k k ℂ)
    (hφ : IsPositiveMap φ) (h1 : φ 1 = 1) (P : ι → Matrix n n ℂ) (hP : ∀ j, (P j).PosSemidef)
    (hsum : ∑ j, P j = 1) (z : ι → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    Bdd 1 (φ (∑ j, z j • P j)) := by
  intro u w
  choose R hR using fun j => exists_eq_conjTranspose_mul_self (hφ _ (hP j))
  have hexp : star u ⬝ᵥ (φ (∑ j, z j • P j) *ᵥ w)
      = ∑ j, z j * (star u ⬝ᵥ (φ (P j) *ᵥ w)) := by
    simp [map_sum, map_smul, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec,
      dotProduct_smul]
  have hsq : ∀ v : k → ℂ, ∑ j, vn (R j *ᵥ v) ^ 2 = vn v ^ 2 := by
    intro v
    have hs : ∑ j, φ (P j) = 1 := by rw [← map_sum, hsum, h1]
    calc ∑ j, vn (R j *ᵥ v) ^ 2 = ∑ j, (star v ⬝ᵥ (φ (P j) *ᵥ v)).re := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [vn_mulVec_sq, ← hR j]
      _ = (star v ⬝ᵥ ((∑ j, φ (P j)) *ᵥ v)).re := by
          simp [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
      _ = vn v ^ 2 := by rw [hs, one_mulVec, vn_sq]
  rw [hexp]
  calc ‖∑ j, z j * (star u ⬝ᵥ (φ (P j) *ᵥ w))‖
      ≤ ∑ j, ‖z j * (star u ⬝ᵥ (φ (P j) *ᵥ w))‖ := norm_sum_le _ _
    _ ≤ ∑ j, vn (R j *ᵥ u) * vn (R j *ᵥ w) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        calc ‖z j‖ * ‖star u ⬝ᵥ (φ (P j) *ᵥ w)‖
            ≤ 1 * (vn (R j *ᵥ u) * vn (R j *ᵥ w)) :=
              mul_le_mul (hz j) (norm_dot_mulVec_le (hR j) u w) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ ≤ Real.sqrt (∑ j, vn (R j *ᵥ u) ^ 2) * Real.sqrt (∑ j, vn (R j *ᵥ w) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = 1 * vn u * vn w := by
        rw [hsq, hsq, Real.sqrt_sq (vn_nonneg _), Real.sqrt_sq (vn_nonneg _)]; ring

end Contr
end FormalResearch.GurvitsBarnum

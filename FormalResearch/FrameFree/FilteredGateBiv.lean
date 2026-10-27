import FormalResearch.FrameFree.FilteredGateReal
import FormalResearch.FrameFree.FilteredGateBasic

/-!
# Filtered-gate law: the Fierz expansion and the bivector bound

For a unitary `T` on `ℂ²⊗ℂ²` put `R = rlg T` (realignment) and `q_T(X) = ‖Rᵀ x‖²` for `X ∈ M₂` (`x` its
vectorisation, `qf`).  `fierz`: `q_T(X) = Σ_{μν} h_{μν} tr(X σ_μ X† σ_ν)` with
`h_{μν} = ¼ tr[(σ_μ⊗1) T (σ_ν⊗1) T†]` (`hh`).  For an orthonormal pair `X₁, X₂` the non-local part of
`Σ_{ab} h_{ab}(p₁+p₂)_{ab}` is `-2 Re(u_a conj v_b)` for explicit bilinear bivector coordinates
`u, v` with `‖u‖²+‖v‖² = 2` (`biv_gen`, `biv_norm`); hence (`qf_pair_le`)
`q_T(X₁) + q_T(X₂) ≤ 2 + 2d` whenever the real `3×3` block `H = (h_{ab})` has `‖H‖ ≤ d`.
-/

open scoped Matrix ComplexConjugate
open Finset Complex

namespace FormalResearch.FrameFree.FTG



noncomputable def vvec (X₁ X₂ : M2) : Fin 3 → ℂ := ![
  -(X₁ 0 0) * X₂ 0 1 + X₁ 0 1 * X₂ 0 0 + X₁ 1 0 * X₂ 1 1 - X₁ 1 1 * X₂ 1 0,
  -Complex.I * (X₁ 0 0 * X₂ 0 1 - X₁ 0 1 * X₂ 0 0 + X₁ 1 0 * X₂ 1 1 - X₁ 1 1 * X₂ 1 0),
  X₁ 0 0 * X₂ 1 1 - X₁ 0 1 * X₂ 1 0 + X₁ 1 0 * X₂ 0 1 - X₁ 1 1 * X₂ 0 0]

noncomputable def uvec (X₁ X₂ : M2) : Fin 3 → ℂ := ![
  X₁ 0 0 * X₂ 1 0 - X₁ 0 1 * X₂ 1 1 - X₁ 1 0 * X₂ 0 0 + X₁ 1 1 * X₂ 0 1,
  -Complex.I * (X₁ 0 0 * X₂ 1 0 + X₁ 0 1 * X₂ 1 1 - X₁ 1 0 * X₂ 0 0 - X₁ 1 1 * X₂ 0 1),
  -(X₁ 0 0) * X₂ 1 1 - X₁ 0 1 * X₂ 1 0 + X₁ 1 0 * X₂ 0 1 + X₁ 1 1 * X₂ 0 0]

theorem biv_gen (X₁ X₂ : M2) (a b : Fin 3) :
    (X₂ * X₂ᴴ).trace * (X₁ * sig a.succ * X₁ᴴ * sig b.succ).trace +
      (X₁ * X₁ᴴ).trace * (X₂ * sig a.succ * X₂ᴴ * sig b.succ).trace
      - ((X₁ * sig a.succ * X₂ᴴ * sig b.succ).trace * (X₂ * X₁ᴴ).trace +
          (X₂ * sig a.succ * X₁ᴴ * sig b.succ).trace * (X₁ * X₂ᴴ).trace)
      = -(uvec X₁ X₂ a * conj (vvec X₁ X₂ b) + conj (uvec X₁ X₂ a) * vvec X₁ X₂ b) := by
  fin_cases a <;> fin_cases b <;>
  simp [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, sig, uvec, vvec] <;>
  ring_nf

theorem biv_norm (X₁ X₂ : M2) :
    ∑ a, (uvec X₁ X₂ a * conj (uvec X₁ X₂ a) + vvec X₁ X₂ a * conj (vvec X₁ X₂ a))
      = 2 * ((X₁ * X₁ᴴ).trace * (X₂ * X₂ᴴ).trace - (X₁ * X₂ᴴ).trace * (X₂ * X₁ᴴ).trace) := by
  simp [Fin.sum_univ_three, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply, uvec, vvec]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- bilinear bound -/
theorem bil_bound (H : Fin 3 → Fin 3 → ℝ) (d : ℝ) (hd0 : 0 ≤ d)
    (hH : ∀ x y : V3, sq3 x = 1 → sq3 y = 1 → ∑ i, ∑ j, x i * H i j * y j ≤ d) (x y : V3) :
    2 * (∑ i, ∑ j, x i * H i j * y j) ≤ d * (sq3 x + sq3 y) := by
  by_cases hx : sq3 x = 0
  · have h0 := (sq3_zero_iff x).mp hx
    have : ∑ i, ∑ j, x i * H i j * y j = 0 := by simp [h0]
    rw [this, hx]; nlinarith [sq3_nonneg y]
  by_cases hy : sq3 y = 0
  · have h0 := (sq3_zero_iff y).mp hy
    have : ∑ i, ∑ j, x i * H i j * y j = 0 := by simp [h0]
    rw [this, hy]; nlinarith [sq3_nonneg x]
  have hxp : 0 < sq3 x := lt_of_le_of_ne (sq3_nonneg x) (Ne.symm hx)
  have hyp : 0 < sq3 y := lt_of_le_of_ne (sq3_nonneg y) (Ne.symm hy)
  have h1 := hH (nrm x) (nrm y) (sq3_nrm x hx) (sq3_nrm y hy)
  have hsx := Real.sqrt_pos.mpr hxp
  have hsy := Real.sqrt_pos.mpr hyp
  have e : ∑ i, ∑ j, nrm x i * H i j * nrm y j =
      (∑ i, ∑ j, x i * H i j * y j) / (Real.sqrt (sq3 x) * Real.sqrt (sq3 y)) := by
    simp only [nrm, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    field_simp
  rw [e, div_le_iff₀ (mul_pos hsx hsy)] at h1
  have h2 : 2 * (Real.sqrt (sq3 x) * Real.sqrt (sq3 y)) ≤ sq3 x + sq3 y := by
    nlinarith [sq_nonneg (Real.sqrt (sq3 x) - Real.sqrt (sq3 y)), Real.sq_sqrt hxp.le, Real.sq_sqrt hyp.le]
  nlinarith



/-- realignment -/
def rlg (T : M4) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun ca db => T (ca.2, db.2) (ca.1, db.1)

noncomputable def qf (R : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) (e : Fin 2 × Fin 2 → ℂ) : ℝ :=
  ∑ j, Complex.normSq (∑ i, e i * R i j)

noncomputable def hh (T : M4) (μ ν : Fin 4) : ℂ :=
  (1 / 4 : ℂ) * (kr (sig μ) 1 * T * kr (sig ν) 1 * Tᴴ).trace

/-- The Hermitian tensor `H_{c a' c' a} = Σ_{bd} T_{(a'b),(cd)} conj T_{(ab),(c'd)}`. -/
noncomputable def Hten (T : M4) (c a' c' a : Fin 2) : ℂ :=
  ∑ b, ∑ d, T (a', b) (c, d) * conj (T (a, b) (c', d))

theorem qf_eq (T : M4) (X : M2) :
    ((qf (rlg T) (fun i => X i.1 i.2) : ℝ) : ℂ) =
      ∑ c, ∑ a', ∑ c', ∑ a, Hten T c a' c' a * X c a' * conj (X c' a) := by
  simp only [qf, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  simp only [Hten, rlg, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.of_apply, map_add, map_mul]
  ring

theorem hh_eq (M N : M2) (T : M4) :
    (kr M 1 * T * kr N 1 * Tᴴ).trace =
      ∑ a, ∑ a', ∑ c, ∑ c', M a a' * N c c' * Hten T c a' c' a := by
  simp only [Hten, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.conjTranspose_apply, star_def]
  simp
  ring

theorem fierz_abs (H : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ) (X : M2) :
    ∑ c, ∑ a', ∑ c', ∑ a, H c a' c' a * X c a' * conj (X c' a) =
      ∑ μ, ∑ ν, ((1 / 4 : ℂ) * ∑ a, ∑ a', ∑ c, ∑ c', sig μ a a' * sig ν c c' * H c a' c' a) *
        (X * sig μ * Xᴴ * sig ν).trace := by
  simp [Fin.sum_univ_two, Fin.sum_univ_four, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply, sig]
  ring_nf
  simp only [Complex.I_sq]
  ring


theorem fierz (T : M4) (X : M2) :
    ((qf (rlg T) (fun i => X i.1 i.2) : ℝ) : ℂ) =
      ∑ μ, ∑ ν, hh T μ ν * (X * sig μ * Xᴴ * sig ν).trace := by
  rw [qf_eq, fierz_abs (Hten T) X]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  rw [hh, hh_eq]

section pair

variable (T : M4) (hT : T * Tᴴ = 1)
include hT

theorem hh_00 : hh T 0 0 = 1 := by
  have h0 : sig 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [sig]
  unfold hh
  rw [h0, kr_one, Matrix.one_mul, Matrix.mul_one, hT]
  simp [Matrix.trace_one]

theorem hh_0b (b : Fin 3) : hh T 0 b.succ = 0 := by
  have h0 : sig 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [sig]
  have hT' : Tᴴ * T = 1 := mul_eq_one_comm.mp hT
  unfold hh
  rw [h0, kr_one, Matrix.one_mul]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hT', Matrix.one_mul]
  have : (kr (sig b.succ) 1).trace = 0 := by
    rw [kr_trace]
    fin_cases b <;> simp [sig, Matrix.trace, Fin.sum_univ_two]
  rw [this]; simp

theorem hh_a0 (a : Fin 3) : hh T a.succ 0 = 0 := by
  have h0 : sig 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [sig]
  unfold hh
  rw [h0, kr_one, Matrix.mul_one, Matrix.mul_assoc, hT, Matrix.mul_one]
  have : (kr (sig a.succ) 1).trace = 0 := by
    rw [kr_trace]
    fin_cases a <;> simp [sig, Matrix.trace, Fin.sum_univ_two]
  rw [this]; simp

end pair

/-- The bivector bound: for an orthonormal pair `X₁, X₂`, `Σ H_{ab}(p₁+p₂)_{ab} ≤ 2d`. -/
theorem biv_sum_le (H : Fin 3 → Fin 3 → ℝ) (d : ℝ) (hd0 : 0 ≤ d)
    (hH : ∀ x y : V3, sq3 x = 1 → sq3 y = 1 → ∑ i, ∑ j, x i * H i j * y j ≤ d)
    (X₁ X₂ : M2) (h11 : (X₁ * X₁ᴴ).trace = 1) (h22 : (X₂ * X₂ᴴ).trace = 1)
    (h12 : (X₁ * X₂ᴴ).trace = 0) (h21 : (X₂ * X₁ᴴ).trace = 0) :
    (∑ a, ∑ b, (H a b : ℂ) * ((X₁ * sig a.succ * X₁ᴴ * sig b.succ).trace +
      (X₂ * sig a.succ * X₂ᴴ * sig b.succ).trace)).re ≤ 2 * d := by
  set ur : V3 := fun a => (uvec X₁ X₂ a).re with hur
  set ui : V3 := fun a => (uvec X₁ X₂ a).im with hui
  set vr : V3 := fun a => (vvec X₁ X₂ a).re with hvr
  set vi : V3 := fun a => (vvec X₁ X₂ a).im with hvi
  have hP : ∀ a b, (X₁ * sig a.succ * X₁ᴴ * sig b.succ).trace + (X₂ * sig a.succ * X₂ᴴ * sig b.succ).trace
      = -(uvec X₁ X₂ a * conj (vvec X₁ X₂ b) + conj (uvec X₁ X₂ a) * vvec X₁ X₂ b) := by
    intro a b
    have := biv_gen X₁ X₂ a b
    rw [h11, h22, h12, h21] at this
    simpa using this
  have hre : (∑ a, ∑ b, (H a b : ℂ) * ((X₁ * sig a.succ * X₁ᴴ * sig b.succ).trace +
      (X₂ * sig a.succ * X₂ᴴ * sig b.succ).trace)).re =
      -2 * ((∑ i, ∑ j, ur i * H i j * vr j) + (∑ i, ∑ j, ui i * H i j * vi j)) := by
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
    simp only [hP, Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      hur, hui, hvr, hvi]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hnorm : sq3 ur + sq3 ui + sq3 vr + sq3 vi = 2 := by
    have := congrArg Complex.re (biv_norm X₁ X₂)
    rw [h11, h22, h12, h21] at this
    simp only [Complex.re_sum, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im] at this
    simp only [sq3, hur, hui, hvr, hvi, sq]
    norm_num at this
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [← this]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  have h1 := bil_bound H d hd0 hH ur (fun b => -vr b)
  have h2 := bil_bound H d hd0 hH ui (fun b => -vi b)
  have e1 : ∑ i, ∑ j, ur i * H i j * (-vr j) = -(∑ i, ∑ j, ur i * H i j * vr j) := by
    simp [Finset.sum_neg_distrib]
  have e2 : ∑ i, ∑ j, ui i * H i j * (-vi j) = -(∑ i, ∑ j, ui i * H i j * vi j) := by
    simp [Finset.sum_neg_distrib]
  have s1 : sq3 (fun b => -vr b) = sq3 vr := by simp [sq3]
  have s2 : sq3 (fun b => -vi b) = sq3 vi := by simp [sq3]
  rw [e1, s1] at h1
  rw [e2, s2] at h2
  rw [hre]
  nlinarith

theorem sum_split4 (f : Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ∑ ν, f μ ν = f 0 0 + ∑ b : Fin 3, f 0 b.succ + ∑ a : Fin 3, f a.succ 0 +
      ∑ a : Fin 3, ∑ b : Fin 3, f a.succ b.succ := by
  simp only [Fin.sum_univ_succ (n := 3), Finset.sum_add_distrib]
  ring

/-- **Pair bound.**  If `T` is unitary with Bloch block `H` (`‖H‖ ≤ d`), then for an orthonormal pair
`X₁, X₂`, `q_T(X₁) + q_T(X₂) ≤ 2 + 2d`. -/
theorem qf_pair_le (T : M4) (hT : T * Tᴴ = 1) (H : Fin 3 → Fin 3 → ℝ) (d : ℝ) (hd0 : 0 ≤ d)
    (hH : ∀ x y : V3, sq3 x = 1 → sq3 y = 1 → ∑ i, ∑ j, x i * H i j * y j ≤ d)
    (hhT : ∀ a b : Fin 3, hh T a.succ b.succ = (H a b : ℂ))
    (X₁ X₂ : M2) (h11 : (X₁ * X₁ᴴ).trace = 1) (h22 : (X₂ * X₂ᴴ).trace = 1)
    (h12 : (X₁ * X₂ᴴ).trace = 0) (h21 : (X₂ * X₁ᴴ).trace = 0) :
    qf (rlg T) (fun i => X₁ i.1 i.2) + qf (rlg T) (fun i => X₂ i.1 i.2) ≤ 2 + 2 * d := by
  have h0 : sig 0 = 1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [sig]
  have key : (((qf (rlg T) (fun i => X₁ i.1 i.2) + qf (rlg T) (fun i => X₂ i.1 i.2) : ℝ)) : ℂ) =
      2 + ∑ a, ∑ b, (H a b : ℂ) * ((X₁ * sig a.succ * X₁ᴴ * sig b.succ).trace +
        (X₂ * sig a.succ * X₂ᴴ * sig b.succ).trace) := by
    push_cast
    rw [fierz T X₁, fierz T X₂, ← Finset.sum_add_distrib]
    simp only [← Finset.sum_add_distrib]
    have := sum_split4 (fun μ ν => hh T μ ν * (X₁ * sig μ * X₁ᴴ * sig ν).trace +
      hh T μ ν * (X₂ * sig μ * X₂ᴴ * sig ν).trace)
    rw [this]
    simp only [hh_00 T hT, hh_0b T hT, hh_a0 T hT, hhT, zero_mul, h0, Matrix.mul_one,
      h11, h22]
    simp only [mul_add]
    norm_num
  have hre := congrArg Complex.re key
  rw [Complex.ofReal_re] at hre
  have := biv_sum_le H d hd0 hH X₁ X₂ h11 h22 h12 h21
  rw [hre, Complex.add_re]
  have e2 : (2 : ℂ).re = 2 := by norm_num
  rw [e2]
  linarith

end FormalResearch.FrameFree.FTG

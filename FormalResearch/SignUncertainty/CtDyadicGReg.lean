module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicArea
public import FormalResearch.SignUncertainty.CtDyadicEta
public import FormalResearch.SignUncertainty.HankelBootArc
public import FormalResearch.SignUncertainty.HankelLangerPsi

/-!
# `ct:dyadic` (1) at the top scale: the arc mass and absolute second moment of `G_reg`

`constant_terms_lower.tex`, `ct:dyadic` Part (2), first half: with `A = √R_J`, `G_reg(w) = (1 - w²/A²)² w Ψ̃(-w²) e^{(4/3) i w³}`
(`ctGReg`), the Cauchy-moment argument needs

* the arc mass `Σ = ∫_0^π ‖G_reg(Ae^{iy})‖ A dy ≤ C_Σ/A`, and
* the absolute second moment `∫_{-A}^A t²‖G_reg(t)‖ dt ≤ C_S A`.

Both are derived here from the two inputs of `ct:dyadic` (1) at the single radius `r = R_J`, stated as named predicates
(`CtCovCircle`, `CtHalfMoment`) and bundled as `CtBandData`, together with the Type-(I) envelope `hankelPsi_envelope` (proved):

* `CtCovCircle` is `(ct:cov)` on the circle `|ũ'| = R_J` (`ũ' = |ũ'|e^{i(π-2φ')}`, `Im ũ' ≥ 0`, so `Re √ũ' = |ũ'|^{1/2} sin φ'`),
  on the covered arc `sin φ' ≥ φ₀(R_J) = C₂ R_J^{-3/4} (log c)^{1/2}`:
  `|Ψ̃(ũ')| ≤ L_{♯♯} |e(ũ')| (Re √ũ')^{-1/2} |ũ'|^{-5/4} (sin φ')^{-1}`;
* `CtHalfMoment` is the second inequality of `(ct:half)` at `R_J`: `∫_0^{R_J} v |Ψ̃(-v)| dv ≤ C c^{1/3}`.

Proved here (unconditional): the unfolding `|G_reg(Ae^{iy})| = 4 sin²y · A |Ψ̃| / e` (`ctGReg_norm_arc`), the reflection symmetry
`‖G_reg(-w̄)‖ = ‖G_reg(w)‖` (from Schwarz reflection `hankelBoot_psi_conj`), the covered-arc bound `|G_reg| A ≤ 4L/A` and the
wedge bound `|G_reg| A ≤ 240 A^{3/2} (sin y)^{3/2}`, the integration over the arc (`ctArcMass_le`), the substitution `v = t²`
for the second moment (`ctSecondMoment_le`), and `ctGRegData_of_band`.
-/

@[expose] public section

open Complex MeasureTheory Set Metric intervalIntegral
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.HalfDiscCauchy FormalResearch.ModularBootstrap.FiveTerm FormalResearch.Special

/-! ### 1. Unfolding on the arc, reflection -/

/-- `‖1 - e^{2iy}‖ = 2 |sin y|`. -/
lemma norm_one_sub_exp_two_mul (y : ℝ) : ‖1 - Complex.exp ((2 * y : ℝ) * I)‖ = 2 * |Real.sin y| := by
  have h := Complex.norm_exp_I_mul_ofReal_sub_one (2 * y)
  rw [show (2 * y) / 2 = y by ring, norm_mul] at h
  rw [show Complex.exp (((2 * y : ℝ) : ℂ) * I) = Complex.exp (I * ((2 * y : ℝ) : ℂ)) by rw [mul_comm],
    norm_sub_rev, h]
  simp

/-- The arc point `w = A e^{iy}`: `w² / A² = e^{2iy}`. -/
lemma arc_sq_div {A : ℝ} (hA : 0 < A) (y : ℝ) :
    ((A : ℂ) * Complex.exp (y * I)) ^ 2 / (A : ℂ) ^ 2 = Complex.exp ((2 * y : ℝ) * I) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  rw [mul_pow, ← Complex.exp_nat_mul]
  push_cast
  field_simp

lemma norm_arc {A : ℝ} (hA : 0 < A) (y : ℝ) : ‖(A : ℂ) * Complex.exp (y * I)‖ = A := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA, Complex.norm_exp_ofReal_mul_I, mul_one]

lemma im_arc (A y : ℝ) : ((A : ℂ) * Complex.exp (y * I)).im = A * Real.sin y := by
  rw [Complex.exp_mul_I]
  simp [Complex.mul_im, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- **Unfolding of `G_reg` on the arc** (`ct:dyadic` Part (2)): for `y ∈ [0, π]`,
`‖G_reg(Ae^{iy})‖ = 4 sin²y · A ‖Ψ̃(-w²)‖ ‖exp((4/3) i w³)‖`. -/
lemma ctGReg_norm_arc {A : ℝ} (hA : 0 < A) (c : ℝ) (f : ℝ → ℝ) {y : ℝ} (hy : y ∈ Icc 0 π) :
    ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ =
      (2 * Real.sin y) ^ 2 * A * ‖hankelPsi c f (-(((A : ℂ) * Complex.exp (y * I)) ^ 2))‖ *
        ‖Complex.exp ((4 / 3 : ℂ) * I * ((A : ℂ) * Complex.exp (y * I)) ^ 3)‖ := by
  have hs : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
  unfold ctGReg
  rw [norm_mul, norm_mul, norm_mul, norm_pow, arc_sq_div hA, norm_one_sub_exp_two_mul, norm_arc hA,
    abs_of_nonneg hs]

/-- Reflection `‖G_reg(-w̄)‖ = ‖G_reg(w)‖` (Schwarz reflection of `Ψ̃`), for `|w|² < R_dom(c)`. -/
lemma ctGReg_norm_reflect {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {A : ℝ}
    {w : ℂ} (hw : ‖w‖ ^ 2 < langerRadius c) :
    ‖ctGReg A c f (-(star w))‖ = ‖ctGReg A c f w‖ := by
  have hmem : -(w ^ 2) ∈ ball (0 : ℂ) (langerRadius c) := by
    rw [mem_ball_zero_iff, norm_neg, norm_pow]; exact hw
  have hpsi : hankelPsi c f (-((-(star w)) ^ 2)) = star (hankelPsi c f (-(w ^ 2))) := by
    have h := hankelBoot_psi_conj hc hf hmem
    rw [← h]
    congr 1
    simp [star_pow]
  have hexp : ‖Complex.exp ((4 / 3 : ℂ) * I * (-(star w)) ^ 3)‖ =
      ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := by
    rw [Complex.norm_exp, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im, pow_succ]
    ring
  unfold ctGReg
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hpsi, norm_star, hexp, norm_neg, norm_star]
  congr 3
  rw [norm_pow, norm_pow]
  congr 1
  rw [← norm_star]
  congr 1
  simp [star_pow, star_sub, star_div₀]

/-- The reflected arc point: `A e^{i(π-y)} = -conj(A e^{iy})`. -/
lemma arc_reflect (A y : ℝ) :
    (A : ℂ) * Complex.exp (((π - y : ℝ) : ℂ) * I) = -(star ((A : ℂ) * Complex.exp (y * I))) := by
  have h1 : Complex.exp (((π - y : ℝ) : ℂ) * I) = -Complex.exp (-(y : ℂ) * I) := by
    rw [show (((π - y : ℝ) : ℂ) * I) = (π : ℂ) * I + (-(y : ℂ) * I) by push_cast; ring, Complex.exp_add,
      Complex.exp_pi_mul_I]
    ring
  have h2 : star (Complex.exp ((y : ℂ) * I)) = Complex.exp (-(y : ℂ) * I) := by
    have := Complex.exp_conj ((y : ℂ) * I)
    rw [show (starRingEnd ℂ) ((y : ℂ) * I) = -(y : ℂ) * I by simp [Complex.conj_ofReal]] at this
    exact this.symm
  rw [h1, star_mul', Complex.star_def, Complex.conj_ofReal]
  rw [show (starRingEnd ℂ) (Complex.exp ((y : ℂ) * I)) = Complex.exp (-(y : ℂ) * I) from h2]
  ring

/-! ### 2. The two named inputs of `ct:dyadic` (1) at the top scale -/

/-- **`(ct:cov)` on the circle `|ũ'| = r`** (named input; the part of `ct:dyadic` (1) used at `r = R_J` by Part (2)).  For
`ũ'` with `Im ũ' ≥ 0` (`ũ' = |ũ'|e^{i(π-2φ')}`, so `Re √ũ' = |ũ'|^{1/2} sin φ'`, `sin φ' = Re √ũ'/√|ũ'|`) on the covered arc
`sin φ' ≥ φ₀(r) = C₂ r^{-3/4} (log c)^{1/2}`:
`|Ψ̃(ũ')| ≤ L_{♯♯} e(ũ') (Re √ũ')^{-1/2} |ũ'|^{-5/4} (sin φ')^{-1}`, `e = airyEnv`, `Ψ̃ = hankelPsi c f`.  The positivity of `Re √ũ'`
excludes the degenerate points of the negative axis.  Only the circle of the band `r - 1 ≤ |ũ'| ≤ r + 1` of the paper is used. -/
def CtCovCircle (c : ℝ) (f : ℝ → ℝ) (r Lsh C₂ : ℝ) : Prop :=
  ∀ u : ℂ, 0 ≤ u.im → ‖u‖ = r → 0 < (u ^ (1 / 2 : ℂ)).re →
    C₂ * r ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ (u ^ (1 / 2 : ℂ)).re / Real.sqrt ‖u‖ →
      ‖hankelPsi c f u‖ ≤ Lsh * airyEnv u * (u ^ (1 / 2 : ℂ)).re ^ (-(1 / 2 : ℝ)) * ‖u‖ ^ (-(5 / 4 : ℝ)) *
        ((u ^ (1 / 2 : ℂ)).re / Real.sqrt ‖u‖)⁻¹

/-- **The first moment of `(ct:half)` at `r = R_J`** (named input): `∫_0^{r} v ‖Ψ̃(-v)‖ dv ≤ C c^{1/3}`. -/
def CtHalfMoment (c : ℝ) (f : ℝ → ℝ) (r Chalf : ℝ) : Prop :=
  ∫ v in (0 : ℝ)..r, v * ‖hankelPsi c f (-(v : ℂ))‖ ≤ Chalf * c ^ (1 / 3 : ℝ)

/-! ### 3. Pointwise bounds on the arc -/

lemma rpow_alg_wedge {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    (2 * s) ^ 2 * A * (60 * (A * s) ^ (-(1 / 2 : ℝ))) * A = 240 * A ^ (3 / 2 : ℝ) * s ^ (3 / 2 : ℝ) := by
  have h1 : A ^ (3 / 2 : ℝ) = A ^ (2 : ℝ) * A ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hA]; norm_num
  have h2 : s ^ (3 / 2 : ℝ) = s ^ (2 : ℝ) * s ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_add hs]; norm_num
  rw [h1, h2, Real.mul_rpow hA.le hs.le, Real.rpow_two, Real.rpow_two]
  ring

lemma rpow_alg_cov {A s : ℝ} (hA : 0 < A) (hs : 0 < s) :
    (2 * s) ^ 2 * A * ((A * s) ^ (-(1 / 2 : ℝ)) * (A ^ 2) ^ (-(5 / 4 : ℝ)) * s⁻¹) * A =
      4 * A⁻¹ * s ^ (1 / 2 : ℝ) := by
  have e1 : (A ^ 2) ^ (-(5 / 4 : ℝ)) = A ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num
  have e2 : A ^ (2 : ℝ) * A ^ (-(1 / 2 : ℝ)) * A ^ (-(5 / 2 : ℝ)) = A⁻¹ := by
    rw [← Real.rpow_add hA, ← Real.rpow_add hA, ← Real.rpow_neg_one]; norm_num
  have e3 : s ^ (2 : ℝ) * s ^ (-(1 / 2 : ℝ)) * s ^ (-(1 : ℝ)) = s ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hs, ← Real.rpow_add hs]; norm_num
  rw [Real.rpow_two] at e2 e3
  rw [Real.rpow_neg_one] at e3
  rw [e1, Real.mul_rpow hA.le hs.le, ← e3, ← e2]
  ring

/-- Data of the arc point `w` in the open upper half-plane: `u = -w²` is off the cut, `Re √u = Im w`, `e(u) = ‖exp((4/3) i w³)‖⁻¹`. -/
lemma arc_data {w : ℂ} (hw : 0 < w.im) :
    ¬ ((-(w ^ 2)).im = 0 ∧ (-(w ^ 2)).re ≤ 0) := by
  rintro ⟨h1, h2⟩
  simp only [Complex.neg_im, Complex.neg_re, pow_two, Complex.mul_im, Complex.mul_re] at h1 h2
  have hre : w.re = 0 := by
    have : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  rw [hre] at h2
  nlinarith

/-- `‖Ψ̃(u)‖ ‖exp((4/3) i w³)‖ ≤ 60 (Im w)^{-1/2}` for `u = -w²`, from the Type-(I) envelope `hankelPsi_envelope`. -/
lemma ctPsi_envelope_arc {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1) {w : ℂ} (hw : 0 < w.im) (hwR : ‖w‖ ^ 2 ≤ langerRadius c) :
    ‖hankelPsi c f (-(w ^ 2))‖ * ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ ≤ 60 * w.im ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨hre, henv⟩ := lowerGood_airyEnv_neg_sq_of_im_pos hw
  have hu : ‖-(w ^ 2)‖ ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by
    rw [← langerRadius_eq, norm_neg, norm_pow]; exact hwR
  have h := hankelPsi_envelope hc hf hε hM hu (arc_data hw)
  rw [hre] at h
  have hE : ‖Complex.exp (-(4 / 3 : ℂ) * (-(w ^ 2)) ^ (3 / 2 : ℂ))‖ = airyEnv (-(w ^ 2)) := by
    rw [Complex.norm_exp, airyEnv]
    congr 1
    simp
  rw [hE, henv] at h
  have hX : 0 < ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  calc _ ≤ 60 * (‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖)⁻¹ * w.im ^ (-(1 / 2 : ℝ)) *
        ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := by gcongr
    _ = _ := by field_simp

/-- **Wedge bound** (Type-(I)): for `y ∈ [0, π]`, `‖G_reg(Ae^{iy})‖ A ≤ 240 A^{3/2} (sin y)^{3/2}`. -/
lemma ctGReg_arc_wedge {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1) {A : ℝ} (hA : 0 < A) (hAR : A ^ 2 ≤ langerRadius c) {y : ℝ} (hy : y ∈ Icc 0 π) :
    ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ * A ≤ 240 * A ^ (3 / 2 : ℝ) * Real.sin y ^ (3 / 2 : ℝ) := by
  have hs0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
  rw [ctGReg_norm_arc hA c f hy]
  rcases hs0.eq_or_lt with hs | hs
  · rw [← hs]; simp
  · have hwim : 0 < ((A : ℂ) * Complex.exp (y * I)).im := by rw [im_arc]; positivity
    have h := ctPsi_envelope_arc hc hf hε hM hwim (by rw [norm_arc hA]; exact hAR)
    rw [im_arc] at h
    have hk : 0 ≤ (2 * Real.sin y) ^ 2 * A * A := by positivity
    calc _ = ((2 * Real.sin y) ^ 2 * A * A) * (‖hankelPsi c f (-(((A : ℂ) * Complex.exp (y * I)) ^ 2))‖ *
          ‖Complex.exp ((4 / 3 : ℂ) * I * ((A : ℂ) * Complex.exp (y * I)) ^ 3)‖) := by ring
      _ ≤ ((2 * Real.sin y) ^ 2 * A * A) * (60 * (A * Real.sin y) ^ (-(1 / 2 : ℝ))) := by gcongr
      _ = _ := by rw [mul_assoc ((2 * Real.sin y) ^ 2 * A) A, mul_comm A, ← mul_assoc]; exact rpow_alg_wedge hA hs

/-- **Covered-arc bound** on `y ∈ [π/2, π)`, from `CtCovCircle`: `‖G_reg(Ae^{iy})‖ A ≤ 4 L/A`. -/
lemma ctGReg_arc_cov_half {c : ℝ} {f : ℝ → ℝ} {A Lsh C₂ : ℝ} (hA : 0 < A) (hL : 0 ≤ Lsh)
    (hcov : CtCovCircle c f (A ^ 2) Lsh C₂) {y : ℝ} (hy : y ∈ Icc (π / 2) π)
    (hthr : C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ Real.sin y) (hs : 0 < Real.sin y) :
    ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ * A ≤ 4 * Lsh / A := by
  have hy' : y ∈ Icc 0 π := ⟨by linarith [hy.1, Real.pi_pos], hy.2⟩
  set w : ℂ := (A : ℂ) * Complex.exp (y * I) with hw
  have hwim : 0 < w.im := by rw [hw, im_arc]; positivity
  obtain ⟨hre, henv⟩ := lowerGood_airyEnv_neg_sq_of_im_pos hwim
  have him : w.im = A * Real.sin y := im_arc A y
  have hnorm : ‖-(w ^ 2)‖ = A ^ 2 := by rw [norm_neg, norm_pow, hw, norm_arc hA]
  have hcos : Real.cos y ≤ 0 := Real.cos_nonpos_of_pi_div_two_le_of_le hy.1 (by linarith [hy.2, Real.pi_pos])
  have hure : 0 ≤ (-(w ^ 2)).im := by
    have : w.re = A * Real.cos y := by
      rw [hw, Complex.exp_mul_I]; simp [Complex.mul_re, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.neg_im, pow_two, Complex.mul_im]
    rw [this, him]; nlinarith [mul_nonneg hA.le (neg_nonneg.2 hcos), mul_pos hA hs]
  have hsq : Real.sqrt ‖-(w ^ 2)‖ = A := by rw [hnorm, Real.sqrt_sq hA.le]
  have hratio : ((-(w ^ 2)) ^ (1 / 2 : ℂ)).re / Real.sqrt ‖-(w ^ 2)‖ = Real.sin y := by
    rw [hre, him, hsq]; field_simp
  have hpos : 0 < ((-(w ^ 2)) ^ (1 / 2 : ℂ)).re := by rw [hre, him]; positivity
  have h := hcov (-(w ^ 2)) hure hnorm hpos (by rw [hratio]; exact hthr)
  rw [hratio, hre, him, hnorm, henv] at h
  rw [ctGReg_norm_arc hA c f hy']
  have hX : 0 < ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hk : 0 ≤ (2 * Real.sin y) ^ 2 * A * A := by positivity
  have hs1 : Real.sin y ^ (1 / 2 : ℝ) ≤ 1 := Real.rpow_le_one hs.le (Real.sin_le_one y) (by norm_num)
  calc _ = ((2 * Real.sin y) ^ 2 * A * A) * (‖hankelPsi c f (-(w ^ 2))‖ *
          ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖) := by ring
    _ ≤ ((2 * Real.sin y) ^ 2 * A * A) * ((Lsh * (‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖)⁻¹ *
          (A * Real.sin y) ^ (-(1 / 2 : ℝ)) * (A ^ 2) ^ (-(5 / 4 : ℝ)) * (Real.sin y)⁻¹) *
          ‖Complex.exp ((4 / 3 : ℂ) * I * w ^ 3)‖) := by gcongr
    _ = Lsh * ((2 * Real.sin y) ^ 2 * A * ((A * Real.sin y) ^ (-(1 / 2 : ℝ)) * (A ^ 2) ^ (-(5 / 4 : ℝ)) *
          (Real.sin y)⁻¹) * A) := by field_simp
    _ = Lsh * (4 * A⁻¹ * Real.sin y ^ (1 / 2 : ℝ)) := by rw [rpow_alg_cov hA hs]
    _ ≤ Lsh * (4 * A⁻¹ * 1) := by gcongr
    _ = 4 * Lsh / A := by ring

/-- `‖G_reg(Ae^{iy})‖ = 0` at `sin y = 0`. -/
lemma ctGReg_arc_zero {A : ℝ} (hA : 0 < A) (c : ℝ) (f : ℝ → ℝ) {y : ℝ} (hy : y ∈ Icc 0 π) (hs : Real.sin y = 0) :
    ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ = 0 := by
  rw [ctGReg_norm_arc hA c f hy, hs]; simp

/-- **Covered-arc bound** on all of `[0, π]` (reflection `y ↦ π - y`): if `φ₀ ≤ sin y`, `‖G_reg(Ae^{iy})‖ A ≤ 4L/A`.
Needs `A² < R_dom(c)` for the Schwarz reflection. -/
lemma ctGReg_arc_cov {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {A Lsh C₂ : ℝ} (hA : 0 < A)
    (hAR : A ^ 2 < langerRadius c) (hL : 0 ≤ Lsh) (hcov : CtCovCircle c f (A ^ 2) Lsh C₂) {y : ℝ}
    (hy : y ∈ Icc 0 π)
    (hthr : C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) ≤ Real.sin y) :
    ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ * A ≤ 4 * Lsh / A := by
  have hs0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
  rcases hs0.eq_or_lt with hs | hs
  · rw [ctGReg_arc_zero hA c f hy hs.symm, zero_mul]; positivity
  · rcases le_total (π / 2) y with hh | hh
    · exact ctGReg_arc_cov_half hA hL hcov ⟨hh, hy.2⟩ hthr hs
    · have hy2 : π - y ∈ Icc (π / 2) π := ⟨by linarith, by linarith [hy.1]⟩
      have hs2 : Real.sin (π - y) = Real.sin y := Real.sin_pi_sub y
      have := ctGReg_arc_cov_half hA hL hcov hy2 (by rw [hs2]; exact hthr) (by rw [hs2]; exact hs)
      rw [arc_reflect, ctGReg_norm_reflect hc hf (by rw [norm_arc hA]; exact hAR)] at this
      exact this

/-- **Pointwise bound on the whole arc**: `‖G_reg(Ae^{iy})‖ A ≤ 4L/A + 240 A^{3/2} φ₀^{3/2}`. -/
lemma ctGReg_arc_le {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1) {A Lsh C₂ : ℝ} (hA : 0 < A) (hAR : A ^ 2 < langerRadius c) (hL : 0 ≤ Lsh)
    (hC : 0 ≤ C₂) (hcov : CtCovCircle c f (A ^ 2) Lsh C₂) {y : ℝ} (hy : y ∈ Icc 0 π) :
    ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ * A ≤
      4 * Lsh / A + 240 * A ^ (3 / 2 : ℝ) *
        (C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)) ^ (3 / 2 : ℝ) := by
  have hc0 : 0 < c := by linarith
  set φ₀ : ℝ := C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) with hφ
  have hφ0 : 0 ≤ φ₀ := by positivity
  have hs0 : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2
  have hp : 0 ≤ 240 * A ^ (3 / 2 : ℝ) * φ₀ ^ (3 / 2 : ℝ) := by positivity
  rcases le_or_gt φ₀ (Real.sin y) with h | h
  · have := ctGReg_arc_cov hc0 hf hA hAR hL hcov hy h
    linarith
  · have := ctGReg_arc_wedge hc hf hε hM hA hAR.le hy
    have h2 : Real.sin y ^ (3 / 2 : ℝ) ≤ φ₀ ^ (3 / 2 : ℝ) := Real.rpow_le_rpow hs0 h.le (by norm_num)
    have h3 : 240 * A ^ (3 / 2 : ℝ) * Real.sin y ^ (3 / 2 : ℝ) ≤ 240 * A ^ (3 / 2 : ℝ) * φ₀ ^ (3 / 2 : ℝ) := by gcongr
    have : 0 ≤ 4 * Lsh / A := by positivity
    linarith

lemma integral_le_const_mul {F : ℝ → ℝ} (hF : Continuous F) {a b K : ℝ} (hab : a ≤ b)
    (h : ∀ y ∈ Icc a b, F y ≤ K) : ∫ y in a..b, F y ≤ (b - a) * K := by
  have := intervalIntegral.integral_mono_on hab (hF.intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume) (c := K)) h
  simpa [mul_comm] using this

/-- **The arc mass of `G_reg`** (`Σ = ∫_0^π ‖G_reg(Ae^{iy})‖ A dy`) from the covered-arc bound and the Type-(I) wedge bound:
`Σ ≤ 8πL/A + 240π A^{3/2} φ₀^{5/2}`, `φ₀ = C₂ A^{-3/2} (log c)^{1/2}`. -/
lemma ctArcMass_le {c ε : ℝ} (hc : 2 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (hε : ε = 1 ∨ ε = -1)
    (hM : hankelMass c f = 1) {A Lsh C₂ : ℝ} (hA : 0 < A) (hAR : A ^ 2 < langerRadius c) (hL : 0 ≤ Lsh)
    (hC : 0 ≤ C₂) (hcov : CtCovCircle c f (A ^ 2) Lsh C₂) :
    hdArcMass A (ctGReg A c f) ≤ 8 * π * Lsh / A + 240 * π * A ^ (3 / 2 : ℝ) *
      ((C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)) *
        (C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c)) ^ (3 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  set φ₀ : ℝ := C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) with hφ
  have hφ0 : 0 ≤ φ₀ := by positivity
  have hGan := ctGReg_analytic hc0 hf hA hAR.le
  have hGc : ContinuousOn (ctGReg A c f) (closedBall (0 : ℂ) A) := hGan.continuousOn
  set F : ℝ → ℝ := fun y => ‖ctGReg A c f ((A : ℂ) * Complex.exp (y * I))‖ * A with hFdef
  have hcont : Continuous F := by
    have h1 : Continuous (fun y : ℝ => (A : ℂ) * Complex.exp (y * I)) := by fun_prop
    have h2 := hGc.comp_continuous h1 (fun y => by rw [mem_closedBall_zero_iff, norm_arc hA])
    exact h2.norm.mul continuous_const
  have hmass : hdArcMass A (ctGReg A c f) = ∫ y in (0 : ℝ)..π, F y := rfl
  rw [hmass]
  set B : ℝ := 4 * Lsh / A + 240 * A ^ (3 / 2 : ℝ) * φ₀ ^ (3 / 2 : ℝ) with hB
  have hFB : ∀ y ∈ Icc 0 π, F y ≤ B := fun y hy => ctGReg_arc_le hc hf hε hM hA hAR hL hC hcov hy
  have hLA : 0 ≤ 4 * Lsh / A := by positivity
  have hP : 0 ≤ 240 * A ^ (3 / 2 : ℝ) * φ₀ ^ (3 / 2 : ℝ) := by positivity
  have hpi := Real.pi_pos
  rcases le_or_gt φ₀ 1 with h1 | h1
  · -- three pieces
    set a : ℝ := π / 2 * φ₀ with ha
    have ha0 : 0 ≤ a := by positivity
    have ha2 : a ≤ π / 2 := by rw [ha]; nlinarith
    have hmid : ∀ y ∈ Icc a (π - a), F y ≤ 4 * Lsh / A := by
      intro y hy
      refine ctGReg_arc_cov (by linarith) hf hA hAR hL hcov ⟨by linarith [hy.1], by linarith [hy.2]⟩ ?_
      rcases le_total y (π / 2) with hh | hh
      · have := Real.mul_le_sin (by linarith [hy.1]) hh
        have h' : φ₀ ≤ 2 / π * y := by
          rw [ha] at hy; have := hy.1; field_simp at this ⊢; linarith
        exact h'.trans this
      · have := Real.mul_le_sin (x := π - y) (by linarith [hy.2]) (by linarith)
        rw [Real.sin_pi_sub] at this
        have h' : φ₀ ≤ 2 / π * (π - y) := by
          have := hy.2; field_simp; rw [ha] at this; nlinarith
        exact h'.trans this
    have i1 : ∫ y in (0 : ℝ)..a, F y ≤ (a - 0) * B :=
      integral_le_const_mul hcont ha0 fun y hy => hFB y ⟨hy.1, by linarith [hy.2]⟩
    have i2 : ∫ y in a..(π - a), F y ≤ (π - a - a) * (4 * Lsh / A) :=
      integral_le_const_mul hcont (by linarith) hmid
    have i3 : ∫ y in (π - a)..π, F y ≤ (π - (π - a)) * B :=
      integral_le_const_mul hcont (by linarith) fun y hy => hFB y ⟨by linarith [hy.1], hy.2⟩
    have hsplit : ∫ y in (0 : ℝ)..π, F y =
        (∫ y in (0 : ℝ)..a, F y) + (∫ y in a..(π - a), F y) + ∫ y in (π - a)..π, F y := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 (π - a))
        (hcont.intervalIntegrable (π - a) π), ← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 a) (hcont.intervalIntegrable a (π - a))]
    have e1 : (a - 0) * B + (π - a - a) * (4 * Lsh / A) + (π - (π - a)) * B =
        π * (4 * Lsh / A) + π * φ₀ * (240 * A ^ (3 / 2 : ℝ) * φ₀ ^ (3 / 2 : ℝ)) := by rw [hB, ha]; ring
    have e2 : 8 * π * Lsh / A + 240 * π * A ^ (3 / 2 : ℝ) * (φ₀ * φ₀ ^ (3 / 2 : ℝ)) =
        2 * (π * (4 * Lsh / A)) + π * φ₀ * (240 * A ^ (3 / 2 : ℝ) * φ₀ ^ (3 / 2 : ℝ)) := by ring
    have h0 : 0 ≤ π * (4 * Lsh / A) := by positivity
    rw [hsplit]
    linarith
  · -- all wedge
    have hwed : ∀ y ∈ Icc 0 π, F y ≤ 240 * A ^ (3 / 2 : ℝ) := by
      intro y hy
      have h := ctGReg_arc_wedge hc hf hε hM hA hAR.le hy
      have hs1 : Real.sin y ^ (3 / 2 : ℝ) ≤ 1 :=
        Real.rpow_le_one (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2) (Real.sin_le_one y) (by norm_num)
      calc F y ≤ _ := h
        _ ≤ 240 * A ^ (3 / 2 : ℝ) * 1 := by gcongr
        _ = _ := by ring
    have := integral_le_const_mul hcont Real.pi_pos.le hwed
    have hge : 1 ≤ φ₀ * φ₀ ^ (3 / 2 : ℝ) := by
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ φ₀ * φ₀ ^ (3 / 2 : ℝ) := by
          gcongr
          exact Real.one_le_rpow h1.le (by norm_num)
    have hA32 : 0 ≤ A ^ (3 / 2 : ℝ) := by positivity
    have hL8 : 0 ≤ 8 * π * Lsh / A := by positivity
    calc _ ≤ (π - 0) * (240 * A ^ (3 / 2 : ℝ)) := this
      _ = 240 * π * A ^ (3 / 2 : ℝ) * 1 := by ring
      _ ≤ 240 * π * A ^ (3 / 2 : ℝ) * (φ₀ * φ₀ ^ (3 / 2 : ℝ)) := by gcongr
      _ ≤ _ := by linarith

/-! ### 4. The absolute second moment, `v = t²` -/

/-- On the diameter, `‖G_reg(t)‖ = (1 - t²/A²)² |t| ‖Ψ̃(-t²)‖`. -/
lemma ctGReg_norm_real (A c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    ‖ctGReg A c f (t : ℂ)‖ = (1 - t ^ 2 / A ^ 2) ^ 2 * |t| * ‖hankelPsi c f (-((t ^ 2 : ℝ) : ℂ))‖ := by
  unfold ctGReg
  have h1 : (1 - (t : ℂ) ^ 2 / (A : ℂ) ^ 2) = ((1 - t ^ 2 / A ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : ‖Complex.exp ((4 / 3 : ℂ) * I * (t : ℂ) ^ 3)‖ = 1 := by
    rw [Complex.norm_exp]; simp [pow_succ, Complex.mul_re, Complex.mul_im]
  rw [norm_mul, norm_mul, norm_mul, h2, mul_one, h1, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  push_cast
  ring_nf

/-- **Second moment by `v = t²`**: `∫_{-A}^A t² ‖G_reg(t)‖ dt ≤ ∫_0^{A²} v ‖Ψ̃(-v)‖ dv`
(equality with the weight `(1 - v/A²)²` inserted, as in the paper). -/
lemma ctSecondMoment_le {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) {A : ℝ} (hA : 0 < A)
    (hAR : A ^ 2 ≤ langerRadius c) :
    ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖ctGReg A c f (t : ℂ)‖ ≤ ∫ v in (0 : ℝ)..(A ^ 2), v * ‖hankelPsi c f (-(v : ℂ))‖ := by
  set g : ℝ → ℝ := fun v => v * ‖hankelPsi c f (-(v : ℂ))‖ with hg
  have hAn := analyticOnNhd_hankelPsi hc hf
  have hgc : ContinuousOn g (Icc 0 (A ^ 2)) := by
    refine continuousOn_id.mul (ContinuousOn.norm ?_)
    refine (hAn.continuousOn).comp (by fun_prop : Continuous fun v : ℝ => -(v : ℂ)).continuousOn ?_
    intro v hv
    rw [mem_closedBall_zero_iff, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv.1,
      ← langerRadius_eq]
    exact hv.2.trans hAR
  set H : ℝ → ℝ := fun t => |t| * g (t ^ 2) with hH
  have hHc : ContinuousOn H (Icc (-A) A) := by
    refine continuous_abs.continuousOn.mul (hgc.comp (by fun_prop : Continuous fun t : ℝ => t ^ 2).continuousOn ?_)
    intro t ht
    refine ⟨sq_nonneg t, ?_⟩
    have : |t| ≤ A := abs_le.2 ⟨ht.1, ht.2⟩
    nlinarith [abs_nonneg t, sq_abs t]
  -- pointwise bound
  have hpt : ∀ t ∈ Icc (-A) A, t ^ 2 * ‖ctGReg A c f (t : ℂ)‖ ≤ H t := by
    intro t ht
    have htA : |t| ≤ A := abs_le.2 ⟨ht.1, ht.2⟩
    have hsq : t ^ 2 ≤ A ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have hfac : (1 - t ^ 2 / A ^ 2) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ 1 - t ^ 2 / A ^ 2 := by rw [sub_nonneg, div_le_one (by positivity)]; exact hsq
      have h1 : 1 - t ^ 2 / A ^ 2 ≤ 1 := by have : 0 ≤ t ^ 2 / A ^ 2 := by positivity
                                            linarith
      nlinarith
    rw [ctGReg_norm_real]
    simp only [hH, hg]
    have hn : 0 ≤ t ^ 2 * (|t| * ‖hankelPsi c f (-((t ^ 2 : ℝ) : ℂ))‖) := by positivity
    calc t ^ 2 * ((1 - t ^ 2 / A ^ 2) ^ 2 * |t| * ‖hankelPsi c f (-((t ^ 2 : ℝ) : ℂ))‖)
        = (1 - t ^ 2 / A ^ 2) ^ 2 * (t ^ 2 * (|t| * ‖hankelPsi c f (-((t ^ 2 : ℝ) : ℂ))‖)) := by ring
      _ ≤ 1 * (t ^ 2 * (|t| * ‖hankelPsi c f (-((t ^ 2 : ℝ) : ℂ))‖)) := by gcongr
      _ = _ := by ring
  -- continuity of the left integrand on [-A, A]
  have hGan := ctGReg_analytic hc hf hA hAR
  have hLc : ContinuousOn (fun t : ℝ => t ^ 2 * ‖ctGReg A c f (t : ℂ)‖) (Icc (-A) A) := by
    refine (continuous_pow 2).continuousOn.mul (ContinuousOn.norm ?_)
    refine hGan.continuousOn.comp Complex.continuous_ofReal.continuousOn ?_
    intro t ht
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨ht.1, ht.2⟩
  have hAA : -A ≤ A := by linarith
  have step1 : ∫ t in (-A)..A, t ^ 2 * ‖ctGReg A c f (t : ℂ)‖ ≤ ∫ t in (-A)..A, H t :=
    intervalIntegral.integral_mono_on hAA ((hLc.intervalIntegrable_of_Icc hAA))
      (hHc.intervalIntegrable_of_Icc hAA) hpt
  -- evenness
  have hHeven : ∀ t, H (-t) = H t := by intro t; simp [hH]
  have step2 : ∫ t in (-A)..A, H t = 2 * ∫ t in (0 : ℝ)..A, H t := by
    have hint0 : IntervalIntegrable H volume 0 A :=
      (hHc.mono (fun t ht => ⟨by linarith [ht.1], by simpa using ht.2⟩ : Icc 0 A ⊆ Icc (-A) A)).intervalIntegrable_of_Icc hA.le
    have hintn : IntervalIntegrable H volume (-A) 0 :=
      (hHc.mono (fun t ht => ⟨ht.1, by linarith [ht.2]⟩ : Icc (-A) 0 ⊆ Icc (-A) A)).intervalIntegrable_of_Icc (by linarith)
    rw [← intervalIntegral.integral_add_adjacent_intervals hintn hint0]
    have : ∫ t in (-A)..0, H t = ∫ t in (0 : ℝ)..A, H t := by
      have h := intervalIntegral.integral_comp_neg (a := 0) (b := A) H
      simp only [hHeven, neg_zero] at h
      exact h.symm
    rw [this]; ring
  -- change of variables v = t²
  have step3 : 2 * ∫ t in (0 : ℝ)..A, H t = ∫ v in (0 : ℝ)..(A ^ 2), g v := by
    have hcv := intervalIntegral.integral_comp_mul_deriv'' (a := 0) (b := A) (f := fun t : ℝ => t ^ 2)
      (f' := fun t => 2 * t) (g := g) (continuous_pow 2).continuousOn
      (fun x _ => by
        have := (hasDerivAt_pow 2 x).hasDerivWithinAt (s := Ioi x)
        simpa using this)
      (by fun_prop) (hgc.mono (by
        rintro _ ⟨t, ht, rfl⟩
        rw [uIcc_of_le hA.le] at ht
        exact ⟨sq_nonneg t, by nlinarith [ht.1, ht.2]⟩))
    simp only [Function.comp_apply] at hcv
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at hcv
    rw [← hcv, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hA.le] at ht
    simp only [hH, abs_of_nonneg ht.1]
    ring
  rw [← step3, ← step2]
  exact step1

/-! ### 5. The bundled input and `CtGRegData` -/

/-- **Boundary inputs of the Cauchy-moment argument** (the part of `ct:dyadic` (1) used by (2); proved from `CtBandData c₁` in
`ctGRegData_of_band`).  For `c ≥ c₀`, every feasible `f` with `M[f] = 1`, `T < cξ(a₁)` and `ũ₁ > φ_c(a₁)` has a radius `A = √R_J` (`R_J` a good Airy
radius of size `≍ c^{2/3}`, `9 c₁ c^{1/3} ≤ A`, i.e. `c₁` small, and `A² ≤ langerRadius c`) with arc mass
`Σ = ∫_0^π ‖G_reg(Ae^{iy})‖ A dy ≤ C_Σ/A` and `∫_{-A}^A t²‖G_reg(t)‖ dt = ∫_0^{R_J} v (1 - v/R_J)² |Ψ̃(-v)| dv ≤ C_S A`. -/
def CtGRegData (c₁ : ℝ) : Prop :=
  ∃ CSig CS c₀ : ℝ, 0 ≤ CSig ∧ 0 ≤ CS ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∃ A : ℝ, 9 * (c₁ * c ^ (1 / 3 : ℝ)) ≤ A ∧ A ^ 2 ≤ langerRadius c ∧
        hdArcMass A (ctGReg A c f) ≤ CSig / A ∧
        ∫ t in (-A)..A, (t : ℝ) ^ 2 * ‖ctGReg A c f (t : ℂ)‖ ≤ CS * A

/-- **Top-scale inputs of `ct:dyadic` (1)** (`T < cξ(a₁)` is the violator regime of `ct:sec4`; it is needed because `ctUtilde` is the arbitrary `invFunOn` value when `T/c ∉ ξ([-3,0])`, where `0 < ctGap` carries no information) (named hypothesis).  For `c ≥ c₀`, every feasible `f` with `M[f] = 1`, `T < cξ(a₁)` and `ũ₁ > φ_c(a₁)` has
a radius `A = √R_J` (`R_J` a good Airy radius of size `≍ c^{2/3}`, `9 c₁ c^{1/3} ≤ A`, i.e. `c₁` small, and `A² < R_dom(c)`) with

* `(ct:cov)` on the circle `|ũ'| = R_J` (`CtCovCircle c f R_J L_{♯♯} C₂`), and
* the first moment of `(ct:half)`, `∫_0^{R_J} v |Ψ̃(-v)| dv ≤ C_half c^{1/3}` (`CtHalfMoment`).

These are the outputs of `ct:dyadic` (1) at the top radius; **proved for `0 < c₁ ≤ 1/900` in `ctBandData_small` (`CtBandTop`)**, from the top-scale bootstrap alone.  `ctGRegData_of_band` derives from them, with the
Type-(I) bound `hankelPsi_envelope` (proved), the boundary inputs `CtGRegData` of Part (2). -/
def CtBandData (c₁ : ℝ) : Prop :=
  ∃ Lsh C₂ Chalf c₀ : ℝ, 0 ≤ Lsh ∧ 0 ≤ C₂ ∧ 0 ≤ Chalf ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ c : ℝ, c₀ ≤ c →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∃ A : ℝ, 9 * (c₁ * c ^ (1 / 3 : ℝ)) ≤ A ∧ A ^ 2 < langerRadius c ∧ ctGoodRadius (A ^ 2) ∧
        CtCovCircle c f (A ^ 2) Lsh C₂ ∧ CtHalfMoment c f (A ^ 2) Chalf

lemma log_le_three_rpow {c : ℝ} (hc : 0 < c) : Real.log c ≤ 3 * c ^ (1 / 3 : ℝ) := by
  have := Real.log_le_rpow_div hc.le (by norm_num : (0 : ℝ) < 1 / 3)
  linarith [this, show c ^ (1 / 3 : ℝ) / (1 / 3) = 3 * c ^ (1 / 3 : ℝ) by ring]

/-- The wedge threshold: `(Aφ₀)² ≤ C₂² · 3c^{1/3}/A` for `φ₀ = C₂ (A²)^{-3/4} (log c)^{1/2}`. -/
lemma wedge_thr_sq {A c C₂ : ℝ} (hA : 0 < A) (hc : 1 ≤ c) :
    (A * (C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c))) ^ 2 ≤ C₂ ^ 2 * (3 * c ^ (1 / 3 : ℝ)) / A := by
  have hB : (A * (A ^ 2) ^ (-(3 / 4 : ℝ))) ^ 2 = A⁻¹ := by
    have h1 : ((A ^ 2) ^ (-(3 / 4 : ℝ))) ^ 2 = (A ^ 2) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
    have h2 : A ^ 2 * (A ^ 2) ^ (-(3 / 2 : ℝ)) = A⁻¹ := by
      have hB0 : (0 : ℝ) < A ^ 2 := by positivity
      calc A ^ 2 * (A ^ 2) ^ (-(3 / 2 : ℝ)) = (A ^ 2) ^ (1 : ℝ) * (A ^ 2) ^ (-(3 / 2 : ℝ)) := by rw [Real.rpow_one]
        _ = (A ^ 2) ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add hB0]; norm_num
        _ = A⁻¹ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num [Real.rpow_neg_one]
    rw [mul_pow, h1, h2]
  have hq : Real.sqrt (Real.log c) ^ 2 ≤ 3 * c ^ (1 / 3 : ℝ) := by
    have hl : 0 ≤ Real.log c := Real.log_nonneg hc
    rw [Real.sq_sqrt hl]; exact log_le_three_rpow (by linarith)
  calc (A * (C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c))) ^ 2
      = C₂ ^ 2 * (A * (A ^ 2) ^ (-(3 / 4 : ℝ))) ^ 2 * Real.sqrt (Real.log c) ^ 2 := by ring
    _ = C₂ ^ 2 * A⁻¹ * Real.sqrt (Real.log c) ^ 2 := by rw [hB]
    _ ≤ C₂ ^ 2 * A⁻¹ * (3 * c ^ (1 / 3 : ℝ)) := by gcongr
    _ = _ := by ring

/-- **`CtGRegData` from the top-scale inputs of `ct:dyadic` (1)**: the arc mass `Σ ≤ C_Σ/A` (covered arc by `(ct:cov)`, wedge by
Type-(I)) and the absolute second moment `∫ t²‖G_reg‖ ≤ C_S A` (from the first `v`-moment of `(ct:half)`, `A ≥ 9 c₁ c^{1/3}`). -/
theorem ctGRegData_of_band {c₁ : ℝ} (hc₁ : 0 < c₁) (hband : CtBandData c₁) : CtGRegData c₁ := by
  obtain ⟨Lsh, C₂, Chalf, c₀, hL, hC, hCh, hb⟩ := hband
  set Y : ℝ := max 1 (C₂ ^ 2 / (3 * c₁)) with hY
  have hY1 : 1 ≤ Y := le_max_left _ _
  refine ⟨8 * π * Lsh + 240 * π * (Y * Y ^ (3 / 2 : ℝ)), Chalf / (9 * c₁), max c₀ 2, by positivity,
    by positivity, ?_⟩
  intro ε hε c hc T f hf hmass hviol hgap
  have hc0 : c₀ ≤ c := (le_max_left _ _).trans hc
  have hc2 : 2 ≤ c := (le_max_right _ _).trans hc
  have hcpos : 0 < c := by linarith
  have hfe := hf.toIsHankelEigenfn
  obtain ⟨A, hA9, hAR, -, hcov, hhalf⟩ := hb ε hε c hc0 T f hf hmass hviol hgap
  have hcs : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hcpos _
  have hA : 0 < A := by have := mul_pos hc₁ hcs; linarith
  refine ⟨A, hA9, hAR.le, ?_, ?_⟩
  · -- arc mass
    have hm := ctArcMass_le hc2 hfe hε hmass hA hAR hL hC hcov
    set φ₀ : ℝ := C₂ * (A ^ 2) ^ (-(3 / 4 : ℝ)) * Real.sqrt (Real.log c) with hφ
    have hφ0 : 0 ≤ φ₀ := by positivity
    have hx2 : (A * φ₀) ^ 2 ≤ C₂ ^ 2 / (3 * c₁) := by
      have h := wedge_thr_sq (C₂ := C₂) hA (by linarith : 1 ≤ c)
      rw [← hφ] at h
      refine h.trans ?_
      rw [div_le_div_iff₀ hA (by positivity)]
      have : 9 * (c₁ * c ^ (1 / 3 : ℝ)) ≤ A := hA9
      nlinarith [mul_nonneg (sq_nonneg C₂) hcs.le]
    have hx : A * φ₀ ≤ Y := by
      by_contra hcon
      push Not at hcon
      have h1 : 1 < A * φ₀ := lt_of_le_of_lt hY1 hcon
      have : A * φ₀ ≤ (A * φ₀) ^ 2 := by nlinarith
      have h2 : C₂ ^ 2 / (3 * c₁) ≤ Y := le_max_right _ _
      linarith
    have hx0 : 0 ≤ A * φ₀ := by positivity
    have hid : A ^ (3 / 2 : ℝ) * (φ₀ * φ₀ ^ (3 / 2 : ℝ)) = (A * φ₀) * (A * φ₀) ^ (3 / 2 : ℝ) / A := by
      rw [Real.mul_rpow hA.le hφ0]; field_simp
    have hmono : (A * φ₀) * (A * φ₀) ^ (3 / 2 : ℝ) ≤ Y * Y ^ (3 / 2 : ℝ) := by gcongr
    calc hdArcMass A (ctGReg A c f) ≤ _ := hm
      _ = (8 * π * Lsh + 240 * π * ((A * φ₀) * (A * φ₀) ^ (3 / 2 : ℝ))) / A := by
          rw [mul_assoc (240 * π), hid]; field_simp
      _ ≤ _ := by gcongr
  · -- second moment
    have h1 := ctSecondMoment_le hcpos hfe hA hAR.le
    have h2 : Chalf * c ^ (1 / 3 : ℝ) ≤ Chalf / (9 * c₁) * A := by
      have : c ^ (1 / 3 : ℝ) ≤ A / (9 * c₁) := by
        rw [le_div_iff₀ (by positivity)]; nlinarith [hA9]
      calc Chalf * c ^ (1 / 3 : ℝ) ≤ Chalf * (A / (9 * c₁)) := by gcongr
        _ = _ := by ring
    exact h1.trans (hhalf.trans h2)

/-- info: 'FormalResearch.SignUncertainty.ctGRegData_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ctGRegData_of_band

/-- info: 'FormalResearch.SignUncertainty.ctArcMass_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ctArcMass_le

/-- info: 'FormalResearch.SignUncertainty.ctSecondMoment_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.ctSecondMoment_le

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.UctSeedAdmiss
public import FormalResearch.SignUncertainty.UctAiryTransPhi

/-!
# `W^seed` on the edge: the amplitude `A_*` and the identity `(uct:KW-seed-edge)` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, proof of `uct:seed-asymp`, `(uct:KW-seed-edge)`.  **Proved.**

* `uctAstar τ = cosh(πτ) (πτ/sinh πτ)² e^{-u_r(τ)} (1+τ²)^{-1/2}`: the TeX amplitude
  `A_*(τ) = |τ|^{5/2}|H_*(iτ)| (6/π² m'(|τ|))^{-1/2}` (`uctAstar_eq_paper` for `τ ≠ 0`); it is even, `C^∞` on `ℝ`, `A_*(0) = 1`.
* `uctMc c δ τ = e^{B_c(iτ)} (φ_{c,δ}(1-iτ)/φ_{c,δ}(1)) A_*(τ)`.
* `seedZ_edge_core`: `(1-iτ)^{-1/2} Z_ε(iτ) e^{-h(iτ)} = e^{-iθ_ε(τ)} (1-iτ)^{5/2} A_*(τ)` for `τ > 0`.
* `kw_seed_edge` (`(uct:KW-seed-edge)`): `K₀(iτ,ξ) W^seed(iτ) = e^{icΦ_Ph(τ;L) - iθ_ε(τ)} M_c(τ) F̃_{*,δ}(-c_s c^{1/3} τ)`
  for all real `τ` (`F̃_{*,δ}(-aτ) = T(iaτ) = seedV δ (aτ)`).
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

/-- `x / sinh x` (value `1` at `0`), as the real part of `sincInv (i x)`. -/
noncomputable def uctSincH (x : ℝ) : ℝ := (sincInv ((x : ℂ) * Complex.I)).re

lemma sincInv_mul_I {x : ℝ} (hx : x ≠ 0) : sincInv ((x : ℂ) * Complex.I) = ((x / Real.sinh x : ℝ) : ℂ) := by
  have hz : (x : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hx) Complex.I_ne_zero
  rw [sincInv_of_ne hz, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hs : Real.sinh x ≠ 0 := Real.sinh_ne_zero.mpr hx
  have hsC : (Real.sinh x : ℂ) ≠ 0 := by exact_mod_cast hs
  push_cast
  field_simp

lemma uctSincH_eq {x : ℝ} (hx : x ≠ 0) : uctSincH x = x / Real.sinh x := by
  unfold uctSincH; rw [sincInv_mul_I hx, Complex.ofReal_re]

lemma uctSincH_zero : uctSincH 0 = 1 := by
  unfold uctSincH; simp [sincInv_zero]

lemma uctSincH_neg (x : ℝ) : uctSincH (-x) = uctSincH x := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [uctSincH_eq hx, uctSincH_eq (neg_ne_zero.mpr hx), Real.sinh_neg, div_neg, neg_div]
    simp

lemma contDiff_uctSincH : ContDiff ℝ ⊤ uctSincH := by
  have h1 : ContDiff ℝ ⊤ (fun x : ℝ => dslope Complex.sin 0 ((x : ℂ) * Complex.I)) :=
    (differentiable_dslope_sin.contDiff.restrict_scalars ℝ).comp
      (Complex.ofRealCLM.contDiff.mul contDiff_const)
  have h2 : ContDiff ℝ ⊤ (fun x : ℝ => (dslope Complex.sin 0 ((x : ℂ) * Complex.I))⁻¹) := by
    refine h1.inv (fun x => ?_)
    refine dslope_sin_ne_zero (fun n hn h => hn ?_)
    have h' := congrArg Complex.re h
    have h2 : (0 : ℝ) = n * π := by simpa using h'
    have h3 : (n : ℝ) = 0 := by
      rcases mul_eq_zero.mp h2.symm with h4 | h4
      · exact h4
      · exact absurd h4 Real.pi_ne_zero
    exact_mod_cast h3
  exact Complex.reCLM.contDiff.comp h2

/-- The amplitude `A_*(τ) = cosh(πτ) (πτ/sinh πτ)² e^{-u_r(τ)} (1+τ²)^{-1/2}`. -/
noncomputable def uctAstar (τ : ℝ) : ℝ :=
  Real.cosh (π * τ) * uctSincH (π * τ) ^ 2 * Real.exp (-uR τ) * (Real.sqrt (1 + τ ^ 2))⁻¹

lemma uctAstar_zero : uctAstar 0 = 1 := by
  simp [uctAstar, uctSincH_zero, uR]

lemma uctAstar_neg (τ : ℝ) : uctAstar (-τ) = uctAstar τ := by
  unfold uctAstar
  rw [mul_neg, Real.cosh_neg, uctSincH_neg, uR_neg, neg_sq]

lemma uctAstar_pos (τ : ℝ) : 0 < uctAstar τ := by
  unfold uctAstar
  have h0 : 0 < uctSincH (π * τ) := by
    by_cases hτ : τ = 0
    · simp [hτ, uctSincH_zero]
    · have hx : π * τ ≠ 0 := mul_ne_zero Real.pi_ne_zero hτ
      rw [uctSincH_eq hx]
      rcases lt_or_gt_of_ne hτ with h | h
      · have : π * τ < 0 := by nlinarith [Real.pi_pos]
        exact div_pos_of_neg_of_neg this (Real.sinh_neg_iff.mpr this)
      · have : 0 < π * τ := by positivity
        exact div_pos this (Real.sinh_pos_iff.mpr this)
  have := Real.sqrt_pos.mpr (by positivity : 0 < 1 + τ ^ 2)
  positivity

lemma contDiff_uctAstar : ContDiff ℝ ⊤ uctAstar := by
  unfold uctAstar
  have h1 : ContDiff ℝ ⊤ (fun τ : ℝ => Real.cosh (π * τ)) := Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)
  have h2 : ContDiff ℝ ⊤ (fun τ : ℝ => uctSincH (π * τ)) := contDiff_uctSincH.comp (contDiff_const.mul contDiff_id)
  have h3 : ContDiff ℝ ⊤ (fun τ : ℝ => Real.exp (-uR τ)) := Real.contDiff_exp.comp contDiff_uR.neg
  have h4 : ContDiff ℝ ⊤ (fun τ : ℝ => (Real.sqrt (1 + τ ^ 2))⁻¹) := by
    refine ContDiff.inv ?_ (fun τ => (Real.sqrt_pos.mpr (by positivity)).ne')
    exact ContDiff.sqrt (contDiff_const.add (contDiff_id.pow 2)) (fun τ => by positivity)
  exact ((h1.mul (h2.pow 2)).mul h3).mul h4


lemma sin_pi_I_mul {τ : ℝ} (hτ : 0 < τ) : Complex.sin ((π : ℂ) * (Complex.I * (τ : ℂ))) ≠ 0 := by
  have : (π : ℂ) * (Complex.I * (τ : ℂ)) = ((π * τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have : Real.sinh (π * τ) ≠ 0 := Real.sinh_ne_zero.mpr (by positivity)
  exact mul_ne_zero (by exact_mod_cast this) Complex.I_ne_zero

lemma seedA_edge {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (τ : ℝ) :
    seedA ε (Complex.I * (τ : ℂ)) = (Real.cosh (π * τ) : ℂ) *
      (if ε = 1 then Complex.exp (2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ)) else 1) := by
  have hcos : Complex.cos ((π : ℂ) * (Complex.I * (τ : ℂ))) = (Real.cosh (π * τ) : ℂ) := by
    have : (π : ℂ) * (Complex.I * (τ : ℂ)) = ((π * τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  unfold seedA
  rcases hε with rfl | rfl
  · simp only [↓reduceIte]
    have hb := bHalf_I_mul τ
    unfold bHalf at hb
    have hbarg : (π : ℂ) / 4 - π * (Complex.I * τ) / 2 = bArg (Complex.I * (τ : ℂ)) := rfl
    rw [hbarg] at hb
    have hc0 : Complex.cos (bArg (Complex.I * (τ : ℂ))) ≠ 0 := by
      intro h0
      rw [Complex.tan_eq_sin_div_cos, h0, div_zero] at hb
      exact (Complex.exp_ne_zero _) hb.symm
    have h2 : Complex.cos ((π : ℂ) * (Complex.I * (τ : ℂ))) =
        2 * Complex.cos (bArg (Complex.I * (τ : ℂ))) ^ 2 * Complex.tan (bArg (Complex.I * (τ : ℂ))) := by
      have : (π : ℂ) * (Complex.I * (τ : ℂ)) = π / 2 - 2 * bArg (Complex.I * (τ : ℂ)) := by
        unfold bArg; ring
      rw [this, Complex.cos_pi_div_two_sub, Complex.sin_two_mul, Complex.tan_eq_sin_div_cos]
      field_simp
    rw [hb] at h2
    have hex : Complex.exp (-(2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ))) *
        Complex.exp (2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_add]; simp
    rw [hcos] at h2
    calc 2 * Complex.cos (bArg (Complex.I * (τ : ℂ))) ^ 2
        = 2 * Complex.cos (bArg (Complex.I * (τ : ℂ))) ^ 2 *
          (Complex.exp (-(2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ))) *
            Complex.exp (2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ))) := by rw [hex, mul_one]
      _ = _ := by rw [h2]; ring
  · have hne : (-1 : ℝ) ≠ 1 := by norm_num
    simp only [hne, ↓reduceIte, mul_one]
    exact hcos

lemma seedZ_edge {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {τ : ℝ} (hτ : 0 < τ) :
    uctSeedZ ε (Complex.I * (τ : ℂ)) = ((Real.cosh (π * τ) * uctSincH (π * τ) ^ 2 : ℝ) : ℂ) *
      (1 - Complex.I * (τ : ℂ)) ^ 2 *
      (if ε = 1 then Complex.exp (2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ)) else 1) := by
  rw [uctSeedZ_eq_of_sin (sin_pi_I_mul hτ), seedA_edge hε τ]
  have hx : π * τ ≠ 0 := by positivity
  have hs : (π : ℂ) * (Complex.I * (τ : ℂ)) = ((π * τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hsc : (π : ℂ) * (Complex.I * (τ : ℂ)) * (1 - Complex.I * (τ : ℂ)) / Complex.sin ((π : ℂ) * (Complex.I * (τ : ℂ))) =
      (uctSincH (π * τ) : ℂ) * (1 - Complex.I * (τ : ℂ)) := by
    rw [mul_div_right_comm, hs, ← sincInv_of_ne (mul_ne_zero (by exact_mod_cast hx) Complex.I_ne_zero), sincInv_mul_I hx,
      uctSincH_eq hx]
  rw [hsc]
  push_cast
  ring


/-- `(1-iτ)^{-1/2} Z_ε(iτ) e^{-h(iτ)} = e^{-iθ_ε(τ)} (1-iτ)^{5/2} A_*(τ)` for `τ > 0`. -/
theorem seedZ_edge_core {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {τ : ℝ} (hτ : 0 < τ) :
    (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * (uctAstar τ : ℂ) := by
  set w : ℂ := 1 - Complex.I * (τ : ℂ) with hw
  have hs0 : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hsC : (Real.sqrt (1 + τ ^ 2) : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hwe : w = (Real.sqrt (1 + τ ^ 2) : ℂ) * Complex.exp (-(Complex.I * (Real.arctan τ : ℝ))) := one_sub_I_mul_eq
  have hw0 : w ≠ 0 := by
    rw [hwe]; exact mul_ne_zero hsC (Complex.exp_ne_zero _)
  set P : ℂ := w ^ (1 / 2 : ℂ) with hP
  have hP2 : P ^ 2 = w := FormalResearch.SignUncertainty.CtOuter.cpow_half_sq w
  have hP0 : P ≠ 0 := by
    intro h; apply hw0; rw [← hP2, h]; simp
  have e1 : w ^ (-(1 / 2 : ℂ)) = P⁻¹ := by rw [Complex.cpow_neg]
  have e2 : w ^ (5 / 2 : ℂ) = w ^ 2 * P := by
    rw [show (5 / 2 : ℂ) = 2 + 1 / 2 by norm_num, Complex.cpow_add _ _ hw0]
    congr 1
    exact_mod_cast Complex.cpow_natCast w 2
  have key : P⁻¹ * w = P := by rw [← hP2]; field_simp
  have hat : Complex.exp (-(Complex.I * (Real.arctan τ : ℝ))) = w * (Real.sqrt (1 + τ ^ 2) : ℂ)⁻¹ := by
    rw [hwe]; field_simp
  have hθ : Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) =
      Complex.exp (-(Complex.I * (outerTheta (-1) τ : ℂ))) *
        (if ε = 1 then Complex.exp (2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ)) else 1) := by
    rcases hε with rfl | rfl
    · simp only [↓reduceIte]
      rw [← Complex.exp_add, outerTheta_plus]
      congr 1; push_cast; ring
    · have hne : (-1 : ℝ) ≠ 1 := by norm_num
      simp [hne]
  have hh : Complex.exp (-outerHbar (Complex.I * (τ : ℂ))) =
      Complex.exp (-(uR τ : ℂ)) * Complex.exp (-(Complex.I * (outerTheta (-1) τ : ℂ))) *
        Complex.exp (-(Complex.I * (Real.arctan τ : ℝ))) := by
    rw [outerHbar_edge, ← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
  have hA : (uctAstar τ : ℂ) = (Real.cosh (π * τ) : ℂ) * (uctSincH (π * τ) : ℂ) ^ 2 * Complex.exp (-(uR τ : ℂ)) *
      (Real.sqrt (1 + τ ^ 2) : ℂ)⁻¹ := by
    unfold uctAstar; push_cast; rfl
  rw [e1, e2, seedZ_edge hε hτ, hh, hθ, hat, hA]
  set E : ℂ := (if ε = 1 then Complex.exp (2 * Complex.I * ((Real.arctan (Real.tanh (π * τ / 2)) : ℝ) : ℂ)) else 1)
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, ← hw]
  linear_combination ((Real.cosh (π * τ) : ℂ) * (uctSincH (π * τ) : ℂ) ^ 2 * w ^ 2 * E * Complex.exp (-(uR τ : ℂ)) *
    Complex.exp (-(Complex.I * (outerTheta (-1) τ : ℂ))) * (Real.sqrt (1 + τ ^ 2) : ℂ)⁻¹) * key


/-- `M_c(τ) = e^{B_c(iτ)} (φ_{c,δ}(1-iτ)/φ_{c,δ}(1)) A_*(τ)` (the smooth amplitude of `(uct:KW-seed-edge)`). -/
noncomputable def uctMc (c δ : ℝ) (τ : ℝ) : ℂ :=
  Complex.exp (FormalResearch.Asymptotics.binetDiff c ((τ : ℂ) * Complex.I)) *
    (uctPhi c δ (1 - (τ : ℂ) * Complex.I) / uctPhi c δ 1) * (uctAstar τ : ℂ)

lemma uctPhi_one (c δ : ℝ) : uctPhi c δ 1 =
    ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * seedT δ (seedScale c : ℂ) := by
  unfold uctPhi seedT seedScale
  simp

lemma uctPhi_eq_seedT (c δ : ℝ) (w : ℂ) : uctPhi c δ w =
    ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) * w ^ (5 / 2 : ℂ) * seedT δ ((seedScale c : ℂ) * w) := rfl

theorem kw_seed_edge_of_core {ε c δ ξ τ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hcore : (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * (uctAstar τ : ℂ)) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * seedW ε δ c ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * uctMc c δ τ * seedV δ (seedScale c * τ) := by
  have hK : ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) ≠ 0 := by
    have : c ^ (5 / 6 : ℝ) / uctCAi ≠ 0 := div_ne_zero (Real.rpow_pos_of_pos hc _).ne' uctCAi_ne
    exact_mod_cast this
  set K : ℂ := ((c ^ (5 / 6 : ℝ) / uctCAi : ℝ) : ℂ) with hKdef
  have hcomm : (τ : ℂ) * Complex.I = Complex.I * (τ : ℂ) := mul_comm _ _
  have hV : seedV δ (seedScale c * τ) = seedT δ ((seedScale c : ℂ) * (Complex.I * (τ : ℂ))) := by
    unfold seedV
    congr 1; push_cast; ring
  rw [mellinK0_imag_outer c ξ τ hξ, ← outerK_eq, hV]
  unfold seedW uctMc
  rw [hcomm, uctPhi_one, uctPhi_eq_seedT]
  have hmd : K * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * seedT δ ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ))) /
      (K * seedT δ (seedScale c : ℂ)) =
      (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * seedT δ ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ))) *
        (seedT δ (seedScale c : ℂ))⁻¹ := by
    rw [mul_assoc K, mul_div_mul_left _ _ hK, div_eq_mul_inv]
  simp only [← hKdef]
  rw [hmd]
  have hexp : Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) := rfl
  set Bc := Complex.exp (FormalResearch.Asymptotics.binetDiff c (Complex.I * (τ : ℂ)))
  set Ph := Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ))
  linear_combination (Bc * Ph * (seedT δ (seedScale c : ℂ))⁻¹ *
    seedT δ ((seedScale c : ℂ) * (Complex.I * (τ : ℂ))) *
    seedT δ ((seedScale c : ℂ) * (1 - Complex.I * (τ : ℂ)))) * hcore


lemma conj_cpow_of_re_pos {w : ℂ} (hw : 0 < w.re) (m : ℂ) : starRingEnd ℂ (w ^ m) = (starRingEnd ℂ w) ^ (starRingEnd ℂ m) := by
  have harg : w.arg ≠ π := arg_ne_pi_of_re_nonneg hw.le
  rw [Complex.conj_cpow w (starRingEnd ℂ m) harg, Complex.conj_conj]

lemma conj_two : starRingEnd ℂ (2 : ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

lemma conj_five : starRingEnd ℂ (5 : ℂ) = 5 := by
  rw [show (5 : ℂ) = ((5 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

theorem seedZ_edge_core_all {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {τ : ℝ} (hτ : τ ≠ 0) :
    (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (uctSeedZ ε (Complex.I * (τ : ℂ)) * Complex.exp (-outerHbar (Complex.I * (τ : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) * (uctAstar τ : ℂ) := by
  rcases lt_or_gt_of_ne hτ with h | h
  · set τ' : ℝ := -τ with hτ'
    have hτ'0 : 0 < τ' := by rw [hτ']; linarith
    have hc := congrArg (starRingEnd ℂ) (seedZ_edge_core hε hτ'0)
    have hcl : Complex.I * (τ' : ℂ) ∈ closedStrip := ⟨by simp, by simp⟩
    have e1 : Complex.I * (τ : ℂ) = starRingEnd ℂ (Complex.I * (τ' : ℂ)) := by simp [hτ']
    have e2 : (1 - Complex.I * (τ : ℂ)) = starRingEnd ℂ (1 - Complex.I * (τ' : ℂ)) := by rw [e1]; simp
    have hre : 0 < (1 - Complex.I * (τ' : ℂ)).re := by simp
    have hθ : outerTheta ε τ = -outerTheta ε τ' := by rw [hτ', outerTheta_neg, neg_neg]
    have hA : uctAstar τ = uctAstar τ' := by rw [hτ', uctAstar_neg]
    have c1 : starRingEnd ℂ ((1 - Complex.I * (τ' : ℂ)) ^ (-(1 / 2 : ℂ))) = (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) := by
      rw [conj_cpow_of_re_pos hre, ← e2]; simp [conj_two]
    have c5 : starRingEnd ℂ ((1 - Complex.I * (τ' : ℂ)) ^ (5 / 2 : ℂ)) = (1 - Complex.I * (τ : ℂ)) ^ (5 / 2 : ℂ) := by
      rw [conj_cpow_of_re_pos hre, ← e2]; simp [conj_two, conj_five]
    have c2 : starRingEnd ℂ (uctSeedZ ε (Complex.I * (τ' : ℂ))) = uctSeedZ ε (Complex.I * (τ : ℂ)) := by
      rw [e1, uctSeedZ_conj]
    have c3 : starRingEnd ℂ (Complex.exp (-outerHbar (Complex.I * (τ' : ℂ)))) =
        Complex.exp (-outerHbar (Complex.I * (τ : ℂ))) := by
      rw [← Complex.exp_conj, map_neg, e1, outerHbar_conj hcl]
    have c4 : starRingEnd ℂ (Complex.exp (-(Complex.I * (outerTheta ε τ' : ℂ)))) =
        Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) := by
      rw [← Complex.exp_conj, hθ]; simp
    have c6 : starRingEnd ℂ (uctAstar τ' : ℂ) = (uctAstar τ : ℂ) := by rw [hA]; simp
    simp only [map_mul, c1, c2, c3, c4, c5, c6] at hc
    exact hc
  · exact seedZ_edge_core hε h

theorem kw_seed_edge {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c δ ξ τ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hτ : τ ≠ 0) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * seedW ε δ c ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * uctMc c δ τ * seedV δ (seedScale c * τ) :=
  kw_seed_edge_of_core hc hξ (seedZ_edge_core_all hε hτ)


lemma outerTheta_zero (ε : ℝ) : outerTheta ε 0 = 0 := by
  have := outerTheta_neg ε 0
  simp only [neg_zero] at this
  linarith

theorem seedZ_edge_core_zero {ε : ℝ} :
    (1 - Complex.I * ((0 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ)) *
        (uctSeedZ ε (Complex.I * ((0 : ℝ) : ℂ)) * Complex.exp (-outerHbar (Complex.I * ((0 : ℝ) : ℂ)))) =
      Complex.exp (-(Complex.I * (outerTheta ε 0 : ℂ))) * (1 - Complex.I * ((0 : ℝ) : ℂ)) ^ (5 / 2 : ℂ) *
        (uctAstar 0 : ℂ) := by
  simp [uctSeedZ_zero, outerHbar_zero, uctAstar_zero, outerTheta_zero]

/-- **`(uct:KW-seed-edge)` at every real `τ`.** -/
theorem kw_seed_edge_all {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {c δ ξ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (τ : ℝ) :
    mellinK0 c ((τ : ℂ) * Complex.I) ξ * seedW ε δ c ((τ : ℂ) * Complex.I) =
      Complex.exp (Complex.I * ((c * edgePhi (Real.log (Real.pi ^ 2 * ξ)) τ : ℝ) : ℂ)) *
        Complex.exp (-(Complex.I * (outerTheta ε τ : ℂ))) * uctMc c δ τ * seedV δ (seedScale c * τ) := by
  by_cases hτ : τ = 0
  · subst hτ
    exact kw_seed_edge_of_core hc hξ seedZ_edge_core_zero
  · exact kw_seed_edge hε hc hξ hτ


lemma norm_uctHstar_edge {τ : ℝ} (hτ : 0 < τ) :
    ‖uctHstar (Complex.I * (τ : ℂ))‖ = π ^ 2 * Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2 := by
  have hx : (π : ℂ) * (Complex.I * (τ : ℂ)) = ((π * τ : ℝ) : ℂ) * Complex.I := by push_cast; ring
  unfold uctHstar
  rw [hx, Complex.sin_mul_I, Complex.cos_mul_I, ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  have hs : 0 < Real.sinh (π * τ) := Real.sinh_pos_iff.mpr (by positivity)
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    abs_of_pos (Real.cosh_pos _), abs_of_pos hs]

/-- `A_*(τ) = τ^{5/2} |H_*(iτ)| / √((6/π²) m'(τ))` for `τ > 0` (the TeX definition of `A_*`; `A_*` is even). -/
theorem uctAstar_eq_paper {τ : ℝ} (hτ : 0 < τ) :
    uctAstar τ = τ ^ (5 / 2 : ℝ) * ‖uctHstar (Complex.I * (τ : ℂ))‖ / Real.sqrt (6 / π ^ 2 * mPrime τ) := by
  rw [norm_uctHstar_edge hτ, ← exp_uR_mul hτ]
  have hx : π * τ ≠ 0 := by positivity
  have hs : 0 < Real.sinh (π * τ) := Real.sinh_pos_iff.mpr (by positivity)
  have h1 : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  have hq : 0 < Real.sqrt (1 + τ ^ 2) := Real.sqrt_pos.mpr h1
  have ht : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have h52 : τ ^ (5 / 2 : ℝ) = τ ^ 2 * Real.sqrt τ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hτ]; norm_num
  unfold uctAstar
  rw [uctSincH_eq hx, h52, Real.exp_neg]
  have he : 0 < Real.exp (uR τ) := Real.exp_pos _
  field_simp

/-- info: 'FormalResearch.SignUncertainty.contDiff_uctAstar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contDiff_uctAstar

/-- info: 'FormalResearch.SignUncertainty.uctAstar_eq_paper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uctAstar_eq_paper

/-- info: 'FormalResearch.SignUncertainty.seedZ_edge_core_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seedZ_edge_core_all

/-- info: 'FormalResearch.SignUncertainty.kw_seed_edge_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kw_seed_edge_all

end FormalResearch.SignUncertainty

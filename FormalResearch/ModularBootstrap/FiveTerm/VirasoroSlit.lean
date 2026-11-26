module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroOuter

/-!
# `G_outer` on the slit `z = iy` (FIVE-0 slice 4): the modulus `|G(iy)| = W_slit(y)`

With `y = tanh(πτ/4)`: `sInv(iy) = iτ`, `Re h̄_a(iτ) = a(τ)`, `Q̂(iy) = slitVal y = (1/2 - i v_x)/x`,
and `exp(a) = W_slit (1+y²)^{3/4} (|b_x|/x)^{1/4}` (`aAmp_eq`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- The strip parameter `τ` of the slit point `iy`: `y = tanh(πτ/4)`. -/
noncomputable def slitTau (y : ℝ) : ℝ := 4 / π * Real.artanh y

lemma slitTau_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ slitTau y :=
  mul_nonneg (by positivity) (Real.artanh_nonneg hy)

lemma tanh_slitTau {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : Real.tanh (π * slitTau y / 4) = y := by
  have : π * slitTau y / 4 = Real.artanh y := by
    unfold slitTau; field_simp
  rw [this, Real.tanh_artanh ⟨by linarith [hy.1], hy.2⟩]

lemma slit_mem_closedStrip (τ : ℝ) : (τ : ℂ) * Complex.I ∈ unitStripCl :=
  ⟨by simp, by simp⟩

lemma sTan_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    sTan ((slitTau y : ℝ) * Complex.I) = Complex.I * (y : ℂ) := by
  rw [sTan_I_mul, tanh_slitTau hy]

lemma sInv_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    sInv (Complex.I * (y : ℂ)) = (slitTau y : ℂ) * Complex.I := by
  rw [← sTan_slit hy]
  exact sInv_sTan (slit_mem_closedStrip _)

lemma slit_mem_closure {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : Complex.I * (y : ℂ) ∈ closure halfDisc := by
  rw [← sTan_slit hy]
  exact sTan_mem_closure (slit_mem_closedStrip _)

lemma slit_ne {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Complex.I * (y : ℂ) ≠ Complex.I ∧ Complex.I * (y : ℂ) ≠ -Complex.I ∧ Complex.I * (y : ℂ) ≠ 1 := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg Complex.im h; simp at this; linarith [hy.2]
  · have := congrArg Complex.im h; simp at this; linarith [hy.1]
  · have := congrArg Complex.re h; simp at this

lemma slit_mem_diff {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    Complex.I * (y : ℂ) ∈ closure halfDisc \ singPts := by
  refine ⟨slit_mem_closure hy, fun h => ?_⟩
  obtain ⟨h1, h2, h3⟩ := slit_ne hy
  simp only [singPts, Set.mem_insert_iff, Set.mem_singleton_iff] at h
  tauto

lemma qBd_slit {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : qBd (Complex.I * (y : ℂ)) = slitVal y :=
  extLim_eq_of_tendsto (slit_mem_closure hy) (tendsto_qHat_slit hy.1 hy.2)

lemma xOf_pos {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 0 < xOf y := by
  have h1 := uSlit_gt_one hy.1 hy.2
  unfold xOf
  exact div_pos (Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (by linarith))) Real.pi_pos

lemma norm_slitVal {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ‖slitVal y‖ = √(vOf y ^ 2 + 1 / 4) / xOf y := by
  have h1 := uSlit_gt_one hy.1 hy.2
  have hx := xOf_pos hy
  have hpi := Real.pi_pos
  set A : ℝ := Real.arsinh (√(uSlit y - 1)) with hA
  set B : ℝ := Real.arsinh (√(uSlit y)) with hB
  have hv : vOf y = A / π := rfl
  have hxe : xOf y = B / π := rfl
  have hBpos : 0 < B := Real.arsinh_pos_iff.mpr (Real.sqrt_pos.mpr (by linarith))
  have hnum : ((π : ℂ) / 2 - Complex.I * (A : ℂ)) = (((π / 2 : ℝ) : ℂ) + ((-A : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  unfold slitVal
  rw [← hA, ← hB, hnum, norm_div, Complex.norm_add_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hBpos, hv, hxe]
  have hq : (π / 2) ^ 2 + (-A) ^ 2 = π ^ 2 * ((A / π) ^ 2 + 1 / 4) := by field_simp; ring
  rw [hq, Real.sqrt_mul (by positivity), Real.sqrt_sq hpi.le]
  field_simp

/-- **The slit modulus**, `|G_outer(iy)| = W_slit(y)` (`cts:Gmod`, first half). -/
theorem gout_modulus {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : ‖Gout (Complex.I * (y : ℂ))‖ = Wslit y := by
  obtain ⟨hy0, hy1⟩ := hy
  have hy' : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, hy1⟩
  set τ : ℝ := slitTau y with hτ
  have hτ0 : 0 ≤ τ := slitTau_nonneg hy0.le
  have htanh : Real.tanh (π * τ / 4) = y := tanh_slitTau hy'
  have hre : (hbarA aAmp (Complex.I * (τ : ℂ))).re = aAmp τ := re_hbarA_left amp_aAmp τ
  have hsI : sInv (Complex.I * (y : ℂ)) = Complex.I * (τ : ℂ) := by
    rw [sInv_slit hy', mul_comm]
  have hA := aAmp_eq hτ0
  rw [htanh] at hA
  have hx := xOf_pos hy'
  have hW : 0 < Wslit y := by
    have h1 : 0 < 1 - y ^ 2 := by nlinarith
    have h2 : 0 < 1 + 6 * y ^ 2 + y ^ 4 := by positivity
    unfold Wslit
    have hxi := xiStar_pos
    have h3 : 0 < 1 - Real.exp (-(4 * π * xOf y)) := by
      rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr
      have := Real.pi_pos; nlinarith
    have h4 : 0 < 1 - Real.exp (-(4 * π * xiStar)) := by
      rw [sub_pos, ← Real.exp_zero]; apply Real.exp_lt_exp.mpr
      have := Real.pi_pos; nlinarith
    positivity
  have hr : 0 < √(vOf y ^ 2 + 1 / 4) / xOf y := by positivity
  have hn1 : ‖(1 : ℂ) - Complex.I * (y : ℂ)‖ = √(1 + y ^ 2) := by
    have : (1 : ℂ) - Complex.I * (y : ℂ) = (1 : ℝ) + ((-y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_add_mul_I]; simp
  have hn2 : ‖(1 : ℂ) + Complex.I * (y : ℂ)‖ = √(1 + y ^ 2) := by
    have : (1 : ℂ) + Complex.I * (y : ℂ) = (1 : ℝ) + ((y : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this, Complex.norm_add_mul_I]; simp
  have hs1 : 0 < √(1 + y ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have e1 : ‖(1 - Complex.I * (y : ℂ)) ^ (1 / 2 : ℂ)‖ = (1 + y ^ 2) ^ (1 / 4 : ℝ) := by
    have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_real, hn1, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  have e2 : ‖(qBd (Complex.I * (y : ℂ))) ^ (-(1 / 4 : ℂ))‖ = (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-(1 / 4 : ℝ)) := by
    have : (-(1 / 4 : ℂ)) = ((-(1 / 4) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_real, qBd_slit hy', norm_slitVal hy']
  unfold Gout
  rw [hsI, norm_mul, norm_div, norm_mul, Complex.norm_exp, hre, e1, e2, norm_pow, hn2,
    Real.sq_sqrt (by positivity)]
  -- now real arithmetic: exp(a) * (1+y²)^(1/4) / (1+y²) * r^(-1/4) = W
  have hlogW : aAmp τ = Real.log (Wslit y) + (3 / 4) * Real.log (1 + y ^ 2) +
      (1 / 4) * Real.log (√(vOf y ^ 2 + 1 / 4) / xOf y) := hA
  have : Real.exp (aAmp τ) = Wslit y * (1 + y ^ 2) ^ (3 / 4 : ℝ) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (1 / 4 : ℝ) := by
    rw [hlogW, Real.exp_add, Real.exp_add, Real.exp_log hW, mul_comm (3 / 4 : ℝ), mul_comm (1 / 4 : ℝ),
      ← Real.rpow_def_of_pos (by positivity), ← Real.rpow_def_of_pos hr]
  rw [this]
  have hp : (1 + y ^ 2) ^ (3 / 4 : ℝ) * (1 + y ^ 2) ^ (1 / 4 : ℝ) = 1 + y ^ 2 := by
    rw [← Real.rpow_add (by positivity)]; norm_num
  have hq : (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (1 / 4 : ℝ) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-(1 / 4 : ℝ)) = 1 := by
    rw [← Real.rpow_add hr]; norm_num
  have h1y : (0 : ℝ) < 1 + y ^ 2 := by positivity
  calc Wslit y * (1 + y ^ 2) ^ (3 / 4 : ℝ) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (1 / 4 : ℝ) *
        (1 + y ^ 2) ^ (1 / 4 : ℝ) / (1 + y ^ 2) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-(1 / 4 : ℝ))
      = Wslit y * ((1 + y ^ 2) ^ (3 / 4 : ℝ) * (1 + y ^ 2) ^ (1 / 4 : ℝ)) / (1 + y ^ 2) *
        ((√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (1 / 4 : ℝ) * (√(vOf y ^ 2 + 1 / 4) / xOf y) ^ (-(1 / 4 : ℝ))) := by
        ring
    _ = Wslit y := by rw [hp, hq]; field_simp

end FormalResearch.ModularBootstrap.FiveTerm

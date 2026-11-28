module

public import Mathlib
public import FormalResearch.SignUncertainty.CtSdAiry
public import FormalResearch.SignUncertainty.CtRoscUpper
public import FormalResearch.SignUncertainty.CtAiryHplus

/-!
# Shared signed half-cubic core (`fs:half-cubic`, phase-free): scalars, contour moments, and Airy pairing

Source: `CFT/common/fine_order_signed.tex`, Lemma FS.1 (`fs:half-cubic`), equations `(fs:scalar)`,
`(fs:moments)`, `(fs:pairing)`. Phase-free; shared between Paper I (`SignUncertainty`) and Paper II
(`ModularBootstrap`).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty.FineOrderSigned

open FormalResearch.Special FormalResearch.SignUncertainty CtSd CtAiryHplus HalfDiscCauchy

/-! ### Scalar Airy functions `J`, `K`, `K'` -/

/-- `J(u) = Ai(u) Bi(u)`. -/
noncomputable def fsJ (u : ℝ) : ℝ := airyAi u * airyBi u

/-- `K(u) = -π (Ai Bi)'(u) = -π (Ai'(u) Bi(u) + Ai(u) Bi'(u))`. -/
noncomputable def fsK (u : ℝ) : ℝ := -π * (airyAi' u * airyBi u + airyAi u * airyBiDeriv u)

/-- `K'(u) = -π (Ai Bi)''(u) = -π (2 Ai'(u) Bi'(u) + 2 u Ai(u) Bi(u))`. -/
noncomputable def fsKp (u : ℝ) : ℝ := -π * (2 * airyAi' u * airyBiDeriv u + 2 * u * airyAi u * airyBi u)

lemma hasDerivAt_fsJ (u : ℝ) : HasDerivAt fsJ (-(fsK u / π)) u := by
  have h : HasDerivAt fsJ (airyAi' u * airyBi u + airyAi u * airyBiDeriv u) u :=
    (hasDerivAt_airyAi u).mul (hasDerivAt_airyBi u)
  refine h.congr_deriv ?_
  unfold fsK
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

lemma hasDerivAt_fsK (u : ℝ) : HasDerivAt fsK (fsKp u) u := by
  have h1 : HasDerivAt (fun x => airyAi' x * airyBi x)
      ((u * airyAi u) * airyBi u + airyAi' u * airyBiDeriv u) u :=
    (hasDerivAt_airyAi' u).mul (hasDerivAt_airyBi u)
  have h2 : HasDerivAt (fun x => airyAi x * airyBiDeriv x)
      (airyAi' u * airyBiDeriv u + airyAi u * (u * airyBi u)) u :=
    (hasDerivAt_airyAi u).mul (hasDerivAt_airyBiDeriv u)
  have h := (h1.add h2).const_mul (-π)
  refine h.congr_deriv ?_
  unfold fsKp
  ring

/-! ### Unified steepest-descent contour `Γ(U, R)` and `(fs:moments)` -/

private lemma sqrt3_lt_two : Real.sqrt 3 < 2 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma fs_chain_v_facts {U R R₀ : ℝ} (hU : ¬ (-1 ≤ U)) (hR1 : 1 ≤ R) (hRR : R < R₀)
    (hUR : kap * |U| ≤ R ^ 2 / 16) :
    let v : ℝ := Real.sqrt (-kap * U)
    0 < v ∧ kap ≤ v ^ 2 ∧ (1 + Real.sqrt 3) * v ≤ R ∧ 3 * v < R₀ ∧ -(v ^ 2) / kap = U := by
  have hU_lt : U < -1 := lt_of_not_ge hU
  have hk0 : 0 < kap := kap_pos
  have hk1 : 1 ≤ kap := kap_ge_one
  have hneg : 0 < -kap * U := by nlinarith
  have hv_sq : Real.sqrt (-kap * U) ^ 2 = -kap * U := Real.sq_sqrt hneg.le
  have hv0 : 0 < Real.sqrt (-kap * U) := Real.sqrt_pos.2 hneg
  have hkv : kap ≤ Real.sqrt (-kap * U) ^ 2 := by rw [hv_sq]; nlinarith
  have hUabs : |U| = -U := abs_of_neg (by linarith)
  have hv_le_R4 : Real.sqrt (-kap * U) ≤ R / 4 := by
    have hv_sq_le : Real.sqrt (-kap * U) ^ 2 ≤ (R / 4) ^ 2 := by
      rw [hv_sq]; rw [hUabs] at hUR; linarith only [hUR]
    have := Real.sqrt_le_sqrt hv_sq_le
    rwa [Real.sqrt_sq hv0.le, Real.sqrt_sq (by positivity)] at this
  have h13 : 1 + Real.sqrt 3 ≤ 3 := by linarith only [sqrt3_lt_two]
  have hRv : (1 + Real.sqrt 3) * Real.sqrt (-kap * U) ≤ R := by
    calc (1 + Real.sqrt 3) * Real.sqrt (-kap * U) ≤ 3 * Real.sqrt (-kap * U) :=
          mul_le_mul_of_nonneg_right h13 hv0.le
      _ ≤ 3 * (R / 4) := by linarith only [hv_le_R4]
      _ ≤ R := by linarith only [hR1]
  have h3v : 3 * Real.sqrt (-kap * U) < R₀ := by
    have : 3 * Real.sqrt (-kap * U) ≤ R := by linarith only [hv_le_R4, hR1]
    linarith only [this, hRR]
  have hUeq : -(Real.sqrt (-kap * U) ^ 2) / kap = U := by rw [hv_sq]; field_simp [hk0.ne']
  exact ⟨hv0, hkv, hRv, h3v, hUeq⟩

/-- Unified steepest-descent chain `Γ(U, R)` inside `B(0, R₀)` ending at `R e^{iπ/6}`. -/
noncomputable def fsChain {U R R₀ : ℝ} (hR1 : 1 ≤ R) (hRR : R < R₀) (hUR : kap * |U| ≤ R ^ 2 / 16) :
    Chain3 R₀ ((R : ℂ) * d6) :=
  if hU : -1 ≤ U then chainA (by linarith only [hR1]) hRR
  else
    let hf := fs_chain_v_facts hU hR1 hRR hUR
    chainB hf.1 hf.2.2.1 hRR hf.2.2.2.1

/-- Constant for `(fs:moments)` on `fsChain`. -/
theorem fsChain_momOK : ∃ C : ℝ, 0 ≤ C ∧ ∀ {U R R₀ : ℝ} (hR1 : 1 ≤ R) (hRR : R < R₀)
    (hUR : kap * |U| ≤ R ^ 2 / 16), MomOK C U (fsChain hR1 hRR hUR) := by
  obtain ⟨Ca, hCa, ha⟩ := chainA_momOK
  obtain ⟨Cb, hCb, hb⟩ := chainB_momOK
  refine ⟨max Ca Cb, le_max_of_le_left hCa, fun {U R R₀} hR1 hRR hUR => ?_⟩
  have hmom_le : ∀ {C₁ C₂ U' : ℝ} {ch : Chain3 R₀ ((R : ℂ) * d6)},
      C₁ ≤ C₂ → MomOK C₁ U' ch → MomOK C₂ U' ch := fun hC ⟨m1, m2, m3⟩ => ⟨
    m1.trans (mul_le_mul_of_nonneg_right hC (by positivity)),
    m2.trans hC,
    m3.trans (mul_le_mul_of_nonneg_right hC (by positivity))⟩
  have hmom_congr : ∀ {C U₁ U₂ : ℝ} {ch : Chain3 R₀ ((R : ℂ) * d6)},
      U₁ = U₂ → MomOK C U₁ ch → MomOK C U₂ ch := by
    rintro C U₁ _ ch rfl h; exact h
  unfold fsChain
  split_ifs with hU
  · exact hmom_le (le_max_left _ _) (ha U R R₀ hU (by linarith only [hR1]) hRR)
  · have hf := fs_chain_v_facts hU hR1 hRR hUR
    exact hmom_congr hf.2.2.2.2
      (hmom_le (le_max_right Ca Cb) (hb (Real.sqrt (-kap * U)) R R₀ hf.1 hf.2.1 hf.2.2.1 hRR hf.2.2.2.1))

lemma fs_tail_cond {U R : ℝ} (hR1 : 1 ≤ R) (hUR : kap * |U| ≤ R ^ 2 / 16) :
    ∀ t : ℝ, R < t → -(t ^ 3 / 6) ≤ nu * U * t := by
  intro t ht
  have hU_le : |U| ≤ R ^ 2 / 16 := (le_mul_of_one_le_left (abs_nonneg U) kap_ge_one).trans hUR
  have ht0 : 0 < t := by linarith only [hR1, ht]
  have ht2 : R ^ 2 ≤ t ^ 2 := by nlinarith only [hR1, ht]
  have hnuU : nu * (-U) ≤ t ^ 2 / 16 := by
    calc nu * (-U) ≤ nu * |U| := mul_le_mul_of_nonneg_left (neg_le_abs U) nu_pos.le
      _ ≤ 1 * |U| := mul_le_mul_of_nonneg_right nu_le_one (abs_nonneg U)
      _ ≤ R ^ 2 / 16 := by linarith only [hU_le]
      _ ≤ t ^ 2 / 16 := by linarith only [ht2]
  have hmul := mul_le_mul_of_nonneg_right hnuU ht0.le
  have hcubic : t ^ 2 / 16 * t ≤ t ^ 3 / 6 := by nlinarith only [show (0 : ℝ) ≤ t ^ 3 by positivity]
  linarith only [hmul, hcubic]

lemma fs_end_im {U R : ℝ} (hR1 : 1 ≤ R) (hUR : kap * |U| ≤ R ^ 2 / 16) :
    R ^ 3 / 12 ≤ (PhU U ((R : ℂ) * d6)).im := by
  have heq : (PhU U ((R : ℂ) * d6)).im = nu * U * R + R ^ 3 / 3 := by
    simpa only [zero_add] using im_ray U R
  rw [heq]
  have hU_le : |U| ≤ R ^ 2 / 16 := (le_mul_of_one_le_left (abs_nonneg U) kap_ge_one).trans hUR
  have h_abs : |nu * U| ≤ R ^ 2 / 16 := by
    rw [abs_mul, abs_of_pos nu_pos]
    exact (mul_le_of_le_one_left (abs_nonneg U) nu_le_one).trans hU_le
  have hmul : -(R ^ 3 / 16) ≤ nu * U * R := by
    have := mul_le_mul_of_nonneg_right (abs_le.1 h_abs).1 (by linarith only [hR1] : 0 ≤ R)
    linarith only [this]
  nlinarith only [hmul, show (0 : ℝ) ≤ R ^ 3 by positivity]

/-! ### `(fs:scalar)`: the three scalar half-cubic identities on `Γ` -/

/-- The finite-contour half-cubic Airy operator `L_U[B]` along a chain `ch` ending at `R e^{iπ/6}`. -/
noncomputable def fsOpCh {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) (B : ℂ → ℂ) : ℝ :=
  -(1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) * ch.intE U (fun w => csr w * B w)).re

/-- `(fs:scalar)`, identity 1: `L_U[1] = K(U) + O(e^{-R³/12})`. -/
theorem fs_scalar_one {R R₀ U : ℝ} (hR0 : 0 < R₀) (hR1 : 1 ≤ R) (hRR : R < R₀)
    (hUR : kap * |U| ≤ R ^ 2 / 16) (ch : Chain3 R₀ ((R : ℂ) * d6)) :
    |fsOpCh ch U (fun _ => 1) - fsK U| ≤ (144 / √π) * Real.exp (-(R ^ 3 / 12)) := by
  have e1 := intE_csr_ray hR0 (by linarith only [hR1]) hRR ch U
  have htail := (Complex.abs_re_le_norm _).trans (ray1_tail hR1 (fs_tail_cond hR1 hUR))
  have hid := CtAiry.airy_id1 U
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hint : ch.intE U (fun w => csr w * (1 : ℂ)) = ch.intE U csr := by simp only [mul_one]
  unfold fsOpCh fsK
  rw [hint, e1, Complex.sub_re]
  have hdiff : -(1 / √π) * ((∫ t in Ioi (0 : ℝ), CtAiry.ray1 U t).re - (∫ t in Ioi R, CtAiry.ray1 U t).re) -
      (-π * (airyAi' U * airyBi U + airyAi U * airyBiDeriv U)) =
      (1 / √π) * (∫ t in Ioi R, CtAiry.ray1 U t).re := by linarith only [hid]
  rw [hdiff, abs_mul, abs_of_pos (one_div_pos.2 hpi)]
  calc (1 / √π) * |(∫ t in Ioi R, CtAiry.ray1 U t).re|
      ≤ (1 / √π) * (144 * Real.exp (-(R ^ 3 / 12))) := mul_le_mul_of_nonneg_left htail (by positivity)
    _ = 144 / √π * Real.exp (-(R ^ 3 / 12)) := by ring

private noncomputable def rayIw (U t : ℝ) : ℂ :=
  Complex.exp (Complex.I * (π / 4 : ℝ)) *
    (csr (0 + (t : ℂ) * d6) * (Complex.I * (0 + (t : ℂ) * d6)) *
      Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6)) * d6)

private lemma d6_eq : d6 = Complex.exp (Complex.I * (π / 6 : ℝ)) := by unfold d6; congr 2

private lemma kap_eq_airy : kap = CtAiry.kap := rfl

private lemma rayIw_eq {t : ℝ} (ht : 0 < t) (U : ℝ) :
    rayIw U t = (Complex.I * CtAiry.al / (kap : ℂ)) * CtAiry.gF (3 / 2) U t := by
  unfold rayIw CtAiry.gF
  have hpt : (0 : ℂ) + (t : ℂ) * d6 = CtAiry.rayPt t := by
    unfold CtAiry.rayPt; rw [d6_eq]; ring
  have hcsr : csr (CtAiry.rayPt t) = CtAiry.rayPt t ^ (1 / 2 : ℂ) := rfl
  have hph : PhU U (CtAiry.rayPt t) = (CtAiry.kap : ℂ) * U * CtAiry.rayPt t + CtAiry.rayPt t ^ 3 / 3 := by
    unfold PhU; rw [kap_eq_airy]
  rw [hpt, hcsr, hph, CtAiry.rayPt_sqrt ht, CtAiry.phase_ray]
  have ht32 : ((t ^ (3 / 2 : ℝ) : ℝ) : ℂ) = ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (t : ℂ) := by
    rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.rpow_add ht, Real.rpow_one]; push_cast; ring
  have hk_ne : (kap : ℂ) ≠ 0 := by exact_mod_cast kap_pos.ne'
  have hk2 : Complex.I * (kap : ℂ) * Complex.exp (Complex.I * (π / 6 : ℝ)) = CtAiry.al := CtAiry.K2
  have hk1 := CtAiry.K1
  unfold CtAiry.rayPt
  rw [ht32, d6_eq]
  calc Complex.exp (Complex.I * (π / 4 : ℝ)) *
        (Complex.exp (Complex.I * (π / 12 : ℝ)) * ((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) *
          (Complex.I * (Complex.exp (Complex.I * (π / 6 : ℝ)) * (t : ℂ))) *
          Complex.exp (CtAiry.al * (U : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3) *
            Complex.exp (Complex.I * (π / 6 : ℝ)))
      = (Complex.exp (Complex.I * (π / 4 : ℝ)) * Complex.exp (Complex.I * (π / 12 : ℝ)) *
          Complex.exp (Complex.I * (π / 6 : ℝ))) * (Complex.I * Complex.exp (Complex.I * (π / 6 : ℝ))) *
          (((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (t : ℂ)) *
          Complex.exp (CtAiry.al * (U : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3) := by ring
    _ = Complex.I * (CtAiry.al / (kap : ℂ)) * (((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (t : ℂ)) *
          Complex.exp (CtAiry.al * (U : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3) := by rw [hk1, ← hk2]; field_simp
    _ = (Complex.I * CtAiry.al / (kap : ℂ)) * (((t ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (t : ℂ) *
          Complex.exp (CtAiry.al * (U : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3)) := by ring

private lemma rayIw_integrable (U : ℝ) : IntegrableOn (rayIw U) (Ioi (0 : ℝ)) := by
  have h := (CtAiry.gF_integrable (p := 3 / 2) (by norm_num) U).const_mul (Complex.I * CtAiry.al / (kap : ℂ))
  exact h.congr ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => (rayIw_eq ht U).symm))

private lemma rayIw_full_val (U : ℝ) :
    -(1 / √π) * (∫ t in Ioi (0 : ℝ), rayIw U t).re = (2 : ℝ) ^ (-(2 / 3) : ℝ) * fsKp U := by
  have hderiv_gI : HasDerivAt (fun u : ℝ => -(1 / √π) * (Complex.I * CtAiry.gI (1 / 2) u).re)
      (-(1 / √π) * (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)).re) U := by
    have hd1 := (CtAiry.hasDerivAt_gI (p := 1 / 2) (by norm_num) U).const_mul Complex.I
    have hre : HasDerivAt (fun u => (Complex.I * CtAiry.gI (1 / 2) u).re)
        (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)).re U := by
      have hc := Complex.reCLM.hasFDerivAt.comp_hasDerivAt U hd1
      simpa only [Function.comp_def, Complex.reCLM_apply,
        show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] using hc
    simpa using hre.const_mul (-(1 / √π))
  have heq : (fun u : ℝ => -(1 / √π) * (Complex.I * CtAiry.gI (1 / 2) u).re) = fsK := by
    ext u; rw [← CtAiry.integral_ray1 u]; exact CtAiry.airy_id1 u
  rw [heq] at hderiv_gI
  have hkp : -(1 / √π) * (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)).re = fsKp U :=
    hderiv_gI.unique (hasDerivAt_fsK U)
  have hint : ∫ t in Ioi (0 : ℝ), rayIw U t = (Complex.I * CtAiry.al / (kap : ℂ)) * CtAiry.gI (3 / 2) U := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => rayIw_eq ht U), MeasureTheory.integral_const_mul]; rfl
  rw [hint]
  have hre_eq : ((Complex.I * CtAiry.al / (kap : ℂ)) * CtAiry.gI (3 / 2) U).re =
      kap⁻¹ * (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)).re := by
    have h1 : (Complex.I * CtAiry.al / (kap : ℂ)) * CtAiry.gI (3 / 2) U =
        ((kap⁻¹ : ℝ) : ℂ) * (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)) := by
      push_cast; ring
    rw [h1, Complex.re_ofReal_mul]
  rw [hre_eq]
  have h23 : kap⁻¹ = (2 : ℝ) ^ (-(2 / 3) : ℝ) := by
    unfold CtSd.kap CtAiry.kap; rw [Real.rpow_neg (by norm_num)]
  rw [h23]
  calc -(1 / √π) * ((2 : ℝ) ^ (-(2 / 3) : ℝ) * (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)).re)
      = (2 : ℝ) ^ (-(2 / 3) : ℝ) * (-(1 / √π) * (Complex.I * (CtAiry.al * CtAiry.gI (3 / 2) U)).re) := by ring
    _ = (2 : ℝ) ^ (-(2 / 3) : ℝ) * fsKp U := by rw [hkp]

/-- `(fs:scalar)`, identity 2: `L_U[i w] = 2^{-2/3} K'(U) + O(e^{-R³/12})`. -/
theorem fs_scalar_Iw {R R₀ U : ℝ} (hR0 : 0 < R₀) (hR1 : 1 ≤ R) (hRR : R < R₀)
    (hUR : kap * |U| ≤ R ^ 2 / 16) (ch : Chain3 R₀ ((R : ℂ) * d6)) :
    |fsOpCh ch U (fun w => Complex.I * w) - (2 : ℝ) ^ (-(2 / 3) : ℝ) * fsKp U| ≤
      (144 / √π) * Real.exp (-(R ^ 3 / 12)) := by
  have hg : Differentiable ℂ (fun w : ℂ => (Complex.I * w) * Complex.exp (Complex.I * PhU U w)) := by
    unfold PhU; fun_prop
  have h1 : ch.intE U (fun w => csr w * (Complex.I * w)) = (chainA (by linarith only [hR1]) hRR).int
      (fun z => csr z * ((Complex.I * z) * Complex.exp (Complex.I * PhU U z))) := by
    have := chain_int_eq_ray hR0 (by linarith only [hR1]) hRR ch hg
    unfold Chain3.intE; simp only [mul_assoc] at this ⊢; exact this
  have hsplit := integral_split_Ioi (rayIw_integrable U) (by linarith only [hR1] : 0 ≤ R)
  have hrayR : ∫ t in (0 : ℝ)..R, rayIw U t = Complex.exp (Complex.I * (π / 4 : ℝ)) *
      ∫ t in (0 : ℝ)..R, csr (0 + (t : ℂ) * d6) * (Complex.I * (0 + (t : ℂ) * d6) *
        Complex.exp (Complex.I * PhU U (0 + (t : ℂ) * d6))) * d6 := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun t _ => by unfold rayIw; ring
  have he_ray : Complex.exp (Complex.I * (π / 4 : ℝ)) * ch.intE U (fun w => csr w * (Complex.I * w)) =
      (∫ t in Ioi (0 : ℝ), rayIw U t) - ∫ t in Ioi R, rayIw U t := by
    rw [h1, chainA_int, hsplit, hrayR]; ring
  have htail_bd : ‖∫ t in Ioi R, rayIw U t‖ ≤ 144 * Real.exp (-(R ^ 3 / 12)) := by
    have htl := tail_le (f := rayIw U) hR1 zero_le_one fun t ht => by
      have ht0 : 0 < t := by linarith only [hR1, ht]
      have ht1 : 1 ≤ t := by linarith only [hR1, ht]
      have h32 : ‖rayIw U t‖ = t ^ (3 / 2 : ℝ) * Real.exp (-(nu * U * t + t ^ 3 / 3)) := by
        rw [rayIw_eq ht0 U, norm_mul, CtAiry.gF, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
        have h_al : ‖Complex.I * CtAiry.al / (kap : ℂ)‖ = 1 := by
          have hk2 : Complex.I * (kap : ℂ) * Complex.exp (Complex.I * (π / 6 : ℝ)) = CtAiry.al := CtAiry.K2
          have hk_ne : (kap : ℂ) ≠ 0 := by exact_mod_cast kap_pos.ne'
          have hkeq : Complex.I * CtAiry.al / (kap : ℂ) = -d6 := by
            rw [d6_eq, ← hk2]
            calc Complex.I * (Complex.I * (kap : ℂ) * Complex.exp (Complex.I * (π / 6 : ℝ))) / (kap : ℂ)
                = (Complex.I * Complex.I) * Complex.exp (Complex.I * (π / 6 : ℝ)) *
                    ((kap : ℂ) / (kap : ℂ)) := by ring
              _ = -Complex.exp (Complex.I * (π / 6 : ℝ)) := by
                    rw [Complex.I_mul_I, div_self hk_ne]; ring
          rw [hkeq, norm_neg, norm_d6]
        have h_exp : ‖Complex.exp (CtAiry.al * (U : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3)‖ =
            Real.exp (-(nu * U * t + t ^ 3 / 3)) := by
          have hph : CtAiry.al * (U : ℂ) * (t : ℂ) - (t : ℂ) ^ 3 / 3 =
              Complex.I * PhU U (0 + (t : ℂ) * d6) := by
            have hpt : CtAiry.rayPt t = 0 + (t : ℂ) * d6 := by unfold CtAiry.rayPt; rw [d6_eq]; ring
            have := CtAiry.phase_ray U t
            rw [hpt] at this
            rw [← this]; unfold PhU; rw [kap_eq_airy]
          rw [hph, norm_exp_I_mul, im_ray]
        rw [h_al, one_mul, h_exp]
      rw [h32]
      have e1 : t ^ (3 / 2 : ℝ) ≤ t ^ 3 := by
        calc t ^ (3 / 2 : ℝ) ≤ t ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num)
          _ = t ^ 3 := by norm_cast
      have e2 : Real.exp (-(nu * U * t + t ^ 3 / 3)) ≤ Real.exp (-(t ^ 3 / 6)) :=
        Real.exp_le_exp.mpr (by linarith only [fs_tail_cond hR1 hUR t ht])
      calc t ^ (3 / 2 : ℝ) * Real.exp (-(nu * U * t + t ^ 3 / 3))
          ≤ t ^ 3 * Real.exp (-(t ^ 3 / 6)) := mul_le_mul e1 e2 (Real.exp_pos _).le (by positivity)
        _ = 1 * (t ^ 3 * Real.exp (-(t ^ 3 / 6))) := by ring
    linarith only [htl]
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  unfold fsOpCh
  rw [he_ray, Complex.sub_re]
  have hdiff : -(1 / √π) * ((∫ t in Ioi (0 : ℝ), rayIw U t).re - (∫ t in Ioi R, rayIw U t).re) -
      (2 : ℝ) ^ (-(2 / 3) : ℝ) * fsKp U = (1 / √π) * (∫ t in Ioi R, rayIw U t).re := by
    linarith only [rayIw_full_val U]
  rw [hdiff, abs_mul, abs_of_pos (one_div_pos.2 hpi)]
  calc (1 / √π) * |(∫ t in Ioi R, rayIw U t).re|
      ≤ (1 / √π) * (144 * Real.exp (-(R ^ 3 / 12))) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans htail_bd) (by positivity)
    _ = 144 / √π * Real.exp (-(R ^ 3 / 12)) := by ring

private lemma lineInt_const_mul (z0 d : ℂ) (a b : ℝ) (k : ℂ) (f : ℂ → ℂ) :
    lineInt z0 d a b (fun z => k * f z) = k * lineInt z0 d a b f := by
  unfold lineInt; rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_congr fun t _ => by ring

private lemma Chain3.intE_const_mul {R₀ : ℝ} {p : ℂ} (ch : Chain3 R₀ p) (U : ℝ) (k : ℂ) (f : ℂ → ℂ) :
    ch.intE U (fun w => k * f w) = k * ch.intE U f := by
  unfold Chain3.intE Chain3.int
  have e1 : (fun z => k * f z * Complex.exp (Complex.I * PhU U z)) =
      fun z => k * (f z * Complex.exp (Complex.I * PhU U z)) := funext fun z => by ring
  rw [e1, lineInt_const_mul, lineInt_const_mul, lineInt_const_mul]; ring

/-- `(fs:scalar)`, identity 3: `L_U[i / w] = 2^{2/3} π J(U) + O(√R e^{-R³/12})`. -/
theorem fs_scalar_Idiv {R R₀ U : ℝ} (hR0 : 0 < R₀) (hR1 : 1 ≤ R) (hRR : R < R₀)
    (hUR : kap * |U| ≤ R ^ 2 / 16) (ch : Chain3 R₀ ((R : ℂ) * d6)) :
    |fsOpCh ch U (fun w => Complex.I / w) - (2 : ℝ) ^ (2 / 3 : ℝ) * π * fsJ U| ≤
      (578 * Real.sqrt R / √π) * Real.exp (-(R ^ 3 / 12)) := by
  have hibp := ch.ibp U (G := fun _ => (1 : ℂ)) (G' := fun _ => (0 : ℂ)) zero_le_one le_rfl
    (fun w _ => hasDerivAt_const w (1 : ℂ)) continuousOn_const
    (fun _ _ => by simp) (fun _ _ => by simp)
  have e_fun : (fun w => csr w * (Complex.I / w)) =
      fun w => (2 * Complex.I) * (csr w / (2 * w) * 1 + csr w * 0) := by
    ext w
    by_cases hw : w = 0
    · subst hw; simp [csr_zero]
    · simp only [mul_one, mul_zero, add_zero]; field_simp
  have hid_ch : ch.intE U (fun w => csr w * (Complex.I / w)) =
      2 * ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2)) +
      2 * Complex.I * (csr ((R : ℂ) * d6) * Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))) := by
    rw [e_fun, ch.intE_const_mul]
    have h1 : ch.intE U (fun w => csr w / (2 * w) * 1 + csr w * 0) =
        csr ((R : ℂ) * d6) * 1 * Complex.exp (Complex.I * PhU U ((R : ℂ) * d6)) -
        Complex.I * ch.intE U (fun w => csr w * 1 * ((kap : ℂ) * U + w ^ 2)) := by
      linear_combination hibp
    rw [h1]; simp only [mul_one]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-2 * ch.intE U (fun w => csr w * ((kap : ℂ) * U + w ^ 2))) * hI
  have e2 := intE_csrW_ray hR0 (by linarith only [hR1]) hRR ch U
  have hkU : kap * |U| ≤ R ^ 2 := by nlinarith only [hUR, sq_nonneg R]
  have htail2 := (Complex.abs_re_le_norm _).trans (ray2_tail hR1 (fs_tail_cond hR1 hUR) hkU)
  have hid2 := CtAiry.airy_id2 U
  set rem := Complex.exp (Complex.I * (π / 4 : ℝ)) *
      (2 * Complex.I * (csr ((R : ℂ) * d6) * Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))))
  have hrem_bd : ‖rem‖ ≤ 2 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := by
    have hcsr_n : ‖csr ((R : ℂ) * d6)‖ = Real.sqrt R := by
      rw [norm_csr, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith only [hR1]), norm_d6, mul_one]
    have hexp_n : ‖Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))‖ ≤ Real.exp (-(R ^ 3 / 12)) := by
      rw [norm_exp_I_mul]; exact Real.exp_le_exp.mpr (by linarith only [fs_end_im hR1 hUR])
    have h2I : ‖(2 : ℂ) * Complex.I‖ = 2 := by rw [norm_mul, Complex.norm_I]; simp
    unfold rem
    rw [norm_mul, norm_phase_pi4, one_mul, norm_mul, h2I, norm_mul, hcsr_n]
    calc 2 * (Real.sqrt R * ‖Complex.exp (Complex.I * PhU U ((R : ℂ) * d6))‖)
        ≤ 2 * (Real.sqrt R * Real.exp (-(R ^ 3 / 12))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp_n (Real.sqrt_nonneg _)) (by norm_num)
      _ = 2 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := by ring
  have hpow2 : 2 * (2 : ℝ) ^ (-(1 / 3) : ℝ) = (2 : ℝ) ^ (2 / 3 : ℝ) := by
    calc (2 : ℝ) * (2 : ℝ) ^ (-(1 / 3) : ℝ) = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(1 / 3) : ℝ) := by rw [Real.rpow_one]
      _ = (2 : ℝ) ^ (1 + -(1 / 3 : ℝ)) := (Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (-(1 / 3))).symm
      _ = (2 : ℝ) ^ (2 / 3 : ℝ) := by norm_num
  have hpi : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  unfold fsOpCh fsJ
  have hsplit : Complex.exp (Complex.I * (π / 4 : ℝ)) * ch.intE U (fun w => csr w * (Complex.I / w)) =
      2 * ((∫ t in Ioi (0 : ℝ), CtAiry.ray2 U t) - ∫ t in Ioi R, CtAiry.ray2 U t) + rem := by
    rw [hid_ch]; unfold rem; linear_combination 2 * e2
  rw [hsplit]
  simp only [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, Complex.add_re,
    Complex.re_ofReal_mul, Complex.sub_re]
  have hdiff : -(1 / √π) * (2 * ((∫ t in Ioi (0 : ℝ), CtAiry.ray2 U t).re - (∫ t in Ioi R, CtAiry.ray2 U t).re) + rem.re) -
      (2 : ℝ) ^ (2 / 3 : ℝ) * π * (airyAi U * airyBi U) =
      (1 / √π) * (2 * (∫ t in Ioi R, CtAiry.ray2 U t).re - rem.re) := by
    rw [← hpow2]; linarith only [hid2]
  rw [hdiff, abs_mul, abs_of_pos (one_div_pos.2 hpi)]
  have hRsqrt : 1 ≤ Real.sqrt R := Real.one_le_sqrt.2 hR1
  have h_in : |2 * (∫ t in Ioi R, CtAiry.ray2 U t).re - rem.re| ≤ 578 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := by
    have h1 : |(∫ t in Ioi R, CtAiry.ray2 U t).re| ≤ 288 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := by
      refine htail2.trans ?_
      have := mul_le_mul_of_nonneg_left hRsqrt (by positivity : (0 : ℝ) ≤ 288 * Real.exp (-(R ^ 3 / 12)))
      linarith only [this]
    have h2 : |rem.re| ≤ 2 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := (Complex.abs_re_le_norm _).trans hrem_bd
    calc |2 * (∫ t in Ioi R, CtAiry.ray2 U t).re - rem.re|
        ≤ 2 * |(∫ t in Ioi R, CtAiry.ray2 U t).re| + |rem.re| := by
          have := abs_sub (2 * (∫ t in Ioi R, CtAiry.ray2 U t).re) rem.re
          rwa [abs_mul, abs_two] at this
      _ ≤ 2 * (288 * Real.sqrt R * Real.exp (-(R ^ 3 / 12))) + 2 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := by
          linarith only [h1, h2]
      _ = 578 * Real.sqrt R * Real.exp (-(R ^ 3 / 12)) := by ring
  calc (1 / √π) * |2 * (∫ t in Ioi R, CtAiry.ray2 U t).re - rem.re|
      ≤ (1 / √π) * (578 * Real.sqrt R * Real.exp (-(R ^ 3 / 12))) :=
        mul_le_mul_of_nonneg_left h_in (by positivity)
    _ = 578 * Real.sqrt R / √π * Real.exp (-(R ^ 3 / 12)) := by ring

/-! ### `(fs:pairing)`: Airy upper-semicircle pairing for `J, K, K'` -/

private lemma circleMap_upper_im {R θ : ℝ} (hR : 0 < R) (hθ : θ ∈ Icc (0 : ℝ) π) :
    0 ≤ (circleMap 0 R θ).im := by
  simp only [circleMap, zero_add, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re, zero_mul, add_zero]
  exact mul_nonneg hR.le (Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2)

private lemma fs_halfDisc_im_bound {F K : ℂ → ℂ} {ρ R B : ℝ} (hR : 0 < R) (hRρ : R < ρ)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hK_cont : ContinuousOn K (closedHalfDisc R))
    (hK_diff : DifferentiableOn ℂ K (openHalfDisc R))
    (hK_bound : ∀ θ ∈ Icc (0 : ℝ) π, ‖K (circleMap 0 R θ)‖ ≤ B * ‖airyUpE (circleMap 0 R θ)‖) :
    |∫ t in (-R)..R, (F (t : ℂ)).re * (K (t : ℂ)).im| ≤
      B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
  have hsub_closed : closedHalfDisc R ⊆ ball 0 ρ := fun z hz => by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hz.1 hRρ
  have hsub_open : openHalfDisc R ⊆ ball 0 ρ := fun z hz => by
    rw [mem_ball_zero_iff]; exact lt_trans hz.1 hRρ
  have hFK_cont : ContinuousOn (fun z => F z * K z) (closedHalfDisc R) :=
    (hF_diff.continuousOn.mono hsub_closed).mul hK_cont
  have hFK_diff : DifferentiableOn ℂ (fun z => F z * K z) (openHalfDisc R) :=
    (hF_diff.mono hsub_open).mul hK_diff
  have hcauchy := halfDisc_cauchy hR hFK_cont hFK_diff
  have him : (∫ t in (-R)..R, (F (t : ℂ) * K (t : ℂ))).im =
      -(Complex.I * ∫ y in (0 : ℝ)..π, F (R * Complex.exp (y * Complex.I)) * K (R * Complex.exp (y * Complex.I)) *
        (R * Complex.exp (y * Complex.I))).im := by
    have hsum := congrArg Complex.im hcauchy
    simp only [Complex.add_im, Complex.zero_im] at hsum; linarith only [hsum]
  have him_eq : ∫ t in (-R)..R, (F (t : ℂ)).re * (K (t : ℂ)).im =
      (∫ t in (-R)..R, (F (t : ℂ) * K (t : ℂ))).im := by
    have hre_f : ContinuousOn (fun t : ℝ => F (t : ℂ) * K (t : ℂ)) (uIcc (-R) R) :=
      hFK_cont.comp Complex.continuous_ofReal.continuousOn fun t ht => by
        rw [uIcc_of_le (by linarith only [hR])] at ht
        exact ⟨by simpa [Complex.norm_real, Real.norm_eq_abs] using abs_le.2 ht, by simp⟩
    have him1 : (∫ t in (-R)..R, F (t : ℂ) * K (t : ℂ)).im = ∫ t in (-R)..R, (F (t : ℂ) * K (t : ℂ)).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hre_f.intervalIntegrable).symm
    rw [him1]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith only [hR])] at ht
    simp [Complex.mul_im, hF_real t (abs_le.2 ht)]
  rw [him_eq, him, abs_neg]
  have hint_bd : ‖Complex.I * ∫ y in (0 : ℝ)..π, F (R * Complex.exp (y * Complex.I)) *
      K (R * Complex.exp (y * Complex.I)) * (R * Complex.exp (y * Complex.I))‖ ≤
      ∫ y in (0 : ℝ)..π, R * ‖F (circleMap 0 R y)‖ * ‖K (circleMap 0 R y)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
    refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans_eq ?_
    refine intervalIntegral.integral_congr fun y _ => ?_
    have hcm : (R : ℂ) * Complex.exp (y * Complex.I) = circleMap 0 R y := by simp [circleMap, mul_comm]
    rw [hcm, norm_mul, norm_mul, show ‖circleMap 0 R y‖ = R by simp [circleMap, abs_of_pos hR]]; ring
  have hmaps : MapsTo (circleMap 0 R) (Icc 0 π) (closedHalfDisc R) := fun θ hθ =>
    ⟨by simp [circleMap, abs_of_pos hR], circleMap_upper_im hR hθ⟩
  have hcF : ContinuousOn (fun θ => F (circleMap 0 R θ)) (Icc 0 π) :=
    (hF_diff.continuousOn.mono hsub_closed).comp (continuous_circleMap 0 R).continuousOn hmaps
  have hcK : ContinuousOn (fun θ => K (circleMap 0 R θ)) (Icc 0 π) :=
    hK_cont.comp (continuous_circleMap 0 R).continuousOn hmaps
  have hcE : ContinuousOn (fun θ => airyUpE (circleMap 0 R θ)) (Icc 0 π) :=
    continuousOn_airyUpE.comp (continuous_circleMap 0 R).continuousOn (fun θ hθ => (hmaps hθ).2)
  have hRHS_cont : ContinuousOn (fun θ => R * ‖F (circleMap 0 R θ)‖ * ‖K (circleMap 0 R θ)‖) (Icc 0 π) :=
    (continuousOn_const.mul hcF.norm).mul hcK.norm
  have hB_cont : ContinuousOn (fun θ => B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖)) (Icc 0 π) :=
    continuousOn_const.mul ((continuousOn_const.mul hcF.norm).mul hcE.norm)
  have hmono : ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖K (circleMap 0 R θ)‖ ≤
      ∫ θ in (0 : ℝ)..π, B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) :=
    intervalIntegral.integral_mono_on Real.pi_pos.le
      (hRHS_cont.intervalIntegrable_of_Icc Real.pi_pos.le)
      (hB_cont.intervalIntegrable_of_Icc Real.pi_pos.le) fun θ hθ => by
      have hK := hK_bound θ hθ
      have hRF0 : 0 ≤ R * ‖F (circleMap 0 R θ)‖ := mul_nonneg hR.le (norm_nonneg _)
      calc R * ‖F (circleMap 0 R θ)‖ * ‖K (circleMap 0 R θ)‖
          ≤ R * ‖F (circleMap 0 R θ)‖ * (B * ‖airyUpE (circleMap 0 R θ)‖) :=
            mul_le_mul_of_nonneg_left hK hRF0
        _ = B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) := by ring
  have hcongr_E : ∫ θ in (0 : ℝ)..π, B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) =
      B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
    calc ∫ θ in (0 : ℝ)..π, B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖)
        = B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ :=
          intervalIntegral.integral_const_mul B _
      _ = B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
          congr 1
          refine intervalIntegral.integral_congr fun θ hθ => ?_
          rw [uIcc_of_le Real.pi_pos.le] at hθ
          rw [norm_airyUpE (circleMap_upper_im hR hθ), div_eq_mul_inv]
  calc |(Complex.I * ∫ y in (0 : ℝ)..π, F (R * Complex.exp (y * Complex.I)) *
          K (R * Complex.exp (y * Complex.I)) * (R * Complex.exp (y * Complex.I))).im|
      ≤ ‖Complex.I * ∫ y in (0 : ℝ)..π, F (R * Complex.exp (y * Complex.I)) *
          K (R * Complex.exp (y * Complex.I)) * (R * Complex.exp (y * Complex.I))‖ := Complex.abs_im_le_norm _
    _ ≤ ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖K (circleMap 0 R θ)‖ := hint_bd
    _ ≤ ∫ θ in (0 : ℝ)..π, B * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) := hmono
    _ = B * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := hcongr_E

private lemma fs_pairing_core {F d K : ℂ → ℂ} {g : ℝ → ℝ} {ρ R D B Cg : ℝ}
    (hR : 0 < R) (hRρ : R < ρ) (hCg : Cg ≠ 0) (_hD : 0 ≤ D)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ)) (hd_diff : DifferentiableOn ℂ d (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hd_real : ∀ x : ℝ, |x| ≤ R → (d (x : ℂ)).im = 0)
    (hd_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖d (circleMap 0 R θ)‖ ≤ D)
    (hK_cont : ContinuousOn K (closedHalfDisc R)) (hK_diff : DifferentiableOn ℂ K (openHalfDisc R))
    (hK_bound : ∀ θ ∈ Icc (0 : ℝ) π, ‖K (circleMap 0 R θ)‖ ≤ B * ‖airyUpE (circleMap 0 R θ)‖)
    (hK_im : ∀ x : ℝ, (K (x : ℂ)).im = Cg * g x) :
    |∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * g x| ≤
      (B / |Cg|) * D * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
  have him := fs_halfDisc_im_bound (F := fun u => F u * d u) (K := K) hR hRρ
    (hF_diff.mul hd_diff) (fun x hx => by simp [Complex.mul_im, hF_real x hx, hd_real x hx])
    hK_cont hK_diff hK_bound
  have heq : ∫ x in (-R)..R, (F (x : ℂ) * d (x : ℂ)).re * (K (x : ℂ)).im =
      Cg * ∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * g x := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (by linarith only [hR])] at hx
    have hx' : |x| ≤ R := abs_le.2 hx
    rw [hK_im x, Complex.mul_re, hF_real x hx', hd_real x hx']; ring
  have hsub : closedHalfDisc R ⊆ ball 0 ρ := fun z hz => by
    rw [mem_ball_zero_iff]; exact lt_of_le_of_lt hz.1 hRρ
  have hmaps : MapsTo (circleMap 0 R) (Icc 0 π) (closedHalfDisc R) := fun θ hθ =>
    ⟨by simp [circleMap, abs_of_pos hR], circleMap_upper_im hR hθ⟩
  have hcE := continuousOn_airyUpE.comp (continuous_circleMap 0 R).continuousOn (fun θ hθ => (hmaps hθ).2)
  have hc1 := (hF_diff.continuousOn.mono hsub).comp (continuous_circleMap 0 R).continuousOn hmaps
  have hc2 := ((hF_diff.mul hd_diff).continuousOn.mono hsub).comp (continuous_circleMap 0 R).continuousOn hmaps
  have hcirc_E : ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ) * d (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ ≤
      D * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on Real.pi_pos.le
      ((continuousOn_const.mul hc2.norm).mul hcE.norm |>.intervalIntegrable_of_Icc Real.pi_pos.le)
      (((continuousOn_const.mul hc1.norm).mul hcE.norm).const_mul D |>.intervalIntegrable_of_Icc Real.pi_pos.le)
      fun θ hθ => ?_
    rw [norm_mul]
    have hD_le := hd_bd θ hθ
    have hR0 : 0 ≤ R := hR.le
    calc R * (‖F (circleMap 0 R θ)‖ * ‖d (circleMap 0 R θ)‖) * ‖airyUpE (circleMap 0 R θ)‖
        ≤ R * (‖F (circleMap 0 R θ)‖ * D) * ‖airyUpE (circleMap 0 R θ)‖ := by gcongr
      _ = D * (R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖) := by ring
  have hcirc : ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ) * d (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) ≤
      D * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
    have h1 : ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ) * d (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) =
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ) * d (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ :=
      intervalIntegral.integral_congr fun θ hθ => by
        rw [uIcc_of_le Real.pi_pos.le] at hθ
        rw [norm_airyUpE (circleMap_upper_im hR hθ), div_eq_mul_inv]
    have h2 : ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) =
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ * ‖airyUpE (circleMap 0 R θ)‖ :=
      intervalIntegral.integral_congr fun θ hθ => by
        rw [uIcc_of_le Real.pi_pos.le] at hθ
        rw [norm_airyUpE (circleMap_upper_im hR hθ), div_eq_mul_inv]
    rw [h1, h2]; exact hcirc_E
  have hB0 : 0 ≤ B := by
    have hK0 := norm_nonneg (K (circleMap 0 R 0))
    have hK_bd := hK_bound 0 ⟨le_rfl, Real.pi_pos.le⟩
    have hE0 : 0 < ‖airyUpE (circleMap 0 R 0)‖ := by
      rw [norm_airyUpE (hmaps ⟨le_rfl, Real.pi_pos.le⟩).2]; exact inv_pos.2 (airyEnv_pos _)
    exact nonneg_of_mul_nonneg_left (hK0.trans hK_bd) hE0
  rw [heq, abs_mul] at him
  have h1 := him.trans (mul_le_mul_of_nonneg_left hcirc hB0)
  have hCg0 : 0 < |Cg| := abs_pos.2 hCg
  have hmul := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hCg0.le)
  calc |∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * g x|
      = |Cg|⁻¹ * (|Cg| * |∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * g x|) := by field_simp
    _ ≤ |Cg|⁻¹ * (B * (D * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ))) := hmul
    _ = (B / |Cg|) * D * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by ring

private lemma norm_hplus_sq_le {u : ℂ} (hu : 0 ≤ u.im) (hR : 1 ≤ ‖u‖) :
    ‖hplus u ^ 2‖ ≤ (5 / π) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by
  have h0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hR; linarith
  have hsq := hplus_sq_asymp hu h0 hR
  have hnorm_u : 0 < ‖u‖ := lt_of_lt_of_le one_pos hR
  have hE : ‖airyUpE u‖ = Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) := by
    rw [norm_airyUpE hu, airyEnv]
    have e : -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re = -((4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) := by ring
    rw [e, Real.exp_neg, inv_inv]
  have hT1 : ‖CtAiryHplus.T1 u‖ = (1 / π) * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by
    unfold CtAiryHplus.T1
    have h43re : ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)).re = (4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      simp [Complex.mul_re]
    rw [norm_mul, norm_mul, norm_neg, norm_div, norm_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, norm_inv, norm_cpow_half, Complex.norm_exp,
      h43re, Real.sqrt_eq_rpow, Real.rpow_neg hnorm_u.le, hE]
  have h4t : 4 * ‖u‖ ^ (-(3 / 2 : ℝ)) ≤ 4 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num : -(3 / 2 : ℝ) ≤ 0); linarith
  have hsqrt : (Real.sqrt ‖u‖)⁻¹ = ‖u‖ ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hnorm_u.le]
  rw [← hE, hsqrt] at hsq
  calc ‖hplus u ^ 2‖ ≤ ‖hplus u ^ 2 - CtAiryHplus.T1 u‖ + ‖CtAiryHplus.T1 u‖ := by
        calc ‖hplus u ^ 2‖ = ‖(hplus u ^ 2 - CtAiryHplus.T1 u) + CtAiryHplus.T1 u‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
    _ ≤ 4 * (1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) +
        (1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by
        have hpos : 0 ≤ 1 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by positivity
        nlinarith [hsq, hT1, mul_le_mul_of_nonneg_right h4t hpos]
    _ = 5 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖ := by ring

private lemma norm_hplus_sq_deriv_le {u : ℂ} (hu : 0 ≤ u.im) (hR : 1 ≤ ‖u‖) :
    ‖2 * hplus u * hplus' u‖ ≤ (24 / π) * ‖airyUpE u‖ := by
  have h0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hR; linarith
  have hd := hplus_sq_deriv_asymp hu h0 hR
  have hE : ‖airyUpE u‖ = Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) := by
    rw [norm_airyUpE hu, airyEnv]
    have e : -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re = -((4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) := by ring
    rw [e, Real.exp_neg, inv_inv]
  have hT2 : ‖CtAiryHplus.T2 u‖ = (2 / π) * ‖airyUpE u‖ := by
    unfold CtAiryHplus.T2
    have h43re : ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)).re = (4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re := by
      simp [Complex.mul_re]
    rw [norm_mul, norm_neg, norm_div, show ‖(2 : ℂ)‖ = 2 by simp, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_exp, h43re, hE]
  have h11t : 11 * ‖u‖ ^ (-(3 / 2 : ℝ)) ≤ 11 := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num : -(3 / 2 : ℝ) ≤ 0); linarith
  rw [← hE] at hd
  calc ‖2 * hplus u * hplus' u‖ ≤ ‖2 * hplus u * hplus' u - CtAiryHplus.T2 u‖ + ‖CtAiryHplus.T2 u‖ := by
        calc ‖2 * hplus u * hplus' u‖ = ‖(2 * hplus u * hplus' u - CtAiryHplus.T2 u) + CtAiryHplus.T2 u‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
    _ ≤ 11 * (2 / π * ‖airyUpE u‖) + (2 / π * ‖airyUpE u‖) := by
        have hpos : 0 ≤ 2 / π * ‖airyUpE u‖ := by positivity
        nlinarith [hd, hT2, mul_le_mul_of_nonneg_right h11t hpos]
    _ = 24 / π * ‖airyUpE u‖ := by ring

private lemma norm_hplus_deriv_sq_le {u : ℂ} (hu : 0 ≤ u.im) (hR : 1 ≤ ‖u‖) :
    ‖hplus' u‖ ^ 2 ≤ (27 / π) * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ := by
  have h0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hR; linarith
  obtain ⟨_, hln⟩ := lead_facts hu h0
  obtain ⟨_, hb2⟩ := sector_bounds hu h0 hR
  have hR_pos : 0 < ‖u‖ := lt_of_lt_of_le one_pos hR
  have ht1 : ‖u‖ ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  have hD_le : ‖deriv airyAiC (airyOmega ^ 2 * u)‖ ≤ (51 / 10) * ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ := by
    have ha : ‖deriv airyAiC (airyOmega ^ 2 * u)‖ ≤
        ‖deriv airyAiC (airyOmega ^ 2 * u) - airyAiDerivLead (airyOmega ^ 2 * u)‖ +
          ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ := by
      calc _ = ‖(deriv airyAiC (airyOmega ^ 2 * u) - airyAiDerivLead (airyOmega ^ 2 * u)) +
            airyAiDerivLead (airyOmega ^ 2 * u)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h41 : 41 / 10 * ‖u‖ ^ (-(3 / 2 : ℝ)) * ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ ≤
        41 / 10 * ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht1 (by norm_num : (0 : ℝ) ≤ 41 / 10))
        (norm_nonneg (airyAiDerivLead (airyOmega ^ 2 * u)))
      linarith
    linarith only [ha, hb2, h41]
  have hDn : ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ = Real.sqrt ‖u‖ * ‖airyAiLead (airyOmega ^ 2 * u)‖ := by
    unfold airyAiDerivLead
    rw [norm_neg, norm_mul, sqrt_rot hu h0, norm_mul, norm_chi, one_mul, norm_cpow_half]
  have hE : ‖airyUpE u‖ = Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) := by
    rw [norm_airyUpE hu, airyEnv]
    have e : -(4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re = -((4 / 3 : ℝ) * (u ^ (3 / 2 : ℂ)).re) := by ring
    rw [e, Real.exp_neg, inv_inv]
  have hD_sq : ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ ^ 2 = ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ / (4 * π) := by
    rw [hDn, mul_pow, Real.sq_sqrt hR_pos.le, hln, ← hE]
    have hpi : 0 < π := Real.pi_pos
    have hsq : Real.sqrt ‖u‖ = ‖u‖ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
    have hsq2 : ‖u‖ = ‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hR_pos]; norm_num
    rw [hsq]
    calc ‖u‖ * (‖airyUpE u‖ / (4 * π * ‖u‖ ^ (1 / 2 : ℝ)))
        = (‖u‖ ^ (1 / 2 : ℝ) * ‖u‖ ^ (1 / 2 : ℝ)) * (‖airyUpE u‖ / (4 * π * ‖u‖ ^ (1 / 2 : ℝ))) := by rw [← hsq2]
      _ = ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ / (4 * π) := by
          have : ‖u‖ ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hR_pos _).ne'
          field_simp
  have hp_norm : ‖hplus' u‖ = 2 * ‖deriv airyAiC (airyOmega ^ 2 * u)‖ := by
    unfold hplus'
    rw [norm_mul, norm_mul, norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, Complex.norm_I,
      mul_one, Complex.norm_conj, norm_airyEps, mul_one, norm_airyOmega_sq, mul_one]
  rw [hp_norm, mul_pow]
  have hsq1 : ‖deriv airyAiC (airyOmega ^ 2 * u)‖ ^ 2 ≤
      (51 / 10) ^ 2 * ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ ^ 2 := by
    have := mul_self_le_mul_self (norm_nonneg _) hD_le
    nlinarith only [this]
  have hpi : 0 < π := Real.pi_pos
  have h27 : (51 / 10 : ℝ) ^ 2 / π ≤ 27 / π := div_le_div_of_nonneg_right (by norm_num) hpi.le
  calc 2 ^ 2 * ‖deriv airyAiC (airyOmega ^ 2 * u)‖ ^ 2
      ≤ 4 * ((51 / 10) ^ 2 * (‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ / (4 * π))) := by nlinarith only [hsq1, hD_sq]
    _ = ((51 / 10) ^ 2 / π) * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ := by ring
    _ ≤ (27 / π) * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ := by
        have hpos : 0 ≤ ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ := by positivity
        nlinarith only [h27, hpos]

private noncomputable def hplusSqDeriv2 (u : ℂ) : ℂ :=
  2 * hplus' u ^ 2 + 2 * u * hplus u ^ 2

private lemma hplus_holo_all :
    Differentiable ℂ (fun u : ℂ => hplus u ^ 2) ∧
    Differentiable ℂ (fun u : ℂ => 2 * hplus u * hplus' u) ∧
    Differentiable ℂ hplusSqDeriv2 := by
  have hc1 : Differentiable ℂ hplus := fun u => (hasDerivAt_hplus u).differentiableAt
  have hc2 : Differentiable ℂ hplus' := by
    have ha : Differentiable ℂ (deriv airyAiC) := by
      have : AnalyticOnNhd ℂ airyAiC univ := fun z _ => differentiable_airyAiC.analyticAt z
      exact fun z => (this z (mem_univ z)).deriv.differentiableAt
    unfold hplus'
    exact (ha.comp (differentiable_const _ |>.mul differentiable_id)).const_mul _
  exact ⟨hc1.pow 2, (hc1.const_mul 2).mul hc2,
    ((hc2.pow 2).const_mul 2).add ((differentiable_id.const_mul 2).mul (hc1.pow 2))⟩

private lemma norm_hplus_sq_deriv2_le {u : ℂ} (hu : 0 ≤ u.im) (hR : 1 ≤ ‖u‖) :
    ‖hplusSqDeriv2 u‖ ≤ (64 / π) * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ := by
  have h1 := norm_hplus_deriv_sq_le hu hR
  have h2 := norm_hplus_sq_le hu hR
  have hR_pos : 0 < ‖u‖ := lt_of_lt_of_le one_pos hR
  have hu_pow : ‖u‖ * ‖u‖ ^ (-(1 / 2 : ℝ)) = ‖u‖ ^ (1 / 2 : ℝ) := by
    calc ‖u‖ * ‖u‖ ^ (-(1 / 2 : ℝ))
        = ‖u‖ ^ (1 : ℝ) * ‖u‖ ^ (-(1 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = ‖u‖ ^ (1 + -(1 / 2 : ℝ)) := (Real.rpow_add hR_pos 1 (-(1 / 2))).symm
      _ = ‖u‖ ^ (1 / 2 : ℝ) := by norm_num
  unfold hplusSqDeriv2
  calc ‖2 * hplus' u ^ 2 + 2 * u * hplus u ^ 2‖
      ≤ 2 * ‖hplus' u‖ ^ 2 + 2 * ‖u‖ * ‖hplus u ^ 2‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by simp, norm_pow]
        · rw [norm_mul, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
    _ ≤ 2 * (27 / π * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖) +
        2 * ‖u‖ * (5 / π * ‖u‖ ^ (-(1 / 2 : ℝ)) * ‖airyUpE u‖) := by gcongr
    _ = 54 / π * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ +
        10 / π * (‖u‖ * ‖u‖ ^ (-(1 / 2 : ℝ))) * ‖airyUpE u‖ := by ring
    _ = 64 / π * ‖u‖ ^ (1 / 2 : ℝ) * ‖airyUpE u‖ := by rw [hu_pow]; ring

/-- **`(fs:pairing)`, `j = 0`**: `|∫_{-R}^R F d J| ≤ (5/(2π)) ‖d‖_∞ R^{-1/2} η_half`. -/
theorem fs_pairing_0 {F d : ℂ → ℂ} {ρ R D : ℝ} (hR : 1 ≤ R) (hRρ : R < ρ)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ)) (hd_diff : DifferentiableOn ℂ d (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hd_real : ∀ x : ℝ, |x| ≤ R → (d (x : ℂ)).im = 0)
    (hd_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖d (circleMap 0 R θ)‖ ≤ D) (hD : 0 ≤ D) :
    |∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * fsJ x| ≤
      (5 / (2 * π)) * D * R ^ (-(1 / 2 : ℝ)) *
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
  have hR0 : 0 < R := by linarith only [hR]
  have h := fs_pairing_core (K := fun u => hplus u ^ 2) (g := fsJ)
    (B := 5 / π * R ^ (-(1 / 2 : ℝ))) (Cg := 2) hR0 hRρ two_ne_zero hD
    hF_diff hd_diff hF_real hd_real hd_bd
    hplus_holo_all.1.continuous.continuousOn hplus_holo_all.1.differentiableOn
    (fun θ hθ => by
      have hnorm : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR0]
      simpa [hnorm] using norm_hplus_sq_le (circleMap_upper_im hR0 hθ) (by rw [hnorm]; exact hR))
    (fun x => by rw [hplus_sq_im x]; unfold fsJ; ring)
  refine h.trans_eq ?_
  rw [abs_two]; ring

/-- **`(fs:pairing)`, `j = 1`**: `|∫_{-R}^R F d K| ≤ 12 ‖d‖_∞ η_half`. -/
theorem fs_pairing_1 {F d : ℂ → ℂ} {ρ R D : ℝ} (hR : 1 ≤ R) (hRρ : R < ρ)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ)) (hd_diff : DifferentiableOn ℂ d (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hd_real : ∀ x : ℝ, |x| ≤ R → (d (x : ℂ)).im = 0)
    (hd_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖d (circleMap 0 R θ)‖ ≤ D) (hD : 0 ≤ D) :
    |∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * fsK x| ≤
      12 * D * ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
  have hR0 : 0 < R := by linarith only [hR]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have h := fs_pairing_core (K := fun u => 2 * hplus u * hplus' u) (g := fsK)
    (B := 24 / π) (Cg := -(2 / π)) hR0 hRρ (by simp [hpi]) hD
    hF_diff hd_diff hF_real hd_real hd_bd
    hplus_holo_all.2.1.continuous.continuousOn hplus_holo_all.2.1.differentiableOn
    (fun θ hθ => by
      have hnorm : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR0]
      exact norm_hplus_sq_deriv_le (circleMap_upper_im hR0 hθ) (by rw [hnorm]; exact hR))
    (fun x => by
      rw [hplus_real, hplus'_real]; unfold fsK
      simp only [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, Complex.mul_im, Complex.mul_re,
        Complex.add_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp; ring)
  refine h.trans_eq ?_
  rw [abs_neg, abs_of_pos (div_pos two_pos Real.pi_pos)]
  field_simp; ring

/-- **`(fs:pairing)`, `j = 2`**: `|∫_{-R}^R F d K'| ≤ 32 ‖d‖_∞ R^{1/2} η_half`. -/
theorem fs_pairing_2 {F d : ℂ → ℂ} {ρ R D : ℝ} (hR : 1 ≤ R) (hRρ : R < ρ)
    (hF_diff : DifferentiableOn ℂ F (ball 0 ρ)) (hd_diff : DifferentiableOn ℂ d (ball 0 ρ))
    (hF_real : ∀ x : ℝ, |x| ≤ R → (F (x : ℂ)).im = 0)
    (hd_real : ∀ x : ℝ, |x| ≤ R → (d (x : ℂ)).im = 0)
    (hd_bd : ∀ θ ∈ Icc (0 : ℝ) π, ‖d (circleMap 0 R θ)‖ ≤ D) (hD : 0 ≤ D) :
    |∫ x in (-R)..R, (F (x : ℂ)).re * (d (x : ℂ)).re * fsKp x| ≤
      32 * D * R ^ (1 / 2 : ℝ) *
        ∫ θ in (0 : ℝ)..π, R * ‖F (circleMap 0 R θ)‖ / airyEnv (circleMap 0 R θ) := by
  have hR0 : 0 < R := by linarith only [hR]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  have h := fs_pairing_core (K := hplusSqDeriv2) (g := fsKp)
    (B := 64 / π * R ^ (1 / 2 : ℝ)) (Cg := -(2 / π)) hR0 hRρ (by simp [hpi]) hD
    hF_diff hd_diff hF_real hd_real hd_bd
    hplus_holo_all.2.2.continuous.continuousOn hplus_holo_all.2.2.differentiableOn
    (fun θ hθ => by
      have hn : ‖circleMap 0 R θ‖ = R := by simp [circleMap, abs_of_pos hR0]
      simpa [hn] using norm_hplus_sq_deriv2_le (circleMap_upper_im hR0 hθ) (hn.symm ▸ hR))
    (fun x => by
      unfold hplusSqDeriv2; rw [hplus_real, hplus'_real]; unfold fsKp
      simp only [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_cast, pow_two, Complex.mul_im, Complex.mul_re,
        Complex.add_im, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      field_simp; ring)
  exact h.trans_eq (by rw [abs_neg, abs_of_pos (div_pos two_pos Real.pi_pos)]; field_simp; ring)
/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_scalar_Iw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_scalar_Iw
/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_scalar_Idiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_scalar_Idiv
/-- info: 'FormalResearch.SignUncertainty.FineOrderSigned.fs_pairing_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fs_pairing_2
end FineOrderSigned
end FormalResearch.SignUncertainty
module

public import Mathlib
public import FormalResearch.Special.AiryAsymSector
public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryEnvelopeSector
public import FormalResearch.Special.AiryBiReal

/-!
# `ct:dyadic` Part (3): `h₊ = Ai + i Bi` on the upper half-plane (DLMF 9.7.5/9.7.6)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, proof of `ct:dyadic` Part (3).  **Proved.**
For `Im u ≥ 0`, `u ≠ 0`, `‖u‖ = R ≥ 1`, with `h₊ = Ai + i Bi = 2iε̄ Ai(ω² u)`:

* `hplus_sq_asymp`: `‖h₊(u)² + π⁻¹ u^{-1/2} e^{(4/3)u^{3/2}}‖ ≤ 4 R^{-3/2} · π⁻¹ R^{-1/2} e^{(4/3) Re u^{3/2}}`,
* `hplus_sq_deriv_asymp`: `‖(h₊²)'(u) + 2π⁻¹ e^{(4/3)u^{3/2}}‖ ≤ 11 R^{-3/2} · 2π⁻¹ e^{(4/3) Re u^{3/2}}`,
* `calD_bound`: `𝒟₊(u) := -(π/2)(h₊²)'(u) - e^{(4/3)u^{3/2}}` obeys `‖𝒟₊(u)‖ ≤ 11 R^{-3/2} e^{(4/3) Re u^{3/2}}`.

The route is the sector asymptotics with relative remainder `airyAiC_sector_asymptotic` at `s = 1/2`
(`|arg ω² u| ≤ 2π/3`), the rotation `Bi - iAi = 2ε̄ Ai(ω² ·)`, and `(ω² u)^{1/2} = ε̄² u^{1/2}`.
-/

@[expose] public section

open Complex Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtAiryHplus

open FormalResearch.Special

/-- `h₊ = Ai + i Bi`. -/
noncomputable def hplus (u : ℂ) : ℂ := airyAiC u + I * airyBiC u

/-- `χ = ε̄² = e^{-iπ/3}`. -/
noncomputable def chi : ℂ := (starRingEnd ℂ airyEps) ^ 2

lemma hplus_eq (u : ℂ) :
    hplus u = 2 * I * (starRingEnd ℂ airyEps) * airyAiC (airyOmega ^ 2 * u) := by
  have h := airyBiC_sub_I_mul_airyAiC u
  unfold hplus
  linear_combination I * h + airyAiC u * Complex.I_sq

lemma chi_eq : chi = ⟨1 / 2, -(√3 / 2)⟩ := by
  unfold chi airyEps
  apply Complex.ext <;> simp [pow_two] <;> nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma chi_sq2 : chi ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := by
  rw [chi_eq]
  apply Complex.ext <;> simp [pow_two] <;> nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma chi_sq : chi ^ 2 = airyOmega ^ 2 := by
  rw [chi_sq2]; unfold airyOmega
  apply Complex.ext <;> simp [pow_two] <;> nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma chi_cube : chi ^ 3 = -1 := by
  have h : chi ^ 3 = chi ^ 2 * chi := by ring
  rw [h, chi_sq2, chi_eq]
  apply Complex.ext <;> simp <;> nlinarith [Real.mul_self_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

lemma re_sqrt_nonneg_im_nonneg {u : ℂ} (hu : 0 ≤ u.im) : 0 ≤ (u ^ (1 / 2 : ℂ)).im := by
  by_cases h0 : u = 0
  · subst h0; simp
  rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_im]
  have : (Complex.log u * (1 / 2 : ℂ)).im = Complex.arg u / 2 := by
    simp [Complex.log_im]; ring
  rw [this]
  have harg : 0 ≤ Complex.arg u := Complex.arg_nonneg_iff.mpr hu
  have hle : Complex.arg u ≤ π := Complex.arg_le_pi u
  refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))

/-- `(ω² u)^{1/2} = ε̄² u^{1/2}` for `Im u ≥ 0`. -/
lemma sqrt_rot {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) :
    (airyOmega ^ 2 * u) ^ (1 / 2 : ℂ) = chi * u ^ (1 / 2 : ℂ) := by
  set p := (airyOmega ^ 2 * u) ^ (1 / 2 : ℂ) with hp
  set v := u ^ (1 / 2 : ℂ) with hv
  have hp2 : p ^ 2 = airyOmega ^ 2 * u := cpow_half_sq _
  have hv2 : v ^ 2 = u := cpow_half_sq u
  have hq2 : (chi * v) ^ 2 = airyOmega ^ 2 * u := by rw [mul_pow, chi_sq, hv2]
  have hvre : 0 ≤ v.re := cpow_half_re_nonneg u
  have hvim : 0 ≤ v.im := re_sqrt_nonneg_im_nonneg hu
  have hpre : 0 ≤ p.re := cpow_half_re_nonneg _
  have hqre : (chi * v).re = v.re / 2 + √3 / 2 * v.im := by
    rw [chi_eq]; simp [Complex.mul_re]; ring
  have hfac : (p - chi * v) * (p + chi * v) = 0 := by
    have : (p - chi * v) * (p + chi * v) = p ^ 2 - (chi * v) ^ 2 := by ring
    rw [this, hp2, hq2, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have hre : p.re + (chi * v).re = 0 := by
      have := congrArg Complex.re h; simpa using this
    have h3 : 0 ≤ √(3 : ℝ) := Real.sqrt_nonneg _
    have hv0 : v.re = 0 := by nlinarith
    have hv1 : v.im = 0 := by
      have : √3 / 2 * v.im ≤ 0 := by nlinarith
      have h3p : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
      nlinarith
    have : v = 0 := Complex.ext hv0 hv1
    rw [this] at hv2
    apply h0
    rw [← hv2]; simp

lemma norm_chi : ‖chi‖ = 1 := by
  unfold chi; rw [norm_pow, norm_conj_airyEps]; simp

lemma chi_ne_zero : chi ≠ 0 := by
  intro h; have := norm_chi; rw [h] at this; simp at this

/-- Real part of `ω² u` for `Im u ≥ 0`. -/
lemma re_rot_ge {u : ℂ} (hu : 0 ≤ u.im) : -(1 / 2) * ‖u‖ ≤ (airyOmega ^ 2 * u).re := by
  have hre : (airyOmega ^ 2 * u).re = -(u.re / 2) + √3 / 2 * u.im := by
    have : airyOmega ^ 2 = ⟨-1 / 2, -(√3 / 2)⟩ := by
      rw [← chi_sq, chi_sq2]
    rw [this]; simp [Complex.mul_re]; ring
  rw [hre]
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h33 : √(3 : ℝ) * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hn : ‖u‖ = √(u.re ^ 2 + u.im ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]; congr 1; ring
  rw [hn]
  have key : u.re - √3 * u.im ≤ √(u.re ^ 2 + u.im ^ 2) := by
    by_cases hx : u.re - √3 * u.im ≤ 0
    · exact hx.trans (Real.sqrt_nonneg _)
    · push_neg at hx
      apply Real.le_sqrt_of_sq_le
      have hy : u.im ≤ √3 * u.re := by nlinarith
      nlinarith [mul_nonneg hu h3.le]
  nlinarith

/-- The three facts about the leading term at `z = ω² u`. -/
lemma lead_facts {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) :
    (airyAiLead (airyOmega ^ 2 * u)) ^ 2 =
        (1 / (4 * (π : ℂ))) * (chi * u ^ (1 / 2 : ℂ))⁻¹ * cexp ((4 / 3) * u ^ (3 / 2 : ℂ)) ∧
    ‖airyAiLead (airyOmega ^ 2 * u)‖ ^ 2 =
        Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) / (4 * π * √‖u‖) := by
  have hz : (airyOmega ^ 2 * u) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by
    intro h; have := norm_airyOmega; rw [h] at this; simp at this)) h0
  set v := u ^ (1 / 2 : ℂ) with hv
  have hroot := sqrt_rot hu h0
  have hv0 : v ≠ 0 := by
    intro h; have := cpow_half_sq u; rw [← hv, h] at this; apply h0; rw [← this]; simp
  have hp3 : (chi * v) ^ 3 = -(u ^ (3 / 2 : ℂ)) := by
    rw [mul_pow, chi_cube, hv, cpow_half_cube]; ring
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  constructor
  · unfold airyAiLead airyLead
    rw [hroot, mul_pow, mul_pow, ← Complex.exp_nat_mul, cpow_half_sq, ← hv, hp3]
    have hc : chi ≠ 0 := chi_ne_zero
    have e1 : ((2 : ℕ) : ℂ) * (-(2 / 3) * -(u ^ (3 / 2 : ℂ))) = 4 / 3 * u ^ (3 / 2 : ℂ) := by
      push_cast; ring
    rw [e1]
    field_simp
    norm_num
  · rw [norm_airyAiLead_sq]
    have hn : ‖airyOmega ^ 2 * u‖ = ‖u‖ := by rw [norm_mul, norm_airyOmega_sq, one_mul]
    rw [hn]
    unfold airyEnv
    rw [← cpow_half_cube, hroot, ← hv, hp3]
    simp only [Complex.neg_re, mul_neg, neg_mul, neg_neg]

/-- Main term of `h₊²`. -/
noncomputable def T1 (u : ℂ) : ℂ := -(1 / (π : ℂ)) * (u ^ (1 / 2 : ℂ))⁻¹ * cexp ((4 / 3) * u ^ (3 / 2 : ℂ))

/-- Main term of `(h₊²)'`. -/
noncomputable def T2 (u : ℂ) : ℂ := -(2 / (π : ℂ)) * cexp ((4 / 3) * u ^ (3 / 2 : ℂ))

/-- `h₊'`. -/
noncomputable def hplus' (u : ℂ) : ℂ :=
  2 * I * (starRingEnd ℂ airyEps) * airyOmega ^ 2 * deriv airyAiC (airyOmega ^ 2 * u)

lemma hasDerivAt_hplus (u : ℂ) : HasDerivAt hplus (hplus' u) u := by
  have h1 : HasDerivAt (fun u : ℂ => airyAiC (airyOmega ^ 2 * u))
      (deriv airyAiC (airyOmega ^ 2 * u) * airyOmega ^ 2) u := by
    have := ((differentiable_airyAiC (airyOmega ^ 2 * u)).hasDerivAt).comp u
      ((hasDerivAt_id u).const_mul (airyOmega ^ 2))
    convert this using 1
    · rfl
    · ring
  have h2 := h1.const_mul (2 * I * (starRingEnd ℂ airyEps))
  have : hplus = fun u => 2 * I * (starRingEnd ℂ airyEps) * airyAiC (airyOmega ^ 2 * u) :=
    funext hplus_eq
  rw [this]
  convert h2 using 1
  unfold hplus'; ring

lemma hasDerivAt_hplus_sq (u : ℂ) :
    HasDerivAt (fun u => hplus u ^ 2) (2 * hplus u * hplus' u) u := by
  have := (hasDerivAt_hplus u).pow 2
  convert this using 1 <;> simp

lemma kap_bound {a c t : ℝ} (ht : 0 < t) (ha : 0 ≤ a) (hac : a * (80 / 7) ≤ c) :
    a / ((1 / 2) ^ 3 * √(1 / 2) * t) ≤ c / t := by
  have hs : (7 / 10 : ℝ) ≤ √(1 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
  have hD : (7 / 80 : ℝ) ≤ (1 / 2) ^ 3 * √(1 / 2) := by nlinarith
  calc a / ((1 / 2) ^ 3 * √(1 / 2) * t) ≤ a / ((7 / 80) * t) := by
        apply div_le_div_of_nonneg_left ha (by positivity)
        exact mul_le_mul_of_nonneg_right hD ht.le
    _ = a * (80 / 7) / t := by field_simp
    _ ≤ c / t := by gcongr

lemma sector_bounds {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) (hR : 1 ≤ ‖u‖) :
    ‖airyAiC (airyOmega ^ 2 * u) - airyAiLead (airyOmega ^ 2 * u)‖ ≤
        6 / 5 * ‖u‖ ^ (-(3 / 2 : ℝ)) * ‖airyAiLead (airyOmega ^ 2 * u)‖ ∧
    ‖deriv airyAiC (airyOmega ^ 2 * u) - airyAiDerivLead (airyOmega ^ 2 * u)‖ ≤
        41 / 10 * ‖u‖ ^ (-(3 / 2 : ℝ)) * ‖airyAiDerivLead (airyOmega ^ 2 * u)‖ := by
  have hn : ‖airyOmega ^ 2 * u‖ = ‖u‖ := by rw [norm_mul, norm_airyOmega_sq, one_mul]
  have hz : 0 < ‖airyOmega ^ 2 * u‖ := by rw [hn]; linarith
  have hre : (2 * (1 / 2 : ℝ) ^ 2 - 1) * ‖airyOmega ^ 2 * u‖ ≤ (airyOmega ^ 2 * u).re := by
    rw [hn]; have := re_rot_ge hu; nlinarith
  have hR0 : 0 < ‖u‖ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hneg : ‖u‖ ^ (-(3 / 2 : ℝ)) = (‖u‖ ^ (3 / 2 : ℝ))⁻¹ := Real.rpow_neg (by linarith) _
  constructor
  · have h := airyAiC_sector_asymptotic (s := 1 / 2) (by norm_num) hz hre
    rw [hn] at h
    have hk := kap_bound (a := 5 / 48) (c := 6 / 5) hR0 (by norm_num) (by norm_num)
    have hk' : 5 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2) * ‖u‖ ^ (3 / 2 : ℝ)) ≤
        6 / 5 * ‖u‖ ^ (-(3 / 2 : ℝ)) := by
      rw [hneg, ← div_eq_mul_inv]; exact hk
    exact h.trans (mul_le_mul_of_nonneg_right hk' (norm_nonneg _))
  · have h := deriv_airyAiC_sector_asymptotic (s := 1 / 2) (by norm_num) (by norm_num) hz hre
    rw [hn] at h
    have hk := kap_bound (a := 17 / 48) (c := 41 / 10) hR0 (by norm_num) (by norm_num)
    have hk' : 17 / 48 / ((1 / 2 : ℝ) ^ 3 * √(1 / 2) * ‖u‖ ^ (3 / 2 : ℝ)) ≤
        41 / 10 * ‖u‖ ^ (-(3 / 2 : ℝ)) := by
      rw [hneg, ← div_eq_mul_inv]; exact hk
    exact h.trans (mul_le_mul_of_nonneg_right hk' (norm_nonneg _))

lemma t_facts {R : ℝ} (hR : 1 ≤ R) : 0 < R ^ (-(3 / 2 : ℝ)) ∧ R ^ (-(3 / 2 : ℝ)) ≤ 1 :=
  ⟨Real.rpow_pos_of_pos (by linarith) _,
    Real.rpow_le_one_of_one_le_of_nonpos hR (by norm_num)⟩

/-- **`h₊²` on the upper half-plane (DLMF 9.7.5/9.7.6)**: for `Im u ≥ 0`, `‖u‖ = R ≥ 1`,
`‖h₊(u)² - T₁(u)‖ ≤ 4 R^{-3/2} · π⁻¹ R^{-1/2} e^{(4/3) Re u^{3/2}}`, `T₁ = -π⁻¹ u^{-1/2} e^{(4/3)u^{3/2}}`. -/
theorem hplus_sq_asymp {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) (hR : 1 ≤ ‖u‖) :
    ‖hplus u ^ 2 - T1 u‖ ≤ 4 * ‖u‖ ^ (-(3 / 2 : ℝ)) *
      (1 / π * (√‖u‖)⁻¹ * Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re)) := by
  obtain ⟨hls, hln⟩ := lead_facts hu h0
  obtain ⟨hb1, -⟩ := sector_bounds hu h0 hR
  obtain ⟨ht0, ht1⟩ := t_facts hR
  set t := ‖u‖ ^ (-(3 / 2 : ℝ)) with htdef
  set z := airyOmega ^ 2 * u with hzdef
  set A := airyAiC z with hA
  set Λ := airyAiLead z with hΛ
  set E := Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) with hE
  have hv0 : u ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := cpow_half_sq u; rw [h] at this; apply h0; rw [← this]; simp
  have hc := chi_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hT1 : T1 u = -4 * chi * Λ ^ 2 := by
    rw [hls]; unfold T1; field_simp
  have hh : hplus u ^ 2 = -4 * chi * A ^ 2 := by
    rw [hplus_eq]; unfold chi
    linear_combination (4 * (starRingEnd ℂ airyEps) ^ 2 * A ^ 2) * Complex.I_sq
  have hdiff : hplus u ^ 2 - T1 u = -4 * chi * ((A - Λ) * (2 * Λ + (A - Λ))) := by
    rw [hh, hT1]; ring
  rw [hdiff, norm_mul, norm_mul, norm_mul, norm_chi]
  have hL0 : 0 ≤ ‖Λ‖ := norm_nonneg _
  have hk0 : 0 ≤ ‖A - Λ‖ := norm_nonneg _
  have h2 : ‖2 * Λ + (A - Λ)‖ ≤ 2 * ‖Λ‖ + ‖A - Λ‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_two]
  have h3 : ‖A - Λ‖ * ‖2 * Λ + (A - Λ)‖ ≤ (6 / 5 * t * ‖Λ‖) * (2 * ‖Λ‖ + 6 / 5 * t * ‖Λ‖) := by
    refine mul_le_mul hb1 (h2.trans ?_) (norm_nonneg _) (by positivity)
    linarith
  have h4 : (6 / 5 * t * ‖Λ‖) * (2 * ‖Λ‖ + 6 / 5 * t * ‖Λ‖) ≤ (96 / 25) * t * ‖Λ‖ ^ 2 := by
    nlinarith [mul_nonneg ht0.le (sq_nonneg ‖Λ‖), mul_nonneg (mul_nonneg ht0.le ht0.le) (sq_nonneg ‖Λ‖)]
  have hR0 : 0 < √‖u‖ := Real.sqrt_pos.mpr (by linarith)
  have h5 : ‖Λ‖ ^ 2 = E / (4 * π * √‖u‖) := hln
  have h6 : (96 / 25) * t * ‖Λ‖ ^ 2 ≤ t * (1 / π * (√‖u‖)⁻¹ * E) := by
    rw [h5]
    have : (96 / 25) * t * (E / (4 * π * √‖u‖)) = (24 / 25) * t * (1 / π * (√‖u‖)⁻¹ * E) := by
      field_simp; ring
    rw [this]
    have hq : 0 ≤ t * (1 / π * (√‖u‖)⁻¹ * E) := by positivity
    nlinarith
  have : ‖(-4 : ℂ)‖ = 4 := by simp
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left (h3.trans h4) (by norm_num : (0 : ℝ) ≤ 4)]

/-- **`(h₊²)'` on the upper half-plane**: `‖(h₊²)'(u) - T₂(u)‖ ≤ 11 R^{-3/2} · 2π⁻¹ e^{(4/3) Re u^{3/2}}`,
`T₂ = -2π⁻¹ e^{(4/3)u^{3/2}}`, for `Im u ≥ 0`, `‖u‖ = R ≥ 1`. -/
theorem hplus_sq_deriv_asymp {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) (hR : 1 ≤ ‖u‖) :
    ‖2 * hplus u * hplus' u - T2 u‖ ≤ 11 * ‖u‖ ^ (-(3 / 2 : ℝ)) *
      (2 / π * Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re)) := by
  obtain ⟨hls, hln⟩ := lead_facts hu h0
  obtain ⟨hb1, hb2⟩ := sector_bounds hu h0 hR
  obtain ⟨ht0, ht1⟩ := t_facts hR
  have hroot := sqrt_rot hu h0
  set t := ‖u‖ ^ (-(3 / 2 : ℝ)) with htdef
  set z := airyOmega ^ 2 * u with hzdef
  set A := airyAiC z with hA
  set A' := deriv airyAiC z with hA'
  set Λ := airyAiLead z with hΛ
  set D := airyAiDerivLead z with hD
  set E := Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) with hE
  have hv0 : u ^ (1 / 2 : ℂ) ≠ 0 := by
    intro h; have := cpow_half_sq u; rw [h] at this; apply h0; rw [← this]; simp
  have hc := chi_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hchi3 : chi * airyOmega ^ 2 = -1 := by rw [← chi_sq, ← pow_succ']; exact chi_cube
  have hDeq : D = -(chi * u ^ (1 / 2 : ℂ) * Λ) := by
    rw [hD, hΛ]; unfold airyAiDerivLead; rw [hroot]
  have hT2 : T2 u = 8 * (Λ * D) := by
    rw [hDeq]
    have : Λ * -(chi * u ^ (1 / 2 : ℂ) * Λ) = -(chi * u ^ (1 / 2 : ℂ) * Λ ^ 2) := by ring
    rw [this, hls]; unfold T2; field_simp; norm_num
  have hh : 2 * hplus u * hplus' u = 8 * (A * A') := by
    rw [hplus_eq]; unfold hplus'; unfold chi at hchi3
    linear_combination (8 * ((starRingEnd ℂ airyEps) ^ 2 * airyOmega ^ 2) * A * A') * Complex.I_sq -
      (8 * A * A') * hchi3
  have hDn : ‖D‖ = √‖u‖ * ‖Λ‖ := by
    rw [hDeq, norm_neg, norm_mul, norm_mul, norm_chi, one_mul, norm_cpow_half]
  have hdiff : 2 * hplus u * hplus' u - T2 u = 8 * (Λ * (A' - D) + (A - Λ) * D + (A - Λ) * (A' - D)) := by
    rw [hh, hT2]; ring
  have hR0 : 0 < √‖u‖ := Real.sqrt_pos.mpr (by linarith)
  have hL0 : 0 ≤ ‖Λ‖ := norm_nonneg _
  have h5 : ‖Λ‖ ^ 2 = E / (4 * π * √‖u‖) := hln
  have hnm : ‖Λ * (A' - D) + (A - Λ) * D + (A - Λ) * (A' - D)‖ ≤
      ‖Λ‖ * (41 / 10 * t * ‖D‖) + 6 / 5 * t * ‖Λ‖ * ‖D‖ + 6 / 5 * t * ‖Λ‖ * (41 / 10 * t * ‖D‖) := by
    refine (norm_add_le _ _).trans ?_
    refine add_le_add ((norm_add_le _ _).trans ?_) ?_
    · refine add_le_add ?_ ?_
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left hb2 hL0
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
    · rw [norm_mul]; exact mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
  have hfin : ‖Λ * (A' - D) + (A - Λ) * D + (A - Λ) * (A' - D)‖ ≤
      (11 / 8) * t * (√‖u‖ * ‖Λ‖ ^ 2) * 8 := by
    refine hnm.trans ?_
    rw [hDn]
    have : (41 / 10 * t * (√‖u‖ * ‖Λ‖)) = 41 / 10 * t * (√‖u‖ * ‖Λ‖) := rfl
    nlinarith [mul_nonneg (mul_nonneg ht0.le hR0.le) (sq_nonneg ‖Λ‖),
      mul_nonneg (mul_nonneg (mul_nonneg ht0.le ht0.le) hR0.le) (sq_nonneg ‖Λ‖)]
  rw [hdiff, norm_mul, show ‖(8 : ℂ)‖ = 8 by simp]
  have e1 : 8 * (√‖u‖ * ‖Λ‖ ^ 2) = 2 / π * E := by
    rw [h5]; field_simp; ring
  nlinarith [hfin, e1]

/-- `𝒟₊(u) = -(π/2)(h₊²)'(u) - e^{(4/3)u^{3/2}}` (`ct:dyadic` Part (3)). -/
noncomputable def calD (u : ℂ) : ℂ :=
  -((π : ℂ) / 2) * (2 * hplus u * hplus' u) - cexp ((4 / 3) * u ^ (3 / 2 : ℂ))

/-- **`ct:dyadic` Part (3), the bound on `𝒟₊`**: for `Im u ≥ 0`, `‖u‖ = R ≥ 1`,
`‖𝒟₊(u)‖ ≤ 11 R^{-3/2} e^{(4/3) Re u^{3/2}}` (the paper's `C R^{-3/2}|e(u)|^{-1}`, `e(u) = e^{-(4/3)Re u^{3/2}}`). -/
theorem calD_bound {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) (hR : 1 ≤ ‖u‖) :
    ‖calD u‖ ≤ 11 * ‖u‖ ^ (-(3 / 2 : ℝ)) * Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re) := by
  have h := hplus_sq_deriv_asymp hu h0 hR
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hid : calD u = -((π : ℂ) / 2) * (2 * hplus u * hplus' u - T2 u) := by
    unfold calD T2; field_simp; ring
  rw [hid, norm_mul, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    show ‖(2 : ℂ)‖ = 2 by simp]
  have hp := Real.pi_pos
  calc π / 2 * ‖2 * hplus u * hplus' u - T2 u‖ ≤ π / 2 * (11 * ‖u‖ ^ (-(3 / 2 : ℝ)) *
        (2 / π * Real.exp ((4 / 3) * (u ^ (3 / 2 : ℂ)).re))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by field_simp

/-! ### The real axis (P3a) -/

lemma hplus_real (x : ℝ) : hplus x = (airyAi x : ℂ) + I * (airyBi x : ℂ) := by
  unfold hplus; rw [airyAiC_ofReal, airyBiC_ofReal]

lemma hplus'_eq (u : ℂ) : hplus' u = deriv airyAiC u + I * airyBiC' u := by
  have h1 : HasDerivAt hplus (deriv airyAiC u + I * airyBiC' u) u := by
    have ha := (differentiable_airyAiC u).hasDerivAt
    have hb := ((isAirySol_airyBiC u).1).const_mul I
    exact ha.add hb
  exact (hasDerivAt_hplus u).unique h1

lemma hplus'_real (x : ℝ) : hplus' x = (airyAi' x : ℂ) + I * (airyBiDeriv x : ℂ) := by
  rw [hplus'_eq, deriv_airyAiC_ofReal, airyBiC'_ofReal]

/-- `Im(h₊(x)²) = 2 Ai(x) Bi(x)` on the real axis. -/
lemma hplus_sq_im (x : ℝ) : (hplus x ^ 2).im = 2 * airyAi x * airyBi x := by
  rw [hplus_real]; simp [pow_two, Complex.mul_im, Complex.mul_re]; ring

lemma cpow_three_halves_neg {v : ℝ} (hv : 0 < v) :
    ((-v : ℝ) : ℂ) ^ (3 / 2 : ℂ) = -(I * ((v ^ (3 / 2 : ℝ) : ℝ) : ℂ)) := by
  have hne : ((-v : ℝ) : ℂ) ≠ 0 := by simp [hv.ne']
  rw [Complex.cpow_def_of_ne_zero hne]
  have hlog : Complex.log ((-v : ℝ) : ℂ) = (Real.log v : ℂ) + π * I := by
    apply Complex.ext
    · rw [Complex.log_re]; simp [abs_of_pos hv]
    · rw [Complex.log_im, Complex.arg_ofReal_of_neg (by linarith)]; simp
  rw [hlog]
  have : ((Real.log v : ℂ) + π * I) * (3 / 2 : ℂ) = ((3 / 2 * Real.log v : ℝ) : ℂ) + ((3 * π / 2 : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [this, Complex.exp_add, ← Complex.ofReal_exp]
  have e1 : Real.exp (3 / 2 * Real.log v) = v ^ (3 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hv]; ring_nf
  rw [e1, Complex.exp_mul_I]
  have hc : Real.cos (3 * π / 2) = 0 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, Real.cos_add_pi, Real.cos_pi_div_two]; simp
  have hs : Real.sin (3 * π / 2) = -1 := by
    rw [show 3 * π / 2 = π / 2 + π by ring, Real.sin_add_pi, Real.sin_pi_div_two]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
  push_cast; ring

/-- **`Im 𝒟₊ = D` on the real axis** (`ct:dyadic` Part (3)): for real `x`,
`Im 𝒟₊(x) = -π(Ai'(x)Bi(x) + Ai(x)Bi'(x)) + 1_{x<0} sin((4/3)(-x)^{3/2})`, i.e. the defect kernel
`D(x) = -π(AiBi)'(x) + 1_{x<0}sin((4/3)(-x)^{3/2})`. -/
theorem calD_im_real (x : ℝ) :
    (calD x).im = -π * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x) +
      (if x < 0 then Real.sin ((4 / 3) * (-x) ^ (3 / 2 : ℝ)) else 0) := by
  unfold calD
  rw [Complex.sub_im, hplus_real, hplus'_real]
  have h1 : (-((π : ℂ) / 2) * (2 * ((airyAi x : ℂ) + I * (airyBi x : ℂ)) *
      ((airyAi' x : ℂ) + I * (airyBiDeriv x : ℂ)))).im =
      -π * (airyAi' x * airyBi x + airyAi x * airyBiDeriv x) := by
    simp [Complex.mul_im, Complex.mul_re]; ring
  rw [h1]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have := cpow_three_halves_neg (v := -x) (by linarith)
    rw [neg_neg] at this
    rw [if_pos hx, this]
    have e : (4 / 3 : ℂ) * -(I * (((-x) ^ (3 / 2 : ℝ) : ℝ) : ℂ)) =
        ((-((4 / 3) * (-x) ^ (3 / 2 : ℝ)) : ℝ) : ℂ) * I := by push_cast; ring
    rw [e, Complex.exp_ofReal_mul_I_im, Real.sin_neg]; ring
  · subst hx
    simp [Complex.cpow_def]
  · rw [if_neg (not_lt.mpr hx.le)]
    have : (x : ℂ) ^ (3 / 2 : ℂ) = ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
      have := Complex.ofReal_cpow hx.le (3 / 2 : ℝ)
      push_cast at this
      exact this.symm
    rw [this]
    have e : (4 / 3 : ℂ) * ((x ^ (3 / 2 : ℝ) : ℝ) : ℂ) = (((4 / 3) * x ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e, ← Complex.ofReal_exp, Complex.ofReal_im]; ring

/-- info: 'FormalResearch.SignUncertainty.CtAiryHplus.hplus_sq_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hplus_sq_asymp

/-- info: 'FormalResearch.SignUncertainty.CtAiryHplus.calD_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calD_bound

/-- info: 'FormalResearch.SignUncertainty.CtAiryHplus.calD_im_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms calD_im_real

end FormalResearch.SignUncertainty.CtAiryHplus

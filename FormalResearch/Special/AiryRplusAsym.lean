module

public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryAsymSector

/-!
# `R₊ = (Bi - iAi)/Ai = 2 e^{(4/3)u^{3/2}} (1 + O(|u|^{-3/2}))` away from the zeros of `Ai`

For `Im u ≥ 0` the connection formula (`airyBiC_sub_I_mul_airyAiC`, DLMF 9.2.10) gives `R₊(u) = 2 ε̄ Ai(ω²u)/Ai(u)`, and the sector asymptotics
of `AiryAsymSector` (DLMF 9.7.5 with explicit constant) apply to `Ai(ω²u)` for all `Im u ≥ 0` and to `Ai(u)` for `Re u ≥ -‖u‖/2`.  With the principal
roots `(ω²u)^{1/2} = -ω u^{1/2}` the leading terms satisfy `Λ(ω²u) = ε e^{(4/3)u^{3/2}} Λ(u)` (`airyAiLead_omega_sq`), whence

* `airyRplus_sub_two_exp_mid` (`Re u ≥ -‖u‖/2`, `Im u ≥ 0`): `‖R₊ - 2E‖ ≤ 16 ‖u‖^{-3/2} ‖E‖`, `E = e^{(4/3)u^{3/2}}`.

Near the negative axis (`Re u ≤ -‖u‖/2`) `Ai(u)` has two exponentials; the rotation identity `Ai(u) = -ω²Ai(ω²u) - ωAi(ωu)` with
`Λ(ωu) = -ω² Λ(u)` (`airyAiLead_omega`, from `(ωu)^{1/2} = ω² u^{1/2}`) shows `Ai(u) = Λ(u)(1 + O(‖u‖^{-3/2} + ‖E‖))` and

* `airyRplus_sub_two_exp_neg` (`Re u ≤ -‖u‖/2`, `Im u ≥ 0`, `‖E‖ ≤ ‖u‖^{-3/2}`): `‖R₊ - 2E‖ ≤ 22 ‖u‖^{-3/2} ‖E‖`.

Both for `‖u‖^{3/2} ≥ 8`.  No good-radius hypothesis is needed: the region where `‖E‖` is not small is the one handled by
`airy_Rplus_bound`.  All proved.
-/

@[expose] public section

open Complex
open scoped Real

namespace FormalResearch.Special

/-- Principal-root uniqueness: a root `t` with `Re t ≥ 0` of `s²` with `Re s > 0` is `s`. -/
lemma airyRp_eq_of_sq {t s : ℂ} (h2 : t ^ 2 = s ^ 2) (ht : 0 ≤ t.re) (hs : 0 < s.re) : t = s := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact h
  · exfalso
    rw [h] at ht
    simp only [Complex.neg_re] at ht
    linarith

lemma airyRp_cpow_half_eq {z s : ℂ} (h : s ^ 2 = z) (hs : 0 < s.re) : z ^ (1 / 2 : ℂ) = s :=
  airyRp_eq_of_sq (by rw [cpow_half_sq, h]) (cpow_half_re_nonneg z) hs

/-- `t = (π/v)^{1/2}` has `Re t > 0`, `Im t ≤ 0` when `Re v, Im v ≥ 0`, `v ≠ 0`. -/
lemma airyRp_t_facts {v : ℂ} (ha : 0 ≤ v.re) (hb : 0 ≤ v.im) (hv : v ≠ 0) :
    0 < ((π / v) ^ (1 / 2 : ℂ)).re ∧ ((π / v) ^ (1 / 2 : ℂ)).im ≤ 0 := by
  set t := (π / v) ^ (1 / 2 : ℂ) with ht
  have h2 : t ^ 2 * v = π := by
    rw [ht, cpow_half_sq]; field_simp
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hα := cpow_half_re_nonneg (π / v)
  rw [← ht] at hα
  have hpi := Real.pi_pos
  have hvn : 0 < v.re ∨ 0 < v.im := by
    by_contra hc
    push Not at hc
    exact hv (Complex.ext (by simpa using le_antisymm hc.1 ha) (by simpa using le_antisymm hc.2 hb))
  set α := t.re
  set β := t.im
  set a := v.re
  set b := v.im
  have hα0 : 0 < α := by
    rcases hα.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at hre him
      rcases hvn with h1 | h1 <;> nlinarith [sq_nonneg β, mul_nonneg ha (sq_nonneg β), mul_nonneg hb (sq_nonneg β)]
  refine ⟨hα0, ?_⟩
  by_contra hcon
  push Not at hcon
  have h3 : β * α > 0 := mul_pos hcon hα0
  have h4 : (α * α - β * β) * a > 2 * (α * β) * b := by nlinarith
  rcases hvn with h1 | h1
  · have : (α * α - β * β) > 0 := by
      by_contra h5; push Not at h5
      nlinarith [mul_nonneg ha (neg_nonneg.2 h5), mul_nonneg hb h3.le]
    nlinarith [mul_nonneg hb this.le, mul_pos h3 h1]
  · have h5 : (α * α - β * β) * a > 0 := by nlinarith [mul_nonneg hb h3.le]
    have h6 : (α * α - β * β) > 0 := by
      by_contra h7; push Not at h7
      nlinarith [mul_nonneg ha (neg_nonneg.2 h7)]
    have h7 : 0 < a := by
      by_contra h8; push Not at h8
      nlinarith
    nlinarith [mul_nonneg hb h6.le, mul_pos h3 h7]

lemma airyRp_omega_ne : airyOmega ≠ 0 := by
  intro h
  have := airyOmega_cube
  rw [h] at this
  norm_num at this

lemma airyRp_omega_re : airyOmega.re = -1 / 2 := rfl
lemma airyRp_omega_im : airyOmega.im = √3 / 2 := rfl
lemma airyRp_omega_sq_re : (airyOmega ^ 2).re = -1 / 2 := by
  simp [pow_two, airyOmega, Complex.mul_re]; nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
lemma airyRp_omega_sq_im : (airyOmega ^ 2).im = -(√3 / 2) := by
  simp [pow_two, airyOmega, Complex.mul_im]; ring

lemma airyRp_omega_pow4 : airyOmega ^ 4 = airyOmega := by
  rw [show 4 = 3 + 1 by norm_num, pow_add, airyOmega_cube, one_mul, pow_one]

lemma airyRp_omega_pow6 : airyOmega ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, airyOmega_cube, one_pow]

/-- `Λ(ω²u) = ε e^{(4/3)u^{3/2}} Λ(u)` for `Im u ≥ 0` (principal root `(ω²u)^{1/2} = -ω u^{1/2}`). -/
theorem airyAiLead_omega_sq {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) :
    airyAiLead (airyOmega ^ 2 * u) =
      airyEps * Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) * airyAiLead u := by
  have hv2 := cpow_half_sq u
  have hvr := cpow_half_re_nonneg u
  have hvi := airyIm_cpow_half_nonneg hu
  set v := u ^ (1 / 2 : ℂ) with hv
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv2; exact h0 (by simpa using hv2.symm)
  have hvn : 0 < v.re ∨ 0 < v.im := by
    by_contra hc
    push Not at hc
    exact hv0 (Complex.ext (by simpa using le_antisymm hc.1 hvr) (by simpa using le_antisymm hc.2 hvi))
  have hpre : 0 < (-(airyOmega * v)).re := by
    simp only [Complex.neg_re, Complex.mul_re, airyRp_omega_re, airyRp_omega_im]
    have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
    rcases hvn with h | h <;> nlinarith [mul_nonneg h3.le hvi, mul_nonneg h3.le hvr]
  have hp : (airyOmega ^ 2 * u) ^ (1 / 2 : ℂ) = -(airyOmega * v) :=
    airyRp_cpow_half_eq (by rw [← hv2]; ring) hpre
  obtain ⟨htr, hti⟩ := airyRp_t_facts hvr hvi hv0
  set t := (π / v) ^ (1 / 2 : ℂ) with ht
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hεt : 0 < (airyEps * t).re := by
    simp only [Complex.mul_re, airyEps]
    nlinarith
  have hroot : (π / (-(airyOmega * v))) ^ (1 / 2 : ℂ) = airyEps * t := by
    refine airyRp_cpow_half_eq ?_ hεt
    rw [mul_pow, ht, cpow_half_sq, airyEps_sq]
    have hω := airyRp_omega_ne
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    field_simp
    linear_combination (-1 : ℂ) * airyOmega_cube
  have hexp : Complex.exp (-(2 / 3 : ℂ) * (-(airyOmega * v)) ^ 3) =
      Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) * Complex.exp (-(2 / 3 : ℂ) * v ^ 3) := by
    rw [← Complex.exp_add, ← cpow_half_cube u]
    congr 1
    linear_combination (2 / 3 : ℂ) * v ^ 3 * airyOmega_cube
  unfold airyAiLead airyLead
  rw [hp, ← hv, hroot, hexp]
  ring

/-- `Λ(ωu) = -ω² Λ(u)` for `Im u ≥ 0` when `√3 Im v ≥ Re v` (`v = u^{1/2}`; principal root `(ωu)^{1/2} = ω² u^{1/2}`). -/
theorem airyAiLead_omega {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0)
    (hq : 0 < (airyOmega ^ 2 * u ^ (1 / 2 : ℂ)).re) :
    airyAiLead (airyOmega * u) = -(airyOmega ^ 2) * airyAiLead u := by
  have hv2 := cpow_half_sq u
  have hvr := cpow_half_re_nonneg u
  have hvi := airyIm_cpow_half_nonneg hu
  set v := u ^ (1 / 2 : ℂ) with hv
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv2; exact h0 (by simpa using hv2.symm)
  have hp : (airyOmega * u) ^ (1 / 2 : ℂ) = airyOmega ^ 2 * v :=
    airyRp_cpow_half_eq (by
      rw [← hv2]
      linear_combination (v ^ 2) * airyRp_omega_pow4) hq
  obtain ⟨htr, hti⟩ := airyRp_t_facts hvr hvi hv0
  set t := (π / v) ^ (1 / 2 : ℂ) with ht
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have hct : 0 < (-(airyOmega ^ 2) * t).re := by
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, airyRp_omega_sq_re, airyRp_omega_sq_im]
    nlinarith
  have hroot : (π / (airyOmega ^ 2 * v)) ^ (1 / 2 : ℂ) = -(airyOmega ^ 2) * t := by
    refine airyRp_cpow_half_eq ?_ hct
    rw [mul_pow, ht, cpow_half_sq]
    have hω := airyRp_omega_ne
    have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
    have hv0' := hv0
    field_simp
    linear_combination airyRp_omega_pow6
  have hexp : Complex.exp (-(2 / 3 : ℂ) * (airyOmega ^ 2 * v) ^ 3) = Complex.exp (-(2 / 3 : ℂ) * v ^ 3) := by
    congr 1
    linear_combination (-(2 / 3 : ℂ) * v ^ 3) * airyRp_omega_pow6
  unfold airyAiLead airyLead
  rw [hp, ← hv, hroot, hexp]
  ring

/-- Algebra of the comparison: `A = εEL + d₁`, `B = L + d₂` with small relative errors give `‖2ε̄A/B - 2E‖ ≤ 4(η₁+η₂)‖E‖`. -/
lemma airyRp_core {A B L E d₁ d₂ : ℂ} {η₁ η₂ : ℝ} (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) (hL : L ≠ 0)
    (hA : A = airyEps * E * L + d₁) (hB : B = L + d₂)
    (h1 : ‖d₁‖ ≤ η₁ * ‖E‖ * ‖L‖) (h2 : ‖d₂‖ ≤ η₂ * ‖L‖) (hη : η₂ ≤ 1 / 2) :
    ‖2 * (starRingEnd ℂ) airyEps * A / B - 2 * E‖ ≤ 4 * (η₁ + η₂) * ‖E‖ := by
  have hLn : 0 < ‖L‖ := norm_pos_iff.2 hL
  have hBn : ‖L‖ / 2 ≤ ‖B‖ := by
    have := norm_sub_norm_le L (-d₂)
    rw [norm_neg, sub_neg_eq_add, ← hB] at this
    nlinarith
  have hB0 : B ≠ 0 := norm_pos_iff.1 (lt_of_lt_of_le (by positivity) hBn)
  have hcε : (starRingEnd ℂ) airyEps * airyEps = 1 := by
    rw [Complex.conj_mul', norm_airyEps]; simp
  have e : 2 * (starRingEnd ℂ) airyEps * A / B - 2 * E =
      2 * ((starRingEnd ℂ) airyEps * d₁ - E * d₂) / B := by
    field_simp
    rw [hA, hB]
    linear_combination (E * L) * hcε
  rw [e, norm_div, div_le_iff₀ (lt_of_lt_of_le (by positivity) hBn)]
  have hn : ‖2 * ((starRingEnd ℂ) airyEps * d₁ - E * d₂)‖ ≤ 2 * (η₁ * ‖E‖ * ‖L‖ + ‖E‖ * (η₂ * ‖L‖)) := by
    rw [norm_mul]
    have : ‖(2 : ℂ)‖ = 2 := by simp
    rw [this]
    gcongr
    calc ‖(starRingEnd ℂ) airyEps * d₁ - E * d₂‖ ≤ ‖(starRingEnd ℂ) airyEps * d₁‖ + ‖E * d₂‖ := norm_sub_le _ _
      _ ≤ η₁ * ‖E‖ * ‖L‖ + ‖E‖ * (η₂ * ‖L‖) := by
        rw [norm_mul, norm_mul, norm_conj_airyEps, one_mul]
        gcongr
  have hE := norm_nonneg E
  calc ‖2 * ((starRingEnd ℂ) airyEps * d₁ - E * d₂)‖ ≤ 2 * (η₁ * ‖E‖ * ‖L‖ + ‖E‖ * (η₂ * ‖L‖)) := hn
    _ ≤ 4 * (η₁ + η₂) * ‖E‖ * ‖B‖ := by
      have : 4 * (η₁ + η₂) * ‖E‖ * (‖L‖ / 2) ≤ 4 * (η₁ + η₂) * ‖E‖ * ‖B‖ := by
        have hη1 : 0 ≤ η₁ + η₂ := by linarith
        gcongr
      nlinarith

/-- Sector asymptotics at `s = 1/2` with the constant `2‖z‖^{-3/2}` (`Re z ≥ -‖z‖/2`, i.e. `|arg z| ≤ 2π/3`). -/
lemma airyRp_sector {z : ℂ} (hz : z ≠ 0) (hre : -(‖z‖ / 2) ≤ z.re) :
    ‖airyAiC z - airyAiLead z‖ ≤ 2 * ‖z‖ ^ (-(3 / 2 : ℝ)) * ‖airyAiLead z‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h := airyAiC_sector_asymptotic (s := 1 / 2) (by norm_num) hzn (by linarith)
  refine h.trans ?_
  gcongr
  have hr : 0 < ‖z‖ ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hzn _
  have hs : (5 : ℝ) / 12 ≤ √(1 / 2) := Real.le_sqrt_of_sq_le (by norm_num)
  rw [Real.rpow_neg hzn.le, div_le_iff₀ (by positivity)]
  have e : 2 * (‖z‖ ^ (3 / 2 : ℝ))⁻¹ * ((1 / 2 : ℝ) ^ 3 * √(1 / 2) * ‖z‖ ^ (3 / 2 : ℝ)) =
      2 * ((1 / 2 : ℝ) ^ 3 * √(1 / 2)) := by field_simp
  rw [e]
  nlinarith

lemma airyRp_lead_ne {z : ℂ} (hz : z ≠ 0) : airyAiLead z ≠ 0 := by
  intro h
  have := norm_airyAiLead_sq z
  rw [h, norm_zero] at this
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have : 0 < airyEnv z / (4 * π * √‖z‖) := by
    have := airyEnv_pos z
    have := Real.pi_pos
    have : 0 < √‖z‖ := Real.sqrt_pos.mpr hzn
    positivity
  linarith [this]

lemma airyRp_inv_le {R : ℝ} (hR : 8 ≤ R ^ (3 / 2 : ℝ)) (hR0 : 0 < R) : R ^ (-(3 / 2 : ℝ)) ≤ 1 / 8 := by
  rw [Real.rpow_neg hR0.le]
  have : (0 : ℝ) < 8 := by norm_num
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le this hR

lemma airyRp_norm_omega_sq_mul (u : ℂ) : ‖airyOmega ^ 2 * u‖ = ‖u‖ := by
  rw [norm_mul, norm_airyOmega_sq, one_mul]

lemma airyRp_norm_omega_mul (u : ℂ) : ‖airyOmega * u‖ = ‖u‖ := by
  rw [norm_mul, norm_airyOmega, one_mul]

/-- The three ingredients on the `ω²`-rotated side, shared by both regions: `A = Ai(ω²u) = ε E Λ(u) + d₁`, `‖d₁‖ ≤ 2ρ‖E‖‖Λ(u)‖`. -/
lemma airyRp_A_bound {u : ℂ} (hu : 0 ≤ u.im) (h0 : u ≠ 0) :
    ‖airyAiC (airyOmega ^ 2 * u) -
        airyEps * Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) * airyAiLead u‖ ≤
      2 * ‖u‖ ^ (-(3 / 2 : ℝ)) * ‖Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ * ‖airyAiLead u‖ := by
  have hz : airyOmega ^ 2 * u ≠ 0 := mul_ne_zero (pow_ne_zero 2 airyRp_omega_ne) h0
  have hre : -(‖airyOmega ^ 2 * u‖ / 2) ≤ (airyOmega ^ 2 * u).re := by
    rw [airyRp_norm_omega_sq_mul]
    simp only [Complex.mul_re, airyRp_omega_sq_re, airyRp_omega_sq_im]
    have := Complex.re_le_norm u
    have h3 : (0 : ℝ) ≤ √3 := Real.sqrt_nonneg 3
    nlinarith [mul_nonneg h3 hu]
  have h := airyRp_sector hz hre
  rw [airyRp_norm_omega_sq_mul, airyAiLead_omega_sq hu h0] at h
  have e : ‖airyEps * Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) * airyAiLead u‖ =
      ‖Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ * ‖airyAiLead u‖ := by
    rw [norm_mul, norm_mul, norm_airyEps, one_mul]
  rw [e] at h
  linarith

/-- **`R₊ = 2E(1 + O(‖u‖^{-3/2}))` for `Im u ≥ 0`, `Re u ≥ -‖u‖/2`** (`|arg u| ≤ 2π/3`, DLMF 9.7.5): with `E = e^{(4/3)u^{3/2}}`,
`‖R₊(u) - 2E‖ ≤ 16 ‖u‖^{-3/2} ‖E‖` for `‖u‖^{3/2} ≥ 8`. -/
theorem airyRplus_sub_two_exp_mid {u : ℂ} (hu : 0 ≤ u.im) (hre : -(‖u‖ / 2) ≤ u.re)
    (hR : 8 ≤ ‖u‖ ^ (3 / 2 : ℝ)) :
    ‖(airyBiC u - I * airyAiC u) / airyAiC u - 2 * Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ ≤
      16 * ‖u‖ ^ (-(3 / 2 : ℝ)) * ‖Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ := by
  have hRpos : 0 < ‖u‖ := by
    by_contra hc
    have : ‖u‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [this, Real.zero_rpow (by norm_num)] at hR
    linarith
  have h0 : u ≠ 0 := norm_pos_iff.1 hRpos
  have hρ := airyRp_inv_le hR hRpos
  have hρ0 : 0 ≤ ‖u‖ ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hu' := airyRp_sector h0 hre
  have hA := airyRp_A_bound hu h0
  rw [airyBiC_sub_I_mul_airyAiC]
  have := airyRp_core (A := airyAiC (airyOmega ^ 2 * u)) (B := airyAiC u) (L := airyAiLead u)
    (E := Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)))
    (d₁ := airyAiC (airyOmega ^ 2 * u) -
        airyEps * Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) * airyAiLead u)
    (d₂ := airyAiC u - airyAiLead u) (η₁ := 2 * ‖u‖ ^ (-(3 / 2 : ℝ))) (η₂ := 2 * ‖u‖ ^ (-(3 / 2 : ℝ)))
    (by positivity) (by positivity) (airyRp_lead_ne h0) (by ring) (by ring) hA hu' (by linarith)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **`R₊ = 2E(1 + O(‖u‖^{-3/2}))` near the negative axis** (`Im u ≥ 0`, `Re u ≤ -‖u‖/2`, DLMF 9.7.5 for the two rotated terms of
`Ai(u) = -ω²Ai(ω²u) - ωAi(ωu)`), provided the subdominant term is small: `‖E‖ ≤ ‖u‖^{-3/2}`.  Then
`‖R₊(u) - 2E‖ ≤ 24 ‖u‖^{-3/2} ‖E‖` for `‖u‖^{3/2} ≥ 8`. -/
theorem airyRplus_sub_two_exp_neg {u : ℂ} (hu : 0 ≤ u.im) (hre : u.re ≤ -(‖u‖ / 2))
    (hE : ‖Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ ≤ ‖u‖ ^ (-(3 / 2 : ℝ)))
    (hR : 8 ≤ ‖u‖ ^ (3 / 2 : ℝ)) :
    ‖(airyBiC u - I * airyAiC u) / airyAiC u - 2 * Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ ≤
      24 * ‖u‖ ^ (-(3 / 2 : ℝ)) * ‖Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ := by
  have hRpos : 0 < ‖u‖ := by
    by_contra hc
    have : ‖u‖ = 0 := le_antisymm (not_lt.1 hc) (norm_nonneg _)
    rw [this, Real.zero_rpow (by norm_num)] at hR
    linarith
  have h0 : u ≠ 0 := norm_pos_iff.1 hRpos
  have hρ := airyRp_inv_le hR hRpos
  have hρ0 : 0 ≤ ‖u‖ ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hRpos.le _
  set R := ‖u‖ with hRdef
  set ρ := R ^ (-(3 / 2 : ℝ)) with hρdef
  set E := Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)) with hEdef
  set L := airyAiLead u with hLdef
  have h3 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have h33 : √3 * √3 = 3 := Real.mul_self_sqrt (by norm_num)
  -- the square root `v = u^{1/2}`
  have hv2 := cpow_half_sq u
  have hvr := cpow_half_re_nonneg u
  have hvi := airyIm_cpow_half_nonneg hu
  have hvn2 := norm_cpow_half_sq u
  set v := u ^ (1 / 2 : ℂ) with hv
  have hv0 : v ≠ 0 := by
    intro h; rw [h] at hv2; exact h0 (by simpa using hv2.symm)
  have hvn : 0 < v.re ∨ 0 < v.im := by
    by_contra hc
    push Not at hc
    exact hv0 (Complex.ext (by simpa using le_antisymm hc.1 hvr) (by simpa using le_antisymm hc.2 hvi))
  have hre2 := congrArg Complex.re hv2
  have hnorm : ‖v‖ ^ 2 = R := hvn2
  rw [Complex.sq_norm, Complex.normSq_apply] at hnorm
  simp only [pow_two, Complex.mul_re] at hre2
  -- `3a² ≤ b²`
  have hab : 3 * v.re ^ 2 ≤ v.im ^ 2 := by nlinarith
  have hsb : 3 * v.re ≤ √3 * v.im := by
    have : (√3 * v.re) ^ 2 ≤ v.im ^ 2 := by nlinarith
    have h1 : √3 * v.re ≤ v.im := by
      exact (pow_le_pow_iff_left₀ (by positivity) hvi two_ne_zero).mp this
    nlinarith
  have hq : 0 < (airyOmega ^ 2 * v).re := by
    simp only [Complex.mul_re, airyRp_omega_sq_re, airyRp_omega_sq_im]
    rcases hvn with h | h <;> nlinarith
  -- sector condition for `ωu`
  have hsec : -(‖airyOmega * u‖ / 2) ≤ (airyOmega * u).re := by
    rw [airyRp_norm_omega_mul]
    simp only [Complex.mul_re, airyRp_omega_re, airyRp_omega_im]
    have hn2 : u.re ^ 2 + u.im ^ 2 = R ^ 2 := by
      have := Complex.sq_norm u
      rw [Complex.normSq_apply] at this
      nlinarith
    have hy : u.im ≤ √3 / 2 * R := by
      have : u.im ^ 2 ≤ (√3 / 2 * R) ^ 2 := by nlinarith
      exact (pow_le_pow_iff_left₀ hu (by positivity) two_ne_zero).mp this
    nlinarith
  have hLω := airyAiLead_omega hu h0 hq
  have hzω : airyOmega * u ≠ 0 := mul_ne_zero airyRp_omega_ne h0
  have hd3 := airyRp_sector hzω hsec
  rw [airyRp_norm_omega_mul, hLω] at hd3
  have hnL : ‖-(airyOmega ^ 2) * L‖ = ‖L‖ := by
    rw [norm_mul, norm_neg, norm_airyOmega_sq, one_mul]
  rw [hnL] at hd3
  have hA := airyRp_A_bound hu h0
  have hrot := airyAiC_rotation u
  have hd2 : airyAiC u - L = -(airyOmega * (airyAiC (airyOmega * u) - -(airyOmega ^ 2) * L)) -
      airyOmega ^ 2 * (airyAiC (airyOmega ^ 2 * u)) - 0 := by
    linear_combination hrot + L * airyOmega_cube
  have hE' : ‖E‖ ≤ ρ := hE
  have hnd2 : ‖airyAiC u - L‖ ≤ 4 * ρ * ‖L‖ := by
    have hA' : airyAiC (airyOmega ^ 2 * u) = airyEps * E * L + (airyAiC (airyOmega ^ 2 * u) - airyEps * E * L) := by ring
    have e2 : airyAiC u - L = -(airyOmega * (airyAiC (airyOmega * u) - -(airyOmega ^ 2) * L) +
        airyOmega ^ 2 * (airyAiC (airyOmega ^ 2 * u) - airyEps * E * L) +
        airyOmega ^ 2 * (airyEps * E * L)) := by
      linear_combination hd2
    rw [e2, norm_neg]
    have hLn := norm_nonneg L
    have hEn := norm_nonneg E
    have t1 : ‖airyOmega * (airyAiC (airyOmega * u) - -(airyOmega ^ 2) * L)‖ ≤ 2 * ρ * ‖L‖ := by
      rw [norm_mul, norm_airyOmega, one_mul]; exact hd3
    have t2 : ‖airyOmega ^ 2 * (airyAiC (airyOmega ^ 2 * u) - airyEps * E * L)‖ ≤ 2 * ρ * ‖E‖ * ‖L‖ := by
      rw [norm_mul, norm_airyOmega_sq, one_mul]; exact hA
    have t3 : ‖airyOmega ^ 2 * (airyEps * E * L)‖ = ‖E‖ * ‖L‖ := by
      rw [norm_mul, norm_airyOmega_sq, one_mul, norm_mul, norm_mul, norm_airyEps, one_mul]
    calc _ ≤ _ := norm_add₃_le
      _ ≤ 4 * ρ * ‖L‖ := by
        rw [t3]
        nlinarith [mul_nonneg hEn hLn, mul_le_mul_of_nonneg_right hE' hLn, mul_nonneg hρ0 hLn,
          mul_nonneg (mul_nonneg hρ0 hEn) hLn, mul_le_mul_of_nonneg_right hE' (mul_nonneg hρ0 hLn)]
  rw [airyBiC_sub_I_mul_airyAiC]
  have := airyRp_core (A := airyAiC (airyOmega ^ 2 * u)) (B := airyAiC u) (L := L) (E := E)
    (d₁ := airyAiC (airyOmega ^ 2 * u) - airyEps * E * L) (d₂ := airyAiC u - L)
    (η₁ := 2 * ρ) (η₂ := 4 * ρ) (by positivity) (by positivity) (airyRp_lead_ne h0) (by ring) (by ring)
    hA hnd2 (by linarith)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Decay of `e^{(4/3)u^{3/2}}` off the negative axis.**  If `‖u‖ = σ⁴`, `Im u ≥ 0`, `Re u ≤ -‖u‖/2` and `Im u ≥ 2σ`, then
`‖e^{(4/3)u^{3/2}}‖ ≤ σ^{-6} = ‖u‖^{-3/2}`.  (With `v = u^{1/2} = a + ib`, `Re u^{3/2} = a(a² - 3b²) ≤ -σ² Im u`.) -/
theorem airyRp_norm_exp_le {u : ℂ} {σ : ℝ} (hσ : 0 < σ) (hR : ‖u‖ = σ ^ 4) (hu : 0 ≤ u.im)
    (hre : u.re ≤ -(‖u‖ / 2)) (hy : 2 * σ ≤ u.im) :
    ‖Complex.exp ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ))‖ ≤ (σ ^ 6)⁻¹ := by
  have hv2 := cpow_half_sq u
  have hvr := cpow_half_re_nonneg u
  have hvi := airyIm_cpow_half_nonneg hu
  have hvn2 := norm_cpow_half_sq u
  have hv3 := cpow_half_cube u
  set v := u ^ (1 / 2 : ℂ) with hv
  have hnorm : ‖v‖ ^ 2 = ‖u‖ := hvn2
  rw [Complex.sq_norm, Complex.normSq_apply, hR] at hnorm
  have hre2 := congrArg Complex.re hv2
  have him2 := congrArg Complex.im hv2
  simp only [pow_two, Complex.mul_re, Complex.mul_im] at hre2 him2
  have hre3 : (u ^ (3 / 2 : ℂ)).re = v.re ^ 3 - 3 * v.re * v.im ^ 2 := by
    rw [← hv3]; simp [pow_succ, Complex.mul_re, Complex.mul_im]; ring
  set a := v.re
  set b := v.im
  rw [hR] at hre
  have ha2 : 4 * a ^ 2 ≤ σ ^ 4 := by nlinarith
  have hb : b ≤ σ ^ 2 := by
    have : b ^ 2 ≤ (σ ^ 2) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ hvi (by positivity) two_ne_zero).mp this
  have hσ2 : 0 < σ ^ 2 := by positivity
  have key : a ^ 3 - 3 * a * b ^ 2 ≤ -(σ ^ 2 * u.im) := by
    have h1 : 2 * σ ^ 4 ≤ 3 * b ^ 2 - a ^ 2 := by nlinarith
    have h2 : 2 * σ ^ 2 * b ≤ 2 * σ ^ 4 := by nlinarith
    have h3 : 0 ≤ a * (3 * b ^ 2 - a ^ 2 - 2 * σ ^ 2 * b) := mul_nonneg hvr (by linarith)
    nlinarith
  have hre4 : ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)).re ≤ -(8 / 3 * σ ^ 3) := by
    have : ((4 / 3 : ℂ) * u ^ (3 / 2 : ℂ)).re = 4 / 3 * (u ^ (3 / 2 : ℂ)).re := by
      simp [Complex.mul_re]
    rw [this, hre3]
    nlinarith [mul_le_mul_of_nonneg_left hy hσ2.le]
  rw [Complex.norm_exp]
  have hpos : 0 < σ ^ 6 := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 8 / 3 * σ ^ 3 by positivity)
  have h6 : σ ^ 6 ≤ Real.exp (8 / 3 * σ ^ 3) := by
    have : 0 ≤ σ ^ 3 := by positivity
    nlinarith [sq_nonneg (σ ^ 3)]
  calc Real.exp _ ≤ Real.exp (-(8 / 3 * σ ^ 3)) := Real.exp_le_exp.2 hre4
    _ = (Real.exp (8 / 3 * σ ^ 3))⁻¹ := Real.exp_neg _
    _ ≤ (σ ^ 6)⁻¹ := inv_anti₀ hpos h6

end FormalResearch.Special

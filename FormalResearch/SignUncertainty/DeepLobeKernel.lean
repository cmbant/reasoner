module

public import FormalResearch.CohnElkies.LobeSaddleCore
public import FormalResearch.CohnElkies.MellinPhaseBounds
public import FormalResearch.CohnElkies.MellinKernel

/-!
# The Mellin kernel on a vertical line `Re ζ = s ≤ 1/2` (`lem:radial-compactness`, Step 2)

For `0 < s ≤ 1/2`, `ξ > 0`, `c > 0` and real `τ`:
`‖K₀(s + iτ, ξ)‖ ≤ 2 e^{1/(4c)} exp(c[(4/9) s³ + s log(π² ξ)]) exp(-c (3/28) s u(τ))`,
`u(τ) = (1/2) min(τ², 1) + max(0, log |τ|)`, from the exact kernel `K₀ = (1-ζ)^{-1/2} e^{B_c(ζ)} e^{c Φ_Mel(ζ;ξ)}`,
`Re Φ_Mel(s + iτ) = Φ_Mel(s) - ∫_0^τ Im g` (`mellinPhi_re_vertical`), the vertical-line bound
`integral_im_stripG_ge` and `g(σ) < (4/3) σ²` (`stripGReal_lt_four_thirds_sq`, so `S̃₀(s) ≤ (4/9) s³`;
the TeX constant `1.18` is not needed).
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- The exponent weight `u(τ) = (1/2) min(τ², 1) + max(0, log |τ|)`. -/
noncomputable def lobeU (τ : ℝ) : ℝ := (1 / 2 : ℝ) * min (τ ^ 2) 1 + max 0 (Real.log |τ|)

lemma stripS0Tilde_ofReal {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    stripS0Tilde (σ : ℂ) = ((∫ s in (0 : ℝ)..1, stripGReal (s * σ) * σ : ℝ) : ℂ) := by
  unfold stripS0Tilde
  rw [← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le zero_le_one] at hs
  by_cases hs0 : s = 0
  · subst hs0; simp [stripG, stripGReal]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hlt : s * σ < 1 := by nlinarith [hs.2]
    have := stripG_ofReal (mul_pos hspos hσ0) hlt
    push_cast at this ⊢
    rw [this]

lemma re_stripS0Tilde_le {σ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) :
    (stripS0Tilde (σ : ℂ)).re ≤ (4 / 9 : ℝ) * σ ^ 3 := by
  have hσ1 : σ < 1 := by linarith
  rw [stripS0Tilde_ofReal hσ0 hσ1, Complex.ofReal_re]
  have hcont : ContinuousOn (fun s : ℝ => stripGReal (s * σ) * σ) (Icc 0 1) := by
    refine ContinuousOn.mul ?_ continuousOn_const
    refine stripGReal_continuousOn.comp (by fun_prop) ?_
    intro s hs
    exact ⟨by nlinarith [hs.1], by nlinarith [hs.2]⟩
  have hint : IntervalIntegrable (fun s : ℝ => stripGReal (s * σ) * σ) volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  have hint2 : IntervalIntegrable (fun s : ℝ => (4 / 3 : ℝ) * s ^ 2 * σ ^ 3) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => (4 / 3 : ℝ) * s ^ 2 * σ ^ 3).intervalIntegrable _ _
  calc ∫ s in (0 : ℝ)..1, stripGReal (s * σ) * σ
      ≤ ∫ s in (0 : ℝ)..1, (4 / 3 : ℝ) * s ^ 2 * σ ^ 3 := by
        refine intervalIntegral.integral_mono_on zero_le_one hint hint2 fun s hs => ?_
        by_cases hs0 : s = 0
        · subst hs0; simp [stripGReal]
        · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
          have := stripGReal_lt_four_thirds_sq (mul_pos hspos hσ0) (by nlinarith [hs.2])
          nlinarith [this]
    _ = (4 / 9 : ℝ) * σ ^ 3 := by
        have : (fun s : ℝ => (4 / 3 : ℝ) * s ^ 2 * σ ^ 3) = fun s => ((4 / 3 : ℝ) * σ ^ 3) * s ^ 2 := by
          funext s; ring
        rw [this, intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring

lemma re_mellinPhi_real_le {σ ξ : ℝ} (hσ0 : 0 < σ) (hσ : σ ≤ 1 / 2) (hξ : 0 < ξ) :
    (mellinPhi (σ : ℂ) ξ).re ≤ (4 / 9 : ℝ) * σ ^ 3 + σ * Real.log (Real.pi ^ 2 * ξ) := by
  unfold mellinPhi
  have hlog : Complex.log ((Real.pi : ℂ) ^ 2 * (ξ : ℂ)) = ((Real.log (Real.pi ^ 2 * ξ) : ℝ) : ℂ) := by
    rw [show (Real.pi : ℂ) ^ 2 * (ξ : ℂ) = ((Real.pi ^ 2 * ξ : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by positivity)]
  rw [Complex.add_re, hlog, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re,
    Complex.ofReal_im]
  have := re_stripS0Tilde_le hσ0 hσ
  nlinarith [this]

/-- The kernel `K₀` on `Re ζ = s ≤ 1/2`, `τ ≥ 0`. -/
lemma norm_mellinK0_vert_le_nonneg {c ξ s τ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hs0 : 0 < s)
    (hs : s ≤ 1 / 2) (hτ : 0 ≤ τ) :
    ‖mellinK0 c ((s : ℂ) + (τ : ℂ) * Complex.I) ξ‖ ≤
      2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ))) := by
  set ζ : ℂ := (s : ℂ) + (τ : ℂ) * Complex.I with hζ
  have hre : ζ.re = s := by simp [hζ]
  have hs1 : s < 1 := by linarith
  have h1ζ : (1 - ζ) ≠ 0 := fun h => by have := congrArg Complex.re h; simp [hre] at this; linarith
  have hn1 : (1 / 2 : ℝ) ≤ ‖1 - ζ‖ := by
    have := Complex.re_le_norm (1 - ζ)
    simp [hre] at this; linarith
  have hpow : ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ ≤ 2 := by
    rw [Complex.norm_cpow_of_ne_zero h1ζ]
    simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re, Complex.neg_im, Complex.div_ofNat_im,
      Complex.one_im, neg_zero, zero_div, mul_zero, Real.exp_zero, div_one]
    have h2 : ‖1 - ζ‖ ^ (-(1 / 2 : ℝ)) = (Real.sqrt ‖1 - ζ‖)⁻¹ := by
      rw [Real.sqrt_eq_rpow]; exact Real.rpow_neg (norm_nonneg _) _
    rw [show (-(1 / 2 : ℝ)) = -(1 / 2 : ℝ) from rfl, h2]
    have h3 : (1 / 2 : ℝ) ≤ Real.sqrt ‖1 - ζ‖ := by
      calc (1 / 2 : ℝ) = Real.sqrt ((1 / 2) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
        _ ≤ Real.sqrt ‖1 - ζ‖ := Real.sqrt_le_sqrt (by nlinarith)
    calc (Real.sqrt ‖1 - ζ‖)⁻¹ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
      _ = 2 := by norm_num
  have hbin : ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ)‖ ≤ Real.exp (1 / (4 * c)) := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ?_)
    have := FormalResearch.Asymptotics.binetDiff_norm_le hc (ζ := ζ) (by rw [hre]; exact hs1)
    refine this.trans ?_
    rw [hre]
    have h : 1 / (1 - s) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc 1 / (12 * c) * (1 / (1 - s) + 1) ≤ 1 / (12 * c) * (2 + 1) := by gcongr
      _ = 1 / (4 * c) := by field_simp; ring
  have hphi := mellinPhi_re_vertical (σ := s) (ξ := ξ) (τ := τ) hs0 hs1 hξ
  have hφ0 := re_mellinPhi_real_le hs0 hs hξ
  have hU : 2 * (3 / 56 : ℝ) * s * lobeU τ ≤ vertUpsilon s τ := by
    rcases eq_or_lt_of_le hτ with h | h
    · subst h; simp [lobeU, vertUpsilon]
    · have := integral_im_stripG_ge hs0 hs h
      simpa [lobeU, vertUpsilon, abs_of_pos h, mul_assoc] using this
  have hexpphi : ‖Complex.exp ((c : ℂ) * mellinPhi ζ ξ)‖ ≤
      Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ))) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [Complex.re_ofReal_mul]
    have : (mellinPhi ζ ξ).re = (mellinPhi (s : ℂ) ξ).re - vertUpsilon s τ := by
      have := hphi
      rw [Complex.sub_re] at this; linarith
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_left hφ0 hc.le, mul_le_mul_of_nonneg_left hU hc.le]
  unfold mellinK0
  rw [norm_mul, norm_mul]
  have hb0 := norm_nonneg ((1 - ζ) ^ (-(1 / 2 : ℂ)))
  have hb1 := norm_nonneg (Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ))
  calc ‖(1 - ζ) ^ (-(1 / 2 : ℂ))‖ * ‖Complex.exp (FormalResearch.Asymptotics.binetDiff c ζ)‖ *
        ‖Complex.exp ((c : ℂ) * mellinPhi ζ ξ)‖
      ≤ 2 * Real.exp (1 / (4 * c)) * (Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ)))) := by
        gcongr
    _ = _ := by ring

/-- The kernel `K₀` on `Re ζ = s ≤ 1/2`, every real `τ`. -/
theorem norm_mellinK0_vert_le {c ξ s τ : ℝ} (hc : 0 < c) (hξ : 0 < ξ) (hs0 : 0 < s)
    (hs : s ≤ 1 / 2) :
    ‖mellinK0 c ((s : ℂ) + (τ : ℂ) * Complex.I) ξ‖ ≤
      2 * Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) *
        Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ))) := by
  rcases le_total 0 τ with h | h
  · exact norm_mellinK0_vert_le_nonneg hc hξ hs0 hs h
  · have hconj : (s : ℂ) + (τ : ℂ) * Complex.I =
        starRingEnd ℂ ((s : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I) := by
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
    have hre : ((s : ℂ) + ((-τ : ℝ) : ℂ) * Complex.I).re = s := by simp
    rw [hconj, mellinK0_conj hξ (by rw [hre]; exact hs0) (by rw [hre]; linarith), Complex.norm_conj]
    have := norm_mellinK0_vert_le_nonneg hc hξ hs0 hs (neg_nonneg.mpr h : 0 ≤ -τ)
    have hu : lobeU (-τ) = lobeU τ := by simp [lobeU, abs_neg]
    rwa [hu] at this

/-- info: 'FormalResearch.SignUncertainty.norm_mellinK0_vert_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_mellinK0_vert_le

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.DeepLobeIntegral
public import FormalResearch.SignUncertainty.MellinMajorantBound
public import FormalResearch.SignUncertainty.MellinInversion
public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# The pointwise deep-lobe bound (`lem:radial-compactness`, Step 2)

For `c > 3/2`, `ε = ±1`, `f ∈ 𝒜_c^ε`, `0 < s ≤ 1/2` with `(3/28) c s ≥ 3`, and `ξ > 0`:
`ρ₀(cξ) |f(cξ)| ≤ (1/(2πξ)) · 18 M[f] e^{1/(6c)+1/(4c)} exp(c[(4/9)s³ + s log(π²ξ)]) / √((3/28) c s)`.

Proof: Mellin inversion on `Re z = c(1-s)` (`mellin_inversion_f`) gives `|f| ≤ (1/2π)∫ Δ^{-σ} |raw|`; for
`z = c(1-ζ)`, `ζ = s + iτ`, the exact kernel identity `(e33)` turns `ρ₀ Δ^{-σ} |raw f(z)|` into
`(cξ)^{-1} |K₀(ζ,ξ)| e^{-c Re ℋ(ζ)} |M̃_f(z)|`; the majorant of `gt:7.4(2)` and `norm_mellinK0_vert_le` bound it
by `(cξ)^{-1} M e^{1/(6c)} (2+|τ|)^{1/2} ‖K₀‖`, and `lobe_integral_le` integrates the lobe weight.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

lemma norm_mellinRaw_eq {f : ℝ → ℝ} {w : ℂ} (hw : 0 < w.re) :
    ‖mellinRaw f w‖ = ‖mellinStrip f w‖ * ‖Complex.Gamma w‖ / (2 * Real.pi) ^ w.re := by
  have hGz : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hw
  have hpz : (((2 * Real.pi : ℝ) : ℂ)) ^ w ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have hraw : mellinRaw f w = mellinStrip f w * (Complex.Gamma w / ((2 * Real.pi : ℝ) : ℂ) ^ w) := by
    unfold mellinStrip; field_simp
  rw [hraw, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
  ring

/-- Exact kernel identity in norms: `ρ₀(cξ) (cξ)^{-σ} ‖raw f w‖ = (cξ)^{-1} ‖K₀(ζ,ξ)‖ e^{-c Re ℋ(ζ)} ‖M̃_f(w)‖`,
`w = c(1-ζ)`, `σ = Re w`. -/
theorem rho0_mul_norm_raw {c : ℝ} (hc : 0 < c) {f : ℝ → ℝ} {ξ : ℝ} (hξ : 0 < ξ) {ζ : ℂ}
    (hζ0 : 0 ≤ ζ.re) (hζ1 : ζ.re < 1) :
    hankelRho0 c (c * ξ) * (c * ξ) ^ (-(((c : ℂ) * (1 - ζ)).re)) *
        ‖mellinRaw f ((c : ℂ) * (1 - ζ))‖ =
      (1 / (c * ξ)) * ‖mellinK0 c ζ ξ‖ * Real.exp (-(c * (stripH ζ).re)) *
        ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖ := by
  set s := ζ.re with hs
  have hwre : ((c : ℂ) * (1 - ζ)).re = c * (1 - s) := by simp [hs]
  have hw0 : 0 < ((c : ℂ) * (1 - ζ)).re := by rw [hwre]; exact mul_pos hc (by linarith)
  have hker := mellin_strip_kernel_eq hc hξ hζ0 hζ1
  have hcξ : 0 < c * ξ := mul_pos hc hξ
  have hGc : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hpos : (0 : ℝ) < 2 * Real.pi * c * ξ := by positivity
  -- norm of the kernel identity
  have hnorm : ‖mellinK0 c ζ ξ‖ = ‖Complex.Gamma ((c : ℂ) * (1 - ζ))‖ / Real.Gamma c *
      (2 * Real.pi * c * ξ) ^ (c * s) * Real.exp (c * (stripH ζ).re) := by
    rw [← hker, norm_mul, norm_mul, norm_div, Complex.norm_exp,
      show (2 * (Real.pi : ℂ) * (c : ℂ) * (ξ : ℂ)) = ((2 * Real.pi * c * ξ : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.Gamma_ofReal, Complex.norm_real,
      Real.norm_of_nonneg hGc.le]
    simp [hs]
  rw [norm_mellinRaw_eq hw0, hwre]
  unfold hankelRho0
  have hexp1 : 0 < Real.exp (c * (stripH ζ).re) := Real.exp_pos _
  have hkey : ‖Complex.Gamma ((c : ℂ) * (1 - ζ))‖ = ‖mellinK0 c ζ ξ‖ * Real.Gamma c /
      ((2 * Real.pi * c * ξ) ^ (c * s) * Real.exp (c * (stripH ζ).re)) := by
    rw [hnorm]
    have : 0 < (2 * Real.pi * c * ξ) ^ (c * s) := Real.rpow_pos_of_pos hpos _
    field_simp
  rw [hkey]
  have e1 : (2 * Real.pi) ^ c / (2 * Real.pi) ^ (c * (1 - s)) = (2 * Real.pi) ^ (c * s) := by
    rw [← Real.rpow_sub (by positivity)]; congr 1; ring
  have e2 : (c * ξ) ^ (c - 1) * (c * ξ) ^ (-(c * (1 - s))) = (c * ξ) ^ (c * s) / (c * ξ) := by
    rw [← Real.rpow_add hcξ, show c - 1 + -(c * (1 - s)) = c * s - 1 by ring,
      Real.rpow_sub hcξ, Real.rpow_one]
  have e3 : (2 * Real.pi * c * ξ) ^ (c * s) = (2 * Real.pi) ^ (c * s) * (c * ξ) ^ (c * s) := by
    rw [show 2 * Real.pi * c * ξ = (2 * Real.pi) * (c * ξ) by ring,
      Real.mul_rpow (by positivity) hcξ.le]
  have hp1 : 0 < (2 * Real.pi) ^ (c * s) := Real.rpow_pos_of_pos (by positivity) _
  have hp2 : 0 < (c * ξ) ^ (c * s) := Real.rpow_pos_of_pos hcξ _
  have hp3 : 0 < (2 * Real.pi) ^ (c * (1 - s)) := Real.rpow_pos_of_pos (by positivity) _
  rw [Real.exp_neg, e3]
  have hq : (2 * Real.pi) ^ c = (2 * Real.pi) ^ (c * s) * (2 * Real.pi) ^ (c * (1 - s)) := by
    rw [← Real.rpow_add (by positivity)]; congr 1; ring
  have hA : 0 < (c * ξ) ^ (c - 1) := Real.rpow_pos_of_pos hcξ _
  have hB' : (c * ξ) ^ (-(c * (1 - s))) = (c * ξ) ^ (c * s) / ((c * ξ) * (c * ξ) ^ (c - 1)) := by
    rw [eq_div_iff (by positivity)]
    have h := e2
    rw [eq_div_iff hcξ.ne'] at h
    calc (c * ξ) ^ (-(c * (1 - s))) * (c * ξ * (c * ξ) ^ (c - 1))
        = (c * ξ) ^ (c - 1) * (c * ξ) ^ (-(c * (1 - s))) * (c * ξ) := by ring
      _ = _ := h
  rw [hB', hq]
  have hG0 : Real.Gamma c ≠ 0 := hGc.ne'
  field_simp

/-- **Pointwise deep-lobe bound.** -/
theorem rho0_abs_f_le {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) {s ξ : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 2) (hk : 28 ≤ c * s)
    (hξ : 0 < ξ) :
    hankelRho0 c (c * ξ) * |f (c * ξ)| ≤
      (1 / (2 * Real.pi * ξ)) * (18 * hankelMass c f * Real.exp (1 / (6 * c)) *
        Real.exp (1 / (4 * c)) *
        Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) /
        Real.sqrt (c * (2 * (3 / 56 : ℝ) * s))) := by
  have hc0 : 0 < c := by linarith
  have hcξ : 0 < c * ξ := mul_pos hc0 hξ
  set σ : ℝ := c * (1 - s) with hσdef
  have hσ0 : 0 < σ := mul_pos hc0 (by linarith)
  have hσ : σ + 1 < c := by rw [hσdef]; nlinarith
  set k : ℝ := c * (2 * (3 / 56 : ℝ) * s) with hkdef
  have hk3 : 3 ≤ k := by rw [hkdef]; nlinarith
  have hkpos : 0 < k := by linarith
  have hρ0 : 0 ≤ hankelRho0 c (c * ξ) := (hankelRho0_pos hc0 hcξ).le
  have hinv := mellin_inversion_f hc hf hε hσ0 hσ hcξ
  have hfbound : |f (c * ξ)| ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ, (c * ξ) ^ (-σ) *
      ‖mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := by
    have h1 : ‖(f (c * ξ) : ℂ)‖ = |f (c * ξ)| := by simp
    rw [← h1, hinv, norm_mul]
    have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hcξ]
    simp
  -- change of variables `y = -c τ`
  have hsub : ∫ y : ℝ, (c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ =
      c * ∫ τ : ℝ, (c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖ := by
    have h1 := MeasureTheory.Measure.integral_comp_mul_left
      (fun y : ℝ => (c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I)‖) (-c)
    rw [smul_eq_mul, abs_inv, abs_neg, abs_of_pos hc0] at h1
    have h2 : ∫ τ : ℝ, (c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖ =
        c⁻¹ * ∫ y : ℝ, (c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + (y : ℂ) * Complex.I)‖ := h1
    rw [h2]; exact (mul_inv_cancel_left₀ hc0.ne' _).symm
  -- pointwise bound in `τ`
  have hM := hankelMass_nonneg hc0 f
  have hpt : ∀ τ : ℝ, hankelRho0 c (c * ξ) *
      ((c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖) ≤
        (1 / (c * ξ)) * (hankelMass c f * Real.exp (1 / (6 * c)) *
          (2 * Real.exp (1 / (4 * c)) *
            Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ)))) *
          ((2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ)))) := by
    intro τ
    set ζ : ℂ := (s : ℂ) + (τ : ℂ) * Complex.I with hζ
    have hζre : ζ.re = s := by simp [hζ]
    have hweq : (σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I = (c : ℂ) * (1 - ζ) := by
      rw [hζ, hσdef]; push_cast; ring
    have hwre : ((c : ℂ) * (1 - ζ)).re = σ := by simp [hζre, hσdef]
    rw [hweq]
    have hid := rho0_mul_norm_raw (f := f) hc0 hξ (ζ := ζ) (by rw [hζre]; exact hs0.le) (by rw [hζre]; linarith)
    rw [hwre] at hid
    have hmaj := norm_mellinStrip_le_majorant_stripH hc hf hε (ζ := ζ) (by rw [hζre]; exact hs0.le)
      (by rw [hζre]; linarith)
    have hK := norm_mellinK0_vert_le (c := c) (ξ := ξ) (s := s) (τ := τ) hc0 hξ hs0 hs
    have hn1 : ‖1 + ζ‖ ^ (1 / 2 : ℝ) ≤ (2 + |τ|) ^ (1 / 2 : ℝ) := by
      refine Real.rpow_le_rpow (norm_nonneg _) ?_ (by norm_num)
      have : 1 + ζ = ((1 + s : ℝ) : ℂ) + (τ : ℂ) * Complex.I := by rw [hζ]; push_cast; ring
      rw [this]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have hkexp : Real.exp (-(c * (2 * (3 / 56 : ℝ) * s * lobeU τ))) = Real.exp (-(k * lobeU τ)) := by
      congr 1; rw [hkdef]; ring
    rw [hkexp] at hK
    rw [← mul_assoc, hid]
    have hE : 0 ≤ Real.exp (-(c * (stripH ζ).re)) := (Real.exp_pos _).le
    have hKn : 0 ≤ ‖mellinK0 c ζ ξ‖ := norm_nonneg _
    have hMe : Real.exp (-(c * (stripH ζ).re)) * ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖ ≤
        hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) := by
      have h1 : ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖ ≤ hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) *
          Real.exp (c * (stripH ζ).re + 1 / (6 * c)) := hmaj
      calc Real.exp (-(c * (stripH ζ).re)) * ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖
          ≤ Real.exp (-(c * (stripH ζ).re)) * (hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) *
            Real.exp (c * (stripH ζ).re + 1 / (6 * c))) := mul_le_mul_of_nonneg_left h1 hE
        _ = hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c)) := by
            rw [Real.exp_add]
            have : Real.exp (-(c * (stripH ζ).re)) * Real.exp (c * (stripH ζ).re) = 1 := by
              rw [← Real.exp_add]; simp
            calc _ = (Real.exp (-(c * (stripH ζ).re)) * Real.exp (c * (stripH ζ).re)) *
                  (hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) * Real.exp (1 / (6 * c))) := by ring
              _ = _ := by rw [this, one_mul]
    have hp : 0 ≤ ‖1 + ζ‖ ^ (1 / 2 : ℝ) := by positivity
    calc 1 / (c * ξ) * ‖mellinK0 c ζ ξ‖ * Real.exp (-(c * (stripH ζ).re)) *
          ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖
        = (1 / (c * ξ)) * ‖mellinK0 c ζ ξ‖ * (Real.exp (-(c * (stripH ζ).re)) *
          ‖mellinStrip f ((c : ℂ) * (1 - ζ))‖) := by ring
      _ ≤ (1 / (c * ξ)) * ‖mellinK0 c ζ ξ‖ * (hankelMass c f * ‖1 + ζ‖ ^ (1 / 2 : ℝ) *
          Real.exp (1 / (6 * c))) := by gcongr
      _ ≤ (1 / (c * ξ)) * (2 * Real.exp (1 / (4 * c)) *
            Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ))) *
            Real.exp (-(k * lobeU τ))) * (hankelMass c f * (2 + |τ|) ^ (1 / 2 : ℝ) *
          Real.exp (1 / (6 * c))) := by
          have hexpn : 0 ≤ Real.exp (1 / (6 * c)) := (Real.exp_pos _).le
          have hMh : 0 ≤ hankelMass c f := hM
          gcongr
      _ = _ := by ring
  -- integrate
  obtain ⟨hFint, hFle⟩ := lobe_integral_le hk3
  set Kc : ℝ := hankelMass c f * Real.exp (1 / (6 * c)) *
          (2 * Real.exp (1 / (4 * c)) *
            Real.exp (c * ((4 / 9 : ℝ) * s ^ 3 + s * Real.log (Real.pi ^ 2 * ξ)))) with hKc
  have hKc0 : 0 ≤ Kc := by rw [hKc]; positivity
  have hint : ∫ τ : ℝ, hankelRho0 c (c * ξ) *
      ((c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖) ≤
      ∫ τ : ℝ, (1 / (c * ξ)) * (Kc * ((2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ)))) :=
    integral_mono_of_nonneg (Eventually.of_forall fun τ => by positivity)
      ((hFint.const_mul Kc).const_mul _) (Eventually.of_forall fun τ => hpt τ)
  have hL : ∫ τ : ℝ, hankelRho0 c (c * ξ) *
      ((c * ξ) ^ (-σ) * ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖) =
      hankelRho0 c (c * ξ) * ∫ τ : ℝ, (c * ξ) ^ (-σ) *
        ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖ := integral_const_mul _ _
  have hR : ∫ τ : ℝ, (1 / (c * ξ)) * (Kc * ((2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ)))) =
      (1 / (c * ξ)) * (Kc * ∫ τ : ℝ, (2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))) := by
    rw [integral_const_mul, integral_const_mul]
  rw [hL, hR] at hint
  have hfin : hankelRho0 c (c * ξ) * |f (c * ξ)| ≤
      hankelRho0 c (c * ξ) * ((1 / (2 * Real.pi)) * (c * ∫ τ : ℝ, (c * ξ) ^ (-σ) *
        ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖)) := by
    refine mul_le_mul_of_nonneg_left ?_ hρ0
    rw [← hsub]; exact hfbound
  have hrhs : hankelRho0 c (c * ξ) * ((1 / (2 * Real.pi)) * (c * ∫ τ : ℝ, (c * ξ) ^ (-σ) *
        ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖)) =
      (1 / (2 * Real.pi)) * c * (hankelRho0 c (c * ξ) * ∫ τ : ℝ, (c * ξ) ^ (-σ) *
        ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖) := by ring
  rw [hrhs] at hfin
  have hF9 : (1 / (c * ξ)) * (Kc * ∫ τ : ℝ, (2 + |τ|) ^ (1 / 2 : ℝ) * Real.exp (-(k * lobeU τ))) ≤
      (1 / (c * ξ)) * (Kc * (9 / Real.sqrt k)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFle hKc0) (by positivity)
  have hcoef : 0 ≤ (1 / (2 * Real.pi)) * c := by positivity
  calc hankelRho0 c (c * ξ) * |f (c * ξ)|
      ≤ (1 / (2 * Real.pi)) * c * (hankelRho0 c (c * ξ) * ∫ τ : ℝ, (c * ξ) ^ (-σ) *
        ‖mellinRaw f ((σ : ℂ) + ((-c * τ : ℝ) : ℂ) * Complex.I)‖) := hfin
    _ ≤ (1 / (2 * Real.pi)) * c * ((1 / (c * ξ)) * (Kc * (9 / Real.sqrt k))) :=
        mul_le_mul_of_nonneg_left (hint.trans hF9) hcoef
    _ = _ := by
        rw [hKc]; field_simp; ring

/-- info: 'FormalResearch.SignUncertainty.rho0_abs_f_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rho0_abs_f_le

end FormalResearch.SignUncertainty

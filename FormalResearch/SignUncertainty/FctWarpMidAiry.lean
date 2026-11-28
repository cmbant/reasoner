/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.Special.AiryKernelOpBounds
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.SignUncertainty.FctInnerSymbolsG0Init

/-!
# Middle-band Airy energy bounds, Bleistein identity, and cutoff-tail Abel IBP (`fct:warp-mid`)

Leaf module for `fct:warp-asymp` (2) (middle band `L ∈ [Sw * c^{-2/3}, 3 * δ_L]`):
* `airyEnergy_two_sided`: two-sided Airy energy bound
  `c_A' √v ≤ v Ai(-v)² + Ai'(-v)² ≤ C_A' √v` for all `v ≥ 1` (`0 < c_A' ≤ C_A'`);
* `fctS_id_eq`, `fctS_sq_eq`: closed forms for `fctS û (fun u => (u : ℂ))` and `fctS û (fun u => (u : ℂ)^2)`
  from `fctInnerSymbolsG0` and `CtAiry.G_eq_HH`;
* `bleistein_airy_energy_id`, `bleistein_airy_energy_lower`: exact evaluation and lower bound for the
  quadratic Bleistein part `Re 𝒮_{-v}[1 + α₁ s² + i γ₁ s]`;
* `mid_abel_tail_ibp`: `n`-fold Abel integration by parts for `fctS (-v) f` when `f` vanishes below
  `U ≥ 2.1 * √v` (`v ≥ 100`), gaining `U^{p + 1/2 - 3n}`.

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff Nat
open FormalResearch.Special

namespace FormalResearch.SignUncertainty

/-! ### 1. Two-sided Airy energy bound `c_A' √v ≤ v Ai(-v)² + Ai'(-v)² ≤ C_A' √v` -/

/-- `v * Ai(-v)² + Ai'(-v)² = K(-v, -v)` is two-sided comparable to `√v` uniformly on `[1, ∞)`. -/
theorem airyEnergy_two_sided :
    ∃ cA CA : ℝ, 0 < cA ∧ cA ≤ CA ∧ ∀ {v : ℝ}, 1 ≤ v →
      cA * Real.sqrt v ≤ v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 ∧
        v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 ≤ CA * Real.sqrt v := by
  let cA : ℝ := min (airyKer (-1) (-1) / 2) (1 / 8 : ℝ)
  let CA : ℝ := 1 / π + 1
  have hK1_pos : 0 < airyKer (-1) (-1) := airyKer_diag_pos (-1)
  have hcA_pos : 0 < cA := lt_min (by positivity) (by norm_num)
  have hpi4 : π < 4 := Real.pi_lt_four
  have hpi_pos : 0 < π := Real.pi_pos
  have hcA_le_CA : cA ≤ CA := by
    have : 1 / 8 ≤ 1 / π + 1 := by
      have : 0 < 1 / π := div_pos one_pos hpi_pos
      linarith only [this]
    exact (min_le_right _ _).trans this
  refine ⟨cA, CA, hcA_pos, hcA_le_CA, fun {v} hv1 => ?_⟩
  have hv0 : 0 < v := by linarith only [hv1]
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have heq : v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 = airyKer (-v) (-v) := by
    rw [airyKer_self]; ring
  rw [heq]
  have hdiag := abs_le.mp (airyKer_diag_neg hv1)
  have hub : airyKer (-v) (-v) ≤ CA * Real.sqrt v := by
    have h1 : 1 / v ≤ Real.sqrt v := by
      rw [div_le_iff₀ hv0]
      have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
      have h1sv : 1 ≤ Real.sqrt v := Real.one_le_sqrt.mpr hv1
      nlinarith only [hv1, h1sv, hsq]
    calc airyKer (-v) (-v) ≤ Real.sqrt v / π + 1 / v := by linarith only [hdiag.2]
      _ ≤ Real.sqrt v / π + 1 * Real.sqrt v := add_le_add le_rfl (by simpa using h1)
      _ = CA * Real.sqrt v := by dsimp only [CA]; ring
  have hlb : cA * Real.sqrt v ≤ airyKer (-v) (-v) := by
    rcases le_or_gt v 4 with hv4 | hv4
    · have hmono : airyKer (-1) (-1) ≤ airyKer (-v) (-v) :=
        antitone_airyKer_diag (by linarith only [hv1] : -v ≤ -1)
      have hsv2 : Real.sqrt v ≤ 2 := by
        rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
        exact Real.sqrt_le_sqrt hv4
      calc cA * Real.sqrt v ≤ (airyKer (-1) (-1) / 2) * Real.sqrt v :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) hsv.le
        _ ≤ (airyKer (-1) (-1) / 2) * 2 :=
            mul_le_mul_of_nonneg_left hsv2 (by positivity)
        _ = airyKer (-1) (-1) := by ring
        _ ≤ airyKer (-v) (-v) := hmono
    · have hsv2 : 2 ≤ Real.sqrt v := by
        rw [show (2 : ℝ) = Real.sqrt 4 by norm_num]
        exact Real.sqrt_le_sqrt hv4.le
      have h1v : 1 / v ≤ 1 / 8 * Real.sqrt v := by
        calc 1 / v ≤ 1 / 4 := div_le_div_of_nonneg_left zero_le_one (by norm_num) hv4.le
          _ = 1 / 8 * 2 := by norm_num
          _ ≤ 1 / 8 * Real.sqrt v := mul_le_mul_of_nonneg_left hsv2 (by norm_num)
      have hpi_inv : 1 / 4 ≤ π⁻¹ := by simpa [one_div] using div_le_div_of_nonneg_left zero_le_one hpi_pos hpi4.le
      have hlo : 1 / 8 * Real.sqrt v ≤ Real.sqrt v / π - 1 / v := by
        have h1 : 1 / 4 * Real.sqrt v ≤ Real.sqrt v / π := by
          calc 1 / 4 * Real.sqrt v ≤ π⁻¹ * Real.sqrt v := mul_le_mul_of_nonneg_right hpi_inv hsv.le
            _ = Real.sqrt v / π := by ring
        linarith only [h1, h1v]
      calc cA * Real.sqrt v ≤ (1 / 8 : ℝ) * Real.sqrt v :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hsv.le
        _ ≤ Real.sqrt v / π - 1 / v := hlo
        _ ≤ airyKer (-v) (-v) := by linarith only [hdiag.1]
  exact ⟨hlb, hub⟩

/-- Cross-term bound: `2 √v |Ai(-v) Ai'(-v)| ≤ v Ai(-v)² + Ai'(-v)²`. -/
lemma airyEnergy_cross_le {v : ℝ} (hv : 0 ≤ v) :
    2 * Real.sqrt v * |airyAi (-v) * airyAi' (-v)| ≤ v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 := by
  rw [abs_mul]
  have hsq : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv
  nlinarith [sq_nonneg (Real.sqrt v * |airyAi (-v)| - |airyAi' (-v)|),
    sq_abs (airyAi (-v)), sq_abs (airyAi' (-v)), hsq]

/-! ### 2. `fctS` on `u` and `u²`, and Bleistein Airy energy identity -/

/-- `fctS û (fun _ => (1 : ℂ)) = fctG0 û`. -/
lemma fctS_one_eq (û : ℝ) : fctS û (fun _ => (1 : ℂ)) = fctG0 û := by
  have hlim := fctInnerSymbolsG0 û
  have h0 := FctSymA.gk_limit 0 û
  simp only [pow_zero] at h0
  exact tendsto_nhds_unique h0 hlim

/-- `fctS û (fun u : ℝ => (u : ℂ)) = I * (-(2 √π) * star (G1 û))`. -/
lemma fctS_id_eq (û : ℝ) :
    fctS û (fun u : ℝ => (u : ℂ)) = Complex.I * (-(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G1 û)) := by
  have hg0 : (fun w => FctSymA.gk w 0) = fctG0 := funext fun w => by
    change fctS w (fun u : ℝ => (u : ℂ) ^ 0) = fctG0 w
    simp_rw [pow_zero]; exact fctS_one_eq w
  have hP0 : HasDerivAt (fun w => FctSymA.gk w 0) (-Complex.I * FctSymA.gk û 1) û :=
    FctSymA.hasDerivAt_gk 0 û
  have hQ0 : HasDerivAt fctG0 (-(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G1 û)) û := by
    have hf : fctG0 = fun w => -(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G0 w) :=
      funext FctSymA.fctG0_eq
    rw [hf]
    exact ((CtAiry.hasDerivAt_G0 û).star).const_mul _
  rw [hg0] at hP0
  have heq := hP0.unique hQ0
  have h1 : FctSymA.gk û 1 = Complex.I * (-(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G1 û)) := by
    calc FctSymA.gk û 1 = (-Complex.I * Complex.I) * FctSymA.gk û 1 := by
            have hII : -Complex.I * Complex.I = 1 := by simp
            rw [hII, one_mul]
      _ = Complex.I * (-Complex.I * FctSymA.gk û 1) := by ring
      _ = Complex.I * (-(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G1 û)) := by rw [heq]
  simpa [FctSymA.gk] using h1

/-- `fctS û (fun u : ℝ => (u : ℂ)^2) = (2 √π) * star (G2 û)`. -/
lemma fctS_sq_eq (û : ℝ) :
    fctS û (fun u : ℝ => (u : ℂ) ^ 2) = (2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G2 û) := by
  have hg1 : (fun w => -Complex.I * FctSymA.gk w 1) =
      fun w => -(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G1 w) := funext fun w => by
    change -Complex.I * fctS w (fun u : ℝ => (u : ℂ) ^ 1) = _
    simp_rw [pow_one, fctS_id_eq w]
    have hII : -Complex.I * Complex.I = 1 := by simp
    rw [← mul_assoc, hII, one_mul]
  have hP1 : HasDerivAt (fun w => -Complex.I * FctSymA.gk w 1) (-FctSymA.gk û 2) û := by
    refine ((FctSymA.hasDerivAt_gk 1 û).const_mul (-Complex.I)).congr_deriv ?_
    ring_nf; simp [Complex.I_sq]
  have hQ1 : HasDerivAt (fun w => -(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G1 w))
      (-(2 * ((√π : ℝ) : ℂ)) * star (CtAiry.G2 û)) û :=
    ((CtAiry.hasDerivAt_G1 û).star).const_mul _
  rw [hg1] at hP1
  have heq := hP1.unique hQ1
  change FctSymA.gk û 2 = _
  linear_combination -heq

private lemma pi_mul_sqrt_pi : π * √π = π ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' Real.pi_pos.le (by norm_num)]
  norm_num

/-- **Exact Bleistein Airy energy identity**: for `v = 2^{-2/3} c^{2/3} b²`,
`Re 𝒮_{-v}[1 + α₁ (2^{-4/3} c^{-2/3} u²) + i γ₁ (2^{-2/3} c^{-1/3} u)]` equals
`2 π^{3/2} ((1 + α₁ b²/2) Ai(-v)² + (-α₁ b²/(2v)) Ai'(-v)² - (γ₁ b / √v) Ai(-v) Ai'(-v))`. -/
theorem bleistein_airy_energy_id {c v b α₁ γ₁ : ℝ} (hc : 0 < c) (hv : 0 < v) (hb : 0 < b)
    (hvb : v = 2 ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * b ^ 2) :
    (fctS (-v) (fun _ => (1 : ℂ)) +
      ((α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * fctS (-v) (fun u : ℝ => (u : ℂ) ^ 2) +
      Complex.I * ((γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
        fctS (-v) (fun u : ℝ => (u : ℂ))).re =
      2 * π ^ (3 / 2 : ℝ) *
        ((1 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 +
          (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 -
          (γ₁ * b / Real.sqrt v) * (airyAi (-v) * airyAi' (-v))) := by
  have hg0 : (fctS (-v) (fun _ => (1 : ℂ))).re = 2 * π ^ (3 / 2 : ℝ) * airyAi (-v) ^ 2 := by
    rw [fctS_one_eq]; unfold fctG0; simp; left; norm_cast
  have hg2 : (fctS (-v) (fun u : ℝ => (u : ℂ) ^ 2)).re =
      4 * π ^ (3 / 2 : ℝ) * (v * airyAi (-v) ^ 2 - airyAi' (-v) ^ 2) := by
    rw [fctS_sq_eq (-v), (CtAiry.G_eq_HH (-v)).2.2]
    unfold CtAiry.HH2
    have hstar : (2 * ((√π : ℝ) : ℂ)) *
        star (-(π : ℂ) * (2 * (airyAi' (-v) : ℂ) ^ 2 + 2 * ((-v : ℝ) : ℂ) * (airyAi (-v) : ℂ) ^ 2 +
          Complex.I * (2 * (airyAi' (-v) : ℂ) * (airyBiDeriv (-v) : ℂ) +
            2 * ((-v : ℝ) : ℂ) * (airyAi (-v) : ℂ) * (airyBi (-v) : ℂ)))) =
        ((4 * (π * √π) * (v * airyAi (-v) ^ 2 - airyAi' (-v) ^ 2) : ℝ) : ℂ) +
          Complex.I * ((2 * √π * π * (2 * airyAi' (-v) * airyBiDeriv (-v) -
            2 * v * airyAi (-v) * airyBi (-v)) : ℝ) : ℂ) := by
      simp only [star_mul', star_neg, star_add, star_pow, Complex.star_def, Complex.conj_ofReal,
        Complex.conj_I, star_ofNat]
      push_cast; ring
    rw [hstar, pi_mul_sqrt_pi, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hg1 : (Complex.I * fctS (-v) (fun u : ℝ => (u : ℂ))).re =
      -(4 * π ^ (3 / 2 : ℝ) * (airyAi (-v) * airyAi' (-v))) := by
    rw [fctS_id_eq (-v), (CtAiry.G_eq_HH (-v)).2.1]
    unfold CtAiry.HH1
    have hI2 : Complex.I * (Complex.I * (-(2 * ((√π : ℝ) : ℂ)) *
        star (-(π : ℂ) * (2 * (airyAi (-v) : ℂ) * (airyAi' (-v) : ℂ) +
          Complex.I * ((airyAi' (-v) : ℂ) * (airyBi (-v) : ℂ) +
            (airyAi (-v) : ℂ) * (airyBiDeriv (-v) : ℂ)))))) =
        ((-(4 * (π * √π) * (airyAi (-v) * airyAi' (-v))) : ℝ) : ℂ) +
          Complex.I * ((2 * √π * π * (airyAi' (-v) * airyBi (-v) + airyAi (-v) * airyBiDeriv (-v)) : ℝ) : ℂ) := by
      have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
      simp only [star_mul', star_neg, star_add, Complex.star_def, Complex.conj_ofReal,
        Complex.conj_I, star_ofNat]
      calc Complex.I * (Complex.I * (-(2 * ((√π : ℝ) : ℂ)) *
            (-(π : ℂ) * (2 * (airyAi (-v) : ℂ) * (airyAi' (-v) : ℂ) +
              (-Complex.I) * ((airyAi' (-v) : ℂ) * (airyBi (-v) : ℂ) +
                (airyAi (-v) : ℂ) * (airyBiDeriv (-v) : ℂ))))))
          = (Complex.I * Complex.I) * (2 * ((√π : ℝ) : ℂ) * (π : ℂ) *
              (2 * (airyAi (-v) : ℂ) * (airyAi' (-v) : ℂ) -
                Complex.I * ((airyAi' (-v) : ℂ) * (airyBi (-v) : ℂ) +
                  (airyAi (-v) : ℂ) * (airyBiDeriv (-v) : ℂ)))) := by ring
        _ = (-1 : ℂ) * _ := by rw [hII]
        _ = _ := by push_cast; ring
    rw [hI2, pi_mul_sqrt_pi, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have h2_43 : (2 : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (-(2 / 3 : ℝ)) = 1 / 4 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  have hc_23 : c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.rpow_add hc]; norm_num
  have hv_sq : Real.sqrt v = 2 ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) * b := by
    have h2 : (2 ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) * b) ^ 2 = v := by
      rw [hvb, mul_pow, mul_pow, ← Real.rpow_natCast (2 ^ _), ← Real.rpow_mul (by norm_num),
        ← Real.rpow_natCast (c ^ _), ← Real.rpow_mul hc.le]
      norm_num
    rw [← h2, Real.sqrt_sq (by positivity)]
  have hcoeff2 : α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) * 2 = α₁ * b ^ 2 / (2 * v) := by
    have hmul : 2 * (α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) * v = α₁ * b ^ 2 / 2 := by
      rw [hvb]
      calc 2 * (α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) *
            ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ) * b ^ 2)
          = 2 * α₁ * ((2 : ℝ) ^ (-(4 / 3 : ℝ)) * (2 : ℝ) ^ (-(2 / 3 : ℝ))) *
              (c ^ (-(2 / 3 : ℝ)) * c ^ (2 / 3 : ℝ)) * b ^ 2 := by ring
        _ = 2 * α₁ * (1 / 4) * 1 * b ^ 2 := by rw [h2_43, hc_23]
        _ = α₁ * b ^ 2 / 2 := by ring
    rw [eq_div_iff (by positivity)]
    linarith only [hmul]
  have hcoeff1 : 2 * (γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) = γ₁ * b / Real.sqrt v := by
    have h2_13 : (2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (-(1 / 3 : ℝ)) = 1 / 2 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have hc_13 : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc]; norm_num
    have hsv_pos : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
    have hmul : 2 * (γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) * Real.sqrt v = γ₁ * b := by
      rw [hv_sq]
      calc 2 * (γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) *
            ((2 : ℝ) ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) * b)
          = 2 * γ₁ * ((2 : ℝ) ^ (-(2 / 3 : ℝ)) * (2 : ℝ) ^ (-(1 / 3 : ℝ))) *
              (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) * b := by ring
        _ = 2 * γ₁ * (1 / 2) * 1 * b := by rw [h2_13, hc_13]
        _ = γ₁ * b := by ring
    rw [eq_div_iff hsv_pos.ne']
    exact hmul
  have hre_split :
      (fctS (-v) (fun _ => (1 : ℂ)) +
        ((α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * fctS (-v) (fun u : ℝ => (u : ℂ) ^ 2) +
        Complex.I * ((γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
          fctS (-v) (fun u : ℝ => (u : ℂ))).re =
      (fctS (-v) (fun _ => (1 : ℂ))).re +
        (α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ))) * (fctS (-v) (fun u : ℝ => (u : ℂ) ^ 2)).re +
        (γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ))) *
          (Complex.I * fctS (-v) (fun u : ℝ => (u : ℂ))).re := by
    have hmul : Complex.I * ((γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
        fctS (-v) (fun u : ℝ => (u : ℂ)) =
        ((γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) : ℝ) : ℂ) *
          (Complex.I * fctS (-v) (fun u : ℝ => (u : ℂ))) := by ring
    rw [Complex.add_re, Complex.add_re, hmul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  rw [hre_split, hg0, hg2, hg1]
  have hv_alg : α₁ * b ^ 2 / (2 * v) * (v * airyAi (-v) ^ 2 - airyAi' (-v) ^ 2) =
      (α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 + (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 := by
    field_simp [hv.ne']
    ring
  calc 2 * π ^ (3 / 2 : ℝ) * airyAi (-v) ^ 2 +
        α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) *
          (4 * π ^ (3 / 2 : ℝ) * (v * airyAi (-v) ^ 2 - airyAi' (-v) ^ 2)) +
        γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)) *
          -(4 * π ^ (3 / 2 : ℝ) * (airyAi (-v) * airyAi' (-v)))
      = 2 * π ^ (3 / 2 : ℝ) * (airyAi (-v) ^ 2 +
          (α₁ * (2 : ℝ) ^ (-(4 / 3 : ℝ)) * c ^ (-(2 / 3 : ℝ)) * 2) * (v * airyAi (-v) ^ 2 - airyAi' (-v) ^ 2) -
          (2 * (γ₁ * (2 : ℝ) ^ (-(2 / 3 : ℝ)) * c ^ (-(1 / 3 : ℝ)))) * (airyAi (-v) * airyAi' (-v))) := by ring
    _ = 2 * π ^ (3 / 2 : ℝ) * (airyAi (-v) ^ 2 +
          (α₁ * b ^ 2 / (2 * v)) * (v * airyAi (-v) ^ 2 - airyAi' (-v) ^ 2) -
          (γ₁ * b / Real.sqrt v) * (airyAi (-v) * airyAi' (-v))) := by rw [hcoeff2, hcoeff1]
    _ = 2 * π ^ (3 / 2 : ℝ) * ((1 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 +
          (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 -
          (γ₁ * b / Real.sqrt v) * (airyAi (-v) * airyAi' (-v))) := by rw [hv_alg]; ring

/-- Lower bound for the Bleistein Airy energy quadratic form (`v ≥ 1`, `-1/2 ≤ α₁ b²`, `0 ≤ P ≤ 1/2`, `-α₁ b² ≥ P - E₁`). -/
lemma bleistein_airy_energy_lower {cA CA v α₁ γ₁ b P E₁ : ℝ}
    (_hcA0 : 0 < cA) (hE_bd : cA * Real.sqrt v ≤ v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 ∧
      v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 ≤ CA * Real.sqrt v)
    (hv : 1 ≤ v) (hα_lo : P - E₁ ≤ -(α₁ * b ^ 2)) (hα_ge : -(1 / 2 : ℝ) ≤ α₁ * b ^ 2)
    (hP_hi : P ≤ 1 / 2) (hP_nn : 0 ≤ P) (hE_nn : 0 ≤ E₁) :
    1 / 2 * airyAi (-v) ^ 2 + (cA / 2 * P - CA / 2 * (E₁ + |γ₁ * b|)) * v ^ (-(1 / 2 : ℝ)) ≤
      (1 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 +
        (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 -
        (γ₁ * b / Real.sqrt v) * (airyAi (-v) * airyAi' (-v)) := by
  have hv0 : 0 < v := by linarith only [hv]
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have h12_α : P / 2 ≤ 1 / 2 + α₁ * b ^ 2 / 2 := by linarith only [hP_hi, hα_ge]
  have hAi2_nn : 0 ≤ airyAi (-v) ^ 2 := sq_nonneg _
  have hAid2_nn : 0 ≤ airyAi' (-v) ^ 2 := sq_nonneg _
  have hrpow : v ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt v := by
    rw [Real.rpow_neg hv0.le, ← Real.sqrt_eq_rpow, one_div]
  have hAi'_le_E : airyAi' (-v) ^ 2 ≤ v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2 := by
    linarith only [mul_nonneg hv0.le hAi2_nn]
  have h_quad :
      P / (2 * v) * (v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2) -
        E₁ / (2 * v) * airyAi' (-v) ^ 2 ≤
      (1 / 2 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 + (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 := by
    have hA_term : P / (2 * v) * (v * airyAi (-v) ^ 2) ≤ (1 / 2 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 := by
      have heq : P / (2 * v) * (v * airyAi (-v) ^ 2) = (P / 2) * airyAi (-v) ^ 2 := by
        field_simp [hv0.ne']
      rw [heq]
      exact mul_le_mul_of_nonneg_right h12_α hAi2_nn
    have hB_term : (P - E₁) / (2 * v) * airyAi' (-v) ^ 2 ≤ (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 := by
      have hdiv : (P - E₁) / (2 * v) ≤ -α₁ * b ^ 2 / (2 * v) :=
        div_le_div_of_nonneg_right (by linarith only [hα_lo]) (by positivity)
      exact mul_le_mul_of_nonneg_right hdiv hAid2_nn
    linarith only [hA_term, hB_term,
      show P / (2 * v) * (v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2) - E₁ / (2 * v) * airyAi' (-v) ^ 2 =
        P / (2 * v) * (v * airyAi (-v) ^ 2) + (P - E₁) / (2 * v) * airyAi' (-v) ^ 2 by ring]
  have h_pos_P : cA / 2 * P * v ^ (-(1 / 2 : ℝ)) ≤ P / (2 * v) * (v * airyAi (-v) ^ 2 + airyAi' (-v) ^ 2) := by
    rw [hrpow]
    have h1 := mul_le_mul_of_nonneg_left hE_bd.1 (div_nonneg hP_nn (by positivity : 0 ≤ 2 * v))
    have heq1 : P / (2 * v) * (cA * Real.sqrt v) = cA / 2 * P * (1 / Real.sqrt v) := by
      have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
      calc P / (2 * v) * (cA * Real.sqrt v) = P * cA * Real.sqrt v / (2 * v) := by ring
        _ = P * cA * Real.sqrt v / (2 * (Real.sqrt v * Real.sqrt v)) := by rw [hsq]
        _ = cA / 2 * P * (1 / Real.sqrt v) := by field_simp [hsv.ne']
    linarith only [h1, heq1]
  have h_err_E : E₁ / (2 * v) * airyAi' (-v) ^ 2 ≤ CA / 2 * E₁ * v ^ (-(1 / 2 : ℝ)) := by
    rw [hrpow]
    have h1 : E₁ / (2 * v) * airyAi' (-v) ^ 2 ≤ E₁ / (2 * v) * (CA * Real.sqrt v) :=
      mul_le_mul_of_nonneg_left (hAi'_le_E.trans hE_bd.2) (div_nonneg hE_nn (by positivity : 0 ≤ 2 * v))
    have heq1 : E₁ / (2 * v) * (CA * Real.sqrt v) = CA / 2 * E₁ * (1 / Real.sqrt v) := by
      have hsq : Real.sqrt v * Real.sqrt v = v := Real.mul_self_sqrt hv0.le
      calc E₁ / (2 * v) * (CA * Real.sqrt v) = E₁ * CA * Real.sqrt v / (2 * v) := by ring
        _ = E₁ * CA * Real.sqrt v / (2 * (Real.sqrt v * Real.sqrt v)) := by rw [hsq]
        _ = CA / 2 * E₁ * (1 / Real.sqrt v) := by field_simp [hsv.ne']
    linarith only [h1, heq1]
  have h_cross : |(γ₁ * b / Real.sqrt v) * (airyAi (-v) * airyAi' (-v))| ≤
      CA / 2 * |γ₁ * b| * v ^ (-(1 / 2 : ℝ)) := by
    rw [hrpow, abs_mul, abs_div, abs_of_pos hsv]
    have hcr := airyEnergy_cross_le hv0.le
    have hcr1 : 2 * Real.sqrt v * |airyAi (-v) * airyAi' (-v)| ≤ CA * Real.sqrt v := hcr.trans hE_bd.2
    have hcr2 : |airyAi (-v) * airyAi' (-v)| ≤ CA / 2 := by
      have : 2 * Real.sqrt v * |airyAi (-v) * airyAi' (-v)| ≤ 2 * Real.sqrt v * (CA / 2) := by
        linarith only [hcr1]
      exact le_of_mul_le_mul_left this (by positivity)
    calc |γ₁ * b| / Real.sqrt v * |airyAi (-v) * airyAi' (-v)|
        ≤ |γ₁ * b| / Real.sqrt v * (CA / 2) := by gcongr
      _ = CA / 2 * |γ₁ * b| * (1 / Real.sqrt v) := by ring
  have hcr_hi := (abs_le.mp h_cross).2
  have h_comb : cA / 2 * P * v ^ (-(1 / 2 : ℝ)) - CA / 2 * E₁ * v ^ (-(1 / 2 : ℝ)) ≤
      (1 / 2 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 + (-α₁ * b ^ 2 / (2 * v)) * airyAi' (-v) ^ 2 := by
    linarith only [h_quad, h_pos_P, h_err_E]
  have h_split_12 : (1 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 =
      1 / 2 * airyAi (-v) ^ 2 + (1 / 2 + α₁ * b ^ 2 / 2) * airyAi (-v) ^ 2 := by ring
  have h_rhs_err : (cA / 2 * P - CA / 2 * (E₁ + |γ₁ * b|)) * v ^ (-(1 / 2 : ℝ)) =
      (cA / 2 * P * v ^ (-(1 / 2 : ℝ)) - CA / 2 * E₁ * v ^ (-(1 / 2 : ℝ))) -
        CA / 2 * |γ₁ * b| * v ^ (-(1 / 2 : ℝ)) := by ring
  linarith only [h_comb, hcr_hi, h_split_12, h_rhs_err]

/-! ### 3. Cutoff-tail Abel integration by parts for `v ≥ 100` (`u ≥ 2.1 * √v`) -/

section MidTailIbp

open FctSymA

private lemma mid_fctD_lower {v ε u : ℝ} (hv : 100 ≤ v) (hu : 2.05 * Real.sqrt v < u) :
    u ^ 2 / 100 ≤ ‖fctD (-v) ε u‖ := by
  have hv0 : 0 < v := by linarith only [hv]
  have hsv : 10 ≤ Real.sqrt v := by
    rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
  have hu0 : 0 < u := by linarith only [hu, hsv]
  have hu2 : 4.2025 * v ≤ u ^ 2 := by
    have h1 : (2.05 * Real.sqrt v) ^ 2 = 4.2025 * v := by
      rw [mul_pow, Real.sq_sqrt hv0.le]; norm_num
    nlinarith only [hu, h1, hsv]
  have him : u ^ 2 / 4 - v ≤ ‖fctD (-v) ε u‖ := by
    have hnorm := Complex.abs_im_le_norm (fctD (-v) ε u)
    have hD_im : (fctD (-v) ε u).im = v - u ^ 2 / 4 := by
      rw [fctD_eq]; simp; ring
    have hpos : 0 ≤ u ^ 2 / 4 - v := by linarith only [hu2, hv0]
    have hab : u ^ 2 / 4 - v ≤ |(fctD (-v) ε u).im| := by
      rw [hD_im, show v - u ^ 2 / 4 = -(u ^ 2 / 4 - v) by ring, abs_neg, abs_of_nonneg hpos]
    exact hab.trans hnorm
  rw [show (4.2025 : ℝ) = 1681 / 400 by norm_num] at hu2
  have hv_le : v ≤ 400 / 1681 * u ^ 2 := by
    calc v = (400 / 1681) * (1681 / 400 * v) := by ring
      _ ≤ (400 / 1681) * u ^ 2 := by gcongr
  have h_eq : u ^ 2 / 4 - 400 / 1681 * u ^ 2 - u ^ 2 / 100 = 1376 / 672400 * u ^ 2 := by ring
  have h_pos : 0 ≤ 1376 / 672400 * u ^ 2 := by positivity
  linarith only [hv_le, h_eq, h_pos, him]

private lemma mid_fctD_ne {v ε u : ℝ} (hv : 100 ≤ v) (hu : 2.05 * Real.sqrt v < u) :
    fctD (-v) ε u ≠ 0 := by
  have hsv : 10 ≤ Real.sqrt v := by
    rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
  have hu0 : 0 < u := by linarith only [hu, hsv]
  have hl := mid_fctD_lower (ε := ε) hv hu
  intro h0
  rw [h0, norm_zero] at hl
  nlinarith only [hl, sq_pos_of_pos hu0]

private lemma mid_contDiffAt_fctQ {v ε u : ℝ} (hv : 100 ≤ v) (hu : 2.05 * Real.sqrt v < u) :
    ContDiffAt ℝ ⊤ (fctQ (-v) ε) u :=
  (contDiff_fctD (-v) ε).contDiffAt.inv (mid_fctD_ne hv hu)

private lemma mid_iteratedDeriv_fctQ_rec {v ε u : ℝ} (hv : 100 ≤ v) (hu : 2.05 * Real.sqrt v < u)
    (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv m (fctQ (-v) ε) u = -(fctD (-v) ε u)⁻¹ * ∑ i ∈ Finset.range m,
      (m.choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD (-v) ε) u *
        iteratedDeriv (m - (i + 1)) (fctQ (-v) ε) u := by
  have hev : (fun x => fctD (-v) ε x * fctQ (-v) ε x) =ᶠ[𝓝 u] fun _ => (1 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact mul_inv_cancel₀ (mid_fctD_ne hv hx)
  have h1 : iteratedDeriv m (fun x => fctD (-v) ε x * fctQ (-v) ε x) u = 0 := by
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]; simp; omega
  rw [iteratedDeriv_fun_mul ((contDiff_fctD (-v) ε).contDiffAt.of_le (by exact_mod_cast le_top))
    ((mid_contDiffAt_fctQ hv hu).of_le (by exact_mod_cast le_top)), Finset.sum_range_succ'] at h1
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero] at h1
  have hD0 : fctD (-v) ε u ≠ 0 := mid_fctD_ne hv hu
  have e : (fctD (-v) ε u)⁻¹ * fctD (-v) ε u = 1 := inv_mul_cancel₀ hD0
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  linear_combination (fctD (-v) ε u)⁻¹ * h1 - (iteratedDeriv m (fctQ (-v) ε) u) * e

private lemma mid_fctQ_norm_zero {v ε u : ℝ} (hv : 100 ≤ v) (hu : 2.05 * Real.sqrt v < u) :
    ‖fctQ (-v) ε u‖ ≤ 100 * u ^ ((-2 : ℝ) - ((0 : ℕ) : ℝ)) := by
  have hsv : 10 ≤ Real.sqrt v := by
    rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
  have hu0 : 0 < u := by linarith only [hu, hsv]
  have hl := mid_fctD_lower (ε := ε) hv hu
  have hpos : 0 < u ^ 2 / 100 := by positivity
  simp only [fctQ, norm_inv, Nat.cast_zero, sub_zero]
  rw [Real.rpow_neg hu0.le, Real.rpow_two]
  calc (‖fctD (-v) ε u‖)⁻¹ ≤ (u ^ 2 / 100)⁻¹ := inv_anti₀ hpos hl
    _ = 100 * (u ^ 2)⁻¹ := by field_simp

private lemma mid_fctQ_bound (m : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (v ε u : ℝ), 100 ≤ v → 0 ≤ ε → ε ≤ 1 →
    2.05 * Real.sqrt v < u → ∀ j ≤ m, ‖iteratedDeriv j (fctQ (-v) ε) u‖ ≤ c * u ^ ((-2 : ℝ) - j) := by
  induction m with
  | zero =>
    refine ⟨100, by norm_num, fun v ε u hv _ _ hu j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    simpa using mid_fctQ_norm_zero (ε := ε) hv hu
  | succ m ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    refine ⟨c + 200 * ((m + 1) * 2 ^ (m + 1)) * c, by positivity, fun v ε u hv hε0 hε1 hu j hj => ?_⟩
    have hsv : 10 ≤ Real.sqrt v := by
      rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
    have hu0 : 0 < u := by linarith only [hu, hsv]
    have hu4 : 4 ≤ u := by linarith only [hu, hsv]
    rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · refine (hc v ε u hv hε0 hε1 hu j (by omega)).trans ?_
      have : 0 ≤ 200 * ((m + 1 : ℝ) * 2 ^ (m + 1)) * c := by positivity
      have hp : 0 < u ^ ((-2 : ℝ) - j) := Real.rpow_pos_of_pos hu0 _
      nlinarith
    · obtain rfl : j = m + 1 := by omega
      rw [mid_iteratedDeriv_fctQ_rec hv hu (m + 1) (by omega)]
      have hDinv : ‖(fctD (-v) ε u)⁻¹‖ ≤ 100 * u ^ ((-2 : ℝ)) := by
        simpa [fctQ] using mid_fctQ_norm_zero (ε := ε) hv hu
      rw [norm_mul, norm_neg]
      have hterm : ∀ i ∈ Finset.range (m + 1),
          ‖((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD (-v) ε) u *
              iteratedDeriv (m + 1 - (i + 1)) (fctQ (-v) ε) u‖ ≤
            ((m + 1).choose (i + 1) : ℝ) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ)) := by
        intro i hi
        rw [Finset.mem_range] at hi
        have hQ := hc v ε u hv hε0 hε1 hu (m + 1 - (i + 1)) (by omega)
        have hm1 : (-1 : ℝ) - (m : ℝ) = (2 - ((i + 1 : ℕ) : ℝ)) + ((-2 : ℝ) - ((m + 1 - (i + 1) : ℕ) : ℝ)) := by
          have : i + 1 ≤ m + 1 := by omega
          rw [Nat.cast_sub this]; push_cast; ring
        have hD' : ‖iteratedDeriv (i + 1) (fctD (-v) ε) u‖ ≤ 2 * u ^ (2 - ((i + 1 : ℕ) : ℝ)) := by
          have hD := iteratedDeriv_fctD_norm_le (-v) ε u hε0 hε1 hu4 (i + 1) (by omega)
          have hup : 0 ≤ u ^ (2 - ((i + 1 : ℕ) : ℝ)) := Real.rpow_nonneg hu0.le _
          linarith only [hD, hup]
        have hCnorm : ‖((m + 1).choose (i + 1) : ℂ)‖ = ((m + 1).choose (i + 1) : ℝ) := by
          simp
        rw [norm_mul, norm_mul, hCnorm]
        calc ((m + 1).choose (i + 1) : ℝ) * ‖iteratedDeriv (i + 1) (fctD (-v) ε) u‖ *
              ‖iteratedDeriv (m + 1 - (i + 1)) (fctQ (-v) ε) u‖
            ≤ ((m + 1).choose (i + 1) : ℝ) * (2 * u ^ (2 - ((i + 1 : ℕ) : ℝ))) *
                (c * u ^ ((-2 : ℝ) - ((m + 1 - (i + 1) : ℕ) : ℝ))) := by gcongr
          _ = ((m + 1).choose (i + 1) : ℝ) * (2 * c) *
                (u ^ (2 - ((i + 1 : ℕ) : ℝ)) * u ^ ((-2 : ℝ) - ((m + 1 - (i + 1) : ℕ) : ℝ))) := by ring
          _ = ((m + 1).choose (i + 1) : ℝ) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ)) := by
              rw [← Real.rpow_add hu0, ← hm1]
      have hsum : ‖∑ i ∈ Finset.range (m + 1),
          ((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD (-v) ε) u *
            iteratedDeriv (m + 1 - (i + 1)) (fctQ (-v) ε) u‖ ≤
          (2 ^ (m + 1) : ℝ) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ)) := by
        refine (norm_sum_le _ _).trans ?_
        have hsum1 : ∑ i ∈ Finset.range (m + 1),
            ‖((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD (-v) ε) u *
              iteratedDeriv (m + 1 - (i + 1)) (fctQ (-v) ε) u‖ ≤
            ∑ i ∈ Finset.range (m + 1),
              ((m + 1).choose (i + 1) : ℝ) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ)) :=
          Finset.sum_le_sum hterm
        have hbin : ∑ i ∈ Finset.range (m + 1), ((m + 1).choose (i + 1) : ℝ) ≤ (2 ^ (m + 1) : ℝ) := by
          have hsub : ∑ i ∈ Finset.range (m + 1), (m + 1).choose (i + 1) ≤
              (m + 1).choose 0 + ∑ i ∈ Finset.range (m + 1), (m + 1).choose (i + 1) := Nat.le_add_left _ _
          have hs' : (m + 1).choose 0 + ∑ i ∈ Finset.range (m + 1), (m + 1).choose (i + 1) =
              ∑ i ∈ Finset.range (m + 2), (m + 1).choose i := by
            rw [Finset.sum_range_succ' (fun k => (m + 1).choose k) (m + 1), add_comm]
          rw [hs', Nat.sum_range_choose (m + 1)] at hsub
          exact_mod_cast hsub
        calc _ ≤ (∑ i ∈ Finset.range (m + 1), ((m + 1).choose (i + 1) : ℝ)) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ)) := by
              rw [Finset.sum_mul, Finset.sum_mul]; exact hsum1
          _ ≤ (2 ^ (m + 1) : ℝ) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ)) := by gcongr
      have hpow : u ^ ((-2 : ℝ)) * u ^ ((-1 : ℝ) - (m : ℝ)) = u ^ ((-2 : ℝ) - ((m + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_add hu0]; congr 1; push_cast; ring
      have hconst : (100 : ℝ) * ((2 ^ (m + 1) : ℝ) * (2 * c)) ≤ c + 200 * ((m + 1 : ℝ) * 2 ^ (m + 1)) * c := by
        have hm1 : (1 : ℝ) ≤ (m + 1 : ℝ) := by norm_cast; omega
        have h2c : 0 ≤ (2 ^ (m + 1) : ℝ) * c := by positivity
        calc (100 : ℝ) * ((2 ^ (m + 1) : ℝ) * (2 * c))
            = 200 * (1 * ((2 ^ (m + 1) : ℝ) * c)) := by ring
          _ ≤ 200 * ((m + 1 : ℝ) * ((2 ^ (m + 1) : ℝ) * c)) := by gcongr
          _ ≤ c + 200 * ((m + 1 : ℝ) * 2 ^ (m + 1)) * c := by linarith [hc0]
      calc ‖(fctD (-v) ε u)⁻¹‖ * ‖∑ i ∈ Finset.range (m + 1), _‖
          ≤ (100 * u ^ ((-2 : ℝ))) * ((2 ^ (m + 1) : ℝ) * (2 * c) * u ^ ((-1 : ℝ) - (m : ℝ))) := by gcongr
        _ = (100 * ((2 ^ (m + 1) : ℝ) * (2 * c))) * (u ^ ((-2 : ℝ)) * u ^ ((-1 : ℝ) - (m : ℝ))) := by ring
        _ = (100 * ((2 ^ (m + 1) : ℝ) * (2 * c))) * u ^ ((-2 : ℝ) - ((m + 1 : ℕ) : ℝ)) := by rw [hpow]
        _ ≤ (c + 200 * ((m + 1 : ℝ) * 2 ^ (m + 1)) * c) * u ^ ((-2 : ℝ) - ((m + 1 : ℕ) : ℝ)) := by gcongr

private lemma mid_fctQ_cont {v u : ℝ} (hv : 100 ≤ v) (hu : 2.05 * Real.sqrt v < u) (m : ℕ) :
    Tendsto (fun ε : ℝ => iteratedDeriv m (fctQ (-v) ε) u) (𝓝[>] 0) (𝓝 (iteratedDeriv m (fctQ (-v) 0) u)) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | m
    · simp only [iteratedDeriv_zero, fctQ]
      exact (continuous_fctD_eps (-v) u).continuousAt.tendsto.inv₀ (mid_fctD_ne hv hu) |>.mono_left
        nhdsWithin_le_nhds
    · have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), iteratedDeriv (m + 1) (fctQ (-v) ε) u =
          -(fctD (-v) ε u)⁻¹ * ∑ i ∈ Finset.range (m + 1),
            ((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD (-v) ε) u *
              iteratedDeriv (m + 1 - (i + 1)) (fctQ (-v) ε) u :=
        Filter.Eventually.of_forall fun ε => mid_iteratedDeriv_fctQ_rec hv hu (m + 1) (by omega)
      rw [mid_iteratedDeriv_fctQ_rec hv hu (m + 1) (by omega)]
      refine Filter.Tendsto.congr' (hev.mono fun _ h => h.symm) ?_
      refine ((continuous_fctD_eps (-v) u).continuousAt.tendsto.inv₀
        (mid_fctD_ne hv hu) |>.mono_left nhdsWithin_le_nhds).neg.mul ?_
      refine tendsto_finsetSum _ fun i hi => ?_
      have him : m + 1 - (i + 1) < m + 1 := by omega
      have hD : Tendsto (fun ε => iteratedDeriv (i + 1) (fctD (-v) ε) u) (𝓝[>] 0)
          (𝓝 (iteratedDeriv (i + 1) (fctD (-v) 0) u)) :=
        (continuous_iteratedDeriv_fctD_eps (-v) u (i + 1) (by omega)).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds
      exact (tendsto_const_nhds.mul hD).mul (ih _ him)

private lemma mid_fam_step (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (v V U q A : ℝ) (h : ℝ → ℝ → ℂ),
    100 ≤ v → V = 2.05 * Real.sqrt v → 2.1 * Real.sqrt v ≤ U → Fam V U (n + 1) q A h →
      Fam V U n (q - 3) (K * A) (fun ε => fctDop (-v) ε (h ε)) := by
  obtain ⟨cQ, hcQ0, hcQ⟩ := mid_fctQ_bound (n + 1)
  refine ⟨(2 ^ (n + 1) : ℝ) * cQ, by positivity, fun v V U q A h hv hV hU hF => ?_⟩
  have hsv : 10 ≤ Real.sqrt v := by
    rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
  have hVU : V < U := by rw [hV]; linarith only [hsv, hU]
  have hU0 : 0 < U := by linarith only [hsv, hU]
  have hA0 := hF.A_nonneg hU0
  have hcont_Q : ∀ ε : ℝ, ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fctQ (-v) ε) (Ioi V) := by
    intro ε
    rw [isOpen_Ioi.contDiffOn_iff]
    intro u hu
    rw [hV] at hu
    exact (mid_contDiffAt_fctQ hv hu).of_le (by exact_mod_cast le_top)
  have hVu : ∀ u, U ≤ u → 2.05 * Real.sqrt v < u := fun u hu => by linarith only [hU, hsv, hu]
  have hiter_eq : ∀ {ε u : ℝ} {r : ℕ}, V < u → ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (h ε) u →
      iteratedDeriv r (fctDop (-v) ε (h ε)) u =
        -∑ k ∈ Finset.range (r + 2), ((r + 1).choose k : ℂ) * iteratedDeriv k (h ε) u *
          iteratedDeriv (r + 1 - k) (fctQ (-v) ε) u := by
    intro ε u r hu hcd
    have hu' : 2.05 * Real.sqrt v < u := by rwa [← hV]
    have hcdQ : ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (fctQ (-v) ε) u :=
      (mid_contDiffAt_fctQ hv hu').of_le (by exact_mod_cast le_top)
    have hmul := iteratedDeriv_fun_mul hcd hcdQ (n := r + 1)
    have hd : fctDop (-v) ε (h ε) = -deriv (fun t => h ε t * fctQ (-v) ε t) := rfl
    rw [hd, iteratedDeriv_neg, ← iteratedDeriv_succ', hmul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    have hF1 : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun s => h ε s * fctQ (-v) ε s) (Ioi V) :=
      (hF.smooth ε hε).mul (hcont_Q ε)
    exact (hF1.deriv_of_isOpen isOpen_Ioi (m := (n : WithTop ℕ∞)) (by norm_cast)).neg
  · intro ε hε u huV huU
    have hev : (fun s => h ε s * fctQ (-v) ε s) =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_Ioo.mem_nhds ⟨huV, huU⟩)] with s hs
      rw [hF.zero ε hε s hs.1 hs.2, zero_mul]
    show -deriv (fun s => h ε s * fctQ (-v) ε s) u = 0
    rw [hev.deriv_eq]; simp
  · intro ε hε r hr u hu
    have huV : V < u := lt_of_lt_of_le hVU hu
    have hu' : 2.05 * Real.sqrt v < u := hVu u hu
    have hcd : ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (h ε) u :=
      ((hF.smooth ε hε).contDiffAt (isOpen_Ioi.mem_nhds huV)).of_le (by exact_mod_cast Nat.succ_le_succ hr)
    rw [hiter_eq huV hcd, norm_neg]
    have hu0 : 0 < u := by linarith only [hU0, hu]
    have hterm : ∀ i ∈ Finset.range (r + 2),
        ‖((r + 1).choose i : ℂ) * iteratedDeriv i (h ε) u * iteratedDeriv (r + 1 - i) (fctQ (-v) ε) u‖ ≤
          ((r + 1).choose i : ℝ) * (A * cQ) * u ^ ((q - 3) - (r : ℝ)) := by
      intro i hi
      have hir : i ≤ r + 1 := by have := Finset.mem_range.mp hi; omega
      have h1 := hF.bound ε hε i (by omega) u hu
      have h2 := hcQ v ε u hv hε.1 hε.2 hu' (r + 1 - i) (by omega)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hpow : u ^ (q - (i : ℝ)) * u ^ ((-2 : ℝ) - ((r + 1 - i : ℕ) : ℝ)) = u ^ ((q - 3) - (r : ℝ)) := by
        rw [← Real.rpow_add hu0, Nat.cast_sub hir]; congr 1; push_cast; ring
      calc ((r + 1).choose i : ℝ) * ‖iteratedDeriv i (h ε) u‖ * ‖iteratedDeriv (r + 1 - i) (fctQ (-v) ε) u‖
          ≤ ((r + 1).choose i : ℝ) * (A * u ^ (q - (i : ℝ))) * (cQ * u ^ ((-2 : ℝ) - ((r + 1 - i : ℕ) : ℝ))) := by
            gcongr
        _ = ((r + 1).choose i : ℝ) * (A * cQ) * (u ^ (q - (i : ℝ)) * u ^ ((-2 : ℝ) - ((r + 1 - i : ℕ) : ℝ))) := by
            ring
        _ = ((r + 1).choose i : ℝ) * (A * cQ) * u ^ ((q - 3) - (r : ℝ)) := by rw [hpow]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hbin : ∑ i ∈ Finset.range (r + 2), ((r + 1).choose i : ℝ) = (2 ^ (r + 1) : ℝ) := by
      exact_mod_cast Nat.sum_range_choose (r + 1)
    rw [hbin]
    have hp : 0 ≤ u ^ ((q - 3) - (r : ℝ)) := by positivity
    have h2 : (2 : ℝ) ^ (r + 1) ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hAc : 0 ≤ A * cQ := mul_nonneg hA0 hcQ0
    calc (2 : ℝ) ^ (r + 1) * (A * cQ) * u ^ ((q - 3) - (r : ℝ))
        ≤ 2 ^ (n + 1) * (A * cQ) * u ^ ((q - 3) - (r : ℝ)) := by gcongr
      _ = (2 ^ (n + 1) * cQ * A) * u ^ ((q - 3) - (r : ℝ)) := by ring
  · intro r hr u hu
    have hu' : 2.05 * Real.sqrt v < u := by rwa [← hV]
    have hcdε : ∀ ε ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (h ε) u := fun ε hε =>
      ((hF.smooth ε hε).contDiffAt (isOpen_Ioi.mem_nhds hu)).of_le (by exact_mod_cast Nat.succ_le_succ hr)
    have hlim : Tendsto (fun ε => -∑ k ∈ Finset.range (r + 2),
        ((r + 1).choose k : ℂ) * iteratedDeriv k (h ε) u * iteratedDeriv (r + 1 - k) (fctQ (-v) ε) u) (𝓝[>] 0)
        (𝓝 (-∑ k ∈ Finset.range (r + 2),
        ((r + 1).choose k : ℂ) * iteratedDeriv k (h 0) u * iteratedDeriv (r + 1 - k) (fctQ (-v) 0) u)) := by
      refine (tendsto_finsetSum _ fun k hk => ?_).neg
      have hkr : k ≤ r + 1 := by have := Finset.mem_range.mp hk; omega
      refine (tendsto_const_nhds.mul (hF.cont k (by omega) u hu)).mul ?_
      exact mid_fctQ_cont hv hu' (r + 1 - k)
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    have hlim' := hlim.congr' (by
      filter_upwards [hmem] with ε hε
      exact (hiter_eq hu (hcdε ε ⟨hε.1.le, hε.2.le⟩)).symm)
    rw [hiter_eq hu (hcdε 0 ⟨le_rfl, zero_le_one⟩)]
    exact hlim'

private lemma mid_fam_main : ∀ n : ℕ, ∀ q : ℝ, q < 3 * n - 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (v V U A : ℝ) (h : ℝ → ℝ → ℂ), 100 ≤ v → V = 2.05 * Real.sqrt v → 2.1 * Real.sqrt v ≤ U → Fam V U n q A h →
      ∃ R : ℂ, Tendsto (fun ε => ∫ u in Ioi U, h ε u * Complex.exp (fctW (-v) ε u)) (𝓝[>] 0) (𝓝 R) ∧
        ‖R‖ ≤ C * A * U ^ (q + 1 - 3 * (n : ℝ)) := by
  intro n
  induction n with
  | zero =>
    intro q hq
    have hq' : q < -1 := by simpa using hq
    refine ⟨1 / (-q - 1), div_nonneg zero_le_one (by linarith), fun v V U A h hv hV hU hF => ?_⟩
    have hsv : 10 ≤ Real.sqrt v := by
      rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
    have hU0 : 0 < U := by linarith only [hsv, hU]
    have hU1 : 1 ≤ U := by linarith only [hsv, hU]
    have hVU : V < U := by rw [hV]; linarith only [hsv, hU]
    have hA0 := hF.A_nonneg hU0
    have hbd : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ u, U ≤ u → ‖h ε u‖ ≤ A * u ^ q := fun ε hε u hu => by
      simpa using hF.bound ε hε 0 le_rfl u hu
    have hint : IntegrableOn (fun u : ℝ => A * u ^ q) (Ioi U) :=
      (integrableOn_Ioi_rpow_of_lt hq' hU0).const_mul A
    have hmeas : ∀ ε ∈ Icc (0 : ℝ) 1, ContinuousOn (h ε) (Ioi U) := fun ε hε =>
      ((hF.smooth ε hε).continuousOn).mono (Ioi_subset_Ioi hVU.le)
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    have hbnd : ‖∫ u in Ioi U, h 0 u * Complex.exp (fctW (-v) 0 u)‖ ≤
        1 / (-q - 1) * A * U ^ (q + 1 - 3 * ((0 : ℕ) : ℝ)) := by
      have hg : ∀ u ∈ Ioi U, ‖h 0 u * Complex.exp (fctW (-v) 0 u)‖ ≤ A * u ^ q := fun u hu => by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le le_rfl u)).trans
          (hbd 0 ⟨le_rfl, zero_le_one⟩ u (le_of_lt hu))
      refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hg))).trans ?_
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hq' hU0]
      have : -U ^ (q + 1) / (q + 1) = (1 / (-q - 1)) * U ^ (q + 1) := by
        have h1 : q + 1 ≠ 0 := by linarith
        have h2 : -q - 1 = -(q + 1) := by ring
        rw [h2, one_div, inv_neg, neg_mul, inv_mul_eq_div, neg_div]
      rw [this]
      simp only [Nat.cast_zero, mul_zero, sub_zero]
      exact le_of_eq (by ring)
    refine ⟨∫ u in Ioi U, h 0 u * Complex.exp (fctW (-v) 0 u), ?_, hbnd⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun u => A * u ^ q) ?_ ?_ hint ?_
    · filter_upwards [hmem] with ε hε
      exact ((hmeas ε ⟨hε.1.le, hε.2.le⟩).mul (continuous_fctW (-v) ε).cexp.continuousOn).aestronglyMeasurable
        measurableSet_Ioi
    · filter_upwards [hmem] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le hε.1.le u)).trans
        (hbd ε ⟨hε.1.le, hε.2.le⟩ u (le_of_lt hu))
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
      have hu' : V < u := hVU.trans hu
      have h1 : Tendsto (fun ε => h ε u) (𝓝[>] 0) (𝓝 (h 0 u)) := by
        simpa using hF.cont 0 le_rfl u hu'
      have h2 : Tendsto (fun ε : ℝ => Complex.exp (fctW (-v) ε u)) (𝓝[>] 0) (𝓝 (Complex.exp (fctW (-v) 0 u))) :=
        (((continuous_fctW_eps (-v) u).cexp).tendsto 0).mono_left nhdsWithin_le_nhds
      exact h1.mul h2
  | succ n ih =>
    intro q hq
    obtain ⟨C', hC'0, hC'⟩ := ih (q - 3) (by push_cast at hq; linarith)
    obtain ⟨K, hK0, hK⟩ := mid_fam_step n
    refine ⟨C' * K, mul_nonneg hC'0 hK0, fun v V U A h hv hV hU hF => ?_⟩
    have hsv : 10 ≤ Real.sqrt v := by
      rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
    have hU0 : 0 < U := by linarith only [hsv, hU]
    have hU1 : 1 ≤ U := by linarith only [hsv, hU]
    have hVU : V < U := by rw [hV]; linarith only [hsv, hU]
    have hF' := hK v V U q A h hv hV hU hF
    obtain ⟨R, hR, hRb⟩ := hC' v V U (K * A) _ hv hV hU hF'
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    have hibp : ∀ ε ∈ Ioo (0 : ℝ) 1, (∫ u in Ioi U, fctDop (-v) ε (h ε) u * Complex.exp (fctW (-v) ε u)) =
        ∫ u in Ioi U, h ε u * Complex.exp (fctW (-v) ε u) := by
      intro ε hε
      have hε' : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1.le, hε.2.le⟩
      have hA0 := hF.A_nonneg hU0
      symm
      refine ibp_cexp (U := U) (g := h ε) (D := fctD (-v) ε) (w := fctW (-v) ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro u hu
        exact ((hF.smooth ε hε').contDiffAt (isOpen_Ioi.mem_nhds (lt_trans hVU hu))).differentiableAt
          (by exact_mod_cast Nat.succ_ne_zero n)
      · intro u _; exact hasDerivAt_fctW (-v) ε u
      · intro u hu
        have hu' : 2.05 * Real.sqrt v < u := by rw [← hV]; exact lt_trans hVU hu
        exact mid_fctD_ne hv hu'
      · intro u _; exact (hasDerivAt_fctD (-v) ε u).differentiableAt
      · exact norm_exp_fctW_le hε.1.le
      · refine integrableOn_amp (σ := q) (A := A) hU1 hε.1
          ((hF.smooth ε hε').continuousOn.mono (Ioi_subset_Ioi hVU.le)) ?_
        intro u hu; simpa using hF.bound ε hε' 0 (Nat.zero_le _) u hu
      · refine integrableOn_amp (σ := q - 3) (A := K * A) hU1 hε.1
          ((hF'.smooth ε hε').continuousOn.mono (Ioi_subset_Ioi hVU.le)) ?_
        intro u hu; simpa [fctDop, fctQ] using hF'.bound ε hε' 0 (Nat.zero_le _) u hu
      · have hc1 : ContinuousAt (fun u => h ε u * fctQ (-v) ε u) U := by
          refine ContinuousAt.mul ((hF.smooth ε hε').continuousOn.continuousAt (isOpen_Ioi.mem_nhds hVU)) ?_
          exact (mid_contDiffAt_fctQ hv (by rw [← hV]; exact hVU)).continuousAt
        have := hc1.tendsto
        rw [hF.zero_at hVU hε', zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · refine tendsto_amp_top (σ := q - 2) (A := 100 * A) (U := U)
          (g := fun u => h ε u * (fctD (-v) ε u)⁻¹) hε.1 ?_
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le hU0 hu
        have h1 := hF.bound ε hε' 0 (Nat.zero_le _) u hu
        have h2 := mid_fctQ_norm_zero (ε := ε) hv (show 2.05 * Real.sqrt v < u by linarith only [hU, hu, hsv])
        simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1 h2
        rw [norm_mul]
        calc ‖h ε u‖ * ‖(fctD (-v) ε u)⁻¹‖ ≤ (A * u ^ q) * (100 * u ^ (-2 : ℝ)) :=
              mul_le_mul h1 (by simpa [fctQ] using h2) (norm_nonneg _) (by positivity)
          _ = 100 * A * u ^ (q - 2) := by
              rw [show q - 2 = q + (-2) by ring, Real.rpow_add hu0]; ring
    have he : (q - 3) + 1 - 3 * (n : ℝ) = q + 1 - 3 * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    refine ⟨R, hR.congr' (by filter_upwards [hmem] with ε hε; exact hibp ε hε), ?_⟩
    refine hRb.trans ?_
    rw [he]; exact le_of_eq (by ring)

/-- **Middle-band cutoff-tail Abel IBP**: for `v ≥ 100`, `2.1 * √v ≤ U`, and `κ ∈ FctSymCls n p B`
vanishing on `[0, U]` (`p < 3n - 1/2`), `FctSLimit (-v) κ (fctS (-v) κ)` holds and
`‖fctS (-v) κ‖ ≤ C * B * U ^ (p + 1/2 - 3n)`. -/
theorem mid_abel_tail_ibp (n : ℕ) (p : ℝ) (hp : p < 3 * n - 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v U B : ℝ) (κ : ℝ → ℂ), 100 ≤ v → 2.1 * Real.sqrt v ≤ U → 0 ≤ B →
      FctSymCls n p B κ → (∀ u ∈ Icc (0 : ℝ) U, κ u = 0) →
      (∃ L, FctSLimit (-v) κ L) ∧ ‖fctS (-v) κ‖ ≤ C * B * U ^ (p + 1 / 2 - 3 * n) := by
  have hq : p - 1 / 2 < 3 * (n : ℝ) - 1 := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := mid_fam_main n (p - 1 / 2) hq
  obtain ⟨Ar, hAr0, hAr⟩ := fctRho_sbd n
  let Ct : ℝ := 2 ^ n * Ar * (2 : ℝ) ^ (|p| + n)
  have hCt0 : 0 ≤ Ct := by positivity
  refine ⟨C₁ * Ct, mul_nonneg hC₁0 hCt0, fun v U B κ hv hU hB hκ hzero => ?_⟩
  have hsv : 10 ≤ Real.sqrt v := by
    rw [show (10 : ℝ) = Real.sqrt 100 by norm_num]; exact Real.sqrt_le_sqrt hv
  have hU0 : 0 < U := by linarith only [hsv, hU]
  set V : ℝ := 2.05 * Real.sqrt v
  have hVU : V < U := by dsimp only [V]; linarith only [hsv, hU]
  have hV_nn : 0 ≤ V := by dsimp only [V]; positivity
  obtain ⟨hκc, hκb⟩ := kappa_sbd hκ hB
  have hsub : Ioi V ⊆ Ioi 0 := Ioi_subset_Ioi hV_nn
  have hr : ContDiffOn ℝ n fctRho (Ioi V) := (contDiffOn_fctRho n).mono hsub
  have hk : ContDiffOn ℝ n κ (Ioi V) := hκc.mono hsub
  have h2 := SBd.mul (V := V) hVU hU0 hr hk (hAr.mono_U (by linarith : (1 : ℝ) ≤ U))
    (hκb.mono_U (by linarith : (2 : ℝ) ≤ U))
  have he : (-(1 / 2 : ℝ)) + p = p - 1 / 2 := by ring
  rw [he] at h2
  have hSB : SBd n U (p - 1 / 2) (Ct * B) (fun u => fctRho u * κ u) :=
    h2.mono_q_A (le_of_eq (by dsimp only [Ct]; ring)) (by linarith)
  have hFam : Fam V U n (p - 1 / 2) (Ct * B) (fun _ u => fctRho u * κ u) :=
    fam_const (hr.mul hk) (fun u huV huU => by rw [hzero u ⟨by linarith only [hV_nn, huV], huU.le⟩, mul_zero]) hSB
  obtain ⟨R, hR, hRb⟩ := hC₁ v V U (Ct * B) _ hv rfl hU hFam
  have hlim_eq : ∀ ε : ℝ, 0 < ε → fctSEps (-v) ε κ =
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
        ∫ u in Ioi U, fctRho u * κ u * Complex.exp (fctW (-v) ε u) := by
    intro ε _
    rw [fctSEps_eq]
    congr 1
    have hpt : (fun u => fctRho u * Complex.exp (fctW (-v) ε u) * κ u) =
        fun u => fctRho u * κ u * Complex.exp (fctW (-v) ε u) := funext fun u => by ring
    rw [hpt]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (f := fun u => fctRho u * κ u * Complex.exp (fctW (-v) ε u))
      measurableSet_Ioi (Ioi_subset_Ioi hU0.le) ?_
    intro u hu
    have hu_le : u ≤ U := by by_contra hgt; exact hu.2 (not_le.mp hgt)
    rw [hzero u ⟨hu.1.le, hu_le⟩, mul_zero, zero_mul]
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hS_lim : FctSLimit (-v) κ (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * R) := by
    unfold FctSLimit
    refine (hR.const_mul (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I))).congr' ?_
    filter_upwards [hmem] with ε hε
    exact (hlim_eq ε hε.1).symm
  refine ⟨⟨_, hS_lim⟩, ?_⟩
  rw [hS_lim.fctS_eq, norm_mul, norm_phase, one_mul]
  refine hRb.trans ?_
  have hp_eq : (p - 1 / 2) + 1 - 3 * (n : ℝ) = p + 1 / 2 - 3 * (n : ℝ) := by ring
  rw [hp_eq]
  exact le_of_eq (by ring)

end MidTailIbp

/-- info: 'FormalResearch.SignUncertainty.airyEnergy_two_sided' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyEnergy_two_sided

/-- info: 'FormalResearch.SignUncertainty.bleistein_airy_energy_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bleistein_airy_energy_id

/-- info: 'FormalResearch.SignUncertainty.bleistein_airy_energy_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bleistein_airy_energy_lower

/-- info: 'FormalResearch.SignUncertainty.mid_abel_tail_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mid_abel_tail_ibp

end FormalResearch.SignUncertainty

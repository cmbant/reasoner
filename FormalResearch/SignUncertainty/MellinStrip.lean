module

public import FormalResearch.SignUncertainty.HankelMellinKernel
public import FormalResearch.SignUncertainty.Radii

/-!
# The Mellin strip of a Hankel eigenfunction (`gt:7.4(1)`)

For `f ∈ 𝒜_c^ε` (`IsHankelEigenfn c ε f`) put
`mellinStrip c f z = (2π)^z Γ(z)^{-1} ∫_0^∞ f(Δ) Δ^{z-1} dΔ` (`fourier_mellin.tex`).

* `integrableOn_abs_mul_rpow_eigen`: the Mellin integrand is absolutely integrable for `0 < Re z ≤ c`.
* `mellinStrip_reflection_of_re_lt`: the reflection `M̃_f(c - z) = ε M̃_f(z)` for `0 < Re z < c/2 - 1/4`
  (Weber's integral and Fubini, `hankelMellin_mul_gamma`, `mellin_hankel_fubini`), `c > 3/2`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- The Mellin integrand of `f ∈ 𝒜_c^ε` is absolutely integrable for `0 < x ≤ c`. -/
theorem integrableOn_abs_mul_rpow_eigen {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {x : ℝ} (hx0 : 0 < x) (hxc : x ≤ c) :
    IntegrableOn (fun Δ : ℝ => |f Δ| * Δ ^ (x - 1)) (Ioi 0) := by
  have hmeas : ∀ t : Set ℝ, MeasurableSet t → t ⊆ Ioi 0 →
      AEStronglyMeasurable (fun Δ : ℝ => |f Δ| * Δ ^ (x - 1)) (volume.restrict t) :=
    fun t ht hts => ContinuousOn.aestronglyMeasurable
      ((continuous_abs.comp_continuousOn (hf.cont.mono fun Δ hΔ => le_of_lt (hts hΔ))).mul
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (ne_of_gt (hts hw)))) ht
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      (f := f) (hf.cont.mono fun Δ hΔ => hΔ.1)
    have hint : IntegrableOn (fun Δ : ℝ => K * Δ ^ (x - 1)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < x - 1))).const_mul K
    refine Integrable.mono' hint (hmeas _ measurableSet_Ioc fun Δ hΔ => hΔ.1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with Δ hΔ
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hΔ.1.le _)]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hK Δ ⟨hΔ.1.le, hΔ.2⟩)
      (Real.rpow_nonneg hΔ.1.le _)
  · have hρ := abs_mul_rho0_integrableOn hc hf.int
    have hint : IntegrableOn (fun Δ : ℝ => (Real.Gamma c / (2 * π) ^ c) *
        (|f Δ| * hankelRho0 c Δ)) (Ioi 1) := (hρ.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
    refine Integrable.mono' hint (hmeas _ measurableSet_Ioi fun Δ hΔ => lt_trans zero_lt_one hΔ) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with Δ hΔ
    have hΔ0 : 0 < Δ := lt_trans zero_lt_one hΔ
    have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
    have hp : 0 < (2 * π) ^ c := Real.rpow_pos_of_pos (by positivity) c
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hΔ0.le _)]
    have hle : Δ ^ (x - 1) ≤ Δ ^ (c - 1) :=
      Real.rpow_le_rpow_of_exponent_le hΔ.le (by linarith)
    have e : (Real.Gamma c / (2 * π) ^ c) * (|f Δ| * hankelRho0 c Δ) = |f Δ| * Δ ^ (c - 1) := by
      unfold hankelRho0; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg _)


/-- The raw Mellin integral `∫_0^∞ f(Δ) Δ^{z-1} dΔ`. -/
noncomputable def mellinRaw (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ Δ in Ioi (0 : ℝ), (f Δ : ℂ) * (Δ : ℂ) ^ (z - 1)

/-- `M̃_f(z) = (2π)^z Γ(z)^{-1} ∫_0^∞ f(Δ) Δ^{z-1} dΔ` (`fourier_mellin.tex`). -/
noncomputable def mellinStrip (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ((2 * π : ℝ) : ℂ) ^ z / Complex.Gamma z * mellinRaw f z

/-- **Reflection on the Weber range** (`gt:7.4(1)`, first half): for `c > 3/2`, `f ∈ 𝒜_c^ε`,
`ε = ±1` and `0 < Re z < c/2 - 1/4`, `M̃_f(c - z) = ε M̃_f(z)`. -/
theorem mellinStrip_reflection_of_re_lt {c ε : ℝ} (hc : 3 / 2 < c) {f : ℝ → ℝ}
    (hf : IsHankelEigenfn c ε f) {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < c / 2 - 1 / 4) :
    mellinStrip f ((c : ℂ) - z) = (ε : ℂ) * mellinStrip f z := by
  have hc0 : 0 < c := by linarith
  have hfc : ContinuousOn f (Ioi 0) := hf.cont.mono Ioi_subset_Ici_self
  have hint : IntegrableOn (fun s : ℝ => |f s| * s ^ (c - 1 - z.re)) (Ioi 0) := by
    have h := integrableOn_abs_mul_rpow_eigen hc0 hf (x := c - z.re) (by linarith) (by linarith)
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    rw [show c - z.re - 1 = c - 1 - z.re by ring]
  have F := mellin_hankel_fubini hc hz0 hz1 hfc hint
  have W := hankelMellin_mul_gamma hc hz0 hz1
  have hL : ∫ Δ in Ioi (0 : ℝ), (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c f Δ : ℂ) =
      (ε : ℂ) * mellinRaw f z := by
    unfold mellinRaw
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
    rw [hf.eigen Δ (le_of_lt hΔ)]
    push_cast
    ring
  have hR : ∫ s in Ioi (0 : ℝ), (f s : ℂ) * (s : ℂ) ^ ((c : ℂ) - 1 - z) = mellinRaw f ((c : ℂ) - z) := by
    unfold mellinRaw
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [show (c : ℂ) - z - 1 = (c : ℂ) - 1 - z by ring]
  rw [hL, hR] at F
  -- algebra
  have hr : (0 : ℝ) < 2 * π := by positivity
  have hinv : ∀ w : ℂ, (1 / ((2 * π : ℝ) : ℂ)) ^ w = (((2 * π : ℝ) : ℂ) ^ w)⁻¹ := fun w => by
    rw [one_div, Complex.inv_cpow]
    rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
  rw [hinv, hinv] at W
  have hz : (((2 * π : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hr.ne'
  have hX : ((2 * π : ℝ) : ℂ) ^ z ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp 
  have hY : ((2 * π : ℝ) : ℂ) ^ ((c : ℂ) - z) ≠ 0 := by rw [Ne, Complex.cpow_eq_zero_iff]; simp 
  have hGz : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz0
  have hGc : Complex.Gamma ((c : ℂ) - z) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using (by linarith : z.re < c))
  unfold mellinStrip
  set Φ := hankelMellin c z
  set a : ℂ := (((2 * π) ^ c / Real.Gamma c : ℝ) : ℂ)
  set X := ((2 * π : ℝ) : ℂ) ^ z
  set Y := ((2 * π : ℝ) : ℂ) ^ ((c : ℂ) - z)
  set Mz := mellinRaw f z
  set Mc := mellinRaw f ((c : ℂ) - z)
  have hΦ : Φ * a = X⁻¹ * Complex.Gamma z * Y / Complex.Gamma ((c : ℂ) - z) := by
    rw [eq_div_iff hGc]
    calc Φ * a * Complex.Gamma ((c : ℂ) - z) = Φ * a * (Y⁻¹ * Complex.Gamma ((c : ℂ) - z)) * Y := by
          field_simp
      _ = _ := by rw [W]
  have hMz : (ε : ℂ) * Mz = Φ * a * Mc := F
  calc Y / Complex.Gamma ((c : ℂ) - z) * Mc
      = X / Complex.Gamma z * (Φ * a) * Mc := by rw [hΦ]; field_simp
    _ = X / Complex.Gamma z * (Φ * a * Mc) := by ring
    _ = (ε : ℂ) * (X / Complex.Gamma z * Mz) := by rw [← hMz]; ring

/-- info: 'FormalResearch.SignUncertainty.mellinStrip_reflection_of_re_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellinStrip_reflection_of_re_lt

end FormalResearch.SignUncertainty

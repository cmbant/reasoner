module

public import FormalResearch.SignUncertainty.HankelBesselData
public import FormalResearch.SignUncertainty.HankelAntiderivLimit
public import FormalResearch.SignUncertainty.HankelBesselLaguerre

/-!
# Mellin transform of the Hankel kernel and the Mellin–Fubini identity

For `c > 3/2` and `0 < x < c/2 - 1/4` the Mellin integral `∫_0^∞ φ_c(w) w^{z-1} dw` (`Re z = x`) converges
absolutely (`|φ_c| ≤ 1`, `|φ_c(w)| ≤ K w^{-(c/2-1/4)}` for `w ≥ 1`). This is the decay input of the
Weber integral used in the proof of `gt:7.4(1)` (`fourier_mellin_proofs.tex`).

* `abs_hankelPhi_tail`: `|φ_c(w)| ≤ K w^{-(c/2-1/4)}` for `w ≥ 1`, `c > 3/2`.
* `integrableOn_abs_phi_mellin`: `w ↦ |φ_c(w)| w^{x-1}` is integrable on `(0,∞)`.
* `hankelMellin c z = ∫_0^∞ φ_c(w) w^{z-1} dw`, scaling lemmas `integral_phi_scale`, `integral_scale_real`.
* `mellin_hankel_fubini`: `∫ Δ^{z-1} (𝓗_c g)(Δ) dΔ = Φ_c(z) ((2π)^c/Γ(c)) ∫ g(s) s^{c-1-z} ds`.
* `hankelMellin_mul_gamma`: Weber's integral in product form,
  `Φ_c(z) ((2π)^c/Γ(c)) (1/2π)^{c-z} Γ(c-z) = (1/2π)^z Γ(z)`, obtained from the Laguerre eigenfunction
  `e^{-2πs}` (`besselHankelTransform_exp`) and Fubini; no Bessel integral tables are used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- Tail bound for `φ_c` itself: `|φ_c(w)| ≤ K w^{-(c/2-1/4)}` for `w ≥ 1`, `c > 3/2`. -/
theorem abs_hankelPhi_tail {c : ℝ} (hc : 3 / 2 < c) :
    ∃ K : ℝ, ∀ w ≥ (1 : ℝ), |hankelPhi c w| ≤ K * w ^ (-(c / 2 - 1 / 4)) := by
  obtain ⟨K, hK⟩ := hankelPhi_tail (c := c - 1) (by linarith)
  refine ⟨K, fun w hw => ?_⟩
  have h := hK w hw
  rw [sub_add_cancel] at h
  rwa [show -(c / 2 - 1 / 4) = -((c - 1) / 2 + 1 / 4) by ring]

/-- The Mellin integrand `|φ_c(w)| w^{x-1}` is integrable on `(0,∞)` for `0 < x < c/2 - 1/4`. -/
theorem integrableOn_abs_phi_mellin {c x : ℝ} (hc : 3 / 2 < c) (hx : 0 < x)
    (hx' : x < c / 2 - 1 / 4) :
    IntegrableOn (fun w : ℝ => |hankelPhi c w| * w ^ (x - 1)) (Ioi 0) := by
  obtain ⟨K, hK⟩ := abs_hankelPhi_tail hc
  have hmeas : ∀ t : Set ℝ, MeasurableSet t → t ⊆ Ioi 0 →
      AEStronglyMeasurable (fun w : ℝ => |hankelPhi c w| * w ^ (x - 1)) (volume.restrict t) :=
    fun t ht hts => ContinuousOn.aestronglyMeasurable
      ((continuous_abs.comp (hankelPhi_continuous c)).continuousOn.mul
        (ContinuousOn.rpow_const continuousOn_id fun w hw => Or.inl (ne_of_gt (hts hw)))) ht
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  refine IntegrableOn.union ?_ ?_
  · -- near 0: `|φ| ≤ 1`
    have hint : IntegrableOn (fun w : ℝ => w ^ (x - 1)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < x - 1))
    refine Integrable.mono' hint (hmeas _ measurableSet_Ioc fun w hw => hw.1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hw.1.le _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hw.1.le _) (abs_hankelPhi_le_one (by linarith) w)
  · -- tail: `|φ(w)| ≤ K w^{-(c/2-1/4)}`
    have hint : IntegrableOn (fun w : ℝ => |K| * w ^ (x - 1 - (c / 2 - 1 / 4))) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul _
    refine Integrable.mono' hint (hmeas _ measurableSet_Ioi fun w hw => lt_trans zero_lt_one hw) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hw0 : 0 < w := lt_trans zero_lt_one hw
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hw0.le _)]
    have h1 := hK w hw.le
    calc |hankelPhi c w| * w ^ (x - 1) ≤ (K * w ^ (-(c / 2 - 1 / 4))) * w ^ (x - 1) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hw0.le _)
      _ ≤ |K| * w ^ (-(c / 2 - 1 / 4)) * w ^ (x - 1) := by
          gcongr
          exact le_abs_self K
      _ = |K| * w ^ (x - 1 - (c / 2 - 1 / 4)) := by
          rw [mul_assoc, ← Real.rpow_add hw0]; ring_nf


/-! ### The Mellin transform of `φ_c` and scaling -/

open Complex in
/-- `Φ_c(z) = ∫_0^∞ φ_c(w) w^{z-1} dw`. -/
noncomputable def hankelMellin (c : ℝ) (z : ℂ) : ℂ :=
  ∫ w in Ioi (0 : ℝ), (hankelPhi c w : ℂ) * (w : ℂ) ^ (z - 1)

/-- Norm of the complex power: `‖w^{z-1}‖ = w^{Re z - 1}` for `w > 0`. -/
lemma norm_cpow_sub_one {w : ℝ} (hw : 0 < w) (z : ℂ) :
    ‖(w : ℂ) ^ (z - 1)‖ = w ^ (z.re - 1) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hw]
  simp

lemma integrableOn_phi_mellin {c : ℝ} (hc : 3 / 2 < c) {z : ℂ} (hz0 : 0 < z.re)
    (hz1 : z.re < c / 2 - 1 / 4) :
    IntegrableOn (fun w : ℝ => (hankelPhi c w : ℂ) * (w : ℂ) ^ (z - 1)) (Ioi 0) := by
  have h := integrableOn_abs_phi_mellin hc hz0 hz1
  have hm : AEStronglyMeasurable (fun w : ℝ => (hankelPhi c w : ℂ) * (w : ℂ) ^ (z - 1))
      (volume.restrict (Ioi 0)) :=
    ContinuousOn.aestronglyMeasurable
      ((Complex.continuous_ofReal.comp (hankelPhi_continuous c)).continuousOn.mul
        (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
          fun w hw => Or.inl (by simpa using (mem_Ioi.mp hw)))) measurableSet_Ioi
  refine h.mono' hm ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [norm_mul, norm_cpow_sub_one hw, Complex.norm_real, Real.norm_eq_abs]

/-- Scaling: for `s > 0`, `∫_0^∞ φ_c(Δ s) Δ^{z-1} dΔ = s^{-z} Φ_c(z)`. -/
lemma integral_phi_scale {c : ℝ} {s : ℝ} (hs : 0 < s) (z : ℂ) :
    ∫ Δ in Ioi (0 : ℝ), (hankelPhi c (Δ * s) : ℂ) * (Δ : ℂ) ^ (z - 1) =
      (s : ℂ) ^ (-z) * hankelMellin c z := by
  have hpt : ∀ Δ : ℝ, 0 < Δ → (hankelPhi c (Δ * s) : ℂ) * (Δ : ℂ) ^ (z - 1) =
      ((s : ℂ) ^ (z - 1))⁻¹ *
        ((hankelPhi c (s * Δ) : ℂ) * ((s * Δ : ℝ) : ℂ) ^ (z - 1)) := by
    intro Δ hΔ
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hs.le hΔ.le, mul_comm Δ s]
    have : (s : ℂ) ^ (z - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hs.ne']
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have h1 := integral_comp_mul_left_Ioi (fun w : ℝ => (hankelPhi c w : ℂ) * (w : ℂ) ^ (z - 1)) 0 hs
  rw [mul_zero] at h1
  unfold hankelMellin
  rw [h1, Complex.real_smul]
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [Complex.cpow_neg, show (s : ℂ) ^ z = (s : ℂ) ^ (z - 1) * s by
    conv_lhs => rw [show z = (z - 1) + 1 by ring]
    rw [Complex.cpow_add _ _ hs0, Complex.cpow_one]]
  push_cast
  field_simp


/-- Real scaling: `∫_0^∞ G(Δ s) Δ^{x-1} dΔ = s^{-x} ∫_0^∞ G(w) w^{x-1} dw`. -/
lemma integral_scale_real (G : ℝ → ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    ∫ Δ in Ioi (0 : ℝ), G (Δ * s) * Δ ^ (x - 1) =
      s ^ (-x) * ∫ w in Ioi (0 : ℝ), G w * w ^ (x - 1) := by
  have hpt : ∀ Δ : ℝ, 0 < Δ → G (Δ * s) * Δ ^ (x - 1) =
      (s ^ (x - 1))⁻¹ * (G (s * Δ) * (s * Δ) ^ (x - 1)) := by
    intro Δ hΔ
    rw [Real.mul_rpow hs.le hΔ.le, mul_comm Δ s]
    have : s ^ (x - 1) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have h1 := integral_comp_mul_left_Ioi (fun w : ℝ => G w * w ^ (x - 1)) 0 hs
  rw [mul_zero] at h1
  rw [h1, smul_eq_mul]
  have e : s ^ (-x) = (s ^ (x - 1))⁻¹ * s⁻¹ := by
    rw [← Real.rpow_neg hs.le, ← Real.rpow_neg_one, ← Real.rpow_add hs]; ring_nf
  rw [e]; ring


/-! ### The Mellin–Fubini identity -/

/-- **Mellin–Fubini identity.** For `c > 3/2`, `0 < Re z < c/2 - 1/4` and `g` continuous with
`∫ |g| s^{c-1-Re z} < ∞`:
`∫_0^∞ Δ^{z-1} (𝓗_c g)(Δ) dΔ = Φ_c(z) · ((2π)^c/Γ(c)) · ∫_0^∞ g(s) s^{c-1-z} ds`. -/
theorem mellin_hankel_fubini {c : ℝ} (hc : 3 / 2 < c) {z : ℂ} (hz0 : 0 < z.re)
    (hz1 : z.re < c / 2 - 1 / 4) {g : ℝ → ℝ} (hgc : ContinuousOn g (Ioi 0))
    (hg : IntegrableOn (fun s : ℝ => |g s| * s ^ (c - 1 - z.re)) (Ioi 0)) :
    ∫ Δ in Ioi (0 : ℝ), (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c g Δ : ℂ) =
      hankelMellin c z * (((2 * π) ^ c / Real.Gamma c : ℝ) : ℂ) *
        ∫ s in Ioi (0 : ℝ), (g s : ℂ) * (s : ℂ) ^ ((c : ℂ) - 1 - z) := by
  have hc0 : 0 < c := by linarith
  set x := z.re with hx
  set a : ℝ := (2 * π) ^ c / Real.Gamma c with ha
  have hρ : ∀ s : ℝ, hankelRho0 c s = a * s ^ (c - 1) := fun s => rfl
  have hA := integrableOn_abs_phi_mellin hc hz0 hz1
  set A : ℝ := ∫ w in Ioi (0 : ℝ), |hankelPhi c w| * w ^ (x - 1) with hAdef
  let Fd : ℝ → ℝ → ℂ := fun Δ s =>
    (Δ : ℂ) ^ (z - 1) * ((g s * hankelRho0 c s * hankelPhi c (Δ * s) : ℝ) : ℂ)
  -- inner integrability and norm integral
  have hinner : ∀ s ∈ Ioi (0 : ℝ), IntegrableOn (fun Δ => Fd Δ s) (Ioi 0) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hI := integrableOn_phi_mellin hc hz0 hz1
    have hI' : IntegrableOn (fun Δ : ℝ => (hankelPhi c (s * Δ) : ℂ) * ((s * Δ : ℝ) : ℂ) ^ (z - 1))
        (Ioi 0) := by
      rw [integrableOn_Ioi_comp_mul_left_iff (fun w : ℝ => (hankelPhi c w : ℂ) * (w : ℂ) ^ (z - 1))
        0 hs0, mul_zero]
      exact hI
    have hI'' : IntegrableOn (fun Δ : ℝ => (((g s * hankelRho0 c s : ℝ)) : ℂ) *
        (((s : ℂ) ^ (z - 1))⁻¹ * ((hankelPhi c (s * Δ) : ℂ) * ((s * Δ : ℝ) : ℂ) ^ (z - 1))))
        (Ioi 0) := (hI'.const_mul (((s : ℂ) ^ (z - 1))⁻¹)).const_mul (((g s * hankelRho0 c s : ℝ)) : ℂ)
    refine hI''.congr_fun (fun Δ hΔ => ?_) measurableSet_Ioi
    have hΔ0 : 0 < Δ := hΔ
    simp only [Fd]
    have hmulc : ((s * Δ : ℝ) : ℂ) ^ (z - 1) = (s : ℂ) ^ (z - 1) * (Δ : ℂ) ^ (z - 1) := by
      rw [Complex.ofReal_mul]; exact Complex.mul_cpow_ofReal_nonneg hs0.le hΔ0.le _
    rw [hmulc, mul_comm Δ s]
    have : (s : ℂ) ^ (z - 1) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; simp [hs0.ne']
    push_cast
    field_simp
  have hnorm : ∀ s ∈ Ioi (0 : ℝ), ∫ Δ in Ioi (0 : ℝ), ‖Fd Δ s‖ =
      |g s| * hankelRho0 c s * (s ^ (-x) * A) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hρ0 : 0 ≤ hankelRho0 c s := hankelRho0_nonneg hc0 hs0.le
    have hpt : ∀ Δ ∈ Ioi (0 : ℝ), ‖Fd Δ s‖ =
        |g s| * hankelRho0 c s * (|hankelPhi c (Δ * s)| * Δ ^ (x - 1)) := by
      intro Δ hΔ
      have hΔ0 : 0 < Δ := hΔ
      simp only [Fd]
      rw [norm_mul, norm_cpow_sub_one hΔ0, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hρ0]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_scale_real (fun w => |hankelPhi c w|) hs0 x]
  have hmeas : AEStronglyMeasurable (Function.uncurry Fd)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
    have h1 : ContinuousOn (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (z - 1)) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      ContinuousOn.cpow_const (Complex.continuous_ofReal.comp continuous_fst).continuousOn
        fun p hp => Or.inl (by simpa using (mem_Ioi.mp hp.1))
    have h2 : ContinuousOn (fun p : ℝ × ℝ => g p.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      hgc.comp continuous_snd.continuousOn fun p hp => hp.2
    have h3 : ContinuousOn (fun p : ℝ × ℝ => hankelRho0 c p.2) (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
      (continuousOn_hankelRho0 c).comp continuous_snd.continuousOn fun p hp => hp.2
    have h4 : Continuous fun p : ℝ × ℝ => hankelPhi c (p.1 * p.2) :=
      (hankelPhi_continuous c).comp (continuous_fst.mul continuous_snd)
    exact h1.mul (Complex.continuous_ofReal.comp_continuousOn ((h2.mul h3).mul h4.continuousOn))
  have hF : Integrable (Function.uncurry Fd)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      exact hinner s hs
    · have hdom : IntegrableOn (fun s : ℝ => (A * a) * (|g s| * s ^ (c - 1 - x))) (Ioi 0) :=
        hg.const_mul _
      refine hdom.congr_fun (fun s hs => ?_) measurableSet_Ioi
      have hs0 : 0 < s := hs
      simp only [Function.uncurry_apply_pair]
      rw [hnorm s hs, hρ, show c - 1 - x = (c - 1) + -x by ring, Real.rpow_add hs0]
      ring
  have hswap := integral_integral_swap hF
  have hL : ∀ Δ : ℝ, ∫ s in Ioi (0 : ℝ), Fd Δ s =
      (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c g Δ : ℂ) := by
    intro Δ
    simp only [Fd]
    rw [integral_const_mul]
    unfold besselHankelTransform hankelKernel
    rw [integral_complex_ofReal]
  have hR : ∀ s ∈ Ioi (0 : ℝ), ∫ Δ in Ioi (0 : ℝ), Fd Δ s =
      hankelMellin c z * (a : ℂ) * ((g s : ℂ) * (s : ℂ) ^ ((c : ℂ) - 1 - z)) := by
    intro s hs
    have hs0 : 0 < s := hs
    have hs0' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    have hpt : ∀ Δ : ℝ, Fd Δ s = (((g s * hankelRho0 c s : ℝ)) : ℂ) *
        ((hankelPhi c (Δ * s) : ℂ) * (Δ : ℂ) ^ (z - 1)) := by
      intro Δ; simp only [Fd]; push_cast; ring
    simp_rw [hpt]
    rw [integral_const_mul, integral_phi_scale hs0 z, hρ]
    have hcp : ((s ^ (c - 1) : ℝ) : ℂ) = (s : ℂ) ^ (((c - 1 : ℝ)) : ℂ) :=
      Complex.ofReal_cpow hs0.le _
    have hexp : (s : ℂ) ^ ((c : ℂ) - 1 - z) = (s : ℂ) ^ (((c - 1 : ℝ)) : ℂ) * (s : ℂ) ^ (-z) := by
      rw [← Complex.cpow_add _ _ hs0']; congr 1; push_cast; ring
    rw [hexp]
    push_cast [hcp]
    ring
  have hlhs : ∫ Δ in Ioi (0 : ℝ), (Δ : ℂ) ^ (z - 1) * (besselHankelTransform c g Δ : ℂ) =
      ∫ Δ in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), Fd Δ s :=
    (integral_congr_ae (Eventually.of_forall fun Δ => (hL Δ).symm))
  rw [hlhs, hswap, setIntegral_congr_fun measurableSet_Ioi hR, integral_const_mul]


/-! ### The Gamma-ratio form (Weber's integral) -/

open Complex in
/-- **Weber's integral, in product form** (`DLMF 10.22.43`), derived from the Laguerre eigenfunction
`e^{-2πs}`: for `c > 3/2`, `0 < Re z < c/2 - 1/4`,
`Φ_c(z) · ((2π)^c/Γ(c)) · (1/(2π))^{c-z} Γ(c-z) = (1/(2π))^z Γ(z)`. -/
theorem hankelMellin_mul_gamma {c : ℝ} (hc : 3 / 2 < c) {z : ℂ} (hz0 : 0 < z.re)
    (hz1 : z.re < c / 2 - 1 / 4) :
    hankelMellin c z * (((2 * π) ^ c / Real.Gamma c : ℝ) : ℂ) *
        ((1 / ((2 * π : ℝ) : ℂ)) ^ ((c : ℂ) - z) * Complex.Gamma ((c : ℂ) - z)) =
      (1 / ((2 * π : ℝ) : ℂ)) ^ z * Complex.Gamma z := by
  have hc0 : 0 < c := by linarith
  have hr : 0 < 2 * π := by positivity
  have hcont : ContinuousOn (fun s : ℝ => Real.exp (-(2 * π * s))) (Ioi 0) := by fun_prop
  have hg : IntegrableOn (fun s : ℝ => |Real.exp (-(2 * π * s))| * s ^ (c - 1 - z.re)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := c - 1 - z.re) (p := 1) (b := 2 * π)
      (by linarith) one_pos hr
    refine h.congr_fun (fun s hs => ?_) measurableSet_Ioi
    simp only
    rw [Real.rpow_one, abs_of_pos (Real.exp_pos _), neg_mul, mul_comm]
  have F := mellin_hankel_fubini hc hz0 hz1 hcont hg
  have hL : ∫ Δ in Ioi (0 : ℝ), (Δ : ℂ) ^ (z - 1) *
        (besselHankelTransform c (fun s => Real.exp (-(2 * π * s))) Δ : ℂ) =
      (1 / ((2 * π : ℝ) : ℂ)) ^ z * Complex.Gamma z := by
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := z) (r := 2 * π) hz0 hr
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun Δ hΔ => ?_
    rw [besselHankelTransform_exp hc0 (le_of_lt hΔ)]
    push_cast
    ring_nf
  have hR : ∫ s in Ioi (0 : ℝ), ((Real.exp (-(2 * π * s)) : ℝ) : ℂ) * (s : ℂ) ^ ((c : ℂ) - 1 - z) =
      (1 / ((2 * π : ℝ) : ℂ)) ^ ((c : ℂ) - z) * Complex.Gamma ((c : ℂ) - z) := by
    have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := (c : ℂ) - z) (r := 2 * π)
      (by simpa using (by linarith : z.re < c)) hr
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    rw [show (c : ℂ) - z - 1 = (c : ℂ) - 1 - z by ring]
    push_cast
    ring_nf
  rw [hL, hR] at F
  exact F.symm


/-- info: 'FormalResearch.SignUncertainty.mellin_hankel_fubini' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mellin_hankel_fubini

/-- info: 'FormalResearch.SignUncertainty.hankelMellin_mul_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelMellin_mul_gamma

end FormalResearch.SignUncertainty

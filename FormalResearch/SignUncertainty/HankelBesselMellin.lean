module

public import FormalResearch.SignUncertainty.HankelBesselMoments
public import FormalResearch.Special.BesselDecay

/-!
# Weber's Mellin integral for the Hankel kernel (`DLMF 10.22.43`)

For `c > 3/2`, `Δ > 0` and `c/2 + 1/4 < Re z < c`, the weighted Hankel kernel
`ρ₀(s) K^{(c)}(Δ,s) = ρ₀(s) φ_c(Δ s)` has the absolutely convergent Mellin transform
`∫_0^∞ s^{-z} ρ₀(s) φ_c(Δ s) ds = (2π)^{2z-c} Γ(c-z) / Γ(z) · Δ^{z-c}`
(`hankel_mellin`; `hankel_mellin_critical` is the line `Re z = c - 5/8`, `c ≥ 2`, used by the radial
eigenidentity of `u1c_o1_upper.tex`, Theorem O.11ak).

* `hankel_laplace`, `integrableOn_mellin_hankel_abs`, `integrableOn_mellin_hankel`, `hankel_mellin`, `hankel_mellin_critical`.

Route: `s^{-z} = Γ(z)^{-1} ∫_0^∞ p^{z-1} e^{-p s} dp`, Fubini, the Laplace transform
`∫ e^{-p s} ρ₀(s) φ_c(Δ s) ds = (2π/p)^c e^{-4π²Δ/p}` (scaling of `integral_hankel_exp`), and the
Gamma integral after `p ↦ 1/p`.  The decay `|φ_c(w)| ≲ w^{-(2c-1)/4}` is `besselNorm_decay`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- Real-power form of `ρ₀` (definitional unfolding). -/
lemma hankelRho0_eq (c s : ℝ) : hankelRho0 c s = (2 * π) ^ c / Real.Gamma c * s ^ (c - 1) := rfl

/-- **Decay of the kernel.** For `c > 3/2` there are `C` with `|φ_c(w)| ≤ C w^{-(2c-1)/4}` for
`w ≥ 1/(16π²)`. -/
lemma abs_hankelPhi_le_decay {c : ℝ} (hc : 3 / 2 < c) :
    ∃ C : ℝ, ∀ w : ℝ, 1 / (16 * π ^ 2) ≤ w →
      |hankelPhi c w| ≤ C * w ^ (-((c - 1 / 2) / 2)) := by
  obtain ⟨C, hC⟩ := besselNorm_decay (ν := c - 2) (by linarith)
  have e1 : c - 2 + 1 = c - 1 := by ring
  have e2 : c - 2 + 3 / 2 = c - 1 / 2 := by ring
  rw [e1, e2] at hC
  refine ⟨C / (4 * π) ^ (c - 1 / 2), fun w hw => ?_⟩
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw
  have hpi : 0 < π := Real.pi_pos
  set x : ℝ := 4 * π * √w with hx
  have hsq : 1 / (4 * π) ≤ √w := by
    rw [Real.le_sqrt (by positivity) hw0.le]
    calc (1 / (4 * π)) ^ 2 = 1 / (16 * π ^ 2) := by field_simp; ring
      _ ≤ w := hw
  have hx1 : 1 ≤ x := by
    rw [hx]
    calc (1 : ℝ) = 4 * π * (1 / (4 * π)) := by field_simp
      _ ≤ 4 * π * √w := by gcongr
  have hxp : 0 < x := by linarith
  have hb := hC x hx1
  have hpow : x ^ (c - 1 / 2) = (4 * π) ^ (c - 1 / 2) * w ^ ((c - 1 / 2) / 2) := by
    rw [hx, Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hw0.le]
    congr 2; ring
  have hxpos : 0 < x ^ (c - 1 / 2) := Real.rpow_pos_of_pos hxp _
  have h4 : 0 < (4 * π) ^ (c - 1 / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hwp : 0 < w ^ ((c - 1 / 2) / 2) := Real.rpow_pos_of_pos hw0 _
  unfold hankelPhi
  rw [Real.rpow_neg hw0.le]
  have : |besselNorm (c - 1) x| ≤ C / x ^ (c - 1 / 2) := by
    rw [le_div_iff₀ hxpos]; exact hb
  calc |besselNorm (c - 1) (4 * π * √w)| ≤ C / x ^ (c - 1 / 2) := this
    _ = C / (4 * π) ^ (c - 1 / 2) * (w ^ ((c - 1 / 2) / 2))⁻¹ := by
      rw [hpow]; field_simp

lemma continuousOn_mellin_abs (c Δ σ : ℝ) :
    ContinuousOn (fun s : ℝ => s ^ (-σ) * (hankelRho0 c s * |hankelPhi c (Δ * s)|)) (Ioi 0) := by
  intro s hs
  have hs0 : s ≠ 0 := (ne_of_gt hs)
  have h1 : ContinuousAt (fun s : ℝ => s ^ (-σ)) s := Real.continuousAt_rpow_const _ _ (Or.inl hs0)
  have h2 : ContinuousAt (fun s : ℝ => s ^ (c - 1)) s := Real.continuousAt_rpow_const _ _ (Or.inl hs0)
  have h3 : Continuous fun s : ℝ => |hankelPhi c (Δ * s)| :=
    (hankelPhi_continuous c).comp (continuous_const.mul continuous_id) |>.abs
  refine ContinuousAt.continuousWithinAt ?_
  unfold hankelRho0
  exact h1.mul ((continuousAt_const.mul h2).mul h3.continuousAt)

/-- **Absolute integrability of the weighted kernel against `s^{-σ}`** on `c/2 + 1/4 < σ < c`. -/
theorem integrableOn_mellin_hankel_abs {c Δ σ : ℝ} (hc : 3 / 2 < c) (hΔ : 0 < Δ)
    (h1 : c / 2 + 1 / 4 < σ) (h2 : σ < c) :
    IntegrableOn (fun s : ℝ => s ^ (-σ) * (hankelRho0 c s * |hankelPhi c (Δ * s)|)) (Ioi 0) := by
  obtain ⟨C, hC⟩ := abs_hankelPhi_le_decay hc
  have hpi : 0 < π := Real.pi_pos
  have hG : 0 < Real.Gamma c := Real.Gamma_pos_of_pos (by linarith)
  set s0 : ℝ := 1 / (16 * π ^ 2 * Δ) with hs0
  have hs0p : 0 < s0 := by positivity
  set K : ℝ := (2 * π) ^ c / Real.Gamma c with hK
  have hKp : 0 < K := by positivity
  have hmeas := (continuousOn_mellin_abs c Δ σ).aestronglyMeasurable (μ := volume)
    (measurableSet_Ioi (a := (0:ℝ)))
  rw [← Ioc_union_Ioi_eq_Ioi hs0p.le]
  refine IntegrableOn.union ?_ ?_
  · -- near 0
    have hint : IntegrableOn (fun s : ℝ => K * s ^ (c - 1 - σ)) (Ioc 0 s0) := by
      refine Integrable.const_mul ?_ K
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := s0) (r := c - 1 - σ)
        (by linarith))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hs0p.le] at this
    refine Integrable.mono' hint (hmeas.mono_set Ioc_subset_Ioi_self) ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hsp : 0 < s := hs.1
    have hφ := abs_hankelPhi_le_one (c := c) (by linarith) (Δ * s)
    have hrp : 0 < s ^ (-σ) := Real.rpow_pos_of_pos hsp _
    have hrc : 0 ≤ hankelRho0 c s := by rw [hankelRho0_eq]; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc s ^ (-σ) * (hankelRho0 c s * |hankelPhi c (Δ * s)|)
        ≤ s ^ (-σ) * (hankelRho0 c s * 1) := by gcongr
      _ = K * s ^ (c - 1 - σ) := by
        rw [hankelRho0_eq, mul_one, show c - 1 - σ = (c - 1) + (-σ) by ring, Real.rpow_add hsp]
        ring
  · -- near infinity
    set e : ℝ := c - 1 - σ - (c - 1 / 2) / 2 with he
    have hint : IntegrableOn (fun s : ℝ => K * (C * Δ ^ (-((c - 1 / 2) / 2))) * s ^ e) (Ioi s0) := by
      refine Integrable.const_mul ?_ _
      exact integrableOn_Ioi_rpow_of_lt (by rw [he]; linarith) hs0p
    refine Integrable.mono' hint (hmeas.mono_set (Ioi_subset_Ioi hs0p.le)) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hsp : 0 < s := lt_trans hs0p hs
    have hΔs : 1 / (16 * π ^ 2) ≤ Δ * s := by
      have : s0 < s := hs
      rw [hs0, div_lt_iff₀ (by positivity)] at this
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have hφ := hC (Δ * s) hΔs
    have hrp : 0 < s ^ (-σ) := Real.rpow_pos_of_pos hsp _
    have hrc : 0 ≤ hankelRho0 c s := by rw [hankelRho0_eq]; positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc s ^ (-σ) * (hankelRho0 c s * |hankelPhi c (Δ * s)|)
        ≤ s ^ (-σ) * (hankelRho0 c s * (C * (Δ * s) ^ (-((c - 1 / 2) / 2)))) := by gcongr
      _ = K * (C * Δ ^ (-((c - 1 / 2) / 2))) * s ^ e := by
        rw [hankelRho0_eq, Real.mul_rpow hΔ.le hsp.le, he,
          show c - 1 - σ - (c - 1 / 2) / 2 = (-σ) + (c - 1) + (-((c - 1 / 2) / 2)) by ring,
          Real.rpow_add hsp, Real.rpow_add hsp]
        ring

/-- **Laplace transform of the weighted Hankel kernel**: for `c > 0`, `Δ ≥ 0`, `p > 0`,
`∫_0^∞ e^{-p s} ρ₀(s) φ_c(Δ s) ds = (2π/p)^c e^{-4π²Δ/p}` (scaling of `integral_hankel_exp`). -/
theorem hankel_laplace {c : ℝ} (hc : 0 < c) {Δ : ℝ} (hΔ : 0 ≤ Δ) {p : ℝ} (hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), Real.exp (-(p * s)) * (hankelRho0 c s * hankelPhi c (Δ * s)) =
      (2 * π / p) ^ c * Real.exp (-(4 * π ^ 2 * Δ / p)) := by
  have hpi : 0 < π := Real.pi_pos
  set κ : ℝ := p / (2 * π) with hκ
  have hκp : 0 < κ := by positivity
  set f : ℝ → ℝ := fun u => Real.exp (-(2 * π * u)) * hankelRho0 c u * hankelPhi c ((Δ / κ) * u)
    with hf
  have h0 := integral_hankel_exp hc (Δ := Δ / κ) (by positivity)
  have h1 := integral_comp_mul_left_Ioi f 0 hκp
  rw [mul_zero] at h1
  have hfk : ∀ x : ℝ, 0 < x → f (κ * x) =
      κ ^ (c - 1) * (Real.exp (-(p * x)) * (hankelRho0 c x * hankelPhi c (Δ * x))) := by
    intro x hx
    have hε : 2 * π * (κ * x) = p * x := by rw [hκ]; field_simp
    have hΔκ : Δ / κ * (κ * x) = Δ * x := by field_simp
    simp only [hf, hε, hΔκ, hankelRho0_eq, Real.mul_rpow hκp.le hx.le]
    ring
  have h2 : ∫ x in Ioi (0 : ℝ), f (κ * x) =
      κ ^ (c - 1) * ∫ x in Ioi (0 : ℝ), Real.exp (-(p * x)) * (hankelRho0 c x * hankelPhi c (Δ * x)) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => hfk x hx)
  have h3 : ∫ x in Ioi (0 : ℝ), f x = Real.exp (-(2 * π * (Δ / κ))) := h0
  rw [h2, h3, smul_eq_mul] at h1
  have hκc : 0 < κ ^ (c - 1) := Real.rpow_pos_of_pos hκp _
  have h4 : ∫ x in Ioi (0 : ℝ), Real.exp (-(p * x)) * (hankelRho0 c x * hankelPhi c (Δ * x)) =
      κ⁻¹ * Real.exp (-(2 * π * (Δ / κ))) / κ ^ (c - 1) := by
    rw [eq_div_iff hκc.ne', mul_comm]; exact h1
  have e1 : κ⁻¹ / κ ^ (c - 1) = (2 * π / p) ^ c := by
    rw [← Real.rpow_neg_one, ← Real.rpow_sub hκp, show -1 - (c - 1) = -c by ring,
      Real.rpow_neg hκp.le, ← Real.inv_rpow hκp.le, hκ, inv_div]
  have e2 : 2 * π * (Δ / κ) = 4 * π ^ 2 * Δ / p := by rw [hκ]; field_simp; ring
  rw [h4, e2, mul_div_right_comm, mul_comm, ← e1]
  ring

/-- The inverted Gamma integral `∫_0^∞ p^{-w-1} e^{-A/p} dp = A^{-w} Γ(w)` for `A > 0`, `Re w > 0`. -/
lemma integral_cpow_mul_exp_neg_div_Ioi {w : ℂ} (hw : 0 < w.re) {A : ℝ} (hA : 0 < A) :
    ∫ p in Ioi (0 : ℝ), (p : ℂ) ^ (-w - 1) * Complex.exp (-((A : ℂ) / p)) =
      ((A : ℂ)) ^ (-w) * Complex.Gamma w := by
  set g : ℝ → ℂ := fun q => (q : ℂ) ^ (w - 1) * Complex.exp (-((A : ℂ) * q)) with hg
  have h0 := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  have hG : ∫ y in Ioi (0 : ℝ), g y = ((A : ℂ)) ^ (-w) * Complex.Gamma w := by
    have := Complex.integral_cpow_mul_exp_neg_mul_Ioi hw hA
    simp only [hg]
    rw [this, one_div, Complex.inv_cpow _ _
      (by rw [Complex.arg_ofReal_of_nonneg hA.le]; exact Real.pi_pos.ne), Complex.cpow_neg]
  rw [← hG, ← h0]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (0 : ℝ) < x := hx
  simp only [hg]
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hxarg : (x : ℂ).arg ≠ π := by
    rw [Complex.arg_ofReal_of_nonneg hx0.le]; exact Real.pi_pos.ne
  rw [Real.rpow_neg_one, Complex.real_smul, ofReal_inv, Complex.inv_cpow _ _ hxarg, abs_neg, abs_one,
    one_mul, show (-1 - 1 : ℝ) = -2 by norm_num, Real.rpow_neg hx0.le, ofReal_inv,
    Complex.ofReal_cpow hx0.le, ← Complex.cpow_neg, ← Complex.cpow_neg,
    ← mul_assoc, ← Complex.cpow_add _ _ hxc, div_eq_mul_inv]
  push_cast
  congr 2; ring_nf

/-- The weighted kernel `s ↦ ρ₀(s) φ_c(Δ s)`. -/
noncomputable def hankelWeighted (c Δ s : ℝ) : ℝ := hankelRho0 c s * hankelPhi c (Δ * s)

lemma measurable_hankelWeighted (c Δ : ℝ) : Measurable (hankelWeighted c Δ) := by
  unfold hankelWeighted hankelRho0
  have h := (hankelPhi_continuous c).comp (continuous_const.mul continuous_id : Continuous fun s : ℝ => Δ * s)
  exact ((measurable_id.pow_const _).const_mul _).mul h.measurable

/-- The integrand of the Fubini argument: `p^{z-1} e^{-s p} ρ₀(s) φ_c(Δ s)`. -/
noncomputable def mellinFubini (c Δ : ℝ) (z : ℂ) (x : ℝ × ℝ) : ℂ :=
  ((x.2 : ℝ) : ℂ) ^ (z - 1) * Complex.exp (-((x.1 : ℂ) * x.2)) * ((hankelWeighted c Δ x.1 : ℝ) : ℂ)

lemma measurable_mellinFubini (c Δ : ℝ) (z : ℂ) : Measurable (mellinFubini c Δ z) := by
  unfold mellinFubini
  have hw := measurable_hankelWeighted c Δ
  refine Measurable.mul (Measurable.mul ?_ ?_) ?_
  · exact (Complex.measurable_ofReal.comp measurable_snd).pow_const _
  · exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp measurable_fst).mul
      (Complex.measurable_ofReal.comp measurable_snd)).neg
  · exact Complex.measurable_ofReal.comp (hw.comp measurable_fst)

lemma norm_mellinFubini {c Δ : ℝ} {z : ℂ} {s p : ℝ} (hp : 0 < p) :
    ‖mellinFubini c Δ z (s, p)‖ = p ^ (z.re - 1) * Real.exp (-(s * p)) * |hankelWeighted c Δ s| := by
  unfold mellinFubini
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp, Complex.norm_exp]
  simp [Complex.norm_real]

lemma integrable_mellinFubini_inner {c Δ : ℝ} {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ => mellinFubini c Δ z (s, p)) (volume.restrict (Ioi (0 : ℝ))) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ => mellinFubini c Δ z (s, p))
      (volume.restrict (Ioi (0 : ℝ))) :=
    ((measurable_mellinFubini c Δ z).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hint : IntegrableOn (fun p : ℝ => |hankelWeighted c Δ s| *
      (p ^ (z.re - 1) * Real.exp (-s * p))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_Ioi (p := z.re - 1) (a := s) (by linarith) hs).const_mul _
  refine Integrable.mono' hint hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun p hp => ?_
  rw [norm_mellinFubini (Set.mem_Ioi.mp hp)]
  have : -(s * p) = -s * p := by ring
  rw [this]; ring_nf; exact le_rfl

lemma integral_mellinFubini_inner {c Δ : ℝ} {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    ∫ p in Ioi (0 : ℝ), mellinFubini c Δ z (s, p) =
      Complex.Gamma z * (s : ℂ) ^ (-z) * ((hankelWeighted c Δ s : ℝ) : ℂ) := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi hz hs
  unfold mellinFubini
  simp only
  rw [integral_mul_const]
  congr 1
  rw [h, one_div, Complex.inv_cpow _ _
    (by rw [Complex.arg_ofReal_of_nonneg hs.le]; exact Real.pi_pos.ne), Complex.cpow_neg]
  ring

lemma integral_norm_mellinFubini_inner {c Δ : ℝ} {z : ℂ} (hz : 0 < z.re) {s : ℝ} (hs : 0 < s) :
    ∫ p in Ioi (0 : ℝ), ‖mellinFubini c Δ z (s, p)‖ =
      Real.Gamma z.re * (s ^ (-z.re) * |hankelWeighted c Δ s|) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi hz hs
  rw [setIntegral_congr_fun measurableSet_Ioi (fun p hp => norm_mellinFubini (Set.mem_Ioi.mp hp)),
    integral_mul_const, h, one_div, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]
  ring

lemma abs_hankelWeighted {c Δ s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    |hankelWeighted c Δ s| = hankelRho0 c s * |hankelPhi c (Δ * s)| := by
  unfold hankelWeighted
  rw [abs_mul, abs_of_nonneg (by rw [hankelRho0_eq]; have := Real.Gamma_pos_of_pos hc; positivity)]

lemma integrable_mellinFubini {c Δ : ℝ} {z : ℂ} (hc : 3 / 2 < c) (hΔ : 0 < Δ)
    (h1 : c / 2 + 1 / 4 < z.re) (h2 : z.re < c) :
    Integrable (mellinFubini c Δ z)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hz : 0 < z.re := by linarith
  rw [integrable_prod_iff (measurable_mellinFubini c Δ z).aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioi]
    exact Filter.Eventually.of_forall fun s hs => integrable_mellinFubini_inner hz hs
  · have hI := (integrableOn_mellin_hankel_abs hc hΔ h1 h2).const_mul (Real.Gamma z.re)
    refine Integrable.congr hI ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hs' : 0 < s := hs
    rw [integral_norm_mellinFubini_inner hz hs', abs_hankelWeighted (by linarith) hs']

/-- The `s`-integral of the Fubini integrand is the Laplace transform of the weighted kernel. -/
lemma integral_mellinFubini_outer {c Δ : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) {z : ℂ} {p : ℝ} (hp : 0 < p) :
    ∫ s in Ioi (0 : ℝ), mellinFubini c Δ z (s, p) =
      ((2 * π : ℝ) : ℂ) ^ (c : ℂ) * ((p : ℂ) ^ (z - 1 - c) *
        Complex.exp (-(((4 * π ^ 2 * Δ : ℝ) : ℂ) / p))) := by
  have hL := hankel_laplace hc hΔ.le hp
  have h1 : ∀ s : ℝ, mellinFubini c Δ z (s, p) =
      (p : ℂ) ^ (z - 1) * ((Real.exp (-(p * s)) * hankelWeighted c Δ s : ℝ) : ℂ) := by
    intro s
    unfold mellinFubini
    push_cast
    rw [mul_comm (s : ℂ) (p : ℂ)]
    ring
  simp_rw [h1]
  rw [integral_const_mul, integral_complex_ofReal]
  unfold hankelWeighted at *
  rw [hL]
  have hp' : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have e1 : (((2 * π / p) ^ c : ℝ) : ℂ) = ((2 * π : ℝ) : ℂ) ^ (c : ℂ) * (p : ℂ) ^ (-(c : ℂ)) := by
    rw [Real.div_rpow (by positivity) hp.le, Complex.ofReal_div, Complex.ofReal_cpow (by positivity),
      Complex.ofReal_cpow hp.le, Complex.cpow_neg, div_eq_mul_inv]
  have e2 : (((Real.exp (-(4 * π ^ 2 * Δ / p))) : ℝ) : ℂ) =
      Complex.exp (-(((4 * π ^ 2 * Δ : ℝ) : ℂ) / p)) := by
    rw [Complex.ofReal_exp]; push_cast; ring_nf
  rw [Complex.ofReal_mul, e1, e2, show z - 1 - (c : ℂ) = (z - 1) + (-(c : ℂ)) by ring,
    Complex.cpow_add _ _ hp']
  ring

/-- **Weber's integral for the Hankel kernel** (`DLMF 10.22.43`, Mellin form): for `c > 3/2`, `Δ > 0`
and `c/2 + 1/4 < Re z < c`,
`∫_0^∞ s^{-z} ρ₀(s) φ_c(Δ s) ds = (2π)^{2z-c} Γ(c-z)/Γ(z) · Δ^{z-c}`, the integral converging
absolutely (`integrableOn_mellin_hankel_abs`). -/
theorem hankel_mellin {c Δ : ℝ} (hc : 3 / 2 < c) (hΔ : 0 < Δ) {z : ℂ}
    (h1 : c / 2 + 1 / 4 < z.re) (h2 : z.re < c) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (-z) * ((hankelWeighted c Δ s : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) ^ (2 * z - c) * Complex.Gamma (c - z) / Complex.Gamma z *
        (Δ : ℂ) ^ (z - c) := by
  have hz : 0 < z.re := by linarith
  have hc0 : 0 < c := by linarith
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioi (0 : ℝ))) (f := fun s p => mellinFubini c Δ z (s, p))
    (integrable_mellinFubini hc hΔ h1 h2)
  have hΓ : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  have hL : ∫ s in Ioi (0 : ℝ), ∫ p in Ioi (0 : ℝ), mellinFubini c Δ z (s, p) =
      Complex.Gamma z * ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (-z) * ((hankelWeighted c Δ s : ℝ) : ℂ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    rw [integral_mellinFubini_inner hz hs]; ring
  have hR : ∫ p in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), mellinFubini c Δ z (s, p) =
      ((2 * π : ℝ) : ℂ) ^ (c : ℂ) * (((4 * π ^ 2 * Δ : ℝ) : ℂ) ^ (-((c : ℂ) - z)) *
        Complex.Gamma ((c : ℂ) - z)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun p hp => integral_mellinFubini_outer hc0 hΔ hp),
      integral_const_mul]
    congr 1
    have hw : 0 < ((c : ℂ) - z).re := by simp; linarith
    rw [← integral_cpow_mul_exp_neg_div_Ioi hw (by positivity : 0 < 4 * π ^ 2 * Δ)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun p hp => ?_)
    congr 2; ring
  rw [hL, hR] at hswap
  have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hA : (((4 * π ^ 2 * Δ : ℝ) : ℂ)) ^ (-((c : ℂ) - z)) =
      ((2 * π : ℝ) : ℂ) ^ (2 * (z - c)) * (Δ : ℂ) ^ (z - c) := by
    have hpos : (0 : ℝ) ≤ 2 * π := by positivity
    rw [show (4 * π ^ 2 * Δ : ℝ) = (2 * π) * ((2 * π) * Δ) by ring]
    generalize 2 * π = a at hpos h2π ⊢
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hpos (by positivity), Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg hpos hΔ.le,
      show -((c : ℂ) - z) = z - c by ring, two_mul, Complex.cpow_add _ _ h2π]
    ring
  rw [hA] at hswap
  refine mul_left_cancel₀ hΓ ?_
  rw [hswap, show 2 * z - (c : ℂ) = c + 2 * (z - c) by ring, Complex.cpow_add _ _ h2π]
  field_simp

/-- Absolute integrability of the complex Mellin integrand of `hankel_mellin`. -/
theorem integrableOn_mellin_hankel {c Δ : ℝ} (hc : 3 / 2 < c) (hΔ : 0 < Δ) {z : ℂ}
    (h1 : c / 2 + 1 / 4 < z.re) (h2 : z.re < c) :
    IntegrableOn (fun s : ℝ => (s : ℂ) ^ (-z) * ((hankelWeighted c Δ s : ℝ) : ℂ)) (Ioi 0) := by
  have hI := integrableOn_mellin_hankel_abs hc hΔ h1 h2
  have hmeas : AEStronglyMeasurable (fun s : ℝ => (s : ℂ) ^ (-z) * ((hankelWeighted c Δ s : ℝ) : ℂ))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((Complex.measurable_ofReal.pow_const _).mul
      (Complex.measurable_ofReal.comp (measurable_hankelWeighted c Δ)))).aestronglyMeasurable
  refine Integrable.mono' hI hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Filter.Eventually.of_forall fun s hs => ?_
  have hs' : 0 < s := hs
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hs', Complex.norm_real, Real.norm_eq_abs,
    abs_hankelWeighted (by linarith) hs']
  simp

/-- **Weber's integral on the critical line** `Re z = c - 5/8`, `c ≥ 2` (the line `σ₁` of the radial
eigenidentity): `∫_0^∞ s^{-z} ρ₀(s) K^{(c)}(Δ,s) ds = (2π)^{2z-c} Γ(c-z)/Γ(z) Δ^{z-c}`. -/
theorem hankel_mellin_critical {c Δ : ℝ} (hc : 2 ≤ c) (hΔ : 0 < Δ) {z : ℂ} (hz : z.re = c - 5 / 8) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ (-z) * ((hankelRho0 c s * hankelKernel c Δ s : ℝ) : ℂ) =
      ((2 * π : ℝ) : ℂ) ^ (2 * z - c) * Complex.Gamma (c - z) / Complex.Gamma z *
        (Δ : ℂ) ^ (z - c) :=
  hankel_mellin (by linarith) hΔ (by rw [hz]; linarith) (by rw [hz]; linarith)

/-- info: 'FormalResearch.SignUncertainty.hankel_laplace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hankel_laplace
/-- info: 'FormalResearch.SignUncertainty.integrableOn_mellin_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms integrableOn_mellin_hankel
/-- info: 'FormalResearch.SignUncertainty.hankel_mellin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hankel_mellin
/-- info: 'FormalResearch.SignUncertainty.hankel_mellin_critical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hankel_mellin_critical

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.RadialRigidity

/-!
# Hardy–Mellin Intertwiner (`general_theorems.tex` Proposition 7.9a)

Source: `CFT/sign_uncertainty/paper/general_theorems.tex` (PR 240, commit `c3d8c90fe`).

Radial Hankel kernel data `HankelKernelData`, Hardy–Mellin intertwiner `(ℐ_c f)(Δ)`,
injection `𝒜_c^{-1} ↪ 𝒜_c^{+1}`, `threshold_pos_le_neg`, and `fourier_radii_pos_le_neg`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis

lemma integrableOn_rpow_mul_exp_neg_mul_Ioi {p a : ℝ} (hp : -1 < p) (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => s ^ p * Real.exp (-a * s)) (Ioi 0) := by
  let b : ℝ := a / 2
  have hb : 0 < b := half_pos ha
  have hexp_int : IntegrableOn (fun s : ℝ => Real.exp (-b * s)) (Ioi 0) := by
    have hderiv : ∀ s ∈ Ici (0 : ℝ), HasDerivAt (fun x : ℝ => -(1 / b) * Real.exp (-b * x))
        (Real.exp (-b * s)) s := fun s _ =>
      ((((hasDerivAt_id' s).const_mul (-b)).exp).const_mul (-(1 / b))).congr_deriv
        (by field_simp [hb.ne'])
    have ht0 : Tendsto (fun x : ℝ => -(1 / b) * Real.exp (-b * x)) atTop (𝓝 0) := by
      have : Tendsto (fun x : ℝ => Real.exp (-b * x)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr hb) tendsto_id)
      simpa using this.const_mul (-(1 / b))
    exact integrableOn_Ioi_deriv_of_nonneg' hderiv
      (fun s _ => (Real.exp_pos _).le) ht0
  have hsm : AEStronglyMeasurable (fun s : ℝ => s ^ p * Real.exp (-a * s)) (volume.restrict (Ioi 0)) :=
    ((ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (ne_of_gt (mem_Ioi.mp hs))).mul
      (by fun_prop : Continuous fun s : ℝ => Real.exp (-a * s)).continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  have h1 : IntegrableOn (fun s : ℝ => s ^ p * Real.exp (-a * s)) (Ioc 0 1) := by
    have hr : IntegrableOn (fun s : ℝ => s ^ p) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' hp)
    refine hr.mono' (hsm.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.1.le _),
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hs.1.le _)
      (Real.exp_le_one_iff.mpr (by nlinarith [hs.1]))
  have h2 : IntegrableOn (fun s : ℝ => s ^ p * Real.exp (-a * s)) (Ioi 1) := by
    let n : ℕ := Nat.ceil p + 1
    have hpn : p ≤ (n : ℝ) := (Nat.le_ceil p).trans (by norm_cast; omega)
    let C : ℝ := (2 / a) ^ n * (n.factorial : ℝ)
    refine ((hexp_int.mono_set (Ioi_subset_Ioi zero_le_one)).const_mul C).mono'
      (hsm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl))
      ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 1 < s) => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _),
      abs_of_pos (Real.exp_pos _)]
    have hpow_le : s ^ p ≤ s ^ n := by
      rw [← Real.rpow_natCast s n]
      exact Real.rpow_le_rpow_of_exponent_le hs.le hpn
    have hfact : (b * s) ^ n / (n.factorial : ℝ) ≤ Real.exp (b * s) :=
      Real.pow_div_factorial_le_exp (b * s) (mul_nonneg hb.le (by linarith)) n
    have hsn : s ^ n ≤ C * Real.exp (b * s) := by
      have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by positivity
      have hb_pos : 0 < b ^ n := pow_pos hb n
      have hmul : (b * s) ^ n ≤ (n.factorial : ℝ) * Real.exp (b * s) := by
        rw [div_le_iff₀ hfac_pos, mul_comm _ (n.factorial : ℝ)] at hfact
        exact hfact
      rw [mul_pow] at hmul
      calc s ^ n = (b ^ n)⁻¹ * (b ^ n * s ^ n) := by field_simp [hb_pos.ne']
        _ ≤ (b ^ n)⁻¹ * ((n.factorial : ℝ) * Real.exp (b * s)) :=
            mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hb_pos.le)
        _ = C * Real.exp (b * s) := by
            dsimp [C, b]; rw [div_eq_mul_inv, mul_pow, inv_pow, mul_inv, inv_inv]; ring
    have hexp_eq : Real.exp (b * s) * Real.exp (-a * s) = Real.exp (-b * s) := by
      rw [← Real.exp_add]; congr 1; dsimp [b]; ring
    calc s ^ p * Real.exp (-a * s) ≤ s ^ n * Real.exp (-a * s) :=
          mul_le_mul_of_nonneg_right hpow_le (Real.exp_pos _).le
      _ ≤ (C * Real.exp (b * s)) * Real.exp (-a * s) :=
          mul_le_mul_of_nonneg_right hsn (Real.exp_pos _).le
      _ = C * Real.exp (-b * s) := by rw [mul_assoc, hexp_eq]
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact h1.union h2

/-! ### Section 3: Hardy–Mellin Intertwiner (`gt:7.9a`, Proposition 7.9a) -/

/-- Radial Hankel kernel data at central charge `c > 0`: continuous bounded `φ` with `φ(0) = 1`
whose `w^{c/2 - 1}` antiderivative is uniformly bounded on `[0, ∞)` and tends to
`Γ(c) / (2π)^c` at `∞`. -/
structure HankelKernelData (c : ℝ) where
  φ : ℝ → ℝ
  φ_zero : φ 0 = 1
  φ_cont : Continuous φ
  φ_bound : ∃ C, 0 ≤ C ∧ ∀ w ≥ 0, |φ w| ≤ C
  antideriv_bound : ∃ M, 0 ≤ M ∧ ∀ X ≥ 0,
    |((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * φ w| ≤ M
  antideriv_tendsto : Tendsto
    (fun X => ((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * φ w)
    atTop (𝓝 1)

/-- Radial Hankel transform `(T_c f)(Δ) = ∫_0^∞ f(s) ρ₀(c, s) φ(Δ s) ds`. -/
noncomputable def hankelTransform (c : ℝ) (K : HankelKernelData c) (f : ℝ → ℝ) (Δ : ℝ) : ℝ :=
  ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s * K.φ (Δ * s)

/-- Radial Hankel eigenfunction `f ∈ 𝒜_c^ε`. -/
structure IsRadialEigenfn (c : ℝ) (K : HankelKernelData c) (ε : ℝ) (f : ℝ → ℝ) : Prop where
  cont : ContinuousOn f (Ici 0)
  int : IntegrableOn (fun Δ => f Δ * hankelRho0 c Δ) (Ioi 0)
  eigen : ∀ Δ ∈ Ici (0 : ℝ), hankelTransform c K f Δ = ε * f Δ

/-- Feasibility at threshold `T`: `f ∈ 𝒜_c^ε \ {0}` (nonzero on `[0, ∞)`), `ε * f(0) ≤ 0`
(so `f(0) ≥ 0` for `ε = -1` and `f(0) ≤ 0` for `ε = +1`), and `f ≥ 0` on `[T, ∞)`. -/
structure IsFeasible (c : ℝ) (K : HankelKernelData c) (ε T : ℝ) (f : ℝ → ℝ) : Prop where
  eigenfn : IsRadialEigenfn c K ε f
  nonzero : ∃ Δ ∈ Ici (0 : ℝ), f Δ ≠ 0
  origin_sign : ε * f 0 ≤ 0
  tail_nonneg : ∀ Δ ≥ T, 0 ≤ f Δ

/-- One-level radial Hankel threshold `T_c^ε`. -/
noncomputable def hankelThreshold (c : ℝ) (K : HankelKernelData c) (ε : ℝ) : ℝ :=
  sInf { T : ℝ | ∃ f, IsFeasible c K ε T f }

/-- Hardy–Mellin intertwiner `(ℐ_c f)(Δ) = Δ^{-c/2} ∫_Δ^∞ f(s) s^{c/2 - 1} ds` for `Δ > 0`,
extended continuously to `[0, ∞)` by `-(2 / c) * f 0` at `Δ = 0`. -/
noncomputable def intertwiner (c : ℝ) (f : ℝ → ℝ) (Δ : ℝ) : ℝ :=
  if 0 < Δ then Δ ^ (-(c / 2)) * ∫ s in Ioi Δ, f s * s ^ (c / 2 - 1) else -(2 / c) * f 0

lemma hankelTransform_integrand_integrableOn {c : ℝ} {K : HankelKernelData c} {f : ℝ → ℝ}
    (hfint : IntegrableOn (fun s => f s * hankelRho0 c s) (Ioi 0)) {Δ : ℝ} (hΔ : 0 ≤ Δ) :
    IntegrableOn (fun s => f s * hankelRho0 c s * K.φ (Δ * s)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := K.φ_bound
  refine (hfint.norm.const_mul C).mono'
    (hfint.aestronglyMeasurable.mul (K.φ_cont.comp (continuous_const_mul Δ)).aestronglyMeasurable)
    ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_)
  rw [Real.norm_eq_abs, abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC (Δ * s) (mul_nonneg hΔ hs.le)) (abs_nonneg _)

private lemma eigenfn_abs_le {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) :
    ∀ {C : ℝ}, (∀ w ≥ 0, |K.φ w| ≤ C) → ∀ Δ ≥ 0, |f Δ| ≤ C * hankelMass c f := by
  intro C hC Δ hΔ
  have heig : |f Δ| = |hankelTransform c K f Δ| := by
    rw [hf.eigen Δ hΔ]; simp
  rw [heig]
  unfold hankelTransform hankelMass
  have hdom : IntegrableOn (fun s => C * (|f s| * hankelRho0 c s)) (Ioi 0) :=
    (abs_mul_rho0_integrableOn hc hf.int).const_mul C
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_const_mul]
  refine setIntegral_mono_on (hankelTransform_integrand_integrableOn hf.int hΔ).norm
    hdom measurableSet_Ioi fun s (hs : 0 < s) => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc hs.le), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC (Δ * s) (mul_nonneg hΔ hs.le))
    (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc hs.le))

lemma feasible_threshold_pos {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {ε T : ℝ}
    {f : ℝ → ℝ} (hf : IsFeasible c K ε T f) : 0 < T := by
  by_contra hT
  have hT0 : T ≤ 0 := not_lt.mp hT
  have hf_nn : ∀ Δ ∈ Ici (0 : ℝ), 0 ≤ f Δ := fun Δ hΔ => hf.tail_nonneg Δ (hT0.trans hΔ)
  have hint_eq : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = ε * f 0 := by
    have h0 := hf.eigenfn.eigen 0 self_mem_Ici
    unfold hankelTransform at h0
    simp_rw [zero_mul, K.φ_zero, mul_one] at h0
    exact h0
  have hint_nn : 0 ≤ ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (hf_nn s (le_of_lt hs)) (hankelRho0_nonneg hc (le_of_lt hs))
  have hint0 : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = 0 :=
    le_antisymm (hint_eq.symm ▸ hf.origin_sign) hint_nn
  have hae0 : (fun s => f s * hankelRho0 c s) =ᵐ[volume.restrict (Ioi 0)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
        mul_nonneg (hf_nn s (le_of_lt hs)) (hankelRho0_nonneg hc (le_of_lt hs)))
      hf.eigenfn.int).mp hint0
  have hcont_prod : ContinuousOn (fun s => f s * hankelRho0 c s) (Ioi 0) :=
    (hf.eigenfn.cont.mono Ioi_subset_Ici_self).mul (continuousOn_hankelRho0 c)
  have hIoi0 : ∀ s ∈ Ioi (0 : ℝ), f s = 0 := fun s hs => by
    by_contra hfs
    have hprod_ne : f s * hankelRho0 c s ≠ 0 := mul_ne_zero hfs (hankelRho0_pos hc hs).ne'
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hcont_prod s hs)
      (|f s * hankelRho0 c s| / 2) (half_pos (abs_pos.mpr hprod_ne))
    let a : ℝ := max 0 (s - δ / 2)
    let b : ℝ := s + δ / 2
    have hab : a < b := by dsimp [a, b]; refine max_lt (by linarith [mem_Ioi.mp hs, hδpos]) (by linarith)
    have hsub_oo : Ioo a b ⊆ Ioi (0 : ℝ) := fun x hx => lt_of_le_of_lt (le_max_left _ _) hx.1
    have hne_oo : ∀ x ∈ Ioo a b, f x * hankelRho0 c x ≠ 0 := fun x hx => by
      have hxs : dist x s < δ := by
        rw [Real.dist_eq, abs_lt]
        have hx1 : s - δ / 2 < x := lt_of_le_of_lt (le_max_right _ _) hx.1
        have hx2 : x < s + δ / 2 := hx.2
        constructor <;> linarith
      have hdist := hδ (hsub_oo hx) hxs
      rw [Real.dist_eq] at hdist
      intro hx0
      rw [hx0, zero_sub, abs_neg] at hdist
      linarith [abs_pos.mpr hprod_ne]
    have hnull : (volume.restrict (Ioi (0 : ℝ))) (Ioo a b) = 0 :=
      measure_mono_null (fun x hx => hne_oo x hx) (ae_iff.mp hae0)
    rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub_oo, Real.volume_Ioo] at hnull
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne' hnull
  have hf0 : f 0 = 0 := by
    have htend : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      (hf.eigenfn.cont 0 self_mem_Ici).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    have htend0 : Tendsto f (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hIoi0 s hs).symm)
    exact tendsto_nhds_unique htend htend0
  obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero
  rcases eq_or_lt_of_le (mem_Ici.mp hΔ) with rfl | hΔpos
  · exact hne hf0
  · exact hne (hIoi0 Δ hΔpos)

/-- Proposition 7.9a(1), integrability: for `f ∈ 𝒜_c^{-1}`, `|f(s)| s^{c/2 - 1}` and
`f(s) s^{c/2 - 1}` are integrable on `(0, ∞)`. -/
theorem intertwiner_integrable {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) :
    IntegrableOn (fun s => |f s| * s ^ (c / 2 - 1)) (Ioi 0) := by
  obtain ⟨C, _, hC⟩ := K.φ_bound
  have hbd : ∀ s ≥ 0, |f s| ≤ C * hankelMass c f := eigenfn_abs_le hc hf hC
  have hsm : AEStronglyMeasurable (fun s => |f s| * s ^ (c / 2 - 1)) (volume.restrict (Ioi 0)) :=
    ((hf.cont.abs.mono Ioi_subset_Ici_self).mul
      (ContinuousOn.rpow_const continuousOn_id fun s hs =>
        Or.inl (ne_of_gt (mem_Ioi.mp hs)))).aestronglyMeasurable measurableSet_Ioi
  have h1 : IntegrableOn (fun s => |f s| * s ^ (c / 2 - 1)) (Ioc 0 1) := by
    have hrpow : IntegrableOn (fun s : ℝ => (C * hankelMass c f) * s ^ (c / 2 - 1)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul _
    refine hrpow.mono' (hsm.mono_measure (Measure.restrict_mono Ioc_subset_Ioi_self le_rfl))
      ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hs0.le _))]
    exact mul_le_mul_of_nonneg_right (hbd s hs0.le) (Real.rpow_nonneg hs0.le _)
  have h2 : IntegrableOn (fun s => |f s| * s ^ (c / 2 - 1)) (Ioi 1) := by
    have hdom : IntegrableOn (fun s => (Real.Gamma c / (2 * π) ^ c) * (|f s| * hankelRho0 c s))
        (Ioi 1) :=
      ((abs_mul_rho0_integrableOn hc hf.int).mono_set (Ioi_subset_Ioi zero_le_one)).const_mul _
    refine hdom.mono' (hsm.mono_measure (Measure.restrict_mono (Ioi_subset_Ioi zero_le_one) le_rfl))
      ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 1 < s) => ?_)
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hs0.le _))]
    have hrle : s ^ (c / 2 - 1) ≤ s ^ (c - 1) :=
      Real.rpow_le_rpow_of_exponent_le hs.le (by linarith)
    calc |f s| * s ^ (c / 2 - 1) ≤ |f s| * s ^ (c - 1) :=
          mul_le_mul_of_nonneg_left hrle (abs_nonneg _)
      _ = (Real.Gamma c / (2 * π) ^ c) * (|f s| * hankelRho0 c s) := by
          unfold hankelRho0
          field_simp [(Real.Gamma_pos_of_pos hc).ne',
            (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * π) c).ne']
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ)]
  exact h1.union h2

private lemma intertwiner_mul_rpow_integrable {c : ℝ} (hc : 0 < c) {K : HankelKernelData c}
    {f : ℝ → ℝ} (hf : IsRadialEigenfn c K (-1) f) :
    IntegrableOn (fun s => f s * s ^ (c / 2 - 1)) (Ioi 0) := by
  refine (intertwiner_integrable hc hf).mono'
    (((hf.cont.mono Ioi_subset_Ici_self).mul
      (ContinuousOn.rpow_const continuousOn_id fun s hs =>
        Or.inl (ne_of_gt (mem_Ioi.mp hs)))).aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _)]

private lemma intertwiner_fubini_identity {c : ℝ} (hc : 0 < c) {K : HankelKernelData c}
    {f : ℝ → ℝ} (hf : IsRadialEigenfn c K (-1) f) {Y : ℝ} (hY : 0 < Y) :
    - ∫ u in Ioc (0 : ℝ) Y, f u * u ^ (c / 2 - 1) =
      ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1) *
        (((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w) := by
  let F : ℝ → ℝ → ℝ := fun u s => u ^ (c / 2 - 1) * (f s * hankelRho0 c s * K.φ (u * s))
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) Y)
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hprod : μ.prod ν = volume.restrict (Ioc (0 : ℝ) Y ×ˢ Ioi (0 : ℝ)) := by
    dsimp [μ, ν]; rw [Measure.volume_eq_prod ℝ ℝ]
    exact Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ioc (0 : ℝ) Y) (Ioi (0 : ℝ))
  have hF_aesm : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := by
    rw [hprod]
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioc.prod measurableSet_Ioi)
    have hp1 : ContinuousOn (fun p : ℝ × ℝ => p.1 ^ (c / 2 - 1)) (Ioc (0 : ℝ) Y ×ˢ Ioi (0 : ℝ)) :=
      ContinuousOn.rpow_const continuous_fst.continuousOn fun _ hp => Or.inl hp.1.1.ne'
    have hf2 : ContinuousOn (fun p : ℝ × ℝ => f p.2) (Ioc (0 : ℝ) Y ×ˢ Ioi (0 : ℝ)) :=
      hf.cont.comp continuous_snd.continuousOn fun _ hp => le_of_lt hp.2
    have hr2 : ContinuousOn (fun p : ℝ × ℝ => hankelRho0 c p.2) (Ioc (0 : ℝ) Y ×ˢ Ioi (0 : ℝ)) :=
      (continuousOn_hankelRho0 c).comp continuous_snd.continuousOn fun _ hp => hp.2
    have hφ : ContinuousOn (fun p : ℝ × ℝ => K.φ (p.1 * p.2)) (Ioc (0 : ℝ) Y ×ˢ Ioi (0 : ℝ)) :=
      (K.φ_cont.comp (continuous_fst.mul continuous_snd)).continuousOn
    exact hp1.mul ((hf2.mul hr2).mul hφ)
  have hF_int : Integrable (Function.uncurry F) (μ.prod ν) := by
    obtain ⟨C, _, hC⟩ := K.φ_bound
    have hGu : Integrable (fun u => C * u ^ (c / 2 - 1)) μ :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hY.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul C
    have hGs : Integrable (fun s => |f s| * hankelRho0 c s) ν :=
      abs_mul_rho0_integrableOn hc hf.int
    refine (hGu.mul_prod hGs).mono' hF_aesm ?_
    rw [hprod]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioi)] with p hp
    have hp1 : 0 < p.1 := hp.1.1
    have hp2 : 0 < p.2 := hp.2
    dsimp [F, Function.uncurry]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hp1.le _),
      abs_of_nonneg (hankelRho0_nonneg hc hp2.le)]
    calc p.1 ^ (c / 2 - 1) * (|f p.2| * hankelRho0 c p.2 * |K.φ (p.1 * p.2)|)
        ≤ p.1 ^ (c / 2 - 1) * (|f p.2| * hankelRho0 c p.2 * C) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hC _ (mul_nonneg hp1.le hp2.le))
              (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc hp2.le)))
            (Real.rpow_nonneg hp1.le _)
      _ = C * p.1 ^ (c / 2 - 1) * (|f p.2| * hankelRho0 c p.2) := by ring
  have hLHS : - ∫ u in Ioc (0 : ℝ) Y, f u * u ^ (c / 2 - 1) =
      ∫ u in Ioc (0 : ℝ) Y, ∫ s in Ioi (0 : ℝ), F u s := by
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    have hu0 : 0 < u := hu.1
    have heig := hf.eigen u hu0.le
    have hsub : -f u = hankelTransform c K f u := by linarith
    dsimp [F]
    rw [show -(f u * u ^ (c / 2 - 1)) = u ^ (c / 2 - 1) * (-f u) by ring, hsub]
    unfold hankelTransform
    rw [← integral_const_mul]
  rw [hLHS]
  change ∫ u, ∫ s, F u s ∂ν ∂μ = _
  rw [integral_integral_swap hF_int]
  refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
  dsimp [F]
  have hpull : ∫ u in Ioc (0 : ℝ) Y, u ^ (c / 2 - 1) * (f s * hankelRho0 c s * K.φ (u * s)) =
      (f s * hankelRho0 c s) * ∫ u in Ioc (0 : ℝ) Y, u ^ (c / 2 - 1) * K.φ (u * s) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => by ring
  rw [hpull]
  have hcov : ∫ u in Ioc (0 : ℝ) Y, u ^ (c / 2 - 1) * K.φ (u * s) =
      s ^ (-(c / 2)) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w := by
    have hcongr : ∫ u in Ioc (0 : ℝ) Y, u ^ (c / 2 - 1) * K.φ (u * s) =
        ∫ u in Ioc (0 : ℝ) Y, s ^ (1 - c / 2) * ((u * s) ^ (c / 2 - 1) * K.φ (u * s)) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      have hu0 : 0 ≤ u := hu.1.le
      have hr : s ^ (1 - c / 2) * (u * s) ^ (c / 2 - 1) = u ^ (c / 2 - 1) := by
        rw [Real.mul_rpow hu0 hs.le, ← mul_assoc, mul_comm (s ^ (1 - c / 2)) _, mul_assoc,
          ← Real.rpow_add hs, show (1 - c / 2) + (c / 2 - 1) = 0 by ring, Real.rpow_zero, mul_one]
      calc u ^ (c / 2 - 1) * K.φ (u * s)
          = (s ^ (1 - c / 2) * (u * s) ^ (c / 2 - 1)) * K.φ (u * s) := by rw [hr]
        _ = s ^ (1 - c / 2) * ((u * s) ^ (c / 2 - 1) * K.φ (u * s)) := by ring
    rw [hcongr, ← intervalIntegral.integral_of_le hY.le, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_right (f := fun w => w ^ (c / 2 - 1) * K.φ w) hs.ne',
      zero_mul, intervalIntegral.integral_of_le (mul_nonneg hY.le hs.le), smul_eq_mul]
    have hexp : s ^ (1 - c / 2) * s⁻¹ = s ^ (-(c / 2)) := by
      rw [← Real.rpow_neg_one s, ← Real.rpow_add hs]
      congr 1; ring
    rw [← mul_assoc, hexp]
  rw [hcov]
  unfold hankelRho0
  have hs_exp : s ^ (c - 1) * s ^ (-(c / 2)) = s ^ (c / 2 - 1) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  calc f s * ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1)) *
        (s ^ (-(c / 2)) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w)
      = f s * (s ^ (c - 1) * s ^ (-(c / 2))) *
          (((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w) := by
        ring
    _ = f s * s ^ (c / 2 - 1) *
          (((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w) := by
        rw [hs_exp]

/-- Proposition 7.9a(1), zero integral: `∫_0^∞ f(s) s^{c/2 - 1} ds = 0` for `f ∈ 𝒜_c^{-1}`. -/
theorem intertwiner_integral_zero {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) :
    ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1) = 0 := by
  have hI_int := intertwiner_mul_rpow_integrable hc hf
  have hAbs_int := intertwiner_integrable hc hf
  let I : ℝ := ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1)
  have hLHS : Tendsto (fun Y : ℝ => - ∫ u in Ioc (0 : ℝ) Y, f u * u ^ (c / 2 - 1)) atTop (𝓝 (-I)) := by
    have ht : Tendsto (fun Y : ℝ => ∫ u in Ioi (0 : ℝ),
        (Ioc (0 : ℝ) Y).indicator (fun u => f u * u ^ (c / 2 - 1)) u) atTop (𝓝 I) := by
      refine tendsto_integral_filter_of_dominated_convergence
        (fun u => |f u| * u ^ (c / 2 - 1)) ?_ (Eventually.of_forall fun Y => ?_) hAbs_int ?_
      · exact Eventually.of_forall fun Y => hI_int.aestronglyMeasurable.indicator measurableSet_Ioc
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
        by_cases hm : u ∈ Ioc (0 : ℝ) Y
        · rw [Set.indicator_of_mem hm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu.le _)]
        · rw [Set.indicator_of_notMem hm, norm_zero]
          exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hu.le _)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop u] with Y hYu
        simp only [Set.indicator_apply, Set.mem_Ioc, hu, hYu, and_self, ↓reduceIte]
    refine ht.neg.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y _
    rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr Ioc_subset_Ioi_self]
  have hRHS : Tendsto (fun Y : ℝ => ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1) *
      (((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w))
      atTop (𝓝 I) := by
    obtain ⟨M, _, hM⟩ := K.antideriv_bound
    let A : ℝ → ℝ := fun X => ((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) X, w ^ (c / 2 - 1) * K.φ w
    refine tendsto_integral_filter_of_dominated_convergence
      (fun s => M * (|f s| * s ^ (c / 2 - 1))) ?_ ?_ (hAbs_int.const_mul M) ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
      have hA_cont : ContinuousOn (fun s => A (Y * s)) (Ioi 0) := by
        intro s hs
        have hs0 : 0 < s := mem_Ioi.mp hs
        let g : ℝ → ℝ := fun w => w ^ (c / 2 - 1) * K.φ w
        have hg_int : IntervalIntegrable g volume 0 (Y * s + 1) := by
          have hr : IntervalIntegrable (fun w : ℝ => w ^ (c / 2 - 1)) volume 0 (Y * s + 1) :=
            intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1)
          obtain ⟨C, hC0, hC⟩ := K.φ_bound
          have hYs1 : 0 ≤ Y * s + 1 := by positivity
          refine (hr.norm.const_mul C).mono_fun ?_ ?_
          · exact (((ContinuousOn.rpow_const continuousOn_id fun x hx =>
              Or.inl (ne_of_gt (mem_Ioi.mp hx))).mul K.φ_cont.continuousOn).aestronglyMeasurable
              measurableSet_Ioi).mono_measure
              (Measure.restrict_mono (by intro x hx; rw [Set.uIoc_of_le hYs1] at hx; exact hx.1) le_rfl)
          · filter_upwards [ae_restrict_mem measurableSet_uIoc] with w hw
            rw [Set.uIoc_of_le hYs1] at hw
            simp only [g, Real.norm_eq_abs]
            rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hw.1.le _),
              abs_of_nonneg (mul_nonneg hC0 (Real.rpow_nonneg hw.1.le _)), mul_comm C]
            exact mul_le_mul_of_nonneg_left (hC w hw.1.le) (Real.rpow_nonneg hw.1.le _)
        have hprim : ContinuousOn (fun x => ∫ w in (0 : ℝ)..x, g w) (uIcc 0 (Y * s + 1)) :=
          intervalIntegral.continuousOn_primitive_interval' hg_int left_mem_uIcc
        rw [Set.uIcc_of_le (by positivity : (0 : ℝ) ≤ Y * s + 1)] at hprim
        have hYs_cont : ContinuousAt (fun x => ∫ w in (0 : ℝ)..x, g w) (Y * s) :=
          hprim.continuousAt (Icc_mem_nhds (mul_pos hY hs0) (by linarith))
        have hA_eq : (fun x => A (Y * x)) =ᶠ[𝓝 s]
            fun x => ((2 * π) ^ c / Real.Gamma c) * ∫ w in (0 : ℝ)..(Y * x), g w := by
          filter_upwards [Ioi_mem_nhds hs0] with x hx
          dsimp only [A]
          rw [intervalIntegral.integral_of_le (mul_pos hY hx).le]
        exact ((((hYs_cont.comp (continuous_const_mul Y).continuousAt).const_mul
          ((2 * π) ^ c / Real.Gamma c)).congr_of_eventuallyEq hA_eq)).continuousWithinAt
      exact hI_int.aestronglyMeasurable.mul (hA_cont.aestronglyMeasurable measurableSet_Ioi)
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with Y hY
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.le _)]
      calc |f s| * s ^ (c / 2 - 1) * |A (Y * s)|
          ≤ |f s| * s ^ (c / 2 - 1) * M := by gcongr; exact hM (Y * s) (mul_nonneg hY hs.le)
        _ = M * (|f s| * s ^ (c / 2 - 1)) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s (hs : 0 < s)
      have hmul : Tendsto (fun Y : ℝ => f s * s ^ (c / 2 - 1) * A (Y * s)) atTop
          (𝓝 (f s * s ^ (c / 2 - 1) * 1)) :=
        tendsto_const_nhds.mul (K.antideriv_tendsto.comp (tendsto_id.atTop_mul_const hs))
      simpa using hmul
  have heq : (fun Y : ℝ => - ∫ u in Ioc (0 : ℝ) Y, f u * u ^ (c / 2 - 1)) =ᶠ[atTop]
      (fun Y : ℝ => ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1) *
        (((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) (Y * s), w ^ (c / 2 - 1) * K.φ w)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
    exact intertwiner_fubini_identity hc hf hY
  have hneg_eq : -I = I := tendsto_nhds_unique (hLHS.congr' heq) hRHS
  change I = 0; linarith

/-- Proposition 7.9a(2), alternative left formula:
`(ℐ_c f)(Δ) = -Δ^{-c/2} ∫_0^Δ f(s) s^{c/2 - 1} ds` for `Δ > 0`. -/
theorem intertwiner_eq_neg_left {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) {Δ : ℝ} (hΔ : 0 < Δ) :
    intertwiner c f Δ = -Δ ^ (-(c / 2)) * ∫ s in Ioc (0 : ℝ) Δ, f s * s ^ (c / 2 - 1) := by
  have hint := intertwiner_mul_rpow_integrable hc hf
  have hsplit : ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1) =
      (∫ s in Ioc (0 : ℝ) Δ, f s * s ^ (c / 2 - 1)) + ∫ s in Ioi Δ, f s * s ^ (c / 2 - 1) := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hΔ.le)),
      Set.Ioc_union_Ioi_eq_Ioi hΔ.le]
  rw [intertwiner_integral_zero hc hf] at hsplit
  have htail : ∫ s in Ioi Δ, f s * s ^ (c / 2 - 1) =
      - ∫ s in Ioc (0 : ℝ) Δ, f s * s ^ (c / 2 - 1) := by linarith
  unfold intertwiner
  simp only [hΔ, ↓reduceIte, htail]; ring

@[simp]
theorem intertwiner_zero (c : ℝ) (f : ℝ → ℝ) : intertwiner c f 0 = -(2 / c) * f 0 := by
  simp [intertwiner]

/-- Proposition 7.9a(2), continuity on `[0, ∞)`: `ℐ_c f` is continuous on `Ici 0`. -/
theorem intertwiner_continuousOn {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) : ContinuousOn (intertwiner c f) (Ici 0) := by
  have hint := intertwiner_mul_rpow_integrable hc hf
  have hIoi : ContinuousOn (intertwiner c f) (Ioi 0) := by
    intro Δ hΔ
    have hΔpos : 0 < Δ := mem_Ioi.mp hΔ
    have hg_int : IntervalIntegrable (fun s => f s * s ^ (c / 2 - 1)) volume 0 (Δ + 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mpr
        (hint.mono_set (Set.Ioc_subset_Ioi_self))
    have hprim : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, f s * s ^ (c / 2 - 1))
        (uIcc 0 (Δ + 1)) :=
      intervalIntegral.continuousOn_primitive_interval' hg_int left_mem_uIcc
    rw [Set.uIcc_of_le (by linarith : (0 : ℝ) ≤ Δ + 1)] at hprim
    have hprim_at : ContinuousAt (fun x => ∫ s in (0 : ℝ)..x, f s * s ^ (c / 2 - 1)) Δ :=
      hprim.continuousAt (Icc_mem_nhds hΔpos (by linarith))
    have hrpow_at : ContinuousAt (fun x : ℝ => -x ^ (-(c / 2))) Δ :=
      (continuousAt_id.rpow_const (Or.inl hΔpos.ne')).neg
    have hev : (intertwiner c f) =ᶠ[𝓝 Δ]
        fun x => -x ^ (-(c / 2)) * ∫ s in (0 : ℝ)..x, f s * s ^ (c / 2 - 1) := by
      filter_upwards [Ioi_mem_nhds hΔpos] with x hx
      rw [intertwiner_eq_neg_left hc hf hx, intervalIntegral.integral_of_le hx.le]
    exact ((hrpow_at.mul hprim_at).congr_of_eventuallyEq hev).continuousWithinAt
  intro Δ hΔ
  rcases eq_or_lt_of_le (mem_Ici.mp hΔ) with rfl | hΔpos
  · rw [Metric.continuousWithinAt_iff]
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp (hf.cont 0 self_mem_Ici)
      (ε * (c / 4)) (by positivity)
    refine ⟨δ, hδpos, fun Δ' hΔ' hdist => ?_⟩
    rcases eq_or_lt_of_le (mem_Ici.mp hΔ') with rfl | hΔ'pos
    · simpa using hε
    · rw [intertwiner_zero, intertwiner_eq_neg_left hc hf hΔ'pos, Real.dist_eq]
      have hrpow_int : ∫ s in Ioc (0 : ℝ) Δ', s ^ (c / 2 - 1) = Δ' ^ (c / 2) / (c / 2) := by
        rw [← intervalIntegral.integral_of_le hΔ'pos.le,
          integral_rpow (Or.inl (by linarith : -1 < c / 2 - 1)),
          Real.zero_rpow (by linarith : c / 2 - 1 + 1 ≠ 0)]
        ring
      have h0_eq : -(2 / c) * f 0 =
          -Δ' ^ (-(c / 2)) * ∫ s in Ioc (0 : ℝ) Δ', f 0 * s ^ (c / 2 - 1) := by
        rw [integral_const_mul, hrpow_int]
        have hpow : Δ' ^ (-(c / 2)) * Δ' ^ (c / 2) = 1 := by
          rw [← Real.rpow_add hΔ'pos, neg_add_cancel, Real.rpow_zero]
        calc -(2 / c) * f 0 = -1 * (f 0 / (c / 2)) := by ring
          _ = -(Δ' ^ (-(c / 2)) * Δ' ^ (c / 2)) * (f 0 / (c / 2)) := by rw [hpow]
          _ = -Δ' ^ (-(c / 2)) * (f 0 * (Δ' ^ (c / 2) / (c / 2))) := by ring
      have hdiff : -Δ' ^ (-(c / 2)) * (∫ s in Ioc (0 : ℝ) Δ', f s * s ^ (c / 2 - 1)) -
          (-(2 / c) * f 0) =
          -Δ' ^ (-(c / 2)) * ∫ s in Ioc (0 : ℝ) Δ', (f s - f 0) * s ^ (c / 2 - 1) := by
        rw [h0_eq, ← mul_sub, ← integral_sub (hint.mono_set Ioc_subset_Ioi_self)
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ'pos.le).mp
            (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul (f 0))]
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioc fun s _ => by ring
      rw [hdiff, abs_mul, abs_neg, abs_of_nonneg (Real.rpow_nonneg hΔ'pos.le _)]
      have hsub_int : IntegrableOn (fun s => (f s - f 0) * s ^ (c / 2 - 1)) (Ioc 0 Δ') :=
        ((hint.mono_set Ioc_subset_Ioi_self).sub
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ'pos.le).mp
            (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul (f 0))).congr_fun
          (fun s _ => by dsimp; ring) measurableSet_Ioc
      have hint_le : |∫ s in Ioc (0 : ℝ) Δ', (f s - f 0) * s ^ (c / 2 - 1)| ≤
          ∫ s in Ioc (0 : ℝ) Δ', (ε * (c / 4)) * s ^ (c / 2 - 1) := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on hsub_int.norm
          (((intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ'pos.le).mp
            (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))).const_mul _)
          measurableSet_Ioc fun s hs => ?_)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs.1.le _)]
        have hsδ : dist s 0 < δ := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1.le]
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hΔ'pos.le] at hdist
          linarith [hs.2]
        exact mul_le_mul_of_nonneg_right (le_of_lt (hδ hs.1.le hsδ)) (Real.rpow_nonneg hs.1.le _)
      have hint_eq : ∫ s in Ioc (0 : ℝ) Δ', (ε * (c / 4)) * s ^ (c / 2 - 1) =
          (ε * (c / 4)) * (Δ' ^ (c / 2) / (c / 2)) := by
        rw [integral_const_mul, hrpow_int]
      have hpow : Δ' ^ (-(c / 2)) * Δ' ^ (c / 2) = 1 := by
        rw [← Real.rpow_add hΔ'pos, neg_add_cancel, Real.rpow_zero]
      calc Δ' ^ (-(c / 2)) * |∫ s in Ioc (0 : ℝ) Δ', (f s - f 0) * s ^ (c / 2 - 1)|
          ≤ Δ' ^ (-(c / 2)) * ((ε * (c / 4)) * (Δ' ^ (c / 2) / (c / 2))) := by
            gcongr; exact hint_le.trans_eq hint_eq
        _ = (ε / 2) * (Δ' ^ (-(c / 2)) * Δ' ^ (c / 2)) := by
            field_simp [hc.ne']; norm_num
        _ = ε / 2 := by rw [hpow, mul_one]
        _ < ε := half_lt_self hε
  · exact (hIoi.continuousAt (Ioi_mem_nhds hΔpos)).continuousWithinAt

private lemma intertwiner_tonelli_bound {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) :
    let μ := volume.restrict (Ioi (0 : ℝ))
    let G : ℝ × ℝ → ℝ := fun p =>
      if p.1 < p.2 then ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * (|f p.2| * p.2 ^ (c / 2 - 1))
      else 0
    Integrable G (μ.prod μ) ∧ ∫ p, G p ∂(μ.prod μ) = (2 / c) * hankelMass c f := by
  intro μ G
  have hprod : μ.prod μ = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    dsimp [μ]; rw [Measure.volume_eq_prod ℝ ℝ]
    exact Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ioi (0 : ℝ)) (Ioi (0 : ℝ))
  have hG_aesm : AEStronglyMeasurable G (μ.prod μ) := by
    rw [hprod]
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
    have h1 : ContinuousOn (fun p : ℝ × ℝ => ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1))
        (Ioi 0 ×ˢ Ioi 0) :=
      (ContinuousOn.rpow_const continuous_fst.continuousOn fun _ hp => Or.inl hp.1.ne').const_mul _
    have h2 : ContinuousOn (fun p : ℝ × ℝ => |f p.2| * p.2 ^ (c / 2 - 1)) (Ioi 0 ×ˢ Ioi 0) :=
      (hf.cont.abs.comp continuous_snd.continuousOn fun _ hp => hp.2.le).mul
        (ContinuousOn.rpow_const continuous_snd.continuousOn fun _ hp => Or.inl hp.2.ne')
    exact h1.mul h2
  have hcol_int : ∀ s ∈ Ioi (0 : ℝ),
      IntegrableOn (fun t => G (t, s)) (Ioi 0) ∧
        ∫ t in Ioi (0 : ℝ), G (t, s) = (2 / c) * (|f s| * hankelRho0 c s) := by
    intro s (hs : 0 < s)
    have hr : IntegrableOn (fun t : ℝ => t ^ (c / 2 - 1)) (Ioc 0 s) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.le).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < c / 2 - 1))
    have hEq : Set.EqOn (fun t => G (t, s))
        ((Ioo (0 : ℝ) s).indicator
          (fun t => ((2 * π) ^ c / Real.Gamma c) * (|f s| * s ^ (c / 2 - 1)) * t ^ (c / 2 - 1)))
        (Ioi 0) := by
      intro t (ht : 0 < t)
      dsimp [G]
      by_cases hts : t < s
      · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioo, ht, and_self]; ring
      · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioo, and_false]
    have hr_oo : IntegrableOn (fun t : ℝ => t ^ (c / 2 - 1)) (Ioo 0 s) :=
      hr.mono_set Ioo_subset_Ioc_self
    have hind_int : IntegrableOn
        ((Ioo (0 : ℝ) s).indicator
          (fun t => ((2 * π) ^ c / Real.Gamma c) * (|f s| * s ^ (c / 2 - 1)) * t ^ (c / 2 - 1)))
        (Ioi 0) := by
      rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioo, IntegrableOn,
        Measure.restrict_restrict measurableSet_Ioo, Set.inter_eq_left.mpr Ioo_subset_Ioi_self]
      exact hr_oo.const_mul _
    have hGt_int : IntegrableOn (fun t => G (t, s)) (Ioi 0) :=
      hind_int.congr_fun hEq.symm measurableSet_Ioi
    refine ⟨hGt_int, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hEq, setIntegral_indicator measurableSet_Ioo,
      Set.inter_eq_right.mpr Ioo_subset_Ioi_self, ← integral_Ioc_eq_integral_Ioo,
      integral_const_mul, ← intervalIntegral.integral_of_le hs.le,
      integral_rpow (Or.inl (by linarith : -1 < c / 2 - 1)),
      Real.zero_rpow (by linarith : c / 2 - 1 + 1 ≠ 0), sub_zero]
    unfold hankelRho0
    have hpow : s ^ (c / 2 - 1) * s ^ (c / 2 - 1 + 1) = s ^ (c - 1) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    calc ((2 * π) ^ c / Real.Gamma c) * (|f s| * s ^ (c / 2 - 1)) * (s ^ (c / 2 - 1 + 1) / (c / 2 - 1 + 1))
        = (1 / (c / 2)) * ((2 * π) ^ c / Real.Gamma c * |f s| * (s ^ (c / 2 - 1) * s ^ (c / 2 - 1 + 1))) := by
          have : c / 2 - 1 + 1 = c / 2 := by ring
          rw [this]; ring
      _ = (2 / c) * (|f s| * ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1))) := by rw [hpow]; ring
  have hcol_ae : ∀ᵐ s ∂μ, Integrable (fun t => G (t, s)) μ :=
    (ae_restrict_mem measurableSet_Ioi).mono fun s hs => (hcol_int s hs).1
  have houter : Integrable (fun s => ∫ t, ‖G (t, s)‖ ∂μ) μ := by
    have hbase : Integrable (fun s => (2 / c) * (|f s| * hankelRho0 c s)) μ :=
      (abs_mul_rho0_integrableOn hc hf.int).const_mul _
    refine hbase.congr ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) => ?_)
    dsimp only
    rw [← (hcol_int s hs).2]
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg]
    dsimp [G]
    split_ifs
    · exact mul_nonneg (mul_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) _)
        (Real.Gamma_pos_of_pos hc).le) (Real.rpow_nonneg ht.le _))
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hs.le _))
    · exact le_rfl
  have hG_int : Integrable G (μ.prod μ) :=
    (integrable_prod_iff' hG_aesm).mpr ⟨hcol_ae, houter⟩
  refine ⟨hG_int, ?_⟩
  rw [integral_prod_symm _ hG_int]
  have h_eq : ∫ s, ∫ t, G (t, s) ∂μ ∂μ = ∫ s in Ioi (0 : ℝ), (2 / c) * (|f s| * hankelRho0 c s) :=
    setIntegral_congr_fun measurableSet_Ioi fun s hs => (hcol_int s hs).2
  rw [h_eq, integral_const_mul]
  rfl

/-- Proposition 7.9a(2), `L¹` mass contraction: `ℐ_c f` lies in `L¹(ρ₀)` and
`M[ℐ_c f] ≤ (2 / c) M[f]`. -/
theorem hankelMass_intertwiner_le {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) :
    IntegrableOn (fun Δ => intertwiner c f Δ * hankelRho0 c Δ) (Ioi 0) ∧
      hankelMass c (intertwiner c f) ≤ (2 / c) * hankelMass c f := by
  obtain ⟨hG_int, hG_eq⟩ := intertwiner_tonelli_bound hc hf
  let μ := volume.restrict (Ioi (0 : ℝ))
  let G : ℝ × ℝ → ℝ := fun p =>
    if p.1 < p.2 then ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * (|f p.2| * p.2 ^ (c / 2 - 1))
    else 0
  have hrow_int : Integrable (fun t => ∫ s in Ioi (0 : ℝ), G (t, s)) μ := hG_int.integral_prod_left
  have hrow_eq : ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), G (t, s) = (2 / c) * hankelMass c f := by
    change ∫ t, ∫ s, G (t, s) ∂μ ∂μ = _
    rw [← integral_prod _ hG_int]
    exact hG_eq
  have hpt : ∀ t ∈ Ioi (0 : ℝ), |intertwiner c f t| * hankelRho0 c t ≤ ∫ s in Ioi (0 : ℝ), G (t, s) := by
    intro t (ht : 0 < t)
    unfold intertwiner
    simp only [ht, ↓reduceIte]
    have hcoeff : ((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) = t ^ (-(c / 2)) * hankelRho0 c t := by
      unfold hankelRho0
      have : t ^ (-(c / 2)) * t ^ (c - 1) = t ^ (c / 2 - 1) := by
        rw [← Real.rpow_add ht]; congr 1; ring
      calc ((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1)
          = ((2 * π) ^ c / Real.Gamma c) * (t ^ (-(c / 2)) * t ^ (c - 1)) := by rw [this]
        _ = t ^ (-(c / 2)) * ((2 * π) ^ c / Real.Gamma c * t ^ (c - 1)) := by ring
    have hs_eq : Set.EqOn (fun s => G (t, s))
        ((Ioi t).indicator (fun s => ((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) * (|f s| * s ^ (c / 2 - 1))))
        (Ioi 0) := by
      intro s _
      dsimp [G]
      by_cases hts : t < s
      · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioi]
      · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioi]
    have hrhs : ∫ s in Ioi (0 : ℝ), G (t, s) =
        ((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) * ∫ s in Ioi t, |f s| * s ^ (c / 2 - 1) := by
      rw [setIntegral_congr_fun measurableSet_Ioi hs_eq, setIntegral_indicator measurableSet_Ioi,
        Set.inter_eq_right.mpr (Ioi_subset_Ioi ht.le), integral_const_mul]
    rw [hrhs, hcoeff, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _)]
    have hnorm : |∫ s in Ioi t, f s * s ^ (c / 2 - 1)| ≤ ∫ s in Ioi t, |f s| * s ^ (c / 2 - 1) := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans_eq (setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (ht.trans hs).le _)]
    calc t ^ (-(c / 2)) * |∫ s in Ioi t, f s * s ^ (c / 2 - 1)| * hankelRho0 c t
        = (t ^ (-(c / 2)) * hankelRho0 c t) * |∫ s in Ioi t, f s * s ^ (c / 2 - 1)| := by ring
      _ ≤ (t ^ (-(c / 2)) * hankelRho0 c t) * ∫ s in Ioi t, |f s| * s ^ (c / 2 - 1) :=
          mul_le_mul_of_nonneg_left hnorm (mul_nonneg (Real.rpow_nonneg ht.le _) (hankelRho0_nonneg hc ht.le))
  have hsm : AEStronglyMeasurable (fun Δ => intertwiner c f Δ * hankelRho0 c Δ) μ :=
    (((intertwiner_continuousOn hc hf).mono Ioi_subset_Ici_self).mul
      (continuousOn_hankelRho0 c)).aestronglyMeasurable measurableSet_Ioi
  have hint_prod : IntegrableOn (fun Δ => intertwiner c f Δ * hankelRho0 c Δ) (Ioi 0) := by
    refine hrow_int.mono' hsm ((ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc ht.le)]
    exact hpt t ht
  refine ⟨hint_prod, ?_⟩
  rw [← hrow_eq]
  unfold hankelMass
  exact setIntegral_mono_on (abs_mul_rho0_integrableOn hc hint_prod) hrow_int measurableSet_Ioi hpt

/-- Proposition 7.9a(2), injectivity on `𝒜_c^{-1}`: if `ℐ_c f = 0` on `[0, ∞)` then `f = 0` on `[0, ∞)`. -/
theorem intertwiner_injective {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) (h0 : ∀ Δ ∈ Ici (0 : ℝ), intertwiner c f Δ = 0) :
    ∀ Δ ∈ Ici (0 : ℝ), f Δ = 0 := by
  have hint := intertwiner_mul_rpow_integrable hc hf
  have hprim0 : ∀ Δ > 0, ∫ s in (0 : ℝ)..Δ, f s * s ^ (c / 2 - 1) = 0 := by
    intro Δ hΔ
    have hI := h0 Δ hΔ.le
    rw [intertwiner_eq_neg_left hc hf hΔ] at hI
    rw [intervalIntegral.integral_of_le hΔ.le]
    have hne : -Δ ^ (-(c / 2)) ≠ 0 := neg_ne_zero.mpr (Real.rpow_pos_of_pos hΔ _).ne'
    exact (mul_eq_zero.mp hI).resolve_left hne
  have hIoi0 : ∀ Δ ∈ Ioi (0 : ℝ), f Δ = 0 := by
    intro Δ (hΔ : 0 < Δ)
    have h_int : IntervalIntegrable (fun s => f s * s ^ (c / 2 - 1)) volume 0 Δ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hΔ.le).mpr (hint.mono_set Ioc_subset_Ioi_self)
    have h_contOn : ContinuousOn (fun s => f s * s ^ (c / 2 - 1)) (Ioi 0) :=
      (hf.cont.mono Ioi_subset_Ici_self).mul
        (ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (ne_of_gt (mem_Ioi.mp hs)))
    have h_cont : ContinuousAt (fun s => f s * s ^ (c / 2 - 1)) Δ :=
      h_contOn.continuousAt (Ioi_mem_nhds hΔ)
    have hsm : StronglyMeasurableAtFilter (fun s => f s * s ^ (c / 2 - 1)) (𝓝 Δ) := by
      rw [← isOpen_Ioi.nhdsWithin_eq hΔ]
      exact h_contOn.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi Δ
    have hderiv : HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, f s * s ^ (c / 2 - 1))
        (f Δ * Δ ^ (c / 2 - 1)) Δ :=
      intervalIntegral.integral_hasDerivAt_right h_int hsm h_cont
    have hderiv0 : HasDerivAt (fun x => ∫ s in (0 : ℝ)..x, f s * s ^ (c / 2 - 1)) 0 Δ := by
      refine (hasDerivAt_const Δ (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hΔ] with x hx
      exact hprim0 x hx
    have hmul0 : f Δ * Δ ^ (c / 2 - 1) = 0 := hderiv.unique hderiv0
    exact (mul_eq_zero.mp hmul0).resolve_right (Real.rpow_pos_of_pos hΔ _).ne'
  intro Δ hΔ
  rcases eq_or_lt_of_le (mem_Ici.mp hΔ) with rfl | hΔpos
  · have ht1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) :=
      (hf.cont 0 self_mem_Ici).mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)
    have ht2 : Tendsto f (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x hx => (hIoi0 x hx).symm)
    exact tendsto_nhds_unique ht1 ht2
  · exact hIoi0 Δ hΔpos

/-- Proposition 7.9a(2), Hankel eigenvalue flip: `T_c(ℐ_c f) = +ℐ_c f`, so `ℐ_c f ∈ 𝒜_c^{+1}`. -/
theorem intertwiner_eigen {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {f : ℝ → ℝ}
    (hf : IsRadialEigenfn c K (-1) f) :
    IsRadialEigenfn c K 1 (intertwiner c f) := by
  refine ⟨intertwiner_continuousOn hc hf, (hankelMass_intertwiner_le hc hf).1, fun Δ hΔ => ?_⟩
  rw [one_mul]
  obtain ⟨hG_int, _⟩ := intertwiner_tonelli_bound hc hf
  let μ := volume.restrict (Ioi (0 : ℝ))
  let G : ℝ × ℝ → ℝ := fun p =>
    if p.1 < p.2 then ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * (|f p.2| * p.2 ^ (c / 2 - 1))
    else 0
  have hprod : μ.prod μ = volume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) := by
    dsimp [μ]; rw [Measure.volume_eq_prod ℝ ℝ]
    exact Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (Ioi (0 : ℝ)) (Ioi (0 : ℝ))
  obtain ⟨C, _, hC⟩ := K.φ_bound
  let F : ℝ × ℝ → ℝ := fun p =>
    if p.1 < p.2 then ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * K.φ (Δ * p.1) *
      (f p.2 * p.2 ^ (c / 2 - 1)) else 0
  have hF_aesm : AEStronglyMeasurable F (μ.prod μ) := by
    rw [hprod]
    refine AEStronglyMeasurable.indicator ?_ (measurableSet_lt measurable_fst measurable_snd)
    refine ContinuousOn.aestronglyMeasurable ?_ (measurableSet_Ioi.prod measurableSet_Ioi)
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * K.φ (Δ * p.1)) (Ioi 0 ×ˢ Ioi 0) :=
      ((ContinuousOn.rpow_const continuous_fst.continuousOn fun _ hp => Or.inl hp.1.ne').const_mul _).mul
        (K.φ_cont.comp (continuous_const_mul Δ |>.comp continuous_fst)).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => f p.2 * p.2 ^ (c / 2 - 1)) (Ioi 0 ×ˢ Ioi 0) :=
      (hf.cont.comp continuous_snd.continuousOn fun _ hp => hp.2.le).mul
        (ContinuousOn.rpow_const continuous_snd.continuousOn fun _ hp => Or.inl hp.2.ne')
    exact h1.mul h2
  have hF_int : Integrable F (μ.prod μ) := by
    refine (hG_int.const_mul C).mono' hF_aesm ?_
    rw [hprod]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hp2 : 0 < p.2 := hp.2
    dsimp [F, G]
    by_cases h12 : p.1 < p.2
    · simp only [h12, ↓reduceIte,
        abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hp1.le _), abs_of_nonneg (Real.rpow_nonneg hp2.le _)]
      rw [abs_of_nonneg (div_nonneg (Real.rpow_nonneg (by positivity) _) (Real.Gamma_pos_of_pos hc).le)]
      calc ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * |K.φ (Δ * p.1)| * (|f p.2| * p.2 ^ (c / 2 - 1))
          ≤ ((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * C * (|f p.2| * p.2 ^ (c / 2 - 1)) := by
            gcongr; exact hC (Δ * p.1) (mul_nonneg (mem_Ici.mp hΔ) hp1.le)
        _ = C * (((2 * π) ^ c / Real.Gamma c) * p.1 ^ (c / 2 - 1) * (|f p.2| * p.2 ^ (c / 2 - 1))) := by ring
    · simp only [h12, ↓reduceIte, abs_zero, mul_zero, le_refl]
  have hLHS : hankelTransform c K (intertwiner c f) Δ = ∫ t, ∫ s, F (t, s) ∂μ ∂μ := by
    unfold hankelTransform
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
    unfold intertwiner
    simp only [ht, ↓reduceIte]
    have hcoeff : t ^ (-(c / 2)) * hankelRho0 c t = ((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) := by
      unfold hankelRho0
      have : t ^ (-(c / 2)) * t ^ (c - 1) = t ^ (c / 2 - 1) := by
        rw [← Real.rpow_add ht]; congr 1; ring
      calc t ^ (-(c / 2)) * ((2 * π) ^ c / Real.Gamma c * t ^ (c - 1))
          = ((2 * π) ^ c / Real.Gamma c) * (t ^ (-(c / 2)) * t ^ (c - 1)) := by ring
        _ = ((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) := by rw [this]
    have hs_eq : Set.EqOn (fun s => F (t, s))
        ((Ioi t).indicator (fun s => (((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) * K.φ (Δ * t)) *
          (f s * s ^ (c / 2 - 1)))) (Ioi 0) := by
      intro s _
      dsimp [F]
      by_cases hts : t < s
      · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioi]
      · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioi]
    rw [show t ^ (-(c / 2)) * (∫ s in Ioi t, f s * s ^ (c / 2 - 1)) * hankelRho0 c t * K.φ (Δ * t) =
        (((2 * π) ^ c / Real.Gamma c) * t ^ (c / 2 - 1) * K.φ (Δ * t)) *
          ∫ s in Ioi t, f s * s ^ (c / 2 - 1) by rw [← hcoeff]; ring]
    rw [← integral_const_mul, ← Set.inter_eq_right.mpr (Ioi_subset_Ioi ht.le),
      ← setIntegral_indicator measurableSet_Ioi]
    exact (setIntegral_congr_fun measurableSet_Ioi hs_eq).symm
  rw [hLHS, integral_integral_swap hF_int]
  rcases eq_or_lt_of_le (mem_Ici.mp hΔ) with rfl | hΔpos
  · have hrhs : ∫ s, ∫ t, F (t, s) ∂μ ∂μ = (2 / c) * ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
      have ht_eq : Set.EqOn (fun t => F (t, s))
          ((Ioo (0 : ℝ) s).indicator
            (fun t => ((2 * π) ^ c / Real.Gamma c) * (f s * s ^ (c / 2 - 1)) * t ^ (c / 2 - 1))) (Ioi 0) := by
        intro t (ht : 0 < t)
        dsimp [F]
        by_cases hts : t < s
        · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioo, ht, and_self, zero_mul, K.φ_zero]; ring
        · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioo, and_false]
      rw [setIntegral_congr_fun measurableSet_Ioi ht_eq, setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.mpr Ioo_subset_Ioi_self, ← integral_Ioc_eq_integral_Ioo,
        integral_const_mul, ← intervalIntegral.integral_of_le hs.le,
        integral_rpow (Or.inl (by linarith : -1 < c / 2 - 1)),
        Real.zero_rpow (by linarith : c / 2 - 1 + 1 ≠ 0), sub_zero]
      unfold hankelRho0
      have : c / 2 - 1 + 1 = c / 2 := by ring
      rw [this]
      have hpow' : s ^ (c / 2 - 1) * s ^ (c / 2) = s ^ (c - 1) := by
        rw [← Real.rpow_add hs]; congr 1; ring
      calc ((2 * π) ^ c / Real.Gamma c) * (f s * s ^ (c / 2 - 1)) * (s ^ (c / 2) / (c / 2))
          = (2 / c) * (f s * ((2 * π) ^ c / Real.Gamma c * (s ^ (c / 2 - 1) * s ^ (c / 2)))) := by ring
        _ = (2 / c) * (f s * ((2 * π) ^ c / Real.Gamma c * s ^ (c - 1))) := by rw [hpow']
    have he0 : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = -f 0 := by
      have := hf.eigen 0 self_mem_Ici
      unfold hankelTransform at this
      simp_rw [zero_mul, K.φ_zero, mul_one, neg_one_mul] at this
      exact this
    rw [hrhs, he0, intertwiner_zero]; ring
  · have hrhs : ∫ s, ∫ t, F (t, s) ∂μ ∂μ =
        Δ ^ (-(c / 2)) * ∫ s in Ioi (0 : ℝ), f s * s ^ (c / 2 - 1) *
          (((2 * π) ^ c / Real.Gamma c) * ∫ w in Ioc (0 : ℝ) (Δ * s), w ^ (c / 2 - 1) * K.φ w) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
      have ht_eq : Set.EqOn (fun t => F (t, s))
          ((Ioo (0 : ℝ) s).indicator
            (fun t => ((2 * π) ^ c / Real.Gamma c) * (f s * s ^ (c / 2 - 1)) * (t ^ (c / 2 - 1) * K.φ (Δ * t))))
          (Ioi 0) := by
        intro t (ht : 0 < t)
        dsimp [F]
        by_cases hts : t < s
        · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioo, ht, and_self]; ring
        · simp only [hts, ↓reduceIte, Set.indicator_apply, Set.mem_Ioo, and_false]
      rw [setIntegral_congr_fun measurableSet_Ioi ht_eq, setIntegral_indicator measurableSet_Ioo,
        Set.inter_eq_right.mpr Ioo_subset_Ioi_self, ← integral_Ioc_eq_integral_Ioo,
        integral_const_mul]
      have hcov : ∫ t in Ioc (0 : ℝ) s, t ^ (c / 2 - 1) * K.φ (Δ * t) =
          Δ ^ (-(c / 2)) * ∫ w in Ioc (0 : ℝ) (Δ * s), w ^ (c / 2 - 1) * K.φ w := by
        have hcongr : ∫ t in Ioc (0 : ℝ) s, t ^ (c / 2 - 1) * K.φ (Δ * t) =
            ∫ t in Ioc (0 : ℝ) s, Δ ^ (1 - c / 2) * ((Δ * t) ^ (c / 2 - 1) * K.φ (Δ * t)) := by
          refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          have hr : Δ ^ (1 - c / 2) * (Δ * t) ^ (c / 2 - 1) = t ^ (c / 2 - 1) := by
            rw [Real.mul_rpow hΔpos.le ht.1.le, ← mul_assoc, ← Real.rpow_add hΔpos,
              show (1 - c / 2) + (c / 2 - 1) = 0 by ring, Real.rpow_zero, one_mul]
          calc t ^ (c / 2 - 1) * K.φ (Δ * t)
              = (Δ ^ (1 - c / 2) * (Δ * t) ^ (c / 2 - 1)) * K.φ (Δ * t) := by rw [hr]
            _ = Δ ^ (1 - c / 2) * ((Δ * t) ^ (c / 2 - 1) * K.φ (Δ * t)) := by ring
        rw [hcongr, ← intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_mul_left (f := fun w => w ^ (c / 2 - 1) * K.φ w) hΔpos.ne',
          mul_zero, intervalIntegral.integral_of_le (mul_pos hΔpos hs).le, smul_eq_mul]
        have hexp : Δ ^ (1 - c / 2) * Δ⁻¹ = Δ ^ (-(c / 2)) := by
          rw [← Real.rpow_neg_one Δ, ← Real.rpow_add hΔpos]; congr 1; ring
        rw [← mul_assoc, hexp]
      rw [hcov]; ring
    rw [hrhs, ← intertwiner_fubini_identity hc hf hΔpos, intertwiner_eq_neg_left hc hf hΔpos]; ring

/-- Proposition 7.9a(3): `ℐ_c` maps any `(-1)`-feasible eigenfunction at threshold `T` to a
`(+1)`-feasible eigenfunction at the same threshold `T`. -/
theorem intertwiner_feasible {c : ℝ} (hc : 0 < c) {K : HankelKernelData c} {T : ℝ} {f : ℝ → ℝ}
    (hf : IsFeasible c K (-1) T f) :
    IsFeasible c K 1 T (intertwiner c f) := by
  refine ⟨intertwiner_eigen hc hf.eigenfn, ?_, ?_, ?_⟩
  · by_contra hzero
    push Not at hzero
    obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero
    exact hne (intertwiner_injective hc hf.eigenfn hzero Δ hΔ)
  · rw [intertwiner_zero]
    have hf0 : 0 ≤ f 0 := by linarith [hf.origin_sign]
    have h2c : 0 ≤ 2 / c := by positivity
    nlinarith
  · have hTpos : 0 < T := feasible_threshold_pos hc hf
    intro Δ hΔ
    have hΔpos : 0 < Δ := lt_of_lt_of_le hTpos hΔ
    unfold intertwiner
    simp only [hΔpos, ↓reduceIte]
    refine mul_nonneg (Real.rpow_nonneg hΔpos.le _) (setIntegral_nonneg measurableSet_Ioi fun s hs => ?_)
    have hsT : T ≤ s := hΔ.trans (le_of_lt hs)
    exact mul_nonneg (hf.tail_nonneg s hsT) (Real.rpow_nonneg (hΔpos.trans hs).le _)

/-- Proposition 7.9a(3), threshold inequality: `T_c^{+1} ≤ T_c^{-1}` whenever `𝒜_c^{-1}` has at least
one feasible eigenfunction. -/
theorem threshold_pos_le_neg {c : ℝ} (hc : 0 < c) {K : HankelKernelData c}
    (hnonempty : ∃ T f, IsFeasible c K (-1) T f) :
    hankelThreshold c K 1 ≤ hankelThreshold c K (-1) := by
  obtain ⟨T₀, f₀, hf₀⟩ := hnonempty
  have hS_ne : { T : ℝ | ∃ f, IsFeasible c K (-1) T f }.Nonempty := ⟨T₀, f₀, hf₀⟩
  have hS_bdd : BddBelow { T : ℝ | ∃ f, IsFeasible c K 1 T f } :=
    ⟨0, fun T ⟨_, hf⟩ => (feasible_threshold_pos hc hf).le⟩
  refine le_csInf hS_ne fun T ⟨f, hf⟩ => ?_
  exact csInf_le hS_bdd ⟨intertwiner c f, intertwiner_feasible hc hf⟩

/-- Proposition 7.9a(3), integer-dimensional Fourier sign-uncertainty radius inequality:
`A_+(d) ≤ A_-(d)` for every integer `d ≥ 4` (with `c = d / 2` and `A_ε(d) = √(2 T_{d/2}^ε)`). -/
theorem fourier_radii_pos_le_neg {d : ℕ} (hd : 4 ≤ d) {K : HankelKernelData ((d : ℝ) / 2)}
    (hnonempty : ∃ T f, IsFeasible ((d : ℝ) / 2) K (-1) T f) :
    Real.sqrt (2 * hankelThreshold ((d : ℝ) / 2) K 1) ≤
      Real.sqrt (2 * hankelThreshold ((d : ℝ) / 2) K (-1)) := by
  have hc : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (4 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (threshold_pos_le_neg hc hnonempty) (by norm_num))


end FormalResearch.SignUncertainty

/-! ### Axiom Checks (`#guard_msgs`) -/

/-- info: 'FormalResearch.SignUncertainty.intertwiner_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_integrable

/-- info: 'FormalResearch.SignUncertainty.intertwiner_integral_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_integral_zero

/-- info: 'FormalResearch.SignUncertainty.intertwiner_eq_neg_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_eq_neg_left

/-- info: 'FormalResearch.SignUncertainty.intertwiner_continuousOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_continuousOn

/-- info: 'FormalResearch.SignUncertainty.hankelMass_intertwiner_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.hankelMass_intertwiner_le

/-- info: 'FormalResearch.SignUncertainty.intertwiner_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_injective

/-- info: 'FormalResearch.SignUncertainty.intertwiner_eigen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_eigen

/-- info: 'FormalResearch.SignUncertainty.intertwiner_feasible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.intertwiner_feasible

/-- info: 'FormalResearch.SignUncertainty.threshold_pos_le_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.threshold_pos_le_neg

/-- info: 'FormalResearch.SignUncertainty.fourier_radii_pos_le_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.fourier_radii_pos_le_neg

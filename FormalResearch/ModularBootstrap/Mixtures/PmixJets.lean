module

public import FormalResearch.ModularBootstrap.Mixtures.JetsG3

/-!
# Product amplitudes, `CommonSource` boundary problem, and unconditional `pmix:jensen` (`ctu:g13`, `pmix:jets`)

Formalizes:
* `jetAmplitude_nullAmp` and product additivity `I1Amp_nullAmp`, `I3Amp_nullAmp` (`ctu:g13`, `ctu:jets` (b));
* `jMinWA`, `c0StarOf`, and `pmix_jets_common` collecting `ctu:jets`, `ctu:common-functional`, `ctu:qy`,
  and `ctu:J-quad` for every `CommonSource` (`pmix:jets`);
* `integral_xChart_sub_div_sq` (`∫₀^∞ (x(t) - ξ_*)/t² dt = ξ_*/√2`), discharging the integrability
  hypotheses of `MixtureData.pmix_jensen` unconditionally (`pmix_jensen_full`, `pmix:jensen`).
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm
open FormalResearch.ModularBootstrap.Crossing

namespace FormalResearch.ModularBootstrap.Mixtures

/-! ### 1. Elementary product factors `1 - e^{-4πμx}` and `FixedWeightProblem.nullPoly` -/

lemma jetAmplitude_one_sub_exp {μ : ℝ} (hμ : 0 < μ) :
    JetAmplitude (fun x => 1 - Real.exp (-4 * π * μ * x)) := by
  have hpi := Real.pi_pos
  have hxi := xiStar_pos
  refine ⟨fun x _ => analyticAt_const.sub ((analyticAt_const.mul analyticAt_id).rexp),
    ⟨1 - Real.exp (-4 * π * μ * xiStar), ?_, fun x hx => ?_⟩,
    ⟨1, fun x _ => sub_le_self _ (Real.exp_pos _).le⟩,
    ⟨4 * π * μ, fun x hx => ?_⟩⟩
  · rw [sub_pos, Real.exp_lt_one_iff]
    nlinarith [mul_pos hpi hμ]
  · simp only [sub_le_sub_iff_left, Real.exp_le_exp]
    nlinarith [mul_pos hpi hμ]
  · have hd : HasDerivAt (fun t => 1 - Real.exp (-4 * π * μ * t))
        (4 * π * μ * Real.exp (-4 * π * μ * x)) x := by
      have h1 : HasDerivAt (fun t : ℝ => -4 * π * μ * t) (-4 * π * μ) x := by
        simpa using (hasDerivAt_id x).const_mul (-4 * π * μ)
      exact (h1.exp.const_sub 1).congr_deriv (by ring)
    rw [hd.deriv, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
    have hexp_le : Real.exp (-4 * π * μ * x) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hpi hμ])
    nlinarith [mul_pos hpi hμ]

/-- The product amplitude `x ↦ Q(e^{-4πx})` attached to a `FixedWeightProblem`. -/
noncomputable def nullAmp (prob : FixedWeightProblem) (x : ℝ) : ℝ :=
  prob.nullPoly (Real.exp (-4 * π * x))

lemma nullAmp_eq_prod (prob : FixedWeightProblem) (x : ℝ) :
    nullAmp prob x = ∏ l : Fin prob.m, (1 - Real.exp (-4 * π * prob.μ l * x)) := by
  unfold nullAmp FixedWeightProblem.nullPoly
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [← Real.exp_mul]
  congr 2; ring

private lemma jetAmplitude_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ l ∈ s, JetAmplitude (f l)) :
    JetAmplitude (fun x => ∏ l ∈ s, f l x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using jetAmplitude_one
  | insert a s ha ih =>
      have ha' : JetAmplitude (f a) := hf a (Finset.mem_insert_self a s)
      have hs' : JetAmplitude (fun x => ∏ l ∈ s, f l x) :=
        ih fun l hl => hf l (Finset.mem_insert_of_mem hl)
      simpa [Finset.prod_insert ha] using ha'.mul hs'

/-- Every fixed-weight product amplitude `Q(e^{-4πx})` satisfies `JetAmplitude` (`ctu:jets`). -/
theorem jetAmplitude_nullAmp (prob : FixedWeightProblem) : JetAmplitude (nullAmp prob) := by
  have heq : nullAmp prob = fun x => ∏ l : Fin prob.m, (1 - Real.exp (-4 * π * prob.μ l * x)) :=
    funext (nullAmp_eq_prod prob)
  rw [heq]
  exact jetAmplitude_finset_prod Finset.univ _ fun l _ => jetAmplitude_one_sub_exp (prob.hμ l)

private lemma I1Amp_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ l ∈ s, JetAmplitude (f l)) :
    I1Amp (fun x => ∏ l ∈ s, f l x) = ∑ l ∈ s, I1Amp (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [I1Amp_one]
  | insert a s ha ih =>
      have ha' : JetAmplitude (f a) := hf a (Finset.mem_insert_self a s)
      have hs' : JetAmplitude (fun x => ∏ l ∈ s, f l x) :=
        jetAmplitude_finset_prod s f fun l hl => hf l (Finset.mem_insert_of_mem hl)
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [I1Amp_mul ha' hs', ih fun l hl => hf l (Finset.mem_insert_of_mem hl)]

private lemma I3Amp_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ l ∈ s, JetAmplitude (f l)) :
    I3Amp (fun x => ∏ l ∈ s, f l x) = ∑ l ∈ s, I3Amp (f l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [I3Amp_one]
  | insert a s ha ih =>
      have ha' : JetAmplitude (f a) := hf a (Finset.mem_insert_self a s)
      have hs' : JetAmplitude (fun x => ∏ l ∈ s, f l x) :=
        jetAmplitude_finset_prod s f fun l hl => hf l (Finset.mem_insert_of_mem hl)
      simp only [Finset.prod_insert ha, Finset.sum_insert ha]
      rw [I3Amp_mul ha' hs', ih fun l hl => hf l (Finset.mem_insert_of_mem hl)]

/-- Product additivity for `I₁(Q)` (`ctu:g13`, `ctu:jets` (b)). -/
theorem I1Amp_nullAmp (prob : FixedWeightProblem) :
    I1Amp (nullAmp prob) = ∑ l : Fin prob.m, I1Amp (fun x => 1 - Real.exp (-4 * π * prob.μ l * x)) := by
  have heq : nullAmp prob = fun x => ∏ l : Fin prob.m, (1 - Real.exp (-4 * π * prob.μ l * x)) :=
    funext (nullAmp_eq_prod prob)
  rw [heq]
  exact I1Amp_finset_prod Finset.univ _ fun l _ => jetAmplitude_one_sub_exp (prob.hμ l)

/-- Product additivity for `I₃(Q)` (`ctu:g13`, `ctu:jets` (b)). -/
theorem I3Amp_nullAmp (prob : FixedWeightProblem) :
    I3Amp (nullAmp prob) = ∑ l : Fin prob.m, I3Amp (fun x => 1 - Real.exp (-4 * π * prob.μ l * x)) := by
  have heq : nullAmp prob = fun x => ∏ l : Fin prob.m, (1 - Real.exp (-4 * π * prob.μ l * x)) :=
    funext (nullAmp_eq_prod prob)
  rw [heq]
  exact I3Amp_finset_prod Finset.univ _ fun l _ => jetAmplitude_one_sub_exp (prob.hμ l)

/-! ### 2. `pmix:jets` common-source boundary minimum and jets -/

/-- Exact minimum `j(w, A) := α_tip g₁(w, A)` of the conjugated boundary functional `𝒥_{w,A}`
(`pmix:jets`, `ctu:common-functional`). -/
noncomputable def jMinWA (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) : ℝ :=
  alphaTip * g1OutWA w hw hA

/-- Product constant `c₀^*(w, Q) := j(w, Q)` for a product amplitude `Q` (`ctu:common-functional`,
`pmix:jets`). -/
noncomputable def c0StarOf (w : ℕ) (hw : 1 ≤ w) (prob : FixedWeightProblem) : ℝ :=
  jMinWA w hw (jetAmplitude_nullAmp prob)

lemma jMinWA_eq (w : ℕ) (hw : 1 ≤ w) {A : ℝ → ℝ} (hA : JetAmplitude A) :
    jMinWA w hw hA = alphaTip * (2 * (w : ℝ) - 3 - 2 / π) + (8 * alphaTip / π) * I1Amp A := by
  unfold jMinWA
  rw [g1OutWA_eq hw hA]
  ring

/-- **`pmix:jets` (first half, Proposition PM.13)** for any `CommonSource` with `w ≥ 1`:
the exact boundary minimum of `𝒥_{w,A}` equals `j(w, A) = α_tip g₁(w, A)` (`ctu:g13A`),
and `ctu:common-functional` (defect identity, minimum, equality criterion, regularisation estimate)
and `g₃(w, A)` all hold for `A = C.src.ampl` (regularisation: the `ctu:J-quad` bound only; the two-sided `D_ε` estimates
and smoothness at `z = 1` are not formalised). -/
theorem pmix_jets_common (C : CommonSource) (hw : 1 ≤ C.src.w) :
    let hA := (pmix_jets_hyp C).1
    IsLeast
        {x : ℝ | ∃ (F : ℂ → ℂ) (c1 : ℝ),
          HAdm F c1 ∧ combJ (WslitWA C.src.w C.src.ampl) (KedgeW C.src.w) F = x}
        (jMinWA C.src.w hw hA) ∧
      g1OutWA C.src.w hw hA = 2 * (C.src.w : ℝ) - 3 - 2 / π + 8 * I1Amp C.src.ampl / π ∧
      g3OutWA C.src.w hw hA =
        (7 / 3) * (2 * (C.src.w : ℝ) - 3) - 10 / (9 * π) -
          24 * I1Amp C.src.ampl / π - 128 * I3Amp C.src.ampl / (3 * π) ∧
      (∀ (ε : ℝ), 0 < ε → ε < 1 →
        HAdm (fun z => mEps ε z * fStar (GoutWA C.src.w C.src.ampl) z)
          (-g1OutWA C.src.w hw hA - ε / 2) ∧
        jMinWA C.src.w hw hA ≤
          combJ (WslitWA C.src.w C.src.ampl) (KedgeW C.src.w)
            (fun z => mEps ε z * fStar (GoutWA C.src.w C.src.ampl) z) ∧
        combJ (WslitWA C.src.w C.src.ampl) (KedgeW C.src.w)
            (fun z => mEps ε z * fStar (GoutWA C.src.w C.src.ampl) z) ≤
          jMinWA C.src.w hw hA + 25 * alphaC * ε ^ 2) := by
  intro hA
  exact ⟨comb_minimum_WA C.src.w hw hA, g1OutWA_eq hw hA, g3OutWA_eq hw hA,
    fun ε hε0 hε1 => comb_regularisation_WA C.src.w hw hA hε0 hε1⟩

/-! ### 3. Shift integral `∫₀^∞ (x(t) - ξ_*)/t² dt = ξ_*/√2` and unconditional `pmix:jensen` -/

private lemma xChart_sub_sq_bound :
    ∀ t : ℝ, 0 ≤ t → 0 ≤ xChart t - xiStar ∧ xChart t - xiStar ≤ 1 / (4 * π) * t ^ 2 := by
  have hpi := Real.pi_pos
  intro t ht
  have hd : ∀ s : ℝ, 0 ≤ s → 0 ≤ deriv xChart s ∧ deriv xChart s ≤ s / (2 * π) := fun s hs => by
    have hxd := xChart_hasDerivAt s
    have hq1 : 1 ≤ qChart s := one_le_qChart s
    have hqpos : 0 < qChart s := qChart_pos s
    have hsq1 : 1 ≤ Real.sqrt (qChart s) := Real.one_le_sqrt.mpr hq1
    have hsq2 : 1 ≤ Real.sqrt (1 + qChart s) := Real.one_le_sqrt.mpr (by linarith)
    have hden_ge : 2 * π ≤ 2 * π * (qChart s * Real.sqrt (qChart s)) * Real.sqrt (1 + qChart s) := by
      have hprod : 1 ≤ qChart s * Real.sqrt (qChart s) * Real.sqrt (1 + qChart s) :=
        one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq1 hsq1) hsq2
      nlinarith
    rw [hxd.deriv]
    refine ⟨div_nonneg hs (by positivity), ?_⟩
    exact div_le_div_of_nonneg_left hs (by positivity) hden_ge
  have hcont_d : Continuous (fun s => deriv xChart s) := by
    have heq : (fun s => deriv xChart s) = fun s =>
        s / (2 * π * (qChart s * Real.sqrt (qChart s)) * Real.sqrt (1 + qChart s)) :=
      funext fun s => (xChart_hasDerivAt s).deriv
    rw [heq]
    have hqc : Continuous qChart := (by fun_prop : Continuous fun s : ℝ => 1 + s ^ 2).sqrt
    refine Continuous.div continuous_id ?_ fun s => by have := qChart_pos s; positivity
    exact (continuous_const.mul (hqc.mul hqc.sqrt)).mul (continuous_const.add hqc).sqrt
  have hid : xChart t - xiStar = ∫ s in (0 : ℝ)..t, deriv xChart s := by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => (xChart_hasDerivAt s).deriv ▸ xChart_hasDerivAt s)
      (hcont_d.intervalIntegrable 0 t)
    rw [xChart_zero] at hftc
    exact hftc.symm
  rw [hid]
  refine ⟨intervalIntegral.integral_nonneg ht fun s hs => (hd s hs.1).1, ?_⟩
  have hmono : ∫ s in (0 : ℝ)..t, deriv xChart s ≤ ∫ s in (0 : ℝ)..t, s / (2 * π) :=
    intervalIntegral.integral_mono_on ht (hcont_d.intervalIntegrable 0 t)
      ((continuous_id.div_const (2 * π)).intervalIntegrable 0 t) fun s hs => (hd s hs.1).2
  have hpow : ∫ s in (0 : ℝ)..t, s / (2 * π) = 1 / (4 * π) * t ^ 2 := by
    simp only [div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_id]
    ring
  linarith

private lemma xChart_le_rpow {t : ℝ} (ht : 1 ≤ t) :
    xChart t ≤ (2 * √2 / π) * t ^ (1 / 2 : ℝ) := by
  have hpi := Real.pi_pos
  have hq : qChart t ≤ 2 * t := by
    unfold qChart
    refine Real.sqrt_le_iff.mpr ⟨by linarith, ?_⟩
    nlinarith
  have hrsq : Real.sqrt (qChart t) ≤ √2 * t ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt hq
  have hars : ∀ u : ℝ, 0 ≤ u → Real.arsinh u ≤ 2 * u := fun u hu => by
    rw [Real.arsinh]
    have hsq : √(1 + u ^ 2) ≤ 1 + u := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hlog : Real.log (u + √(1 + u ^ 2)) ≤ Real.log (1 + 2 * u) :=
      Real.log_le_log (by positivity) (by linarith)
    have h1 := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + 2 * u)
    linarith
  unfold xChart
  rw [div_le_iff₀ hpi]
  calc Real.arsinh (Real.sqrt (qChart t))
      ≤ 2 * Real.sqrt (qChart t) := hars _ (Real.sqrt_nonneg _)
    _ ≤ 2 * (√2 * t ^ (1 / 2 : ℝ)) := by gcongr
    _ = 2 * √2 / π * t ^ (1 / 2 : ℝ) * π := by field_simp

/-- `(x(t) - ξ_*) / t²` is integrable on `(0, ∞)`. -/
lemma integrableOn_xChart_sub_div_sq :
    IntegrableOn (fun t : ℝ => (xChart t - xiStar) / t ^ 2) (Ioi 0) := by
  have hpi := Real.pi_pos
  have hcont : ContinuousOn (fun t : ℝ => (xChart t - xiStar) / t ^ 2) (Ioi 0) :=
    (continuous_xChart.sub continuous_const).continuousOn.div (continuous_id.pow 2).continuousOn
      fun t ht => pow_ne_zero 2 (ne_of_gt ht)
  have h1 : IntegrableOn (fun t : ℝ => (xChart t - xiStar) / t ^ 2) (Ioo 0 1) := by
    refine Integrable.mono' (integrableOn_const (hs := measure_Ioo_lt_top.ne) (C := 1 / (4 * π)))
      ((hcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
    refine (ae_restrict_iff' measurableSet_Ioo).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    obtain ⟨hnn, hup⟩ := xChart_sub_sq_bound t ht0.le
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnn, abs_of_pos (pow_pos ht0 2),
      div_le_iff₀ (pow_pos ht0 2)]
    linarith
  have h2 : IntegrableOn (fun t : ℝ => (xChart t - xiStar) / t ^ 2) (Ioi 1) := by
    have hinv : IntegrableOn (fun t : ℝ => (2 * √2 / π) * t ^ (-3 / 2 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) one_pos).const_mul _
    refine Integrable.mono' hinv
      ((hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hnn := (xChart_sub_sq_bound t ht0.le).1
    have hle : xChart t - xiStar ≤ (2 * √2 / π) * t ^ (1 / 2 : ℝ) := by
      linarith [xChart_le_rpow ht1.le, xiStar_pos]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnn, abs_of_pos (pow_pos ht0 2),
      div_le_iff₀ (pow_pos ht0 2)]
    have hrp : t ^ (-3 / 2 : ℝ) * t ^ 2 = t ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]
      norm_num
    rw [mul_assoc, hrp]
    exact hle
  have hu : Ioi (0 : ℝ) = Ioo 0 1 ∪ ({1} ∪ Ioi 1) := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioo, mem_singleton_iff]; constructor <;> intro h
    · rcases lt_trichotomy x 1 with h1 | rfl | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h1)
    · rcases h with h | rfl | h <;> linarith
  have hsing : IntegrableOn (fun t : ℝ => (xChart t - xiStar) / t ^ 2) {1} volume :=
    integrableOn_singleton (hx := isCompact_singleton.measure_lt_top)
  rw [hu]
  exact h1.union (hsing.union h2)

/-- Integration by parts of `shift_integral`:
`∫₀^∞ (x(t) - ξ_*) / t² dt = ξ_* / √2` (`pmix:jets` / `pmix:jensen`). -/
theorem integral_xChart_sub_div_sq :
    ∫ t in Ioi (0 : ℝ), (xChart t - xiStar) / t ^ 2 = xiStar / √2 := by
  have hpi := Real.pi_pos
  have hu : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun s => xChart s - xiStar) (t * shiftDensity t) t :=
    fun t _ => by
      have h := (xChart_hasDerivAt t).sub_const xiStar
      refine h.congr_deriv ?_
      unfold shiftDensity; ring
  have hv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun s : ℝ => -s⁻¹) (t ^ 2)⁻¹ t := fun t ht =>
    (hasDerivAt_inv (ne_of_gt ht)).neg.congr_deriv (by ring)
  have huv' : IntegrableOn ((fun s => xChart s - xiStar) * fun s : ℝ => (s ^ 2)⁻¹) (Ioi 0) :=
    integrableOn_xChart_sub_div_sq.congr_fun
      (fun t _ => by simp [div_eq_mul_inv]) measurableSet_Ioi
  have hu'v : IntegrableOn ((fun s => s * shiftDensity s) * fun s : ℝ => -s⁻¹) (Ioi 0) := by
    have hcont_s : ContinuousWithinAt shiftPrim (Ici 0) 0 :=
      (shiftPrim_hasDerivAt 0).continuousAt.continuousWithinAt
    have hint_s : IntegrableOn shiftDensity (Ioi 0) :=
      integrableOn_Ioi_deriv_of_nonneg hcont_s (fun t _ => shiftPrim_hasDerivAt t)
        (fun t _ => shiftDensity_nonneg t) tendsto_shiftPrim
    refine hint_s.neg.congr_fun ?_ measurableSet_Ioi
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    show -shiftDensity t = t * shiftDensity t * -t⁻¹
    field_simp
  have h0 : Tendsto ((fun s => xChart s - xiStar) * fun s : ℝ => -s⁻¹) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun t : ℝ => 1 / (4 * π) * t) (𝓝[>] 0) (𝓝 0) by
      have : Tendsto (fun t : ℝ => 1 / (4 * π) * t) (𝓝 0) (𝓝 (1 / (4 * π) * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    obtain ⟨hnn, hup⟩ := xChart_sub_sq_bound t ht0.le
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos ht0,
      abs_of_nonneg hnn]
    calc (xChart t - xiStar) * t⁻¹ ≤ (1 / (4 * π) * t ^ 2) * t⁻¹ :=
          mul_le_mul_of_nonneg_right hup (inv_nonneg.mpr ht0.le)
      _ = 1 / (4 * π) * t := by field_simp
  have hinf : Tendsto ((fun s => xChart s - xiStar) * fun s : ℝ => -s⁻¹) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (show Tendsto (fun t : ℝ => (2 * √2 / π) * t ^ (-1 / 2 : ℝ))
        atTop (𝓝 0) by
      simpa only [mul_zero, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) from by ring] using
        (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (2 * √2 / π))
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht1
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
    have hnn := (xChart_sub_sq_bound t ht0.le).1
    have hle : xChart t - xiStar ≤ (2 * √2 / π) * t ^ (1 / 2 : ℝ) := by
      linarith [xChart_le_rpow ht1, xiStar_pos]
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul, abs_neg, abs_inv, abs_of_pos ht0,
      abs_of_nonneg hnn]
    have hrp : t ^ (1 / 2 : ℝ) * t⁻¹ = t ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht0]
      norm_num
    calc (xChart t - xiStar) * t⁻¹ ≤ ((2 * √2 / π) * t ^ (1 / 2 : ℝ)) * t⁻¹ :=
          mul_le_mul_of_nonneg_right hle (inv_nonneg.mpr ht0.le)
      _ = 2 * √2 / π * t ^ (-1 / 2 : ℝ) := by rw [mul_assoc, hrp]
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v h0 hinf
  simp only [sub_zero, zero_sub] at hibp
  have heq1 : ∫ t in Ioi (0 : ℝ), (xChart t - xiStar) / t ^ 2 =
      ∫ t in Ioi (0 : ℝ), (xChart t - xiStar) * (t ^ 2)⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by simp [div_eq_mul_inv]
  have heq2 : ∫ t in Ioi (0 : ℝ), t * shiftDensity t * -t⁻¹ = -(xiStar / √2) := by
    rw [← shift_integral, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : t ≠ 0 := ne_of_gt ht
    field_simp
  rw [heq1, hibp, heq2, neg_neg]

namespace MixtureData

lemma logAmp_comp_eq (M : MixtureData) (i : Fin M.s) (t : ℝ) :
    logAmp (M.compAmp i) t =
      -4 * π * M.r i * (xChart t - xiStar) + logAmp (nullAmp (M.Q i)) t := by
  have hx := xiStar_pos.trans_le (xiStar_le_xChart t)
  have hQ0 : 0 < nullAmp (M.Q i) xiStar :=
    (M.Q i).nullPoly_pos (Real.exp_pos (-4 * π * xiStar)).le
      (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, xiStar_pos]))
  have hQt : 0 < nullAmp (M.Q i) (xChart t) :=
    (M.Q i).nullPoly_pos (Real.exp_pos (-4 * π * xChart t)).le
      (Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos]))
  unfold nullAmp at hQ0 hQt
  unfold logAmp compAmp nullAmp
  have hsplit : Real.exp (-4 * π * M.r i * xChart t) *
        (M.Q i).nullPoly (Real.exp (-4 * π * xChart t)) /
        (Real.exp (-4 * π * M.r i * xiStar) * (M.Q i).nullPoly (Real.exp (-4 * π * xiStar))) =
      Real.exp (-4 * π * M.r i * (xChart t - xiStar)) *
        ((M.Q i).nullPoly (Real.exp (-4 * π * xChart t)) /
          (M.Q i).nullPoly (Real.exp (-4 * π * xiStar))) := by
    rw [mul_sub, Real.exp_sub]
    ring
  rw [hsplit, Real.log_mul (Real.exp_pos _).ne' (div_pos hQt hQ0).ne', Real.log_exp]

lemma integrableOn_logAmp_comp (M : MixtureData) (i : Fin M.s) :
    IntegrableOn (fun t => logAmp (M.compAmp i) t / t ^ 2) (Ioi 0) := by
  have h1 : IntegrableOn (fun t => (-4 * π * M.r i) * ((xChart t - xiStar) / t ^ 2)) (Ioi 0) :=
    integrableOn_xChart_sub_div_sq.const_mul (-4 * π * M.r i)
  have h2 : IntegrableOn (fun t => logAmp (nullAmp (M.Q i)) t / t ^ 2) (Ioi 0) :=
    integrableOn_logAmp_div_sq (jetAmplitude_nullAmp (M.Q i))
  refine (h1.add h2).congr_fun ?_ measurableSet_Ioi
  intro t _
  simp only [Pi.add_apply]
  rw [M.logAmp_comp_eq i t]
  ring

lemma integral_logAmp_comp (M : MixtureData) (i : Fin M.s) :
    ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 =
      -4 * π * M.r i * (xiStar / √2) + I1Amp (nullAmp (M.Q i)) := by
  have h1 : IntegrableOn (fun t => (-4 * π * M.r i) * ((xChart t - xiStar) / t ^ 2)) (Ioi 0) :=
    integrableOn_xChart_sub_div_sq.const_mul _
  have h2 : IntegrableOn (fun t => logAmp (nullAmp (M.Q i)) t / t ^ 2) (Ioi 0) :=
    integrableOn_logAmp_div_sq (jetAmplitude_nullAmp (M.Q i))
  have hcon : ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 =
      ∫ t in Ioi (0 : ℝ), ((-4 * π * M.r i) * ((xChart t - xiStar) / t ^ 2) +
        logAmp (nullAmp (M.Q i)) t / t ^ 2) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [M.logAmp_comp_eq i t]; ring
  rw [hcon, integral_add h1 h2, integral_const_mul, integral_xChart_sub_div_sq,
    integral_logAmp_div_sq_eq_I1Amp (jetAmplitude_nullAmp (M.Q i))]

/-- **Unconditional Jensen comparison for boundary minima (`pmix:jets`, eq. `pmix:jensen`)**:
for any rebased positive mixture `M` (`∃ i₀, M.r i₀ = 0`) and any weight `w ≥ 1`,
`∑ i, p_i [c₀^*(w, Q_i) - 12 ξ̄ r_i] ≤ j(w, A)` (where `ξ̄ = ξ_*² / 3`), with equality
if and only if all normalized component amplitudes `A_i(x) / A_i(ξ_*)` coincide on `[ξ_*, ∞)`. -/
theorem pmix_jensen_full (M : MixtureData) {i₀ : Fin M.s} (hi₀ : M.r i₀ = 0)
    {w : ℕ} (hw : 1 ≤ w) :
    let hA := (pmix_jets_hyp (M.commonSource hi₀)).1
    ∑ i, M.jensenWeight i * (c0StarOf w hw (M.Q i) - 12 * (xiStar ^ 2 / 3) * M.r i) ≤
        jMinWA w hw hA ∧
      jMinWA w hw hA -
          ∑ i, M.jensenWeight i * (c0StarOf w hw (M.Q i) - 12 * (xiStar ^ 2 / 3) * M.r i) =
        (8 * alphaTip / π) *
          ∫ t in Ioi (0 : ℝ),
            ∑ i, M.jensenWeight i * Real.log (M.jensenWeight i /
              (M.d i * M.compAmp i (xChart t) / M.toSource.ampl (xChart t))) / t ^ 2 ∧
      (∑ i, M.jensenWeight i * (c0StarOf w hw (M.Q i) - 12 * (xiStar ^ 2 / 3) * M.r i) =
          jMinWA w hw hA ↔
        ∀ i j, ∀ x : ℝ, xiStar ≤ x →
          M.compAmp i x / M.compAmp i xiStar = M.compAmp j x / M.compAmp j xiStar) := by
  intro hA
  have hpi := Real.pi_pos
  have hA_eq : M.toSource.ampl = (M.commonSource hi₀).src.ampl := rfl
  have hint : ∀ i, IntegrableOn (fun t => logAmp (M.compAmp i) t / t ^ 2) (Ioi 0) :=
    M.integrableOn_logAmp_comp
  have hintA : IntegrableOn (fun t => logAmp M.toSource.ampl t / t ^ 2) (Ioi 0) :=
    integrableOn_logAmp_div_sq hA
  obtain ⟨hle, hiff⟩ := M.pmix_jensen hint hintA
  have hpos_coeff : 0 < 8 * alphaTip / π := by unfold alphaTip; have := xiStar_pos; positivity
  have hR : jMinWA w hw hA =
      alphaTip * (2 * (w : ℝ) - 3 - 2 / π) +
        (8 * alphaTip / π) * ∫ t in Ioi (0 : ℝ), logAmp M.toSource.ampl t / t ^ 2 := by
    rw [jMinWA_eq w hw hA, ← integral_logAmp_div_sq_eq_I1Amp hA, hA_eq]
  have hL : ∑ i, M.jensenWeight i * (c0StarOf w hw (M.Q i) - 12 * (xiStar ^ 2 / 3) * M.r i) =
      alphaTip * (2 * (w : ℝ) - 3 - 2 / π) +
        (8 * alphaTip / π) * ∑ i, M.jensenWeight i *
          ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 := by
    have hcomp_term : ∀ i, c0StarOf w hw (M.Q i) - 12 * (xiStar ^ 2 / 3) * M.r i =
        alphaTip * (2 * (w : ℝ) - 3 - 2 / π) +
          (8 * alphaTip / π) * ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 := fun i => by
      unfold c0StarOf
      rw [jMinWA_eq w hw (jetAmplitude_nullAmp (M.Q i)), M.integral_logAmp_comp i]
      have ha : alphaTip = xiStar / (4 * √2) := rfl
      have hconst : 12 * (xiStar ^ 2 / 3) * M.r i =
          (8 * alphaTip / π) * (4 * π * M.r i * (xiStar / √2)) := by
        rw [ha]
        field_simp
        rw [Real.sq_sqrt (by norm_num)]
        ring
      linarith [hconst]
    simp_rw [hcomp_term, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.sum_jensenWeight,
      one_mul]
    simp_rw [mul_left_comm (M.jensenWeight _) (8 * alphaTip / π), ← Finset.mul_sum]
  have hdiff : jMinWA w hw hA -
      ∑ i, M.jensenWeight i * (c0StarOf w hw (M.Q i) - 12 * (xiStar ^ 2 / 3) * M.r i) =
      (8 * alphaTip / π) *
        ((∫ t in Ioi (0 : ℝ), logAmp M.toSource.ampl t / t ^ 2) -
          ∑ i, M.jensenWeight i * ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2) := by
    rw [hR, hL]; ring
  have hkl : (∫ t in Ioi (0 : ℝ), logAmp M.toSource.ampl t / t ^ 2) -
        ∑ i, M.jensenWeight i * ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 =
      ∫ t in Ioi (0 : ℝ),
        ∑ i, M.jensenWeight i * Real.log (M.jensenWeight i /
          (M.d i * M.compAmp i (xChart t) / M.toSource.ampl (xChart t))) / t ^ 2 := by
    have hsum_int : ∑ i, M.jensenWeight i * ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 =
        ∫ t in Ioi (0 : ℝ), ∑ i, M.jensenWeight i * (logAmp (M.compAmp i) t / t ^ 2) := by
      simp_rw [← integral_const_mul]
      rw [← integral_finsetSum _ fun i _ => (hint i).const_mul (M.jensenWeight i)]
    have hs_eq : (fun t => ∑ i, M.jensenWeight i * (logAmp (M.compAmp i) t / t ^ 2)) =
        fun t => (∑ i, M.jensenWeight i * logAmp (M.compAmp i) t) / t ^ 2 := by
      ext t; simp [Finset.sum_div, mul_div_assoc]
    have hint_sum : IntegrableOn
        (fun t => (∑ i, M.jensenWeight i * logAmp (M.compAmp i) t) / t ^ 2) (Ioi 0) := by
      rw [← hs_eq]
      exact integrable_finsetSum _ fun i _ => (hint i).const_mul _
    rw [hsum_int, hs_eq, ← integral_sub hintA hint_sum]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    have hAt_pos : 0 < M.toSource.ampl (xChart t) := by
      rw [M.ampl_eq_sum]
      exact Finset.sum_pos (fun i _ =>
        mul_pos (M.hd i) (M.compAmp_pos i (xiStar_pos.trans_le (xiStar_le_xChart t))))
        ⟨⟨0, M.hs⟩, Finset.mem_univ _⟩
    have hA0_pos := M.ampl_xi_pos
    have hpt_id : ∀ i, M.jensenWeight i / (M.d i * M.compAmp i (xChart t) / M.toSource.ampl (xChart t)) =
        Real.exp (logAmp M.toSource.ampl t - logAmp (M.compAmp i) t) := fun i => by
      have hi0 := M.compAmp_pos i xiStar_pos
      have hit := M.compAmp_pos i (xiStar_pos.trans_le (xiStar_le_xChart t))
      unfold logAmp jensenWeight
      rw [Real.exp_sub, Real.exp_log (div_pos hAt_pos hA0_pos), Real.exp_log (div_pos hit hi0)]
      field_simp [M.hd i |>.ne']
    have hpt_sum : ∑ i, M.jensenWeight i * Real.log (M.jensenWeight i /
          (M.d i * M.compAmp i (xChart t) / M.toSource.ampl (xChart t))) =
        logAmp M.toSource.ampl t - ∑ i, M.jensenWeight i * logAmp (M.compAmp i) t := by
      simp_rw [hpt_id, Real.log_exp, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
        M.sum_jensenWeight, one_mul]
    rw [← Finset.sum_div, hpt_sum, sub_div]
  refine ⟨?_, ?_, ?_⟩
  · rw [hL, hR]
    nlinarith [hle]
  · rw [hdiff, hkl]
  · rw [hL, hR]
    constructor
    · intro heq
      have heq' : ∑ i, M.jensenWeight i * ∫ t in Ioi (0 : ℝ), logAmp (M.compAmp i) t / t ^ 2 =
          ∫ t in Ioi (0 : ℝ), logAmp M.toSource.ampl t / t ^ 2 := by
        exact mul_left_cancel₀ hpos_coeff.ne' (by linarith)
      exact hiff.mp heq'
    · intro hcoinc
      rw [hiff.mpr hcoinc]

end MixtureData

end FormalResearch.ModularBootstrap.Mixtures

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.jetAmplitude_nullAmp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.jetAmplitude_nullAmp

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.pmix_jets_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.pmix_jets_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_jensen_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.MixtureData.pmix_jensen_full

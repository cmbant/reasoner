module

public import FormalResearch.SignUncertainty.CtChartSser
public import FormalResearch.SignUncertainty.CtChartIntegral
public import FormalResearch.SignUncertainty.CtCfuGerm
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Complex germs of the dispersion: `k`, `n`, `ñ`, `p = z ñ` over `ℂ` (CFU chart, `ct:cfu` Step 2/3)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 2: `m(τ) = τ² n(τ²)`, `∫₀^τ m = τ³ ñ(τ²)`, `n`, `ñ` analytic.
**Proved.**  Complex versions of the real germs `CtCfu.kfun`, `nfun`, `ntil`: `C^∞` over `ℂ` at `0` (hence analytic), restricting to the real germs on `ℝ`,
conjugation symmetric, with `k = 2n + 2z n'` and `n = 3ñ + 2z ñ'` (so `p' = (n - ñ)/2`).
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty.CtChart

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

open CtCfu (kfun nfun ntil rr)

/-- `k(y) = π² S_3(π² y)/S_1(π² y)` over `ℂ`. -/
noncomputable def kC (y : ℂ) : ℂ := (π : ℂ) ^ 2 * SserC 3 ((π : ℂ) ^ 2 * y) / SserC 1 ((π : ℂ) ^ 2 * y)

/-- `n(z) = ½ ∫₀¹ k(t z) dt` over `ℂ`. -/
noncomputable def nC (z : ℂ) : ℂ := (1 / 2) * ∫ t in (0 : ℝ)..1, kC ((t : ℂ) * z)

/-- `ñ(z) = ∫₀¹ s² n(z s²) ds` over `ℂ`. -/
noncomputable def ntC (z : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, (s : ℂ) ^ 2 * nC (z * (s : ℂ) ^ 2)

/-- `p(z) = z ñ(z)`. -/
noncomputable def pC (z : ℂ) : ℂ := z * ntC z

lemma SserC1_zero : SserC 1 0 = 1 := by simp [SserC_zero]

lemma contDiffAt_kC : ContDiffAt ℂ ∞' kC 0 := by
  unfold kC
  have h3 : ContDiff ℂ ∞' (fun y : ℂ => SserC 3 ((π : ℂ) ^ 2 * y)) :=
    (contDiff_SserC 3).comp (contDiff_const.mul contDiff_id)
  have h1 : ContDiff ℂ ∞' (fun y : ℂ => SserC 1 ((π : ℂ) ^ 2 * y)) :=
    (contDiff_SserC 1).comp (contDiff_const.mul contDiff_id)
  refine (contDiffAt_const.mul h3.contDiffAt).div h1.contDiffAt ?_
  simp [SserC1_zero]

lemma contDiffAt_nC : ContDiffAt ℂ ∞' nC 0 := by
  unfold nC
  refine contDiffAt_const.mul (contDiffAt_segInt (F := fun z w => kC (w * z)) ?_)
  intro t ht
  have h : ContDiffAt ℂ ∞' kC ((t : ℂ) * 0) := by simpa using contDiffAt_kC
  exact h.comp (0, (t : ℂ)) (by fun_prop : ContDiff ℂ ∞' fun p : ℂ × ℂ => p.2 * p.1).contDiffAt

lemma contDiffAt_ntC : ContDiffAt ℂ ∞' ntC 0 := by
  unfold ntC
  refine contDiffAt_segInt (F := fun z w => w ^ 2 * nC (z * w ^ 2)) ?_
  intro t ht
  have h : ContDiffAt ℂ ∞' nC ((fun p : ℂ × ℂ => p.1 * p.2 ^ 2) (0, (t : ℂ))) := by simpa using contDiffAt_nC
  have h2 : ContDiffAt ℂ ∞' (fun p : ℂ × ℂ => nC (p.1 * p.2 ^ 2)) (0, (t : ℂ)) :=
    ContDiffAt.comp (g := nC) (f := fun p : ℂ × ℂ => p.1 * p.2 ^ 2) (0, (t : ℂ)) h
      (by fun_prop : ContDiff ℂ ∞' fun p : ℂ × ℂ => p.1 * p.2 ^ 2).contDiffAt
  exact (contDiff_snd.pow 2).contDiffAt.mul h2

lemma contDiffAt_pC : ContDiffAt ℂ ∞' pC 0 := by
  unfold pC; exact contDiffAt_id.mul contDiffAt_ntC

/-! ### Restriction to the real axis and conjugation symmetry -/

lemma kC_ofReal (x : ℝ) : kC (x : ℂ) = (kfun x : ℂ) := by
  unfold kC kfun
  have := SserC_ofReal 3 (π ^ 2 * x)
  have h1 := SserC_ofReal 1 (π ^ 2 * x)
  push_cast at this h1 ⊢
  rw [this, h1]

lemma nC_ofReal (x : ℝ) : nC (x : ℂ) = (nfun x : ℂ) := by
  unfold nC nfun
  have : ∀ t : ℝ, kC ((t : ℂ) * (x : ℂ)) = (kfun (t * x) : ℂ) := fun t => by
    rw [← Complex.ofReal_mul]; exact kC_ofReal _
  simp only [this]
  rw [intervalIntegral.integral_ofReal]
  push_cast; rfl

lemma ntC_ofReal (x : ℝ) : ntC (x : ℂ) = (ntil x : ℂ) := by
  unfold ntC ntil
  have : ∀ s : ℝ, (s : ℂ) ^ 2 * nC ((x : ℂ) * (s : ℂ) ^ 2) = ((s ^ 2 * nfun (x * s ^ 2) : ℝ) : ℂ) := fun s => by
    have e : (x : ℂ) * (s : ℂ) ^ 2 = ((x * s ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, nC_ofReal]; push_cast; ring
  simp only [this]
  rw [intervalIntegral.integral_ofReal]

lemma intInt_conj (f : ℝ → ℂ) :
    ∫ t in (0 : ℝ)..1, starRingEnd ℂ (f t) = starRingEnd ℂ (∫ t in (0 : ℝ)..1, f t) := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
  exact integral_conj

lemma kC_conj (y : ℂ) : kC (starRingEnd ℂ y) = starRingEnd ℂ (kC y) := by
  unfold kC
  have e1 : (π : ℂ) ^ 2 * starRingEnd ℂ y = starRingEnd ℂ ((π : ℂ) ^ 2 * y) := by simp
  rw [e1, SserC_conj, SserC_conj]
  simp [map_div₀]

lemma nC_conj (z : ℂ) : nC (starRingEnd ℂ z) = starRingEnd ℂ (nC z) := by
  unfold nC
  rw [map_mul, ← intInt_conj]
  congr 1
  · simp only [one_div, map_inv₀, map_ofNat]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    show _ = _
    have : (t : ℂ) * starRingEnd ℂ z = starRingEnd ℂ ((t : ℂ) * z) := by simp
    rw [this, kC_conj]

lemma ntC_conj (z : ℂ) : ntC (starRingEnd ℂ z) = starRingEnd ℂ (ntC z) := by
  unfold ntC
  rw [← intInt_conj]
  refine intervalIntegral.integral_congr fun t _ => ?_
  show _ = _
  rw [map_mul, ← nC_conj]; simp

lemma pC_conj (z : ℂ) : pC (starRingEnd ℂ z) = starRingEnd ℂ (pC z) := by
  unfold pC; rw [map_mul, ntC_conj]

lemma pC_ofReal (x : ℝ) : pC (x : ℂ) = ((x * ntil x : ℝ) : ℂ) := by
  unfold pC; rw [ntC_ofReal]; push_cast; ring

/-! ### Analyticity and the identity theorem along the real axis -/

lemma analyticAt_of_cd {f : ℂ → ℂ} {z : ℂ} (h : ContDiffAt ℂ ∞' f z) : AnalyticAt ℂ f z := by
  have h1 : ∀ᶠ y in 𝓝 z, ContDiffAt ℂ 1 f y := (h.of_le (by simp)).eventually (by simp)
  obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp h1
  exact DifferentiableOn.analyticAt (s := Metric.ball z r)
    (fun y hy => ((hb y hy).differentiableAt (by simp)).differentiableWithinAt) (Metric.ball_mem_nhds z hr)

lemma analyticAt_kC : AnalyticAt ℂ kC 0 := analyticAt_of_cd contDiffAt_kC
lemma analyticAt_nC : AnalyticAt ℂ nC 0 := analyticAt_of_cd contDiffAt_nC
lemma analyticAt_ntC : AnalyticAt ℂ ntC 0 := analyticAt_of_cd contDiffAt_ntC
lemma analyticAt_pC : AnalyticAt ℂ pC 0 := analyticAt_of_cd contDiffAt_pC

lemma tendsto_ofReal_nhdsGT : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) : ℂ)) := Complex.continuous_ofReal.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hx)

/-- Identity theorem along the positive real axis. -/
lemma eventually_eq_of_real {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), f (x : ℂ) = g (x : ℂ)) : ∀ᶠ z in 𝓝 (0 : ℂ), f z = g z := by
  have hd : AnalyticAt ℂ (fun z => f z - g z) 0 := hf.sub hg
  have hfr : ∃ᶠ z in 𝓝[≠] (0 : ℂ), (fun z => f z - g z) z = 0 := by
    have h2 : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), (fun z => f z - g z) (x : ℂ) = 0 := h.mono fun x hx => sub_eq_zero.mpr hx
    exact (tendsto_ofReal_nhdsGT.frequently h2.frequently)
  have := hd.frequently_zero_iff_eventually_zero.mp hfr
  exact this.mono fun z hz => sub_eq_zero.mp hz

lemma deriv_eq_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℂ f (x : ℂ))
    (hg : DifferentiableAt ℝ g x) (h : ∀ y : ℝ, f (y : ℂ) = (g y : ℂ)) :
    deriv f (x : ℂ) = ((deriv g x : ℝ) : ℂ) := by
  have h1 := hf.hasDerivAt.comp_ofReal
  have h2 := hg.hasDerivAt.ofReal_comp
  have : (fun y : ℝ => f (y : ℂ)) = fun y => (g y : ℂ) := funext h
  rw [this] at h1
  exact h1.unique h2

/-! ### The real relations `k = 2n + 2z n'`, `n = 3ñ + 2z ñ'` -/

lemma real_rel1 {z : ℝ} (hz0 : 0 < z) (hz : z < rr) : kfun z = 2 * nfun z + 2 * z * deriv nfun z := by
  set τ : ℝ := Real.sqrt z with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.mpr hz0
  have hτ2 : τ ^ 2 = z := Real.sq_sqrt hz0.le
  have hev : ∀ᶠ u in 𝓝 τ, hankelEdgeM u = u ^ 2 * nfun (u ^ 2) := by
    have h1 : ∀ᶠ u in 𝓝 τ, 0 < u := lt_mem_nhds hτ0
    have h2 : ∀ᶠ u in 𝓝 τ, u ^ 2 < rr := by
      have : Continuous fun u : ℝ => u ^ 2 := by fun_prop
      exact (this.continuousAt (x := τ)).eventually (gt_mem_nhds (by show τ ^ 2 < rr; rw [hτ2]; exact hz))
    filter_upwards [h1, h2] with u hu hu2 using CtCfu.hankelEdgeM_eq hu.le hu2
  have hd1 : HasDerivAt hankelEdgeM (τ * kfun z) τ := by
    refine (hankelEdgeM_hasDerivAt hτ0).congr_deriv ?_
    rw [CtCfu.hankelEdgeM'_eq hτ0 (by rw [hτ2]; exact hz), hτ2]
  have hdn : DifferentiableAt ℝ nfun z :=
    (CtCfu.contDiffOn_nfun.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith [CtCfu.rr_pos], hz⟩)
  have hd2 : HasDerivAt (fun u : ℝ => u ^ 2 * nfun (u ^ 2))
      (2 * τ * nfun z + τ ^ 2 * (deriv nfun z * (2 * τ))) τ := by
    have h3 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
    have h4 : HasDerivAt nfun (deriv nfun z) ((fun u : ℝ => u ^ 2) τ) := by show HasDerivAt nfun _ (τ ^ 2); rw [hτ2]; exact hdn.hasDerivAt
    have h5 := HasDerivAt.comp (h := fun u : ℝ => u ^ 2) τ h4 h3
    have := (hasDerivAt_pow 2 τ).mul h5
    convert this using 1
    · funext u; simp
    · simp only [Function.comp, hτ2]; norm_num
  have := hd1.unique (hd2.congr_of_eventuallyEq hev)
  have hτne : τ ≠ 0 := hτ0.ne'
  have h6 : τ * kfun z = τ * (2 * nfun z + 2 * z * deriv nfun z) := by
    rw [this, ← hτ2]; ring
  exact mul_left_cancel₀ hτne h6

lemma real_rel2 {z : ℝ} (hz0 : 0 < z) (hz : z < rr) : nfun z = 3 * ntil z + 2 * z * deriv ntil z := by
  set τ : ℝ := Real.sqrt z with hτ
  have hτ0 : 0 < τ := Real.sqrt_pos.mpr hz0
  have hτ2 : τ ^ 2 = z := Real.sq_sqrt hz0.le
  have hev : ∀ᶠ u in 𝓝 τ, ∫ t in (0 : ℝ)..u, hankelEdgeM t = u ^ 3 * ntil (u ^ 2) := by
    have h1 : ∀ᶠ u in 𝓝 τ, 0 < u := lt_mem_nhds hτ0
    have h2 : ∀ᶠ u in 𝓝 τ, u ^ 2 < rr := by
      have : Continuous fun u : ℝ => u ^ 2 := by fun_prop
      exact (this.continuousAt (x := τ)).eventually (gt_mem_nhds (by show τ ^ 2 < rr; rw [hτ2]; exact hz))
    filter_upwards [h1, h2] with u hu hu2 using CtCfu.integral_hankelEdgeM_eq hu.le hu2
  have hcont : ContinuousOn hankelEdgeM (Set.Ici 0) := hankelEdgeM_continuousOn
  have hint : IntervalIntegrable hankelEdgeM MeasureTheory.volume 0 τ :=
    (hcont.mono (fun x hx => by rw [Set.uIcc_of_le hτ0.le] at hx; exact hx.1)).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter hankelEdgeM (𝓝 τ) :=
    (hcont.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi τ hτ0
  have hd1 : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, hankelEdgeM t) (hankelEdgeM τ) τ :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas (hankelEdgeM_hasDerivAt hτ0).continuousAt
  have hdn : DifferentiableAt ℝ ntil z :=
    (CtCfu.contDiffOn_ntil.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨by linarith [CtCfu.rr_pos], hz⟩)
  have hd2 : HasDerivAt (fun u : ℝ => u ^ 3 * ntil (u ^ 2))
      (3 * τ ^ 2 * ntil z + τ ^ 3 * (deriv ntil z * (2 * τ))) τ := by
    have h3 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * τ) τ := by simpa using hasDerivAt_pow 2 τ
    have h4 : HasDerivAt ntil (deriv ntil z) ((fun u : ℝ => u ^ 2) τ) := by show HasDerivAt ntil _ (τ ^ 2); rw [hτ2]; exact hdn.hasDerivAt
    have h5 := HasDerivAt.comp (h := fun u : ℝ => u ^ 2) τ h4 h3
    have := (hasDerivAt_pow 3 τ).mul h5
    convert this using 1
    · funext u; simp
    · simp only [Function.comp, hτ2]; norm_num
  have h7 := hd1.unique (hd2.congr_of_eventuallyEq hev)
  rw [CtCfu.hankelEdgeM_eq hτ0.le (by rw [hτ2]; exact hz), hτ2] at h7
  have hτne : τ ^ 2 ≠ 0 := by positivity
  have h8 : τ ^ 2 * nfun z = τ ^ 2 * (3 * ntil z + 2 * z * deriv ntil z) := by
    rw [hτ2, h7, ← hτ2]; ring
  exact mul_left_cancel₀ hτne h8

/-! ### The relations over `ℂ` and the values at `0` -/

lemma ev_real_analytic {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), AnalyticAt ℂ f (x : ℂ) := by
  have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ f z := hf.eventually_analyticAt
  have h2 : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
    tendsto_ofReal_nhdsGT.mono_right nhdsWithin_le_nhds
  exact h2.eventually h1

lemma ev_real_lt : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x ∧ x < rr :=
  by filter_upwards [Ioo_mem_nhdsGT CtCfu.rr_pos] with x hx using hx

lemma nfun_diff {x : ℝ} (h0 : 0 < x) (h1 : x < rr) : DifferentiableAt ℝ nfun x :=
  (CtCfu.contDiffOn_nfun.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds ⟨by linarith [CtCfu.rr_pos], h1⟩)

lemma ntil_diff {x : ℝ} (h0 : 0 < x) (h1 : x < rr) : DifferentiableAt ℝ ntil x :=
  (CtCfu.contDiffOn_ntil.differentiableOn (by simp)).differentiableAt
    (isOpen_Ioo.mem_nhds ⟨by linarith [CtCfu.rr_pos], h1⟩)

/-- `k = 2 n + 2 z n'`. -/
lemma rel_k : ∀ᶠ z in 𝓝 (0 : ℂ), kC z = 2 * nC z + 2 * z * deriv nC z := by
  refine eventually_eq_of_real analyticAt_kC ?_ ?_
  · exact (analyticAt_const.mul analyticAt_nC).add ((analyticAt_const.mul analyticAt_id).mul analyticAt_nC.deriv)
  · filter_upwards [ev_real_lt, ev_real_analytic analyticAt_nC] with x hx hxa
    rw [kC_ofReal, nC_ofReal, deriv_eq_of_real (f := nC) (g := nfun) hxa.differentiableAt (nfun_diff hx.1 hx.2) nC_ofReal,
      real_rel1 hx.1 hx.2]
    push_cast; ring

/-- `n = 3 ñ + 2 z ñ'`. -/
lemma rel_n : ∀ᶠ z in 𝓝 (0 : ℂ), nC z = 3 * ntC z + 2 * z * deriv ntC z := by
  refine eventually_eq_of_real analyticAt_nC ?_ ?_
  · exact (analyticAt_const.mul analyticAt_ntC).add ((analyticAt_const.mul analyticAt_id).mul analyticAt_ntC.deriv)
  · filter_upwards [ev_real_lt, ev_real_analytic analyticAt_ntC] with x hx hxa
    rw [nC_ofReal, ntC_ofReal, deriv_eq_of_real (f := ntC) (g := ntil) hxa.differentiableAt (ntil_diff hx.1 hx.2) ntC_ofReal,
      real_rel2 hx.1 hx.2]
    push_cast; ring

lemma kC_zero : kC 0 = (π : ℂ) ^ 2 / 6 := by
  have := kC_ofReal 0
  rw [Complex.ofReal_zero, CtCfu.kfun_zero] at this
  rw [this]; push_cast; ring

lemma nC_zero : nC 0 = (π : ℂ) ^ 2 / 12 := by
  have := nC_ofReal 0
  rw [Complex.ofReal_zero, CtCfu.nfun_zero] at this
  rw [this]; push_cast; ring

lemma ntC_zero : ntC 0 = (π : ℂ) ^ 2 / 36 := by
  have := ntC_ofReal 0
  rw [Complex.ofReal_zero, CtCfu.ntil_zero] at this
  rw [this]; push_cast; ring

lemma hasDerivAt_nC_zero : HasDerivAt nC (-(7 * (π : ℂ) ^ 4 / 1440)) 0 := by
  have hd : DifferentiableAt ℂ nC 0 := analyticAt_nC.differentiableAt
  have h := deriv_eq_of_real (f := nC) (g := nfun) (x := 0) (by simpa using hd)
    CtCfu.hasDerivAt_nfun_zero.differentiableAt nC_ofReal
  have h2 : deriv nC 0 = -(7 * (π : ℂ) ^ 4 / 1440) := by
    simpa [CtCfu.hasDerivAt_nfun_zero.deriv] using h
  rw [← h2]; exact hd.hasDerivAt

lemma hasDerivAt_ntC_zero : HasDerivAt ntC (-(7 * (π : ℂ) ^ 4 / 7200)) 0 := by
  have hd : DifferentiableAt ℂ ntC 0 := analyticAt_ntC.differentiableAt
  have h := deriv_eq_of_real (f := ntC) (g := ntil) (x := 0) (by simpa using hd)
    CtCfu.hasDerivAt_ntil_zero.differentiableAt ntC_ofReal
  have h2 : deriv ntC 0 = -(7 * (π : ℂ) ^ 4 / 7200) := by
    simpa [CtCfu.hasDerivAt_ntil_zero.deriv] using h
  rw [← h2]; exact hd.hasDerivAt

lemma hasDerivAt_kC_zero : HasDerivAt kC (-(7 * (π : ℂ) ^ 4 / 360)) 0 := by
  have hd : DifferentiableAt ℂ kC 0 := analyticAt_kC.differentiableAt
  have h := deriv_eq_of_real (f := kC) (g := kfun) (x := 0) (by simpa using hd)
    CtCfu.hasDerivAt_kfun_zero.differentiableAt kC_ofReal
  have h2 : deriv kC 0 = -(7 * (π : ℂ) ^ 4 / 360) := by
    simpa [CtCfu.hasDerivAt_kfun_zero.deriv] using h
  rw [← h2]; exact hd.hasDerivAt

end FormalResearch.SignUncertainty.CtChart

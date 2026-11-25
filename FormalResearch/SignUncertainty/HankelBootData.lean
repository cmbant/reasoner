module

public import FormalResearch.SignUncertainty.HankelBandAssembly
public import FormalResearch.SignUncertainty.HankelTransportMass

/-!
# Hankel bootstrap data: chart glue and band moments with explicit `r_∞` slack (M5-S6a-1)

The Hankel profile `f` lives on the Hankel side; `hankelPsiR c f x = Re Ψ̃(x)` on the real axis.  The
first band moment `B₁` of the Hankel band instance is transported to the Langer variable `x` by the
change of variables `u = c ξ(x)`, and the Hankel sign `Re Ψ̃ ≥ -r_∞` and the transport bound
`|Re Ψ̃ - Q| ≤ r_∞` (with `Q = hankelPsiLead`) are carried along with their explicit slack.

Results (each a proved statement):
* `hankelBootU_xi`: the chart inverts `ξ`: `ũ(ξ(x)) = x` for `|x| ≤ langerRadius c`.
* `hankelBoot_psi_ge`: `-r_∞ ≤ Re Ψ̃(u)` for `-R ≤ u ≤ u_T`.
* `hankelBootB1_le_moment`: `B₁ ≤ ∫_{-R}^{u_T} ((-u)/R) Re Ψ̃ + R r_∞`.
* `hankelBootMoment_ge`, `hankelBootB1_le_B1k`, `hankelBootB1k_nonneg`: the truncated moments.
* `hankelBootB2_nonneg`, `hankelBootB1_nonneg`: nonnegativity of the dm-side moments.
* `hankelBoot_bandB1_eq`, `hankelBoot_bandB2_eq`: the bridge to `bandB1`, `bandB2` of `hankelBandInstance`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

open FormalResearch.ModularBootstrap.StripBand

namespace FormalResearch.SignUncertainty

/-- Ψ-side truncated first band moment `∫_{-R}^{u_T} min(1,(k+1)(-u)/R) Re Ψ̃(u) du` (no slack). -/
noncomputable def hankelBootMoment (c : ℝ) (f : ℝ → ℝ) (R u_T : ℝ) (k : ℕ) : ℝ :=
  ∫ u in (-R)..u_T, min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u

/-- The `B_1^{(k)}` of the Hankel bootstrap instance: moment plus explicit slack `2 R r_∞`. -/
noncomputable def hankelBootB1k (c : ℝ) (f : ℝ → ℝ) (R u_T : ℝ) (k : ℕ) : ℝ :=
  hankelBootMoment c f R u_T k + 2 * R * hankelRinf c

/-- dm-side first band moment (the `bandB1` of `hankelBandInstance`, with `R` free). -/
noncomputable def hankelBootB1 (c : ℝ) (f : ℝ → ℝ) (R u_T : ℝ) : ℝ :=
  R⁻¹ * ∫ ξ in Set.Icc (hankelXi c u_T) (hankelXi c (-R)), (-hankelBandU c ξ) ∂(hankelDmPos c f)

/-- dm-side tail mass `B_2` (the `bandB2` of `hankelBandInstance`, with `R` free). -/
noncomputable def hankelBootB2 (c : ℝ) (f : ℝ → ℝ) (R : ℝ) : ℝ :=
  (hankelDmPos c f (Set.Ici (hankelXi c (-R)))).toReal

/-- Shifted quadrature test `Ψ̃(u+ℓ)(1+u/R)^{k+1}`. -/
noncomputable def hankelBootShifted (c : ℝ) (f : ℝ → ℝ) (R ℓ : ℝ) (k : ℕ) (u : ℂ) : ℂ :=
  hankelPsi c f (u + (ℓ : ℂ)) * (1 + u / (R : ℂ)) ^ (k + 1)

/-- The Langer-side `|u_T| ≤ r_c` for `u_T ∈ [-3, 0]` at scale `c ≥ 3·10⁶`. -/
lemma hankelBoot_abs_uT {c u_T : ℝ} (hc : 3e6 ≤ c) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) :
    |u_T| ≤ langerRadius c := by
  rw [abs_of_nonpos hu0]
  linarith [(hankel_radius_ge hc).1]

/-- Points of `[-R, u_T]` lie in the Langer disc when `R ≤ r_c` and `|u_T| ≤ r_c`. -/
lemma hankelBoot_mem_Icc {c R u_T x : ℝ} (hu : |u_T| ≤ langerRadius c) (hRA : R ≤ langerRadius c)
    (hx : x ∈ Icc (-R) u_T) : |x| ≤ langerRadius c :=
  abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2, le_abs_self u_T]⟩

/-- `Re Ψ̃` is continuous on the band `[-R, u_T]`. -/
lemma hankelBoot_psiR_cont {c ε R u_T : ℝ} {f : ℝ → ℝ} (hc0 : 0 < c) (hfe : IsHankelEigenfn c ε f)
    (hu : |u_T| ≤ langerRadius c) (hRA : R ≤ langerRadius c) :
    ContinuousOn (hankelPsiR c f) (Icc (-R) u_T) :=
  (continuousOn_hankelPsiR hc0 hfe).mono fun _ hx => abs_le.1 (hankelBoot_mem_Icc hu hRA hx)

/-- The leading term `Q = hankelPsiLead` is continuous on the band `[-R, u_T]`. -/
lemma hankelBoot_psiLead_cont {c ε R u_T : ℝ} {f : ℝ → ℝ} (hc0 : 0 < c) (hfe : IsHankelEigenfn c ε f)
    (hu : |u_T| ≤ langerRadius c) (hRA : R ≤ langerRadius c) :
    ContinuousOn (hankelPsiLead c f) (Icc (-R) u_T) :=
  (continuousOn_hankelQ hc0 hfe).mono fun _ hx => abs_le.1 (hankelBoot_mem_Icc hu hRA hx)

/-- **Chart glue (item 1).** The chart inverts the Langer map: `ũ(ξ(x)) = x` for `|x| ≤ r_c`. -/
theorem hankelBootU_xi {c x : ℝ} (hc : 0 < c) (hx : |x| ≤ langerRadius c) :
    hankelBandU c (hankelXi c x) = x := by
  have hK := langerScale_pos hc
  have hx' : |x| ≤ langerScale c * 4.94e-4 := hx
  obtain ⟨hreal, -⟩ := chartYinv_real_point hc hx'
  have hyn : ‖((x / langerScale c : ℝ) : ℂ)‖ ≤ 4.94e-4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hK, div_le_iff₀ hK]
    linarith
  obtain ⟨-, hspec⟩ := chartYinv_spec etaC (exists_chartY_small langerEta_etaC hyn)
  rw [hreal] at hspec
  have hpi : Real.pi ^ 2 ≠ 0 := by positivity
  have hxi : Real.pi ^ 2 * hankelXi c x - 1 =
      (chartYinv etaC (((x / langerScale c : ℝ)) : ℂ)).re := by
    unfold hankelXi
    field_simp
    ring
  unfold hankelBandU
  rw [hxi, hspec, Complex.ofReal_re]
  field_simp

/-- **Sign (item 2).** `-r_∞ ≤ Re Ψ̃(u)` for `-R ≤ u ≤ u_T`. -/
theorem hankelBoot_psi_ge {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (_hR0 : 0 < R) (_hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) {u : ℝ}
    (hu1 : -R ≤ u) (hu2 : u ≤ u_T) : -hankelRinf c ≤ hankelPsiR c f u := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hx : |u| ≤ langerRadius c := hankelBoot_mem_Icc hu hRA ⟨hu1, hu2⟩
  refine hankel_psi_sign hc5 hf hε hM hx ?_
  rw [← hT]
  exact hankel_phi_anti hc0 hx hu hu2

/-- Pointwise measure bridge: on a measurable set inside `(0, ∞)` where the density is nonnegative,
the `dm_+` integral is the Lebesgue integral against the density. -/
theorem hankelBoot_dm_setIntegral {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Ioi (0 : ℝ))
    (hnn : ∀ ξ ∈ s, 0 ≤ hankelDmDens c f ξ) (g : ℝ → ℝ) :
    ∫ ξ in s, g ξ ∂(hankelDmPos c f) = ∫ ξ in s, g ξ * hankelDmDens c f ξ := by
  calc ∫ ξ in s, g ξ ∂(hankelDmPos c f) = ∫ ξ, s.indicator g ξ ∂(hankelDmPos c f) :=
        (integral_indicator hs).symm
    _ = ∫ ξ in Ioi (0 : ℝ), max (hankelDmDens c f ξ) 0 • s.indicator g ξ :=
        hankelDmPos_integral hc hf _
    _ = ∫ ξ in Ioi (0 : ℝ), s.indicator (fun ξ => g ξ * hankelDmDens c f ξ) ξ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
        by_cases h : ξ ∈ s
        · simp only [Set.indicator_of_mem h, smul_eq_mul, max_eq_left (hnn ξ h)]
          ring
        · simp [Set.indicator_of_notMem h]
    _ = ∫ ξ in s, g ξ * hankelDmDens c f ξ := by
        rw [setIntegral_indicator hs, Set.inter_eq_right.2 hsub]

/-- Change of variables: `R · B₁ = ∫_{-R}^{u_T} (-x) Q(x) dx` with `Q = hankelPsiLead`. -/
theorem hankelBoot_R_mul_B1 {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 0 < c) (hf : IsHankelFeasible c ε T f)
    (hT : c * hankelXi c u_T = T) (hu : |u_T| ≤ langerRadius c) (hRA : R ≤ langerRadius c)
    (hR : 0 < R) (hRu : -R ≤ u_T) :
    R * hankelBootB1 c f R u_T = ∫ x in (-R)..u_T, (-x) * hankelPsiLead c f x := by
  have hfe := hf.toIsHankelEigenfn
  have hRA' : |-R| ≤ langerRadius c := by rw [abs_neg, abs_of_pos hR]; exact hRA
  have hmonoξ : hankelXi c u_T ≤ hankelXi c (-R) :=
    le_of_mul_le_mul_left (hankel_phi_anti hc hRA' hu hRu) hc
  have hξa : 0 < hankelXi c u_T := hankelXi_pos hc hu
  have hIsub : Icc (hankelXi c u_T) (hankelXi c (-R)) ⊆ Ioi (0 : ℝ) :=
    fun ξ hξ => lt_of_lt_of_le hξa hξ.1
  have hnn : ∀ ξ ∈ Icc (hankelXi c u_T) (hankelXi c (-R)), 0 ≤ hankelDmDens c f ξ := by
    intro ξ hξ
    have hξpos : 0 < ξ := hIsub hξ
    have hcξ : T ≤ c * ξ := by
      rw [← hT]
      exact mul_le_mul_of_nonneg_left hξ.1 hc.le
    unfold hankelDmDens
    exact mul_nonneg hc.le (mul_nonneg (hf.tail_nonneg _ hcξ) (hankelRho0_nonneg hc (mul_pos hc hξpos).le))
  have hset : ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-R)), (-hankelBandU c ξ) ∂(hankelDmPos c f) =
      ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-R)), (-hankelBandU c ξ) * hankelDmDens c f ξ :=
    hankelBoot_dm_setIntegral hc hfe measurableSet_Icc hIsub hnn (fun ξ => -hankelBandU c ξ)
  have hB1 : R * hankelBootB1 c f R u_T =
      ∫ ξ in hankelXi c u_T..hankelXi c (-R), (-hankelBandU c ξ) * hankelDmDens c f ξ := by
    unfold hankelBootB1
    rw [← mul_assoc, mul_inv_cancel₀ hR.ne', one_mul, hset, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hmonoξ]
  have hscale : ∀ ξ : ℝ, (-hankelBandU c ξ) * hankelDmDens c f ξ =
      c * (-hankelBandU c ((c * ξ) / c) * (hankelRho0 c (c * ξ) * f (c * ξ))) := by
    intro ξ
    unfold hankelDmDens
    rw [mul_div_cancel_left₀ ξ hc.ne']
    ring
  have hstep1 : ∫ ξ in hankelXi c u_T..hankelXi c (-R), (-hankelBandU c ξ) * hankelDmDens c f ξ =
      c * ∫ ξ in hankelXi c u_T..hankelXi c (-R),
        (-hankelBandU c ((c * ξ) / c) * (hankelRho0 c (c * ξ) * f (c * ξ))) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun ξ _ => hscale ξ
  have hstep2 : ∫ ξ in hankelXi c u_T..hankelXi c (-R),
      (-hankelBandU c ((c * ξ) / c) * (hankelRho0 c (c * ξ) * f (c * ξ))) =
      c⁻¹ • ∫ u in (c * hankelXi c u_T)..(c * hankelXi c (-R)),
        (-hankelBandU c (u / c) * (hankelRho0 c u * f u)) :=
    intervalIntegral.integral_comp_mul_left (f := fun u => -hankelBandU c (u / c) * (hankelRho0 c u * f u))
      hc.ne'
  have hstep4 : ∫ u in (c * hankelXi c u_T)..(c * hankelXi c (-R)),
      (-hankelBandU c (u / c) * (hankelRho0 c u * f u)) =
      -∫ u in (c * hankelXi c (-R))..(c * hankelXi c u_T), (-hankelBandU c (u / c) * (hankelRho0 c u * f u)) :=
    intervalIntegral.integral_symm _ _
  have hsub : ∫ x in (-R)..u_T,
      (-hankelBandU c ((c * hankelXi c x) / c) * (hankelRho0 c (c * hankelXi c x) * f (c * hankelXi c x))) *
        (c * hankelXiD c x) =
      ∫ u in (c * hankelXi c (-R))..(c * hankelXi c u_T), (-hankelBandU c (u / c) * (hankelRho0 c u * f u)) :=
    hankel_subst hc hRA' hu hRu (fun u => -hankelBandU c (u / c) * (hankelRho0 c u * f u))
  rw [hB1, hstep1, hstep2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, hstep4, ← hsub,
    ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hRu] at hx
  have hxA : |x| ≤ langerRadius c := hankelBoot_mem_Icc hu hRA hx
  rw [mul_div_cancel_left₀ _ hc.ne', hankelBootU_xi hc hxA]
  unfold hankelPsiLead
  ring

/-- **Band moment upper bound (item 3).** `B₁ ≤ ∫_{-R}^{u_T} ((-u)/R) Re Ψ̃ + R r_∞`. -/
theorem hankelBootB1_le_moment {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) :
    hankelBootB1 c f R u_T ≤
      (∫ u in (-R)..u_T, ((-u) / R) * hankelPsiR c f u) + R * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hR := hankelBoot_R_mul_B1 hc0 hf hT hu hRA hR0 hRu
  have hΨc := hankelBoot_psiR_cont hc0 hfe hu hRA
  have hQc := hankelBoot_psiLead_cont hc0 hfe hu hRA
  have hint1 : IntervalIntegrable (fun x => (-x) * hankelPsiLead c f x) volume (-R) u_T :=
    ((continuousOn_id.neg).mul hQc).intervalIntegrable_of_Icc hRu
  have hint2 : IntervalIntegrable (fun x => (-x) * hankelPsiR c f x) volume (-R) u_T :=
    ((continuousOn_id.neg).mul hΨc).intervalIntegrable_of_Icc hRu
  have hpt : ∀ x ∈ Icc (-R) u_T,
      (-x) * hankelPsiLead c f x ≤ (-x) * hankelPsiR c f x + R * hankelRinf c := by
    intro x hx
    have hxA := hankelBoot_mem_Icc hu hRA hx
    have hd := abs_le.1 (hankelPsiR_sub_Q_le hc5 hfe hε hM hxA)
    have h1 : (-x) * (hankelPsiLead c f x - hankelPsiR c f x) ≤ (-x) * hankelRinf c :=
      mul_le_mul_of_nonneg_left (by linarith [hd.1]) (by linarith [hx.2])
    have h2 : (-x) * hankelRinf c ≤ R * hankelRinf c :=
      mul_le_mul_of_nonneg_right (by linarith [hx.1]) hr
    nlinarith [h1, h2]
  have hmono := intervalIntegral.integral_mono_on hRu hint1 (hint2.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add hint2 intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  have hJ : ∫ u in (-R)..u_T, ((-u) / R) * hankelPsiR c f u =
      R⁻¹ * ∫ u in (-R)..u_T, (-u) * hankelPsiR c f u := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u _ => ?_
    show ((-u) / R) * hankelPsiR c f u = R⁻¹ * ((-u) * hankelPsiR c f u)
    ring
  have hlen := mul_le_mul_of_nonneg_right (show u_T - -R ≤ R by linarith) (mul_nonneg hR0.le hr)
  have hkey : R * hankelBootB1 c f R u_T ≤
      (∫ u in (-R)..u_T, (-u) * hankelPsiR c f u) + R * (R * hankelRinf c) := by
    rw [hR]
    linarith
  rw [hJ]
  calc hankelBootB1 c f R u_T = R⁻¹ * (R * hankelBootB1 c f R u_T) := by
        rw [← mul_assoc, inv_mul_cancel₀ hR0.ne', one_mul]
    _ ≤ R⁻¹ * ((∫ u in (-R)..u_T, (-u) * hankelPsiR c f u) + R * (R * hankelRinf c)) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 hR0.le)
    _ = R⁻¹ * (∫ u in (-R)..u_T, (-u) * hankelPsiR c f u) + R * hankelRinf c := by
        rw [mul_add]
        congr 1
        field_simp

/-- Lower bound for the truncated moment: `-R r_∞ ≤ ∫_{-R}^{u_T} min(1,(k+1)(-u)/R) Re Ψ̃`. -/
theorem hankelBootMoment_ge {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (k : ℕ) :
    -(R * hankelRinf c) ≤ hankelBootMoment c f R u_T k := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hΨc := hankelBoot_psiR_cont hc0 hfe hu hRA
  have hmc : Continuous (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R)) := by fun_prop
  have hint : IntervalIntegrable (fun u => min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u)
      volume (-R) u_T :=
    (hmc.continuousOn.mul hΨc).intervalIntegrable_of_Icc hRu
  have hpt : ∀ u ∈ Icc (-R) u_T,
      -hankelRinf c ≤ min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u := by
    intro u hu'
    have hψ := hankelBoot_psi_ge hc hf hε hM hT hu0 hu3 hR0 hRu hRA hu'.1 hu'.2
    have hm0 : 0 ≤ min 1 (((k : ℝ) + 1) * (-u) / R) :=
      le_min zero_le_one (div_nonneg (mul_nonneg (by positivity) (by linarith [hu'.2])) hR0.le)
    have hm1 : min 1 (((k : ℝ) + 1) * (-u) / R) ≤ 1 := min_le_left _ _
    have h1 : min 1 (((k : ℝ) + 1) * (-u) / R) * (-hankelRinf c) ≤
        min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u :=
      mul_le_mul_of_nonneg_left hψ hm0
    have h2 : -hankelRinf c ≤ min 1 (((k : ℝ) + 1) * (-u) / R) * (-hankelRinf c) := by
      nlinarith [hm0, hm1, hr]
    linarith
  have hmono := intervalIntegral.integral_mono_on hRu intervalIntegrable_const hint hpt
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  unfold hankelBootMoment
  have hlen := mul_le_mul_of_nonneg_right (show u_T - -R ≤ R by linarith) hr
  linarith

/-- The truncated moment dominates the dm-side moment with slack `2 R r_∞` (item 5). -/
theorem hankelBootB1_le_B1k {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (k : ℕ) :
    hankelBootB1 c f R u_T ≤ hankelBootB1k c f R u_T k := by
  have hc0 : 0 < c := by linarith
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hfe := hf.toIsHankelEigenfn
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hfe hε hM
  have hbase := hankelBootB1_le_moment hc hf hε hM hT hu0 hu3 hR0 hRu hRA
  have hΨc := hankelBoot_psiR_cont hc0 hfe hu hRA
  have hmc : Continuous (fun u : ℝ => min 1 (((k : ℝ) + 1) * (-u) / R)) := by fun_prop
  have hint_a : IntervalIntegrable (fun u => ((-u) / R) * hankelPsiR c f u) volume (-R) u_T :=
    ((((continuousOn_id.neg).div_const R)).mul hΨc).intervalIntegrable_of_Icc hRu
  have hint_b : IntervalIntegrable (fun u => min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u)
      volume (-R) u_T :=
    (hmc.continuousOn.mul hΨc).intervalIntegrable_of_Icc hRu
  have hpt : ∀ u ∈ Icc (-R) u_T,
      ((-u) / R) * hankelPsiR c f u ≤
        min 1 (((k : ℝ) + 1) * (-u) / R) * hankelPsiR c f u + hankelRinf c := by
    intro u hu'
    have hψ := hankelBoot_psi_ge hc hf hε hM hT hu0 hu3 hR0 hRu hRA hu'.1 hu'.2
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have ht0 : 0 ≤ (-u) / R := div_nonneg (by linarith [hu'.2]) hR0.le
    have ht1 : (-u) / R ≤ 1 := (div_le_one hR0).2 (by linarith [hu'.1])
    have htm : (-u) / R ≤ min 1 (((k : ℝ) + 1) * (-u) / R) := by
      refine le_min ht1 ?_
      rw [div_le_div_iff_of_pos_right hR0]
      nlinarith [mul_nonneg hk (show 0 ≤ -u by linarith [hu'.2])]
    have hm1 : min 1 (((k : ℝ) + 1) * (-u) / R) ≤ 1 := min_le_left _ _
    have h1 : ((-u) / R - min 1 (((k : ℝ) + 1) * (-u) / R)) * hankelPsiR c f u ≤
        ((-u) / R - min 1 (((k : ℝ) + 1) * (-u) / R)) * (-hankelRinf c) :=
      mul_le_mul_of_nonpos_left hψ (by linarith)
    have h2 : ((-u) / R - min 1 (((k : ℝ) + 1) * (-u) / R)) * (-hankelRinf c) ≤ hankelRinf c := by
      nlinarith [hr, hm1, ht0]
    nlinarith [h1, h2]
  have hmono := intervalIntegral.integral_mono_on hRu hint_a (hint_b.add intervalIntegrable_const) hpt
  rw [intervalIntegral.integral_add hint_b intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul] at hmono
  unfold hankelBootB1k hankelBootMoment
  have hlen := mul_le_mul_of_nonneg_right (show u_T - -R ≤ R by linarith) hr
  linarith

/-- The truncated moment with slack is nonnegative (item 6). -/
theorem hankelBootB1k_nonneg {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hR0 : 0 < R) (hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) (k : ℕ) :
    0 ≤ hankelBootB1k c f R u_T k := by
  have hc5 : (5000 : ℝ) ≤ c := by linarith
  have hr : 0 ≤ hankelRinf c := hankelRinf_nonneg hc5 hf.toIsHankelEigenfn hε hM
  have hmom := hankelBootMoment_ge hc hf hε hM hT hu0 hu3 hR0 hRu hRA k
  have hRr := mul_nonneg hR0.le hr
  unfold hankelBootB1k
  linarith

/-- The dm-side tail mass is nonnegative (item 7). -/
theorem hankelBootB2_nonneg (c : ℝ) (f : ℝ → ℝ) (R : ℝ) : 0 ≤ hankelBootB2 c f R := by
  unfold hankelBootB2
  exact ENNReal.toReal_nonneg

/-- The dm-side first band moment is nonnegative (item 8). -/
theorem hankelBootB1_nonneg {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (_hf : IsHankelFeasible c ε T f)
    (_hε : ε = 1 ∨ ε = -1) (_hM : hankelMass c f = 1) (_hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hR0 : 0 < R) (_hRu : -R ≤ u_T) (hRA : R ≤ langerRadius c) :
    0 ≤ hankelBootB1 c f R u_T := by
  have hc0 : 0 < c := by linarith
  have hu : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hK := langerScale_pos hc0
  unfold hankelBootB1
  refine mul_nonneg (inv_nonneg.2 hR0.le) ?_
  refine setIntegral_nonneg measurableSet_Icc fun ξ hξ => ?_
  obtain ⟨h0, h1⟩ := hankelBand_w_band hc0 hu0 hu hR0.le hRA hξ
  have hU := hankelBandU_le hc0 h0 (by linarith)
  have hnn : 0 ≤ langerScale c * (Real.pi ^ 2 * ξ - 1) / 2 :=
    div_nonneg (mul_nonneg hK.le h0) (by norm_num)
  show 0 ≤ -hankelBandU c ξ
  linarith

/-- The bridge: `bandB1` of `hankelBandInstance` is the Hankel `B₁` at the instance radius `R`. -/
theorem hankelBoot_bandB1_eq {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1) :
    bandB1 (hankelBandInstance hc hε hf.toIsHankelEigenfn hM hu0 hu3 hRlb hRub
        (fun Δ hΔ => hf.tail_nonneg Δ (by rw [← hT]; exact hΔ))) =
      hankelBootB1 c f R u_T :=
  rfl

/-- The bridge: `bandB2` of `hankelBandInstance` is the Hankel `B₂` at the instance radius `R`. -/
theorem hankelBoot_bandB2_eq {c ε T u_T R : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hf : IsHankelFeasible c ε T f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) (hT : c * hankelXi c u_T = T) (hu0 : u_T ≤ 0)
    (hu3 : -3 ≤ u_T) (hRlb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hRub : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1) :
    bandB2 (hankelBandInstance hc hε hf.toIsHankelEigenfn hM hu0 hu3 hRlb hRub
        (fun Δ hΔ => hf.tail_nonneg Δ (by rw [← hT]; exact hΔ))) =
      hankelBootB2 c f R :=
  rfl

/-- info: 'FormalResearch.SignUncertainty.hankelBootU_xi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootU_xi

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_psi_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_psi_ge

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_dm_setIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_dm_setIntegral

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_R_mul_B1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_R_mul_B1

/-- info: 'FormalResearch.SignUncertainty.hankelBootB1_le_moment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB1_le_moment

/-- info: 'FormalResearch.SignUncertainty.hankelBootMoment_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootMoment_ge

/-- info: 'FormalResearch.SignUncertainty.hankelBootB1_le_B1k' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB1_le_B1k

/-- info: 'FormalResearch.SignUncertainty.hankelBootB1k_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB1k_nonneg

/-- info: 'FormalResearch.SignUncertainty.hankelBootB2_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB2_nonneg

/-- info: 'FormalResearch.SignUncertainty.hankelBootB1_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBootB1_nonneg

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_bandB1_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_bandB1_eq

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_bandB2_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_bandB2_eq

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_abs_uT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_abs_uT

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_mem_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_mem_Icc

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_psiR_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_psiR_cont

/-- info: 'FormalResearch.SignUncertainty.hankelBoot_psiLead_cont' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelBoot_psiLead_cont

end FormalResearch.SignUncertainty

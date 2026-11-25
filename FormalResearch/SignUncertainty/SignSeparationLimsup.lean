module

public import FormalResearch.SignUncertainty.Headlines
public import FormalResearch.SignUncertainty.HbUpperM1

/-!
# The retired separation bound `limsup (T_c^{+1} - T_c^{-1}) ≤ -2/π²` (old `gt:7.9c`)

Paper I no longer states this result: the old `thm:intro-separation` / `gt:7.9c` was deleted from
`CFT/sign_uncertainty/paper/` (archived in QIprojects
`CFT/sign_uncertainty/history/notes/archived_sign_separation.md`). It is superseded by the paper's
`eq:ct-split` (in `thm:ct-upper`): `T_c^{+1} - T_c^{-1} = -1/π + π A c^{-2/3} + O(c^{-3/4})`, which gives
the sharp `limsup = -1/π` (`2/π² < 1/π`). That sharp form needs the five-term bounds (plan milestone M10),
not the intertwiner argument below, and will be a corollary there rather than a separate headline.

The proof goes through `SeparationInputs`, whose one field `hb_thresholds_upper` is now the theorem
`hbThresholdsUpper` (`HbUpperM1.lean`); `separation_neg_two_div_pi_sq_unconditional` records the resulting
unconditional statement. The file is kept because its Hardy–Mellin intertwiner and radial-compactness steps
(`SignSeparation.lean`) are reusable. It is not a Paper I headline and nothing new should be built on it.
Formerly `thm_intro_separation{,_hankel,_radii}` in `Headlines.lean`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial FourierTransform RealInnerProductSpace

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.CohnElkies

/-- Inputs of the retired separation bound (old `gt:7.9c`), Hankel side. -/
structure SeparationInputs : Prop where
  /-- `u1co:O9p` at one level. -/
  hb_thresholds_upper : HbThresholdsUpper

/-! ### The separation bound `limsup (T⁺ - T⁻) ≤ -2/π²` -/

section Separation

variable (I : SeparationInputs)
include I

/-- Feasible thresholds exist for large `c` (`hb_thresholds_upper`) and are bounded below. -/
private lemma neg_nonempty_ev : ∃ c_u : ℝ, ∀ c : ℝ, c_u ≤ c → ∃ T f, IsHankelFeasible c (-1) T f := by
  obtain ⟨C, c_u, h⟩ := I.hb_thresholds_upper
  exact ⟨c_u, fun c hc => by obtain ⟨T, f, hf, -⟩ := h c hc (-1) (Or.inr rfl); exact ⟨T, f, hf⟩⟩

/-- `(T_c^{-1} - c/π²)/c^{1/3} → A` from `radial_rigidity_lower` and `hb_thresholds_upper`. -/
private lemma hankelT_neg_airy_order :
    Tendsto (fun c : ℝ => (hankelT (-1) c - c / π ^ 2) / c ^ (1 / 3 : ℝ)) atTop
      (𝓝 airyOrderCoeff) := by
  obtain ⟨C₂, c_u, hup⟩ := I.hb_thresholds_upper
  have hA := airyOrderCoeff_pos
  have hnn : ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c (-1) T f →
      c / π ^ 2 + (airyOrderCoeff - airyOrderCoeff) * c ^ (1 / 3 : ℝ) ≤ T :=
    radial_rigidity_lower airyOrderCoeff hA
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · -- lower side
    set ε : ℝ := (airyOrderCoeff - a) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    filter_upwards [radial_rigidity_lower ε hεpos, eventually_ge_atTop c_u,
      eventually_gt_atTop (0 : ℝ)] with c hc hcu hc0
    obtain ⟨T₀, f₀, hf₀, -⟩ := hup c hcu (-1) (Or.inr rfl)
    have hge : c / π ^ 2 + (airyOrderCoeff - ε) * c ^ (1 / 3 : ℝ) ≤ hankelT (-1) c :=
      le_csInf ⟨T₀, f₀, hf₀⟩ fun T ⟨f, hf⟩ => hc T f hf
    have hq : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [lt_div_iff₀ hq]
    nlinarith [hge]
  · -- upper side
    have hq0 : Tendsto (fun c : ℝ => C₂ * c ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul C₂
    have hb' : 0 < b - airyOrderCoeff := by linarith
    filter_upwards [hq0.eventually (gt_mem_nhds hb'), hnn, eventually_ge_atTop c_u,
      eventually_gt_atTop (0 : ℝ)] with c hqc hnc hcu hc0
    obtain ⟨T₀, f₀, hf₀, hT₀⟩ := hup c hcu (-1) (Or.inr rfl)
    have hbdd : BddBelow {T : ℝ | ∃ f, IsHankelFeasible c (-1) T f} :=
      ⟨c / π ^ 2 + (airyOrderCoeff - airyOrderCoeff) * c ^ (1 / 3 : ℝ),
        fun T ⟨f, hf⟩ => hnc T f hf⟩
    have hle : hankelT (-1) c ≤ T₀ := csInf_le hbdd ⟨f₀, hf₀⟩
    have hq : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [div_lt_iff₀ hq]
    have hinv : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
      rw [← Real.rpow_add hc0]; norm_num
    have h1 := mul_lt_mul_of_pos_right hqc hq
    rw [mul_assoc, hinv, mul_one] at h1
    nlinarith [h1, hle, hT₀]

/-- `gt:7.5` profile identification with the `C¹` clause of `lem:radial-compactness`: the window profile
`Ψ_{f,c}/M[f]` of a near-optimal `(-1)`-feasible `f` is `C¹` on each window and converges to
`G_Ai/‖G_Ai‖₁` together with its first derivative, locally uniformly. Derived from
`radial_compactness` (the `C¹` clause and the derivative convergence), `radial_rigidity_profile`
(identification of the limit) and the threshold asymptotics from `hb_thresholds_upper`, along a sequence of
counterexamples. -/
theorem SeparationInputs.radial_profile_c1 :
    ∀ R η : ℝ, 0 < η → ∀ᶠ c : ℝ in atTop, ∀ (T : ℝ) (f : ℝ → ℝ),
      IsHankelFeasible c (-1) T f → hankelT (-1) c ≤ T → T ≤ hankelT (-1) c + 1 / c →
        ContDiffOn ℝ 1 (fun u => hankelWindowProfile c f u / hankelMass c f) (Ioo (-R) R) ∧
        ∀ u ∈ Ioo (-R) R,
          |hankelWindowProfile c f u / hankelMass c f - HermiteBiehlerData.airy.normG u| ≤ η ∧
          |deriv (fun v => hankelWindowProfile c f v / hankelMass c f) u -
            deriv HermiteBiehlerData.airy.normG u| ≤ η := by
  intro R η hη
  by_contra hcon
  have hfreq : ∃ᶠ c : ℝ in atTop, ∃ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c (-1) T f ∧
      hankelT (-1) c ≤ T ∧ T ≤ hankelT (-1) c + 1 / c ∧
      ¬ (ContDiffOn ℝ 1 (fun u => hankelWindowProfile c f u / hankelMass c f) (Ioo (-R) R) ∧
        ∀ u ∈ Ioo (-R) R,
          |hankelWindowProfile c f u / hankelMass c f - HermiteBiehlerData.airy.normG u| ≤ η ∧
          |deriv (fun v => hankelWindowProfile c f v / hankelMass c f) u -
            deriv HermiteBiehlerData.airy.normG u| ≤ η) := by
    rw [Filter.not_eventually] at hcon
    refine hcon.mono fun c hc => ?_
    by_contra h
    apply hc
    intro T f hf h1 h2
    by_contra hD
    exact h ⟨T, f, hf, h1, h2, hD⟩
  obtain ⟨ns, hns, hns_prop⟩ := exists_seq_forall_of_frequently hfreq
  choose T f hfeas hlo hhi hbad using hns_prop
  obtain ⟨Rk, hRc, hRT, hRf⟩ := exists_airy_package radial_compactness ns hns T f hfeas
  have hD : -(HermiteBiehlerData.airy.tm / hankelBeta1) = airyOrderCoeff := by
    show -(airyZero 1 / hankelBeta1) = |airyZero 1| / hankelBeta1
    rw [abs_of_neg (airyZero_neg 1), neg_div]
  have hpos : ∀ᶠ n in atTop, 0 < ns n := hns.eventually (eventually_gt_atTop 0)
  have hmul : ∀ c x : ℝ, 0 < c → c ^ (-(1 / 3 : ℝ)) * x = x / c ^ (1 / 3 : ℝ) := fun c x hc => by
    rw [Real.rpow_neg hc.le, inv_mul_eq_div]
  have hAtt0 : Tendsto (fun n => (ns n) ^ (-(1 / 3 : ℝ)) * (T n - ns n / π ^ 2)) atTop
      (𝓝 airyOrderCoeff) := by
    have h1 : Tendsto (fun n => (hankelT (-1) (ns n) - ns n / π ^ 2) / (ns n) ^ (1 / 3 : ℝ))
        atTop (𝓝 airyOrderCoeff) := (hankelT_neg_airy_order I).comp hns
    have h2 : Tendsto (fun n => (ns n) ^ (-(1 / 3 : ℝ)) * (1 / ns n)) atTop (𝓝 0) := by
      have h3 := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp hns
      have h4 := tendsto_inv_atTop_zero.comp hns
      simpa [Function.comp] using h3.mul h4
    have h5 := h1.add h2
    rw [add_zero] at h5
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h5 ?_ ?_
    · filter_upwards [hpos] with n hn
      rw [hmul _ _ hn]
      exact div_le_div_of_nonneg_right (by linarith [hlo n]) (Real.rpow_nonneg hn.le _)
    · filter_upwards [hpos] with n hn
      rw [hmul _ _ hn, hmul _ _ hn, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith [hhi n]) (Real.rpow_nonneg hn.le _)
  have hAtt : Tendsto (fun n => (Rk.c n) ^ (-(1 / 3 : ℝ)) * (Rk.T n - Rk.c n / π ^ 2)) atTop
      (𝓝 (-(HermiteBiehlerData.airy.tm / hankelBeta1))) := by
    rw [hD, hRc, hRT]; exact hAtt0
  have hloc := (radial_rigidity_profile Rk hAtt).1
  simp only [hRc, hRf] at hloc
  obtain ⟨ms, F, C, ν, hms, hloc2, hC1, hder, -, -, -, -, -⟩ :=
    radial_compactness.normalized_compactness (-1) (Or.inr rfl) ns f hns
      (fun n => (hfeas n).toIsHankelEigenfn)
  have hloc3 : TendstoLocallyUniformlyOn (fun k u => hankelWindowProfile (ns (ms k)) (f (ms k)) u /
      hankelMass (ns (ms k)) (f (ms k))) HermiteBiehlerData.airy.normG atTop univ := by
    intro u hu x hx
    obtain ⟨t, ht, h'⟩ := hloc u hu x hx
    exact ⟨t, ht, hms.tendsto_atTop.eventually h'⟩
  have hFre : (fun u : ℝ => (F (u : ℂ)).re) = HermiteBiehlerData.airy.normG := by
    funext u
    exact tendsto_nhds_unique (hloc2.tendsto_at (mem_univ u)) (hloc3.tendsto_at (mem_univ u))
  rw [hFre] at hloc2 hder
  have e1 := Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hloc2 (Icc (-R) R)
      (subset_univ _) isCompact_Icc) η hη
  have e2 := Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hder (Icc (-R) R)
      (subset_univ _) isCompact_Icc) η hη
  obtain ⟨k, hk1, hk2, hk3⟩ := (e1.and (e2.and (hC1 R))).exists
  refine hbad (ms k) ⟨hk3, fun u hu => ⟨?_, ?_⟩⟩
  · have := hk1 u (Ioo_subset_Icc_self hu)
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le
  · have := hk2 u (Ioo_subset_Icc_self hu)
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this.le

/-- The package of `SignSeparationPackage` built from `SeparationInputs`, with its thresholds. -/
private lemma exists_package : ∃ P : SignSeparationPackage, ∀ c : ℝ, P.c₀ ≤ c →
    P.Tpos c = hankelT 1 c ∧ P.Tneg c = hankelT (-1) c := by
  classical
  obtain ⟨c_u, hc_u⟩ := neg_nonempty_ev I
  have hc1 : ∀ c : ℝ, max 1 c_u ≤ c → 1 ≤ c := fun c hc => le_trans (le_max_left _ _) hc
  have hK : ∀ c : ℝ, ∀ hc : max 1 c_u ≤ c,
      (Classical.choose (bessel_kernel_data c (hc1 c hc))).φ = hankelPhi c :=
    fun c hc => Classical.choose_spec (bessel_kernel_data c (hc1 c hc))
  let P : SignSeparationPackage :=
    { c₀ := max 1 c_u
      hc₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
      K := fun c hc => Classical.choose (bessel_kernel_data c (hc1 c hc))
      neg_feasible := fun c hc => by
        obtain ⟨T, f, hf⟩ := hc_u c (le_trans (le_max_right _ _) hc)
        exact ⟨T, f, ((Classical.choose (bessel_kernel_data c (hc1 c hc))).isFeasible_iff
          (hK c hc) (-1) T f).2 hf⟩
      Tneg_airy_order := by
        refine (hankelT_neg_airy_order I).congr' ?_
        filter_upwards [eventually_ge_atTop (max 1 c_u)] with c hc
        simp only [hc, ↓reduceDIte, (Classical.choose (bessel_kernel_data c (hc1 c hc))).threshold_eq
          (hK c hc)]
      c1_profile := fun R η hη => by
        filter_upwards [I.radial_profile_c1 R η hη] with c hcev hc T f hf hT1 hT2
        have hKc := hK c hc
        rw [(Classical.choose (bessel_kernel_data c (hc1 c hc))).isFeasible_iff hKc] at hf
        simp only [(Classical.choose (bessel_kernel_data c (hc1 c hc))).threshold_eq hKc] at hT1 hT2
        exact hcev T f hf hT1 hT2 }
  refine ⟨P, fun c hc => ?_⟩
  have hKc := hK c hc
  have hc' : max 1 c_u ≤ c := hc
  constructor
  · show (if hc' : max 1 c_u ≤ c then hankelThreshold c
        (Classical.choose (bessel_kernel_data c (hc1 c hc'))) 1 else 0) = _
    simp only [hc', ↓reduceDIte, (Classical.choose (bessel_kernel_data c (hc1 c hc))).threshold_eq hKc]
  · show (if hc' : max 1 c_u ≤ c then hankelThreshold c
        (Classical.choose (bessel_kernel_data c (hc1 c hc'))) (-1) else 0) = _
    simp only [hc', ↓reduceDIte, (Classical.choose (bessel_kernel_data c (hc1 c hc))).threshold_eq hKc]

/-- Theorem 7.9c(1) in quantitative form: `T_c^{+1} - T_c^{-1} ≤ -2/π² + ε₀` eventually. -/
private lemma separation_eventually (ε₀ : ℝ) (hε₀ : 0 < ε₀) :
    ∀ᶠ c : ℝ in atTop, hankelT 1 c - hankelT (-1) c ≤ -(2 / π ^ 2) + ε₀ := by
  obtain ⟨P, hP⟩ := exists_package I
  filter_upwards [sign_separation_eventually_le P ε₀ hε₀, eventually_ge_atTop P.c₀] with c hc hc₀
  rw [← (hP c hc₀).1, ← (hP c hc₀).2]
  exact hc

/-- **Separation bound, Hankel form (`gt:7.9c(1)`, `thm:intro-separation`, first line):**
`limsup_{c→∞} (T_c^{+1} - T_c^{-1}) ≤ -2/π²` (limsup in `EReal`, so no coboundedness is assumed).

Proved from `SeparationInputs` (`hb_thresholds_upper`) and the theorem `radial_compactness`
(`radial_rigidity_lower` and `radial_profile_c1` derived), with the Hardy–Mellin intertwiner argument of
`sign_separation_eventually_le`. -/
theorem separation_neg_two_div_pi_sq_hankel :
    Filter.limsup (fun c : ℝ => ((hankelT 1 c - hankelT (-1) c : ℝ) : EReal)) atTop ≤
      ((-(2 / π ^ 2) : ℝ) : EReal) := by
  rw [Filter.limsup_le_iff]
  intro y hy
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hr : -(2 / π ^ 2) < r := EReal.coe_lt_coe_iff.1 hr1
  filter_upwards [separation_eventually I ((r + 2 / π ^ 2) / 2) (by linarith)] with c hc
  refine lt_trans (EReal.coe_lt_coe_iff.2 ?_) hr2
  linarith

end Separation

section SeparationEuclid

variable (I : SeparationInputs)
include I

/-- For large `c`, the exact origin option does not change `T_c^{-1}` (`gt:7.9b`). -/
private lemma neg_T0_eq_ev : ∀ᶠ c : ℝ in atTop, hankelT0 c = hankelT (-1) c := by
  obtain ⟨c_u, hc_u⟩ := neg_nonempty_ev I
  filter_upwards [radial_rigidity_lower airyOrderCoeff airyOrderCoeff_pos,
    eventually_ge_atTop (max 1 c_u), eventually_gt_atTop (0 : ℝ)] with c hc hcu hc0
  have hc1 : 1 ≤ c := le_trans (le_max_left _ _) hcu
  have hne := hc_u c (le_trans (le_max_right _ _) hcu)
  refine hankelT0_eq_hankelT hc0 (bessel_kernel_data c hc1) (laguerre_odd_mode (by linarith)) hne ?_
  have hge : c / π ^ 2 + (airyOrderCoeff - airyOrderCoeff) * c ^ (1 / 3 : ℝ) ≤ hankelT (-1) c :=
    le_csInf hne fun T ⟨f, hf⟩ => hc T f hf
  have h4 : 1 / (4 * π) < 1 / π ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.pi_gt_three, Real.pi_lt_four]
  have := mul_lt_mul_of_pos_left h4 hc0
  have e1 : c / π ^ 2 = c * (1 / π ^ 2) := by ring
  have e2 : c / (4 * π) = c * (1 / (4 * π)) := by ring
  rw [sub_self, zero_mul, add_zero] at hge
  linarith

/-- **Separation bound, Euclidean form (`gt:7.9c(2)`, `thm:intro-separation`, second line):**
`limsup_{d→∞} ½(A_sign^+(d)² - A_sign^-(d)²) ≤ -2/π²` (integer `d`, limsup in `EReal`).

From `separation_neg_two_div_pi_sq_hankel`'s inputs and the dictionary `hankel_euclid_dictionary`
(`EuclidRadialProjection.lean`): `A_sign^+(d)²/2 = T_{d/2}^{+1}` and `A_sign^-(d)²/2 = T_{d/2}^{-1,0} =
T_{d/2}^{-1}` for large `d`. -/
theorem separation_neg_two_div_pi_sq_radii :
    Filter.limsup (fun d : ℕ => (((aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 : ℝ) : EReal)) atTop ≤
      ((-(2 / π ^ 2) : ℝ) : EReal) := by
  have hc_tend : Tendsto (fun d : ℕ => (d : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)
  rw [Filter.limsup_le_iff]
  intro y hy
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hr : -(2 / π ^ 2) < r := EReal.coe_lt_coe_iff.1 hr1
  filter_upwards [hc_tend.eventually (separation_eventually I ((r + 2 / π ^ 2) / 2) (by linarith)),
    hc_tend.eventually (neg_T0_eq_ev I), eventually_ge_atTop 2] with d hd hT0 hd2
  refine lt_trans (EReal.coe_lt_coe_iff.2 ?_) hr2
  obtain ⟨hp, hn⟩ := hankel_euclid_dictionary d hd2
  have : (aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 =
      hankelT 1 ((d : ℝ) / 2) - hankelT (-1) ((d : ℝ) / 2) := by
    rw [← hT0, ← hn, ← hp]; ring
  rw [this]
  linarith

end SeparationEuclid

/-- **Retired separation bound** (old `gt:7.9c`): both lines of the old `eq:intro-separation`. -/
theorem separation_neg_two_div_pi_sq (I : SeparationInputs) :
    Filter.limsup (fun c : ℝ => ((hankelT 1 c - hankelT (-1) c : ℝ) : EReal)) atTop ≤
        ((-(2 / π ^ 2) : ℝ) : EReal) ∧
    Filter.limsup (fun d : ℕ => (((aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 : ℝ) : EReal)) atTop ≤
        ((-(2 / π ^ 2) : ℝ) : EReal) :=
  ⟨separation_neg_two_div_pi_sq_hankel I, separation_neg_two_div_pi_sq_radii I⟩

/-- `SeparationInputs` holds: its only field is the theorem `hbThresholdsUpper`. -/
theorem separationInputs_holds : SeparationInputs := ⟨hbThresholdsUpper⟩

/-- **Retired separation bound, unconditional** (old `gt:7.9c`, deleted from Paper I; superseded by the
sharp `eq:ct-split`, `T⁺ - T⁻ → -1/π`): `limsup (T_c^{+1} - T_c^{-1}) ≤ -2/π²` and the Euclidean form
`limsup (A_sign^+(d)² - A_sign^-(d)²)/2 ≤ -2/π²`. -/
theorem separation_neg_two_div_pi_sq_unconditional :
    Filter.limsup (fun c : ℝ => ((hankelT 1 c - hankelT (-1) c : ℝ) : EReal)) atTop ≤
        ((-(2 / π ^ 2) : ℝ) : EReal) ∧
    Filter.limsup (fun d : ℕ => (((aSignPos d ^ 2 - aSignNeg d ^ 2) / 2 : ℝ) : EReal)) atTop ≤
        ((-(2 / π ^ 2) : ℝ) : EReal) :=
  separation_neg_two_div_pi_sq separationInputs_holds

/-! ### Axiom checks -/

/-- info: 'FormalResearch.SignUncertainty.separation_neg_two_div_pi_sq_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separation_neg_two_div_pi_sq_hankel

/-- info: 'FormalResearch.SignUncertainty.separation_neg_two_div_pi_sq_radii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separation_neg_two_div_pi_sq_radii

/-- info: 'FormalResearch.SignUncertainty.separation_neg_two_div_pi_sq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separation_neg_two_div_pi_sq

/-- info: 'FormalResearch.SignUncertainty.SignSeparationPackage.langer_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SignSeparationPackage.langer_approx

/-- info: 'FormalResearch.SignUncertainty.separation_neg_two_div_pi_sq_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms separation_neg_two_div_pi_sq_unconditional

end FormalResearch.SignUncertainty

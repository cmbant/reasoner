module

public import Mathlib
public import FormalResearch.SignUncertainty.CtRoscSubst
public import FormalResearch.SignUncertainty.CtTransBand

/-!
# `ct:dyadic` (4), `(ct:rosc)`: the mass identity `∫ W₆ f_c = ε f(0) - M_all + small` (pieces `T2`-`T5` of `CtRoscBook`)

`constant_terms_lower.tex`, `ct:dyadic` (4) (proof of `(ct:combined)`, `gt:7.7p` (b), (c), `(ct:gvac-def)`).  With `W₆(u) = (1 - (u/R)^{12})²`, `1 - W₆(u) = w_R(|u|)` on `[-R, R]`
(`taperW`), the quantity `∫_{-R}^R W₆ f_c` is expanded as

`∫_{-R}^R f_c - ∫_{-R}^0 w_R(-u) f_c - ∫_0^R w_R(u) f_c`,

* `∫_{-R}^R f_c = ∫_{-R'}^{φ(R)} Re Ψ̃ dx` (`x = φ_c(u)`, `ctPhiR_subst`) `= ∫_{cξ(φ R)}^{cξ(-R')} ρ₀ f + O((R' + φ R) r_∞)` (`ct_psi_mass`);
* `ε f(0) = ∫_{cξ(a)}^{cξ(-R')} ρ₀ f + ∫_{Δ > cξ(-R')} ρ₀ f + (lobe)` (`ct_mass_split`: the mass identity `∫_0^∞ ρ₀ f = ε f(0)` and `deep_lobe_mass_thm` at `x = φ(R)`);
* `M_all = ∫_{(0,Λ)} w̃ h + ∫_{L > Λ} h` (`ctMall_split`), `∫_{L > Λ} h = ∫_{Δ > cξ(-R')} ρ₀ f` (`hankelHL_tail_eq`);
* `∫_{-R}^0 w_R(-u) f_c = ∫_{-R'}^0 w_R(-û x) Re Ψ̃ dx + (strip)` (`neg_decomp`) `= ∫_{(0,Λ)} w̃ h + O(R' r_∞) + (strip)` (`ct_trans_transport`, `ctTaper_eq`).

`ct_rosc_mass` collects the identity; the positive lobe `∫_0^R w_R f_c` (`pos_lobe_le`) is treated in `CtRoscPos`.

All proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- **The tail of `dm` in the Hankel variable**: for `ξ₀ > 0`, `∫_{L > log π²ξ₀} h(L) dL = ∫_{Δ > cξ₀} ρ₀ f`. -/
lemma hankelHL_tail_eq {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) {ξ₀ : ℝ} (hξ : 0 < ξ₀) :
    ∫ L in Ioi (Real.log (π ^ 2 * ξ₀)), hankelHL c f L = ∫ u in Ioi (c * ξ₀), hankelRho0 c u * f u := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  have key := integral_logvar c f (fun ξ => (Ioi ξ₀).indicator (fun _ => (1 : ℝ)) ξ)
  have h1 : (fun L => (Ioi ξ₀).indicator (fun _ => (1 : ℝ)) (Real.exp L / π ^ 2) * hankelHL c f L) =
      (Ioi (Real.log (π ^ 2 * ξ₀))).indicator (hankelHL c f) := by
    funext L
    have hiff : ξ₀ < Real.exp L / π ^ 2 ↔ Real.log (π ^ 2 * ξ₀) < L := by
      rw [lt_div_iff₀ hpi, Real.log_lt_iff_lt_exp (by positivity)]
      constructor <;> intro h <;> linarith
    by_cases hL : Real.log (π ^ 2 * ξ₀) < L
    · simp [Set.indicator_of_mem, hL, hiff.2 hL]
    · have : ¬ ξ₀ < Real.exp L / π ^ 2 := fun h => hL (hiff.1 h)
      simp [Set.indicator_of_notMem, hL, this]
  rw [h1, integral_indicator measurableSet_Ioi] at key
  rw [key]
  have h2 : ∫ ξ in Ioi (0 : ℝ), (Ioi ξ₀).indicator (fun _ => (1 : ℝ)) ξ * hankelDmDens c f ξ =
      ∫ ξ in Ioi ξ₀, hankelDmDens c f ξ := by
    have : (fun ξ => (Ioi ξ₀).indicator (fun _ => (1 : ℝ)) ξ * hankelDmDens c f ξ) =
        (Ioi ξ₀).indicator (hankelDmDens c f) := by
      funext ξ
      by_cases hξ' : ξ₀ < ξ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hξ']
    rw [this, setIntegral_indicator measurableSet_Ioi, Set.inter_eq_right.2 (Ioi_subset_Ioi hξ.le)]
  rw [h2]
  unfold hankelDmDens
  have h3 := integral_comp_mul_left_Ioi (fun u => hankelRho0 c u * f u) ξ₀ hc
  have h4 : ∫ ξ in Ioi ξ₀, c * (f (c * ξ) * hankelRho0 c (c * ξ)) =
      c * ∫ ξ in Ioi ξ₀, hankelRho0 c (c * ξ) * f (c * ξ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ _ => ?_
    ring
  rw [h4, h3, smul_eq_mul]
  field_simp

/-- **`M_all` is the taper mass on `(0, Λ)` plus the tail**: `M_all = ∫_{(0,Λ)} w̃ h + ∫_{L > Λ} h` (`w̃ = 0` for `L ≤ 0`, `w̃ = 1` for `L > Λ`). -/
lemma ctMall_split {ε c R : ℝ} {f : ℝ → ℝ} (hc : 0 < c) (hB : TaperBand ε c R) (hf : IsHankelEigenfn c ε f) :
    ctMall R ε c f = (∫ L in Ioo 0 (ctTaperLam ε c R), ctTaper ε c R L * hankelHL c f L) +
      ∫ L in Ioi (ctTaperLam ε c R), hankelHL c f L := by
  have hR := hB.inputs.R_pos
  have hI := integrable_ctTaper_mul hc hB hf
  have hΛ := hB.inputs.Lam_pos
  unfold ctMall
  have e1 := integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hI
  rw [compl_Iic] at e1
  have e2 : ∫ L in Iic (0 : ℝ), ctTaper ε c R L * hankelHL c f L = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun L hL => by
      simp [ctTaper, mem_Iic.1 hL]
  have hI0 := hI.integrableOn (s := Ioi (0 : ℝ))
  have e3 : ∫ L in Ioi (0 : ℝ), ctTaper ε c R L * hankelHL c f L =
      (∫ L in Ioc 0 (ctTaperLam ε c R), ctTaper ε c R L * hankelHL c f L) +
        ∫ L in Ioi (ctTaperLam ε c R), ctTaper ε c R L * hankelHL c f L := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hI.integrableOn) (hI.integrableOn),
      Ioc_union_Ioi_eq_Ioi hΛ.le]
  have e4 : ∫ L in Ioi (ctTaperLam ε c R), ctTaper ε c R L * hankelHL c f L =
      ∫ L in Ioi (ctTaperLam ε c R), hankelHL c f L := by
    refine setIntegral_congr_fun measurableSet_Ioi fun L hL => ?_
    have hL' : ctTaperLam ε c R < L := hL
    have hL0 : ¬ L ≤ 0 := not_le.2 (hΛ.trans hL')
    have hLΛ : ¬ L ≤ ctTaperLam ε c R := not_le.2 hL'
    simp [ctTaper, hL0, hLΛ, taperW_of_ge hR le_rfl]
  rw [integral_Ioc_eq_integral_Ioo] at e3
  linarith

/-- On `(0, Λ]` the taper is `w_R(-û(-v'(L)))`. -/
lemma ctTaper_eq {ε c R L : ℝ} (hc : 0 < c) (hr0 : 0 ≤ ctRprime ε c R) (hrA : ctRprime ε c R ≤ langerRadius c)
    (hL0 : 0 < L) (hLΛ : L ≤ ctTaperLam ε c R) :
    ctTaper ε c R L = taperW R (-ctUhat ε c (-(ctVprime c L))) := by
  rw [← ctTaperV_eq hc hr0 hrA hL0 hLΛ]
  simp [ctTaper, not_le.2 hL0, hLΛ]

/-- **Taper transport on `(-R', 0)`** (`gt:7.7p` (b), `ct_trans_transport` with `G = w_R(-û(·))`):
`|∫_{(-R',0)} w_R(-û x) Re Ψ̃ dx - ∫_{(0,Λ)} w̃ h| ≤ R' r_∞`. -/
lemma ct_taper_transport {ε c C ρ M R : ℝ} {f : ℝ → ℝ} (X : CtRoscCtx ε c C ρ M f) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) :
    |(∫ x in Ioo (-ctRprime ε c R) 0, taperW R (-ctUhat ε c x) * hankelPsiR c f x) -
      ∫ L in Ioo 0 (ctTaperLam ε c R), ctTaper ε c R L * hankelHL c f L| ≤ ctRprime ε c R * hankelRinf c := by
  have hc0 := X.c_pos
  have hRp := ctRprime_bounds X.H X.W hR1 hRm
  have hA : ctRmax ctChartC1 c < langerRadius c := by
    have := X.H.Rm_add_lt
    have : 0 ≤ C * c ^ (-(1 / 3 : ℝ)) := mul_nonneg X.H.C_nn (Real.rpow_nonneg hc0.le _)
    linarith
  have hr0 : 0 < ctRprime ε c R := by linarith [hRp.1]
  have hrA : ctRprime ε c R ≤ langerRadius c := by linarith [hRp.2.1]
  have hR0 : 0 < R := by linarith
  have hG : ∀ x, |taperW R (-ctUhat ε c x)| ≤ 1 := fun x => by
    rw [abs_of_nonneg (taperW_nonneg hR0 _)]; exact taperW_le_one hR0 _
  have hGc : ContinuousOn (fun x => taperW R (-ctUhat ε c x)) (Ico (-ctRprime ε c R) 0) := by
    intro x hx
    have hx0 : x < 0 := hx.2
    have hxw : -ρ < ctMu c * x := X.W.mu_mul_lt hc0 (by linarith [hx.1, hRp.2.1])
    have hU : ContinuousAt (ctUhat ε c) x := (ctUhat_hasDerivAt X.W.win hc0 hx0 hxw).continuousAt
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : Continuous (taperW R) := by unfold taperW taperX; fun_prop
    exact h1.continuousAt.comp hU.neg
  have key := ct_trans_transport (by linarith [X.H.hc] : (5000 : ℝ) ≤ c) X.hf X.hε X.hM hr0 hrA hG hGc
  have hcongr : ∫ L in Ioo 0 (Real.log (π ^ 2 * hankelXi c (-ctRprime ε c R))),
        taperW R (-ctUhat ε c (-ctVprime c L)) * hankelHL c f L =
      ∫ L in Ioo 0 (ctTaperLam ε c R), ctTaper ε c R L * hankelHL c f L := by
    refine setIntegral_congr_fun measurableSet_Ioo fun L hL => ?_
    rw [ctTaper_eq hc0 hr0.le hrA hL.1 hL.2.le]
  rw [hcongr] at key
  exact key

/-- **The mass identity of `(ct:rosc)`** (`ct:dyadic` (4), proof of `(ct:combined)`, expansion of `I_R(H)`): at `1 < R ≤ R_max` with `k φ(R) ≥ 1`,
`|∫_{-R}^R (1 - w_R(|u|)) f_c - ε f(0) + M_all|` is bounded by
the three transport errors `(φ(R) + 2R') r_∞`, the edge strip `2(λM/R)^{12}(1 + 2A r_∞)`, the lobe `8(e^{-5(kφ(R))^{3/2}} + e^{-c/25})` and the positive
lobe piece `|∫_0^R w_R f_c|`. -/
lemma ct_rosc_mass {ε c C ρ M R : ℝ} {f : ℝ → ℝ} (X : CtRoscCtx ε c C ρ M f) (hR1 : 1 < R)
    (hRm : R ≤ ctRmax ctChartC1 c) (hk : 1 ≤ langerLobeK * ctPhiR ε c R) :
    |(∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u) - ε * f 0 + ctMall R ε c f| ≤
      (ctPhiR ε c R + ctRprime ε c R) * hankelRinf c + ctRprime ε c R * hankelRinf c +
        2 * (ctLam c * M / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) +
        8 * (Real.exp (-5 * (langerLobeK * ctPhiR ε c R) ^ (3 / 2 : ℝ)) + Real.exp (-(1 / 25) * c)) +
        |∫ u in Ioo 0 R, taperW R u * ctFr ε c f u| := by
  have hc0 := X.c_pos
  have hc3 : (3e6 : ℝ) ≤ c := X.H.hc
  have hRp := ctRprime_bounds X.H X.W hR1 hRm
  have hR0 : 0 < R := by linarith
  have hAlt : ctRmax ctChartC1 c < langerRadius c := by
    have := X.H.Rm_add_lt
    have : 0 ≤ C * c ^ (-(1 / 3 : ℝ)) := mul_nonneg X.H.C_nn (Real.rpow_nonneg hc0.le _)
    linarith
  set Rp := ctRprime ε c R with hRpdef
  set a := ctPhiR ε c R with hadef
  set δ := ctLam c * M with hδdef
  have hδ0 : 0 ≤ δ := mul_nonneg (ctLam_pos hc0).le X.W.win.2.1
  have haA : |a| ≤ langerRadius c := (X.H.abs_ctPhiR_lt (by rw [abs_of_pos hR0]; exact hRm)).le
  have ha0 : 0 ≤ a := by
    by_contra h
    push Not at h
    have := mul_neg_of_pos_of_neg langerLobeK_pos h
    linarith
  have hr0 : 0 ≤ Rp := by linarith [hRp.1]
  have hrA : Rp ≤ langerRadius c := by linarith [hRp.2.1]
  have hra : |-Rp| ≤ langerRadius c := by rw [abs_neg, abs_of_nonneg hr0]; exact hrA
  have hB : TaperBand ε c R := taperBand_of_window X.W.win (by linarith) X.W.cM X.W.lam hR1.le
    (X.W.mu_mul_lt hc0 (by linarith)) (by linarith)
  -- (1) the substitution `x = φ(u)` for `∫ f_c`
  have hFr : ∫ u in Ioo (-R) R, ctFr ε c f u = ∫ x in (-Rp)..a, hankelPsiR c f x := by
    have h1 := X.H.ctPhiR_subst (a := -R) (b := R) (by linarith) hRm (by linarith) (hankelPsiR c f)
    rw [ctPhiR_neg_R X.H X.W hR1 hRm] at h1
    rw [intervalIntegral.integral_of_le (by linarith [hRp.1, ha0]), integral_Ioc_eq_integral_Ioo, h1]
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    unfold ctFr; ring
  -- (2) Hankel variable
  have e1 := ct_psi_mass hc3 X.hf X.hε X.hM haA hra (by linarith [hRp.1] : -Rp ≤ a)
  -- (3) mass identity
  have e4 := ct_mass_split hc3 X.hf X.hε X.hM ha0 (abs_le.1 haA).2 hr0 hrA hk
  -- (4) `M_all`
  have hξ0 : 0 < hankelXi c (-Rp) := hankelXi_pos hc0 hra
  have hMall := ctMall_split hc0 hB X.hf
  have hTl : ∫ L in Ioi (ctTaperLam ε c R), hankelHL c f L = ∫ u in Ioi (c * hankelXi c (-Rp)), hankelRho0 c u * f u :=
    hankelHL_tail_eq hc0 f hξ0
  -- (5) taper transport
  have e3 := ct_taper_transport X hR1 hRm
  -- (6) negative half
  set g : ℝ → ℝ := fun u => taperW R (-u) * ctFr ε c f u with hg
  have hmeas : AEStronglyMeasurable (fun u => taperW R (-u)) volume := by
    have h1 : Continuous (taperW R) := by unfold taperW taperX; fun_prop
    exact (h1.comp continuous_neg).aestronglyMeasurable
  have hint : IntegrableOn g (Ioo (-R) 0) :=
    (X.integrableOn_ctFr (a := -R) (b := 0) (by linarith) (by linarith [X.H.Rm_pos])).bdd_mul (c := 1)
      hmeas.restrict (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (taperW_nonneg hR0 _)]; exact taperW_le_one hR0 _)
  have e2 := X.neg_decomp hR1 hRm hint
  have hsubst : ∫ x in Ioo (-Rp) 0, ctUhatD ε c x * g (ctUhat ε c x) =
      ∫ x in Ioo (-Rp) 0, taperW R (-ctUhat ε c x) * hankelPsiR c f x := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [hg]
    rw [← ctFr_ctUhat X.H X.W f hR1 hRm hx]; ring
  have hstrip : ∫ u in Ioo (-δ) 0, |g u| ≤ 2 * (δ / R) ^ 12 * (1 + 2 * langerRadius c * hankelRinf c) := by
    refine X.strip_le hR1 hRm (by positivity) fun u hu => ?_
    simp only [hg]
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [abs_of_nonneg (taperW_nonneg hR0 _)]
    refine (taperW_le_pow hR0 (by linarith [hu.2] : 0 ≤ -u)).trans ?_
    have : (-u / R) ≤ δ / R := div_le_div_of_nonneg_right (by linarith [hu.1]) hR0.le
    have h0 : 0 ≤ -u / R := div_nonneg (by linarith [hu.2]) hR0.le
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 this 12) (by norm_num)
  -- (7) splitting of the weighted integral
  have hTint : IntegrableOn (fun u => taperW R |u| * ctFr ε c f u) (Ioo (-R) R) := by
    have h1 : Continuous (taperW R) := by unfold taperW taperX; fun_prop
    exact ((X.integrableOn_ctFr (by linarith) hRm).bdd_mul (c := 1)
      (h1.comp continuous_abs).aestronglyMeasurable.restrict (Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (taperW_nonneg hR0 _)]; exact taperW_le_one hR0 _))
  have hI1 : IntegrableOn (ctFr ε c f) (Ioo (-R) R) := X.integrableOn_ctFr (by linarith) hRm
  have hsplitT : ∫ u in Ioo (-R) R, taperW R |u| * ctFr ε c f u =
      (∫ u in Ioo (-R) 0, g u) + ∫ u in Ioo 0 R, taperW R u * ctFr ε c f u := by
    have hU : Ioc (-R) 0 ∪ Ioc 0 R = Ioc (-R) R := Ioc_union_Ioc_eq_Ioc (by linarith) hR0.le
    have hTI : IntegrableOn (fun u => taperW R |u| * ctFr ε c f u) (Ioc (-R) R) := by
      have := hTint
      rwa [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc] at this
    rw [integral_Ioc_eq_integral_Ioo.symm, ← hU,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (hTI.mono_set (by rw [← hU]; exact subset_union_left))
        (hTI.mono_set (by rw [← hU]; exact subset_union_right)),
      integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
    congr 1
    · refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      simp only [hg]; rw [abs_of_neg hu.2]
    · refine setIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
      rw [abs_of_pos hu.1]
  have hsplitI : ∫ u in Ioo (-R) R, (1 - taperW R |u|) * ctFr ε c f u =
      (∫ u in Ioo (-R) R, ctFr ε c f u) - ∫ u in Ioo (-R) R, taperW R |u| * ctFr ε c f u := by
    rw [← integral_sub hI1 hTint]
    refine setIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    ring
  -- assemble
  rw [hsplitI, hsplitT, hFr, hMall, hTl]
  rw [hsubst] at e2
  have e1' : |(∫ x in (-Rp)..a, hankelPsiR c f x) -
      ∫ u in (c * hankelXi c a)..(c * hankelXi c (-Rp)), hankelRho0 c u * f u| ≤ (a + Rp) * hankelRinf c := by
    simpa [sub_neg_eq_add] using e1
  have e2' := e2.trans hstrip
  have hP := neg_abs_le (∫ u in Ioo 0 R, taperW R u * ctFr ε c f u)
  have hP' := le_abs_self (∫ u in Ioo 0 R, taperW R u * ctFr ε c f u)
  rw [abs_le] at e1' e4 e3 e2' ⊢
  constructor <;> linarith [e1'.1, e1'.2, e4.1, e4.2, e3.1, e3.2, e2'.1, e2'.2]

/-- info: 'FormalResearch.SignUncertainty.ct_rosc_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_rosc_mass

/-- info: 'FormalResearch.SignUncertainty.ct_taper_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_taper_transport

/-- info: 'FormalResearch.SignUncertainty.hankelHL_tail_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelHL_tail_eq

end FormalResearch.SignUncertainty

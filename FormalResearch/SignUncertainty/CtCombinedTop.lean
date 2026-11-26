module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicCombined
public import FormalResearch.SignUncertainty.CtBoasEventual
public import FormalResearch.SignUncertainty.CtOuterBandFinal

/-!
# `ct:dyadic` (4): the steps of `(ct:combined)` that need only the top-scale moments

`CtCombinedPieces` (`CtDyadicCombined`) lists the five steps of the proof of `(ct:combined)`.  This file proves those that use only the
top-scale moments `∫_{(0,L_J]} v'|h| ≤ K c^{1/3}` and `∫_{L>L_J}|h| ≤ K c^{-1/3}` of `ct_boas_moments_top` (so no scale-`r` bootstrap):

* `ct_combined_trunc` (`CtCombinedPieces.trunc`): `|∫ w̃ dm - ∫_{ξ ≥ ξ(-v₀)} w̃ dm| = O(c^{-29/21})`, from `boas_field_trunc_lo` with `𝔰 = 0`;
* `ct_outer_pointwise` (`ct:cfu` (2) for `dualK` at `ξ = e^L/π²`, identifying `dualK`, `boasX` with the outer-band `τ₀`) and `ct_combined_outer`
  (`CtCombinedPieces.outer`): `∫_{ξ>ξ(-R')} K dm = -∫_{ξ>ξ(-R')} sin X dm + O(c^{-4/3})`, with `B₂(R') = O(c^{-1/3})` the Chebyshev tail of the first moment;
* `CtCombinedOpen`, `ct_lower_of_open`: the three steps still open (`rosc`, `window`, `trans`) as the named inputs of `thm:ct-lower`.

**Proved**, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- **`CtCombinedPieces.trunc`** (`ct:dyadic` (1), taper estimate, used in the proof of `(ct:combined)`): for small `c₁`,
`|∫ w̃_R dm - ∫_{ξ ≥ ξ(-v₀)} w̃_R dm| ≤ 2^{12}(K+1)c₁^{-24} c^{-29/21} ≤ C c^{-4/3} log c`. -/
theorem ct_combined_trunc : ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
    CtDyadicBound c₁ fun R ε c f => ctMall R ε c f - ctMtr R ε c f := by
  obtain ⟨K, cM, hK0, hmom⟩ := ct_boas_moments_top
  obtain ⟨κ₀, hκ₀, cL, hcL1, hL⟩ := ctLv0_facts
  obtain ⟨γ, hγ, hband⟩ := taperBand_pm
  refine ⟨min γ (1 / 200), lt_min hγ (by norm_num), fun c₁ hc₁ hc₁le => ?_⟩
  have hc₁3 : c₁ ≤ 1 / 200 := hc₁le.trans (min_le_right _ _)
  obtain ⟨cB, hcB3, hB⟩ := hband c₁ hc₁ (hc₁le.trans (min_le_left _ _))
  have hev : ∀ᶠ c : ℝ in atTop, cM ≤ c ∧ cL ≤ c ∧ cB ≤ c ∧ Real.exp 7 ≤ c ∧
      (2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) := by
    filter_upwards [eventually_ge_atTop cM, eventually_ge_atTop cL, eventually_ge_atTop cB, eventually_ge_atTop (Real.exp 7),
      ev_hcR hc₁] with c h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨2 ^ 12 * (K + 1) / c₁ ^ 24, c₀, fun c hc ε hε T f hf hm hT _hgap R hR _hgood => ?_⟩
  obtain ⟨hcM, hcL, hcB, hc7, hc47, hcR⟩ := hc₀ c hc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc3 : 3 ≤ c := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hlog7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc7
  have hf' := hf.toIsHankelEigenfn
  have hBR : TaperBand ε c R := hB c hcB ε hε R hR.1 hR.2
  have hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith
    nlinarith [hR.2]
  obtain ⟨LJ, Lt, -, hLJe, hLJv, -, hLt0, hLtLJ, -, -, -, -, hMom, -⟩ := hmom c ε T f hcM hf hε hm hT
  obtain ⟨hL0, hLe, hLv, -⟩ := hL c hcL
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf'
  have hmass1 : ∫ L, |hankelHL c f L| = 1 := by rw [integral_abs_hankelHL hc0 hf', hm]
  have hLJ0 : 0 ≤ LJ := hLt0.trans hLtLJ
  obtain ⟨hΛJ, -⟩ := boas_geometry hc0 hBR hLJ0 hLJe hLJv hRhi
  have hLΛ : ctLv0 c ≤ ctTaperLam ε c R := lmin_le_lam hc0 hBR hL0.le hLe hLv (hcR.trans hR.1)
  have key := boas_field_trunc_lo (sf := fun _ => 0) (fun L => ⟨le_rfl, zero_le_one⟩) hc3 hBR hc₁ hR.1 hh hmass1 hL0 hLe
    hLv hLΛ (hLΛ.trans hΛJ) hLJe hK0 hMom
  -- `M_all - M_tr = ∫_{L < L_min} w̃ h`
  have hI1 := integrable_ctTaper_mul hc0 hBR hf'
  have hsplit := integral_add_compl (measurableSet_Ici (a := ctLv0 c)) hI1
  rw [compl_Ici] at hsplit
  have e1 : ctMall R ε c f - ctMtr R ε c f = ∫ L in Iio (ctLv0 c), ctTaper ε c R L * hankelHL c f L := by
    unfold ctMall ctMtr; linarith
  have e2 : |∫ L in Iio (ctLv0 c), ctTaper ε c R L * hankelHL c f L| ≤
      ∫ L in Iio (ctLv0 c), ctTaper ε c R L * (1 - 0) * |hankelHL c f L| := by
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    refine setIntegral_congr_fun measurableSet_Iio fun L _ => ?_
    simp only [abs_mul, sub_zero, mul_one, abs_of_nonneg (hBR.inputs.reg.mem L).1]
  -- the rate
  have hpow : c ^ (-(29 / 21) : ℝ) ≤ c ^ (-(4 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hC0 : 0 ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 := by positivity
  have hcp : 0 ≤ c ^ (-(4 / 3) : ℝ) := (Real.rpow_pos_of_pos hc0 _).le
  have hη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R :=
    mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f (le_trans (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hc0.le _)) hR.1))
  calc |ctMall R ε c f - ctMtr R ε c f| ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) := by
        rw [e1]; exact e2.trans key
    _ ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
        refine mul_le_mul_of_nonneg_left (hpow.trans ?_) hC0
        nlinarith
    _ ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) * Real.log c) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0

/-- info: 'FormalResearch.SignUncertainty.ct_combined_trunc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined_trunc

/-! ### The outer band -/

/-- **`ct:cfu` (2) for `dualK` in the variable `L`** (`(ct:K-outer)`): for `c ≥ 2`, `ε = ±1`, `L > 0` with `μ₀ = c min(1, L^{3/2}) ≥ M`,
`|K_ε(ξ(L);c) + sin X(L)| ≤ K'/μ₀`, `X = cΦ_Ph(τ₀;L) - θ_ε(τ₀)` (`boasX`). -/
theorem ct_outer_pointwise : ∃ M K' : ℝ, 0 < M ∧ 0 ≤ K' ∧ ∀ {c ε L : ℝ}, 2 ≤ c → (ε = 1 ∨ ε = -1) → 0 < L →
    M ≤ c * min 1 (L * Real.sqrt L) →
    |CtDual.dualK ε c (Real.exp L / π ^ 2) + Real.sin (boasX c ε L)| ≤ K' / (c * min 1 (L * Real.sqrt L)) := by
  have key : ∀ {ε : ℝ}, (ε = -1 ∨ ε = 1) → ∃ M K' : ℝ, 0 < M ∧ 0 ≤ K' ∧ ∀ {c L : ℝ}, 2 ≤ c → 0 < L →
      M ≤ c * min 1 (L * Real.sqrt L) →
      |CtDual.dualK ε c (Real.exp L / π ^ 2) + Real.sin (boasX c ε L)| ≤ K' / (c * min 1 (L * Real.sqrt L)) := by
    intro ε hε
    obtain ⟨M, K, hM, hK, H⟩ := CtOsc.ct_cfu_outer hε
    refine ⟨M, K, hM, hK, fun {c L} hc hL hlarge => ?_⟩
    obtain ⟨τ0, hτ0, hm, I, hI, hb⟩ := H hc hL hlarge
    have hτ : τ0 = tau0 L := hankelEdgeM_strictMonoOn.injOn (mem_Ici.2 hτ0.le) (mem_Ici.2 (tau0_pos hL).le)
      (hm.trans (hankelEdgeM_tau0 hL).symm)
    have hlog : Real.log (π ^ 2 * (Real.exp L / π ^ 2)) = L := by
      rw [show π ^ 2 * (Real.exp L / π ^ 2) = Real.exp L by field_simp, Real.log_exp]
    have hphase : ∀ τ : ℝ, CtSd.phaseL L τ = CtOsc.phaseP τ0 τ := by
      intro τ; unfold CtSd.phaseL CtOsc.phaseP; rw [hm]
    have hdI : CtDual.dualI ε c (Real.exp L / π ^ 2) = I := by
      refine Filter.Tendsto.limUnder_eq (hI.congr fun T => ?_)
      refine intervalIntegral.integral_congr fun τ _ => ?_
      simp only [CtDual.dualP_eq, hlog, hphase]
    have hK : CtDual.dualK ε c (Real.exp L / π ^ 2) = -Real.sqrt (π * c / 12) * I.re := by
      unfold CtDual.dualK; rw [hdI]
    have hX : boasX c ε L = c * (-CtOsc.phaseP τ0 τ0) - CtOuter.outerTheta ε τ0 := by
      unfold boasX
      rw [← hτ, CtCfu.edgePhi_eq]
      unfold CtOsc.phaseP; rw [hm]; ring_nf
    rw [hK, hX]
    have := hb
    rw [sub_neg_eq_add] at this
    exact this
  obtain ⟨M1, K1, hM1, hK1, H1⟩ := key (ε := 1) (Or.inr rfl)
  obtain ⟨M2, K2, hM2, hK2, H2⟩ := key (ε := -1) (Or.inl rfl)
  refine ⟨max M1 M2, max K1 K2, lt_max_of_lt_left hM1, le_max_of_le_left hK1, fun {c ε L} hc hε hL hlarge => ?_⟩
  have hc0 : 0 < c := by linarith
  have hmin : 0 < c * min 1 (L * Real.sqrt L) := by
    have : 0 < L * Real.sqrt L := mul_pos hL (Real.sqrt_pos.2 hL)
    positivity
  rcases hε with rfl | rfl
  · exact (H1 hc hL ((le_max_left _ _).trans hlarge)).trans (div_le_div_of_nonneg_right (le_max_left _ _) hmin.le)
  · exact (H2 hc hL ((le_max_right _ _).trans hlarge)).trans (div_le_div_of_nonneg_right (le_max_right _ _) hmin.le)

/-- info: 'FormalResearch.SignUncertainty.ct_outer_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_pointwise

/-- **`CtCombinedPieces.outer`** (`ct:cfu` (2) with `B₂(R') = O(c^{-1/3})`): for small `c₁`,
`|∫_{ξ>ξ(-R')} K_ε dm + ∫_{ξ>ξ(-R')} sin X dm| ≤ C c^{-4/3}`.  The tail mass `∫_{L>Λ}|h| ≤ C c^{-1/3}` is the Chebyshev tail of the
top-scale first moment (`tail_chebyshev`, `ct_boas_moments_top`), `Λ ≍ 1` from `Rprime_le_Lam`. -/
theorem ct_combined_outer : ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
    CtDyadicBound c₁ fun R ε c f => ctKout R ε c f + ctSout R ε c f := by
  obtain ⟨M, K', hM, hK', Hp⟩ := ct_outer_pointwise
  obtain ⟨K, cM, hK0, hmom⟩ := ct_boas_moments_top
  obtain ⟨γ, hγ, hband⟩ := taperBand_pm
  have hκ := langerKappa_pos
  refine ⟨min γ (1 / 200), lt_min hγ (by norm_num), fun c₁ hc₁ hc₁le => ?_⟩
  have hc₁3 : c₁ ≤ 1 / 200 := hc₁le.trans (min_le_right _ _)
  obtain ⟨cB, hcB3, hB⟩ := hband c₁ hc₁ (hc₁le.trans (min_le_left _ _))
  set lam₀ : ℝ := c₁ ^ 2 / (4 * langerKappa) with hlam₀
  have hlam0 : 0 < lam₀ := by positivity
  set μ₀ : ℝ := min 1 (lam₀ * Real.sqrt lam₀) with hμ₀
  have hμ0 : 0 < μ₀ := lt_min one_pos (mul_pos hlam0 (Real.sqrt_pos.2 hlam0))
  have hev : ∀ᶠ c : ℝ in atTop, cM ≤ c ∧ cB ≤ c ∧ Real.exp 7 ≤ c ∧ M / μ₀ ≤ c ∧ (2 ≤ c ^ (4 / 7 : ℝ) ∧
      c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) := by
    filter_upwards [eventually_ge_atTop cM, eventually_ge_atTop cB, eventually_ge_atTop (Real.exp 7),
      eventually_ge_atTop (M / μ₀), ev_hcR hc₁] with c h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨K' / μ₀ * (2 * K / c₁ ^ 2 + K), c₀, fun c hc ε hε T f hf hm hT _hgap R hR _hgood => ?_⟩
  obtain ⟨hcM, hcB, hc7, hcMμ, hc47, hcR⟩ := hc₀ c hc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc3 : 3 ≤ c := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hlog7 : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc7
  have hf' := hf.toIsHankelEigenfn
  have hBR : TaperBand ε c R := hB c hcB ε hε R hR.1 hR.2
  have hR0 : 0 < R := lt_of_lt_of_le (mul_pos (by positivity) (Real.rpow_pos_of_pos hc0 _)) hR.1
  have hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith
    nlinarith [hR.2]
  obtain ⟨LJ, Lt, -, hLJe, hLJv, -, hLt0, hLtLJ, -, -, -, -, hMom, hTail⟩ := hmom c ε T f hcM hf hε hm hT
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf'
  have hLJ0 : 0 ≤ LJ := hLt0.trans hLtLJ
  obtain ⟨hΛJ, hgeom⟩ := boas_geometry hc0 hBR hLJ0 hLJe hLJv hRhi
  set Λ : ℝ := ctTaperLam ε c R with hΛ
  have hΛ0 : 0 < Λ := hBR.inputs.Lam_pos
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hR1 : 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by linarith
  -- `Λ ≥ λ₀`
  have hΛlow : lam₀ ≤ Λ := by
    have h1 : R - 1 / 2 ≤ 1.0025 * langerScale c * Λ := hBR.Rprime_ge.trans hBR.Rprime_le_Lam
    have h2 : c₁ ^ 2 * c ^ (2 / 3 : ℝ) / 2 ≤ R - 1 / 2 := by linarith [hR.1]
    unfold langerScale at h1
    rw [hlam₀, div_le_iff₀ (by positivity)]
    have h3 : c ^ (2 / 3 : ℝ) * c₁ ^ 2 ≤ c ^ (2 / 3 : ℝ) * (Λ * (4 * langerKappa)) := by
      linarith only [h1, h2, mul_pos (mul_pos hκ h23) hΛ0]
    exact le_of_mul_le_mul_left h3 h23
  -- the pointwise bound on `(Λ, ∞)`
  have hpt : ∀ L ∈ Ioi Λ, ‖(CtDual.dualK ε c (Real.exp L / π ^ 2) + Real.sin (boasX c ε L)) * hankelHL c f L‖ ≤
      K' / (c * μ₀) * |hankelHL c f L| := by
    intro L hL
    have hL0 : 0 < L := hΛ0.trans hL
    have hLl : lam₀ ≤ L := hΛlow.trans (le_of_lt hL)
    have hmin : μ₀ ≤ min 1 (L * Real.sqrt L) :=
      min_le_min le_rfl (mul_le_mul hLl (Real.sqrt_le_sqrt hLl) (Real.sqrt_nonneg _) hL0.le)
    have hlarge : M ≤ c * min 1 (L * Real.sqrt L) := by
      have : M ≤ c * μ₀ := by rwa [div_le_iff₀ hμ0] at hcMμ
      exact this.trans (mul_le_mul_of_nonneg_left hmin hc0.le)
    have := Hp (by linarith : 2 ≤ c) hε hL0 hlarge
    rw [norm_mul, Real.norm_eq_abs]
    refine mul_le_mul ?_ (by rw [Real.norm_eq_abs]) (norm_nonneg _) (by positivity)
    refine this.trans ?_
    exact div_le_div_of_nonneg_left hK' (by positivity) (mul_le_mul_of_nonneg_left hmin hc0.le)
  -- integrals
  have hI1 := integrable_dualK_hankelHL (by linarith : 2 ≤ c) hε hf'
  have hI2 : Integrable (fun L => hankelHL c f L * Real.sin (boasX c ε L)) := by
    have := hh.bdd_mul (c := 1) (Real.measurable_sin.comp (measurable_boasX c ε)).aestronglyMeasurable
      (Eventually.of_forall fun L => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
    exact this.congr (Eventually.of_forall fun L => by simp only [Function.comp_apply]; ring)
  have hsum : ctKout R ε c f + ctSout R ε c f =
      ∫ L in Ioi Λ, (CtDual.dualK ε c (Real.exp L / π ^ 2) + Real.sin (boasX c ε L)) * hankelHL c f L := by
    unfold ctKout ctSout
    rw [← integral_add hI1.integrableOn hI2.integrableOn]
    refine integral_congr_ae (Eventually.of_forall fun L => ?_)
    simp only; ring
  have hmeasg : Integrable (fun L => K' / (c * μ₀) * |hankelHL c f L|) (volume.restrict (Ioi Λ)) :=
    (hh.abs.integrableOn).const_mul _
  have hb1 : |ctKout R ε c f + ctSout R ε c f| ≤ K' / (c * μ₀) * ∫ L in Ioi Λ, |hankelHL c f L| := by
    rw [hsum, ← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le hmeasg ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpt))
  -- the tail mass
  have hR'pos : 0 < R - 1 / 2 := by linarith only [hR.1, hR1]
  have htail := tail_chebyshev (c := c) (Λ := Λ) (R' := R - 1 / 2) (M := K * c ^ (1 / 3 : ℝ)) (B := K * c ^ (-(1 / 3) : ℝ))
    hh hc0 hLJe hΛ0.le hΛJ hR'pos (fun L hL => hgeom L hL.1.le hL.2) hMom hTail
  -- algebra
  set s : ℝ := c ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hc0 _
  have e23 : c ^ (2 / 3 : ℝ) = s * s := by rw [hs, ← Real.rpow_add hc0]; norm_num
  have em13 : c ^ (-(1 / 3) : ℝ) = s⁻¹ := by rw [hs, Real.rpow_neg hc0.le]
  have em43 : c ^ (-(4 / 3) : ℝ) = c⁻¹ * s⁻¹ := by
    calc c ^ (-(4 / 3) : ℝ) = c ^ ((-1 : ℝ) + -(1 / 3)) := by norm_num
      _ = c ^ (-1 : ℝ) * c ^ (-(1 / 3) : ℝ) := Real.rpow_add hc0 _ _
      _ = c⁻¹ * s⁻¹ := by rw [Real.rpow_neg_one, Real.rpow_neg hc0.le]
  rw [em13] at htail
  have hq : K * s / (R - 1 / 2) ≤ 2 * K / c₁ ^ 2 * s⁻¹ := by
    have h2 : c₁ ^ 2 * (s * s) / 2 ≤ R - 1 / 2 := by rw [← e23]; linarith [hR.1]
    rw [div_le_iff₀ hR'pos]
    have : 2 * K / c₁ ^ 2 * s⁻¹ * (R - 1 / 2) ≥ 2 * K / c₁ ^ 2 * s⁻¹ * (c₁ ^ 2 * (s * s) / 2) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e : 2 * K / c₁ ^ 2 * s⁻¹ * (c₁ ^ 2 * (s * s) / 2) = K * s := by
      field_simp
    linarith
  have hmass : ∫ L in Ioi Λ, |hankelHL c f L| ≤ (2 * K / c₁ ^ 2 + K) * s⁻¹ := by
    have := htail.trans (add_le_add_left hq _)
    linarith only [this]
  have hlog1 : 1 ≤ Real.log c := by linarith
  have hη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R :=
    mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hCnn : 0 ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) := by positivity
  have hfin : K' / (c * μ₀) * ∫ L in Ioi Λ, |hankelHL c f L| ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) * (c ^ (-(4 / 3) : ℝ)) := by
    refine (mul_le_mul_of_nonneg_left hmass (by positivity)).trans (le_of_eq ?_)
    rw [em43]; field_simp
  have hX : c ^ (-(4 / 3) : ℝ) ≤ c ^ (-(4 / 3) : ℝ) * Real.log c := by
    exact le_mul_of_one_le_right (Real.rpow_pos_of_pos hc0 (-(4 / 3) : ℝ)).le hlog1
  calc |ctKout R ε c f + ctSout R ε c f| ≤ _ := hb1.trans hfin
    _ ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) * (c ^ (-(4 / 3) : ℝ) * Real.log c) := mul_le_mul_of_nonneg_left hX hCnn
    _ ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) * Real.log c) :=
        mul_le_mul_of_nonneg_left (by linarith) hCnn

/-- info: 'FormalResearch.SignUncertainty.ct_combined_outer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_combined_outer

/-! ### What remains: `CtCombinedOpen` -/

/-- **The three steps of `(ct:combined)` not yet in Lean** (the named inputs of `thm:ct-lower` now; `trunc` and `outer` are proved above):

* `rosc`: `P_R(H) + g_vac/2π + ∫ w̃ dm + 2(s₁ - s₂) = O(c⁻¹η_R)` (`(ct:rosc)`, the half-disc `ap:thmD` with the `R₊ = -ih₊/Ai` comparison
  (P3a), the mass identity `gt:7.7p` (c), the transport `gt:7.7p` (b));
* `window`: `∫_{ξ ≤ ξ(-R')} K dm + s₁ = O(c⁻¹η_R + c^{-4/3} log c)` (`ct:cfu` (1) substituted, `(ct:H2-orth)` (P3b), `(ct:half)`, the sub-chart
  radial compactness);
* `trans`: `∫_{ξ ≥ ξ(-v₀)} w̃ sin X dm - s₂ - ∫_{ξ>ξ(-R')} sin X dm = O(c^{-4/3})` (the transition band: `(ct:theta-cfu-match)`, the transport `gt:7.7p` (b)
  and the first moment). -/
structure CtCombinedOpen (c₁ : ℝ) : Prop where
  rosc : CtDyadicBound c₁ fun R ε c f => ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f)
  window : CtDyadicBound c₁ fun R ε c f => ctKin R ε c f + ctOscS1 R ε c f
  trans : CtDyadicBound c₁ fun R ε c f => ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f

/-- **`thm:ct-lower` from the three open steps of `ct:dyadic` (4)**: `ct_lower` with `CtLowerInputs.dyadic` replaced by `CtCombinedOpen`
(`rosc`, `window`, `trans`); the steps `trunc` and `outer` are `ct_combined_trunc`, `ct_combined_outer`. -/
theorem ct_lower_of_open
    (P : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtCombinedOpen c₁) : CtLowerStatement := by
  obtain ⟨c₁₀, hc₁₀, hP⟩ := P
  obtain ⟨g₁, hg₁, hT⟩ := ct_combined_trunc
  obtain ⟨g₂, hg₂, hO⟩ := ct_combined_outer
  refine ct_lower_of_pieces ⟨min c₁₀ (min g₁ g₂), lt_min hc₁₀ (lt_min hg₁ hg₂), fun c₁ h1 h2 => ?_⟩
  have a1 : c₁ ≤ c₁₀ := h2.trans (min_le_left _ _)
  have a2 : c₁ ≤ g₁ := h2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have a3 : c₁ ≤ g₂ := h2.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨(hP c₁ h1 a1).rosc, hT c₁ h1 a2, (hP c₁ h1 a1).window, hO c₁ h1 a3, (hP c₁ h1 a1).trans⟩

/-- info: 'FormalResearch.SignUncertainty.ct_lower_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower_of_open

end FormalResearch.SignUncertainty

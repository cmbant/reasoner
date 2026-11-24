module

public import FormalResearch.ModularBootstrap.Constants
public import FormalResearch.Analysis.Scheffe
public import FormalResearch.Special.AiryCftSignUncertainty
public import FormalResearch.Special.AiryCftSignEqualityMain
public import FormalResearch.Complex.Hurwitz
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Airy-scale lower bound (Theorem C) and spectral rigidity (Theorem R)

Formalizes `CFT/modular_bootstrap/paper/local_airy_model.tex` (Theorem C) and
`CFT/modular_bootstrap/paper/rigidity.tex` (Theorem R `(R1)`–`(R3)`):

1. **Generalized Scheffé Lemma** (`tendsto_integral_norm_sub_of_tendsto_ae`).
2. **Local `s`-variable sign uncertainty & equality rigidity**
   (`local_sign_uncertainty`, `local_sign_equality`).
3. **Theorem C** (`BlowupFamilyPackage`, `theorem_C_eventually`, `theorem_C`, `theorem_C_real`).
4. **Theorem R** (`RigidityFamilyPackage`, `Att`, `att_tendsto_s1`, `theorem_R1`, `theorem_R2`,
   `theorem_R3`).
5. **Non-vacuity** (`rigidity_hypotheses_nonvacuous`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap

open FormalResearch.Special
open FormalResearch.ArgPrinciple
open FormalResearch.Analysis

/-! ### Section 0: Airy-node scaling helpers and zero-order properties of `phiStar` -/

lemma neg_betaTip_mul_sNode (n : ℕ) : -betaTip * sNode n = airyZero n := by
  unfold sNode
  rw [abs_of_neg (airyZero_neg n)]
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  field_simp

lemma neg_betaTip_mul_s1 : -betaTip * s1 = airyZero 1 := neg_betaTip_mul_sNode 1

lemma sNode_strictAnti_airyZero {n m : ℕ} (hn : 1 ≤ n) (h : n < m) : sNode n < sNode m := by
  unfold sNode
  rw [abs_of_neg (airyZero_neg n), abs_of_neg (airyZero_neg m)]
  exact div_lt_div_of_pos_right (by linarith [airyZero_lt_of_lt hn h]) betaTip_pos

lemma s1_lt_sNode {k : ℕ} (hk : 2 ≤ k) : s1 < sNode k := sNode_strictAnti_airyZero le_rfl hk

lemma Aopt_eq_mul_s1 : Aopt = (2 / 3 : ℝ) * xiStar * s1 := by
  unfold Aopt cStar s1 sNode; ring

lemma two_thirds_xiStar_mul_sNode {k : ℕ} :
    (2 / 3 : ℝ) * xiStar * sNode k = (|airyZero k| / |airyZero 1|) * Aopt := by
  rw [Aopt_eq_mul_s1]; unfold s1 sNode
  have ha1 : |airyZero 1| ≠ 0 := abs_ne_zero.mpr (airyZero_neg 1).ne
  have hb : betaTip ≠ 0 := betaTip_pos.ne'
  field_simp

lemma two_thirds_xiStar_pos : 0 < (2 / 3 : ℝ) * xiStar := by
  have := xiStar_pos; positivity

lemma phiStar_ofReal (s : ℝ) :
    phiStar (s : ℂ) = (((2 * LStar)⁻¹ * (localExtremalC (s : ℂ)).re : ℝ) : ℂ) := by
  unfold phiStar
  rw [localExtremalC_ofReal]
  push_cast
  simp [Complex.ofReal_re]

lemma phiStar_re (s : ℝ) :
    (phiStar (s : ℂ)).re = (2 * LStar)⁻¹ * (localExtremalC (s : ℂ)).re := by
  rw [phiStar_ofReal, Complex.ofReal_re]

lemma phiStar_im (s : ℝ) : (phiStar (s : ℂ)).im = 0 := by
  rw [phiStar_ofReal, Complex.ofReal_im]

lemma phiStar_nonneg {s : ℝ} (hs : s1 ≤ s) : 0 ≤ (phiStar (s : ℂ)).re := by
  rw [phiStar_re]
  have h2L : 0 < 2 * LStar := by have := LStar_pos; positivity
  exact mul_nonneg (inv_nonneg.mpr h2L.le) (localExtremalC_nonneg hs)

lemma phiStar_ne_zero : ∃ z : ℂ, phiStar z ≠ 0 := by
  refine ⟨0, ?_⟩
  unfold phiStar localExtremalC
  have h2L : (2 * (LStar : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr LStar_pos.ne'))
  have hb : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
  have ha : airyExtremal (-(betaTip : ℂ) * 0) ≠ 0 := by
    rw [mul_zero]
    intro h0
    have h1 := airyExtremal_re 0
    have h0' : airyExtremal ((0 : ℝ) : ℂ) = 0 := by simpa using h0
    rw [h0', Complex.zero_re] at h1
    have ha0 := airyAi_pos (le_refl (0 : ℝ))
    have hz := airyZero_neg 1
    have hpos : 0 < airyAi 0 ^ 2 / (0 - airyZero 1) := div_pos (by positivity) (by linarith)
    linarith
  exact mul_ne_zero h2L (mul_ne_zero hb ha)

lemma conj_airyExtremal (u : ℂ) :
    starRingEnd ℂ (airyExtremal u) = airyExtremal (starRingEnd ℂ u) := by
  by_cases hu : u = (airyZero 1 : ℂ)
  · subst hu
    rw [Complex.conj_ofReal]
    unfold airyExtremal
    rw [airyAiC_airyZero]
    simp
  · have huc : starRingEnd ℂ u ≠ (airyZero 1 : ℂ) := fun h => hu <| by
      have := congrArg (starRingEnd ℂ) h
      simpa [Complex.conj_ofReal] using this
    rw [airyExtremal_eq hu, airyExtremal_eq huc]
    simp only [map_neg, map_div₀, map_pow, map_sub, Complex.conj_ofReal, conj_airyAiC]

lemma conj_phiStar (s : ℂ) :
    phiStar (starRingEnd ℂ s) = starRingEnd ℂ (phiStar s) := by
  simp only [phiStar, localExtremalC, map_mul, map_inv₀, map_neg, map_ofNat,
    Complex.conj_ofReal, conj_airyExtremal]

lemma phiStar_eq_zero_iff (s : ℂ) :
    phiStar s = 0 ↔ ∃ k : ℕ, 1 ≤ k ∧ s = (sNode k : ℂ) := by
  have h2L : (2 * (LStar : ℂ))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr LStar_pos.ne'))
  have hb : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
  constructor
  · intro hs
    have ha : airyExtremal (-(betaTip : ℂ) * s) = 0 := by
      unfold phiStar localExtremalC at hs
      exact ((mul_eq_zero.mp hs).resolve_left h2L |> mul_eq_zero.mp).resolve_left hb
    by_cases hu : -(betaTip : ℂ) * s = (airyZero 1 : ℂ)
    · refine ⟨1, le_rfl, ?_⟩
      have hs1 : -(betaTip : ℂ) * (sNode 1 : ℂ) = (airyZero 1 : ℂ) := by
        exact_mod_cast neg_betaTip_mul_sNode 1
      exact mul_left_cancel₀ (neg_ne_zero.mpr hb) (hu.trans hs1.symm)
    · rw [airyExtremal_eq hu] at ha
      have hsq : airyAiC (-(betaTip : ℂ) * s) ^ 2 = 0 := by
        by_contra hnz
        exact div_ne_zero hnz (sub_ne_zero.mpr hu) (neg_eq_zero.mp ha)
      obtain ⟨k, hk, hku⟩ := (airyAiC_eq_zero_iff _).mp (sq_eq_zero_iff.mp hsq)
      have hsk : -(betaTip : ℂ) * (sNode k : ℂ) = (airyZero k : ℂ) := by
        exact_mod_cast neg_betaTip_mul_sNode k
      exact ⟨k, hk, mul_left_cancel₀ (neg_ne_zero.mpr hb) (hku.trans hsk.symm)⟩
  · rintro ⟨k, -, rfl⟩
    unfold phiStar localExtremalC
    have hsk : -(betaTip : ℂ) * (sNode k : ℂ) = (airyZero k : ℂ) := by
      exact_mod_cast neg_betaTip_mul_sNode k
    rw [hsk]
    by_cases hk1 : (airyZero k : ℂ) = (airyZero 1 : ℂ)
    · rw [hk1]; unfold airyExtremal; rw [airyAiC_airyZero]; simp
    · rw [airyExtremal_eq hk1, airyAiC_airyZero]; simp

private lemma analyticOrderAt_airyAiC_zero {k : ℕ} :
    analyticOrderAt airyAiC (airyZero k : ℂ) = 1 := by
  have han : AnalyticAt ℂ airyAiC (airyZero k : ℂ) := differentiable_airyAiC.analyticAt _
  rw [← ENat.natCast_one, han.analyticOrderAt_eq_natCast]
  have hd_diff : Differentiable ℂ (dslope airyAiC (airyZero k : ℂ)) := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).2
      differentiable_airyAiC.differentiableOn z (mem_univ z)).differentiableAt Filter.univ_mem
  refine ⟨dslope airyAiC (airyZero k : ℂ), hd_diff.analyticAt _,
    by rw [dslope_same]; exact airyZero_deriv_ne_zero k, Eventually.of_forall fun u => ?_⟩
  have h := sub_smul_dslope airyAiC (airyZero k : ℂ) u
  rw [airyAiC_airyZero, sub_zero, smul_eq_mul] at h
  simpa [pow_one, smul_eq_mul] using h.symm

private lemma analyticOrderAt_airyExtremal_one :
    analyticOrderAt airyExtremal (airyZero 1 : ℂ) = 1 := by
  have hd1 : Differentiable ℂ (dslope airyAiC (airyZero 1 : ℂ)) := fun z =>
    ((Complex.differentiableOn_dslope Filter.univ_mem).2
      differentiable_airyAiC.differentiableOn z (mem_univ z)).differentiableAt Filter.univ_mem
  have han1 : AnalyticAt ℂ airyAiC (airyZero 1 : ℂ) := differentiable_airyAiC.analyticAt _
  have han2 : AnalyticAt ℂ (dslope airyAiC (airyZero 1 : ℂ)) (airyZero 1 : ℂ) := hd1.analyticAt _
  have heq : airyExtremal = -(airyAiC * dslope airyAiC (airyZero 1 : ℂ)) := rfl
  have h0 : analyticOrderAt (dslope airyAiC (airyZero 1 : ℂ)) (airyZero 1 : ℂ) = 0 := by
    rw [han2.analyticOrderAt_eq_zero, dslope_same]; exact airyZero_deriv_ne_zero 1
  rw [heq, analyticOrderAt_neg, analyticOrderAt_mul han1 han2, analyticOrderAt_airyAiC_zero, h0, add_zero]

private lemma analyticOrderAt_airyExtremal_node {k : ℕ} (hk : 2 ≤ k) :
    analyticOrderAt airyExtremal (airyZero k : ℂ) = 2 := by
  have hne : (airyZero k : ℂ) ≠ (airyZero 1 : ℂ) := fun h => by
    have := airyZero_lt_of_lt (n := 1) (m := k) le_rfl (by omega)
    linarith [Complex.ofReal_injective h]
  have hnhds : airyExtremal =ᶠ[𝓝 (airyZero k : ℂ)]
      ((fun u : ℂ => -(u - (airyZero 1 : ℂ))⁻¹) * airyAiC ^ 2) := by
    filter_upwards [(continuousAt_id.eventually_ne hne)] with u hu
    dsimp only [id_eq] at hu
    change airyExtremal u = -(u - (airyZero 1 : ℂ))⁻¹ * airyAiC u ^ 2
    rw [airyExtremal_eq hu]; ring
  rw [analyticOrderAt_congr hnhds]
  have han_inv : AnalyticAt ℂ (fun u : ℂ => -(u - (airyZero 1 : ℂ))⁻¹) (airyZero k : ℂ) :=
    (analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hne) |>.neg
  have han_Ai : AnalyticAt ℂ airyAiC (airyZero k : ℂ) := differentiable_airyAiC.analyticAt _
  rw [analyticOrderAt_mul han_inv (han_Ai.pow 2),
    han_inv.analyticOrderAt_eq_zero.mpr (by simp [sub_ne_zero.mpr hne]), zero_add,
    analyticOrderAt_pow han_Ai, analyticOrderAt_airyAiC_zero]
  norm_num

private lemma analyticOrderNatAt_phiStar_aux {k m : ℕ}
    (hord : analyticOrderAt airyExtremal (airyZero k : ℂ) = m) :
    analyticOrderNatAt phiStar (sNode k : ℂ) = m := by
  obtain ⟨g, hg, hg0, hfg⟩ := (differentiable_airyExtremal.analyticAt _).analyticOrderAt_eq_natCast.mp hord
  have hsk : -(betaTip : ℂ) * (sNode k : ℂ) = (airyZero k : ℂ) := by
    exact_mod_cast neg_betaTip_mul_sNode k
  have hc0 : ((2 * LStar : ℝ) : ℂ)⁻¹ * (betaTip : ℂ) ≠ 0 := by
    have := LStar_pos; have := betaTip_pos
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast (by positivity : 2 * LStar ≠ 0)))
      (Complex.ofReal_ne_zero.mpr betaTip_pos.ne')
  have hnhds : ∀ᶠ s in 𝓝 (sNode k : ℂ), phiStar s = (s - (sNode k : ℂ)) ^ m *
      ((((2 * LStar : ℝ) : ℂ)⁻¹ * (betaTip : ℂ) * (-(betaTip : ℂ)) ^ m) * g (-(betaTip : ℂ) * s)) := by
    have ht : Tendsto (fun s : ℂ => -(betaTip : ℂ) * s) (𝓝 (sNode k : ℂ)) (𝓝 (airyZero k : ℂ)) := by
      rw [← hsk]
      exact (tendsto_const_nhds (x := -(betaTip : ℂ))).mul tendsto_id
    filter_upwards [ht.eventually hfg] with s hs
    have hphi : phiStar s = ((2 * LStar : ℝ) : ℂ)⁻¹ * (betaTip : ℂ) * airyExtremal (-(betaTip : ℂ) * s) := by
      unfold phiStar localExtremalC; push_cast; ring
    rw [hphi, hs, ← hsk]
    have hfac : -(betaTip : ℂ) * s - -(betaTip : ℂ) * (sNode k : ℂ) = -(betaTip : ℂ) * (s - (sNode k : ℂ)) := by ring
    simp only [smul_eq_mul]; rw [hfac, mul_pow]; ring
  have hgcomp : AnalyticAt ℂ (fun s : ℂ =>
      (((2 * LStar : ℝ) : ℂ)⁻¹ * (betaTip : ℂ) * (-(betaTip : ℂ)) ^ m) * g (-(betaTip : ℂ) * s)) (sNode k : ℂ) :=
    analyticAt_const.mul ((by simpa [hsk] using hg : AnalyticAt ℂ g _).comp (analyticAt_const.mul analyticAt_id))
  have hne0 : (((2 * LStar : ℝ) : ℂ)⁻¹ * (betaTip : ℂ) * (-(betaTip : ℂ)) ^ m) *
      g (-(betaTip : ℂ) * (sNode k : ℂ)) ≠ 0 := by
    rw [hsk]; exact mul_ne_zero (mul_ne_zero hc0 (pow_ne_zero m (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr betaTip_pos.ne')))) hg0
  have hnat := (differentiable_phiStar.analyticAt _).analyticOrderAt_eq_natCast.mpr ⟨_, hgcomp, hne0, hnhds⟩
  simp [analyticOrderNatAt, hnat]

theorem analyticOrderNatAt_phiStar_s1 : analyticOrderNatAt phiStar (s1 : ℂ) = 1 :=
  analyticOrderNatAt_phiStar_aux analyticOrderAt_airyExtremal_one

theorem analyticOrderNatAt_phiStar_sNode {k : ℕ} (hk : 2 ≤ k) :
    analyticOrderNatAt phiStar (sNode k : ℂ) = 2 :=
  analyticOrderNatAt_phiStar_aux (analyticOrderAt_airyExtremal_node hk)

-- Generalized Scheffé Lemma is imported from `FormalResearch.Analysis.Scheffe`.
/-! ### Section 2: Local `s`-variable Sign Uncertainty and Equality Rigidity -/

private lemma local_pullback_bound {Φ : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ s : ℂ, ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s)) :
    ∃ C' : ℝ, 0 ≤ C' ∧
      ∀ u : ℂ, ‖Φ (-u / (betaTip : ℂ))‖ ≤ C' * (1 + ‖u‖) ^ |ν| * airyEnv u := by
  let K : ℝ := max 1 betaTip⁻¹
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C * K ^ |ν|, by positivity, fun u => ?_⟩
  have hbu := hb (-u / (betaTip : ℂ))
  have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
  rw [show -(betaTip : ℂ) * (-u / (betaTip : ℂ)) = u by field_simp] at hbu
  have hnorm_s : ‖-u / (betaTip : ℂ)‖ = ‖u‖ * betaTip⁻¹ := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos betaTip_pos, div_eq_mul_inv]
  have hlin : 1 + ‖-u / (betaTip : ℂ)‖ ≤ K * (1 + ‖u‖) := by
    rw [hnorm_s]; have : betaTip⁻¹ ≤ K := le_max_right _ _; nlinarith [norm_nonneg u, le_max_left 1 betaTip⁻¹]
  have hp : (1 + ‖-u / (betaTip : ℂ)‖) ^ ν ≤ K ^ |ν| * (1 + ‖u‖) ^ |ν| :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (-u / (betaTip : ℂ))]) (le_abs_self ν)).trans
      ((Real.rpow_le_rpow (by linarith [norm_nonneg (-u / (betaTip : ℂ))]) hlin (abs_nonneg ν)).trans_eq
        (Real.mul_rpow hKpos.le (by linarith [norm_nonneg u])))
  calc ‖Φ (-u / (betaTip : ℂ))‖ ≤ C * (1 + ‖-u / (betaTip : ℂ)‖) ^ ν * airyEnv u := hbu
    _ ≤ C * (K ^ |ν| * (1 + ‖u‖) ^ |ν|) * airyEnv u := by gcongr; exact (airyEnv_pos u).le
    _ = (C * K ^ |ν|) * (1 + ‖u‖) ^ |ν| * airyEnv u := by ring

/-- Hypotheses of the Airy sign-uncertainty theorems for `f(u) = Φ(-u/β)` from those of a blow-up
limit `Φ` in the `s`-variable (threshold `y`, i.e. `f ≥ 0` on `(-∞, -β y]`). -/
lemma local_pullback_setup {Φ : ℂ → ℂ} {C ν : ℝ}
    (hΦ_diff : Differentiable ℂ Φ) (hΦ_int : Integrable (fun s : ℝ => Φ (s : ℂ)))
    (hC : 0 ≤ C) (hb : ∀ s : ℂ, ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s))
    (hΦ_real : ∀ s : ℝ, (Φ (s : ℂ)).im = 0) {y : ℝ}
    (hΦ_nonneg : ∀ s : ℝ, y ≤ s → 0 ≤ (Φ (s : ℂ)).re)
    (hΦ_int_le : (∫ s : ℝ, (Φ (s : ℂ)).re) ≤ 0) (hΦ_ne : ∃ z : ℂ, Φ z ≠ 0) :
    let f : ℂ → ℂ := fun u => Φ (-u / (betaTip : ℂ))
    Differentiable ℂ f ∧ Integrable (fun u : ℝ => f (u : ℂ)) ∧
      (∃ C' : ℝ, 0 ≤ C' ∧ ∀ u : ℂ, ‖f u‖ ≤ C' * (1 + ‖u‖) ^ |ν| * airyEnv u) ∧
      (∀ u : ℝ, (f (u : ℂ)).im = 0) ∧
      (∀ u : ℝ, u ≤ -betaTip * y → 0 ≤ (f (u : ℂ)).re) ∧
      (∫ u : ℝ, (f (u : ℂ)).re) ≤ 0 ∧ (∃ w : ℂ, f w ≠ 0) := by
  intro f
  have hfc : ∀ u : ℝ, f (u : ℂ) = Φ (((-betaTip⁻¹ * u : ℝ) : ℂ)) := fun u => by
    dsimp [f]; push_cast; ring_nf
  obtain ⟨C', hC', hb'⟩ := local_pullback_bound hC hb
  obtain ⟨z, hz⟩ := hΦ_ne
  refine ⟨hΦ_diff.comp ((differentiable_id.neg).div_const _), ?_, ⟨C', hC', hb'⟩,
    fun u => by rw [hfc]; exact hΦ_real _, fun u hu => ?_, ?_, ⟨-(betaTip : ℂ) * z, ?_⟩⟩
  · simp_rw [hfc]; exact hΦ_int.comp_mul_left' (neg_ne_zero.mpr (inv_ne_zero betaTip_pos.ne'))
  · rw [hfc]; apply hΦ_nonneg
    have h1 := mul_le_mul_of_nonneg_left hu (inv_pos.mpr betaTip_pos).le
    rw [show betaTip⁻¹ * (-betaTip * y) = -y by field_simp [betaTip_pos.ne']] at h1
    linarith
  · have hcomp : ∫ u : ℝ, (f (u : ℂ)).re = betaTip * ∫ s : ℝ, (Φ (s : ℂ)).re := by
      simp_rw [hfc]
      rw [Measure.integral_comp_mul_left (fun s : ℝ => (Φ (s : ℂ)).re) (-betaTip⁻¹)]
      simp only [abs_neg, abs_inv, abs_of_pos betaTip_pos, inv_inv, smul_eq_mul]
    rw [hcomp]; exact mul_nonpos_of_nonneg_of_nonpos betaTip_pos.le hΦ_int_le
  · dsimp [f]; have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    rwa [show -(-(betaTip : ℂ) * z) / (betaTip : ℂ) = z by field_simp]

/-- **Local `s`-variable sign uncertainty** (Theorem B in the `s`-variable). -/
theorem local_sign_uncertainty {Φ : ℂ → ℂ} {C ν : ℝ}
    (hΦ_diff : Differentiable ℂ Φ) (hΦ_int : Integrable (fun s : ℝ => Φ (s : ℂ)))
    (hC : 0 ≤ C) (hb : ∀ s : ℂ, ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s))
    (hΦ_real : ∀ s : ℝ, (Φ (s : ℂ)).im = 0) {y : ℝ}
    (hΦ_nonneg : ∀ s : ℝ, y ≤ s → 0 ≤ (Φ (s : ℂ)).re)
    (hΦ_int_le : (∫ s : ℝ, (Φ (s : ℂ)).re) ≤ 0) (hΦ_ne : ∃ z : ℂ, Φ z ≠ 0) :
    s1 ≤ y := by
  obtain ⟨hfd, hfi, ⟨C', hC', hb'⟩, hfreal, hfnonneg, hfint, hfne⟩ :=
    local_pullback_setup hΦ_diff hΦ_int hC hb hΦ_real hΦ_nonneg hΦ_int_le hΦ_ne
  have hu1 := airy_sign_uncertainty hfd hfi hC' hb' hfreal hfnonneg hfint hfne
  rw [← neg_betaTip_mul_s1] at hu1
  nlinarith [betaTip_pos]

lemma integral_norm_eq_two_mul_neg_part {Φ : ℝ → ℂ}
    (hΦ_int : Integrable Φ) (hΦ_real : ∀ s : ℝ, (Φ s).im = 0)
    (hΦ_zero : (∫ s : ℝ, (Φ s).re) = 0) :
    ∫ s : ℝ, ‖Φ s‖ = 2 * ∫ s : ℝ, max 0 (-(Φ s).re) := by
  have hre_int : Integrable (fun s : ℝ => (Φ s).re) := hΦ_int.re
  let Φp : ℝ → ℝ := fun s => max 0 ((Φ s).re)
  let Φm : ℝ → ℝ := fun s => max 0 (-(Φ s).re)
  have hp_int : Integrable Φp := by
    refine Integrable.mono' hΦ_int.norm
      (((continuous_const.max continuous_id).comp_aestronglyMeasurable hre_int.aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_of_nonneg (le_max_left _ _)]
    exact max_le (norm_nonneg _) (Complex.re_le_norm _)
  have hm_int : Integrable Φm := by
    refine Integrable.mono' hΦ_int.norm
      (((continuous_const.max continuous_id).comp_aestronglyMeasurable hre_int.neg.aestronglyMeasurable)) ?_
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_of_nonneg (le_max_left _ _)]
    exact max_le (norm_nonneg _) ((neg_le_abs _).trans (Complex.abs_re_le_norm (Φ s)))
  have hsplit_re : (fun s : ℝ => (Φ s).re) = fun s => Φp s - Φm s := by
    ext s; dsimp [Φp, Φm]
    rcases le_total 0 (Φ s).re with h | h
    · simp [h]
    · simp [h]
  have hsplit_norm : (fun s : ℝ => ‖Φ s‖) = fun s => Φp s + Φm s := by
    ext s; dsimp [Φp, Φm]
    have hΦc : Φ s = ((Φ s).re : ℂ) := Complex.ext (by simp) (by simp [hΦ_real s])
    have hnorm : ‖Φ s‖ = |(Φ s).re| := by
      conv_lhs => rw [hΦc]
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    rcases le_total 0 (Φ s).re with h | h
    · rw [abs_of_nonneg h, max_eq_right h, max_eq_left (by linarith), add_zero]
    · rw [abs_of_nonpos h, max_eq_left h, max_eq_right (by linarith), zero_add]
  have hp_eq_hm : ∫ s : ℝ, Φp s = ∫ s : ℝ, Φm s := by
    have h0 : ∫ s : ℝ, (Φp s - Φm s) = 0 := by rw [← hsplit_re]; exact hΦ_zero
    rw [integral_sub hp_int hm_int] at h0; linarith
  rw [hsplit_norm, integral_add hp_int hm_int, hp_eq_hm]; ring

/-- `‖Φ‖₁ = 1` from `∫ Re Φ = 0`, `‖Φ‖₁ ≤ 1` and the half-mass bound `1/2 ≤ ∫ Φ₋`. -/
lemma norm_integral_eq_one {Φ : ℝ → ℂ}
    (hΦ_int : Integrable Φ) (hΦ_real : ∀ s : ℝ, (Φ s).im = 0)
    (hΦ_zero : (∫ s : ℝ, (Φ s).re) = 0) (hle : ∫ s : ℝ, ‖Φ s‖ ≤ 1)
    (hneg : (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Φ s).re)) :
    ∫ s : ℝ, ‖Φ s‖ = 1 := by
  have := integral_norm_eq_two_mul_neg_part hΦ_int hΦ_real hΦ_zero
  linarith

/-- **Local `s`-variable equality rigidity**: under `y = s1`, `∫ ‖Φ‖ ≤ 1`, and `1 / 2 ≤ ∫ Φ₋`,
forces `Φ = phiStar`, `∫ Φ = 0`, and `∫ ‖Φ‖ = 1`. -/
theorem local_sign_equality {Φ : ℂ → ℂ} {C ν : ℝ}
    (hΦ_diff : Differentiable ℂ Φ) (hΦ_int : Integrable (fun s : ℝ => Φ (s : ℂ)))
    (hC : 0 ≤ C) (hb : ∀ s : ℂ, ‖Φ s‖ ≤ C * (1 + ‖s‖) ^ ν * airyEnv (-(betaTip : ℂ) * s))
    (hΦ_real : ∀ s : ℝ, (Φ (s : ℂ)).im = 0)
    (hΦ_nonneg : ∀ s : ℝ, s1 ≤ s → 0 ≤ (Φ (s : ℂ)).re)
    (hΦ_int_le : (∫ s : ℝ, (Φ (s : ℂ)).re) ≤ 0) (hΦ_ne : ∃ z : ℂ, Φ z ≠ 0)
    (hΦ_norm_le : ∫ s : ℝ, ‖Φ (s : ℂ)‖ ≤ 1)
    (hΦ_neg_ge : (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Φ (s : ℂ)).re)) :
    Φ = phiStar ∧ (∫ s : ℝ, Φ (s : ℂ)) = 0 ∧ (∫ s : ℝ, ‖Φ (s : ℂ)‖) = 1 := by
  obtain ⟨hfd, hfi, ⟨C', hC', hb'⟩, hfreal, hfnonneg, hfint, hfne⟩ :=
    local_pullback_setup hΦ_diff hΦ_int hC hb hΦ_real hΦ_nonneg hΦ_int_le hΦ_ne
  rw [neg_betaTip_mul_s1] at hfnonneg
  obtain ⟨c, hc_neg, hc_eq, -⟩ := airy_sign_equality hfd hfi hC' hb' hfreal hfnonneg hfint hfne
  let κ : ℝ := -c / betaTip
  have hκ_pos : 0 < κ := div_pos (neg_pos.mpr hc_neg) betaTip_pos
  have hΦ_eq_loc : ∀ s : ℂ, Φ s = (κ : ℂ) * localExtremalC s := fun s => by
    have h1 := hc_eq (-(betaTip : ℂ) * s)
    have hb0 : (betaTip : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr betaTip_pos.ne'
    rw [show -(-(betaTip : ℂ) * s) / (betaTip : ℂ) = s by field_simp] at h1
    rw [h1]; unfold localExtremalC
    have hκc : (κ : ℂ) * (betaTip : ℂ) = ((-c : ℝ) : ℂ) := by
      dsimp [κ]; push_cast; field_simp
    rw [← mul_assoc, hκc]
  have hΦ_int_zero : (∫ s : ℝ, Φ (s : ℂ)) = 0 := by
    simp_rw [hΦ_eq_loc]; rw [integral_const_mul, localExtremalC_integral, mul_zero]
  have hΦ_re_zero : (∫ s : ℝ, (Φ (s : ℂ)).re) = 0 := by
    have hre := integral_re hΦ_int
    change (∫ s : ℝ, (Φ (s : ℂ)).re) = (∫ s : ℝ, Φ (s : ℂ)).re at hre
    rw [hre, hΦ_int_zero, Complex.zero_re]
  have hnorm_eq_one : ∫ s : ℝ, ‖Φ (s : ℂ)‖ = 1 :=
    norm_integral_eq_one (Φ := fun s : ℝ => Φ (s : ℂ)) hΦ_int hΦ_real hΦ_re_zero hΦ_norm_le hΦ_neg_ge
  have hnorm_scale : ∫ s : ℝ, ‖Φ (s : ℂ)‖ = κ * (2 * LStar) := by
    have hns : ∀ s : ℝ, ‖Φ (s : ℂ)‖ = κ * ‖localExtremalC (s : ℂ)‖ := fun s => by
      rw [hΦ_eq_loc (s : ℂ), norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ_pos]
    simp_rw [hns, integral_const_mul]
    rw [show (∫ s : ℝ, ‖localExtremalC (s : ℂ)‖) = 2 * LStar by linarith [LStar_eq_half_norm_integral]]
  have hκ_eq : κ = (2 * LStar)⁻¹ := by
    rw [hnorm_scale] at hnorm_eq_one
    exact eq_inv_of_mul_eq_one_left (by linarith)
  have hΦ_eq_phiStar : Φ = phiStar := by
    ext s; rw [hΦ_eq_loc s, hκ_eq]; unfold phiStar; push_cast; rfl
  exact ⟨hΦ_eq_phiStar, hΦ_int_zero, hnorm_eq_one⟩

/-! ### Section 3: Blow-up family package (Proposition T) and Theorem C -/

/-- Packaged hypotheses of Proposition T (`blowup_limit.tex` / `local_airy_model.tex`)
plus the Theorem A lower bound and scaling relation for a weakly feasible family. -/
structure BlowupFamilyPackage (ι : Type*) (p : Filter ι) where
  c' : ι → ℝ
  s₁ : ι → ℝ
  t₁ : ι → ℝ
  Φ : ι → ℂ → ℂ
  γ : ι → ℝ
  hc'_tendsto : Tendsto c' p atTop
  hγ_nonneg : ∀ᶠ n in p, 0 ≤ γ n
  scaling_eq : ∀ᶠ n in p,
    t₁ n = xiBar * c' n + (2 / 3 : ℝ) * xiStar * (c' n) ^ (1 / 3 : ℝ) * s₁ n +
      (1 / 3 : ℝ) * (c' n) ^ (-(1 / 3 : ℝ)) * (s₁ n) ^ 2
  theorem_A_lower : ∃ C₀ : ℝ, ∀ᶠ n in p, -C₀ ≤ s₁ n
  propT_subseq : ∀ (ns : ℕ → ι), Tendsto ns atTop p →
    (∃ B : ℝ, ∀ k : ℕ, s₁ (ns k) ≤ B) →
    ∃ (ms : ℕ → ℕ) (s₁Star : ℝ) (Ψ : ℂ → ℂ) (γLim mEsc : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => s₁ (ns (ms k))) atTop (nhds s₁Star) ∧
      TendstoLocallyUniformlyOn (fun k => Φ (ns (ms k))) Ψ atTop univ ∧
      Tendsto (fun k => γ (ns (ms k))) atTop (nhds γLim) ∧
      Differentiable ℂ Ψ ∧
      Integrable (fun s : ℝ => Ψ (s : ℂ)) ∧
      (∃ C : ℝ, 0 ≤ C ∧
        ∀ s : ℂ, ‖Ψ s‖ ≤ C * (1 + ‖s‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * s)) ∧
      (∃ z : ℂ, Ψ z ≠ 0) ∧
      (∀ s : ℝ, (Ψ (s : ℂ)).im = 0) ∧
      (∀ s : ℝ, s₁Star ≤ s → 0 ≤ (Ψ (s : ℂ)).re) ∧
      (∫ s : ℝ, ‖Ψ (s : ℂ)‖ ≤ 1) ∧
      0 ≤ γLim ∧ 0 ≤ mEsc ∧
      (∫ s : ℝ, (Ψ (s : ℂ)).re) = -(γLim + mEsc) ∧
      (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(Ψ (s : ℂ)).re)

lemma BlowupFamilyPackage.scaled_excess_eq {ι : Type*} {p : Filter ι}
    (F : BlowupFamilyPackage ι p) :
    ∀ᶠ n in p, (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) =
      (2 / 3 : ℝ) * xiStar * F.s₁ n + (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2 := by
  filter_upwards [F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ)), F.scaling_eq] with n hc' hsc
  have hc'0 : 0 < F.c' n := by linarith
  have hp13 : 0 < (F.c' n) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'0 _
  have hpow : (F.c' n) ^ (-(1 / 3 : ℝ)) / (F.c' n) ^ (1 / 3 : ℝ) = (F.c' n) ^ (-(2 / 3 : ℝ)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hc'0.le, ← Real.rpow_add hc'0]; congr 1; norm_num
  rw [hsc, show xiBar * F.c' n + (2 / 3 : ℝ) * xiStar * (F.c' n) ^ (1 / 3 : ℝ) * F.s₁ n +
      (1 / 3 : ℝ) * (F.c' n) ^ (-(1 / 3 : ℝ)) * (F.s₁ n) ^ 2 - xiBar * F.c' n =
      (2 / 3 : ℝ) * xiStar * (F.c' n) ^ (1 / 3 : ℝ) * F.s₁ n +
        (1 / 3 : ℝ) * (F.c' n) ^ (-(1 / 3 : ℝ)) * (F.s₁ n) ^ 2 by ring, add_div]
  rw [show (2 / 3 : ℝ) * xiStar * (F.c' n) ^ (1 / 3 : ℝ) * F.s₁ n / (F.c' n) ^ (1 / 3 : ℝ) =
      (2 / 3 : ℝ) * xiStar * F.s₁ n by field_simp [hp13.ne'],
    show (1 / 3 : ℝ) * (F.c' n) ^ (-(1 / 3 : ℝ)) * (F.s₁ n) ^ 2 / (F.c' n) ^ (1 / 3 : ℝ) =
      (1 / 3 : ℝ) * ((F.c' n) ^ (-(1 / 3 : ℝ)) / (F.c' n) ^ (1 / 3 : ℝ)) * (F.s₁ n) ^ 2 by ring,
    hpow]

/-- **Extraction lemma** for lower bounds on the scaled excess `(t₁ - ξ̄ c')/c'^{1/3}`: if every
Proposition T limit along a sequence in `Q` with `s₁` bounded above has `s₁^* ≥ S`, then for every
`ε > 0`, eventually `(2/3) ξ_* S - ε ≤ (t₁ - ξ̄ c')/c'^{1/3}`.  Theorem C is the case `Q = True`,
`S = s1`; the two-level theorem (`TwoLevel.PinnedLimit`) takes `Q` the pinned sign. -/
theorem eventually_excess_ge_of_limit {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p) (Q : ι → Prop) (hQ : ∀ᶠ n in p, Q n) (S : ℝ)
    (hS : ∀ ns : ℕ → ι, Tendsto ns atTop p → (∀ k, Q (ns k)) → (∃ B : ℝ, ∀ k : ℕ, F.s₁ (ns k) ≤ B) →
      ∃ (ms : ℕ → ℕ) (s₁Star : ℝ), StrictMono ms ∧
        Tendsto (fun k => F.s₁ (ns (ms k))) atTop (nhds s₁Star) ∧ S ≤ s₁Star) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in p,
      (2 / 3 : ℝ) * xiStar * S - ε ≤ (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) := by
  intro ε hε
  by_contra hnot
  rw [Filter.not_eventually] at hnot
  simp only [not_le] at hnot
  have hev : ∀ᶠ n in p, (1 ≤ F.c' n ∧
      (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) =
        (2 / 3 : ℝ) * xiStar * F.s₁ n + (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2) ∧
      Q n :=
    ((F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))).and F.scaled_excess_eq).and hQ
  obtain ⟨ns, hns, hprops⟩ := exists_seq_forall_of_frequently (hnot.and_eventually hev)
  have hB : ∀ k : ℕ, F.s₁ (ns k) ≤
      ((2 / 3 : ℝ) * xiStar * S - ε) / ((2 / 3 : ℝ) * xiStar) := fun k => by
    obtain ⟨hlt, ⟨hc'1, hex⟩, -⟩ := hprops k
    have hnn : 0 ≤ (1 / 3 : ℝ) * (F.c' (ns k)) ^ (-(2 / 3 : ℝ)) * (F.s₁ (ns k)) ^ 2 := by
      have : 0 ≤ (F.c' (ns k)) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
      positivity
    rw [hex] at hlt; rw [le_div_iff₀' two_thirds_xiStar_pos]; linarith
  obtain ⟨ms, s₁Star, hms, hs₁lim, hle⟩ :=
    hS ns hns (fun k => (hprops k).2.2) ⟨_, hB⟩
  have hlim_le := le_of_tendsto hs₁lim (Eventually.of_forall fun k => hB (ms k))
  rw [le_div_iff₀' two_thirds_xiStar_pos] at hlim_le
  have := mul_le_mul_of_nonneg_left hle two_thirds_xiStar_pos.le
  linarith

/-- **Theorem C** (`local_airy_model.tex`), eventual-ε form. -/
theorem theorem_C_eventually {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in p, Aopt - ε ≤ (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) := by
  intro ε hε
  have h := eventually_excess_ge_of_limit F (fun _ => True) (Eventually.of_forall fun _ => trivial) s1
    (fun ns hns _ hB => by
      obtain ⟨ms, s₁Star, Ψ, γLim, mEsc, hms, hs₁lim, _, _, hΨd, hΨi, ⟨C, hC, hΨb⟩, hΨne,
        hΨreal, hΨnn, _, hγLim, hmEsc, hΨint, _⟩ := F.propT_subseq ns hns hB
      exact ⟨ms, s₁Star, hms, hs₁lim,
        local_sign_uncertainty hΨd hΨi hC hΨb hΨreal hΨnn (by linarith) hΨne⟩) ε hε
  rwa [← Aopt_eq_mul_s1] at h

/-- **Theorem C** (`local_airy_model.tex`), `EReal` `liminf` form (unconditional even when
`s₁ → +∞`). -/
theorem theorem_C {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p) :
    (Aopt : EReal) ≤
      Filter.liminf (fun n => (((F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) : ℝ) : EReal)) p := by
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hxL, hxA⟩ := EReal.exists_between_coe_real hlt
  have hev := theorem_C_eventually F (Aopt - x) (sub_pos.mpr (EReal.coe_lt_coe_iff.mp hxA))
  have hle : (x : EReal) ≤ _ := le_liminf_of_le (by isBoundedDefault)
    (hev.mono fun _ hn => EReal.coe_le_coe_iff.mpr (by linarith))
  exact absurd (hle.trans_lt hxL) (lt_irrefl _)

/-- **Theorem C**, `ℝ`-valued `liminf` form when the excess is cobounded above on `p`. -/
theorem theorem_C_real {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p)
    (hbdd : p.IsCoboundedUnder (· ≥ ·)
      (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ))) :
    Aopt ≤ Filter.liminf (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ)) p := by
  by_contra hlt; push Not at hlt
  set L := Filter.liminf (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ)) p
  have := le_liminf_of_le hbdd (theorem_C_eventually F ((Aopt - L) / 2) (by linarith))
  linarith

/-! ### Section 4: Hypothesis `Att`, Step 0, `(R1)`, and `(R2)` -/

/-- **Hypothesis `Att`** (`rigidity.tex`): `t₁ = xiBar * c' + Aopt * c'^(1/3) + o(c'^(1/3))`. -/
def Att {ι : Type*} {p : Filter ι} (F : BlowupFamilyPackage ι p) : Prop :=
  Tendsto (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ)) p (nhds Aopt)

/-- `excess → A` forces `s₁ → A / ((2/3) ξ_*)`; `att_tendsto_s1` is the case `A = Aopt`. -/
theorem tendsto_s₁_of_tendsto_excess {ι : Type*} {p : Filter ι}
    (F : BlowupFamilyPackage ι p) {A : ℝ}
    (hA : Tendsto (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ)) p (nhds A)) :
    Tendsto F.s₁ p (nhds (A / ((2 / 3 : ℝ) * xiStar))) := by
  obtain ⟨C₀, hC₀⟩ := F.theorem_A_lower
  let B₀ : ℝ := max C₀ ((A + 1) / ((2 / 3 : ℝ) * xiStar))
  have hs₁_bdd : ∀ᶠ n in p, |F.s₁ n| ≤ B₀ := by
    have hq_ub := hA.eventually (eventually_le_nhds (by linarith : A < A + 1))
    filter_upwards [hC₀, hq_ub, F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ)),
      F.scaled_excess_eq] with n hnC₀ hnq hc'1 hex
    have hnn : 0 ≤ (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2 := by
      have : 0 ≤ (F.c' n) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _; positivity
    have hub : F.s₁ n ≤ (A + 1) / ((2 / 3 : ℝ) * xiStar) := by
      rw [le_div_iff₀' two_thirds_xiStar_pos]; linarith
    exact abs_le.mpr ⟨by linarith [le_max_left C₀ ((A + 1) / ((2 / 3 : ℝ) * xiStar))],
      hub.trans (le_max_right _ _)⟩
  have hc'neg : Tendsto (fun n => (F.c' n) ^ (-(2 / 3 : ℝ))) p (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp F.hc'_tendsto
  have hquad : Tendsto (fun n => (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2) p (nhds 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using (hc'neg.const_mul ((1 / 3 : ℝ) * B₀ ^ 2)))
    filter_upwards [hs₁_bdd, F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hn hc'1
    have hpow_nn : 0 ≤ (F.c' n) ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg (by linarith) _
    have hsq : (F.s₁ n) ^ 2 ≤ B₀ ^ 2 := sq_le_sq.mpr (by rwa [abs_of_nonneg (le_trans (abs_nonneg _) hn)])
    rw [Real.norm_of_nonneg (by positivity)]; nlinarith
  have hlin : Tendsto (fun n => (2 / 3 : ℝ) * xiStar * F.s₁ n) p (nhds A) := by
    have hdiff : Tendsto (fun n => (F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) -
        (1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) * (F.s₁ n) ^ 2) p (nhds A) := by
      simpa using hA.sub hquad
    refine hdiff.congr' (F.scaled_excess_eq.mono fun n hex => by linarith)
  have hdiv := hlin.const_mul (((2 / 3 : ℝ) * xiStar)⁻¹)
  rw [inv_mul_eq_div] at hdiv
  exact hdiv.congr fun n => by field_simp [xiStar_pos.ne']

/-- **Step 0 (`att_tendsto_s1`)**: under `Att` and Theorem A (`-C₀ ≤ s₁`), `s₁ → s1`. -/
theorem att_tendsto_s1 {ι : Type*} {p : Filter ι}
    (F : BlowupFamilyPackage ι p) (hAtt : Att F) :
    Tendsto F.s₁ p (nhds s1) := by
  have h := tendsto_s₁_of_tendsto_excess F hAtt
  rwa [show Aopt / ((2 / 3 : ℝ) * xiStar) = s1 by
    rw [Aopt_eq_mul_s1]; field_simp [xiStar_pos.ne']] at h

private lemma att_subseq_phiStar_zero {ι : Type*} {p : Filter ι}
    (F : BlowupFamilyPackage ι p) (hAtt : Att F) (ns : ℕ → ι) (hns : Tendsto ns atTop p) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧
      TendstoLocallyUniformlyOn (fun k => F.Φ (ns (ms k))) phiStar atTop univ ∧
      Tendsto (fun k => F.γ (ns (ms k))) atTop (nhds 0) := by
  have hs₁_ns := (att_tendsto_s1 F hAtt).comp hns
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp (hs₁_ns.eventually (eventually_le_nhds (by linarith : s1 < s1 + 1)))
  let ns' : ℕ → ι := fun k => ns (k + k₀)
  obtain ⟨ms', s₁Star, Ψ, γLim, mEsc, hms', hs₁Star, hΦlim, hγlim, hΨd, hΨi, ⟨C, hC, hΨb⟩,
    hΨne, hΨreal, hΨnn, hΨnorm, hγnn, hmEscnn, hΨint, hΨneg⟩ :=
    F.propT_subseq ns' (hns.comp (tendsto_add_atTop_nat k₀)) ⟨s1 + 1, fun k => hk₀ (k + k₀) (by omega)⟩
  have hs₁_eq : s₁Star = s1 :=
    tendsto_nhds_unique hs₁Star (hs₁_ns.comp ((tendsto_add_atTop_nat k₀).comp hms'.tendsto_atTop))
  subst hs₁_eq
  obtain ⟨hΨeq, hΨ0, -⟩ := local_sign_equality hΨd hΨi hC hΨb hΨreal hΨnn (by linarith) hΨne hΨnorm hΨneg
  have hγ0 : γLim = 0 := by
    have hre0 : (∫ s : ℝ, (Ψ (s : ℂ)).re) = 0 := by
      have hre := integral_re hΨi
      change (∫ s : ℝ, (Ψ (s : ℂ)).re) = (∫ s : ℝ, Ψ (s : ℂ)).re at hre
      rw [hre, hΨ0, Complex.zero_re]
    linarith
  rw [hΨeq] at hΦlim; rw [hγ0] at hγlim
  exact ⟨fun k => ms' k + k₀, fun a b hab => Nat.add_lt_add_right (hms' hab) k₀, hΦlim, hγlim⟩

/-- **Theorem R `(R1)`** (`rigidity.tex`): under `Att`, along the whole family,
`s₁ → s1`, `Φ → phiStar` locally uniformly on `ℂ`, and `γ → 0`. -/
theorem theorem_R1 {ι : Type*} {p : Filter ι} [p.IsCountablyGenerated]
    (F : BlowupFamilyPackage ι p) (hAtt : Att F) :
    Tendsto F.s₁ p (nhds s1) ∧
    TendstoLocallyUniformlyOn F.Φ phiStar p univ ∧
    Tendsto F.γ p (nhds 0) := by
  refine ⟨att_tendsto_s1 F hAtt, ?_, ?_⟩
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK; rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
    by_contra hnot
    have hfreq : ∃ᶠ n in p, ∃ z ∈ K, ε ≤ dist (phiStar z) (F.Φ n z) := by
      rw [Filter.not_eventually] at hnot
      refine hnot.mono fun n hn => ?_
      push Not at hn; exact hn
    obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently hfreq
    obtain ⟨ms, _, hΦlim, -⟩ := att_subseq_phiStar_zero F hAtt ns hns
    have hev := Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΦlim K (subset_univ K) hK) ε hε
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hev
    obtain ⟨z, hzK, hzbad⟩ := hbad (ms k₀)
    linarith [hk₀ k₀ le_rfl z hzK]
  · refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, _, _, hγlim⟩ := att_subseq_phiStar_zero F hAtt ns hns
    exact ⟨ms, hγlim⟩

/-- Full Theorem R package extending `BlowupFamilyPackage` with real-domain `L¹` properties,
disc holomorphicity, conjugation symmetry, tail nonnegativity, and `s₁` zero property. -/
structure RigidityFamilyPackage (ι : Type*) (p : Filter ι) extends BlowupFamilyPackage ι p where
  domain_integrable : ∀ᶠ n in p,
    IntegrableOn (fun s : ℝ => Φ n (s : ℂ)) (Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ)))
  domain_norm_integral :
    Tendsto (fun n => ∫ s in Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ)), ‖Φ n (s : ℂ)‖) p (nhds 1)
  holo_balls : ∀ R : ℝ, ∀ᶠ n in p, DifferentiableOn ℂ (Φ n) (ball 0 R)
  real_symm : ∀ R : ℝ, ∀ᶠ n in p,
    ∀ z ∈ ball 0 R, Φ n (starRingEnd ℂ z) = starRingEnd ℂ (Φ n z)
  nonneg_tail : ∀ᶠ n in p, ∀ s : ℝ, s₁ n ≤ s → 0 ≤ (Φ n (s : ℂ)).re
  s1_is_zero : ∀ᶠ n in p, Φ n (s₁ n : ℂ) = 0

/-- Extension of `Φ n` by `0` outside the real domain `{b > 0} = (-xiStar * c'^(2/3), ∞)`. -/
noncomputable def phiExt {ι : Type*} {p : Filter ι} (F : RigidityFamilyPackage ι p) (n : ι) :
    ℝ → ℂ :=
  (Ioi (-xiStar * (F.c' n) ^ (2 / 3 : ℝ))).indicator (fun s : ℝ => F.Φ n (s : ℂ))

private lemma phiStar_tail_norm_tendsto :
    Tendsto (fun R : ℝ => ∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖) atTop (nhds 0) := by
  have hcomp : ∀ R : ℝ, 0 ≤ R →
      ∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖ =
        (∫ s : ℝ, ‖phiStar (s : ℂ)‖) - ∫ s in Icc (-R) R, ‖phiStar (s : ℂ)‖ := fun R _ => by
    have hset : Ioi R ∪ Iio (-R) = (Icc (-R) R)ᶜ := by
      ext s; simp only [mem_union, mem_Ioi, mem_Iio, mem_compl_iff, mem_Icc, not_and_or, not_le]; tauto
    rw [hset]
    linarith [integral_add_compl (s := Icc (-R) R) measurableSet_Icc phiStar_integrable.norm]
  have hIcc : Tendsto (fun R : ℝ => ∫ s in Icc (-R) R, ‖phiStar (s : ℂ)‖) atTop
      (nhds (∫ s : ℝ, ‖phiStar (s : ℂ)‖)) := by
    have heq : ∀ R : ℝ, ∫ s in Icc (-R) R, ‖phiStar (s : ℂ)‖ =
        ∫ s : ℝ, (Icc (-R) R).indicator (fun t => ‖phiStar (t : ℂ)‖) s := fun R =>
      (integral_indicator measurableSet_Icc).symm
    simp_rw [heq]
    refine tendsto_integral_filter_of_dominated_convergence (fun s => ‖phiStar (s : ℂ)‖)
      (Eventually.of_forall fun R =>
        (phiStar_integrable.norm.indicator measurableSet_Icc).aestronglyMeasurable)
      (Eventually.of_forall fun R => Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _)]
        simp only [Set.indicator]; split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
      phiStar_integrable.norm (Eventually.of_forall fun s => ?_)
    have hev : ∀ᶠ R : ℝ in atTop, s ∈ Icc (-R) R :=
      (eventually_ge_atTop |s|).mono fun _ hR => abs_le.mp hR
    exact tendsto_const_nhds.congr' (hev.mono fun R hR => (indicator_of_mem hR _).symm)
  have hdiff : Tendsto (fun R : ℝ =>
      (∫ s : ℝ, ‖phiStar (s : ℂ)‖) - ∫ s in Icc (-R) R, ‖phiStar (s : ℂ)‖) atTop (nhds 0) := by
    simpa [sub_self] using (tendsto_const_nhds (x := ∫ s : ℝ, ‖phiStar (s : ℂ)‖)).sub hIcc
  exact hdiff.congr' ((eventually_ge_atTop (0 : ℝ)).mono fun R hR => (hcomp R hR).symm)

/-- `L¹` convergence of the blow-ups to a unit-norm locally uniform limit (Scheffé); the first two
clauses of `theorem_R2` are the case `Ψ = phiStar`. -/
theorem l1_of_tendstoLocallyUniformlyOn {ι : Type*} {p : Filter ι} [p.NeBot]
    [p.IsCountablyGenerated] (F : RigidityFamilyPackage ι p) {Ψ : ℂ → ℂ}
    (hΨi : Integrable (fun s : ℝ => Ψ (s : ℂ))) (hΨn : ∫ s : ℝ, ‖Ψ (s : ℂ)‖ = 1)
    (hΦ : TendstoLocallyUniformlyOn F.Φ Ψ p univ) :
    Tendsto (fun n => ∫ s : ℝ, ‖phiExt F n s - Ψ (s : ℂ)‖) p (nhds 0) ∧
    Tendsto (fun n => ∫ s in Ioi (-xiStar * (F.c' n) ^ (2 / 3 : ℝ)),
      ‖F.Φ n (s : ℂ) - Ψ (s : ℂ)‖) p (nhds 0) := by
  have hleft_tendsto : Tendsto (fun n => -xiStar * (F.c' n) ^ (2 / 3 : ℝ)) p atBot := by
    have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp F.hc'_tendsto
    simpa [neg_mul] using tendsto_neg_atBot_iff.mpr (hpow.const_mul_atTop xiStar_pos)
  have hpt : ∀ s : ℝ, Tendsto (fun n => phiExt F n s) p (nhds (Ψ (s : ℂ))) := fun s =>
    (hΦ.tendsto_at (mem_univ _)).congr'
      ((hleft_tendsto.eventually (eventually_lt_atBot s)).mono fun n hn => (indicator_of_mem hn _).symm)
  have hext_int : ∀ᶠ n in p, Integrable (phiExt F n) :=
    F.domain_integrable.mono fun n hn => (integrable_indicator_iff measurableSet_Ioi).mpr hn
  have hext_norm : Tendsto (fun n => ∫ s : ℝ, ‖phiExt F n s‖) p (nhds (∫ s : ℝ, ‖Ψ (s : ℂ)‖)) := by
    rw [hΨn]
    exact F.domain_norm_integral.congr fun n => by
      dsimp [phiExt]; simp_rw [norm_indicator_eq_indicator_norm]; exact (integral_indicator measurableSet_Ioi).symm
  have hL1 := tendsto_integral_norm_sub_of_tendsto_ae hext_int hΨi
    (Eventually.of_forall hpt) hext_norm
  refine ⟨hL1, ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun n =>
      setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _) ?_ hL1
  filter_upwards [hext_int] with n hn
  have hcongr : ∫ s in Ioi (-xiStar * (F.c' n) ^ (2 / 3 : ℝ)), ‖F.Φ n (s : ℂ) - Ψ (s : ℂ)‖ =
      ∫ s in Ioi (-xiStar * (F.c' n) ^ (2 / 3 : ℝ)), ‖phiExt F n s - Ψ (s : ℂ)‖ :=
    setIntegral_congr_fun measurableSet_Ioi fun s hs => by rw [phiExt, indicator_of_mem hs]
  rw [hcongr]
  exact setIntegral_le_integral (hn.sub hΨi).norm (Eventually.of_forall fun _ => norm_nonneg _)

/-- **Theorem R `(R2)`** (`rigidity.tex`): `L¹` convergence on `{b > 0}` (and `ℝ`) and mass tightness. -/
theorem theorem_R2 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : RigidityFamilyPackage ι p) (hAtt : Att F.toBlowupFamilyPackage) :
    Tendsto (fun n => ∫ s : ℝ, ‖phiExt F n s - phiStar (s : ℂ)‖) p (nhds 0) ∧
    Tendsto (fun n => ∫ s in Ioi (-xiStar * (F.c' n) ^ (2 / 3 : ℝ)),
      ‖F.Φ n (s : ℂ) - phiStar (s : ℂ)‖) p (nhds 0) ∧
    (∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n in p, ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖ < ε) ∧
    Tendsto (fun R : ℝ => Filter.limsup (fun n => ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖) p)
      atTop (nhds 0) := by
  obtain ⟨_, hΦunif, _⟩ := theorem_R1 F.toBlowupFamilyPackage hAtt
  have hext_int : ∀ᶠ n in p, Integrable (phiExt F n) :=
    F.domain_integrable.mono fun n hn => (integrable_indicator_iff measurableSet_Ioi).mpr hn
  obtain ⟨hL1, hL1_dom⟩ :=
    l1_of_tendstoLocallyUniformlyOn F phiStar_integrable phiStar_norm_integral hΦunif
  have htail_ub : ∀ R : ℝ, ∀ᶠ n in p,
      ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖ ≤
        (∫ s : ℝ, ‖phiExt F n s - phiStar (s : ℂ)‖) +
          ∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖ := fun R => by
    filter_upwards [hext_int] with n hn
    have hm : MeasurableSet (Ioi R ∪ Iio (-R)) := measurableSet_Ioi.union measurableSet_Iio
    have hi1 : IntegrableOn (fun s : ℝ => ‖phiExt F n s - phiStar (s : ℂ)‖) (Ioi R ∪ Iio (-R)) :=
      (hn.sub phiStar_integrable).norm.integrableOn
    have hi2 : IntegrableOn (fun s : ℝ => ‖phiStar (s : ℂ)‖) (Ioi R ∪ Iio (-R)) :=
      phiStar_integrable.norm.integrableOn
    calc ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖
        ≤ ∫ s in Ioi R ∪ Iio (-R), (‖phiExt F n s - phiStar (s : ℂ)‖ + ‖phiStar (s : ℂ)‖) :=
          setIntegral_mono_on hn.norm.integrableOn (hi1.add hi2) hm fun s _ => by
            simpa [sub_add_cancel] using norm_add_le (phiExt F n s - phiStar (s : ℂ)) (phiStar (s : ℂ))
      _ = (∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s - phiStar (s : ℂ)‖) +
            ∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖ := integral_add hi1 hi2
      _ ≤ (∫ s : ℝ, ‖phiExt F n s - phiStar (s : ℂ)‖) +
            ∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖ :=
          add_le_add (setIntegral_le_integral (hn.sub phiStar_integrable).norm
            (Eventually.of_forall fun _ => norm_nonneg _)) le_rfl
  have htight_eps : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ᶠ n in p, ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := eventually_atTop.mp (phiStar_tail_norm_tendsto.eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2)))
    refine ⟨max R 1, by positivity, ?_⟩
    have hR' := hR (max R 1) (le_max_left _ _)
    filter_upwards [htail_ub (max R 1),
      hL1.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2))] with n h1 h2
    linarith
  have htight_lim : Tendsto
      (fun R : ℝ => Filter.limsup (fun n => ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖) p)
      atTop (nhds 0) := by
    refine squeeze_zero (fun R => ?_) (fun R => ?_) phiStar_tail_norm_tendsto
    · have h0 : (0 : ℝ) = Filter.limsup (fun _ : ι => (0 : ℝ)) p := (Filter.limsup_const (0 : ℝ)).symm
      rw [h0]
      refine limsup_le_limsup (Eventually.of_forall fun n =>
        setIntegral_nonneg (measurableSet_Ioi.union measurableSet_Iio) fun _ _ => norm_nonneg _)
        (isCoboundedUnder_le_of_le p fun _ => le_rfl) ?_
      refine ⟨1 + ∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖, eventually_map.mpr ?_⟩
      filter_upwards [htail_ub R, hL1.eventually (eventually_lt_nhds zero_lt_one)] with n h1 h2
      linarith
    · refine le_of_forall_pos_lt_add fun ε hε => ?_
      have hlt : ∀ᶠ n in p, ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖ ≤
          (∫ s in Ioi R ∪ Iio (-R), ‖phiStar (s : ℂ)‖) + ε / 2 := by
        filter_upwards [htail_ub R, hL1.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < ε / 2))] with n h1 h2
        linarith
      have hcb : p.IsCoboundedUnder (· ≤ ·) (fun n => ∫ s in Ioi R ∪ Iio (-R), ‖phiExt F n s‖) :=
        isCoboundedUnder_le_of_le p fun n =>
          setIntegral_nonneg (measurableSet_Ioi.union measurableSet_Iio) fun _ _ => norm_nonneg (phiExt F n _)
      exact (limsup_le_of_le hcb hlt).trans_lt (by linarith)
  exact ⟨hL1, hL1_dom, htight_eps, htight_lim⟩

/-! ### Section 5: Theorem R `(R3)` — Hurwitz zero persistence and scaling limits -/

/-- Rescaling map `t(b) = c' (ξ_* + c'^{-2/3} s)^2 / 3` from the Airy variable `s` to `t`. -/
noncomputable def tScale (c' : ℝ) (s : ℂ) : ℂ :=
  ((c' / 3 : ℝ) : ℂ) * ((xiStar : ℂ) + ((c' ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * s) ^ 2

private lemma exists_disc_in_ball {c : ℂ} {R : ℝ} (h : ‖c‖ + 1 ≤ R) : ball c 1 ⊆ ball 0 R :=
  fun z hz => by
    rw [mem_ball, dist_zero_right]; rw [mem_ball, dist_eq_norm] at hz
    calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ < 1 + ‖c‖ := by linarith
      _ ≤ R := by linarith

private lemma phiStar_not_eventually_zero (z₀ : ℂ) : ¬ ∀ᶠ z in 𝓝 z₀, phiStar z = 0 := fun h => by
  obtain ⟨w, hw⟩ := phiStar_ne_zero
  exact hw ((differentiable_phiStar.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ z₀) h (mem_univ w))

private lemma analyticOrderNatAt_le_zeroCount {g : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hg : DifferentiableOn ℂ g (ball c R)) (hr : 0 < r) (hrR : r < R)
    (hsph : ∀ z ∈ sphere c r, g z ≠ 0) {z : ℂ} (hz : z ∈ ball c r) :
    analyticOrderNatAt g z ≤ zeroCount g c r := by
  obtain ⟨hw, hgw⟩ := exists_nonzero_of_sphere hr hrR hsph
  have hfin := support_orderNat_finite hg hw hgw hrR
  have h1 : zeroCount g c r = ∑ w ∈ hfin.toFinset, analyticOrderNatAt g w := by
    unfold zeroCount; rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
  by_cases hord : analyticOrderNatAt g z = 0
  · rw [hord]; exact Nat.zero_le _
  · rw [h1]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (hfin.mem_toFinset.mpr ⟨hz, hord⟩)

private lemma even_analyticOrderNatAt_of_nonneg_real {g : ℂ → ℂ} {x₀ R δ : ℝ}
    (hg : DifferentiableOn ℂ g (ball (x₀ : ℂ) R)) (hR : 0 < R) (hδ : 0 < δ)
    (hne : ∃ w ∈ ball (x₀ : ℂ) R, g w ≠ 0)
    (hreal : ∀ x : ℝ, |x - x₀| < δ → (g (x : ℂ)).im = 0)
    (hnn : ∀ x : ℝ, |x - x₀| < δ → 0 ≤ (g (x : ℂ)).re) (hz : g (x₀ : ℂ) = 0) :
    Even (analyticOrderNatAt g (x₀ : ℂ)) ∧ 2 ≤ analyticOrderNatAt g (x₀ : ℂ) := by
  have han := (hg.analyticOnNhd isOpen_ball) (x₀ : ℂ) (mem_ball_self hR)
  obtain ⟨w, hw, hgw⟩ := hne
  have hfin_ord := order_ne_top hg hw hgw (mem_ball_self hR)
  obtain ⟨h, hh_an, hh0, hgh⟩ := han.analyticOrderAt_ne_top.mp hfin_ord
  set m := analyticOrderNatAt g (x₀ : ℂ)
  have hm_pos : 1 ≤ m := by
    have hnz := han.analyticOrderAt_ne_zero.mpr hz
    have : m ≠ 0 := fun h0 => hnz ((ENat.toNat_eq_zero.mp h0).resolve_right hfin_ord)
    omega
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hgh
  have hh_cont := hh_an.continuousAt
  let ρ := min δ ε
  have hρ : 0 < ρ := lt_min hδ hε
  have hh_re_pos : 0 ≤ (h (x₀ : ℂ)).re ∧ (h (x₀ : ℂ)).im = 0 := by
    have hseq : Tendsto (fun k : ℕ => x₀ + ρ / (k + 2 : ℝ)) atTop (nhds x₀) := by
      simpa using tendsto_const_nhds.add
        (tendsto_const_nhds.div_atTop
          (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))))
    have hcomp := hh_cont.tendsto.comp (Complex.continuous_ofReal.tendsto x₀ |>.comp hseq)
    have hval : ∀ k : ℕ, 0 ≤ (h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).re ∧
        (h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).im = 0 := fun k => by
      have hk_pos : 0 < ρ / (k + 2 : ℝ) := div_pos hρ (by positivity)
      have hdist : |x₀ + ρ / (k + 2 : ℝ) - x₀| < ρ := by
        simpa [abs_of_pos hk_pos] using (div_lt_iff₀ (by positivity : (0 : ℝ) < k + 2)).mpr (by nlinarith)
      have hm1 : ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) ∈ ball (x₀ : ℂ) ε := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hdist.trans_le (min_le_right _ _)
      have heq : g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) =
          (((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) - (x₀ : ℂ)) ^ m * h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) := by
        simpa [smul_eq_mul] using hball hm1
      have hpow_pos : 0 < (ρ / (k + 2 : ℝ)) ^ m := pow_pos hk_pos m
      have hpow_c : (((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) - (x₀ : ℂ)) ^ m =
          (((ρ / (k + 2 : ℝ)) ^ m : ℝ) : ℂ) := by push_cast; ring
      rw [hpow_c] at heq
      have hne_c : (((ρ / (k + 2 : ℝ)) ^ m : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpow_pos.ne'
      have hdiv : h ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) =
          g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) / (((ρ / (k + 2 : ℝ)) ^ m : ℝ) : ℂ) := by
        rw [heq]; field_simp
      rw [hdiv]
      have him : (g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).im = 0 :=
        hreal _ (hdist.trans_le (min_le_left _ _))
      have hgcast : g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ) =
          ((g ((x₀ + ρ / (k + 2 : ℝ) : ℝ) : ℂ)).re : ℂ) :=
        Complex.ext (by simp) (by simpa using him)
      rw [hgcast, ← Complex.ofReal_div, Complex.ofReal_re, Complex.ofReal_im]
      exact ⟨div_nonneg (hnn _ (hdist.trans_le (min_le_left _ _))) hpow_pos.le, rfl⟩
    exact ⟨ge_of_tendsto (Complex.continuous_re.tendsto _ |>.comp hcomp) (Eventually.of_forall fun k => (hval k).1),
      tendsto_nhds_unique (Complex.continuous_im.tendsto _ |>.comp hcomp)
        (tendsto_const_nhds.congr fun k => (hval k).2.symm)⟩
  have hh_re_strict : 0 < (h (x₀ : ℂ)).re :=
    lt_of_le_of_ne hh_re_pos.1 fun h0 => hh0 (Complex.ext h0.symm hh_re_pos.2)
  have heven : Even m := by
    by_contra hodd; rw [Nat.not_even_iff_odd] at hodd
    obtain ⟨ε', hε', hball'⟩ := Metric.mem_nhds_iff.mp
      ((Complex.continuous_re.continuousAt.comp hh_cont).eventually (Ioi_mem_nhds hh_re_strict))
    let η := min (ρ / 2) (ε' / 2)
    have hη_pos : 0 < η := by positivity
    have hdist_ρ : |(x₀ - η) - x₀| < ρ := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη_pos]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hdist_ε' : |(x₀ - η) - x₀| < ε' := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hη_pos]
      exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have heq : g ((x₀ - η : ℝ) : ℂ) = (((x₀ - η : ℝ) : ℂ) - (x₀ : ℂ)) ^ m * h ((x₀ - η : ℝ) : ℂ) := by
      have heq0 := hball (by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact hdist_ρ.trans_le (min_le_right _ _))
      change g ((x₀ - η : ℝ) : ℂ) = (((x₀ - η : ℝ) : ℂ) - (x₀ : ℂ)) ^ m • h ((x₀ - η : ℝ) : ℂ) at heq0
      rw [smul_eq_mul] at heq0
      exact heq0
    rw [show (((x₀ - η : ℝ) : ℂ) - (x₀ : ℂ)) ^ m = ((((-η) ^ m : ℝ)) : ℂ) by push_cast; ring] at heq
    have hre_g : (g ((x₀ - η : ℝ) : ℂ)).re = (-η) ^ m * (h ((x₀ - η : ℝ) : ℂ)).re := by
      rw [heq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hpow_neg : (-η) ^ m < 0 := hodd.pow_neg_iff.mpr (by linarith)
    have hhpos : 0 < (h ((x₀ - η : ℝ) : ℂ)).re := hball' (by
      rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact hdist_ε')
    have hgnn := hnn _ (hdist_ρ.trans_le (min_le_left _ _))
    have hgre_neg : (g ((x₀ - η : ℝ) : ℂ)).re < 0 := by
      rw [hre_g]; exact mul_neg_of_neg_of_pos hpow_neg hhpos
    linarith
  obtain ⟨t, ht⟩ := heven; exact ⟨⟨t, ht⟩, by omega⟩

/-- **Theorem R `(R3)`, part 1**: unique simple real zero `s₁ n` near `s1`. -/
theorem theorem_R3_s1 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : RigidityFamilyPackage ι p) (hAtt : Att F.toBlowupFamilyPackage) :
    ∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
      (∀ z ∈ sphere (s1 : ℂ) r, F.Φ n z ≠ 0) ∧ zeroCount (F.Φ n) (s1 : ℂ) r = 1 ∧
      (F.s₁ n : ℂ) ∈ ball (s1 : ℂ) r ∧ F.Φ n (F.s₁ n : ℂ) = 0 ∧
      analyticOrderNatAt (F.Φ n) (F.s₁ n : ℂ) = 1 ∧
      (∀ z ∈ ball (s1 : ℂ) r, F.Φ n z = 0 → z = (F.s₁ n : ℂ)) := by
  obtain ⟨hs₁_lim, hΦunif, -⟩ := theorem_R1 F.toBlowupFamilyPackage hAtt
  let U : Set ℂ := ball (0 : ℂ) (‖(s1 : ℂ)‖ + 1)
  have hcU : (s1 : ℂ) ∈ U := exists_disc_in_ball le_rfl (mem_ball_self zero_lt_one)
  have hΦU : TendstoLocallyUniformlyOn F.Φ phiStar p U := hΦunif.mono (subset_univ U)
  have hFdU := F.holo_balls (‖(s1 : ℂ)‖ + 1)
  have hphiU : DifferentiableOn ℂ phiStar U := differentiable_phiStar.differentiableOn
  obtain ⟨ρ, hρ, hρU, hρne⟩ := exists_punctured_disc hphiU isOpen_ball hcU (phiStar_not_eventually_zero _)
  refine ⟨min (ρ / 2) (1 / 2), by positivity, fun r hr hle => ?_⟩
  have hrρ : r < ρ := lt_of_le_of_lt (hle.trans (min_le_left _ _)) (by linarith)
  have hsph : ∀ z ∈ sphere (s1 : ℂ) r, phiStar z ≠ 0 := fun z hz =>
    hρne z (by rw [mem_sphere.mp hz]; exact hr) (by rw [mem_sphere.mp hz]; exact hrρ)
  have hzc := hurwitz_zeroCount isOpen_ball hΦU hFdU hphiU hr hrρ hρU hsph
  have hzc_phi : zeroCount phiStar (s1 : ℂ) r = 1 := by
    rw [zeroCount_eq_orderNat (hphiU.mono hρU) hr hrρ hrρ hρne, analyticOrderNatAt_phiStar_s1]
  have hs1_ball : ∀ᶠ n in p, (F.s₁ n : ℂ) ∈ ball (s1 : ℂ) r :=
    (Complex.continuous_ofReal.tendsto s1 |>.comp hs₁_lim).eventually (isOpen_ball.mem_nhds (mem_ball_self hr))
  filter_upwards [hzc, hFdU, hs1_ball, F.s1_is_zero] with n ⟨hsph_n, hcnt_n⟩ hdn hs1_mem hs1_zero
  rw [hzc_phi] at hcnt_n
  have hdn_ball := hdn.mono hρU
  have huniq : ∀ z ∈ ball (s1 : ℂ) r, F.Φ n z = 0 → z = (F.s₁ n : ℂ) := fun z hz hfz =>
    eq_of_zeroCount_eq_one hdn_ball hr hrρ hsph_n hcnt_n hz hs1_mem hfz hs1_zero
  obtain ⟨hw, hgw⟩ := exists_nonzero_of_sphere hr hrρ hsph_n
  have hge1 : 1 ≤ analyticOrderNatAt (F.Φ n) (F.s₁ n : ℂ) := by
    have hnz := (orderNat_ne_zero_iff hdn_ball hw hgw (ball_subset_ball hrρ.le hs1_mem)).mpr hs1_zero; omega
  have hle1 : analyticOrderNatAt (F.Φ n) (F.s₁ n : ℂ) ≤ 1 := by
    rw [← hcnt_n]; exact analyticOrderNatAt_le_zeroCount hdn_ball hr hrρ hsph_n hs1_mem
  exact ⟨hsph_n, hcnt_n, hs1_mem, hs1_zero, le_antisymm hle1 hge1, huniq⟩

/-- **Theorem R `(R3)`, part 2**: near each higher node `sNode k` (`k ≥ 2`), `Φ n` has
`zeroCount = 2` (either one real double zero or a conjugate pair of simple zeros), converging to
`sNode k`. -/
theorem theorem_R3_node {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : RigidityFamilyPackage ι p) (hAtt : Att F.toBlowupFamilyPackage) {k : ℕ} (hk : 2 ≤ k) :
    ∃ r₀ > 0,
      (∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
        (∀ z ∈ sphere (sNode k : ℂ) r, F.Φ n z ≠ 0) ∧ zeroCount (F.Φ n) (sNode k : ℂ) r = 2 ∧
        ((∃ x : ℝ, (x : ℂ) ∈ ball (sNode k : ℂ) r ∧ F.Φ n (x : ℂ) = 0 ∧
            analyticOrderNatAt (F.Φ n) (x : ℂ) = 2 ∧
            ∀ z ∈ ball (sNode k : ℂ) r, F.Φ n z = 0 → z = (x : ℂ)) ∨
         (∃ z : ℂ, z ∈ ball (sNode k : ℂ) r ∧ z.im ≠ 0 ∧ F.Φ n z = 0 ∧
            F.Φ n (starRingEnd ℂ z) = 0 ∧ analyticOrderNatAt (F.Φ n) z = 1 ∧
            analyticOrderNatAt (F.Φ n) (starRingEnd ℂ z) = 1 ∧
            ∀ w ∈ ball (sNode k : ℂ) r, F.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z))) ∧
      (∀ ε > 0, ∀ᶠ n in p,
        (∃ z ∈ ball (sNode k : ℂ) r₀, F.Φ n z = 0) ∧
        ∀ z ∈ ball (sNode k : ℂ) r₀, F.Φ n z = 0 → z ∈ ball (sNode k : ℂ) ε) := by
  obtain ⟨hs₁_lim, hΦunif, -⟩ := theorem_R1 F.toBlowupFamilyPackage hAtt
  let c : ℂ := (sNode k : ℂ)
  let U : Set ℂ := ball (0 : ℂ) (‖c‖ + 1)
  have hcU : c ∈ U := exists_disc_in_ball le_rfl (mem_ball_self zero_lt_one)
  have hΦU : TendstoLocallyUniformlyOn F.Φ phiStar p U := hΦunif.mono (subset_univ U)
  have hFdU := F.holo_balls (‖c‖ + 1)
  have hsymU := F.real_symm (‖c‖ + 1)
  have hphiU : DifferentiableOn ℂ phiStar U := differentiable_phiStar.differentiableOn
  obtain ⟨ρ, hρ, hρU, hρne⟩ := exists_punctured_disc hphiU isOpen_ball hcU (phiStar_not_eventually_zero _)
  let r₀ := min (ρ / 2) ((sNode k - s1) / 4)
  have hr₀ : 0 < r₀ := lt_min (by positivity) (by linarith [s1_lt_sNode hk])
  have hr₀_prop : ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
      (∀ z ∈ sphere c r, F.Φ n z ≠ 0) ∧ zeroCount (F.Φ n) c r = 2 ∧
      ((∃ x : ℝ, (x : ℂ) ∈ ball c r ∧ F.Φ n (x : ℂ) = 0 ∧
          analyticOrderNatAt (F.Φ n) (x : ℂ) = 2 ∧ ∀ z ∈ ball c r, F.Φ n z = 0 → z = (x : ℂ)) ∨
       (∃ z : ℂ, z ∈ ball c r ∧ z.im ≠ 0 ∧ F.Φ n z = 0 ∧ F.Φ n (starRingEnd ℂ z) = 0 ∧
          analyticOrderNatAt (F.Φ n) z = 1 ∧ analyticOrderNatAt (F.Φ n) (starRingEnd ℂ z) = 1 ∧
          ∀ w ∈ ball c r, F.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z)) := fun r hr hle => by
    have hrρ : r < ρ := lt_of_le_of_lt (hle.trans (min_le_left _ _)) (by linarith)
    have hrgap : r < (sNode k - s1) / 2 :=
      lt_of_le_of_lt (hle.trans (min_le_right _ _)) (by linarith [s1_lt_sNode hk])
    have hsph : ∀ z ∈ sphere c r, phiStar z ≠ 0 := fun z hz =>
      hρne z (by rw [mem_sphere.mp hz]; exact hr) (by rw [mem_sphere.mp hz]; exact hrρ)
    have hzc := hurwitz_zeroCount isOpen_ball hΦU hFdU hphiU hr hrρ hρU hsph
    have hzc_phi : zeroCount phiStar c r = 2 := by
      rw [zeroCount_eq_orderNat (hphiU.mono hρU) hr hrρ hrρ hρne, analyticOrderNatAt_phiStar_sNode hk]
    have hs₁_lt := hs₁_lim.eventually (eventually_lt_nhds (by linarith [s1_lt_sNode hk] : s1 < s1 + (sNode k - s1) / 4))
    filter_upwards [hzc, hFdU, hsymU, F.nonneg_tail, hs₁_lt] with n ⟨hsph_n, hcnt_n⟩ hdn hsn hnn_n hs₁n
    rw [hzc_phi] at hcnt_n
    have hdn_ball := hdn.mono hρU
    obtain ⟨hw, hgw⟩ := exists_nonzero_of_sphere hr hrρ hsph_n
    have hfin := support_orderNat_finite hdn_ball hw hgw hrρ
    have hsum : ∑ w ∈ hfin.toFinset, analyticOrderNatAt (F.Φ n) w = 2 := by
      rw [← hcnt_n]; unfold zeroCount; rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
    have hmem_iff : ∀ w, w ∈ hfin.toFinset ↔ w ∈ ball c r ∧ F.Φ n w = 0 := fun w => by
      rw [hfin.mem_toFinset, mem_inter_iff, Function.mem_support]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (orderNat_ne_zero_iff hdn_ball hw hgw (ball_subset_ball hrρ.le h1)).mp h2⟩,
        fun ⟨h1, h2⟩ => ⟨h1, (orderNat_ne_zero_iff hdn_ball hw hgw (ball_subset_ball hrρ.le h1)).mpr h2⟩⟩
    have hord_pos : ∀ w ∈ hfin.toFinset, 1 ≤ analyticOrderNatAt (F.Φ n) w := fun w hw' => by
      simp only [hfin.mem_toFinset, mem_inter_iff, Function.mem_support, ne_eq] at hw'; omega
    refine ⟨hsph_n, hcnt_n, ?_⟩
    by_cases hreal_zero : ∃ x : ℝ, (x : ℂ) ∈ ball c r ∧ F.Φ n (x : ℂ) = 0
    · left
      obtain ⟨x, hx_ball, hfx⟩ := hreal_zero
      have hx_diff : 0 < r - dist (x : ℂ) c := sub_pos.mpr (mem_ball.mp hx_ball)
      have hx_sub : ball (x : ℂ) (r - dist (x : ℂ) c) ⊆ ball c r := ball_subset_ball' (by linarith)
      have hx_ball_ρ := hx_sub.trans (ball_subset_ball hrρ.le)
      have hne_x : ∃ w ∈ ball (x : ℂ) (r - dist (x : ℂ) c), F.Φ n w ≠ 0 := by
        by_contra hcon; push Not at hcon
        have han := hdn_ball.analyticOnNhd isOpen_ball
        exact hgw (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball c ρ).isPreconnected
          (ball_subset_ball hrρ.le hx_ball) (Eventually.mono (isOpen_ball.mem_nhds (mem_ball_self hx_diff)) hcon) hw)
      have hreal_x : ∀ y : ℝ, |y - x| < r - dist (x : ℂ) c → (F.Φ n (y : ℂ)).im = 0 := fun y hy => by
        have hsym := hsn (y : ℂ) (hρU (hx_ball_ρ (by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hy)))
        rw [Complex.conj_ofReal] at hsym; have := congrArg Complex.im hsym; simp at this; linarith
      have hnn_x : ∀ y : ℝ, |y - x| < r - dist (x : ℂ) c → 0 ≤ (F.Φ n (y : ℂ)).re := fun y hy => by
        have hball_y : (y : ℂ) ∈ ball c r := hx_sub (by
          rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hy)
        have hyn : |y - sNode k| < r := by
          rw [← Real.norm_eq_abs, ← Complex.norm_real]
          simpa [c, Complex.ofReal_sub, dist_eq_norm] using mem_ball.mp hball_y
        exact hnn_n y (by linarith [(abs_lt.mp hyn).1])
      obtain ⟨_, hord_ge2⟩ := even_analyticOrderNatAt_of_nonneg_real (hdn_ball.mono hx_ball_ρ)
        hx_diff hx_diff hne_x hreal_x hnn_x hfx
      have hx_fin := (hmem_iff (x : ℂ)).mpr ⟨hx_ball, hfx⟩
      have hord_eq2 : analyticOrderNatAt (F.Φ n) (x : ℂ) = 2 :=
        le_antisymm (by rw [← hsum]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx_fin) hord_ge2
      refine ⟨x, hx_ball, hfx, hord_eq2, fun z hz hfz => ?_⟩
      by_contra hzx
      have hz_fin := (hmem_iff z).mpr ⟨hz, hfz⟩
      have hpair : ∑ w ∈ ({z, (x : ℂ)} : Finset ℂ), analyticOrderNatAt (F.Φ n) w ≤ 2 := by
        rw [← hsum]
        refine Finset.sum_le_sum_of_subset fun w hw' => ?_
        rcases Finset.mem_insert.mp hw' with rfl | hw'
        · exact hz_fin
        · rw [Finset.mem_singleton.mp hw']; exact hx_fin
      rw [Finset.sum_pair hzx, hord_eq2] at hpair; have := hord_pos z hz_fin; omega
    · right
      push Not at hreal_zero
      obtain ⟨z, hz_ball, hfz⟩ := exists_zero_of_zeroCount_ne_zero (by rw [hcnt_n]; norm_num)
      have hzim : z.im ≠ 0 := fun him =>
        hreal_zero z.re (by simpa [Complex.ext (by simp : (z.re : ℂ).re = z.re) (by simp [him])] using hz_ball)
          (by simpa [Complex.ext (by simp : (z.re : ℂ).re = z.re) (by simp [him])] using hfz)
      have hzc_ball : starRingEnd ℂ z ∈ ball c r := by
        rw [mem_ball, dist_eq_norm] at hz_ball ⊢
        rwa [show starRingEnd ℂ z - c = starRingEnd ℂ (z - c) by simp [c], Complex.norm_conj]
      have hfzc : F.Φ n (starRingEnd ℂ z) = 0 := by
        rw [hsn z (hρU (ball_subset_ball hrρ.le hz_ball)), hfz]; simp
      have hzne : z ≠ starRingEnd ℂ z := fun heq => by
        have := congrArg Complex.im heq; simp at this; exact hzim (by linarith)
      have hz_fin := (hmem_iff z).mpr ⟨hz_ball, hfz⟩
      have hzc_fin := (hmem_iff _).mpr ⟨hzc_ball, hfzc⟩
      have hpair : ∑ w ∈ ({z, starRingEnd ℂ z} : Finset ℂ), analyticOrderNatAt (F.Φ n) w ≤ 2 := by
        rw [← hsum]
        refine Finset.sum_le_sum_of_subset fun w hw' => ?_
        rcases Finset.mem_insert.mp hw' with rfl | hw'
        · exact hz_fin
        · rw [Finset.mem_singleton.mp hw']; exact hzc_fin
      rw [Finset.sum_pair hzne] at hpair
      have h1 := hord_pos z hz_fin; have h2 := hord_pos _ hzc_fin
      have hord_z : analyticOrderNatAt (F.Φ n) z = 1 := by omega
      have hord_zc : analyticOrderNatAt (F.Φ n) (starRingEnd ℂ z) = 1 := by omega
      refine ⟨z, hz_ball, hzim, hfz, hfzc, hord_z, hord_zc, fun w hw_ball hfw => ?_⟩
      by_contra hnot; push Not at hnot
      have hw_fin := (hmem_iff w).mpr ⟨hw_ball, hfw⟩
      have htri : ∑ u ∈ insert w ({z, starRingEnd ℂ z} : Finset ℂ), analyticOrderNatAt (F.Φ n) u ≤ 2 := by
        rw [← hsum]
        refine Finset.sum_le_sum_of_subset fun u hu' => ?_
        rcases Finset.mem_insert.mp hu' with rfl | hu'
        · exact hw_fin
        · rcases Finset.mem_insert.mp hu' with rfl | hu'
          · exact hz_fin
          · rw [Finset.mem_singleton.mp hu']; exact hzc_fin
      rw [Finset.sum_insert (by simp [hnot.1, hnot.2]), Finset.sum_pair hzne, hord_z, hord_zc] at htri
      have := hord_pos w hw_fin; omega
  refine ⟨r₀, hr₀, hr₀_prop, fun ε hε => ?_⟩
  let r := min ε r₀
  have hr : 0 < r := lt_min hε hr₀
  have hr_le_r₀ : r ≤ r₀ := min_le_right _ _
  have hr_le_ε : r ≤ ε := min_le_left _ _
  have hr₀ρ : r₀ < ρ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  filter_upwards [hr₀_prop r₀ hr₀ le_rfl, hr₀_prop r hr hr_le_r₀, hFdU] with n hn0 hnr hdn
  have hex : ∃ z ∈ ball c r₀, F.Φ n z = 0 :=
    exists_zero_of_zeroCount_ne_zero (by rw [hn0.2.1]; norm_num)
  refine ⟨hex, fun z hz hfz => ?_⟩
  obtain ⟨hw0, hgw0⟩ := exists_nonzero_of_sphere hr₀ hr₀ρ hn0.1
  have hdn_ball := hdn.mono hρU
  have hfin0 := support_orderNat_finite hdn_ball hw0 hgw0 hr₀ρ
  have hsum0 : ∑ u ∈ hfin0.toFinset, analyticOrderNatAt (F.Φ n) u = 2 := by
    rw [← hn0.2.1]; unfold zeroCount; rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin0]
  have hmem0 : ∀ u, u ∈ ball c r₀ → F.Φ n u = 0 → u ∈ hfin0.toFinset := fun u hu hfu =>
    hfin0.mem_toFinset.mpr ⟨hu, (orderNat_ne_zero_iff hdn_ball hw0 hgw0 (ball_subset_ball hr₀ρ.le hu)).mpr hfu⟩
  have hpos0 : ∀ u ∈ hfin0.toFinset, 1 ≤ analyticOrderNatAt (F.Φ n) u := fun u hu => by
    simp only [hfin0.mem_toFinset, mem_inter_iff, Function.mem_support, ne_eq] at hu; omega
  rcases hnr.2.2 with ⟨x, hx_ball, hfx, hx_ord, -⟩ | ⟨w, hw_ball, hwim, hfw, hfwc, -, -, -⟩
  · have hx0 := ball_subset_ball hr_le_r₀ hx_ball
    have hzx : z = (x : ℂ) := by
      by_contra hne
      have hpair : ∑ u ∈ ({z, (x : ℂ)} : Finset ℂ), analyticOrderNatAt (F.Φ n) u ≤ 2 := by
        rw [← hsum0]
        refine Finset.sum_le_sum_of_subset fun u hu => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with huz | hux
        · rw [huz]; exact hmem0 z hz hfz
        · rw [hux]; exact hmem0 (x : ℂ) hx0 hfx
      rw [Finset.sum_pair hne, hx_ord] at hpair; have := hpos0 z (hmem0 z hz hfz); omega
    rw [hzx]; exact ball_subset_ball hr_le_ε hx_ball
  · have hwc_ball : starRingEnd ℂ w ∈ ball c r := by
      rw [mem_ball, dist_eq_norm] at hw_ball ⊢
      rwa [show starRingEnd ℂ w - c = starRingEnd ℂ (w - c) by simp [c], Complex.norm_conj]
    have hw0 := ball_subset_ball hr_le_r₀ hw_ball
    have hwc0 := ball_subset_ball hr_le_r₀ hwc_ball
    have hw_ne : w ≠ starRingEnd ℂ w := fun heq =>
      hwim (by have := congrArg Complex.im heq; simp at this; linarith)
    have hzw : z = w ∨ z = starRingEnd ℂ w := by
      by_contra hnot; push Not at hnot
      have htri : ∑ u ∈ insert z ({w, starRingEnd ℂ w} : Finset ℂ), analyticOrderNatAt (F.Φ n) u ≤ 2 := by
        rw [← hsum0]
        refine Finset.sum_le_sum_of_subset fun u hu => ?_
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with huz | huw | huwc
        · rw [huz]; exact hmem0 z hz hfz
        · rw [huw]; exact hmem0 w hw0 hfw
        · rw [huwc]; exact hmem0 _ hwc0 hfwc
      rw [Finset.sum_insert (by simp [hnot.1, hnot.2]), Finset.sum_pair hw_ne] at htri
      have := hpos0 z (hmem0 z hz hfz); have := hpos0 w (hmem0 w hw0 hfw)
      have := hpos0 _ (hmem0 _ hwc0 hfwc); omega
    rcases hzw with rfl | rfl
    · exact ball_subset_ball hr_le_ε hw_ball
    · exact ball_subset_ball hr_le_ε hwc_ball

/-- **Theorem R `(R3)`, part 3**: compact sets disjoint from all Airy nodes are eventually zero-free. -/
theorem theorem_R3_compact_disjoint {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : RigidityFamilyPackage ι p) (hAtt : Att F.toBlowupFamilyPackage)
    {K : Set ℂ} (hK : IsCompact K) (hdisj : ∀ k : ℕ, 1 ≤ k → (sNode k : ℂ) ∉ K) :
    ∀ᶠ n in p, ∀ z ∈ K, F.Φ n z ≠ 0 := by
  obtain ⟨_, hΦunif, -⟩ := theorem_R1 F.toBlowupFamilyPackage hAtt
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  have hz : ∀ z ∈ K, phiStar z = 0 → z ∈ (∅ : Set ℂ) := fun z hzK hfz => by
    obtain ⟨k, hk, rfl⟩ := (phiStar_eq_zero_iff z).mp hfz; exact hdisj k hk hzK
  simpa using hurwitz_no_zeros_off isOpen_ball (hΦunif.mono (subset_univ _))
    ((F.holo_balls R).mono fun _ hd => hd.continuousOn) hK hR isOpen_empty hz

/-- **Theorem R `(R3)`, part 4**: rescaling `tScale` sends any sequence `z n → sNode k` to
`(|a_k|/|a_1|) Aopt` and (for `k = 2`) `(ζ₂ - t₁) / c^(1/3) → (|a_2|/|a_1| - 1) Aopt`. -/
theorem theorem_R3_tScale_tendsto {ι : Type*} {p : Filter ι}
    (F : RigidityFamilyPackage ι p) (hAtt : Att F.toBlowupFamilyPackage)
    {k : ℕ} (hk : 1 ≤ k) {z : ι → ℂ} (hz : Tendsto z p (nhds (sNode k : ℂ))) :
    Tendsto (fun n => (tScale (F.c' n) (z n) - ((xiBar * F.c' n : ℝ) : ℂ)) /
        (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p
      (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) ∧
    (k = 2 →
      Tendsto (fun n => (tScale (F.c' n) (z n) - (F.t₁ n : ℂ)) /
          ((((F.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ))) p
        (nhds ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ)))) := by
  have heq : ∀ᶠ n in p,
      (tScale (F.c' n) (z n) - ((xiBar * F.c' n : ℝ) : ℂ)) /
        (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ) =
      (((2 / 3 : ℝ) * xiStar : ℝ) : ℂ) * z n +
        (((1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * z n ^ 2 := by
    filter_upwards [F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hc'1
    have hc'0 : 0 < F.c' n := by linarith
    have hp13 : (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hc'0 _).ne'
    have hmul1 : F.c' n * (F.c' n) ^ (-(2 / 3 : ℝ)) = (F.c' n) ^ (1 / 3 : ℝ) := by
      rw [show F.c' n * (F.c' n) ^ (-(2 / 3 : ℝ)) = (F.c' n) ^ (1 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) by
        rw [Real.rpow_one], ← Real.rpow_add hc'0]; congr 1; norm_num
    have hmul2 : F.c' n * ((F.c' n) ^ (-(2 / 3 : ℝ))) ^ 2 = (F.c' n) ^ (-(1 / 3 : ℝ)) := by
      have hsq : ((F.c' n) ^ (-(2 / 3 : ℝ))) ^ 2 = (F.c' n) ^ (-(4 / 3 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc'0.le]; norm_num
      rw [hsq, show F.c' n * (F.c' n) ^ (-(4 / 3 : ℝ)) = (F.c' n) ^ (1 : ℝ) * (F.c' n) ^ (-(4 / 3 : ℝ)) by
        rw [Real.rpow_one], ← Real.rpow_add hc'0]; congr 1; norm_num
    have hmul3 : (F.c' n) ^ (-(1 / 3 : ℝ)) / (F.c' n) ^ (1 / 3 : ℝ) = (F.c' n) ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hc'0.le, ← Real.rpow_add hc'0]; congr 1; norm_num
    unfold tScale xiBar
    have hnum : ((F.c' n / 3 : ℝ) : ℂ) * ((xiStar : ℂ) + (((F.c' n) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * z n) ^ 2 -
          ((xiStar ^ 2 / 3 * F.c' n : ℝ) : ℂ) =
        (((2 / 3 : ℝ) * xiStar * (F.c' n * (F.c' n) ^ (-(2 / 3 : ℝ))) : ℝ) : ℂ) * z n +
          (((1 / 3 : ℝ) * (F.c' n * ((F.c' n) ^ (-(2 / 3 : ℝ))) ^ 2) : ℝ) : ℂ) * z n ^ 2 := by
      push_cast; ring
    rw [hnum, hmul1, hmul2, ← hmul3]; push_cast; field_simp [hp13]
  have hc'neg : Tendsto (fun n => (F.c' n) ^ (-(2 / 3 : ℝ))) p (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp F.hc'_tendsto
  have hmain : Tendsto (fun n => (tScale (F.c' n) (z n) - ((xiBar * F.c' n : ℝ) : ℂ)) /
      (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) := by
    have hc'negC : Tendsto (fun n => (((1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ)) p (nhds 0) := by
      have h0 := hc'neg.const_mul (1 / 3 : ℝ); rw [mul_zero] at h0
      exact (Complex.continuous_ofReal.tendsto 0).comp h0
    have h1 : Tendsto (fun n => (((2 / 3 : ℝ) * xiStar : ℝ) : ℂ) * z n +
        (((1 / 3 : ℝ) * (F.c' n) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) * z n ^ 2) p
        (nhds ((((2 / 3 : ℝ) * xiStar : ℝ) : ℂ) * (sNode k : ℂ) + 0)) :=
      (tendsto_const_nhds.mul hz).add (by simpa using hc'negC.mul (hz.pow 2))
    rw [add_zero, ← Complex.ofReal_mul, two_thirds_xiStar_mul_sNode] at h1
    exact h1.congr' (heq.mono fun _ h => h.symm)
  refine ⟨hmain, ?_⟩
  rintro rfl
  have hratio_real : Tendsto (fun n => (F.c' n) ^ (1 / 3 : ℝ) / (F.c' n + 1) ^ (1 / 3 : ℝ)) p (nhds 1) := by
    have hdiv : Tendsto (fun n => F.c' n / (F.c' n + 1)) p (nhds 1) := by
      have heq_r : ∀ᶠ n in p, F.c' n / (F.c' n + 1) = 1 - (F.c' n + 1)⁻¹ := by
        filter_upwards [F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hc'1
        field_simp [show F.c' n + 1 ≠ 0 by linarith]; ring
      have hinv := tendsto_inv_atTop_zero.comp (F.hc'_tendsto.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
      simpa using (tendsto_const_nhds.sub hinv).congr' (heq_r.mono fun _ h => h.symm)
    have hrpow := (Real.continuousAt_rpow_const 1 (1 / 3 : ℝ) (Or.inl one_ne_zero)).tendsto.comp hdiv
    rw [Real.one_rpow] at hrpow
    refine hrpow.congr' ?_
    filter_upwards [F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hc'1
    dsimp only [Function.comp_def]
    exact Real.div_rpow (show 0 ≤ F.c' n by linarith) (show 0 ≤ F.c' n + 1 by linarith) (1 / 3 : ℝ)
  have hratio : Tendsto (fun n => (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ) /
      (((F.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p (nhds 1) :=
    ((Complex.continuous_ofReal.tendsto 1).comp hratio_real).congr fun n => by
      dsimp only [Function.comp_def]; push_cast; rfl
  have hAttC : Tendsto (fun n =>
      (((F.t₁ n - xiBar * F.c' n) / (F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p (nhds (Aopt : ℂ)) :=
    (Complex.continuous_ofReal.tendsto Aopt).comp hAtt
  have hprod := (hmain.sub hAttC).mul hratio
  rw [show ((((|airyZero 2| / |airyZero 1|) * Aopt : ℝ) : ℂ) - (Aopt : ℂ)) * 1 =
      ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ)) by push_cast; ring] at hprod
  refine hprod.congr' ?_
  filter_upwards [F.hc'_tendsto.eventually (eventually_ge_atTop (1 : ℝ))] with n hc'1
  have hp13 : (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by linarith) _).ne'
  have hp13_add : (((F.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos (by linarith) _).ne'
  push_cast; field_simp [hp13, hp13_add]; ring

/-- **Theorem R `(R3)`** (`rigidity.tex`): full combined statement of local Hurwitz zero
counts, real-double-or-conjugate-pair structure, compact zero-free regions, and scaling limits. -/
theorem theorem_R3 {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    (F : RigidityFamilyPackage ι p) (hAtt : Att F.toBlowupFamilyPackage) :
    (∃ r₀ > 0, ∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
      zeroCount (F.Φ n) (s1 : ℂ) r = 1 ∧ (F.s₁ n : ℂ) ∈ ball (s1 : ℂ) r ∧
      F.Φ n (F.s₁ n : ℂ) = 0 ∧ analyticOrderNatAt (F.Φ n) (F.s₁ n : ℂ) = 1 ∧
      ∀ z ∈ ball (s1 : ℂ) r, F.Φ n z = 0 → z = (F.s₁ n : ℂ)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ r₀ > 0,
      (∀ r, 0 < r → r ≤ r₀ → ∀ᶠ n in p,
        zeroCount (F.Φ n) (sNode k : ℂ) r = 2 ∧
        ((∃ x : ℝ, (x : ℂ) ∈ ball (sNode k : ℂ) r ∧ F.Φ n (x : ℂ) = 0 ∧
            analyticOrderNatAt (F.Φ n) (x : ℂ) = 2 ∧
            ∀ z ∈ ball (sNode k : ℂ) r, F.Φ n z = 0 → z = (x : ℂ)) ∨
         (∃ z : ℂ, z ∈ ball (sNode k : ℂ) r ∧ z.im ≠ 0 ∧ F.Φ n z = 0 ∧
            F.Φ n (starRingEnd ℂ z) = 0 ∧ analyticOrderNatAt (F.Φ n) z = 1 ∧
            analyticOrderNatAt (F.Φ n) (starRingEnd ℂ z) = 1 ∧
            ∀ w ∈ ball (sNode k : ℂ) r, F.Φ n w = 0 → w = z ∨ w = starRingEnd ℂ z))) ∧
      (∀ z : ι → ℂ, (∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ F.Φ n (z n) = 0) →
        Tendsto z p (nhds (sNode k : ℂ)) ∧
        Tendsto (fun n => (tScale (F.c' n) (z n) - ((xiBar * F.c' n : ℝ) : ℂ)) /
            (((F.c' n) ^ (1 / 3 : ℝ) : ℝ) : ℂ)) p
          (nhds ((((|airyZero k| / |airyZero 1|) * Aopt : ℝ) : ℂ))) ∧
        (k = 2 →
          Tendsto (fun n => (tScale (F.c' n) (z n) - (F.t₁ n : ℂ)) /
              ((((F.c' n + 1) ^ (1 / 3 : ℝ) : ℝ) : ℂ))) p
            (nhds ((((|airyZero 2| / |airyZero 1| - 1) * Aopt : ℝ) : ℂ))))) ∧
      (∃ z : ι → ℂ, ∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ F.Φ n (z n) = 0)) ∧
    (∀ K : Set ℂ, IsCompact K → (∀ k : ℕ, 1 ≤ k → (sNode k : ℂ) ∉ K) →
      ∀ᶠ n in p, ∀ z ∈ K, F.Φ n z ≠ 0) := by
  classical
  refine ⟨?_, fun k hk => ?_, fun K hK hdisj => theorem_R3_compact_disjoint F hAtt hK hdisj⟩
  · obtain ⟨r₀, hr₀, h1⟩ := theorem_R3_s1 F hAtt
    exact ⟨r₀, hr₀, fun r hr hle => (h1 r hr hle).mono fun _ hn => hn.2⟩
  · obtain ⟨r₀, hr₀, hnode, hconv⟩ := theorem_R3_node F hAtt hk
    have hsel : ∀ z : ι → ℂ, (∀ᶠ n in p, z n ∈ ball (sNode k : ℂ) r₀ ∧ F.Φ n (z n) = 0) →
        Tendsto z p (nhds (sNode k : ℂ)) := fun z hz => by
      rw [Metric.tendsto_nhds]; intro ε hε
      filter_upwards [hz, hconv ε hε] with n ⟨hz_mem, hfz⟩ ⟨_, hball_ε⟩
      simpa [mem_ball] using hball_ε (z n) hz_mem hfz
    refine ⟨r₀, hr₀, fun r hr hle => (hnode r hr hle).mono fun _ hn => hn.2, fun z hz => ?_, ?_⟩
    · exact ⟨hsel z hz, theorem_R3_tScale_tendsto F hAtt (by omega) (hsel z hz)⟩
    · refine ⟨fun n => if h : ∃ w ∈ ball (sNode k : ℂ) r₀, F.Φ n w = 0 then h.choose else 0, ?_⟩
      filter_upwards [(hconv 1 one_pos).mono fun _ hn => hn.1] with n hn
      rw [dite_eq_left hn]
      exact hn.choose_spec

/-! ### Section 6: Non-vacuity sanity check -/

/-- **Non-vacuity sanity theorem**: the constant family `Φₙ := phiStar`, `γₙ := 0`, `s₁ := s1`,
`c' n := n + 40` satisfies every hypothesis of `RigidityFamilyPackage` and `Att`. -/
theorem rigidity_hypotheses_nonvacuous :
    ∃ F : RigidityFamilyPackage ℕ atTop, Att F.toBlowupFamilyPackage := by
  let c' : ℕ → ℝ := fun n => (n : ℝ) + 40
  let s₁ : ℕ → ℝ := fun _ => s1
  let t₁ : ℕ → ℝ := fun n =>
    xiBar * c' n + (2 / 3 : ℝ) * xiStar * (c' n) ^ (1 / 3 : ℝ) * s1 +
      (1 / 3 : ℝ) * (c' n) ^ (-(1 / 3 : ℝ)) * s1 ^ 2
  have hc'_tend : Tendsto c' atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  obtain ⟨C₀, hC₀nn, hC₀b⟩ := airyExtremal_bound
  have hphi_bound : ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, ‖phiStar s‖ ≤ C * (1 + ‖s‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * s) := by
    let C := (2 * LStar)⁻¹ * betaTip * C₀
    have h2L_pos : 0 < 2 * LStar := by have := LStar_pos; positivity
    refine ⟨C, by have := betaTip_pos; positivity, fun s => ?_⟩
    have h1 : ‖phiStar s‖ = (2 * LStar)⁻¹ * betaTip * ‖airyExtremal (-(betaTip : ℂ) * s)‖ := by
      unfold phiStar localExtremalC
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos LStar_pos,
        abs_of_pos betaTip_pos]
      ring
    have h2 := hC₀b (-(betaTip : ℂ) * s)
    rw [Real.rpow_zero, mul_one] at h2
    have h3 : 1 ≤ (1 + ‖s‖) ^ (1 / 2 : ℝ) :=
      Real.one_le_rpow (by linarith [norm_nonneg s]) (by norm_num)
    have h4 : C₀ * airyEnv (-(betaTip : ℂ) * s) ≤
        C₀ * (1 + ‖s‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * s) := by
      have henv := (airyEnv_pos (-(betaTip : ℂ) * s)).le
      nlinarith [mul_nonneg hC₀nn henv]
    rw [h1]
    calc (2 * LStar)⁻¹ * betaTip * ‖airyExtremal (-(betaTip : ℂ) * s)‖
        ≤ (2 * LStar)⁻¹ * betaTip * (C₀ * airyEnv (-(betaTip : ℂ) * s)) := by
          gcongr; have := betaTip_pos; positivity
      _ ≤ (2 * LStar)⁻¹ * betaTip *
            (C₀ * (1 + ‖s‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * s)) := by
          gcongr; have := betaTip_pos; positivity
      _ = C * (1 + ‖s‖) ^ (1 / 2 : ℝ) * airyEnv (-(betaTip : ℂ) * s) := by dsimp [C]; ring
  have hphi_re_zero : (∫ s : ℝ, (phiStar (s : ℂ)).re) = 0 := by
    have hre := integral_re phiStar_integrable
    change (∫ s : ℝ, (phiStar (s : ℂ)).re) = (∫ s : ℝ, phiStar (s : ℂ)).re at hre
    rw [hre, phiStar_integral, Complex.zero_re]
  have hphi_neg_half : (1 / 2 : ℝ) ≤ ∫ s : ℝ, max 0 (-(phiStar (s : ℂ)).re) := by
    have h2 := integral_norm_eq_two_mul_neg_part phiStar_integrable phiStar_im hphi_re_zero
    rw [phiStar_norm_integral] at h2; linarith
  have hdom_norm : Tendsto
      (fun n => ∫ s in Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ)), ‖phiStar (s : ℂ)‖) atTop (nhds 1) := by
    rw [← phiStar_norm_integral]
    have hleft : Tendsto (fun n => -xiStar * (c' n) ^ (2 / 3 : ℝ)) atTop atBot := by
      simpa [neg_mul] using tendsto_neg_atBot_iff.mpr
        (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_tend).const_mul_atTop xiStar_pos)
    have heq : ∀ n : ℕ, ∫ s in Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ)), ‖phiStar (s : ℂ)‖ =
        ∫ s : ℝ, (Ioi (-xiStar * (c' n) ^ (2 / 3 : ℝ))).indicator (fun t => ‖phiStar (t : ℂ)‖) s :=
      fun n => (integral_indicator measurableSet_Ioi).symm
    simp_rw [heq]
    refine tendsto_integral_of_dominated_convergence (fun s => ‖phiStar (s : ℂ)‖)
      (fun n => (phiStar_integrable.norm.indicator measurableSet_Ioi).aestronglyMeasurable)
      phiStar_integrable.norm
      (fun n => Eventually.of_forall fun s => by
        rw [Real.norm_of_nonneg (indicator_nonneg (fun _ _ => norm_nonneg _) _)]
        simp only [Set.indicator]; split_ifs
        · exact le_rfl
        · exact norm_nonneg _)
      (Eventually.of_forall fun s =>
        tendsto_const_nhds.congr' ((hleft.eventually (eventually_lt_atBot s)).mono fun _ hn =>
          (indicator_of_mem hn _).symm))
  have hconst_unif : TendstoLocallyUniformlyOn (fun _ : ℕ => phiStar) phiStar atTop univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ _; rw [Metric.tendstoUniformlyOn_iff]; intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa using hε
  let B : BlowupFamilyPackage ℕ atTop :=
    { c' := c', s₁ := s₁, t₁ := t₁, Φ := fun _ => phiStar, γ := fun _ => 0
      hc'_tendsto := hc'_tend
      hγ_nonneg := Eventually.of_forall fun _ => le_rfl
      scaling_eq := Eventually.of_forall fun _ => rfl
      theorem_A_lower := ⟨0, Eventually.of_forall fun _ => by simp [s₁, s1_pos.le]⟩
      propT_subseq := fun _ _ _ =>
        ⟨id, s1, phiStar, 0, 0, strictMono_id, tendsto_const_nhds,
          hconst_unif, tendsto_const_nhds, differentiable_phiStar,
          phiStar_integrable, hphi_bound, phiStar_ne_zero, phiStar_im,
          fun _ hs => phiStar_nonneg hs, phiStar_norm_integral.le, le_rfl, le_rfl,
          by simpa using hphi_re_zero, hphi_neg_half⟩ }
  let R : RigidityFamilyPackage ℕ atTop :=
    { toBlowupFamilyPackage := B
      domain_integrable := Eventually.of_forall fun _ => phiStar_integrable.integrableOn
      domain_norm_integral := hdom_norm
      holo_balls := fun _ => Eventually.of_forall fun _ => differentiable_phiStar.differentiableOn
      real_symm := fun _ => Eventually.of_forall fun _ z _ => conj_phiStar z
      nonneg_tail := Eventually.of_forall fun _ _ hs => phiStar_nonneg hs
      s1_is_zero := Eventually.of_forall fun _ =>
        (phiStar_eq_zero_iff (s1 : ℂ)).mpr ⟨1, le_rfl, rfl⟩ }
  refine ⟨R, ?_⟩
  have hexc : ∀ n : ℕ, (t₁ n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ) =
      Aopt + (1 / 3 : ℝ) * (c' n) ^ (-(2 / 3 : ℝ)) * s1 ^ 2 := fun n => by
    have hc'0 : 0 < c' n := by dsimp [c']; positivity
    have hp13 : 0 < (c' n) ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc'0 _
    have hpow : (c' n) ^ (-(1 / 3 : ℝ)) / (c' n) ^ (1 / 3 : ℝ) = (c' n) ^ (-(2 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg hc'0.le, ← Real.rpow_add hc'0]; congr 1; norm_num
    dsimp [t₁]
    rw [show xiBar * c' n + 2 / 3 * xiStar * (c' n) ^ (1 / 3 : ℝ) * s1 +
        1 / 3 * (c' n) ^ (-(1 / 3 : ℝ)) * s1 ^ 2 - xiBar * c' n =
        2 / 3 * xiStar * (c' n) ^ (1 / 3 : ℝ) * s1 +
          1 / 3 * (c' n) ^ (-(1 / 3 : ℝ)) * s1 ^ 2 by ring, add_div]
    rw [show 2 / 3 * xiStar * (c' n) ^ (1 / 3 : ℝ) * s1 / (c' n) ^ (1 / 3 : ℝ) = Aopt by
      rw [Aopt_eq_mul_s1]; field_simp [hp13.ne'],
      show 1 / 3 * (c' n) ^ (-(1 / 3 : ℝ)) * s1 ^ 2 / (c' n) ^ (1 / 3 : ℝ) =
        1 / 3 * (c' n) ^ (-(2 / 3 : ℝ)) * s1 ^ 2 by rw [← hpow]; ring]
  change Tendsto (fun n => (t₁ n - xiBar * c' n) / (c' n) ^ (1 / 3 : ℝ)) atTop (nhds Aopt)
  simp_rw [hexc]
  have hquad : Tendsto (fun n => (1 / 3 : ℝ) * (c' n) ^ (-(2 / 3 : ℝ)) * s1 ^ 2) atTop (nhds 0) := by
    have h0 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hc'_tend).const_mul (1 / 3 : ℝ)
    simpa using h0.mul_const (s1 ^ 2)
  simpa using tendsto_const_nhds.add hquad

/-! ### Axiom checks for all headline theorems -/
/-- info: 'FormalResearch.ModularBootstrap.local_sign_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.local_sign_uncertainty

/-- info: 'FormalResearch.ModularBootstrap.local_sign_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.local_sign_equality

/-- info: 'FormalResearch.ModularBootstrap.theorem_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.theorem_C

/-- info: 'FormalResearch.ModularBootstrap.att_tendsto_s1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.att_tendsto_s1

/-- info: 'FormalResearch.ModularBootstrap.theorem_R1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.theorem_R1

/-- info: 'FormalResearch.ModularBootstrap.theorem_R2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.theorem_R2

/-- info: 'FormalResearch.ModularBootstrap.theorem_R3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.theorem_R3

/-- info: 'FormalResearch.ModularBootstrap.rigidity_hypotheses_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.rigidity_hypotheses_nonvacuous

end FormalResearch.ModularBootstrap

module

public import Mathlib
public import FormalResearch.SignUncertainty.CtCombinedTop
public import FormalResearch.SignUncertainty.CtLangerEdgeChart
public import FormalResearch.SignUncertainty.CtRoscAssembly
public import FormalResearch.SignUncertainty.CtBoasLmin

/-!
# `ct:dyadic` (4), the transition band

`constant_terms_lower.tex`, proof of `ct:dyadic` (4) / `(ct:combined)`, the transition band `v' ∈ [v₀, R']`. Provides the decomposition
`ct_trans_decomp` and rate bound `trans_rate_bound` (`∫_{ξ ≥ ξ(-v₀)} w̃ sin X dm - s₂ - ∫_{ξ>ξ(-R')} sin X dm = O(c^{-4/3})`) consumed
by `CtLowerLogFreeSkeleton.ct_combined_trans_sharp`, using the chart identification `ct_langer_edge` (`CtLangerEdgeChart`):

* `phase_remainder`, `ct_trans_phase_pt`: at one point, `X = (4/3)v'^{3/2} + 2√v'δ` (`(ct:theta-cfu-match)`: `2v'^{1/2}(v - v') = -θ_ε(τ₀)`,
  `v - v' = δ = -λψ_ε ∈ (0, λM]`) and `|sin X - sin((4/3)v^{3/2})| ≤ (2/3)δ²/√v'`;
* `trans_weight_bound`, `ct_trans_E1`: against `w̃ ≤ 2((v'+δ)/R)^{12}` and the top-scale first moment `∫ v'|h| ≤ Kc^{1/3}`;
* `ct_trans_transport`: `s₂` in the Langer variable `x = ũ`, `L = log π²ξ(x)`, with the transport error `R' r_∞`;
* `ct_trans_decomp`, `trans_rate_bound`: the assembly with the taper estimate `boas_field_trunc_lo` for `L < L_min`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `v^{3/2} = v √v`. -/
lemma ct_rpow32 {v : ℝ} (hv : 0 ≤ v) : v ^ (3 / 2 : ℝ) = v * Real.sqrt v := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hv (by norm_num), Real.rpow_one]

/-- **Taylor remainder of `(4/3) v^{3/2}` at `v' ≤ v`** (exact): with `t = √v'`, `u = √v`,
`(4/3)v^{3/2} - (4/3)v'^{3/2} - 2√v'(v - v') = (2/3)(u - t)²(2u + t) ∈ [0, (2/3)(v - v')²/√v']`. -/
lemma phase_remainder {v' v : ℝ} (hv' : 0 < v') (hvv : v' ≤ v) :
    0 ≤ 4 / 3 * v ^ (3 / 2 : ℝ) - (4 / 3 * v' ^ (3 / 2 : ℝ) + 2 * Real.sqrt v' * (v - v')) ∧
      4 / 3 * v ^ (3 / 2 : ℝ) - (4 / 3 * v' ^ (3 / 2 : ℝ) + 2 * Real.sqrt v' * (v - v')) ≤
        2 / 3 * (v - v') ^ 2 / Real.sqrt v' := by
  have hv : 0 ≤ v := hv'.le.trans hvv
  set t := Real.sqrt v' with ht
  set u := Real.sqrt v with hu
  have ht0 : 0 < t := Real.sqrt_pos.2 hv'
  have htu : t ≤ u := Real.sqrt_le_sqrt hvv
  have e1 : v' = t ^ 2 := (Real.sq_sqrt hv'.le).symm
  have e2 : v = u ^ 2 := (Real.sq_sqrt hv).symm
  rw [ct_rpow32 hv, ct_rpow32 hv'.le, ← ht, ← hu]
  have key : 4 / 3 * (v * u) - (4 / 3 * (v' * t) + 2 * t * (v - v')) = 2 / 3 * (u - t) ^ 2 * (2 * u + t) := by
    rw [e1, e2]; ring
  rw [key]
  have hu0 : 0 < u := lt_of_lt_of_le ht0 htu
  refine ⟨by positivity, ?_⟩
  rw [e1, e2, le_div_iff₀ ht0]
  have : (2 / 3 * (u - t) ^ 2 * (2 * u + t)) * t ≤ 2 / 3 * (u ^ 2 - t ^ 2) ^ 2 := by
    have h : (u - t) ^ 2 * ((2 * u + t) * t) ≤ (u - t) ^ 2 * (u + t) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      nlinarith [sq_nonneg u]
    nlinarith [h]
  exact this


open FormalResearch.CohnElkies

/-- `ctTau0 a` is the genuine `τ₀(a)` near `0⁻`: the unique positive solution. -/
lemma ctTau0_unique {ε : ℝ} (hε : ε = 1 ∨ ε = -1) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ Ioo (-ρ) 0, ∀ τ : ℝ, 0 < τ →
    edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) → ctTau0 a = τ := by
  obtain ⟨ρ, τ0, ψ, Ξ, hρ, -, -, hmain, -⟩ := CtCfu.cfu_psi_langer hε
  refine ⟨ρ, hρ, fun a ha τ hτ hΦ => ?_⟩
  obtain ⟨hpos, hphi, huniq, -, -⟩ := hmain a ha
  have hspec : 0 < ctTau0 a ∧ edgePhi (hankelEdgeM (ctTau0 a)) (ctTau0 a) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) :=
    Classical.epsilon_spec (p := fun τ : ℝ => 0 < τ ∧ edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2))
      ⟨τ0 a, hpos, hphi⟩
  rw [huniq _ hspec.1 hspec.2, huniq τ hτ hΦ]

/-- `2λ = √μ` (`λ = 2^{-2/3}c^{-1/3}`, `μ = 2^{2/3}c^{-2/3}`). -/
lemma two_mul_ctLam {c : ℝ} (hc : 0 < c) : 2 * ctLam c = Real.sqrt (ctMu c) := by
  have h : ctMu c = (2 * ctLam c) ^ 2 := by
    unfold ctMu ctLam
    have e1 : ((2 : ℝ) ^ (-(2 / 3) : ℝ)) ^ 2 = (2 : ℝ) ^ (-(4 / 3) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have e2 : (c ^ (-(1 / 3) : ℝ)) ^ 2 = c ^ (-(2 / 3) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
    have e3 : (2 : ℝ) ^ ((2 : ℝ) / 3) = 2 ^ 2 * (2 : ℝ) ^ (-(4 / 3) : ℝ) := by
      rw [show (2 : ℝ) ^ 2 = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_add (by norm_num)]; norm_num
    rw [mul_pow, mul_pow, e1, e2, e3]; ring
  rw [h, Real.sqrt_sq (by have := ctLam_pos hc; positivity)]

/-- **The phase estimate at one point of the transition band** (`(ct:theta-cfu-match)` and the Taylor expansion of `(4/3)v^{3/2}` about
`v'`, proof of `(ct:combined)`): for `0 < L`, `e^L - 1 ≤ 5·10⁻⁴`, with `v' = v'(L)` (`ctVprime`), `v = -û(-v')` and `δ = v - v'`, under
`ct_langer_edge` and the `ψ_ε`-window `(ρ, M)` containing `μ(-v')`: `0 < δ ≤ λM` and
`|sin X(L) - sin((4/3)v^{3/2})| ≤ (2/3)δ²/√v'` (`X = boasX`).  Here `X = (4/3)v'^{3/2} + 2√v' δ` exactly. -/
theorem ct_trans_phase_pt {ε c ρ M L : ℝ} (hW : PsiWin ε ρ M)
    (hU : ∀ a ∈ Ioo (-ρ) 0, ∀ τ : ℝ, 0 < τ →
      edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) → ctTau0 a = τ)
    (hc : 0 < c) (hL : 0 < L) (hLe : Real.exp L - 1 ≤ 5e-4) (hwin : -ρ < ctMu c * (-(ctVprime c L))) :
    0 < -ctUhat ε c (-(ctVprime c L)) - ctVprime c L ∧
      -ctUhat ε c (-(ctVprime c L)) - ctVprime c L ≤ ctLam c * M ∧
      |Real.sin (boasX c ε L) - Real.sin (4 / 3 * (-ctUhat ε c (-(ctVprime c L))) ^ (3 / 2 : ℝ))| ≤
        2 / 3 * (-ctUhat ε c (-(ctVprime c L)) - ctVprime c L) ^ 2 / Real.sqrt (ctVprime c L) := by
  have hK := langerScale_pos hc
  have hg := ctChartG_pos hL hLe
  have hmu := ctMu_pos hc
  have hlam := ctLam_pos hc
  set v' := ctVprime c L with hv'
  have hv'pos : 0 < v' := mul_pos hK hg
  set a := ctMu c * (-v') with ha
  have ha0 : a < 0 := mul_neg_of_pos_of_neg hmu (by linarith)
  have haρ : a ∈ Ioo (-ρ) 0 := ⟨hwin, ha0⟩
  have hna : -a = ctMu c * v' := by rw [ha]; ring
  -- the phase at the edge
  have hΦ : c * edgePhi L (tau0 L) = 4 / 3 * v' ^ (3 / 2 : ℝ) := by
    rw [ct_langer_edge hL hLe, hv']
    unfold ctVprime langerScale
    have : (c ^ (2 / 3 : ℝ) * langerKappa * ctChartG L) ^ (3 / 2 : ℝ) = c * (langerKappa * ctChartG L) ^ (3 / 2 : ℝ) := by
      rw [mul_assoc, Real.mul_rpow (by positivity) (by have := langerKappa_pos; positivity), ← Real.rpow_mul hc.le]
      norm_num
    rw [this]; ring
  have hmu32 : ctMu c ^ (3 / 2 : ℝ) = 2 * c⁻¹ := by
    unfold ctMu
    rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by norm_num), ← Real.rpow_mul hc.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hΦ' : edgePhi L (tau0 L) = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) := by
    rw [hna, Real.mul_rpow hmu.le hv'pos.le, hmu32]
    have : edgePhi L (tau0 L) = (4 / 3 * v' ^ (3 / 2 : ℝ)) / c := by
      rw [← hΦ]; field_simp
    rw [this]; field_simp; ring
  have hτ : ctTau0 a = tau0 L := hU a haρ _ (tau0_pos hL) (by rw [hankelEdgeM_tau0 hL]; exact hΦ')
  have hsa : 0 < Real.sqrt (-a) := Real.sqrt_pos.2 (by linarith)
  have hθ : CtOuter.outerTheta ε (tau0 L) = ctPsi ε a * Real.sqrt (-a) := by
    unfold ctPsi; rw [← hτ]; field_simp
  obtain ⟨hψ0, hψM, -, -⟩ := hW.2.2 a haρ
  have hUh : ctUhat ε c (-v') = -v' + ctLam c * ctPsi ε a := by rw [ctUhat_eq]
  set δ := -ctUhat ε c (-v') - v' with hδ
  have hδe : δ = -(ctLam c * ctPsi ε a) := by rw [hδ, hUh]; ring
  have hδpos : 0 < δ := by rw [hδe]; have := mul_neg_of_pos_of_neg hlam hψ0; linarith
  have hδM : δ ≤ ctLam c * M := by
    rw [hδe]
    have := (abs_le.1 hψM).1
    nlinarith
  have hsq : Real.sqrt (-a) = 2 * ctLam c * Real.sqrt v' := by
    rw [hna, Real.sqrt_mul hmu.le, ← two_mul_ctLam hc]
  have hX : boasX c ε L = 4 / 3 * v' ^ (3 / 2 : ℝ) + 2 * Real.sqrt v' * δ := by
    unfold boasX
    rw [hΦ, hθ, hsq, hδe]; ring
  have hY : -ctUhat ε c (-v') = v' + δ := by rw [hδ]; ring
  refine ⟨hδpos, hδM, ?_⟩
  rw [hY, hX]
  obtain ⟨h1, h2⟩ := phase_remainder hv'pos (v := v' + δ) (by linarith)
  have e : v' + δ - v' = δ := by ring
  rw [e] at h1 h2
  refine (Real.abs_sin_sub_sin_le _ _).trans ?_
  rw [abs_sub_comm, abs_of_nonneg h1]
  exact h2

/-- `v'(L(x)) = -x`: the band variable at `L = log(π²ξ(x))`. -/
lemma ctVprime_log_hankelXi {c x : ℝ} (hc : 0 < c) (hx : |x| ≤ langerRadius c) :
    ctVprime c (Real.log (π ^ 2 * hankelXi c x)) = -x := by
  have hpos : 0 < π ^ 2 * hankelXi c x := by have := hankelXi_pos hc hx; positivity
  have h := hankelBandU_hankelXi hc hx
  rw [hankelBandU_eq] at h
  unfold ctVprime ctChartG
  rw [Real.exp_log hpos, mul_neg]
  linarith

/-- **Transport on the band, in the variable `L`** (`gt:7.7p` (b), substituted `ξ = e^L/π²`): for a function `G` with `|G| ≤ 1`, continuous on
`[-r, 0)`, `0 < r ≤ A`, `Λ = log(π²ξ(-r))`:
`|∫_{-r}^0 G(x) Re Ψ̃(x) dx - ∫_0^Λ G(-v'(L)) h(L) dL| ≤ r r_∞`.  (`dm = -c ξ'(x) (ρ₀ f)(cξ(x)) dx` up to `r_∞ dx`, and `L = L(x)` is the
decreasing chart `ũ(ξ(L)) = -v'(L)`.) -/
theorem ct_trans_transport {c ε : ℝ} (hc : 5000 ≤ c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f)
    (hε : ε = 1 ∨ ε = -1) (hM : hankelMass c f = 1) {r : ℝ} (hr0 : 0 < r) (hrA : r ≤ langerRadius c)
    {G : ℝ → ℝ} (hG : ∀ x, |G x| ≤ 1) (hGc : ContinuousOn G (Ico (-r) 0)) :
    |(∫ x in Ioo (-r) 0, G x * hankelPsiR c f x) -
      ∫ L in Ioo 0 (Real.log (π ^ 2 * hankelXi c (-r))), G (-ctVprime c L) * hankelHL c f L| ≤ r * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hA := langerRadius_pos hc0
  have hmem : ∀ x ∈ Icc (-r) 0, |x| ≤ langerRadius c := fun x hx =>
    abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsub : Icc (-r) 0 ⊆ Icc (-(langerRadius c)) (langerRadius c) := fun x hx =>
    abs_le.1 (hmem x hx)
  -- integrability
  have hPc : ContinuousOn (hankelPsiR c f) (Icc (-r) 0) := (continuousOn_hankelPsiR hc0 hf).mono hsub
  have hQc : ContinuousOn (hankelPsiLead c f) (Icc (-r) 0) := (continuousOn_hankelQ hc0 hf).mono hsub
  have hGm : AEStronglyMeasurable G (volume.restrict (Ioo (-r) 0)) := (hGc.mono Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo
  have hbd : ∀ᵐ x ∂(volume.restrict (Ioo (-r) 0)), ‖G x‖ ≤ 1 :=
    Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hG x
  have hIP : Integrable (fun x => G x * hankelPsiR c f x) (volume.restrict (Ioo (-r) 0)) :=
    Integrable.bdd_mul (c := 1) ((hPc.integrableOn_Icc).mono_set Ioo_subset_Icc_self) hGm hbd
  have hIQ : Integrable (fun x => G x * hankelPsiLead c f x) (volume.restrict (Ioo (-r) 0)) :=
    Integrable.bdd_mul (c := 1) ((hQc.integrableOn_Icc).mono_set Ioo_subset_Icc_self) hGm hbd
  -- (1) transport error
  have h1 : |(∫ x in Ioo (-r) 0, G x * hankelPsiR c f x) - ∫ x in Ioo (-r) 0, G x * hankelPsiLead c f x| ≤
      r * hankelRinf c := by
    rw [← integral_sub hIP hIQ, ← Real.norm_eq_abs]
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (-r) 0)
      (f := fun x => G x * hankelPsiR c f x - G x * hankelPsiLead c f x) (C := hankelRinf c)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) (fun x hx => by
        rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have := hankelPsiR_sub_Q_le hc hf hε hM (hmem x (Ioo_subset_Icc_self hx))
        calc |G x| * |hankelPsiR c f x - hankelPsiLead c f x| ≤ 1 * hankelRinf c :=
              mul_le_mul (hG x) this (abs_nonneg _) zero_le_one
          _ = hankelRinf c := one_mul _)
    refine this.trans (le_of_eq ?_)
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  -- (2) the substitution `L = log(π² ξ(x))`
  set Fm : ℝ → ℝ := fun x => Real.log (π ^ 2 * hankelXi c x) with hFm
  set Fd : ℝ → ℝ := fun x => hankelXiD c x / hankelXi c x with hFd
  have hxi : ∀ x ∈ Icc (-r) 0, 0 < hankelXi c x := fun x hx => hankelXi_pos hc0 (hmem x hx)
  have hder : ∀ x ∈ Icc (-r) 0, HasDerivAt Fm (Fd x) x := by
    intro x hx
    have h1 := ((hasDerivAt_hankelXi hc0 (hmem x hx)).const_mul (π ^ 2)).log
      (by have := hxi x hx; positivity)
    refine h1.congr_deriv ?_
    have := hxi x hx
    simp only [hFd]; field_simp
  have hcont : ContinuousOn Fm (uIcc (-r) 0) := by
    rw [uIcc_of_le (by linarith)]
    exact fun x hx => (hder x hx).continuousAt.continuousWithinAt
  have hmm : min (-r) 0 = -r := min_eq_left (by linarith)
  have hMM : max (-r) 0 = 0 := max_eq_right (by linarith)
  have hFdn : ∀ x ∈ Icc (-r) 0, Fd x ≤ 0 := by
    intro x hx
    exact div_nonpos_of_nonpos_of_nonneg (hankelXiD_neg hc0 (hmem x hx)).le (hxi x hx).le
  have key := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonpos (a := -r) (b := 0) (f := Fm) (f' := Fd)
    (g := fun L => G (-ctVprime c L) * hankelHL c f L) hcont
    (fun x hx => by rw [hmm, hMM] at hx; exact hder x ⟨hx.1.le, hx.2.le⟩)
    (fun x hx => by rw [hmm, hMM] at hx; exact hFdn x ⟨hx.1.le, hx.2.le⟩)
  have hpt : ∀ x ∈ uIcc (-r) 0, ((fun L => G (-ctVprime c L) * hankelHL c f L) ∘ Fm) x * Fd x =
      -(G x * hankelPsiLead c f x) := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hxi' := hxi x hx
    have hv : ctVprime c (Fm x) = -x := ctVprime_log_hankelXi hc0 (hmem x hx)
    have hex : Real.exp (Fm x) / π ^ 2 = hankelXi c x := by
      simp only [hFm]
      rw [Real.exp_log (by positivity)]; field_simp
    simp only [Function.comp_apply, hv, neg_neg, hankelHL, hex, hFd, hankelPsiLead]
    field_simp
  rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_neg] at key
  have hF0 : Fm 0 = 0 := by
    simp only [hFm]
    rw [hankelXi_zero hc0, show π ^ 2 * (1 / π ^ 2) = 1 by field_simp, Real.log_one]
  have hΛ0 : 0 < Fm (-r) := (hankel_band_edge hc0 hr0 hrA).1
  have hL : ∫ x in (-r)..0, G x * hankelPsiLead c f x = ∫ x in Ioo (-r) 0, G x * hankelPsiLead c f x := by
    rw [intervalIntegral.integral_of_le (by linarith : -r ≤ 0), integral_Ioc_eq_integral_Ioo]
  have hR : ∫ u in Fm (-r)..Fm 0, G (-ctVprime c u) * hankelHL c f u =
      -∫ L in Ioo 0 (Fm (-r)), G (-ctVprime c L) * hankelHL c f L := by
    rw [hF0, intervalIntegral.integral_symm, intervalIntegral.integral_of_le hΛ0.le, integral_Ioc_eq_integral_Ioo]
  have h2 : (∫ x in Ioo (-r) 0, G x * hankelPsiLead c f x) =
      ∫ L in Ioo 0 (Real.log (π ^ 2 * hankelXi c (-r))), G (-ctVprime c L) * hankelHL c f L := by
    rw [← hL]
    simp only [hFm] at key hR
    linarith
  rw [h2] at h1
  exact h1

/-- `ct:dyadic` window for both signs: one `(ρ, M)` with `PsiWin ε ρ M` and the uniqueness of `τ₀` on `(-ρ, 0)`, for `ε = ±1`. -/
lemma ct_window_pm : ∃ ρ M : ℝ, 0 < ρ ∧ 0 ≤ M ∧ ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → PsiWin ε ρ M ∧
    ∀ a ∈ Ioo (-ρ) 0, ∀ τ : ℝ, 0 < τ → edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) → ctTau0 a = τ := by
  obtain ⟨ρ₁, M₁, hρ₁, hM₁, h₁⟩ := ctPsi_window (ε := 1) (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hρ₂, hM₂, h₂⟩ := ctPsi_window (ε := -1) (Or.inr rfl)
  obtain ⟨ρ₃, hρ₃, h₃⟩ := ctTau0_unique (ε := 1) (Or.inl rfl)
  obtain ⟨ρ₄, hρ₄, h₄⟩ := ctTau0_unique (ε := -1) (Or.inr rfl)
  set ρ := min (min ρ₁ ρ₂) (min ρ₃ ρ₄) with hρ
  have hρ0 : 0 < ρ := lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρ₄)
  have hsub : ∀ ρ' : ℝ, ρ ≤ ρ' → Ioo (-ρ) 0 ⊆ Ioo (-ρ') 0 := fun ρ' h a ha => ⟨by linarith [ha.1], ha.2⟩
  have hu : ∀ a ∈ Ioo (-ρ) 0, ∀ τ : ℝ, 0 < τ → edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) →
      ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ctTau0 a = τ := by
    intro a ha τ hτ hΦ ε hε
    rcases hε with rfl | rfl
    · exact h₃ a (hsub ρ₃ (by simp [hρ]) ha) τ hτ hΦ
    · exact h₄ a (hsub ρ₄ (by simp [hρ]) ha) τ hτ hΦ
  refine ⟨ρ, max M₁ M₂, hρ0, le_max_of_le_left hM₁, fun ε hε => ⟨⟨hρ0, le_max_of_le_left hM₁, fun a ha => ?_⟩,
    fun a ha τ hτ hΦ => hu a ha τ hτ hΦ ε hε⟩⟩
  rcases hε with rfl | rfl
  · obtain ⟨h1, h2, h3, h4⟩ := h₁ a (hsub ρ₁ (by simp [hρ]) ha)
    exact ⟨h1, h2.trans (le_max_left _ _), h3, h4.trans (le_max_left _ _)⟩
  · obtain ⟨h1, h2, h3, h4⟩ := h₂ a (hsub ρ₂ (by simp [hρ]) ha)
    exact ⟨h1, h2.trans (le_max_right _ _), h3, h4.trans (le_max_right _ _)⟩

/-- The weight estimate of the transition band: `w̃ (2/3)δ²/√v' ≤ 174 δ² v'/(R√R)` for `1 ≤ v' ≤ R`, `0 ≤ δ ≤ 1/2`
(`w̃ ≤ 2((v'+δ)/R)^{12} ≤ 260 (v'/R)^{12}` and `(v'/R)^{12}/√v' ≤ v'/(R√R)`). -/
lemma trans_weight_bound {R v' δ : ℝ} (hR : 0 < R) (hv1 : 1 ≤ v') (hvR : v' ≤ R) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) :
    taperW R (v' + δ) * (2 / 3 * δ ^ 2 / Real.sqrt v') ≤ 174 * δ ^ 2 * v' / (R * Real.sqrt R) := by
  have hv0 : 0 < v' := by linarith
  set z := v' / R with hz
  have hz0 : 0 < z := div_pos hv0 hR
  have hz1 : z ≤ 1 := (div_le_one hR).2 hvR
  have hw1 := taperW_le_pow hR (v := v' + δ) (by linarith)
  have hq : (v' + δ) / R ≤ 3 / 2 * z := by
    rw [hz, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hR.le
  have hw2 : taperW R (v' + δ) ≤ 2 * (3 / 2) ^ 12 * z ^ 12 := by
    refine hw1.trans ?_
    have := pow_le_pow_left₀ (by positivity) hq 12
    rw [mul_pow] at this
    linarith
  have hsR := Real.sqrt_pos.2 hR
  have hsv := Real.sqrt_pos.2 hv0
  have hsz : Real.sqrt v' = Real.sqrt z * Real.sqrt R := by
    rw [← Real.sqrt_mul hz0.le, hz]; field_simp
  have hzs : z ≤ Real.sqrt z := by
    exact (Real.le_sqrt hz0.le hz0.le).2 (by nlinarith)
  have hz12 : z ^ 12 ≤ z * Real.sqrt z := by
    have : z ^ 12 ≤ z ^ 2 := pow_le_pow_of_le_one hz0.le hz1 (by norm_num)
    nlinarith
  have hkey : z ^ 12 / Real.sqrt v' ≤ v' / (R * Real.sqrt R) := by
    rw [div_le_div_iff₀ hsv (by positivity), hsz]
    have : z ^ 12 * (R * Real.sqrt R) ≤ z * Real.sqrt z * (R * Real.sqrt R) :=
      mul_le_mul_of_nonneg_right hz12 (by positivity)
    have e : v' * (Real.sqrt z * Real.sqrt R) = z * Real.sqrt z * (R * Real.sqrt R) := by
      rw [hz]; field_simp
    rw [e]; exact this
  have hnn : 0 ≤ 2 / 3 * δ ^ 2 := by positivity
  calc taperW R (v' + δ) * (2 / 3 * δ ^ 2 / Real.sqrt v')
      ≤ (2 * (3 / 2) ^ 12 * z ^ 12) * (2 / 3 * δ ^ 2 / Real.sqrt v') :=
        mul_le_mul_of_nonneg_right hw2 (by positivity)
    _ = (2 * (3 / 2) ^ 12 * (2 / 3 * δ ^ 2)) * (z ^ 12 / Real.sqrt v') := by ring
    _ ≤ (2 * (3 / 2) ^ 12 * (2 / 3 * δ ^ 2)) * (v' / (R * Real.sqrt R)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ ≤ 174 * δ ^ 2 * v' / (R * Real.sqrt R) := by
        rw [← mul_div_assoc, div_le_div_iff_of_pos_right (by positivity)]
        nlinarith [mul_nonneg (sq_nonneg δ) hv0.le]

/-- `v(L) = -û(-v'(L))` on the transition band `0 < L ≤ Λ` (the taper variable in the Langer chart). -/
lemma ctTaperV_eq {ε c R L : ℝ} (hc : 0 < c) (hr0 : 0 ≤ ctRprime ε c R) (hrA : ctRprime ε c R ≤ langerRadius c)
    (hL0 : 0 < L) (hLΛ : L ≤ ctTaperLam ε c R) :
    ctTaperV ε c L = -ctUhat ε c (-(ctVprime c L)) := by
  obtain ⟨h1, -⟩ := ctUtildeXi_band hc hr0 hrA hL0.le hLΛ
  unfold ctTaperV
  rw [h1]

/-- `x ↦ w_R(-û(x)) sin((4/3)(-û(x))^{3/2})` is continuous on `[-r, 0)` inside the window, with `|·| ≤ 1`. -/
lemma ctTransG_cont {ε c R ρ M r : ℝ} (hW : PsiWin ε ρ M) (hc : 0 < c) (hrw : -ρ < ctMu c * (-r)) :
    ContinuousOn (fun x => taperW R (-ctUhat ε c x) * Real.sin (4 / 3 * (-ctUhat ε c x) ^ (3 / 2 : ℝ))) (Ico (-r) 0) := by
  intro x hx
  have hx0 : x < 0 := hx.2
  have hxw : -ρ < ctMu c * x := by
    have := mul_le_mul_of_nonneg_left hx.1 (ctMu_pos hc).le
    linarith
  have hU : ContinuousAt (ctUhat ε c) x := (ctUhat_hasDerivAt hW hc hx0 hxw).continuousAt
  refine ContinuousAt.continuousWithinAt ?_
  have h1 : Continuous (taperW R) := by unfold taperW taperX; fun_prop
  refine (h1.continuousAt.comp hU.neg).mul ?_
  exact Real.continuous_sin.continuousAt.comp ((hU.neg.rpow_const (Or.inr (by norm_num))).const_mul _)

lemma ctTransG_abs {R : ℝ} (hR : 0 < R) (u : ℝ) :
    |taperW R u * Real.sin (4 / 3 * u ^ (3 / 2 : ℝ))| ≤ 1 := by
  rw [abs_mul, abs_of_nonneg (taperW_nonneg hR u)]
  calc taperW R u * |Real.sin _| ≤ 1 * 1 :=
        mul_le_mul (taperW_le_one hR u) (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- **The phase-error integral of the transition band**: on `L ∈ (L_min, Λ]`,
`|∫ w̃ h (sin X - sin((4/3)v^{3/2}))| ≤ 174 (λM)² (∫_{(0,L_J]} v'|h|)/(R√R)` (`ct:dyadic` (4), transition band: the phase error
`O(c^{-2/3}v'^{-1/2})` against `w̃ ≤ C (v'/R)^{12}`).  Hypotheses: the window `(ρ, M)`, `TaperBand`, `R' ≤ A`. -/
theorem ct_trans_E1 {ε c R ρ M K LJ Lmin : ℝ} {f : ℝ → ℝ} (hW : PsiWin ε ρ M)
    (hU : ∀ a ∈ Ioo (-ρ) 0, ∀ τ : ℝ, 0 < τ → edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) → ctTau0 a = τ)
    (hc : 1 ≤ c) (hB : TaperBand ε c R) (hf : IsHankelEigenfn c ε f) (hrA : ctRprime ε c R ≤ langerRadius c)
    (hRρ : -ρ < ctMu c * (-R)) (hL0 : 0 < Lmin) (hLv : ctVprime c Lmin = c ^ (4 / 7 : ℝ))
    (hLΛ : Lmin ≤ ctTaperLam ε c R) (hΛJ : ctTaperLam ε c R ≤ LJ) (hLJe : Real.exp LJ - 1 ≤ 5e-4)
    (hMom : ∫ L in Ioc 0 LJ, ctVprime c L * |hankelHL c f L| ≤ K * c ^ (1 / 3 : ℝ)) :
    |∫ L in Ioc Lmin (ctTaperLam ε c R), ctTaper ε c R L * (hankelHL c f L *
        (Real.sin (boasX c ε L) - Real.sin (4 / 3 * (ctTaperV ε c L) ^ (3 / 2 : ℝ))))| ≤
      174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * c ^ (1 / 3 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hI := hB.inputs
  have hR0 := hI.R_pos
  set Λ := ctTaperLam ε c R with hΛ
  have hΛ0 : 0 < Λ := hI.Lam_pos
  have hLJ0 : 0 ≤ LJ := hΛ0.le.trans hΛJ
  have hvΛ : 0 < ctVprime c Λ := mul_pos (langerScale_pos hc0) (ctChartG_pos hΛ0 hB.Lam_le_small)
  have hr0 : 0 ≤ ctRprime ε c R := hvΛ.le.trans (hB.vp_le_R Λ hΛ0 le_rfl)
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf
  have hD0 : 0 ≤ 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) := by
    have := Real.sqrt_pos.2 hR0
    positivity
  -- the integrability of `v'|h|` on `(0, L_J]`
  have hIv : IntegrableOn (fun L => ctVprime c L * |hankelHL c f L|) (Ioc 0 LJ) := by
    have hmeas : AEStronglyMeasurable (ctVprime c) (volume.restrict (Ioc 0 LJ)) :=
      ((ctVprime_continuousOn hLJe).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    refine Integrable.bdd_mul (c := ctVprime c LJ) hh.abs.integrableOn hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun L hL => ?_)
    have hLe' : Real.exp L - 1 ≤ 5e-4 := by linarith [Real.exp_le_exp.2 hL.2]
    have hpos : 0 < ctVprime c L := mul_pos (langerScale_pos hc0) (ctChartG_pos hL.1 hLe')
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact (ctVprime_strictMonoOn hc0 hLJe).monotoneOn ⟨hL.1.le, hL.2⟩ ⟨hLJ0, le_rfl⟩ hL.2
  have hLminJ : Lmin ≤ LJ := hLΛ.trans hΛJ
  have hc1' : (1 : ℝ) ≤ c ^ (4 / 7 : ℝ) := Real.one_le_rpow hc (by norm_num)
  -- pointwise bound on `(L_min, Λ]`
  have hpt : ∀ L ∈ Ioc Lmin Λ, ‖ctTaper ε c R L * (hankelHL c f L *
      (Real.sin (boasX c ε L) - Real.sin (4 / 3 * (ctTaperV ε c L) ^ (3 / 2 : ℝ))))‖ ≤
      174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (ctVprime c L * |hankelHL c f L|) := by
    intro L hL
    have hL0' : 0 < L := hL0.trans hL.1
    have hLΛ' : L ≤ Λ := hL.2
    have hLe' : Real.exp L - 1 ≤ 5e-4 := by linarith [Real.exp_le_exp.2 (hLΛ'.trans hΛJ)]
    have hv'pos : 0 < ctVprime c L := mul_pos (langerScale_pos hc0) (ctChartG_pos hL0' hLe')
    have hv1 : 1 ≤ ctVprime c L := by
      have := (ctVprime_strictMonoOn hc0 hLJe).monotoneOn ⟨hL0.le, hLminJ⟩ ⟨hL0'.le, hLΛ'.trans hΛJ⟩ hL.1.le
      rw [hLv] at this
      linarith
    have hvR : ctVprime c L ≤ R := (hB.vp_le_R L hL0' hLΛ').trans hB.Rprime_le
    have hwin : -ρ < ctMu c * (-(ctVprime c L)) := by
      have := mul_le_mul_of_nonneg_left (neg_le_neg hvR) (ctMu_pos hc0).le
      linarith
    obtain ⟨hδ0, hδM, hsin⟩ := ct_trans_phase_pt hW hU hc0 hL0' hLe' hwin
    have hV := ctTaperV_eq hc0 hr0 hrA hL0' hLΛ'
    set δ := -ctUhat ε c (-(ctVprime c L)) - ctVprime c L with hδ
    have hvδ : ctTaperV ε c L = ctVprime c L + δ := by rw [hV]; ring
    have hδ12 : δ ≤ 1 / 2 := by have := hB.v_le L hL0' hLΛ'; linarith
    have hwt : ctTaper ε c R L = taperW R (ctVprime c L + δ) := by
      unfold ctTaper; rw [if_neg (not_le.2 hL0'), if_pos hLΛ', hvδ]
    have hw0 : 0 ≤ taperW R (ctVprime c L + δ) := taperW_nonneg hR0 _
    have hwb := trans_weight_bound hR0 hv1 hvR hδ0.le hδ12
    have hδ2 : δ ^ 2 ≤ (ctLam c * M) ^ 2 := pow_le_pow_left₀ hδ0.le hδM 2
    rw [hV, hwt, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw0]
    have hs : |Real.sin (boasX c ε L) - Real.sin (4 / 3 * (-ctUhat ε c (-(ctVprime c L))) ^ (3 / 2 : ℝ))| ≤
        2 / 3 * δ ^ 2 / Real.sqrt (ctVprime c L) := hsin
    have hden : 0 ≤ 174 * δ ^ 2 * ctVprime c L / (R * Real.sqrt R) := by
      have := Real.sqrt_pos.2 hR0
      positivity
    calc taperW R (ctVprime c L + δ) * (|hankelHL c f L| * |Real.sin (boasX c ε L) -
          Real.sin (4 / 3 * (-ctUhat ε c (-(ctVprime c L))) ^ (3 / 2 : ℝ))|)
        ≤ taperW R (ctVprime c L + δ) * (|hankelHL c f L| * (2 / 3 * δ ^ 2 / Real.sqrt (ctVprime c L))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) hw0
      _ = |hankelHL c f L| * (taperW R (ctVprime c L + δ) * (2 / 3 * δ ^ 2 / Real.sqrt (ctVprime c L))) := by ring
      _ ≤ |hankelHL c f L| * (174 * δ ^ 2 * ctVprime c L / (R * Real.sqrt R)) :=
          mul_le_mul_of_nonneg_left hwb (abs_nonneg _)
      _ ≤ |hankelHL c f L| * (174 * (ctLam c * M) ^ 2 * ctVprime c L / (R * Real.sqrt R)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine div_le_div_of_nonneg_right ?_ (by have := Real.sqrt_pos.2 hR0; positivity)
          nlinarith [hv'pos]
      _ = 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (ctVprime c L * |hankelHL c f L|) := by ring
  -- integrate
  have hg : IntegrableOn (fun L => 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (ctVprime c L * |hankelHL c f L|))
      (Ioc Lmin Λ) := (hIv.mono_set (Ioc_subset_Ioc hL0.le hΛJ)).const_mul _
  have h1 := norm_integral_le_of_norm_le (μ := volume.restrict (Ioc Lmin Λ)) hg
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hpt))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [integral_const_mul]
  refine mul_le_mul_of_nonneg_left ((setIntegral_mono_set hIv ?_ (Ioc_subset_Ioc hL0.le hΛJ).eventuallySubset).trans hMom) hD0
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun L hL => ?_)
  have hLe' : Real.exp L - 1 ≤ 5e-4 := by linarith [Real.exp_le_exp.2 hL.2]
  exact mul_nonneg (mul_pos (langerScale_pos hc0) (ctChartG_pos hL.1 hLe')).le (abs_nonneg _)

/-- **The transition band, decomposed**: the window `(ρ, M)`, `TaperBand`, the top-scale first moment and `R' ≤ A`,
`|∫_{ξ ≥ ξ(-v₀)} w̃ sin X dm - s₂ - ∫_{ξ>ξ(-R')} sin X dm| ≤ 174(λM)²(Kc^{1/3})/(R√R) + 2^{12}(K+1)c₁^{-24}c^{-29/21} + R' r_∞`:
the phase error (`ct_trans_E1`), the taper estimate for `L < L_min` (`boas_field_trunc_lo`) and the transport error (`ct_trans_transport`). -/
theorem ct_trans_decomp {ε c R ρ M K LJ c₁ : ℝ} {f : ℝ → ℝ} (hW : PsiWin ε ρ M)
    (hU : ∀ a ∈ Ioo (-ρ) 0, ∀ τ : ℝ, 0 < τ → edgePhi (hankelEdgeM τ) τ = (2 / 3) * (-a) ^ ((3 : ℝ) / 2) → ctTau0 a = τ)
    (hε : ε = 1 ∨ ε = -1) (hc5 : 5000 ≤ c) (hBR : TaperBand ε c R) (hf' : IsHankelEigenfn c ε f)
    (hm : hankelMass c f = 1) (hc₁ : 0 < c₁) (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hr0 : 0 < ctRprime ε c R) (hrA : ctRprime ε c R ≤ langerRadius c) (hRρ : -ρ < ctMu c * (-R))
    (hL0 : 0 < ctLv0 c) (hLe : Real.exp (ctLv0 c) - 1 ≤ 5e-4) (hLv : ctVprime c (ctLv0 c) = c ^ (4 / 7 : ℝ))
    (hLΛ : ctLv0 c ≤ ctTaperLam ε c R) (hΛJ : ctTaperLam ε c R ≤ LJ) (hLJe : Real.exp LJ - 1 ≤ 5e-4) (hK0 : 0 ≤ K)
    (hMom : ∫ L in Ioc 0 LJ, ctVprime c L * |hankelHL c f L| ≤ K * c ^ (1 / 3 : ℝ)) :
    |ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f| ≤
      174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * c ^ (1 / 3 : ℝ)) +
        2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) + ctRprime ε c R * hankelRinf c := by
  have hc0 : 0 < c := by linarith
  have hc3 : 3 ≤ c := by linarith
  have hI := hBR.inputs
  have hR0 : 0 < R := hI.R_pos
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf'
  have hmass1 : ∫ L, |hankelHL c f L| = 1 := by rw [integral_abs_hankelHL hc0 hf', hm]
  have hrR : ctRprime ε c R ≤ R := hBR.Rprime_le
  have hrw : -ρ < ctMu c * (-(ctRprime ε c R)) := by
    have := mul_le_mul_of_nonneg_left (neg_le_neg hrR) (ctMu_pos hc0).le
    linarith
  -- notation
  set Λ := ctTaperLam ε c R with hΛ
  set Lm := ctLv0 c with hLm
  have hΛ0 : 0 < Λ := hI.Lam_pos
  have hR' := ctRprime ε c R
  set G : ℝ → ℝ := fun x => taperW R (-ctUhat ε c x) * Real.sin (4 / 3 * (-ctUhat ε c x) ^ (3 / 2 : ℝ)) with hG
  have hGb : ∀ x, |G x| ≤ 1 := fun x => ctTransG_abs hR0 _
  have hGc : ContinuousOn G (Ico (-(ctRprime ε c R)) 0) := ctTransG_cont hW hc0 hrw
  set g : ℝ → ℝ := fun L => G (-ctVprime c L) * hankelHL c f L with hg
  -- the equalities on `(0, Λ]`
  have hgeq : ∀ L ∈ Ioc 0 Λ, g L = ctTaper ε c R L * (hankelHL c f L *
      Real.sin (4 / 3 * (ctTaperV ε c L) ^ (3 / 2 : ℝ))) := by
    intro L hL
    have hV := ctTaperV_eq hc0 hr0.le hrA hL.1 hL.2
    have hwt : ctTaper ε c R L = taperW R (ctTaperV ε c L) := by
      unfold ctTaper; rw [if_neg (not_le.2 hL.1), if_pos hL.2]
    simp only [hg, hG]
    rw [hwt, ← hV]
    ring
  -- integrability of `g` on `(0, Λ]`
  have hvc : ContinuousOn (fun L => -ctVprime c L) (Ioc 0 Λ) :=
    ((ctVprime_continuousOn hBR.Lam_le_small).mono Ioc_subset_Icc_self).neg
  have hmaps : MapsTo (fun L => -ctVprime c L) (Ioc 0 Λ) (Ico (-(ctRprime ε c R)) 0) := by
    intro L hL
    have hLe' : Real.exp L - 1 ≤ 5e-4 := by linarith [Real.exp_le_exp.2 hL.2, hBR.Lam_le_small]
    have hpos : 0 < ctVprime c L := mul_pos (langerScale_pos hc0) (ctChartG_pos hL.1 hLe')
    exact ⟨by linarith [hBR.vp_le_R L hL.1 hL.2], by linarith⟩
  have hgI : IntegrableOn g (Ioc 0 Λ) := by
    have hm : AEStronglyMeasurable (fun L => G (-ctVprime c L)) (volume.restrict (Ioc 0 Λ)) :=
      (hGc.comp hvc hmaps).aestronglyMeasurable measurableSet_Ioc
    exact Integrable.bdd_mul (c := 1) hh.integrableOn hm
      (Eventually.of_forall fun L => by rw [Real.norm_eq_abs]; exact hGb _)
  -- integrability of the `sin X` integrand
  have hΦX : Integrable (fun L => ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) := by
    have hw : Measurable (ctTaper ε c R) := measurable_ctTaper hI
    have : Integrable (fun L => (ctTaper ε c R L * Real.sin (boasX c ε L)) * hankelHL c f L) := by
      refine hh.bdd_mul (c := 1) (hw.mul (Real.measurable_sin.comp (measurable_boasX c ε))).aestronglyMeasurable
        (Eventually.of_forall fun L => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hI.reg.mem L).1]
      calc ctTaper ε c R L * |Real.sin (boasX c ε L)| ≤ 1 * 1 :=
            mul_le_mul (hI.reg.mem L).2 (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    refine this.congr (Eventually.of_forall fun L => ?_)
    simp only; ring
  -- `ctStr = ∫_{(L_min, Λ]} + ctSout`
  have hStr : ctStr R ε c f = (∫ L in Ioc Lm Λ, ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) +
      ctSout R ε c f := by
    unfold ctStr
    rw [← Icc_union_Ioi_eq_Ici hLΛ, setIntegral_union
      (Set.disjoint_left.2 (fun x (hx : x ∈ Icc Lm Λ) (hx' : x ∈ Ioi Λ) => absurd hx.2 (not_le.2 hx'))) measurableSet_Ioi hΦX.integrableOn
      hΦX.integrableOn, integral_Icc_eq_integral_Ioc]
    congr 1
    unfold ctSout
    refine setIntegral_congr_fun measurableSet_Ioi fun L hL => ?_
    simp only [ctTaper_eq_one_of_gt hI hL, one_mul]
  have hS2 : ctOscS2 R ε c f = ∫ x in Ioo (-(ctRprime ε c R)) 0, G x * hankelPsiR c f x := by
    unfold ctOscS2
    refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
    simp only [hG]; ring
  have hTr : |ctOscS2 R ε c f - ∫ L in Ioo 0 Λ, g L| ≤ ctRprime ε c R * hankelRinf c := by
    rw [hS2]; exact ct_trans_transport hc5 hf' hε hm hr0 hrA hGb hGc
  have hsplit : ∫ L in Ioo 0 Λ, g L = (∫ L in Ioc 0 Lm, g L) + ∫ L in Ioc Lm Λ, g L := by
    have := setIntegral_union (Set.Ioc_disjoint_Ioc_of_le (a := 0) (b := Lm) (c := Lm) (d := Λ) le_rfl) measurableSet_Ioc
      (hgI.mono_set (Ioc_subset_Ioc le_rfl hLΛ)) (hgI.mono_set (Ioc_subset_Ioc hL0.le le_rfl))
    rw [Ioc_union_Ioc_eq_Ioc hL0.le hLΛ] at this
    rw [← integral_Ioc_eq_integral_Ioo]; exact this
  have hI1 : |(∫ L in Ioc Lm Λ, ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) -
      ∫ L in Ioc Lm Λ, g L| ≤ 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * c ^ (1 / 3 : ℝ)) := by
    rw [← integral_sub hΦX.integrableOn (hgI.mono_set (Ioc_subset_Ioc hL0.le le_rfl))]
    have := ct_trans_E1 hW hU (by linarith) hBR hf' hrA hRρ hL0 hLv hLΛ hΛJ hLJe hMom
    refine le_of_eq_of_le ?_ this
    congr 1
    refine integral_congr_ae ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun L hL => ?_)
    simp only
    rw [hgeq L ⟨hL0.trans hL.1, hL.2⟩]; ring
  have hI2 : |∫ L in Ioc 0 Lm, g L| ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) := by
    have key := boas_field_trunc_lo (sf := fun _ => 0) (fun L => ⟨le_rfl, zero_le_one⟩) hc3 hBR hc₁ hRlo hh hmass1 hL0 hLe
      hLv hLΛ (hLΛ.trans hΛJ) hLJe hK0 hMom
    have hwh : Integrable (fun L => ctTaper ε c R L * (1 - 0) * |hankelHL c f L|) := by
      refine (integrable_ctTaper_mul hc0 hBR hf').norm.congr (Eventually.of_forall fun L => ?_)
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hI.reg.mem L).1, sub_zero, mul_one]
    rw [integral_Ioc_eq_integral_Ioo, ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le (hwh.integrableOn) ((ae_restrict_iff' measurableSet_Ioo).2
      (Eventually.of_forall fun L hL => ?_))).trans (le_trans ?_ key)
    · have hgL := hgeq L ⟨hL.1, hL.2.le.trans hLΛ⟩
      rw [hgL, norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (hI.reg.mem L).1, sub_zero, mul_one]
      calc ctTaper ε c R L * (|hankelHL c f L| * |Real.sin (4 / 3 * ctTaperV ε c L ^ (3 / 2 : ℝ))|)
          ≤ ctTaper ε c R L * (|hankelHL c f L| * 1) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _))
              (hI.reg.mem L).1
        _ = ctTaper ε c R L * |hankelHL c f L| := by ring
    · refine setIntegral_mono_set hwh.integrableOn ?_ (Ioo_subset_Iio_self).eventuallySubset
      exact Eventually.of_forall fun L => mul_nonneg (mul_nonneg (hI.reg.mem L).1 (by norm_num)) (abs_nonneg _)
  -- assemble
  have hQ : ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f =
      ((∫ L in Ioc Lm Λ, ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) - ∫ L in Ioc Lm Λ, g L) -
        (∫ L in Ioc 0 Lm, g L) - (ctOscS2 R ε c f - ∫ L in Ioo 0 Λ, g L) := by
    rw [hStr, hsplit]; ring
  rw [hQ]
  have h12 := abs_sub (a := (∫ L in Ioc Lm Λ, ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) - (∫ L in Ioc Lm Λ, g L))
    (b := ∫ L in Ioc 0 Lm, g L)
  have h123 := abs_sub (a := ((∫ L in Ioc Lm Λ, ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) - (∫ L in Ioc Lm Λ, g L)) -
    ∫ L in Ioc 0 Lm, g L) (b := ctOscS2 R ε c f - ∫ L in Ioo 0 Λ, g L)
  linarith [hI1, hI2, hTr]

/-- The rates of the transition band: the three error terms of `ct_trans_decomp` are `≤ C c^{-4/3}` with
`C = 174M²K/c₁³ + 2^{12}(K+1)/c₁^{24} + 8|I₀|c₁²` (`λ ≤ c^{-1/3}`, `R√R ≥ c₁³c`, `c^{-29/21} ≤ c^{-4/3}`, `R' r_∞ ≤ 4c₁²c^{2/3} r_∞ ≤ C c^{-4/3}`). -/
lemma trans_rate_bound {c c₁ R R' M K : ℝ} (hc0 : 0 < c) (hc₁ : 0 < c₁) (hR1 : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hR2 : R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (hrR : R' ≤ R) (hrinf0 : 0 ≤ hankelRinf c)
    (hexpo : c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000 * c)) ≤ 1) (hM0 : 0 ≤ M) (hK0 : 0 ≤ K) (hc3 : 3 ≤ c) :
    174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * c ^ (1 / 3 : ℝ)) +
        2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) + R' * hankelRinf c ≤
      (174 * M ^ 2 * K / c₁ ^ 3 + 2 ^ 12 * (K + 1) / c₁ ^ 24 + 8 * |hankelTailI0| * c₁ ^ 2) * c ^ (-(4 / 3) : ℝ) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by positivity) hR1
  set s : ℝ := c ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hc0 _
  have hs3 : s ^ 3 = c := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have e23 : c ^ (2 / 3 : ℝ) = s * s := by rw [hs, ← Real.rpow_add hc0]; norm_num
  have em43 : c ^ (-(4 / 3) : ℝ) = c⁻¹ * s⁻¹ := by
    calc c ^ (-(4 / 3) : ℝ) = c ^ ((-1 : ℝ) + -(1 / 3)) := by norm_num
      _ = c ^ (-1 : ℝ) * c ^ (-(1 / 3) : ℝ) := Real.rpow_add hc0 _ _
      _ = c⁻¹ * s⁻¹ := by rw [Real.rpow_neg_one, Real.rpow_neg hc0.le]
  have hcp : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  -- `R√R ≥ c₁³ c`
  have hRsq : c₁ ^ 3 * c ≤ R * Real.sqrt R := by
    have h1 : c₁ * s ≤ Real.sqrt R :=
      (Real.le_sqrt (by positivity) hR0.le).2 (by
        have : (c₁ * s) ^ 2 = c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by rw [e23]; ring
        rw [this]; exact hR1)
    have h2 : c₁ ^ 2 * (s * s) ≤ R := by rw [← e23]; exact hR1
    calc c₁ ^ 3 * c = (c₁ ^ 2 * (s * s)) * (c₁ * s) := by rw [← hs3]; ring
      _ ≤ R * Real.sqrt R := mul_le_mul h2 h1 (by positivity) hR0.le
  have hlam : ctLam c ≤ s⁻¹ := ctLam_le hc0
  have hb1 : 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * s) ≤ 174 * M ^ 2 * K / c₁ ^ 3 * c ^ (-(4 / 3) : ℝ) := by
    have hlM : (ctLam c * M) ^ 2 ≤ (s⁻¹ * M) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (ctLam_pos hc0).le hM0) (mul_le_mul_of_nonneg_right hlam hM0) 2
    calc 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * s)
        ≤ 174 * (s⁻¹ * M) ^ 2 / (c₁ ^ 3 * c) * (K * s) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) ≤ 174 * (ctLam c * M) ^ 2 / (c₁ ^ 3 * c) :=
                div_le_div_of_nonneg_left (by positivity) (by positivity) hRsq
            _ ≤ 174 * (s⁻¹ * M) ^ 2 / (c₁ ^ 3 * c) :=
                div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 174 * M ^ 2 * K / c₁ ^ 3 * c ^ (-(4 / 3) : ℝ) := by
          rw [em43, ← hs3]; field_simp
  have hpow : c ^ (-(29 / 21) : ℝ) ≤ c ^ (-(4 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hb3 : 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(4 / 3) : ℝ) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hb4 : R' * hankelRinf c ≤ 8 * |hankelTailI0| * c₁ ^ 2 * c ^ (-(4 / 3) : ℝ) := by
    have hc13 : c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c := by
      rw [← Real.rpow_add hc0]; norm_num
    have hc73 : c ^ (-(4 / 3) : ℝ) * c ^ (7 / 3 : ℝ) = c := by
      rw [← Real.rpow_add hc0]; norm_num
    have hI0 : hankelTailI0 ≤ |hankelTailI0| := le_abs_self _
    have hrinf : hankelRinf c ≤ 2 * |hankelTailI0| * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000 * c)) := by
      unfold hankelRinf
      have : -(c / 40000) = -(1 / 40000 * c) := by ring
      rw [this]
      have := Real.exp_pos (-(1 / 40000 * c))
      have := Real.rpow_pos_of_pos hc0 (1 / 3 : ℝ)
      nlinarith [mul_le_mul_of_nonneg_right hI0 (mul_pos ‹0 < c ^ (1 / 3 : ℝ)› ‹0 < Real.exp (-(1 / 40000 * c))›).le]
    calc R' * hankelRinf c ≤ (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) * hankelRinf c :=
          mul_le_mul_of_nonneg_right (hrR.trans hR2) hrinf0
      _ ≤ (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) * (2 * |hankelTailI0| * c ^ (1 / 3 : ℝ) * Real.exp (-(1 / 40000 * c))) :=
          mul_le_mul_of_nonneg_left hrinf (by positivity)
      _ = 8 * |hankelTailI0| * c₁ ^ 2 * ((c ^ (2 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) * Real.exp (-(1 / 40000 * c))) := by
          ring
      _ = 8 * |hankelTailI0| * c₁ ^ 2 * (c * Real.exp (-(1 / 40000 * c))) := by rw [hc13]
      _ ≤ 8 * |hankelTailI0| * c₁ ^ 2 * c ^ (-(4 / 3) : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc c * Real.exp (-(1 / 40000 * c)) = c ^ (-(4 / 3) : ℝ) * (c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000 * c))) := by
                rw [← mul_assoc, hc73]
            _ ≤ c ^ (-(4 / 3) : ℝ) * 1 := mul_le_mul_of_nonneg_left hexpo hcp.le
            _ = c ^ (-(4 / 3) : ℝ) := mul_one _
  nlinarith [hb1, hb3, hb4]

/-- info: 'FormalResearch.SignUncertainty.ct_trans_E1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_trans_E1

end FormalResearch.SignUncertainty

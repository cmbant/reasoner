module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasRates
public import FormalResearch.SignUncertainty.CtBoasMoments
public import FormalResearch.SignUncertainty.CtBoasMeasurable
public import FormalResearch.SignUncertainty.CtBoasLmin
public import FormalResearch.SignUncertainty.CtDyadicRegime
public import FormalResearch.SignUncertainty.CtDyadicStatement

/-!
# `ct:boas-ineq` for the concrete Hankel problem

`constant_terms_lower.tex`, `ct:boas` (inequality `ct:boas-ineq`) with the taper `w̃_R`: the concrete `BoasInputs`
(`h = hankelHL c f`, `X = boasX c ε`, `ν = boasNu c`, `wt = ctTaper ε c R`, `sf = 𝔰_far ∘ Δ`, `χ_j = tent`, `Q_j = tentQ`) and
the bound `ℬ ≥ -C c^{-4/3} log c`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies

/-- The Gaussian step in the variable `L`: `sf(L) = 𝔰_far(c e^L/π²)`. -/
noncomputable def boasSf (c : ℝ) (L : ℝ) : ℝ := sFar c (c * (Real.exp L / π ^ 2))

/-- `A_j = 3M_j' + 2S_jC_l` of `ct:Bj-pointwise`. -/
noncomputable def boasAj (ε c R Cθ a : ℝ) (j : ℕ) : ℝ :=
  3 * tapMp (ctTaper ε c R) (tapMsig c a) (taperK0 2) a j + 2 * tapS (ctTaper ε c R) (taperKw 2) a j * boasCl Cθ a j

/-- `B_j = 2S_jC_q`. -/
noncomputable def boasBj (ε c R a : ℝ) (j : ℕ) : ℝ := 2 * tapS (ctTaper ε c R) (taperKw 2) a j * boasCq c a j

/-- `K_* = 15K_mp + 7290K_wC_θ + 4050K_w`, `K_mp = (13/12)K₀`. -/
noncomputable def boasKstarC (Cθ : ℝ) : ℝ :=
  15 * (13 / 12 * taperK0 2) + 7290 * taperKw 2 * Cθ + 4050 * taperKw 2

/-- `s_j = M_j^σ W_j`. -/
noncomputable def boasSj (c a : ℝ) (j : ℕ) : ℝ := tapMsig c a j * boasW c a j

/-- The weight `e` of `ct:Bj-pointwise`, cut to `U = ⋃_{j<J} Q_j` (where the estimates hold; a bounded measurable function). -/
noncomputable def boasEU (ε c R a : ℝ) (J : ℕ) : ℝ → ℝ :=
  (⋃ j ∈ Finset.range J, tentQ a j).indicator (boasE c (ctTaper ε c R))

section fields

variable {ε c R a Cθ : ℝ} {J : ℕ}

/-- The field `freeze`. -/
theorem boas_field_freeze (hc : 3 ≤ c) (hCθ0 : 0 ≤ Cθ) (ha : 0 < a)
    (hθ' : ∀ t : ℝ, |deriv (CtOuter.outerTheta ε) t| ≤ Cθ / (1 + |t|) ^ 2)
    (I : TaperChartInputs ε c R 2) :
    ∀ j < J, ∀ L L0,
      |ctTaper ε c R L * (1 - boasSf c L) * tent (tentNode a) j L * boasKernel (boasX c ε) L -
          ctTaper ε c R L0 * (1 - boasSf c L0) * tent (tentNode a) j L0 *
            boasFrozenKernel (boasX c ε) (boasNu c) L0 L| ≤
        (tentQ a j).indicator (fun L => boasAj ε c R Cθ a j * |L - L0| +
          boasBj ε c R a j * (L - L0) ^ 2) L + boasKd a j * (L - L0) ^ 2 := by
  have hc1 : 1 < c := by linarith
  have hreg := I.reg
  have hsf : ∀ L, 0 ≤ boasSf c L ∧ boasSf c L ≤ 1 := fun L => ⟨sFar_nonneg hc1 _, sFar_le_one hc1 _⟩
  obtain ⟨hlip, hSup, -, -⟩ := ctTaper_block_bounds hc1 ha I
  exact boas_freeze_field (J := J) (c := c) (a := a) (Cθ := Cθ) (by linarith) hCθ0 ha hθ' hreg.mem hsf
    (Mp := fun j => tapMp (ctTaper ε c R) (tapMsig c a) (taperK0 2) a j)
    (S := fun j => tapS (ctTaper ε c R) (taperKw 2) a j)
    (fun j _ => tapMp_nonneg hreg ha (fun j => sigLip_nonneg hc1 _) j) (fun j _ => tapS_nonneg hreg j)
    (fun j _ => hlip j) (fun j _ => hSup j)

/-- The field `pointwise` (with `e` the uncut weight). -/
theorem boas_field_pointwise (hc : 3 ≤ c) (hCθ : 0 ≤ Cθ) (ha : 0 < a) (I : TaperChartInputs ε c R 2) :
    ∀ j < J, ∀ L ∈ tentQ a j,
      boasAj ε c R Cθ a j * boasW c a j + boasBj ε c R a j * boasW c a j ^ 2 ≤
        3 * boasSj c a j + boasKstarC Cθ * boasE c (ctTaper ε c R) L := by
  have hc1 : 1 < c := by linarith
  have hreg := I.reg
  obtain ⟨-, -, hMp, hS⟩ := ctTaper_block_bounds hc1 ha I
  have hK0 : 0 ≤ taperK0 2 := by have := taperKw_nonneg 2; unfold taperK0; positivity
  exact boas_pointwise_field (J := J) (c := c) (a := a) (Cθ := Cθ) (Kmp := 13 / 12 * taperK0 2) (Kw := taperKw 2)
    (by linarith) hCθ ha (by positivity) (taperKw_nonneg 2) (fun L => (hreg.mem L).1)
    (Mp := fun j => tapMp (ctTaper ε c R) (tapMsig c a) (taperK0 2) a j)
    (S := fun j => tapS (ctTaper ε c R) (taperKw 2) a j) (Msig := tapMsig c a)
    (fun j _ => tapS_nonneg hreg j) (fun j _ => hMp j) (fun j _ => hS j)

/-- The field `P_lb` with `Pb = 30c^{-4}` (`ct:P-lb` bookkeeping): `n = ⌈c⁶⌉`, blocks `a ≤ L_j`, `x_{J+1} ≤ log c`, the threshold `L_T ≤ a/2`,
and the regime `a³c ≥ 36·10⁶ log c`, `e^{-c} ≤ c^{-12}`, `c ≥ 2`. -/
theorem boas_field_Plb {T Lt : ℝ} {f : ℝ → ℝ} (hc3 : 3 ≤ c) (hF1 : 156000000000 * Real.log c ^ 2 ≤ (c ^ (1 / 3 : ℝ)) ^ 3)
    (hF2 : 8320 * Real.log c ≤ c ^ (1 / 3 : ℝ)) (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    (hmass : hankelMass c f = 1) (ha : 0 < a) (ha1 : a ≤ 1) (hlo : c ^ (-(1 / 3) : ℝ) ≤ a)
    (hhi : tentNode a (J + 1) ≤ Real.log c) (hLT : ∀ L, Lt ≤ L → T ≤ c * (Real.exp L / π ^ 2)) (hLTa : Lt ≤ a / 2)
    (hreg : 36000000 * Real.log c ≤ a ^ 3 * c) (hexp : Real.exp (-c) ≤ (c ^ 12)⁻¹) (X wt sf : ℝ → ℝ) :
    ∀ j < J, ∀ L0, 0 < wt L0 * (1 - sf L0) * tent (tentNode a) j L0 →
      -(30 * (c ^ 4)⁻¹) ≤ ∫ L, gaussK (boasW c a j) (L - L0) * hankelHL c f L * boasFrozenKernel X (boasNu c) L0 L := by
  have hc2 : 2 ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hlog1 : 1 ≤ Real.log c := by
    have : Real.exp 1 ≤ c := by have := Real.exp_one_lt_d9; linarith
    simpa using Real.log_le_log (Real.exp_pos 1) this
  have hn1 : c ^ 6 ≤ (⌈c ^ 6⌉₊ : ℝ) := Nat.le_ceil _
  have hn2 : (⌈c ^ 6⌉₊ : ℝ) ≤ 2 * c ^ 6 := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ c ^ 6)
    have : (1 : ℝ) ≤ c ^ 6 := one_le_pow₀ (by linarith)
    linarith
  have hn : 2 ≤ ⌈c ^ 6⌉₊ := by
    have : (2 : ℝ) ≤ (⌈c ^ 6⌉₊ : ℝ) := by
      have : (2 : ℝ) ≤ c ^ 6 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hc2 6]
      linarith
    exact_mod_cast this
  refine boas_P_lb_field (J := J) (by linarith) hF1 hF2 hf hε ha hlo hhi hLT (le_trans hLTa (by linarith)) hn
    (Pb := 30 * (c ^ 4)⁻¹) ?_ X wt sf
  intro j hj L0 hL0
  have hx := tentNode_strictMono ha
  have hLj : tentNode a (j + 1) ≤ Real.log c := le_trans (hx.monotone (by omega)) hhi
  have haL0 : 0.97 * a ≤ L0 := by
    have h2 : a ≤ tentNode a j := hx.monotone (Nat.zero_le j)
    have h3 := min_tentNode_succ_le ha j
    have h4 : tentNode a j ≤ tentNode a (j + 1) := hx.monotone (Nat.le_succ j)
    have h5 : min (tentNode a j) 1 ≤ tentNode a j := min_le_left _ _
    have h6 : tentDelta a j ≤ 37 / 1296 * tentNode a j := by
      unfold tentDelta; linarith
    linarith [hL0.1]
  have hW1 := boasW_lower (j := j) (by linarith) hlog1 ha hLj
  have hWpos : 0 < boasW c a j := by
    unfold boasW
    have h1 := tau0_pos (tentNode_pos ha (j + 1))
    have h2 : 0 < Real.log c := by linarith
    have h3 := tentNode_pos ha (j + 1)
    positivity
  have hW2 := boasW_sq_le (j := j) (by linarith) hlog1 ha ha1 (c := c)
  have hexpo : c ≤ 1 / (2 * boasW c a j ^ 2) * (L0 - Lt) ^ 2 := by
    set W := boasW c a j
    set P : ℝ := 2000000 * Real.log c / (c ^ 2 * a) with hP
    have hP0 : 0 < P := by positivity
    have h1 : 1 / (2 * P) ≤ 1 / (2 * W ^ 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have h2 : (a / 3) ^ 2 ≤ (L0 - Lt) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h3 : 1 / (2 * P) * (a / 3) ^ 2 ≤ 1 / (2 * W ^ 2) * (L0 - Lt) ^ 2 :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    refine le_trans ?_ h3
    have : 1 / (2 * P) * (a / 3) ^ 2 = a ^ 3 * c ^ 2 / (36000000 * Real.log c) := by
      rw [hP]; field_simp; ring
    rw [this, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hreg hc0.le]
  rw [hmass]
  exact frozenPb_le hc2 hn1 hn2 hWpos hW1 hexpo hexp

/-! ### Geometry of the band variable -/

/-- `Λ ≤ L_J`, and `v' ≥ R - 1/2` on `[Λ, L_J]` (so the tail beyond `Λ` is a Chebyshev tail of the first moment). -/
lemma boas_geometry {ε c R LJ : ℝ} (hc : 0 < c) (hB : TaperBand ε c R) (hLJ0 : 0 ≤ LJ) (hLJe : Real.exp LJ - 1 ≤ 5e-4)
    (hLJv : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ ctVprime c LJ) (hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ)) :
    ctTaperLam ε c R ≤ LJ ∧ ∀ L, ctTaperLam ε c R ≤ L → L ≤ LJ → R - 1 / 2 ≤ ctVprime c L := by
  have hΛ0 := hB.inputs.Lam_pos
  have hΛe := hB.Lam_le_small
  have hvΛ : R - 1 / 2 ≤ ctVprime c (ctTaperLam ε c R) := by
    have h1 := hB.inputs.v_Lam
    have h2 := hB.v_le _ hΛ0 le_rfl
    linarith
  have hle : ctTaperLam ε c R ≤ LJ := by
    by_contra hcon
    rw [not_le] at hcon
    have h0 := ctVprime_strictMonoOn hc hΛe ⟨hLJ0, hcon.le⟩ ⟨hΛ0.le, le_rfl⟩ hcon
    have h1 := hB.vp_le_R _ hΛ0 le_rfl
    have h2 := hB.Rprime_le
    linarith
  refine ⟨hle, fun L hL hLJ => ?_⟩
  have := (ctVprime_strictMonoOn hc hLJe).monotoneOn ⟨hΛ0.le, hle⟩ ⟨hΛ0.le.trans hL, hLJ⟩ hL
  linarith

/-- `L_min ≤ Λ` once `c^{4/7} + 1/2 ≤ R`. -/
lemma lmin_le_lam {ε c R Lmin : ℝ} (hc : 0 < c) (hB : TaperBand ε c R) (hL0 : 0 ≤ Lmin)
    (hLe : Real.exp Lmin - 1 ≤ 5e-4) (hLv : ctVprime c Lmin = c ^ (4 / 7 : ℝ))
    (hR : c ^ (4 / 7 : ℝ) + 1 / 2 ≤ R) : Lmin ≤ ctTaperLam ε c R := by
  have hΛ0 := hB.inputs.Lam_pos
  have hvΛ : R - 1 / 2 ≤ ctVprime c (ctTaperLam ε c R) := by
    have h1 := hB.inputs.v_Lam
    have h2 := hB.v_le _ hΛ0 le_rfl
    linarith
  by_contra hcon
  rw [not_le] at hcon
  have := ctVprime_strictMonoOn hc hLe ⟨hΛ0.le, hcon.le⟩ ⟨hL0, le_rfl⟩ hcon
  rw [hLv] at this
  linarith

/-- The field `trunc_lo` (`ct:dyadic` (1), the taper estimate): `∫_{L<L_min} w̃(1 - 𝔰_far)|h| ≤ 2^{12}(K+1)c₁^{-24}c^{-29/21}`
from the first moment `∫_{(0,L_J]} v'|h| ≤ Kc^{1/3}` (`ct_boas_moments_top`). -/
theorem boas_field_trunc_lo {c₁ K Lmin LJ : ℝ} {h : ℝ → ℝ} (hc : 3 ≤ c) (hB : TaperBand ε c R) (hc₁ : 0 < c₁)
    (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hh : Integrable h) (hmass : ∫ L, |h L| = 1)
    (hL0 : 0 < Lmin) (hLe : Real.exp Lmin - 1 ≤ 5e-4) (hLv : ctVprime c Lmin = c ^ (4 / 7 : ℝ))
    (hLΛ : Lmin ≤ ctTaperLam ε c R) (hLJ : Lmin ≤ LJ) (hLJe : Real.exp LJ - 1 ≤ 5e-4) (hK0 : 0 ≤ K)
    (hMom : ∫ L in Ioc 0 LJ, ctVprime c L * |h L| ≤ K * c ^ (1 / 3 : ℝ)) :
    ∫ L in Iio Lmin, ctTaper ε c R L * (1 - boasSf c L) * |h L| ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have hc1 : 1 < c := by linarith
  have hR0 := hB.inputs.R_pos
  have hI := hB.inputs
  have hc4 : 1 ≤ c ^ (4 / 7 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hc13 : 1 ≤ c ^ (1 / 3 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hmono := (ctVprime_strictMonoOn hc0 hLe).monotoneOn
  have hvp : ∀ L, 0 < L → L < Lmin → 0 ≤ ctVprime c L ∧ ctVprime c L ≤ c ^ (4 / 7 : ℝ) := by
    intro L hL1 hL2
    refine ⟨ctVprime_nonneg hc0 hL1.le (by linarith [Real.exp_le_exp.2 hL2.le]), ?_⟩
    rw [← hLv]; exact hmono ⟨hL1.le, hL2.le⟩ ⟨hL0.le, le_rfl⟩ hL2.le
  have hint1 : IntegrableOn (fun L => ctVprime c L * |h L|) (Icc 0 LJ) := integrableOn_vprime_mul_abs hh hLJe
  have hsub : Ioo 0 Lmin ⊆ Icc 0 LJ := fun x hx => ⟨hx.1.le, hx.2.le.trans hLJ⟩
  have hsub' : Ioo 0 Lmin ⊆ Ioc 0 LJ := fun x hx => ⟨hx.1, hx.2.le.trans hLJ⟩
  have key := boas_trunc_lo (h := h) (wt := ctTaper ε c R) (sf := boasSf c) (v := fun L => ctVprime c L + 1 / 2)
    (R := R) (V0 := c ^ (4 / 7 : ℝ) + 1 / 2) (Mv := K * c ^ (1 / 3 : ℝ) + 1 / 2) (Lmin := Lmin) hR0
    (by linarith) (fun L => ⟨sFar_nonneg hc1 _, sFar_le_one hc1 _⟩) (fun L => (hI.reg.mem L).1)
    (fun L hL => ctTaper_nonpos ε c R hL) ?_ ?_ ?_ ?_
  · refine key.trans ?_
    have hV : c ^ (4 / 7 : ℝ) + 1 / 2 ≤ 2 * c ^ (4 / 7 : ℝ) := by linarith
    have hMv0 : 0 ≤ K * c ^ (1 / 3 : ℝ) + 1 / 2 := by positivity
    have hMv : K * c ^ (1 / 3 : ℝ) + 1 / 2 ≤ (K + 1) * c ^ (1 / 3 : ℝ) := by nlinarith
    exact trunc_lo_rate hc1.le hc₁ hRlo (by linarith) hV hMv0 hMv
  · intro L hL1 hL2
    have hLΛ' : L ≤ ctTaperLam ε c R := hL2.le.trans hLΛ
    rw [ctTaper_eq_of_pos ε c R hL1]
    refine (taperW_le_pow hR0 (hI.profile.v_pos L hL1).le).trans ?_
    have hVb : ctTaperVbar ε c R L ≤ ctVprime c L + 1 / 2 := by
      unfold ctTaperVbar
      rw [if_pos hLΛ']
      exact (min_le_right _ _).trans (hB.v_le L hL1 hLΛ')
    have := pow_le_pow_left₀ (div_nonneg (hI.profile.v_pos L hL1).le hR0.le)
      (div_le_div_of_nonneg_right hVb hR0.le) 12
    linarith
  · intro L hL1 hL2
    obtain ⟨h1, h2⟩ := hvp L hL1 hL2
    exact ⟨by linarith, by linarith⟩
  · have : IntegrableOn (fun L => ctVprime c L * |h L| + 1 / 2 * |h L|) (Ioo 0 Lmin) :=
      (hint1.mono_set hsub).add (hh.abs.integrableOn.const_mul _)
    exact this.congr_fun (fun L _ => by ring) measurableSet_Ioo
  · have hA : IntegrableOn (fun L => ctVprime c L * |h L|) (Ioo 0 Lmin) := hint1.mono_set hsub
    have hBi : IntegrableOn (fun L => 1 / 2 * |h L|) (Ioo 0 Lmin) := hh.abs.integrableOn.const_mul _
    have e : ∫ L in Ioo 0 Lmin, (ctVprime c L + 1 / 2) * |h L| =
        (∫ L in Ioo 0 Lmin, ctVprime c L * |h L|) + ∫ L in Ioo 0 Lmin, 1 / 2 * |h L| := by
      rw [← integral_add hA hBi]
      exact integral_congr_ae (ae_of_all _ fun L => by ring)
    have h1 : ∫ L in Ioo 0 Lmin, ctVprime c L * |h L| ≤ K * c ^ (1 / 3 : ℝ) := by
      refine le_trans ?_ hMom
      exact setIntegral_mono_set (hint1.mono_set Ioc_subset_Icc_self)
        ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun L hL =>
          mul_nonneg (ctVprime_nonneg hc0 hL.1.le (by linarith [Real.exp_le_exp.2 hL.2])) (abs_nonneg _)))
        (ae_of_all _ hsub')
    have h2 : ∫ L in Ioo 0 Lmin, 1 / 2 * |h L| ≤ 1 / 2 := by
      rw [integral_const_mul]
      have : ∫ L in Ioo 0 Lmin, |h L| ≤ 1 := by
        rw [← hmass]; exact setIntegral_le_integral hh.abs (ae_of_all _ fun L => abs_nonneg _)
      linarith
    rw [e]; linarith

/-! ### The `e`-moment -/

/-- The constant of `(ct:Bj-pointwise)` (f): `C_e = 2·10¹¹√((1.0025κ)³)K/c₁⁵ + 7·10⁷(2K/c₁² + K)/(Λ₀√Λ₀)`, `Λ₀ = c₁²/(2.01κ)`,
`κ = langerKappa`. -/
noncomputable def boasCe (c₁ K : ℝ) : ℝ :=
  200000000000 * √((1.0025 * langerKappa) ^ 3) * K / c₁ ^ 5 +
    70000000 * (2 * K / c₁ ^ 2 + K) / ((c₁ ^ 2 / (2.01 * langerKappa)) * √(c₁ ^ 2 / (2.01 * langerKappa)))

lemma boasCe_nonneg {c₁ K : ℝ} (hc₁ : 0 < c₁) (hK : 0 ≤ K) : 0 ≤ boasCe c₁ K := by
  have := langerKappa_pos
  unfold boasCe; positivity

/-- **The tail constant**: `K c^{1/3}/(R - 1/2) + K c^{-1/3} ≤ (2K/c₁² + K) c^{-1/3}` for `R ≥ max(1, c₁²c^{2/3})`. -/
lemma B2_arith {c c₁ K R : ℝ} (hc : 1 ≤ c) (hc₁ : 0 < c₁) (hK : 0 ≤ K) (hR1 : 1 ≤ R)
    (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) :
    K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) + K * c ^ (-(1 / 3) : ℝ) ≤ (2 * K / c₁ ^ 2 + K) * c ^ (-(1 / 3) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have h13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hm13 : 0 < c ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  set r : ℝ := c₁ ^ 2 * c ^ (2 / 3 : ℝ) with hr
  have hr0 : 0 < r := by positivity
  have hRh : r / 2 ≤ R - 1 / 2 := by linarith
  have h1 : K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) ≤ K * c ^ (1 / 3 : ℝ) / (r / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hRh
  have h2 : K * c ^ (1 / 3 : ℝ) / (r / 2) = 2 * K / c₁ ^ 2 * c ^ (-(1 / 3) : ℝ) := by
    rw [hr]
    have : c ^ (-(1 / 3) : ℝ) * c ^ (2 / 3 : ℝ) = c ^ (1 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    rw [← this]; field_simp
  nlinarith

/-- **The arithmetic of the `e`-moment**: with `α_e = 2·10¹¹√((1.0025κ)³) log c/(R²√R)`, `β_e = 7·10⁷ log c/(cΛ₀√Λ₀)`,
`M_v = Kc^{1/3}` and `B₂ = Kc^{1/3}/(R - 1/2) + Kc^{-1/3}`, for `R ≥ c₁²c^{2/3}`, `R ≥ 1`:
`α_eM_v + β_eB₂ ≤ C_e c^{-4/3} log c`. -/
lemma e_moment_arith {c c₁ K R : ℝ} (hc : 1 ≤ c) (hc₁ : 0 < c₁) (hK : 0 ≤ K) (hR1 : 1 ≤ R)
    (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) :
    200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R) * (K * c ^ (1 / 3 : ℝ)) +
      70000000 * Real.log c / (c * ((c₁ ^ 2 / (2.01 * langerKappa)) * √(c₁ ^ 2 / (2.01 * langerKappa)))) *
        (K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) + K * c ^ (-(1 / 3) : ℝ)) ≤ boasCe c₁ K * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
  have hc0 : 0 < c := by linarith
  have hlog : 0 ≤ Real.log c := Real.log_nonneg hc
  have hκ := langerKappa_pos
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h13 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hm13 : 0 < c ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have h43 : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hR0 : 0 < R := by linarith
  set r : ℝ := c₁ ^ 2 * c ^ (2 / 3 : ℝ) with hr
  have hr0 : 0 < r := by positivity
  -- `R²√R ≥ c₁⁵ c^{5/3}`
  have hsq : √r = c₁ * c ^ (1 / 3 : ℝ) := by
    have h3 : (c ^ (1 / 3 : ℝ)) ^ 2 = c ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hr, show c₁ ^ 2 * c ^ (2 / 3 : ℝ) = (c₁ * c ^ (1 / 3 : ℝ)) ^ 2 by rw [mul_pow, h3]]
    exact Real.sqrt_sq (by positivity)
  have hRR : r ^ 2 * √r ≤ R ^ 2 * √R :=
    mul_le_mul (pow_le_pow_left₀ hr0.le hRlo 2) (Real.sqrt_le_sqrt hRlo) (Real.sqrt_nonneg _) (by positivity)
  have e1 : r ^ 2 * √r = c₁ ^ 5 * (c ^ (4 / 3 : ℝ) * c ^ (1 / 3 : ℝ)) := by
    rw [hsq, hr]
    have : (c ^ (2 / 3 : ℝ)) ^ 2 = c ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [mul_pow, this]; ring
  have e2 : c ^ (4 / 3 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (5 / 3 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
  have hc15 : 0 < c ^ (5 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  -- first term
  have t1 : 200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R) * (K * c ^ (1 / 3 : ℝ)) ≤
      200000000000 * √((1.0025 * langerKappa) ^ 3) * K / c₁ ^ 5 * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
    have h1 : c₁ ^ 5 * c ^ (5 / 3 : ℝ) ≤ R ^ 2 * √R := by rw [← e2, ← e1]; exact hRR
    have e3 : c ^ (1 / 3 : ℝ) / c ^ (5 / 3 : ℝ) = c ^ (-(4 / 3) : ℝ) := by
      rw [← Real.rpow_sub hc0]; norm_num
    have hA : 0 ≤ 200000000000 * √((1.0025 * langerKappa) ^ 3) := by positivity
    calc 200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R) * (K * c ^ (1 / 3 : ℝ))
        ≤ 200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (c₁ ^ 5 * c ^ (5 / 3 : ℝ)) * (K * c ^ (1 / 3 : ℝ)) := by
          gcongr
      _ = 200000000000 * √((1.0025 * langerKappa) ^ 3) * K / c₁ ^ 5 * (c ^ (1 / 3 : ℝ) / c ^ (5 / 3 : ℝ) * Real.log c) := by
          field_simp
      _ = _ := by rw [e3]
  -- second term
  have t2 : 70000000 * Real.log c / (c * ((c₁ ^ 2 / (2.01 * langerKappa)) * √(c₁ ^ 2 / (2.01 * langerKappa)))) *
        (K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) + K * c ^ (-(1 / 3) : ℝ)) ≤
      70000000 * (2 * K / c₁ ^ 2 + K) / ((c₁ ^ 2 / (2.01 * langerKappa)) * √(c₁ ^ 2 / (2.01 * langerKappa))) *
        (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
    set Λ0 : ℝ := c₁ ^ 2 / (2.01 * langerKappa) with hΛ0
    have hΛ0p : 0 < Λ0 := by positivity
    have hden : 0 < Λ0 * √Λ0 := by positivity
    have hB2 := B2_arith hc hc₁ hK hR1 hRlo
    have hB2' : 0 ≤ K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) + K * c ^ (-(1 / 3) : ℝ) := by
      have : 0 < R - 1 / 2 := by linarith
      positivity
    have e4 : c⁻¹ * c ^ (-(1 / 3) : ℝ) = c ^ (-(4 / 3) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
    calc 70000000 * Real.log c / (c * (Λ0 * √Λ0)) * (K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) + K * c ^ (-(1 / 3) : ℝ))
        ≤ 70000000 * Real.log c / (c * (Λ0 * √Λ0)) * ((2 * K / c₁ ^ 2 + K) * c ^ (-(1 / 3) : ℝ)) :=
          mul_le_mul_of_nonneg_left hB2 (by positivity)
      _ = 70000000 * (2 * K / c₁ ^ 2 + K) / (Λ0 * √Λ0) * (c⁻¹ * c ^ (-(1 / 3) : ℝ) * Real.log c) := by
          field_simp
      _ = _ := by rw [e4]
  unfold boasCe
  nlinarith [t1, t2, mul_nonneg h43.le hlog]

/-- **The fields `e_nonneg`, `e_int`, `e_moment`** (`ct:Bj-pointwise` (f)): for `U = ⋃_{j<J}Q_j` with `v' ≥ 1` below `Λ`, the cut weight
`boasEU` is nonnegative, bounded, measurable, `|h|·e` is integrable, and `∫_U |h| e ≤ C_e c^{-4/3} log c`, from the top-scale
moments `∫_{(0,L_J]} v'|h| ≤ Kc^{1/3}`, `∫_{L>L_J}|h| ≤ Kc^{-1/3}` by Chebyshev (`tail_chebyshev`). -/
theorem boas_field_e {c₁ K LJ : ℝ} {h : ℝ → ℝ} (hc : 3 ≤ c) (hB : TaperBand ε c R) (hc₁ : 0 < c₁)
    (hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R) (hR1 : 1 ≤ R) (hh : Integrable h) (hLJ0 : 0 ≤ LJ)
    (hLJe : Real.exp LJ - 1 ≤ 5e-4) (hΛJ : ctTaperLam ε c R ≤ LJ)
    (hgeom : ∀ L, ctTaperLam ε c R ≤ L → L ≤ LJ → R - 1 / 2 ≤ ctVprime c L)
    (hU : ∀ L ∈ ⋃ j ∈ Finset.range J, tentQ a j, 0 < L ∧ (L ≤ ctTaperLam ε c R → 1 ≤ ctVprime c L))
    (hK0 : 0 ≤ K) (hMom : ∫ L in Ioc 0 LJ, ctVprime c L * |h L| ≤ K * c ^ (1 / 3 : ℝ))
    (hTail : ∫ L in Ioi LJ, |h L| ≤ K * c ^ (-(1 / 3) : ℝ)) :
    (∀ L, 0 ≤ boasEU ε c R a J L) ∧ Integrable (fun L => |h L| * boasEU ε c R a J L) ∧
      ∫ L in ⋃ j ∈ Finset.range J, tentQ a j, |h L| * boasEU ε c R a J L ≤
        boasCe c₁ K * (c ^ (-(4 / 3) : ℝ) * Real.log c) := by
  have hc0 : 0 < c := by linarith
  have hI := hB.inputs
  set U : Set ℝ := ⋃ j ∈ Finset.range J, tentQ a j with hUdef
  have hUm : MeasurableSet U := Finset.measurableSet_biUnion _ fun j _ => measurableSet_tentQ a j
  set Λ := ctTaperLam ε c R with hΛdef
  have hκ := langerKappa_pos
  have hΛ0 : c₁ ^ 2 / (2.01 * langerKappa) ≤ Λ := ctTaperLam_ge hB hc0 hR1 hRlo
  have hΛ0p : 0 < c₁ ^ 2 / (2.01 * langerKappa) := by positivity
  obtain ⟨hsm, hlg, hα, hβ⟩ := ctE_moment_pointwise hB hc hΛ0p hΛ0 hU
  set αe : ℝ := 200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R) with hαe
  set βe : ℝ := 70000000 * Real.log c / (c * (c₁ ^ 2 / (2.01 * langerKappa) * √(c₁ ^ 2 / (2.01 * langerKappa)))) with hβe
  have hEU : ∀ L ∈ U, boasEU ε c R a J L = boasE c (ctTaper ε c R) L := fun L hL => by
    unfold boasEU; rw [indicator_of_mem hL]
  have hE0 : ∀ L, 0 ≤ boasEU ε c R a J L := by
    intro L
    unfold boasEU
    refine indicator_nonneg (fun L hL => ?_) L
    rw [boasE_eq]
    exact mul_nonneg (hI.reg.mem L).1 (boasBracket_nonneg hc0 (hU L hL).1)
  have hEb : ∀ L, boasEU ε c R a J L ≤ αe * R + βe := by
    intro L
    by_cases hL : L ∈ U
    · rw [hEU L hL]
      have hR0 := hI.R_pos
      rcases le_or_gt L Λ with h1 | h1
      · have h2 := hsm L hL h1
        have h3 : ctVprime c L ≤ R := (hB.vp_le_R L (hU L hL).1 h1).trans hB.Rprime_le
        have : αe * ctVprime c L ≤ αe * R := mul_le_mul_of_nonneg_left h3 hα
        linarith
      · have := hlg L hL h1
        have : 0 ≤ αe * R := mul_nonneg hα hR0.le
        linarith
    · unfold boasEU
      rw [indicator_of_notMem hL]
      have : 0 ≤ αe * R := mul_nonneg hα hI.R_pos.le
      linarith [hβ]
  have hEm : Measurable (boasEU ε c R a J) := (measurable_boasE (measurable_ctTaper hI)).indicator hUm
  have hint : Integrable (fun L => |h L| * boasEU ε c R a J L) :=
    hh.abs.mul_bdd hEm.aestronglyMeasurable (c := αe * R + βe)
      (ae_of_all _ fun L => by rw [Real.norm_eq_abs, abs_of_nonneg (hE0 L)]; exact hEb L)
  refine ⟨hE0, hint, ?_⟩
  have hint1 := integrableOn_vprime_mul_abs (c := c) hh hLJe
  have hUsub : U ∩ Iic Λ ⊆ Ioc 0 LJ := fun x hx => ⟨(hU x hx.1).1, hx.2.trans hΛJ⟩
  have hvint : IntegrableOn (fun L => ctVprime c L * |h L|) (U ∩ Iic Λ) :=
    hint1.mono_set (fun x hx => ⟨(hUsub hx).1.le, (hUsub hx).2⟩)
  have hmom : ∫ L in U ∩ Iic Λ, ctVprime c L * |h L| ≤ K * c ^ (1 / 3 : ℝ) := by
    refine le_trans ?_ hMom
    exact setIntegral_mono_set (hint1.mono_set Ioc_subset_Icc_self)
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun L hL =>
        mul_nonneg (ctVprime_nonneg hc0 hL.1.le (by linarith [Real.exp_le_exp.2 hL.2])) (abs_nonneg _)))
      (ae_of_all _ hUsub)
  have hB2 : ∫ L in Ioi Λ, |h L| ≤ K * c ^ (1 / 3 : ℝ) / (R - 1 / 2) + K * c ^ (-(1 / 3) : ℝ) :=
    tail_chebyshev (R' := R - 1 / 2) hh hc0 hLJe hI.Lam_pos.le hΛJ (by linarith)
      (fun L hL => hgeom L hL.1.le hL.2) hMom hTail
  have hsplit := boas_e_moment_split (U := U) (Lam := Λ) (v := ctVprime c) (e := boasEU ε c R a J) hUm hh hint
    (fun L hL hLΛ => by rw [hEU L hL]; exact hsm L hL hLΛ) (fun L hL hLΛ => by rw [hEU L hL]; exact hlg L hL hLΛ)
    hvint hmom hB2 hα hβ
  exact hsplit.trans (e_moment_arith (by linarith) hc₁ hK0 hR1 hRlo)

/-- **The block set `U = ⋃ Q_j`**: `L ≥ (11/12)a > 0` on `Q_j`, and `v' ≥ 1` below `Λ` (`v'(L) ≥ 0.998K·(11/12)(5/6)L_min ≥
0.76 c^{4/7}`, `a = (5/6)L_min`, `v'(L_min) = c^{4/7} ≤ 1.0025 K L_min`). -/
lemma boas_U_facts {Lmin Λ : ℝ} (hc0 : 0 < c) (ha : a = 5 / 6 * Lmin) (hL0 : 0 < Lmin) (ha1 : a ≤ 1)
    (hLme : Real.exp Lmin - 1 ≤ 5e-4) (hLv : ctVprime c Lmin = c ^ (4 / 7 : ℝ)) (hΛe : Real.exp Λ - 1 ≤ 5e-4)
    (hc47 : 2 ≤ c ^ (4 / 7 : ℝ)) :
    ∀ L ∈ ⋃ j ∈ Finset.range J, tentQ a j, 0 < L ∧ (L ≤ Λ → 1 ≤ ctVprime c L) := by
  have ha0 : 0 < a := by rw [ha]; positivity
  have hK := langerScale_pos hc0
  intro L hL
  obtain ⟨j, -, hj⟩ := Set.mem_iUnion₂.1 hL
  have h1 := tentQ_ge ha0 j hj
  have h2 : a ≤ tapEll a j := by
    unfold tapEll
    exact le_min ((tentNode_strictMono ha0).monotone (Nat.zero_le (j + 1))) ha1
  have hLa : 11 / 12 * a ≤ L := by linarith
  refine ⟨by linarith, fun hLΛ => ?_⟩
  have hL0' : 0 ≤ L := by linarith
  have hLe : Real.exp L - 1 ≤ 5e-4 := by linarith [Real.exp_le_exp.2 hLΛ]
  have hb := (ctVprime_bounds hc0 hL0' hLe).1
  have hKL := (ctVprime_bounds hc0 hL0.le hLme).2
  rw [hLv] at hKL
  have e1 : 55 / 72 * (langerScale c * Lmin) ≤ langerScale c * L := by
    have : 55 / 72 * Lmin ≤ L := by rw [ha] at hLa; linarith
    nlinarith [mul_le_mul_of_nonneg_left this hK.le]
  nlinarith [mul_le_mul_of_nonneg_left e1 (by norm_num : (0 : ℝ) ≤ 0.998)]

/-- **The field `s_moment`** (`ct:sigma-prime` (e)): `Σ_j s_j∫_{Q_j}|h| ≤ 7(e^{-(log c)²}M[f] + (2000 log c/c) B₂)` with
`B₂ ≥ ∫_{L>Λ}|h|` (the blocks of the second class lie above `L_far - 5/2 > Λ`). -/
theorem boas_field_s {κ B2 Λ : ℝ} {h : ℝ → ℝ} (hκ : 0 < κ)
    (hc : max (Real.exp 7) (max 1 (84000 ^ 2 / κ)) ≤ c) (ha : κ * c ^ (-(2 / 21) : ℝ) ≤ a) (ha1 : a ≤ 1)
    (hJ : ∀ j < J, tentNode a (j + 1) ≤ Real.log (π ^ 2 * Real.log c) + 2) (hh : Integrable h)
    (hmass : ∫ L, |h L| = 1) (hΛ : Λ < Real.log (π ^ 2 * Real.log c) - 5 / 2)
    (hB2 : ∫ L in Ioi Λ, |h L| ≤ B2) :
    ∑ j ∈ Finset.range J, boasSj c a j * ∫ L in tentQ a j, |h L| ≤
      7 * (Real.exp (-(Real.log c ^ 2)) + 2000 * Real.log c / c * B2) := by
  have ha0 : 0 < a := lt_of_lt_of_le (by
    have := Real.rpow_pos_of_pos (lt_of_lt_of_le (by positivity) (le_trans (le_max_left _ _) hc)) (-(2 / 21) : ℝ)
    positivity) ha
  have hc7 : Real.exp 7 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hlog : 7 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc7
  have hs := boas_s_moment_split (J := J) (Q := tentQ a) (s := boasSj c a) (K0 := 7)
    (s1 := Real.exp (-(Real.log c ^ 2))) (s2 := 2000 * Real.log c / c) (Lcut := Real.log (π ^ 2 * Real.log c) - 5 / 2)
    (fun j _ => measurableSet_tentQ a j) hh (by norm_num) (Real.exp_pos _).le (by positivity)
    (fun L => tentQ_overlap ha0 J L)
    (fun j hj => boas_s_classes_large hκ hc ha ha1 (hJ j hj))
  refine hs.trans ?_
  rw [hmass]
  have hmono : ∫ L in Ici (Real.log (π ^ 2 * Real.log c) - 5 / 2), |h L| ≤ B2 := by
    refine le_trans ?_ hB2
    exact setIntegral_mono_set hh.abs.integrableOn (ae_of_all _ fun L => abs_nonneg _)
      (ae_of_all _ fun L (hL : L ∈ Ici (Real.log (π ^ 2 * Real.log c) - 5 / 2)) => show Λ < L from by
        have : Real.log (π ^ 2 * Real.log c) - 5 / 2 ≤ L := hL
        linarith)
  have hs2 : 0 ≤ 2000 * Real.log c / c := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmono hs2]

end fields

end FormalResearch.SignUncertainty

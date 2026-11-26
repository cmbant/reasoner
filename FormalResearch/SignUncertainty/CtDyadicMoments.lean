module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicTaperChart

/-!
# `ct:dyadic` (1), `ct:boas` Step 3 and Step 5 (e), (f): the truncation and moment fields of `BoasInputs`

`constant_terms_lower.tex`, proof of `ct:boas`, Step 3 ("truncation"), Step 5 (e) `(ct:sigma-prime)`, (f) and the taper estimate
`∫_{ξ(0)}^{ξ(-v₀)} w̃_R |dm| = O(c^{-29/21})` of `ct:dyadic` (1) (proof of `(ct:combined)`).  Notation as in `BoasInputs`
(`h(L)dL = dm`, `wt = w̃`, `sf = 𝔰_far(Δ(L))`).

* `boas_trunc_hi` (field `trunc_hi`, **proved, unconditional**): `∫_{L > L_far+1} w̃(1 - 𝔰_far)|h| ≤ e' ∫|h|`,
  `e' = √2 e^{-4(log c)²}` (`one_sub_sFar_le`: `1 - 𝔰_far(Δ) ≤ e'` for `Δ ≥ 2D`).
* `boas_trunc_lo` (field `trunc_lo`): `∫_{L < L_min} w̃(1 - 𝔰_far)|h| ≤ 2V₀^{11}M_v/R^{12}` from `w̃ ≤ 2(v/R)^{12}` (`taperW_le_pow`),
  `v ≤ V₀` below `L_min` (`V₀ ≈ v₀ = c^{4/7}`) and the first moment `∫ v|h| ≤ M_v` (`ct:dyadic` (1), `ct:half`, second inequality:
  `∫ v dm ≤ C c^{1/3}`); `trunc_lo_rate` is the exponent bookkeeping `2V₀^{11}M_v/R^{12} ≤ C c^{-29/21}` for `V₀ ≤ 2c^{4/7}`,
  `R ≥ c₁²c^{2/3}`, `M_v ≤ C_m c^{1/3}`; `ctTaper_le_pow` and `ctTaper_nonpos` supply the taper hypotheses for the concrete `ctTaper`.
* `boas_e_moment_split` (field `e_moment`): `∫_U |h| e ≤ α_e M_v + β_e B₂` from the pointwise bounds of `(ct:Bj-pointwise)` (f)
  (`e ≤ α_e v` for `L ≤ Λ`, `e ≤ β_e` for `L > Λ`), the first moment and `B₂(R') = ∫_{L>Λ}|h|`.
* `boas_s_moment_split` (field `s_moment`): `Σ_j s_j∫_{Q_j}|h| ≤ K₀(s₁ ∫|h| + s₂ ∫_{L ≥ L_cut}|h|)` for blocks of two classes
  (`s_j ≤ s₁`; or `s_j ≤ s₂` with `Q_j ⊂ [L_cut, ∞)`), the aggregation of `(ct:sigma-prime)` (e).

**Proved.**  The pointwise inputs are proved in `CtDyadicPointwise` and `CtDyadicSigma` (`ctE_moment_pointwise`: `e ≤ α_e v'` for `L ≤ Λ`,
`e ≤ β_e` for `L > Λ`, from `τ₀ ≍ L^{1/2}`, `τ₀ ≍ e^L`; `boas_s_classes`: the two classes of `s_j`) from `TaperBand`
(`CtDyadicTaperBuild`).  Not done: the moments `ct:half`, `B₂ = O(c^{-1/3})` (`ct:dyadic` (1), the multiscale bootstrap, not in Lean),
and the final `O(c^{-4/3} log c)` accounting.
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow

/-! ### `trunc_hi` -/

lemma farD_sq_eq {c : ℝ} (hc : 1 < c) : farD c ^ 2 / (4 * farW c ^ 2) = 4 * Real.log c ^ 2 := by
  have : c ≠ 0 := by positivity
  unfold farD farW; field_simp

/-- `0 ≤ 1 - 𝔰_far(Δ) ≤ e'` for `Δ ≥ 2D`. -/
lemma one_sub_sFar_le {c Δ : ℝ} (hc : 1 < c) (hΔ : 2 * farD c ≤ Δ) :
    0 ≤ 1 - sFar c Δ ∧ 1 - sFar c Δ ≤ farE2 c := by
  have hW : 0 < farW c := by unfold farW; linarith
  have hD := farD_pos hc
  have hint : Integrable fun x => gaussK (farW c) (Δ - x) := (integrable_gaussK hW).comp_sub_left Δ
  have hall : ∫ x, gaussK (farW c) (Δ - x) = 1 := by
    rw [integral_sub_left_eq_self (gaussK (farW c)) volume Δ]; exact integral_gaussK hW
  have hsplit := integral_add_compl (measurableSet_Ioi (a := farD c)) hint
  rw [hall] at hsplit
  have hcompl : (Ioi (farD c))ᶜ = Iic (farD c) := by ext x; simp
  rw [hcompl] at hsplit
  have e : 1 - sFar c Δ = ∫ x in Iic (farD c), gaussK (farW c) (Δ - x) := by unfold sFar; linarith
  rw [e]
  refine ⟨setIntegral_nonneg measurableSet_Iic fun x _ => gaussK_nonneg' _ _ hW, ?_⟩
  have := gaussK_set_le hW (measurableSet_Iic (a := farD c)) Δ (farD c)
    (fun x hx => by
      simp only [mem_Iic] at hx
      rw [abs_of_nonneg (by linarith)]; linarith) hD.le
  rw [farD_sq_eq hc] at this
  unfold farE2
  exact this

/-- **The field `trunc_hi` of `BoasInputs`** (`ct:boas` Step 3, truncation above `L_far + 1`): for `Δ(L) ≥ 2D` on
`L > L_far + 1` (`π² log c ≤ e^{L_far}`), `∫_{L>L_far+1} w̃(1 - 𝔰_far)|h| ≤ e' ∫|h|`, `e' = √2 e^{-4(log c)²}`. -/
theorem boas_trunc_hi {c : ℝ} (hc : 1 < c) {h wt sf : ℝ → ℝ} {Lfar : ℝ} (hh : Integrable h)
    (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1) (hsf : ∀ L, sf L = sFar c (c * (Real.exp L / π ^ 2)))
    (hLfar : π ^ 2 * Real.log c ≤ Real.exp Lfar) :
    ∫ L in Ioi (Lfar + 1), wt L * (1 - sf L) * |h L| ≤ farE2 c * ∫ L, |h L| := by
  have hlog : 0 < Real.log c := Real.log_pos hc
  have hc0 : 0 < c := by linarith
  have hπ : 0 < π ^ 2 := by positivity
  have he2 : 0 ≤ farE2 c := by unfold farE2; positivity
  have hpt : ∀ L ∈ Ioi (Lfar + 1), wt L * (1 - sf L) * |h L| ≤ farE2 c * |h L| := by
    intro L hL
    have hLm : Lfar + 1 < L := hL
    have h1 : 2 * (π ^ 2 * Real.log c) ≤ Real.exp L := by
      have : Real.exp (Lfar + 1) ≤ Real.exp L := Real.exp_le_exp.2 hLm.le
      rw [Real.exp_add] at this
      have h3 : 2 < Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      nlinarith [Real.exp_pos Lfar]
    have h2 : 2 * farD c ≤ c * (Real.exp L / π ^ 2) := by
      unfold farD
      rw [← mul_div_assoc, le_div_iff₀ hπ]; nlinarith
    obtain ⟨hs0, hs1⟩ := one_sub_sFar_le hc h2
    rw [hsf L]
    have hw' := hw L
    have h4 : wt L * (1 - sFar c (c * (Real.exp L / π ^ 2))) ≤ farE2 c := by
      calc _ ≤ 1 * (1 - sFar c (c * (Real.exp L / π ^ 2))) :=
            mul_le_mul_of_nonneg_right hw'.2 hs0
        _ ≤ _ := by linarith
    exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
  calc ∫ L in Ioi (Lfar + 1), wt L * (1 - sf L) * |h L|
      ≤ ∫ L in Ioi (Lfar + 1), farE2 c * |h L| := by
        refine integral_mono_of_nonneg (ae_of_all _ fun L => ?_) (hh.abs.const_mul _).integrableOn
          ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ hpt))
        have h1 : 0 ≤ 1 - sf L := by rw [hsf L]; exact sub_nonneg.2 (sFar_le_one hc _)
        exact mul_nonneg (mul_nonneg (hw L).1 h1) (abs_nonneg _)
    _ ≤ ∫ L, farE2 c * |h L| :=
        setIntegral_le_integral (hh.abs.const_mul _) (ae_of_all _ fun L => by positivity)
    _ = farE2 c * ∫ L, |h L| := integral_const_mul _ _

/-! ### `trunc_lo` and the taper estimate -/

/-- `w̃ ≤ 2(v̄/R)^{12}` for `L > 0` and `w̃ = 0` for `L ≤ 0` (the concrete taper). -/
lemma ctTaper_le_pow {ε c R A : ℝ} (I : TaperChartInputs ε c R A) {L : ℝ} (hL : 0 < L) :
    ctTaper ε c R L ≤ 2 * (ctTaperVbar ε c R L / R) ^ 12 := by
  rw [ctTaper_eq_of_pos ε c R hL]
  exact taperW_le_pow I.R_pos (I.profile.v_pos L hL).le

lemma ctTaper_nonpos (ε c R : ℝ) {L : ℝ} (hL : L ≤ 0) : ctTaper ε c R L = 0 := by
  unfold ctTaper; rw [if_pos hL]

/-- **The field `trunc_lo` of `BoasInputs`** (the taper estimate of `ct:dyadic` (1)): if `w̃ ≤ 2(v/R)^{12}` and `0 ≤ v ≤ V₀`
on `(0, L_min)`, `w̃ = 0` on `L ≤ 0` and `∫_{(0,L_min)} v|h| ≤ M_v`, then
`∫_{L < L_min} w̃(1 - 𝔰_far)|h| ≤ 2V₀^{11}M_v/R^{12}`. -/
theorem boas_trunc_lo {h wt sf v : ℝ → ℝ} {R V0 Mv Lmin : ℝ} (hR : 0 < R) (hV0 : 0 ≤ V0)
    (hsf : ∀ L, 0 ≤ sf L ∧ sf L ≤ 1) (hw0 : ∀ L, 0 ≤ wt L) (hwt0 : ∀ L, L ≤ 0 → wt L = 0)
    (hwle : ∀ L, 0 < L → L < Lmin → wt L ≤ 2 * (v L / R) ^ 12)
    (hv : ∀ L, 0 < L → L < Lmin → 0 ≤ v L ∧ v L ≤ V0)
    (hvint : IntegrableOn (fun L => v L * |h L|) (Ioo 0 Lmin))
    (hmom : ∫ L in Ioo 0 Lmin, v L * |h L| ≤ Mv) :
    ∫ L in Iio Lmin, wt L * (1 - sf L) * |h L| ≤ 2 * V0 ^ 11 * Mv / R ^ 12 := by
  set K : ℝ := 2 * V0 ^ 11 / R ^ 12 with hK
  have hK0 : 0 ≤ K := by positivity
  set g : ℝ → ℝ := (Ioo 0 Lmin).indicator (fun L => K * (v L * |h L|)) with hg
  have hgint : Integrable g := (integrable_indicator_iff measurableSet_Ioo).2 (hvint.const_mul K)
  have hpt : ∀ L ∈ Iio Lmin, wt L * (1 - sf L) * |h L| ≤ g L := by
    intro L hL
    have hLm : L < Lmin := hL
    by_cases h0 : L ≤ 0
    · rw [hwt0 L h0]
      have : 0 ≤ g L := by
        rw [hg]; apply Set.indicator_nonneg
        intro x hx
        have := hv x hx.1 hx.2
        exact mul_nonneg hK0 (mul_nonneg this.1 (abs_nonneg _))
      simpa using this
    · have hL0 : 0 < L := not_le.1 h0
      rw [hg, Set.indicator_of_mem (show L ∈ Ioo 0 Lmin from ⟨hL0, hLm⟩)]
      obtain ⟨hv0, hvV⟩ := hv L hL0 hLm
      have h1 : wt L ≤ K * v L := by
        have h2 := hwle L hL0 hLm
        have h3 : (v L / R) ^ 12 ≤ (V0 / R) ^ 11 * (v L / R) := by
          rw [pow_succ]
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (div_nonneg hv0 hR.le) (div_le_div_of_nonneg_right hvV hR.le) 11)
            (div_nonneg hv0 hR.le)
        calc wt L ≤ 2 * (V0 / R) ^ 11 * (v L / R) := by nlinarith
          _ = K * v L := by rw [hK]; field_simp
      have hs := hsf L
      have h5 : wt L * (1 - sf L) ≤ K * v L := by
        calc _ ≤ wt L * 1 := mul_le_mul_of_nonneg_left (by linarith) (hw0 L)
          _ ≤ _ := by linarith
      calc wt L * (1 - sf L) * |h L| ≤ K * v L * |h L| := mul_le_mul_of_nonneg_right h5 (abs_nonneg _)
        _ = K * (v L * |h L|) := by ring
  calc ∫ L in Iio Lmin, wt L * (1 - sf L) * |h L| ≤ ∫ L in Iio Lmin, g L := by
        refine integral_mono_of_nonneg (ae_of_all _ fun L => ?_) hgint.integrableOn
          ((ae_restrict_iff' measurableSet_Iio).2 (ae_of_all _ hpt))
        exact mul_nonneg (mul_nonneg (hw0 L) (sub_nonneg.2 (hsf L).2)) (abs_nonneg _)
    _ = ∫ L in Ioo 0 Lmin, K * (v L * |h L|) := by
        have hi : Iio Lmin ∩ Ioo 0 Lmin = Ioo 0 Lmin := inter_eq_right.2 fun x hx => hx.2
        rw [hg, setIntegral_indicator measurableSet_Ioo, hi]
    _ = K * ∫ L in Ioo 0 Lmin, v L * |h L| := integral_const_mul _ _
    _ ≤ K * Mv := mul_le_mul_of_nonneg_left hmom hK0
    _ = 2 * V0 ^ 11 * Mv / R ^ 12 := by rw [hK]; ring

/-- **The rate of the taper estimate**, `O(c^{-29/21})`: `V₀ ≤ 2c^{4/7}` (`V₀ ≈ v₀ = c^{4/7}`), `R ≥ c₁²c^{2/3}`,
`0 ≤ M_v ≤ C_m c^{1/3}` give `2V₀^{11}M_v/R^{12} ≤ (2^{12}C_m/c₁^{24}) c^{-29/21}`. -/
lemma trunc_lo_rate {c c1 Cm R V0 Mv : ℝ} (hc : 1 ≤ c) (hc1 : 0 < c1) (hR : c1 ^ 2 * c ^ (2 / 3 : ℝ) ≤ R)
    (hV0 : 0 ≤ V0) (hV0' : V0 ≤ 2 * c ^ (4 / 7 : ℝ)) (hMv0 : 0 ≤ Mv) (hMv : Mv ≤ Cm * c ^ (1 / 3 : ℝ)) :
    2 * V0 ^ 11 * Mv / R ^ 12 ≤ 2 ^ 12 * Cm / c1 ^ 24 * c ^ (-(29 / 21) : ℝ) := by
  have hc0 : 0 < c := by linarith
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hD : 0 < (c1 ^ 2 * c ^ (2 / 3 : ℝ)) ^ 12 := by positivity
  have e1 : (c ^ (4 / 7 : ℝ)) ^ 11 = c ^ (44 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have e2 : (c ^ (2 / 3 : ℝ)) ^ 12 = c ^ (8 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have e3 : c ^ (44 / 7 : ℝ) * c ^ (1 / 3 : ℝ) = c ^ (8 : ℝ) * c ^ (-(29 / 21) : ℝ) := by
    rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
  have hden : (c1 ^ 2 * c ^ (2 / 3 : ℝ)) ^ 12 = c1 ^ 24 * c ^ (8 : ℝ) := by
    rw [mul_pow, ← pow_mul, e2]
  have hnum2 : (2 * c ^ (4 / 7 : ℝ)) ^ 11 = 2 ^ 11 * c ^ (44 / 7 : ℝ) := by rw [mul_pow, e1]
  have hV : V0 ^ 11 ≤ (2 * c ^ (4 / 7 : ℝ)) ^ 11 := pow_le_pow_left₀ hV0 hV0' 11
  have hR12 : (c1 ^ 2 * c ^ (2 / 3 : ℝ)) ^ 12 ≤ R ^ 12 := pow_le_pow_left₀ (by positivity) hR 12
  have hnum : 2 * V0 ^ 11 * Mv ≤ 2 * (2 * c ^ (4 / 7 : ℝ)) ^ 11 * (Cm * c ^ (1 / 3 : ℝ)) :=
    mul_le_mul (by linarith) hMv hMv0 (by positivity)
  calc 2 * V0 ^ 11 * Mv / R ^ 12 ≤ 2 * V0 ^ 11 * Mv / (c1 ^ 2 * c ^ (2 / 3 : ℝ)) ^ 12 :=
        div_le_div_of_nonneg_left (by positivity) hD hR12
    _ ≤ 2 * (2 * c ^ (4 / 7 : ℝ)) ^ 11 * (Cm * c ^ (1 / 3 : ℝ)) / (c1 ^ 2 * c ^ (2 / 3 : ℝ)) ^ 12 :=
        div_le_div_of_nonneg_right hnum hD.le
    _ = 2 ^ 12 * Cm * (c ^ (44 / 7 : ℝ) * c ^ (1 / 3 : ℝ)) / (c1 ^ 24 * c ^ (8 : ℝ)) := by
        rw [hden, hnum2]; ring
    _ = 2 ^ 12 * Cm / c1 ^ 24 * c ^ (-(29 / 21) : ℝ) := by
        rw [e3]
        have : c ^ (8 : ℝ) ≠ 0 := by positivity
        have : c1 ^ 24 ≠ 0 := by positivity
        field_simp

/-! ### `e_moment` and `s_moment` -/

/-- **The field `e_moment` of `BoasInputs`** (`(ct:Bj-pointwise)` (f), the splitting at `Λ`): `∫_U |h| e ≤ α_e M_v + β_e B₂`
from `e ≤ α_e v` on `U ∩ (-∞, Λ]`, `e ≤ β_e` on `U ∩ (Λ, ∞)`, `∫_{U∩(-∞,Λ]} v|h| ≤ M_v` and `∫_{L>Λ}|h| ≤ B₂`. -/
theorem boas_e_moment_split {h e v : ℝ → ℝ} {U : Set ℝ} {Lam αe βe Mv B2 : ℝ} (hU : MeasurableSet U)
    (hh : Integrable h) (hint : Integrable fun L => |h L| * e L)
    (hsm : ∀ L ∈ U, L ≤ Lam → e L ≤ αe * v L) (hlg : ∀ L ∈ U, Lam < L → e L ≤ βe)
    (hvint : IntegrableOn (fun L => v L * |h L|) (U ∩ Iic Lam))
    (hmom : ∫ L in U ∩ Iic Lam, v L * |h L| ≤ Mv) (hB2 : ∫ L in Ioi Lam, |h L| ≤ B2)
    (hα : 0 ≤ αe) (hβ : 0 ≤ βe) :
    ∫ L in U, |h L| * e L ≤ αe * Mv + βe * B2 := by
  have hs1 : MeasurableSet (U ∩ Iic Lam) := hU.inter measurableSet_Iic
  have hs2 : MeasurableSet (U ∩ Ioi Lam) := hU.inter measurableSet_Ioi
  have hsplit : U = (U ∩ Iic Lam) ∪ (U ∩ Ioi Lam) := by
    ext x; simp only [mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · intro hx; rcases le_or_gt x Lam with h1 | h1
      · exact Or.inl ⟨hx, h1⟩
      · exact Or.inr ⟨hx, h1⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hd : Disjoint (U ∩ Iic Lam) (U ∩ Ioi Lam) := by
    rw [Set.disjoint_left]; rintro x ⟨_, h1⟩ ⟨_, h2⟩
    simp only [mem_Iic, mem_Ioi] at h1 h2; linarith
  rw [hsplit, setIntegral_union hd hs2 hint.integrableOn hint.integrableOn]
  have p1 : ∫ L in U ∩ Iic Lam, |h L| * e L ≤ αe * Mv := by
    calc ∫ L in U ∩ Iic Lam, |h L| * e L ≤ ∫ L in U ∩ Iic Lam, αe * (v L * |h L|) := by
          refine setIntegral_mono_on hint.integrableOn (hvint.const_mul αe) hs1 fun L hL => ?_
          have := mul_le_mul_of_nonneg_left (hsm L hL.1 hL.2) (abs_nonneg (h L))
          nlinarith [this]
      _ = αe * ∫ L in U ∩ Iic Lam, v L * |h L| := integral_const_mul _ _
      _ ≤ αe * Mv := mul_le_mul_of_nonneg_left hmom hα
  have p2 : ∫ L in U ∩ Ioi Lam, |h L| * e L ≤ βe * B2 := by
    calc ∫ L in U ∩ Ioi Lam, |h L| * e L ≤ ∫ L in U ∩ Ioi Lam, βe * |h L| := by
          refine setIntegral_mono_on hint.integrableOn (hh.abs.const_mul βe).integrableOn hs2 fun L hL => ?_
          have := mul_le_mul_of_nonneg_left (hlg L hL.1 hL.2) (abs_nonneg (h L))
          nlinarith [this]
      _ = βe * ∫ L in U ∩ Ioi Lam, |h L| := integral_const_mul _ _
      _ ≤ βe * ∫ L in Ioi Lam, |h L| :=
          mul_le_mul_of_nonneg_left
            (setIntegral_mono_set hh.abs.integrableOn (ae_of_all _ fun L => abs_nonneg _)
              (ae_of_all _ inter_subset_right)) hβ
      _ ≤ βe * B2 := mul_le_mul_of_nonneg_left hB2 hβ
  linarith

/-- **The field `s_moment` of `BoasInputs`** (`(ct:sigma-prime)` (e)): blocks of two classes, `s_j ≤ s₁` or (`s_j ≤ s₂` and
`Q_j ⊂ [L_cut, ∞)`), with bounded overlap `K₀`, give `Σ_j s_j ∫_{Q_j}|h| ≤ K₀(s₁ ∫|h| + s₂ ∫_{L ≥ L_cut}|h|)`. -/
theorem boas_s_moment_split {h : ℝ → ℝ} {J : ℕ} {Q : ℕ → Set ℝ} {s : ℕ → ℝ} {K0 s1 s2 Lcut : ℝ}
    (hQ : ∀ j < J, MeasurableSet (Q j)) (hh : Integrable h) (hK0 : 0 ≤ K0) (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2)
    (hmult : ∀ L, ∑ j ∈ Finset.range J, (Q j).indicator (fun _ => (1 : ℝ)) L ≤ K0)
    (hcls : ∀ j < J, s j ≤ s1 ∨ (s j ≤ s2 ∧ Q j ⊆ Ici Lcut)) :
    ∑ j ∈ Finset.range J, s j * ∫ L in Q j, |h L| ≤
      K0 * (s1 * (∫ L, |h L|) + s2 * ∫ L in Ici Lcut, |h L|) := by
  set g : ℝ → ℝ := (Ici Lcut).indicator fun L => |h L| with hg
  have hg0 : ∀ L, 0 ≤ g L := fun L => Set.indicator_nonneg (fun x _ => abs_nonneg _) L
  have hgint : Integrable g := hh.abs.indicator measurableSet_Ici
  have hA := sum_setIntegral_le (g := fun L => |h L|) hQ (fun L => abs_nonneg _) hh.abs hmult
  have hB := sum_setIntegral_le (g := g) hQ hg0 hgint hmult
  have hAi : ∫ L in ⋃ j ∈ Finset.range J, Q j, |h L| ≤ ∫ L, |h L| :=
    setIntegral_le_integral hh.abs (ae_of_all _ fun L => abs_nonneg _)
  have hBi : ∫ L in ⋃ j ∈ Finset.range J, Q j, g L ≤ ∫ L in Ici Lcut, |h L| := by
    have h1 : ∫ L in ⋃ j ∈ Finset.range J, Q j, g L ≤ ∫ L, g L := setIntegral_le_integral hgint (ae_of_all _ hg0)
    have h2 : ∫ L, g L = ∫ L in Ici Lcut, |h L| := integral_indicator measurableSet_Ici
    linarith
  have hpj : ∀ j ∈ Finset.range J, s j * ∫ L in Q j, |h L| ≤
      s1 * (∫ L in Q j, |h L|) + s2 * ∫ L in Q j, g L := by
    intro j hj
    have hj' := Finset.mem_range.1 hj
    have hI0 : 0 ≤ ∫ L in Q j, |h L| := setIntegral_nonneg (hQ j hj') fun _ _ => abs_nonneg _
    have hG0 : 0 ≤ ∫ L in Q j, g L := setIntegral_nonneg (hQ j hj') fun L _ => hg0 L
    rcases hcls j hj' with h1 | ⟨h1, h2⟩
    · exact (mul_le_mul_of_nonneg_right h1 hI0).trans (le_add_of_nonneg_right (mul_nonneg hs2 hG0))
    · have e : ∫ L in Q j, g L = ∫ L in Q j, |h L| := by
        refine setIntegral_congr_fun (hQ j hj') fun L hL => ?_
        rw [hg, Set.indicator_of_mem (h2 hL)]
      rw [e]
      exact (mul_le_mul_of_nonneg_right h1 hI0).trans (le_add_of_nonneg_left (mul_nonneg hs1 hI0))
  calc ∑ j ∈ Finset.range J, s j * ∫ L in Q j, |h L|
      ≤ ∑ j ∈ Finset.range J, (s1 * (∫ L in Q j, |h L|) + s2 * ∫ L in Q j, g L) := Finset.sum_le_sum hpj
    _ = s1 * (∑ j ∈ Finset.range J, ∫ L in Q j, |h L|) + s2 * ∑ j ∈ Finset.range J, ∫ L in Q j, g L := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ s1 * (K0 * (∫ L, |h L|)) + s2 * (K0 * ∫ L in Ici Lcut, |h L|) := by
        gcongr
        · exact hA.trans (mul_le_mul_of_nonneg_left hAi hK0)
        · exact hB.trans (mul_le_mul_of_nonneg_left hBi hK0)
    _ = K0 * (s1 * (∫ L, |h L|) + s2 * ∫ L in Ici Lcut, |h L|) := by ring

/-- info: 'FormalResearch.SignUncertainty.boas_trunc_hi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_trunc_hi

/-- info: 'FormalResearch.SignUncertainty.boas_trunc_lo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_trunc_lo

/-- info: 'FormalResearch.SignUncertainty.trunc_lo_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trunc_lo_rate

/-- info: 'FormalResearch.SignUncertainty.boas_e_moment_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_e_moment_split

/-- info: 'FormalResearch.SignUncertainty.boas_s_moment_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_s_moment_split

end FormalResearch.SignUncertainty

module

public import FormalResearch.SignUncertainty.HermiteBiehlerData
public import FormalResearch.Analysis.Scheffe
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.LiminfLimsup

/-!
# Chart Compactness and All-Level Hermite–Biehler Rigidity (`FT-CC`)

Abstract Airy-chart compactness and Hermite–Biehler rigidity interface shared between Paper II
(`ModularBootstrap.FoldTip`) and Paper I (`SignUncertainty`), importing ONLY
`FormalResearch.SignUncertainty.HermiteBiehlerData`, `FormalResearch.Analysis.Scheffe`, and Mathlib
(nothing Hankel- or Virasoro-specific).

## Setting and orientation
In Airy chart coordinates `u : ℝ` matching `HermiteBiehlerData D`, extremal profiles are `≥ 0`
on the left ray `(-∞, D.tm]` and have tail tightness `∫_{Ioi R} |ψ n u| du → 0` (`u → +∞`).
Along any family `n` in filter `p`:
- `ψ n : ℝ → ℝ` is normalized (`∫ |ψ n u| = 1`, `∫ ψ n u ≤ 0`), nonnegative on `(-∞, uT n]`,
  and nonnegative at prescribed sites `uSite t n → t` (`t ∈ D.S \ {D.tm}`);
- `tail_tight`: for every `ε > 0`, `∫_{Ioi R} |ψ n u| ≤ ε` for all large `R` and eventually in `n`;
- `compactness_subseq`: any subsequence along which `uT` is bounded below has a further
  subsequence converging locally uniformly on `ℝ` to an Airy-envelope entire function `F`
  real on `ℝ`, with `uT → uLim`.

## Main results
- `ChartCompactness.uT_bddAbove`: `∃ B, ∀ᶠ n in p, uT n ≤ B` (deep-lobe contradiction if `uT → +∞`).
- `ChartCompactness.subseq_extremal`: subsequence extraction forcing `uLim = D.tm` and limit `D.normG`.
- `chartCompactness_limsup_ereal`, `chartCompactness_limsup`: `limsup uT ≤ D.tm`.
- `chartCompactness_profile`: when `uT → D.tm`, `ψ → D.normG` locally uniformly on `ℝ` and in `L¹(ℝ)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set

namespace FormalResearch.ModularBootstrap.FoldTip

open FormalResearch.SignUncertainty
open FormalResearch.Analysis
open FormalResearch.Special

/-- Abstract chart-compactness interface at any Hermite–Biehler level `D`, in Airy chart
coordinates `u : ℝ` where nonnegativity holds on `(-∞, uT n]` and tails are tight as `u → +∞`. -/
structure ChartCompactness (ι : Type*) (p : Filter ι) (D : HermiteBiehlerData) where
  ψ : ι → ℝ → ℝ
  uT : ι → ℝ
  uSite : D.S → ι → ℝ
  ψ_int : ∀ᶠ n in p, Integrable (ψ n)
  ψ_l1_eq_one : ∀ᶠ n in p, ∫ u : ℝ, |ψ n u| = 1
  ψ_integral_le_zero : ∀ᶠ n in p, ∫ u : ℝ, ψ n u ≤ 0
  ψ_tail_nonneg : ∀ᶠ n in p, ∀ u : ℝ, u ≤ uT n → 0 ≤ ψ n u
  ψ_site_nonneg : ∀ t : D.S, (t : ℝ) ≠ D.tm → ∀ᶠ n in p, 0 ≤ ψ n (uSite t n)
  uSite_tendsto : ∀ t : D.S, (t : ℝ) ≠ D.tm → Tendsto (uSite t) p (𝓝 (t : ℝ))
  tail_tight : ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∀ᶠ n in p, ∫ u in Ioi R, |ψ n u| ≤ ε
  compactness_subseq : ∀ (ns : ℕ → ι), Tendsto ns atTop p →
    (∃ B : ℝ, ∀ k : ℕ, B ≤ uT (ns k)) →
    ∃ (ms : ℕ → ℕ) (uLim : ℝ) (F : ℂ → ℂ) (C ν : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => uT (ns (ms k))) atTop (𝓝 uLim) ∧
      TendstoLocallyUniformlyOn (fun k u => ψ (ns (ms k)) u)
        (fun u : ℝ => (F (u : ℂ)).re) atTop univ ∧
      Differentiable ℂ F ∧
      Integrable (fun u : ℝ => F (u : ℂ)) ∧
      0 ≤ C ∧
      (∀ z : ℂ, ‖F z‖ ≤ C * (1 + ‖z‖) ^ ν * airyEnv z) ∧
      (∀ u : ℝ, (F (u : ℂ)).im = 0)

/-! ### Private integration & negative-part helpers -/

private lemma neg_part_integrable_cc {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable (fun u : ℝ => max 0 (-g u)) := by
  refine hg.abs.mono' ((continuous_const.max continuous_neg).comp_aestronglyMeasurable hg.aestronglyMeasurable) ?_
  filter_upwards with u
  rw [Real.norm_of_nonneg (le_max_left _ _)]
  exact max_le (abs_nonneg _) (neg_le_abs _)

private lemma neg_mass_ge_half_of_normalized {g : ℝ → ℝ} (hg : Integrable g)
    (hl1 : ∫ u : ℝ, |g u| = 1) (hint : ∫ u : ℝ, g u ≤ 0) :
    (1 / 2 : ℝ) ≤ ∫ u : ℝ, max 0 (-g u) := by
  have hsplit : (fun u => |g u| - g u) = fun u => 2 * max 0 (-g u) := by
    ext u
    rcases le_total 0 (g u) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith), sub_self, mul_zero]
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
  have hsub := integral_sub hg.abs hg
  rw [hsplit, integral_const_mul] at hsub
  linarith

private lemma integral_Icc_tendsto_cc {g : ℝ → ℝ} (hg : Integrable g) :
    Tendsto (fun R : ℝ => ∫ u in Icc (-R) R, g u) atTop (𝓝 (∫ u : ℝ, g u)) := by
  have heq : ∀ R : ℝ, ∫ u in Icc (-R) R, g u = ∫ u : ℝ, (Icc (-R) R).indicator g u := fun R =>
    (integral_indicator measurableSet_Icc).symm
  simp_rw [heq]
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖g u‖)
    (Eventually.of_forall fun R => (hg.indicator measurableSet_Icc).aestronglyMeasurable)
    (Eventually.of_forall fun R => Eventually.of_forall fun u => by
      simp only [Set.indicator]; split_ifs <;> simp)
    hg.norm (Eventually.of_forall fun u => ?_)
  exact tendsto_const_nhds.congr'
    ((eventually_ge_atTop |u|).mono fun R hR => (Set.indicator_of_mem (mem_Icc.mpr (abs_le.mp hR)) g).symm)

private lemma setIntegral_Icc_tendsto_of_tendstoUniformlyOn_cc
    {g : ℕ → ℝ → ℝ} {G : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hunif : TendstoUniformlyOn g G atTop (Icc a b))
    (hg_int : ∀ᶠ k in atTop, IntegrableOn (g k) (Icc a b))
    (hG_int : IntegrableOn G (Icc a b)) :
    Tendsto (fun k => ∫ u in Icc a b, g k u) atTop (𝓝 (∫ u in Icc a b, G u)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ := ε / (b - a + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hunif' := Metric.tendstoUniformlyOn_iff.mp hunif δ hδ
  filter_upwards [hg_int, hunif'] with k hki hku
  rw [Real.dist_eq, ← integral_sub hki hG_int]
  have h1 : |∫ u in Icc a b, (g k u - G u)| ≤ ∫ u in Icc a b, |g k u - G u| := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun u => g k u - G u)
  have h2 : ∫ u in Icc a b, |g k u - G u| ≤ ∫ _u in Icc a b, δ := by
    refine setIntegral_mono_on (hki.sub hG_int).abs continuousOn_const.integrableOn_Icc
      measurableSet_Icc fun u hu => ?_
    simpa [Real.dist_eq, abs_sub_comm] using (hku u hu).le
  have h3 : ∫ _u in Icc a b, δ = (b - a) * δ := by
    rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith)]
  have h4 : (b - a) * δ < ε := by
    dsimp [δ]; rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
  linarith

/-! ### Boundedness above of `uT` and subsequence extraction -/

/-- **Tail-tightness prevents `uT → +∞`**: eventually `uT n ≤ R₀`. -/
theorem ChartCompactness.uT_bddAbove {ι : Type*} {p : Filter ι} {D : HermiteBiehlerData}
    (C : ChartCompactness ι p D) :
    ∃ B : ℝ, ∀ᶠ n in p, C.uT n ≤ B := by
  obtain ⟨R₀, hR₀⟩ := C.tail_tight (1 / 4) (by norm_num)
  refine ⟨R₀, ?_⟩
  filter_upwards [C.ψ_int, C.ψ_l1_eq_one, C.ψ_integral_le_zero, C.ψ_tail_nonneg, hR₀ R₀ le_rfl] with
    n hψ_int hl1 hint htail htight
  by_contra hbad
  have hRu : R₀ < C.uT n := lt_of_not_ge hbad
  have hm_int := neg_part_integrable_cc hψ_int
  have hhalf := neg_mass_ge_half_of_normalized hψ_int hl1 hint
  have hzero_left : ∫ u in Iic R₀, max 0 (-C.ψ n u) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
      max_eq_left (by linarith [htail u (hu.trans hRu.le)])
  have hdecomp : (∫ u in Iic R₀, max 0 (-C.ψ n u)) + ∫ u in Ioi R₀, max 0 (-C.ψ n u) =
      ∫ u : ℝ, max 0 (-C.ψ n u) := by
    rw [← compl_Iic]
    exact integral_add_compl measurableSet_Iic hm_int
  have hright_le : ∫ u in Ioi R₀, max 0 (-C.ψ n u) ≤ ∫ u in Ioi R₀, |C.ψ n u| :=
    setIntegral_mono_on hm_int.integrableOn hψ_int.abs.integrableOn measurableSet_Ioi fun u _ =>
      max_le (abs_nonneg _) (neg_le_abs _)
  linarith

/-- Subsequence rigidity: any sequence along `p` whose threshold `uT` is bounded below and eventually
`≥ D.tm - ε` admits a further subsequence with `uT → D.tm` and `ψ → D.normG` locally uniformly. -/
theorem ChartCompactness.subseq_extremal {ι : Type*} {p : Filter ι} {D : HermiteBiehlerData}
    (C : ChartCompactness ι p D)
    (ns : ℕ → ι) (hns : Tendsto ns atTop p)
    (hB : ∃ B : ℝ, ∀ k : ℕ, B ≤ C.uT (ns k))
    (hLower : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, D.tm - ε ≤ C.uT (ns k)) :
    ∃ (ms : ℕ → ℕ) (uLim : ℝ),
      StrictMono ms ∧
      Tendsto (fun k => C.uT (ns (ms k))) atTop (𝓝 uLim) ∧
      TendstoLocallyUniformlyOn (fun k u => C.ψ (ns (ms k)) u) D.normG atTop univ ∧
      uLim = D.tm := by
  obtain ⟨ms, uLim, F, C_env, ν, hms, hu_lim, hΨ_lim, hFd, hFi, hC_env, hFb, hFreal⟩ :=
    C.compactness_subseq ns hns hB
  let ψ' : ℕ → ℝ → ℝ := fun k u => C.ψ (ns (ms k)) u
  let uT' : ℕ → ℝ := fun k => C.uT (ns (ms k))
  have htm_le : D.tm ≤ uLim := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have h1 : D.tm - ε ≤ uLim :=
      ge_of_tendsto hu_lim (hms.tendsto_atTop.eventually (hLower ε hε))
    linarith
  have hsub : Tendsto (fun k => ns (ms k)) atTop p := hns.comp hms.tendsto_atTop
  have hψ_int : ∀ᶠ k in atTop, Integrable (ψ' k) := hsub.eventually C.ψ_int
  have hψ_l1 : ∀ᶠ k in atTop, ∫ u : ℝ, |ψ' k u| = 1 := hsub.eventually C.ψ_l1_eq_one
  have hψ_le0 : ∀ᶠ k in atTop, ∫ u : ℝ, ψ' k u ≤ 0 := hsub.eventually C.ψ_integral_le_zero
  have hψ_tail : ∀ᶠ k in atTop, ∀ u : ℝ, u ≤ uT' k → 0 ≤ ψ' k u := hsub.eventually C.ψ_tail_nonneg
  have hF_cont : Continuous (fun u : ℝ => (F (u : ℂ)).re) :=
    Complex.continuous_re.comp (hFd.continuous.comp Complex.continuous_ofReal)
  have hF_nonneg_band : ∀ u : ℝ, u ≤ uLim → 0 ≤ (F (u : ℂ)).re := by
    have hlt_case : ∀ u : ℝ, u < uLim → 0 ≤ (F (u : ℂ)).re := fun u hu => by
      have hev_le : ∀ᶠ k in atTop, u ≤ uT' k :=
        (hu_lim.eventually (Ioi_mem_nhds hu)).mono fun _ h => h.le
      refine ge_of_tendsto (hΨ_lim.tendsto_at (mem_univ u)) ?_
      filter_upwards [hψ_tail, hev_le] with k htk hlek
      exact htk u hlek
    intro u hu
    rcases hu.eq_or_lt with heq | hlt
    · rw [heq]
      have hseq : Tendsto (fun j : ℕ => uLim - ((j : ℝ) + 1)⁻¹) atTop (𝓝 uLim) := by
        simpa using (tendsto_const_nhds (x := uLim)).sub
          (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
      exact ge_of_tendsto (hF_cont.continuousAt.tendsto.comp hseq)
        (Eventually.of_forall fun j => hlt_case _ (by linarith [show (0 : ℝ) < ((j : ℝ) + 1)⁻¹ by positivity]))
    · exact hlt_case u hlt
  have hF_sites : ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ (F (t : ℂ)).re := by
    intro t htS htne
    let ts : D.S := ⟨t, htS⟩
    let u' : ℕ → ℝ := fun k => C.uSite ts (ns (ms k))
    have hasymp : Tendsto u' atTop (𝓝 t) := (C.uSite_tendsto ts htne).comp hsub
    have hψ_at_u' : ∀ᶠ k in atTop, 0 ≤ ψ' k (u' k) := hsub.eventually (C.ψ_site_nonneg ts htne)
    have hlim_u' : Tendsto (fun k => ψ' k (u' k)) atTop (𝓝 ((F (t : ℂ)).re)) := by
      have hdiff : Tendsto (fun k => ψ' k (u' k) - (F (u' k : ℂ)).re) atTop (𝓝 0) := by
        rw [Metric.tendsto_nhds]; intro ε hε
        have hunif := Metric.tendstoUniformlyOn_iff.mp
          ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
            (Icc (t - 1) (t + 1)) (subset_univ _) isCompact_Icc) ε hε
        filter_upwards [hunif, hasymp.eventually (Icc_mem_nhds (by linarith : t - 1 < t) (by linarith : t < t + 1))] with k h1 h2
        rw [Real.dist_eq, sub_zero]
        simpa [Real.dist_eq, abs_sub_comm] using h1 (u' k) h2
      simpa using hdiff.add (hF_cont.continuousAt.tendsto.comp hasymp)
    exact ge_of_tendsto hlim_u' hψ_at_u'
  have hF_int_le : (∫ u : ℝ, (F (u : ℂ)).re) ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨R₀, hR₀⟩ := C.tail_tight (ε / 2) (half_pos hε)
    have hIcc := integral_Icc_tendsto_cc hFi.re
    obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp (hIcc.eventually (Metric.ball_mem_nhds _ (half_pos hε)))
    let R := max (max R₀ R₁) (|uLim| + 1)
    have hR0 : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
    have hR1 : R₁ ≤ R := (le_max_right _ _).trans (le_max_left _ _)
    have hRm : -R < uLim := by
      have := le_abs_self uLim; have := neg_abs_le uLim
      linarith [le_max_right (max R₀ R₁) (|uLim| + 1)]
    have hIcc_bd : ∫ u : ℝ, (F (u : ℂ)).re < (∫ u in Icc (-R) R, (F (u : ℂ)).re) + ε / 2 := by
      have hd := hR₁ R hR1
      rw [Real.dist_eq, abs_lt] at hd
      simp only [RCLike.re_to_complex] at hd
      linarith [hd.1, hd.2]
    have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
      (Icc (-R) R) (subset_univ _) isCompact_Icc)
    have hRpos : 0 ≤ R := by linarith [le_max_right (max R₀ R₁) (|uLim| + 1), abs_nonneg uLim]
    have hlim := setIntegral_Icc_tendsto_of_tendstoUniformlyOn_cc (by linarith : -R ≤ R) hunif
      (hψ_int.mono fun k hk => hk.integrableOn) hFi.re.integrableOn
    have hleft_le : ∀ᶠ k in atTop, -R ≤ uT' k :=
      (hu_lim.eventually (Ioi_mem_nhds hRm)).mono fun _ h => h.le
    have hk_le : ∀ᶠ k in atTop, ∫ u in Icc (-R) R, ψ' k u ≤ ε / 2 := by
      filter_upwards [hψ_int, hψ_le0, hψ_tail, hleft_le, hsub.eventually (hR₀ R hR0)] with
        k hψk hle0 htk hleT htight
      have hleft_nn : 0 ≤ ∫ u in Iio (-R), ψ' k u :=
        setIntegral_nonneg measurableSet_Iio fun u hu => htk u (le_trans (le_of_lt hu) hleT)
      have hright_bd : -∫ u in Ioi R, ψ' k u ≤ ∫ u in Ioi R, |ψ' k u| := by
        rw [← integral_neg]
        exact setIntegral_mono_on hψk.neg.integrableOn hψk.abs.integrableOn measurableSet_Ioi fun u _ =>
          neg_le_abs _
      have hdecomp : (∫ u in Iio (-R), ψ' k u) + (∫ u in Icc (-R) R, ψ' k u) +
          (∫ u in Ioi R, ψ' k u) = ∫ u : ℝ, ψ' k u := by
        have h12 : (∫ u in Iio (-R), ψ' k u) + ∫ u in Icc (-R) R, ψ' k u =
            ∫ u in Iic R, ψ' k u := by
          rw [← setIntegral_union (Set.disjoint_left.mpr fun _ hx1 hx2 => not_le.mpr (mem_Iio.mp hx1) (mem_Icc.mp hx2).1)
            measurableSet_Icc hψk.integrableOn hψk.integrableOn, Iio_union_Icc_eq_Iic (by linarith)]
        rw [h12, ← compl_Iic]
        exact integral_add_compl measurableSet_Iic hψk
      linarith
    have hIcc_le : ∫ u in Icc (-R) R, (F (u : ℂ)).re ≤ ε / 2 := le_of_tendsto hlim hk_le
    linarith
  have hF_neg_half : (1 / 2 : ℝ) ≤ ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) := by
    have hm_int := neg_part_integrable_cc hFi.re
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨R₀, hR₀⟩ := C.tail_tight ε hε
    let R := max R₀ (|uLim| + 1)
    have hR0 : R₀ ≤ R := le_max_left _ _
    have hRm : -R < uLim := by
      have := le_abs_self uLim; have := neg_abs_le uLim
      linarith [le_max_right R₀ (|uLim| + 1)]
    have hRpos : 0 ≤ R := by linarith [le_max_right R₀ (|uLim| + 1), abs_nonneg uLim]
    have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
      (Icc (-R) R) (subset_univ _) isCompact_Icc)
    have hunif_m : TendstoUniformlyOn (fun k u => max 0 (-ψ' k u))
        (fun u => max 0 (-(F (u : ℂ)).re)) atTop (Icc (-R) R) := by
      rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
      intro δ hδ
      exact (hunif δ hδ).mono fun k hk u hu => by
        have h1 := hk u hu
        rw [Real.dist_eq] at h1 ⊢
        have hlip : |max 0 (-(F (u : ℂ)).re) - max 0 (-ψ' k u)| ≤ |(F (u : ℂ)).re - ψ' k u| := by
          rcases le_total 0 (-(F (u : ℂ)).re) with a | a <;>
            rcases le_total 0 (-ψ' k u) with b | b
          · rw [max_eq_right a, max_eq_right b,
              show -(F (u : ℂ)).re - -ψ' k u = -((F (u : ℂ)).re - ψ' k u) by ring, abs_neg]
          · rw [max_eq_right a, max_eq_left b, sub_zero, abs_of_nonneg a]
            linarith [neg_abs_le ((F (u : ℂ)).re - ψ' k u)]
          · rw [max_eq_left a, max_eq_right b, zero_sub, abs_neg, abs_of_nonneg b]
            linarith [le_abs_self ((F (u : ℂ)).re - ψ' k u)]
          · rw [max_eq_left a, max_eq_left b, sub_self, abs_zero]; exact abs_nonneg _
        exact lt_of_le_of_lt hlip h1
    have hlim := setIntegral_Icc_tendsto_of_tendstoUniformlyOn_cc (by linarith : -R ≤ R) hunif_m
      (hψ_int.mono fun k hk => (neg_part_integrable_cc hk).integrableOn) hm_int.integrableOn
    have hleft_le : ∀ᶠ k in atTop, -R ≤ uT' k :=
      (hu_lim.eventually (Ioi_mem_nhds hRm)).mono fun _ h => h.le
    have hk_ge : ∀ᶠ k in atTop, (1 / 2 : ℝ) - ε ≤ ∫ u in Icc (-R) R, max 0 (-ψ' k u) := by
      filter_upwards [hψ_int, hψ_l1, hψ_le0, hψ_tail, hleft_le, hsub.eventually (hR₀ R hR0)] with
        k hψk hl1 hle0 htk hleT htight
      have hhalf := neg_mass_ge_half_of_normalized hψk hl1 hle0
      have hmk := neg_part_integrable_cc hψk
      have hleft0 : ∫ u in Iio (-R), max 0 (-ψ' k u) = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun u hu =>
          max_eq_left (by linarith [htk u (le_trans (le_of_lt hu) hleT)])
      have hright_le : ∫ u in Ioi R, max 0 (-ψ' k u) ≤ ∫ u in Ioi R, |ψ' k u| :=
        setIntegral_mono_on hmk.integrableOn hψk.abs.integrableOn measurableSet_Ioi fun u _ =>
          max_le (abs_nonneg _) (neg_le_abs _)
      have hdecomp : (∫ u in Iio (-R), max 0 (-ψ' k u)) + (∫ u in Icc (-R) R, max 0 (-ψ' k u)) +
          (∫ u in Ioi R, max 0 (-ψ' k u)) = ∫ u : ℝ, max 0 (-ψ' k u) := by
        have h12 : (∫ u in Iio (-R), max 0 (-ψ' k u)) + ∫ u in Icc (-R) R, max 0 (-ψ' k u) =
            ∫ u in Iic R, max 0 (-ψ' k u) := by
          rw [← setIntegral_union (Set.disjoint_left.mpr fun _ hx1 hx2 => not_le.mpr (mem_Iio.mp hx1) (mem_Icc.mp hx2).1)
            measurableSet_Icc hmk.integrableOn hmk.integrableOn, Iio_union_Icc_eq_Iic (by linarith)]
        rw [h12, ← compl_Iic]
        exact integral_add_compl measurableSet_Iic hmk
      linarith
    have hIcc_ge : (1 / 2 : ℝ) - ε ≤ ∫ u in Icc (-R) R, max 0 (-(F (u : ℂ)).re) :=
      ge_of_tendsto hlim hk_ge
    have hIcc_le_tot : ∫ u in Icc (-R) R, max 0 (-(F (u : ℂ)).re) ≤ ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) :=
      setIntegral_le_integral hm_int (Eventually.of_forall fun u => le_max_left _ _)
    linarith
  have hF_ne : ∃ z : ℂ, -F z ≠ 0 := by
    by_contra h0; push Not at h0
    have hFz : ∀ u : ℝ, max 0 (-(F (u : ℂ)).re) = 0 := fun u => by
      have hz := neg_eq_zero.mp (h0 (u : ℂ))
      rw [hz]; simp
    simp_rw [hFz, integral_zero] at hF_neg_half
    linarith
  obtain ⟨b, _, hH_eq, hnz⟩ := D.uniqueness (H := fun z => -F z) hFd.neg hFi.neg hC_env
    (fun z => by simpa using hFb z) (fun u => neg_eq_zero.mpr (hFreal u))
    (by rw [integral_neg, Complex.neg_re, neg_nonneg]; exact le_of_eq_of_le (integral_re hFi).symm hF_int_le)
    (fun t ht _ => by rw [Complex.neg_re]; linarith [hF_sites t ht ‹_›])
    (fun u hu => by rw [Complex.neg_re]; linarith [hF_nonneg_band u (hu.trans htm_le)])
  obtain ⟨-, hb_ratio, hH_deriv⟩ := hnz hF_ne
  have hF_eq : ∀ z : ℂ, F z = (b : ℂ) * D.G z := fun z => by
    have hz := hH_eq z; linear_combination -hz
  have huLim_eq : uLim = D.tm := by
    by_contra hne
    have hlt : D.tm < uLim := lt_of_le_of_ne htm_le (Ne.symm hne)
    have hF_tm : (F (D.tm : ℂ)).re = 0 := by
      rw [hF_eq, D.G_eq_zero_on_S D.tm D.tm_mem, mul_zero, Complex.zero_re]
    have hloc_min : IsLocalMin (fun u : ℝ => (F (u : ℂ)).re) D.tm := by
      filter_upwards [Iio_mem_nhds hlt] with u hu
      rw [hF_tm]; exact hF_nonneg_band u (le_of_lt hu)
    have hd_re : HasDerivAt (fun u : ℝ => (F (u : ℂ)).re) (deriv F (D.tm : ℂ)).re D.tm :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm
        (by simpa using (hFd (D.tm : ℂ)).hasDerivAt.comp_ofReal)
    have hd_im : HasDerivAt (fun u : ℝ => (F (u : ℂ)).im) (deriv F (D.tm : ℂ)).im D.tm :=
      Complex.imCLM.hasFDerivAt.comp_hasDerivAt D.tm
        (by simpa using (hFd (D.tm : ℂ)).hasDerivAt.comp_ofReal)
    have him0 : (deriv F (D.tm : ℂ)).im = 0 := by
      have e : (fun u : ℝ => (F (u : ℂ)).im) = fun _ => 0 := funext hFreal
      rw [e] at hd_im
      exact hd_im.unique (hasDerivAt_const D.tm 0)
    have hre0 : (deriv F (D.tm : ℂ)).re = 0 := by
      rw [← hd_re.deriv]
      exact hloc_min.deriv_eq_zero
    have hdH0 : deriv (fun z => -F z) (D.tm : ℂ) = 0 := by
      have hdH : HasDerivAt (fun z => -F z) (-deriv F (D.tm : ℂ)) (D.tm : ℂ) :=
        (hFd (D.tm : ℂ)).hasDerivAt.neg
      rw [hdH.deriv, show deriv F (D.tm : ℂ) = 0 from Complex.ext hre0 him0, neg_zero]
    exact hH_deriv D.tm D.tm_mem hdH0
  have hF_zero : ∫ u : ℝ, (F (u : ℂ)).re = 0 := by
    have heq : (fun u : ℝ => (F (u : ℂ)).re) = fun u : ℝ => b * (D.G (u : ℂ)).re := by
      ext u; rw [hF_eq (u : ℂ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [heq, integral_const_mul]
    exact mul_eq_zero_of_right b ((integral_re D.G_int).trans (by rw [D.G_integral_zero]; rfl))
  have hF_l1_eq : ∫ u : ℝ, ‖F (u : ℂ)‖ = 2 * ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) := by
    have hre_int : Integrable (fun u : ℝ => (F (u : ℂ)).re) := hFi.re
    have hre_neg : Integrable (fun u : ℝ => -(F (u : ℂ)).re) := hre_int.neg
    have hp_int : Integrable (fun u : ℝ => max 0 (F (u : ℂ)).re) :=
      (neg_part_integrable_cc hre_neg).congr (Eventually.of_forall fun u => by simp)
    have hm_int : Integrable (fun u : ℝ => max 0 (-(F (u : ℂ)).re)) :=
      neg_part_integrable_cc hre_int
    have hsp2 : (fun u : ℝ => ‖F (u : ℂ)‖) = fun u : ℝ => max 0 (F (u : ℂ)).re + max 0 (-(F (u : ℂ)).re) := by
      ext u
      have hcast : F (u : ℂ) = ((F (u : ℂ)).re : ℂ) := Complex.ext rfl (hFreal u)
      conv_lhs => rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      rcases le_total 0 (F (u : ℂ)).re with h | h <;> simp [abs_of_nonneg, abs_of_nonpos, h]
    have hp_eq : ∫ u : ℝ, max 0 (F (u : ℂ)).re = ∫ u : ℝ, max 0 (-(F (u : ℂ)).re) := by
      have h0 : ∫ u : ℝ, (max 0 (F (u : ℂ)).re - max 0 (-(F (u : ℂ)).re)) = 0 := by
        calc ∫ u : ℝ, (max 0 (F (u : ℂ)).re - max 0 (-(F (u : ℂ)).re))
            = ∫ u : ℝ, (F (u : ℂ)).re := by
              refine integral_congr_ae (Eventually.of_forall fun u => ?_)
              rcases le_total 0 (F (u : ℂ)).re with h | h <;> simp [h]
          _ = 0 := hF_zero
      rw [integral_sub hp_int hm_int] at h0; linarith
    rw [hsp2, integral_add hp_int hm_int, hp_eq]; ring
  have hF_l1_one : ∫ u : ℝ, ‖F (u : ℂ)‖ = 1 := by
    refine le_antisymm ?_ (by linarith)
    have hF_abs_int : Integrable (fun u : ℝ => |(F (u : ℂ)).re|) := hFi.re.abs
    have hnorm_eq : (fun u : ℝ => ‖F (u : ℂ)‖) = fun u : ℝ => |(F (u : ℂ)).re| := by
      ext u
      have hcast : F (u : ℂ) = ((F (u : ℂ)).re : ℂ) := Complex.ext rfl (hFreal u)
      conv_lhs => rw [hcast, Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm_eq]
    refine le_of_tendsto (integral_Icc_tendsto_cc hF_abs_int)
      ((eventually_ge_atTop (0 : ℝ)).mono fun R' hR' => ?_)
    have hunif := ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_lim
      (Icc (-R') R') (subset_univ _) isCompact_Icc)
    have hunif_abs : TendstoUniformlyOn (fun k u => |ψ' k u|) (fun u => |(F (u : ℂ)).re|)
        atTop (Icc (-R') R') := by
      rw [Metric.tendstoUniformlyOn_iff] at hunif ⊢
      intro ε hε
      exact (hunif ε hε).mono fun k hk u hu =>
        lt_of_le_of_lt (by simpa [Real.dist_eq] using abs_abs_sub_abs_le (F (u : ℂ)).re (ψ' k u)) (hk u hu)
    have hlim := setIntegral_Icc_tendsto_of_tendstoUniformlyOn_cc (by linarith : -R' ≤ R') hunif_abs
      (hψ_int.mono fun k hk => hk.abs.integrableOn) hF_abs_int.integrableOn
    refine le_of_tendsto hlim ?_
    filter_upwards [hψ_int, hψ_l1] with k hψk hl1k
    have hle := setIntegral_le_integral (s := Icc (-R') R') hψk.abs (Eventually.of_forall fun _ => abs_nonneg _)
    linarith
  have hb_val : b = (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ := by
    have hnorm : (fun u : ℝ => ‖-F (u : ℂ)‖) = fun u : ℝ => ‖F (u : ℂ)‖ := funext fun _ => norm_neg _
    rw [hb_ratio, hnorm, hF_l1_one, one_div]
  have hF_normG : (fun u : ℝ => (F (u : ℂ)).re) = D.normG := by
    ext u
    rw [hF_eq (u : ℂ), Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      hb_val, HermiteBiehlerData.normG, inv_mul_eq_div]
  rw [hF_normG] at hΨ_lim
  exact ⟨ms, uLim, hms, hu_lim, hΨ_lim, huLim_eq⟩

/-! ### Abstract rigidity headlines -/

/-- **All-level Hermite–Biehler chart rigidity (`EReal` `limsup`)**:
`limsup_{p} uT ≤ D.tm`. -/
theorem chartCompactness_limsup_ereal {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (C : ChartCompactness ι p D) :
    Filter.limsup (fun n => (C.uT n : EReal)) p ≤ (D.tm : EReal) := by
  have hev : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in p, C.uT n ≤ D.tm + ε := by
    intro ε hε
    by_contra hnot
    rw [Filter.not_eventually] at hnot
    simp only [not_le] at hnot
    obtain ⟨ns, hns, hgt⟩ := exists_seq_forall_of_frequently hnot
    obtain ⟨ms, uLim, _, hu_lim, _, hu_eq⟩ := C.subseq_extremal ns hns
      ⟨D.tm + ε, fun k => (hgt k).le⟩
      (fun δ hδ => Eventually.of_forall fun k => by linarith [hgt k])
    have hu_ge : D.tm + ε ≤ uLim :=
      ge_of_tendsto hu_lim (Eventually.of_forall fun k => (hgt (ms k)).le)
    linarith
  by_contra hlt
  push Not at hlt
  obtain ⟨x, hxA, hxL⟩ := EReal.exists_between_coe_real hlt
  have h1 := hev (x - D.tm) (sub_pos.mpr (EReal.coe_lt_coe_iff.mp hxA))
  have h1' : ∀ᶠ n in p, C.uT n ≤ x := h1.mono fun _ hn => by linarith
  have hle : Filter.limsup (fun n => (C.uT n : EReal)) p ≤ (x : EReal) :=
    Filter.limsup_le_of_le (by isBoundedDefault) (h1'.mono fun _ hn => EReal.coe_le_coe_iff.mpr hn)
  exact absurd (hxL.trans_le hle) (lt_irrefl _)

/-- **All-level Hermite–Biehler chart rigidity (`ℝ` `limsup`)**:
`limsup_{p} uT ≤ D.tm` whenever `uT` is cobounded below (for instance, once `uT` has a limit
or finite lower bound). -/
theorem chartCompactness_limsup {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (C : ChartCompactness ι p D)
    (hbdd : p.IsCoboundedUnder (· ≤ ·) C.uT) :
    Filter.limsup C.uT p ≤ D.tm := by
  by_contra hlt
  push Not at hlt
  set L := Filter.limsup C.uT p
  have hfreq : ∃ᶠ n in p, (D.tm + L) / 2 < C.uT n := by
    by_contra hnot
    rw [Filter.not_frequently] at hnot
    have hle := limsup_le_of_le hbdd (hnot.mono fun _ hn => not_lt.mp hn)
    linarith
  obtain ⟨ns, hns, hgt_s⟩ := exists_seq_forall_of_frequently hfreq
  obtain ⟨ms, uLim, _, hu_lim, _, hu_eq⟩ := C.subseq_extremal ns hns
    ⟨(D.tm + L) / 2, fun k => (hgt_s k).le⟩
    (fun δ hδ => Eventually.of_forall fun k => by linarith [hgt_s k])
  have hu_ge := ge_of_tendsto hu_lim (Eventually.of_forall fun k => (hgt_s (ms k)).le)
  linarith

/-- **All-level Hermite–Biehler profile rigidity**:
when `uT → D.tm` along `p`, the normalized chart profiles `ψ n` converge locally uniformly on `ℝ`
and in `L¹(ℝ)` to `D.normG = G_N / ‖G_N‖₁` (via `Analysis.Scheffe`). -/
theorem chartCompactness_profile {ι : Type*} {p : Filter ι} [p.NeBot] [p.IsCountablyGenerated]
    {D : HermiteBiehlerData} (C : ChartCompactness ι p D)
    (hAtt : Tendsto C.uT p (𝓝 D.tm)) :
    TendstoLocallyUniformlyOn C.ψ D.normG p univ ∧
    Tendsto (fun n => ∫ u : ℝ, |C.ψ n u - D.normG u|) p (𝓝 0) := by
  have hloc : TendstoLocallyUniformlyOn C.ψ D.normG p univ := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ]
    intro K _ hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    by_contra hnot
    have hfreq : ∃ᶠ n in p, ∃ u ∈ K, ε ≤ dist (D.normG u) (C.ψ n u) := by
      rw [Filter.not_eventually] at hnot
      exact hnot.mono fun _ hn => by push Not at hn; exact hn
    obtain ⟨ns, hns, hbad⟩ := exists_seq_forall_of_frequently hfreq
    have hgt1 := (hAtt.comp hns).eventually (Ioi_mem_nhds (by linarith : D.tm - 1 < D.tm))
    obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hgt1
    let ns' : ℕ → ι := fun k => ns (k + k₀)
    have hns' : Tendsto ns' atTop p := hns.comp (tendsto_add_atTop_nat k₀)
    obtain ⟨ms, _, _, _, hΨ_unif, -⟩ := C.subseq_extremal ns' hns'
      ⟨D.tm - 1, fun k => (hk₀ (k + k₀) (by omega)).le⟩
      (fun δ hδ => (hAtt.comp hns').eventually (eventually_ge_nhds (by linarith)))
    have hev := Metric.tendstoUniformlyOn_iff.mp
      ((tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mp hΨ_unif K (subset_univ K) hK) ε hε
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hev
    obtain ⟨u, huK, hubad⟩ := hbad (ms j₀ + k₀)
    linarith [hj₀ j₀ le_rfl u huK]
  have hL1 : Tendsto (fun n => ∫ u : ℝ, |C.ψ n u - D.normG u|) p (𝓝 0) := by
    have hae : ∀ᵐ u ∂volume, Tendsto (fun n => C.ψ n u) p (𝓝 (D.normG u)) :=
      Eventually.of_forall fun u => hloc.tendsto_at (mem_univ u)
    have hnorm : Tendsto (fun n => ∫ u : ℝ, ‖C.ψ n u‖) p (𝓝 (∫ u : ℝ, ‖D.normG u‖)) := by
      have hG : ∫ u : ℝ, ‖D.normG u‖ = 1 := by
        simpa [Real.norm_eq_abs] using D.normG_abs_integral
      rw [hG]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [C.ψ_l1_eq_one] with n hl1
      simpa only [Real.norm_eq_abs] using hl1.symm
    simpa only [Real.norm_eq_abs] using
      tendsto_integral_norm_sub_of_tendsto_ae C.ψ_int D.normG_integrable hae hnorm
  exact ⟨hloc, hL1⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.ChartCompactness.uT_bddAbove' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.ChartCompactness.uT_bddAbove

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.chartCompactness_limsup_ereal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.chartCompactness_limsup_ereal

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.chartCompactness_limsup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.chartCompactness_limsup

/-- info: 'FormalResearch.ModularBootstrap.FoldTip.chartCompactness_profile' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FoldTip.chartCompactness_profile

end FormalResearch.ModularBootstrap.FoldTip

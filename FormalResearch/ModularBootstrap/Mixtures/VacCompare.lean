module

public import FormalResearch.ModularBootstrap.Mixtures.RampedSource
public import FormalResearch.ModularBootstrap.Upper.Assembly.BumpedDesignWindow

/-!
# `pmix:vac`: the comparison of `V_mix` with the Cardy weight of the trivial product

`positive_mixtures.tex`, Proposition PM.9 (`pmix:vac`), proof: "on any compact `u`-window `x = ξ_* + O(n^{-2/3})`, so
`pmix:weight`(b) gives `V_mix/V_Vir = 𝔮_mix(ξ_*)(1 + O(n^{-2/3}))`" and "`0 < V_mix ≤ C_up K_{a'}^{(w)}`".

For a `CommonSource` `C` (an atomic signed shift measure with the comparison floor; rebased positive mixtures are instances)
write `V_s = C.src.cardyV (c'/12)` and `V_t = (trivialProductProblem w hw).cardyV (c'/12) = K^{(w)}_{c'/12}`.

* `ShiftSource.qMix`: `𝔮_mix(ξ_*) = (2ξ_*)^{w-1} A(ξ_*)/(1 - e^{-4πξ_*})²`; `FK^{mix}_c = FKc (qMix) 1 c' = A(ξ_*) FK^{(w,1)}_c`
  (`FKc_qMix`), the ratio `F^{(w,1)}/F^{mix} = 1/A(ξ_*)` of the paper;
* `cmp_window`: for every `S`, `δ > 0` and `c'` large, `|V_s(t) - A(ξ_*) V_t(t)| ≤ δ V_t(t)` and `V_t(t) > 0` at `t = c'(ξ_* + λσ)²/3`,
  `|σ| ≤ S` (the comparison on compact windows);
* `cmp_global`: `0 ≤ V_s ≤ ‖λ‖_TV V_t` for `c'/12 ≥ a₀` (the global tail comparison);
* `psiAirySrc`, `psiScaleSrc`, `integral_psiAirySrc`: the window density `Ψ^{mix}_g(u) = g V_s J` and
  `∫ Ψ^{mix} du = ∫_0^∞ g V_s dt = -g_vac/(2π)`.

All results are proved unconditionally.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Mixtures

open Real Filter Topology Set MeasureTheory
open scoped Real
open FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Crossing
  FormalResearch.ModularBootstrap.FixedWeight FormalResearch.ModularBootstrap.Upper.Window.Cardy
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Bessel FormalResearch.ModularBootstrap.WeightAxioms
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Positivity
  FormalResearch.Special

/-- The trivial product `Q ≡ 1` at the weight of the source (`V = K_a^{(w)}`). -/
abbrev ShiftSource.triv (src : ShiftSource) : FixedWeightProblem := trivialProductProblem src.w src.hw

/-- `𝔮_mix(ξ_*) = (2ξ_*)^{w-1} A(ξ_*)/(1 - e^{-4πξ_*})²` (`pmix:vac`; `= qProb prob` for `A = Q(e^{-4πx})`). -/
noncomputable def ShiftSource.qMix (src : ShiftSource) : ℝ :=
  (2 * xiStar) ^ (src.w - 1) * src.ampl xiStar / (1 - Real.exp (-(4 * π * xiStar))) ^ 2

lemma qProb_triv (w : ℕ) (hw : 1 ≤ w) :
    qProb (trivialProductProblem w hw) =
      (2 * xiStar) ^ (w - 1) / (1 - Real.exp (-(4 * π * xiStar))) ^ 2 := by
  unfold qProb
  simp

lemma ShiftSource.qMix_eq (src : ShiftSource) :
    src.qMix = src.ampl xiStar * qProb src.triv := by
  unfold qMix
  rw [qProb_triv]
  ring

lemma CommonSource.qMix_pos (C : CommonSource) : 0 < C.src.qMix := by
  have h1 := one_sub_exp_xiStar_pos
  have h2 := C.ampl_pos xiStar_pos
  have h3 := xiStar_pos
  unfold ShiftSource.qMix
  positivity

/-- `FK^{mix}_c = A(ξ_*) FK^{(w,1)}_c`. -/
lemma FKc_qMix (src : ShiftSource) (c' : ℝ) :
    FKc src.qMix 1 c' = src.ampl xiStar * FKc (qProb src.triv) 1 c' := by
  rw [src.qMix_eq, FKc_scale, FKc_scale (qProb src.triv)]
  ring

/-! ### Global domination -/

/-- `0 ≤ V_s ≤ ‖λ‖_TV V_t` on `[0, ∞)` at every charge `a = c'/12` with the floor. -/
lemma cmp_global {C : CommonSource} {c' : ℝ} (hc' : C.a₀ ≤ c' / 12) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ C.src.cardyV (c' / 12) t ∧
      C.src.cardyV (c' / 12) t ≤ C.src.tv * C.src.triv.cardyV (c' / 12) t := by
  have hA := C.at_ hc'
  refine ⟨hA.nonneg_V ht, ?_⟩
  rw [trivial_cardyV]
  exact hA.upper ht

/-- The source weight is positive on `(0, ∞)` at every charge with the floor. -/
lemma triv_cardyV_pos {C : CommonSource} {c' : ℝ} (hc' : 0 < c') {t : ℝ} (ht : 0 < t) :
    0 < C.src.triv.cardyV (c' / 12) t :=
  C.src.triv.cardyV_pos (by simp; positivity) ht

lemma triv_cardyV_nonneg (src : ShiftSource) {c' : ℝ} (hc' : 0 < c') {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ src.triv.cardyV (c' / 12) t :=
  src.triv.cardyV_nonneg (by simp; positivity) ht

/-! ### The comparison on compact windows -/

/-- **Comparison on compact windows** (`pmix:vac`, "`V_mix/V_Vir = 𝔮_mix(ξ_*)(1 + O(n^{-2/3}))`"). -/
theorem cmp_window (C : CommonSource) (S : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ c' in atTop, ∀ σ ∈ Icc (-S) S,
      0 < C.src.triv.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) ∧
      |C.src.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) -
          C.src.ampl xiStar * C.src.triv.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3)| ≤
        δ * C.src.triv.cardyV (c' / 12) (c' * (xiStar + lambdaComb c' * σ) ^ 2 / 3) := by
  have hξ := xiStar_pos
  have hA0 := C.at_ (le_refl C.a₀)
  obtain ⟨Cx, hCx, hreal⟩ := C.src.real_asymp (S := C.a₀) hA0.shift (x₀ := xiStar / 2) (half_pos hξ)
  obtain ⟨C1, hC1, htriv⟩ := cardyV_asymptotic_real C.src.triv (x₀ := xiStar / 2) (half_pos hξ)
  set L : ℝ := ∑ j, |C.src.coef j| * (4 * π * C.src.shift j) with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _)
    (by have := C.src.hshift j; positivity)
  set As : ℝ := C.src.ampl xiStar with hAs
  have hAs0 : 0 < As := C.ampl_pos hξ
  have hδ4 : 0 < δ / 4 := by positivity
  filter_upwards [eventually_ge_atTop (max 1 (24 * C.a₀)), eventually_ge_atTop (2 * C1 + 1),
    lambda_mul_le (S * L) hδ4, lambda_mul_le S (half_pos hξ),
    eventually_ge_atTop (4 * (Cx + As * C1) / δ + 1), eventually_gt_atTop (0 : ℝ)]
    with c' hc1 hc2 hlL hlS hc3 hc0 σ hσ
  have hlam := lambdaComb_pos' hc0
  have hσabs : |σ| ≤ S := abs_le.mpr ⟨hσ.1, hσ.2⟩
  have hx : xiStar / 2 ≤ xiStar + lambdaComb c' * σ := by
    have := mul_le_mul_of_nonneg_left hσ.1 hlam.le
    nlinarith only [this, hlS]
  have hxpos : 0 < xiStar + lambdaComb c' * σ := by linarith
  set x : ℝ := xiStar + lambdaComb c' * σ with hxdef
  have hSx : 0 < (2 * x) ^ (C.src.w - 1) * besselAs (c' * (2 * π * x / 3)) :=
    mul_pos (by positivity) (besselAs_pos (by positivity))
  set Sx : ℝ := (2 * x) ^ (C.src.w - 1) * besselAs (c' * (2 * π * x / 3)) with hSxdef
  have e1 := hreal hc1 hx
  have e2 := htriv (c' := c') (x := x) (by simpa using (le_max_left (1 : ℝ) _).trans hc1) hx
  rw [trivialProductProblem_nullPoly] at e2
  set Vs : ℝ := C.src.cardyV (c' / 12) (c' * x ^ 2 / 3) with hVs
  set Vt : ℝ := C.src.triv.cardyV (c' / 12) (c' * x ^ 2 / 3) with hVt
  set a : ℝ := Vs / Sx with ha
  set b : ℝ := Vt / Sx with hb
  have hcc : C1 / c' ≤ 1 / 2 := by
    rw [div_le_iff₀ hc0]; linarith
  have e2' : |b - 1| ≤ C1 / c' := e2
  have hb1 : 1 / 2 ≤ b := by
    have := (abs_le.mp e2').1
    linarith
  have hVt_eq : Vt = b * Sx := by rw [hb]; field_simp
  have hVs_eq : Vs = a * Sx := by rw [ha]; field_simp
  have hVtpos : 0 < Vt := by rw [hVt_eq]; positivity
  refine ⟨hVtpos, ?_⟩
  -- |A(x) - A(ξ_*)| ≤ L λ S
  have hAlip : |C.src.ampl x - As| ≤ L * (lambdaComb c' * S) := by
    have h1 := C.src.abs_ampl_sub_le hxpos.le hξ.le
    have h2 : |x - xiStar| ≤ lambdaComb c' * S := by
      have : x - xiStar = lambdaComb c' * σ := by rw [hxdef]; ring
      rw [this, abs_mul, abs_of_pos hlam]
      exact mul_le_mul_of_nonneg_left hσabs hlam.le
    calc |C.src.ampl x - As| ≤ L * |x - xiStar| := h1
      _ ≤ L * (lambdaComb c' * S) := mul_le_mul_of_nonneg_left h2 hL0
  have hLlS : L * (lambdaComb c' * S) ≤ δ / 4 := by
    have : lambdaComb c' * (S * L) ≤ δ / 4 := hlL
    nlinarith only [this]
  have hCx_le : Cx / c' ≤ δ / 4 - As * (C1 / c') + 0 := by
    have : (Cx + As * C1) / c' ≤ δ / 4 := by
      rw [div_le_iff₀ hc0]
      have h3 : 4 * (Cx + As * C1) / δ ≤ c' := by linarith
      rw [div_le_iff₀ hδ] at h3
      nlinarith only [h3]
    have e : (Cx + As * C1) / c' = Cx / c' + As * (C1 / c') := by ring
    linarith
  have hab : |a - As * b| ≤ δ / 2 := by
    have hd : a - As * b = (a - C.src.ampl x) + (C.src.ampl x - As) - As * (b - 1) := by ring
    have h4 : |As * (b - 1)| ≤ As * (C1 / c') := by
      rw [abs_mul, abs_of_pos hAs0]
      exact mul_le_mul_of_nonneg_left e2' hAs0.le
    rw [hd]
    calc |(a - C.src.ampl x) + (C.src.ampl x - As) - As * (b - 1)|
        ≤ |(a - C.src.ampl x) + (C.src.ampl x - As)| + |As * (b - 1)| := abs_sub _ _
      _ ≤ (|a - C.src.ampl x| + |C.src.ampl x - As|) + |As * (b - 1)| := by
          gcongr; exact abs_add_le _ _
      _ ≤ (Cx / c' + L * (lambdaComb c' * S)) + As * (C1 / c') := by
          gcongr
      _ ≤ δ / 2 := by linarith
  have hfin : |Vs - As * Vt| = |a - As * b| * Sx := by
    have : Vs - As * Vt = (a - As * b) * Sx := by rw [hVs_eq, hVt_eq]; ring
    rw [this, abs_mul, abs_of_pos hSx]
  rw [hfin, hVt_eq]
  calc |a - As * b| * Sx ≤ (δ / 2) * Sx := mul_le_mul_of_nonneg_right hab hSx.le
    _ ≤ δ * b * Sx := by
        have : δ / 2 ≤ δ * b := by nlinarith only [hb1, hδ]
        exact mul_le_mul_of_nonneg_right this hSx.le
    _ = δ * (b * Sx) := by ring

/-! ### The window density of the source -/

/-- `Ψ^{mix}_g(u) = g(t(u)) V_s(t(u)) J(t(u))` (the Cardy-window density of `sr:P` for the source). -/
noncomputable def psiAirySrc (src : ShiftSource) (c : ℝ) (g : ℝ → ℝ) (u : ℝ) : ℝ :=
  g (tAiry c u) * src.cardyV (c / 12) (tAiry c u) * jAiry c (tAiry c u)

/-- The scaling `2/(C_* FK^{mix}_c)` of `Ψ^{mix}`. -/
noncomputable def psiScaleSrc (src : ShiftSource) (c : ℝ) : ℝ := 2 / (CStar * FKc src.qMix 1 c)

lemma psiAirySrc_ofProblem (prob : FixedWeightProblem) (c : ℝ) (g : ℝ → ℝ) (u : ℝ) :
    psiAirySrc (ShiftSource.ofProblem prob) c g u = psiAiry prob c g u := rfl

lemma psiScaleSrc_pos (C : CommonSource) {c : ℝ} (hc : 0 < c) : 0 < psiScaleSrc C.src c := by
  have := FKc_pos C.qMix_pos 1 hc
  have := CStar_pos
  unfold psiScaleSrc; positivity

/-- `Ψ^{mix}_g = Ψ^{(w,1)}_{g ρ}` with `ρ = V_s / V_t` (for `t > 0`; both vanish at `t = 0` because `J(0) = 0`). -/
lemma psiAirySrc_eq_psiAiry_triv {src : ShiftSource} {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) (u : ℝ) :
    psiAirySrc src c g u =
      psiAiry src.triv c (fun t => g t * (src.cardyV (c / 12) t / src.triv.cardyV (c / 12) t)) u := by
  unfold psiAirySrc psiAiry
  set t := tAiry c u with ht
  rcases (tAiry_nonneg hc u).eq_or_lt with h0 | hpos
  · rw [← h0] at ht
    simp only [ht, jAiry_zero, mul_zero]
  · have hV : 0 < src.triv.cardyV (c / 12) t := src.triv.cardyV_pos (by simp; positivity) hpos
    field_simp

/-- **`∫ Ψ^{mix}_g du = ∫_0^∞ g V_s dt = -g_vac/(2π)`**. -/
theorem integral_psiAirySrc (src : ShiftSource) {c : ℝ} (hc : 0 < c) (g : ℝ → ℝ) :
    ∫ u, psiAirySrc src c g u = -src.gVac (c / 12) g / (2 * π) := by
  have h1 : ∀ u, psiAirySrc src c g u =
      psiAiry src.triv c (fun t => g t * (src.cardyV (c / 12) t / src.triv.cardyV (c / 12) t)) u :=
    psiAirySrc_eq_psiAiry_triv hc g
  simp_rw [h1]
  rw [integral_psiAiry src.triv hc]
  have h2 : ∫ t in Ioi (0 : ℝ), g t * (src.cardyV (c / 12) t / src.triv.cardyV (c / 12) t) *
      src.triv.cardyV (c / 12) t = ∫ t in Ioi (0 : ℝ), g t * src.cardyV (c / 12) t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have hV : 0 < src.triv.cardyV (c / 12) t :=
      src.triv.cardyV_pos (by simp; positivity) (show (0 : ℝ) < t from ht)
    field_simp
  rw [h2]
  unfold ShiftSource.gVac
  field_simp

/-- `Ψ^{mix}_g ∈ L¹(du)` for a source test function. -/
theorem integrable_psiAirySrc {C : CommonSource} {c : ℝ} (hc : 0 < c) (hA : C.F.At (c / 12)) {g : ℝ → ℝ}
    (hg : TestClass C.src (c / 12) g) : Integrable (psiAirySrc C.src c g) := by
  have h1 : ∀ u, psiAirySrc C.src c g u =
      psiAiry C.src.triv c
        (fun t => g t * (C.src.cardyV (c / 12) t / C.src.triv.cardyV (c / 12) t)) u :=
    psiAirySrc_eq_psiAiry_triv hc g
  rw [funext h1, integrable_psiAiry_iff C.src.triv hc]
  have hint : IntegrableOn (fun t => g t * C.src.cardyV (c / 12) t) (Ioi 0) := by
    refine hg.int_cardy.mono' ?_ ?_
    · exact ((hg.cont.mono Ioi_subset_Ici_self).mul
        (C.src.continuous_cardyV _).continuousOn).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA.nonneg_V (le_of_lt ht))]
  refine hint.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have hV : 0 < C.src.triv.cardyV (c / 12) t := triv_cardyV_pos hc ht
  field_simp

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.cmp_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmp_window

end FormalResearch.ModularBootstrap.Mixtures

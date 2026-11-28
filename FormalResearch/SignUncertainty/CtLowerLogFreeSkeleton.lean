module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.CtRoscAssembly
public import FormalResearch.SignUncertainty.CtCombinedTop
public import FormalResearch.SignUncertainty.CtTransBand
public import FormalResearch.SignUncertainty.CtRoscBookProof
public import FormalResearch.SignUncertainty.HankelThresholds

/-!
# Log-free `thm:ct-lower` skeleton (`eq:ct-lower` left half, `constant_terms_lower.tex`)

Proves the log-free statement `CtLowerLogFreeStatement`: `Δ₅^ε(c) - C c⁻¹ ≤ T` for every
`IsHankelFeasible c ε T f` (`c ≥ c₀`, `ε = ±1`), from **two named inputs** (`CtLowerLogFreeInputs`):
1. `window_signed`: log-free `(ct:K-signed)` + `(ct:H2-orth)` window bound
   `CtDyadicBoundSharp c₁ (fun R ε c f => ctKin R ε c f + ctOscS1 R ε c f)`;
2. `boas_sharp`: log-free `(ct:boas)` bound `CtBoasSharpStatement c₁`.

The other four pieces of `ct:dyadic` (4) (`rosc`, `trunc`, `outer`, `trans`), log-free `ctChartGap_sharp`,
and `ct_node_lower` (already log-free) are proved unconditionally here.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.CohnElkies

/-! ### Log-free predicates and two-input structure -/

/-- Log-free `CtDyadicBound`: `|Q| ≤ C (c⁻¹ η_R + c^{-4/3})`. -/
def CtDyadicBoundSharp (c₁ : ℝ) (Q : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (airyZero 1) → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → ctGoodRadius R →
        |Q R ε c f| ≤ C * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ))

/-- Log-free **`ct:dyadic` (4), `(ct:combined)`**. -/
def CtDyadicCombinedSharpStatement (c₁ : ℝ) : Prop :=
  CtDyadicBoundSharp c₁ fun R ε c f =>
    ctBudget R ε c f + ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)

/-- Log-free **`ct:boas`**: `-(C c^{-4/3}) ≤ ∫_{L ≥ ctLv0 c} w̃_R(ξ(L)) K_ε h dL`. -/
def CtBoasSharpStatement (c₁ : ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (airyZero 1) → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → ctGoodRadius R →
        -(C * c ^ (-(4 / 3) : ℝ)) ≤
          ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)

/-- Log-free **`ct_pass`**: `ctBudget R ε c f ≤ C₀ c^{-4/3}` at some `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`. -/
def CtPassLogFreeStatement (c₁ : ℝ) : Prop :=
  ∃ C₀ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (airyZero 1) → 0 < ctGap ε c T →
      ∃ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
        ctBudget R ε c f ≤ C₀ * c ^ (-(4 / 3) : ℝ)

/-- Log-free **`thm:ct-lower` (`eq:ct-lower`, left half)**: `Δ₅^ε(c) - C c⁻¹ ≤ T` (`= CtLowerStatement`). -/
abbrev CtLowerLogFreeStatement : Prop := CtLowerStatement

/-! ### Log-free assembly of `(ct:combined)` -/

/-- Log-free analogue of `ct_dyadicCombined_of_bounds`: sums the five log-free pieces of
`ctKernel_split` together with `ctKin + ctKout = 0`. -/
theorem ct_dyadicCombined_sharp_of_bounds :
    ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
      CtDyadicBoundSharp c₁ (fun R ε c f => ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f)) →
      CtDyadicBoundSharp c₁ (fun R ε c f => ctMall R ε c f - ctMtr R ε c f) →
      CtDyadicBoundSharp c₁ (fun R ε c f => ctKin R ε c f + ctOscS1 R ε c f) →
      CtDyadicBoundSharp c₁ (fun R ε c f => ctKout R ε c f + ctSout R ε c f) →
      CtDyadicBoundSharp c₁ (fun R ε c f => ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f) →
      CtDyadicCombinedSharpStatement c₁ := by
  obtain ⟨γ, hγ, hB⟩ := taperBand_pm
  refine ⟨γ, hγ, fun c₁ hc₁ hle ⟨C₁, c₁', H₁⟩ ⟨C₂, c₂, H₂⟩ ⟨C₃, c₃, H₃⟩ ⟨C₄, c₄, H₄⟩ ⟨C₅, c₅, H₅⟩ => ?_⟩
  obtain ⟨cB, hcB3, hBc⟩ := hB c₁ hc₁ hle
  refine ⟨|C₁| + |C₂| + 2 * |C₃| + 2 * |C₄| + 2 * |C₅|,
    max cB (max (max c₁' c₂) (max c₃ (max c₄ c₅))),
    fun c hc ε hε T f hfeas hm hT hgap R hR hgood => ?_⟩
  have hcB : cB ≤ c := (le_max_left _ _).trans hc
  have h1 : c₁' ≤ c := ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc
  have h2 : c₂ ≤ c := ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))).trans hc
  have h3 : c₃ ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc
  have h4 : c₄ ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have h5 : c₅ ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))).trans hc
  have hc0 : 0 < c := by linarith only [hcB3, hcB]
  have hc2 : 2 ≤ c := by linarith only [hcB3, hcB]
  have hb := hBc c hcB ε hε R hR.1 hR.2
  have hsplit := ctKernel_split hc0 hb hfeas.toIsHankelEigenfn
  have hkin_out : ctKin R ε c f + ctKout R ε c f = 0 :=
    ctKin_add_ctKout hc2 hε hfeas.toIsHankelEigenfn (ctTaperLam ε c R)
  have b1 := H₁ c h1 ε hε T f hfeas hm hT hgap R hR hgood
  have b2 := H₂ c h2 ε hε T f hfeas hm hT hgap R hR hgood
  have b3 := H₃ c h3 ε hε T f hfeas hm hT hgap R hR hgood
  have b4 := H₄ c h4 ε hε T f hfeas hm hT hgap R hR hgood
  have b5 := H₅ c h5 ε hε T f hfeas hm hT hgap R hR hgood
  set X : ℝ := c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)
  have hX0 : 0 ≤ X := by
    have hR0 : 0 ≤ R := le_trans (by positivity) hR.1
    have hη := ctEta_nonneg c₁ ε c f hR0
    positivity
  have hS : ctBudget R ε c f + ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L) =
      (ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f)) -
      (ctMall R ε c f - ctMtr R ε c f) - 2 * (ctKin R ε c f + ctOscS1 R ε c f) -
      2 * (ctKout R ε c f + ctSout R ε c f) - 2 * (ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f) := by
    rw [hsplit]
    linear_combination 2 * hkin_out
  show |ctBudget R ε c f + ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)| ≤ _
  rw [hS]
  have htri : ∀ a₁ a₂ a₃ a₄ a₅ : ℝ, |a₁ - a₂ - 2 * a₃ - 2 * a₄ - 2 * a₅| ≤
      |a₁| + |a₂| + 2 * |a₃| + 2 * |a₄| + 2 * |a₅| := by
    intro a₁ a₂ a₃ a₄ a₅
    have := abs_sub (a₁ - a₂ - 2 * a₃ - 2 * a₄) (2 * a₅)
    have := abs_sub (a₁ - a₂ - 2 * a₃) (2 * a₄)
    have := abs_sub (a₁ - a₂) (2 * a₃)
    have := abs_sub a₁ a₂
    simp only [abs_mul, show |(2 : ℝ)| = 2 by norm_num] at *
    linarith
  have b1' : |ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f)| ≤ |C₁| * X :=
    b1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  have b2' : |ctMall R ε c f - ctMtr R ε c f| ≤ |C₂| * X :=
    b2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  have b3' : |ctKin R ε c f + ctOscS1 R ε c f| ≤ |C₃| * X :=
    b3.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  have b4' : |ctKout R ε c f + ctSout R ε c f| ≤ |C₄| * X :=
    b4.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  have b5' : |ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f| ≤ |C₅| * X :=
    b5.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hX0)
  exact (htri _ _ _ _ _).trans (by nlinarith)

/-! ### The four already log-free pieces of `(ct:combined)` -/

private lemma rosc_arith_sharp {q d a Cb B x cn : ℝ} (hq : |q| ≤ d + a) (hd : d ≤ Cb * cn)
    (ha : a ≤ B * x) (hcn : 0 ≤ cn) (hB : 0 ≤ B) (hx : 0 ≤ x) : |q| ≤ (|Cb| + B) * (x + cn) := by
  have h1 : Cb * cn ≤ |Cb| * cn := mul_le_mul_of_nonneg_right (le_abs_self Cb) hcn
  have h2 : B * x ≤ B * (x + cn) := mul_le_mul_of_nonneg_left (by linarith) hB
  nlinarith [abs_nonneg Cb]

/-- Log-free **`rosc`** (`(ct:rosc)`): `ct_combined_rosc` without multiplying `c^{-4/3}` by `log c`. -/
theorem ct_combined_rosc_sharp :
    ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → CtRoscBook c₁ →
      CtDyadicBoundSharp c₁ fun R ε c f => ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f) := by
  obtain ⟨ρ₁, M₁, hρ₁, hM₁, hw₁⟩ := ctPsi_window (ε := 1) (Or.inl rfl)
  obtain ⟨ρ₂, M₂, hρ₂, hM₂, hw₂⟩ := ctPsi_window (ε := -1) (Or.inr rfl)
  obtain ⟨Ccmp, R₀, hCcmp, hcmp⟩ := airyRplusComparison
  refine ⟨min ctChartC1 (min (ρ₁ / 16) (ρ₂ / 16)), lt_min ctChartC1_pos (lt_min (by positivity) (by positivity)), ?_⟩
  intro c₁ hc₁ hγ hBook
  have hle : c₁ ≤ ctChartC1 := hγ.trans (min_le_left _ _)
  have hρ1 : c₁ ≤ ρ₁ / 16 := hγ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρ2 : c₁ ≤ ρ₂ / 16 := hγ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc₁1 : c₁ ≤ 1 := hle.trans (ctChartC1_le.trans (by norm_num))
  obtain ⟨C₁, c₀₁, hC₁, H₁⟩ := ctChartComplex_of_le hc₁ hle
  obtain ⟨C₂, c₀₂, hC₂, H₂⟩ := ctChartComplex_ctChartC1
  obtain ⟨Cb, c₀b, Hb⟩ := hBook
  set t : ℝ := max R₀ 1 / c₁ ^ 2 with ht
  have hc12 : 0 < c₁ ^ 2 := by positivity
  have ht0 : 0 ≤ t := by positivity
  set X : ℝ := max (max (max c₀₁ c₀₂) (max c₀b 3e6)) (max (max (t ^ (3 / 2 : ℝ)) ((M₁ + M₂ + 1) / c₁ ^ 2))
    ((|C₂| + 1) ^ 3))
  refine ⟨|Cb| + Ccmp * (c₁ ^ 3)⁻¹, X, ?_⟩
  intro c hcX ε hε T f hfeas hmass hT hgap R hR hgood
  have hc3 : 3e6 ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hcX
  have hc0 : 0 < c := by linarith
  have hc01 : c₀₁ ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hcX
  have hc02 : c₀₂ ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hcX
  have hc0b : c₀b ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hcX
  have hct : t ^ (3 / 2 : ℝ) ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hcX
  have hcM : (M₁ + M₂ + 1) / c₁ ^ 2 ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hcX
  have hcC : (|C₂| + 1) ^ 3 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hcX
  have hRt := le_rpow_two_thirds ht0 hct
  have hmax : max R₀ 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by
    have := mul_le_mul_of_nonneg_left hRt hc12.le
    rwa [ht, mul_div_cancel₀ _ hc12.ne'] at this
  have hR0' : R₀ ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := (le_max_left _ _).trans hmax
  have hRpos : 0 < c₁ ^ 2 * c ^ (2 / 3 : ℝ) := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hmax)
  have hRlo : c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R := hR.1
  have hRhi : R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) := hR.2
  have hR0 : 0 < R := lt_of_lt_of_le hRpos hRlo
  obtain ⟨N, hN, hD⟩ := airy_circleData hR0 (ctGoodRadius_ne_zero hR0 hgood)
  have hMc : M₁ < 2 * c₁ ^ 2 * c ∧ M₂ < 2 * c₁ ^ 2 * c := by
    have h1 : M₁ + M₂ + 1 ≤ c₁ ^ 2 * c := by rw [div_le_iff₀ hc12] at hcM; linarith
    constructor <;> nlinarith [mul_pos hc12 hc0]
  have hcC' : C₂ * c ^ (-(1 / 3 : ℝ)) < 1 := by
    have h1 : |C₂| + 1 ≤ c ^ (1 / 3 : ℝ) := by
      have := Real.rpow_le_rpow (by positivity) hcC (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at this
    have h2 : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_lt_one h2]
    linarith [le_abs_self C₂]
  have hair : ‖ctRoscAiry R ε c f N‖ ≤ Ccmp * R ^ (-(3 / 2) : ℝ) * ctEta c₁ ε c f R := by
    have hcmpR : ∀ θ ∈ Icc (0 : ℝ) π, ‖ctW6 R (circleMap 0 R θ)‖ *
        ‖airyRplus (circleMap 0 R θ) - 2 * airyUpE (circleMap 0 R θ)‖ ≤
          Ccmp * R ^ (-(3 / 2) : ℝ) * ‖airyUpE (circleMap 0 R θ)‖ := fun θ hθ =>
      hcmp R (hR0'.trans hRlo) hgood θ hθ
    rcases hε with rfl | rfl
    · exact ctRoscAiry_le hc₁ hle (H₁ 1 (Or.inl rfl) c hc01) (H₂ 1 (Or.inl rfl) c hc02) ⟨hρ₁, hM₁, hw₁⟩
        (by nlinarith only [hc₁, hc₁1, hρ1]) hMc.1 hc3 hcC' hfeas.toIsHankelEigenfn hR0 hRhi hD hcmpR
    · exact ctRoscAiry_le hc₁ hle (H₁ (-1) (Or.inr rfl) c hc01) (H₂ (-1) (Or.inr rfl) c hc02) ⟨hρ₂, hM₂, hw₂⟩
        (by nlinarith only [hc₁, hc₁1, hρ2]) hMc.2 hc3 hcC' hfeas.toIsHankelEigenfn hR0 hRhi hD hcmpR
  have hbk := Hb c hc0b ε hε T f hfeas hmass hT hgap R hR hgood N hN
  have hKle : R ^ (-(3 / 2) : ℝ) ≤ (c₁ ^ 3)⁻¹ * c⁻¹ := by
    rw [← rpow_neg_three_halves hc₁ hc0]
    exact Real.rpow_le_rpow_of_nonpos hRpos hRlo (by norm_num)
  have hη := ctEta_nonneg c₁ ε c f hR0.le
  have hcneg : 0 ≤ c ^ (-(4 / 3) : ℝ) := Real.rpow_nonneg hc0.le _
  set Q : ℝ := ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f)
  have h1 : |Q| ≤ ‖(Q : ℂ) - ctRoscAiry R ε c f N‖ + ‖ctRoscAiry R ε c f N‖ := by
    rw [← Real.norm_eq_abs, ← Complex.norm_real]
    calc ‖(Q : ℂ)‖ = ‖((Q : ℂ) - ctRoscAiry R ε c f N) + ctRoscAiry R ε c f N‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  have h2 : Ccmp * R ^ (-(3 / 2) : ℝ) * ctEta c₁ ε c f R ≤ Ccmp * (c₁ ^ 3)⁻¹ * (c⁻¹ * ctEta c₁ ε c f R) := by
    have := mul_le_mul_of_nonneg_left hKle hCcmp
    calc _ ≤ Ccmp * ((c₁ ^ 3)⁻¹ * c⁻¹) * ctEta c₁ ε c f R := mul_le_mul_of_nonneg_right this hη
      _ = _ := by ring
  have hpos1 : 0 ≤ Ccmp * (c₁ ^ 3)⁻¹ := mul_nonneg hCcmp (by positivity)
  have hcη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R := mul_nonneg (inv_nonneg.2 hc0.le) hη
  exact rosc_arith_sharp h1 hbk (hair.trans h2) hcneg hpos1 hcη

/-- Log-free **`trunc`**: `ct_combined_trunc` without the final `log c` factor. -/
theorem ct_combined_trunc_sharp : ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
    CtDyadicBoundSharp c₁ fun R ε c f => ctMall R ε c f - ctMtr R ε c f := by
  obtain ⟨K, cM, hK0, hmom⟩ := ct_boas_moments_top
  obtain ⟨κ₀, hκ₀, cL, hcL1, hL⟩ := ctLv0_facts
  obtain ⟨γ, hγ, hband⟩ := taperBand_pm
  refine ⟨min γ (1 / 200), lt_min hγ (by norm_num), fun c₁ hc₁ hc₁le => ?_⟩
  have hc₁3 : c₁ ≤ 1 / 200 := hc₁le.trans (min_le_right _ _)
  obtain ⟨cB, hcB3, hB⟩ := hband c₁ hc₁ (hc₁le.trans (min_le_left _ _))
  have hev : ∀ᶠ c : ℝ in atTop, cM ≤ c ∧ cL ≤ c ∧ cB ≤ c ∧ Real.exp 7 ≤ c ∧
      (2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) := by
    filter_upwards [eventually_ge_atTop cM, eventually_ge_atTop cL, eventually_ge_atTop cB,
      eventually_ge_atTop (Real.exp 7), ev_hcR hc₁] with c h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨2 ^ 12 * (K + 1) / c₁ ^ 24, c₀, fun c hc ε hε T f hf hm hT _hgap R hR _hgood => ?_⟩
  obtain ⟨hcM, hcL, hcB, hc7, hc47, hcR⟩ := hc₀ c hc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc3 : 3 ≤ c := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
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
  have hpow : c ^ (-(29 / 21) : ℝ) ≤ c ^ (-(4 / 3) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hC0 : 0 ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 := by positivity
  have hη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R :=
    mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f (le_trans (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hc0.le _)) hR.1))
  calc |ctMall R ε c f - ctMtr R ε c f| ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) := by
        rw [e1]; exact e2.trans key
    _ ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(4 / 3) : ℝ) := mul_le_mul_of_nonneg_left hpow hC0
    _ ≤ 2 ^ 12 * (K + 1) / c₁ ^ 24 * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hC0

/-- Log-free **`outer`**: `ct_combined_outer` without the final `log c` factor. -/
theorem ct_combined_outer_sharp : ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
    CtDyadicBoundSharp c₁ fun R ε c f => ctKout R ε c f + ctSout R ε c f := by
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
  have hΛlow : lam₀ ≤ Λ := by
    have h1 : R - 1 / 2 ≤ 1.0025 * langerScale c * Λ := hBR.Rprime_ge.trans hBR.Rprime_le_Lam
    have h2 : c₁ ^ 2 * c ^ (2 / 3 : ℝ) / 2 ≤ R - 1 / 2 := by linarith [hR.1]
    unfold langerScale at h1
    rw [hlam₀, div_le_iff₀ (by positivity)]
    have h3 : c ^ (2 / 3 : ℝ) * c₁ ^ 2 ≤ c ^ (2 / 3 : ℝ) * (Λ * (4 * langerKappa)) := by
      linarith only [h1, h2, mul_pos (mul_pos hκ h23) hΛ0]
    exact le_of_mul_le_mul_left h3 h23
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
    exact this.trans (div_le_div_of_nonneg_left hK' (by positivity) (mul_le_mul_of_nonneg_left hmin hc0.le))
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
  have hR'pos : 0 < R - 1 / 2 := by linarith only [hR.1, hR1]
  have htail := tail_chebyshev (c := c) (Λ := Λ) (R' := R - 1 / 2) (M := K * c ^ (1 / 3 : ℝ)) (B := K * c ^ (-(1 / 3) : ℝ))
    hh hc0 hLJe hΛ0.le hΛJ hR'pos (fun L hL => hgeom L hL.1.le hL.2) hMom hTail
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
    have e : 2 * K / c₁ ^ 2 * s⁻¹ * (c₁ ^ 2 * (s * s) / 2) = K * s := by field_simp
    linarith
  have hmass : ∫ L in Ioi Λ, |hankelHL c f L| ≤ (2 * K / c₁ ^ 2 + K) * s⁻¹ := by
    have := htail.trans (add_le_add_left hq _)
    linarith only [this]
  have hη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R :=
    mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hCnn : 0 ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) := by positivity
  have hfin : K' / (c * μ₀) * ∫ L in Ioi Λ, |hankelHL c f L| ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) * c ^ (-(4 / 3) : ℝ) := by
    refine (mul_le_mul_of_nonneg_left hmass (by positivity)).trans (le_of_eq ?_)
    rw [em43]; field_simp
  calc |ctKout R ε c f + ctSout R ε c f| ≤ _ := hb1.trans hfin
    _ ≤ K' / μ₀ * (2 * K / c₁ ^ 2 + K) * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCnn

/-- Log-free **`trans`**: `ct_combined_trans` without the final `log c` factor. -/
theorem ct_combined_trans_sharp : ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ →
    CtDyadicBoundSharp c₁ fun R ε c f => ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f := by
  obtain ⟨K, cM, hK0, hmom⟩ := ct_boas_moments_top
  obtain ⟨κ₀, hκ₀, cL, hcL1, hL⟩ := ctLv0_facts
  obtain ⟨γ, hγ, hband⟩ := taperBand_pm
  obtain ⟨ρ, M, hρ, hM0, hwin⟩ := ct_window_pm
  refine ⟨min (min γ (1 / 200)) (min 1 (ρ / 16)), lt_min (lt_min hγ (by norm_num)) (lt_min one_pos (by positivity)),
    fun c₁ hc₁ hc₁le => ?_⟩
  have hc₁a : c₁ ≤ γ := (hc₁le.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hc₁b : c₁ ≤ 1 / 200 := (hc₁le.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hc₁c : c₁ ≤ 1 := (hc₁le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hc₁d : c₁ ≤ ρ / 16 := (hc₁le.trans (min_le_right _ _)).trans (min_le_right _ _)
  obtain ⟨cB, hcB3, hB⟩ := hband c₁ hc₁ hc₁a
  have hev : ∀ᶠ c : ℝ in atTop, cM ≤ c ∧ cL ≤ c ∧ cB ≤ c ∧ Real.exp 7 ≤ c ∧ 5000 ≤ c ∧
      (2 ≤ c ^ (4 / 7 : ℝ) ∧ c ^ (4 / 7 : ℝ) + 1 / 2 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ)) ∧
      c ^ (7 / 3 : ℝ) * Real.exp (-(1 / 40000 * c)) ≤ 1 := by
    filter_upwards [eventually_ge_atTop cM, eventually_ge_atTop cL, eventually_ge_atTop cB,
      eventually_ge_atTop (Real.exp 7), eventually_ge_atTop (5000 : ℝ), ev_hcR hc₁,
      eventually_rpow_mul_exp_le (7 / 3) (1 / 40000) (by norm_num)] with c h1 h2 h3 h4 h5 h6 h7
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hev
  refine ⟨174 * M ^ 2 * K / c₁ ^ 3 + 2 ^ 12 * (K + 1) / c₁ ^ 24 + 8 * |hankelTailI0| * c₁ ^ 2, c₀,
    fun c hc ε hε T f hf hm hT _hgap R hR _hgood => ?_⟩
  obtain ⟨hcM, hcL, hcB, hc7, hc5, ⟨hc47, hcR⟩, hexpo⟩ := hc₀ c hc
  have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 7) hc7
  have hc3 : 3 ≤ c := le_trans (by linarith [Real.add_one_le_exp (7 : ℝ)]) hc7
  have hf' := hf.toIsHankelEigenfn
  have hBR : TaperBand ε c R := hB c hcB ε hε R hR.1 hR.2
  have hI := hBR.inputs
  have hR0 : 0 < R := hI.R_pos
  have h23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hRhi : R ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) := by
    have : 4 * c₁ ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := by nlinarith
    nlinarith [hR.2]
  obtain ⟨hW, hU⟩ := hwin ε hε
  obtain ⟨LJ, Lt, -, hLJe, hLJv, -, hLt0, hLtLJ, -, -, -, -, hMom, -⟩ := hmom c ε T f hcM hf hε hm hT
  obtain ⟨hL0, hLe, hLv, -⟩ := hL c hcL
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc0 hf'
  have hmass1 : ∫ L, |hankelHL c f L| = 1 := by rw [integral_abs_hankelHL hc0 hf', hm]
  have hLJ0 : 0 ≤ LJ := hLt0.trans hLtLJ
  obtain ⟨hΛJ, -⟩ := boas_geometry hc0 hBR hLJ0 hLJe hLJv hRhi
  have hLΛ : ctLv0 c ≤ ctTaperLam ε c R := lmin_le_lam hc0 hBR hL0.le hLe hLv (hcR.trans hR.1)
  have hrR : ctRprime ε c R ≤ R := hBR.Rprime_le
  have hrA : ctRprime ε c R ≤ langerRadius c := by
    have hκ := hankelLangerKappa_bounds.1
    rw [langerRadius_eq]
    have : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ c ^ (2 / 3 : ℝ) * langerKappa * 4.94e-4 := by nlinarith
    linarith
  have hR1 : 1 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) := by linarith
  have hr0 : 0 < ctRprime ε c R := by have := hBR.Rprime_ge; linarith [hR.1]
  have hRρ : -ρ < ctMu c * (-R) := by
    have h2 : (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ 2 := by
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hμR : ctMu c * R ≤ 8 * c₁ ^ 2 := by
      unfold ctMu
      have e : c ^ (-(2 / 3) : ℝ) * c ^ (2 / 3 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; norm_num
      calc (2 : ℝ) ^ ((2 : ℝ) / 3) * c ^ (-(2 / 3) : ℝ) * R
          ≤ 2 * c ^ (-(2 / 3) : ℝ) * (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hc0.le _)) hR.2 hR0.le (by positivity)
        _ = 8 * c₁ ^ 2 * (c ^ (-(2 / 3) : ℝ) * c ^ (2 / 3 : ℝ)) := by ring
        _ = 8 * c₁ ^ 2 := by rw [e, mul_one]
    nlinarith [sq_nonneg c₁]
  have hdec := ct_trans_decomp (K := K) (LJ := LJ) hW hU hε hc5 hBR hf' hm hc₁ hR.1 hr0 hrA hRρ hL0 hLe hLv hLΛ hΛJ hLJe hK0 hMom
  have hrate := trans_rate_bound hc0 hc₁ hR.1 hR.2 hrR (hankelRinf_nonneg hc5 hf' hε hm) hexpo hM0 hK0 hc3
  have hη : 0 ≤ c⁻¹ * ctEta c₁ ε c f R :=
    mul_nonneg (inv_nonneg.2 hc0.le) (ctEta_nonneg c₁ ε c f hR0.le)
  have hCnn : 0 ≤ 174 * M ^ 2 * K / c₁ ^ 3 + 2 ^ 12 * (K + 1) / c₁ ^ 24 + 8 * |hankelTailI0| * c₁ ^ 2 := by positivity
  calc |ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f|
      ≤ 174 * (ctLam c * M) ^ 2 / (R * Real.sqrt R) * (K * c ^ (1 / 3 : ℝ)) +
        2 ^ 12 * (K + 1) / c₁ ^ 24 * c ^ (-(29 / 21) : ℝ) + ctRprime ε c R * hankelRinf c := hdec
    _ ≤ (174 * M ^ 2 * K / c₁ ^ 3 + 2 ^ 12 * (K + 1) / c₁ ^ 24 + 8 * |hankelTailI0| * c₁ ^ 2) * c ^ (-(4 / 3) : ℝ) := hrate
    _ ≤ (174 * M ^ 2 * K / c₁ ^ 3 + 2 ^ 12 * (K + 1) / c₁ ^ 24 + 8 * |hankelTailI0| * c₁ ^ 2) *
          (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)) :=
        mul_le_mul_of_nonneg_left (by linarith) hCnn

/-! ### Log-free chart gap `ctChartGap_sharp` -/

/-- Log-free **`chart_gap` for one sign, given `c₀^ε < 0`** (`ct:langer-inv` with `ct:five-term-node`
and `thm:hankel-one-two`): once `K ≥ K₀` (`K₀ = 4(|Cx| + |C5|) + 1`), `T ≤ Δ₅^ε(c) - K c⁻¹`
implies `T < c ξ(a₁)` and `(K β₁ / 2) c^{-4/3} ≤ ctGap ε c T`. -/
theorem ctChartGap_eps_sharp {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (hκ : ctKappa ε < 0) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {K : ℝ}, K₀ ≤ K → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
      ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
        T ≤ ctDelta5 ε c - K * c⁻¹ →
        T < c * hankelXi c (airyZero 1) ∧
          K * hankelBeta1 / 2 * c ^ (-(4 / 3) : ℝ) ≤ ctGap ε c T := by
  obtain ⟨Cx, hCx⟩ := hankelXi_expansion
  obtain ⟨C5, c5, hc5, hnode⟩ := ctNode_expansion hε
  obtain ⟨cq, hcq, hquant⟩ := hankel_quantC1_of_feasible
  set K₀ : ℝ := 4 * (|Cx| + |C5|) + 1 with hK₀_def
  refine ⟨K₀, by positivity, fun {K} hK_ge => ?_⟩
  have hK : 0 < K := lt_of_lt_of_le (by positivity) hK_ge
  have hβ := hankelBeta1_pos
  set q' : ℝ := 9 * π ^ 2 / (25 * hankelBeta1 ^ 2)
  have hq'0 : 0 ≤ q' := by positivity
  set Rk : ℝ := max 1 (12 * hankelBeta1 * q')
  set Rrem : ℝ := |(-airyZero 1 / hankelBeta1) * (CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε)|
  have hRrem0 : 0 ≤ Rrem := abs_nonneg _
  have hkap_pos : 0 < -ctKappa ε := neg_pos.2 hκ
  set c_gap : ℝ := max (max (max c5 cq) (max 3e6 (Rk ^ 3)))
    (max ((2 * (Rrem + |Cx|) / (-ctKappa ε) + 1) ^ 3) 1)
  refine ⟨c_gap, fun c hc T f hf hm hT => ?_⟩
  have hc5' : c5 ≤ c := (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hcq' : cq ≤ c := (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_left _ _)).trans hc
  have hc3e6 : 3e6 ≤ c := (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hc
  have hcRk : Rk ^ 3 ≤ c := (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)).trans hc
  have hcKap : (2 * (Rrem + |Cx|) / (-ctKappa ε) + 1) ^ 3 ≤ c :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith only [hc3e6]
  obtain ⟨h3, h1, h2, h4⟩ := rpow_third_facts hc0
  set k : ℝ := c ^ (1 / 3 : ℝ)
  have hk_pos : 0 < k := Real.rpow_pos_of_pos hc0 _
  have hk_ge_Rk : Rk ≤ k := by
    have hp := Real.rpow_le_rpow (by positivity) hcRk (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at hp
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk_ge_Rk
  have hka : 12 * hankelBeta1 * q' ≤ k := (le_max_right _ _).trans hk_ge_Rk
  have ha1_abs : |airyZero 1| ≤ 3 := by
    have := airyZero_one
    rw [abs_le]; constructor <;> linarith only [this.1, this.2]
  have hXa1 := hCx c hc3e6 (airyZero 1) ha1_abs
  have h_del_lt : ctDelta5 ε c < c * hankelXi c (airyZero 1) := by
    have hdiff : ctDelta5 ε c - ctChartX c (airyZero 1) = ctKappa ε +
        (-airyZero 1 / hankelBeta1) * (CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε) * (k⁻¹) ^ 2 := by
      rw [ctDelta5_eq_k hc0, ctChartX_eq_k hc0]
      unfold ctKappa
      ring
    have hk_kap : 2 * (Rrem + |Cx|) / (-ctKappa ε) + 1 ≤ k := by
      have hp := Real.rpow_le_rpow (by positivity) hcKap (by norm_num : (0 : ℝ) ≤ 1 / 3)
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        show ((3 : ℕ) : ℝ) * (1 / 3) = 1 by norm_num, Real.rpow_one] at hp
    have hinv_le1 : k⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk1
    have hrem_bd : (-airyZero 1 / hankelBeta1) * (CtOuter.ctTheta1 ε + 12 / π ^ 2 * CtOuter.ctTheta3 ε) * (k⁻¹) ^ 2 ≤ Rrem * k⁻¹ := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul, abs_pow, abs_of_pos (inv_pos.2 hk_pos)]
      calc Rrem * (k⁻¹) ^ 2 = Rrem * (k⁻¹ * k⁻¹) := by ring
        _ ≤ Rrem * (1 * k⁻¹) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hinv_le1 (inv_nonneg.2 hk_pos.le)) hRrem0
        _ = Rrem * k⁻¹ := by ring
    have hc_inv_le : c⁻¹ ≤ k⁻¹ := by
      rw [← h3, inv_le_inv₀ (by positivity) hk_pos]
      have : 1 ≤ k ^ 2 := one_le_pow₀ hk1
      nlinarith only [this, hk_pos]
    have hCx_bd : ctChartX c (airyZero 1) - c * hankelXi c (airyZero 1) ≤ |Cx| * k⁻¹ := by
      have := (abs_sub_comm (c * hankelXi c (airyZero 1)) (ctChartX c (airyZero 1))) ▸ hXa1
      calc ctChartX c (airyZero 1) - c * hankelXi c (airyZero 1)
          ≤ |ctChartX c (airyZero 1) - c * hankelXi c (airyZero 1)| := le_abs_self _
        _ ≤ Cx * c⁻¹ := this
        _ ≤ |Cx| * c⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self Cx) (inv_nonneg.2 hc0.le)
        _ ≤ |Cx| * k⁻¹ := mul_le_mul_of_nonneg_left hc_inv_le (abs_nonneg Cx)
    have hsmall : (Rrem + |Cx|) * k⁻¹ < -ctKappa ε := by
      have hk_gt : 2 * (Rrem + |Cx|) / (-ctKappa ε) < k := by linarith only [hk_kap]
      have h1 : (Rrem + |Cx|) * k⁻¹ ≤ (-ctKappa ε) / 2 := by
        rcases eq_or_lt_of_le (show 0 ≤ Rrem + |Cx| by positivity) with h0 | hpos
        · rw [← h0, zero_mul]; positivity
        · have : 2 * (Rrem + |Cx|) / (-ctKappa ε) ≤ k := hk_gt.le
          rw [div_le_iff₀ hkap_pos] at this
          rw [mul_comm, inv_mul_le_iff₀ hk_pos]
          linarith only [this]
      linarith only [h1, hkap_pos]
    linarith only [hdiff, hrem_bd, hCx_bd, hsmall]
  have hTc : T < c * hankelXi c (airyZero 1) := by
    have hKinv : 0 ≤ K * c⁻¹ := by positivity
    linarith only [hT, hKinv, h_del_lt]
  refine ⟨hTc, ?_⟩
  obtain ⟨u_T, ha1_uT, -, hxi_uT, hB2⟩ := hquant c ε T f hcq' hf hε hm hTc
  obtain ⟨hu0, hu3⟩ := hankelBoot_uT_range ha1_uT hB2
  have hxiT : hankelXi c u_T = T / c := by rw [eq_div_iff hc0.ne']; linarith [hxi_uT]
  have hexT : ∃ x ∈ Icc (-3 : ℝ) 0, hankelXi c x = T / c := ⟨u_T, ⟨hu3, hu0⟩, hxiT⟩
  have hu₁spec : ctUtilde c T ∈ Icc (-3 : ℝ) 0 ∧ hankelXi c (ctUtilde c T) = T / c := by
    unfold ctUtilde; exact Function.invFunOn_pos hexT
  set u₁ : ℝ := ctUtilde c T
  obtain ⟨⟨φ₀, hφ₀_mem, hφ₀_eq⟩, hnode_bd⟩ := hnode c hc5'
  have hexφ : ∃ x ∈ Icc (-3 : ℝ) (-2), ctUhat ε c x = airyZero 1 := ⟨φ₀, hφ₀_mem, hφ₀_eq⟩
  set φ : ℝ := Function.invFunOn (ctUhat ε c) (Icc (-3 : ℝ) (-2)) (airyZero 1)
  have hφspec : φ ∈ Icc (-3 : ℝ) (-2) ∧ ctUhat ε c φ = airyZero 1 := Function.invFunOn_pos hexφ
  have hgap_eq : ctGap ε c T = u₁ - φ := rfl
  rw [hgap_eq]
  have hu₁_abs : |u₁| ≤ 3 := abs_le.2 ⟨hu₁spec.1.1, by linarith [hu₁spec.1.2]⟩
  have hXu₁ := hCx c hc3e6 u₁ hu₁_abs
  have hCu₁ : ctChartX c u₁ - T ≤ |Cx| * c⁻¹ := by
    have hT_eq : T = c * hankelXi c u₁ := by rw [hu₁spec.2, mul_div_cancel₀ _ hc0.ne']
    rw [hT_eq]
    have h1 := (abs_sub_comm (c * hankelXi c u₁) (ctChartX c u₁)) ▸ hXu₁
    exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self Cx) (inv_nonneg.2 hc0.le)))
  have hφ_bd : ctDelta5 ε c - ctChartX c φ ≤ |C5| * c⁻¹ := by
    have h1 := hnode_bd φ hφspec.1 hφspec.2
    rw [abs_sub_comm] at h1
    exact (le_abs_self _).trans (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C5) (inv_nonneg.2 hc0.le)))
  have h_sub_le : ctChartX c u₁ - ctChartX c φ ≤ -(3 / 4 * K * ((k⁻¹) ^ 3 * 1)) := by
    have hinv3 : (k⁻¹) ^ 3 * 1 = c⁻¹ := by rw [mul_one, inv_pow, h3]
    rw [hinv3]
    have hKC : |Cx| + |C5| - K ≤ -(3 / 4 * K) := by linarith only [hK_ge, hK₀_def]
    calc ctChartX c u₁ - ctChartX c φ
        = (ctChartX c u₁ - T) + (T - ctDelta5 ε c) + (ctDelta5 ε c - ctChartX c φ) := by ring
      _ ≤ |Cx| * c⁻¹ + (-K * c⁻¹) + |C5| * c⁻¹ := by linarith only [hCu₁, hT, hφ_bd]
      _ = (|Cx| + |C5| - K) * c⁻¹ := by ring
      _ ≤ -(3 / 4 * K) * c⁻¹ := mul_le_mul_of_nonneg_right hKC (inv_nonneg.2 hc0.le)
      _ = -(3 / 4 * K * c⁻¹) := by ring
  rw [ctChartX_sub hc0] at h_sub_le
  have hgap_chain := gap_from_chain hk1 hβ hq'0 hka hK zero_le_one hu₁spec.1 hφspec.1 h_sub_le
  have hc43_eq : (k⁻¹) ^ 3 * k⁻¹ * 1 = c ^ (-(4 / 3) : ℝ) := by rw [h4]; ring
  rw [hc43_eq] at hgap_chain
  exact hgap_chain

/-- Log-free **`chart_gap`** for both signs `ε = ±1`. -/
theorem ctChartGap_sharp (hκ : ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ctKappa ε < 0) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ {K : ℝ}, K₀ ≤ K → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c →
      ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ (T : ℝ) (f : ℝ → ℝ),
        IsHankelFeasible c ε T f → hankelMass c f = 1 →
        T ≤ ctDelta5 ε c - K * c⁻¹ →
        T < c * hankelXi c (airyZero 1) ∧
          K * hankelBeta1 / 2 * c ^ (-(4 / 3) : ℝ) ≤ ctGap ε c T := by
  obtain ⟨K₁, hK₁, H₁⟩ := ctChartGap_eps_sharp (Or.inl rfl) (hκ 1 (Or.inl rfl))
  obtain ⟨K₂, hK₂, H₂⟩ := ctChartGap_eps_sharp (Or.inr rfl) (hκ (-1) (Or.inr rfl))
  refine ⟨max K₁ K₂, lt_max_of_lt_left hK₁, fun {K} hK => ?_⟩
  obtain ⟨c₁, hc₁⟩ := H₁ ((le_max_left K₁ K₂).trans hK)
  obtain ⟨c₂, hc₂⟩ := H₂ ((le_max_right K₁ K₂).trans hK)
  refine ⟨max c₁ c₂, fun c hc ε hε T f hf hm hT => ?_⟩
  rcases hε with rfl | rfl
  · exact hc₁ c ((le_max_left _ _).trans hc) T f hf hm hT
  · exact hc₂ c ((le_max_right _ _).trans hc) T f hf hm hT

/-! ### Log-free reduction from `(window_signed, boas_sharp)` to `CtLowerLogFreeStatement` -/

/-- Log-free `ct_pass`: combines `ct_dyadic_radius_proved`, `CtDyadicCombinedSharpStatement`,
and `CtBoasSharpStatement` to get `ctBudget R ε c f ≤ C₀ c^{-4/3}` at some good radius `R`. -/
theorem ct_pass_logfree {c₁ : ℝ} (hr : CtDyadicRadiusStatement c₁)
    (hd : CtDyadicCombinedSharpStatement c₁) (hb : CtBoasSharpStatement c₁) :
    CtPassLogFreeStatement c₁ := by
  obtain ⟨Cη, c₀r, hr_bd⟩ := hr
  obtain ⟨Cd, c₀d, hd_bd⟩ := hd
  obtain ⟨Cb, c₀b, hb_bd⟩ := hb
  refine ⟨max 0 Cd * (max 0 Cη + 1) + max 0 Cb, max (max c₀r c₀d) (max c₀b 1), ?_⟩
  intro c hc ε hε T f hf hm hT hgap
  have hcr : c₀r ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcd : c₀d ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcb : c₀b ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
  have hc1 : 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
  have hc0 : 0 < c := by linarith only [hc1]
  obtain ⟨R, hR, hgood, hη⟩ := hr_bd c hcr ε hε T f hf hm hT hgap
  have hdR := hd_bd c hcd ε hε T f hf hm hT hgap R hR hgood
  have hbR := hb_bd c hcb ε hε T f hf hm hT hgap R hR hgood
  set I : ℝ := ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)
  have hd_le : ctBudget R ε c f + I ≤ Cd * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)) :=
    (le_abs_self _).trans hdR
  have hc43 : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hη_mul : c⁻¹ * ctEta c₁ ε c f R ≤ Cη * c ^ (-(4 / 3) : ℝ) := by
    have hcm : c⁻¹ * c ^ (-(1 / 3) : ℝ) = c ^ (-(4 / 3) : ℝ) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
    calc c⁻¹ * ctEta c₁ ε c f R ≤ c⁻¹ * (Cη * c ^ (-(1 / 3) : ℝ)) :=
          mul_le_mul_of_nonneg_left hη (inv_nonneg.2 hc0.le)
      _ = Cη * (c⁻¹ * c ^ (-(1 / 3) : ℝ)) := by ring
      _ = Cη * c ^ (-(4 / 3) : ℝ) := by rw [hcm]
  have h_sum_η : c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) ≤ (max 0 Cη + 1) * c ^ (-(4 / 3) : ℝ) := by
    have hCη : Cη ≤ max 0 Cη := le_max_right _ _
    nlinarith only [hη_mul, hc43, hCη]
  have hη_nn : 0 ≤ c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) := by
    have hR0 : 0 ≤ R := by linarith only [hR.1, show 0 ≤ c₁ ^ 2 * c ^ (2 / 3 : ℝ) by positivity]
    have hη_nn' := ctEta_nonneg c₁ ε c f hR0
    positivity
  have hCd_le : Cd * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ)) ≤
      max 0 Cd * ((max 0 Cη + 1) * c ^ (-(4 / 3) : ℝ)) :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hη_nn).trans
      (mul_le_mul_of_nonneg_left h_sum_η (le_max_left _ _))
  have hCb_le : -(I) ≤ max 0 Cb * c ^ (-(4 / 3) : ℝ) := by
    have h1 : -(I) ≤ Cb * c ^ (-(4 / 3) : ℝ) := by linarith only [hbR]
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hc43.le)
  refine ⟨R, hR, ?_⟩
  nlinarith only [hd_le, hCd_le, hCb_le]

/-- Log-free **`ct_lower_of_pass_node`**: derives `Δ₅^ε(c) - C c⁻¹ ≤ T` from
`CtPassLogFreeStatement c₁` and `CtNodeLowerStatement c₁` (which is already log-free!). -/
theorem ct_lower_of_pass_node_logfree {c₁ : ℝ} (hP : CtPassLogFreeStatement c₁)
    (hN : CtNodeLowerStatement c₁) : CtLowerLogFreeStatement := by
  obtain ⟨C₀, c₂, h2⟩ := hP
  obtain ⟨κ, κ', C', c₃, hκ, hκ', h3⟩ := hN
  obtain ⟨K₀, hK₀, hgap_all⟩ := ctChartGap_sharp (fun _ hε => ctKappa_neg hε)
  set M : ℝ := max C₀ 0 + 2 with hM
  have hM0 : 0 < M := by positivity
  have hβ := hankelBeta1_pos
  set K : ℝ := max K₀ (2 * M / (κ * hankelBeta1)) with hK_def
  have hKpos : 0 < K := lt_of_lt_of_le hK₀ (le_max_left _ _)
  have hK_ge : K₀ ≤ K := le_max_left _ _
  have hK_bd : 2 * M / (κ * hankelBeta1) ≤ K := le_max_right _ _
  obtain ⟨c₄, h4⟩ := hgap_all hK_ge
  have hC'_ge1 : 0 < max C' 1 := by positivity
  have hlog_bd : ∀ᶠ c : ℝ in atTop,
      max 1 (max c₂ (max c₃ c₄)) ≤ c ∧
      c ^ (4 / 3 : ℝ) * Real.exp (-(κ' / 2 * c)) ≤ 1 ∧
      Real.log (max C' 1) * (2 / κ') ≤ c := by
    refine Filter.Eventually.and (eventually_ge_atTop _) (Filter.Eventually.and ?_ (eventually_ge_atTop _))
    exact eventually_rpow_mul_exp_le (4 / 3 : ℝ) (κ' / 2) (half_pos hκ')
  obtain ⟨c₀, hc₀⟩ := eventually_atTop.1 hlog_bd
  refine ⟨c₀, K, fun c hc ε hε T f hfeas => ?_⟩
  obtain ⟨hcmax, hexp1, hclog⟩ := hc₀ c hc
  have hc1 : 1 ≤ c := (le_max_left _ _).trans hcmax
  have hc₂ : c₂ ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hcmax
  have hc₃ : c₃ ≤ c := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hcmax
  have hc₄ : c₄ ≤ c := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hcmax
  have hc0 : 0 < c := by linarith only [hc1]
  have hC'_exp : C' * Real.exp (-κ' * c) ≤ c ^ (-(4 / 3) : ℝ) := by
    have hexp2 : Real.exp (-(κ' / 2 * c)) ≤ (max C' 1)⁻¹ := by
      have h1 : Real.log (max C' 1) ≤ κ' / 2 * c := by
        rw [← div_le_iff₀' (half_pos hκ')]
        exact hclog.trans_eq' (by ring)
      have h2 : max C' 1 ≤ Real.exp (κ' / 2 * c) := by
        simpa [Real.exp_log hC'_ge1] using Real.exp_le_exp.mpr h1
      rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hC'_ge1]
      exact h2
    have hmul : (c ^ (4 / 3 : ℝ) * Real.exp (-(κ' / 2 * c))) * Real.exp (-(κ' / 2 * c)) ≤ 1 * (max C' 1)⁻¹ :=
      mul_le_mul hexp1 hexp2 (Real.exp_pos _).le zero_le_one
    have hexp_eq : Real.exp (-(κ' / 2 * c)) * Real.exp (-(κ' / 2 * c)) = Real.exp (-κ' * c) := by
      rw [← Real.exp_add]; congr 1; ring
    have hc43 : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
    have hinv43 : c ^ (-(4 / 3) : ℝ) = (c ^ (4 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le _
    have hcomb : max C' 1 * Real.exp (-κ' * c) ≤ c ^ (-(4 / 3) : ℝ) := by
      rw [hinv43, inv_eq_one_div, le_div_iff₀' hc43]
      have : max C' 1 * (c ^ (4 / 3 : ℝ) * Real.exp (-κ' * c)) ≤ max C' 1 * (max C' 1)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ hC'_ge1.le
        calc c ^ (4 / 3 : ℝ) * Real.exp (-κ' * c)
            = (c ^ (4 / 3 : ℝ) * Real.exp (-(κ' / 2 * c))) * Real.exp (-(κ' / 2 * c)) := by
                rw [← hexp_eq]; ring
          _ ≤ 1 * (max C' 1)⁻¹ := hmul
          _ = (max C' 1)⁻¹ := one_mul _
      calc c ^ (4 / 3 : ℝ) * (max C' 1 * Real.exp (-κ' * c))
          = max C' 1 * (c ^ (4 / 3 : ℝ) * Real.exp (-κ' * c)) := by ring
        _ ≤ max C' 1 * (max C' 1)⁻¹ := this
        _ = 1 := mul_inv_cancel₀ hC'_ge1.ne'
    have hC_le : C' ≤ max C' 1 := le_max_left _ _
    exact (mul_le_mul_of_nonneg_right hC_le (Real.exp_pos _).le).trans hcomb
  by_contra hlt
  push Not at hlt
  obtain ⟨g, hg_feas, hg_mass⟩ := hankel_feasible_normalize hc0 hfeas
  obtain ⟨hT, hgap_lb⟩ := h4 c hc₄ ε hε T g hg_feas hg_mass hlt.le
  have hgap_pos : 0 < ctGap ε c T := lt_of_lt_of_le (by positivity) hgap_lb
  obtain ⟨R, hR, hB_ub⟩ := h2 c hc₂ ε hε T g hg_feas hg_mass hT hgap_pos
  have hN_lb := h3 c hc₃ ε hε T g hg_feas hg_mass hT hgap_pos R hR
  have hc43 : 0 < c ^ (-(4 / 3) : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hM_lb : M * c ^ (-(4 / 3) : ℝ) ≤ κ * ctGap ε c T := by
    have h1 : M ≤ κ * (K * hankelBeta1 / 2) := by
      rw [div_le_iff₀ (by positivity)] at hK_bd
      nlinarith only [hK_bd, hκ, hβ]
    calc M * c ^ (-(4 / 3) : ℝ) ≤ κ * (K * hankelBeta1 / 2) * c ^ (-(4 / 3) : ℝ) :=
          mul_le_mul_of_nonneg_right h1 hc43.le
      _ = κ * (K * hankelBeta1 / 2 * c ^ (-(4 / 3) : ℝ)) := by ring
      _ ≤ κ * ctGap ε c T := mul_le_mul_of_nonneg_left hgap_lb hκ.le
  have h_contra : M * c ^ (-(4 / 3) : ℝ) ≤ (C₀ + 1) * c ^ (-(4 / 3) : ℝ) := by
    calc M * c ^ (-(4 / 3) : ℝ) ≤ κ * ctGap ε c T := hM_lb
      _ ≤ ctBudget R ε c g + C' * Real.exp (-κ' * c) := hN_lb
      _ ≤ C₀ * c ^ (-(4 / 3) : ℝ) + c ^ (-(4 / 3) : ℝ) := add_le_add hB_ub hC'_exp
      _ = (C₀ + 1) * c ^ (-(4 / 3) : ℝ) := by ring
  have hM_le : M ≤ C₀ + 1 := le_of_mul_le_mul_right h_contra hc43
  linarith only [hM, hM_le, le_max_left C₀ (0 : ℝ)]

/-- Log-free **`ct_lower_of_boas`**: proves `CtLowerLogFreeStatement` from log-free
`CtDyadicCombinedSharpStatement` and `CtBoasSharpStatement`. -/
theorem ct_lower_of_boas_logfree
    (D : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtDyadicCombinedSharpStatement c₁)
    (B : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtBoasSharpStatement c₁) :
    CtLowerLogFreeStatement := by
  obtain ⟨a₁, ha₁, hd⟩ := D
  obtain ⟨a₂, ha₂, hb⟩ := B
  obtain ⟨a₃, ha₃, hn⟩ := ct_node_lower
  obtain ⟨a₄, ha₄, hr⟩ := ct_dyadic_radius_proved
  set c₁ : ℝ := min a₁ (min a₂ (min a₃ a₄))
  have hpos : 0 < c₁ := lt_min ha₁ (lt_min ha₂ (lt_min ha₃ ha₄))
  exact ct_lower_of_pass_node_logfree
    (ct_pass_logfree (hr c₁ hpos (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
      (hd c₁ hpos (min_le_left _ _))
      (hb c₁ hpos (le_trans (min_le_right _ _) (min_le_left _ _))))
    (hn c₁ hpos (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))

/-- info: 'FormalResearch.SignUncertainty.ctChartGap_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctChartGap_sharp

/-- info: 'FormalResearch.SignUncertainty.ct_lower_of_boas_logfree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower_of_boas_logfree

end FormalResearch.SignUncertainty
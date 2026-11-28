module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLower
public import FormalResearch.SignUncertainty.CtDyadicRegime
public import FormalResearch.SignUncertainty.CtBoasMeasurable
public import FormalResearch.SignUncertainty.CtBoasHhatHol
public import FormalResearch.SignUncertainty.CtDualLim
public import FormalResearch.SignUncertainty.CtChartPsiAnalytic

/-!
# `ct:dyadic` (4), `(ct:combined)`: concrete integrals and exact kernel splitting

`constant_terms_lower.tex`, `ct:dyadic` (4) (objects of `(ct:combined)`). Notation (all concrete): `h = hankelHL`
(`dm = h dL`, `ξ = e^L/π²`), `w̃ = ctTaper`, `Λ = ctTaperLam = L(ξ(-R'))`, `X = boasX`, `K = dualK` (`K_ε(ξ;c)`),
`s₁ = ∫_0^R f_c(-v) sin(4/3 v^{3/2}) dv` (`ctOscS1`), `s₂ = ∫_0^R w_R(v) f_c(-v) sin(4/3 v^{3/2}) dv` (`ctOscS2`),
`M_all = ∫ w̃ h` (`ctMall`), `M_tr = ∫_{L ≥ L(ξ(-v₀))} w̃ h`, `S_tr = ∫_{L ≥ L(ξ(-v₀))} w̃ h sin X`, `K_in = ∫_{L ≤ Λ} K h`, `K_out = ∫_{L > Λ} K h`,
`S_out = ∫_{L > Λ} h sin X`.

Provides the log-variable change of variables `integral_logvar`/`integrable_logvar`, exact Cauchy duality `ctKin_add_ctKout`,
taper bundle `taperBand_pm`, and kernel split `ctKernel_split`, consumed by `CtLowerLogFreeSkeleton` (`ct_dyadicCombined_sharp_of_bounds`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### The concrete quantities -/

/-- **The chart constant of `s₁`**: `min(c₁₀, 1/900)`, `c₁₀` the constant of `ct_chart_complex` (so `CtChartComplex c₁` holds for every `0 < c₁ ≤ ctChartC1`).  It only
fixes which of the (pairwise agreeing, `ctPhiC_agree`) complex charts `φ_c` defines `ctOscS1`: all that matters is `R ≤ 4c₁²c^{2/3} < R_max(ctChartC1)`. -/
noncomputable def ctChartC1 : ℝ := min (Classical.choose ct_chart_complex) (1 / 900)

lemma ctChartC1_pos : 0 < ctChartC1 :=
  lt_min (Classical.choose_spec ct_chart_complex).1 (by norm_num)

lemma ctChartC1_le : ctChartC1 ≤ 1 / 900 := min_le_right _ _

lemma ctChartComplex_ctChartC1 : CtChartComplex ctChartC1 :=
  (Classical.choose_spec ct_chart_complex).2 _ ctChartC1_pos (min_le_left _ _)

/-- `s₁ = ∫_0^R f_c(-v) sin(4/3 v^{3/2}) dv` (`ct:dyadic` (3)-(4); the integral bounded by `η_R` through Cauchy's theorem on the half-disc, `ct:dyadic` (4) (iv)),
`f_c = Ψ̃(φ_c)φ_c'` with the complex chart `φ_c` (`ctFcC`, `ctChartC1`), real on `ℝ`; the integral runs over the whole interval `v ∈ (0, R)`, including the
edge strip `ũ ∈ (0, ũ₀)` where the real chart `ctPhi` is a junk value. -/
noncomputable def ctOscS1 (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ v in Ioo 0 R, (ctFcC ctChartC1 ε c f (-(v : ℂ))).re * Real.sin (4 / 3 * v ^ (3 / 2 : ℝ))

/-- `s₂ = ∫_0^R w_R(v) f_c(-v) sin(4/3 v^{3/2}) dv`, `w_R = 2(v/R)^{12} - (v/R)^{24}` (`taperW`), in the Langer variable as `ctOscS1`
(`v = -û(x)`, `f_c(-v) dv = Ψ̃(x) dx`, `x ∈ (-R', 0)`). -/
noncomputable def ctOscS2 (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioo (-(ctRprime ε c R)) 0,
    taperW R (-ctUhat ε c x) * (hankelPsiR c f x * Real.sin (4 / 3 * (-ctUhat ε c x) ^ (3 / 2 : ℝ)))

/-- `M_all = ∫ w̃_R dm` over the whole line (`w̃ = 0` for `L ≤ 0`, i.e. `ξ ≤ ξ(0)`). -/
noncomputable def ctMall (R ε c : ℝ) (f : ℝ → ℝ) : ℝ := ∫ L, ctTaper ε c R L * hankelHL c f L

/-- `M_tr = ∫_{ξ ≥ ξ(-v₀)} w̃_R dm`. -/
noncomputable def ctMtr (R ε c : ℝ) (f : ℝ → ℝ) : ℝ := ∫ L in Ici (ctLv0 c), ctTaper ε c R L * hankelHL c f L

/-- `S_tr = ∫_{ξ ≥ ξ(-v₀)} w̃_R sin X dm`. -/
noncomputable def ctStr (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))

/-- `K_in = ∫_{ξ ≤ ξ(-R')} K_ε dm` (`Λ = L(ξ(-R'))`). -/
noncomputable def ctKin (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ L in Iic (ctTaperLam ε c R), CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L

/-- `K_out = ∫_{ξ > ξ(-R')} K_ε dm`. -/
noncomputable def ctKout (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ L in Ioi (ctTaperLam ε c R), CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L

/-- `S_out = ∫_{ξ > ξ(-R')} sin X dm`. -/
noncomputable def ctSout (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ L in Ioi (ctTaperLam ε c R), hankelHL c f L * Real.sin (boasX c ε L)

/-! ### The exact duality in the variable `L` -/

/-- The substitution `ξ = e^L/π²` for `dm`: `∫_ℝ F(ξ(L)) h(L) dL = ∫_{ξ>0} F(ξ) dm(ξ)` (`dm = c (fρ₀)(cξ) dξ`, `h = ξ · dm/dξ`). -/
lemma integral_logvar (c : ℝ) (f F : ℝ → ℝ) :
    ∫ L, F (Real.exp L / π ^ 2) * hankelHL c f L = ∫ ξ in Ioi (0 : ℝ), F ξ * hankelDmDens c f ξ := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set ψ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hψ
  have himg : ψ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hψ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt ψ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn ψ univ := by
    intro a _ b _ hab
    simp only [hψ] at hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 hab)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hd hinj
    (fun ξ => F ξ * hankelDmDens c f ξ)
  rw [himg, setIntegral_univ] at key
  rw [key]
  refine integral_congr_ae (ae_of_all _ fun L => ?_)
  have hp : 0 < Real.exp L / π ^ 2 := by positivity
  simp only [smul_eq_mul, hψ, abs_of_pos hp, hankelHL, hankelDmDens]
  ring

/-- Integrability transfers along the same substitution. -/
lemma integrable_logvar (c : ℝ) (f F : ℝ → ℝ) :
    Integrable (fun L => F (Real.exp L / π ^ 2) * hankelHL c f L) ↔
      IntegrableOn (fun ξ => F ξ * hankelDmDens c f ξ) (Ioi (0 : ℝ)) := by
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  set ψ : ℝ → ℝ := fun L => Real.exp L / π ^ 2 with hψ
  have himg : ψ '' univ = Ioi 0 := by
    ext ξ
    simp only [mem_image, mem_univ, true_and, mem_Ioi, hψ]
    constructor
    · rintro ⟨L, rfl⟩; positivity
    · intro hξ
      refine ⟨Real.log (π ^ 2 * ξ), ?_⟩
      rw [Real.exp_log (by positivity)]; field_simp
  have hd : ∀ L ∈ (univ : Set ℝ), HasDerivWithinAt ψ (Real.exp L / π ^ 2) univ L :=
    fun L _ => ((Real.hasDerivAt_exp L).div_const _).hasDerivWithinAt
  have hinj : InjOn ψ univ := by
    intro a _ b _ hab
    simp only [hψ] at hab
    exact Real.exp_injective ((div_left_inj₀ hpi.ne').1 hab)
  have key := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hd hinj
    (fun ξ => F ξ * hankelDmDens c f ξ)
  rw [himg] at key
  rw [key, integrableOn_univ]
  refine integrable_congr (ae_of_all _ fun L => ?_)
  have hp : 0 < Real.exp L / π ^ 2 := by positivity
  simp only [smul_eq_mul, hψ, abs_of_pos hp, hankelHL, hankelDmDens]
  ring

/-- `K_ε(ξ(L)) h(L) ∈ L¹(dL)` (`ct:dual-id` (2): `|K_ε| ≤ K_b` and `h ∈ L¹`; measurability of `K_ε` comes from `ct_dual_id_part2`). -/
lemma integrable_dualK_hankelHL {c ε : ℝ} (hc : 2 ≤ c) (hε : ε = 1 ∨ ε = -1) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) :
    Integrable (fun L => CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) := by
  obtain ⟨Kb, -, H⟩ := CtDual.ct_dual_id_part2 hε
  exact (integrable_logvar c f (CtDual.dualK ε c)).2 ((H hc).2 hf).1

/-- **`ct:dual-id` (2) in the variable `L`**: for any split point `Λ`, `∫_{L ≤ Λ} K h + ∫_{L > Λ} K h = 0` (`c ≥ 2`, `f ∈ 𝒜_c^ε`). -/
theorem ctKin_add_ctKout {c ε : ℝ} (hc : 2 ≤ c) (hε : ε = 1 ∨ ε = -1) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (Λ : ℝ) :
    (∫ L in Iic Λ, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L) +
      ∫ L in Ioi Λ, CtDual.dualK ε c (Real.exp L / π ^ 2) * hankelHL c f L = 0 := by
  obtain ⟨Kb, -, H⟩ := CtDual.ct_dual_id_part2 hε
  have hh := (H hc).2 hf
  have hint := hh.1
  have h0 := hh.2
  have hI := integrable_dualK_hankelHL hc hε hf
  have := integral_add_compl (measurableSet_Iic (a := Λ)) hI
  rw [compl_Iic, integral_logvar c f (CtDual.dualK ε c)] at this
  rw [this]; exact h0

/-! ### The assembly -/

/-- `TaperBand` for both signs `ε = ±1` at once. -/
lemma taperBand_pm : ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → ∃ c₀ : ℝ, 3 ≤ c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
    ∀ ε : ℝ, (ε = 1 ∨ ε = -1) → ∀ R : ℝ, c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
      TaperBand ε c R := by
  obtain ⟨γ₁, hγ₁, h₁⟩ := taperBand_regime (ε := 1) (Or.inl rfl)
  obtain ⟨γ₂, hγ₂, h₂⟩ := taperBand_regime (ε := -1) (Or.inr rfl)
  refine ⟨min γ₁ γ₂, lt_min hγ₁ hγ₂, fun c₁ hc₁ hγ => ?_⟩
  obtain ⟨a, ha3, ha⟩ := h₁ c₁ hc₁ (hγ.trans (min_le_left _ _))
  obtain ⟨b, hb3, hb⟩ := h₂ c₁ hc₁ (hγ.trans (min_le_right _ _))
  refine ⟨max a b, ha3.trans (le_max_left _ _), fun c hc ε hε R h1 h2 => ?_⟩
  rcases hε with rfl | rfl
  · exact ha c ((le_max_left _ _).trans hc) R h1 h2
  · exact hb c ((le_max_right _ _).trans hc) R h1 h2

/-- `w̃ h ∈ L¹` (`h ∈ L¹`, `0 ≤ w̃ ≤ 1` measurable). -/
lemma integrable_ctTaper_mul {ε c R : ℝ} {f : ℝ → ℝ} (hc : 0 < c) (hB : TaperBand ε c R) (hf : IsHankelEigenfn c ε f) :
    Integrable (fun L => ctTaper ε c R L * hankelHL c f L) := by
  have hI := hB.inputs
  refine (integrable_hankelHL hc hf).bdd_mul (c := 1) (measurable_ctTaper hI).aestronglyMeasurable
    (Eventually.of_forall fun L => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hI.reg.mem L).1]; exact (hI.reg.mem L).2

/-- The kernel integral of `(ct:combined)` splits as `M_tr - 2 S_tr` (integrability: `h ∈ L¹`, `0 ≤ w̃ ≤ 1` measurable, `sin` bounded). -/
lemma ctKernel_split {ε c R : ℝ} {f : ℝ → ℝ} (hc : 0 < c) (hB : TaperBand ε c R) (hf : IsHankelEigenfn c ε f) :
    (∫ L in Ici (ctLv0 c), ctTaper ε c R L * (hankelHL c f L * boasKernel (boasX c ε) L)) =
      ctMtr R ε c f - 2 * ctStr R ε c f := by
  have hI := hB.inputs
  have hh : Integrable (hankelHL c f) := integrable_hankelHL hc hf
  have hw : Measurable (ctTaper ε c R) := measurable_ctTaper hI
  have hX : Measurable (boasX c ε) := measurable_boasX c ε
  have h1 := integrable_ctTaper_mul hc hB hf
  have h2 : Integrable (fun L => ctTaper ε c R L * (hankelHL c f L * Real.sin (boasX c ε L))) := by
    have : Integrable (fun L => (ctTaper ε c R L * Real.sin (boasX c ε L)) * hankelHL c f L) := by
      refine hh.bdd_mul (c := 1) (hw.mul (Real.measurable_sin.comp hX)).aestronglyMeasurable (Eventually.of_forall fun L => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hI.reg.mem L).1]
      calc ctTaper ε c R L * |Real.sin (boasX c ε L)| ≤ 1 * 1 :=
            mul_le_mul (hI.reg.mem L).2 (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    refine this.congr (Eventually.of_forall fun L => ?_)
    simp only; ring
  unfold ctMtr ctStr
  rw [← integral_const_mul, ← integral_sub h1.integrableOn (h2.integrableOn.const_mul 2)]
  refine setIntegral_congr_fun measurableSet_Ici fun L _ => ?_
  simp only [boasKernel]; ring

/-- info: 'FormalResearch.SignUncertainty.ctKin_add_ctKout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctKin_add_ctKout

end FormalResearch.SignUncertainty

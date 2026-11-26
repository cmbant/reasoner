module

public import Mathlib
public import FormalResearch.SignUncertainty.CtLowerFinal
public import FormalResearch.SignUncertainty.CtDyadicRegime
public import FormalResearch.SignUncertainty.CtBoasMeasurable
public import FormalResearch.SignUncertainty.CtBoasHhatHol
public import FormalResearch.SignUncertainty.CtDualLim

/-!
# `ct:dyadic` (4), `(ct:combined)`: the assembly from the five steps of its proof

`constant_terms_lower.tex`, `ct:dyadic` (4) (proof of `(ct:combined)`).  The proof there has the following steps, each an estimate of
a concrete integral up to `O(c⁻¹η_R + c^{-4/3} log c)` at a good radius `R ∈ [c₁²c^{2/3}, 4c₁²c^{2/3}]`.  Notation (all concrete): `h = hankelHL`
(`dm = h dL`, `ξ = e^L/π²`), `w̃ = ctTaper`, `Λ = ctTaperLam = L(ξ(-R'))`, `X = boasX`, `K = dualK` (`K_ε(ξ;c)`),
`s₁ = ∫_0^R f_c(-v) sin(4/3 v^{3/2}) dv` (`ctOscS1`), `s₂ = ∫_0^R w_R(v) f_c(-v) sin(4/3 v^{3/2}) dv` (`ctOscS2`),
`M_all = ∫ w̃ h` (`ctMall`), `M_tr = ∫_{L ≥ L(ξ(-v₀))} w̃ h`, `S_tr = ∫_{L ≥ L(ξ(-v₀))} w̃ h sin X`, `K_in = ∫_{L ≤ Λ} K h`, `K_out = ∫_{L > Λ} K h`,
`S_out = ∫_{L > Λ} h sin X`.

* `rosc` (`CtCombinedPieces.rosc`): `P_R(H) + g_vac/2π + M_all + 2(s₁ - s₂) = O(c⁻¹η_R)`: `(ct:rosc)` (Part (3), the half-disc form of
  `ap:thmD` with `h₊² = (Ai + iBi)²`), the mass identity `∫_{-R}^R f_c = -g_vac/2π - ∫_{ξ>ξ(-R')} dm` (`gt:7.7p` (c), `gt:7.7c` (c)), the lobe piece
  and the transport `|f_c(-v) dv - dm| ≤ C r_∞ dv'` (`gt:7.7p` (b)): the displayed identity before "Now add twice `ct:dual-id`".
* `trunc`: `|M_all - M_tr| = O(c^{-29/21})` (`∫_{ξ(0)}^{ξ(-v₀)} w̃ |dm|`, from the first moment; the proved `boas_trunc_lo` with `𝔰_far = 0`).
* `window`: `K_in + s₁ = O(c⁻¹η_R + c^{-4/3} log c)`: the sub-chart bullet (radial compactness, `|K| ≤ K_b`) and the Airy-window bullet (`ct:cfu` (1) substituted,
  `(ct:H2-orth)`, the half moment `(ct:half)` for the CFU remainder, `|s₁| ≤ η_R`).
* `outer`: `K_out + S_out = O(c^{-4/3})` (`ct:cfu` (2) with `B₂(R') = O(c^{-1/3})`).
* `trans`: `S_tr - s₂ - S_out = O(c^{-4/3})` (`w̃ = 1` beyond `Λ`; the transition band: `(ct:theta-cfu-match)` and the first moment); proved in `CtTransBand` (`ct_combined_trans`) (the chart identification `ct_langer_edge` of `CtLangerEdgeChart` is proved).

`s₁`, `s₂` are written in the Langer variable `x = ũ ∈ (-R', 0)` (`v = -û(x)`, `f_c(-v)dv = Ψ̃(x)dx`), see `ctOscS1`.

Together with the proved exact duality `K_in + K_out = 0` (`ct:dual-id` (2), `ct_dual_id_part2`) they give `(ct:combined)`
(`ct_combined_of_pieces`): the left side is `e₁ - e_T - 2e_w - 2e_o - 2e_tr`, an exact linear combination.  The assembly is **proved**; the five
fields are the named inputs (`CtCombinedPieces`), the exact remaining gap of `thm:ct-lower`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### The concrete quantities -/

/-- `s₁ = ∫_0^R f_c(-v) sin(4/3 v^{3/2}) dv` (the integral bounded by `η_R` through Cauchy's theorem on the half-disc, `ct:dyadic` (4) (iv)),
written in the Langer variable: `v = -û(x)`, `f_c(-v) dv = Ψ̃(x) dx` (exact, `f_c = Ψ̃(φ_c) φ_c'`), `x ∈ (-R', 0)`, `R' = -φ_c(-R)`.  It omits the
sliver `v ∈ (0, -û(0⁻))` (`|û(0⁻)| = O(c^{-1/3})`), the lobe `ũ > 0` on which the Lean `ctPhi` (inverse of `û` on `u ≤ 0` only) is a junk
value; the paper's integral over it is `O(c^{-1/2} ∫|Ψ̃|_{ũ>0}) = O(e^{-κc})`. -/
noncomputable def ctOscS1 (R ε c : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioo (-(ctRprime ε c R)) 0, hankelPsiR c f x * Real.sin (4 / 3 * (-ctUhat ε c x) ^ (3 / 2 : ℝ))

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

/-- `|Q(R, ε, c, f)| ≤ C (c⁻¹ η_R + c^{-4/3} log c)` at every good radius of the window, under the hypotheses of `ct:dyadic`
(feasible `f`, `M[f] = 1`, violator `T < cξ(a₁)`, `ũ₁ > φ_c(a₁)`), uniformly in `c ≥ c₀`, `ε = ±1`, `f`. -/
def CtDyadicBound (c₁ : ℝ) (Q : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ) : Prop :=
  ∃ C c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∀ ε : ℝ, (ε = 1 ∨ ε = -1) →
    ∀ (T : ℝ) (f : ℝ → ℝ), IsHankelFeasible c ε T f → hankelMass c f = 1 →
      T < c * hankelXi c (FormalResearch.Special.airyZero 1) → 0 < ctGap ε c T →
      ∀ R : ℝ, R ∈ Icc (c₁ ^ 2 * c ^ (2 / 3 : ℝ)) (4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ)) → ctGoodRadius R →
        |Q R ε c f| ≤ C * (c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) * Real.log c)

/-- **The named inputs of `ct:dyadic` (4)**: the five estimates of the proof of `(ct:combined)` (see the module docstring), each about the
concrete objects of `thm:ct-lower`, each a step proved in the paper. -/
structure CtCombinedPieces (c₁ : ℝ) : Prop where
  /-- `(ct:rosc)` + mass identity + lobe + transport: `P_R(H) + g_vac/2π + ∫ w̃ dm = -2(s₁ - s₂) + O(c⁻¹η_R)`. -/
  rosc : CtDyadicBound c₁ fun R ε c f => ctBudget R ε c f + ctMall R ε c f + 2 * (ctOscS1 R ε c f - ctOscS2 R ε c f)
  /-- the taper estimate `∫_{ξ(0)}^{ξ(-v₀)} w̃ |dm| = O(c^{-29/21})`. -/
  trunc : CtDyadicBound c₁ fun R ε c f => ctMall R ε c f - ctMtr R ε c f
  /-- sub-chart and Airy window: `∫_{ξ ≤ ξ(-R')} K dm = -s₁ + O(c⁻¹η_R + c^{-4/3} log c)` (`ct:cfu` (1), `(ct:H2-orth)`, `(ct:half)`). -/
  window : CtDyadicBound c₁ fun R ε c f => ctKin R ε c f + ctOscS1 R ε c f
  /-- outer band: `∫_{ξ > ξ(-R')} K dm = -∫_{ξ > ξ(-R')} sin X dm + O(c^{-4/3})` (`ct:cfu` (2)). -/
  outer : CtDyadicBound c₁ fun R ε c f => ctKout R ε c f + ctSout R ε c f
  /-- transition band: `∫_{ξ ≥ ξ(-v₀)} w̃ sin X dm = s₂ + ∫_{ξ > ξ(-R')} sin X dm + O(c^{-4/3})`. -/
  trans : CtDyadicBound c₁ fun R ε c f => ctStr R ε c f - ctOscS2 R ε c f - ctSout R ε c f

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

/-- **`ct:dyadic` (4), `(ct:combined)`, from its five steps** (`CtCombinedPieces`) and the proved duality `ct_dual_id_part2`:
for `c₁` small, the named inputs give `CtDyadicInputs c₁`. -/
theorem ct_dyadicInputs_of_pieces :
    ∃ γ : ℝ, 0 < γ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ γ → CtCombinedPieces c₁ → CtDyadicInputs c₁ := by
  obtain ⟨γ, hγ, hB⟩ := taperBand_pm
  refine ⟨γ, hγ, fun c₁ hc₁ hc₁γ P => ⟨?_⟩⟩
  obtain ⟨cB, hcB3, hBand⟩ := hB c₁ hc₁ hc₁γ
  obtain ⟨C1, d1, H1⟩ := P.rosc
  obtain ⟨C2, d2, H2⟩ := P.trunc
  obtain ⟨C3, d3, H3⟩ := P.window
  obtain ⟨C4, d4, H4⟩ := P.outer
  obtain ⟨C5, d5, H5⟩ := P.trans
  refine ⟨|C1| + |C2| + 2 * |C3| + 2 * |C4| + 2 * |C5|,
    max cB (max d1 (max d2 (max d3 (max d4 d5)))), ?_⟩
  intro c hc ε hε T f hf hm hT hg R hR hgood
  simp only [max_le_iff] at hc
  obtain ⟨hcB, hc1, hc2, hc3, hc4, hc5⟩ := hc
  have hcpos : 0 < c := by linarith
  have hR0 : 0 ≤ R := le_trans (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hcpos.le _)) hR.1
  have hBR : TaperBand ε c R := hBand c hcB ε hε R hR.1 hR.2
  rw [ctKernel_split hcpos hBR hf.toIsHankelEigenfn]
  have hdual : ctKin R ε c f + ctKout R ε c f = 0 :=
    ctKin_add_ctKout (by linarith) hε hf.toIsHankelEigenfn _
  have e1 := H1 c hc1 ε hε T f hf hm hT hg R hR hgood
  have e2 := H2 c hc2 ε hε T f hf hm hT hg R hR hgood
  have e3 := H3 c hc3 ε hε T f hf hm hT hg R hR hgood
  have e4 := H4 c hc4 ε hε T f hf hm hT hg R hR hgood
  have e5 := H5 c hc5 ε hε T f hf hm hT hg R hR hgood
  set E : ℝ := c⁻¹ * ctEta c₁ ε c f R + c ^ (-(4 / 3) : ℝ) * Real.log c with hE
  have hlog : 0 ≤ Real.log c := Real.log_nonneg (by linarith)
  have hE0 : 0 ≤ E :=
    add_nonneg (mul_nonneg (inv_nonneg.2 hcpos.le) (ctEta_nonneg c₁ ε c f hR0))
      (mul_nonneg (Real.rpow_nonneg hcpos.le _) hlog)
  have mk : ∀ {C : ℝ} {Q : ℝ}, |Q| ≤ C * E → |Q| ≤ |C| * E := fun h =>
    h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hE0)
  have a1 := abs_le.1 (mk e1)
  have a2 := abs_le.1 (mk e2)
  have a3 := abs_le.1 (mk e3)
  have a4 := abs_le.1 (mk e4)
  have a5 := abs_le.1 (mk e5)
  rw [abs_le]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, a4.1, a4.2, a5.1, a5.2, hdual]

/-- **`thm:ct-lower` from the five steps of `ct:dyadic` (4)**: `ct_lower` with `CtLowerInputs.dyadic` replaced by `CtCombinedPieces` (the named
inputs `rosc`, `trunc`, `window`, `outer`, `trans`; see the module docstring for what each needs). -/
theorem ct_lower_of_pieces
    (P : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧ ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → CtCombinedPieces c₁) : CtLowerStatement := by
  obtain ⟨c₁₀, hc₁₀, hP⟩ := P
  obtain ⟨γ, hγ, H⟩ := ct_dyadicInputs_of_pieces
  exact ct_lower ⟨⟨min c₁₀ γ, lt_min hc₁₀ hγ, fun c₁ h1 h2 =>
    H c₁ h1 (h2.trans (min_le_right _ _)) (hP c₁ h1 (h2.trans (min_le_left _ _)))⟩⟩

/-- info: 'FormalResearch.SignUncertainty.ctKin_add_ctKout' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctKin_add_ctKout

/-- info: 'FormalResearch.SignUncertainty.ct_dyadicInputs_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_dyadicInputs_of_pieces

/-- info: 'FormalResearch.SignUncertainty.ct_lower_of_pieces' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_lower_of_pieces

end FormalResearch.SignUncertainty

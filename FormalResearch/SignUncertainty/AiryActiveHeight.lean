module

public import FormalResearch.SignUncertainty.CeCanonicalDefs
public import FormalResearch.SignUncertainty.CeCanonicalSide
public import FormalResearch.SignUncertainty.OneProfileEnvelope
public import FormalResearch.SignUncertainty.ShellGapOriginFloor

/-!
# Active Laplace heights, strictification, and deflation (`lem:airy-active-height`)

Source: `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex` (`lem:airy-shell-buffer`, lines 101–135;
`lem:airy-active-height`, lines 139–212) and `ce_shells.tex` (`lem:deflation-identity`, lines 290–312).

Main results:

* `laplaceL_analyticAt`, `laplaceL_eq_zero_of_eventuallyEq_zero`: for `H ∈ 𝒢` (`InAiryClass`),
  `y ↦ laplaceL (fun u => (H u).re) y` is real-analytic on `(0, ∞)` (`holomorphic_right`) and
  vanishes near some `y > 0` only when `H ≡ 0` (via `airyFtilde` analyticity on `{Im ζ > 0}` and
  Fourier–Airy inversion `airy_converse_ae`).
* `deflation_inAiryClass`, `deflation_identity`, `deflation_laplace_pos` (`lem:deflation-identity`):
  for `H ∈ 𝒢` and a real zero `z₀` of `H`, the quotient `Q = dslope H z₀` belongs to `𝒢`, satisfies
  `L_Q(y) = e^{z₀ y} (∫ Q + ∫_0^y e^{-z₀ s} L_H(s) ds)` for `y ≥ 0`, and has `L_Q(y) > 0` for all
  `y > 0` whenever `H ≢ 0`, `L_H ≥ 0` on `[0, ∞)`, and `∫ Q ≥ 0`.
* `exists_airy_shell_buffer` (`lem:airy-shell-buffer`): for every `D : ShellHBData` and `v₁ < D.tm`,
  there exists a positive-mass buffer `B ∈ 𝒢` strictly negative on `(-∞, v₁]` and on `shellSites D`
  with `L_B(0) > 0` and `L_B(y) > 0` for all `y ≥ Y_B` (`Y_B > 0`).
* `airy_active_height_strictify_buffer` and **`airy_active_height`** (`lem:airy-active-height` (1)–(4)):
  proves `AiryActiveHeight D` unconditionally (both the general buffer strictification of part (1)
  and the field type of `CeCanonicalDefs.AiryActiveHeight`), discharging the former `active_height`
  field of `CeCanonicalInputs`.

Not formalised: the generalised `(J, S)` form of `lem:airy-shell-buffer` (arbitrary node set `J` and
finite site set `S`; only `J = {1, …, m}`, `S = shellSites D` is proved) and the location clause
`L_B(y_*) ≤ 0` of part (2) for a prescribed buffer `B`; neither is used by `thm:ce-canonical-iff`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Real-analyticity and injectivity of `laplaceL` on `(0, ∞)` for `InAiryClass` -/

/-- Complex Laplace transform on `{w : ℂ | 0 < w.re}` of a real profile `g : ℝ → ℝ`. -/
private noncomputable def laplaceLC (g : ℝ → ℝ) (w : ℂ) : ℂ :=
  ∫ u : ℝ, ((g u : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))

private lemma laplaceLC_ofReal (g : ℝ → ℝ) (y : ℝ) :
    laplaceLC g (y : ℂ) = ((laplaceL g y : ℝ) : ℂ) := by
  unfold laplaceLC laplaceL
  have heq : (fun u : ℝ => ((g u : ℝ) : ℂ) * Complex.exp ((y : ℂ) * (u : ℂ))) =
      fun u : ℝ => ((g u * Real.exp (y * u) : ℝ) : ℂ) := by
    ext u
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  rw [heq]
  exact integral_ofReal

/-- For `H ∈ 𝒢`, `laplaceL (fun u => (H u).re)` is real-analytic at every `y > 0`. -/
theorem laplaceL_analyticAt {H : ℂ → ℂ} (hH : InAiryClass H) {y : ℝ} (hy : 0 < y) :
    AnalyticAt ℝ (laplaceL (fun u => (H (u : ℂ)).re)) y := by
  let g : ℝ → ℝ := fun u => (H (u : ℂ)).re
  have hDiff : DifferentiableOn ℂ (laplaceLC g) {w : ℂ | 0 < w.re} :=
    hH.to_polyLeftAiryRightBound.holomorphic_right
  have hisOpen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hAnC : AnalyticAt ℂ (laplaceLC g) (y : ℂ) :=
    (hDiff.analyticOnNhd hisOpen) (y : ℂ) (by simpa using hy)
  have hAnR : AnalyticAt ℝ (laplaceLC g) ((y : ℝ) : ℂ) := hAnC.restrictScalars (𝕜 := ℝ)
  have hcomp : AnalyticAt ℝ (fun t : ℝ => (laplaceLC g (t : ℂ)).re) y :=
    (Complex.reCLM.analyticAt _).comp (hAnR.comp (Complex.ofRealCLM.analyticAt y))
  have hfun : (fun t : ℝ => (laplaceLC g (t : ℂ)).re) = laplaceL g := by
    ext t; rw [laplaceLC_ofReal, Complex.ofReal_re]
  rwa [hfun] at hcomp

/-- If `H ∈ 𝒢` and `laplaceL (fun u => (H u).re)` vanishes in a neighbourhood of some `y₀ > 0`,
then `H = 0` identically on `ℂ`. -/
theorem laplaceL_eq_zero_of_eventuallyEq_zero {H : ℂ → ℂ} (hH : InAiryClass H) {y₀ : ℝ}
    (hy₀ : 0 < y₀) (hev : laplaceL (fun u => (H (u : ℂ)).re) =ᶠ[𝓝 y₀] 0) :
    ∀ z : ℂ, H z = 0 := by
  let g : ℝ → ℝ := fun u => (H (u : ℂ)).re
  -- Step 1: `laplaceL g = 0` on all `(0, ∞)` by real-analytic continuation.
  have hAn_Ioi : AnalyticOnNhd ℝ (laplaceL g) (Ioi 0) :=
    fun y hy => laplaceL_analyticAt hH hy
  have hfreq_y₀ : ∃ᶠ y in 𝓝[≠] y₀, laplaceL g y = 0 :=
    (eventually_nhdsWithin_of_eventually_nhds hev).frequently
  have hL_zero : ∀ y : ℝ, 0 < y → laplaceL g y = 0 := fun y hy =>
    hAn_Ioi.eqOn_zero_of_preconnected_of_frequently_eq_zero
      (convex_Ioi (0 : ℝ)).isPreconnected hy₀ hfreq_y₀ hy
  -- Step 2: Upgrade `H` to `AiryClassG H` and `AiryHinf (airyFtilde H) B` (`OneProfileEnvelope`).
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, hreal⟩ := hH
  have hG : AiryClassG H := by
    refine ⟨hd, hi, C, ⌈ν⌉₊, hC, fun z => (hb z).trans ?_⟩
    have h1 : (1 + ‖z‖) ^ ν ≤ (1 + ‖z‖) ^ (⌈ν⌉₊ : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) (Nat.le_ceil ν)
    rw [Real.rpow_natCast] at h1
    gcongr
    exact (airyEnv_pos z).le
  let B : ℝ := airyPhiK * ∫ x : ℝ, ‖H (x : ℂ)‖
  have hAH : AiryHinf (airyFtilde H) B :=
    ⟨airyFtilde_diffContOnCl hG, fun ζ hζ => airyFtilde_norm_le hG hζ⟩
  -- Step 3: `airyFtilde H (I * y) = 0` for all `y > 0`.
  have hFt_imag : ∀ y : ℝ, 0 < y → airyFtilde H (I * (y : ℂ)) = 0 := by
    intro y hy
    unfold airyFtilde airyFhat
    have hhat0 : (∫ u : ℝ, H (u : ℂ) * cexp (-(I * (I * (y : ℂ)) * (u : ℂ)))) = 0 := by
      have heq : (fun u : ℝ => H (u : ℂ) * cexp (-(I * (I * (y : ℂ)) * (u : ℂ)))) =
          fun u : ℝ => ((g u * Real.exp (y * u) : ℝ) : ℂ) := by
        ext u
        have hHu : H (u : ℂ) = ((g u : ℝ) : ℂ) := Complex.ext rfl (hreal u)
        have hexp : -(I * (I * (y : ℂ)) * (u : ℂ)) = ((y * u : ℝ) : ℂ) := by
          rw [← mul_assoc, I_mul_I]
          push_cast; ring
        rw [hHu, hexp, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
      rw [heq, integral_complex_ofReal]
      exact Complex.ofReal_eq_zero.mpr (hL_zero y hy)
    rw [hhat0, mul_zero]
  -- Step 4: Identity theorem on the open upper half-plane `{ζ : ℂ | 0 < ζ.im}`.
  let UHP : Set ℂ := {ζ : ℂ | 0 < ζ.im}
  have hUHP_open : IsOpen UHP := isOpen_lt continuous_const Complex.continuous_im
  have hUHP_conv : Convex ℝ UHP := by
    intro w₁ hw₁ w₂ hw₂ a b ha hb hab
    show 0 < (a • w₁ + b • w₂).im
    simp only [Complex.add_im, Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rcases ha.eq_or_lt with rfl | ha_pos
    · rw [zero_add] at hab; subst hab; simp [ (show 0 < w₂.im from hw₂) ]
    · have hb_nn : 0 ≤ b * w₂.im := mul_nonneg hb (le_of_lt hw₂)
      linarith [mul_pos ha_pos (show 0 < w₁.im from hw₁)]
  have hFt_an : AnalyticOnNhd ℂ (airyFtilde H) UHP :=
    hAH.diffContOnCl.differentiableOn.analyticOnNhd hUHP_open
  have hmap_I : Tendsto (fun y : ℝ => I * (y : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] I) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous (fun y : ℝ => I * (y : ℂ)) :=
        continuous_const.mul Complex.continuous_ofReal
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with y hy
      intro hIy
      have h1 : (y : ℂ) = 1 := mul_left_cancel₀ I_ne_zero (by simpa using hIy)
      exact hy (Complex.ofReal_injective h1)
  have hfreq_I : ∃ᶠ ζ in 𝓝[≠] I, airyFtilde H ζ = 0 := by
    refine hmap_I.frequently ?_
    refine Filter.Eventually.frequently ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (isOpen_Ioi.mem_nhds one_pos)] with y hy
    exact hFt_imag y hy
  have hFt_UHP : ∀ ζ ∈ UHP, airyFtilde H ζ = 0 := fun ζ hζ =>
    hFt_an.eqOn_zero_of_preconnected_of_frequently_eq_zero
      hUHP_conv.isPreconnected (by simp [UHP] : I ∈ UHP) hfreq_I hζ
  -- Step 5: `airyIeta (airyFtilde H) 1 = 0`, so `airy_converse_ae` forces `H = 0`.
  have hIeta0 : ∀ z : ℂ, airyIeta (airyFtilde H) 1 z = 0 := by
    intro z
    unfold airyIeta airyKE airyLam
    have h0 : ∀ ξ : ℝ, airyFtilde H ((ξ : ℂ) + I) = 0 := fun ξ =>
      hFt_UHP _ (by simp [UHP])
    simp [h0]
  have hae := airy_converse_ae hAH hi (fun _ => rfl)
  let f : ℂ → ℂ := fun z => ((2 * π : ℝ) : ℂ)⁻¹ * airyIeta (airyFtilde H) 1 z
  have hfd : Differentiable ℂ f := (differentiable_airyIeta hAH one_pos).const_mul _
  have hc1 : Continuous (fun x : ℝ => H (x : ℂ)) := hd.continuous.comp Complex.continuous_ofReal
  have hc2 : Continuous (fun x : ℝ => f (x : ℂ)) := hfd.continuous.comp Complex.continuous_ofReal
  have heq_f : (fun x : ℝ => f (x : ℂ)) = fun x : ℝ => H (x : ℂ) :=
    (Continuous.ae_eq_iff_eq volume hc2 hc1).mp hae
  have hreal0 : ∀ x : ℝ, H (x : ℂ) = 0 := by
    intro x
    have hx := (congrFun heq_f x).symm
    dsimp [f] at hx
    rw [hx, hIeta0, mul_zero]
  exact eq_of_eq_on_real hd (differentiable_const 0) hreal0

/-! ### Deflation identity (`lem:deflation-identity`, `ce_shells.tex`) -/

/-- Dividing `H ∈ 𝒢` by `z - z₀` at a real zero `z₀` keeps `Q = dslope H z₀` in `𝒢`, and
`u ↦ (H u).re / (u - z₀)` is integrable with integral `∫ (Q u).re`. -/
theorem deflation_inAiryClass {H : ℂ → ℂ} (hH : InAiryClass H) {z₀ : ℝ}
    (hz₀ : (H (z₀ : ℂ)).re = 0) :
    InAiryClass (dslope H (z₀ : ℂ)) ∧
    Integrable (fun u : ℝ => (H (u : ℂ)).re / (u - z₀)) ∧
    (∫ u : ℝ, (H (u : ℂ)).re / (u - z₀)) = ∫ u : ℝ, (dslope H (z₀ : ℂ) (u : ℂ)).re := by
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, hreal⟩ := hH
  have hHz₀ : H (z₀ : ℂ) = 0 := Complex.ext hz₀ (hreal z₀)
  let Q : ℂ → ℂ := dslope H (z₀ : ℂ)
  have hQd : Differentiable ℂ Q := EntireDiv.differentiable_dslope_entire hd (z₀ : ℂ)
  obtain ⟨ψ', hψ'd, hψ'eq, C'', hC'', hb''⟩ := at47_div_point hd z₀ hHz₀ hC hb
  have hQ_eq : ∀ z : ℂ, Q z = ψ' z := by
    have h0 := airy_entire_eq_zero_of_real_interval (hQd.sub hψ'd) (by linarith : z₀ + 1 < z₀ + 2)
      fun x hx1 _ => sub_eq_zero.mpr <| by
        have hne : (x : ℂ) - (z₀ : ℂ) ≠ 0 :=
          sub_ne_zero.mpr fun h => (by linarith : x ≠ z₀) (Complex.ofReal_injective h)
        have h1 := sub_smul_dslope H (z₀ : ℂ) (x : ℂ)
        rw [hHz₀, sub_zero, smul_eq_mul, mul_comm] at h1
        exact mul_right_cancel₀ hne (h1.trans (hψ'eq (x : ℂ)))
    exact fun z => sub_eq_zero.mp (h0 z)
  have hQ_env : ∀ z : ℂ, ‖Q z‖ ≤ C'' * (1 + ‖z‖) ^ ν * airyEnv z := by
    intro z; rw [hQ_eq z]; exact hb'' z
  have hQ_of_ne : ∀ u : ℝ, u ≠ z₀ → Q (u : ℂ) = (((H (u : ℂ)).re / (u - z₀) : ℝ) : ℂ) := by
    intro u hu
    have hne : (u : ℂ) ≠ (z₀ : ℂ) := fun h => hu (Complex.ofReal_injective h)
    dsimp [Q]
    rw [dslope_of_ne _ hne, slope_def_field, hHz₀, sub_zero]
    have hHu : H (u : ℂ) = (((H (u : ℂ)).re : ℝ) : ℂ) :=
      Complex.ext (by simp) (by simp [hreal u])
    conv_lhs => rw [hHu]
    rw [← Complex.ofReal_sub, ← Complex.ofReal_div]
  have hQ_real : ∀ u : ℝ, (Q (u : ℂ)).im = 0 := by
    have hcont : Continuous (fun u : ℝ => (Q (u : ℂ)).im) :=
      Complex.continuous_im.comp (hQd.continuous.comp Complex.continuous_ofReal)
    have hdense : Dense ({z₀}ᶜ : Set ℝ) := (Set.finite_singleton z₀).countable.dense_compl ℝ
    have hext := Continuous.ext_on hdense hcont continuous_const (g := fun _ => (0 : ℝ))
      fun u hu => by rw [hQ_of_ne u hu, Complex.ofReal_im]
    exact fun u => congrFun hext u
  -- Integrability of `Q` on `ℝ`: compact `[z₀ - 1, z₀ + 1]` plus complement dominated by `H`.
  have hQ_cont : Continuous (fun u : ℝ => Q (u : ℂ)) := hQd.continuous.comp Complex.continuous_ofReal
  have hQ_Icc : IntegrableOn (fun u : ℝ => Q (u : ℂ)) (Icc (z₀ - 1) (z₀ + 1)) :=
    hQ_cont.continuousOn.integrableOn_Icc
  have hQ_compl : IntegrableOn (fun u : ℝ => Q (u : ℂ)) (Icc (z₀ - 1) (z₀ + 1))ᶜ := by
    have hdom : Integrable (fun u : ℝ => H (u : ℂ)) (volume.restrict (Icc (z₀ - 1) (z₀ + 1))ᶜ) :=
      hi.integrableOn
    refine hdom.mono hQ_cont.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with u hu
    have hdist : 1 < |u - z₀| := by
      by_contra hle
      push Not at hle
      have habs := abs_le.mp hle
      exact hu ⟨by linarith, by linarith⟩
    have hne : u ≠ z₀ := fun heq => by simp [heq] at hdist; linarith
    have hne_c : (u : ℂ) ≠ (z₀ : ℂ) := fun h => hne (Complex.ofReal_injective h)
    dsimp [Q]
    rw [dslope_of_ne _ hne_c, slope_def_field, hHz₀, sub_zero, norm_div,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact div_le_self (norm_nonneg _) hdist.le
  have hQ_int : Integrable (fun u : ℝ => Q (u : ℂ)) := by
    rw [← integrableOn_univ, ← Set.union_compl_self (Icc (z₀ - 1) (z₀ + 1))]
    exact hQ_Icc.union hQ_compl
  have hQ_class : InAiryClass Q := ⟨hQd, hQ_int, ⟨C'', ν, hC'', hQ_env⟩, hQ_real⟩
  -- Almost-everywhere equality `(H u).re / (u - z₀) = (Q u).re`.
  have hae : (fun u : ℝ => (Q (u : ℂ)).re) =ᵐ[volume] fun u : ℝ => (H (u : ℂ)).re / (u - z₀) := by
    have hcompl : ({z₀}ᶜ : Set ℝ) ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; simp)
    filter_upwards [hcompl] with u hu
    rw [hQ_of_ne u hu, Complex.ofReal_re]
  have hdiv_int : Integrable (fun u : ℝ => (H (u : ℂ)).re / (u - z₀)) :=
    hQ_int.re.congr hae
  exact ⟨hQ_class, hdiv_int, (integral_congr_ae hae).symm⟩

/-- **`lem:deflation-identity` (`ce_shells.tex`, `eq:deflation-identity`):**
for `H ∈ 𝒢` and a real zero `z₀` of `H`, `Q = dslope H z₀ ∈ 𝒢` satisfies
`L_Q(y) = e^{z₀ y} (∫ Q + ∫_0^y e^{-z₀ s} L_H(s) ds)` for all `y ≥ 0`. -/
theorem deflation_identity {H : ℂ → ℂ} (hH : InAiryClass H) {z₀ : ℝ}
    (hz₀ : (H (z₀ : ℂ)).re = 0) {y : ℝ} (hy : 0 ≤ y) :
    laplaceL (fun u => (dslope H (z₀ : ℂ) (u : ℂ)).re) y =
      Real.exp (z₀ * y) * ((∫ u : ℝ, (dslope H (z₀ : ℂ) (u : ℂ)).re) +
        ∫ s in (0 : ℝ)..y, Real.exp (-z₀ * s) * laplaceL (fun u => (H (u : ℂ)).re) s) := by
  obtain ⟨hQ_class, -, -⟩ := deflation_inAiryClass hH hz₀
  have hHz₀ : H (z₀ : ℂ) = 0 := Complex.ext hz₀ (hH.2.2.2 z₀)
  let q : ℝ → ℝ := fun u => (dslope H (z₀ : ℂ) (u : ℂ)).re
  let h : ℝ → ℝ := fun u => (H (u : ℂ)).re
  have hqh : ∀ u : ℝ, (u - z₀) * q u = h u := by
    intro u
    have h1 := sub_smul_dslope H (z₀ : ℂ) (u : ℂ)
    rw [hHz₀, sub_zero, smul_eq_mul, ← Complex.ofReal_sub] at h1
    have hre := congrArg Complex.re h1
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hre
    exact hre
  let g : ℝ → ℝ := fun s => Real.exp (-z₀ * s) * laplaceL q s
  let g' : ℝ → ℝ := fun s => Real.exp (-z₀ * s) * laplaceL h s
  have hg_cont : ContinuousOn g (Icc 0 y) := by
    refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul ?_)
    exact hQ_class.laplace_continuousOn_Ici.mono Icc_subset_Ici_self
  have hg'_cont : ContinuousOn g' (Icc 0 y) := by
    refine ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul ?_)
    exact hH.laplace_continuousOn_Ici.mono Icc_subset_Ici_self
  have hg_deriv : ∀ s ∈ Ioo 0 y, HasDerivAt g (g' s) s := by
    intro s hs
    have hd_exp : HasDerivAt (fun t : ℝ => Real.exp (-z₀ * t))
        (-z₀ * Real.exp (-z₀ * s)) s := by
      simpa [mul_comm] using ((hasDerivAt_id s).const_mul (-z₀)).exp
    have hd_lap : HasDerivAt (laplaceL q) (∫ u : ℝ, (u * q u) * Real.exp (s * u)) s :=
      hQ_class.to_polyLeftAiryRightBound.hasDerivAt_integral hs.1
    refine (hd_exp.mul hd_lap).congr_deriv ?_
    have hint_q : Integrable (fun u : ℝ => q u * Real.exp (s * u)) :=
      hQ_class.to_polyLeftAiryRightBound.integrable_exp hs.1
    have hint_uq : Integrable (fun u : ℝ => (u * q u) * Real.exp (s * u)) :=
      hQ_class.to_polyLeftAiryRightBound.mul_id.integrable_exp hs.1
    have hcomb : (∫ u : ℝ, (u * q u) * Real.exp (s * u)) - z₀ * laplaceL q s = laplaceL h s := by
      unfold laplaceL
      rw [← integral_const_mul, ← integral_sub hint_uq (hint_q.const_mul z₀)]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      dsimp only
      rw [← hqh u]
      ring
    dsimp [g']
    rw [← hcomb]
    ring
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy hg_cont hg_deriv
    (hg'_cont.intervalIntegrable_of_Icc hy)
  have hg0 : g 0 = ∫ u : ℝ, q u := by
    dsimp [g, laplaceL]
    simp
  rw [hg0] at hftc
  have h1 : Real.exp (-z₀ * y) * laplaceL q y =
      (∫ u : ℝ, q u) + ∫ s in (0 : ℝ)..y, g' s := by linarith [hftc]
  calc laplaceL q y
      = Real.exp (z₀ * y) * (Real.exp (-z₀ * y) * laplaceL q y) := by
        rw [← mul_assoc, ← Real.exp_add]; simp
    _ = Real.exp (z₀ * y) * ((∫ u : ℝ, q u) + ∫ s in (0 : ℝ)..y, g' s) := by rw [h1]

/-- Strict Laplace positivity of `Q = dslope H z₀` on `(0, ∞)` when `H ≢ 0`, `L_H ≥ 0`, and
`∫ Q ≥ 0` (`lem:deflation-identity`, final sentence). -/
theorem deflation_laplace_pos {H : ℂ → ℂ} (hH : InAiryClass H) (hnz : ∃ z : ℂ, H z ≠ 0)
    (hL_nn : ∀ s : ℝ, 0 ≤ s → 0 ≤ laplaceL (fun u => (H (u : ℂ)).re) s)
    {z₀ : ℝ} (hz₀ : (H (z₀ : ℂ)).re = 0)
    (hmass : 0 ≤ ∫ u : ℝ, (dslope H (z₀ : ℂ) (u : ℂ)).re)
    {y : ℝ} (hy : 0 < y) :
    0 < laplaceL (fun u => (dslope H (z₀ : ℂ) (u : ℂ)).re) y := by
  rw [deflation_identity hH hz₀ hy.le]
  refine mul_pos (Real.exp_pos _) ?_
  let g' : ℝ → ℝ := fun s => Real.exp (-z₀ * s) * laplaceL (fun u => (H (u : ℂ)).re) s
  have hg'_cont : ContinuousOn g' (Icc 0 y) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      (hH.laplace_continuousOn_Ici.mono Icc_subset_Ici_self)
  have hg'_nn : ∀ s ∈ Icc 0 y, 0 ≤ g' s := fun s hs =>
    mul_nonneg (Real.exp_pos _).le (hL_nn s hs.1)
  -- There is some `s₀ ∈ Ioo 0 y` with `0 < g' s₀`, otherwise `laplaceL H = 0` on `Ioo 0 y`.
  have hex_pos : ∃ s₀ ∈ Ioo 0 y, 0 < g' s₀ := by
    by_contra hall
    push Not at hall
    have hev0 : laplaceL (fun u => (H (u : ℂ)).re) =ᶠ[𝓝 (y / 2)] 0 := by
      have hmem : Ioo 0 y ∈ 𝓝 (y / 2) := Ioo_mem_nhds (by linarith) (by linarith)
      filter_upwards [hmem] with s hs
      have hle := hall s hs
      have hge := hg'_nn s ⟨hs.1.le, hs.2.le⟩
      have hg0 : g' s = 0 := le_antisymm hle hge
      exact (mul_eq_zero.mp hg0).resolve_left (Real.exp_pos _).ne'
    obtain ⟨z, hz⟩ := hnz
    exact hz (laplaceL_eq_zero_of_eventuallyEq_zero hH (by linarith : 0 < y / 2) hev0 z)
  obtain ⟨s₀, hs₀, hpos₀⟩ := hex_pos
  -- By continuity on `Icc 0 y`, `g' ≥ g'(s₀)/2` on a subinterval `[a, b] ⊆ [0, y]` with `a < b`.
  have hcont_at : ContinuousWithinAt g' (Icc 0 y) s₀ := hg'_cont s₀ ⟨hs₀.1.le, hs₀.2.le⟩
  have hnhds : Icc 0 y ∈ 𝓝 s₀ := Icc_mem_nhds hs₀.1 hs₀.2
  have hcont_s₀ : ContinuousAt g' s₀ := hcont_at.continuousAt hnhds
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp hcont_s₀ (g' s₀ / 2) (half_pos hpos₀)
  let r : ℝ := min (δ / 2) (min (s₀ / 2) ((y - s₀) / 2))
  have hr_pos : 0 < r := lt_min (half_pos hδ_pos) (lt_min (half_pos hs₀.1) (half_pos (sub_pos.mpr hs₀.2)))
  have ha_ge : 0 ≤ s₀ - r := by
    have : r ≤ s₀ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [hs₀.1]
  have hb_le : s₀ + r ≤ y := by
    have : r ≤ (y - s₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith [hs₀.2]
  have hab : s₀ - r ≤ s₀ + r := by linarith
  have hsub_ball : ∀ s ∈ Icc (s₀ - r) (s₀ + r), g' s₀ / 2 ≤ g' s := by
    intro s hs
    have hr_lt : r < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
    have hdist : dist s s₀ < δ := by
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have hd := abs_lt.mp (by simpa [Real.dist_eq] using hδ hdist)
    linarith
  have hint_pos : 0 < ∫ s in (0 : ℝ)..y, g' s := by
    have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
      ((hg'_cont.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (μ := volume) ha_ge)
      ((hg'_cont.mono (Icc_subset_Icc ha_ge hb_le)).intervalIntegrable_of_Icc (μ := volume) hab)).symm
    have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
      ((hg'_cont.mono (Icc_subset_Icc_right hb_le)).intervalIntegrable_of_Icc (μ := volume) (by linarith))
      ((hg'_cont.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (μ := volume) hb_le)).symm
    have h1_nn : 0 ≤ ∫ s in (0 : ℝ)..(s₀ - r), g' s :=
      intervalIntegral.integral_nonneg ha_ge fun s hs => hg'_nn s ⟨hs.1, hs.2.trans (by linarith)⟩
    have h3_nn : 0 ≤ ∫ s in (s₀ + r)..y, g' s :=
      intervalIntegral.integral_nonneg hb_le fun s hs => hg'_nn s ⟨(by linarith : 0 ≤ s₀ + r).trans hs.1, hs.2⟩
    have h2_ge : (2 * r) * (g' s₀ / 2) ≤ ∫ s in (s₀ - r)..(s₀ + r), g' s := by
      have hconst : ∫ _s in (s₀ - r)..(s₀ + r), (g' s₀ / 2) = (2 * r) * (g' s₀ / 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
      rw [← hconst]
      exact intervalIntegral.integral_mono_on hab (intervalIntegrable_const (μ := volume))
        ((hg'_cont.mono (Icc_subset_Icc ha_ge hb_le)).intervalIntegrable_of_Icc (μ := volume) hab) hsub_ball
    have h2_pos : 0 < ∫ s in (s₀ - r)..(s₀ + r), g' s :=
      lt_of_lt_of_le (mul_pos (by linarith) (half_pos hpos₀)) h2_ge
    linarith
  linarith

/-! ### Positive-mass shell buffer (`lem:airy-shell-buffer`, `ce_airy_lp_proofs.tex`) -/

private lemma inAiryClass_shift {F : ℂ → ℂ} (hF : InAiryClass F) {s : ℝ} (hs : 0 ≤ s) :
    InAiryClass (fun z => F (z + (s : ℂ))) := by
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, hreal⟩ := hF
  refine ⟨hd.comp (differentiable_id.add (differentiable_const (s : ℂ))), ?_,
    ⟨C * (1 + s) ^ |ν|, |ν|, by positivity, fun z => airy_shift_bound hC hb hs z⟩, ?_⟩
  · have hcomp := hi.comp_add_right s
    refine hcomp.congr (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Complex.ofReal_add]
  · intro x
    dsimp only
    rw [← Complex.ofReal_add]
    exact hreal (x + s)

/-- **`lem:airy-shell-buffer` (`ce_airy_lp_proofs.tex`, lines 101–135):**
for every `D : ShellHBData` and `v₁ < D.tm`, there exist `B : ℂ → ℂ` and `Y_B > 0` such that
`B ∈ 𝒢`, `(B u).re < 0` for all `u ≤ v₁` and for all `s ∈ shellSites D`, `0 < laplaceL B 0`,
and `0 < laplaceL B y` for all `y ≥ Y_B`. -/
theorem exists_airy_shell_buffer (D : ShellHBData) {v₁ : ℝ} (hv₁ : v₁ < D.tm) :
    ∃ (B : ℂ → ℂ) (Y_B : ℝ),
      InAiryClass B ∧
      0 < Y_B ∧
      (∀ u : ℝ, u ≤ v₁ → (B (u : ℂ)).re < 0) ∧
      (∀ t ∈ shellSites D, (B (t : ℂ)).re < 0) ∧
      0 < laplaceL (fun u => (B (u : ℂ)).re) 0 ∧
      (∀ y : ℝ, Y_B ≤ y → 0 < laplaceL (fun u => (B (u : ℂ)).re) y) := by
  classical
  -- 1. Terminal cardinal `C_N = dslope (-D.G) D.tm ∈ 𝒢` has positive integral `I_CN > 0`.
  let negG : ℂ → ℂ := fun z => -D.G z
  have hnegG_cl : InAiryClass negG := D.G_inAiryClass.neg
  have hnegG_tm : (negG (D.tm : ℂ)).re = 0 := by
    dsimp [negG]; rw [D.G_eq_zero_on_S D.tm D.tm_mem]; simp
  obtain ⟨hCN_cl, -, -⟩ := deflation_inAiryClass hnegG_cl hnegG_tm
  let C_N : ℂ → ℂ := dslope negG (D.tm : ℂ)
  change InAiryClass C_N at hCN_cl
  -- Show `(C_N D.tm).re = -(deriv D.G D.tm).re > 0`.
  have hCN_tm_pos : 0 < (C_N (D.tm : ℂ)).re := by
    have hd_real : HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).re) (deriv D.G (D.tm : ℂ)).re D.tm := by
      have hdC : HasDerivAt (fun x : ℝ => D.G (x : ℂ)) (deriv D.G (D.tm : ℂ)) D.tm := by
        simpa using (D.G_diff (D.tm : ℂ)).hasDerivAt.comp_ofReal
      exact (Complex.reCLM.hasFDerivAt.comp_hasDerivAt D.tm hdC).congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl)
    have hd_im0 : (deriv D.G (D.tm : ℂ)).im = 0 := by
      have hdC : HasDerivAt (fun x : ℝ => D.G (x : ℂ)) (deriv D.G (D.tm : ℂ)) D.tm := by
        simpa using (D.G_diff (D.tm : ℂ)).hasDerivAt.comp_ofReal
      have hd_im : HasDerivAt (fun x : ℝ => (D.G (x : ℂ)).im) (deriv D.G (D.tm : ℂ)).im D.tm :=
        (Complex.imCLM.hasFDerivAt.comp_hasDerivAt D.tm hdC).congr_of_eventuallyEq
          (Eventually.of_forall fun _ => rfl)
      have hconst : (fun x : ℝ => (D.G (x : ℂ)).im) = fun _ => 0 := funext D.G_real
      rw [hconst] at hd_im
      exact hd_im.unique (hasDerivAt_const D.tm (0 : ℝ))
    have hd_re_ne : (deriv D.G (D.tm : ℂ)).re ≠ 0 := by
      intro h0
      exact D.G_deriv_ne_zero D.tm D.tm_mem (Complex.ext h0 hd_im0)
    -- Left difference quotient `(G(D.tm - t) - G(D.tm)) / (-t) ≤ 0` for `t > 0`, so `deriv.re ≤ 0`.
    have hd_re_le : (deriv D.G (D.tm : ℂ)).re ≤ 0 := by
      by_contra hgt
      push Not at hgt
      have hslope := hd_real.tendsto_slope_zero_left
      have hev := hslope.eventually (Ioi_mem_nhds hgt)
      rw [eventually_nhdsWithin_iff] at hev
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
      let h : ℝ := -min (δ / 2) 1
      have hh_neg : h < 0 := neg_neg_of_pos (lt_min (half_pos hδ_pos) one_pos)
      have hh_dist : dist h 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_neg hh_neg]
        dsimp [h]; rw [neg_neg]
        exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
      have hpos_q : 0 < h⁻¹ • ((D.G ((D.tm + h : ℝ) : ℂ)).re - (D.G (D.tm : ℂ)).re) :=
        hδ hh_dist hh_neg
      rw [D.G_eq_zero_on_S D.tm D.tm_mem, Complex.zero_re, sub_zero, smul_eq_mul] at hpos_q
      have hnn := D.G_nonneg_left (D.tm + h) (by linarith)
      have hnp : h⁻¹ * (D.G ((D.tm + h : ℝ) : ℂ)).re ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr hh_neg.le) hnn
      linarith
    have hd_re_neg : (deriv D.G (D.tm : ℂ)).re < 0 := lt_of_le_of_ne hd_re_le hd_re_ne
    dsimp [C_N, negG]
    rw [dslope_same]
    change 0 < (deriv (-D.G) (D.tm : ℂ)).re
    rw [((D.G_diff (D.tm : ℂ)).hasDerivAt.neg).deriv, Complex.neg_re]
    linarith
  have hCN_sites : ∀ t ∈ shellSites D, C_N (t : ℂ) = 0 := by
    intro t ht
    obtain ⟨ht_ne, htS⟩ := Finset.mem_erase.1 ht
    have hne : (t : ℂ) ≠ (D.tm : ℂ) := fun h => ht_ne (Complex.ofReal_injective h)
    dsimp [C_N, negG]
    rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S t htS, D.G_eq_zero_on_S D.tm D.tm_mem,
      neg_zero, sub_self, zero_div]
  have hCN_int_pos : 0 < ∫ u : ℝ, (C_N (u : ℂ)).re := by
    by_cases hQ : D.Q = 0
    · -- `D.Q = 0`: `D.S = {D.tm}` so `C_N(u) * (u - D.tm)² = N(u)² ≥ 0` for all `u ∈ ℝ`!
      have hcard1 : D.S.card = 1 := by
        rcases D.m_eq with ⟨_, hc⟩ | ⟨hQne, _⟩
        · exact hc
        · exact absurd hQ hQne
      have hS_eq : D.S = {D.tm} := by
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
        have htm_a : D.tm = a := Finset.mem_singleton.mp (ha ▸ D.tm_mem)
        rwa [htm_a]
      have hCN_nn : ∀ u : ℝ, 0 ≤ (C_N (u : ℂ)).re := by
        intro u
        by_cases hu : u = D.tm
        · rw [hu]; exact hCN_tm_pos.le
        · have hne : (u : ℂ) ≠ (D.tm : ℂ) := fun h => hu (Complex.ofReal_injective h)
          have hprod := D.G_prod_eq (u : ℂ)
          rw [hcard1, hS_eq] at hprod
          unfold at47_pr at hprod
          rw [Finset.prod_singleton, pow_one, airyPQN_ofReal] at hprod
          have hsub_ne : u - D.tm ≠ 0 := sub_ne_zero.mpr hu
          have hGu : (D.G (u : ℂ)).re = -(at47_Nf D.P D.Q u ^ 2 / (u - D.tm)) := by
            have h1 : D.G (u : ℂ) = (((-(at47_Nf D.P D.Q u ^ 2) / (u - D.tm) : ℝ) : ℂ)) := by
              rw [Complex.ofReal_div, Complex.ofReal_sub, eq_div_iff (sub_ne_zero.mpr hne)]
              unfold at47_Nf
              push_cast at hprod ⊢
              linear_combination hprod
            rw [h1, Complex.ofReal_re, neg_div]
          dsimp [C_N, negG]
          rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero,
            sub_zero]
          have hGu_c : -D.G (u : ℂ) = ((-(D.G (u : ℂ)).re : ℝ) : ℂ) :=
            Complex.ext (by simp) (by simp [D.G_real u])
          rw [hGu_c, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re, hGu, neg_neg,
            div_div, ← sq]
          positivity
      -- Continuous `≥ 0` function positive at `D.tm` has strictly positive integral.
      have hcont : Continuous (fun u : ℝ => (C_N (u : ℂ)).re) :=
        Complex.continuous_re.comp (hCN_cl.1.continuous.comp Complex.continuous_ofReal)
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := D.tm))
        ((C_N (D.tm : ℂ)).re / 2) (half_pos hCN_tm_pos)
      let r : ℝ := δ / 2
      have hr_pos : 0 < r := half_pos hδ_pos
      have hge_Icc : ∀ u ∈ Icc (D.tm - r) (D.tm + r), (C_N (D.tm : ℂ)).re / 2 ≤ (C_N (u : ℂ)).re := by
        intro u hu
        have hdist : dist u D.tm < δ := by
          rw [Real.dist_eq, abs_lt]
          dsimp [r] at hu
          exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
        have hd := abs_lt.mp (by simpa [Real.dist_eq] using hδ hdist)
        linarith
      have hset_le : (∫ u in Icc (D.tm - r) (D.tm + r), (C_N (u : ℂ)).re) ≤
          ∫ u : ℝ, (C_N (u : ℂ)).re :=
        setIntegral_le_integral hCN_cl.2.1.re (Eventually.of_forall hCN_nn)
      have hconst_le : (∫ _u in Icc (D.tm - r) (D.tm + r), ((C_N (D.tm : ℂ)).re / 2)) ≤
          ∫ u in Icc (D.tm - r) (D.tm + r), (C_N (u : ℂ)).re :=
        setIntegral_mono_on (integrableOn_const (hs := measure_Icc_lt_top.ne))
          hCN_cl.2.1.re.integrableOn measurableSet_Icc hge_Icc
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hconst_le
      have hpos_lb : 0 < (D.tm + r - (D.tm - r)) * ((C_N (D.tm : ℂ)).re / 2) :=
        mul_pos (by linarith) (half_pos hCN_tm_pos)
      linarith
    · -- `D.Q ≠ 0`: HB quadrature `airyPQ_hasSum_unc` reduces `∫ C_N` to the single `D.tm` term!
      obtain ⟨C_env, ν_env, hC_env, hb_env⟩ := hCN_cl.2.2.1
      have hsum1 := airyPQ_hasSum_unc D.hHB hQ hCN_cl.1 hCN_cl.2.1 hC_env hb_env
      let z_tm : {z : ℂ // airyPQN D.P D.Q z = 0} := ⟨(D.tm : ℂ), D.S_zero D.tm_mem⟩
      have hzero_other : ∀ z : {z : ℂ // airyPQN D.P D.Q z = 0}, z ≠ z_tm → C_N z.1 = 0 := by
        intro z hzne
        have hzr : z.1 = ((z.1.re : ℝ) : ℂ) := airyPQ_zero_eq_ofReal D.hHB z.2
        have hx_ne : z.1.re ≠ D.tm := by
          intro heq
          apply hzne
          apply Subtype.ext
          rw [hzr, heq]
        have hx_c_ne : (z.1.re : ℂ) ≠ (D.tm : ℂ) := fun h => hx_ne (Complex.ofReal_injective h)
        have hGx0 : D.G (z.1.re : ℂ) = 0 := by
          by_cases hxS : z.1.re ∈ D.S
          · exact D.G_eq_zero_on_S _ hxS
          · have hp := D.G_prod_eq (z.1.re : ℂ)
            have hz0 : airyPQN D.P D.Q (z.1.re : ℂ) = 0 := hzr ▸ z.2
            rw [hz0, zero_pow two_ne_zero, mul_zero] at hp
            exact (mul_eq_zero.mp hp).resolve_right (at47_pr_ne_zero hxS)
        rw [hzr]
        dsimp [C_N, negG]
        rw [dslope_of_ne _ hx_c_ne, slope_def_field, hGx0, D.G_eq_zero_on_S D.tm D.tm_mem,
          neg_zero, sub_self, zero_div]
      have hsum2 : HasSum (fun z : {z : ℂ // airyPQN D.P D.Q z = 0} =>
          C_N z.1 * (airyPQD D.P D.Q z.1 / airyPQN' D.P D.Q z.1 ^ 2))
          (C_N (D.tm : ℂ) * (airyPQD D.P D.Q (D.tm : ℂ) / airyPQN' D.P D.Q (D.tm : ℂ) ^ 2)) :=
        hasSum_single z_tm fun z hz => by rw [hzero_other z hz, zero_mul]
      have hint_eq := hsum1.unique hsum2
      obtain ⟨hD_pos, hN'_ne⟩ := airyPQ_zero_weight_pos D.hHB hQ (D.S_zero D.tm_mem)
      have hN'_im0 : (airyPQN' D.P D.Q (D.tm : ℂ)).im = 0 := by
        unfold airyPQN'
        rw [airyPQc_ofReal, airyPQc_ofReal, airyPQc_ofReal, airyPQc_ofReal,
          airyAiC_ofReal, deriv_airyAiC_ofReal]
        simp
      have hN'_c : airyPQN' D.P D.Q (D.tm : ℂ) = ((airyPQN' D.P D.Q (D.tm : ℂ)).re : ℂ) :=
        Complex.ext rfl hN'_im0
      have hN'_re_ne : (airyPQN' D.P D.Q (D.tm : ℂ)).re ≠ 0 :=
        fun h0 => hN'_ne (by rw [hN'_c, h0, Complex.ofReal_zero])
      have hCN_c : C_N (D.tm : ℂ) = ((C_N (D.tm : ℂ)).re : ℂ) := Complex.ext rfl (hCN_cl.2.2.2 D.tm)
      have hre_int : (∫ u : ℝ, (C_N (u : ℂ)).re) = (∫ u : ℝ, C_N (u : ℂ)).re := by
        simpa [RCLike.re_to_complex] using integral_re hCN_cl.2.1
      rw [hre_int, hint_eq, hCN_c, airyPQD_ofReal, hN'_c, ← Complex.ofReal_pow, ← Complex.ofReal_div,
        ← Complex.ofReal_mul, Complex.ofReal_re]
      have hsq_pos : 0 < (airyPQN' D.P D.Q (D.tm : ℂ)).re ^ 2 := sq_pos_of_ne_zero hN'_re_ne
      positivity
  -- 2. Build `B₀ = -D.G + η C_N - η' J_0` and shift by a small `s > 0`.
  let η : ℝ := (D.tm - v₁) / 2
  have hη_pos : 0 < η := by dsimp [η]; linarith
  let I_CN : ℝ := ∫ u : ℝ, (C_N (u : ℂ)).re
  let I_J0 : ℝ := ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re
  have hIJ0_pos : 0 < I_J0 := by
    obtain ⟨c₁, _, hc₁_pos, _, hbd⟩ := airyLaplace_airyRefJ0_bounds
    have h0 := (hbd 0 le_rfl).1
    unfold airyLaplace at h0
    simp only [zero_pow (by norm_num : 3 ≠ 0), neg_zero, zero_div, Real.exp_zero, one_mul,
      zero_mul, mul_one, add_zero, Real.one_rpow] at h0
    linarith
  let η' : ℝ := (η * I_CN) / (2 * I_J0)
  have hη'_pos : 0 < η' := by positivity
  let B₀ : ℂ → ℂ := fun z => (negG z + (η : ℂ) * C_N z) - (η' : ℂ) * airyRefJ0 z
  have hB₀_cl : InAiryClass B₀ :=
    (hnegG_cl.add (hCN_cl.smul η)).sub (airyRefJ0_inAiryClass.smul η')
  have hB₀_re : ∀ u : ℝ, (B₀ (u : ℂ)).re =
      -(D.G (u : ℂ)).re + η * (C_N (u : ℂ)).re - η' * (airyRefJ0 (u : ℂ)).re := by
    intro u
    dsimp [B₀, negG]
    simp [Complex.mul_re, hCN_cl.2.2.2 u, airyRefJ0_inAiryClass.2.2.2 u]
  have hB₀_int_pos : 0 < ∫ u : ℝ, (B₀ (u : ℂ)).re := by
    have h1 : Integrable (fun u : ℝ => -(D.G (u : ℂ)).re) := by
      simpa [RCLike.re_to_complex] using D.G_int.re.neg
    have h2 : Integrable (fun u : ℝ => η * (C_N (u : ℂ)).re) := by
      simpa [RCLike.re_to_complex] using hCN_cl.2.1.re.const_mul η
    have h12 : Integrable (fun u : ℝ => -(D.G (u : ℂ)).re + η * (C_N (u : ℂ)).re) := h1.add h2
    have h3 : Integrable (fun u : ℝ => η' * (airyRefJ0 (u : ℂ)).re) := by
      simpa [RCLike.re_to_complex] using airyRefJ0_inAiryClass.2.1.re.const_mul η'
    have hint_G0 : (∫ u : ℝ, -(D.G (u : ℂ)).re) = 0 := by
      rw [integral_neg]
      have hre : (∫ u : ℝ, (D.G (u : ℂ)).re) = (∫ u : ℝ, D.G (u : ℂ)).re := by
        simpa [RCLike.re_to_complex] using integral_re D.G_int
      rw [hre, D.G_integral_zero, Complex.zero_re, neg_zero]
    simp_rw [hB₀_re]
    rw [integral_sub h12 h3, integral_add h1 h2, hint_G0, zero_add,
      integral_const_mul, integral_const_mul]
    change 0 < η * I_CN - η' * I_J0
    dsimp [η']
    have hcancel : (η * I_CN) / (2 * I_J0) * I_J0 = (η * I_CN) / 2 := by
      field_simp [hIJ0_pos.ne']
    rw [hcancel]
    linarith [mul_pos hη_pos hCN_int_pos]
  have hB₀_left : ∀ u : ℝ, u ≤ D.tm - η → (B₀ (u : ℂ)).re < 0 := by
    intro u hu
    rw [hB₀_re u]
    have hu_lt : u < D.tm := by linarith
    have hne : (u : ℂ) ≠ (D.tm : ℂ) := fun h => hu_lt.ne (Complex.ofReal_injective h)
    have hCN_u : (C_N (u : ℂ)).re = (-(D.G (u : ℂ)).re) / (u - D.tm) := by
      dsimp [C_N, negG]
      rw [dslope_of_ne _ hne, slope_def_field, D.G_eq_zero_on_S D.tm D.tm_mem, neg_zero, sub_zero]
      have hc : -D.G (u : ℂ) = ((-(D.G (u : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [D.G_real u])
      rw [hc, ← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [hCN_u]
    have hfac : -(D.G (u : ℂ)).re + η * (-(D.G (u : ℂ)).re / (u - D.tm)) ≤ 0 := by
      have hden_neg : u - D.tm < 0 := sub_neg.mpr hu_lt
      have heq : -(D.G (u : ℂ)).re + η * (-(D.G (u : ℂ)).re / (u - D.tm)) =
          (-(D.G (u : ℂ)).re) * ((u - D.tm + η) / (u - D.tm)) := by
        field_simp [hden_neg.ne]; ring
      rw [heq]
      have hratio_nn : 0 ≤ (u - D.tm + η) / (u - D.tm) :=
        div_nonneg_of_nonpos (by linarith) hden_neg.le
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (D.G_nonneg_left u hu_lt.le)) hratio_nn
    linarith [mul_pos hη'_pos (airyRefJ0_pos u)]
  have hB₀_sites : ∀ t ∈ shellSites D, (B₀ (t : ℂ)).re < 0 := by
    intro t ht
    obtain ⟨_, htS⟩ := Finset.mem_erase.1 ht
    rw [hB₀_re t, D.G_eq_zero_on_S t htS, hCN_sites t ht, Complex.zero_re, neg_zero, mul_zero,
      add_zero, zero_sub, neg_lt_zero]
    exact mul_pos hη'_pos (airyRefJ0_pos t)
  -- Choose shift `0 < s ≤ (D.tm - v₁) / 4` preserving `< 0` on the finite set `shellSites D`.
  have hcont_B₀ : Continuous (fun u : ℝ => (B₀ (u : ℂ)).re) :=
    Complex.continuous_re.comp (hB₀_cl.1.continuous.comp Complex.continuous_ofReal)
  have hex_shift : ∃ s : ℝ, 0 < s ∧ s ≤ (D.tm - v₁) / 4 ∧
      ∀ t ∈ shellSites D, (B₀ ((t + s : ℝ) : ℂ)).re < 0 := by
    have hpt : ∀ t ∈ shellSites D, ∃ δ : ℝ, 0 < δ ∧
        ∀ s : ℝ, 0 ≤ s → s ≤ δ → (B₀ ((t + s : ℝ) : ℂ)).re < 0 := by
      intro t ht
      have hneg := hB₀_sites t ht
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hcont_B₀.continuousAt (x := t))
        (-(B₀ (t : ℂ)).re / 2) (by linarith)
      refine ⟨δ / 2, half_pos hδ_pos, fun s hs0 hs_le => ?_⟩
      have hdist : dist (t + s) t < δ := by
        rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs0]
        linarith
      have hd := hδ (x := t + s) hdist
      rw [Real.dist_eq] at hd
      have hd' := abs_lt.mp hd
      linarith
    choose δ_fn hδ_fn_pos hδ_fn using fun (t : {x // x ∈ shellSites D}) => hpt t.1 t.2
    by_cases hne_sites : (shellSites D).Nonempty
    · have hatt_ne : (shellSites D).attach.Nonempty := Finset.attach_nonempty_iff.mpr hne_sites
      let δ_min : ℝ := (shellSites D).attach.inf' hatt_ne δ_fn
      have hδ_min_pos : 0 < δ_min := (Finset.lt_inf'_iff _).mpr fun t _ => hδ_fn_pos t
      let s : ℝ := min ((D.tm - v₁) / 4) δ_min
      have hs_pos : 0 < s := lt_min (by linarith) hδ_min_pos
      refine ⟨s, hs_pos, min_le_left _ _, fun t ht => ?_⟩
      have hs_le : s ≤ δ_fn ⟨t, ht⟩ :=
        (min_le_right _ _).trans (Finset.inf'_le _ (Finset.mem_attach _ ⟨t, ht⟩))
      exact hδ_fn ⟨t, ht⟩ s hs_pos.le hs_le
    · refine ⟨(D.tm - v₁) / 4, by linarith, le_rfl, fun t ht => absurd ⟨t, ht⟩ hne_sites⟩
  obtain ⟨s_sh, hs_pos, hs_le, hs_sites⟩ := hex_shift
  let B_sh : ℂ → ℂ := fun z => B₀ (z + (s_sh : ℂ))
  have hB_sh_cl : InAiryClass B_sh := inAiryClass_shift hB₀_cl hs_pos.le
  have hB_sh_re : ∀ u : ℝ, (B_sh (u : ℂ)).re = (B₀ ((u + s_sh : ℝ) : ℂ)).re := by
    intro u; dsimp [B_sh]; rw [Complex.ofReal_add]
  have hB_sh_left : ∀ u : ℝ, u ≤ v₁ → (B_sh (u : ℂ)).re < 0 := by
    intro u hu
    rw [hB_sh_re u]
    exact hB₀_left (u + s_sh) (by dsimp [η]; linarith)
  have hB_sh_int : (∫ u : ℝ, (B_sh (u : ℂ)).re) = ∫ u : ℝ, (B₀ (u : ℂ)).re := by
    simp_rw [hB_sh_re]
    exact integral_add_right_eq_self (fun u : ℝ => (B₀ (u : ℂ)).re) s_sh
  -- Exponentially damped Laplace bound `|airyLaplace B_sh y| ≤ e^{-s_sh y} * M_B0` for `y ≥ 0`.
  let M_B0 : ℝ := ∫ u : ℝ, ‖B₀ (u : ℂ)‖
  have hMB0_nn : 0 ≤ M_B0 := integral_nonneg fun _ => norm_nonneg _
  have hB_sh_lap_abs : ∀ y : ℝ, 0 ≤ y →
      |airyLaplace (fun u => (B_sh (u : ℂ)).re) y| ≤ Real.exp (-s_sh * y) * M_B0 := by
    intro y hy
    have hshift_lap : airyLaplace (fun u => (B_sh (u : ℂ)).re) y =
        Real.exp (-s_sh * y) * airyLaplace (fun u => (B₀ (u : ℂ)).re) y := by
      unfold airyLaplace
      simp_rw [hB_sh_re]
      have hlin : ∀ u : ℝ, (B₀ ((u + s_sh : ℝ) : ℂ)).re * Real.exp (y * u) =
          Real.exp (-s_sh * y) * ((B₀ ((u + s_sh : ℝ) : ℂ)).re * Real.exp (y * (u + s_sh))) := by
        intro u
        rw [mul_comm (Real.exp (-s_sh * y)), mul_assoc, ← Real.exp_add]
        congr 2; ring
      simp_rw [hlin]
      rw [integral_const_mul, integral_add_right_eq_self (fun v : ℝ => (B₀ (v : ℂ)).re * Real.exp (y * v)) s_sh]
      ring
    have hub1 : airyLaplace (fun u => (B₀ (u : ℂ)).re) y ≤ M_B0 :=
      airyLaplace_re_le_l1 hB₀_cl hy
    have hub2 : -airyLaplace (fun u => (B₀ (u : ℂ)).re) y ≤ M_B0 := by
      have hneg := airyLaplace_re_le_l1 hB₀_cl.neg hy
      have heq_neg : airyLaplace (fun u => ((-B₀ (u : ℂ)).re)) y =
          -airyLaplace (fun u => (B₀ (u : ℂ)).re) y := by
        unfold airyLaplace
        simp only [Complex.neg_re, neg_mul, integral_neg, mul_neg]
      have hnorm_neg : (∫ u : ℝ, ‖-B₀ (u : ℂ)‖) = M_B0 := by simp [M_B0]
      rwa [heq_neg, hnorm_neg] at hneg
    rw [hshift_lap, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, hub1⟩) (Real.exp_pos _).le
  -- 3. Auxiliary unshifted profile `B₁ = airyTrialSquareWitness 1 (fun _ => 1) d` (`v₁ < d < a₁`).
  have htm_le_a1 : D.tm ≤ airyZero 1 := D.tm_le_airyZero_one
  let d : ℝ := (v₁ + airyZero 1) / 2
  have hv₁_lt_d : v₁ < d := by dsimp [d]; linarith
  have hd_lt_a1 : d < airyZero 1 := by dsimp [d]; linarith
  let c1 : Fin 1 → ℝ := fun _ => 1
  have hc1_sum_ne : (∑ n : Fin 1, c1 n) ≠ 0 := by simp [c1]
  let B₁ : ℂ → ℂ := airyTrialSquareWitness 1 c1 d
  have hB₁_cl : InAiryClass B₁ := airyTrialSquareWitness_inAiryClass c1 d
  have hB₁_left : ∀ u : ℝ, u ≤ v₁ → (B₁ (u : ℂ)).re ≤ 0 := by
    intro u hu
    dsimp [B₁]
    rw [airyTrialSquareWitness_re]
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  have hB₁_int_pos : 0 < ∫ u : ℝ, (B₁ (u : ℂ)).re := by
    dsimp [B₁]
    rw [integral_airyTrialSquareWitness]
    simp only [Fin.sum_univ_one, Fin.val_zero, c1, one_pow, mul_one, airyZ, zero_add]
    linarith
  -- Large-`y` polynomial Laplace lower bound for `B₁` via `airyTrialSquareWitness_ge_refJ0_tail`.
  obtain ⟨U, b, hU_gt, hb_pos, htail_ge⟩ := airyTrialSquareWitness_ge_refJ0_tail hc1_sum_ne d
  obtain ⟨c_J, _, hc_J_pos, _, hJ_lap_bd⟩ := airyLaplace_airyRefJ0_bounds
  let g_err : ℝ → ℝ := fun u => (B₁ (u : ℂ)).re - b * (airyRefJ0 (u : ℂ)).re
  have hg_err_int : Integrable g_err := hB₁_cl.2.1.re.sub (airyRefJ0_inAiryClass.2.1.re.const_mul b)
  let M_err : ℝ := ∫ u : ℝ, |g_err u|
  have hM_err_nn : 0 ≤ M_err := integral_nonneg fun _ => abs_nonneg _
  have hlim_err : Tendsto (fun y : ℝ =>
      M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (2 * y) ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * y))
        atTop (𝓝 0) := by
      have ha := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) (1 / 24 : ℝ) (by norm_num)
      have hb := ha.const_mul ((2 : ℝ) ^ (5 / 2 : ℝ))
      rw [mul_zero] at hb
      refine hb.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy0
      rw [Real.mul_rpow (by norm_num) hy0, mul_assoc]
    have h2 := h1.const_mul M_err
    rw [mul_zero] at h2
    refine squeeze_zero_norm' ?_ h2
    have hU_nn : 0 ≤ 24 * U + 2 := by
      have : 0 < U := lt_of_le_of_lt (le_max_left 0 d) hU_gt
      positivity
    filter_upwards [eventually_ge_atTop (max 1 (Real.sqrt (24 * U + 2)))] with y hy
    have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one hy1
    have hy_sq : 24 * U + 2 ≤ y ^ 2 := by
      have hsr : Real.sqrt (24 * U + 2) ≤ y := (le_max_right _ _).trans hy
      calc 24 * U + 2 = (Real.sqrt (24 * U + 2)) ^ 2 := (Real.sq_sqrt hU_nn).symm
        _ ≤ y ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsr 2
    have hexp_le : y * U - y ^ 3 / 12 ≤ -(1 / 24 : ℝ) * y := by
      have hmul : (24 * U + 2) * y ≤ y ^ 3 :=
        (mul_le_mul_of_nonneg_right hy_sq hy0.le).trans_eq (by ring)
      have hy3 : 0 ≤ y ^ 3 := by positivity
      have h24 : 24 * (y * U - y ^ 3 / 12 + (1 / 24 : ℝ) * y) =
          ((24 * U + 2) * y - y ^ 3) - y ^ 3 - y := by ring
      linarith
    have hrpow_le : (1 + y) ^ (5 / 2 : ℝ) ≤ (2 * y) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.norm_of_nonneg (by positivity)]
    calc M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)
        = M_err * ((1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) := by ring
      _ ≤ M_err * ((2 * y) ^ (5 / 2 : ℝ) * Real.exp (-(1 / 24 : ℝ) * y)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hrpow_le (Real.exp_le_exp.mpr hexp_le) (Real.exp_pos _).le (by positivity))
            hM_err_nn
  obtain ⟨Y₁, hY₁⟩ := eventually_atTop.mp
    (hlim_err.eventually (gt_mem_nhds (mul_pos (half_pos hb_pos) hc_J_pos)))
  have hB₁_lap_lb : ∀ y : ℝ, max Y₁ 1 ≤ y →
      ((b / 2) * c_J) * (1 + y) ^ (-(5 / 2 : ℝ)) ≤ airyLaplace (fun u => (B₁ (u : ℂ)).re) y := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (by norm_num) ((le_max_right Y₁ 1).trans hy)
    have hyY₁ : Y₁ ≤ y := (le_max_left _ _).trans hy
    have hF_y : Integrable (fun u : ℝ => (B₁ (u : ℂ)).re * Real.exp (y * u)) :=
      hB₁_cl.integrable_exp_nonneg hy0
    have hJ_y : Integrable (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) :=
      airyRefJ0_inAiryClass.integrable_exp_nonneg hy0
    have hg_y : Integrable (fun u : ℝ => g_err u * Real.exp (y * u)) := by
      have heq : (fun u : ℝ => g_err u * Real.exp (y * u)) =
          fun u : ℝ => (B₁ (u : ℂ)).re * Real.exp (y * u) -
            b * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ext u; dsimp [g_err]; ring
      rw [heq]; exact hF_y.sub (hJ_y.const_mul b)
    have hsplit_g : (∫ u : ℝ, g_err u * Real.exp (y * u)) =
        (∫ u in Iic U, g_err u * Real.exp (y * u)) + ∫ u in Ioi U, g_err u * Real.exp (y * u) := by
      rw [← compl_Iic]
      exact (integral_add_compl measurableSet_Iic hg_y).symm
    have hIoi_nn : 0 ≤ ∫ u in Ioi U, g_err u * Real.exp (y * u) :=
      setIntegral_nonneg measurableSet_Ioi fun u (hu : U < u) =>
        mul_nonneg (by dsimp [g_err]; linarith [htail_ge u hu.le]) (Real.exp_pos _).le
    have hIic_lb : -M_err * Real.exp (y * U) ≤ ∫ u in Iic U, g_err u * Real.exp (y * u) := by
      have h1 : (∫ u in Iic U, -(g_err u * Real.exp (y * u))) ≤
          ∫ u in Iic U, |g_err u| * Real.exp (y * U) := by
        refine setIntegral_mono_on hg_y.neg.integrableOn (hg_err_int.abs.mul_const _).integrableOn
          measurableSet_Iic fun u (hu : u ≤ U) => ?_
        have hexp : Real.exp (y * u) ≤ Real.exp (y * U) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hy0)
        nlinarith [neg_abs_le (g_err u), Real.exp_pos (y * u), abs_nonneg (g_err u)]
      have h2 : (∫ u in Iic U, |g_err u| * Real.exp (y * U)) ≤ M_err * Real.exp (y * U) := by
        rw [integral_mul_const]
        exact mul_le_mul_of_nonneg_right
          (setIntegral_le_integral hg_err_int.abs (Eventually.of_forall fun _ => abs_nonneg _))
          (Real.exp_pos _).le
      rw [integral_neg] at h1
      linarith
    have hg_int_eq : (∫ u : ℝ, g_err u * Real.exp (y * u)) =
        (∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u)) -
          b * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u) := by
      have heq : (fun u : ℝ => g_err u * Real.exp (y * u)) =
          fun u : ℝ => (B₁ (u : ℂ)).re * Real.exp (y * u) -
            b * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ext u; dsimp [g_err]; ring
      rw [heq, integral_sub hF_y (hJ_y.const_mul b), integral_const_mul]
    have hdiff_lap : -M_err * Real.exp (y * U - y ^ 3 / 12) ≤
        airyLaplace (fun u => (B₁ (u : ℂ)).re) y -
          b * airyLaplace (fun u => (airyRefJ0 (u : ℂ)).re) y := by
      unfold airyLaplace
      have hexp_split : Real.exp (y * U - y ^ 3 / 12) =
          Real.exp (-y ^ 3 / 12) * Real.exp (y * U) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp_split]
      have hmul_lb := mul_le_mul_of_nonneg_left
        (by linarith : -M_err * Real.exp (y * U) ≤
          (∫ u : ℝ, (B₁ (u : ℂ)).re * Real.exp (y * u)) -
            b * ∫ u : ℝ, (airyRefJ0 (u : ℂ)).re * Real.exp (y * u))
        (Real.exp_pos (-y ^ 3 / 12)).le
      linarith
    have herr_lt := hY₁ y hyY₁
    have h1y_pos : 0 < (1 + y) ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    have hrpow_inv : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith : 0 < 1 + y)]; norm_num
    have herr_small : M_err * Real.exp (y * U - y ^ 3 / 12) <
        ((b / 2) * c_J) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      have h1y_neg_pos : 0 < (1 + y) ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
      have hmul : (M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12)) *
          (1 + y) ^ (-(5 / 2 : ℝ)) < ((b / 2) * c_J) * (1 + y) ^ (-(5 / 2 : ℝ)) :=
        mul_lt_mul_of_pos_right herr_lt h1y_neg_pos
      have lhs_eq : M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12) *
          (1 + y) ^ (-(5 / 2 : ℝ)) = M_err * Real.exp (y * U - y ^ 3 / 12) := by
        calc M_err * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (y * U - y ^ 3 / 12) *
              (1 + y) ^ (-(5 / 2 : ℝ))
            = M_err * Real.exp (y * U - y ^ 3 / 12) *
                ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by ring
          _ = M_err * Real.exp (y * U - y ^ 3 / 12) := by rw [hrpow_inv, mul_one]
      rwa [lhs_eq] at hmul
    have hJ_lb := mul_le_mul_of_nonneg_left (hJ_lap_bd y hy0).1 hb_pos.le
    linarith
  -- 4. Choose `ε > 0` small so `B = B_sh + ε B₁ < 0` on `shellSites D`, then pick `Y_B` large.
  have hex_eps : ∃ ε : ℝ, 0 < ε ∧
      ∀ t ∈ shellSites D, (B_sh (t : ℂ)).re + ε * (B₁ (t : ℂ)).re < 0 := by
    by_cases hne_sites : (shellSites D).Nonempty
    · have hatt_ne : (shellSites D).attach.Nonempty := Finset.attach_nonempty_iff.mpr hne_sites
      let ratio_fn : {x // x ∈ shellSites D} → ℝ := fun t =>
        (-(B_sh (t.1 : ℂ)).re) / (|(B₁ (t.1 : ℂ)).re| + 1)
      have hratio_pos : ∀ t : {x // x ∈ shellSites D}, 0 < ratio_fn t := by
        intro t
        dsimp [ratio_fn]
        rw [hB_sh_re t.1]
        have hneg := hs_sites t.1 t.2
        exact div_pos (by linarith) (by positivity)
      let ε : ℝ := ((shellSites D).attach.inf' hatt_ne ratio_fn) / 2
      have hε_pos : 0 < ε := half_pos ((Finset.lt_inf'_iff _).mpr fun t _ => hratio_pos t)
      refine ⟨ε, hε_pos, fun t ht => ?_⟩
      have hε_lt : ε < ratio_fn ⟨t, ht⟩ :=
        lt_of_lt_of_le (half_lt_self ((Finset.lt_inf'_iff _).mpr fun x _ => hratio_pos x))
          (Finset.inf'_le _ (Finset.mem_attach _ ⟨t, ht⟩))
      dsimp [ratio_fn] at hε_lt
      have hden_pos : 0 < |(B₁ (t : ℂ)).re| + 1 := by positivity
      have hmul := (lt_div_iff₀ hden_pos).mp hε_lt
      have habs := le_abs_self ((B₁ (t : ℂ)).re)
      nlinarith
    · exact ⟨1, one_pos, fun t ht => absurd ⟨t, ht⟩ hne_sites⟩
  obtain ⟨ε, hε_pos, hε_sites⟩ := hex_eps
  let B : ℂ → ℂ := fun z => B_sh z + (ε : ℂ) * B₁ z
  have hB_cl : InAiryClass B := hB_sh_cl.add (hB₁_cl.smul ε)
  have hB_re : ∀ u : ℝ, (B (u : ℂ)).re = (B_sh (u : ℂ)).re + ε * (B₁ (u : ℂ)).re := by
    intro u; dsimp [B]; simp [Complex.mul_re, hB₁_cl.2.2.2 u]
  have hB_left : ∀ u : ℝ, u ≤ v₁ → (B (u : ℂ)).re < 0 := by
    intro u hu
    rw [hB_re u]
    linarith [hB_sh_left u hu, mul_nonpos_of_nonneg_of_nonpos hε_pos.le (hB₁_left u hu)]
  have hB_sites : ∀ t ∈ shellSites D, (B (t : ℂ)).re < 0 := by
    intro t ht; rw [hB_re t]; exact hε_sites t ht
  have hB_lap0 : 0 < laplaceL (fun u => (B (u : ℂ)).re) 0 := by
    unfold laplaceL
    simp only [zero_mul, Real.exp_zero, mul_one]
    simp_rw [hB_re]
    have hsh_int : Integrable (fun u : ℝ => (B_sh (u : ℂ)).re) := by
      simpa [RCLike.re_to_complex] using hB_sh_cl.2.1.re
    have hB1_int : Integrable (fun u : ℝ => ε * (B₁ (u : ℂ)).re) := by
      simpa [RCLike.re_to_complex] using hB₁_cl.2.1.re.const_mul ε
    rw [integral_add hsh_int hB1_int, integral_const_mul, hB_sh_int]
    linarith [mul_pos hε_pos hB₁_int_pos]
  -- Large-`y` domination: `M_B0 * (1 + y)^{5/2} * exp(-s_sh * y) → 0`.
  have hlim_sh : Tendsto (fun y : ℝ => M_B0 * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => (2 * y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y)) atTop (𝓝 0) := by
      have ha := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (5 / 2 : ℝ) s_sh hs_pos
      have hb := ha.const_mul ((2 : ℝ) ^ (5 / 2 : ℝ))
      rw [mul_zero] at hb
      refine hb.congr' ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy0
      rw [Real.mul_rpow (by norm_num) hy0, mul_assoc, neg_mul]
    have h2 := h1.const_mul M_B0
    rw [mul_zero] at h2
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy1
    have hrpow_le : (1 + y) ^ (5 / 2 : ℝ) ≤ (2 * y) ^ (5 / 2 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    rw [Real.norm_of_nonneg (by positivity)]
    calc M_B0 * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y)
        = M_B0 * ((1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y)) := by ring
      _ ≤ M_B0 * ((2 * y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hrpow_le (Real.exp_pos _).le) hMB0_nn
  let c_tail : ℝ := ε * ((b / 2) * c_J)
  have hc_tail_pos : 0 < c_tail := by positivity
  obtain ⟨Y₂, hY₂⟩ := eventually_atTop.mp (hlim_sh.eventually (gt_mem_nhds hc_tail_pos))
  let Y_B : ℝ := max (max Y₁ 1) Y₂
  have hYB_pos : 0 < Y_B := lt_of_lt_of_le zero_lt_one ((le_max_right Y₁ 1).trans (le_max_left _ _))
  refine ⟨B, Y_B, hB_cl, hYB_pos, hB_left, hB_sites, hB_lap0, fun y hy => ?_⟩
  have hy0 : 0 ≤ y := (hYB_pos.trans_le hy).le
  have hy_Y₁1 : max Y₁ 1 ≤ y := (le_max_left _ _).trans hy
  have hy_Y₂ : Y₂ ≤ y := (le_max_right _ _).trans hy
  have hsh_small : Real.exp (-s_sh * y) * M_B0 < c_tail * (1 + y) ^ (-(5 / 2 : ℝ)) := by
    have hlt := hY₂ y hy_Y₂
    have h1y_neg_pos : 0 < (1 + y) ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hmul : (M_B0 * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y)) *
        (1 + y) ^ (-(5 / 2 : ℝ)) < c_tail * (1 + y) ^ (-(5 / 2 : ℝ)) :=
      mul_lt_mul_of_pos_right hlt h1y_neg_pos
    have hrpow_inv : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by linarith : 0 < 1 + y)]; norm_num
    have lhs_eq : M_B0 * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y) *
        (1 + y) ^ (-(5 / 2 : ℝ)) = Real.exp (-s_sh * y) * M_B0 := by
      calc M_B0 * (1 + y) ^ (5 / 2 : ℝ) * Real.exp (-s_sh * y) * (1 + y) ^ (-(5 / 2 : ℝ))
          = (Real.exp (-s_sh * y) * M_B0) *
              ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by ring
        _ = Real.exp (-s_sh * y) * M_B0 := by rw [hrpow_inv, mul_one]
    rwa [lhs_eq] at hmul
  have hlap_B_add : airyLaplace (fun u => (B (u : ℂ)).re) y =
      airyLaplace (fun u => (B_sh (u : ℂ)).re) y +
        ε * airyLaplace (fun u => (B₁ (u : ℂ)).re) y := by
    unfold airyLaplace
    simp_rw [hB_re, add_mul, mul_assoc]
    rw [integral_add (hB_sh_cl.integrable_exp_nonneg hy0)
      ((hB₁_cl.integrable_exp_nonneg hy0).const_mul ε), integral_const_mul]
    ring
  have hB₁_lb := mul_le_mul_of_nonneg_left (hB₁_lap_lb y hy_Y₁1) hε_pos.le
  have hB_sh_lb : -(Real.exp (-s_sh * y) * M_B0) ≤ airyLaplace (fun u => (B_sh (u : ℂ)).re) y :=
    neg_le_of_abs_le (hB_sh_lap_abs y hy0)
  have hairy_pos : 0 < airyLaplace (fun u => (B (u : ℂ)).re) y := by
    rw [hlap_B_add]
    dsimp [c_tail] at hsh_small
    linarith
  unfold airyLaplace at hairy_pos
  unfold laplaceL
  exact pos_of_mul_pos_right hairy_pos (Real.exp_pos _).le

/-! ### `lem:airy-active-height` (1)–(4) (`ce_airy_lp_proofs.tex` lines 139–212) -/

/-- **`lem:airy-active-height` (1), general buffer form (`ce_airy_lp_proofs.tex`, lines 142–147):**
given a weak witness `H` at `v` and a buffer `B` at `v₁ > v` (`B < 0` on `(-∞, v₁]` and on
`shellSites D`, `L_B(0) > 0`, `L_B(y) > 0` for `y ≥ Y_B`) such that `L_B(y) > 0` at every `y > 0`
where `L_H(y) = 0`, we have `(v : EReal) < uSh D`. -/
theorem airy_active_height_strictify_buffer (D : ShellHBData) {v v₁ Y_B : ℝ} (hvv₁ : v < v₁)
    {H B : ℂ → ℂ} (hH : OneProfileFeasibleWitness D v H) (hB_cl : InAiryClass B)
    (_hYB : 0 < Y_B) (hB_left : ∀ u : ℝ, u ≤ v₁ → (B (u : ℂ)).re < 0)
    (hB_sites : ∀ t ∈ shellSites D, (B (t : ℂ)).re < 0)
    (hB_lap0 : 0 < laplaceL (fun u => (B (u : ℂ)).re) 0)
    (hB_large : ∀ y : ℝ, Y_B ≤ y → 0 < laplaceL (fun u => (B (u : ℂ)).re) y)
    (h_no_common_zero : ∀ y : ℝ, 0 < y → laplaceL (fun u => (H (u : ℂ)).re) y = 0 →
      0 < laplaceL (fun u => (B (u : ℂ)).re) y) :
    (v : EReal) < uSh D := by
  let L_H : ℝ → ℝ := laplaceL (fun u => (H (u : ℂ)).re)
  let L_B : ℝ → ℝ := laplaceL (fun u => (B (u : ℂ)).re)
  have hLH_cont : ContinuousOn L_H (Ici 0) := hH.1.laplace_continuousOn_Ici
  have hLB_cont : ContinuousOn L_B (Ici 0) := hB_cl.laplace_continuousOn_Ici
  -- Compact set `K_neg = {y ∈ [0, Y_B] | L_B(y) ≤ 0}`; on `K_neg`, `y > 0` so `L_H(y) > 0`.
  let K_neg : Set ℝ := {y ∈ Icc 0 Y_B | L_B y ≤ 0}
  have hK_compact : IsCompact K_neg := by
    have heq : K_neg = Icc 0 Y_B ∩ (Ici 0 ∩ {y | L_B y ≤ 0}) := by
      ext y; simp only [K_neg, mem_ofPred_eq, mem_inter_iff, mem_Icc, mem_Ici]
      exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, h1, h3⟩, fun ⟨h12, _, h3⟩ => ⟨h12, h3⟩⟩
    rw [heq]
    refine isCompact_Icc.inter_right ?_
    exact hLB_cont.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic
  have hLH_pos_on_K : ∀ y ∈ K_neg, 0 < L_H y := by
    intro y ⟨hy_Icc, hy_le⟩
    have hy_pos : 0 < y := by
      rcases hy_Icc.1.eq_or_lt with rfl | hpos
      · exact absurd hy_le (not_le.mpr hB_lap0)
      · exact hpos
    have hLH_nn : 0 ≤ L_H y := hH.2.2.2.2 y hy_pos.le
    rcases hLH_nn.eq_or_lt with h0 | hpos
    · exact absurd (h_no_common_zero y hy_pos h0.symm) (not_lt.mpr hy_le)
    · exact hpos
  have hLH_nn_all : ∀ y : ℝ, 0 ≤ y → 0 ≤ L_H y := fun y hy => hH.2.2.2.2 y hy
  -- Choose `η > 0` such that `L_H y + η * L_B y > 0` for ALL `y ≥ 0`.
  have hex_eta : ∃ η : ℝ, 0 < η ∧ ∀ y : ℝ, 0 ≤ y → 0 < L_H y + η * L_B y := by
    by_cases hKne : K_neg.Nonempty
    · obtain ⟨y_min, hy_minK, hy_min⟩ :=
        hK_compact.exists_isMinOn hKne (hLH_cont.mono (fun y hy => hy.1.1))
      have hm_pos : 0 < L_H y_min := hLH_pos_on_K y_min hy_minK
      obtain ⟨y_lo, hy_loK, hy_lo⟩ :=
        hK_compact.exists_isMinOn hKne (hLB_cont.mono (fun y hy => hy.1.1))
      let M_neg : ℝ := |L_B y_lo| + 1
      have hM_pos : 0 < M_neg := by positivity
      let η : ℝ := L_H y_min / (2 * M_neg)
      have hη_pos : 0 < η := by positivity
      refine ⟨η, hη_pos, fun y hy => ?_⟩
      by_cases hy_gt : Y_B ≤ y
      · have hB_pos : 0 < L_B y := hB_large y hy_gt
        linarith [hLH_nn_all y hy, mul_pos hη_pos hB_pos]
      · by_cases hLB_pos : 0 < L_B y
        · linarith [hLH_nn_all y hy, mul_pos hη_pos hLB_pos]
        · have hyK : y ∈ K_neg := ⟨⟨hy, (not_le.mp hy_gt).le⟩, not_lt.mp hLB_pos⟩
          have h1 : L_H y_min ≤ L_H y := hy_min hyK
          have h2 : L_B y_lo ≤ L_B y := hy_lo hyK
          have h3 : -M_neg ≤ L_B y := by
            dsimp [M_neg]
            linarith [neg_abs_le (L_B y_lo)]
          have h4 : -(L_H y_min / 2) ≤ η * L_B y := by
            have hmul := mul_le_mul_of_nonneg_left h3 hη_pos.le
            have hcancel : η * (-M_neg) = -(L_H y_min / 2) := by
              dsimp [η]; field_simp [hM_pos.ne']
            rwa [hcancel] at hmul
          linarith
    · refine ⟨1, one_pos, fun y hy => ?_⟩
      by_cases hy_gt : Y_B ≤ y
      · have hB_pos : 0 < L_B y := hB_large y hy_gt
        linarith [hLH_nn_all y hy, hB_pos]
      · have hLB_pos : 0 < L_B y := by
          by_contra hle
          exact hKne ⟨y, ⟨hy, (not_le.mp hy_gt).le⟩, not_lt.mp hle⟩
        linarith [hLH_nn_all y hy, hLB_pos]
  obtain ⟨η, hη_pos, hη_lap⟩ := hex_eta
  let W : ℂ → ℂ := fun z => H z + (η : ℂ) * B z
  have hW_cl : InAiryClass W := hH.1.add (hB_cl.smul η)
  have hW_re : ∀ u : ℝ, (W (u : ℂ)).re = (H (u : ℂ)).re + η * (B (u : ℂ)).re := by
    intro u; dsimp [W]; simp [Complex.mul_re, hB_cl.2.2.2 u]
  have hW_v_neg : (W (v : ℂ)).re < 0 := by
    rw [hW_re v]
    linarith [hH.2.2.2.1 v le_rfl, mul_neg_of_pos_of_neg hη_pos (hB_left v hvv₁.le)]
  -- Continuity of `W` at `v` extends `< 0` to `(-∞, v']` for some `v' ∈ (v, v₁)`.
  have hW_cont : Continuous (fun u : ℝ => (W (u : ℂ)).re) :=
    Complex.continuous_re.comp (hW_cl.1.continuous.comp Complex.continuous_ofReal)
  obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hW_cont.continuousAt (x := v))
    (-(W (v : ℂ)).re / 2) (by linarith)
  let v' : ℝ := v + min (δ / 2) ((v₁ - v) / 2)
  have hv_lt_v' : v < v' := by
    dsimp [v']
    have : 0 < min (δ / 2) ((v₁ - v) / 2) := lt_min (half_pos hδ_pos) (by linarith)
    linarith
  have hv'_le_v₁ : v' ≤ v₁ := by
    dsimp [v']
    have : min (δ / 2) ((v₁ - v) / 2) ≤ (v₁ - v) / 2 := min_le_right _ _
    linarith
  have hW_left_v' : ∀ u : ℝ, u ≤ v' → (W (u : ℂ)).re < 0 := by
    intro u hu
    rcases le_or_gt u v with huv | huv
    · rw [hW_re u]
      linarith [hH.2.2.2.1 u huv, mul_neg_of_pos_of_neg hη_pos (hB_left u (huv.trans hvv₁.le))]
    · have hdist : dist u v < δ := by
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr huv)]
        have : min (δ / 2) ((v₁ - v) / 2) < δ :=
          lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ_pos)
        dsimp [v'] at hu
        linarith
      have hd := abs_lt.mp (by simpa [Real.dist_eq] using hδ hdist)
      linarith
  have hW_nz : ∃ z : ℂ, W z ≠ 0 := by
    refine ⟨(v : ℂ), fun h0 => ?_⟩
    rw [h0, Complex.zero_re] at hW_v_neg
    exact lt_irrefl 0 hW_v_neg
  have hW_sites : ∀ t ∈ D.S, t ≠ D.tm → (W (t : ℂ)).re < 0 := by
    intro t htS htm
    rw [hW_re t]
    have ht_sh : t ∈ shellSites D := Finset.mem_erase.2 ⟨htm, htS⟩
    linarith [hH.2.2.1 t htS htm, mul_neg_of_pos_of_neg hη_pos (hB_sites t ht_sh)]
  have hW_lap_nn : ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u : ℝ, (W (u : ℂ)).re * Real.exp (y * u) := by
    intro y hy
    simp_rw [hW_re, add_mul, mul_assoc]
    rw [integral_add (hH.1.integrable_exp_nonneg hy) ((hB_cl.integrable_exp_nonneg hy).const_mul η),
      integral_const_mul]
    exact (hη_lap y hy).le
  have hstrict : OneProfileStrictFeasible D v' :=
    ⟨W, ⟨hW_cl, hW_nz, fun t ht htm => (hW_sites t ht htm).le,
      fun u hu => (hW_left_v' u hu).le, hW_lap_nn⟩, hW_sites⟩
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hv_lt_v')
    (le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileStrictFeasible D u) => (u : EReal)) v' hstrict)

/-- Real-analytic function `f ≥ 0` on `(0, ∞)` not identically zero near `y > 0` with `f y = 0`
has `Even (analyticOrderNatAt f y)` and `deriv f y = 0`. -/
private lemma even_analyticOrderNatAt_of_nonneg {f : ℝ → ℝ} {y : ℝ} (hy : 0 < y)
    (hf_an : AnalyticAt ℝ f y) (hnot_ev0 : ¬ (f =ᶠ[𝓝 y] 0))
    (hf_nn : ∀ t : ℝ, 0 < t → 0 ≤ f t) (hfy : f y = 0) :
    Even (analyticOrderNatAt f y) ∧ deriv f y = 0 := by
  have hmin : IsLocalMin f y := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    rw [hfy]
    exact hf_nn t ht
  have hderiv0 : deriv f y = 0 := hmin.deriv_eq_zero
  have hne_top : analyticOrderAt f y ≠ ⊤ := mt analyticOrderAt_eq_top.mp hnot_ev0
  set n : ℕ := analyticOrderNatAt f y
  have hord : analyticOrderAt f y = (n : ℕ∞) := (Nat.cast_analyticOrderNatAt hne_top).symm
  obtain ⟨g, hg_an, hg_ne, hfg⟩ := (hf_an.analyticOrderAt_eq_natCast).mp hord
  refine ⟨?_, hderiv0⟩
  by_contra hn_not_even
  have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_not_even
  -- Near `y`, `f x = (x - y)^n * g x` and `g` has the sign of `g y ≠ 0`.
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := Metric.eventually_nhds_iff.mp hfg
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ := Metric.continuousAt_iff.mp hg_an.continuousAt
    (|g y| / 2) (half_pos (abs_pos.mpr hg_ne))
  let r : ℝ := min (y / 2) (min (δ₁ / 2) (δ₂ / 2))
  have hr_pos : 0 < r :=
    lt_min (half_pos hy) (lt_min (half_pos hδ₁_pos) (half_pos hδ₂_pos))
  have hr_lt_y : r < y := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hy)
  have hr_lt_1 : r < δ₁ :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _)) (half_lt_self hδ₁_pos)
  have hr_lt_2 : r < δ₂ :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (half_lt_self hδ₂_pos)
  have hf_plus : f (y + r) = r ^ n * g (y + r) := by
    have h := hδ₁ (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hr_pos]; exact hr_lt_1)
    simpa [smul_eq_mul] using h
  have hf_minus : f (y - r) = -(r ^ n * g (y - r)) := by
    have h := hδ₁ (by rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hr_pos]; exact hr_lt_1)
    have hsub : y - r - y = -r := by ring
    rw [hsub, hn_odd.neg_pow, smul_eq_mul, neg_mul] at h
    exact h
  have hg_plus_close := abs_lt.mp (by
    simpa [Real.dist_eq] using hδ₂ (x := y + r)
      (by rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hr_pos]; exact hr_lt_2))
  have hg_minus_close := abs_lt.mp (by
    simpa [Real.dist_eq] using hδ₂ (x := y - r)
      (by rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hr_pos]; exact hr_lt_2))
  have hrn_pos : 0 < r ^ n := pow_pos hr_pos n
  have hnn_plus : 0 ≤ f (y + r) := hf_nn (y + r) (by linarith)
  have hnn_minus : 0 ≤ f (y - r) := hf_nn (y - r) (by linarith)
  rcases lt_trichotomy (g y) 0 with hgy_neg | hgy0 | hgy_pos
  · rw [abs_of_neg hgy_neg] at hg_plus_close
    have hg_neg : g (y + r) < 0 := by linarith
    have : f (y + r) < 0 := by rw [hf_plus]; exact mul_neg_of_pos_of_neg hrn_pos hg_neg
    linarith
  · exact hg_ne hgy0
  · rw [abs_of_pos hgy_pos] at hg_minus_close
    have hg_pos : 0 < g (y - r) := by linarith
    have : f (y - r) < 0 := by rw [hf_minus]; linarith [mul_pos hrn_pos hg_pos]
    linarith

/-- Sum of two weak witnesses at the same cutoff `b` is a weak witness at `b`. -/
private lemma oneProfileFeasibleWitness_add {D : ShellHBData} {b : ℝ} {H₁ H₂ : ℂ → ℂ}
    (h₁ : OneProfileFeasibleWitness D b H₁) (h₂ : OneProfileFeasibleWitness D b H₂) :
    OneProfileFeasibleWitness D b (fun z => H₁ z + H₂ z) := by
  refine ⟨h₁.1.add h₂.1, ?_, ?_, ?_, ?_⟩
  · -- Non-vanishing: if `H₁ + H₂ = 0`, then on `(-∞, b]` both `≤ 0` force `H₁ = 0`, contradiction!
    by_contra hall0
    push Not at hall0
    have hH₁_ivl : ∀ x : ℝ, b - 2 < x → x < b - 1 → H₁ (x : ℂ) = 0 := by
      intro x _ hx2
      have hxb : x ≤ b := by linarith
      have hsum_re : (H₁ (x : ℂ)).re + (H₂ (x : ℂ)).re = 0 := by
        have h := congrArg Complex.re (hall0 (x : ℂ))
        simpa using h
      have h1 := h₁.2.2.2.1 x hxb
      have h2 := h₂.2.2.2.1 x hxb
      exact Complex.ext (by rw [Complex.zero_re]; linarith) (by rw [Complex.zero_im]; exact h₁.1.2.2.2 x)
    have hH₁_0 := airy_entire_eq_zero_of_real_interval h₁.1.1 (by linarith : b - 2 < b - 1) hH₁_ivl
    obtain ⟨z₀, hz₀⟩ := h₁.2.1
    exact hz₀ (hH₁_0 z₀)
  · intro t ht htm
    rw [Complex.add_re]
    linarith [h₁.2.2.1 t ht htm, h₂.2.2.1 t ht htm]
  · intro u hu
    rw [Complex.add_re]
    linarith [h₁.2.2.2.1 u hu, h₂.2.2.2.1 u hu]
  · intro y hy
    simp_rw [Complex.add_re, add_mul]
    rw [integral_add (h₁.1.integrable_exp_nonneg hy) (h₂.1.integrable_exp_nonneg hy)]
    exact add_nonneg (h₁.2.2.2.2 y hy) (h₂.2.2.2.2 y hy)

private lemma uLP_le_tm_aux (D : ShellHBData) : uLP D ≤ (D.tm : EReal) :=
  iSup₂_le fun u hu => EReal.coe_le_coe_iff.2 ((one_profile_threshold_le_and_endpoint_iff D).1 u hu)

private lemma uSh_le_uLP_aux (D : ShellHBData) : uSh D ≤ uLP D :=
  iSup₂_le fun u ⟨H, hH, _⟩ =>
    le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) u ⟨H, hH⟩

/-- **`lem:airy-active-height` (`ce_airy_lp_proofs.tex` lines 139–212), proved unconditionally:**
instantiates `AiryActiveHeight D` for every `D : ShellHBData` (discharging the former
`active_height` field of `CeCanonicalInputs`). -/
theorem airy_active_height (D : ShellHBData) : AiryActiveHeight D := by
  -- Part (1): strictify
  have h_strictify : ∀ v : ℝ, v < D.tm → ∀ H : ℂ → ℂ, OneProfileFeasibleWitness D v H →
      (∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (H (u : ℂ)).re) y) → (v : EReal) < uSh D := by
    intro v hv H hH hLpos
    let v₁ : ℝ := (v + D.tm) / 2
    obtain ⟨B, Y_B, hB_cl, hYB, hB_left, hB_sites, hB_lap0, hB_large⟩ :=
      exists_airy_shell_buffer D (v₁ := v₁) (by dsimp [v₁]; linarith)
    refine airy_active_height_strictify_buffer D (by dsimp [v₁]; linarith : v < v₁) hH
      hB_cl hYB hB_left hB_sites hB_lap0 hB_large fun y hy h0 => ?_
    exact absurd h0 (hLpos y hy).ne'
  refine ⟨h_strictify, ?_, ?_, ?_⟩
  -- Part (2): common positive Laplace zero of even order when `u_LP < t_m`
  · intro hlt_tm
    -- First show `uLP D` is attained at some `b₀ < D.tm` (`airySquareAttained` gives feasibility).
    obtain ⟨q₀, -, -, -, -, hwit₀, -, -⟩ := (airySquareAttained D).witness
    have hbot : uLP D ≠ ⊥ := by
      have hle : ((airyLambdaOf (shellSites D) : ℝ) : EReal) ≤ uLP D :=
        le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal))
          (airyLambdaOf (shellSites D)) ⟨_, hwit₀⟩
      intro h0; rw [h0] at hle; exact EReal.coe_ne_bot _ (le_bot_iff.mp hle)
    have htop : uLP D ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hlt_tm.le
    let b₀ : ℝ := (uLP D).toReal
    have hb₀_eq : uLP D = (b₀ : EReal) := (EReal.coe_toReal htop hbot).symm
    have hb₀_lt : b₀ < D.tm := EReal.coe_lt_coe_iff.mp (hb₀_eq ▸ hlt_tm)
    -- Attainment of `OneProfileFeasible D b₀`.
    obtain ⟨C_env, ν_env, hC_env, hbound_env⟩ :=
      one_profile_envelope_aux D (airyLambdaOf (shellSites D)) ⟨_, hwit₀⟩
    obtain ⟨u_s, hu_s_feas, hu_s_max⟩ := one_profile_maximizer_exists D
      { u₀ := airyLambdaOf (shellSites D)
        u₀_feasible := ⟨_, hwit₀⟩
        C₀ := C_env
        ν₀ := ν_env
        hC₀ := hC_env
        uniform_env := fun {u H} hu hH hn z => hbound_env u hu H hH hn z }
    have hus_eq : (u_s : EReal) = uLP D :=
      le_antisymm
        (le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) u_s hu_s_feas)
        (iSup₂_le fun u hu => EReal.coe_le_coe_iff.mpr (hu_s_max hu))
    have hus_b₀ : u_s = b₀ := EReal.coe_injective (hus_eq.trans hb₀_eq)
    rw [hus_b₀] at hu_s_feas
    obtain ⟨H₀, hH₀⟩ := hu_s_feas
    -- Choose a buffer `B` at `v₁ = (b₀ + D.tm) / 2`.
    let v₁ : ℝ := (b₀ + D.tm) / 2
    obtain ⟨B, Y_B, hB_cl, hYB, hB_left, hB_sites, hB_lap0, hB_large⟩ :=
      exists_airy_shell_buffer D (v₁ := v₁) (by dsimp [v₁]; linarith)
    let L_B : ℝ → ℝ := laplaceL (fun u => (B (u : ℂ)).re)
    let K_neg : Set ℝ := {y ∈ Icc 0 Y_B | L_B y ≤ 0}
    have hK_compact : IsCompact K_neg := by
      have heq : K_neg = Icc 0 Y_B ∩ (Ici 0 ∩ {y | L_B y ≤ 0}) := by
        ext y; simp only [K_neg, mem_ofPred_eq, mem_inter_iff, mem_Icc, mem_Ici]
        exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨h1, h2⟩, h1, h3⟩, fun ⟨h12, _, h3⟩ => ⟨h12, h3⟩⟩
      rw [heq]
      exact isCompact_Icc.inter_right
        (hB_cl.laplace_continuousOn_Ici.preimage_isClosed_of_isClosed isClosed_Ici isClosed_Iic)
    -- Compactness + finite subcover: there exists `ystar ∈ K_neg` where EVERY optimizer at `b₀` vanishes!
    let Opt := {H : ℂ → ℂ // OneProfileFeasibleWitness D b₀ H}
    have hex_common : ∃ y ∈ K_neg, ∀ H : Opt, laplaceL (fun u => (H.1 (u : ℂ)).re) y = 0 := by
      by_contra hno
      push Not at hno
      -- For each `y ∈ K_neg`, `y > 0`, and `hno y` gives `H_y : Opt` with `L_{H_y}(y) > 0`.
      let U_open : Opt → Set ℝ := fun H => Ioi 0 ∩ {w : ℝ | 0 < laplaceL (fun u => (H.1 (u : ℂ)).re) w}
      have hU_open : ∀ H : Opt, IsOpen (U_open H) := by
        intro H
        have hcont : ContinuousOn (laplaceL (fun u => (H.1 (u : ℂ)).re)) (Ioi 0) :=
          H.2.1.laplace_continuousOn_Ici.mono Ioi_subset_Ici_self
        exact hcont.isOpen_inter_preimage isOpen_Ioi isOpen_Ioi
      have hcover : K_neg ⊆ ⋃ H : Opt, U_open H := by
        intro y hyK
        have hy_pos : 0 < y := by
          rcases hyK.1.1.eq_or_lt with rfl | hpos
          · exact absurd hyK.2 (not_le.mpr hB_lap0)
          · exact hpos
        obtain ⟨H_y, hne0⟩ := hno y hyK
        have hpos_L : 0 < laplaceL (fun u => (H_y.1 (u : ℂ)).re) y :=
          lt_of_le_of_ne (H_y.2.2.2.2.2 y hy_pos.le) (Ne.symm hne0)
        exact mem_iUnion.mpr ⟨H_y, hy_pos, hpos_L⟩
      obtain ⟨F_sub, hF_cover⟩ := hK_compact.elim_finite_subcover U_open hU_open hcover
      -- Finite sum `H_sum = H₀ + ∑_{H ∈ F_sub} H` is an optimizer at `b₀` with no zero in `K_neg`!
      have hex_sum : ∀ S_fin : Finset Opt, ∃ H_S : ℂ → ℂ,
          OneProfileFeasibleWitness D b₀ H_S ∧
          ∀ y : ℝ, 0 ≤ y → laplaceL (fun u => (H₀ (u : ℂ)).re) y +
            (∑ H ∈ S_fin, laplaceL (fun u => (H.1 (u : ℂ)).re) y) =
            laplaceL (fun u => (H_S (u : ℂ)).re) y := by
        classical
        intro S_fin
        induction S_fin using Finset.induction_on with
        | empty =>
          exact ⟨H₀, hH₀, fun y _ => by simp⟩
        | insert H_a S_rest ha ih =>
          obtain ⟨H_rest, hH_rest, hlap_rest⟩ := ih
          refine ⟨fun z => H_rest z + H_a.1 z, oneProfileFeasibleWitness_add hH_rest H_a.2,
            fun y hy => ?_⟩
          rw [Finset.sum_insert ha, ← add_assoc, add_right_comm (laplaceL _ y), hlap_rest y hy]
          unfold laplaceL
          simp_rw [Complex.add_re, add_mul]
          rw [integral_add (hH_rest.1.integrable_exp_nonneg hy) (H_a.2.1.integrable_exp_nonneg hy)]
      obtain ⟨H_sum, hH_sum, hlap_sum⟩ := hex_sum F_sub
      have h_strict := airy_active_height_strictify_buffer D (by dsimp [v₁]; linarith : b₀ < v₁)
        hH_sum hB_cl hYB hB_left hB_sites hB_lap0 hB_large fun y hy hsum0 => ?_
      · have hle_ulp : uSh D ≤ (b₀ : EReal) := hb₀_eq ▸ uSh_le_uLP_aux D
        exact absurd (h_strict.trans_le hle_ulp) (lt_irrefl _)
      · by_contra hLB_le
        have hy_lt : y < Y_B := by
          by_contra hy_ge
          exact hLB_le (hB_large y (not_lt.mp hy_ge))
        have hyK : y ∈ K_neg := ⟨⟨hy.le, hy_lt.le⟩, not_lt.mp hLB_le⟩
        obtain ⟨H_i, hHi_mem, hy_Ui⟩ := mem_iUnion₂.mp (hF_cover hyK)
        have hpos_i : 0 < laplaceL (fun u => (H_i.1 (u : ℂ)).re) y := hy_Ui.2
        have hsum_ge : laplaceL (fun u => (H_i.1 (u : ℂ)).re) y ≤
            ∑ H ∈ F_sub, laplaceL (fun u => (H.1 (u : ℂ)).re) y :=
          Finset.single_le_sum (fun H _ => H.2.2.2.2.2 y hy.le) hHi_mem
        have h0_nn : 0 ≤ laplaceL (fun u => (H₀ (u : ℂ)).re) y := hH₀.2.2.2.2 y hy.le
        have htot := hlap_sum y hy.le
        linarith
    obtain ⟨ystar, hystarK, hystar0⟩ := hex_common
    have hystar_pos : 0 < ystar := by
      rcases hystarK.1.1.eq_or_lt with rfl | hpos
      · exact absurd hystarK.2 (not_le.mpr hB_lap0)
      · exact hpos
    refine ⟨ystar, hystar_pos, fun b hb H hH => ?_⟩
    have hbb₀ : b = b₀ := EReal.coe_injective (hb.symm.trans hb₀_eq)
    subst hbb₀
    have hLy0 : laplaceL (fun u => (H (u : ℂ)).re) ystar = 0 := hystar0 ⟨H, hH⟩
    have han : AnalyticAt ℝ (laplaceL (fun u => (H (u : ℂ)).re)) ystar :=
      laplaceL_analyticAt hH.1 hystar_pos
    have hnot_ev0 : ¬ (laplaceL (fun u => (H (u : ℂ)).re) =ᶠ[𝓝 ystar] 0) := by
      intro hev
      obtain ⟨z₀, hz₀⟩ := hH.2.1
      exact hz₀ (laplaceL_eq_zero_of_eventuallyEq_zero hH.1 hystar_pos hev z₀)
    obtain ⟨heven, hderiv0⟩ := even_analyticOrderNatAt_of_nonneg hystar_pos han hnot_ev0
      (fun t ht => hH.2.2.2.2 t ht.le) hLy0
    exact ⟨han, heven, hLy0, hderiv0⟩
  -- Part (3): quotient_mass (`∫ H/(u - b) ≥ 0 ⇒ u_sh = b`, valid for all `b ≤ D.tm` including `b = D.tm`)
  · intro b hb H hH hmass_nn
    have hbtm : b ≤ D.tm := EReal.coe_le_coe_iff.mp (hb ▸ uLP_le_tm_aux D)
    -- First show `(H b).re = 0` by maximality of `b = uLP D`.
    have hHb0 : (H (b : ℂ)).re = 0 := by
      have hle0 : (H (b : ℂ)).re ≤ 0 := hH.2.2.2.1 b le_rfl
      refine le_antisymm hle0 ?_
      by_contra hneg
      push Not at hneg
      have hcont : Continuous (fun u : ℝ => (H (u : ℂ)).re) :=
        Complex.continuous_re.comp (hH.1.1.continuous.comp Complex.continuous_ofReal)
      obtain ⟨δ, hδ_pos, hδ⟩ := Metric.continuousAt_iff.mp (hcont.continuousAt (x := b))
        (-(H (b : ℂ)).re / 2) (by linarith)
      let b' : ℝ := b + δ / 2
      have hb_lt_b' : b < b' := by dsimp [b']; linarith
      have hH_b' : OneProfileFeasibleWitness D b' H := by
        refine ⟨hH.1, hH.2.1, hH.2.2.1, fun u hu => ?_, hH.2.2.2.2⟩
        rcases le_or_gt u b with hub | hub
        · exact hH.2.2.2.1 u hub
        · have hdist : dist u b < δ := by
            rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hub)]
            dsimp [b'] at hu; linarith
          have hd := abs_lt.mp (by simpa [Real.dist_eq] using hδ hdist)
          linarith
      have hle_ulp : (b' : EReal) ≤ uLP D :=
        le_iSup₂ (f := fun (u : ℝ) (_ : OneProfileFeasible D u) => (u : EReal)) b' ⟨H, hH_b'⟩
      rw [hb] at hle_ulp
      exact absurd (EReal.coe_le_coe_iff.mp hle_ulp) (not_le.mpr hb_lt_b')
    obtain ⟨hQb_cl, -, hQb_int_eq⟩ := deflation_inAiryClass hH.1 hHb0
    let Q_b : ℂ → ℂ := dslope H (b : ℂ)
    change InAiryClass Q_b at hQb_cl
    have hQb_mass : 0 ≤ ∫ u : ℝ, (Q_b (u : ℂ)).re := hQb_int_eq ▸ hmass_nn
    have hQb_lap_pos : ∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (Q_b (u : ℂ)).re) y :=
      fun y hy => deflation_laplace_pos hH.1 hH.2.1 hH.2.2.2.2 hHb0 hQb_mass hy
    -- For every `v < b` (`v < D.tm`), `H + ((b - v)/2) Q_b` is a weak witness at `v` with `L > 0`.
    have hv_lt_ush : ∀ v : ℝ, v < b → (v : EReal) < uSh D := by
      intro v hvb
      let τ : ℝ := (b - v) / 2
      have hτ_pos : 0 < τ := by dsimp [τ]; linarith
      let W : ℂ → ℂ := fun z => H z + (τ : ℂ) * Q_b z
      have hW_cl : InAiryClass W := hH.1.add (hQb_cl.smul τ)
      have hW_re : ∀ u : ℝ, (W (u : ℂ)).re = (H (u : ℂ)).re + τ * (Q_b (u : ℂ)).re := by
        intro u; dsimp [W]; simp [Complex.mul_re, hQb_cl.2.2.2 u]
      have hW_lap_pos : ∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (W (u : ℂ)).re) y := by
        intro y hy
        unfold laplaceL
        simp_rw [hW_re, add_mul, mul_assoc]
        rw [integral_add (hH.1.integrable_exp_nonneg hy.le)
          ((hQb_cl.integrable_exp_nonneg hy.le).const_mul τ), integral_const_mul]
        exact add_pos_of_nonneg_of_pos (hH.2.2.2.2 y hy.le) (mul_pos hτ_pos (hQb_lap_pos y hy))
      have hW_nz : ∃ z : ℂ, W z ≠ 0 := by
        by_contra hall0
        push Not at hall0
        have hpos1 := hW_lap_pos 1 one_pos
        unfold laplaceL at hpos1
        simp [hall0] at hpos1
      have hHb_c : H (b : ℂ) = 0 := Complex.ext hHb0 (hH.1.2.2.2 b)
      have hQb_of_ne : ∀ u : ℝ, u ≠ b → (Q_b (u : ℂ)).re = (H (u : ℂ)).re / (u - b) := by
        intro u hu
        have hne : (u : ℂ) ≠ (b : ℂ) := fun h => hu (Complex.ofReal_injective h)
        dsimp [Q_b]
        rw [dslope_of_ne _ hne, slope_def_field, hHb_c, sub_zero]
        have hHu : H (u : ℂ) = (((H (u : ℂ)).re : ℝ) : ℂ) :=
          Complex.ext (by simp) (by simp [hH.1.2.2.2 u])
        conv_lhs => rw [hHu]
        rw [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
      have hW_sites : ∀ t ∈ D.S, t ≠ D.tm → (W (t : ℂ)).re ≤ 0 := by
        intro t htS htm
        have htm_lt_t : D.tm < t := lt_of_le_of_ne (D.tm_min t htS) htm.symm
        have hb_lt_t : b < t := hbtm.trans_lt htm_lt_t
        rw [hW_re t, hQb_of_ne t hb_lt_t.ne']
        have hfac : (H (t : ℂ)).re + τ * ((H (t : ℂ)).re / (t - b)) =
            (H (t : ℂ)).re * (1 + τ / (t - b)) := by ring
        rw [hfac]
        have hpos_r : 0 ≤ 1 + τ / (t - b) := by
          have : 0 < t - b := sub_pos.mpr hb_lt_t
          positivity
        exact mul_nonpos_of_nonpos_of_nonneg (hH.2.2.1 t htS htm) hpos_r
      have hW_left : ∀ u : ℝ, u ≤ v → (W (u : ℂ)).re ≤ 0 := by
        intro u huv
        have hu_lt_b : u < b := huv.trans_lt hvb
        rw [hW_re u, hQb_of_ne u hu_lt_b.ne]
        have hden_neg : u - b < 0 := sub_neg.mpr hu_lt_b
        have hfac : (H (u : ℂ)).re + τ * ((H (u : ℂ)).re / (u - b)) =
            (H (u : ℂ)).re * ((u - b + τ) / (u - b)) := by field_simp [hden_neg.ne]
        rw [hfac]
        have hratio_nn : 0 ≤ (u - b + τ) / (u - b) :=
          div_nonneg_of_nonpos (by dsimp [τ]; linarith) hden_neg.le
        exact mul_nonpos_of_nonpos_of_nonneg (hH.2.2.2.1 u hu_lt_b.le) hratio_nn
      have hW_lap_nn : ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u : ℝ, (W (u : ℂ)).re * Real.exp (y * u) := by
        intro y hy
        rcases hy.eq_or_lt with rfl | hypos
        · simp only [zero_mul, Real.exp_zero, mul_one]
          simp_rw [hW_re]
          have hH_re_int : Integrable (fun u : ℝ => (H (u : ℂ)).re) := by
            simpa [RCLike.re_to_complex] using hH.1.2.1.re
          have hQb_re_int : Integrable (fun u : ℝ => τ * (Q_b (u : ℂ)).re) := by
            simpa [RCLike.re_to_complex] using hQb_cl.2.1.re.const_mul τ
          rw [integral_add hH_re_int hQb_re_int, integral_const_mul]
          have hH0 : 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re := by simpa using hH.2.2.2.2 0 le_rfl
          exact add_nonneg hH0 (mul_nonneg hτ_pos.le hQb_mass)
        · exact (hW_lap_pos y hypos).le
      exact h_strictify v (hvb.trans_le hbtm) W ⟨hW_cl, hW_nz, hW_sites, hW_left, hW_lap_nn⟩ hW_lap_pos
    -- Deduce `uSh D = (b : EReal)`.
    refine le_antisymm (hb ▸ uSh_le_uLP_aux D) ?_
    by_contra hnot_ge
    push Not at hnot_ge
    obtain ⟨v, hsh_lt_v, hv_lt_b⟩ := EReal.lt_iff_exists_real_btwn.mp hnot_ge
    exact lt_irrefl _ (hsh_lt_v.trans (hv_lt_ush v (EReal.coe_lt_coe_iff.mp hv_lt_b)))
  -- Part (4): deflation obstruction (`b < t_m`, `z > b`, `(H z).re = 0`)
  · intro hlt_tm b hb H hH z hbz hHz0 hsite_cond
    have hb_lt_tm : b < D.tm := EReal.coe_lt_coe_iff.mp (hb ▸ hlt_tm)
    obtain ⟨hQz_cl, _, hQz_int_eq⟩ := deflation_inAiryClass hH.1 hHz0
    let Q_z : ℂ → ℂ := dslope H (z : ℂ)
    change InAiryClass Q_z at hQz_cl
    rw [hQz_int_eq]
    by_contra hnot_neg
    have hQz_mass : 0 ≤ ∫ u : ℝ, (Q_z (u : ℂ)).re := not_lt.mp hnot_neg
    have hQz_lap_pos : ∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (Q_z (u : ℂ)).re) y :=
      fun y hy => deflation_laplace_pos hH.1 hH.2.1 hH.2.2.2.2 hHz0 hQz_mass hy
    -- Choose `0 < σ < z - b` smaller than `z - s` for every `s ∈ shellSites D` with `s < z`.
    let S_lt : Finset ℝ := (shellSites D).filter (· < z)
    have hex_sigma : ∃ σ : ℝ, 0 < σ ∧ σ < z - b ∧ ∀ s ∈ S_lt, σ < z - s := by
      by_cases hSne : S_lt.Nonempty
      · let gap : ℝ := S_lt.inf' hSne (fun s => z - s)
        have hgap_pos : 0 < gap := (Finset.lt_inf'_iff _).mpr fun s hs =>
          sub_pos.mpr (Finset.mem_filter.1 hs).2
        let σ : ℝ := min ((z - b) / 2) (gap / 2)
        have hσ_pos : 0 < σ := lt_min (half_pos (sub_pos.mpr hbz)) (half_pos hgap_pos)
        refine ⟨σ, hσ_pos, lt_of_le_of_lt (min_le_left _ _) (half_lt_self (sub_pos.mpr hbz)),
          fun s hs => ?_⟩
        exact lt_of_le_of_lt (min_le_right _ _)
          (lt_of_lt_of_le (half_lt_self hgap_pos) (Finset.inf'_le _ hs))
      · exact ⟨(z - b) / 2, half_pos (sub_pos.mpr hbz), half_lt_self (sub_pos.mpr hbz),
          fun s hs => absurd ⟨s, hs⟩ hSne⟩
    obtain ⟨σ, hσ_pos, hσ_zb, hσ_sites⟩ := hex_sigma
    let W : ℂ → ℂ := fun w => H w + (σ : ℂ) * Q_z w
    have hW_cl : InAiryClass W := hH.1.add (hQz_cl.smul σ)
    have hW_re : ∀ u : ℝ, (W (u : ℂ)).re = (H (u : ℂ)).re + σ * (Q_z (u : ℂ)).re := by
      intro u; dsimp [W]; simp [Complex.mul_re, hQz_cl.2.2.2 u]
    have hW_lap_pos : ∀ y : ℝ, 0 < y → 0 < laplaceL (fun u => (W (u : ℂ)).re) y := by
      intro y hy
      unfold laplaceL
      simp_rw [hW_re, add_mul, mul_assoc]
      rw [integral_add (hH.1.integrable_exp_nonneg hy.le)
        ((hQz_cl.integrable_exp_nonneg hy.le).const_mul σ), integral_const_mul]
      exact add_pos_of_nonneg_of_pos (hH.2.2.2.2 y hy.le) (mul_pos hσ_pos (hQz_lap_pos y hy))
    have hW_nz : ∃ w : ℂ, W w ≠ 0 := by
      by_contra hall0
      push Not at hall0
      have hpos1 := hW_lap_pos 1 one_pos
      unfold laplaceL at hpos1
      simp [hall0] at hpos1
    have hHz_c : H (z : ℂ) = 0 := Complex.ext hHz0 (hH.1.2.2.2 z)
    have hQz_of_ne : ∀ u : ℝ, u ≠ z → (Q_z (u : ℂ)).re = (H (u : ℂ)).re / (u - z) := by
      intro u hu
      have hne : (u : ℂ) ≠ (z : ℂ) := fun h => hu (Complex.ofReal_injective h)
      dsimp [Q_z]
      rw [dslope_of_ne _ hne, slope_def_field, hHz_c, sub_zero]
      have hHu : H (u : ℂ) = (((H (u : ℂ)).re : ℝ) : ℂ) :=
        Complex.ext (by simp) (by simp [hH.1.2.2.2 u])
      conv_lhs => rw [hHu]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re]
    have hW_left : ∀ u : ℝ, u ≤ b → (W (u : ℂ)).re ≤ 0 := by
      intro u hub
      have hu_lt_z : u < z := hub.trans_lt hbz
      rw [hW_re u, hQz_of_ne u hu_lt_z.ne]
      have hden_neg : u - z < 0 := sub_neg.mpr hu_lt_z
      have hfac : (H (u : ℂ)).re + σ * ((H (u : ℂ)).re / (u - z)) =
          (H (u : ℂ)).re * ((u - z + σ) / (u - z)) := by field_simp [hden_neg.ne]
      rw [hfac]
      have hratio_nn : 0 ≤ (u - z + σ) / (u - z) :=
        div_nonneg_of_nonpos (by linarith) hden_neg.le
      exact mul_nonpos_of_nonpos_of_nonneg (hH.2.2.2.1 u hub) hratio_nn
    have hW_sites : ∀ t ∈ D.S, t ≠ D.tm → (W (t : ℂ)).re ≤ 0 := by
      intro t htS htm
      have ht_sh : t ∈ shellSites D := Finset.mem_erase.2 ⟨htm, htS⟩
      rcases lt_trichotomy t z with hlt_z | rfl | hgt_z
      · rw [hW_re t, hQz_of_ne t hlt_z.ne]
        have hden_neg : t - z < 0 := sub_neg.mpr hlt_z
        have hfac : (H (t : ℂ)).re + σ * ((H (t : ℂ)).re / (t - z)) =
            (H (t : ℂ)).re * ((t - z + σ) / (t - z)) := by field_simp [hden_neg.ne]
        rw [hfac]
        have hσ_lt := hσ_sites t (Finset.mem_filter.2 ⟨ht_sh, hlt_z⟩)
        have hratio_nn : 0 ≤ (t - z + σ) / (t - z) :=
          div_nonneg_of_nonpos (by linarith) hden_neg.le
        exact mul_nonpos_of_nonpos_of_nonneg (hH.2.2.1 t htS htm) hratio_nn
      · rcases hsite_cond with hnot_sh | hderiv_le
        · exact absurd ht_sh hnot_sh
        · rw [hW_re t, hHz0, zero_add]
          dsimp [Q_z]
          rw [dslope_same]
          exact mul_nonpos_of_nonneg_of_nonpos hσ_pos.le hderiv_le
      · rw [hW_re t, hQz_of_ne t hgt_z.ne']
        have hden_pos : 0 < t - z := sub_pos.mpr hgt_z
        have hfac : (H (t : ℂ)).re + σ * ((H (t : ℂ)).re / (t - z)) =
            (H (t : ℂ)).re * (1 + σ / (t - z)) := by ring
        rw [hfac]
        exact mul_nonpos_of_nonpos_of_nonneg (hH.2.2.1 t htS htm) (by positivity)
    have hW_lap_nn : ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u : ℝ, (W (u : ℂ)).re * Real.exp (y * u) := by
      intro y hy
      rcases hy.eq_or_lt with rfl | hypos
      · simp only [zero_mul, Real.exp_zero, mul_one]
        simp_rw [hW_re]
        have hH_re_int : Integrable (fun u : ℝ => (H (u : ℂ)).re) := by
          simpa [RCLike.re_to_complex] using hH.1.2.1.re
        have hQz_re_int : Integrable (fun u : ℝ => σ * (Q_z (u : ℂ)).re) := by
          simpa [RCLike.re_to_complex] using hQz_cl.2.1.re.const_mul σ
        rw [integral_add hH_re_int hQz_re_int, integral_const_mul]
        have hH0 : 0 ≤ ∫ u : ℝ, (H (u : ℂ)).re := by simpa using hH.2.2.2.2 0 le_rfl
        exact add_nonneg hH0 (mul_nonneg hσ_pos.le hQz_mass)
      · exact (hW_lap_pos y hypos).le
    have hstrict := h_strictify b hb_lt_tm W ⟨hW_cl, hW_nz, hW_sites, hW_left, hW_lap_nn⟩ hW_lap_pos
    have hle_ulp : uSh D ≤ (b : EReal) := hb ▸ uSh_le_uLP_aux D
    exact lt_irrefl _ (hstrict.trans_le hle_ulp)

/-- info: 'FormalResearch.SignUncertainty.deflation_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.deflation_identity

/-- info: 'FormalResearch.SignUncertainty.exists_airy_shell_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.exists_airy_shell_buffer

/-- info: 'FormalResearch.SignUncertainty.airy_active_height_strictify_buffer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_active_height_strictify_buffer

/-- info: 'FormalResearch.SignUncertainty.airy_active_height' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.airy_active_height

end FormalResearch.SignUncertainty

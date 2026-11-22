module

public import FormalResearch.ModularBootstrap.StripMultiplier.LemmaS4
public import FormalResearch.ModularBootstrap.Chart.EdgeFunctions
public import FormalResearch.ModularBootstrap.Chart.ExponentAndSaddle
public import FormalResearch.ModularBootstrap.StripBand.StripPoissonRep
public import FormalResearch.ModularBootstrap.StripBand.BandReductionBV
public import FormalResearch.Asymptotics.StirlingHalfInt

/-!
# Edge Representation, Poisson Identity, and Kernel Factorization (Lemmas J4.1 & J4.2)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, Lemma J4.1 (`vlo:J41`,
lines 482–497) and Lemma J4.2 (`vlo:J42`, lines 499–514).

Defines:
* `edgeKernelK c' τ t`: the Mellin edge kernel `K(τ, x)` (with `t = c' x^2 / 3`);
* `edgeHV c' g ζ`: the damped strip multiplier `H_V(ζ) = tebPrefactor c' ζ * tildeWV c' g ζ`;
* `edgeA1 c' τ`, `edgeA2 c' t`, `edgeRV c' τ t`, `edgePhi c' τ t`, `edgeTheta c' τ t`: the kernel
  factorization pieces of Lemma J4.2;
* `wFactor w ω`: the general-weight `(w ≥ 1)` factor `(2π / (3 ω))^{(w - 1) / 2}` with uniform
  sup and `τ`-derivative bounds on `ω(iτ)`.

Proves:
* `lemma_J4_1`: **Lemma J4.1 (`vlo:J41`)** — edge integral representation of `W̃_V(iτ)`,
  strip Poisson representation `H_V(ζ₀) = ∫_ℝ Q(τ) H_V(iτ) dτ`, `‖Q‖₁ ≤ 1`, and
  `sup |Q| + TV(Q) ≤ 2 / σ₀` on `0 < σ₀ ≤ 0.04`.
* `lemma_J4_2`: **Lemma J4.2 (`vlo:J42`)** — exact kernel factorization
  `K(τ, t) = A₁(τ) A₂(t) exp(c' (R_V - i Φ)) = A₁(τ) A₂(t) exp(c' (R_V + i Θ))`,
  parity and derivative of `Φ` (`Θ`), unimodality of `R_V`, uniform bounds on `A₁, A₁', A₂`,
  and the uniform sub-Cardy kernel bound `‖K(τ, t)‖ ≤ C e^{-κ c'}` on `0 < x ≤ ξ_* / 2`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.StripMultiplier

open Crossing Integration ComplexBessel Mellin Chart ChartGeometry StripBand
open FormalResearch.StripPoisson

/-! ### Section 1: Edge kernel, `H_V`, and factorization definitions -/

/-- Edge Mellin kernel `K(τ, x) = e^{-c' Υ(iτ)} (2π)^z t^{z-1} / (Γ(z) V(t))` as a function of
`(τ, t)` (`t > 0`, `z = 1/2 + c' ω(iτ)`) (`lower_o1_two_edge.tex`, Lemma J4.1, `vlo:J41`). -/
noncomputable def edgeKernelK (c' : ℝ) (τ t : ℝ) : ℂ :=
  if 0 < t then
    let z : ℂ := 1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))
    Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
      (Complex.Gamma z * (virasoroProblem.cardyV (c' / 12) t : ℂ))
  else 0

/-- Damped strip function `H_V(ζ) = c'^{5/6} (ζ(1 - ζ))^{5/2} e^{-ζ(1 - ζ)} W̃_V(ζ)`
(`lower_o1_two_edge.tex`, Lemma J4.1, `vlo:J41`). -/
noncomputable def edgeHV (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  tebPrefactor c' ζ * tildeWV c' g ζ

/-- Edge amplitude `A₁(τ) = S_{c'}(ω(iτ))⁻¹` at `w = 1` (`lower_o1_two_edge.tex`, Lemma J4.2). -/
noncomputable def edgeA1 (c' τ : ℝ) : ℂ :=
  (stirlingS c' (chartOmega (Complex.I * (τ : ℂ))))⁻¹

/-- General-weight factor `(2π / (3 ω))^{(w - 1) / 2}` appearing in `A₁(τ)` at weight `w ≥ 1`. -/
noncomputable def wFactor (w : ℝ) (ω : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) / (3 * ω)) ^ (((w - 1) / 2 : ℝ) : ℂ)

/-- Energy amplitude `A₂(x) = t^{-1/2} e^{c' L(x)} / V(t)` (`x = √(3 t / c')`) at `w = 1`
(`lower_o1_two_edge.tex`, Lemma J4.2). -/
noncomputable def edgeA2 (c' t : ℝ) : ℝ :=
  (1 / √t) * Real.exp (c' * Bessel.besselL (√(3 * t / c'))) / virasoroProblem.cardyV (c' / 12) t

/-- Real damping exponent `R_V(τ; x) = -D(x₀(τ), x)` (`x = √(3 t / c')`)
(`lower_o1_two_edge.tex`, Lemma J4.2). -/
noncomputable def edgeRV (c' τ t : ℝ) : ℝ :=
  -crudeDivergenceD (edgeX0 τ) (√(3 * t / c'))

/-- Phase `Φ(τ; t) = Im Φ_V(iτ; √(3t/c')) = -Θ(τ; x)` for Proposition `TE.3(1)`
(`lower_o1_two_edge.tex`, Lemma J4.2 & Proposition Y_V). -/
noncomputable def edgePhi (c' τ t : ℝ) : ℝ :=
  (chartPhiV (Complex.I * (τ : ℂ)) (√(3 * t / c') : ℂ)).im

/-- Opposite-sign phase `Θ(τ; t) = -Φ(τ; t) = -Im Φ_V(iτ; √(3t/c'))` (`lower_o1_two_edge.tex`, Lemma J4.2). -/
noncomputable def edgeTheta (c' τ t : ℝ) : ℝ :=
  -edgePhi c' τ t

/-! ### Section 2: Lemma J4.1 — Representation and Poisson identity -/

lemma measurable_edgeKernelK {c' : ℝ} (hc' : 0 ≤ c') :
    Measurable (Function.uncurry (edgeKernelK c')) := by
  have hω_cont : Continuous (fun τ : ℝ => chartOmega (Complex.I * (τ : ℂ))) :=
    continuousOn_chartOmega.comp_continuous (by fun_prop) fun τ => by simp
  have hΥ_cont : Continuous (fun τ : ℝ => chartUpsilon (Complex.I * (τ : ℂ))) :=
    lemma_S3_strip.2.2.2.1.comp_continuous (by fun_prop) fun τ => by simp [stripClosed]
  have hz_cont : Continuous (fun τ : ℝ => 1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))) :=
    continuous_const.add (continuous_const.mul hω_cont)
  have hgam_cont : Continuous (fun τ : ℝ =>
      Complex.Gamma (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)))) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hre : 0 < (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
      have hmu : 0 < (chartOmega (Complex.I * (τ : ℂ))).re := by
        rw [chartOmega_left_edge]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
        exact lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
      linarith [mul_nonneg hc' hmu.le]
    have hdiff : DifferentiableAt ℂ Complex.Gamma
        (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))) :=
      Complex.differentiableAt_Gamma _ fun m hm => by
        have := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [Nat.cast_nonneg (α := ℝ) m]
    exact ContinuousAt.comp hdiff.continuousAt (hz_cont.continuousAt (x := τ))
  have h2pi_cont : Continuous (fun τ : ℝ =>
      (2 * (Real.pi : ℂ)) ^ (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)))) := by
    refine Continuous.const_cpow hz_cont (Or.inl ?_)
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hV_cont : Continuous (fun t : ℝ => (virasoroProblem.cardyV (c' / 12) t : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_cardyV virasoroProblem (c' / 12))
  have hnum_meas : Measurable (fun p : ℝ × ℝ =>
      Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (p.1 : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
        Complex.exp ((1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)) - 1) *
          Complex.log (p.2 : ℂ)) /
        (Complex.Gamma (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
          (virasoroProblem.cardyV (c' / 12) p.2 : ℂ))) := by
    have m1 : Measurable (fun p : ℝ × ℝ =>
        Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (p.1 : ℂ)))) :=
      ((hΥ_cont.const_mul (-(c' : ℂ))).cexp.comp continuous_fst).measurable
    have m2 : Measurable (fun p : ℝ × ℝ =>
        (2 * (Real.pi : ℂ)) ^ (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)))) :=
      (h2pi_cont.comp continuous_fst).measurable
    have m3 : Measurable (fun p : ℝ × ℝ =>
        Complex.exp ((1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)) - 1) *
          Complex.log (p.2 : ℂ))) := by
      refine Measurable.cexp (Measurable.mul ?_ ?_)
      · exact ((hz_cont.sub continuous_const).comp continuous_fst).measurable
      · exact Complex.measurable_log.comp (Complex.continuous_ofReal.comp continuous_snd).measurable
    have m4 : Measurable (fun p : ℝ × ℝ =>
        Complex.Gamma (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
          (virasoroProblem.cardyV (c' / 12) p.2 : ℂ)) :=
      ((hgam_cont.comp continuous_fst).mul (hV_cont.comp continuous_snd)).measurable
    exact ((m1.mul m2).mul m3).div m4
  have heq : Function.uncurry (edgeKernelK c') = fun p : ℝ × ℝ =>
      if 0 < p.2 then
        Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (p.1 : ℂ))) *
          (2 * (Real.pi : ℂ)) ^ (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
          Complex.exp ((1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)) - 1) *
            Complex.log (p.2 : ℂ)) /
          (Complex.Gamma (1 / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
            (virasoroProblem.cardyV (c' / 12) p.2 : ℂ))
      else 0 := by
    ext ⟨τ, t⟩
    unfold edgeKernelK Function.uncurry
    by_cases ht : 0 < t
    · simp only [ht, ↓reduceIte]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      rw [Complex.cpow_def_of_ne_zero ht_ne, mul_comm (Complex.log (t : ℂ))]
    · simp [ht]
  rw [heq]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) hnum_meas measurable_const

lemma tildeWV_edge_integral {c' : ℝ} (hc' : 24 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) (τ : ℝ) :
    tildeWV c' g (Complex.I * (τ : ℂ)) =
      ∫ t in Ioi (0 : ℝ),
        edgeKernelK c' τ t * ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ) := by
  have hc'_pos : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let ω := chartOmega (Complex.I * (τ : ℂ))
  let z : ℂ := 1 / 2 + (c' : ℂ) * ω
  have hω_re : 0 < ω.re := by
    dsimp [ω]; rw [chartOmega_left_edge τ]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
  have hz_re : 0 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
    linarith [mul_pos hc'_pos hω_re]
  have hint := integrableOn_mellinTransformG ha hg hz_re
  let Cfac : ℂ := Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
    (2 * (Real.pi : ℂ)) ^ z / Complex.Gamma z
  have hcongr : EqOn (fun t : ℝ => edgeKernelK c' τ t *
        ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ))
      (fun t : ℝ => Cfac * ((g t : ℂ) * (t : ℂ) ^ (z - 1))) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) t := by
      have := virasoro_cardyV_ge ha ht0.le
      have h8 : 0 < 8 * Real.pi ^ 4 * t ^ 2 := by positivity
      linarith
    have hV_ne : (virasoroProblem.cardyV (c' / 12) t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hV_pos.ne'
    unfold edgeKernelK
    simp only [ht0, ↓reduceIte]
    dsimp [Cfac, z, ω]
    push_cast
    field_simp [hV_ne]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
  unfold tildeWV
  rw [mellinMGEntire_of_re_pos g hz_re]
  unfold mellinMG mellinTransformG
  dsimp [Cfac, z, ω]
  ring

lemma stripPoissonQ_norm_L1_le {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) (η₀ : ℝ) :
    ∫ τ : ℝ, |stripPoissonQ σ₀ η₀ (-1) τ| ≤ 1 := by
  have hp_int : Integrable (fun τ : ℝ => stripPoissonP σ₀ (τ - η₀)) :=
    (stripPoissonP_integrable h0 h1).comp_sub_right η₀
  have hp1_int : Integrable (fun τ : ℝ => stripPoissonP1 σ₀ (τ + η₀)) :=
    (stripPoissonP1_integrable h0 h1).comp_add_right η₀
  have hsum_int : Integrable (fun τ : ℝ => stripPoissonP σ₀ (τ - η₀) + stripPoissonP1 σ₀ (τ + η₀)) :=
    hp_int.add hp1_int
  have hQ_le : ∀ τ : ℝ, |stripPoissonQ σ₀ η₀ (-1) τ| ≤
      stripPoissonP σ₀ (τ - η₀) + stripPoissonP1 σ₀ (τ + η₀) := fun τ =>
    stripPoissonQ_abs_le h0 h1 η₀ (by norm_num) τ
  have hmono : ∫ τ : ℝ, |stripPoissonQ σ₀ η₀ (-1) τ| ≤
      ∫ τ : ℝ, (stripPoissonP σ₀ (τ - η₀) + stripPoissonP1 σ₀ (τ + η₀)) := by
    refine integral_mono ?_ hsum_int hQ_le
    refine hsum_int.mono' ?_ (ae_of_all _ fun τ => ?_)
    · exact ((hp_int.sub hp1_int).aestronglyMeasurable.congr
        (ae_of_all _ fun τ => by simp [stripPoissonQ, sub_eq_add_neg])).norm
    · rw [Real.norm_eq_abs, abs_abs]
      exact hQ_le τ
  have hp_val : ∫ τ : ℝ, stripPoissonP σ₀ (τ - η₀) = 1 - σ₀ := by
    rw [integral_sub_right_eq_self (stripPoissonP σ₀) η₀, stripPoissonP_integral h0 h1]
  have hp1_val : ∫ τ : ℝ, stripPoissonP1 σ₀ (τ + η₀) = σ₀ := by
    rw [integral_add_right_eq_self (stripPoissonP1 σ₀) η₀, stripPoissonP1_integral h0 h1]
  rw [integral_add hp_int hp1_int, hp_val, hp1_val] at hmono
  linarith

/-- **Lemma J4.1 (representation and Poisson identity)** (`lower_o1_two_edge.tex`, §J4, `vlo:J41`,
lines 482–497):
for `c' ≥ c₀` (the threshold of Lemma S4), `g ∈ TestClass virasoroProblem (c'/12)`, and any `ζ₀`
with `0 < ζ₀.re < 1`:
1. `W̃_V(iτ) = ∫_{(0, ∞)} K(τ, t) g(t) V(t) dt` for all `τ : ℝ`;
2. `H_V(iτ) = 𝒜_V(τ) W̃_V(iτ)` and `H_V(ζ₀) = ∫_ℝ Q(τ) H_V(iτ) dτ` with `Q(τ) = p(τ - η₀) - p₁(τ + η₀)`;
3. `‖Q‖₁ ≤ 1`, and for `0 < ζ₀.re ≤ 0.04`, `sup |Q| + TV(Q) ≤ 2 / ζ₀.re`. -/
theorem lemma_J4_1 :
    ∃ C c₀ : ℝ, 0 < C ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g →
        (∀ τ : ℝ, tildeWV c' g (Complex.I * (τ : ℂ)) =
          ∫ t in Ioi (0 : ℝ),
            edgeKernelK c' τ t * ((g t * virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)) ∧
        (∀ τ : ℝ, edgeHV c' g ((τ : ℂ) * Complex.I) =
          tebAmp0 c' τ * tildeWV c' g ((τ : ℂ) * Complex.I)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re < 1 →
          edgeHV c' g ζ₀ =
            ∫ τ : ℝ, (stripPoissonQ ζ₀.re ζ₀.im (-1) τ : ℂ) *
              edgeHV c' g ((τ : ℂ) * Complex.I)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re ≤ 0.04 →
          (∫ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| ≤ 1) ∧
          (∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| +
            (eVariationOn (stripPoissonQ ζ₀.re ζ₀.im (-1)) univ).toReal ≤ 2 / ζ₀.re)) := by
  obtain ⟨C, c₀, hC, hc₀, hS4⟩ := lemma_S4
  refine ⟨C, c₀, hC, hc₀, fun {c'} hc' {g} hg => ?_⟩
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  obtain ⟨hdiff, hcont, href, hbd⟩ := hS4 hc' hg
  refine ⟨fun τ => tildeWV_edge_integral hc'_24 hg τ, fun _ => rfl, ?_, ?_⟩
  · intro ζ₀ hσ₀ hσ₁
    have hH_cont : ContinuousOn (edgeHV c' g) stripClosed :=
      (tebPrefactor_continuousOn c').mul hcont
    have hH_holo : DifferentiableOn ℂ (edgeHV c' g) stripOpen :=
      (tebPrefactor_differentiableOn c').mul hdiff
    have hH_symm : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
        edgeHV c' g (1 - ζ) = (-1 : ℝ) * edgeHV c' g ζ := fun ζ h0 h1 => by
      dsimp [edgeHV]
      rw [tebPrefactor_symm, href ζ ⟨h0, h1⟩]
      push_cast; ring
    let M : ℝ := virasoroProblem.cardyNorm (c' / 12) g
    have hM_nn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg
      (by rw [virasoroProblem_totalShift]; linarith) g
    have hH_bd : ∃ M_H : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖edgeHV c' g ζ‖ ≤ M_H := by
      let m_H : ℕ := 3
      refine ⟨c' ^ (5 / 6 : ℝ) * (C * M) * (2 : ℝ) ^ (5 : ℝ) *
        ((2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ)), fun ζ h0 h1 => ?_⟩
      have hpf := norm_tebPrefactor_le c' hc'_pos.le h0 h1
      have hW := hbd ζ ⟨h0, h1⟩
      have hζ1 : ‖ζ‖ ≤ 1 + |ζ.im| := by
        have hre1 : ζ.re ^ 2 ≤ 1 := by nlinarith
        have hsq : ‖ζ‖ ^ 2 ≤ (1 + |ζ.im|) ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          nlinarith [sq_abs ζ.im, abs_nonneg ζ.im]
        nlinarith [norm_nonneg ζ, abs_nonneg ζ.im]
      have hprod_le : ‖ζ * (1 - ζ)‖ ≤ (1 + ‖ζ‖) ^ 2 := by
        rw [norm_mul, sq]
        have h1' : ‖ζ‖ ≤ 1 + ‖ζ‖ := by linarith
        have h2' : ‖1 - ζ‖ ≤ 1 + ‖ζ‖ := (norm_sub_le 1 ζ).trans (by rw [norm_one])
        exact mul_le_mul h1' h2' (norm_nonneg _) (by positivity)
      have hpow5 : ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ) * (1 + |ζ.im|) ^ (5 : ℝ) := by
        have h1' : ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) ≤ (1 + ‖ζ‖) ^ (5 : ℝ) := by
          have h := Real.rpow_le_rpow (norm_nonneg _) hprod_le (by norm_num : (0 : ℝ) ≤ 5 / 2)
          rwa [← Real.rpow_natCast (1 + ‖ζ‖) 2, ← Real.rpow_mul (by positivity),
            show (2 : ℕ) * (5 / 2 : ℝ) = 5 by norm_num] at h
        have h2' : (1 + ‖ζ‖) ^ (5 : ℝ) ≤ (2 * (1 + |ζ.im|)) ^ (5 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg ζ.im]) (by norm_num)
        exact h1'.trans (h2'.trans_eq (Real.mul_rpow (by norm_num) (by positivity)))
      have him_bound : (1 + |ζ.im|) ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2) ≤
          (2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ) := by
        rcases le_or_gt |ζ.im| 1 with him | him
        · have h1' : (1 + |ζ.im|) ^ (5 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
          have h2' : Real.exp (-ζ.im ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ζ.im])
          calc (1 + |ζ.im|) ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2)
              ≤ (2 : ℝ) ^ (5 : ℝ) * 1 := mul_le_mul h1' h2' (Real.exp_pos _).le (by positivity)
            _ ≤ (2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ) := by
                gcongr; exact le_max_left _ _
        · have h1' : (1 + |ζ.im|) ^ (5 : ℝ) ≤ (2 : ℝ) ^ (5 : ℝ) * |ζ.im| ^ (5 : ℝ) := by
            rw [← Real.mul_rpow (by norm_num) (abs_nonneg _)]
            exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
          have hfac : |ζ.im| ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2) ≤ (Nat.factorial m_H : ℝ) := by
            have hle : |ζ.im| ^ (5 : ℝ) ≤ (|ζ.im| ^ 2) ^ m_H := by
              rw [← Real.rpow_natCast (|ζ.im| ^ 2) m_H, ← Real.rpow_natCast |ζ.im| 2,
                ← Real.rpow_mul (abs_nonneg _)]
              refine Real.rpow_le_rpow_of_exponent_le him.le ?_
              dsimp [m_H]; norm_num
            have hexp_le : (|ζ.im| ^ 2) ^ m_H / (Nat.factorial m_H : ℝ) ≤ Real.exp (|ζ.im| ^ 2) :=
              (Finset.single_le_sum (f := fun i => (|ζ.im| ^ 2) ^ i / (Nat.factorial i : ℝ))
                (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m_H))).trans
                (Real.sum_le_exp_of_nonneg (sq_nonneg _) (m_H + 1))
            have hfac_pos : (0 : ℝ) < Nat.factorial m_H := Nat.cast_pos.mpr (Nat.factorial_pos _)
            rw [div_le_iff₀ hfac_pos] at hexp_le
            have hexp_mul : Real.exp (ζ.im ^ 2) * Real.exp (-ζ.im ^ 2) = 1 := by
              rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
            have hsq : |ζ.im| ^ 2 = ζ.im ^ 2 := sq_abs ζ.im
            rw [hsq] at hexp_le hle
            calc |ζ.im| ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2)
                ≤ ((ζ.im ^ 2) ^ m_H) * Real.exp (-ζ.im ^ 2) := by gcongr
              _ ≤ (Real.exp (ζ.im ^ 2) * (Nat.factorial m_H : ℝ)) * Real.exp (-ζ.im ^ 2) := by
                  gcongr
              _ = (Nat.factorial m_H : ℝ) * (Real.exp (ζ.im ^ 2) * Real.exp (-ζ.im ^ 2)) := by ring
              _ = (Nat.factorial m_H : ℝ) := by rw [hexp_mul, mul_one]
          calc (1 + |ζ.im|) ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2)
              ≤ (2 : ℝ) ^ (5 : ℝ) * |ζ.im| ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2) := by gcongr
            _ = (2 : ℝ) ^ (5 : ℝ) * (|ζ.im| ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2)) := by ring
            _ ≤ (2 : ℝ) ^ (5 : ℝ) * (Nat.factorial m_H : ℝ) := by gcongr
            _ ≤ (2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ) := by
                gcongr; exact le_max_right _ _
      calc ‖edgeHV c' g ζ‖
          = ‖tebPrefactor c' ζ‖ * ‖tildeWV c' g ζ‖ := norm_mul _ _
        _ ≤ (c' ^ (5 / 6 : ℝ) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2)) * (C * M) := by
            gcongr
        _ = c' ^ (5 / 6 : ℝ) * (C * M) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2) := by ring
        _ ≤ c' ^ (5 / 6 : ℝ) * (C * M) * ((2 : ℝ) ^ (5 : ℝ) * (1 + |ζ.im|) ^ (5 : ℝ)) *
              Real.exp (-ζ.im ^ 2) := by gcongr
        _ = c' ^ (5 / 6 : ℝ) * (C * M) * (2 : ℝ) ^ (5 : ℝ) *
              ((1 + |ζ.im|) ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2)) := by ring
        _ ≤ c' ^ (5 / 6 : ℝ) * (C * M) * (2 : ℝ) ^ (5 : ℝ) *
              ((2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ)) := by gcongr
    obtain ⟨M_H, hH_bd'⟩ := hH_bd
    exact (stripPoisson_representation_symm hH_cont hH_holo hH_bd' hH_symm hσ₀ hσ₁).2
  · intro ζ₀ hσ₀ hσ₀_le
    have hσ₁ : ζ₀.re < 1 := by linarith
    refine ⟨stripPoissonQ_norm_L1_le hσ₀ hσ₁ ζ₀.im, fun τ => ?_⟩
    have h1 := (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im (ε := -1) (by norm_num) τ).trans
      (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
    have h2 := stripPoissonQ_tv_le hσ₀ hσ₀_le ζ₀.im (ε := -1) (by norm_num)
    calc |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| +
          (eVariationOn (stripPoissonQ ζ₀.re ζ₀.im (-1)) univ).toReal
        ≤ 1 / ζ₀.re + 1 / ζ₀.re := add_le_add h1 h2
      _ = 2 / ζ₀.re := by ring

/-! ### Section 3: Lemma J4.2 — Kernel factorization, amplitude/phase bounds, sub-Cardy bound -/

lemma edgeX0_even (τ : ℝ) : edgeX0 (-τ) = edgeX0 τ := by
  unfold edgeX0; rw [mul_neg, Real.cosh_neg]

lemma edgeY0_odd (τ : ℝ) : edgeY0 (-τ) = -edgeY0 τ := by
  unfold edgeY0
  rw [show Real.pi * -τ / 2 = -(Real.pi * τ / 2) by ring, Real.sinh_neg, mul_neg,
    Real.arsinh_neg, neg_div]

lemma edgeMu_even (τ : ℝ) : edgeMu (-τ) = edgeMu τ := by
  unfold edgeMu; rw [edgeX0_even]

lemma edgeNu_odd (τ : ℝ) : edgeNu (-τ) = -edgeNu τ := by
  unfold edgeNu; rw [edgeX0_even, edgeY0_odd]; ring

lemma edgeX0Deriv_even (τ : ℝ) : edgeX0Deriv (-τ) = -edgeX0Deriv τ := by
  unfold edgeX0Deriv
  rw [show Real.pi * -τ / 2 = -(Real.pi * τ / 2) by ring, Real.sinh_neg,
    show Real.pi * -τ = -(Real.pi * τ) by ring, Real.cosh_neg]
  ring

lemma edgeNuDeriv_even (τ : ℝ) : edgeNuDeriv (-τ) = edgeNuDeriv τ := by
  have hd : HasDerivAt (fun s : ℝ => edgeNu (-s)) (edgeNuDeriv (-τ) * (-1)) τ :=
    (hasDerivAt_edgeNu (-τ)).comp τ (hasDerivAt_id τ).neg
  have hd2 : HasDerivAt (fun s : ℝ => -edgeNu s) (-edgeNuDeriv τ) τ := (hasDerivAt_edgeNu τ).neg
  have heq : (fun s => edgeNu (-s)) = (fun s => -edgeNu s) := funext edgeNu_odd
  rw [heq] at hd
  have h := hd.unique hd2
  linarith

lemma edgeMuDeriv_odd (τ : ℝ) : edgeMuDeriv (-τ) = -edgeMuDeriv τ := by
  unfold edgeMuDeriv; rw [edgeX0Deriv_even]; ring

lemma norm_chartOmega_left_edge_ge :
    ∃ c_ω : ℝ, 0 < c_ω ∧ ∀ τ : ℝ, c_ω * (1 + |τ|) ^ 2 ≤ ‖chartOmega (Complex.I * (τ : ℂ))‖ := by
  obtain ⟨cx₁, _, hcx₁, _, hx_as⟩ := lemma_J4_0.2.2.1
  let c_ω : ℝ := min (muStar / 2) (Real.pi * cx₁ / 6) / 2
  have hc_pos : 0 < c_ω := by
    have := muStar_pos; have := Real.pi_pos; positivity
  refine ⟨c_ω, hc_pos, fun τ => ?_⟩
  have hnorm_abs : ‖chartOmega (Complex.I * (τ : ℂ))‖ =
      ‖chartOmega (Complex.I * ((|τ| : ℝ) : ℂ))‖ := by
    rcases le_or_gt 0 τ with hτ | hτ
    · rw [abs_of_nonneg hτ]
    · rw [abs_of_neg hτ, chartOmega_left_edge, chartOmega_left_edge, edgeMu_even, edgeNu_odd,
        ← Complex.norm_conj]
      congr 1
      apply Complex.ext <;> simp
  rw [hnorm_abs]
  have hτ_nn : 0 ≤ |τ| := abs_nonneg τ
  have hmu : muStar ≤ edgeMu |τ| := edgeMu_ge_muStar |τ|
  have hx : cx₁ * (1 + |τ|) ≤ edgeX0 |τ| := (hx_as |τ| hτ_nn).1
  have hy : (1 / 2 : ℝ) * |τ| ≤ edgeY0 |τ| := (edgeY0_bounds hτ_nn).1
  have hnu : (Real.pi * cx₁ / 3) * |τ| * (1 + |τ|) ≤ edgeNu |τ| := by
    unfold edgeNu
    have hpi := Real.pi_pos
    have h1 : (2 * Real.pi / 3) * (cx₁ * (1 + |τ|)) * ((1 / 2) * |τ|) ≤
        (2 * Real.pi / 3) * edgeX0 |τ| * edgeY0 |τ| :=
      mul_le_mul (mul_le_mul_of_nonneg_left hx (by positivity)) hy
        (mul_nonneg (by norm_num) (abs_nonneg τ))
        (mul_nonneg (by positivity) (edgeX0_pos hτ_nn).le)
    linarith
  have hquad : (1 + |τ|) ^ 2 ≤ 2 * (1 + |τ| * (1 + |τ|)) := by
    nlinarith [sq_nonneg |τ|]
  rw [chartOmega_left_edge]
  have hre_le : edgeMu |τ| ≤ ‖(edgeMu |τ| : ℂ) - Complex.I * (edgeNu |τ| : ℂ)‖ := by
    have h := Complex.abs_re_le_norm ((edgeMu |τ| : ℂ) - Complex.I * (edgeNu |τ| : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self] at h
    exact le_trans (le_abs_self _) h
  have him_le : edgeNu |τ| ≤ ‖(edgeMu |τ| : ℂ) - Complex.I * (edgeNu |τ| : ℂ)‖ := by
    have h := Complex.abs_im_le_norm ((edgeMu |τ| : ℂ) - Complex.I * (edgeNu |τ| : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      one_mul, Complex.ofReal_re, mul_zero, zero_add, zero_sub, abs_neg] at h
    have hnu_nn : 0 ≤ edgeNu |τ| := by
      unfold edgeNu
      have hpi := Real.pi_pos
      have hx0 := (edgeX0_pos hτ_nn).le
      have hy0 : 0 ≤ edgeY0 |τ| := by
        linarith [(edgeY0_bounds hτ_nn).1, abs_nonneg τ]
      exact mul_nonneg (mul_nonneg (by positivity) hx0) hy0
    exact (le_of_eq (abs_of_nonneg hnu_nn).symm).trans h
  have hsum : (muStar + (Real.pi * cx₁ / 3) * |τ| * (1 + |τ|)) / 2 ≤
      ‖(edgeMu |τ| : ℂ) - Complex.I * (edgeNu |τ| : ℂ)‖ := by
    linarith
  have hmin : min (muStar / 2) (Real.pi * cx₁ / 6) * (1 + |τ|) ^ 2 / 2 ≤
      (muStar + (Real.pi * cx₁ / 3) * |τ| * (1 + |τ|)) / 2 := by
    have hm1 : 2 * c_ω ≤ muStar / 2 := by dsimp [c_ω]; linarith [min_le_left (muStar / 2) (Real.pi * cx₁ / 6)]
    have hm2 : 2 * c_ω ≤ Real.pi * cx₁ / 6 := by dsimp [c_ω]; linarith [min_le_right (muStar / 2) (Real.pi * cx₁ / 6)]
    calc min (muStar / 2) (Real.pi * cx₁ / 6) * (1 + |τ|) ^ 2 / 2
        = c_ω * (1 + |τ|) ^ 2 := by dsimp [c_ω]; ring
      _ ≤ c_ω * (2 * (1 + |τ| * (1 + |τ|))) := mul_le_mul_of_nonneg_left hquad hc_pos.le
      _ = (2 * c_ω) + (2 * c_ω) * |τ| * (1 + |τ|) := by ring
      _ ≤ (muStar / 2) + (Real.pi * cx₁ / 6) * |τ| * (1 + |τ|) := by
          gcongr
      _ = (muStar + (Real.pi * cx₁ / 3) * |τ| * (1 + |τ|)) / 2 := by ring
  calc c_ω * (1 + |τ|) ^ 2
      = min (muStar / 2) (Real.pi * cx₁ / 6) * (1 + |τ|) ^ 2 / 2 := by dsimp [c_ω]; ring
    _ ≤ (muStar + (Real.pi * cx₁ / 3) * |τ| * (1 + |τ|)) / 2 := hmin
    _ ≤ ‖(edgeMu |τ| : ℂ) - Complex.I * (edgeNu |τ| : ℂ)‖ := hsum

lemma edgeKernelK_factorization {c' : ℝ} (hc' : 24 ≤ c') (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    edgeKernelK c' τ t =
      edgeA1 c' τ * (edgeA2 c' t : ℂ) *
        Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ))) := by
  have hc'_pos : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let x : ℝ := √(3 * t / c')
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have ht_eq : t = c' * x ^ 2 / 3 := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  have ht_c_eq : (t : ℂ) = (c' : ℂ) * (x : ℂ) ^ 2 / 3 := by exact_mod_cast ht_eq
  let ω := chartOmega (Complex.I * (τ : ℂ))
  let z : ℂ := 1 / 2 + (c' : ℂ) * ω
  have hω_re : 0 < ω.re := by
    dsimp [ω]; rw [chartOmega_left_edge τ]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
  have hω_ne : ω ≠ 0 := by intro h; rw [h, Complex.zero_re] at hω_re; exact lt_irrefl 0 hω_re
  have hz_re : 0 < z.re := by
    dsimp [z]
    simp only [Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
    linarith [mul_pos hc'_pos hω_re]
  have hgam_ne : Complex.Gamma z ≠ 0 :=
    Complex.Gamma_ne_zero fun m hm => by
      have := congrArg Complex.re hm
      simp only [Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) m]
  have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h2pi_ne : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have h2pit_ne : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero h2pi_ne ht_ne))
  have hst := gamma_mul_two_pi_t_cpow_neg hc'_pos hω_re.le hω_ne
    (show 0 < (x : ℂ).re by simpa using hx_pos)
  dsimp only at hst
  rw [← ht_c_eq] at hst
  have hcpow_num : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) =
      (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z * (t : ℂ)⁻¹ := by
    have hmul : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z = (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ z := by
      have h1 : (2 * (Real.pi : ℂ) * (t : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) * (t : ℂ) := by
        push_cast; ring
      rw [h1, Complex.mul_cpow_ofReal_nonneg (by positivity : (0 : ℝ) ≤ 2 * Real.pi) ht.le]
      push_cast; rfl
    have hsub : (t : ℂ) ^ (z - 1) = (t : ℂ) ^ z * (t : ℂ)⁻¹ := by
      rw [sub_eq_add_neg, Complex.cpow_add _ _ ht_ne, Complex.cpow_neg_one]
    rw [hmul, hsub]; ring
  have hS_ne : stirlingS c' ω ≠ 0 := Complex.exp_ne_zero _
  have ht_half_ne : (t : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl ht_ne)
  have hexp_J_ne : Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) ≠ 0 := Complex.exp_ne_zero _
  have hratio : (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z =
      (stirlingS c' ω)⁻¹ * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
        Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
    have hinv : Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹ =
        (t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) * stirlingS c' ω := by
      rwa [Complex.cpow_neg] at hst
    have hgam_eq : (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z / Complex.Gamma z =
        (stirlingS c' ω)⁻¹ * ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by
      rw [Complex.exp_neg]
      calc (2 * (Real.pi : ℂ) * (t : ℂ)) ^ z / Complex.Gamma z
          = (Complex.Gamma z * ((2 * (Real.pi : ℂ) * (t : ℂ)) ^ z)⁻¹)⁻¹ := by
            field_simp [hgam_ne, h2pit_ne]
        _ = ((t : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)) *
              stirlingS c' ω)⁻¹ := by rw [hinv]
        _ = (stirlingS c' ω)⁻¹ * ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
              (Complex.exp ((c' : ℂ) * stirlingJ ω (x : ℂ)))⁻¹ := by
            field_simp [hS_ne, ht_half_ne, hexp_J_ne]
    have hthalf_inv : ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹ = (t : ℂ) ^ (-(1 / 2 : ℂ)) := by
      rw [← Complex.cpow_neg, neg_neg, ← Complex.cpow_neg_one, ← Complex.cpow_add _ _ ht_ne]
      congr 1; norm_num
    rw [hcpow_num, mul_div_right_comm, hgam_eq]
    calc (stirlingS c' ω)⁻¹ * ((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) * (t : ℂ)⁻¹
        = (stirlingS c' ω)⁻¹ * (((t : ℂ) ^ (-(1 / 2 : ℂ)))⁻¹ * (t : ℂ)⁻¹) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by ring
      _ = (stirlingS c' ω)⁻¹ * (t : ℂ) ^ (-(1 / 2 : ℂ)) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) := by rw [hthalf_inv]
  have hthalf_c : (t : ℂ) ^ (-(1 / 2 : ℂ)) = ((1 / √t : ℝ) : ℂ) := by
    rw [show (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) by norm_num,
      ← Complex.ofReal_cpow ht.le, Real.rpow_neg ht.le, Real.sqrt_eq_rpow, one_div]
    norm_num
  have hV_pos : 0 < virasoroProblem.cardyV (c' / 12) t := by
    have := virasoro_cardyV_ge ha ht.le
    have h8 : 0 < 8 * Real.pi ^ 4 * t ^ 2 := by positivity
    linarith
  have hV_ne : (virasoroProblem.cardyV (c' / 12) t : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hV_pos.ne'
  -- Relate -(chartPhiV (I*τ) x) to edgeRV - I * edgePhi
  have hphi_re : -(chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ)).re = edgeRV c' τ t := by
    rw [re_chartPhiV_edge_eq_Ec τ (x : ℂ)]
    have hE_eq : crudeExponentEc (chartOmega (Complex.I * (τ : ℂ))) (x : ℂ) =
        crudeDivergenceD (edgeX0 τ) x := by
      rw [crudeExponentEc_eq hω_re (Complex.ofReal_ne_zero.mpr hx_pos.ne')]
      have hx_norm : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx_pos.le]
      have hx_re : (x : ℂ).re = x := Complex.ofReal_re x
      have hx_arg : (x : ℂ).arg = 0 := Complex.arg_ofReal_of_nonneg hx_pos.le
      have hω_re_eq : (chartOmega (Complex.I * (τ : ℂ))).re = edgeMu τ := by
        rw [chartOmega_left_edge]
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
      have h3mu : 3 * (chartOmega (Complex.I * (τ : ℂ))).re / Real.pi = edgeX0 τ := by
        rw [hω_re_eq]; unfold edgeMu; field_simp [Real.pi_pos.ne']
      rw [hx_norm, hx_re, hx_arg, h3mu]
      simp
    rw [hE_eq]; rfl
  have hphi_eq : -chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ) =
      (edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ) := by
    apply Complex.ext
    · simpa [Complex.neg_re, Complex.sub_re, Complex.mul_re] using hphi_re
    · dsimp [x]; simp [edgePhi, Complex.mul_im]
  have htipL_eq : tipL (x : ℂ) = ((Bessel.besselL x : ℝ) : ℂ) := by
    unfold tipL Bessel.besselL; push_cast; ring
  have hexp_L : Complex.exp ((c' : ℂ) * tipL (x : ℂ)) =
      ((Real.exp (c' * Bessel.besselL x) : ℝ) : ℂ) := by
    rw [htipL_eq, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  unfold edgeKernelK edgeA1 edgeA2
  simp only [ht, ↓reduceIte]
  change Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
      (Complex.Gamma z * (virasoroProblem.cardyV (c' / 12) t : ℂ)) =
    (stirlingS c' ω)⁻¹ *
      (((1 / √t * Real.exp (c' * Bessel.besselL x) /
        virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)) *
      Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ)))
  rw [show Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) /
        (Complex.Gamma z * (virasoroProblem.cardyV (c' / 12) t : ℂ)) =
      Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        ((2 * (Real.pi : ℂ)) ^ z * (t : ℂ) ^ (z - 1) / Complex.Gamma z) /
        (virasoroProblem.cardyV (c' / 12) t : ℂ) by ring,
    hratio, hthalf_c]
  have hexp_split : Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ))) =
      Complex.exp ((c' : ℂ) * tipL (x : ℂ)) *
        Complex.exp ((c' : ℂ) * (-chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    unfold chartPhiV
    change -(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ)) +
        -((c' : ℂ) * stirlingJ ω (x : ℂ)) =
      (c' : ℂ) * tipL (x : ℂ) +
        (c' : ℂ) * -(chartUpsilon (Complex.I * (τ : ℂ)) + stirlingJ ω (x : ℂ) + tipL (x : ℂ))
    dsimp [ω]; ring
  calc Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        ((stirlingS c' ω)⁻¹ * ((1 / √t : ℝ) : ℂ) *
          Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ)))) /
        (virasoroProblem.cardyV (c' / 12) t : ℂ)
      = (stirlingS c' ω)⁻¹ * (((1 / √t : ℝ) : ℂ) / (virasoroProblem.cardyV (c' / 12) t : ℂ)) *
          (Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
            Complex.exp (-((c' : ℂ) * stirlingJ ω (x : ℂ)))) := by ring
    _ = (stirlingS c' ω)⁻¹ * (((1 / √t : ℝ) : ℂ) / (virasoroProblem.cardyV (c' / 12) t : ℂ)) *
          (Complex.exp ((c' : ℂ) * tipL (x : ℂ)) *
            Complex.exp ((c' : ℂ) * (-chartPhiV (Complex.I * (τ : ℂ)) (x : ℂ)))) := by rw [hexp_split]
    _ = (stirlingS c' ω)⁻¹ * (((1 / √t * Real.exp (c' * Bessel.besselL x) /
            virasoroProblem.cardyV (c' / 12) t : ℝ) : ℂ)) *
          Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) - Complex.I * (edgePhi c' τ t : ℂ))) := by
          rw [hexp_L, hphi_eq]
          push_cast; ring

lemma edgeX0_pos_all (τ : ℝ) : 0 < edgeX0 τ := by
  rcases le_total 0 τ with h | h
  · exact edgeX0_pos h
  · rw [← edgeX0_even]; exact edgeX0_pos (by linarith)

lemma xiStar_le_edgeX0_all (τ : ℝ) : xiStar ≤ edgeX0 τ := by
  rcases le_total 0 τ with h | h
  · exact xiStar_le_edgeX0 h
  · rw [← edgeX0_even]; exact xiStar_le_edgeX0 (by linarith)

lemma edgeKernelK_factorization_theta {c' : ℝ} (hc' : 24 ≤ c') (τ : ℝ) {t : ℝ} (ht : 0 < t) :
    edgeKernelK c' τ t =
      edgeA1 c' τ * (edgeA2 c' t : ℂ) *
        Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) + Complex.I * (edgeTheta c' τ t : ℂ))) := by
  rw [edgeKernelK_factorization hc' τ ht]
  congr 2
  unfold edgeTheta
  push_cast; ring

lemma edgeRV_nonpos {c' τ t : ℝ} (ht : 0 < t) (hc' : 0 < c') : edgeRV c' τ t ≤ 0 := by
  unfold edgeRV
  rw [neg_nonpos]
  exact crudeDivergenceD_nonneg (edgeX0_pos_all τ) (Real.sqrt_pos.mpr (by positivity))

lemma edgeRV_even (c' τ t : ℝ) : edgeRV c' (-τ) t = edgeRV c' τ t := by
  unfold edgeRV; rw [edgeX0_even]

lemma edgeRV_continuousOn (c' t : ℝ) : ContinuousOn (fun τ => edgeRV c' τ t) (Ioi 0) := by
  unfold edgeRV crudeDivergenceD
  have hx0_cont : Continuous edgeX0 :=
    continuous_iff_continuousAt.mpr fun s => (hasDerivAt_edgeX0 s).continuousAt
  refine Continuous.continuousOn ?_
  by_cases hrt : √(3 * t / c') = 0
  · simp only [hrt, zero_div, Real.log_zero, mul_zero, sub_zero]
    exact (continuous_const.mul (continuous_const.sub hx0_cont)).neg
  · refine (continuous_const.mul ((continuous_const.sub hx0_cont).sub (hx0_cont.mul ?_))).neg
    rw [continuous_iff_continuousAt]
    intro s
    exact (continuous_const.div hx0_cont fun r => (edgeX0_pos_all r).ne').continuousAt.log
      (div_ne_zero hrt (edgeX0_pos_all s).ne')

/-- Explicit left-edge stationary time `τ₀(t)` (`0` when `√(3 t / c') ≤ ξ_*`, and the unique
nonnegative solution of `x₀(τ) = √(3 t / c')` otherwise). -/
noncomputable def edgeTau0 (c' t : ℝ) : ℝ :=
  if √(3 * t / c') ≤ xiStar then 0
  else Real.arcosh (Real.sinh (Real.pi * √(3 * t / c')) ^ 2) / Real.pi

lemma edgeTau0_nonneg (c' t : ℝ) : 0 ≤ edgeTau0 c' t := by
  unfold edgeTau0
  split_ifs with h
  · exact le_rfl
  · have hx : xiStar < √(3 * t / c') := lt_of_not_ge h
    have hs_xi : Real.sinh (Real.pi * xiStar) = 1 := by
      have h0 := sinh_pi_edgeX0 0
      rw [edgeX0_zero, mul_zero, Real.cosh_zero, Real.sqrt_one] at h0
      exact h0
    have hs_gt : 1 < Real.sinh (Real.pi * √(3 * t / c')) :=
      hs_xi ▸ Real.sinh_strictMono (mul_lt_mul_of_pos_left hx Real.pi_pos)
    have hs2_ge : 1 ≤ Real.sinh (Real.pi * √(3 * t / c')) ^ 2 := by nlinarith
    exact div_nonneg (Real.arcosh_nonneg hs2_ge) Real.pi_pos.le

lemma edgeX0_strictMonoOn : StrictMonoOn edgeX0 (Ici 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 0)
    (continuous_iff_continuousAt.mpr fun s => (hasDerivAt_edgeX0 s).continuousAt).continuousOn
    fun τ hτ => ?_
  rw [interior_Ici] at hτ
  rw [(hasDerivAt_edgeX0 τ).deriv, edgeX0Deriv_eq_of_nonneg hτ.le]
  have hc_gt : 1 < Real.cosh (Real.pi * τ) := by
    have : Real.cosh 0 < Real.cosh (Real.pi * τ) := by
      have hmul : 0 < Real.pi * τ := mul_pos Real.pi_pos (mem_Ioi.mp hτ)
      rw [Real.cosh_zero]
      exact Real.one_lt_cosh.mpr hmul.ne'
    simpa [Real.cosh_zero] using this
  have hc_inv : 1 / Real.cosh (Real.pi * τ) < 1 := by
    rw [div_lt_one (Real.cosh_pos _)]
    exact hc_gt
  have hsub : 0 < 1 - 1 / Real.cosh (Real.pi * τ) := by linarith
  positivity

lemma edgeX0_edgeTau0 {c' t : ℝ} (_hc' : 0 < c') (hx : xiStar < √(3 * t / c')) :
    0 < edgeTau0 c' t ∧ edgeX0 (edgeTau0 c' t) = √(3 * t / c') := by
  have hnot : ¬ √(3 * t / c') ≤ xiStar := not_le.mpr hx
  unfold edgeTau0
  simp only [hnot, ↓reduceIte]
  set x : ℝ := √(3 * t / c')
  have hs_gt : 1 < Real.sinh (Real.pi * x) := by
    have hpi_lt : Real.pi * xiStar < Real.pi * x := mul_lt_mul_of_pos_left hx Real.pi_pos
    have hs_xi : Real.sinh (Real.pi * xiStar) = 1 := by
      have h := sinh_pi_edgeX0 0
      rw [edgeX0_zero, mul_zero, Real.cosh_zero, Real.sqrt_one] at h
      exact h
    exact hs_xi ▸ Real.sinh_strictMono hpi_lt
  have hs2_gt : 1 < Real.sinh (Real.pi * x) ^ 2 := by nlinarith
  have har_pos : 0 < Real.arcosh (Real.sinh (Real.pi * x) ^ 2) := by
    have h0 : (0 : ℝ) ≤ Real.arcosh (Real.sinh (Real.pi * x) ^ 2) := Real.arcosh_nonneg hs2_gt.le
    rcases eq_or_lt_of_le h0 with hzero | hpos
    · have hcosh := Real.cosh_arcosh hs2_gt.le
      rw [← hzero, Real.cosh_zero] at hcosh
      linarith
    · exact hpos
  have hτ_pos : 0 < Real.arcosh (Real.sinh (Real.pi * x) ^ 2) / Real.pi :=
    div_pos har_pos Real.pi_pos
  refine ⟨hτ_pos, ?_⟩
  unfold edgeX0
  rw [mul_comm Real.pi _, div_mul_cancel₀ _ Real.pi_pos.ne', Real.cosh_arcosh hs2_gt.le,
    Real.sqrt_sq (by linarith [hs_gt]), Real.arsinh_sinh (Real.pi * x),
    mul_div_cancel_left₀ _ Real.pi_pos.ne']

lemma edgeRV_unimodal {c' t : ℝ} (hc' : 0 < c') (ht : 0 < t) :
    MonotoneOn (fun τ => edgeRV c' τ t) (Ioi 0 ∩ Iic (edgeTau0 c' t)) ∧
    AntitoneOn (fun τ => edgeRV c' τ t) (Ioi 0 ∩ Ici (edgeTau0 c' t)) := by
  let x : ℝ := √(3 * t / c')
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  let g : ℝ → ℝ := fun y => -(2 * Real.pi / 3) * (x - y - y * Real.log (x / y))
  have hg_eq : ∀ τ : ℝ, edgeRV c' τ t = g (edgeX0 τ) := fun τ => by
    unfold edgeRV crudeDivergenceD; dsimp [g, x]; ring
  have hg_deriv : ∀ y > 0, HasDerivAt g ((2 * Real.pi / 3) * Real.log (x / y)) y := by
    intro y hy
    have hlog : HasDerivAt (fun u : ℝ => Real.log (x / u)) (-1 / y) y := by
      have hdiv : HasDerivAt (fun u : ℝ => x / u) (-x / y ^ 2) y := by
        have h1 := (hasDerivAt_inv hy.ne').const_mul x
        have heq : (fun u : ℝ => x * u⁻¹) = fun u => x / u := by ext u; ring
        rw [heq] at h1
        exact h1.congr_deriv (by ring)
      have h1 := hdiv.log (div_pos hx_pos hy).ne'
      refine h1.congr_deriv ?_
      field_simp [hx_pos.ne', hy.ne']
    have hprod : HasDerivAt (fun u : ℝ => u * Real.log (x / u))
        (1 * Real.log (x / y) + y * (-1 / y)) y :=
      (hasDerivAt_id y).mul hlog
    have hinner : HasDerivAt (fun u : ℝ => x - u - u * Real.log (x / u))
        (0 - 1 - (1 * Real.log (x / y) + y * (-1 / y))) y :=
      ((hasDerivAt_const y x).sub (hasDerivAt_id y)).sub hprod
    refine (hinner.const_mul (-(2 * Real.pi / 3))).congr_deriv ?_
    field_simp [hy.ne']
    ring
  have hg_mono : MonotoneOn g (Ioc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 x) ?_ ?_ ?_
    · intro y hy
      exact (hg_deriv y (mem_Ioc.mp hy).1).continuousAt.continuousWithinAt
    · intro y hy
      exact (hg_deriv y (mem_Ioc.mp (interior_subset hy)).1).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ioc] at hy
      rw [(hg_deriv y hy.1).deriv]
      have h1 : 1 ≤ x / y := (one_le_div hy.1).mpr hy.2.le
      exact mul_nonneg (by positivity) (Real.log_nonneg h1)
  have hg_anti : AntitoneOn g (Ici x) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici x) ?_ ?_ ?_
    · intro y hy
      exact (hg_deriv y (lt_of_lt_of_le hx_pos (mem_Ici.mp hy))).continuousAt.continuousWithinAt
    · intro y hy
      have hy_gt : x < y := by simpa [interior_Ici] using hy
      exact (hg_deriv y (lt_trans hx_pos hy_gt)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      have hy_pos : 0 < y := lt_trans hx_pos hy
      rw [(hg_deriv y hy_pos).deriv]
      have h1 : x / y ≤ 1 := (div_le_one hy_pos).mpr hy.le
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Real.log_nonpos (div_pos hx_pos hy_pos).le h1)
  constructor
  · intro τ₁ h₁ τ₂ h₂ h₁₂
    dsimp only
    rw [hg_eq τ₁, hg_eq τ₂]
    by_cases hx_le : x ≤ xiStar
    · have h0 : edgeTau0 c' t = 0 := by unfold edgeTau0; simp only [show √(3 * t / c') = x by rfl, hx_le, ↓reduceIte]
      exfalso; linarith [mem_Ioi.mp h₁.1, mem_Iic.mp h₁.2, h0]
    · have hxe := (edgeX0_edgeTau0 hc' (not_le.mp hx_le)).2
      change edgeX0 (edgeTau0 c' t) = x at hxe
      have hm1 : edgeX0 τ₁ ∈ Ioc 0 x := by
        refine ⟨edgeX0_pos h₁.1.le, ?_⟩
        rw [← hxe]
        exact edgeX0_strictMonoOn.monotoneOn h₁.1.le (edgeTau0_nonneg c' t) h₁.2
      have hm2 : edgeX0 τ₂ ∈ Ioc 0 x := by
        refine ⟨edgeX0_pos h₂.1.le, ?_⟩
        rw [← hxe]
        exact edgeX0_strictMonoOn.monotoneOn h₂.1.le (edgeTau0_nonneg c' t) h₂.2
      exact hg_mono hm1 hm2 (edgeX0_strictMonoOn.monotoneOn h₁.1.le h₂.1.le h₁₂)
  · intro τ₁ h₁ τ₂ h₂ h₁₂
    dsimp only
    rw [hg_eq τ₁, hg_eq τ₂]
    have hx_le_1 : x ≤ edgeX0 τ₁ := by
      by_cases hx_le : x ≤ xiStar
      · exact hx_le.trans (xiStar_le_edgeX0 h₁.1.le)
      · have hxe := (edgeX0_edgeTau0 hc' (not_le.mp hx_le)).2
        change edgeX0 (edgeTau0 c' t) = x at hxe
        rw [← hxe]
        exact edgeX0_strictMonoOn.monotoneOn (edgeTau0_nonneg c' t) h₁.1.le h₁.2
    have hm1 : edgeX0 τ₁ ∈ Ici x := hx_le_1
    have hm2 : edgeX0 τ₂ ∈ Ici x :=
      hx_le_1.trans (edgeX0_strictMonoOn.monotoneOn h₁.1.le h₂.1.le h₁₂)
    exact hg_anti hm1 hm2 (edgeX0_strictMonoOn.monotoneOn h₁.1.le h₂.1.le h₁₂)

lemma edgePhi_odd {c' τ t : ℝ} (hc' : 0 < c') (ht : 0 < t) :
    edgePhi c' (-τ) t = -edgePhi c' τ t := by
  have hx_pos : 0 < √(3 * t / c') := Real.sqrt_pos.mpr (by positivity)
  have hω_re : 0 ≤ (chartOmega (Complex.I * (τ : ℂ))).re := by
    rw [chartOmega_left_edge]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact (lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)).le
  have hconj := chartPhiV_conj (ζ := Complex.I * (τ : ℂ)) (by simp) (by simp) hω_re hx_pos
  have hstar : starRingEnd ℂ (Complex.I * (τ : ℂ)) = Complex.I * ((-τ : ℝ) : ℂ) := by
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  rw [hstar] at hconj
  unfold edgePhi
  rw [hconj, Complex.conj_im]

lemma hasDerivAt_chartOmega_left_edge (τ : ℝ) :
    HasDerivAt (fun s : ℝ => chartOmega (Complex.I * (s : ℂ)))
      ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)) τ := by
  have heq : (fun s : ℝ => chartOmega (Complex.I * (s : ℂ))) =
      fun s : ℝ => (edgeMu s : ℂ) - Complex.I * (edgeNu s : ℂ) :=
    funext chartOmega_left_edge
  rw [heq]
  exact (hasDerivAt_edgeMu τ).ofReal_comp.sub ((hasDerivAt_edgeNu τ).ofReal_comp.const_mul Complex.I)

lemma hasDerivAt_edgePhi {c' t : ℝ} (hc' : 0 < c') (ht : 0 < t) (τ : ℝ) :
    HasDerivAt (fun s => edgePhi c' s t)
      (2 * edgeNuDeriv τ * Real.log (√(3 * t / c') / edgeX0 τ)) τ := by
  let x : ℝ := √(3 * t / c')
  have hx_pos : 0 < x := Real.sqrt_pos.mpr (by positivity)
  have hS5 := (lemma_S5_deriv (b := (x : ℂ)) (by simpa using hx_pos)).2.2
  have hζ_ne : Complex.I * (τ : ℂ) ≠ (1 / 2 : ℂ) := by
    intro h; have := congrArg Complex.re h; simp at this
  have hd_within := hS5 (Complex.I * (τ : ℂ)) (by simp) (by simp) hζ_ne
  have hmap : ∀ᶠ s : ℝ in 𝓝 τ, Complex.I * (s : ℂ) ∈ {w : ℂ | 0 ≤ w.re ∧ w.re ≤ 1 / 2} :=
    Filter.Eventually.of_forall fun s => by simp
  have hline : HasDerivAt (fun s : ℝ => Complex.I * (s : ℂ)) Complex.I τ :=
    ((Complex.ofRealCLM.hasDerivAt (x := τ)).const_mul Complex.I).congr_deriv (by simp)
  have hcomp_c := hd_within.comp_hasDerivAt τ hline hmap
  have hd_om : HasDerivAt chartOmega (deriv chartOmega (Complex.I * (τ : ℂ)))
      (Complex.I * (τ : ℂ)) :=
    (analyticAt_chartOmega (by simp) (by simp)).differentiableAt.hasDerivAt
  have hcomp := hd_om.comp τ hline
  have hderiv_om_I : deriv chartOmega (Complex.I * (τ : ℂ)) * Complex.I =
      (edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ) :=
    hcomp.unique (hasDerivAt_chartOmega_left_edge τ)
  have hlog_b : Complex.log (chartB (Complex.I * (τ : ℂ)) / (x : ℂ)) =
      (Real.log (edgeX0 τ / x) : ℂ) := by
    rw [chartB_left_edge]
    have hdiv_pos : 0 < edgeX0 τ / x := div_pos (edgeX0_pos_all τ) hx_pos
    rw [show (edgeX0 τ : ℂ) / (x : ℂ) = ((edgeX0 τ / x : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_log hdiv_pos.le).symm
  have hd_phi_c : HasDerivAt (fun s : ℝ => chartPhiV (Complex.I * (s : ℂ)) (x : ℂ))
      (2 * (Real.log (edgeX0 τ / x) : ℂ) *
        ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))) τ := by
    refine hcomp_c.congr_deriv ?_
    rw [hlog_b, mul_assoc, hderiv_om_I]
  have hd_im := Complex.imCLM.hasFDerivAt.comp_hasDerivAt τ hd_phi_c
  refine hd_im.congr_deriv ?_
  have him_val : (2 * (Real.log (edgeX0 τ / x) : ℂ) *
      ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))).im =
      -2 * Real.log (edgeX0 τ / x) * edgeNuDeriv τ := by
    simp only [Complex.mul_im, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re, Complex.sub_im,
      Complex.I_re, Complex.I_im]
    ring
  change (2 * (Real.log (edgeX0 τ / x) : ℂ) *
      ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))).im =
      2 * edgeNuDeriv τ * Real.log (x / edgeX0 τ)
  rw [him_val, show edgeX0 τ / x = (x / edgeX0 τ)⁻¹ by rw [inv_div], Real.log_inv]
  ring

lemma hasDerivAt_edgeTheta {c' t : ℝ} (hc' : 0 < c') (ht : 0 < t) (τ : ℝ) :
    HasDerivAt (fun s => edgeTheta c' s t)
      (2 * edgeNuDeriv τ * Real.log (edgeX0 τ / √(3 * t / c'))) τ := by
  have hd := (hasDerivAt_edgePhi hc' ht τ).neg
  refine hd.congr_deriv ?_
  rw [show √(3 * t / c') / edgeX0 τ = (edgeX0 τ / √(3 * t / c'))⁻¹ by rw [inv_div],
    Real.log_inv]
  ring

lemma edgeA1_norm_le {c' : ℝ} (hc' : 48 / muStar ≤ c') (τ : ℝ) :
    ‖edgeA1 c' τ‖ ≤ 2 := by
  have hc'_pos : 0 < c' := lt_of_lt_of_le (div_pos (by norm_num) muStar_pos) hc'
  have hω_re : 0 ≤ (chartOmega (Complex.I * (τ : ℂ))).re := by
    rw [chartOmega_left_edge]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact (lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)).le
  have hmu_norm : muStar ≤ ‖chartOmega (Complex.I * (τ : ℂ))‖ := by
    calc muStar ≤ edgeMu τ := edgeMu_ge_muStar τ
      _ = (chartOmega (Complex.I * (τ : ℂ))).re := by
          rw [chartOmega_left_edge]
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
      _ ≤ ‖chartOmega (Complex.I * (τ : ℂ))‖ := Complex.re_le_norm _
  have h48 : 48 ≤ c' * ‖chartOmega (Complex.I * (τ : ℂ))‖ := by
    calc (48 : ℝ) = (48 / muStar) * muStar := by field_simp [muStar_pos.ne']
      _ ≤ c' * ‖chartOmega (Complex.I * (τ : ℂ))‖ :=
          mul_le_mul hc' hmu_norm muStar_pos.le hc'_pos.le
  exact norm_stirlingS_inv_le hc'_pos hω_re h48

private lemma abs_edgeMuDeriv_le (τ : ℝ) : |edgeMuDeriv τ| ≤ Real.pi / 6 := by
  have habs : |edgeMuDeriv τ| = (Real.pi / 3) * |edgeX0Deriv τ| := by
    unfold edgeMuDeriv; rw [abs_mul, abs_of_pos (by positivity)]
  have hxd : |edgeX0Deriv τ| ≤ 1 / 2 := by
    rcases le_or_gt 0 τ with h | h
    · rw [abs_of_nonneg (edgeX0Deriv_nonneg h)]
      exact edgeX0Deriv_le_half h
    · have hm : 0 ≤ -τ := by linarith
      have hev : edgeX0Deriv τ = -edgeX0Deriv (-τ) := by
        calc edgeX0Deriv τ = edgeX0Deriv (-(-τ)) := by rw [neg_neg]
          _ = -edgeX0Deriv (-τ) := edgeX0Deriv_even (-τ)
      rw [hev, abs_neg, abs_of_nonneg (edgeX0Deriv_nonneg hm)]
      exact edgeX0Deriv_le_half hm
  rw [habs]
  calc (Real.pi / 3) * |edgeX0Deriv τ| ≤ (Real.pi / 3) * (1 / 2) :=
        mul_le_mul_of_nonneg_left hxd (by positivity)
    _ = Real.pi / 6 := by ring

lemma edgeA1_deriv_bounds :
    ∃ C_A1' : ℝ, 0 < C_A1' ∧ ∀ {c' : ℝ}, 48 / muStar ≤ c' →
      ∀ τ : ℝ, ∃ d : ℂ, HasDerivAt (edgeA1 c') d τ ∧
        ‖d‖ ≤ C_A1' / (c' * (1 + |τ|) ^ 3) := by
  obtain ⟨c_ω, hc_ω_pos, hω_ge⟩ := norm_chartOmega_left_edge_ge
  obtain ⟨cnu₁, cnu₂, _, hcnu₂_pos, hnu_as⟩ := lemma_J4_0.2.2.2.2.1
  let C_ω' : ℝ := Real.pi / 6 + cnu₂
  have hC_ω'_pos : 0 < C_ω' := by have := Real.pi_pos; positivity
  let C_A1' : ℝ := (7 / 2) * C_ω' / c_ω ^ 2
  refine ⟨C_A1', by positivity, fun {c'} hc' τ => ?_⟩
  have hc'_pos : 0 < c' := lt_of_lt_of_le (div_pos (by norm_num) muStar_pos) hc'
  let ω : ℂ := chartOmega (Complex.I * (τ : ℂ))
  have hω_re : 0 < ω.re := by
    dsimp [ω]; rw [chartOmega_left_edge]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
  have hω_ne : ω ≠ 0 := by intro h; rw [h, Complex.zero_re] at hω_re; exact lt_irrefl 0 hω_re
  have hd_logS : HasDerivAt (stirlingLogS c') (deriv (stirlingLogS c') ω) ω :=
    (hasDerivAt_stirlingLogS hc'_pos hω_re.le hω_ne).differentiableAt.hasDerivAt
  have hd_comp := hd_logS.comp τ (hasDerivAt_chartOmega_left_edge τ)
  have heq : edgeA1 c' =
      fun s : ℝ => Complex.exp (-stirlingLogS c' (chartOmega (Complex.I * (s : ℂ)))) := by
    ext s; unfold edgeA1 stirlingS; rw [Complex.exp_neg]
  have hd_A1 : HasDerivAt (edgeA1 c')
      (-(deriv (stirlingLogS c') ω * ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))) *
        edgeA1 c' τ) τ := by
    rw [heq]
    refine (hd_comp.neg.cexp).congr_deriv ?_
    dsimp [edgeA1, stirlingS, ω]
    rw [Complex.exp_neg]
    ring
  refine ⟨_, hd_A1, ?_⟩
  have hmu_norm : muStar ≤ ‖ω‖ := by
    calc muStar ≤ edgeMu τ := edgeMu_ge_muStar τ
      _ = ω.re := by
          dsimp [ω]; rw [chartOmega_left_edge]
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
      _ ≤ ‖ω‖ := Complex.re_le_norm ω
  have h1_cω : 1 ≤ c' * ‖ω‖ := by
    calc (1 : ℝ) ≤ 48 := by norm_num
      _ = (48 / muStar) * muStar := by field_simp [muStar_pos.ne']
      _ ≤ c' * ‖ω‖ := mul_le_mul hc' hmu_norm muStar_pos.le hc'_pos.le
  have hd_log_bd : ‖deriv (stirlingLogS c') ω‖ ≤ (7 / 4 : ℝ) / (c' * ‖ω‖ ^ 2) :=
    norm_deriv_stirlingLogS_le hc'_pos hω_re.le h1_cω
  have hω'_bd : ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖ ≤ C_ω' * (1 + |τ|) := by
    have hmu_d : |edgeMuDeriv τ| ≤ Real.pi / 6 := abs_edgeMuDeriv_le τ
    have hnu_d : |edgeNuDeriv τ| ≤ cnu₂ * (1 + |τ|) := by
      have hnd : edgeNuDeriv τ = edgeNuDeriv |τ| := by
        rcases le_total 0 τ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, edgeNuDeriv_even]
      rw [hnd]
      have h1 := (hnu_as |τ| (abs_nonneg τ)).2
      have h2 := (hnu_as |τ| (abs_nonneg τ)).1
      have hpos : 0 ≤ edgeNuDeriv |τ| := by
        have : 0 < cnu₁ * (1 + |τ|) := by positivity
        linarith
      rwa [abs_of_nonneg hpos]
    calc ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖
        ≤ ‖(edgeMuDeriv τ : ℂ)‖ + ‖Complex.I * (edgeNuDeriv τ : ℂ)‖ := norm_sub_le _ _
      _ = |edgeMuDeriv τ| + |edgeNuDeriv τ| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (Real.pi / 6) * 1 + cnu₂ * (1 + |τ|) := by linarith
      _ ≤ (Real.pi / 6) * (1 + |τ|) + cnu₂ * (1 + |τ|) := by
          gcongr; linarith [abs_nonneg τ]
      _ = C_ω' * (1 + |τ|) := by dsimp [C_ω']; ring
  have hA1_bd : ‖edgeA1 c' τ‖ ≤ 2 := edgeA1_norm_le hc' τ
  have hω_lb := hω_ge τ
  have h1t : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
  have hden_le : c' * (c_ω * (1 + |τ|) ^ 2) ^ 2 ≤ c' * ‖ω‖ ^ 2 := by
    gcongr
  calc ‖-(deriv (stirlingLogS c') ω * ((edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ))) *
          edgeA1 c' τ‖
      = ‖deriv (stirlingLogS c') ω‖ * ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖ *
          ‖edgeA1 c' τ‖ := by rw [norm_mul, norm_neg, norm_mul]
    _ ≤ ((7 / 4 : ℝ) / (c' * ‖ω‖ ^ 2)) * (C_ω' * (1 + |τ|)) * 2 := by
        gcongr
    _ ≤ ((7 / 4 : ℝ) / (c' * (c_ω * (1 + |τ|) ^ 2) ^ 2)) * (C_ω' * (1 + |τ|)) * 2 := by
        gcongr
    _ = C_A1' / (c' * (1 + |τ|) ^ 3) := by
        dsimp [C_A1']
        field_simp [hc'_pos.ne', hc_ω_pos.ne', (by linarith : (1 + |τ|) ≠ 0)]
        ring

lemma edgeA2_norm_le {c' : ℝ} (hc' : 10000 ≤ c') {t : ℝ} (ht : 0 < t)
    (hx_lo : xiStar / 2 ≤ √(3 * t / c')) :
    0 ≤ edgeA2 c' t ∧ edgeA2 c' t ≤ 6 * Real.pi * √10 := by
  have hc'_pos : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let x : ℝ := √(3 * t / c')
  have ht_eq : t = c' * x ^ 2 / 3 := by
    dsimp [x]; rw [Real.sq_sqrt (by positivity)]; field_simp [hc'_pos.ne']
  have hcomp := Bessel.besselV_comparison hc' hx_lo
  have hV_eq : virasoroProblem.cardyV (c' / 12) t = Bessel.besselV (c' / 12) t :=
    virasoro_cardyV_eq_besselV ha ht.le
  have hA2_eq : edgeA2 c' t =
      1 / √(c' * x ^ 2 / 3) * Real.exp (c' * Bessel.besselL x) /
        Bessel.besselV (c' / 12) (c' * x ^ 2 / 3) := by
    unfold edgeA2
    rw [hV_eq, ← ht_eq]
  have hx10 : (1 / 10 : ℝ) ≤ x := by
    have := Bessel.one_fifth_le_xiStar
    dsimp [x] at hx_lo ⊢
    linarith
  have hsqrt_x : (1 / √10 : ℝ) ≤ √x := by
    have := Real.sqrt_le_sqrt hx10
    rwa [Real.sqrt_div (by norm_num), Real.sqrt_one] at this
  have hpi_le : 6 * Real.pi / √x ≤ 6 * Real.pi * √10 := by
    rw [div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))]
    have hsq10 : √10 * (1 / √10) = 1 := by
      field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 10)]
    calc 6 * Real.pi = (6 * Real.pi * √10) * (1 / √10) := by rw [mul_assoc, hsq10, mul_one]
      _ ≤ (6 * Real.pi * √10) * √x := by gcongr
  rw [hA2_eq]
  refine ⟨le_trans (by positivity) hcomp.1, hcomp.2.trans hpi_le⟩

/-- Sub-Cardy kernel bound (`lower_o1_two_edge.tex`, Lemma J4.2): for `c' ≥ c₀` and
`0 < t ≤ c' (ξ_*/2)^2 / 3`, `‖edgeKernelK c' τ t‖ ≤ C_sub exp(-κ_sub c')` uniformly in `τ`. -/
lemma edgeKernelK_subCardy_bound :
    ∃ C_sub κ_sub c₀ : ℝ, 0 < C_sub ∧ 0 < κ_sub ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
        ∀ τ : ℝ, ‖edgeKernelK c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c') := by
  let x_c : ℝ := xiStar / 2
  have hxc_lb : (1 / 10 : ℝ) ≤ x_c := by
    dsimp [x_c]; linarith [Bessel.one_fifth_le_xiStar]
  have hxc_pos : 0 < x_c := by linarith
  let κ_D : ℝ := (2 * Real.pi / 3) * x_c * (2 * Real.log 2 - 1)
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h1 : (1 : ℝ) < Real.log 4 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      exact hexp
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hlog2 : 0 < 2 * Real.log 2 - 1 := by
    have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have h1 : (1 : ℝ) < Real.log 4 := by
      rw [← Real.exp_lt_exp, Real.exp_log (by norm_num)]
      exact hexp
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    linarith
  have hκD_pos : 0 < κ_D := by
    dsimp [κ_D]; have := Real.pi_pos; positivity
  let c₀ : ℝ := max 10000 (48 / muStar)
  have hc₀_ge : 10000 ≤ c₀ := le_max_left _ _
  have hc₀_mu : 48 / muStar ≤ c₀ := le_max_right _ _
  let K_rem : ℝ := 2 * ((2 / 144) * Real.exp (16 * Real.pi * x_c) * Real.exp 4 *
    (Real.exp 1) ^ 2 / (2 * Real.pi * x_c / 3 - 6 / 10000)) * (1 / √(x_c ^ 2 / 3))
  have hden_pos : 0 < 2 * Real.pi * x_c / 3 - 6 / 10000 := by
    have hpi_xi := Bessel.three_quarters_le_pi_mul_xiStar
    dsimp [x_c]
    linarith [Real.pi_pos]
  have hKrem_pos : 0 < K_rem := by
    dsimp [K_rem]; positivity
  let κ_sub : ℝ := κ_D / 2
  let C_sub : ℝ := K_rem * (2 / κ_D)
  refine ⟨C_sub, κ_sub, c₀, by positivity, by positivity, hc₀_ge,
    fun {c'} hc' {t} ht hx_le τ => ?_⟩
  have hc'_10000 : 10000 ≤ c' := hc₀_ge.trans hc'
  have hc'_mu : 48 / muStar ≤ c' := hc₀_mu.trans hc'
  have hc'_pos : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  let t_c : ℝ := c' * x_c ^ 2 / 3
  have htc_pos : 0 < t_c := by positivity
  have ht_le_tc : t ≤ t_c := by
    have hsq : 3 * t / c' ≤ x_c ^ 2 := by
      calc 3 * t / c' = (√(3 * t / c')) ^ 2 := (Real.sq_sqrt (by positivity)).symm
        _ ≤ x_c ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hx_le 2
    rw [div_le_iff₀ hc'_pos] at hsq
    dsimp [t_c]
    linarith
  let r : ℝ := Real.pi * c' * x_c / 3
  have hr_ge : 1250 ≤ r := by
    have := Bessel.three_quarters_le_pi_mul_xiStar
    dsimp [r, x_c]
    nlinarith
  let k : ℕ := Nat.floor r
  have hk_le_r : (k : ℝ) ≤ r := Nat.floor_le (by linarith)
  have hr_lt_k1 : r < (k : ℝ) + 1 := Nat.lt_floor_add_one r
  have hk_ge_1250 : 1250 ≤ k := Nat.le_floor hr_ge
  have hk_ge_2 : 2 ≤ k := by omega
  let m : ℕ := k - 2
  have hk_eq : k = m + 2 := by omega
  have hm_ge_1 : 1 ≤ m := by omega
  let ω : ℂ := chartOmega (Complex.I * (τ : ℂ))
  let z : ℂ := 1 / 2 + (c' : ℂ) * ω
  have hω_re_ge : muStar ≤ ω.re := by
    dsimp [ω]; rw [chartOmega_left_edge]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact edgeMu_ge_muStar τ
  have hz_re_sub : (k : ℝ) ≤ z.re - 1 := by
    have h1 : z.re - 1 = c' * ω.re - 1 / 2 := by
      dsimp [z]
      simp only [Complex.div_ofNat_re, Complex.one_re, Complex.re_ofReal_mul]
      ring
    have hmu_eq : muStar = 2 * (Real.pi * x_c / 3) := by
      unfold muStar; dsimp [x_c]; ring
    have h2 : 2 * r = c' * muStar := by dsimp [r]; rw [hmu_eq]; ring
    linarith [mul_le_mul_of_nonneg_left hω_re_ge hc'_pos.le]
  have hv_pos : 0 < Bessel.besselVCoeff (c' / 12) k := besselVCoeff_pos ha hk_ge_2
  have hV_lb : Bessel.besselVCoeff (c' / 12) k * t ^ k ≤ virasoroProblem.cardyV (c' / 12) t :=
    besselVCoeff_mul_pow_le_cardyV ha ht.le k
  have hpow_mono : t ^ (z.re - 1) / t ^ k ≤ t_c ^ (z.re - 1) / t_c ^ k := by
    have hdiv1 : t ^ (z.re - 1) / t ^ k = t ^ (z.re - 1 - (k : ℝ)) := by
      rw [← Real.rpow_natCast t k, ← Real.rpow_sub ht]
    have hdiv2 : t_c ^ (z.re - 1) / t_c ^ k = t_c ^ (z.re - 1 - (k : ℝ)) := by
      rw [← Real.rpow_natCast t_c k, ← Real.rpow_sub htc_pos]
    rw [hdiv1, hdiv2]
    exact Real.rpow_le_rpow ht.le ht_le_tc (by linarith)
  have hV_tc_pos : 0 < virasoroProblem.cardyV (c' / 12) t_c := by
    have := Integration.virasoro_cardyV_ge ha htc_pos.le
    have h8 : 0 < 8 * Real.pi ^ 4 * t_c ^ 2 := by positivity
    linarith
  have hV_t_pos : 0 < virasoroProblem.cardyV (c' / 12) t := by
    have := Integration.virasoro_cardyV_ge ha ht.le
    have h8 : 0 < 8 * Real.pi ^ 4 * t ^ 2 := by positivity
    linarith
  let P0 : ℝ := ‖Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
      (2 * (Real.pi : ℂ)) ^ z / Complex.Gamma z‖
  have hK_norm_eq : ∀ s > 0, ‖edgeKernelK c' τ s‖ =
      P0 * s ^ (z.re - 1) / virasoroProblem.cardyV (c' / 12) s := fun s hs => by
    unfold edgeKernelK
    simp only [hs, ↓reduceIte]
    have hV_s_pos : 0 < virasoroProblem.cardyV (c' / 12) s := by
      have := Integration.virasoro_cardyV_ge ha hs.le
      have h8 : 0 < 8 * Real.pi ^ 4 * s ^ 2 := by positivity
      linarith
    have hnorm_s : ‖(s : ℂ) ^ (z - 1)‖ = s ^ (z.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hs]; simp
    have hnorm_V : ‖(virasoroProblem.cardyV (c' / 12) s : ℂ)‖ =
        virasoroProblem.cardyV (c' / 12) s := by
      rw [Complex.norm_real, Real.norm_of_nonneg hV_s_pos.le]
    have hsplit : Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ z * (s : ℂ) ^ (z - 1) /
        (Complex.Gamma z * (virasoroProblem.cardyV (c' / 12) s : ℂ)) =
        (Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
          (2 * (Real.pi : ℂ)) ^ z / Complex.Gamma z) *
          (s : ℂ) ^ (z - 1) / (virasoroProblem.cardyV (c' / 12) s : ℂ) := by ring
    change ‖Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ z * (s : ℂ) ^ (z - 1) /
        (Complex.Gamma z * (virasoroProblem.cardyV (c' / 12) s : ℂ))‖ =
        P0 * s ^ (z.re - 1) / virasoroProblem.cardyV (c' / 12) s
    rw [hsplit, norm_div, norm_mul, hnorm_s, hnorm_V]
  have hK_le_tc : ‖edgeKernelK c' τ t‖ ≤
      (‖edgeKernelK c' τ t_c‖ * virasoroProblem.cardyV (c' / 12) t_c) /
        (Bessel.besselVCoeff (c' / 12) k * t_c ^ k) := by
    rw [hK_norm_eq t ht, hK_norm_eq t_c htc_pos]
    have hV_cancel : P0 * t_c ^ (z.re - 1) / virasoroProblem.cardyV (c' / 12) t_c *
        virasoroProblem.cardyV (c' / 12) t_c = P0 * t_c ^ (z.re - 1) :=
      div_mul_cancel₀ _ hV_tc_pos.ne'
    rw [hV_cancel]
    calc P0 * t ^ (z.re - 1) / virasoroProblem.cardyV (c' / 12) t
        ≤ P0 * t ^ (z.re - 1) / (Bessel.besselVCoeff (c' / 12) k * t ^ k) := by
          gcongr
      _ = P0 / Bessel.besselVCoeff (c' / 12) k * (t ^ (z.re - 1) / t ^ k) := by ring
      _ ≤ P0 / Bessel.besselVCoeff (c' / 12) k * (t_c ^ (z.re - 1) / t_c ^ k) := by
          gcongr
      _ = P0 * t_c ^ (z.re - 1) / (Bessel.besselVCoeff (c' / 12) k * t_c ^ k) := by ring
  have hfact_tc := edgeKernelK_factorization (by linarith : 24 ≤ c') τ htc_pos
  have hx_tc : √(3 * t_c / c') = x_c := by
    dsimp [t_c]; rw [show 3 * (c' * x_c ^ 2 / 3) / c' = x_c ^ 2 by field_simp [hc'_pos.ne']]
    exact Real.sqrt_sq hxc_pos.le
  have hnum_eq : ‖edgeKernelK c' τ t_c‖ * virasoroProblem.cardyV (c' / 12) t_c =
      ‖edgeA1 c' τ‖ * (1 / √t_c) * Real.exp (c' * Bessel.besselL x_c) *
        Real.exp (c' * edgeRV c' τ t_c) := by
    rw [hfact_tc]
    have hexp_norm : ‖Complex.exp ((c' : ℂ) * ((edgeRV c' τ t_c : ℂ) -
        Complex.I * (edgePhi c' τ t_c : ℂ)))‖ = Real.exp (c' * edgeRV c' τ t_c) := by
      rw [Complex.norm_exp]
      congr 1
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, zero_mul, Complex.ofReal_im, mul_zero, sub_zero]
    rw [norm_mul, norm_mul, hexp_norm, Complex.norm_real, Real.norm_of_nonneg (by
      unfold edgeA2; positivity)]
    rw [show edgeA2 c' t_c = (1 / √t_c) * Real.exp (c' * Bessel.besselL x_c) /
        virasoroProblem.cardyV (c' / 12) t_c by unfold edgeA2; rw [hx_tc]]
    field_simp [hV_tc_pos.ne']
  have hRV_le : edgeRV c' τ t_c ≤ -κ_D := by
    unfold edgeRV
    rw [hx_tc, neg_le_neg_iff]
    let gD : ℝ → ℝ := fun y => (2 * Real.pi / 3) * (x_c - y - y * Real.log (x_c / y))
    have hgD_deriv : ∀ y > 0, HasDerivAt gD ((2 * Real.pi / 3) * Real.log (y / x_c)) y := by
      intro y hy
      have hlog : HasDerivAt (fun u : ℝ => Real.log (x_c / u)) (-1 / y) y := by
        have hdiv : HasDerivAt (fun u : ℝ => x_c / u) (-x_c / y ^ 2) y := by
          have h1 := (hasDerivAt_inv hy.ne').const_mul x_c
          have hfn : (fun u : ℝ => x_c * u⁻¹) = fun u => x_c / u := by ext u; ring
          rw [hfn] at h1
          exact h1.congr_deriv (by ring)
        refine (hdiv.log (div_pos hxc_pos hy).ne').congr_deriv ?_
        field_simp [hxc_pos.ne', hy.ne']
      have hinner : HasDerivAt (fun u : ℝ => x_c - u - u * Real.log (x_c / u))
          (0 - 1 - (1 * Real.log (x_c / y) + y * (-1 / y))) y :=
        ((hasDerivAt_const y x_c).sub (hasDerivAt_id y)).sub ((hasDerivAt_id y).mul hlog)
      refine (hinner.const_mul (2 * Real.pi / 3)).congr_deriv ?_
      rw [show x_c / y = (y / x_c)⁻¹ by rw [inv_div], Real.log_inv]
      field_simp [hy.ne']
      ring
    have hgD_mono : MonotoneOn gD (Ici x_c) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici x_c) ?_ ?_ ?_
      · intro y hy
        exact (hgD_deriv y (lt_of_lt_of_le hxc_pos (mem_Ici.mp hy))).continuousAt.continuousWithinAt
      · intro y hy
        have hy_gt : x_c < y := by simpa [interior_Ici] using hy
        exact (hgD_deriv y (lt_trans hxc_pos hy_gt)).differentiableAt.differentiableWithinAt
      · intro y hy
        rw [interior_Ici] at hy
        rw [(hgD_deriv y (lt_trans hxc_pos hy)).deriv]
        have h1 : 1 ≤ y / x_c := (one_le_div hxc_pos).mpr hy.le
        exact mul_nonneg (by positivity) (Real.log_nonneg h1)
    have h2x_mem : 2 * x_c ∈ Ici x_c := by change x_c ≤ 2 * x_c; linarith
    have hx0_mem : edgeX0 τ ∈ Ici x_c := by
      change x_c ≤ edgeX0 τ
      have hxi_pos := xiStar_pos
      have : x_c ≤ xiStar := by dsimp [x_c]; linarith
      exact this.trans (xiStar_le_edgeX0_all τ)
    have h2x_le : 2 * x_c ≤ edgeX0 τ := by
      have : 2 * x_c = xiStar := by dsimp [x_c]; ring
      rw [this]; exact xiStar_le_edgeX0_all τ
    have hD_val : gD (2 * x_c) = κ_D := by
      dsimp [gD, κ_D]
      rw [show x_c / (2 * x_c) = 2⁻¹ by field_simp [hxc_pos.ne'], Real.log_inv]
      ring
    calc κ_D = gD (2 * x_c) := hD_val.symm
      _ ≤ gD (edgeX0 τ) := hgD_mono h2x_mem hx0_mem h2x_le
      _ = crudeDivergenceD (edgeX0 τ) x_c := rfl
  have hv_k_lb : ((4 * Real.pi ^ 2) ^ k / ((k ! : ℝ) ^ 2)) *
      ((k : ℝ) * ((k : ℝ) - 1) * (c' / 12 - 2) ^ m) ≤ Bessel.besselVCoeff (c' / 12) k := by
    unfold Bessel.besselVCoeff
    have hb := Bessel.besselV_bracket_ge ha m
    have hb' : ((k : ℝ) * ((k : ℝ) - 1) * (c' / 12 - 2) ^ m) ≤
        (c' / 12) ^ k - 2 * (c' / 12 - 1) ^ k + (c' / 12 - 2) ^ k := by
      rw [hk_eq]
      convert hb using 2
      push_cast; ring
    exact mul_le_mul_of_nonneg_left hb' (by positivity)
  have hc_minus_2 : (c' / 12) * Real.exp (-48 / c') ≤ c' / 12 - 2 := by
    have hu : (24 / c' : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ hc'_pos (by norm_num)]; linarith
    have hu_pos : 0 < 24 / c' := by positivity
    have h1mu : 0 < 1 - 24 / c' := by linarith
    have hexp_inv : 1 / (1 - 24 / c') ≤ Real.exp (48 / c') := by
      have h1 : 1 / (1 - 24 / c') = 1 + (24 / c') / (1 - 24 / c') := by
        rw [div_eq_iff h1mu.ne', add_mul, one_mul, div_mul_cancel₀ _ h1mu.ne']
        ring
      have h2 : (24 / c') / (1 - 24 / c') ≤ 48 / c' := by
        rw [div_le_iff₀ h1mu]
        calc 24 / c' = (48 / c') * (1 / 2) := by ring
          _ ≤ (48 / c') * (1 - 24 / c') := by gcongr; linarith
      calc 1 / (1 - 24 / c') = 1 + (24 / c') / (1 - 24 / c') := h1
        _ ≤ 1 + 48 / c' := by linarith
        _ ≤ Real.exp (48 / c') := by linarith [Real.add_one_le_exp (48 / c')]
    have h_exp : Real.exp (-48 / c') ≤ 1 - 24 / c' := by
      rw [show (-48 / c' : ℝ) = -(48 / c') by ring, Real.exp_neg]
      exact (inv_le_comm₀ (Real.exp_pos _) h1mu).mpr (by simpa [one_div] using hexp_inv)
    have h_mul := mul_le_mul_of_nonneg_left h_exp (by positivity : (0 : ℝ) ≤ c' / 12)
    have h_eq : (c' / 12) * (1 - 24 / c') = c' / 12 - 2 := by
      field_simp [hc'_pos.ne']; ring
    rwa [h_eq] at h_mul
  have hm_exp : Real.exp (-16 * Real.pi * x_c) * (c' / 12) ^ m ≤ (c' / 12 - 2) ^ m := by
    have h1 : ((c' / 12) * Real.exp (-48 / c')) ^ m ≤ (c' / 12 - 2) ^ m :=
      pow_le_pow_left₀ (by positivity) hc_minus_2 m
    have h2 : Real.exp (-48 / c') ^ m = Real.exp (-(48 / c' * (m : ℝ))) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    have h3 : -16 * Real.pi * x_c ≤ -(48 / c' * (m : ℝ)) := by
      have hm_le_r : (m : ℝ) ≤ r := by
        have : (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : m ≤ k)
        linarith
      have h48 : 48 / c' * (m : ℝ) ≤ 48 / c' * r :=
        mul_le_mul_of_nonneg_left hm_le_r (by positivity)
      have hr_val : 48 / c' * r = 16 * Real.pi * x_c := by
        dsimp [r]; field_simp [hc'_pos.ne']; ring
      linarith
    calc Real.exp (-16 * Real.pi * x_c) * (c' / 12) ^ m
        ≤ Real.exp (-(48 / c' * (m : ℝ))) * (c' / 12) ^ m := by gcongr
      _ = ((c' / 12) * Real.exp (-48 / c')) ^ m := by rw [mul_pow, h2, mul_comm]
      _ ≤ (c' / 12 - 2) ^ m := h1
  have hk_fac_ub : (k ! : ℝ) ≤ Real.exp 1 * √(k : ℝ) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
    have hst_k : (k ! : ℝ) =
        Stirling.stirlingSeq k * (√(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
      have hden : √(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k ≠ 0 := by positivity
      rw [Stirling.stirlingSeq, div_mul_cancel₀ _ hden]
    have hst_le : Stirling.stirlingSeq k ≤ Stirling.stirlingSeq 1 := by
      have hk_succ : k = (k - 1) + 1 := by omega
      rw [hk_succ]
      exact Stirling.stirlingSeq'_antitone (Nat.zero_le (k - 1))
    have hst_1 : Stirling.stirlingSeq 1 = Real.exp 1 / √2 := by
      rw [Stirling.stirlingSeq]
      simp [Nat.factorial_one, div_eq_mul_inv]
    have hsqrt2 : √(2 * (k : ℝ)) = √2 * √(k : ℝ) := Real.sqrt_mul zero_le_two _
    have hexp_k : (Real.exp 1) ^ k = Real.exp (k : ℝ) := by
      rw [← Real.exp_nat_mul, mul_one]
    rw [hst_k]
    calc Stirling.stirlingSeq k * (√(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k)
        ≤ (Real.exp 1 / √2) * (√(2 * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k) := by
          gcongr; exact hst_1 ▸ hst_le
      _ = Real.exp 1 * √(k : ℝ) * (k : ℝ) ^ k * Real.exp (-(k : ℝ)) := by
          rw [hsqrt2, div_pow, hexp_k, Real.exp_neg]
          have hsq2 : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
          field_simp [hsq2]
  have hk_fac_sq_ub : (k ! : ℝ) ^ 2 ≤
      (Real.exp 1) ^ 2 * (k : ℝ) * r ^ (2 * k) * Real.exp (-2 * (k : ℝ)) := by
    have h1 : (k ! : ℝ) ^ 2 ≤ (Real.exp 1 * √(k : ℝ) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hk_fac_ub 2
    have h2 : (Real.exp 1 * √(k : ℝ) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) ^ 2 =
        (Real.exp 1) ^ 2 * (k : ℝ) * ((k : ℝ) ^ k) ^ 2 * Real.exp (-2 * (k : ℝ)) := by
      have hsqrt_sq : √(k : ℝ) ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
      have hexp_sq : Real.exp (-(k : ℝ)) ^ 2 = Real.exp (-2 * (k : ℝ)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      calc (Real.exp 1 * √(k : ℝ) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) ^ 2
          = (Real.exp 1) ^ 2 * √(k : ℝ) ^ 2 * ((k : ℝ) ^ k) ^ 2 * Real.exp (-(k : ℝ)) ^ 2 := by ring
        _ = (Real.exp 1) ^ 2 * (k : ℝ) * ((k : ℝ) ^ k) ^ 2 * Real.exp (-2 * (k : ℝ)) := by
          rw [hsqrt_sq, hexp_sq]
    have h3 : ((k : ℝ) ^ k) ^ 2 ≤ r ^ (2 * k) := by
      rw [← pow_mul, mul_comm k 2]
      exact pow_le_pow_left₀ (Nat.cast_nonneg k) hk_le_r (2 * k)
    calc (k ! : ℝ) ^ 2 ≤ (Real.exp 1 * √(k : ℝ) * (k : ℝ) ^ k * Real.exp (-(k : ℝ))) ^ 2 := h1
      _ = (Real.exp 1) ^ 2 * (k : ℝ) * ((k : ℝ) ^ k) ^ 2 * Real.exp (-2 * (k : ℝ)) := h2
      _ ≤ (Real.exp 1) ^ 2 * (k : ℝ) * r ^ (2 * k) * Real.exp (-2 * (k : ℝ)) := by gcongr
  have hr2k_eq : (c' / 12) ^ k * ((4 * Real.pi ^ 2) ^ k * t_c ^ k) = r ^ (2 * k) := by
    rw [← mul_pow, ← mul_pow, pow_mul]
    congr 1
    have hbase : (c' / 12) * (4 * Real.pi ^ 2 * t_c) = r ^ 2 := by
      dsimp [t_c, r]
      ring
    exact hbase
  have hk_nn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hk1_nn : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hvk_lb : (k : ℝ) * ((k : ℝ) - 1) * Real.exp (-16 * Real.pi * x_c) /
      ((c' / 12) ^ 2 * (Real.exp 1) ^ 2 * (k : ℝ) * Real.exp (-2 * (k : ℝ))) ≤
      Bessel.besselVCoeff (c' / 12) k * t_c ^ k := by
    have hm_rel : (c' / 12) ^ m = (c' / 12) ^ k / (c' / 12) ^ 2 := by
      rw [hk_eq, pow_add]; field_simp [hc'_pos.ne']
    have hr2k_pos : 0 < r ^ (2 * k) := by positivity
    calc (k : ℝ) * ((k : ℝ) - 1) * Real.exp (-16 * Real.pi * x_c) /
          ((c' / 12) ^ 2 * (Real.exp 1) ^ 2 * (k : ℝ) * Real.exp (-2 * (k : ℝ)))
        = (r ^ (2 * k) / ((Real.exp 1) ^ 2 * (k : ℝ) * r ^ (2 * k) * Real.exp (-2 * (k : ℝ)))) *
            ((k : ℝ) * ((k : ℝ) - 1) * (Real.exp (-16 * Real.pi * x_c) *
              ((c' / 12) ^ k / (c' / 12) ^ 2))) *
            (1 / (c' / 12) ^ k) := by
          field_simp [hc'_pos.ne', hr2k_pos.ne']
      _ = (((4 * Real.pi ^ 2) ^ k * t_c ^ k) /
              ((Real.exp 1) ^ 2 * (k : ℝ) * r ^ (2 * k) * Real.exp (-2 * (k : ℝ)))) *
            ((k : ℝ) * ((k : ℝ) - 1) * (Real.exp (-16 * Real.pi * x_c) * (c' / 12) ^ m)) := by
          rw [← hm_rel, ← hr2k_eq]
          field_simp [hc'_pos.ne']
      _ ≤ (((4 * Real.pi ^ 2) ^ k * t_c ^ k) / ((k ! : ℝ) ^ 2)) *
            ((k : ℝ) * ((k : ℝ) - 1) * (c' / 12 - 2) ^ m) := by
          gcongr
      _ = ((4 * Real.pi ^ 2) ^ k / ((k ! : ℝ) ^ 2)) *
            ((k : ℝ) * ((k : ℝ) - 1) * (c' / 12 - 2) ^ m) * t_c ^ k := by ring
      _ ≤ Bessel.besselVCoeff (c' / 12) k * t_c ^ k := by gcongr
  have hratio_ub : Real.exp (c' * Bessel.besselL x_c) /
      (Bessel.besselVCoeff (c' / 12) k * t_c ^ k) ≤
      (2 / 144) * Real.exp (16 * Real.pi * x_c) * Real.exp 4 * (Real.exp 1) ^ 2 /
        (2 * Real.pi * x_c / 3 - 6 / 10000) * c' := by
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hk1_pos : (0 : ℝ) < (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge_2
      linarith
    have hk1_lb : (2 * Real.pi * x_c / 3 - 6 / 10000) * c' / 2 ≤ (k : ℝ) - 1 := by
      have hr_eq : r = (2 * Real.pi * x_c / 3) * c' / 2 := by dsimp [r]; ring
      have hc3 : (3 : ℝ) ≤ (6 / 10000) * c' / 2 := by linarith
      linarith
    have h2r_eq : c' * Bessel.besselL x_c = 2 * r := by
      unfold Bessel.besselL; dsimp [r]; ring
    have hexp_diff : Real.exp (2 * r) * Real.exp (-2 * (k : ℝ)) ≤ Real.exp 4 := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (c' * Bessel.besselL x_c) / (Bessel.besselVCoeff (c' / 12) k * t_c ^ k)
        = Real.exp (2 * r) * (Bessel.besselVCoeff (c' / 12) k * t_c ^ k)⁻¹ := by
          rw [h2r_eq, div_eq_mul_inv]
      _ ≤ Real.exp (2 * r) * ((k : ℝ) * ((k : ℝ) - 1) * Real.exp (-16 * Real.pi * x_c) /
            ((c' / 12) ^ 2 * (Real.exp 1) ^ 2 * (k : ℝ) * Real.exp (-2 * (k : ℝ))))⁻¹ := by
          gcongr
      _ = ((c' / 12) ^ 2 * (Real.exp 1) ^ 2 / (Real.exp (-16 * Real.pi * x_c) * ((k : ℝ) - 1))) *
            (Real.exp (2 * r) * Real.exp (-2 * (k : ℝ))) := by
          field_simp [hk_pos.ne', hk1_pos.ne']
      _ ≤ (c' ^ 2 / 144 * (Real.exp 1) ^ 2 /
            (Real.exp (-16 * Real.pi * x_c) * ((2 * Real.pi * x_c / 3 - 6 / 10000) * c' / 2))) *
            Real.exp 4 := by
          gcongr
          linarith [show (c' / 12) ^ 2 = c' ^ 2 / 144 by ring]
      _ = (2 / 144) * Real.exp (16 * Real.pi * x_c) * Real.exp 4 * (Real.exp 1) ^ 2 /
            (2 * Real.pi * x_c / 3 - 6 / 10000) * c' := by
          rw [show (-16 * Real.pi * x_c : ℝ) = -(16 * Real.pi * x_c) by ring, Real.exp_neg]
          field_simp [hc'_pos.ne', hden_pos.ne']
  have hsqrt_tc_lb : √(x_c ^ 2 / 3) ≤ √t_c := by
    have h1 : x_c ^ 2 / 3 ≤ t_c := by
      dsimp [t_c]
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_left (sq_nonneg _) (by linarith)) (by norm_num)
    exact Real.sqrt_le_sqrt h1
  have hc_exp_half : c' * Real.exp (-κ_sub * c') ≤ 2 / κ_D := by
    have hadd : κ_sub * c' ≤ Real.exp (κ_sub * c') := by
      linarith [Real.add_one_le_exp (κ_sub * c')]
    have hexp_pos : 0 < Real.exp (κ_sub * c') := Real.exp_pos _
    rw [show -κ_sub * c' = -(κ_sub * c') by ring, Real.exp_neg]
    calc c' * (Real.exp (κ_sub * c'))⁻¹ ≤ c' * (κ_sub * c')⁻¹ := by gcongr
      _ = 2 / κ_D := by dsimp [κ_sub]; field_simp [hc'_pos.ne', hκD_pos.ne']
  have hA1_bd : ‖edgeA1 c' τ‖ ≤ 2 := edgeA1_norm_le hc'_mu τ
  calc ‖edgeKernelK c' τ t‖
      ≤ (‖edgeKernelK c' τ t_c‖ * virasoroProblem.cardyV (c' / 12) t_c) /
          (Bessel.besselVCoeff (c' / 12) k * t_c ^ k) := hK_le_tc
    _ = ‖edgeA1 c' τ‖ * (1 / √t_c) *
          (Real.exp (c' * Bessel.besselL x_c) / (Bessel.besselVCoeff (c' / 12) k * t_c ^ k)) *
          Real.exp (c' * edgeRV c' τ t_c) := by rw [hnum_eq]; ring
    _ ≤ 2 * (1 / √(x_c ^ 2 / 3)) *
          ((2 / 144) * Real.exp (16 * Real.pi * x_c) * Real.exp 4 * (Real.exp 1) ^ 2 /
            (2 * Real.pi * x_c / 3 - 6 / 10000) * c') *
          Real.exp (c' * (-κ_D)) := by
        gcongr
    _ = K_rem * (c' * Real.exp (-κ_sub * c')) * Real.exp (-κ_sub * c') := by
        have hexp_split : Real.exp (c' * (-κ_D)) =
            Real.exp (-κ_sub * c') * Real.exp (-κ_sub * c') := by
          rw [← Real.exp_add]; congr 1; dsimp [κ_sub]; ring
        rw [hexp_split]
        dsimp [K_rem]
        ring
    _ ≤ K_rem * (2 / κ_D) * Real.exp (-κ_sub * c') := by
        gcongr
    _ = C_sub * Real.exp (-κ_sub * c') := rfl

lemma wFactor_bound_and_deriv {w : ℝ} (hw : 1 ≤ w) :
    ∃ C_w : ℝ, 0 < C_w ∧ ∀ {c' : ℝ}, 48 / muStar ≤ c' → ∀ τ : ℝ,
      ‖wFactor w (chartOmega (Complex.I * (τ : ℂ)))‖ ≤ C_w ∧
      (∃ dw : ℂ, HasDerivAt (fun s : ℝ => wFactor w (chartOmega (Complex.I * (s : ℂ)))) dw τ ∧
        ‖dw‖ ≤ C_w / (1 + |τ|)) ∧
      ‖edgeA1 c' τ * wFactor w (chartOmega (Complex.I * (τ : ℂ)))‖ ≤ 2 * C_w ∧
      (∃ d_prod : ℂ, HasDerivAt
          (fun s : ℝ => edgeA1 c' s * wFactor w (chartOmega (Complex.I * (s : ℂ))))
          d_prod τ ∧ ‖d_prod‖ ≤ C_w / (1 + |τ|)) := by
  obtain ⟨c_ω, hc_ω_pos, hω_ge⟩ := norm_chartOmega_left_edge_ge
  obtain ⟨cnu₁, cnu₂, hcnu₁_pos, hcnu₂_pos, hnu_as⟩ := lemma_J4_0.2.2.2.2.1
  obtain ⟨C_A1', hC_A1'_pos, hA1_deriv⟩ := edgeA1_deriv_bounds
  let r : ℝ := (w - 1) / 2
  have hr_nn : 0 ≤ r := by dsimp [r]; linarith
  let B0 : ℝ := ((2 * Real.pi / 3) / muStar) ^ r
  have hB0_pos : 0 < B0 := by have := Real.pi_pos; have := muStar_pos; positivity
  let C_ω' : ℝ := Real.pi / 6 + cnu₂
  have hC_ω'_pos : 0 < C_ω' := by have := Real.pi_pos; positivity
  let C_w : ℝ := max B0 (max (r * B0 * (C_ω' / c_ω)) (2 * C_A1' * B0 + 2 * (r * B0 * (C_ω' / c_ω))))
  refine ⟨C_w, lt_of_lt_of_le hB0_pos (le_max_left _ _), fun {c'} hc' τ => ?_⟩
  have hc'_pos : 0 < c' := lt_of_lt_of_le (div_pos (by norm_num) muStar_pos) hc'
  have hc'_ge1 : 1 ≤ c' := by
    have hmu_le : muStar ≤ Real.pi * 1 / 3 := by
      unfold muStar
      gcongr
      have hs_xi : Real.sinh (Real.pi * xiStar) = 1 := by
        have h := sinh_pi_edgeX0 0
        rw [edgeX0_zero, mul_zero, Real.cosh_zero, Real.sqrt_one] at h; exact h
      have hs_pi : 1 < Real.sinh Real.pi := by
        have h1 : 4 < Real.exp Real.pi := by
          linarith [Real.add_one_le_exp Real.pi, Real.pi_gt_three]
        have h2 : Real.exp (-Real.pi) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
        rw [Real.sinh_eq]
        linarith
      by_contra hlt; push Not at hlt
      have h1 : Real.pi ≤ Real.pi * xiStar := le_mul_of_one_le_right Real.pi_pos.le hlt.le
      linarith [Real.sinh_strictMono.monotone h1]
    have hmu_le2 : muStar ≤ 48 := by linarith [Real.pi_lt_four]
    calc (1 : ℝ) = 48 / 48 := by norm_num
      _ ≤ 48 / muStar := div_le_div_of_nonneg_left (by norm_num) muStar_pos hmu_le2
      _ ≤ c' := hc'
  let ω : ℂ := chartOmega (Complex.I * (τ : ℂ))
  have hω_re : 0 < ω.re := by
    dsimp [ω]; rw [chartOmega_left_edge]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
    exact lt_of_lt_of_le muStar_pos (edgeMu_ge_muStar τ)
  have hω_ne : ω ≠ 0 := by intro h; rw [h, Complex.zero_re] at hω_re; exact lt_irrefl 0 hω_re
  have hmu_norm : muStar ≤ ‖ω‖ := by
    calc muStar ≤ edgeMu τ := edgeMu_ge_muStar τ
      _ = ω.re := by
          dsimp [ω]; rw [chartOmega_left_edge]
          simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            zero_mul, Complex.ofReal_im, mul_zero, sub_zero, sub_self]
      _ ≤ ‖ω‖ := Complex.re_le_norm ω
  have h2pi3_ne : (2 * (Real.pi : ℂ) / 3) ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')) (by norm_num)
  have harg_ne : 2 * (Real.pi : ℂ) / (3 * ω) ≠ 0 := by
    rw [show 2 * (Real.pi : ℂ) / (3 * ω) = (2 * (Real.pi : ℂ) / 3) * ω⁻¹ by ring]
    exact mul_ne_zero h2pi3_ne (inv_ne_zero hω_ne)
  have hwF_norm : ‖wFactor w ω‖ ≤ B0 := by
    unfold wFactor
    have hnorm_cp : ‖(2 * (Real.pi : ℂ) / (3 * ω)) ^ (((w - 1) / 2 : ℝ) : ℂ)‖ =
        ‖2 * (Real.pi : ℂ) / (3 * ω)‖ ^ r := by
      rw [Complex.norm_cpow_of_ne_zero harg_ne]
      simp [r, Complex.ofReal_im]
    rw [hnorm_cp]
    have hnorm_arg : ‖2 * (Real.pi : ℂ) / (3 * ω)‖ ≤ (2 * Real.pi / 3) / muStar := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le]
      rw [show 2 * Real.pi / (3 * ‖ω‖) = (2 * Real.pi / 3) / ‖ω‖ by ring]
      exact div_le_div_of_nonneg_left (by positivity) muStar_pos hmu_norm
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm_arg hr_nn
  have hwF_re : 0 < (2 * (Real.pi : ℂ) / (3 * ω)).re := by
    have h_inv_re : 0 < (ω⁻¹).re := by
      rw [Complex.inv_re]
      exact div_pos hω_re (Complex.normSq_pos.mpr hω_ne)
    rw [show 2 * (Real.pi : ℂ) / (3 * ω) = ((2 * Real.pi / 3 : ℝ) : ℂ) * ω⁻¹ by push_cast; ring]
    rw [Complex.re_ofReal_mul]
    exact mul_pos (by positivity) h_inv_re
  have hslit : 2 * (Real.pi : ℂ) / (3 * ω) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl hwF_re)
  let ω' : ℂ := (edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)
  have hd_arg : HasDerivAt (fun s : ℝ => 2 * (Real.pi : ℂ) / (3 * chartOmega (Complex.I * (s : ℂ))))
      (-(2 * (Real.pi : ℂ) / 3) * ω' / ω ^ 2) τ := by
    have hd1 := (hasDerivAt_chartOmega_left_edge τ).inv hω_ne
    have heq : (fun s : ℝ => 2 * (Real.pi : ℂ) / (3 * chartOmega (Complex.I * (s : ℂ)))) =
        fun s : ℝ => (2 * (Real.pi : ℂ) / 3) * (chartOmega (Complex.I * (s : ℂ)))⁻¹ := by
      ext s; ring
    rw [heq]
    refine (hd1.const_mul (2 * (Real.pi : ℂ) / 3)).congr_deriv ?_
    dsimp [ω, ω']; ring
  have hd_wF : HasDerivAt (fun s : ℝ => wFactor w (chartOmega (Complex.I * (s : ℂ))))
      (-(r : ℂ) * wFactor w ω * (ω' / ω)) τ := by
    have hd_outer : HasDerivAt (fun z : ℂ => 2 * (Real.pi : ℂ) / (3 * z))
        (-(2 * (Real.pi : ℂ) / 3) / ω ^ 2) ω := by
      have h3 : HasDerivAt (fun z : ℂ => (3 : ℂ) * z) 3 ω := by
        simpa using (hasDerivAt_id ω).const_mul (3 : ℂ)
      have hd := (hasDerivAt_const ω (2 * (Real.pi : ℂ))).div h3 (mul_ne_zero (by norm_num) hω_ne)
      refine hd.congr_deriv ?_
      field_simp [hω_ne]; ring
    have hcp := (hd_outer.cpow_const (c := (r : ℂ)) hslit).scomp τ (hasDerivAt_chartOmega_left_edge τ)
    refine hcp.congr_deriv ?_
    unfold wFactor
    have hr1 : ω' * ((r : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) *
        (-(2 * (Real.pi : ℂ) / 3) / ω ^ 2)) =
        -(r : ℂ) * (2 * (Real.pi : ℂ) / (3 * ω)) ^ (r : ℂ) * (ω' / ω) := by
      have hrw : (2 * (Real.pi : ℂ) / (3 * ω)) ^ (r : ℂ) =
          (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) * (2 * (Real.pi : ℂ) / (3 * ω)) := by
        calc (2 * (Real.pi : ℂ) / (3 * ω)) ^ (r : ℂ)
            = (2 * (Real.pi : ℂ) / (3 * ω)) ^ (((r : ℂ) - 1) + 1) := by ring_nf
          _ = (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) *
                (2 * (Real.pi : ℂ) / (3 * ω)) ^ (1 : ℂ) :=
              Complex.cpow_add _ 1 harg_ne
          _ = (2 * (Real.pi : ℂ) / (3 * ω)) ^ ((r : ℂ) - 1) * (2 * (Real.pi : ℂ) / (3 * ω)) := by
              rw [Complex.cpow_one]
      rw [hrw]
      field_simp [harg_ne, hω_ne, h2pi3_ne]
    simpa [r, ω, smul_eq_mul] using hr1
  have hω'_bd : ‖ω'‖ ≤ C_ω' * (1 + |τ|) := by
    dsimp [ω']
    have hmu_d : |edgeMuDeriv τ| ≤ Real.pi / 6 := abs_edgeMuDeriv_le τ
    have hnu_d : |edgeNuDeriv τ| ≤ cnu₂ * (1 + |τ|) := by
      have hnd : edgeNuDeriv τ = edgeNuDeriv |τ| := by
        rcases le_total 0 τ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, edgeNuDeriv_even]
      rw [hnd]
      have h1 := (hnu_as |τ| (abs_nonneg τ)).2
      have h2 := (hnu_as |τ| (abs_nonneg τ)).1
      have hpos : 0 ≤ edgeNuDeriv |τ| := by
        have : 0 < cnu₁ * (1 + |τ|) := by positivity
        linarith
      rwa [abs_of_nonneg hpos]
    calc ‖(edgeMuDeriv τ : ℂ) - Complex.I * (edgeNuDeriv τ : ℂ)‖
        ≤ |edgeMuDeriv τ| + |edgeNuDeriv τ| := by
          refine (norm_sub_le _ _).trans_eq ?_
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ C_ω' * (1 + |τ|) := by
          dsimp [C_ω']; nlinarith [abs_nonneg τ, Real.pi_pos]
  have hdw_norm : ‖-(r : ℂ) * wFactor w ω * (ω' / ω)‖ ≤
      (r * B0 * (C_ω' / c_ω)) / (1 + |τ|) := by
    have h1t : 0 < 1 + |τ| := by linarith [abs_nonneg τ]
    have hω_lb := hω_ge τ
    calc ‖-(r : ℂ) * wFactor w ω * (ω' / ω)‖
        = r * ‖wFactor w ω‖ * (‖ω'‖ / ‖ω‖) := by
          rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr_nn, norm_div]
      _ ≤ r * B0 * (C_ω' * (1 + |τ|) / (c_ω * (1 + |τ|) ^ 2)) := by
          gcongr
      _ = (r * B0 * (C_ω' / c_ω)) / (1 + |τ|) := by
          field_simp [hc_ω_pos.ne', h1t.ne']
  obtain ⟨d1, hd1, hd1_norm⟩ := hA1_deriv hc' τ
  have hd_prod := hd1.mul hd_wF
  have hd_prod_norm : ‖d1 * wFactor w ω + edgeA1 c' τ * (-(r : ℂ) * wFactor w ω * (ω' / ω))‖ ≤
      C_w / (1 + |τ|) := by
    have h1t : 1 ≤ 1 + |τ| := by linarith [abs_nonneg τ]
    have hc_pow : 1 + |τ| ≤ c' * (1 + |τ|) ^ 3 := by
      have h1 : 1 + |τ| ≤ (1 + |τ|) ^ 3 := by nlinarith [sq_nonneg (1 + |τ|)]
      calc 1 + |τ| ≤ (1 + |τ|) ^ 3 := h1
        _ ≤ c' * (1 + |τ|) ^ 3 := le_mul_of_one_le_left (by positivity) hc'_ge1
    have hA1_bd : ‖edgeA1 c' τ‖ ≤ 2 := edgeA1_norm_le hc' τ
    have hCw_prod : 2 * C_A1' * B0 + 2 * (r * B0 * (C_ω' / c_ω)) ≤ C_w :=
      (le_max_right _ _).trans (le_max_right _ _)
    calc ‖d1 * wFactor w ω + edgeA1 c' τ * (-(r : ℂ) * wFactor w ω * (ω' / ω))‖
        ≤ ‖d1‖ * ‖wFactor w ω‖ + ‖edgeA1 c' τ‖ * ‖-(r : ℂ) * wFactor w ω * (ω' / ω)‖ := by
          refine (norm_add_le _ _).trans_eq ?_; rw [norm_mul, norm_mul]
      _ ≤ (C_A1' / (c' * (1 + |τ|) ^ 3)) * B0 + 2 * ((r * B0 * (C_ω' / c_ω)) / (1 + |τ|)) := by
          gcongr
      _ ≤ (C_A1' / (1 + |τ|)) * B0 + 2 * ((r * B0 * (C_ω' / c_ω)) / (1 + |τ|)) := by
          gcongr
      _ = (C_A1' * B0 + 2 * (r * B0 * (C_ω' / c_ω))) / (1 + |τ|) := by ring
      _ ≤ (2 * C_A1' * B0 + 2 * (r * B0 * (C_ω' / c_ω))) / (1 + |τ|) := by
          gcongr; linarith
      _ ≤ C_w / (1 + |τ|) := by gcongr
  refine ⟨hwF_norm.trans (le_max_left _ _), ⟨_, hd_wF, hdw_norm.trans ?_⟩, ?_, ⟨_, hd_prod, hd_prod_norm⟩⟩
  · gcongr; exact (le_max_left _ _).trans (le_max_right _ _)
  · calc ‖edgeA1 c' τ * wFactor w ω‖ = ‖edgeA1 c' τ‖ * ‖wFactor w ω‖ := norm_mul _ _
      _ ≤ 2 * B0 := by gcongr; exact edgeA1_norm_le hc' τ
      _ ≤ 2 * C_w := by gcongr; exact le_max_left _ _

/-- **Lemma J4.2 (kernel factorization)** (`lower_o1_two_edge.tex`, §J4, `vlo:J42`, lines 499–514):
collects the exact factorization `K(τ, t) = A₁(τ) A₂(t) exp(c'(R_V - i Φ)) = A₁(τ) A₂(t) exp(c'(R_V + i Θ))`,
exponent `R_V ≤ 0` (even and unimodal), phase `Φ` (odd, `∂_τ Φ = 2 ν'(τ) log(x / x₀(τ))`),
uniform amplitude and derivative bounds on `A₁, A₂`, and the uniform sub-Cardy bound `|K| ≤ C e^{-κ c'}`
on `0 < x ≤ ξ_* / 2` (plus the general-weight `w ≥ 1` `ω`-factor bound). -/
theorem lemma_J4_2 :
    ∃ C_A1 C_A1' C_A2 C_sub κ_sub c₀ : ℝ,
      0 < C_A1 ∧ 0 < C_A1' ∧ 0 < C_A2 ∧ 0 < C_sub ∧ 0 < κ_sub ∧ 10000 ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' →
        (∀ τ : ℝ, ‖edgeA1 c' τ‖ ≤ C_A1 ∧
          ∃ d : ℂ, HasDerivAt (edgeA1 c') d τ ∧ ‖d‖ ≤ C_A1' / (c' * (1 + |τ|) ^ 3)) ∧
        (∀ {t : ℝ}, 0 < t → xiStar / 2 ≤ √(3 * t / c') →
          0 ≤ edgeA2 c' t ∧ edgeA2 c' t ≤ C_A2) ∧
        (∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
          ∀ τ : ℝ, ‖edgeKernelK c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c')) ∧
        (∀ {t : ℝ}, 0 < t → ∀ τ : ℝ,
          edgeKernelK c' τ t = edgeA1 c' τ * (edgeA2 c' t : ℂ) *
            Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) + Complex.I * (edgeTheta c' τ t : ℂ))) ∧
          edgeRV c' τ t ≤ 0 ∧ edgeRV c' (-τ) t = edgeRV c' τ t ∧
          edgeTheta c' (-τ) t = -edgeTheta c' τ t ∧
          HasDerivAt (fun s => edgeTheta c' s t)
            (2 * edgeNuDeriv τ * Real.log (edgeX0 τ / √(3 * t / c'))) τ) ∧
        (∀ {t : ℝ}, 0 < t →
          MonotoneOn (fun τ => edgeRV c' τ t) (Ioi 0 ∩ Iic (edgeTau0 c' t)) ∧
          AntitoneOn (fun τ => edgeRV c' τ t) (Ioi 0 ∩ Ici (edgeTau0 c' t))) := by
  obtain ⟨C_A1', hC_A1', hA1⟩ := edgeA1_deriv_bounds
  obtain ⟨C_sub, κ_sub, c₀, hC_sub, hκ_sub, hc₀, hsub⟩ := edgeKernelK_subCardy_bound
  refine ⟨2, C_A1', 6 * Real.pi * √10, C_sub, κ_sub, c₀,
    by norm_num, hC_A1', by positivity, hC_sub, hκ_sub, hc₀, fun {c'} hc' => ?_⟩
  have hc₀_ge : 10000 ≤ c' := hc₀.trans hc'
  have hc'_24 : 24 ≤ c' := by linarith
  have hc'_pos : 0 < c' := by linarith
  have hmu_le : 48 / muStar ≤ c' := by
    -- Show `48 / muStar ≤ 10000`: since `3/4 ≤ π * xiStar`, `1/4 ≤ muStar`, so `48 / muStar ≤ 192`
    have hmu_lb : 1 / 4 ≤ muStar := by
      unfold muStar; linarith [Bessel.three_quarters_le_pi_mul_xiStar]
    have h48 : 48 / muStar ≤ 192 := by
      rw [div_le_iff₀ muStar_pos]; linarith
    linarith
  refine ⟨fun τ => ⟨edgeA1_norm_le hmu_le τ, hA1 hmu_le τ⟩,
    fun {t} ht hx => edgeA2_norm_le hc₀_ge ht hx,
    fun {t} ht hx τ => hsub hc' ht hx τ,
    fun {t} ht τ => ⟨edgeKernelK_factorization_theta hc'_24 τ ht, edgeRV_nonpos ht hc'_pos,
      edgeRV_even c' τ t, by unfold edgeTheta; rw [edgePhi_odd hc'_pos ht, neg_neg],
      hasDerivAt_edgeTheta hc'_pos ht τ⟩,
    fun {t} ht => edgeRV_unimodal hc'_pos ht⟩

/-! ### Axiom Verification -/

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.lemma_J4_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_1

/-- info: 'FormalResearch.ModularBootstrap.StripMultiplier.lemma_J4_2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_2

end FormalResearch.ModularBootstrap.StripMultiplier

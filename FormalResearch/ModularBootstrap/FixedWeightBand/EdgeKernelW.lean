module

public import FormalResearch.ModularBootstrap.FixedWeightBand.EdgeKernelWFactor

/-!
# Edge Representation, Poisson Identity, and Kernel Factorization at Weight `w`
# (Lemmas J4.1 and J4.2, `vlo:J41`, `vlo:J42`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, §J4, Lemma J4.1 (`vlo:J41`) and
Lemma J4.2 (`vlo:J42`); Lemma J4.0 (`vlo:J40`, edge functions) is weight free and is the existing
`Chart.lemma_J4_0`.

For `prob : FixedWeightProblem` (weight `w = prob.w ≥ 1`, any null-state product `Q`),
`V = prob.cardyV (c'/12)`, `z = w/2 + c' ω(iτ)`, `t = c' x²/3` (definitions in `EdgeKernelWFactor`):

* `lemma_J4_1_W`: for `c' ≥ c₀` and `g ∈ TestClass prob (c'/12)`,
  `W̃_V(iτ) = ∫₀^∞ K(τ, t) g(t) V(t) dt` (`W̃_V = tildeWW w c' g`), `H_V(iτ) = 𝒜_V(τ) W̃_V(iτ)`,
  the strip Poisson identity `H_V(ζ₀) = ∫ Q(τ) H_V(iτ) dτ` for `0 < Re ζ₀ < 1`, `‖Q‖₁ ≤ 1` and
  `sup |Q| + TV(Q) ≤ 2/Re ζ₀` on `Re ζ₀ ≤ 0.04`.  The Poisson part needs only that `W̃_V` is bounded,
  continuous, holomorphic and antisymmetric on the strip (`lemma_S4_W`), so it is proved for any
  such multiplier (`edgeHV_poisson_of_multiplier`).
* `lemma_J4_2_W`: kernel factorization `K = A₁ A₂ exp(c'(R_V + iΘ))`, `R_V ≤ 0` even and unimodal,
  `Θ` odd with `∂_τ Θ = 2ν'(τ) log(x₀(τ)/x)`, the amplitude bounds `|A₁| ≤ C`,
  `|A₁'| ≤ C/(1+|τ|)`, `0 ≤ A₂ ≤ C` on `x ≥ ξ*/2`, and the sub-Cardy kernel bound
  `|K| ≤ C e^{-κ c'}` on `0 < x ≤ ξ*/2`, uniformly in `τ`.  The sharper form of the `A₁` derivative
  bound (`C/(c'(1+|τ|)³)` for the `S^{(w)}` part; the `ω`-factor contributes `((w-1)/2) C_F/(1+|τ|)`
  and vanishes at `w = 1`) is `edgeA1W_bounds`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.FixedWeightBand

open Crossing WeightAxioms ComplexBessel Chart ChartGeometry StripBand
open FormalResearch.StripPoisson
open FormalResearch.ModularBootstrap.StripMultiplier
  (edgeRV edgePhi edgeTheta edgeTau0 edgeX0_pos_all edgeRV_nonpos edgeRV_even edgePhi_odd
    hasDerivAt_edgeTheta edgeRV_unimodal stripPoissonQ_norm_L1_le)

/-! ### Section 1: Measurability of the kernel -/

/-- Damped strip function `H_V(ζ) = c'^{5/6} (ζ(1 - ζ))^{5/2} e^{-ζ(1 - ζ)} W̃_V(ζ)`
(`lower_o1_two_edge.tex`, Lemma J4.1, `vlo:J41`) at weight `w`. -/
noncomputable def edgeHVW (w : ℕ) (c' : ℝ) (g : ℝ → ℝ) (ζ : ℂ) : ℂ :=
  tebPrefactor c' ζ * tildeWW w c' g ζ

lemma measurable_edgeKernelKW (prob : FixedWeightProblem) {c' : ℝ} (hc' : 0 ≤ c') :
    Measurable (Function.uncurry (edgeKernelKW prob c')) := by
  have hω_cont : Continuous (fun τ : ℝ => chartOmega (Complex.I * (τ : ℂ))) :=
    continuousOn_chartOmega.comp_continuous (by fun_prop) fun τ => by simp
  have hΥ_cont : Continuous (fun τ : ℝ => chartUpsilon (Complex.I * (τ : ℂ))) :=
    lemma_S3_strip.2.2.2.1.comp_continuous (by fun_prop) fun τ => by simp [stripClosed]
  have hz_cont : Continuous (fun τ : ℝ =>
      (prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))) :=
    continuous_const.add (continuous_const.mul hω_cont)
  have hgam_cont : Continuous (fun τ : ℝ =>
      Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)))) := by
    rw [continuous_iff_continuousAt]
    intro τ
    have hre : 0 < ((prob.w : ℂ) / 2 +
        (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))).re := by
      have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re,
        Complex.re_ofReal_mul]
      have hmu := re_chartOmega_edge_pos τ
      nlinarith [mul_nonneg hc' hmu.le]
    have hdiff : DifferentiableAt ℂ Complex.Gamma
        ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ))) :=
      Complex.differentiableAt_Gamma _ fun m hm => by
        have := congrArg Complex.re hm
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [Nat.cast_nonneg (α := ℝ) m]
    exact ContinuousAt.comp hdiff.continuousAt (hz_cont.continuousAt (x := τ))
  have h2pi_cont : Continuous (fun τ : ℝ =>
      (2 * (Real.pi : ℂ)) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (τ : ℂ)))) := by
    refine Continuous.const_cpow hz_cont (Or.inl ?_)
    exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_pos.ne')
  have hV_cont : Continuous (fun t : ℝ => (prob.cardyV (c' / 12) t : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_cardyV prob (c' / 12))
  have hnum_meas : Measurable (fun p : ℝ × ℝ =>
      Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (p.1 : ℂ))) *
        (2 * (Real.pi : ℂ)) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
        Complex.exp (((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)) - 1) *
          Complex.log (p.2 : ℂ)) /
        (Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
          (prob.cardyV (c' / 12) p.2 : ℂ))) := by
    have m1 : Measurable (fun p : ℝ × ℝ =>
        Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (p.1 : ℂ)))) :=
      ((hΥ_cont.const_mul (-(c' : ℂ))).cexp.comp continuous_fst).measurable
    have m2 : Measurable (fun p : ℝ × ℝ =>
        (2 * (Real.pi : ℂ)) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)))) :=
      (h2pi_cont.comp continuous_fst).measurable
    have m3 : Measurable (fun p : ℝ × ℝ =>
        Complex.exp (((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)) - 1) *
          Complex.log (p.2 : ℂ))) := by
      refine Measurable.cexp (Measurable.mul ?_ ?_)
      · exact ((hz_cont.sub continuous_const).comp continuous_fst).measurable
      · exact Complex.measurable_log.comp (Complex.continuous_ofReal.comp continuous_snd).measurable
    have m4 : Measurable (fun p : ℝ × ℝ =>
        Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
          (prob.cardyV (c' / 12) p.2 : ℂ)) :=
      ((hgam_cont.comp continuous_fst).mul (hV_cont.comp continuous_snd)).measurable
    exact ((m1.mul m2).mul m3).div m4
  have heq : Function.uncurry (edgeKernelKW prob c') = fun p : ℝ × ℝ =>
      if 0 < p.2 then
        Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (p.1 : ℂ))) *
          (2 * (Real.pi : ℂ)) ^ ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
          Complex.exp (((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ)) - 1) *
            Complex.log (p.2 : ℂ)) /
          (Complex.Gamma ((prob.w : ℂ) / 2 + (c' : ℂ) * chartOmega (Complex.I * (p.1 : ℂ))) *
            (prob.cardyV (c' / 12) p.2 : ℂ))
      else 0 := by
    ext ⟨τ, t⟩
    unfold edgeKernelKW Function.uncurry
    by_cases ht : 0 < t
    · simp only [ht, ↓reduceIte]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
      rw [Complex.cpow_def_of_ne_zero ht_ne, mul_comm (Complex.log (t : ℂ))]
    · simp [ht]
  rw [heq]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) hnum_meas measurable_const

/-! ### Section 2: Lemma J4.1 -/

/-- The Mellin integral representation `W̃_V(iτ) = ∫₀^∞ K(τ, t) g(t) V(t) dt` at weight `w`. -/
lemma tildeWW_edge_integral (prob : FixedWeightProblem) {c' : ℝ}
    (hc' : max 1 (24 * prob.totalShift) ≤ c') (g : ℝ → ℝ) (τ : ℝ) :
    tildeWW prob.w c' g (Complex.I * (τ : ℂ)) =
      ∫ t in Ioi (0 : ℝ),
        edgeKernelKW prob c' τ t * ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ) := by
  obtain ⟨hS, ha0, hc'_pos⟩ := shift_le_of_max_le prob hc'
  let ω := chartOmega (Complex.I * (τ : ℂ))
  let z : ℂ := (prob.w : ℂ) / 2 + (c' : ℂ) * ω
  have hω_re : 0 < ω.re := re_chartOmega_edge_pos τ
  have hz_re : 0 < z.re := by
    dsimp [z]
    have hw1 : (1 : ℝ) ≤ prob.w := by exact_mod_cast prob.hw
    simp only [Complex.div_ofNat_re, Complex.natCast_re, Complex.re_ofReal_mul]
    nlinarith [mul_pos hc'_pos hω_re]
  let Cfac : ℂ := Complex.exp (-(c' : ℂ) * chartUpsilon (Complex.I * (τ : ℂ))) *
    (2 * (Real.pi : ℂ)) ^ z / Complex.Gamma z
  have hcongr : EqOn (fun t : ℝ => edgeKernelKW prob c' τ t *
        ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ))
      (fun t : ℝ => Cfac * ((g t : ℂ) * (t : ℂ) ^ (z - 1))) (Ioi 0) := by
    intro t ht
    have ht0 : 0 < t := mem_Ioi.mp ht
    have hV_pos : 0 < prob.cardyV (c' / 12) t := cardyV_pos_of_max hc' ht0
    have hV_ne : (prob.cardyV (c' / 12) t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hV_pos.ne'
    unfold edgeKernelKW
    simp only [ht0, ↓reduceIte]
    dsimp [Cfac, z, ω]
    push_cast
    field_simp [hV_ne]
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
  unfold tildeWW
  rw [mellinMGEntireW_of_re_pos prob.w g hz_re]
  unfold mellinMGW mellinTransformW
  dsimp [Cfac, z, ω]
  ring

/-- If `W` is bounded by `B` on the closed strip, so is `𝒜_V W` (the prefactor `c'^{5/6} (ζ(1-ζ))^{5/2}
e^{-ζ(1-ζ)}` is bounded by a polynomial in `|Im ζ|` times `e^{-(Im ζ)²}`). -/
lemma edgeHV_bounded_of_multiplier {c' : ℝ} (hc' : 0 < c') {W : ℂ → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hbd : ∀ ζ ∈ stripClosed, ‖W ζ‖ ≤ B) :
    ∃ M_H : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖tebPrefactor c' ζ * W ζ‖ ≤ M_H := by
  let m_H : ℕ := 3
  refine ⟨c' ^ (5 / 6 : ℝ) * B * (2 : ℝ) ^ (5 : ℝ) *
    ((2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ)), fun ζ h0 h1 => ?_⟩
  have hpf := norm_tebPrefactor_le c' hc'.le h0 h1
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
  calc ‖tebPrefactor c' ζ * W ζ‖
      = ‖tebPrefactor c' ζ‖ * ‖W ζ‖ := norm_mul _ _
    _ ≤ (c' ^ (5 / 6 : ℝ) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2)) * B := by
        gcongr
    _ = c' ^ (5 / 6 : ℝ) * B * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2) := by ring
    _ ≤ c' ^ (5 / 6 : ℝ) * B * ((2 : ℝ) ^ (5 : ℝ) * (1 + |ζ.im|) ^ (5 : ℝ)) *
          Real.exp (-ζ.im ^ 2) := by gcongr
    _ = c' ^ (5 / 6 : ℝ) * B * (2 : ℝ) ^ (5 : ℝ) *
          ((1 + |ζ.im|) ^ (5 : ℝ) * Real.exp (-ζ.im ^ 2)) := by ring
    _ ≤ c' ^ (5 / 6 : ℝ) * B * (2 : ℝ) ^ (5 : ℝ) *
          ((2 : ℝ) ^ (5 : ℝ) * max 1 (Nat.factorial m_H : ℝ)) := by gcongr

/-- **Strip Poisson identity for the damped multiplier** (`vlo:J41`): for any `W` holomorphic on
the open strip, continuous and bounded on the closed strip with `W (1 - ζ) = -W ζ`, the function
`H = 𝒜_V W` satisfies `H(ζ₀) = ∫ Q(τ) H(iτ) dτ`, `Q(τ) = p(τ - η₀) - p₁(τ + η₀)`. -/
theorem edgeHV_poisson_of_multiplier {c' : ℝ} (hc' : 0 < c') {W : ℂ → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hdiff : DifferentiableOn ℂ W stripOpen) (hcont : ContinuousOn W stripClosed)
    (href : ∀ ζ ∈ stripClosed, W (1 - ζ) = -W ζ) (hbd : ∀ ζ ∈ stripClosed, ‖W ζ‖ ≤ B)
    {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1) :
    tebPrefactor c' ζ₀ * W ζ₀ =
      ∫ τ : ℝ, (stripPoissonQ ζ₀.re ζ₀.im (-1) τ : ℂ) *
        (tebPrefactor c' ((τ : ℂ) * Complex.I) * W ((τ : ℂ) * Complex.I)) := by
  have hH_cont : ContinuousOn (fun ζ => tebPrefactor c' ζ * W ζ) stripClosed :=
    (tebPrefactor_continuousOn c').mul hcont
  have hH_holo : DifferentiableOn ℂ (fun ζ => tebPrefactor c' ζ * W ζ) stripOpen :=
    (tebPrefactor_differentiableOn c').mul hdiff
  have hH_symm : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 →
      (fun ζ => tebPrefactor c' ζ * W ζ) (1 - ζ) =
        ((-1 : ℝ) : ℂ) * (fun ζ => tebPrefactor c' ζ * W ζ) ζ := fun ζ h0 h1 => by
    dsimp only
    rw [tebPrefactor_symm, href ζ ⟨h0, h1⟩]
    push_cast; ring
  obtain ⟨M_H, hM_H⟩ := edgeHV_bounded_of_multiplier hc' hB hbd
  exact (stripPoisson_representation_symm hH_cont hH_holo hM_H hH_symm hσ₀ hσ₁).2

/-- Bounds on the Poisson kernel `Q = p(· - η₀) - p₁(· + η₀)` (weight free): `‖Q‖₁ ≤ 1` and
`sup |Q| + TV(Q) ≤ 2/σ₀` for `0 < σ₀ ≤ 0.04`. -/
lemma stripPoissonQ_bounds_J41 {ζ₀ : ℂ} (hσ₀ : 0 < ζ₀.re) (hσ₀_le : ζ₀.re ≤ 0.04) :
    (∫ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| ≤ 1) ∧
      (∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| +
        (eVariationOn (stripPoissonQ ζ₀.re ζ₀.im (-1)) univ).toReal ≤ 2 / ζ₀.re) := by
  have hσ₁ : ζ₀.re < 1 := by linarith
  refine ⟨stripPoissonQ_norm_L1_le hσ₀ hσ₁ ζ₀.im, fun τ => ?_⟩
  have h1 := (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im (ε := -1) (by norm_num) τ).trans
    (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
  have h2 := stripPoissonQ_tv_le hσ₀ hσ₀_le ζ₀.im (ε := -1) (by norm_num)
  calc |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| +
        (eVariationOn (stripPoissonQ ζ₀.re ζ₀.im (-1)) univ).toReal
      ≤ 1 / ζ₀.re + 1 / ζ₀.re := add_le_add h1 h2
    _ = 2 / ζ₀.re := by ring

/-- **Lemma J4.1 at weight `w` (representation and Poisson identity)**
(`lower_o1_two_edge.tex`, §J4, `vlo:J41`): for a fixed-weight problem `prob` there is `c₀` with
`max 1 (24 S) ≤ c₀` such that for `c' ≥ c₀` and `g ∈ TestClass prob (c'/12)`:
1. `W̃_V(iτ) = ∫_{(0,∞)} K(τ, t) g(t) V(t) dt` for all `τ`;
2. `H_V(iτ) = 𝒜_V(τ) W̃_V(iτ)` and `H_V(ζ₀) = ∫_ℝ Q(τ) H_V(iτ) dτ` for `0 < Re ζ₀ < 1`,
   `Q(τ) = p(τ - η₀) - p₁(τ + η₀)`;
3. `‖Q‖₁ ≤ 1`, and `sup |Q| + TV(Q) ≤ 2/Re ζ₀` for `0 < Re ζ₀ ≤ 0.04`.
The Virasoro `StripMultiplier.lemma_J4_1` is the `w = 1` instance (`EdgeKernelWBridge`). -/
theorem lemma_J4_1_W (prob : FixedWeightProblem) :
    ∃ c₀ : ℝ, max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass prob (c' / 12) g →
        (∀ τ : ℝ, tildeWW prob.w c' g (Complex.I * (τ : ℂ)) =
          ∫ t in Ioi (0 : ℝ),
            edgeKernelKW prob c' τ t * ((g t * prob.cardyV (c' / 12) t : ℝ) : ℂ)) ∧
        (∀ τ : ℝ, edgeHVW prob.w c' g ((τ : ℂ) * Complex.I) =
          tebAmp0 c' τ * tildeWW prob.w c' g ((τ : ℂ) * Complex.I)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re < 1 →
          edgeHVW prob.w c' g ζ₀ =
            ∫ τ : ℝ, (stripPoissonQ ζ₀.re ζ₀.im (-1) τ : ℂ) *
              edgeHVW prob.w c' g ((τ : ℂ) * Complex.I)) ∧
        (∀ {ζ₀ : ℂ}, 0 < ζ₀.re → ζ₀.re ≤ 0.04 →
          (∫ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| ≤ 1) ∧
          (∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im (-1) τ| +
            (eVariationOn (stripPoissonQ ζ₀.re ζ₀.im (-1)) univ).toReal ≤ 2 / ζ₀.re)) := by
  obtain ⟨C, c₀, hC, hc₀, hS4⟩ := lemma_S4_W prob
  refine ⟨c₀, hc₀, fun {c'} hc' {g} hg => ?_⟩
  have hc'max : max 1 (24 * prob.totalShift) ≤ c' := hc₀.trans hc'
  obtain ⟨hS, ha0, hc'_pos⟩ := shift_le_of_max_le prob hc'max
  obtain ⟨hdiff, hcont, href, hbd⟩ := hS4 hc' hg
  refine ⟨fun τ => tildeWW_edge_integral prob hc'max g τ, fun _ => rfl, ?_,
    fun {ζ₀} hσ₀ hσ₀_le => stripPoissonQ_bounds_J41 hσ₀ hσ₀_le⟩
  intro ζ₀ hσ₀ hσ₁
  have hM_nn : 0 ≤ C * prob.cardyNorm (c' / 12) g :=
    mul_nonneg hC.le (prob.cardyNorm_nonneg hS g)
  exact edgeHV_poisson_of_multiplier hc'_pos hM_nn hdiff hcont href hbd hσ₀ hσ₁

/-! ### Section 3: Lemma J4.2 -/

/-- **Lemma J4.2 at weight `w` (kernel factorization)** (`lower_o1_two_edge.tex`, §J4, `vlo:J42`):
there are constants `C_A1, C_A1', C_A2, C_sub, κ_sub > 0` and `c₀ ≥ max 1 (24 S)` such that for
`c' ≥ c₀`:
1. `|A₁(τ)| ≤ C_A1`, `A₁` is differentiable with `|A₁'(τ)| ≤ C_A1'/(1+|τ|)`
   (`A₁ = S^{(w)}_{c'}(ω(iτ))^{-1} (2π/(3ω(iτ)))^{(w-1)/2}`);
2. `0 ≤ A₂(x) ≤ C_A2` for `x = √(3t/c') ≥ ξ*/2` (`A₂ = x^{w-1} t^{-1/2} e^{c'L(x)}/V(t)`);
3. `|K(τ, x)| ≤ C_sub e^{-κ_sub c'}` for `0 < x ≤ ξ*/2`, uniformly in `τ`;
4. for `t > 0`: `K = A₁ A₂ exp(c'(R_V + iΘ))`, `R_V = -D(x₀(τ), x) ≤ 0` even in `τ`, `Θ` odd with
   `∂_τ Θ = 2ν'(τ) log(x₀(τ)/x)`;
5. `τ ↦ R_V(τ; x)` is nondecreasing on `(0, τ₀(x)]` and nonincreasing on `[τ₀(x), ∞)`.
`R_V`, `Θ`, `x₀`, `ν'` are the weight-free `StripMultiplier.edgeRV`, `edgeTheta`, `edgeX0`,
`edgeNuDeriv`. -/
theorem lemma_J4_2_W (prob : FixedWeightProblem) :
    ∃ C_A1 C_A1' C_A2 C_sub κ_sub c₀ : ℝ,
      0 < C_A1 ∧ 0 < C_A1' ∧ 0 < C_A2 ∧ 0 < C_sub ∧ 0 < κ_sub ∧
      max 1 (24 * prob.totalShift) ≤ c₀ ∧
      ∀ {c' : ℝ}, c₀ ≤ c' →
        (∀ τ : ℝ, ‖edgeA1W prob.w c' τ‖ ≤ C_A1 ∧
          ∃ d : ℂ, HasDerivAt (edgeA1W prob.w c') d τ ∧ ‖d‖ ≤ C_A1' / (1 + |τ|)) ∧
        (∀ {t : ℝ}, 0 < t → xiStar / 2 ≤ √(3 * t / c') →
          0 ≤ edgeA2W prob c' t ∧ edgeA2W prob c' t ≤ C_A2) ∧
        (∀ {t : ℝ}, 0 < t → √(3 * t / c') ≤ xiStar / 2 →
          ∀ τ : ℝ, ‖edgeKernelKW prob c' τ t‖ ≤ C_sub * Real.exp (-κ_sub * c')) ∧
        (∀ {t : ℝ}, 0 < t → ∀ τ : ℝ,
          edgeKernelKW prob c' τ t = edgeA1W prob.w c' τ * (edgeA2W prob c' t : ℂ) *
            Complex.exp ((c' : ℂ) * ((edgeRV c' τ t : ℂ) + Complex.I * (edgeTheta c' τ t : ℂ))) ∧
          edgeRV c' τ t ≤ 0 ∧ edgeRV c' (-τ) t = edgeRV c' τ t ∧
          edgeTheta c' (-τ) t = -edgeTheta c' τ t ∧
          HasDerivAt (fun s => edgeTheta c' s t)
            (2 * edgeNuDeriv τ * Real.log (edgeX0 τ / √(3 * t / c'))) τ) ∧
        (∀ {t : ℝ}, 0 < t →
          MonotoneOn (fun τ => edgeRV c' τ t) (Ioi 0 ∩ Iic (edgeTau0 c' t)) ∧
          AntitoneOn (fun τ => edgeRV c' τ t) (Ioi 0 ∩ Ici (edgeTau0 c' t))) := by
  obtain ⟨C_A1, C_A1', hC_A1, hC_A1', hA1⟩ := edgeA1W_deriv_le prob.hw
  obtain ⟨C_A2, c₂, hC_A2, hc₂, hA2⟩ := edgeA2W_nonneg_le prob
  obtain ⟨C_sub, κ_sub, c₃, hC_sub, hκ_sub, hc₃, hsub⟩ := edgeKernelKW_subCardy_bound prob
  refine ⟨C_A1, C_A1', C_A2, C_sub, κ_sub, max (max c₂ c₃) (max 1 (1 / muStar)),
    hC_A1, hC_A1', hC_A2, hC_sub, hκ_sub,
    hc₂.trans ((le_max_left _ _).trans (le_max_left _ _)), fun {c'} hc' => ?_⟩
  have hc₂' : c₂ ≤ c' := (le_max_left _ _).trans ((le_max_left _ _).trans hc')
  have hc₃' : c₃ ≤ c' := (le_max_right _ _).trans ((le_max_left _ _).trans hc')
  have hc_mu : max 1 (1 / muStar) ≤ c' := (le_max_right _ _).trans hc'
  have hc'max : max 1 (24 * prob.totalShift) ≤ c' := hc₂.trans hc₂'
  obtain ⟨-, -, hc'_pos⟩ := shift_le_of_max_le prob hc'max
  refine ⟨fun τ => hA1 hc_mu τ, fun {t} ht hx => hA2 hc₂' ht hx,
    fun {t} ht hx τ => hsub hc₃' ht hx τ,
    fun {t} ht τ => ⟨edgeKernelKW_factorization_theta prob hc'max τ ht, edgeRV_nonpos ht hc'_pos,
      edgeRV_even c' τ t, by unfold edgeTheta; rw [edgePhi_odd hc'_pos ht, neg_neg],
      hasDerivAt_edgeTheta hc'_pos ht τ⟩,
    fun {t} ht => edgeRV_unimodal hc'_pos ht⟩

/-! ### Axiom verification -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_J4_1_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_1_W

/-- info: 'FormalResearch.ModularBootstrap.FixedWeightBand.lemma_J4_2_W' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_J4_2_W

end FormalResearch.ModularBootstrap.FixedWeightBand

module

public import FormalResearch.ModularBootstrap.Blowup.PotentialAndWeight
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Complex entropy/mass, concrete test interface, tip rescaling, and Lemma T5 (`blowup_limit.tex`)

Formalizes:
* `lemma_T4`: **Lemma T4** (`blowup_limit.tex`, Lemma `bl:T4`), wrapping `lemmaE_complex` and
  `lemmaS_complex` from `SlitStrip/EntropyAndDeficit.lean`.
* `StripBootstrapInputs`: minimal bundle collecting the uniform strip/potential inputs
  (`LemmaGPotentialInput`, `PoissonJensenInput`, `FixedGapInput`, `c_PJ_complex`, `C_PJ_complex`),
  with `stripBootstrapInputs_nonvacuous`.
* `BlowupTest`: concrete per-test interface (real `g`, holomorphic continuation `G` on
  `|Im b| < 1/2`, weight `V = V_C`, mass `M[g]`, weak feasibility, tip threshold `x₁`, vacuum
  `gVac`, Hankel vacuum identity, real/complex PJ and deep-lobe bounds). Designed as the minimal
  interface that the parallel `Crossing/` test-class formalization can instantiate directly.
* `tipRescale` (`Φ_c`): the exact tip rescaling `Φ_c(ζ) = W_C(b) G(b) / M` (`b = ξ_* + ε ζ`),
  together with strip holomorphy, Schwarz reflection symmetry (`tipRescale_real_symm`), exact
  real-axis `L¹`, vacuum, and half-negative-mass identities (`BlowupTest.halfMass_derived`,
  showing weak feasibility's half-mass condition follows automatically from `g ≥ 0` on `[t₁, ∞)`
  and `∫ g V = -gVac/(2π) ≤ 0`), and `BlowupTest.toWeaklyFeasibleTest`.
* `lemma_T5`: **Lemma T5** (`blowup_limit.tex`, Lemma `bl:T5`), combining Lemmas T1, T2, T3, T4,
  and strip Poisson--Jensen (`hPJ_complex`). Note the tiny TeX typo in `blowup_limit.tex` Lemma T5
  saying `C₁,…,C₄` when only `C₁, C₂, C₃` appear in the inequality.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real

namespace FormalResearch.ModularBootstrap

/-! ### Section 1: Lemma T4 (complex entropy and edge mass) -/

/-- **Lemma T4** (`blowup_limit.tex`, Lemma `bl:T4`): for `z_b = x + i y` in the upper half-plane
with `‖z_b - σ_*‖ ≤ 0.1`, recalls `lemmaE_complex` and `lemmaS_complex` from
`EntropyAndDeficit.lean`. -/
theorem lemma_T4 {x y : ℝ} (hy : 0 < y)
    (hz : ‖(x : ℂ) + y * I - (sigmaStar : ℂ)‖ ≤ 0.1) :
    1 - slitMass x y ≤ (2 / (0.3 * π)) * y ∧
      slitEntropy x y ≤
        Real.log (1 / y) + Real.log (1 / ‖(x : ℂ) + y * I - (sigmaStar : ℂ)‖) +
          slitEntropyComplexConst := by
  refine ⟨?_, lemmaS_complex hy hz⟩
  calc 1 - slitMass x y ≤ 2 * y / (0.3 * π) := lemmaE_complex hy hz
    _ = (2 / (0.3 * π)) * y := by ring

/-! ### Section 2: Upstream inputs bundle and concrete `BlowupTest` interface -/

/-- Named upstream analytic inputs for strip Poisson--Jensen and slit-strip majorant bounds
(`lower_o1_two_edge.tex`, Lemmas B, G, PJ). The classical Bessel `I_0` asymptotic is passed
separately as `hI0 : BesselI0Asymptotic`. -/
structure StripBootstrapInputs where
  pot : LemmaGPotentialInput
  pj : PoissonJensenInput
  fg : FixedGapInput
  c_PJ_complex : ℝ
  hc_PJ_complex : 39 ≤ c_PJ_complex
  C_PJ_complex : ℝ

/-- Non-vacuity witness for `StripBootstrapInputs`. -/
theorem stripBootstrapInputs_nonvacuous : Nonempty StripBootstrapInputs := by
  obtain ⟨pot⟩ := lemmaGPotentialInput_nonvacuous
  obtain ⟨pj, fg, _⟩ := slitStrip_hypotheses_nonvacuous
  exact ⟨{
    pot := pot
    pj := pj
    fg := fg
    c_PJ_complex := 39
    hc_PJ_complex := le_rfl
    C_PJ_complex := 0
  }⟩

/-- Minimal concrete per-test interface for weakly feasible modular bootstrap tests at `c' = c - 1`.
Designed for direct instantiation by the parallel `Crossing/` test-class formalization. -/
structure BlowupTest (inp : StripBootstrapInputs) (c' : ℝ) where
  g : ℝ → ℝ
  G : ℂ → ℂ
  V : ℝ → ℝ
  K_a : ℝ → ℝ
  M : ℝ
  t₁ : ℝ
  x₁ : ℝ
  gVac : ℝ
  hM_pos : 0 < M
  hx₁_nonneg : 0 ≤ x₁
  ht₁_eq : t₁ = c' * x₁ ^ 2 / 3
  hgVac_nonneg : 0 ≤ gVac
  hg_cont : ContinuousOn g (Ici 0)
  hV_cont : ContinuousOn V (Ici 0)
  hV_pos : ∀ t > 0, 0 < V t
  hV_nonneg : ∀ t ≥ 0, 0 ≤ V t
  hV_eq_C : ∀ t : ℝ, (V t : ℂ) = V_C (c' : ℂ) (t : ℂ)
  hG_holo : DifferentiableOn ℂ G {b : ℂ | |b.im| < 1 / 2}
  hG_real : ∀ x : ℝ, G (x : ℂ) = (g (c' * x ^ 2 / 3) : ℂ)
  hM_int : IntegrableOn (fun t => |g t| * V t) (Ioi 0)
  hM_eq : ∫ t in Ioi 0, |g t| * V t = M
  hg_nonneg_tail : ∀ t, t₁ ≤ t → 0 ≤ g t
  hVac_int : IntegrableOn (fun t => g t * V t) (Ioi 0)
  hVac_eq : ∫ t in Ioi 0, g t * V t = -gVac / (2 * π)
  hV_le_two_Ka : ∀ x ∈ Icc (0.05 : ℝ) xiStar, V (c' * x ^ 2 / 3) ≤ 2 * K_a (c' * x ^ 2 / 3)
  hKa_ub : ∀ x ∈ Icc (0.05 : ℝ) xiStar,
    K_a (c' * x ^ 2 / 3) ≤ inp.pj.C_K * Real.exp (c' * ((2 * π / 3) * x)) / Real.sqrt c'
  hPJ_real : ∀ x ∈ Ico 0 xiStar, g (c' * x ^ 2 / 3) ≠ 0 →
    Real.log |g (c' * x ^ 2 / 3)| ≤ c' * inp.pj.U x + Real.log M - (1 / 2 : ℝ) * Real.log c' +
      (5 / 2 : ℝ) * (1 - inp.pj.rs.slitMassAt x) * Real.log c' + inp.pj.rs.slitEntropyAt x +
      inp.pj.C_PJ
  hDeepLobe : inp.fg.c_deep ≤ c' →
    ∫ t in (0 : ℝ)..(c' * (0.05 : ℝ) ^ 2 / 3), |g t| * V t ≤
      inp.fg.C_deep * Real.exp (-inp.fg.κ_deep * c') * M
  hPJ_complex : inp.c_PJ_complex ≤ c' → ∀ z : ℂ, 0 < z.im → ‖z - (sigmaStar : ℂ)‖ ≤ 0.1 →
    let b := slitBoundaryMapC z
    |b.im| < 1 / 2 → G b ≠ 0 →
      Real.log ‖G b‖ ≤ c' * inp.pot.U b + Real.log M - (1 / 2 : ℝ) * Real.log c' +
        (5 / 2 : ℝ) * (1 - slitMass z.re z.im) * Real.log c' + slitEntropy z.re z.im +
        inp.C_PJ_complex

/-- Left-endpoint coordinate `-xiStar * c'^(2/3)` corresponding to `b = 0` (`t = 0`). -/
noncomputable def tipSMin (c' : ℝ) : ℝ := -xiStar * c' ^ ((2 : ℝ) / 3)

/-- Tip threshold coordinate `s₁ = (x₁ - ξ_*) / ε`. -/
noncomputable def tipS₁ {inp : StripBootstrapInputs} (c' : ℝ) (test : BlowupTest inp c') : ℝ :=
  (test.x₁ - xiStar) / tipEps c'

/-- Exact scaling relation between `t₁ = c' x₁^2 / 3` and `s₁ = (x₁ - ξ_*) / ε`. -/
lemma tipS₁_scaling_eq {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    test.t₁ = xiBar * c' + (2 / 3 : ℝ) * xiStar * c' ^ (1 / 3 : ℝ) * tipS₁ c' test +
      (1 / 3 : ℝ) * c' ^ (-(1 / 3 : ℝ)) * (tipS₁ c' test) ^ 2 := by
  have hx₁ : test.x₁ = xiStar + tipEps c' * tipS₁ c' test := by
    unfold tipS₁
    have hε : tipEps c' ≠ 0 := (tipEps_pos hc').ne'
    field_simp [hε]; ring
  have hce : c' * tipEps c' = c' ^ (1 / 3 : ℝ) := by
    unfold tipEps
    calc c' * c' ^ (-(2 / 3 : ℝ)) = c' ^ (1 : ℝ) * c' ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
      _ = c' ^ (1 + -(2 / 3 : ℝ)) := (Real.rpow_add hc' _ _).symm
      _ = c' ^ (1 / 3 : ℝ) := by norm_num
  have hce2 : c' * tipEps c' ^ 2 = c' ^ (-(1 / 3 : ℝ)) := by
    unfold tipEps
    calc c' * (c' ^ (-(2 / 3 : ℝ))) ^ 2
        = c' ^ (1 : ℝ) * c' ^ (-(4 / 3 : ℝ)) := by
            rw [Real.rpow_one, ← Real.rpow_natCast (c' ^ (-(2 / 3 : ℝ))) 2,
              ← Real.rpow_mul hc'.le]
            norm_num
      _ = c' ^ (-(1 / 3 : ℝ)) := by
          rw [← Real.rpow_add hc']; norm_num
  rw [test.ht₁_eq, hx₁]
  unfold xiBar
  rw [show c' * (xiStar + tipEps c' * tipS₁ c' test) ^ 2 / 3 =
      xiStar ^ 2 / 3 * c' + (2 / 3 : ℝ) * xiStar * (c' * tipEps c') * tipS₁ c' test +
        (1 / 3 : ℝ) * (c' * tipEps c' ^ 2) * (tipS₁ c' test) ^ 2 by ring,
    hce, hce2]

lemma tipSMin_eq_neg_div_tipEps {c' : ℝ} (hc' : 0 < c') :
    tipSMin c' = -xiStar / tipEps c' := by
  unfold tipSMin tipEps
  rw [Real.rpow_neg hc'.le, div_inv_eq_mul]

lemma BlowupTest.ht₁_nonneg {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 ≤ c')
    (test : BlowupTest inp c') : 0 ≤ test.t₁ := by
  rw [test.ht₁_eq]; positivity

/-- Weak feasibility half-mass on `[0, t₁]` follows automatically from `g ≥ 0` on `[t₁, ∞)`,
`∫_0^∞ |g| V = M`, and `∫_0^∞ g V = -gVac/(2π) ≤ 0`. -/
lemma BlowupTest.halfMass_derived {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 ≤ c')
    (test : BlowupTest inp c') :
    test.M / 2 ≤ ∫ t in (0 : ℝ)..test.t₁, |test.g t| * test.V t := by
  have ht₁_nn : 0 ≤ test.t₁ := test.ht₁_nonneg hc'
  have hneg_int : IntegrableOn (fun t => max 0 (-test.g t) * test.V t) (Ioi 0) := by
    have heq : (fun t => max 0 (-test.g t) * test.V t) =
        fun t => ((|test.g t| * test.V t) - (test.g t * test.V t)) / 2 := by
      funext t
      rcases le_total (test.g t) 0 with h | h
      · have : max 0 (-test.g t) = -test.g t := max_eq_right (neg_nonneg.mpr h)
        rw [this, abs_of_nonpos h]; ring
      · have : max 0 (-test.g t) = 0 := max_eq_left (neg_nonpos.mpr h)
        rw [this, abs_of_nonneg h]; ring
    rw [heq]
    exact (test.hM_int.sub test.hVac_int).div_const 2
  have hhalf_all : test.M / 2 ≤ ∫ t in Ioi 0, max 0 (-test.g t) * test.V t := by
    have hsplit : (fun t => max 0 (-test.g t) * test.V t) =
        fun t => (|test.g t| * test.V t - test.g t * test.V t) / 2 := by
      funext t
      rcases le_total (test.g t) 0 with h | h
      · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    rw [hsplit]
    have hdiv : ∫ t in Ioi 0, (|test.g t| * test.V t - test.g t * test.V t) / 2 =
        (∫ t in Ioi 0, |test.g t| * test.V t - test.g t * test.V t) / 2 :=
      integral_div 2 _
    rw [hdiv, integral_sub test.hM_int test.hVac_int, test.hM_eq, test.hVac_eq, neg_div]
    have hgvac : 0 ≤ test.gVac / (2 * π) := div_nonneg test.hgVac_nonneg (by positivity)
    linarith
  have htail_zero : ∫ t in Ioi test.t₁, max 0 (-test.g t) * test.V t = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    have hgnn : 0 ≤ test.g t := test.hg_nonneg_tail t (mem_Ioi.mp ht).le
    rw [max_eq_left (neg_nonpos.mpr hgnn), zero_mul]
  have hunion : (∫ t in Ioc 0 test.t₁, max 0 (-test.g t) * test.V t) +
      (∫ t in Ioi test.t₁, max 0 (-test.g t) * test.V t) =
      ∫ t in Ioi 0, max 0 (-test.g t) * test.V t := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hneg_int.mono_set Ioc_subset_Ioi_self)
      (hneg_int.mono_set (Ioi_subset_Ioi ht₁_nn)), Ioc_union_Ioi_eq_Ioi ht₁_nn]
  have hle_neg : ∫ t in Ioc 0 test.t₁, max 0 (-test.g t) * test.V t ≤
      ∫ t in Ioc 0 test.t₁, |test.g t| * test.V t := by
    refine setIntegral_mono_on (hneg_int.mono_set Ioc_subset_Ioi_self)
      (test.hM_int.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht => ?_
    have hgn : max 0 (-test.g t) ≤ |test.g t| :=
      max_le (abs_nonneg _) (neg_le_abs _)
    exact mul_le_mul_of_nonneg_right hgn (test.hV_nonneg t ht.1.le)
  rw [intervalIntegral.integral_of_le ht₁_nn]
  linarith

/-- Coerce a `BlowupTest` at `c' > 0` to `WeaklyFeasibleTest inp.pj inp.fg c'` so `theorem_A`
and `proposition_M` from `EntropyAndDeficit.lean` apply directly. -/
noncomputable def BlowupTest.toWeaklyFeasibleTest {inp : StripBootstrapInputs} {c' : ℝ}
    (hc' : 0 ≤ c') (test : BlowupTest inp c') :
    WeaklyFeasibleTest inp.pj inp.fg c' where
  g := test.g
  V := test.V
  K_a := test.K_a
  M := test.M
  t₁ := test.t₁
  hM_pos := test.hM_pos
  ht₁_nonneg := test.ht₁_nonneg hc'
  hg_cont := test.hg_cont
  hV_cont := test.hV_cont
  hV_nonneg := test.hV_nonneg
  hM_int := test.hM_int
  hM_eq := test.hM_eq
  hV_le_two_Ka := test.hV_le_two_Ka
  hKa_ub := test.hKa_ub
  hPJ := test.hPJ_real
  hDeepLobe := test.hDeepLobe
  hHalfMass := test.halfMass_derived hc'

/-! ### Section 3: Tip rescaling `Φ_c`, holomorphy, Schwarz reflection, and real integrals -/

/-- Exact tip rescaling `Φ_c(ζ) = W(b) G(b) / M` where `b = ξ_* + ε ζ`, `ε = c'^{-2/3}`
(`blowup_limit.tex`, §1). -/
noncomputable def tipRescale {inp : StripBootstrapInputs} (c' : ℝ)
    (test : BlowupTest inp c') (ζ : ℂ) : ℂ :=
  W_C c' (bScale c' ζ) * test.G (bScale c' ζ) / (test.M : ℂ)

/-- Real coordinate maps `b(s) = ξ_* + ε s` and `t(s) = c' b(s)^2 / 3`. -/
noncomputable def tipBReal (c' s : ℝ) : ℝ := xiStar + tipEps c' * s
noncomputable def tipTReal (c' s : ℝ) : ℝ := c' * (tipBReal c' s) ^ 2 / 3

lemma bScale_ofReal (c' s : ℝ) : bScale c' (s : ℂ) = ((tipBReal c' s : ℝ) : ℂ) := by
  unfold bScale tipBReal; push_cast; rfl

/-- `tipRescale` is holomorphic on the horizontal strip `{ζ : ℂ | |ζ.im| < 1 / (2 ε)}`. -/
theorem tipRescale_holo {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    DifferentiableOn ℂ (tipRescale c' test) {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')} := by
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'
  have hW : DifferentiableOn ℂ (fun ζ => W_C c' (bScale c' ζ))
      {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')} := fun ζ _ => by
    have hb : DifferentiableAt ℂ (bScale c') ζ := by
      unfold bScale
      exact (differentiableAt_const _).add ((differentiableAt_const _).mul differentiableAt_id)
    exact ((W_C_entire c' (bScale c' ζ)).comp ζ hb).differentiableWithinAt
  have hG : DifferentiableOn ℂ (fun ζ => test.G (bScale c' ζ))
      {ζ : ℂ | |ζ.im| < 1 / (2 * tipEps c')} := by
    refine test.hG_holo.comp ?_ ?_
    · unfold bScale
      exact (differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)
    · intro ζ hζ
      rw [mem_ofPred_eq] at hζ ⊢
      have him : (bScale c' ζ).im = tipEps c' * ζ.im := by
        unfold bScale
        simp [Complex.add_im, Complex.mul_im]
      rw [him, abs_mul, abs_of_pos hε_pos]
      have hlt : |ζ.im| * (2 * tipEps c') < 1 :=
        (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * tipEps c')).mp hζ
      linarith
  intro ζ hζ
  unfold tipRescale
  exact (((hW ζ hζ).mul (hG ζ hζ)).div_const (test.M : ℂ))

/-- On `ball (0 : ℂ) R`, `tipRescale` is holomorphic as soon as `2 * R * ε < 1`. -/
theorem tipRescale_holo_ball {inp : StripBootstrapInputs} {c' R : ℝ} (hc' : 0 < c')
    (hR : 2 * R * tipEps c' < 1) (test : BlowupTest inp c') :
    DifferentiableOn ℂ (tipRescale c' test) (ball 0 R) := by
  refine (tipRescale_holo hc' test).mono fun ζ hζ => ?_
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'
  have him : |ζ.im| < R := (Complex.abs_im_le_norm ζ).trans_lt (mem_ball_zero_iff.mp hζ)
  rw [mem_ofPred_eq, lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * tipEps c')]
  nlinarith

/-- On the real axis, `tipRescale c' test (s : ℂ)` is real and equals the exact weight-test
product `ε (2 c' / 3) b(s) g(t(s)) V(t(s)) / M`. -/
lemma tipRescale_real_on_real {inp : StripBootstrapInputs} {c' : ℝ} (test : BlowupTest inp c')
    (s : ℝ) :
    tipRescale c' test (s : ℂ) =
      ((tipEps c' * (2 * c' / 3) * tipBReal c' s *
        test.V (tipTReal c' s) * test.g (tipTReal c' s) / test.M : ℝ) : ℂ) := by
  unfold tipRescale W_C tipTReal
  rw [bScale_ofReal]
  have ht_cast : ((c' : ℂ) * ((tipBReal c' s : ℝ) : ℂ) ^ 2 / 3) =
      (((c' * tipBReal c' s ^ 2 / 3 : ℝ) : ℂ)) := by push_cast; ring
  rw [ht_cast, ← test.hV_eq_C, test.hG_real]
  push_cast; ring

lemma tipRescale_im_eq_zero {inp : StripBootstrapInputs} {c' : ℝ} (test : BlowupTest inp c')
    (s : ℝ) : (tipRescale c' test (s : ℂ)).im = 0 := by
  rw [tipRescale_real_on_real test s, Complex.ofReal_im]

/-- Schwarz reflection symmetry `Φ_c (conj ζ) = conj (Φ_c ζ)` on the open strip
`{ζ : ℂ | |ζ.im| < 1 / (2 ε)}`, proved via the identity principle. -/
theorem tipRescale_real_symm {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') {ζ : ℂ} (hζ : |ζ.im| < 1 / (2 * tipEps c')) :
    tipRescale c' test (starRingEnd ℂ ζ) = starRingEnd ℂ (tipRescale c' test ζ) := by
  let S : Set ℂ := {w : ℂ | |w.im| < 1 / (2 * tipEps c')}
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'
  have hL_pos : 0 < 1 / (2 * tipEps c') := by positivity
  have hS_open : IsOpen S := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hS_conv : Convex ℝ S := by
    intro x hx y hy a b ha hb hab
    rw [mem_ofPred_eq] at hx hy ⊢
    let m : ℝ := max |x.im| |y.im|
    have hm_lt : m < 1 / (2 * tipEps c') := max_lt hx hy
    have him_eq : (a • x + b • y).im = a * x.im + b * y.im := by simp
    rw [him_eq]
    calc |a * x.im + b * y.im|
        ≤ |a * x.im| + |b * y.im| := abs_add_le _ _
      _ = a * |x.im| + b * |y.im| := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * m + b * m := add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hb)
      _ = m := by linear_combination m * hab
      _ < 1 / (2 * tipEps c') := hm_lt
  have hS_conj : ∀ w ∈ S, starRingEnd ℂ w ∈ S := fun w hw => by
    simpa [S, Complex.conj_im] using hw
  have hf : DifferentiableOn ℂ (tipRescale c' test) S := tipRescale_holo hc' test
  let g : ℂ → ℂ := fun w => starRingEnd ℂ (tipRescale c' test (starRingEnd ℂ w))
  have hg : DifferentiableOn ℂ g S := fun w hw => by
    have hw' := hS_conj w hw
    have hd := (hf.differentiableAt (hS_open.mem_nhds hw')).conj_conj
    simp only [Complex.conj_conj] at hd
    exact hd.differentiableWithinAt
  have h0S : (0 : ℂ) ∈ S := by simpa [S] using hL_pos
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), tipRescale c' test w = g w := by
    rw [Filter.frequently_iff]
    intro U hU
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hU
    obtain ⟨V, hV, hVU⟩ := hU
    obtain ⟨r, hr_pos, hr_ball⟩ := Metric.mem_nhds_iff.mp hV
    let δ : ℝ := min (r / 2) (1 / (4 * tipEps c'))
    have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
    refine ⟨(δ : ℂ), hVU ⟨hr_ball ?_, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ_pos]
      exact (min_le_left _ _).trans_lt (half_lt_self hr_pos)
    · exact Complex.ofReal_ne_zero.mpr hδ_pos.ne'
    · dsimp [g]
      rw [Complex.conj_ofReal]
      exact (Complex.conj_eq_iff_im.mpr (tipRescale_im_eq_zero test δ)).symm
  have heq : EqOn (tipRescale c' test) g S :=
    (hf.analyticOnNhd hS_open).eqOn_of_preconnected_of_frequently_eq
      (hg.analyticOnNhd hS_open) hS_conv.isPreconnected h0S hfreq
  have h1 := congr_arg (starRingEnd ℂ) (heq hζ)
  rw [Complex.conj_conj] at h1
  exact h1.symm

/-- Exact change-of-variables image and derivative facts for `tipTReal c'` on `Ioi (tipSMin c')`. -/
lemma tipTReal_deriv {c' s : ℝ} :
    HasDerivAt (tipTReal c') (tipEps c' * (2 * c' / 3) * tipBReal c' s) s := by
  unfold tipTReal tipBReal
  have hb : HasDerivAt (fun x => xiStar + tipEps c' * x) (tipEps c') s := by
    simpa using ((hasDerivAt_id s).const_mul (tipEps c')).const_add xiStar
  have hsq := ((hb.pow 2).const_mul c').div_const 3
  refine hsq.congr_deriv ?_
  ring

lemma tipBReal_pos_iff {c' s : ℝ} (hc' : 0 < c') :
    0 < tipBReal c' s ↔ tipSMin c' < s := by
  unfold tipBReal
  rw [tipSMin_eq_neg_div_tipEps hc']
  have hε := tipEps_pos hc'
  constructor <;> intro h
  · rw [div_lt_iff₀ hε]; linarith
  · rw [div_lt_iff₀ hε] at h; linarith

lemma tipTReal_injOn {c' : ℝ} (hc' : 0 < c') :
    InjOn (tipTReal c') (Ioi (tipSMin c')) := by
  intro x hx y hy hxy
  have hbx : 0 < tipBReal c' x := (tipBReal_pos_iff hc').mpr hx
  have hby : 0 < tipBReal c' y := (tipBReal_pos_iff hc').mpr hy
  unfold tipTReal at hxy
  have hsq : tipBReal c' x ^ 2 = tipBReal c' y ^ 2 := by
    have hc'0 : c' ≠ 0 := hc'.ne'
    linarith [show c' * tipBReal c' x ^ 2 = c' * tipBReal c' y ^ 2 by linarith,
      mul_left_cancel₀ hc'0 (show c' * tipBReal c' x ^ 2 = c' * tipBReal c' y ^ 2 by linarith)]
  have hb_eq : tipBReal c' x = tipBReal c' y := by nlinarith
  unfold tipBReal at hb_eq
  exact mul_left_cancel₀ (tipEps_pos hc').ne' (by linarith)

lemma tipTReal_image_Ioi {c' a : ℝ} (hc' : 0 < c') (ha : tipSMin c' ≤ a) :
    tipTReal c' '' Ioi a = Ioi (tipTReal c' a) := by
  have hε_pos := tipEps_pos hc'
  have hba : 0 ≤ tipBReal c' a := by
    unfold tipBReal
    rw [tipSMin_eq_neg_div_tipEps hc'] at ha
    have : -xiStar ≤ tipEps c' * a := (div_le_iff₀' hε_pos).mp (by simpa [neg_div] using ha)
    linarith
  ext t
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, rfl⟩
    have hbs : tipBReal c' a < tipBReal c' s := by
      unfold tipBReal; gcongr; exact hs
    unfold tipTReal
    have hsq : tipBReal c' a ^ 2 < tipBReal c' s ^ 2 := by nlinarith
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hsq hc') (by norm_num)
  · intro ht
    have ht_pos : 0 < t := lt_of_le_of_lt (by unfold tipTReal; positivity) ht
    let s : ℝ := (Real.sqrt (3 * t / c') - xiStar) / tipEps c'
    have hbs : tipBReal c' s = Real.sqrt (3 * t / c') := by
      unfold tipBReal
      have hm : tipEps c' * s = Real.sqrt (3 * t / c') - xiStar := by
        dsimp [s]; rw [mul_div_cancel₀ _ hε_pos.ne']
      linarith
    have hsq_lt : tipBReal c' a ^ 2 < 3 * t / c' := by
      unfold tipTReal at ht
      have h3 : c' * tipBReal c' a ^ 2 < 3 * t := by
        rw [mem_Ioi, div_lt_iff₀ (by norm_num : (0 : ℝ) < 3)] at ht; linarith
      rw [lt_div_iff₀ hc']; linarith
    have hb_lt : tipBReal c' a < Real.sqrt (3 * t / c') := by
      rw [← Real.sqrt_sq hba]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hsq_lt
    have hs_gt : a < s := by
      rw [← hbs] at hb_lt
      unfold tipBReal at hb_lt
      have : tipEps c' * a < tipEps c' * s := by linarith
      exact lt_of_mul_lt_mul_left this hε_pos.le
    refine ⟨s, hs_gt, ?_⟩
    unfold tipTReal
    rw [hbs, Real.sq_sqrt (by positivity)]
    field_simp [hc'.ne']

/-- Exact domain `L¹` integrability and norm `= 1` for `tipRescale c' test` on
`Ioi (tipSMin c')`. -/
lemma tipRescale_integrableOn_domain {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    IntegrableOn (fun s : ℝ => tipRescale c' test (s : ℂ)) (Ioi (tipSMin c')) := by
  have him : tipTReal c' '' Ioi (tipSMin c') = Ioi 0 := by
    have ht0 : tipTReal c' (tipSMin c') = 0 := by
      unfold tipTReal tipBReal
      rw [tipSMin_eq_neg_div_tipEps hc']
      field_simp [(tipEps_pos hc').ne']
      ring
    rw [tipTReal_image_Ioi hc' le_rfl, ht0]
  have hint_real : IntegrableOn (fun t : ℝ => test.g t * test.V t * test.M⁻¹) (Ioi 0) :=
    test.hVac_int.mul_const test.M⁻¹
  have hcomp := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    (tipTReal_injOn hc') (fun t => test.g t * test.V t * test.M⁻¹)).mp
    (by rwa [him])
  refine hcomp.ofReal.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s :=
    mul_nonneg (mul_nonneg (tipEps_pos hc').le (by positivity))
      ((tipBReal_pos_iff hc').mpr hs).le
  have hscalar : tipEps c' * (2 * c' / 3) * tipBReal c' s *
      test.V (tipTReal c' s) * test.g (tipTReal c' s) / test.M =
      |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        (test.g (tipTReal c' s) * test.V (tipTReal c' s) * test.M⁻¹) := by
    rw [smul_eq_mul, abs_of_nonneg hder_nn, div_eq_mul_inv]; ring
  rw [tipRescale_real_on_real]
  dsimp only
  rw [hscalar]
  rfl

theorem tipRescale_norm_integral {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    ∫ s in Ioi (tipSMin c'), ‖tipRescale c' test (s : ℂ)‖ = 1 := by
  have him : tipTReal c' '' Ioi (tipSMin c') = Ioi 0 := by
    have ht0 : tipTReal c' (tipSMin c') = 0 := by
      unfold tipTReal tipBReal
      rw [tipSMin_eq_neg_div_tipEps hc']
      field_simp [(tipEps_pos hc').ne']; ring
    rw [tipTReal_image_Ioi hc' le_rfl, ht0]
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    (tipTReal_injOn hc') (fun t => |test.g t| * test.V t / test.M)
  rw [him] at hcov
  have heq : EqOn (fun s : ℝ => ‖tipRescale c' test (s : ℂ)‖)
      (fun s => |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        (|test.g (tipTReal c' s)| * test.V (tipTReal c' s) / test.M))
      (Ioi (tipSMin c')) := fun s hs => by
    have hbs : 0 < tipBReal c' s := (tipBReal_pos_iff hc').mpr hs
    have hts : 0 < tipTReal c' s := by unfold tipTReal; positivity
    have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s :=
      mul_nonneg (mul_nonneg (tipEps_pos hc').le (by positivity)) hbs.le
    dsimp only
    rw [tipRescale_real_on_real, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul,
      abs_of_nonneg hder_nn, abs_div, abs_of_pos test.hM_pos, abs_mul, abs_mul,
      abs_of_nonneg hder_nn, abs_of_pos (test.hV_pos _ hts)]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, ← hcov, integral_div, test.hM_eq,
    div_self test.hM_pos.ne']

theorem tipRescale_integral_vac {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    ∫ s in Ioi (tipSMin c'), (tipRescale c' test (s : ℂ)).re =
      -(test.gVac / (2 * π * test.M)) := by
  have him : tipTReal c' '' Ioi (tipSMin c') = Ioi 0 := by
    have ht0 : tipTReal c' (tipSMin c') = 0 := by
      unfold tipTReal tipBReal
      rw [tipSMin_eq_neg_div_tipEps hc']
      field_simp [(tipEps_pos hc').ne']; ring
    rw [tipTReal_image_Ioi hc' le_rfl, ht0]
  have hcov := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun s _ => (tipTReal_deriv (c' := c') (s := s)).hasDerivWithinAt)
    (tipTReal_injOn hc') (fun t => test.g t * test.V t / test.M)
  rw [him] at hcov
  have heq : EqOn (fun s : ℝ => (tipRescale c' test (s : ℂ)).re)
      (fun s => |tipEps c' * (2 * c' / 3) * tipBReal c' s| •
        (test.g (tipTReal c' s) * test.V (tipTReal c' s) / test.M))
      (Ioi (tipSMin c')) := fun s hs => by
    have hbs : 0 < tipBReal c' s := (tipBReal_pos_iff hc').mpr hs
    have hder_nn : 0 ≤ tipEps c' * (2 * c' / 3) * tipBReal c' s :=
      mul_nonneg (mul_nonneg (tipEps_pos hc').le (by positivity)) hbs.le
    dsimp only
    rw [tipRescale_real_on_real, Complex.ofReal_re, smul_eq_mul, abs_of_nonneg hder_nn]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, ← hcov, integral_div, test.hVac_eq]
  field_simp [Real.pi_pos.ne', test.hM_pos.ne']

theorem tipRescale_nonneg_tail {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    ∀ s : ℝ, tipS₁ c' test ≤ s → 0 ≤ (tipRescale c' test (s : ℂ)).re := by
  intro s hs
  rw [tipRescale_real_on_real, Complex.ofReal_re]
  have hb₁ : 0 ≤ tipBReal c' (tipS₁ c' test) := by
    unfold tipBReal tipS₁
    have hε : tipEps c' ≠ 0 := (tipEps_pos hc').ne'
    calc 0 ≤ test.x₁ := test.hx₁_nonneg
      _ = xiStar + tipEps c' * ((test.x₁ - xiStar) / tipEps c') := by field_simp [hε]; ring
  have hbs : 0 ≤ tipBReal c' s := by
    have : tipBReal c' (tipS₁ c' test) ≤ tipBReal c' s := by
      unfold tipBReal; gcongr; exact (tipEps_pos hc').le
    linarith
  have hts₁ : test.t₁ ≤ tipTReal c' s := by
    have hx_le : test.x₁ ≤ tipBReal c' s := by
      calc test.x₁ = tipBReal c' (tipS₁ c' test) := by
            unfold tipBReal tipS₁; field_simp [(tipEps_pos hc').ne']; ring
        _ ≤ tipBReal c' s := by unfold tipBReal; gcongr; exact (tipEps_pos hc').le
    rw [test.ht₁_eq]
    unfold tipTReal
    have hsq : test.x₁ ^ 2 ≤ tipBReal c' s ^ 2 := by nlinarith [test.hx₁_nonneg]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hc'.le) (by norm_num)
  have hgnn : 0 ≤ test.g (tipTReal c' s) := test.hg_nonneg_tail _ hts₁
  have htnn : 0 ≤ tipTReal c' s := test.ht₁_nonneg hc'.le |>.trans hts₁
  have hVnn : 0 ≤ test.V (tipTReal c' s) := test.hV_nonneg _ htnn
  have hε_nn : 0 ≤ tipEps c' := (tipEps_pos hc').le
  exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hε_nn (by positivity)) hbs) hVnn) hgnn)
    test.hM_pos.le

theorem tipRescale_half_neg_mass {inp : StripBootstrapInputs} {c' : ℝ} (hc' : 0 < c')
    (test : BlowupTest inp c') :
    (1 / 2 : ℝ) ≤ ∫ s in Ioc (tipSMin c') (tipS₁ c' test),
      max 0 (-(tipRescale c' test (s : ℂ)).re) := by
  let f : ℝ → ℝ := fun s => (tipRescale c' test (s : ℂ)).re
  let fneg : ℝ → ℝ := fun s => max 0 (-f s)
  have hf_int : IntegrableOn f (Ioi (tipSMin c')) :=
    (tipRescale_integrableOn_domain hc' test).re
  have hfnorm_int : IntegrableOn (fun s : ℝ => ‖tipRescale c' test (s : ℂ)‖) (Ioi (tipSMin c')) :=
    (tipRescale_integrableOn_domain hc' test).norm
  have hfneg_int : IntegrableOn fneg (Ioi (tipSMin c')) := by
    have heq : fneg = fun s => (|f s| - f s) / 2 := by
      funext s
      dsimp [fneg]
      rcases le_total (f s) 0 with h | h
      · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    rw [heq]
    have habs : IntegrableOn (fun s => |f s|) (Ioi (tipSMin c')) := by
      refine hfnorm_int.congr_fun (fun s _ => ?_) measurableSet_Ioi
      dsimp [f]; rw [tipRescale_real_on_real, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
    exact (habs.sub hf_int).div_const 2
  have hfneg_total : (1 / 2 : ℝ) ≤ ∫ s in Ioi (tipSMin c'), fneg s := by
    have heq : fneg = fun s : ℝ => (‖tipRescale c' test (s : ℂ)‖ - f s) / 2 := by
      funext s
      dsimp [fneg, f]
      rw [tipRescale_real_on_real, Complex.norm_real, Complex.ofReal_re, Real.norm_eq_abs]
      rcases le_total ((tipEps c' * (2 * c' / 3) * tipBReal c' s *
          test.V (tipTReal c' s) * test.g (tipTReal c' s) / test.M : ℝ)) 0 with h | h
      · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]; ring
      · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]; ring
    rw [heq, integral_div, integral_sub hfnorm_int hf_int,
      tipRescale_norm_integral hc' test, tipRescale_integral_vac hc' test]
    have hgvac : 0 ≤ test.gVac / (2 * π * test.M) :=
      div_nonneg test.hgVac_nonneg (by positivity [Real.pi_pos, test.hM_pos])
    linarith
  have hsMin_le : tipSMin c' ≤ tipS₁ c' test := by
    rw [tipSMin_eq_neg_div_tipEps hc']
    unfold tipS₁
    have hε := tipEps_pos hc'
    exact div_le_div_of_nonneg_right (by linarith [test.hx₁_nonneg]) hε.le
  have htail_zero : ∫ s in Ioi (tipS₁ c' test), fneg s = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    dsimp [fneg, f]
    exact max_eq_left (neg_nonpos.mpr (tipRescale_nonneg_tail hc' test s (mem_Ioi.mp hs).le))
  have hunion : (∫ s in Ioc (tipSMin c') (tipS₁ c' test), fneg s) +
      (∫ s in Ioi (tipS₁ c' test), fneg s) = ∫ s in Ioi (tipSMin c'), fneg s := by
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hfneg_int.mono_set Ioc_subset_Ioi_self) (hfneg_int.mono_set (Ioi_subset_Ioi hsMin_le)),
      Ioc_union_Ioi_eq_Ioi hsMin_le]
  linarith

/-! ### Section 4: Lemma T5 (complex majorant at the tip) -/

/-- **Lemma T5** (`blowup_limit.tex`, Lemma `bl:T5`): complex majorant for `tipRescale` in the
slit tip neighborhood `ε |ζ| ≤ ρ_T5`, `ζ ∉ [0, ∞)` and `c' ≥ c₀`.
*(Note: `blowup_limit.tex` mentions constants `C₁,…,C₄` in prose when only `C₁, C₂, C₃` appear in
the formula; formalised here with the three constants `C₁, C₂, C₃`.)* -/
theorem lemma_T5 (hI0 : BesselI0Asymptotic) (inp : StripBootstrapInputs) :
    ∃ ρ_T5 C₁ C₂ C₃ c₀ : ℝ,
      0 < ρ_T5 ∧ 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 39 ≤ c₀ ∧
      ∀ {c' : ℝ} (test : BlowupTest inp c') {ζ : ℂ},
        c₀ ≤ c' → ¬ (ζ.im = 0 ∧ 0 ≤ ζ.re) →
        tipEps c' * ‖ζ‖ ≤ ρ_T5 →
        tipRescale c' test ζ ≠ 0 →
          Real.log ‖tipRescale c' test ζ‖ ≤
            tipH ζ - Real.log (tipDist ζ) +
              C₁ + C₂ * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) +
              C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' := by
  obtain ⟨ρ₁, C_T1, ψ, hρ₁_pos, hCT1_nn, _, _, _, _, hT1⟩ := lemma_T1
  obtain ⟨ρ₂, C_T2, hρ₂_pos, hCT2_nn, hT2⟩ := lemma_T2 inp.pot
  obtain ⟨ρ₃, C_W, hρ₃_pos, hCW_nn, hT3_W⟩ := lemma_T3_W_bound hI0
  let ρ_T5 : ℝ := min ρ₁ (min ρ₂ (min ρ₃ (min (1 / (4 * (C_T1 + 1) ^ 2))
    (min (1 / (6 * (C_W + 1))) 0.25))))
  have hρ_pos : 0 < ρ_T5 := by positivity
  let c₀ : ℝ := max inp.c_PJ_complex ((6 * (C_W + 1)) ^ (3 / 2 : ℝ))
  have hc₀_39 : 39 ≤ c₀ := le_trans inp.hc_PJ_complex (le_max_left _ _)
  let C₁ : ℝ := Real.log (3 * kappa0 / 2) + Real.log (2 * slitQ) +
    slitEntropyComplexConst + inp.C_PJ_complex
  let C₂ : ℝ := C_T2
  let C₃ : ℝ := (5 / 2 : ℝ) * (2 / (0.3 * π)) * (3 / (2 * √slitQ))
  have hC₃_nn : 0 ≤ C₃ := by positivity [slitQ_pos]
  refine ⟨ρ_T5, C₁, C₂, C₃, c₀, hρ_pos, hCT2_nn, hC₃_nn, hc₀_39,
    fun {c'} test {ζ} hc' hζ hεζ hΦ_ne => ?_⟩
  have hc'_39 : 39 ≤ c' := hc₀_39.trans hc'
  have hc'_pos : 0 < c' := by linarith
  have hc'_gt1 : 1 < c' := by linarith
  have hε_pos : 0 < tipEps c' := tipEps_pos hc'_pos
  have hεζ_1 : tipEps c' * ‖ζ‖ ≤ ρ₁ := hεζ.trans (min_le_left _ _)
  have hεζ_2 : tipEps c' * ‖ζ‖ ≤ ρ₂ := hεζ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεζ_3 : tipEps c' * ‖ζ‖ ≤ ρ₃ :=
    hεζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεζ_T1 : tipEps c' * ‖ζ‖ ≤ 1 / (4 * (C_T1 + 1) ^ 2) :=
    hεζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hεζ_W : tipEps c' * ‖ζ‖ ≤ 1 / (6 * (C_W + 1)) :=
    hεζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hεζ_25 : tipEps c' * ‖ζ‖ ≤ 0.25 :=
    hεζ.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  set b := bScale c' ζ
  have hW_ne : W_C c' b ≠ 0 := fun h => hΦ_ne (by unfold tipRescale; rw [h]; ring)
  have hG_ne : test.G b ≠ 0 := fun h => hΦ_ne (by unfold tipRescale; rw [h]; ring)
  have hb_im : |b.im| < 1 / 2 := by
    have him : b.im = tipEps c' * ζ.im := by unfold b bScale; simp [Complex.add_im, Complex.mul_im]
    rw [him, abs_mul, abs_of_pos hε_pos]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm ζ) hε_pos.le).trans_lt
      (hεζ_25.trans_lt (by norm_num))
  -- Step 1: Lemma T1 gives `z_b` with `slitBoundaryMapC z_b = b`, `‖z_b - σ_*‖ ≤ 0.1`, etc.
  obtain ⟨_, hz_im_pos, hz_cl, hz_map, _, hz_im_bd, _, hz_prod_bd⟩ := hT1 hc'_pos hζ hεζ_1
  set v : ℂ := I * ((√(tipEps c') : ℝ) : ℂ) * (-ζ) ^ (1 / 2 : ℂ)
  set z_b : ℂ := (sigmaStar : ℂ) + ψ v
  have hCT1_sqrt : C_T1 * Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / 2 := by
    have hsqrt_le : Real.sqrt (tipEps c' * ‖ζ‖) ≤ 1 / (2 * (C_T1 + 1)) := by
      have h1 : 1 / (4 * (C_T1 + 1) ^ 2) = (1 / (2 * (C_T1 + 1))) ^ 2 := by
        field_simp [show C_T1 + 1 ≠ 0 by positivity]; ring
      calc Real.sqrt (tipEps c' * ‖ζ‖) ≤ Real.sqrt ((1 / (2 * (C_T1 + 1))) ^ 2) :=
            Real.sqrt_le_sqrt (h1 ▸ hεζ_T1)
        _ = 1 / (2 * (C_T1 + 1)) := Real.sqrt_sq (by positivity)
    calc C_T1 * Real.sqrt (tipEps c' * ‖ζ‖)
        ≤ C_T1 * (1 / (2 * (C_T1 + 1))) := mul_le_mul_of_nonneg_left hsqrt_le hCT1_nn
      _ = (C_T1 / (C_T1 + 1)) * (1 / 2) := by
          field_simp [show C_T1 + 1 ≠ 0 by positivity]
      _ ≤ 1 * (1 / 2) := by
          gcongr; exact (div_le_one (by linarith)).mpr (by linarith)
      _ = 1 / 2 := one_mul _
  -- Step 2: Lower bound `y * |z_b - σ_*|` and upper bound `y`.
  have hd_pos : 0 < tipDist ζ := tipDist_pos_of_not_nonneg hζ
  have hprod_lb : (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) ≤
      z_b.im * ‖z_b - (sigmaStar : ℂ)‖ := by
    have hbase_nn : 0 ≤ (tipEps c' / slitQ) * tipDist ζ :=
      mul_nonneg (div_nonneg hε_pos.le slitQ_pos.le) hd_pos.le
    have h1 := (abs_le.mp hz_prod_bd).1
    have h2 : C_T1 * Real.sqrt (tipEps c' * ‖ζ‖) * ((tipEps c' / slitQ) * tipDist ζ) ≤
        (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) :=
      mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    linarith
  have hy_ub : z_b.im ≤ (3 / (2 * √slitQ)) * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) := by
    have hsqrt_re_nn : 0 ≤ ((-ζ) ^ (1 / 2 : ℂ)).re := by
      by_cases h0 : -ζ = 0
      · rw [h0]; simp
      · rw [Complex.cpow_def_of_ne_zero h0, Complex.exp_re]
        refine mul_nonneg (Real.exp_pos _).le (Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ ?_)
        · have := Complex.neg_pi_lt_arg (-ζ)
          have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = (-ζ).arg / 2 := by
            simp [Complex.log_im]; ring
          rw [him]; linarith
        · have := Complex.arg_le_pi (-ζ)
          have him : (Complex.log (-ζ) * (1 / 2 : ℂ)).im = (-ζ).arg / 2 := by
            simp [Complex.log_im]; ring
          rw [him]; linarith
    have hbase_nn : 0 ≤ Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re :=
      mul_nonneg (Real.sqrt_nonneg _) hsqrt_re_nn
    have h1 := (abs_le.mp hz_im_bd).2
    have h2 : C_T1 * Real.sqrt (tipEps c' * ‖ζ‖) *
        (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) ≤
        (1 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) :=
      mul_le_mul_of_nonneg_right hCT1_sqrt hbase_nn
    have hre_le : ((-ζ) ^ (1 / 2 : ℂ)).re ≤ Real.sqrt ‖ζ‖ := by
      have hnorm : ‖(-ζ) ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖ζ‖ := by
        simpa [norm_neg] using FormalResearch.Special.norm_cpow_half (-ζ)
      exact (Complex.re_le_norm _).trans_eq hnorm
    calc z_b.im ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * ((-ζ) ^ (1 / 2 : ℂ)).re) := by
          linarith
      _ ≤ (3 / 2 : ℝ) * (Real.sqrt (tipEps c' / slitQ) * Real.sqrt ‖ζ‖) := by gcongr
      _ = (3 / (2 * √slitQ)) * Real.sqrt (tipEps c' * ‖ζ‖) := by
          rw [Real.sqrt_div hε_pos.le, Real.sqrt_mul hε_pos.le]; ring
      _ = (3 / (2 * √slitQ)) * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) := by
          rw [← Real.sqrt_eq_rpow]
  -- Step 3: Strip Poisson--Jensen + Lemma T4 (`z_b.re + z_b.im * I = z_b`).
  have hz_eta : (z_b.re : ℂ) + (z_b.im : ℂ) * I = z_b := Complex.re_add_im z_b
  have hT4 := lemma_T4 hz_im_pos (by rw [hz_eta]; exact hz_cl)
  have hc'_PJ : inp.c_PJ_complex ≤ c' := (le_max_left _ _).trans hc'
  have hG_PJ := test.hPJ_complex hc'_PJ z_b hz_im_pos hz_cl (by simpa [hz_map] using hb_im)
    (by simpa [hz_map] using hG_ne)
  rw [hz_map] at hG_PJ
  have hlogc'_nn : 0 ≤ Real.log c' := Real.log_nonneg hc'_gt1.le
  have hm_term : (5 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c' ≤
      C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' := by
    have h1 : 1 - slitMass z_b.re z_b.im ≤
        (2 / (0.3 * π)) * ((3 / (2 * √slitQ)) * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ)) :=
      hT4.1.trans (mul_le_mul_of_nonneg_left hy_ub (by positivity))
    calc (5 / 2 : ℝ) * (1 - slitMass z_b.re z_b.im) * Real.log c'
        ≤ (5 / 2 : ℝ) * ((2 / (0.3 * π)) * ((3 / (2 * √slitQ)) *
            (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ))) * Real.log c' := by gcongr
      _ = C₃ * (tipEps c' * ‖ζ‖) ^ (1 / 2 : ℝ) * Real.log c' := by dsimp [C₃]; ring
  have hS_term : slitEntropy z_b.re z_b.im ≤
      (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) +
        slitEntropyComplexConst := by
    have hz_ne_sigma : ‖z_b - (sigmaStar : ℂ)‖ ≠ 0 := by
      intro h0
      have : z_b.im * ‖z_b - (sigmaStar : ℂ)‖ = 0 := by rw [h0, mul_zero]
      have hpos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by
        positivity [slitQ_pos]
      linarith
    have hz_norm_pos : 0 < ‖z_b - (sigmaStar : ℂ)‖ := lt_of_le_of_ne (norm_nonneg _) hz_ne_sigma.symm
    have hprod_pos : 0 < (1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ) := by
      positivity [slitQ_pos]
    have hlog_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) ≤
        (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
      have hmul_inv : Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) =
          Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) := by
        rw [← Real.log_mul (one_div_pos.mpr hz_im_pos).ne' (one_div_pos.mpr hz_norm_pos).ne']
        ring_nf
      have hinv_le : 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖) ≤
          (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
        calc 1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)
            ≤ 1 / ((1 / 2 : ℝ) * ((tipEps c' / slitQ) * tipDist ζ)) :=
              one_div_le_one_div_of_le hprod_pos hprod_lb
          _ = (tipEps c')⁻¹ * (2 * slitQ) / tipDist ζ := by
              field_simp [hε_pos.ne', slitQ_pos.ne', hd_pos.ne']
          _ = (c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ := by
              unfold tipEps; rw [← Real.rpow_neg hc'_pos.le, neg_neg]
      have hlog_step : Real.log (1 / (z_b.im * ‖z_b - (sigmaStar : ℂ)‖)) ≤
          Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) :=
        Real.log_le_log (one_div_pos.mpr (mul_pos hz_im_pos hz_norm_pos)) hinv_le
      have hlog_rhs : Real.log ((c' ^ (2 / 3 : ℝ)) * (2 * slitQ) / tipDist ζ) =
          (2 / 3 : ℝ) * Real.log c' + Real.log (2 * slitQ) - Real.log (tipDist ζ) := by
        rw [Real.log_div (by positivity [slitQ_pos]) hd_pos.ne',
          Real.log_mul (Real.rpow_pos_of_pos hc'_pos _).ne' (by positivity [slitQ_pos]),
          Real.log_rpow hc'_pos]
      linarith
    have hS' : slitEntropy z_b.re z_b.im ≤
        Real.log (1 / z_b.im) + Real.log (1 / ‖z_b - (sigmaStar : ℂ)‖) +
          slitEntropyComplexConst := by
      simpa [hz_eta] using hT4.2
    linarith
  -- Step 4: Bound `log ‖W_C c' b‖` from Lemma T3.
  have hW_log : Real.log ‖W_C c' b‖ ≤
      Real.log (3 * kappa0 / 2) - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
    have hTW := hT3_W hc'_39 hεζ_3
    dsimp only at hTW
    have hε_le : tipEps c' ≤ 1 / (6 * (C_W + 1)) := by
      have h6_pos : (0 : ℝ) < 6 * (C_W + 1) := by positivity
      have hpow_le : (6 * (C_W + 1)) ^ (3 / 2 : ℝ) ≤ c' := (le_max_right _ _).trans hc'
      have h23 : 6 * (C_W + 1) ≤ c' ^ (2 / 3 : ℝ) := by
        calc 6 * (C_W + 1) = ((6 * (C_W + 1)) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ) := by
              rw [← Real.rpow_mul h6_pos.le]; norm_num
          _ ≤ c' ^ (2 / 3 : ℝ) := Real.rpow_le_rpow (by positivity) hpow_le (by norm_num)
      unfold tipEps
      rw [Real.rpow_neg hc'_pos.le, ← one_div]
      exact one_div_le_one_div_of_le h6_pos h23
    have hinv_le : 1 / c' ≤ 1 / (6 * (C_W + 1)) := by
      have h6_pos : (0 : ℝ) < 6 * (C_W + 1) := by positivity
      have h6_le_c : 6 * (C_W + 1) ≤ c' := by
        have h1 : (1 : ℝ) ≤ 6 * (C_W + 1) := by linarith
        have h2 : 6 * (C_W + 1) ≤ (6 * (C_W + 1)) ^ (3 / 2 : ℝ) := by
          calc 6 * (C_W + 1) = (6 * (C_W + 1)) ^ (1 : ℝ) := (Real.rpow_one _).symm
            _ ≤ (6 * (C_W + 1)) ^ (3 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
        exact h2.trans ((le_max_right _ _).trans hc')
      exact one_div_le_one_div_of_le h6_pos h6_le_c
    have hrel_half : C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c') ≤ 1 / 2 := by
      have hsum : tipEps c' * (1 + ‖ζ‖) + 1 / c' ≤ 3 * (1 / (6 * (C_W + 1))) := by
        have : tipEps c' * (1 + ‖ζ‖) = tipEps c' + tipEps c' * ‖ζ‖ := by ring
        linarith
      calc C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c')
          ≤ C_W * (3 * (1 / (6 * (C_W + 1)))) := mul_le_mul_of_nonneg_left hsum hCW_nn
        _ = (C_W / (C_W + 1)) * (1 / 2) := by
            field_simp [show C_W + 1 ≠ 0 by positivity]; ring
        _ ≤ 1 * (1 / 2) := by gcongr; exact (div_le_one (by linarith)).mpr (by linarith)
        _ = 1 / 2 := one_mul _
    have hkap_norm : ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ =
        kappa0 * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
      have hkap_pos : 0 < kappaC c' := mul_pos (Real.rpow_pos_of_pos hc'_pos _) kappa0_pos
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkap_pos,
        Complex.norm_exp, Complex.re_ofReal_mul]
      unfold kappaC; ring
    have hW_ub : ‖W_C c' b‖ ≤ (3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
      have hdiff : ‖W_C c' b‖ ≤
          (1 + C_W * (tipEps c' * (1 + ‖ζ‖) + 1 / c')) *
            ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ := by
        have htri := norm_sub_norm_le (W_C c' b) ((kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b))
        linarith [hTW]
      calc ‖W_C c' b‖
          ≤ (3 / 2 : ℝ) * ‖(kappaC c' : ℂ) * Complex.exp ((c' : ℂ) * tipL b)‖ :=
            hdiff.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
        _ = (3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re) := by
            rw [hkap_norm]; ring
    have hW_log_step : Real.log ‖W_C c' b‖ ≤
        Real.log ((3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) :=
      Real.log_le_log (norm_pos_iff.mpr hW_ne) hW_ub
    have hlog_eq : Real.log ((3 * kappa0 / 2) * c' ^ (-(1 / 6 : ℝ)) * Real.exp (c' * (tipL b).re)) =
        Real.log (3 * kappa0 / 2) - (1 / 6 : ℝ) * Real.log c' + c' * (tipL b).re := by
      have hkap0 : 0 < 3 * kappa0 / 2 := by positivity [kappa0_pos]
      rw [Real.log_mul (mul_pos hkap0 (Real.rpow_pos_of_pos hc'_pos _)).ne' (Real.exp_pos _).ne',
        Real.log_mul hkap0.ne' (Real.rpow_pos_of_pos hc'_pos _).ne',
        Real.log_rpow hc'_pos, Real.log_exp]
      ring
    linarith
  -- Step 5: Lemma T2 bounds `c' * (U b + Re L b) ≤ H(ζ) + C_T2 * ε * ‖ζ‖^(5/2)`.
  have hT2_bd := (hT2 hc'_pos hζ hεζ_2).2
  have hpot_bd : c' * (inp.pot.U b + (tipL b).re) ≤
      tipH ζ + C_T2 * tipEps c' * ‖ζ‖ ^ (5 / 2 : ℝ) := by
    have := (abs_le.mp hT2_bd).2
    linarith
  -- Step 6: Combine all pieces!
  have hΦ_log : Real.log ‖tipRescale c' test ζ‖ =
      Real.log ‖W_C c' b‖ + Real.log ‖test.G b‖ - Real.log test.M := by
    unfold tipRescale
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos test.hM_pos,
      Real.log_div (mul_pos (norm_pos_iff.mpr hW_ne) (norm_pos_iff.mpr hG_ne)).ne'
        test.hM_pos.ne',
      Real.log_mul (norm_pos_iff.mpr hW_ne).ne' (norm_pos_iff.mpr hG_ne).ne']
  dsimp [C₁, C₂]
  linarith

end FormalResearch.ModularBootstrap

section AxiomChecks
open FormalResearch.ModularBootstrap

/-- info: 'FormalResearch.ModularBootstrap.lemma_T4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T4

/-- info: 'FormalResearch.ModularBootstrap.stripBootstrapInputs_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripBootstrapInputs_nonvacuous

/-- info: 'FormalResearch.ModularBootstrap.BlowupTest.halfMass_derived' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms BlowupTest.halfMass_derived

/-- info: 'FormalResearch.ModularBootstrap.tipRescale_holo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipRescale_holo

/-- info: 'FormalResearch.ModularBootstrap.tipRescale_real_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipRescale_real_symm

/-- info: 'FormalResearch.ModularBootstrap.tipRescale_norm_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipRescale_norm_integral

/-- info: 'FormalResearch.ModularBootstrap.tipRescale_integral_vac' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipRescale_integral_vac

/-- info: 'FormalResearch.ModularBootstrap.tipRescale_half_neg_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tipRescale_half_neg_mass

/-- info: 'FormalResearch.ModularBootstrap.lemma_T5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemma_T5

end AxiomChecks

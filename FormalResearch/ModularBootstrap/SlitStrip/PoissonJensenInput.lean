module

public import FormalResearch.ModularBootstrap.SlitStrip.Majorant
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The geometric inputs of Theorem A, discharged

`EntropyAndDeficit.theorem_A` takes a `PoissonJensenInput` (real-slice data `rs`, a majorant `U` with
`g_deficit`, and constants) and a `FixedGapInput`.  This file builds the `PoissonJensenInput` from the
actual slit-strip geometry (`CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G, `vlo:Gap`):

* `rs = realSliceData`: preimage coordinates of `ξ_* - δ` under the conformal map `confB`
  (`ConformalMap.lean`, `RealSlice.lean`);
* `U = majorantReal`: the harmonic majorant on the real axis, with `g_deficit` *proved*
  (`majorantReal_g_deficit`, `Majorant.lean`).

so that `theorem_A_geometry` has no geometric hypothesis left: its only inputs are the constants
`c_PJ, C_PJ, C_K`, the `FixedGapInput` (Bessel/fixed-gap estimates) and, inside each
`WeaklyFeasibleTest`, the Poisson--Jensen inequality `hPJ` itself.

The one geometric statement that is *not* proved is the harmonic-measure identification `h = U`
(`HarmonicMajorantIdentification`): it is what justifies that `hPJ` is the right inequality for this
`U` (the paper derives `hPJ` from Poisson--Jensen using `h = U`), but no declaration of
`EntropyAndDeficit` or of this development needs it as a hypothesis.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap

/-- **The real-axis harmonic-measure identification `h = U` (Lemma G, `vlo:Gap`)**, stated for
`b = x ∈ [0, ξ_*)`, with `z_b = x_UHP + i y_UHP` the upper-half-plane preimage of `b`
(`realSliceData`, `confB_slice`):
`U(x) = h(x) = -∫_slits L dω_b = -∫_{σ ∈ (-1,0) ∪ (1,∞)} L(𝓑(σ)) P_{z_b}(σ) dσ`,
where `P_{z_b}` is the upper-half-plane Poisson kernel (`poissonKernel`) and `𝓑(σ) = slitBoundaryMap σ`
is the real boundary value of the conformal map on the slits (`confB_real_re`).

**Not proved.** The paper's proof is the maximum principle for harmonic functions of at most linear
growth on the slit strip (Phragmén–Lindelöf with the comparison function
`ε cosh(λ Re b) cos(λ Im b)`), applied to the difference of `h` (a Poisson integral) and the explicit
`U = U_0 + (4π/3) Im ∫_0^b p`; Mathlib has no Poisson-integral Dirichlet theory on the half-plane.
As a numerical sanity check (scratch `mpmath` quadrature, not part of the tree) both sides agree to
20 digits at `x = 0, 0.1, 0.2, 0.25`.  Nothing in `theorem_A_geometry` uses this statement; it is the bridge between `U` and the
harmonic measure that the Poisson--Jensen inequality `hPJ` is proved with. -/
def HarmonicMajorantIdentification : Prop :=
  ∀ x ∈ Ico (0 : ℝ) xiStar,
    majorantReal x =
      -∫ σ in slitPreimage,
        slitL (slitBoundaryMap σ) *
          poissonKernel (realSliceData.xUHP (xiStar - x)) (realSliceData.yUHP (xiStar - x)) σ

/-- **The `PoissonJensenInput` of the slit-strip geometry**: real-slice data from the conformal map
and the explicit harmonic majorant, with only the free constants `c_PJ, C_PJ, C_K` left. -/
noncomputable def slitStripPoissonJensenInput (c_PJ C_PJ C_K : ℝ) (hc_PJ : 1 ≤ c_PJ)
    (hC_K : 0 < C_K) : PoissonJensenInput where
  rs := realSliceData
  c_PJ := c_PJ
  C_PJ := C_PJ
  C_K := C_K
  U := majorantReal
  hc_PJ := hc_PJ
  hC_K := hC_K
  g_deficit := fun _ hx => majorantReal_g_deficit hx

/-- **Theorem A with the geometry proved** (`lower_o1_two_edge.tex`, Lemma G + Theorem A): the
statement of `theorem_A` for the `PoissonJensenInput` built from the conformal map; the remaining
inputs are the constants, the `FixedGapInput`, and the Poisson--Jensen inequality `hPJ` carried by each
`WeaklyFeasibleTest`. -/
theorem theorem_A_geometry (c_PJ C_PJ C_K : ℝ) (hc_PJ : 1 ≤ c_PJ) (hC_K : 0 < C_K)
    (fg : FixedGapInput) :
    ∃ C_A c_A : ℝ, 0 < C_A ∧ 1 ≤ c_A ∧
      ∀ {c' : ℝ}, c_A ≤ c' →
        ∀ test : WeaklyFeasibleTest (slitStripPoissonJensenInput c_PJ C_PJ C_K hc_PJ hC_K) fg c',
          xiBar * c' - C_A * c' ^ ((1 : ℝ) / 3) ≤ test.t₁ :=
  theorem_A (slitStripPoissonJensenInput c_PJ C_PJ C_K hc_PJ hC_K) fg

/-! ### Non-vacuity of `HarmonicMajorantIdentification`: its integrand is integrable

If the integrand were not integrable, the Bochner integral in `HarmonicMajorantIdentification`
would be the junk value `0` and the statement would not mean what the paper says.  We prove it is
integrable on the slit preimage (logarithmic singularities at `σ = 0, ±1`, logarithmic growth
against the `σ⁻²` decay of the Poisson kernel at infinity), and that the right-hand side is `≤ 0`. -/

private lemma poissonKernel_le_bracket {x y : ℝ} (hy : 0 < y) (u : ℝ) :
    poissonKernel x y u ≤ (y * ((1 + 2 * x ^ 2) / y ^ 2 + 2) / π) * (1 + u ^ 2)⁻¹ := by
  unfold poissonKernel
  have hD : 0 < (u - x) ^ 2 + y ^ 2 := by positivity
  have hpi := Real.pi_pos
  have hM : 1 + u ^ 2 ≤ ((1 + 2 * x ^ 2) / y ^ 2 + 2) * ((u - x) ^ 2 + y ^ 2) := by
    have h1 : (1 + 2 * x ^ 2) ≤ (1 + 2 * x ^ 2) / y ^ 2 * ((u - x) ^ 2 + y ^ 2) := by
      calc 1 + 2 * x ^ 2 = (1 + 2 * x ^ 2) / y ^ 2 * y ^ 2 := by field_simp
        _ ≤ _ := by gcongr; nlinarith [sq_nonneg (u - x)]
    nlinarith [sq_nonneg (u - 2 * x), sq_nonneg (u - x)]
  rw [div_le_iff₀ (by positivity)]
  have : (y * ((1 + 2 * x ^ 2) / y ^ 2 + 2) / π * (1 + u ^ 2)⁻¹) * (π * ((u - x) ^ 2 + y ^ 2)) =
      y * (((1 + 2 * x ^ 2) / y ^ 2 + 2) * ((u - x) ^ 2 + y ^ 2)) / (1 + u ^ 2) := by
    field_simp
  rw [this, le_div_iff₀ (by positivity)]
  nlinarith

private lemma integrable_abs_log_mul_poisson (x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) := by
  set C₀ : ℝ := y * ((1 + 2 * x ^ 2) / y ^ 2 + 2) / π with hC₀
  have hC₀0 : 0 ≤ C₀ := by rw [hC₀]; positivity
  have hmeas : AEStronglyMeasurable (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) volume :=
    ((continuous_poissonKernel x hy).measurable.mul
      (Real.measurable_log.comp measurable_abs).abs).aestronglyMeasurable.congr
      (Eventually.of_forall fun u => mul_comm _ _)
  -- the bracket majorant
  have hbr : Integrable (fun u : ℝ => (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) := by
    refine integrable_rpow_neg_one_add_norm_sq (E := ℝ) (r := 3 / 2) ?_
    simp; norm_num
  -- compact part
  have hK : IntegrableOn (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) (Icc (-1) 1) := by
    have hlog : IntervalIntegrable (fun u : ℝ => |Real.log (|u|)|) volume (-1) 1 := by
      have := (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).abs
      have e : (fun u : ℝ => |Real.log (|u|)|) = fun u => |Real.log u| := by
        funext u; rw [Real.log_abs]
      rw [e]; exact this
    have h2 : IntegrableOn (fun u : ℝ => |Real.log (|u|)|) (Icc (-1) 1) := by
      rw [integrableOn_Icc_iff_integrableOn_Ioc]
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hlog
    exact h2.mul_continuousOn (continuous_poissonKernel x hy).continuousOn isCompact_Icc
  -- tails
  have hT : IntegrableOn (fun u : ℝ => |Real.log (|u|)| * poissonKernel x y u) (Icc (-1) 1)ᶜ := by
    refine Integrable.mono' (g := fun u => 2 * C₀ * (1 + ‖u‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2))
      (hbr.const_mul (2 * C₀)).integrableOn hmeas.restrict ?_
    refine (ae_restrict_iff' isClosed_Icc.measurableSet.compl).mpr (Eventually.of_forall fun u hu => ?_)
    have hu1 : 1 ≤ |u| := by
      simp only [mem_compl_iff, mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hpos : 0 < 1 + u ^ 2 := by positivity
    have hlog : |Real.log (|u|)| ≤ 2 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by
      rw [abs_of_nonneg (Real.log_nonneg hu1)]
      have h1 : Real.log |u| = Real.log (u ^ 2) / 2 := by
        rw [← sq_abs u, Real.log_pow]; push_cast; ring
      have h2 := Real.log_le_rpow_div (x := u ^ 2) (sq_nonneg u) (by norm_num : (0 : ℝ) < 1 / 4)
      have h3 : (u ^ 2) ^ (1 / 4 : ℝ) ≤ (1 + u ^ 2) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (sq_nonneg u) (by linarith) (by norm_num)
      rw [h1]
      have : Real.log (u ^ 2) ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by
        calc Real.log (u ^ 2) ≤ (u ^ 2) ^ (1 / 4 : ℝ) / (1 / 4) := h2
          _ = 4 * (u ^ 2) ^ (1 / 4 : ℝ) := by ring
          _ ≤ 4 * (1 + u ^ 2) ^ (1 / 4 : ℝ) := by gcongr
      linarith
    have hP := poissonKernel_le_bracket (x := x) hy u
    have hP0 := poissonKernel_nonneg (x := x) hy.le u
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hP0), Real.norm_eq_abs, sq_abs]
    calc |Real.log (|u|)| * poissonKernel x y u
        ≤ (2 * (1 + u ^ 2) ^ (1 / 4 : ℝ)) * (C₀ * (1 + u ^ 2)⁻¹) :=
          mul_le_mul hlog hP hP0 (by positivity)
      _ = 2 * C₀ * (1 + u ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
          rw [show (-(3 / 2 : ℝ) / 2) = 1 / 4 + (-1) by norm_num, Real.rpow_add hpos,
            Real.rpow_neg_one]
          ring
  have := hK.union hT
  rwa [union_compl_self, integrableOn_univ] at this

private lemma integrable_abs_log_sub_mul_poisson (a x : ℝ) {y : ℝ} (hy : 0 < y) :
    Integrable (fun σ : ℝ => |Real.log (|σ - a|)| * poissonKernel x y σ) := by
  have h := (integrable_abs_log_mul_poisson (x - a) hy).comp_sub_right a
  refine h.congr (Eventually.of_forall fun σ => ?_)
  simp only [poissonKernel]
  congr 3
  ring

private lemma abs_slitBoundaryMap_le (σ : ℝ) :
    |slitBoundaryMap σ| ≤
      (2 * π)⁻¹ * (|Real.log (|σ - 1|)| + |Real.log (|σ - 0|)| + |Real.log (|σ + 1|)|) := by
  unfold slitBoundaryMap
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have e1 : Real.log (|σ - 1|) = Real.log (1 - σ) := by
    rw [Real.log_abs, ← Real.log_neg_eq_log]; ring_nf
  have e2 : Real.log (|σ - 0|) = Real.log (-σ) := by
    rw [Real.log_abs, ← Real.log_neg_eq_log]; ring_nf
  have e3 : Real.log (|σ + 1|) = Real.log (1 + σ) := by
    rw [Real.log_abs, add_comm]
  rw [e1, e2, e3]
  by_cases h1 : 1 - σ = 0
  · rw [h1]; simp; positivity
  by_cases h2 : -σ = 0
  · rw [h2]; simp; positivity
  by_cases h3 : 1 + σ = 0
  · rw [h3]; simp; positivity
  rw [Real.log_div h1 (mul_ne_zero h2 h3), Real.log_mul h2 h3]
  calc |Real.log (1 - σ) - (Real.log (-σ) + Real.log (1 + σ))|
      ≤ |Real.log (1 - σ)| + |Real.log (-σ) + Real.log (1 + σ)| := abs_sub _ _
    _ ≤ |Real.log (1 - σ)| + (|Real.log (-σ)| + |Real.log (1 + σ)|) := by
        gcongr; exact abs_add_le _ _
    _ = _ := by ring

/-- **The integrand of `HarmonicMajorantIdentification` is integrable on the slit preimage**
(so the right-hand side is a genuine integral and not the junk value `0` of a non-integrable
integrand), for every `y > 0`. -/
theorem identification_integrand_integrable (x : ℝ) {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun σ : ℝ => slitL (slitBoundaryMap σ) * poissonKernel x y σ) slitPreimage := by
  have hsum : Integrable (fun σ : ℝ => (1 / 3 : ℝ) *
      (|Real.log (|σ - 1|)| * poissonKernel x y σ + |Real.log (|σ - 0|)| * poissonKernel x y σ +
        |Real.log (|σ - (-1)|)| * poissonKernel x y σ)) :=
    (((integrable_abs_log_sub_mul_poisson 1 x hy).add
      (integrable_abs_log_sub_mul_poisson 0 x hy)).add
      (integrable_abs_log_sub_mul_poisson (-1) x hy)).const_mul _
  refine (hsum.mono' ?_ (Eventually.of_forall fun σ => ?_)).integrableOn
  · have hB : Measurable slitBoundaryMap := by unfold slitBoundaryMap; fun_prop
    unfold slitL
    exact (((measurable_const.mul (hB.abs)).div_const 3).mul
      (continuous_poissonKernel x hy).measurable).aestronglyMeasurable
  · have hP := poissonKernel_nonneg (x := x) hy.le σ
    have hB := abs_slitBoundaryMap_le σ
    unfold slitL
    rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hP), sub_neg_eq_add]
    have hpi := Real.pi_pos
    have : 2 * π * |slitBoundaryMap σ| / 3 ≤ (1 / 3 : ℝ) *
        (|Real.log (|σ - 1|)| + |Real.log (|σ - 0|)| + |Real.log (|σ + 1|)|) := by
      have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 2 * π)
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
      linarith
    calc 2 * π * |slitBoundaryMap σ| / 3 * poissonKernel x y σ
        ≤ ((1 / 3 : ℝ) * (|Real.log (|σ - 1|)| + |Real.log (|σ - 0|)| + |Real.log (|σ + 1|)|)) *
            poissonKernel x y σ := by gcongr
      _ = _ := by ring

/-- The right-hand side of `HarmonicMajorantIdentification` is `≤ 0`, as `U ≤ 0` on `[0, ξ_*)`
requires; and the integral is over a genuinely integrable function. -/
theorem identification_rhs_nonpos (x : ℝ) {y : ℝ} (hy : 0 < y) :
    -∫ σ in slitPreimage, slitL (slitBoundaryMap σ) * poissonKernel x y σ ≤ 0 := by
  rw [neg_nonpos]
  refine setIntegral_nonneg (measurableSet_Ioo.union measurableSet_Ioi) fun σ _ => ?_
  have hP := poissonKernel_nonneg (x := x) hy.le σ
  unfold slitL
  positivity

/-! ### Axiom checks for the headline theorems -/

/-- info: 'FormalResearch.ModularBootstrap.theorem_A_geometry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.theorem_A_geometry

/-- info: 'FormalResearch.ModularBootstrap.identification_integrand_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.identification_integrand_integrable

/-- info: 'FormalResearch.ModularBootstrap.identification_rhs_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.identification_rhs_nonpos

end FormalResearch.ModularBootstrap

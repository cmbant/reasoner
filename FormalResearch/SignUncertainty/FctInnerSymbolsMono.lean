/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbolsA

/-!
# Lemma `fct:inner-symbols` (FCT.5b) (a), monomials: `𝒮[u^k] = i^k ∂_û^k 𝒮[1]` (proved), and the regularised ODE identity

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (a), last sentence.  For `ε > 0` the regularised integrals `𝒮_ε[u^k](û)` are differentiable in `û` with
`∂_û 𝒮_ε[u^k] = -i 𝒮_ε[u^{k+1}]` (`hasDerivAt_fctSEps`, differentiation under the integral, dominated by the Gaussian).  By `fctInnerSymbolsA` and `fctInnerSymbolsA_unif`
(Abel limits and the bound uniform in `ε ∈ (0,1)`, `|û| ≤ M`) the same identity passes to the limit `ε ↓ 0` (FTC in `û`), whence `∂_û g_k = -i g_{k+1}` for `g_k = 𝒮[u^k]`
(`hasDerivAt_gk`) and `g_k = i^k ∂^k g_0` (`iteratedDeriv_gk`).

Also proved here: the regularised ODE identity `½𝒮_ε[1] - iû 𝒮_ε[u] - (i/4) 𝒮_ε[u³] - 2ε 𝒮_ε[u²] = 0` (`fctSEps_ode`, from `∫_0^∞ ∂_u(u^{1/2} e^{w_ε}) = 0`),
the first step towards the third-order ODE `y'''= 4ûy' + 2y` for `𝒮[1]` (the closed form, `FctInnerSymbolsG0`, is still a named input).

Headline: `fctInnerSymbolsMonomial : FctInnerSymbolsMonomial`.

Class: proved.
-/
@[expose] public section
open Set Filter Topology MeasureTheory
open scoped Real ContDiff Interval

namespace FormalResearch.SignUncertainty
namespace FctSymA


/-- The monomial `u^k` is a symbol of order `k` with constant `k!` (and `C^{k+1}`). -/
lemma powSym (k : ℕ) : FctSymCls (k + 1) (k : ℝ) (Nat.factorial k : ℝ) (fun u => (u : ℂ) ^ k) := by
  have hc : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  have hpow : ContDiff ℝ ∞ (fun u : ℝ => (u : ℂ) ^ k) :=
    (Complex.ofRealCLM.contDiff (n := ∞)).pow k
  refine ⟨(hc.pow k).contDiffOn, fun r hr u hu => ?_⟩
  have hu0 : 0 ≤ u := hu
  have hf : ContDiffAt ℝ r (fun u : ℝ => (u : ℂ) ^ k) u := hpow.contDiffAt.of_le (by exact_mod_cast le_top)
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hf hu]
  have e : (fun u : ℝ => (u : ℂ) ^ k) = fun u => (((u ^ k : ℝ)) : ℂ) := by funext u; simp
  have hg : ContDiffAt ℝ r (fun u : ℝ => u ^ k) u := (contDiff_id.pow k).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [e, norm_iteratedDeriv_ofReal (fun u => u ^ k) r u hg, iteratedDeriv_pow]
  have hpos : 0 < (1 + u) ^ ((k : ℝ) - r) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rcases Nat.lt_or_ge k r with hlt | hge
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hlt]; simp; positivity
  · have hd : k.descFactorial r ≤ Nat.factorial k := by
      calc k.descFactorial r = 1 * k.descFactorial r := (one_mul _).symm
        _ ≤ (k - r).factorial * k.descFactorial r := Nat.mul_le_mul_right _ (Nat.factorial_pos _)
        _ = Nat.factorial k := Nat.factorial_mul_descFactorial hge
    have h1 : ((k.descFactorial r : ℕ) : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast hd
    have h2 : u ^ (k - r) ≤ (1 + u) ^ ((k : ℝ) - r) := by
      rw [show ((k : ℝ) - r) = ((k - r : ℕ) : ℝ) by rw [Nat.cast_sub hge], Real.rpow_natCast]
      exact pow_le_pow_left₀ hu0 (by linarith) _
    exact mul_le_mul h1 h2 (by positivity) (by positivity)


lemma hasDerivAt_fctW_û (w ε u : ℝ) : HasDerivAt (fun w' : ℝ => fctW w' ε u) (-(Complex.I * (u : ℂ))) w := by
  have h : HasDerivAt (fun w' : ℝ => ((w' * u + u ^ 3 / 12 : ℝ) : ℂ)) (u : ℂ) w := by
    have : HasDerivAt (fun w' : ℝ => w' * u + u ^ 3 / 12) u w := by
      simpa using ((hasDerivAt_id w).mul_const u).add_const (u ^ 3 / 12)
    exact this.ofReal_comp
  have := ((h.const_mul Complex.I).neg).sub_const (((ε * u ^ 2 : ℝ)) : ℂ)
  have e : (fun w' : ℝ => fctW w' ε u) = fun w' => -(Complex.I * ((w' * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ) := rfl
  rw [e]
  exact this

lemma integrableOn_hk {ε : ℝ} (hε : 0 < ε) (û : ℝ) (k : ℕ) :
    IntegrableOn (fun u : ℝ => fctRho u * Complex.exp (fctW û ε u) * (u : ℂ) ^ k) (Ioi 0) := by
  have hint0 : IntegrableOn (fun x : ℝ => x ^ ((k : ℝ) - 1 / 2) * Real.exp (-ε * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hε (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hcont : ContinuousOn (fun u : ℝ => fctRho u * Complex.exp (fctW û ε u) * (u : ℂ) ^ k) (Ioi 0) :=
    (((contDiffOn_fctRho 0).continuousOn).mul (continuous_fctW û ε).cexp.continuousOn).mul
      (Continuous.continuousOn (by fun_prop))
  refine Integrable.mono' hint0 (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
  simp only [norm_mul, norm_fctRho hu, norm_exp_fctW, norm_pow, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hu)]
  rw [show -ε * u ^ 2 = -(ε * u ^ 2) by ring, mul_assoc, mul_comm (Real.exp _), ← mul_assoc,
    show (k : ℝ) - 1 / 2 = -(1 / 2) + k by ring, Real.rpow_add hu, Real.rpow_natCast]

/-- For `ε > 0` the regularised integral of `u^k` is differentiable in `û` with derivative `-i · (regularised integral of u^{k+1})`. -/
lemma hasDerivAt_fctSEps {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : ℝ) :
    HasDerivAt (fun w' : ℝ => fctSEps w' ε (fun u => (u : ℂ) ^ k))
      (-Complex.I * fctSEps w ε (fun u => (u : ℂ) ^ (k + 1))) w := by
  set F : ℝ → ℝ → ℂ := fun w' u => fctRho u * Complex.exp (fctW w' ε u) * (u : ℂ) ^ k with hF
  set F' : ℝ → ℝ → ℂ := fun w' u => fctRho u * (Complex.exp (fctW w' ε u) * (-(Complex.I * (u : ℂ)))) * (u : ℂ) ^ k with hF'
  set μ : Measure ℝ := volume.restrict (Ioi 0) with hμ
  have hint0 : IntegrableOn (fun x : ℝ => x ^ ((k : ℝ) - 1 / 2) * Real.exp (-ε * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hε (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hint1 : IntegrableOn (fun x : ℝ => x ^ ((k : ℝ) + 1 / 2) * Real.exp (-ε * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hε (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
  have hcontF : ∀ w' : ℝ, ContinuousOn (F w') (Ioi 0) := fun w' =>
    (((contDiffOn_fctRho 0).continuousOn).mul (continuous_fctW w' ε).cexp.continuousOn).mul
      (Continuous.continuousOn (by fun_prop))
  have hcontF' : ∀ w' : ℝ, ContinuousOn (F' w') (Ioi 0) := fun w' =>
    (((contDiffOn_fctRho 0).continuousOn).mul
      (((continuous_fctW w' ε).cexp).mul (by fun_prop : Continuous fun u : ℝ => -(Complex.I * (u : ℂ)))).continuousOn).mul
      (Continuous.continuousOn (by fun_prop))
  have hnormF : ∀ w' u : ℝ, 0 < u → ‖F w' u‖ = u ^ ((k : ℝ) - 1 / 2) * Real.exp (-ε * u ^ 2) := by
    intro w' u hu
    simp only [hF, norm_mul, norm_fctRho hu, norm_exp_fctW, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le]
    rw [show -ε * u ^ 2 = -(ε * u ^ 2) by ring, mul_assoc, mul_comm (Real.exp _), ← mul_assoc,
      show (k : ℝ) - 1 / 2 = -(1 / 2) + k by ring, Real.rpow_add hu, Real.rpow_natCast]
  have hnormF' : ∀ w' u : ℝ, 0 < u → ‖F' w' u‖ = u ^ ((k : ℝ) + 1 / 2) * Real.exp (-ε * u ^ 2) := by
    intro w' u hu
    simp only [hF', norm_mul, norm_fctRho hu, norm_exp_fctW, norm_pow, Complex.norm_real, Real.norm_of_nonneg hu.le, norm_neg,
      Complex.norm_I]
    rw [show -ε * u ^ 2 = -(ε * u ^ 2) by ring, one_mul, mul_assoc, mul_comm (Real.exp _), ← mul_assoc,
      show (k : ℝ) + 1 / 2 = -(1 / 2) + (k + 1 : ℕ) by push_cast; ring, Real.rpow_add hu, Real.rpow_natCast]
    ring

  have hmeasF : ∀ w' : ℝ, AEStronglyMeasurable (F w') μ := fun w' => (hcontF w').aestronglyMeasurable measurableSet_Ioi
  have hmeasF' : ∀ w' : ℝ, AEStronglyMeasurable (F' w') μ := fun w' => (hcontF' w').aestronglyMeasurable measurableSet_Ioi
  have hFint : Integrable (F w) μ := by
    refine Integrable.mono' hint0 (hmeasF w) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    exact (hnormF w u hu).le
  obtain ⟨-, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := F') (x₀ := w)
    (bound := fun u => u ^ ((k : ℝ) + 1 / 2) * Real.exp (-ε * u ^ 2)) (s := univ) univ_mem
    (Filter.Eventually.of_forall hmeasF) hFint (hmeasF' w)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu w' _ => (hnormF' w' u hu).le))
    hint1
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu w' _ => by
      have := (((hasDerivAt_fctW_û w' ε u).cexp).const_mul (fctRho u)).mul_const ((u : ℂ) ^ k)
      exact this))
  have e1 : ∀ w' : ℝ, fctSEps w' ε (fun u => (u : ℂ) ^ k) =
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u, F w' u ∂μ := fun w' => fctSEps_eq w' ε _
  have e2 : fctSEps w ε (fun u => (u : ℂ) ^ (k + 1)) =
      Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u, fctRho u * Complex.exp (fctW w ε u) * (u : ℂ) ^ (k + 1) ∂μ :=
    fctSEps_eq w ε _
  have e3 : ∫ u, F' w u ∂μ = -Complex.I * ∫ u, fctRho u * Complex.exp (fctW w ε u) * (u : ℂ) ^ (k + 1) ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hF']
    ring
  have := hd.const_mul (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I))
  rw [e2, show -Complex.I * (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * ∫ u, fctRho u * Complex.exp (fctW w ε u) * (u : ℂ) ^ (k + 1) ∂μ) =
    Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * (-Complex.I * ∫ u, fctRho u * Complex.exp (fctW w ε u) * (u : ℂ) ^ (k + 1) ∂μ) by ring, ← e3]
  simp only [e1]
  exact this


/-- `𝒮[u^k](û)`. -/
noncomputable def gk (û : ℝ) (k : ℕ) : ℂ := fctS û (fun u => (u : ℂ) ^ k)

lemma powSym_cond (k : ℕ) : (k : ℝ) < 3 * ((k + 1 : ℕ) : ℝ) - 1 / 2 := by
  push_cast
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

/-- The Abel limit of `u^k` exists for every real `û`: it is `gk û k`. -/
lemma gk_limit (k : ℕ) (û : ℝ) : FctSLimit û (fun u => (u : ℂ) ^ k) (gk û k) := by
  obtain ⟨C, hC0, hC⟩ := fctInnerSymbolsA (|û| + 1) (k + 1) k (by positivity) (by omega) (powSym_cond k)
  obtain ⟨⟨L, hL⟩, -⟩ := hC û (Nat.factorial k : ℝ) _ (by linarith) (Nat.cast_nonneg _) (powSym k)
  have := hL.fctS_eq
  unfold gk
  rw [this]; exact hL

/-- Local bounds: `‖gk û k‖ ≤ C` and `‖𝒮_ε[u^k](û)‖ ≤ C` for `|û| ≤ M`, `0 < ε < 1`. -/
lemma gk_bound (k : ℕ) (M : ℝ) (hM : 0 < M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ û : ℝ, |û| ≤ M →
    ‖gk û k‖ ≤ C ∧ ∀ ε ∈ Ioo (0 : ℝ) 1, ‖fctSEps û ε (fun u => (u : ℂ) ^ k)‖ ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := fctInnerSymbolsA M (k + 1) k hM (by omega) (powSym_cond k)
  obtain ⟨C₂, hC₂0, hC₂⟩ := fctInnerSymbolsA_unif M (k + 1) k hM (by omega) (powSym_cond k)
  refine ⟨max (C₁ * (Nat.factorial k : ℝ)) (C₂ * (Nat.factorial k : ℝ)), by positivity, fun û hû => ⟨?_, fun ε hε => ?_⟩⟩
  · obtain ⟨-, h2, -⟩ := hC₁ û (Nat.factorial k : ℝ) _ hû (Nat.cast_nonneg _) (powSym k)
    exact h2.trans (le_max_left _ _)
  · exact (hC₂ û (Nat.factorial k : ℝ) _ hû (Nat.cast_nonneg _) (powSym k) ε hε).trans (le_max_right _ _)

/-- Integral form of `∂_û 𝒮[u^k] = -i 𝒮[u^{k+1}]`. -/
lemma gk_ftc (k : ℕ) (a b : ℝ) :
    gk b k - gk a k = ∫ w in a..b, -Complex.I * gk w (k + 1) := by
  set M : ℝ := max |a| |b| + 1 with hMdef
  have hM : 0 < M := by positivity
  obtain ⟨C, hC0, hC⟩ := gk_bound (k + 1) M hM
  have hw : ∀ w ∈ Ι a b, |w| ≤ M := by
    intro w hw
    have : w ∈ uIcc a b := Set.uIoc_subset_uIcc hw
    have h0 : |w| ≤ max |a| |b| := by
      rcases Set.mem_uIcc.1 this with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact abs_le_max_abs_abs h1 h2
      · rw [max_comm]; exact abs_le_max_abs_abs h1 h2
    linarith
  have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  have hF : ∀ ε ∈ Ioo (0 : ℝ) 1, fctSEps b ε (fun u => (u : ℂ) ^ k) - fctSEps a ε (fun u => (u : ℂ) ^ k) =
      ∫ w in a..b, -Complex.I * fctSEps w ε (fun u => (u : ℂ) ^ (k + 1)) := by
    intro ε hε
    symm
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun w _ => hasDerivAt_fctSEps hε.1 k w) ?_
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul (continuous_iff_continuousAt.2 fun w => (hasDerivAt_fctSEps hε.1 (k + 1) w).continuousAt)
  have hlhs : Tendsto (fun ε => fctSEps b ε (fun u => (u : ℂ) ^ k) - fctSEps a ε (fun u => (u : ℂ) ^ k)) (𝓝[>] 0)
      (𝓝 (gk b k - gk a k)) := (gk_limit k b).sub (gk_limit k a)
  have hrhs : Tendsto (fun ε => ∫ w in a..b, -Complex.I * fctSEps w ε (fun u => (u : ℂ) ^ (k + 1))) (𝓝[>] 0)
      (𝓝 (∫ w in a..b, -Complex.I * gk w (k + 1))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ ?_ ?_
    · filter_upwards [hmem] with ε hε
      exact (continuous_const.mul (continuous_iff_continuousAt.2 fun w =>
        (hasDerivAt_fctSEps hε.1 (k + 1) w).continuousAt)).aestronglyMeasurable
    · filter_upwards [hmem] with ε hε
      refine Filter.Eventually.of_forall fun w hwI => ?_
      rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
      exact (hC w (hw w hwI)).2 ε hε
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun w hwI => ?_
      exact tendsto_const_nhds.mul (gk_limit (k + 1) w)
  exact tendsto_nhds_unique hlhs (hrhs.congr' (by filter_upwards [hmem] with ε hε; exact (hF ε hε).symm))


lemma gk_lipschitz (k : ℕ) (M : ℝ) (hM : 0 < M) : ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, |a| ≤ M → |b| ≤ M →
    ‖gk b k - gk a k‖ ≤ C * |b - a| := by
  obtain ⟨C, hC0, hC⟩ := gk_bound (k + 1) M hM
  refine ⟨C, hC0, fun a b ha hb => ?_⟩
  rw [gk_ftc k a b]
  refine intervalIntegral.norm_integral_le_of_norm_le_const (fun w hw => ?_)
  have hw' : w ∈ uIcc a b := Set.uIoc_subset_uIcc hw
  have h0 : |w| ≤ max |a| |b| := by
    rcases Set.mem_uIcc.1 hw' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact abs_le_max_abs_abs h1 h2
    · rw [max_comm]; exact abs_le_max_abs_abs h1 h2
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact (hC w ((h0.trans (max_le ha hb)))).1

lemma continuous_gk (k : ℕ) : Continuous (fun w : ℝ => gk w k) := by
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  obtain ⟨C, hC0, hC⟩ := gk_lipschitz k (|w₀| + 1) (by positivity)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (g := fun w : ℝ => C * |w - w₀|) (Filter.Eventually.of_forall fun w => norm_nonneg _) ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds w₀ one_pos] with w hw
    rw [Metric.mem_ball, Real.dist_eq] at hw
    have : |w| ≤ |w₀| + 1 := by
      have := abs_sub_abs_le_abs_sub w w₀
      linarith
    exact hC w₀ w (by linarith) this
  · have : Tendsto (fun w : ℝ => C * |w - w₀|) (𝓝 w₀) (𝓝 (C * |w₀ - w₀|)) :=
      (continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).tendsto w₀
    simpa using this

lemma hasDerivAt_gk (k : ℕ) (w : ℝ) : HasDerivAt (fun w' : ℝ => gk w' k) (-Complex.I * gk w (k + 1)) w := by
  have hcont : Continuous (fun x : ℝ => -Complex.I * gk x (k + 1)) := continuous_const.mul (continuous_gk (k + 1))
  have h1 := intervalIntegral.integral_hasDerivAt_right (f := fun x : ℝ => -Complex.I * gk x (k + 1)) (a := 0) (b := w)
    (hcont.intervalIntegrable _ _) (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt
  have h2 := h1.const_add (gk 0 k)
  refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w' => ?_)
  have := gk_ftc k 0 w'
  simp only
  rw [← this]; ring

lemma iteratedDeriv_gk (k : ℕ) : iteratedDeriv k (fun w : ℝ => gk w 0) = fun w => (-Complex.I) ^ k * gk w k := by
  induction k with
  | zero => funext w; simp
  | succ k ih =>
    funext w
    rw [iteratedDeriv_succ, ih]
    have := (hasDerivAt_gk k w).const_mul ((-Complex.I) ^ k)
    rw [this.deriv, pow_succ]; ring

/-- **`fct:inner-symbols` (a), monomials** (Lemma FCT.5b (a), last sentence): `𝒮[u^k] = i^k ∂_û^k 𝒮[1]`. -/
theorem fctInnerSymbolsMonomial : FctInnerSymbolsMonomial := by
  intro k û
  have e : (fun w : ℝ => fctS w (fun _ => (1 : ℂ))) = fun w : ℝ => gk w 0 := by
    funext w; unfold gk; simp
  rw [e, iteratedDeriv_gk k]
  have e2 : Complex.I ^ k * ((-Complex.I) ^ k * gk û k) = gk û k := by
    rw [← mul_assoc, ← mul_pow]; simp
  rw [e2]
  exact gk_limit k û


/-- Regularised ODE identity: `∫_0^∞ ∂_u (u^{1/2} e^{w_ε}) du = 0`. -/
lemma fctSEps_ode {ε : ℝ} (hε : 0 < ε) (û : ℝ) :
    (1 / 2 : ℂ) * fctSEps û ε (fun u => (u : ℂ) ^ 0) - Complex.I * û * fctSEps û ε (fun u => (u : ℂ) ^ 1)
      - (Complex.I / 4) * fctSEps û ε (fun u => (u : ℂ) ^ 3) - 2 * ε * fctSEps û ε (fun u => (u : ℂ) ^ 2) = 0 := by
  set r : ℝ → ℂ := fun u => ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
  set f : ℝ → ℂ := fun u => r u * Complex.exp (fctW û ε u) with hf
  set h : ℕ → ℝ → ℂ := fun k u => fctRho u * Complex.exp (fctW û ε u) * (u : ℂ) ^ k with hh
  set f' : ℝ → ℂ := fun u => (1 / 2 : ℂ) * h 0 u - Complex.I * û * h 1 u - (Complex.I / 4) * h 3 u - 2 * ε * h 2 u with hf'
  have hderiv : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt f (f' u) u := by
    intro u hu
    have hu0 : 0 < u := hu
    have h1 : HasDerivAt r (((1 / 2 : ℝ) * u ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) u :=
      (Real.hasDerivAt_rpow_const (Or.inl hu0.ne')).ofReal_comp
    have h2 := h1.mul (hasDerivAt_fctW û ε u).cexp
    refine h2.congr_deriv ?_
    have e1 : u ^ ((1 / 2 : ℝ) - 1) = u ^ (-(1 / 2 : ℝ)) := by norm_num
    have e2 : ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ) = fctRho u * (u : ℂ) := by
      unfold fctRho
      rw [← Complex.ofReal_mul, show (u ^ (1 / 2 : ℝ)) = u ^ (-(1 / 2 : ℝ) + 1) by norm_num,
        Real.rpow_add_one hu0.ne']
    have e3 : (((1 / 2 : ℝ) * u ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) = (1 / 2 : ℂ) * fctRho u := by
      rw [e1]; unfold fctRho; push_cast; ring
    rw [e3]
    simp only [hf', hh, hr, fctD, e2]
    generalize fctRho u = ρ
    push_cast
    ring
  have hint : IntegrableOn f' (Ioi 0) :=
    ((((integrableOn_hk hε û 0).const_mul (1 / 2 : ℂ)).sub ((integrableOn_hk hε û 1).const_mul (Complex.I * û))).sub
      ((integrableOn_hk hε û 3).const_mul (Complex.I / 4))).sub ((integrableOn_hk hε û 2).const_mul (2 * ε))
  have hlim : Tendsto f atTop (𝓝 0) := by
    have := tendsto_amp_top (û := û) (ε := ε) (U := 0) (σ := 1 / 2) (A := 1) (g := r) hε (fun u hu => by
      show ‖((u ^ (1 / 2 : ℝ) : ℝ) : ℂ)‖ ≤ 1 * u ^ (1 / 2 : ℝ)
      rw [one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu _)])
    exact this
  have hcont : ContinuousWithinAt f (Ici 0) 0 := by
    have h1 : ContinuousAt (fun u : ℝ => ((u ^ (1 / 2 : ℝ) : ℝ) : ℂ)) 0 :=
      Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num)))
    exact (h1.mul (continuous_fctW û ε).cexp.continuousAt).continuousWithinAt
  have h0 := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  have hf0 : f 0 = 0 := by simp [hf, hr]
  rw [hf0, sub_zero] at h0
  have hk := integrableOn_hk hε û
  have i0 : IntegrableOn (fun u => (1 / 2 : ℂ) * h 0 u) (Ioi 0) := (hk 0).const_mul _
  have i1 : IntegrableOn (fun u => Complex.I * û * h 1 u) (Ioi 0) := (hk 1).const_mul _
  have i3 : IntegrableOn (fun u => (Complex.I / 4) * h 3 u) (Ioi 0) := (hk 3).const_mul _
  have i2 : IntegrableOn (fun u => (2 * ε : ℂ) * h 2 u) (Ioi 0) := (hk 2).const_mul _
  have e3 : ∫ u in Ioi (0 : ℝ), f' u = (1 / 2 : ℂ) * (∫ u in Ioi (0 : ℝ), h 0 u) - Complex.I * û * (∫ u in Ioi (0 : ℝ), h 1 u)
      - (Complex.I / 4) * (∫ u in Ioi (0 : ℝ), h 3 u) - 2 * ε * (∫ u in Ioi (0 : ℝ), h 2 u) := by
    simp only [hf']
    rw [integral_sub (f := fun u => (1 / 2 : ℂ) * h 0 u - Complex.I * û * h 1 u - (Complex.I / 4) * h 3 u)
        (g := fun u => (2 * ε : ℂ) * h 2 u) ((i0.sub i1).sub i3) i2,
      integral_sub (f := fun u => (1 / 2 : ℂ) * h 0 u - Complex.I * û * h 1 u) (g := fun u => (Complex.I / 4) * h 3 u)
        (i0.sub i1) i3,
      integral_sub (f := fun u => (1 / 2 : ℂ) * h 0 u) (g := fun u => Complex.I * û * h 1 u) i0 i1,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e3] at h0
  simp only [fctSEps_eq]
  have : ∀ k : ℕ, (∫ u in Ioi (0 : ℝ), fctRho u * Complex.exp (fctW û ε u) * (u : ℂ) ^ k) = ∫ u in Ioi (0 : ℝ), h k u := fun k => rfl
  simp only [this]
  linear_combination (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I)) * h0

end FctSymA

/-- info: 'FormalResearch.SignUncertainty.FctSymA.fctInnerSymbolsMonomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctSymA.fctInnerSymbolsMonomial

end FormalResearch.SignUncertainty

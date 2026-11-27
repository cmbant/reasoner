module

public import FormalResearch.SignUncertainty.AiryFarCardinalLaplace
public import FormalResearch.SignUncertainty.AiryCauchyBounds
public import FormalResearch.Special.AiryCftQUniform
public import FormalResearch.Special.AiryGoodCircles
public import Mathlib.Analysis.Complex.AbsMax

/-!
# Hermite--Airy Rational Approximation (`lem:al-hermite-approx`)

Source:
* `CFT/sign_uncertainty/paper/ce_airy_lp_proofs.tex` (lines 803–869):
  For real-on-`ℝ` `F ∈ 𝒢 ∩ 𝓢(ℝ)`, the Hermite--Airy expansion `(eq:al-hermite)` holds on all of `ℂ`
  (proved without contour residue calculus by dividing `F - S` twice at each zero via `dslope`, bounding
  the entire quotient `(F - S) / Ai²` on good circles via `airyQ_mem_half` and `good_circle_exists`, and
  applying the maximum modulus principle), `∑ F'(a_n)/Ai'(a_n)² = 0`, and the partial sums `F_N ∈ ℛ_Ai^gen`
  satisfy (a)–(d).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric FormalResearch.Special
open scoped Real Nat ContDiff Uniformity

namespace FormalResearch.SignUncertainty

/-! ### Section 3: Hermite--Airy Rational Approximation (`lem:al-hermite-approx`) -/

/-- Monotonicity of `Ai'(x)² - x Ai(x)²` gives the uniform floor `Ai'(a₁)² ≤ Ai'(a_{n+1})²`. -/
lemma airyAi'_airyZ_sq_ge_zero (n : ℕ) :
    airyAi' (airyZ 0) ^ 2 ≤ airyAi' (airyZ n) ^ 2 := by
  let E : ℝ → ℝ := fun x => airyAi' x ^ 2 - x * airyAi x ^ 2
  have hdE : ∀ x : ℝ, HasDerivAt E (-(airyAi x ^ 2)) x := fun x => by
    have hA := hasDerivAt_airyAi x
    have hB := hasDerivAt_airyAi' x
    have h1 : HasDerivAt (fun t => airyAi' t ^ 2) (2 * airyAi' x * (x * airyAi x)) x :=
      (hB.pow 2).congr_deriv (by ring)
    have h2 : HasDerivAt (fun t => t * airyAi t ^ 2)
        (1 * airyAi x ^ 2 + x * (2 * airyAi x * airyAi' x)) x :=
      (hasDerivAt_id' x).mul ((hA.pow 2).congr_deriv (by ring))
    exact (h1.sub h2).congr_deriv (by ring)
  have hanti : Antitone E := antitone_of_deriv_nonpos
    (fun x => (hdE x).differentiableAt)
    (fun x => by rw [(hdE x).deriv]; linarith [sq_nonneg (airyAi x)])
  have hle := hanti (airyZ_anti (Nat.zero_le n))
  have hz0 : airyAi (airyZ 0) = 0 := airyAi_airyZero 1
  have hzn : airyAi (airyZ n) = 0 := airyAi_airyZero (n + 1)
  dsimp [E] at hle
  rw [hz0, hzn] at hle
  linarith

/-- Because `Ai''(a_{n+1}) = a_{n+1} Ai(a_{n+1}) = 0`, the Airy cardinal `k_n(z) = Ai(z)/(z - a_{n+1})`
has zero first derivative at its own node `a_{n+1}`. -/
lemma deriv_airyCardinal_same (n : ℕ) : deriv (airyCardinal n) (airyZ n : ℂ) = 0 := by
  set a : ℂ := (airyZ n : ℂ)
  have hmul : ∀ z : ℂ, (z - a) * airyCardinal n z = airyAiC z := fun z => by
    by_cases hz : z = a
    · subst hz; simp [a, airyAiC_airyZ]
    · rw [airyCardinal_of_ne n hz, mul_div_cancel₀ _ (sub_ne_zero.mpr hz)]
  have hd1 : ∀ z : ℂ, deriv airyAiC z = airyCardinal n z + (z - a) * deriv (airyCardinal n) z := by
    intro z
    have h1 : HasDerivAt (fun w : ℂ => (w - a) * airyCardinal n w)
        (1 * airyCardinal n z + (z - a) * deriv (airyCardinal n) z) z :=
      ((hasDerivAt_id' z).sub_const a).mul ((differentiable_airyCardinal n z).hasDerivAt)
    rw [funext hmul] at h1
    have hd_eq := h1.deriv
    rwa [one_mul] at hd_eq
  have hd_card2 : DifferentiableAt ℂ (deriv (airyCardinal n)) a :=
    (((differentiable_airyCardinal n).contDiff (n := (2 : ℕ))).differentiable_iteratedDeriv' 1 a)
      |>.congr_of_eventuallyEq (Eventually.of_forall fun z => congrFun iteratedDeriv_one.symm z)
  have hd2_rhs : HasDerivAt (fun z : ℂ => airyCardinal n z + (z - a) * deriv (airyCardinal n) z)
      (2 * deriv (airyCardinal n) a) a := by
    have hp1 := (differentiable_airyCardinal n a).hasDerivAt
    have hp2 := ((hasDerivAt_id' a).sub_const a).mul hd_card2.hasDerivAt
    exact (hp1.add hp2).congr_deriv (by ring)
  have hd2_lhs : HasDerivAt (deriv airyAiC) 0 a := by
    have h := hasDerivAt_deriv_airyAiC a
    rw [show a * airyAiC a = 0 by simp [a, airyAiC_airyZ]] at h
    exact h
  rw [← funext hd1] at hd2_rhs
  have heq := hd2_rhs.unique hd2_lhs
  exact (mul_eq_zero.mp heq).resolve_left two_ne_zero

private lemma airyCardinal_at_airyZ (n m : ℕ) :
    airyCardinal n (airyZ m : ℂ) = if n = m then (airyAi' (airyZ m) : ℂ) else 0 := by
  split_ifs with hnm
  · subst hnm; exact airyCardinal_same_eq_airyAi' n
  · have hne : (airyZ m : ℂ) ≠ (airyZ n : ℂ) := fun h =>
      hnm (airyZ_injective (Complex.ofReal_injective h.symm))
    rw [airyCardinal_of_ne n hne, airyAiC_airyZ, zero_div]

private lemma airySeedG_at_airyZ (n m : ℕ) :
    airySeedG n (airyZ m : ℂ) = if n = m then ((airyAi' (airyZ m) ^ 2 : ℝ) : ℂ) else 0 := by
  unfold airySeedG
  rw [airyCardinal_at_airyZ]
  split_ifs with hnm
  · push_cast; rfl
  · simp

private lemma airySeedF_at_airyZ (n m : ℕ) : airySeedF n (airyZ m : ℂ) = 0 := by
  unfold airySeedF
  rw [airyAiC_airyZ, zero_mul]

private lemma deriv_airySeedG_at_airyZ (n m : ℕ) : deriv (airySeedG n) (airyZ m : ℂ) = 0 := by
  have hd : HasDerivAt (airySeedG n)
      (2 * airyCardinal n (airyZ m : ℂ) * deriv (airyCardinal n) (airyZ m : ℂ)) (airyZ m : ℂ) := by
    unfold airySeedG
    exact (((differentiable_airyCardinal n (airyZ m : ℂ)).hasDerivAt.pow 2).congr_deriv (by ring))
  rw [hd.deriv, airyCardinal_at_airyZ]
  split_ifs with hnm
  · subst hnm; rw [deriv_airyCardinal_same, mul_zero]
  · simp

private lemma deriv_airySeedF_at_airyZ (n m : ℕ) :
    deriv (airySeedF n) (airyZ m : ℂ) =
      if n = m then ((airyAi' (airyZ m) ^ 2 : ℝ) : ℂ) else 0 := by
  have hd : HasDerivAt (airySeedF n)
      (deriv airyAiC (airyZ m : ℂ) * airyCardinal n (airyZ m : ℂ) +
        airyAiC (airyZ m : ℂ) * deriv (airyCardinal n) (airyZ m : ℂ)) (airyZ m : ℂ) := by
    unfold airySeedF
    exact (differentiable_airyAiC (airyZ m : ℂ)).hasDerivAt.mul
      ((differentiable_airyCardinal n (airyZ m : ℂ)).hasDerivAt)
  rw [hd.deriv, airyAiC_airyZ, zero_mul, add_zero, deriv_airyAiC_ofReal, airyCardinal_at_airyZ]
  split_ifs with hnm
  · push_cast; ring
  · simp

/-- Single `n`-th Hermite--Airy term `[F(a_{n+1}) g_{n+1}(z) + F'(a_{n+1}) f_{n+1}(z)] / Ai'(a_{n+1})²`
(`(eq:al-hermite)`). -/
noncomputable def airyHermiteTerm (F : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ((((F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) * airySeedG n z) +
    ((((deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) * airySeedF n z)

/-- `N`-th partial sum `F_N` of the Hermite--Airy expansion `(eq:al-hermite)`. -/
noncomputable def airyHermitePartialSum (F : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, airyHermiteTerm F n z

/-- Rapid coefficient summability for `F ∈ 𝒢 ∩ 𝓢(ℝ)`. -/
private lemma airyHermite_coeff_summable {F : ℂ → ℂ} {S_F : SchwartzMap ℝ ℝ}
    (hSF : ∀ u : ℝ, S_F u = (F (u : ℂ)).re)
    (hderiv_SF : ∀ u : ℝ, deriv (S_F : ℝ → ℝ) u = (deriv F (u : ℂ)).re) (M : ℕ) :
    Summable (fun n : ℕ => |airyZ n| ^ M *
      (|(F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2| +
       |(deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2|)) := by
  have hAi'0_pos : 0 < airyAi' (airyZ 0) ^ 2 :=
    sq_pos_of_ne_zero (airyAi'_airyZ_ne_zero 0)
  have hcoeff_decay : ∀ K_ord : ℕ, ∃ K_M : ℝ, 0 ≤ K_M ∧
      ∀ n : ℕ, |airyZ n| ^ K_ord *
        (|(F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2| +
         |(deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2|) ≤ K_M := by
    intro K_ord
    obtain ⟨C0, hC0_pos, hC0⟩ := S_F.decay K_ord 0
    obtain ⟨C1, hC1_pos, hC1⟩ := S_F.decay K_ord 1
    refine ⟨(C0 + C1) / airyAi' (airyZ 0) ^ 2, by positivity, fun n => ?_⟩
    have h0 := hC0 (airyZ n)
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
      Real.norm_eq_abs, hSF (airyZ n)] at h0
    have h1 := hC1 (airyZ n)
    rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
      Real.norm_eq_abs, hderiv_SF (airyZ n)] at h1
    have hden_ge := airyAi'_airyZ_sq_ge_zero n
    have hden_pos : 0 < airyAi' (airyZ n) ^ 2 := lt_of_lt_of_le hAi'0_pos hden_ge
    rw [abs_div, abs_div, abs_of_pos hden_pos, ← add_div, ← mul_div_assoc, mul_add]
    exact div_le_div₀ (by positivity) (add_le_add h0 h1) hAi'0_pos hden_ge
  obtain ⟨K, hK_nn, hK⟩ := hcoeff_decay (M + 2)
  refine (summable_airyZ_inv_sq.mul_left K).of_nonneg_of_le (fun _ => by positivity) fun n => ?_
  have h1 := hK n
  rw [pow_add, sq_abs] at h1
  set c_n := |(F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2| +
    |(deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2|
  calc |airyZ n| ^ M * c_n
      = (|airyZ n| ^ M * (airyZ n) ^ 2 * c_n) * ((airyZ n) ^ 2)⁻¹ := by
        have hne0 : airyZ n ≠ 0 := (airyZ_neg n).ne
        field_simp [hne0]
    _ ≤ K * ((airyZ n) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right h1 (by positivity)

/-- Core expansion and derivative-quadrature step of `lem:al-hermite-approx`:
proves `(eq:al-hermite)` on all of `ℂ` via `dslope`-twice, good circles, and Maximum Modulus,
together with `∑ F'(a_n)/Ai'(a_n)² = 0` and local compact-ball summable majorants. -/
private lemma airyHermite_quadrature_and_expansion {F : ℂ → ℂ} (hF : InAiryClass F)
    (hF_im : ∀ u : ℝ, (F (u : ℂ)).im = 0)
    {S_F : SchwartzMap ℝ ℝ} (hSF : ∀ u : ℝ, S_F u = (F (u : ℂ)).re) :
    (∀ z : ℂ, HasSum (fun n : ℕ => airyHermiteTerm F n z) (F z)) ∧
    HasSum (fun n : ℕ => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2) 0 ∧
    (∀ R : ℝ, 1 ≤ R → ∃ u_R : ℕ → ℝ, Summable u_R ∧
      ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) R, ‖airyHermiteTerm F n z‖ ≤ u_R n) := by
  have hF_ofReal : ∀ u : ℝ, F (u : ℂ) = (S_F u : ℂ) := fun u => by
    apply Complex.ext
    · simp [hSF u]
    · simp [hF_im u]
  have hderiv_SF : ∀ u : ℝ, deriv (S_F : ℝ → ℝ) u = (deriv F (u : ℂ)).re := fun u => by
    have h1 := iteratedDeriv_re_of_differentiable hF.1 1 u
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    have hfun : (fun t : ℝ => (F (t : ℂ)).re) = (S_F : ℝ → ℝ) := funext fun t => (hSF t).symm
    rwa [hfun] at h1
  have hderiv_F_ofReal : ∀ u : ℝ, deriv F (u : ℂ) = ((deriv (S_F : ℝ → ℝ) u : ℝ) : ℂ) := fun u => by
    have hd1 : HasDerivAt (fun t : ℝ => F (t : ℂ)) (deriv F (u : ℂ)) u :=
      (hF.1 (u : ℂ)).hasDerivAt.comp_ofReal
    have hd2 : HasDerivAt (fun t : ℝ => (S_F t : ℂ)) ((deriv (S_F : ℝ → ℝ) u : ℝ) : ℂ) u :=
      S_F.differentiableAt.hasDerivAt.ofReal_comp
    rw [funext hF_ofReal] at hd1
    exact hd1.unique hd2
  set cG : ℕ → ℝ := fun n => (F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cF : ℕ → ℝ := fun n => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cAbs : ℕ → ℝ := fun n => |cG n| + |cF n|
  have hcoeff_summable : ∀ M : ℕ, Summable (fun n : ℕ => |airyZ n| ^ M * cAbs n) :=
    airyHermite_coeff_summable hSF hderiv_SF
  -- 1. Quadrature for `deriv F`: `HasSum cF 0`
  have hcF_hasSum_zero : HasSum cF 0 := by
    obtain ⟨C₀, ν₀, hC₀_nn, hb₀⟩ := hF.2.2.1
    have hdF_diff : Differentiable ℂ (deriv F) := by
      simpa [iteratedDeriv_one] using
        (hF.1.contDiff (n := (2 : ℕ))).differentiable_iteratedDeriv' 1
    have hdF_bd := deriv_inAiryClass_bound hF.1 hC₀_nn hb₀
    obtain ⟨D0, _, hD0⟩ := S_F.decay 0 1
    obtain ⟨D2, _, hD2⟩ := S_F.decay 2 1
    have hdSF_int : Integrable (deriv (S_F : ℝ → ℝ)) := by
      have hdom : Integrable (fun x : ℝ => (D0 + D2) * (1 + x ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.const_mul (D0 + D2)
      refine hdom.mono' ((S_F.smooth (⊤ : ℕ∞)).iterate_deriv 1 |>.continuous.aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      have b0 := hD0 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
        Real.norm_eq_abs, pow_zero, one_mul] at b0
      have b2 := hD2 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_one,
        Real.norm_eq_abs, sq_abs] at b2
      rw [Real.norm_eq_abs, le_mul_inv_iff₀ (by positivity)]
      nlinarith [abs_nonneg (deriv (S_F : ℝ → ℝ) x)]
    have hdF_int : Integrable (fun x : ℝ => deriv F (x : ℂ)) := by
      simp_rw [hderiv_F_ofReal]
      exact hdSF_int.ofReal
    obtain ⟨B1, hB1_pos, hB1⟩ := S_F.decay 1 0
    have hint_dSF_zero : (∫ x : ℝ, deriv (S_F : ℝ → ℝ) x) = 0 := by
      have ht_top : Tendsto (S_F : ℝ → ℝ) atTop (𝓝 0) := by
        have hinv : Tendsto (fun x : ℝ => B1 * x⁻¹) atTop (𝓝 0) := by
          simpa using tendsto_inv_atTop_zero.const_mul B1
        refine squeeze_zero_norm' ?_ hinv
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        have hb := hB1 x
        rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
          pow_one, abs_of_pos hx] at hb
        exact (le_mul_inv_iff₀' hx).mpr (by linarith)
      have ht_bot : Tendsto (S_F : ℝ → ℝ) atBot (𝓝 0) := by
        have hinv : Tendsto (fun x : ℝ => B1 * (-x)⁻¹) atBot (𝓝 0) := by
          have h1 : Tendsto (fun y : ℝ => B1 * y⁻¹) atTop (𝓝 0) := by
            simpa using tendsto_inv_atTop_zero.const_mul B1
          exact h1.comp tendsto_neg_atBot_atTop
        refine squeeze_zero_norm' ?_ hinv
        filter_upwards [eventually_lt_atBot (0 : ℝ)] with x hx
        have hb := hB1 x
        rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
          pow_one, abs_of_neg hx] at hb
        have hnx : 0 < -x := neg_pos.mpr hx
        exact (le_mul_inv_iff₀' hnx).mpr (by linarith)
      have h1 := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
        (fun x _ => S_F.differentiableAt.hasDerivAt) hdSF_int.integrableOn ht_top
      have h2 := MeasureTheory.integral_Iic_of_hasDerivAt_of_tendsto' (a := (0 : ℝ))
        (fun x _ => S_F.differentiableAt.hasDerivAt) hdSF_int.integrableOn ht_bot
      have hdisj0 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
      rw [← setIntegral_univ, ← Iic_union_Ioi,
        setIntegral_union hdisj0 measurableSet_Ioi
          hdSF_int.integrableOn hdSF_int.integrableOn, h1, h2]
      ring
    have hq := airyQ_hasSum_unc hdF_diff hdF_int (by positivity) hdF_bd
    have hre := hq.map Complex.reCLM.toAddMonoidHom Complex.continuous_re
    change HasSum (fun n : ℕ => (deriv F (airyZ n : ℂ) / (deriv airyAiC (airyZ n : ℂ)) ^ 2).re)
      (∫ x : ℝ, deriv F (x : ℂ)).re at hre
    have hint_re : (∫ x : ℝ, deriv F (x : ℂ)).re = ∫ x : ℝ, deriv (S_F : ℝ → ℝ) x := by
      refine (integral_re hdF_int).symm.trans ?_
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact (hderiv_SF x).symm
    rw [hint_re, hint_dSF_zero] at hre
    refine hre.congr_fun fun n => ?_
    rw [deriv_airyAiC_ofReal, ← Complex.ofReal_pow, Complex.div_ofReal_re]
  -- 2. Local uniform majorant on every `closedBall (0 : ℂ) R` (`R ≥ 1`)
  have hball_maj : ∀ R : ℝ, 1 ≤ R → ∃ u_R : ℕ → ℝ, Summable u_R ∧
      ∀ n : ℕ, ∀ z ∈ closedBall (0 : ℂ) R, ‖airyHermiteTerm F n z‖ ≤ u_R n := by
    intro R _
    obtain ⟨M_Ai, hM_Ai⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      differentiable_airyAiC.continuous.continuousOn
    set B_Ai : ℝ := max M_Ai 0
    have hterm_cont : ∀ n : ℕ, Continuous (airyHermiteTerm F n) := fun n => by
      unfold airyHermiteTerm airySeedG airySeedF
      exact (continuous_const.mul ((differentiable_airyCardinal n).continuous.pow 2)).add
        (continuous_const.mul (differentiable_airyAiC.continuous.mul
          (differentiable_airyCardinal n).continuous))
    choose B_n hB_n using fun n : ℕ =>
      (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn (hterm_cont n).continuousOn
    let u_R : ℕ → ℝ := fun n =>
      if R + 1 ≤ -airyZ n then B_Ai ^ 2 * cAbs n else max (B_n n) 0
    have hu_sum : Summable u_R := by
      have hbase : Summable (fun n : ℕ => B_Ai ^ 2 * cAbs n) := by
        simpa [pow_zero, one_mul] using (hcoeff_summable 0).mul_left (B_Ai ^ 2)
      refine hbase.congr_cofinite ?_
      rw [Nat.cofinite_eq_atTop]
      filter_upwards [eventually_le_neg_airyZ (R + 1)] with n hn
      simp only [u_R, hn, ↓reduceIte]
    refine ⟨u_R, hu_sum, fun n z hz => ?_⟩
    dsimp [u_R]
    split_ifs with hn
    · have hne : z ≠ (airyZ n : ℂ) := by
        intro heq
        have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
        rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZ_neg n)] at h1
        linarith
      have hdist_ge1 : 1 ≤ ‖z - (airyZ n : ℂ)‖ := by
        have h1 : ‖z‖ ≤ R := mem_closedBall_zero_iff.mp hz
        have htri : ‖(airyZ n : ℂ)‖ ≤ ‖z - (airyZ n : ℂ)‖ + ‖z‖ := by
          calc ‖(airyZ n : ℂ)‖ = ‖(airyZ n : ℂ) - z + z‖ := by ring_nf
            _ ≤ ‖(airyZ n : ℂ) - z‖ + ‖z‖ := norm_add_le _ _
            _ = ‖z - (airyZ n : ℂ)‖ + ‖z‖ := by rw [norm_sub_rev]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZ_neg n)] at htri
        linarith
      have hAi_le : ‖airyAiC z‖ ≤ B_Ai := (hM_Ai z hz).trans (le_max_left _ _)
      have hcard_le : ‖airyCardinal n z‖ ≤ B_Ai := by
        rw [airyCardinal_of_ne n hne, norm_div]
        exact (div_le_self (norm_nonneg _) hdist_ge1).trans hAi_le
      have hG_le : ‖airySeedG n z‖ ≤ B_Ai ^ 2 := by
        unfold airySeedG; rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hcard_le 2
      have hF_le : ‖airySeedF n z‖ ≤ B_Ai ^ 2 := by
        unfold airySeedF; rw [norm_mul, sq]
        exact mul_le_mul hAi_le hcard_le (norm_nonneg _) (le_max_right _ _)
      unfold airyHermiteTerm
      calc ‖((cG n : ℂ) * airySeedG n z) + ((cF n : ℂ) * airySeedF n z)‖
          ≤ ‖(cG n : ℂ) * airySeedG n z‖ + ‖(cF n : ℂ) * airySeedF n z‖ := norm_add_le _ _
        _ = |cG n| * ‖airySeedG n z‖ + |cF n| * ‖airySeedF n z‖ := by
            simp [Complex.norm_real]
        _ ≤ |cG n| * B_Ai ^ 2 + |cF n| * B_Ai ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hG_le (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hF_le (abs_nonneg _))
        _ = B_Ai ^ 2 * cAbs n := by dsimp [cAbs]; ring
    · exact (hB_n n z hz).trans (le_max_left _ _)
  -- 3. Entirety and termwise derivative of `S z := ∑' n, airyHermiteTerm F n z`
  let S : ℂ → ℂ := fun z => ∑' n : ℕ, airyHermiteTerm F n z
  have hterm_diff : ∀ n : ℕ, Differentiable ℂ (airyHermiteTerm F n) := fun n => by
    unfold airyHermiteTerm airySeedG airySeedF
    exact ((differentiable_const _).mul ((differentiable_airyCardinal n).pow 2)).add
      ((differentiable_const _).mul (differentiable_airyAiC.mul (differentiable_airyCardinal n)))
  have hS_hasSum : ∀ z : ℂ, HasSum (fun n : ℕ => airyHermiteTerm F n z) (S z) := by
    intro z
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj (max ‖z‖ 1) (le_max_right _ _)
    have hz_mem : z ∈ closedBall (0 : ℂ) (max ‖z‖ 1) := by
      rw [mem_closedBall_zero_iff]; exact le_max_left _ _
    exact (Summable.of_norm_bounded hu_R fun n => hbd_R n z hz_mem).hasSum
  have hS_diff : Differentiable ℂ S := by
    intro z₀
    set R : ℝ := max (‖z₀‖ + 1) 1
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj R (le_max_right _ _)
    have hU : IsOpen (ball (0 : ℂ) R) := isOpen_ball
    have hdiffOn := differentiableOn_tsum_of_summable_norm hu_R
      (fun n => (hterm_diff n).differentiableOn) hU
      (fun n w hw => hbd_R n w (ball_subset_closedBall hw))
    have hz₀_mem : z₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith [le_max_left (‖z₀‖ + 1) 1]
    exact hdiffOn.differentiableAt (hU.mem_nhds hz₀_mem)
  have hS_deriv_hasSum : ∀ z₀ : ℂ,
      HasSum (fun n : ℕ => deriv (airyHermiteTerm F n) z₀) (deriv S z₀) := by
    intro z₀
    set R : ℝ := max (‖z₀‖ + 1) 1
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj R (le_max_right _ _)
    have hz₀_mem : z₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith [le_max_left (‖z₀‖ + 1) 1]
    exact hasSum_deriv_of_summable_norm hu_R
      (fun n => (hterm_diff n).differentiableOn) isOpen_ball
      (fun n w hw => hbd_R n w (ball_subset_closedBall hw)) hz₀_mem
  -- 4. `S` matches `F` and `deriv F` at every Airy zero `airyZ m`
  have hS_at_airyZ : ∀ m : ℕ, S (airyZ m : ℂ) = F (airyZ m : ℂ) := by
    intro m
    have hsingle : HasSum (fun n : ℕ => airyHermiteTerm F n (airyZ m : ℂ)) (F (airyZ m : ℂ)) := by
      refine (hasSum_ite_eq m (F (airyZ m : ℂ))).congr_fun fun n => ?_
      unfold airyHermiteTerm
      rw [airySeedG_at_airyZ, airySeedF_at_airyZ, mul_zero, add_zero]
      split_ifs with hnm
      · subst hnm
        have hne : airyAi' (airyZ n) ^ 2 ≠ 0 := pow_ne_zero 2 (airyAi'_airyZ_ne_zero n)
        calc (((F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) *
              ((airyAi' (airyZ n) ^ 2 : ℝ) : ℂ)
            = (((F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 * airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) :=
              (Complex.ofReal_mul _ _).symm
          _ = ((F (airyZ n : ℂ)).re : ℂ) := by rw [div_mul_cancel₀ _ hne]
          _ = F (airyZ n : ℂ) := by rw [← hSF, ← hF_ofReal]
      · simp
    exact (hS_hasSum (airyZ m : ℂ)).unique hsingle
  have hderivS_at_airyZ : ∀ m : ℕ, deriv S (airyZ m : ℂ) = deriv F (airyZ m : ℂ) := by
    intro m
    have hsingle : HasSum (fun n : ℕ => deriv (airyHermiteTerm F n) (airyZ m : ℂ))
        (deriv F (airyZ m : ℂ)) := by
      refine (hasSum_ite_eq m (deriv F (airyZ m : ℂ))).congr_fun fun n => ?_
      have hd_term : deriv (airyHermiteTerm F n) (airyZ m : ℂ) =
          (cG n : ℂ) * deriv (airySeedG n) (airyZ m : ℂ) +
            (cF n : ℂ) * deriv (airySeedF n) (airyZ m : ℂ) := by
        unfold airyHermiteTerm
        exact ((((airySeedG_inAiryClass n).1 (airyZ m : ℂ)).hasDerivAt.const_mul (cG n : ℂ)).add
          (((airySeedF_inAiryClass n).1 (airyZ m : ℂ)).hasDerivAt.const_mul (cF n : ℂ))).deriv
      rw [hd_term, deriv_airySeedG_at_airyZ, mul_zero, zero_add, deriv_airySeedF_at_airyZ]
      split_ifs with hnm
      · subst hnm
        have hne : airyAi' (airyZ n) ^ 2 ≠ 0 := pow_ne_zero 2 (airyAi'_airyZ_ne_zero n)
        dsimp [cF]
        calc (((deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) *
              ((airyAi' (airyZ n) ^ 2 : ℝ) : ℂ)
            = (((deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 *
                airyAi' (airyZ n) ^ 2 : ℝ) : ℂ) := (Complex.ofReal_mul _ _).symm
          _ = ((deriv F (airyZ n : ℂ)).re : ℂ) := by rw [div_mul_cancel₀ _ hne]
          _ = deriv F (airyZ n : ℂ) := by rw [← hderiv_SF, ← hderiv_F_ofReal]
      · simp
    exact (hS_deriv_hasSum (airyZ m : ℂ)).unique hsingle
  -- 5. Entire quotient `Q = (F - S) / Ai²`, good circles, and Maximum Modulus
  have hS_eq_F : ∀ z : ℂ, S z = F z := by
    classical
    let Δ : ℂ → ℂ := fun z => F z - S z
    have hΔ_diff : Differentiable ℂ Δ := hF.1.sub hS_diff
    have hΔ_zero : ∀ m : ℕ, Δ (airyZ m : ℂ) = 0 := fun m =>
      sub_eq_zero.mpr (hS_at_airyZ m).symm
    have hdΔ_zero : ∀ m : ℕ, deriv Δ (airyZ m : ℂ) = 0 := fun m => by
      have hd := ((hF.1 (airyZ m : ℂ)).hasDerivAt.sub (hS_diff (airyZ m : ℂ)).hasDerivAt).deriv
      change deriv Δ (airyZ m : ℂ) = _ at hd
      rw [hd, hderivS_at_airyZ, sub_self]
    let Q : ℂ → ℂ := fun z =>
      if h : ∃ m : ℕ, z = (airyZ m : ℂ) then
        dslope (dslope Δ (airyZ h.choose : ℂ)) (airyZ h.choose : ℂ) z /
          airyCardinal h.choose z ^ 2
      else Δ z / airyAiC z ^ 2
    have hQ_local_eq : ∀ (m : ℕ) {z : ℂ}, z ≠ (airyZ m : ℂ) → airyAiC z ≠ 0 →
        dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ) z / airyCardinal m z ^ 2 =
          Δ z / airyAiC z ^ 2 := by
      intro m z hz hAi
      have hds1 : dslope Δ (airyZ m : ℂ) z = Δ z / (z - (airyZ m : ℂ)) := by
        rw [dslope_of_ne _ hz, slope_def_field, hΔ_zero m, sub_zero]
      have hds1_same : dslope Δ (airyZ m : ℂ) (airyZ m : ℂ) = 0 := by
        rw [dslope_same, hdΔ_zero m]
      have hds2 : dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ) z =
          Δ z / (z - (airyZ m : ℂ)) ^ 2 := by
        rw [dslope_of_ne _ hz, slope_def_field, hds1, hds1_same, sub_zero, div_div, sq]
      rw [hds2, airyCardinal_of_ne m hz, div_pow]
      have hsub_ne : (z - (airyZ m : ℂ)) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hz)
      have hAi2_ne : airyAiC z ^ 2 ≠ 0 := pow_ne_zero 2 hAi
      field_simp [hsub_ne, hAi2_ne]
    have hQ_diff : Differentiable ℂ Q := by
      intro z₀
      by_cases hAi0 : airyAiC z₀ = 0
      · obtain ⟨k, hk1, hkz⟩ := (airyAiC_eq_zero_iff z₀).mp hAi0
        set m : ℕ := k - 1
        have hz₀_eq : z₀ = (airyZ m : ℂ) := by
          rw [hkz]; unfold airyZ; rw [Nat.sub_add_cancel hk1]
        let U_m : Set ℂ := {z : ℂ | airyCardinal m z ≠ 0}
        have hUm_open : IsOpen U_m :=
          isOpen_ne_fun (differentiable_airyCardinal m).continuous continuous_const
        have hz₀_Um : z₀ ∈ U_m := by
          change airyCardinal m z₀ ≠ 0
          rw [hz₀_eq, airyCardinal_same_eq_airyAi']
          exact Complex.ofReal_ne_zero.mpr (airyAi'_airyZ_ne_zero m)
        have hds_entire : Differentiable ℂ (dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ)) := by
          have hd1 : Differentiable ℂ (dslope Δ (airyZ m : ℂ)) :=
            differentiableOn_univ.mp
              ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hΔ_diff.differentiableOn)
          exact differentiableOn_univ.mp
            ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hd1.differentiableOn)
        have hev : Q =ᶠ[𝓝 z₀] fun z =>
            dslope (dslope Δ (airyZ m : ℂ)) (airyZ m : ℂ) z / airyCardinal m z ^ 2 := by
          filter_upwards [hUm_open.mem_nhds hz₀_Um] with z hz_Um
          change airyCardinal m z ≠ 0 at hz_Um
          by_cases hzm : z = (airyZ m : ℂ)
          · dsimp only [Q]
            split_ifs with hex
            · have hchoose : hex.choose = m :=
                airyZ_injective (Complex.ofReal_injective (hex.choose_spec.symm.trans hzm))
              rw [hchoose]
            · exact absurd ⟨m, hzm⟩ hex
          · have hno : ¬ ∃ m' : ℕ, z = (airyZ m' : ℂ) := by
              rintro ⟨m', rfl⟩
              have hm' : m' ≠ m := fun heq => hzm (heq ▸ rfl)
              have hc0 : airyCardinal m (airyZ m' : ℂ) = 0 := by
                rw [airyCardinal_at_airyZ]
                simp [hm'.symm]
              exact hz_Um hc0
            have hAi_ne : airyAiC z ≠ 0 := by
              intro h0
              obtain ⟨k', hk'1, hk'z⟩ := (airyAiC_eq_zero_iff z).mp h0
              exact hno ⟨k' - 1, by rw [hk'z]; simp [airyZ, Nat.sub_add_cancel hk'1]⟩
            simp only [Q, hno, ↓reduceDIte]
            exact (hQ_local_eq m hzm hAi_ne).symm
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
        exact (hds_entire z₀).div ((differentiable_airyCardinal m z₀).pow 2)
          (pow_ne_zero 2 hz₀_Um)
      · have hopen : IsOpen {z : ℂ | airyAiC z ≠ 0} :=
          isOpen_ne_fun differentiable_airyAiC.continuous continuous_const
        have hev : Q =ᶠ[𝓝 z₀] fun z => Δ z / airyAiC z ^ 2 := by
          filter_upwards [hopen.mem_nhds hAi0] with z hz
          have hno : ¬ ∃ m : ℕ, z = (airyZ m : ℂ) := by
            rintro ⟨m, rfl⟩
            exact hz (airyAiC_airyZ m)
          simp only [Q, hno, ↓reduceDIte]
        refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
        exact (hΔ_diff z₀).div ((differentiable_airyAiC z₀).pow 2) (pow_ne_zero 2 hAi0)
    have hΔ_eq_mul : ∀ z : ℂ, Δ z = airyAiC z ^ 2 * Q z := by
      intro z
      dsimp only [Q]
      split_ifs with hex
      · obtain ⟨m, rfl⟩ := hex
        rw [hΔ_zero m, airyAiC_airyZ m, zero_pow two_ne_zero, zero_mul]
      · have hAi_ne : airyAiC z ≠ 0 := by
          intro h0
          obtain ⟨k, hk1, hkz⟩ := (airyAiC_eq_zero_iff z).mp h0
          exact hex ⟨k - 1, by rw [hkz]; simp [airyZ, Nat.sub_add_cancel hk1]⟩
        exact (mul_div_cancel₀ (Δ z) (pow_ne_zero 2 hAi_ne)).symm
    obtain ⟨C₀, ν₀, hC₀_nn, hb₀⟩ := hF.2.2.1
    have hz2F_int : Integrable (fun x : ℝ => (x : ℂ) ^ 2 * F (x : ℂ)) := by
      obtain ⟨E2, _, hE2⟩ := S_F.decay 2 0
      obtain ⟨E4, _, hE4⟩ := S_F.decay 4 0
      have hdom : Integrable (fun x : ℝ => (E2 + E4) * (1 + x ^ 2)⁻¹) :=
        integrable_inv_one_add_sq.const_mul (E2 + E4)
      refine hdom.mono'
        (((continuous_ofReal.pow 2).mul (hF.1.continuous.comp continuous_ofReal)).aestronglyMeasurable)
        (Eventually.of_forall fun x => ?_)
      have b2 := hE2 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
        Real.norm_eq_abs, sq_abs] at b2
      have b4 := hE4 x
      rw [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero,
        Real.norm_eq_abs, show |x| ^ 4 = x ^ 2 * x ^ 2 by rw [← sq_abs]; ring] at b4
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
        hF_ofReal x, Complex.norm_real, Real.norm_eq_abs, le_mul_inv_iff₀ (by positivity)]
      nlinarith [abs_nonneg (S_F x), sq_nonneg x]
    have hz2F_growth : ∀ z : ℂ, ‖z ^ 2 * F z‖ ≤ C₀ * (1 + ‖z‖) ^ (ν₀ + 2) * airyEnv z := by
      intro z
      have hz_pos : 0 < 1 + ‖z‖ := by positivity
      have h1 : ‖z‖ ^ 2 ≤ (1 + ‖z‖) ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        exact pow_le_pow_left₀ (norm_nonneg z) (by linarith) 2
      rw [norm_mul, norm_pow]
      calc ‖z‖ ^ 2 * ‖F z‖
          ≤ (1 + ‖z‖) ^ (2 : ℝ) * (C₀ * (1 + ‖z‖) ^ ν₀ * airyEnv z) :=
            mul_le_mul h1 (hb₀ z) (norm_nonneg _) (by positivity)
        _ = C₀ * ((1 + ‖z‖) ^ ν₀ * (1 + ‖z‖) ^ (2 : ℝ)) * airyEnv z := by ring
        _ = C₀ * (1 + ‖z‖) ^ (ν₀ + 2) * airyEnv z := by rw [← Real.rpow_add hz_pos]
    obtain ⟨C_half, hChalf_nn, hChalf⟩ := airyQ_mem_half
      ((differentiable_id.pow 2).mul hF.1) hz2F_int hC₀_nn hz2F_growth
    have hsum_good : Summable (fun n : ℕ => (2 + 80000 * |airyZ n| ^ 2) * cAbs n) := by
      have hs0 := (hcoeff_summable 0).mul_left 2
      have hs2 := (hcoeff_summable 2).mul_left 80000
      refine (hs0.add hs2).congr fun n => ?_
      simp [pow_zero]; ring
    set M_good : ℝ := ∑' n : ℕ, (2 + 80000 * |airyZ n| ^ 2) * cAbs n
    have hMgood_nn : 0 ≤ M_good := tsum_nonneg fun _ => by positivity
    have hQ_zero : ∀ z₀ : ℂ, Q z₀ = 0 := by
      intro z₀
      set K_tot : ℝ := 50 * π * C_half + M_good
      have hnorm_zero : ‖Q z₀‖ ≤ 0 := by
        refine le_of_forall_pos_le_add fun δ hδ => ?_
        rw [zero_add]
        set k : ℕ := max 10 (max (⌈‖z₀‖⌉₊ + 1) (⌈K_tot / δ⌉₊ + 1))
        have hk10 : 10 ≤ k := le_max_left _ _
        obtain ⟨r, hr_lo, hr_hi, hgood⟩ := good_circle_exists k hk10
        have hr_ge10 : 10 ≤ r := by
          have : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk10
          linarith
        have hr_pos : 0 < r := by linarith
        have hz₀_in : z₀ ∈ ball (0 : ℂ) r := by
          rw [mem_ball_zero_iff]
          have hk_z : ⌈‖z₀‖⌉₊ + 1 ≤ k := (le_max_left _ _).trans (le_max_right _ _)
          have h1 : ‖z₀‖ < (k : ℝ) := by
            calc ‖z₀‖ ≤ (⌈‖z₀‖⌉₊ : ℝ) := Nat.le_ceil _
              _ < (k : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk_z)
          linarith
        have hdist_zeros : ∀ n : ℕ,
            (1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ)) ≤ |-r - airyZ n| := by
          intro n
          by_cases h1 : 1 ≤ |-r - airyZ n|
          · have hrp : (1 + r) ^ (-(1 / 2 : ℝ)) ≤ 1 := by
              simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith)
                (by norm_num : -(1 / 2 : ℝ) ≤ 0)
            linarith
          · push Not at h1
            have hgood_neg := hgood ((-r : ℝ) : ℂ) (by
              rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hr_pos])
            have henv_neg : airyEnv ((-r : ℝ) : ℂ) = 1 :=
              airyEnv_ofReal_neg (by linarith)
            rw [henv_neg, mul_one, airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs,
              sq_abs] at hgood_neg
            have hAi_lb : (1 / 10) * (1 + r) ^ (-(1 / 4 : ℝ)) ≤ |airyAi (-r)| := by
              have hsq : ((1 / 10) * (1 + r) ^ (-(1 / 4 : ℝ))) ^ 2 ≤ airyAi (-r) ^ 2 := by
                refine le_trans ?_ hgood_neg
                rw [mul_pow, ← Real.rpow_natCast ((1 + r) ^ _),
                  ← Real.rpow_mul (by linarith : 0 ≤ 1 + r)]
                have hpi4 : 25 * π ≤ 100 := by linarith [Real.pi_lt_four]
                have hdiv : (1 / 10 : ℝ) ^ 2 ≤ 1 / (25 * π) := by
                  rw [show (1 / 10 : ℝ) ^ 2 = 1 / 100 by norm_num]
                  exact one_div_le_one_div_of_le (by positivity) hpi4
                norm_num at *
                exact mul_le_mul_of_nonneg_right hdiv (by positivity)
              have hnn : 0 ≤ (1 / 10) * (1 + r) ^ (-(1 / 4 : ℝ)) := by positivity
              nlinarith [sq_abs (airyAi (-r)), abs_nonneg (airyAi (-r))]
            let lo : ℝ := min (-r) (airyZ n)
            let hi : ℝ := max (-r) (airyZ n)
            have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
              (s := Icc lo hi) (f := airyAi)
              (C := 10 * (1 + r) ^ (1 / 4 : ℝ))
              (fun t _ => (hasDerivAt_airyAi t).differentiableAt)
              (fun t ht => by
                rw [(hasDerivAt_airyAi t).deriv, Real.norm_eq_abs]
                have ht_neg : t ≤ 0 := by
                  have : hi ≤ 0 := max_le (by linarith) (airyZ_neg n).le
                  exact ht.2.trans this
                have ht_abs : |t| ≤ r + 1 := by
                  rw [abs_of_nonpos ht_neg]
                  have hlo_ge : -(r + 1) ≤ lo := by
                    refine le_min (by linarith) ?_
                    have h1_b := abs_le.mp h1.le
                    linarith [h1_b.1, h1_b.2]
                  linarith [ht.1]
                have hb_d := (airyAi_and_deriv_neg_bounds ht_neg).2
                refine hb_d.trans ?_
                have h16 : 1 + |t| ≤ 16 * (1 + r) := by linarith
                calc 5 * (1 + |t|) ^ (1 / 4 : ℝ)
                    ≤ 5 * (16 * (1 + r)) ^ (1 / 4 : ℝ) :=
                      mul_le_mul_of_nonneg_left
                        (Real.rpow_le_rpow (by positivity) h16 (by norm_num)) (by norm_num)
                  _ = 5 * (16 ^ (1 / 4 : ℝ) * (1 + r) ^ (1 / 4 : ℝ)) := by
                      rw [Real.mul_rpow (by norm_num) (by positivity)]
                  _ = 10 * (1 + r) ^ (1 / 4 : ℝ) := by
                      have h16_4 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
                        rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num,
                          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
                        norm_num
                      rw [h16_4]; ring)
              (convex_Icc lo hi)
              ⟨min_le_right _ _, le_max_right _ _⟩
              ⟨min_le_left _ _, le_max_left _ _⟩
            have hz_zero : airyAi (airyZ n) = 0 := airyAi_airyZero (n + 1)
            rw [hz_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
            have hprod := hAi_lb.trans hmvt
            have hrpos14 : 0 < 10 * (1 + r) ^ (1 / 4 : ℝ) := by positivity
            rw [← div_le_iff₀' hrpos14] at hprod
            have hrhs_eq : ((1 / 10 : ℝ) * (1 + r) ^ (-(1 / 4 : ℝ))) /
                (10 * (1 + r) ^ (1 / 4 : ℝ)) =
                (1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ)) := by
              have hp : (1 + r) ^ (1 / 4 : ℝ) ≠ 0 :=
                (Real.rpow_pos_of_pos (by positivity) _).ne'
              rw [show -(1 / 2 : ℝ) = -(1 / 4 : ℝ) + -(1 / 4 : ℝ) by norm_num,
                Real.rpow_add (by positivity : 0 < 1 + r),
                Real.rpow_neg (by positivity : 0 ≤ 1 + r)]
              field_simp [hp]
              ring
            rwa [hrhs_eq] at hprod
        have hfront : ∀ ζ ∈ frontier (ball (0 : ℂ) r), ‖Q ζ‖ ≤ K_tot / r := by
          intro ζ hζ
          rw [frontier_ball (0 : ℂ) hr_pos.ne', mem_sphere_zero_iff_norm] at hζ
          have hAi_good := hgood ζ hζ
          have hAi_pos : 0 < ‖airyAiC ζ‖ ^ 2 := by
            refine lt_of_lt_of_le ?_ hAi_good
            have := airyEnv_pos ζ
            have : 0 < (1 + r) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
            positivity
          have hAi_ne : airyAiC ζ ≠ 0 := fun h0 => by simp [h0] at hAi_pos
          have hQ_eq : Q ζ = (F ζ - S ζ) / airyAiC ζ ^ 2 := by
            have hno : ¬ ∃ m : ℕ, ζ = (airyZ m : ℂ) := by
              rintro ⟨m, rfl⟩; exact hAi_ne (airyAiC_airyZ m)
            simp only [Q, hno, ↓reduceDIte]
            rfl
          have hF_div : ‖F ζ / airyAiC ζ ^ 2‖ ≤ (50 * π * C_half) / r := by
            have henv_ζ_pos : 0 < airyEnv ζ := airyEnv_pos ζ
            have hz2 := hChalf ζ
            change ‖ζ ^ 2 * F ζ‖ ≤ C_half * (1 + ‖ζ‖) ^ (1 / 2 : ℝ) * airyEnv ζ at hz2
            rw [norm_mul, norm_pow, hζ] at hz2
            have hF_ub : ‖F ζ‖ ≤ C_half * (1 + r) ^ (1 / 2 : ℝ) * airyEnv ζ / r ^ 2 := by
              rw [le_div_iff₀ (sq_pos_of_pos hr_pos)]
              linarith
            rw [norm_div, norm_pow]
            calc ‖F ζ‖ / ‖airyAiC ζ‖ ^ 2
                ≤ (C_half * (1 + r) ^ (1 / 2 : ℝ) * airyEnv ζ / r ^ 2) /
                    (1 / (25 * π) * (1 + r) ^ (-(1 / 2 : ℝ)) * airyEnv ζ) := by
                  refine div_le_div₀ (by positivity) hF_ub ?_ hAi_good
                  have : 0 < (1 + r) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
                  positivity
              _ = 25 * π * C_half * ((1 + r) / r ^ 2) := by
                  have he_ne : (airyEnv ζ) ≠ 0 := (airyEnv_pos ζ).ne'
                  have hr_ne : r ^ 2 ≠ 0 := (sq_pos_of_pos hr_pos).ne'
                  have hpi_ne : π ≠ 0 := Real.pi_pos.ne'
                  have hr12 : (1 + r) ^ (1 / 2 : ℝ) / (1 + r) ^ (-(1 / 2 : ℝ)) = 1 + r := by
                    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + r), div_inv_eq_mul,
                      ← Real.rpow_add (by positivity : 0 < 1 + r)]
                    norm_num
                  calc (C_half * (1 + r) ^ (1 / 2 : ℝ) * airyEnv ζ / r ^ 2) /
                        (1 / (25 * π) * (1 + r) ^ (-(1 / 2 : ℝ)) * airyEnv ζ)
                      = 25 * π * C_half *
                          ((1 + r) ^ (1 / 2 : ℝ) / (1 + r) ^ (-(1 / 2 : ℝ))) / r ^ 2 := by
                        field_simp [he_ne, hr_ne, hpi_ne]
                    _ = 25 * π * C_half * ((1 + r) / r ^ 2) := by rw [hr12]; ring
              _ ≤ (50 * π * C_half) / r := by
                  have h1r : (1 + r) / r ^ 2 ≤ 2 / r := by
                    rw [div_le_div_iff₀ (sq_pos_of_pos hr_pos) hr_pos]
                    nlinarith
                  calc 25 * π * C_half * ((1 + r) / r ^ 2)
                      ≤ 25 * π * C_half * (2 / r) :=
                        mul_le_mul_of_nonneg_left h1r (by positivity)
                    _ = (50 * π * C_half) / r := by ring
          have hS_div : ‖S ζ / airyAiC ζ ^ 2‖ ≤ M_good / r := by
            have hdiv_sum : HasSum (fun n : ℕ => airyHermiteTerm F n ζ / airyAiC ζ ^ 2)
                (S ζ / airyAiC ζ ^ 2) := by
              simpa [div_eq_mul_inv] using (hS_hasSum ζ).mul_right ((airyAiC ζ ^ 2)⁻¹)
            have hterm_le : ∀ n : ℕ, ‖airyHermiteTerm F n ζ / airyAiC ζ ^ 2‖ ≤
                ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r := by
              intro n
              have hdist_ζ : |-r - airyZ n| ≤ ‖ζ - (airyZ n : ℂ)‖ := by
                have htri : |‖ζ‖ - ‖(airyZ n : ℂ)‖| ≤ ‖ζ - (airyZ n : ℂ)‖ :=
                  abs_norm_sub_norm_le ζ (airyZ n : ℂ)
                rw [hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZ_neg n)] at htri
                have heq_abs : |-r - airyZ n| = |r - (-airyZ n)| := by
                  rw [← abs_neg]; ring_nf
                rwa [heq_abs]
              have hd_pos : 0 < ‖ζ - (airyZ n : ℂ)‖ :=
                lt_of_lt_of_le (by positivity) ((hdist_zeros n).trans hdist_ζ)
              have hne_ζ : ζ ≠ (airyZ n : ℂ) := sub_ne_zero.mp (norm_pos_iff.mp hd_pos)
              have hsimp : airyHermiteTerm F n ζ / airyAiC ζ ^ 2 =
                  (cG n : ℂ) / (ζ - (airyZ n : ℂ)) ^ 2 +
                    (cF n : ℂ) / (ζ - (airyZ n : ℂ)) := by
                unfold airyHermiteTerm airySeedG airySeedF
                rw [airyCardinal_of_ne n hne_ζ]
                have hAi2_ne : airyAiC ζ ^ 2 ≠ 0 := pow_ne_zero 2 hAi_ne
                have hsub_ne : ζ - (airyZ n : ℂ) ≠ 0 := sub_ne_zero.mpr hne_ζ
                field_simp [hAi2_ne, hsub_ne]
                rfl
              rw [hsimp]
              have hinv_le : max (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ (‖ζ - (airyZ n : ℂ)‖)⁻¹ ≤
                  (2 + 80000 * |airyZ n| ^ 2) / r := by
                by_cases hcase : |airyZ n| ≤ r / 2
                · have hd_ge : r / 2 ≤ ‖ζ - (airyZ n : ℂ)‖ := by
                    have htri : ‖ζ‖ - ‖(airyZ n : ℂ)‖ ≤ ‖ζ - (airyZ n : ℂ)‖ :=
                      norm_sub_norm_le ζ (airyZ n : ℂ)
                    rw [hζ, Complex.norm_real, Real.norm_eq_abs] at htri
                    linarith
                  have hi1 : (‖ζ - (airyZ n : ℂ)‖)⁻¹ ≤ 2 / r := by
                    rw [← one_div, div_le_div_iff₀ hd_pos hr_pos]
                    linarith
                  have hi2 : (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ ≤ 2 / r := by
                    have hge1 : 1 ≤ ‖ζ - (airyZ n : ℂ)‖ := by linarith
                    have hsq_ge : ‖ζ - (airyZ n : ℂ)‖ ≤ ‖ζ - (airyZ n : ℂ)‖ ^ 2 := by nlinarith
                    exact (inv_anti₀ hd_pos hsq_ge).trans hi1
                  exact (max_le hi2 hi1).trans
                    (div_le_div_of_nonneg_right (by linarith [sq_nonneg |airyZ n|]) hr_pos.le)
                · push Not at hcase
                  have hd_lb := (hdist_zeros n).trans hdist_ζ
                  have h100 : (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ ≤ 10000 * (1 + r) := by
                    have hsq : ((1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ))) ^ 2 ≤
                        ‖ζ - (airyZ n : ℂ)‖ ^ 2 :=
                      pow_le_pow_left₀ (by positivity) hd_lb 2
                    have hlhs : ((1 / 100) * (1 + r) ^ (-(1 / 2 : ℝ))) ^ 2 =
                        (10000 * (1 + r))⁻¹ := by
                      rw [mul_pow, ← Real.rpow_natCast ((1 + r) ^ _),
                        ← Real.rpow_mul (by positivity : 0 ≤ 1 + r)]
                      have hexp_eq : -(1 / 2 : ℝ) * (2 : ℕ) = -1 := by norm_num
                      rw [hexp_eq, Real.rpow_neg_one, mul_inv]
                      norm_num
                    rw [hlhs] at hsq
                    exact (inv_le_inv₀ (sq_pos_of_pos hd_pos) (by positivity)).mpr hsq |>.trans_eq
                      (inv_inv _)
                  have h100_1 : (‖ζ - (airyZ n : ℂ)‖)⁻¹ ≤ 10000 * (1 + r) := by
                    by_cases hd1 : 1 ≤ ‖ζ - (airyZ n : ℂ)‖
                    · exact (inv_le_one_of_one_le₀ hd1).trans (by linarith)
                    · push Not at hd1
                      have hsq_le : ‖ζ - (airyZ n : ℂ)‖ ^ 2 ≤ ‖ζ - (airyZ n : ℂ)‖ := by nlinarith
                      exact (inv_anti₀ (sq_pos_of_pos hd_pos) hsq_le).trans h100
                  have hbound_r : 10000 * (1 + r) ≤ (2 + 80000 * |airyZ n| ^ 2) / r := by
                    rw [le_div_iff₀ hr_pos]
                    have hA2 : r ^ 2 < 4 * |airyZ n| ^ 2 := by nlinarith
                    nlinarith
                  exact (max_le h100 h100_1).trans hbound_r
              calc ‖(cG n : ℂ) / (ζ - (airyZ n : ℂ)) ^ 2 + (cF n : ℂ) / (ζ - (airyZ n : ℂ))‖
                  ≤ ‖(cG n : ℂ) / (ζ - (airyZ n : ℂ)) ^ 2‖ +
                      ‖(cF n : ℂ) / (ζ - (airyZ n : ℂ))‖ := norm_add_le _ _
                _ = |cG n| * (‖ζ - (airyZ n : ℂ)‖ ^ 2)⁻¹ +
                      |cF n| * (‖ζ - (airyZ n : ℂ)‖)⁻¹ := by
                    simp [div_eq_mul_inv, Complex.norm_real]
                _ ≤ |cG n| * ((2 + 80000 * |airyZ n| ^ 2) / r) +
                      |cF n| * ((2 + 80000 * |airyZ n| ^ 2) / r) :=
                    add_le_add
                      (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hinv_le) (abs_nonneg _))
                      (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hinv_le) (abs_nonneg _))
                _ = ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r := by dsimp [cAbs]; ring
            rw [← hdiv_sum.tsum_eq]
            have hsum_r : Summable (fun n : ℕ => ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r) :=
              hsum_good.div_const r
            calc ‖∑' n : ℕ, airyHermiteTerm F n ζ / airyAiC ζ ^ 2‖
                ≤ ∑' n : ℕ, ‖airyHermiteTerm F n ζ / airyAiC ζ ^ 2‖ :=
                  norm_tsum_le_tsum_norm
                    (hsum_r.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le)
              _ ≤ ∑' n : ℕ, ((2 + 80000 * |airyZ n| ^ 2) * cAbs n) / r :=
                  Summable.tsum_le_tsum hterm_le
                    (hsum_r.of_nonneg_of_le (fun _ => norm_nonneg _) hterm_le) hsum_r
              _ = M_good / r := tsum_div_const
          rw [hQ_eq, sub_div]
          calc ‖F ζ / airyAiC ζ ^ 2 - S ζ / airyAiC ζ ^ 2‖
              ≤ ‖F ζ / airyAiC ζ ^ 2‖ + ‖S ζ / airyAiC ζ ^ 2‖ := norm_sub_le _ _
            _ ≤ (50 * π * C_half) / r + M_good / r := add_le_add hF_div hS_div
            _ = K_tot / r := by dsimp [K_tot]; ring
        have hmax_mod := Complex.norm_le_of_forall_mem_frontier_norm_le
          isBounded_ball hQ_diff.differentiableOn.diffContOnCl hfront (subset_closure hz₀_in)
        refine hmax_mod.trans ?_
        have hk_K : ⌈K_tot / δ⌉₊ + 1 ≤ k := (le_max_right _ _).trans (le_max_right _ _)
        have hKr : K_tot / δ ≤ r := by
          calc K_tot / δ ≤ (⌈K_tot / δ⌉₊ : ℝ) := Nat.le_ceil _
            _ ≤ (k : ℝ) := by exact_mod_cast (Nat.le_of_succ_le hk_K)
            _ ≤ r := hr_lo
        rw [div_le_iff₀ hr_pos]
        have := (div_le_iff₀ hδ).mp hKr
        linarith
      exact norm_le_zero_iff.mp hnorm_zero
    intro z
    have h0 : Δ z = 0 := by rw [hΔ_eq_mul z, hQ_zero z, mul_zero]
    exact (sub_eq_zero.mp h0).symm
  exact ⟨fun z => hS_eq_F z ▸ hS_hasSum z, hcF_hasSum_zero, hball_maj⟩

/-- **Lemma `lem:al-hermite-approx`** (`ce_airy_lp_proofs.tex` lines 803–869):
for real-on-`ℝ` `F ∈ 𝒢 ∩ 𝓢(ℝ)`, the Hermite--Airy expansion `(eq:al-hermite)` holds on all of `ℂ`,
`∑ F'(a_n)/Ai'(a_n)² = 0`, and the partial sums `F_N ∈ ℛ_Ai^gen` satisfy (a)–(d). -/
theorem lem_al_hermite_approx {F : ℂ → ℂ} (hF : InAiryClass F)
    (hF_im : ∀ u : ℝ, (F (u : ℂ)).im = 0)
    (hF_schwartz : ∃ S_F : SchwartzMap ℝ ℝ, ∀ u : ℝ, S_F u = (F (u : ℂ)).re) :
    (∀ z : ℂ, HasSum (fun n : ℕ => airyHermiteTerm F n z) (F z)) ∧
    HasSum (fun n : ℕ => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2) 0 ∧
    (∀ N : ℕ, InGenRationalAiry (airyHermitePartialSum F N) ∧
      airyBetaInf (airyHermitePartialSum F N) =
        -∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 ∧
      airyBetaPlus (airyHermitePartialSum F N) =
        ∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2) ∧
    (∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn (fun N z => airyHermitePartialSum F N z) F atTop K) ∧
    Tendsto (fun N : ℕ => ∫ u : ℝ, ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖)
      atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => ∫ u : ℝ, (airyHermitePartialSum F N (u : ℂ)).re)
      atTop (𝓝 (∫ u : ℝ, (F (u : ℂ)).re)) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ u : ℝ, u ≤ 0 →
      (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re - (airyHermitePartialSum F N (u : ℂ)).re| < ε) ∧
    (∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ y : ℝ, 0 ≤ y →
      (1 + y) ^ (5 / 2 : ℝ) *
        |airyLaplace (fun u => (F (u : ℂ)).re) y -
          airyLaplace (fun u => (airyHermitePartialSum F N (u : ℂ)).re) y| < ε) ∧
    Tendsto (fun N : ℕ => airyBetaInf (airyHermitePartialSum F N)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ => airyBetaPlus (airyHermitePartialSum F N)) atTop (𝓝 0) := by
  obtain ⟨S_F, hSF⟩ := hF_schwartz
  have hderiv_SF : ∀ u : ℝ, deriv (S_F : ℝ → ℝ) u = (deriv F (u : ℂ)).re := fun u => by
    have h1 := iteratedDeriv_re_of_differentiable hF.1 1 u
    rw [iteratedDeriv_one, iteratedDeriv_one] at h1
    have hfun : (fun t : ℝ => (F (t : ℂ)).re) = (S_F : ℝ → ℝ) := funext fun t => (hSF t).symm
    rwa [hfun] at h1
  obtain ⟨hF_hasSum, hcF_hasSum_zero, hball_maj⟩ :=
    airyHermite_quadrature_and_expansion hF hF_im hSF
  set cG : ℕ → ℝ := fun n => (F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cF : ℕ → ℝ := fun n => (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2
  set cAbs : ℕ → ℝ := fun n => |cG n| + |cF n|
  have hcoeff_summable : ∀ M : ℕ, Summable (fun n : ℕ => |airyZ n| ^ M * cAbs n) :=
    airyHermite_coeff_summable hSF hderiv_SF
  -- Partial sums lie in `InGenRationalAiry` with exact `β_∞` and `β_+`
  have hpartial_coeffs : ∀ N : ℕ,
      InGenRationalAiry (airyHermitePartialSum F N) ∧
      airyBetaInf (airyHermitePartialSum F N) =
        -∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 ∧
      airyBetaPlus (airyHermitePartialSum F N) =
        ∑ n ∈ Finset.range N, (deriv F (airyZ n : ℂ)).re / airyAi' (airyZ n) ^ 2 := by
    intro N
    have hterm_c : ∀ n : ℕ, HasGenRationalAiryCoeffs (airyHermiteTerm F n) (-cF n) 0 := fun n => by
      change HasGenRationalAiryCoeffs
        (fun z => (cG n : ℂ) * airySeedG n z + (cF n : ℂ) * airySeedF n z) (-cF n) 0
      have h1 := (hasGenRationalAiryCoeffs_airySeedG n).smul (cG n)
      have h2 := (hasGenRationalAiryCoeffs_airySeedF n).smul (cF n)
      have h3 := h1.add h2
      simpa only [mul_zero, zero_add, mul_neg, mul_one] using h3
    have hsum_c := HasGenRationalAiryCoeffs.finset_sum (Finset.range N)
      (fun n => airyHermiteTerm F n) (fun n => -cF n) (fun _ => 0) (fun n _ => hterm_c n)
    have hfun : (fun z => ∑ n ∈ Finset.range N, airyHermiteTerm F n z) =
        airyHermitePartialSum F N := rfl
    rw [hfun, Finset.sum_neg_distrib, Finset.sum_const_zero] at hsum_c
    obtain ⟨_, _, hb_inf, hb_plus⟩ := hsum_c.beta_eq
    exact ⟨⟨_, _, hsum_c⟩, by dsimp [cF] at hb_inf; linarith, by dsimp [cF] at hb_plus; linarith⟩
  -- Summable majorant tails (`k + N` indexing matching `sum_add_tsum_nat_add`)
  obtain ⟨C_L, hCL_pos, hCL_bd⟩ := airySeed_l1_and_laplace_bounds
  set C_L1 : ℝ := max C_L 1
  have hCL_le_CL1 : C_L ≤ C_L1 := le_max_left _ _
  have hwL_sum : Summable (fun n : ℕ => C_L1 * (1 + |airyZ n|) * cAbs n) := by
    have hs0 := (hcoeff_summable 0).mul_left C_L1
    have hs1 := (hcoeff_summable 1).mul_left C_L1
    refine (hs0.add hs1).congr fun n => ?_
    simp [pow_zero, pow_one]; ring
  have hwNeg_sum : Summable (fun n : ℕ => 400 * |airyZ n| ^ 2 * cAbs n) := by
    simpa [mul_assoc] using (hcoeff_summable 2).mul_left 400
  have htail_zero : ∀ {w : ℕ → ℝ}, Summable w →
      Tendsto (fun N : ℕ => ∑' k : ℕ, w (k + N)) atTop (𝓝 0) := by
    intro w hw
    have h1 := hw.hasSum.tendsto_sum_nat
    have h2 : ∀ N : ℕ, ∑' k : ℕ, w (k + N) = (∑' n : ℕ, w n) - ∑ n ∈ Finset.range N, w n :=
      fun N => eq_sub_iff_add_eq'.mpr (hw.sum_add_tsum_nat_add N)
    have hsub := h1.const_sub (∑' n : ℕ, w n)
    rw [sub_self] at hsub
    exact hsub.congr fun N => (h2 N).symm
  -- Term L¹ and Laplace bounds
  have hterm_int_and_l1 : ∀ n : ℕ,
      Integrable (fun u : ℝ => airyHermiteTerm F n (u : ℂ)) ∧
      (∫ u : ℝ, ‖airyHermiteTerm F n (u : ℂ)‖) ≤ C_L1 * (1 + |airyZ n|) * cAbs n := by
    intro n
    have hint : Integrable (fun u : ℝ => airyHermiteTerm F n (u : ℂ)) := by
      unfold airyHermiteTerm
      exact ((airySeedG_inAiryClass n).2.1.const_mul _).add
        ((airySeedF_inAiryClass n).2.1.const_mul _)
    refine ⟨hint, ?_⟩
    obtain ⟨hg1, hf1, _, _⟩ := hCL_bd n
    have hpt : ∀ u : ℝ, ‖airyHermiteTerm F n (u : ℂ)‖ ≤
        |cG n| * ‖airySeedG n (u : ℂ)‖ + |cF n| * ‖airySeedF n (u : ℂ)‖ := fun u => by
      unfold airyHermiteTerm
      calc ‖(cG n : ℂ) * airySeedG n (u : ℂ) + (cF n : ℂ) * airySeedF n (u : ℂ)‖
          ≤ ‖(cG n : ℂ) * airySeedG n (u : ℂ)‖ + ‖(cF n : ℂ) * airySeedF n (u : ℂ)‖ :=
            norm_add_le _ _
        _ = |cG n| * ‖airySeedG n (u : ℂ)‖ + |cF n| * ‖airySeedF n (u : ℂ)‖ := by
            simp [Complex.norm_real]
    have hmono := integral_mono hint.norm
      (((airySeedG_inAiryClass n).2.1.norm.const_mul |cG n|).add
        ((airySeedF_inAiryClass n).2.1.norm.const_mul |cF n|)) hpt
    change (∫ x : ℝ, ‖airyHermiteTerm F n (x : ℂ)‖) ≤
      ∫ x : ℝ, |cG n| * ‖airySeedG n (x : ℂ)‖ + |cF n| * ‖airySeedF n (x : ℂ)‖ at hmono
    rw [integral_add ((airySeedG_inAiryClass n).2.1.norm.const_mul _)
      ((airySeedF_inAiryClass n).2.1.norm.const_mul _),
      integral_const_mul, integral_const_mul, hg1, mul_one] at hmono
    refine hmono.trans ?_
    have hf1' : (∫ u : ℝ, ‖airySeedF n (u : ℂ)‖) ≤ C_L1 * |airyZ n| :=
      hf1.trans (mul_le_mul_of_nonneg_right hCL_le_CL1 (abs_nonneg _))
    dsimp [cAbs]
    have hp_nn : 0 ≤ C_L1 * |airyZ n| * |cG n| := by positivity
    nlinarith [abs_nonneg (cG n), abs_nonneg (cF n), abs_nonneg (airyZ n),
      le_max_right C_L 1]
  have hFN_int : ∀ N : ℕ, Integrable (fun u : ℝ => airyHermitePartialSum F N (u : ℂ)) := by
    intro N
    induction N with
    | zero =>
      have hz : (fun u : ℝ => airyHermitePartialSum F 0 (u : ℂ)) = fun _ => 0 := by
        ext u; simp [airyHermitePartialSum]
      rw [hz]; exact integrable_zero _ _ _
    | succ N ih =>
      have hs : (fun u : ℝ => airyHermitePartialSum F (N + 1) (u : ℂ)) =
          fun u : ℝ => airyHermitePartialSum F N (u : ℂ) + airyHermiteTerm F N (u : ℂ) := by
        ext u; simp [airyHermitePartialSum, Finset.sum_range_succ]
      rw [hs]; exact ih.add (hterm_int_and_l1 N).1
  have hterm_lap_bd : ∀ n : ℕ, ∀ y : ℝ, 0 ≤ y →
      |airyLaplace (fun u => (airyHermiteTerm F n (u : ℂ)).re) y| ≤
        C_L1 * (1 + |airyZ n|) * cAbs n * (1 + y) ^ (-(5 / 2 : ℝ)) := by
    intro n y hy
    obtain ⟨_, _, hgl, hfl⟩ := hCL_bd n
    have hre : ∀ u : ℝ,
        (airyHermiteTerm F n (u : ℂ)).re * Real.exp (y * u) =
        cG n * ((airySeedG n (u : ℂ)).re * Real.exp (y * u)) +
          cF n * ((airySeedF n (u : ℂ)).re * Real.exp (y * u)) := fun u => by
      change (((cG n : ℂ) * airySeedG n (u : ℂ) + (cF n : ℂ) * airySeedF n (u : ℂ)).re) *
        Real.exp (y * u) = _
      simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      ring
    have hlin : airyLaplace (fun u => (airyHermiteTerm F n (u : ℂ)).re) y =
        cG n * airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y +
          cF n * airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y := by
      unfold airyLaplace
      simp_rw [hre]
      have hiG : Integrable (fun u : ℝ => (airySeedG n (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedG_inAiryClass n).integrable_exp_nonneg hy
      have hiF : Integrable (fun u : ℝ => (airySeedF n (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedF_inAiryClass n).integrable_exp_nonneg hy
      rw [integral_add (hiG.const_mul _) (hiF.const_mul _),
        integral_const_mul, integral_const_mul]
      ring
    rw [hlin]
    have hg_le := (hgl y hy).trans
      (mul_le_mul_of_nonneg_right hCL_le_CL1 (by positivity))
    have hf_le := (hfl y hy).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCL_le_CL1 (abs_nonneg _)) (by positivity))
    calc |cG n * airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y +
          cF n * airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y|
        ≤ |cG n| * |airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y| +
            |cF n| * |airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y| := by
          simpa [abs_mul] using abs_add_le
            (cG n * airyLaplace (fun u => (airySeedG n (u : ℂ)).re) y)
            (cF n * airyLaplace (fun u => (airySeedF n (u : ℂ)).re) y)
      _ ≤ |cG n| * (C_L1 * (1 + y) ^ (-(5 / 2 : ℝ))) +
            |cF n| * (C_L1 * |airyZ n| * (1 + y) ^ (-(5 / 2 : ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left hg_le (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hf_le (abs_nonneg _))
      _ ≤ C_L1 * (1 + |airyZ n|) * cAbs n * (1 + y) ^ (-(5 / 2 : ℝ)) := by
          dsimp [cAbs]
          have hp : 0 ≤ (1 + y) ^ (-(5 / 2 : ℝ)) := by positivity
          have hp1 : 0 ≤ C_L1 * |airyZ n| * |cG n| := by positivity
          have hp2 : 0 ≤ C_L1 * |cF n| := by positivity
          have h1 : |cG n| * C_L1 + |cF n| * (C_L1 * |airyZ n|) ≤
              C_L1 * (1 + |airyZ n|) * (|cG n| + |cF n|) := by linarith
          calc |cG n| * (C_L1 * (1 + y) ^ (-(5 / 2 : ℝ))) +
                |cF n| * (C_L1 * |airyZ n| * (1 + y) ^ (-(5 / 2 : ℝ)))
              = (|cG n| * C_L1 + |cF n| * (C_L1 * |airyZ n|)) * (1 + y) ^ (-(5 / 2 : ℝ)) := by ring
            _ ≤ (C_L1 * (1 + |airyZ n|) * (|cG n| + |cF n|)) * (1 + y) ^ (-(5 / 2 : ℝ)) :=
                mul_le_mul_of_nonneg_right h1 hp
  -- Tail representation `F z - airyHermitePartialSum F N z = ∑' k, airyHermiteTerm F (k + N) z`
  have hrem_eq : ∀ N : ℕ, ∀ z : ℂ,
      F z - airyHermitePartialSum F N z = ∑' k : ℕ, airyHermiteTerm F (k + N) z := by
    intro N z
    have hsplit := (hF_hasSum z).summable.sum_add_tsum_nat_add N
    rw [(hF_hasSum z).tsum_eq] at hsplit
    unfold airyHermitePartialSum
    exact (eq_sub_iff_add_eq'.mpr hsplit).symm
  -- L¹ convergence of `F - F_N` to `0`
  have hl1_tendsto : Tendsto (fun N : ℕ =>
      ∫ u : ℝ, ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => integral_nonneg fun _ => norm_nonneg _) (fun N => ?_)
      (htail_zero hwL_sum)
    simp_rw [hrem_eq N]
    have hfn_int : ∀ k : ℕ, Integrable (fun u : ℝ => airyHermiteTerm F (k + N) (u : ℂ)) :=
      fun k => (hterm_int_and_l1 (k + N)).1
    have hnorm_sum : Summable (fun k : ℕ => ∫ u : ℝ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      refine (hwL_sum.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun k => (hterm_int_and_l1 (k + N)).2)
    have hhas := (integral_tsum_of_summable_integral_norm
      (F := fun (k : ℕ) (u : ℝ) => ‖airyHermiteTerm F (k + N) (u : ℂ)‖)
      (fun k => (hfn_int k).norm)
      (by
        refine hnorm_sum.congr fun k => ?_
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)])).symm
    have hpt_sum : ∀ u : ℝ, Summable (fun k : ℕ => ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      intro u
      obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj (max |u| 1) (le_max_right _ _)
      have hu_mem : (u : ℂ) ∈ closedBall (0 : ℂ) (max |u| 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact le_max_left _ _
      exact (hu_R.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun k => hbd_R (k + N) (u : ℂ) hu_mem)
    have htsum_norm_int : Integrable (fun u : ℝ => ∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      refine ⟨aestronglyMeasurable_of_tendsto_ae atTop
        (fun M => Finset.aestronglyMeasurable_sum (Finset.range M)
          fun k _ => (hfn_int k).norm.aestronglyMeasurable)
        (Eventually.of_forall fun u =>
          (hpt_sum u).hasSum.tendsto_sum_nat.congr fun M =>
            (Finset.sum_apply u (Finset.range M)
              (fun k (a : ℝ) => ‖airyHermiteTerm F (k + N) (a : ℂ)‖)).symm), ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun _ => tsum_nonneg fun _ => norm_nonneg _)]
      have heq_ofReal : ∀ u : ℝ,
          ENNReal.ofReal (∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) =
            ∑' k : ℕ, ENNReal.ofReal ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
        fun u => ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hpt_sum u)
      simp_rw [heq_ofReal]
      rw [lintegral_tsum fun k => (hfn_int k).norm.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
      have hterm_lint : ∀ k : ℕ,
          (∫⁻ u : ℝ, ENNReal.ofReal ‖airyHermiteTerm F (k + N) (u : ℂ)‖) =
            ENNReal.ofReal (∫ u : ℝ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖) :=
        fun k => (ofReal_integral_eq_lintegral_ofReal (hfn_int k).norm
          (Eventually.of_forall fun _ => norm_nonneg _)).symm
      simp_rw [hterm_lint]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => integral_nonneg fun _ => norm_nonneg _) hnorm_sum]
      exact ENNReal.ofReal_lt_top
    have hrem_int : Integrable (fun u : ℝ => ‖∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      have hsub_int : Integrable (fun u : ℝ => F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)) :=
        hF.2.1.sub (hFN_int N)
      simpa [hrem_eq N] using hsub_int.norm
    calc (∫ u : ℝ, ‖∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)‖)
        ≤ ∫ u : ℝ, ∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
          integral_mono hrem_int htsum_norm_int
            (fun u => norm_tsum_le_tsum_norm (hpt_sum u))
      _ = ∑' k : ℕ, ∫ u : ℝ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖ := hhas
      _ ≤ ∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N) :=
          Summable.tsum_le_tsum (fun k => (hterm_int_and_l1 (k + N)).2)
            hnorm_sum (hwL_sum.comp_injective (add_left_injective N))
  -- Assemble all 10 conjuncts
  refine ⟨hF_hasSum, hcF_hasSum_zero, hpartial_coeffs, ?_, hl1_tendsto, ?_, ?_, ?_, ?_, ?_⟩
  · -- Uniform convergence on compact `K ⊂ ℂ`
    intro K hK
    obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    set R1 : ℝ := max R 1
    obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj R1 (le_max_right _ _)
    have hunif := tendstoUniformlyOn_tsum_nat hu_R
      (f := fun n z => airyHermiteTerm F n z) (s := closedBall (0 : ℂ) R1)
      (fun n z hz => hbd_R n z hz)
    have hfun : (fun z => ∑' n : ℕ, airyHermiteTerm F n z) = F :=
      funext fun z => (hF_hasSum z).tsum_eq
    rw [hfun] at hunif
    exact hunif.mono (hKR.trans (closedBall_subset_closedBall (le_max_left R 1)))
  · -- `∫ F_N → ∫ F`
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hl1_tendsto ε hε] with N hN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at hN
    rw [Real.dist_eq, abs_sub_comm]
    have hF_re_int : Integrable (fun u : ℝ => (F (u : ℂ)).re) := hF.2.1.re
    have hFN_re_int : Integrable (fun u : ℝ => (airyHermitePartialSum F N (u : ℂ)).re) :=
      (hFN_int N).re
    rw [← integral_sub hF_re_int hFN_re_int]
    refine (le_trans abs_integral_le_integral_abs
      (integral_mono (hF_re_int.sub hFN_re_int).abs
        (hF.2.1.sub (hFN_int N)).norm fun u => ?_)).trans_lt hN
    change |(F (u : ℂ)).re - (airyHermitePartialSum F N (u : ℂ)).re| ≤
      ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  · -- (b) Negative-axis `(1 + |u|)^{3/2} |F(u) - F_N(u)| → 0`
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (htail_zero hwNeg_sum) ε hε] with N hN
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg fun _ => by positivity)] at hN
    intro u hu
    have hpt_norm_sum : Summable (fun k : ℕ => ‖airyHermiteTerm F (k + N) (u : ℂ)‖) := by
      obtain ⟨u_R, hu_R, hbd_R⟩ := hball_maj (max |u| 1) (le_max_right _ _)
      have hu_mem : (u : ℂ) ∈ closedBall (0 : ℂ) (max |u| 1) := by
        rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs]
        exact le_max_left _ _
      exact (hu_R.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => norm_nonneg _) (fun k => hbd_R (k + N) (u : ℂ) hu_mem)
    have hterm_w : ∀ k : ℕ,
        (1 + |u|) ^ (3 / 2 : ℝ) * ‖airyHermiteTerm F (k + N) (u : ℂ)‖ ≤
          400 * |airyZ (k + N)| ^ 2 * cAbs (k + N) := by
      intro k
      set m := k + N
      obtain ⟨hwf, hwg, _, _⟩ := airySeed_neg_weighted_bounds m hu
      have hA_gt2 : 2 < |airyZ m| := two_lt_abs_airyZ m
      have hA_32_le : |airyZ m| ^ (3 / 2 : ℝ) ≤ |airyZ m| ^ 2 := by
        rw [show |airyZ m| ^ 2 = |airyZ m| ^ (2 : ℝ) by rw [Real.rpow_two]]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hnG : ‖airySeedG m (u : ℂ)‖ = (airySeedG m (u : ℂ)).re := by
        rw [airySeedG_ofReal, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sq_nonneg _), Complex.ofReal_re]
      have hnF : ‖airySeedF m (u : ℂ)‖ = |(airySeedF m (u : ℂ)).re| := by
        rw [airySeedF_ofReal, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      have htri_m : ‖airyHermiteTerm F m (u : ℂ)‖ ≤
          |cG m| * ‖airySeedG m (u : ℂ)‖ + |cF m| * ‖airySeedF m (u : ℂ)‖ := by
        unfold airyHermiteTerm
        calc ‖(cG m : ℂ) * airySeedG m (u : ℂ) + (cF m : ℂ) * airySeedF m (u : ℂ)‖
            ≤ ‖(cG m : ℂ) * airySeedG m (u : ℂ)‖ + ‖(cF m : ℂ) * airySeedF m (u : ℂ)‖ :=
              norm_add_le _ _
          _ = |cG m| * ‖airySeedG m (u : ℂ)‖ + |cF m| * ‖airySeedF m (u : ℂ)‖ := by
              simp [Complex.norm_real]
      have hm_le : |cF m| * (240 * |airyZ m| ^ (3 / 2 : ℝ)) ≤
          |cF m| * (400 * |airyZ m| ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (abs_nonneg _)
      calc (1 + |u|) ^ (3 / 2 : ℝ) * ‖airyHermiteTerm F m (u : ℂ)‖
          ≤ (1 + |u|) ^ (3 / 2 : ℝ) *
              (|cG m| * ‖airySeedG m (u : ℂ)‖ + |cF m| * ‖airySeedF m (u : ℂ)‖) :=
            mul_le_mul_of_nonneg_left htri_m (by positivity)
        _ = |cG m| * ((1 + |u|) ^ (3 / 2 : ℝ) * (airySeedG m (u : ℂ)).re) +
              |cF m| * ((1 + |u|) ^ (3 / 2 : ℝ) * |(airySeedF m (u : ℂ)).re|) := by
            rw [hnG, hnF]; ring
        _ ≤ |cG m| * (400 * |airyZ m| ^ 2) + |cF m| * (240 * |airyZ m| ^ (3 / 2 : ℝ)) :=
            add_le_add (mul_le_mul_of_nonneg_left hwg (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hwf (abs_nonneg _))
        _ ≤ |cG m| * (400 * |airyZ m| ^ 2) + |cF m| * (400 * |airyZ m| ^ 2) := by linarith
        _ = 400 * |airyZ m| ^ 2 * cAbs m := by dsimp [cAbs]; ring
    calc (1 + |u|) ^ (3 / 2 : ℝ) * |(F (u : ℂ)).re - (airyHermitePartialSum F N (u : ℂ)).re|
        ≤ (1 + |u|) ^ (3 / 2 : ℝ) * ‖F (u : ℂ) - airyHermitePartialSum F N (u : ℂ)‖ := by
          rw [← Complex.sub_re]
          exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
      _ = (1 + |u|) ^ (3 / 2 : ℝ) * ‖∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)‖ := by
          rw [hrem_eq N]
      _ ≤ (1 + |u|) ^ (3 / 2 : ℝ) * ∑' k : ℕ, ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
          mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hpt_norm_sum) (by positivity)
      _ = ∑' k : ℕ, (1 + |u|) ^ (3 / 2 : ℝ) * ‖airyHermiteTerm F (k + N) (u : ℂ)‖ :=
          (tsum_mul_left).symm
      _ ≤ ∑' k : ℕ, 400 * |airyZ (k + N)| ^ 2 * cAbs (k + N) :=
          Summable.tsum_le_tsum hterm_w (hpt_norm_sum.mul_left _)
            (hwNeg_sum.comp_injective (add_left_injective N))
      _ < ε := hN
  · -- (c) Twisted Laplace `(1 + y)^{5/2} |ℒ_y(F) - ℒ_y(F_N)| → 0`
    obtain ⟨C_pos, hCpos_pos, hpos_J0⟩ := exists_airyAi_sq_div_le_refJ0
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp (htail_zero hwL_sum) ε hε] with N hN
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (tsum_nonneg fun _ => by positivity)] at hN
    intro y hy
    set I_Jy : ℝ := ∫ u in Ioi (0 : ℝ), (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)
    have hJ_int_y : IntegrableOn (fun u : ℝ => (airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) (Ioi 0) :=
      (integrable_airyRefJ0_mul_exp hy).integrableOn
    have hterm_y_int : ∀ m : ℕ,
        Integrable (fun u : ℝ => (airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)) ∧
        (∫ u : ℝ, ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) ≤
          (C_L1 * (1 + |airyZ m|) + C_pos * I_Jy) * cAbs m := by
      intro m
      have hiG : Integrable (fun u : ℝ => (airySeedG m (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedG_inAiryClass m).integrable_exp_nonneg hy
      have hiF : Integrable (fun u : ℝ => (airySeedF m (u : ℂ)).re * Real.exp (y * u)) :=
        (airySeedF_inAiryClass m).integrable_exp_nonneg hy
      have hre_eq : (fun u : ℝ => (airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)) =
          fun u : ℝ => cG m * ((airySeedG m (u : ℂ)).re * Real.exp (y * u)) +
            cF m * ((airySeedF m (u : ℂ)).re * Real.exp (y * u)) := by
        ext u
        change (((cG m : ℂ) * airySeedG m (u : ℂ) + (cF m : ℂ) * airySeedF m (u : ℂ)).re) *
          Real.exp (y * u) = _
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        ring
      have hint_m : Integrable (fun u : ℝ => (airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)) := by
        rw [hre_eq]; exact (hiG.const_mul _).add (hiF.const_mul _)
      refine ⟨hint_m, ?_⟩
      have hdisj0 : Disjoint (Iic (0 : ℝ)) (Ioi (0 : ℝ)) :=
        Set.disjoint_left.mpr fun _ h1 h2 => not_lt_of_ge h1 h2
      have hsplit : (∫ u : ℝ, ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) =
          (∫ u in Iic (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) +
            ∫ u in Ioi (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖ := by
        rw [← setIntegral_univ, ← Iic_union_Ioi]
        exact setIntegral_union hdisj0 measurableSet_Ioi
          hint_m.norm.integrableOn hint_m.norm.integrableOn
      have hneg_le : (∫ u in Iic (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) ≤
          C_L1 * (1 + |airyZ m|) * cAbs m := by
        have hmono := setIntegral_mono_on hint_m.norm.integrableOn
          (hterm_int_and_l1 m).1.norm.integrableOn measurableSet_Iic fun u (hu : u ≤ 0) => by
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
            have hexp1 : Real.exp (y * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
            calc |(airyHermiteTerm F m (u : ℂ)).re| * Real.exp (y * u)
                ≤ ‖airyHermiteTerm F m (u : ℂ)‖ * 1 :=
                  mul_le_mul (Complex.abs_re_le_norm _) hexp1 (Real.exp_pos _).le (norm_nonneg _)
              _ = ‖airyHermiteTerm F m (u : ℂ)‖ := mul_one _
        exact hmono.trans ((setIntegral_le_integral (hterm_int_and_l1 m).1.norm
          (Eventually.of_forall fun _ => norm_nonneg _)).trans (hterm_int_and_l1 m).2)
      have hpos_le : (∫ u in Ioi (0 : ℝ), ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖) ≤
          C_pos * I_Jy * cAbs m := by
        have hpt_pos : ∀ u ∈ Ioi (0 : ℝ),
            ‖(airyHermiteTerm F m (u : ℂ)).re * Real.exp (y * u)‖ ≤
              (C_pos * cAbs m) * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by
          intro u (hu : 0 < u)
          have hne : u ≠ airyZ m := by linarith [airyZ_neg m]
          have hA2 : 2 < -airyZ m := by
            have := two_lt_abs_airyZ m
            rwa [abs_of_neg (airyZ_neg m)] at this
          have hden_gt : u + 2 < u - airyZ m := by linarith
          have hf_le : |(airySeedF m (u : ℂ)).re| ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
            rw [airySeedF_re_of_ne m hne, abs_of_nonneg (div_nonneg (sq_nonneg _) (by linarith))]
            exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden_gt.le).trans
              (hpos_J0 u hu.le)
          have hg_le : |(airySeedG m (u : ℂ)).re| ≤ C_pos * (airyRefJ0 (u : ℂ)).re := by
            rw [airySeedG_re_of_ne m hne, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
            have hsq_ge : u + 2 ≤ (u - airyZ m) ^ 2 := by nlinarith
            exact (div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hsq_ge).trans
              (hpos_J0 u hu.le)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          have hterm_re : |(airyHermiteTerm F m (u : ℂ)).re| ≤
              (C_pos * cAbs m) * (airyRefJ0 (u : ℂ)).re := by
            have hre_u : (airyHermiteTerm F m (u : ℂ)).re =
                cG m * (airySeedG m (u : ℂ)).re + cF m * (airySeedF m (u : ℂ)).re := by
              change (((cG m : ℂ) * airySeedG m (u : ℂ) +
                (cF m : ℂ) * airySeedF m (u : ℂ)).re) = _
              simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
                Complex.ofReal_im, zero_mul, sub_zero]
            rw [hre_u]
            calc |cG m * (airySeedG m (u : ℂ)).re + cF m * (airySeedF m (u : ℂ)).re|
                ≤ |cG m| * |(airySeedG m (u : ℂ)).re| + |cF m| * |(airySeedF m (u : ℂ)).re| := by
                  simpa [abs_mul] using abs_add_le
                    (cG m * (airySeedG m (u : ℂ)).re) (cF m * (airySeedF m (u : ℂ)).re)
              _ ≤ |cG m| * (C_pos * (airyRefJ0 (u : ℂ)).re) +
                    |cF m| * (C_pos * (airyRefJ0 (u : ℂ)).re) :=
                  add_le_add (mul_le_mul_of_nonneg_left hg_le (abs_nonneg _))
                    (mul_le_mul_of_nonneg_left hf_le (abs_nonneg _))
              _ = (C_pos * cAbs m) * (airyRefJ0 (u : ℂ)).re := by dsimp [cAbs]; ring
          calc |(airyHermiteTerm F m (u : ℂ)).re| * Real.exp (y * u)
              ≤ ((C_pos * cAbs m) * (airyRefJ0 (u : ℂ)).re) * Real.exp (y * u) :=
                mul_le_mul_of_nonneg_right hterm_re (Real.exp_pos _).le
            _ = (C_pos * cAbs m) * ((airyRefJ0 (u : ℂ)).re * Real.exp (y * u)) := by ring
        have hmono := setIntegral_mono_on hint_m.norm.integrableOn
          (hJ_int_y.const_mul (C_pos * cAbs m)) measurableSet_Ioi hpt_pos
        rw [integral_const_mul] at hmono
        exact hmono.trans_eq (by dsimp [I_Jy]; ring)
      rw [hsplit]
      linarith
    have hsum_y : Summable (fun k : ℕ =>
        ∫ u : ℝ, ‖(airyHermiteTerm F (k + N) (u : ℂ)).re * Real.exp (y * u)‖) := by
      have hmaj : Summable (fun m : ℕ => (C_L1 * (1 + |airyZ m|) + C_pos * I_Jy) * cAbs m) := by
        refine (hwL_sum.add ((hcoeff_summable 0).mul_left (C_pos * I_Jy))).congr fun m => ?_
        simp [pow_zero]; ring
      exact (hmaj.comp_injective (add_left_injective N)).of_nonneg_of_le
        (fun _ => integral_nonneg fun _ => norm_nonneg _)
        (fun k => (hterm_y_int (k + N)).2)
    have hhas_lap := hasSum_integral_of_summable_integral_norm
      (F := fun (k : ℕ) (u : ℝ) => (airyHermiteTerm F (k + N) (u : ℂ)).re * Real.exp (y * u))
      (fun k => (hterm_y_int (k + N)).1) hsum_y
    have hint_FN_y_all : ∀ M : ℕ,
        Integrable (fun u : ℝ => (airyHermitePartialSum F M (u : ℂ)).re * Real.exp (y * u)) := by
      intro M
      induction M with
      | zero =>
        have hz : (fun u : ℝ => (airyHermitePartialSum F 0 (u : ℂ)).re * Real.exp (y * u)) =
            fun _ => 0 := by ext u; simp [airyHermitePartialSum]
        rw [hz]; exact integrable_zero _ _ _
      | succ M ih =>
        have hs : (fun u : ℝ => (airyHermitePartialSum F (M + 1) (u : ℂ)).re * Real.exp (y * u)) =
            fun u : ℝ => (airyHermitePartialSum F M (u : ℂ)).re * Real.exp (y * u) +
              (airyHermiteTerm F M (u : ℂ)).re * Real.exp (y * u) := by
          ext u; simp [airyHermitePartialSum, Finset.sum_range_succ, add_mul]
        rw [hs]; exact ih.add (hterm_y_int M).1
    have hrem_lap : airyLaplace (fun u => (F (u : ℂ)).re) y -
        airyLaplace (fun u => (airyHermitePartialSum F N (u : ℂ)).re) y =
        ∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y := by
      have hint_F_y : Integrable (fun u : ℝ => (F (u : ℂ)).re * Real.exp (y * u)) :=
        hF.integrable_exp_nonneg hy
      have hint_FN_y := hint_FN_y_all N
      unfold airyLaplace
      rw [← mul_sub, ← integral_sub hint_F_y hint_FN_y]
      have hpt_re : ∀ u : ℝ,
          (F (u : ℂ)).re * Real.exp (y * u) -
            (airyHermitePartialSum F N (u : ℂ)).re * Real.exp (y * u) =
          ∑' k : ℕ, (airyHermiteTerm F (k + N) (u : ℂ)).re * Real.exp (y * u) := by
        intro u
        rw [← sub_mul, ← Complex.sub_re, hrem_eq N]
        have hs_c : HasSum (fun k : ℕ => airyHermiteTerm F (k + N) (u : ℂ))
            (∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)) :=
          ((hF_hasSum (u : ℂ)).summable.comp_injective (add_left_injective N)).hasSum
        have hs_re : HasSum (fun k : ℕ => (airyHermiteTerm F (k + N) (u : ℂ)).re)
            (∑' k : ℕ, airyHermiteTerm F (k + N) (u : ℂ)).re := by
          unfold HasSum at hs_c ⊢
          simp_rw [← Complex.re_sum]
          exact (Complex.continuous_re.tendsto _).comp hs_c
        rw [← hs_re.tsum_eq, ← tsum_mul_right]
      simp_rw [hpt_re]
      rw [← hhas_lap.tsum_eq, ← tsum_mul_left]
    rw [hrem_lap]
    have hlap_sum : Summable (fun k : ℕ =>
        |airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y|) :=
      ((hwL_sum.comp_injective (add_left_injective N)).mul_right
        ((1 + y) ^ (-(5 / 2 : ℝ)))).of_nonneg_of_le
        (fun _ => abs_nonneg _) (fun k => hterm_lap_bd (k + N) y hy)
    have hlap_norm_sum : Summable (fun k : ℕ =>
        ‖airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y‖) := by
      simpa only [Real.norm_eq_abs] using hlap_sum
    have hlap_tsum_le : |∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y| ≤
        (∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) * (1 + y) ^ (-(5 / 2 : ℝ)) := by
      calc |∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y|
          ≤ ∑' k : ℕ, |airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y| := by
            simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hlap_norm_sum
        _ ≤ ∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N) * (1 + y) ^ (-(5 / 2 : ℝ)) :=
            Summable.tsum_le_tsum (fun k => hterm_lap_bd (k + N) y hy) hlap_sum
              ((hwL_sum.comp_injective (add_left_injective N)).mul_right _)
        _ = (∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) *
              (1 + y) ^ (-(5 / 2 : ℝ)) := tsum_mul_right
    have hy_cancel : (1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add (by positivity : 0 < 1 + y), add_neg_cancel, Real.rpow_zero]
    calc (1 + y) ^ (5 / 2 : ℝ) *
          |∑' k : ℕ, airyLaplace (fun u => (airyHermiteTerm F (k + N) (u : ℂ)).re) y|
        ≤ (1 + y) ^ (5 / 2 : ℝ) *
            ((∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) *
              (1 + y) ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hlap_tsum_le (by positivity)
      _ = (∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N)) *
            ((1 + y) ^ (5 / 2 : ℝ) * (1 + y) ^ (-(5 / 2 : ℝ))) := by ring
      _ = ∑' k : ℕ, C_L1 * (1 + |airyZ (k + N)|) * cAbs (k + N) := by rw [hy_cancel, mul_one]
      _ < ε := hN
  · -- (d1) `airyBetaInf (F_N) → 0`
    have heq : (fun N : ℕ => airyBetaInf (airyHermitePartialSum F N)) =
        fun N : ℕ => -∑ n ∈ Finset.range N, cF n :=
      funext fun N => (hpartial_coeffs N).2.1
    rw [heq]
    simpa using hcF_hasSum_zero.tendsto_sum_nat.neg
  · -- (d2) `airyBetaPlus (F_N) → 0`
    have heq : (fun N : ℕ => airyBetaPlus (airyHermitePartialSum F N)) =
        fun N : ℕ => ∑ n ∈ Finset.range N, cF n :=
      funext fun N => (hpartial_coeffs N).2.2
    rw [heq]
    exact hcF_hasSum_zero.tendsto_sum_nat

/-- info: 'FormalResearch.SignUncertainty.lem_al_hermite_approx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.SignUncertainty.lem_al_hermite_approx

end FormalResearch.SignUncertainty




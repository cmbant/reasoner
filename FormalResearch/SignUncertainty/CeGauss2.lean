module

public import FormalResearch.CohnElkies.CancelledSymbolAndLaplace
public import FormalResearch.CohnElkies.AirySeedSymbols
public import FormalResearch.SignUncertainty.ConvSourceG1

/-!
# The Gaussian form of the Airy-square transform: the bounds `(ceo:gauss.2)` (Lemma O.11g, D1 / F2 leaf)

`ceG1_twisted_bounds` is the second half of Lemma O.11g (`ceo:gauss`, `ce_o1_route.tex`): there are `0 < b_g ≤ C_g` with
`|g̃₁(i z)| ≤ C_g (1 + Re z)^{-9/2}` for `Re z ≥ 0` and `g̃₁(i x) ≥ b_g (1 + x)^{-9/2}` for real `x ≥ 0`
(`g₁ = Ai²/(u - a₁)²`, `g̃₁(i z) = k e^{-z³/12} ∫ g₁ e^{z u}`).  The Gaussian form `(ceo:gauss.1)` and the Laplace transform of `Ai²`
(`(ceo:O11n.7)`) are `airyTwistedLaplaceC_ceG1_eq` / `airySquare_gaussian_transform` (`CancelledSymbolAndLaplace`, `AiryGaussianTransform`).

Class: proved.  The proof follows the TeX: `φ₁(t) = t q(t)` with `q` continuous and positive on `[0, ∞)` (so `b t ≤ φ₁ ≤ C t` on `[0,1]`, resp.
`[0,∞)`), the modulus bound `|e^{-(t-s)²/(4y)}| ≤ 1` for `Re y > 0`, `∫ t e^{-x t/2} dt = 4/x²`, and, for the lower bound, the box `[0,1/x]²` and
the unit interval `[0,1]`, where the integrand is `≥ min g₁ > 0`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The normalised first Dirichlet eigenfunction `φ₁(t) = Ai(a₁ + t)/Ai'(a₁)` factors as `t · q(t)` with `q = dslope Ai a₁ (a₁ + ·)/Ai'(a₁)`. -/
noncomputable def ceGaussQ (t : ℝ) : ℝ := dslope airyAi (airyZero 1) (airyZero 1 + t) / airyAi' (airyZero 1)

lemma continuous_dslope_airyAi_aux (a : ℝ) : Continuous (dslope airyAi a) := by
  rw [← continuousOn_univ, continuousOn_dslope univ_mem]
  exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi a⟩

lemma continuous_ceGaussQ : Continuous ceGaussQ :=
  ((continuous_dslope_airyAi_aux (airyZero 1)).comp (continuous_const.add continuous_id)).div_const _

lemma dirichletPhi_zero_eq (t : ℝ) : dirichletPhi 0 t = t * ceGaussQ t := by
  unfold dirichletPhi ceGaussQ
  have h := sub_smul_dslope airyAi (airyZero 1) (airyZero 1 + t)
  rw [airyAi_airyZero, sub_zero, add_sub_cancel_left, smul_eq_mul] at h
  rw [zero_add, add_comm t, mul_div_assoc', h]

lemma ceGaussQ_pos {t : ℝ} (ht : 0 ≤ t) : 0 < ceGaussQ t := by
  unfold ceGaussQ
  refine div_pos ?_ airyAi'_first_pos
  rcases eq_or_lt_of_le ht with h | h
  · subst h; rw [add_zero, dslope_same, deriv_airyAi]; exact airyAi'_first_pos
  · have h1 := sub_smul_dslope airyAi (airyZero 1) (airyZero 1 + t)
    rw [airyAi_airyZero, sub_zero, add_sub_cancel_left, smul_eq_mul] at h1
    have h2 : 0 < airyAi (airyZero 1 + t) := airyAi_pos_of_gt_first (by linarith)
    rw [← h1] at h2
    exact (pos_iff_pos_of_mul_pos h2).mp h

/-- Upper bound `0 ≤ φ₁(t) ≤ C t` for `t ≥ 0`. -/
lemma dirichletPhi_zero_le : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → dirichletPhi 0 t ≤ C * t := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn continuous_ceGaussQ.continuousOn
  have h3 : (0 : ℝ) < airyAi' (airyZero 1) := airyAi'_first_pos
  refine ⟨max (|M|) (3 / airyAi' (airyZero 1)) + 1, by positivity, fun t ht => ?_⟩
  rw [dirichletPhi_zero_eq]
  rcases le_or_gt t 1 with h1 | h1
  · have := hM t ⟨ht, h1⟩
    rw [Real.norm_eq_abs] at this
    have hq : ceGaussQ t ≤ max (|M|) (3 / airyAi' (airyZero 1)) + 1 := by
      have := (le_abs_self _).trans this
      have := le_abs_self M
      linarith [le_max_left (|M|) (3 / airyAi' (airyZero 1))]
    nlinarith
  · have hq : t * ceGaussQ t ≤ 3 / airyAi' (airyZero 1) := by
      rw [← dirichletPhi_zero_eq]
      unfold dirichletPhi
      rw [zero_add, add_comm t]
      exact div_le_div_of_nonneg_right ((le_abs_self _).trans (abs_airyAi_le_three _)) h3.le
    have : 3 / airyAi' (airyZero 1) ≤ (max (|M|) (3 / airyAi' (airyZero 1)) + 1) * t := by
      have := le_max_right (|M|) (3 / airyAi' (airyZero 1))
      have h30 : 0 ≤ 3 / airyAi' (airyZero 1) := by positivity
      nlinarith [abs_nonneg M]
    linarith

lemma dirichletPhi_zero_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ dirichletPhi 0 t := by
  rw [dirichletPhi_zero_eq]; exact mul_nonneg ht (ceGaussQ_pos ht).le

/-- Lower bound `φ₁(t) ≥ b t` on `[0, 1]`. -/
lemma dirichletPhi_zero_ge : ∃ b : ℝ, 0 < b ∧ ∀ t : ℝ, 0 ≤ t → t ≤ 1 → b * t ≤ dirichletPhi 0 t := by
  obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    continuous_ceGaussQ.continuousOn
  refine ⟨ceGaussQ t₀, ceGaussQ_pos ht₀.1, fun t ht ht1 => ?_⟩
  rw [dirichletPhi_zero_eq, mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin ⟨ht, ht1⟩) ht


lemma continuous_dirichletPhi_zero : Continuous (dirichletPhi 0) := by
  have : dirichletPhi 0 = fun t => t * ceGaussQ t := funext dirichletPhi_zero_eq
  rw [this]; exact continuous_id.mul continuous_ceGaussQ

lemma norm_gaussExp_le {y : ℂ} (hy : 0 < y.re) (t s : ℝ) :
    ‖Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y))‖ ≤
      Real.exp (-(y.re / 2) * t) * Real.exp (-(y.re / 2) * s) := by
  have h : -y * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * y) =
      (-y * ((t + s : ℝ) : ℂ) / 2) + (-(((t - s : ℝ) : ℂ) ^ 2) / (4 * y)) := by ring
  rw [h, Complex.exp_add, norm_mul]
  have h1 : ‖Complex.exp (-y * ((t + s : ℝ) : ℂ) / 2)‖ = Real.exp (-(y.re / 2) * t) * Real.exp (-(y.re / 2) * s) := by
    rw [Complex.norm_exp, ← Real.exp_add]
    congr 1
    simp [Complex.mul_re]
    ring
  have h2 : ‖Complex.exp (-(((t - s : ℝ) : ℂ) ^ 2) / (4 * y))‖ ≤ 1 := norm_gaussKern_le hy (t - s)
  rw [h1]
  calc _ ≤ Real.exp (-(y.re / 2) * t) * Real.exp (-(y.re / 2) * s) * 1 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := mul_one _

lemma integrableOn_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(a * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := a) (by norm_num) one_pos ha
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one]; ring_nf

lemma integral_mul_exp_neg {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(a * t)) = 1 / a ^ 2 := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := a) (by norm_num) ha
  norm_num at this
  rw [this]; simp

/-- `u(t) = φ₁(t) e^{-a t}` is integrable on `(0, ∞)` with integral at most `C / a²`. -/
lemma phi_exp_integral {C : ℝ} (hC : ∀ t : ℝ, 0 ≤ t → dirichletPhi 0 t ≤ C * t) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => dirichletPhi 0 t * Real.exp (-(a * t))) (Ioi 0) ∧
    ∫ t in Ioi (0 : ℝ), dirichletPhi 0 t * Real.exp (-(a * t)) ≤ C / a ^ 2 := by
  have hint := (integrableOn_mul_exp_neg ha).const_mul C
  have hle : ∀ t ∈ Ioi (0 : ℝ), dirichletPhi 0 t * Real.exp (-(a * t)) ≤ C * (t * Real.exp (-(a * t))) := by
    intro t ht
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hC t (le_of_lt ht)) (Real.exp_pos _).le
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ dirichletPhi 0 t * Real.exp (-(a * t)) := fun t ht =>
    mul_nonneg (dirichletPhi_zero_nonneg (le_of_lt ht)) (Real.exp_pos _).le
  have hcont : Continuous fun t : ℝ => dirichletPhi 0 t * Real.exp (-(a * t)) :=
    continuous_dirichletPhi_zero.mul (by fun_prop)
  refine ⟨?_, ?_⟩
  · refine hint.mono' hcont.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_of_nonneg (hnn t ht)]; exact hle t ht
  · calc _ ≤ ∫ t in Ioi (0 : ℝ), C * (t * Real.exp (-(a * t))) :=
          setIntegral_mono_on (by
            refine hint.mono' hcont.aestronglyMeasurable ?_
            refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
            rw [Real.norm_of_nonneg (hnn t ht)]; exact hle t ht) hint measurableSet_Ioi hle
      _ = C / a ^ 2 := by rw [integral_const_mul, integral_mul_exp_neg ha]; ring


/-- The bound `|g̃₁(i z)| ≤ C x^{-9/2}` for `x = Re z ≥ 1` (from the Gaussian form). -/
lemma norm_ceG1_twisted_le_of_one_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re → ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) z‖ ≤ C * z.re ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨Cφ, hCφ, hφ⟩ := dirichletPhi_zero_le
  refine ⟨16 * ceK * Cφ ^ 2, by have := ceK_pos; positivity, fun z hz => ?_⟩
  have hx : 0 < z.re := by linarith
  have hz0 : z ≠ 0 := fun h => by rw [h] at hx; simp at hx
  set x := z.re with hxdef
  have ha : 0 < x / 2 := by positivity
  obtain ⟨hui, huJ⟩ := phi_exp_integral hφ ha
  set u : ℝ → ℝ := fun t => dirichletPhi 0 t * Real.exp (-(x / 2 * t)) with hu
  set J := ∫ t in Ioi (0 : ℝ), u t with hJ
  have hu0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ u t := fun t ht =>
    mul_nonneg (dirichletPhi_zero_nonneg (le_of_lt ht)) (Real.exp_pos _).le
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi hu0
  rw [airyTwistedLaplaceC_ceG1_eq hx, norm_mul, norm_mul, Complex.norm_real]
  -- the double integral
  have hdouble : ‖∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
        Complex.exp (-z * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * z))‖ ≤ J * J := by
    have hinner : ∀ t ∈ Ioi (0 : ℝ), ‖∫ s in Ioi (0 : ℝ), ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
        Complex.exp (-z * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * z))‖ ≤ u t * J := by
      intro t ht
      have := norm_integral_le_of_norm_le (hui.const_mul (u t)) (μ := volume.restrict (Ioi (0 : ℝ)))
        (f := fun s => ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
          Complex.exp (-z * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * z)))
        (by
          refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (dirichletPhi_zero_nonneg (le_of_lt ht))
            (dirichletPhi_zero_nonneg (le_of_lt hs)))]
          have := norm_gaussExp_le hx t s
          simp only [hu]
          calc dirichletPhi 0 t * dirichletPhi 0 s * ‖_‖ ≤ dirichletPhi 0 t * dirichletPhi 0 s *
                (Real.exp (-(z.re / 2) * t) * Real.exp (-(z.re / 2) * s)) :=
                mul_le_mul_of_nonneg_left this (mul_nonneg (dirichletPhi_zero_nonneg (le_of_lt ht)) (dirichletPhi_zero_nonneg (le_of_lt hs)))
            _ = _ := by rw [hxdef]; ring_nf)
      rwa [integral_const_mul] at this
    have := norm_integral_le_of_norm_le (hui.mul_const J) (μ := volume.restrict (Ioi (0 : ℝ)))
      (f := fun t => ∫ s in Ioi (0 : ℝ), ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
        Complex.exp (-z * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * z)))
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hinner t ht))
    rwa [integral_mul_const] at this
  have hJb : J ≤ Cφ / (x / 2) ^ 2 := huJ
  have hJb' : J * J ≤ (4 * Cφ / x ^ 2) ^ 2 := by
    have : Cφ / (x / 2) ^ 2 = 4 * Cφ / x ^ 2 := by field_simp; ring
    rw [this] at hJb
    nlinarith
  have hn : ‖(4 * (π : ℂ) * z) ^ (-(1 / 2 : ℂ))‖ ≤ x ^ (-(1 / 2 : ℝ)) := by
    have e : (-(1 / 2 : ℂ)) = ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_cpow_real, norm_mul, norm_mul]
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    have hpi : ‖(π : ℂ)‖ = π := by simp [abs_of_pos Real.pi_pos]
    rw [h4, hpi]
    have hge : x ≤ 4 * π * ‖z‖ := by
      have := Complex.re_le_norm z
      nlinarith [Real.pi_gt_three, norm_nonneg z]
    exact Real.rpow_le_rpow_of_nonpos hx hge (by norm_num)
  rw [Real.norm_of_nonneg ceK_pos.le]
  have hD : ‖∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
        Complex.exp (-z * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * z))‖ ≤ (4 * Cφ / x ^ 2) ^ 2 :=
    hdouble.trans hJb'
  have h4 : x ^ (-(4 : ℝ)) = ((x ^ 2)⁻¹) ^ 2 := by
    rw [Real.rpow_neg hx.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  calc ceK * ‖(4 * (π : ℂ) * z) ^ (-(1 / 2 : ℂ))‖ * ‖∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), _‖
      ≤ ceK * x ^ (-(1 / 2 : ℝ)) * (4 * Cφ / x ^ 2) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hn ceK_pos.le) hD (norm_nonneg _)
          (mul_nonneg ceK_pos.le (Real.rpow_nonneg hx.le _))
    _ = 16 * ceK * Cφ ^ 2 * x ^ (-(9 / 2 : ℝ)) := by
        have : x ^ (-(9 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * ((x ^ 2)⁻¹) ^ 2 := by
          rw [show (-(9 / 2 : ℝ)) = -(1 / 2 : ℝ) + (-(4 : ℝ)) by norm_num, Real.rpow_add hx, h4]
        rw [this]; field_simp; norm_num


/-- `|g̃₁(i z)| ≤ C (1 + Re z)^{-9/2}` for `Re z ≥ 0` (upper half of `ceo:gauss.2`). -/
lemma norm_ceG1_twisted_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 0 ≤ z.re → ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) z‖ ≤ C * (1 + z.re) ^ (-(9 / 2 : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := norm_ceG1_twisted_le_of_one_le
  obtain ⟨Cu, hCu, hu⟩ := hasU2_ceG1.rhp
  have hc2 : (0 : ℝ) < 2 ^ (9 / 2 : ℝ) := by positivity
  refine ⟨max (C₁ * 2 ^ (9 / 2 : ℝ)) (Cu * 2 ^ (9 / 2 : ℝ)), by positivity, fun z hz => ?_⟩
  set x := z.re with hxdef
  have hpos : 0 < 1 + x := by linarith
  rcases le_or_gt 1 x with h1 | h1
  · refine (h₁ z h1).trans ?_
    have hxp : 0 < x := by linarith
    have : x ^ (-(9 / 2 : ℝ)) ≤ 2 ^ (9 / 2 : ℝ) * (1 + x) ^ (-(9 / 2 : ℝ)) := by
      have h2 : (1 + x) ^ (-(9 / 2 : ℝ)) ≥ (2 * x) ^ (-(9 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
      rw [Real.mul_rpow (by norm_num) hxp.le] at h2
      have h3 : (2 : ℝ) ^ (-(9 / 2 : ℝ)) * 2 ^ (9 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      have h4 : 0 < (1 + x) ^ (-(9 / 2 : ℝ)) := by positivity
      nlinarith [Real.rpow_nonneg hxp.le (-(9 / 2 : ℝ)), h3]
    calc C₁ * x ^ (-(9 / 2 : ℝ)) ≤ C₁ * (2 ^ (9 / 2 : ℝ) * (1 + x) ^ (-(9 / 2 : ℝ))) := by gcongr
      _ = (C₁ * 2 ^ (9 / 2 : ℝ)) * (1 + x) ^ (-(9 / 2 : ℝ)) := by ring
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hw : 0 ≤ (z / (ceCs : ℂ)).re := by
      rw [Complex.div_ofReal_re]; exact div_nonneg hz ceCs_pos.le
    have := hu (z / (ceCs : ℂ)) hw
    rw [mul_div_cancel₀ _ (by exact_mod_cast ceCs_pos.ne')] at this
    have hn1 : 1 ≤ ‖1 + z / (ceCs : ℂ)‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp only [Complex.add_re, Complex.one_re]; linarith
    have hn : ‖1 + z / (ceCs : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
    have hb : 1 ≤ 2 ^ (9 / 2 : ℝ) * (1 + x) ^ (-(9 / 2 : ℝ)) := by
      have : (2 : ℝ) ^ (-(9 / 2 : ℝ)) ≤ (1 + x) ^ (-(9 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by norm_num)
      have h3 : (2 : ℝ) ^ (9 / 2 : ℝ) * 2 ^ (-(9 / 2 : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; norm_num
      nlinarith
    calc ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) z‖ ≤ Cu * ‖1 + z / (ceCs : ℂ)‖ ^ (-(5 / 2 : ℝ)) := this
      _ ≤ Cu * 1 := by gcongr
      _ ≤ (Cu * 2 ^ (9 / 2 : ℝ)) * (1 + x) ^ (-(9 / 2 : ℝ)) := by nlinarith
      _ ≤ _ := by gcongr; exact le_max_right _ _


/-- The real Gaussian integrand of `(ceo:gauss.1)`. -/
noncomputable def ceGaussF (x t s : ℝ) : ℝ :=
  dirichletPhi 0 t * dirichletPhi 0 s * Real.exp (-(x * (t + s)) / 2 - (t - s) ^ 2 / (4 * x))

/-- Real form of `(ceo:gauss.1)`: `g̃₁(i x) = k (4 π x)^{-1/2} ∬ φ₁(t) φ₁(s) e^{-x(t+s)/2 - (t-s)²/(4x)}`. -/
lemma airyTwistedLaplace_ceG1_real_form {x : ℝ} (hx : 0 < x) :
    airyTwistedLaplace (ceG1 (airyZero 1)) x = ceK * (4 * π * x) ^ (-(1 / 2 : ℝ)) *
      ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ceGaussF x t s := by
  apply Complex.ofReal_injective
  rw [← airyTwistedLaplaceC_ofReal, airyTwistedLaplaceC_ceG1_eq (by simpa using hx)]
  have hF : ∀ t s : ℝ, ((dirichletPhi 0 t * dirichletPhi 0 s : ℝ) : ℂ) *
      Complex.exp (-((x : ℝ) : ℂ) * ((t + s : ℝ) : ℂ) / 2 - ((t - s : ℝ) : ℂ) ^ 2 / (4 * ((x : ℝ) : ℂ))) =
      ((ceGaussF x t s : ℝ) : ℂ) := by
    intro t s
    unfold ceGaussF
    push_cast
    ring_nf
  simp_rw [hF]
  simp_rw [integral_complex_ofReal]
  have hc : ((4 * (π : ℂ) * ((x : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ))) = (((4 * π * x) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  rw [hc]
  push_cast
  ring

lemma ceGaussF_nonneg {x : ℝ} {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) : 0 ≤ ceGaussF x t s :=
  mul_nonneg (mul_nonneg (dirichletPhi_zero_nonneg ht) (dirichletPhi_zero_nonneg hs)) (Real.exp_pos _).le

lemma continuous_ceGaussF {x : ℝ} : Continuous (fun p : ℝ × ℝ => ceGaussF x p.1 p.2) := by
  unfold ceGaussF
  have := continuous_dirichletPhi_zero
  fun_prop


lemma ceGaussF_le_prod {x : ℝ} (hx : 0 < x) {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    ceGaussF x t s ≤ (dirichletPhi 0 t * Real.exp (-(x / 2 * t))) * (dirichletPhi 0 s * Real.exp (-(x / 2 * s))) := by
  unfold ceGaussF
  have h1 : Real.exp (-(x * (t + s)) / 2 - (t - s) ^ 2 / (4 * x)) ≤ Real.exp (-(x / 2 * t)) * Real.exp (-(x / 2 * s)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 0 ≤ (t - s) ^ 2 / (4 * x) := by positivity
    nlinarith
  have hp := mul_nonneg (dirichletPhi_zero_nonneg ht) (dirichletPhi_zero_nonneg hs)
  calc dirichletPhi 0 t * dirichletPhi 0 s * Real.exp (-(x * (t + s)) / 2 - (t - s) ^ 2 / (4 * x))
      ≤ dirichletPhi 0 t * dirichletPhi 0 s * (Real.exp (-(x / 2 * t)) * Real.exp (-(x / 2 * s))) :=
        mul_le_mul_of_nonneg_left h1 hp
    _ = _ := by ring

lemma integrableOn_ceGaussF_inner {C : ℝ} (hC : ∀ t : ℝ, 0 ≤ t → dirichletPhi 0 t ≤ C * t) {x : ℝ} (hx : 0 < x) {t : ℝ}
    (ht : 0 ≤ t) : IntegrableOn (fun s => ceGaussF x t s) (Ioi 0) := by
  obtain ⟨hui, -⟩ := phi_exp_integral hC (show 0 < x / 2 by positivity)
  refine (hui.const_mul (dirichletPhi 0 t * Real.exp (-(x / 2 * t)))).mono' ?_ ?_
  · exact (continuous_ceGaussF.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_of_nonneg (ceGaussF_nonneg ht (le_of_lt hs))]
    exact ceGaussF_le_prod hx ht (le_of_lt hs)

lemma integrableOn_ceGaussF_outer {C : ℝ} (hC : ∀ t : ℝ, 0 ≤ t → dirichletPhi 0 t ≤ C * t) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => ∫ s in Ioi (0 : ℝ), ceGaussF x t s) (Ioi 0) := by
  obtain ⟨hui, -⟩ := phi_exp_integral hC (show 0 < x / 2 by positivity)
  set J := ∫ s in Ioi (0 : ℝ), dirichletPhi 0 s * Real.exp (-(x / 2 * s))
  refine (hui.mul_const J).mono' ?_ ?_
  · have := (continuous_ceGaussF (x := x)).aestronglyMeasurable (μ := (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ))))
    exact this.integral_prod_right'
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have h0 : 0 ≤ ∫ s in Ioi (0 : ℝ), ceGaussF x t s :=
      setIntegral_nonneg measurableSet_Ioi fun s hs => ceGaussF_nonneg (le_of_lt ht) (le_of_lt hs)
    rw [Real.norm_of_nonneg h0]
    obtain ⟨hui', -⟩ := phi_exp_integral hC (show 0 < x / 2 by positivity)
    calc ∫ s in Ioi (0 : ℝ), ceGaussF x t s ≤ ∫ s in Ioi (0 : ℝ), (dirichletPhi 0 t * Real.exp (-(x / 2 * t))) *
          (dirichletPhi 0 s * Real.exp (-(x / 2 * s))) :=
          setIntegral_mono_on (integrableOn_ceGaussF_inner hC hx (le_of_lt ht)) (hui'.const_mul _) measurableSet_Ioi
            fun s hs => ceGaussF_le_prod hx (le_of_lt ht) (le_of_lt hs)
      _ = _ := by rw [integral_const_mul]

lemma integral_Ioc_id {a : ℝ} (ha : 0 ≤ a) : ∫ s in Ioc (0 : ℝ) a, s = a ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le ha, integral_id]; ring

/-- Lower bound of the Gaussian double integral for `x ≥ 1`. -/
lemma ceGaussR_lower {b C : ℝ} (hb0 : 0 < b) (hb : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → b * t ≤ dirichletPhi 0 t)
    (hC : ∀ t : ℝ, 0 ≤ t → dirichletPhi 0 t ≤ C * t) {x : ℝ} (hx : 1 ≤ x) :
    b ^ 2 * Real.exp (-(5 / 4 : ℝ)) / (4 * x ^ 4) ≤ ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ceGaussF x t s := by
  have hx0 : 0 < x := by linarith
  set a : ℝ := 1 / x with ha
  have ha0 : 0 < a := by positivity
  have ha1 : a ≤ 1 := by rw [ha]; exact div_le_one_of_le₀ hx hx0.le
  set E : ℝ := Real.exp (-(5 / 4 : ℝ)) with hE
  have hpt : ∀ t s : ℝ, 0 < t → t ≤ a → 0 < s → s ≤ a → b ^ 2 * E * (t * s) ≤ ceGaussF x t s := by
    intro t s ht hta hs hsa
    unfold ceGaussF
    have h1 := hb t ht.le (hta.trans ha1)
    have h2 := hb s hs.le (hsa.trans ha1)
    have hexp : E ≤ Real.exp (-(x * (t + s)) / 2 - (t - s) ^ 2 / (4 * x)) := by
      rw [hE]; apply Real.exp_le_exp.mpr
      have hxa : x * a = 1 := by rw [ha]; field_simp
      have e1 : x * (t + s) ≤ 2 := by nlinarith
      have e2 : (t - s) ^ 2 ≤ 1 := by nlinarith
      have e3 : (t - s) ^ 2 / (4 * x) ≤ 1 / 4 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith
      linarith
    calc b ^ 2 * E * (t * s) = (b * t) * (b * s) * E := by ring
      _ ≤ dirichletPhi 0 t * dirichletPhi 0 s * Real.exp (-(x * (t + s)) / 2 - (t - s) ^ 2 / (4 * x)) := by
        have h1' : 0 ≤ b * t := by positivity
        have h2' : 0 ≤ b * s := by positivity
        have hE0 : 0 ≤ E := (Real.exp_pos _).le
        calc (b * t) * (b * s) * E ≤ dirichletPhi 0 t * dirichletPhi 0 s * E :=
              mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 h2' (dirichletPhi_zero_nonneg ht.le)) hE0
          _ ≤ _ := mul_le_mul_of_nonneg_left hexp (mul_nonneg (dirichletPhi_zero_nonneg ht.le) (dirichletPhi_zero_nonneg hs.le))
  have hG : ∀ t ∈ Ioc (0 : ℝ) a, b ^ 2 * E * (a ^ 2 / 2) * t ≤ ∫ s in Ioi (0 : ℝ), ceGaussF x t s := by
    intro t ht
    have h1 : ∫ s in Ioc (0 : ℝ) a, ceGaussF x t s ≤ ∫ s in Ioi (0 : ℝ), ceGaussF x t s :=
      setIntegral_mono_set (integrableOn_ceGaussF_inner hC hx0 ht.1.le)
        (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ceGaussF_nonneg ht.1.le (le_of_lt hs))
        (Filter.Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
    have hcont : Continuous fun s => ceGaussF x t s := by
      unfold ceGaussF; have := continuous_dirichletPhi_zero; fun_prop
    have h2 : ∫ s in Ioc (0 : ℝ) a, b ^ 2 * E * (t * s) ≤ ∫ s in Ioc (0 : ℝ) a, ceGaussF x t s :=
      setIntegral_mono_on ((continuous_const.mul (continuous_const.mul continuous_id)).integrableOn_Ioc)
        (hcont.integrableOn_Ioc) measurableSet_Ioc fun s hs => hpt t s ht.1 ht.2 hs.1 hs.2
    have h3 : ∫ s in Ioc (0 : ℝ) a, b ^ 2 * E * (t * s) = b ^ 2 * E * (a ^ 2 / 2) * t := by
      rw [show (fun s : ℝ => b ^ 2 * E * (t * s)) = fun s => (b ^ 2 * E * t) * s by funext s; ring,
        integral_const_mul, integral_Ioc_id ha0.le]; ring
    linarith
  have hout := integrableOn_ceGaussF_outer hC hx0
  have h1 : ∫ t in Ioc (0 : ℝ) a, (∫ s in Ioi (0 : ℝ), ceGaussF x t s) ≤ ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ceGaussF x t s :=
    setIntegral_mono_set hout
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
        setIntegral_nonneg measurableSet_Ioi fun s hs => ceGaussF_nonneg (le_of_lt ht) (le_of_lt hs))
      (Filter.Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
  have h2 : ∫ t in Ioc (0 : ℝ) a, b ^ 2 * E * (a ^ 2 / 2) * t ≤ ∫ t in Ioc (0 : ℝ) a, ∫ s in Ioi (0 : ℝ), ceGaussF x t s :=
    setIntegral_mono_on ((continuous_const.mul continuous_id).integrableOn_Ioc)
      (hout.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hG
  have h3 : ∫ t in Ioc (0 : ℝ) a, b ^ 2 * E * (a ^ 2 / 2) * t = b ^ 2 * E * (a ^ 2 / 2) * (a ^ 2 / 2) := by
    rw [integral_const_mul, integral_Ioc_id ha0.le]
  have h4 : b ^ 2 * E / (4 * x ^ 4) = b ^ 2 * E * (a ^ 2 / 2) * (a ^ 2 / 2) := by
    rw [ha]; field_simp; ring
  linarith


lemma ceGauss2_integrable_mul_exp {x : ℝ} (hx : 0 ≤ x) : Integrable (fun u : ℝ => ceG1 (airyZero 1) u * Real.exp (x * u)) := by
  have h := (hasU2_ceG1.integrable (x : ℂ) (by simpa using hx)).re
  refine h.congr (Eventually.of_forall fun u => ?_)
  have e : ((ceG1 (airyZero 1) u : ℝ) : ℂ) * Complex.exp ((x : ℂ) * (u : ℂ)) =
      ((ceG1 (airyZero 1) u * Real.exp (x * u) : ℝ) : ℂ) := by push_cast; rfl
  simp only [e, RCLike.re_to_complex, Complex.ofReal_re]

/-- Lower bound of `g̃₁(i x)` on `[0, 1]`. -/
lemma ceG1_twisted_lower_unit : ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, 0 ≤ x → x ≤ 1 → m ≤ airyTwistedLaplace (ceG1 (airyZero 1)) x := by
  obtain ⟨u₀, hu₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn (nonempty_Icc.mpr zero_le_one)
    (continuous_ceG1 (airyZero 1)).continuousOn
  have hm : 0 < ceG1 (airyZero 1) u₀ := convG1_pos_of_ge (by have := hu₀.1; have := airyZero_neg 1; linarith)
  refine ⟨ceK * Real.exp (-(1 / 12 : ℝ)) * ceG1 (airyZero 1) u₀, by have := ceK_pos; positivity, fun x hx0 hx1 => ?_⟩
  unfold airyTwistedLaplace
  have hint := ceGauss2_integrable_mul_exp hx0
  have hle : ceG1 (airyZero 1) u₀ ≤ ∫ u : ℝ, ceG1 (airyZero 1) u * Real.exp (x * u) := by
    have h1 : ∫ u in Icc (0 : ℝ) 1, ceG1 (airyZero 1) u₀ ≤ ∫ u in Icc (0 : ℝ) 1, ceG1 (airyZero 1) u * Real.exp (x * u) :=
      setIntegral_mono_on (integrableOn_const (by simp)) hint.integrableOn measurableSet_Icc fun u hu => by
        have := hmin hu
        have he : 1 ≤ Real.exp (x * u) := Real.one_le_exp (mul_nonneg hx0 hu.1)
        calc ceG1 (airyZero 1) u₀ ≤ ceG1 (airyZero 1) u := this
          _ = ceG1 (airyZero 1) u * 1 := (mul_one _).symm
          _ ≤ _ := mul_le_mul_of_nonneg_left he (convG1_nonneg u)
    have h2 : ∫ u in Icc (0 : ℝ) 1, ceG1 (airyZero 1) u * Real.exp (x * u) ≤ ∫ u : ℝ, ceG1 (airyZero 1) u * Real.exp (x * u) :=
      setIntegral_le_integral hint (Eventually.of_forall fun u => mul_nonneg (convG1_nonneg u) (Real.exp_pos _).le)
    have h3 : ∫ u in Icc (0 : ℝ) 1, ceG1 (airyZero 1) u₀ = ceG1 (airyZero 1) u₀ := by simp
    linarith
  have hexp : Real.exp (-(1 / 12 : ℝ)) ≤ Real.exp (-(x ^ 3) / 12) := by
    apply Real.exp_le_exp.mpr
    have : x ^ 3 ≤ 1 := pow_le_one₀ hx0 hx1
    linarith
  have hk := ceK_pos
  calc ceK * Real.exp (-(1 / 12 : ℝ)) * ceG1 (airyZero 1) u₀ ≤ ceK * Real.exp (-(x ^ 3) / 12) * ∫ u : ℝ, ceG1 (airyZero 1) u * Real.exp (x * u) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hexp hk.le) hle hm.le (by positivity)

/-- **Lemma O.11g (`ceo:gauss`), the bounds `(ceo:gauss.2)`.**  There are constants `0 < b_g ≤ C_g` with
`‖g̃₁(i z)‖ ≤ C_g (1 + Re z)^{-9/2}` for `Re z ≥ 0` and `g̃₁(i x) ≥ b_g (1 + x)^{-9/2}` for real `x ≥ 0`, where
`g₁ = Ai²/(u - a₁)²` and `g̃₁(i z) = ceK e^{-z³/12} ∫ g₁(u) e^{z u} du` (`airyTwistedLaplaceC`, `airyTwistedLaplace`).  Proof as in the TeX:
the Gaussian form `airyTwistedLaplaceC_ceG1_eq` (`(ceo:gauss.1)`, proved in `CancelledSymbolAndLaplace` from `airySquare_gaussian_transform`),
`φ₁(t) ≍ min(t,1)` and `Re (1/y) ≥ 0`; on `0 ≤ Re z ≤ 1` the `U.2` bound, and the lower bound on `[0,1]` from `g₁ > 0` on `[0,1]`. -/
theorem ceG1_twisted_bounds : ∃ bg Cg : ℝ, 0 < bg ∧ bg ≤ Cg ∧
    (∀ z : ℂ, 0 ≤ z.re → ‖airyTwistedLaplaceC (ceG1 (airyZero 1)) z‖ ≤ Cg * (1 + z.re) ^ (-(9 / 2 : ℝ))) ∧
    (∀ x : ℝ, 0 ≤ x → bg * (1 + x) ^ (-(9 / 2 : ℝ)) ≤ airyTwistedLaplace (ceG1 (airyZero 1)) x) := by
  obtain ⟨Cu, hCu, hU⟩ := norm_ceG1_twisted_le
  obtain ⟨m, hm, hmx⟩ := ceG1_twisted_lower_unit
  obtain ⟨b, hb0, hb⟩ := dirichletPhi_zero_ge
  obtain ⟨C, hC0, hC⟩ := dirichletPhi_zero_le
  set b₂ : ℝ := ceK * (4 * π) ^ (-(1 / 2 : ℝ)) * (b ^ 2 * Real.exp (-(5 / 4 : ℝ)) / 4) with hb₂
  have hb₂0 : 0 < b₂ := by have := ceK_pos; positivity
  have hlow : ∀ x : ℝ, 0 ≤ x → min m b₂ * (1 + x) ^ (-(9 / 2 : ℝ)) ≤ airyTwistedLaplace (ceG1 (airyZero 1)) x := by
    intro x hx0
    have hpos : 0 < 1 + x := by linarith
    have hone : (1 + x) ^ (-(9 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hmin0 : 0 < min m b₂ := lt_min hm hb₂0
    rcases le_or_gt x 1 with h1 | h1
    · calc min m b₂ * (1 + x) ^ (-(9 / 2 : ℝ)) ≤ min m b₂ * 1 := by gcongr
        _ ≤ m := by rw [mul_one]; exact min_le_left _ _
        _ ≤ _ := hmx x hx0 h1
    · have hx : 0 < x := by linarith
      rw [airyTwistedLaplace_ceG1_real_form hx]
      have hR := ceGaussR_lower hb0 hb hC (x := x) h1.le
      have hxp : (4 * π * x) ^ (-(1 / 2 : ℝ)) = (4 * π) ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) :=
        Real.mul_rpow (by positivity) hx.le
      have hk := ceK_pos
      have hx4 : x ^ (-(9 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * (x ^ 4)⁻¹ := by
        have h4 : x ^ (-(4 : ℝ)) = (x ^ 4)⁻¹ := by
          rw [Real.rpow_neg hx.le, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        rw [show (-(9 / 2 : ℝ)) = -(1 / 2 : ℝ) + (-(4 : ℝ)) by norm_num, Real.rpow_add hx, h4]
      have hmono : (1 + x) ^ (-(9 / 2 : ℝ)) ≤ x ^ (-(9 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hx (by linarith) (by norm_num)
      have hcore : b₂ * x ^ (-(9 / 2 : ℝ)) ≤ ceK * (4 * π * x) ^ (-(1 / 2 : ℝ)) *
          ∫ t in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), ceGaussF x t s := by
        rw [hxp, hx4]
        have hq : 0 ≤ ceK * ((4 * π) ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ))) := by positivity
        calc b₂ * (x ^ (-(1 / 2 : ℝ)) * (x ^ 4)⁻¹) = ceK * ((4 * π) ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ))) *
              (b ^ 2 * Real.exp (-(5 / 4 : ℝ)) / (4 * x ^ 4)) := by
              rw [hb₂]; field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hR hq
      calc min m b₂ * (1 + x) ^ (-(9 / 2 : ℝ)) ≤ b₂ * x ^ (-(9 / 2 : ℝ)) :=
            mul_le_mul (min_le_right _ _) hmono (by positivity) hb₂0.le
        _ ≤ _ := hcore
  refine ⟨min m b₂, max Cu (min m b₂), lt_min hm hb₂0, le_max_right _ _, fun z hz => ?_, hlow⟩
  exact (hU z hz).trans (by gcongr; exact le_max_left _ _)

/-- info: 'FormalResearch.SignUncertainty.ceG1_twisted_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceG1_twisted_bounds

end FormalResearch.SignUncertainty

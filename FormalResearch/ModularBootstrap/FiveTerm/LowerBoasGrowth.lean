module

public import FormalResearch.ModularBootstrap.FiveTerm.LowerBoasGrowthPJ

/-!
# Uniform growth bound `cts:h-growth` for `boasH` across `|Im ζ| ≤ 2 log c'`

Bridges the strip `|Im ζ| < 1` via the Maximum Modulus Principle on `[ζ₁, T] × [-1, 1]`
with the holomorphic damping factor `(c' : ℂ)^2 * (1 + ζ/c')^3 * exp(A₀ exp(-(π/4)(ζ-ζ₁)) + η exp((π/4) ζ))`,
then lets `η ↓ 0`.
-/

@[expose] public section

open Real Complex MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

open FormalResearch.Special
open FormalResearch.ModularBootstrap
open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Integration
open FormalResearch.ModularBootstrap.ConcreteBootstrap
open FormalResearch.ModularBootstrap.Upper.Comb

noncomputable section

private lemma cos_pi_quarter_ge_half {y : ℝ} (hy : |y| ≤ 1) :
    (1 / 2 : ℝ) ≤ Real.cos ((π / 4 : ℝ) * y) := by
  have h0 : 0 ≤ (π / 4 : ℝ) * |y| := by positivity
  have hpi3 : (π / 4 : ℝ) * |y| ≤ π / 3 := by
    have := Real.pi_pos
    nlinarith only [hy, this]
  have hpi : π / 3 ≤ π := by linarith only [Real.pi_pos]
  have hanti := Real.strictAntiOn_cos.antitoneOn ⟨h0, hpi3.trans hpi⟩ ⟨by positivity, hpi⟩ hpi3
  rw [Real.cos_pi_div_three] at hanti
  have hcos : Real.cos ((π / 4 : ℝ) * y) = Real.cos ((π / 4 : ℝ) * |y|) := by
    rcases le_or_gt 0 y with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, show (π / 4 : ℝ) * -y = -((π / 4 : ℝ) * y) by ring, Real.cos_neg]
  linarith only [hanti, hcos]

/-- Uniform growth bound `‖H_c(ζ)‖ ≤ C c'^2 ‖1 + ζ / c'‖^3 exp(2π |Im ζ|)` across
`{ζ | (3/8) * zetaMin c' ≤ Re ζ ∧ |Im ζ| ≤ 2 log c'}` (`cts:h-growth`). -/
theorem boasH_growth :
    ∃ cc₀ C : ℝ, 10000 ≤ cc₀ ∧ 0 < C ∧
      ∀ {c' : ℝ}, cc₀ ≤ c' → ∀ {g : ℝ → ℝ},
        TestClass virasoroProblem (c' / 12) g → (∃ t ≥ 0, g t ≠ 0) →
        ∀ {ζ : ℂ}, (3 / 8 : ℝ) * zetaMin c' ≤ ζ.re → |ζ.im| ≤ 2 * Real.log c' →
          ζ ∈ zetaStrip c' ∧
            ‖boasH c' g ζ‖ ≤ C * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 * Real.exp (2 * π * |ζ.im|) := by
  obtain ⟨c_pj, C₁, hc_pj, hC₁, h_pj⟩ := boasH_strip_pj
  obtain ⟨c_sup, C_e, hc_sup, hC_e, h_sup⟩ := boasH_strip_sup
  have hev_damp : ∀ᶠ c' : ℝ in atTop,
      20 * c' * Real.exp (-((π / 4 : ℝ) * ((1 / 8 : ℝ) * zetaMin c'))) ≤ 1 := by
    have hpow : Tendsto (fun c' : ℝ => c' ^ (5 / 7 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5 / 7)
    filter_upwards [eventually_ge_atTop (1 : ℝ), hpow.eventually_ge_atTop 184320] with c' hc1 hc57
    have hc0 : 0 < c' := by linarith
    have hu_eq : (π / 4 : ℝ) * ((1 / 8 : ℝ) * zetaMin c') = c' ^ (6 / 7 : ℝ) / 48 := by
      unfold zetaMin
      have hpi := Real.pi_pos.ne'
      field_simp [hpi]
      ring
    have hu_nn : 0 ≤ c' ^ (6 / 7 : ℝ) / 48 := by positivity
    have hexp_sq : (c' ^ (6 / 7 : ℝ) / 48) ^ 2 / 4 ≤ Real.exp (c' ^ (6 / 7 : ℝ) / 48) := by
      have h1 : c' ^ (6 / 7 : ℝ) / 96 ≤ Real.exp (c' ^ (6 / 7 : ℝ) / 96) := by
        linarith only [Real.add_one_le_exp (c' ^ (6 / 7 : ℝ) / 96)]
      have h2 : (c' ^ (6 / 7 : ℝ) / 96) ^ 2 ≤ Real.exp (c' ^ (6 / 7 : ℝ) / 96) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      have h3 : Real.exp (c' ^ (6 / 7 : ℝ) / 96) ^ 2 = Real.exp (c' ^ (6 / 7 : ℝ) / 48) := by
        rw [← Real.exp_nat_mul]; congr 1; ring
      nlinarith only [h2, h3]
    have hc12 : (c' ^ (6 / 7 : ℝ)) ^ 2 = c' ^ (12 / 7 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have hprod : c' * c' ^ (5 / 7 : ℝ) = c' ^ (12 / 7 : ℝ) := by
      calc c' * c' ^ (5 / 7 : ℝ) = c' ^ (1 : ℝ) * c' ^ (5 / 7 : ℝ) := by rw [Real.rpow_one]
        _ = c' ^ (12 / 7 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    have h20 : 20 * c' ≤ Real.exp (c' ^ (6 / 7 : ℝ) / 48) := by
      have h1 : 9216 * (20 * c') ≤ c' ^ (12 / 7 : ℝ) := by
        calc 9216 * (20 * c') = 184320 * c' := by ring
          _ ≤ c' ^ (5 / 7 : ℝ) * c' := by gcongr
          _ = c' ^ (12 / 7 : ℝ) := by rw [mul_comm, hprod]
      have h2 : (c' ^ (6 / 7 : ℝ) / 48) ^ 2 / 4 = c' ^ (12 / 7 : ℝ) / 9216 := by
        rw [div_pow, hc12]; ring
      linarith only [h1, h2, hexp_sq]
    rw [hu_eq, Real.exp_neg]
    exact mul_inv_le_one_of_le₀ h20 (Real.exp_pos _).le
  obtain ⟨c_damp, hc_damp⟩ := eventually_atTop.mp hev_damp
  let M₀ : ℝ := max (C₁ * Real.exp (2 * π)) (max C_e 1)
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨max 10000 (max c_pj (max c_sup c_damp)), M₀ * Real.exp 1, le_max_left _ _, by positivity,
    fun {c'} hc' {g} hg hnz {ζ} hζ_re hζ_im => ?_⟩
  have hc10000 : 10000 ≤ c' := (le_max_left _ _).trans hc'
  have hcpj_le : c_pj ≤ c' := ((le_max_left _ _).trans (le_max_right _ _)).trans hc'
  have hcsup_le : c_sup ≤ c' := ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hcdamp_le : c_damp ≤ c' := ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hc'
  have hc0 : 0 < c' := by linarith
  have hc1 : 1 ≤ c' := by linarith
  have hζ_pos : 0 < ζ.re := lt_of_lt_of_le (mul_pos (by norm_num) (zetaMin_pos hc0)) hζ_re
  have hζ_mem : ζ ∈ zetaStrip c' := mem_zetaStrip_of_log_im hc10000 hζ_pos hζ_im
  refine ⟨hζ_mem, ?_⟩
  by_cases him1 : 1 ≤ |ζ.im|
  · have hbd := (h_pj hcpj_le hg hnz hζ_pos him1 hζ_im).2
    have hC₁_le : C₁ ≤ M₀ * Real.exp 1 := by
      have h1 : C₁ ≤ C₁ * Real.exp (2 * π) :=
        le_mul_of_one_le_right hC₁.le (Real.one_le_exp (by positivity))
      have h2 : C₁ * Real.exp (2 * π) ≤ M₀ := le_max_left _ _
      exact h1.trans (h2.trans (le_mul_of_one_le_right hM₀_pos.le (Real.one_le_exp zero_le_one)))
    exact hbd.trans (by gcongr)
  · have him_lt1 : |ζ.im| < 1 := not_le.mp him1
    set ζ₁ : ℝ := (1 / 4 : ℝ) * zetaMin c'
    have hζ₁_pos : 0 < ζ₁ := mul_pos (by norm_num) (zetaMin_pos hc0)
    have hζ₁_le_c : ζ₁ ≤ c' := by
      have h67 : c' ^ (6 / 7 : ℝ) ≤ c' := by
        calc c' ^ (6 / 7 : ℝ) ≤ c' ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
          _ = c' := Real.rpow_one c'
      have hpi : 2 / (3 * π) ≤ 1 :=
        (div_le_one (by positivity [Real.pi_pos])).mpr (by linarith only [Real.pi_gt_three])
      have h67_pos : 0 < c' ^ (6 / 7 : ℝ) := Real.rpow_pos_of_pos hc0 (6 / 7)
      dsimp [ζ₁, zetaMin]
      nlinarith only [h67, hpi, h67_pos]
    have hdiff_ζ : (1 / 8 : ℝ) * zetaMin c' ≤ ζ.re - ζ₁ := by dsimp [ζ₁]; linarith only [hζ_re]
    have hstep_η : ∀ η : ℝ, 0 < η → η ≤ 1 →
        ‖boasH c' g ζ‖ ≤ M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
          Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁))) +
            η * Real.exp ((π / 4 : ℝ) * ζ.re)) := by
      intro η hη_pos _
      let B_T : ℝ := 2 * π + (7 * π / 3 : ℝ) * c' + max 0 (Real.log C_e)
      have hBT_pos : 0 < B_T := by
        have := Real.pi_pos; dsimp [B_T]; positivity
      let T : ℝ := max (max (ζ.re + 1) (2 * ζ₁ + 1)) ((128 / (η * π ^ 2)) * B_T + 1)
      have hT_ge1 : 1 ≤ T := le_trans (by linarith [hζ₁_pos]) ((le_max_right _ _).trans (le_max_left _ _))
      have hT_gt_ζ : ζ.re < T := by linarith [(le_max_left _ _).trans (le_max_left _ _ : max (ζ.re + 1) (2 * ζ₁ + 1) ≤ T)]
      have hζ₁_lt_T : ζ₁ < T := by linarith [(le_max_right _ _).trans (le_max_left _ _ : max (ζ.re + 1) (2 * ζ₁ + 1) ≤ T)]
      let E : ℂ → ℂ := fun w =>
        (20 * c' : ℂ) * Complex.exp (-((π / 4 : ℝ) : ℂ) * (w - (ζ₁ : ℂ))) +
          (η : ℂ) * Complex.exp (((π / 4 : ℝ) : ℂ) * w)
      let D : ℂ → ℂ := fun w =>
        (c' : ℂ) ^ 2 * (1 + w / (c' : ℂ)) ^ 3 * Complex.exp (E w)
      let Φ : ℂ → ℂ := fun w => boasH c' g w / D w
      have hE_re : ∀ w : ℂ,
          (E w).re = 20 * c' * Real.exp (-(π / 4) * (w.re - ζ₁)) * Real.cos ((π / 4) * w.im) +
            η * Real.exp ((π / 4) * w.re) * Real.cos ((π / 4) * w.im) := by
        intro w
        have h1 : (-((π / 4 : ℝ) : ℂ) * (w - (ζ₁ : ℂ))).re = -(π / 4) * (w.re - ζ₁) := by
          simp [Complex.sub_re]
        have h2 : (-((π / 4 : ℝ) : ℂ) * (w - (ζ₁ : ℂ))).im = -((π / 4) * w.im) := by
          simp [Complex.sub_im]
        have h3 : (((π / 4 : ℝ) : ℂ) * w).re = (π / 4) * w.re := by simp
        have h4 : (((π / 4 : ℝ) : ℂ) * w).im = (π / 4) * w.im := by simp
        dsimp [E]
        rw [show (20 : ℂ) * (c' : ℂ) = ((20 * c' : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.exp_re, Complex.exp_re,
          h1, h2, h3, h4, Real.cos_neg]
        ring
      have hE_re_lb : ∀ w : ℂ, |w.im| ≤ 1 →
          10 * c' * Real.exp (-(π / 4) * (w.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * w.re) ≤ (E w).re := by
        intro w hw
        have hc := cos_pi_quarter_ge_half hw
        rw [hE_re]
        have he1 : 0 ≤ 20 * c' * Real.exp (-(π / 4) * (w.re - ζ₁)) := by positivity
        have he2 : 0 ≤ η * Real.exp ((π / 4) * w.re) := by positivity
        nlinarith only [hc, he1, he2]
      have hE_re_ub : ∀ w : ℂ,
          (E w).re ≤ 20 * c' * Real.exp (-(π / 4) * (w.re - ζ₁)) + η * Real.exp ((π / 4) * w.re) := by
        intro w
        rw [hE_re]
        have hc := Real.cos_le_one ((π / 4 : ℝ) * w.im)
        have he1 : 0 ≤ 20 * c' * Real.exp (-(π / 4) * (w.re - ζ₁)) := by positivity
        have he2 : 0 ≤ η * Real.exp ((π / 4) * w.re) := by positivity
        nlinarith only [hc, he1, he2]
      let U : Set ℂ := {w : ℂ | ζ₁ < w.re ∧ w.re < T ∧ -1 < w.im ∧ w.im < 1}
      have hU_open : IsOpen U :=
        (isOpen_lt continuous_const Complex.continuous_re).inter
          ((isOpen_lt Complex.continuous_re continuous_const).inter
            ((isOpen_lt continuous_const Complex.continuous_im).inter
              (isOpen_lt Complex.continuous_im continuous_const)))
      have hU_bdd : Bornology.IsBounded U :=
        (Metric.isBounded_ball (x := (0 : ℂ)) (r := T + 1)).subset fun w hw => by
          rw [Metric.mem_ball, dist_zero_right]
          have hnorm : ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
          have hre_abs : |w.re| ≤ T := by rw [abs_of_pos (hζ₁_pos.trans hw.1)]; exact hw.2.1.le
          have him_abs : |w.im| < 1 := abs_lt.mpr hw.2.2
          linarith only [hnorm, hre_abs, him_abs]
      have hcl_sub : closure U ⊆ {w : ℂ | ζ₁ ≤ w.re ∧ w.re ≤ T ∧ -1 ≤ w.im ∧ w.im ≤ 1} := by
        refine closure_minimal (fun w hw => ⟨hw.1.le, hw.2.1.le, hw.2.2.1.le, hw.2.2.2.le⟩) ?_
        exact (isClosed_le continuous_const Complex.continuous_re).inter
          ((isClosed_le Complex.continuous_re continuous_const).inter
            ((isClosed_le continuous_const Complex.continuous_im).inter
              (isClosed_le Complex.continuous_im continuous_const)))
      have hV_open : IsOpen (zetaStrip c') := isOpen_zetaStrip c'
      have hcl_strip : closure U ⊆ zetaStrip c' := by
        intro w hw
        have hm := hcl_sub hw
        refine mem_zetaStrip_of_log_im hc10000 (lt_of_lt_of_le hζ₁_pos hm.1) ?_
        have h1log : (1 : ℝ) ≤ 2 * Real.log c' := by
          have : 1 ≤ Real.log c' := by rw [Real.le_log_iff_exp_le hc0]; linarith only [Real.exp_one_lt_d9, hc10000]
          linarith only [this]
        exact (abs_le.mpr ⟨hm.2.2.1, hm.2.2.2⟩).trans h1log
      have hD_diff : DifferentiableOn ℂ D (zetaStrip c') := by
        have hlin : DifferentiableOn ℂ (fun w => 1 + w / (c' : ℂ)) (zetaStrip c') :=
          (differentiable_const 1 |>.add (differentiable_id.div_const _)).differentiableOn
        have hE_diff : DifferentiableOn ℂ E (zetaStrip c') := by
          have h1 : Differentiable ℂ (fun w : ℂ =>
              (20 * c' : ℂ) * Complex.exp (-((π / 4 : ℝ) : ℂ) * (w - (ζ₁ : ℂ)))) :=
            ((differentiable_id.sub_const _).const_mul _).cexp.const_mul _
          have h2 : Differentiable ℂ (fun w : ℂ => (η : ℂ) * Complex.exp (((π / 4 : ℝ) : ℂ) * w)) :=
            (differentiable_id.const_mul _).cexp.const_mul _
          exact (h1.add h2).differentiableOn
        exact ((hlin.pow 3).const_mul _).mul hE_diff.cexp
      have hD_ne : ∀ w ∈ zetaStrip c', D w ≠ 0 := by
        intro w hw
        have hre_1 : (1 + w / (c' : ℂ)).re = 1 + w.re / c' := by simp [Complex.div_ofReal_re]
        have h1_pos : (1 : ℝ) ≤ ‖1 + w / (c' : ℂ)‖ := by
          have h1re : 1 ≤ (1 + w / (c' : ℂ)).re := by linarith only [hre_1, div_nonneg hw.1.le hc0.le]
          exact h1re.trans (Complex.re_le_norm _)
        have h1_ne : (1 + w / (c' : ℂ)) ≠ 0 := fun h0 => by rw [h0, norm_zero] at h1_pos; linarith
        exact mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hc0.ne'))
          (pow_ne_zero 3 h1_ne)) (Complex.exp_ne_zero _)
      have hΦ_diff : DifferentiableOn ℂ Φ (zetaStrip c') :=
        (differentiableOn_boasH (by linarith) hg).div hD_diff hD_ne
      have hdiffU : DiffContOnCl ℂ Φ U :=
        ⟨hΦ_diff.mono (subset_trans subset_closure hcl_strip), hΦ_diff.continuousOn.mono hcl_strip⟩
      have hbd_fr : ∀ z ∈ frontier U, ‖Φ z‖ ≤ M₀ := by
        intro z hz
        have hzm := hcl_sub hz.1
        have hz_not : ¬ (ζ₁ < z.re ∧ z.re < T ∧ -1 < z.im ∧ z.im < 1) := by
          intro h; exact hz.2 (hU_open.interior_eq.symm ▸ h)
        have hD_norm : ∀ w ∈ closure U,
            c' ^ 2 * ‖1 + w / (c' : ℂ)‖ ^ 3 *
              Real.exp (10 * c' * Real.exp (-(π / 4) * (w.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * w.re)) ≤
            ‖D w‖ := by
          intro w hw
          have hwm := hcl_sub hw
          dsimp [D]
          rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hc0, Complex.norm_exp]
          gcongr
          exact hE_re_lb w (abs_le.mpr ⟨hwm.2.2.1, hwm.2.2.2⟩)
        have hD_lb := hD_norm z hz.1
        have hnorm_1 : 1 ≤ ‖1 + z / (c' : ℂ)‖ := by
          have h1 : (1 + z / (c' : ℂ)).re = 1 + z.re / c' := by simp [Complex.div_ofReal_re]
          have hre_z : 0 < z.re := lt_of_lt_of_le hζ₁_pos hzm.1
          have : 1 ≤ 1 + z.re / c' := by linarith only [div_nonneg hre_z.le hc0.le]
          linarith only [h1, Complex.re_le_norm (1 + z / (c' : ℂ)), this]
        have hcase : z.re = ζ₁ ∨ z.re = T ∨ |z.im| = 1 := by
          by_contra h
          push Not at h
          exact hz_not ⟨lt_of_le_of_ne hzm.1 (Ne.symm h.1), lt_of_le_of_ne hzm.2.1 h.2.1,
            lt_of_le_of_ne hzm.2.2.1 (fun he => h.2.2 (by rw [← he, abs_neg, abs_one])),
            lt_of_le_of_ne hzm.2.2.2 (fun he => h.2.2 (by rw [he, abs_one]))⟩
        rcases hcase with hleft | hright | hhoriz
        · have hz_mem := hcl_strip hz.1
          have hsup_z := h_sup hcsup_le hg hnz hz_mem
          obtain ⟨_, _, _, hbre_rt⟩ := bOfZeta_re_bounds hc0 hz_mem (lt_of_lt_of_le hζ₁_pos hzm.1).le
          have hbre_le4 : (bOfZeta c' z).re ≤ 4 := by
            have h1 : 3 * (z.re / c') + 1 / 2 ≤ 4 := by
              rw [hleft]; have : ζ₁ / c' ≤ 1 := (div_le_one hc0).mpr hζ₁_le_c
              linarith only [this]
            have h2 : Real.sqrt (3 * (z.re / c') + 1 / 2) ≤ 2 := by
              calc Real.sqrt (3 * (z.re / c') + 1 / 2) ≤ Real.sqrt (2 ^ 2) := Real.sqrt_le_sqrt (by linarith only [h1])
                _ = 2 := Real.sqrt_sq (by norm_num)
            linarith only [hbre_rt, h2]
          have h2pi3_le10 : (2 * π / 3) * c' * (bOfZeta c' z).re ≤ 10 * c' := by
            have hpi : 2 * π / 3 ≤ 2.1 := by linarith only [Real.pi_lt_d4]
            have h1 : (2 * π / 3) * (bOfZeta c' z).re ≤ 10 := by
              have hpos_b : 0 ≤ (bOfZeta c' z).re := (xiStar_pos.trans (bOfZeta_mem hc0 hz_mem).1).le
              nlinarith only [hpi, hbre_le4, hpos_b]
            nlinarith only [h1, hc0]
          have hexp_d_ge : Real.exp (10 * c') ≤
              Real.exp (10 * c' * Real.exp (-(π / 4) * (z.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * z.re)) := by
            refine Real.exp_le_exp.mpr ?_
            rw [hleft, sub_self, mul_zero, Real.exp_zero, mul_one]
            linarith only [show 0 ≤ (η / 2) * Real.exp ((π / 4) * ζ₁) by positivity]
          have hD_pos : 0 < ‖D z‖ := norm_pos_iff.mpr (hD_ne z hz_mem)
          dsimp [Φ]
          rw [norm_div, div_le_iff₀ hD_pos]
          calc ‖boasH c' g z‖ ≤ C_e * Real.exp ((2 * π / 3) * c' * (bOfZeta c' z).re) := hsup_z
            _ ≤ C_e * Real.exp (10 * c') := by gcongr
            _ ≤ M₀ * (c' ^ 2 * 1 ^ 3 * Real.exp (10 * c')) := by
                have hce_m : C_e ≤ M₀ := (le_max_left _ _).trans (le_max_right _ _)
                have hc2_ge1 : 1 ≤ c' ^ 2 := by nlinarith only [hc1]
                calc C_e * Real.exp (10 * c') ≤ M₀ * (1 * Real.exp (10 * c')) := by
                      nlinarith only [hce_m, Real.exp_pos (10 * c')]
                  _ ≤ M₀ * (c' ^ 2 * 1 ^ 3 * Real.exp (10 * c')) := by
                      have := mul_le_mul_of_nonneg_left hc2_ge1 (Real.exp_pos (10 * c')).le
                      nlinarith only [hM₀_pos, this]
            _ ≤ M₀ * (c' ^ 2 * ‖1 + z / (c' : ℂ)‖ ^ 3 *
                Real.exp (10 * c' * Real.exp (-(π / 4) * (z.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * z.re))) := by
                gcongr
            _ ≤ M₀ * ‖D z‖ := by gcongr
        · have hz_mem := hcl_strip hz.1
          have hsup_z := h_sup hcsup_le hg hnz hz_mem
          obtain ⟨_, _, _, hbre_rt⟩ := bOfZeta_re_bounds hc0 hz_mem (lt_of_lt_of_le hζ₁_pos hzm.1).le
          have hrt_ub : Real.sqrt (3 * (T / c') + 1 / 2) ≤ 3 * (T / c') + 3 / 2 := by
            have h0 : 0 ≤ 3 * (T / c') + 1 / 2 := by positivity
            rw [Real.sqrt_le_iff]
            refine ⟨by positivity, ?_⟩
            nlinarith only [h0]
          have hl_ub : Real.log C_e + (2 * π / 3) * c' * (bOfZeta c' z).re ≤
              (η / 2) * Real.exp ((π / 4) * T) := by
            have hb_sub : (bOfZeta c' z).re ≤ 3 * (T / c') + 7 / 2 := by rw [hright] at hbre_rt; linarith only [hbre_rt, hrt_ub]
            have hlin_b : (2 * π / 3) * c' * (bOfZeta c' z).re ≤ 2 * π * T + (7 * π / 3) * c' := by
              have h1 : (2 * π / 3) * c' * (3 * (T / c') + 7 / 2) = 2 * π * T + (7 * π / 3) * c' := by
                field_simp [hc0.ne']
              have h2 : (2 * π / 3) * c' * (bOfZeta c' z).re ≤ (2 * π / 3) * c' * (3 * (T / c') + 7 / 2) := by
                gcongr
              linarith only [h1, h2]
            have hexp_T : (η * π ^ 2 / 128) * T ^ 2 ≤ (η / 2) * Real.exp ((π / 4) * T) := by
              have h1 : (π / 8) * T ≤ Real.exp ((π / 8) * T) := by
                linarith only [Real.add_one_le_exp ((π / 8) * T)]
              have h2 : ((π / 8) * T) ^ 2 ≤ Real.exp ((π / 8) * T) ^ 2 :=
                pow_le_pow_left₀ (by positivity) h1 2
              have h3 : Real.exp ((π / 8) * T) ^ 2 = Real.exp ((π / 4) * T) := by
                rw [← Real.exp_nat_mul]; congr 1; ring
              have h4 : (η / 2) * ((π / 8) * T) ^ 2 = (η * π ^ 2 / 128) * T ^ 2 := by ring
              nlinarith only [h2, h3, h4, hη_pos]
            have hBT_le : B_T * T ≤ (η * π ^ 2 / 128) * T ^ 2 := by
              have hT_bd : (128 / (η * π ^ 2)) * B_T ≤ T := by
                linarith only [(le_max_right _ _ : (128 / (η * π ^ 2)) * B_T + 1 ≤ T)]
              have hpi_ne : η * π ^ 2 ≠ 0 := by positivity
              have h1 : B_T ≤ (η * π ^ 2 / 128) * T := by
                rw [← div_le_iff₀' (by positivity : (0 : ℝ) < η * π ^ 2 / 128)]
                calc B_T / (η * π ^ 2 / 128) = (128 / (η * π ^ 2)) * B_T := by field_simp [hpi_ne]
                  _ ≤ T := hT_bd
              nlinarith only [h1, hT_ge1]
            have hBT_ge : Real.log C_e + 2 * π * T + (7 * π / 3) * c' ≤ B_T * T := by
              have hlog_le : Real.log C_e ≤ max 0 (Real.log C_e) := le_max_right _ _
              dsimp [B_T]
              have h1 : 1 * ((7 * π / 3) * c' + max 0 (Real.log C_e)) ≤ T * ((7 * π / 3) * c' + max 0 (Real.log C_e)) :=
                mul_le_mul_of_nonneg_right hT_ge1 (by have := Real.pi_pos; positivity)
              nlinarith only [hlog_le, h1]
            linarith only [hlin_b, hBT_ge, hBT_le, hexp_T]
          have hCe_eq : C_e * Real.exp ((2 * π / 3) * c' * (bOfZeta c' z).re) =
              Real.exp (Real.log C_e + (2 * π / 3) * c' * (bOfZeta c' z).re) := by
            rw [Real.exp_add, Real.exp_log hC_e]
          have hexp_d_ge : Real.exp ((η / 2) * Real.exp ((π / 4) * T)) ≤
              Real.exp (10 * c' * Real.exp (-(π / 4) * (z.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * z.re)) := by
            refine Real.exp_le_exp.mpr ?_
            rw [hright]
            linarith only [show 0 ≤ 10 * c' * Real.exp (-(π / 4) * (T - ζ₁)) by positivity]
          have hD_pos : 0 < ‖D z‖ := norm_pos_iff.mpr (hD_ne z hz_mem)
          dsimp [Φ]
          rw [norm_div, div_le_iff₀ hD_pos]
          calc ‖boasH c' g z‖ ≤ C_e * Real.exp ((2 * π / 3) * c' * (bOfZeta c' z).re) := hsup_z
            _ = Real.exp (Real.log C_e + (2 * π / 3) * c' * (bOfZeta c' z).re) := hCe_eq
            _ ≤ Real.exp ((η / 2) * Real.exp ((π / 4) * T)) := Real.exp_le_exp.mpr hl_ub
            _ ≤ M₀ * (c' ^ 2 * 1 ^ 3 * Real.exp ((η / 2) * Real.exp ((π / 4) * T))) := by
                have h1m : 1 ≤ M₀ := (le_max_right _ _).trans (le_max_right _ _)
                have hc2_ge1 : 1 ≤ c' ^ 2 := by nlinarith only [hc1]
                calc Real.exp ((η / 2) * Real.exp ((π / 4) * T))
                    ≤ M₀ * (1 * Real.exp ((η / 2) * Real.exp ((π / 4) * T))) := by
                      nlinarith only [h1m, Real.exp_pos ((η / 2) * Real.exp ((π / 4) * T))]
                  _ ≤ M₀ * (c' ^ 2 * 1 ^ 3 * Real.exp ((η / 2) * Real.exp ((π / 4) * T))) := by
                      have := mul_le_mul_of_nonneg_left hc2_ge1 (Real.exp_pos ((η / 2) * Real.exp ((π / 4) * T))).le
                      simp only [one_pow, mul_one]
                      exact mul_le_mul_of_nonneg_left (by linarith only [this]) hM₀_pos.le
            _ ≤ M₀ * (c' ^ 2 * ‖1 + z / (c' : ℂ)‖ ^ 3 *
                Real.exp (10 * c' * Real.exp (-(π / 4) * (z.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * z.re))) := by
                gcongr
            _ ≤ M₀ * ‖D z‖ := by gcongr
        · have hz_pos : 0 < z.re := lt_of_lt_of_le hζ₁_pos hzm.1
          have h1log : 1 ≤ 2 * Real.log c' := by
            have : 1 ≤ Real.log c' := by rw [Real.le_log_iff_exp_le hc0]; linarith only [Real.exp_one_lt_d9, hc10000]
            linarith only [this]
          have hpj_z := (h_pj hcpj_le hg hnz hz_pos (by linarith only [hhoriz]) (by linarith only [hhoriz, h1log])).2
          rw [hhoriz, mul_one] at hpj_z
          have hexp_ge1 : 1 ≤ Real.exp (10 * c' * Real.exp (-(π / 4) * (z.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * z.re)) :=
            Real.one_le_exp (by positivity)
          have hD_pos : 0 < ‖D z‖ := norm_pos_iff.mpr (hD_ne z (hcl_strip hz.1))
          dsimp [Φ]
          rw [norm_div, div_le_iff₀ hD_pos]
          calc ‖boasH c' g z‖ ≤ C₁ * Real.exp (2 * π) * (c' ^ 2 * ‖1 + z / (c' : ℂ)‖ ^ 3) := by linarith only [hpj_z]
            _ ≤ M₀ * (c' ^ 2 * ‖1 + z / (c' : ℂ)‖ ^ 3 * 1) := by
                have hcm : C₁ * Real.exp (2 * π) ≤ M₀ := le_max_left _ _
                have hn_nn : 0 ≤ c' ^ 2 * ‖1 + z / (c' : ℂ)‖ ^ 3 := by positivity
                nlinarith only [hcm, hn_nn]
            _ ≤ M₀ * (c' ^ 2 * ‖1 + z / (c' : ℂ)‖ ^ 3 *
                Real.exp (10 * c' * Real.exp (-(π / 4) * (z.re - ζ₁)) + (η / 2) * Real.exp ((π / 4) * z.re))) := by
                gcongr
            _ ≤ M₀ * ‖D z‖ := by gcongr
      have hζ_U : ζ ∈ U := ⟨by dsimp [ζ₁]; linarith only [hζ_re, zetaMin_pos hc0], hT_gt_ζ,
        (abs_lt.mp him_lt1).1, (abs_lt.mp him_lt1).2⟩
      have hΦ_ζ := Complex.norm_le_of_forall_mem_frontier_norm_le hU_bdd hdiffU hbd_fr (subset_closure hζ_U)
      have hD_ζ_pos : 0 < ‖D ζ‖ := norm_pos_iff.mpr (hD_ne ζ hζ_mem)
      dsimp [Φ] at hΦ_ζ
      rw [norm_div, div_le_iff₀ hD_ζ_pos] at hΦ_ζ
      have hD_ub : ‖D ζ‖ ≤ c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
          Real.exp (20 * c' * Real.exp (-(π / 4) * (ζ.re - ζ₁)) + η * Real.exp ((π / 4) * ζ.re)) := by
        dsimp [D]
        rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0,
          Complex.norm_exp]
        gcongr
        exact hE_re_ub ζ
      exact hΦ_ζ.trans (mul_le_mul_of_nonneg_left hD_ub hM₀_pos.le |>.trans_eq (by ring))
    have hlim : ‖boasH c' g ζ‖ ≤ M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
        Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁)))) := by
      have htend : Tendsto (fun η : ℝ => M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
            Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁))) +
              η * Real.exp ((π / 4 : ℝ) * ζ.re)))
          (𝓝[>] 0) (𝓝 (M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
            Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁)))))) := by
        have h1 : Continuous (fun η : ℝ => M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
            Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁))) +
              η * Real.exp ((π / 4 : ℝ) * ζ.re))) := by fun_prop
        simpa using (h1.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
      refine ge_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with η hη
      exact hstep_η η hη.1 hη.2.le
    have hdamp_1 : 20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁))) ≤ 1 := by
      have h1 : Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁))) ≤
          Real.exp (-((π / 4 : ℝ) * ((1 / 8 : ℝ) * zetaMin c'))) :=
        Real.exp_le_exp.mpr (by nlinarith only [Real.pi_pos, hdiff_ζ])
      calc 20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁)))
          ≤ 20 * c' * Real.exp (-((π / 4 : ℝ) * ((1 / 8 : ℝ) * zetaMin c'))) := by gcongr
        _ ≤ 1 := hc_damp c' hcdamp_le
    have hexp_1 : Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁)))) ≤
        Real.exp 1 * Real.exp (2 * π * |ζ.im|) := by
      calc Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁))))
          ≤ Real.exp 1 := Real.exp_le_exp.mpr hdamp_1
        _ ≤ Real.exp 1 * Real.exp (2 * π * |ζ.im|) :=
            le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp (by positivity))
    calc ‖boasH c' g ζ‖
        ≤ M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 *
            Real.exp (20 * c' * Real.exp (-((π / 4 : ℝ) * (ζ.re - ζ₁)))) := hlim
      _ ≤ M₀ * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 * (Real.exp 1 * Real.exp (2 * π * |ζ.im|)) := by gcongr
      _ = M₀ * Real.exp 1 * c' ^ 2 * ‖1 + ζ / (c' : ℂ)‖ ^ 3 * Real.exp (2 * π * |ζ.im|) := by ring

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.boasH_growth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.boasH_growth

module

public import FormalResearch.SignUncertainty.TwoEdgeOriginBridge
public import FormalResearch.SignUncertainty.ConvSourcePreEdge
public import FormalResearch.SignUncertainty.CePostEdge
public import FormalResearch.SignUncertainty.CeDualLine
public import FormalResearch.SignUncertainty.MellinLiftGeneral
public import FormalResearch.SignUncertainty.CeHankelPairFromEigen

/-!
# Base helpers for the general two-edge Mellin–Hankel lift (`lem:ce-lift-assembly`)

* `airyBetaInf_neg_of_neg_tail`: negative left-ray `c₀ (1 + |u|)^{-3/2}` bound implies `airyBetaInf F < 0`.
* `eta_tune_convSource`: uniform `O(c^{-5/6})` tuning for `D₀ c - S_c`.
* `CeTwoEdgeLiftWitness`: bundled Mellin–Hankel eigenfunction pair `(fp c, fm c)` for `D_lift c ± S_c`.
* `admissLift_twoEdge_eq`: vertical-line `σ = 0` identity matching `admissLift` to `iMain S + iDual D`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma airySeedG0_eq_ceG1 :
    (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) = ceG1 (airyZero 1) := by
  have hcard : ∀ u : ℝ, airyCardinalR 0 u = dslope airyAi (airyZero 1) u := by
    have hne_eq : ∀ x : ℝ, x ≠ airyZero 1 →
        airyCardinalR 0 x = dslope airyAi (airyZero 1) x := by
      intro x hx
      have hx' : x ≠ airyZ 0 := hx
      rw [airyCardinalR_of_ne 0 hx', dslope_of_ne _ hx, slope_def_field, airyAi_airyZero 1, sub_zero]
      rfl
    intro u
    by_cases hu : u = airyZero 1
    · subst hu
      have h0_seq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hseq : Tendsto (fun n : ℕ => airyZero 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝 (airyZero 1)) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := airyZero 1)).add h0_seq
      have hne_n : ∀ n : ℕ, airyZero 1 + 1 / ((n : ℝ) + 1) ≠ airyZero 1 := by
        intro n h
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith only [h, hpos]
      have hcont_d : Continuous (dslope airyAi (airyZero 1)) := by
        rw [← continuousOn_univ, continuousOn_dslope univ_mem]
        exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi _⟩
      exact tendsto_nhds_unique ((continuous_airyCardinalR 0).tendsto _ |>.comp hseq)
        ((hcont_d.tendsto _ |>.comp hseq).congr fun n => (hne_eq _ (hne_n n)).symm)
    · exact hne_eq u hu
  ext u
  rw [airySeedG_re, hcard u]
  rfl

private lemma cohnTheta_tendsto_atTop : Tendsto cohnTheta atTop atTop := by
  unfold cohnTheta
  exact ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul_atTop
    (by norm_num : (0 : ℝ) < 2 / 3)).atTop_add tendsto_const_nhds

private lemma cohnTheta_continuousOn (R M : ℝ) :
    ContinuousOn cohnTheta (Icc R M) := by
  unfold cohnTheta
  exact (continuousOn_const.mul (continuousOn_id.rpow_const fun _ _ =>
    Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).add continuousOn_const

/-- Any `F` with `HasGenRationalAiryCoeffs F β₀₀ β₁₁` satisfying `c₀ (1 + |u|)^{-3/2} ≤ -(F u).re`
for `u ≤ w_cut` has `airyBetaInf F < 0`. -/
lemma airyBetaInf_neg_of_neg_tail {F : ℂ → ℂ} {β₀₀ β₁₁ c₀ w_cut : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁) (hc₀ : 0 < c₀)
    (hneg : ∀ u : ℝ, u ≤ w_cut → c₀ * (1 + |u|) ^ (-(3 / 2 : ℝ)) ≤ -(F (u : ℂ)).re) :
    airyBetaInf F < 0 := by
  obtain ⟨R₀, K, hR5, hK0, hwkb⟩ := hF.neg_axis_wkb
  have hc₀1 : 0 < c₀ / 2 := by positivity
  let R : ℝ := max (max R₀ (max 5 (-w_cut + 1))) ((2 * K / c₀ + 1) ^ 2)
  have hR1 : 1 ≤ R := (by norm_num : (1 : ℝ) ≤ 5).trans
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hR_pos : 0 < R := by linarith
  have hR_w : -w_cut + 1 ≤ R :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hR_R0 : R₀ ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hR_K : (2 * K / c₀ + 1) ^ 2 ≤ R := le_max_right _ _
  have hpi2 : π * (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≥ 1 := by
    have h23 : (2 : ℝ) ^ (3 / 2 : ℝ) < 3 := by
      have hsq : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 < 3 ^ 2 := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by norm_num)]; norm_num
      nlinarith [Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (3 / 2 : ℝ)]
    have hinv : (1 / 3 : ℝ) < (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.rpow_neg (by norm_num), one_div]
      exact inv_strictAnti₀ (Real.rpow_pos_of_pos (by norm_num) _) h23
    nlinarith [Real.pi_gt_three]
  have hpt_bd : ∀ x : ℝ, R ≤ x →
      β₀₀ * Real.sin (cohnTheta x) ^ 2 + β₁₁ * Real.cos (cohnTheta x) ^ 2 ≤ -(c₀ / 2) := by
    intro x hx
    have hx1 : 1 ≤ x := hR1.trans hx
    have hx0 : 0 < x := by linarith
    have hneg_x := hneg (-x) (by linarith)
    rw [abs_of_neg (by linarith : -x < 0), neg_neg] at hneg_x
    have hrpow_x : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)) ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.mul_rpow (by norm_num) hx0.le]
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
    have hFx_neg : π * x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re ≤ -c₀ := by
      have h1 : c₀ * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))) ≤ -(F ((-x : ℝ) : ℂ)).re :=
        (mul_le_mul_of_nonneg_left hrpow_x hc₀.le).trans hneg_x
      have h2 : c₀ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ -(x ^ (3 / 2 : ℝ) * (F ((-x : ℝ) : ℂ)).re) := by
        have hmul := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0.le (3 / 2 : ℝ))
        have hcan : x ^ (3 / 2 : ℝ) * (c₀ * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ)))) =
            c₀ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
          calc x ^ (3 / 2 : ℝ) * (c₀ * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (-(3 / 2 : ℝ))))
              = c₀ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) * (x ^ (3 / 2 : ℝ) * x ^ (-(3 / 2 : ℝ))) := by ring
            _ = c₀ * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
                rw [← Real.rpow_add hx0]; simp
        linarith
      have h3 := mul_le_mul_of_nonneg_left h2 Real.pi_pos.le
      have h4 : c₀ ≤ π * (c₀ * (2 : ℝ) ^ (-(3 / 2 : ℝ))) := by
        calc c₀ = c₀ * 1 := (mul_one c₀).symm
          _ ≤ c₀ * (π * (2 : ℝ) ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hpi2 hc₀.le
          _ = _ := by ring
      linarith
    have hw := hwkb x (hR_R0.trans hx)
    have hK_bd : K * x ^ (-(1 / 2 : ℝ)) ≤ c₀ / 2 := by
      have hrx : 2 * K / c₀ + 1 ≤ √x := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * K / c₀ + 1)]
        exact Real.sqrt_le_sqrt (hR_K.trans hx)
      have hsqrt_pos : 0 < √x := Real.sqrt_pos.mpr hx0
      rw [show x ^ (-(1 / 2 : ℝ)) = (√x)⁻¹ by rw [Real.sqrt_eq_rpow, Real.rpow_neg hx0.le],
        ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have h2K : 2 * K / c₀ ≤ √x := by linarith
      calc K = (c₀ / 2) * (2 * K / c₀) := by field_simp [hc₀.ne']
        _ ≤ (c₀ / 2) * √x := mul_le_mul_of_nonneg_left h2K hc₀1.le
    linarith [(abs_le.mp hw).1]
  let k : ℕ := Nat.ceil (max (cohnTheta R / (2 * π)) 0) + 1
  have hk_gt : cohnTheta R < 2 * π * (k : ℝ) := by
    have h1 : cohnTheta R / (2 * π) ≤ (Nat.ceil (max (cohnTheta R / (2 * π)) 0) : ℝ) :=
      (le_max_left _ _).trans (Nat.le_ceil _)
    have h2 : cohnTheta R ≤ 2 * π * (Nat.ceil (max (cohnTheta R / (2 * π)) 0) : ℝ) := by
      calc cohnTheta R = 2 * π * (cohnTheta R / (2 * π)) := by field_simp [Real.pi_pos.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hk_eq : (k : ℝ) = (Nat.ceil (max (cohnTheta R / (2 * π)) 0) : ℝ) + 1 := by
      dsimp [k]; push_cast; rfl
    calc cohnTheta R ≤ 2 * π * (Nat.ceil (max (cohnTheta R / (2 * π)) 0) : ℝ) := h2
      _ < 2 * π * ((Nat.ceil (max (cohnTheta R / (2 * π)) 0) : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (lt_add_one _) (by positivity)
      _ = 2 * π * (k : ℝ) := by rw [hk_eq]
  obtain ⟨M₀, hM₀⟩ := (tendsto_atTop.mp cohnTheta_tendsto_atTop (2 * π * (k : ℝ) + π / 2)).exists_forall_of_atTop
  let M : ℝ := max R M₀
  have hRM : R ≤ M := le_max_left _ _
  have hM_val : 2 * π * (k : ℝ) + π / 2 ≤ cohnTheta M := hM₀ M (le_max_right _ _)
  obtain ⟨x₁, hx₁, hx₁_eq⟩ := intermediate_value_Icc hRM (cohnTheta_continuousOn R M)
    ⟨hk_gt.le, by linarith [Real.pi_pos]⟩
  obtain ⟨x₂, hx₂, hx₂_eq⟩ := intermediate_value_Icc hRM (cohnTheta_continuousOn R M)
    ⟨by linarith [Real.pi_pos], hM_val⟩
  have h2k : 2 * π * (k : ℝ) = ((2 * k : ℕ) : ℝ) * π := by push_cast; ring
  have hsin : Real.sin (2 * π * (k : ℝ)) = 0 := by rw [h2k]; exact Real.sin_nat_mul_pi (2 * k)
  have hcos : Real.cos (2 * π * (k : ℝ)) = 1 := by
    rw [h2k, Real.cos_nat_mul_pi (2 * k)]
    simp [(even_two_mul k).neg_one_pow]
  have hβ₁₁ : β₁₁ ≤ -(c₀ / 2) := by
    have h := hpt_bd x₁ hx₁.1; rw [hx₁_eq] at h
    rw [hsin, hcos] at h; simpa using h
  have hβ₀₀ : β₀₀ ≤ -(c₀ / 2) := by
    have h := hpt_bd x₂ hx₂.1; rw [hx₂_eq] at h
    rw [Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, hsin, hcos] at h
    simpa using h
  obtain ⟨_, _, hbinf, _⟩ := hF.beta_eq
  linarith

lemma liftW_add {X Y : ℝ → ℝ} (hX : HasU2 X) (hY : HasU2 Y) (δ₀ : ℝ) (m : ℕ) :
    liftW (fun u => X u + Y u) δ₀ m = fun v => liftW X δ₀ m v + liftW Y δ₀ m v := by
  ext v; exact liftSymbol_add_seed hX hY δ₀ m (by simp)

lemma liftW_const_mul {X : ℝ → ℝ} (a δ₀ : ℝ) (m : ℕ) :
    liftW (fun u => a * X u) δ₀ m = fun v => (a : ℂ) * liftW X δ₀ m v := by
  ext v; exact liftSymbol_const_mul_seed a X δ₀ m ((v : ℂ) * Complex.I)

/-- Uniform `O(c^{-5/6})` tuning of `η` for `D₀ c - S_c` where `D₀ c = X + (∫ S_c) g₁`. -/
lemma eta_tune_convSource {X : ℝ → ℝ} (hUX : HasU2 X) (hX_mass : ∫ u : ℝ, X u = 0)
    {p γ θ lam : ℝ} (hp : 1 / 2 < p) (hp1 : p < 1) (hγ : 0 < γ) (hθ : 0 ≤ θ) (hlam : 0 < lam)
    (m : ℕ) :
    let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
    let S_c : ℝ → ℝ → ℝ := convSourceFamily p γ θ lam
    let D₀ : ℝ → ℝ → ℝ := fun c u => X u + (∫ v : ℝ, S_c c v) * g₁ u
    ∃ c_η C_η : ℝ, 2000 ≤ c_η ∧ 0 < C_η ∧
      ∀ {K c : ℝ}, 1 ≤ K → c_η ≤ c →
        ∃ η : ℝ,
          liftSymbol (fun u => (D₀ c u - S_c c u) + η * g₁ u)
              (ceBeta1 * K * liftEps c / 2) m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ) -
            liftSymbol (fun u => (D₀ c u - S_c c u) + η * g₁ u)
              (ceBeta1 * K * liftEps c / 2) m 0 = 0 ∧
          |η| ≤ C_η * c ^ (-(5 / 6 : ℝ)) := by
  dsimp only
  have hk0 : 0 < ceK := ceK_pos
  have hUg : HasU2 (fun u : ℝ => (airySeedG 0 (u : ℂ)).re) := by
    rw [airySeedG0_eq_ceG1]; exact hasU2_ceG1
  obtain ⟨CX, hCX0, hCX⟩ := hUX.rhp
  obtain ⟨Cg, hCg0, hCg⟩ := hUg.rhp
  obtain ⟨CD, hCD0, hCD⟩ := convSource_twisted_unif hp hp1 hγ.le hθ hlam
  obtain ⟨m₀, M₀, hm₀, hM₀, hmass⟩ := convSourceFamily_mass hp hp1 hγ hθ hlam
  let B_edge : ℝ := CX + M₀ * Cg + CD + 1
  let c_η : ℝ := max 2000 ((4 * Cg / ceK + 1) ^ 2)
  let C_η : ℝ := 2 / ceK * B_edge + 1
  refine ⟨c_η, C_η, le_max_left _ _, by positivity, fun {K c} hK hc => ?_⟩
  have hc2k : 2000 ≤ c := (le_max_left _ _).trans hc
  have hc0 : 0 < c := by linarith
  have hc1 : 1 ≤ c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε1 : liftEps c ≤ 1 := liftEps_le_one hc1
  let δ₀ : ℝ := ceBeta1 * K * liftEps c / 2
  have hδ0 : 0 ≤ δ₀ := by have := ceBeta1_pos; positivity
  let S_c : ℝ → ℝ := convSourceFamily p γ θ lam c
  let g₁ : ℝ → ℝ := fun u => (airySeedG 0 (u : ℂ)).re
  let M_c : ℝ := ∫ v : ℝ, S_c v
  have hMc_bd : m₀ * liftEps c ≤ M_c ∧ M_c ≤ M₀ * liftEps c := hmass hc2k
  have hMc0 : 0 ≤ M_c := le_trans (mul_nonneg hm₀.le hε0.le) hMc_bd.1
  have hUS : HasU2 S_c :=
    hasU2_convSource hp hp1 (by positivity : 0 < lam * liftEps c ^ 2)
  let Y₀ : ℝ → ℝ := fun u => (X u + M_c * g₁ u) - S_c u
  have hUY₀ : HasU2 Y₀ := by
    simpa [Y₀, sub_eq_add_neg] using (hUX.add (hUg.smul M_c)).add (hUS.smul (-1))
  let x : ℝ := c ^ (1 / 3 : ℝ)
  have hx0 : 0 < x := Real.rpow_pos_of_pos hc0 _
  have hrhp_bd : ∀ {C : ℝ}, 0 ≤ C → ∀ (A : ℝ → ℝ),
      (∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC A ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) →
      ‖liftSymbol A δ₀ m (x : ℂ)‖ ≤ C * c ^ (-(5 / 6 : ℝ)) := by
    intro C hC A hA
    have hx_re : 0 ≤ (x : ℂ).re := by simp [hx0.le]
    have h1 := hA (x : ℂ) hx_re
    have hnorm : ‖1 + (x : ℂ)‖ = 1 + x := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hpow : ‖1 + (x : ℂ)‖ ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) := by
      rw [hnorm]
      have hx_pow : x ^ (-(5 / 2 : ℝ)) = c ^ (-(5 / 6 : ℝ)) := by
        dsimp [x]; rw [← Real.rpow_mul hc0.le]; norm_num
      calc (1 + x) ^ (-(5 / 2 : ℝ)) ≤ x ^ (-(5 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)
        _ = c ^ (-(5 / 6 : ℝ)) := hx_pow
    unfold liftSymbol
    rw [norm_mul]
    exact (mul_le_mul (norm_liftMultiplier_le_one hδ0 m hx_re)
      (h1.trans (mul_le_mul_of_nonneg_left hpow hC)) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hgx_norm : ‖liftSymbol g₁ δ₀ m (x : ℂ)‖ ≤ Cg * c ^ (-(5 / 6 : ℝ)) := hrhp_bd hCg0.le g₁ hCg
  have hgx : |(liftSymbol (ceG1 (airyZero 1)) δ₀ m (x : ℂ)).re| ≤ ceK / 2 := by
    rw [← airySeedG0_eq_ceG1]
    have hc_c12 : 4 * Cg / ceK + 1 ≤ √c := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 4 * Cg / ceK + 1)]
      exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hc)
    have hsqrt_pos : 0 < √c := Real.sqrt_pos.mpr hc0
    have hc56 : c ^ (-(5 / 6 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    have hcg_le : Cg * c ^ (-(1 / 2 : ℝ)) ≤ ceK / 4 := by
      rw [show c ^ (-(1 / 2 : ℝ)) = (√c)⁻¹ by rw [Real.sqrt_eq_rpow, Real.rpow_neg hc0.le],
        ← div_eq_mul_inv, div_le_iff₀ hsqrt_pos]
      have h4 : 4 * Cg / ceK ≤ √c := by linarith
      calc Cg = (ceK / 4) * (4 * Cg / ceK) := by field_simp [hk0.ne']
        _ ≤ (ceK / 4) * √c := mul_le_mul_of_nonneg_left h4 (by positivity)
    exact (Complex.abs_re_le_norm _).trans (hgx_norm.trans
      ((mul_le_mul_of_nonneg_left hc56 hCg0.le).trans (by linarith)))
  obtain ⟨η, hη0, hη_bd⟩ := exists_eta_tune hUY₀ m hx0.le hgx
  have hY₀_int : ∫ u : ℝ, Y₀ u = 0 := by
    have hintX : Integrable X :=
      (Complex.reCLM.integrable_comp (hUX.integrable 0 le_rfl)).congr (ae_of_all _ fun u => by simp)
    have hintG : Integrable g₁ :=
      (Complex.reCLM.integrable_comp (hUg.integrable 0 le_rfl)).congr (ae_of_all _ fun u => by simp [g₁])
    have hintS : Integrable S_c :=
      (Complex.reCLM.integrable_comp (hUS.integrable 0 le_rfl)).congr (ae_of_all _ fun u => by simp)
    calc ∫ u : ℝ, Y₀ u
        = ∫ u : ℝ, ((X u + M_c * g₁ u) - S_c u) := rfl
      _ = (∫ u : ℝ, (X u + M_c * g₁ u)) - ∫ u : ℝ, S_c u :=
            integral_sub (hintX.add (hintG.const_mul M_c)) hintS
      _ = ((∫ u : ℝ, X u) + ∫ u : ℝ, M_c * g₁ u) - M_c := by
            rw [integral_add hintX (hintG.const_mul M_c)]
      _ = (0 + M_c * 1) - M_c := by
            rw [hX_mass, integral_const_mul, show (∫ u : ℝ, g₁ u) = 1 from integral_airySeedG 0]
      _ = 0 := by ring
  have hY₀_0 : liftSymbol Y₀ δ₀ m 0 = 0 := by
    rw [liftSymbol_zero_eq hUY₀ δ₀ m, hY₀_int, mul_zero, Complex.ofReal_zero]
  have hY₀_x : ‖liftSymbol Y₀ δ₀ m (x : ℂ)‖ ≤ B_edge * c ^ (-(5 / 6 : ℝ)) := by
    have hX_bd : ‖liftSymbol X δ₀ m (x : ℂ)‖ ≤ CX * c ^ (-(5 / 6 : ℝ)) := hrhp_bd hCX0.le X hCX
    have hS_bd : ‖liftSymbol S_c δ₀ m (x : ℂ)‖ ≤ CD * c ^ (-(5 / 6 : ℝ)) :=
      hrhp_bd hCD0.le S_c (fun w hw => hCD hε0 hε1 hw)
    have h12 : liftSymbol Y₀ δ₀ m (x : ℂ) = liftSymbol (fun u => X u + M_c * g₁ u) δ₀ m (x : ℂ) +
        (-1 : ℂ) * liftSymbol S_c δ₀ m (x : ℂ) := by
      have hfn : Y₀ = fun u => (X u + M_c * g₁ u) + (-1) * S_c u := by ext u; dsimp [Y₀]; ring
      rw [hfn, liftSymbol_add_seed (hUX.add (hUg.smul M_c)) (hUS.smul (-1)) δ₀ m (by simpa using hx0.le),
        liftSymbol_const_mul_seed (-1) S_c δ₀ m (x : ℂ)]
      push_cast; rfl
    have h1 : liftSymbol (fun u => X u + M_c * g₁ u) δ₀ m (x : ℂ) =
        liftSymbol X δ₀ m (x : ℂ) + (M_c : ℂ) * liftSymbol g₁ δ₀ m (x : ℂ) := by
      rw [liftSymbol_add_seed hUX (hUg.smul M_c) δ₀ m (by simpa using hx0.le),
        liftSymbol_const_mul_seed M_c g₁ δ₀ m (x : ℂ)]
    rw [h12, h1]
    calc ‖liftSymbol X δ₀ m (x : ℂ) + (M_c : ℂ) * liftSymbol g₁ δ₀ m (x : ℂ) +
            (-1 : ℂ) * liftSymbol S_c δ₀ m (x : ℂ)‖
        ≤ ‖liftSymbol X δ₀ m (x : ℂ)‖ + ‖(M_c : ℂ) * liftSymbol g₁ δ₀ m (x : ℂ)‖ +
            ‖(-1 : ℂ) * liftSymbol S_c δ₀ m (x : ℂ)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ CX * c ^ (-(5 / 6 : ℝ)) + M₀ * (Cg * c ^ (-(5 / 6 : ℝ))) + CD * c ^ (-(5 / 6 : ℝ)) := by
          refine add_le_add (add_le_add hX_bd ?_) ?_
          · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hMc0]
            have hM1 : M_c ≤ M₀ := hMc_bd.2.trans (mul_le_of_le_one_right hM₀.le hε1)
            exact mul_le_mul hM1 hgx_norm (norm_nonneg _) hM₀.le
          · rw [norm_mul, norm_neg, norm_one, one_mul]; exact hS_bd
      _ ≤ B_edge * c ^ (-(5 / 6 : ℝ)) := by
          have : 0 ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
          dsimp [B_edge]; nlinarith
  refine ⟨η, ?_, ?_⟩
  · have hgg : ∀ u : ℝ, (airySeedG 0 (u : ℂ)).re = ceG1 (airyZero 1) u :=
      congr_fun airySeedG0_eq_ceG1
    simpa [Y₀, g₁, M_c, S_c, δ₀, x, hgg] using hη0
  · rw [hY₀_0, sub_zero] at hη_bd
    calc |η| ≤ 2 / ceK * ‖liftSymbol Y₀ δ₀ m (x : ℂ)‖ := hη_bd
      _ ≤ 2 / ceK * (B_edge * c ^ (-(5 / 6 : ℝ))) := mul_le_mul_of_nonneg_left hY₀_x (by positivity)
      _ ≤ C_η * c ^ (-(5 / 6 : ℝ)) := by
          have : 0 ≤ c ^ (-(5 / 6 : ℝ)) := Real.rpow_nonneg hc0.le _
          dsimp [C_η]; nlinarith

/-- Exact vertical-line identity `c^{1/3} ρ₀(cξ) f_W(cξ) = I_main[S](ξ) + I_dual[D](ξ)` at `σ = 0`. -/
lemma admissLift_twoEdge_eq {S D : ℝ → ℝ} (hUS : HasU2 S) (hUD : HasU2 D)
    {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c ξ : ℝ} (hc4 : 4 ≤ c) (hξ : 0 < ξ) :
    ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) *
        admissLift c (fun ζ => liftSymbol S δ₀ m (ζ / (liftEps c : ℂ)) +
          liftSymbol D δ₀ m ((1 - ζ) / (liftEps c : ℂ))) (c * ξ) : ℝ) : ℂ) =
      iMain S δ₀ m c ξ + iDual D δ₀ m c ξ := by
  have hc0 : 0 < c := by linarith
  have hε0 : 0 < liftEps c := liftEps_pos hc0
  have hε_inv : (liftEps c)⁻¹ = c ^ (1 / 3 : ℝ) := by
    unfold liftEps; rw [← Real.rpow_neg_one, ← Real.rpow_mul hc0.le]; norm_num
  have hsm := twoEdge_W_tilde_stripM1 (S := fun _ => S) (D := fun _ => D) (δ₀ := fun _ => δ₀)
    (m := m) hc4 hUS hUD hδ
  have hrep := admiss_vert_rep (by linarith : 1 ≤ c) hsm (σ := 0) le_rfl zero_lt_one hξ
  simp only [Complex.ofReal_zero, zero_add] at hrep
  let G_τ : ℝ → ℂ := fun τ =>
    mellinK0 c ((τ : ℂ) * Complex.I) ξ *
      (liftSymbol S δ₀ m (((τ : ℂ) * Complex.I) / (liftEps c : ℂ)) +
        liftSymbol D δ₀ m ((1 - (τ : ℂ) * Complex.I) / (liftEps c : ℂ)))
  have hsub := Measure.integral_comp_mul_left G_τ (liftEps c)
  have hpt : ∀ v : ℝ, G_τ (liftEps c * v) =
      iMainIntegrand S δ₀ m c ξ v + iDualIntegrand D δ₀ m c ξ v := by
    intro v
    have h1 : (((liftEps c * v : ℝ) : ℂ) * Complex.I) / (liftEps c : ℂ) =
        (v : ℂ) * Complex.I := by
      push_cast
      have hne : (liftEps c : ℂ) ≠ 0 := by exact_mod_cast hε0.ne'
      field_simp
    have h2 : (1 - ((liftEps c * v : ℝ) : ℂ) * Complex.I) / (liftEps c : ℂ) =
        (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) - (v : ℂ) * Complex.I := by
      rw [sub_div, one_div, ← Complex.ofReal_inv, hε_inv, h1]
    dsimp only [G_τ, iMainIntegrand, iDualIntegrand]
    rw [h1, h2, mul_add]
  have hsub' : ∫ v : ℝ, (iMainIntegrand S δ₀ m c ξ v + iDualIntegrand D δ₀ m c ξ v) =
      |(liftEps c)⁻¹| • ∫ τ : ℝ, G_τ τ := by
    rw [← hsub]
    exact integral_congr_ae (ae_of_all _ fun v => (hpt v).symm)
  have hint_im : Integrable (fun v : ℝ => iMainIntegrand S δ₀ m c ξ v) :=
    hUS.integrable_iMainIntegrand hδ m hc0 hξ
  have hint_id : Integrable (fun v : ℝ => iDualIntegrand D δ₀ m c ξ v) :=
    hUD.integrable_iDualIntegrand hδ m hc0 hξ
  have hscaled : ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ∫ τ : ℝ, G_τ τ =
      (∫ v : ℝ, iMainIntegrand S δ₀ m c ξ v) + (∫ v : ℝ, iDualIntegrand D δ₀ m c ξ v) := by
    calc ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ∫ τ : ℝ, G_τ τ
        = |(liftEps c)⁻¹| • ∫ τ : ℝ, G_τ τ := by
            rw [abs_of_pos (inv_pos.mpr hε0), hε_inv, Complex.real_smul]
      _ = ∫ v : ℝ, (iMainIntegrand S δ₀ m c ξ v + iDualIntegrand D δ₀ m c ξ v) := hsub'.symm
      _ = (∫ v : ℝ, iMainIntegrand S δ₀ m c ξ v) + (∫ v : ℝ, iDualIntegrand D δ₀ m c ξ v) :=
            integral_add hint_im hint_id
  calc ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) *
        admissLift c (fun ζ => liftSymbol S δ₀ m (ζ / (liftEps c : ℂ)) +
          liftSymbol D δ₀ m ((1 - ζ) / (liftEps c : ℂ))) (c * ξ) : ℝ) : ℂ)
      = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (((hankelRho0 c (c * ξ) *
          admissLift c (fun ζ => liftSymbol S δ₀ m (ζ / (liftEps c : ℂ)) +
            liftSymbol D δ₀ m ((1 - ζ) / (liftEps c : ℂ))) (c * ξ) : ℝ)) : ℂ) := by
          push_cast; ring
    _ = ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
          (((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) * ∫ τ : ℝ, G_τ τ) := by rw [hrep]
    _ = ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) * (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ∫ τ : ℝ, G_τ τ) := by
          ring
    _ = ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) *
          ((∫ v : ℝ, iMainIntegrand S δ₀ m c ξ v) + (∫ v : ℝ, iDualIntegrand D δ₀ m c ξ v)) := by
          rw [hscaled]
    _ = iMain S δ₀ m c ξ + iDual D δ₀ m c ξ := by
          unfold iMain iDual
          rw [show ((2 * Real.pi * ξ : ℝ) : ℂ)⁻¹ = ((1 / (2 * Real.pi * ξ) : ℝ) : ℂ) by
            rw [one_div]; push_cast; rfl]
          ring

/-- **Witness bundle for `lem:ce-lift-assembly` (`ce_lift_proofs.tex`):**
for fixed `X_base`, source parameters `(p, γ, θ, lam)`, and `K`, provides the tuned
Hankel eigenfunction pair `(fp c, fm c)` for `c ≥ c_min` with `fm c 0 = 0 < fp c 0`,
strict positivity `0 < (fp - fm)/2` on `[0, ∞)`, and exact physical representation
`c^{1/3} ρ₀ (fp + fm)/2 = I_main[D_lift] + I_dual[S_c]`. -/
structure CeTwoEdgeLiftWitness (X_base : ℂ → ℂ) (p γ θ lam K : ℝ) where
  c_min : ℝ
  hc2k : 2000 ≤ c_min
  hcK : 8 * K ^ 3 ≤ c_min
  m_α : ℝ
  M_α : ℝ
  hm_α : 0 < m_α
  hM_α : m_α ≤ M_α
  α₁ : ℝ → ℝ
  hα₁_bd : ∀ {c : ℝ}, c_min ≤ c → m_α ≤ α₁ c ∧ α₁ c ≤ M_α
  fp : ℝ → ℝ → ℝ
  fm : ℝ → ℝ → ℝ
  hp : ∀ {c : ℝ}, c_min ≤ c → IsHankelEigenfn c 1 (fp c)
  hm : ∀ {c : ℝ}, c_min ≤ c → IsHankelEigenfn c (-1) (fm c)
  hfm0 : ∀ {c : ℝ}, c_min ≤ c → fm c 0 = 0
  hfp0 : ∀ {c : ℝ}, c_min ≤ c → 0 < fp c 0
  hhat_pos : ∀ {c Δ : ℝ}, c_min ≤ c → 0 ≤ Δ → 0 < (fp c Δ - fm c Δ) / 2
  hphys_eq : ∀ {c ξ : ℝ}, c_min ≤ c → 0 < ξ →
    ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * ((fp c (c * ξ) + fm c (c * ξ)) / 2) : ℝ) : ℂ) =
      iMain (fun u => (X_base (u : ℂ)).re + liftEps c * α₁ c * (airySeedG 0 (u : ℂ)).re)
          (ceBeta1 * K * liftEps c / 2) 4 c ξ +
        iDual (convSourceFamily p γ θ lam c) (ceBeta1 * K * liftEps c / 2) 4 c ξ
  horig_eq : ∀ {c : ℝ}, c_min ≤ c → (fp c 0 + fm c 0) / 2 = (fp c 0 - fm c 0) / 2

end FormalResearch.SignUncertainty

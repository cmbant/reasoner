module

public import FormalResearch.ModularBootstrap.Spin.Assembly
public import FormalResearch.ModularBootstrap.Spin.SpinS4Statements

/-!
# SPIN-S4 Lemma `s4:2.1` (Fold-localised negative mass at the `log n` scale)

Proves `spinS4_2_1 : SpinS4_2_1` (`spinning_s4.tex`, Theorem 2.1) by adapting the three-class
outward-telescoping argument of `Spin/Assembly.lean` (`spin_tip_localisation_quad`) to arbitrary
decay order `p > 0` at scale `δ = K_p n^{-2/3} log n` and arbitrary disc offset `x₁ ≤ ξ_* + C_x n^{-2/3}`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap

private lemma lintegral_prod_scale_s4 {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, f (c₁ * p.1, c₂ * p.2) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) * ∫⁻ p : ℝ × ℝ, f p := by
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    (MeasurableEquiv.mulLeft₀ c₁ hc₁.ne').prodCongr (MeasurableEquiv.mulLeft₀ c₂ hc₂.ne')
  have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (c₁⁻¹ * c₂⁻¹) • (volume : Measure (ℝ × ℝ)) := by
    have he : (e : ℝ × ℝ → ℝ × ℝ) = Prod.map (c₁ * ·) (c₂ * ·) := rfl
    rw [he, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ (measurable_const_mul c₁) (measurable_const_mul c₂),
      Real.map_volume_mul_left hc₁.ne', Real.map_volume_mul_left hc₂.ne',
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      abs_of_pos (inv_pos.mpr hc₁), abs_of_pos (inv_pos.mpr hc₂),
      ENNReal.ofReal_mul (inv_pos.mpr hc₁).le]
  have heq : ∫⁻ p : ℝ × ℝ, f (c₁ * p.1, c₂ * p.2) =
      ∫⁻ p : ℝ × ℝ, f p ∂(Measure.map e volume) :=
    (lintegral_map_equiv f e).symm
  rw [heq, hmp, lintegral_smul_measure, smul_eq_mul]

private lemma lintegral_xi_d_s4 (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ p : ℝ × ℝ, f p =
      ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, f (q.1 + q.2, q.1 - q.2) := by
  let e₁ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1 + q.2, q.2)
      invFun := fun q => (q.1 - q.2, q.2)
      left_inv := fun q => by ext <;> simp
      right_inv := fun q => by ext <;> simp
      measurable_toFun := (measurable_fst.add measurable_snd).prodMk measurable_snd
      measurable_invFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd }
  let e₂ : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
    { toFun := fun q => (q.1, q.1 - 2 * q.2)
      invFun := fun q => (q.1, (q.1 - q.2) / 2)
      left_inv := fun q => Prod.ext rfl (by ring)
      right_inv := fun q => Prod.ext rfl (by ring)
      measurable_toFun := measurable_fst.prodMk (measurable_fst.sub (measurable_const.mul measurable_snd))
      measurable_invFun := measurable_fst.prodMk ((measurable_fst.sub measurable_snd).div_const 2) }
  let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := e₁.trans e₂
  have h1 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ q : ℝ × ℝ, g (e₁ q) = ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₁ q)) (hg.comp e₁.measurable).aemeasurable,
      lintegral_lintegral_swap (f := fun x y => g (e₁ (x, y))) (hg.comp e₁.measurable).aemeasurable,
      lintegral_lintegral_swap (f := fun x y => g (x, y)) hg.aemeasurable]
    refine lintegral_congr fun y => ?_
    simpa [e₁] using lintegral_add_right_eq_self (fun x => g (x, y)) y
  have h2 : ∀ g : ℝ × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ q : ℝ × ℝ, g (e₂ q) = ENNReal.ofReal (1 / 2) * ∫⁻ q : ℝ × ℝ, g q := by
    intro g hg
    rw [Measure.volume_eq_prod, lintegral_prod _ hg.aemeasurable,
      lintegral_prod (fun q => g (e₂ q)) (hg.comp e₂.measurable).aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun x => ?_
    let e4 : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ (-2 : ℝ) (by norm_num)
    have hm4 : Measure.map e4 (volume : Measure ℝ) = ENNReal.ofReal (1 / 2) • (volume : Measure ℝ) := by
      have h := Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0)
      have habs : |(-2 : ℝ)⁻¹| = 1 / 2 := by norm_num
      rwa [habs] at h
    have hl : ∫⁻ y : ℝ, g (x, x + (-2 : ℝ) * y) =
        ENNReal.ofReal (1 / 2) * ∫⁻ z : ℝ, g (x, x + z) := by
      have h := (lintegral_map_equiv (μ := (volume : Measure ℝ)) (fun z => g (x, x + z)) e4).symm
      rwa [hm4, lintegral_smul_measure, smul_eq_mul] at h
    have hshift : ∫⁻ z : ℝ, g (x, x + z) = ∫⁻ z : ℝ, g (x, z) :=
      lintegral_add_left_eq_self (fun z => g (x, z)) x
    have heq : (fun y : ℝ => g (e₂ (x, y))) = fun y : ℝ => g (x, x + (-2 : ℝ) * y) := by
      ext y; simp [e₂, sub_eq_add_neg]
    rw [heq, hl, hshift]
  have hmap_e : Measure.map e (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2) • (volume : Measure (ℝ × ℝ)) := by
    ext s hs
    rw [Measure.map_apply e.measurable hs, smul_apply, smul_eq_mul]
    have h_ind := h1 (fun q => (s.indicator 1) (e₂ q)) ((measurable_const.indicator hs).comp e₂.measurable)
    have h_ind2 := h2 (s.indicator 1) (measurable_const.indicator hs)
    have h_lhs : ∫⁻ q : ℝ × ℝ, (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₂ (e₁ q)) = volume (e ⁻¹' s) := by
      have : (fun q => (s.indicator (1 : ℝ × ℝ → ℝ≥0∞)) (e₂ (e₁ q))) =
          (e ⁻¹' s).indicator (1 : ℝ × ℝ → ℝ≥0∞) := by ext q; rfl
      rw [this, lintegral_indicator_one (e.measurable hs)]
    rw [← h_lhs, h_ind, h_ind2, lintegral_indicator_one hs]
  have he_eq : ∀ q : ℝ × ℝ, e q = (q.1 + q.2, q.1 - q.2) := by
    intro q
    change e₂ (e₁ q) = (q.1 + q.2, q.1 - q.2)
    simp only [e₁, e₂, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
    exact Prod.ext rfl (by dsimp; ring)
  have hl : ∫⁻ q : ℝ × ℝ, f (q.1 + q.2, q.1 - q.2) =
      ENNReal.ofReal (1 / 2) * ∫⁻ p : ℝ × ℝ, f p := by
    have h := (lintegral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) f e).symm
    simp_rw [he_eq] at h
    rw [h, hmap_e, lintegral_smul_measure, smul_eq_mul]
  rw [hl, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

private lemma tsum_gamma_pair_s4 {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    (∑' q : ℕ × ℕ, ENNReal.ofReal (γ ^ q.1 * γ ^ q.2)) =
      ENNReal.ofReal ((1 - γ)⁻¹ * (1 - γ)⁻¹) := by
  have hs : Summable (fun q : ℕ × ℕ => γ ^ q.1 * γ ^ q.2) :=
    (summable_geometric_of_lt_one hγ0 hγ1).mul_of_nonneg (summable_geometric_of_lt_one hγ0 hγ1)
      (fun _ => pow_nonneg hγ0 _) (fun _ => pow_nonneg hγ0 _)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun q => mul_nonneg (pow_nonneg hγ0 _) (pow_nonneg hγ0 _)) hs,
    hs.tsum_prod' (fun m => (summable_geometric_of_lt_one hγ0 hγ1).mul_left (γ ^ m))]
  have hrow : (∑' m : ℕ, ∑' ℓ : ℕ, γ ^ m * γ ^ ℓ) = (1 - γ)⁻¹ * (1 - γ)⁻¹ := by
    simp_rw [tsum_mul_left, tsum_geometric_of_lt_one hγ0 hγ1]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hγ0 hγ1]
  rw [hrow]

private lemma spinS4_2_1_A1_bound
    {n k p C κ δ bStar D C_cls1 : ℝ} {Φ : ℝ × ℝ → ℝ}
    (ha2 : 2 < n / 12) (hn_pos : 0 < n) (hC0_nn : 0 ≤ C) (hκ0 : 0 < κ) (hδ_pos : 0 < δ)
    (hbStar_ge : xiStar / 2 ≤ bStar) (hbStar_le : bStar ≤ xiStar)
    (hD_eq : D = 3 * bStar / 4) (hC1_eq : C_cls1 = 4 * xiStar * (2 * xiStar + C) * C * 2)
    (hS_int : IntegrableOn (fun d : ℝ => spinSlitIntegral (n / 12) Φ d) (Icc (-D) D))
    (hS_le : ∫ d in Icc (-D) D, spinSlitIntegral (n / 12) Φ d ≤ C)
    (hS_ae : ∀ᵐ d ∂(volume.restrict (Icc (-D) D)),
      IntegrableOn (fun s : ℝ => (n / 12) * Real.exp (12 * (n / 12) * spinL s) *
        |spinDeltaA (n / 12) Φ (s + d) (s - d)|) {s : ℝ | bStar ≤ |s|})
    (hfold_b : ∀ ξ d : ℝ, |ξ| < bStar → |d| ≤ D →
      IntegrableOn (fun s : ℝ => (n / 12) * Real.exp (12 * (n / 12) * spinL s) *
        |spinDeltaA (n / 12) Φ (s + d) (s - d)|) {s : ℝ | bStar ≤ |s|} →
      (n / 12) * Real.exp (n * spinL ξ) * |spinDeltaA (n / 12) Φ (ξ + d) (ξ - d)| ≤
        C * n ^ k * (1 + spinSlitIntegral (n / 12) Φ d) * (bStar - |ξ|)⁻¹ *
          Real.exp (-κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2)))
    (hfold_exp : Real.exp (-κ * n * (δ / 4) ^ ((3 : ℝ) / 2)) ≤ n ^ (-(k + p + 4))) :
    let a := n / 12
    let A_cls1 : Set (ℝ × ℝ) :=
      {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ (y.1 + y.2) / 2 ≤ bStar - δ / 4 ∧ |(y.1 - y.2) / 2| ≤ D}
    ∫⁻ y in A_cls1, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
      ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) := by
  intro a A_cls1
  have hA1_meas : MeasurableSet A_cls1 :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet.inter
          (isClosed_le (((continuous_fst.sub continuous_snd).div_const 2).abs)
            continuous_const).measurableSet))
  let K_fac : ℝ := C * n ^ k * (δ / 4)⁻¹ * n ^ (-(k + p + 4))
  have hK_nn : 0 ≤ K_fac := by dsimp [K_fac]; positivity
  let F1 : ℝ × ℝ → ℝ≥0∞ := fun y =>
    if y ∈ A_cls1 then ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ ((y.1 - y.2) / 2))) else 0
  have hpt : ∀ ξ d : ℝ, (ξ + d, ξ - d) ∈ A_cls1 →
      IntegrableOn (fun s : ℝ => a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|)
        {s : ℝ | bStar ≤ |s|} →
      ENNReal.ofReal (|spinDeltaA a Φ (ξ + d) (ξ - d)| * spinWc a (ξ + d) * spinWc a (ξ - d)) ≤
        ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d)) := by
    intro ξ d hy hS_d
    refine ENNReal.ofReal_le_ofReal ?_
    have hsum : (ξ + d + (ξ - d)) / 2 = ξ := by ring
    have hdiff : (ξ + d - (ξ - d)) / 2 = d := by ring
    have hξ_pos : 0 < ξ := by linarith [hy.1, hy.2.1]
    have hξ_le : ξ ≤ bStar - δ / 4 := by simpa [hsum] using hy.2.2.1
    have hξ_lt : |ξ| < bStar := by rw [abs_of_pos hξ_pos]; linarith [hξ_le, hδ_pos]
    have hd_le : |d| ≤ D := by simpa [hdiff] using hy.2.2.2
    have hδy_ge : δ / 4 ≤ bStar - |ξ| := by rw [abs_of_pos hξ_pos]; linarith [hξ_le]
    have hw : spinWc a (ξ + d) * spinWc a (ξ - d) ≤ a * Real.exp (n * spinL ξ) := by
      have h := spinWc_mul_le_exp ha2.le hy.1.le hy.2.1.le
      simpa [a, hsum, show 12 * (n / 12) = n by ring] using h
    have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
      unfold spinSlitIntegral
      exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet fun _ _ => by positivity
    have hfb := hfold_b ξ d hξ_lt hd_le hS_d
    have hinv_le : (bStar - |ξ|)⁻¹ ≤ (δ / 4)⁻¹ := inv_anti₀ (by positivity) hδy_ge
    have hexp_mono : Real.exp (-κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2)) ≤
        Real.exp (-κ * n * (δ / 4) ^ ((3 : ℝ) / 2)) := by
      refine Real.exp_le_exp.mpr ?_
      have hpow_le : (δ / 4) ^ ((3 : ℝ) / 2) ≤ (bStar - |ξ|) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow (by positivity) hδy_ge (by norm_num)
      have hmul : κ * n * (δ / 4) ^ ((3 : ℝ) / 2) ≤ κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left hpow_le (mul_pos hκ0 hn_pos).le
      linarith
    have hfb' : a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| ≤
        C * n ^ k * (1 + spinSlitIntegral a Φ d) * (bStar - |ξ|)⁻¹ *
          Real.exp (-κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2)) := hfb
    calc |spinDeltaA a Φ (ξ + d) (ξ - d)| * spinWc a (ξ + d) * spinWc a (ξ - d)
        = |spinDeltaA a Φ (ξ + d) (ξ - d)| * (spinWc a (ξ + d) * spinWc a (ξ - d)) := by ring
      _ ≤ |spinDeltaA a Φ (ξ + d) (ξ - d)| * (a * Real.exp (n * spinL ξ)) :=
          mul_le_mul_of_nonneg_left hw (abs_nonneg _)
      _ = a * Real.exp (n * spinL ξ) * |spinDeltaA a Φ (ξ + d) (ξ - d)| := by ring
      _ ≤ C * n ^ k * (1 + spinSlitIntegral a Φ d) * (bStar - |ξ|)⁻¹ *
            Real.exp (-κ * n * (bStar - |ξ|) ^ ((3 : ℝ) / 2)) := hfb'
      _ ≤ C * n ^ k * (1 + spinSlitIntegral a Φ d) * (δ / 4)⁻¹ *
            Real.exp (-κ * n * (δ / 4) ^ ((3 : ℝ) / 2)) := by gcongr
      _ ≤ C * n ^ k * (1 + spinSlitIntegral a Φ d) * (δ / 4)⁻¹ * n ^ (-(k + p + 4)) := by gcongr
      _ = K_fac * (1 + spinSlitIntegral a Φ d) := by dsimp [K_fac]; ring
  have hS_ae_prod : ∀ᵐ q : ℝ × ℝ ∂volume, q.2 ∈ Icc (-D) D →
      IntegrableOn (fun s : ℝ => a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + q.2) (s - q.2)|)
        {s : ℝ | bStar ≤ |s|} := by
    rw [ae_restrict_iff' measurableSet_Icc] at hS_ae
    rw [Measure.volume_eq_prod]
    exact Measure.quasiMeasurePreserving_snd.ae hS_ae
  have hstep_ae : ∫⁻ y in A_cls1,
        ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
      ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, F1 (q.1 + q.2, q.1 - q.2) := by
    rw [← lintegral_indicator hA1_meas,
      lintegral_xi_d_s4 (A_cls1.indicator (fun y =>
        ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)))]
    refine mul_le_mul_of_nonneg_left (lintegral_mono_ae ?_) zero_le
    filter_upwards [hS_ae_prod] with q hq_int
    by_cases hq : (q.1 + q.2, q.1 - q.2) ∈ A_cls1
    · have hdiff : (q.1 + q.2 - (q.1 - q.2)) / 2 = q.2 := by ring
      have hq2 : q.2 ∈ Icc (-D) D := by have := hq.2.2.2; rw [hdiff] at this; exact abs_le.mp this
      simp only [Set.indicator_of_mem hq, F1, hq, ↓reduceIte, hdiff]
      exact hpt q.1 q.2 hq (hq_int hq2)
    · simp only [Set.indicator_of_notMem hq, F1, hq, ↓reduceIte, le_rfl]
  refine hstep_ae.trans ?_
  have hdom : ∀ q : ℝ × ℝ, F1 (q.1 + q.2, q.1 - q.2) ≤
      (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) q.1 *
      ((Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) q.2) := by
    intro q
    by_cases hq : (q.1 + q.2, q.1 - q.2) ∈ A_cls1
    · have hsum : (q.1 + q.2 + (q.1 - q.2)) / 2 = q.1 := by ring
      have hdiff : (q.1 + q.2 - (q.1 - q.2)) / 2 = q.2 := by ring
      have hq1 : q.1 ∈ Icc (0 : ℝ) bStar :=
        ⟨by linarith [hq.1, hq.2.1], by have := hq.2.2.1; rw [hsum] at this; linarith [hδ_pos]⟩
      have hq2 : q.2 ∈ Icc (-D) D := by have := hq.2.2.2; rw [hdiff] at this; exact abs_le.mp this
      simp only [F1, hq, ↓reduceIte, Set.indicator_of_mem hq1, Set.indicator_of_mem hq2,
        Pi.one_apply, one_mul, hdiff, le_rfl]
    · simp only [F1, hq, ↓reduceIte, zero_le]
  have hprod_int : ∫⁻ q : ℝ × ℝ,
      (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) q.1 *
      ((Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) q.2) =
      (∫⁻ ξ : ℝ, (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) ξ) *
      (∫⁻ d : ℝ, (Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) d) := by
    rw [Measure.volume_eq_prod]
    refine lintegral_prod_mul (measurable_const.indicator measurableSet_Icc).aemeasurable ?_
    rw [aemeasurable_indicator_iff measurableSet_Icc]
    exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      ((aemeasurable_const.add hS_int.aestronglyMeasurable.aemeasurable).const_mul K_fac)
  have hξ_val : ∫⁻ ξ : ℝ, (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) ξ = ENNReal.ofReal bStar := by
    rw [lintegral_indicator_one measurableSet_Icc, Real.volume_Icc, sub_zero]
  have hd_val : ∫⁻ d : ℝ,
      (Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) d ≤
      ENNReal.ofReal (K_fac * (2 * D + C)) := by
    rw [lintegral_indicator measurableSet_Icc]
    have hint_1S : IntegrableOn (fun d : ℝ => K_fac * (1 + spinSlitIntegral a Φ d)) (Icc (-D) D) :=
      ((integrableOn_const (hs := measure_Icc_lt_top.ne)).add hS_int).const_mul K_fac
    have hnn_1S : ∀ d ∈ Icc (-D) D, 0 ≤ K_fac * (1 + spinSlitIntegral a Φ d) := fun d _ => by
      have hS_nn : 0 ≤ spinSlitIntegral a Φ d := by
        unfold spinSlitIntegral
        exact setIntegral_nonneg (isClosed_le continuous_const continuous_abs).measurableSet fun _ _ => by positivity
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint_1S (ae_restrict_of_forall_mem measurableSet_Icc hnn_1S)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul, integral_add (integrableOn_const (hs := measure_Icc_lt_top.ne)) hS_int]
    have h1 : ∫ _ in Icc (-D) D, (1 : ℝ) = 2 * D := by
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by rw [hD_eq]; linarith [hbStar_ge, xiStar_pos])]
      ring
    rw [h1]; exact mul_le_mul_of_nonneg_left (by linarith) hK_nn
  calc ENNReal.ofReal 2 * ∫⁻ q : ℝ × ℝ, F1 (q.1 + q.2, q.1 - q.2)
      ≤ ENNReal.ofReal 2 *
          ((∫⁻ ξ : ℝ, (Icc (0 : ℝ) bStar).indicator (1 : ℝ → ℝ≥0∞) ξ) *
           (∫⁻ d : ℝ, (Icc (-D) D).indicator (fun d => ENNReal.ofReal (K_fac * (1 + spinSlitIntegral a Φ d))) d)) := by
        rw [← hprod_int]; gcongr; exact hdom _
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal bStar * ENNReal.ofReal (K_fac * (2 * D + C))) := by
        rw [hξ_val]; gcongr
    _ = ENNReal.ofReal (2 * (bStar * (K_fac * (2 * D + C)))) := by
        rw [← ENNReal.ofReal_mul (by linarith [hbStar_ge, xiStar_pos]), ← ENNReal.ofReal_mul (by norm_num)]
    _ ≤ ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hD_le : D ≤ xiStar := by rw [hD_eq]; linarith
        have hK_eq : K_fac = C * n ^ k * (4 * δ⁻¹) * n ^ (-(k + p + 4)) := by
          dsimp [K_fac]; rw [inv_div]; ring
        rw [hK_eq]
        have h2D : 2 * D + C ≤ 2 * xiStar + C := by linarith
        have hfac_nn : 0 ≤ C * n ^ k * (4 * δ⁻¹) * n ^ (-(k + p + 4)) := by positivity
        have h2D_nn : 0 ≤ 2 * D + C := by rw [hD_eq]; linarith [hbStar_ge, xiStar_pos, hC0_nn]
        have hbStar_nn : 0 ≤ bStar := by linarith [hbStar_ge, xiStar_pos]
        have hxi_nn : 0 ≤ xiStar := xiStar_pos.le
        calc 2 * (bStar * (C * n ^ k * (4 * δ⁻¹) * n ^ (-(k + p + 4)) * (2 * D + C)))
            ≤ 2 * (xiStar * (C * n ^ k * (4 * δ⁻¹) * n ^ (-(k + p + 4)) * (2 * xiStar + C))) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              refine mul_le_mul hbStar_le (mul_le_mul_of_nonneg_left h2D hfac_nn)
                (mul_nonneg hfac_nn h2D_nn) hxi_nn
          _ = C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4)) := by rw [hC1_eq]; ring

private lemma spinS4_2_1_q_term
    {n δ bStar x₁ C_x A1_bound : ℝ} {Φ : ℝ × ℝ → ℝ}
    (ha2 : 2 < n / 12) (hn_pos : 0 < n) (hδ_pos : 0 < δ) (hx₁0 : 0 ≤ x₁)
    (hx₁_ub : x₁ ≤ xiStar + C_x * n ^ (-(2 / 3 : ℝ)))
    (hbStar_ge : xiStar / 2 ≤ bStar)
    (hxi_delta : xiStar - δ ≤ bStar - δ / 2)
    (hCx_sm : max C_x 0 * n ^ (-(2 / 3 : ℝ)) < (3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4)
    (hδ_gap : δ < (3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4)
    (hΦ : SpinTestClass (n / 12) Φ)
    (hA1_bound :
      ∫⁻ y in {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧
          (y.1 + y.2) / 2 ≤ bStar - δ / 4 ∧ |(y.1 - y.2) / 2| ≤ 3 * bStar / 4},
        ENNReal.ofReal (|spinDeltaA (n / 12) Φ y.1 y.2| * spinWc (n / 12) y.1 * spinWc (n / 12) y.2) ≤
        ENNReal.ofReal A1_bound)
    (hDelta_en :
      ∫⁻ y : ℝ × ℝ,
        ENNReal.ofReal (|spinDeltaA (n / 12) Φ y.1 y.2| * spinWc (n / 12) y.1 * spinWc (n / 12) y.2) ≤
        ENNReal.ofReal 4)
    (q : ℕ × ℕ) :
    let a := n / 12
    let E : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧
      (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ (q.1 + q.2) / 2 < xiStar - δ}
    ∫⁻ p in E,
      ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
        spinWc a p.1 * spinWc a p.2) ≤
    ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
      (ENNReal.ofReal A1_bound + ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 6)))) := by
  intro a E
  let D : ℝ := 3 * bStar / 4
  let A_cls1 : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ (y.1 + y.2) / 2 ≤ bStar - δ / 4 ∧ |(y.1 - y.2) / 2| ≤ D}
  have hE_meas : MeasurableSet E :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet.inter
        (isOpen_lt ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet))
  have hA1_meas : MeasurableSet A_cls1 :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet.inter
          (isClosed_le (((continuous_fst.sub continuous_snd).div_const 2).abs)
            continuous_const).measurableSet))
  have hsqrt2 : Real.sqrt 2 < 149 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hdiff_pos : 0 < (3 / 2 - Real.sqrt 2) * (xiStar / 2) :=
    mul_pos (by linarith) (half_pos xiStar_pos)
  have hlam1 : 0 < spinLambda a ^ q.1 := pow_pos (by linarith [spinLambda_gt_one ha2]) _
  have hlam2 : 0 < spinLambda a ^ q.2 := pow_pos (by linarith [spinLambda_gt_one ha2]) _
  have hlam1_ge : 1 ≤ spinLambda a ^ q.1 := one_le_pow₀ (spinLambda_gt_one ha2).le
  have hlam2_ge : 1 ≤ spinLambda a ^ q.2 := one_le_pow₀ (spinLambda_gt_one ha2).le
  let g1 : ℝ × ℝ → ℝ≥0∞ := fun y =>
    A_cls1.indicator (fun y => ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)) y
  let g2 : ℝ × ℝ → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (Real.exp (-(π * n * δ / 6))) *
      ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)
  have hpt_q : ∀ x ∈ E,
      ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * x.1) (spinLambda a ^ q.2 * x.2)| *
        spinWc a x.1 * spinWc a x.2) ≤
      g1 (spinLambda a ^ q.1 * x.1, spinLambda a ^ q.2 * x.2) +
      g2 (spinLambda a ^ q.1 * x.1, spinLambda a ^ q.2 * x.2) := by
    intro x hx
    set y1 := spinLambda a ^ q.1 * x.1
    set y2 := spinLambda a ^ q.2 * x.2
    have hy1_pos : 0 < y1 := mul_pos hlam1 hx.1
    have hy2_pos : 0 < y2 := mul_pos hlam2 hx.2.1
    have hpx1 : x.1 ≤ y1 := le_mul_of_one_le_left hx.1.le hlam1_ge
    have hpx2 : x.2 ≤ y2 := le_mul_of_one_le_left hx.2.1.le hlam2_ge
    have hw_ratio : spinWc a x.1 * spinWc a x.2 ≤
        Real.exp (-(4 * π * a * ((y1 - x.1) + (y2 - x.2)))) * (spinWc a y1 * spinWc a y2) := by
      have hw1 := spinWc_exp_mono ha2.le hx.1.le hpx1
      have hw2 := spinWc_exp_mono ha2.le hx.2.1.le hpx2
      calc spinWc a x.1 * spinWc a x.2
          ≤ (Real.exp (-(4 * π * a * (y1 - x.1))) * spinWc a y1) *
              (Real.exp (-(4 * π * a * (y2 - x.2))) * spinWc a y2) :=
            mul_le_mul hw1 hw2 (spinWc_nonneg ha2.le x.2)
              (mul_nonneg (Real.exp_pos _).le (spinWc_nonneg ha2.le y1))
        _ = Real.exp (-(4 * π * a * (y1 - x.1)) + -(4 * π * a * (y2 - x.2))) *
              (spinWc a y1 * spinWc a y2) := by rw [Real.exp_add]; ring
        _ = Real.exp (-(4 * π * a * ((y1 - x.1) + (y2 - x.2)))) *
              (spinWc a y1 * spinWc a y2) := by congr 2; ring
    by_cases hy : (y1, y2) ∈ A_cls1
    · refine le_trans ?_ le_self_add
      dsimp [g1]
      rw [Set.indicator_of_mem hy]
      refine ENNReal.ofReal_le_ofReal ?_
      have hexp1 : Real.exp (-(4 * π * a * ((y1 - x.1) + (y2 - x.2)))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have ha0 : 0 ≤ a := by dsimp [a]; linarith [ha2]
        have hsum_nn : 0 ≤ (y1 - x.1) + (y2 - x.2) := by linarith [hpx1, hpx2]
        have hprod_nn : 0 ≤ 4 * π * a * ((y1 - x.1) + (y2 - x.2)) := by positivity
        linarith
      have hw_le : spinWc a x.1 * spinWc a x.2 ≤ spinWc a y1 * spinWc a y2 :=
        hw_ratio.trans (mul_le_of_le_one_left
          (mul_nonneg (spinWc_nonneg ha2.le y1) (spinWc_nonneg ha2.le y2)) hexp1)
      calc |spinDeltaA a Φ y1 y2| * spinWc a x.1 * spinWc a x.2
          = |spinDeltaA a Φ y1 y2| * (spinWc a x.1 * spinWc a x.2) := by ring
        _ ≤ |spinDeltaA a Φ y1 y2| * (spinWc a y1 * spinWc a y2) :=
            mul_le_mul_of_nonneg_left hw_le (abs_nonneg _)
        _ = |spinDeltaA a Φ y1 y2| * spinWc a y1 * spinWc a y2 := by ring
    · refine le_trans ?_ le_add_self
      dsimp [g2]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hgap : δ / 2 ≤ (y1 - x.1) + (y2 - x.2) := by
        by_contra hlt
        push Not at hlt
        have h1 : (y1 + y2) / 2 ≤ bStar - δ / 4 := by linarith [hx.2.2.2, hxi_delta]
        have h2 : |(y1 - y2) / 2| ≤ D := by
          by_contra hd_gt
          push Not at hd_gt
          dsimp [D] at hd_gt
          have hmax_y : 3 * bStar / 2 < max y1 y2 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hd_gt
            rcases le_total y1 y2 with hle | hle
            · rw [max_eq_right hle, abs_of_nonpos (sub_nonpos.mpr hle)] at *
              linarith [hy1_pos, hy2_pos]
            · rw [max_eq_left hle, abs_of_nonneg (sub_nonneg.mpr hle)] at *
              linarith [hy1_pos, hy2_pos]
          have hx_ub : x₁ ≤ xiStar + max C_x 0 * n ^ (-(2 / 3 : ℝ)) :=
            hx₁_ub.trans (by
              have hrp : 0 ≤ n ^ (-(2 / 3 : ℝ)) := Real.rpow_nonneg hn_pos.le _
              gcongr; exact le_max_left _ _)
          have hmax_x : max x.1 x.2 ≤ Real.sqrt 2 * (xiStar + max C_x 0 * n ^ (-(2 / 3 : ℝ))) := by
            have hsq_le : x.1 ^ 2 ≤ 2 * x₁ ^ 2 ∧ x.2 ^ 2 ≤ 2 * x₁ ^ 2 := by
              constructor <;> nlinarith [hx.2.2.1, sq_nonneg x.1, sq_nonneg x.2]
            have hr2 : Real.sqrt (2 * x₁ ^ 2) = Real.sqrt 2 * x₁ := by
              rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hx₁0]
            have hle1 : x.1 ≤ Real.sqrt 2 * x₁ := by
              rw [← hr2]; exact (Real.le_sqrt_of_sq_le hsq_le.1)
            have hle2 : x.2 ≤ Real.sqrt 2 * x₁ := by
              rw [← hr2]; exact (Real.le_sqrt_of_sq_le hsq_le.2)
            exact max_le (hle1.trans (mul_le_mul_of_nonneg_left hx_ub (Real.sqrt_nonneg _)))
              (hle2.trans (mul_le_mul_of_nonneg_left hx_ub (Real.sqrt_nonneg _)))
          have hdiff_y : 3 * bStar / 2 - Real.sqrt 2 * (xiStar + max C_x 0 * n ^ (-(2 / 3 : ℝ))) <
              max y1 y2 - max x.1 x.2 := by linarith
          have hbig_gap : δ / 2 ≤ 3 * bStar / 2 - Real.sqrt 2 * (xiStar + max C_x 0 * n ^ (-(2 / 3 : ℝ))) := by
            have h3 : Real.sqrt 2 * (max C_x 0 * n ^ (-(2 / 3 : ℝ))) ≤
                2 * ((3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4) := by
              have hrp : 0 ≤ max C_x 0 * n ^ (-(2 / 3 : ℝ)) :=
                mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hn_pos.le _)
              nlinarith [hsqrt2, hCx_sm, hrp]
            have h1' : (3 / 2 - Real.sqrt 2) * (xiStar / 2) ≤ 3 * bStar / 2 - Real.sqrt 2 * xiStar := by
              have hb2' : xiStar / 2 ≤ bStar := hbStar_ge
              nlinarith [xiStar_pos]
            have h2' : 0 ≤ (3 / 2 - Real.sqrt 2) * (xiStar / 2) := hdiff_pos.le
            have h4 : δ / 2 ≤ (3 / 2 - Real.sqrt 2) * (xiStar / 2) / 8 := by linarith [hδ_gap]
            calc δ / 2 ≤ (3 / 2 - Real.sqrt 2) * (xiStar / 2) - 2 * ((3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4) := by linarith
              _ ≤ 3 * bStar / 2 - Real.sqrt 2 * xiStar - Real.sqrt 2 * (max C_x 0 * n ^ (-(2 / 3 : ℝ))) := by linarith
              _ = 3 * bStar / 2 - Real.sqrt 2 * (xiStar + max C_x 0 * n ^ (-(2 / 3 : ℝ))) := by ring
          have hmax_le : max y1 y2 - max x.1 x.2 ≤ (y1 - x.1) + (y2 - x.2) := by
            rcases le_total y1 y2 with hle | hle
            · rw [max_eq_right hle]
              have := le_max_right x.1 x.2
              linarith [hpx1]
            · rw [max_eq_left hle]
              have := le_max_left x.1 x.2
              linarith [hpx2]
          linarith
        exact hy ⟨hy1_pos, hy2_pos, h1, h2⟩
      have hexp_le : Real.exp (-(4 * π * a * ((y1 - x.1) + (y2 - x.2)))) ≤
          Real.exp (-(π * n * δ / 6)) := by
        refine Real.exp_le_exp.mpr ?_
        have h4a : 4 * π * a = π * n / 3 := by dsimp [a]; ring
        rw [h4a]
        have hpn : 0 ≤ π * n / 3 := by positivity
        have : π * n / 3 * (δ / 2) ≤ π * n / 3 * ((y1 - x.1) + (y2 - x.2)) :=
          mul_le_mul_of_nonneg_left hgap hpn
        linarith
      have hw_le : spinWc a x.1 * spinWc a x.2 ≤
          Real.exp (-(π * n * δ / 6)) * (spinWc a y1 * spinWc a y2) :=
        hw_ratio.trans (mul_le_mul_of_nonneg_right hexp_le
          (mul_nonneg (spinWc_nonneg ha2.le y1) (spinWc_nonneg ha2.le y2)))
      calc |spinDeltaA a Φ y1 y2| * spinWc a x.1 * spinWc a x.2
          = |spinDeltaA a Φ y1 y2| * (spinWc a x.1 * spinWc a x.2) := by ring
        _ ≤ |spinDeltaA a Φ y1 y2| * (Real.exp (-(π * n * δ / 6)) * (spinWc a y1 * spinWc a y2)) :=
            mul_le_mul_of_nonneg_left hw_le (abs_nonneg _)
        _ = Real.exp (-(π * n * δ / 6)) * (|spinDeltaA a Φ y1 y2| * spinWc a y1 * spinWc a y2) := by
            ring
  have hinv_eq : (spinLambda a ^ q.1)⁻¹ * (spinLambda a ^ q.2)⁻¹ =
      spinGamma a ^ q.1 * spinGamma a ^ q.2 := by unfold spinLambda; simp [inv_pow]
  calc ∫⁻ p in E,
          ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
            spinWc a p.1 * spinWc a p.2)
      ≤ ∫⁻ p : ℝ × ℝ,
          (g1 (spinLambda a ^ q.1 * p.1, spinLambda a ^ q.2 * p.2) +
           g2 (spinLambda a ^ q.1 * p.1, spinLambda a ^ q.2 * p.2)) := by
        rw [← lintegral_indicator hE_meas]
        refine lintegral_mono fun p => ?_
        by_cases hp : p ∈ E
        · simp only [Set.indicator_of_mem hp]; exact hpt_q p hp
        · simp [Set.indicator_of_notMem hp]
    _ = ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) * ∫⁻ y : ℝ × ℝ, (g1 y + g2 y) := by
        rw [lintegral_prod_scale_s4 hlam1 hlam2 (fun y => g1 y + g2 y), hinv_eq]
    _ = ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) * ((∫⁻ y : ℝ × ℝ, g1 y) + ∫⁻ y : ℝ × ℝ, g2 y) := by
        congr 1
        refine lintegral_add_left' ?_ _
        have hG : Continuous (fun p : ℝ × ℝ => spinG a Φ p.1 p.2) := by
          unfold spinG; exact hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
        have hDa : Continuous (fun p : ℝ × ℝ => spinDa a Φ p.1 p.2) := by
          unfold spinDa
          exact (((hG.sub (hG.comp ((continuous_const.mul continuous_fst).prodMk continuous_snd))).sub
            (hG.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))).add
            (hG.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))))
        have hDelta : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ p.1 p.2) := by
          unfold spinDeltaA
          exact hDa.comp ((continuous_const.mul continuous_fst).prodMk (continuous_const.mul continuous_snd))
        have hWc : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
        exact ((ENNReal.continuous_ofReal.comp
          ((hDelta.abs.mul (hWc.comp continuous_fst)).mul (hWc.comp continuous_snd))).measurable.indicator
            hA1_meas).aemeasurable
    _ ≤ ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
          (ENNReal.ofReal A1_bound + ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 6)))) := by
        gcongr
        · rw [lintegral_indicator hA1_meas]; exact hA1_bound
        · dsimp [g2]
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          calc ENNReal.ofReal (Real.exp (-(π * n * δ / 6))) *
                  ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2)
              ≤ ENNReal.ofReal (Real.exp (-(π * n * δ / 6))) * ENNReal.ofReal 4 := by gcongr
            _ = ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 6))) := by
                rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]

/-- **`s4:2.1` (Theorem 2.1, fold-localised negative mass at the `log n` scale).** -/
theorem spinS4_2_1 : SpinS4_2_1 := by
  intro C_x p hp
  obtain ⟨k, C, κ, _δ₀, n₀, hk0, _hC0, hκ0, hn₀, hS22b_main⟩ := spinS22b
  have hC0_nn : 0 ≤ C := _hC0.le
  let M_exp : ℝ := (k + p + 4) / (κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)))
  have hM_pos : 0 < M_exp := by positivity
  let K_p : ℝ := max 1 (M_exp ^ ((2 : ℝ) / 3))
  have hK_pos : 0 < K_p := by positivity
  have hK_exp : k + p + 4 ≤ κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) * K_p ^ ((3 : ℝ) / 2) := by
    have h1 : M_exp ≤ K_p ^ ((3 : ℝ) / 2) := by
      calc M_exp = (M_exp ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2) := by
            rw [← Real.rpow_mul hM_pos.le]; norm_num
        _ ≤ K_p ^ ((3 : ℝ) / 2) :=
            Real.rpow_le_rpow (by positivity) (le_max_right _ _) (by norm_num)
    have hfac : 0 < κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
    calc k + p + 4 = (κ * (4 : ℝ) ^ (-(3 / 2 : ℝ))) * M_exp := by
          dsimp [M_exp]; field_simp [hfac.ne']
      _ ≤ (κ * (4 : ℝ) ^ (-(3 / 2 : ℝ))) * K_p ^ ((3 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left h1 hfac.le
  let C_cls1 : ℝ := 4 * xiStar * (2 * xiStar + C) * C * 2
  have hC1_nn : 0 ≤ C_cls1 := by dsimp [C_cls1]; have := xiStar_pos; positivity
  have htend_inv_n : Tendsto (fun n : ℝ => n⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have htend_delta : Tendsto (fun n : ℝ => K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) atTop (𝓝 0) := by
    have ht0 : Tendsto (fun n : ℝ => Real.log n / n ^ (2 / 3 : ℝ)) atTop (𝓝 0) :=
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).tendsto_div_nhds_zero
    have h_eq : (fun n : ℝ => K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) =ᶠ[atTop]
        fun n => K_p * (Real.log n / n ^ (2 / 3 : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      rw [Real.rpow_neg hn.le, div_eq_mul_inv]; ring
    have hlim : Tendsto (fun n : ℝ => K_p * (Real.log n / n ^ (2 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := K_p)).mul ht0
    exact hlim.congr' h_eq.symm
  have htend_Cx : Tendsto (fun n : ℝ => max C_x 0 * n ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℝ => n ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    simpa using (tendsto_const_nhds (x := max C_x 0)).mul h0
  have htend_n_delta : Tendsto (fun n : ℝ => n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n)) atTop atTop := by
    have h13 : Tendsto (fun n : ℝ => n ^ (1 / 3 : ℝ)) atTop atTop :=
      tendsto_rpow_atTop (by norm_num)
    have hev : ∀ᶠ n : ℝ in atTop,
        K_p * n ^ (1 / 3 : ℝ) ≤ n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) := by
      filter_upwards [eventually_ge_atTop (Real.exp 1)] with n hn
      have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos 1) hn
      have hlog1 : 1 ≤ Real.log n := by
        have := Real.log_le_log (Real.exp_pos 1) hn; rwa [Real.log_exp] at this
      have hn_pow : n * n ^ (-(2 / 3 : ℝ)) = n ^ (1 / 3 : ℝ) := by
        calc n * n ^ (-(2 / 3 : ℝ)) = n ^ (1 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
          _ = n ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := by rw [Real.rpow_add hn0]
          _ = n ^ (1 / 3 : ℝ) := by norm_num
      calc K_p * n ^ (1 / 3 : ℝ) = (n * n ^ (-(2 / 3 : ℝ))) * K_p * 1 := by rw [hn_pow]; ring
        _ ≤ (n * n ^ (-(2 / 3 : ℝ))) * K_p * Real.log n := by gcongr
        _ = n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) := by ring
    exact tendsto_atTop_mono' atTop hev (h13.const_mul_atTop hK_pos)
  have htend_t1 : ∀ᶠ n : ℝ in atTop,
      C_cls1 * n ^ (k + 2) * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n)⁻¹ * n ^ (-(k + p + 4)) ≤
        (1 / 2 : ℝ) * n ^ (-p) := by
    have hq : Tendsto (fun n : ℝ => (C_cls1 / K_p) * n ^ (-(4 / 3 : ℝ))) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := C_cls1 / K_p)).mul (tendsto_rpow_neg_atTop (by norm_num))
    filter_upwards [eventually_ge_atTop (Real.exp 1), hq.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with n hn hq_lt
    have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos 1) hn
    have hlog1 : 1 ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos 1) hn; rwa [Real.log_exp] at this
    have hinv_le : (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n)⁻¹ ≤ K_p⁻¹ * n ^ (2 / 3 : ℝ) := by
      rw [mul_inv, mul_inv, Real.rpow_neg hn0.le, inv_inv, mul_assoc]
      have h1 : (Real.log n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlog1
      calc K_p⁻¹ * (n ^ (2 / 3 : ℝ) * (Real.log n)⁻¹)
          ≤ K_p⁻¹ * (n ^ (2 / 3 : ℝ) * 1) := by gcongr
        _ = K_p⁻¹ * n ^ (2 / 3 : ℝ) := by ring
    have hpow_comb : n ^ (k + 2) * n ^ (2 / 3 : ℝ) * n ^ (-(k + p + 4)) =
        n ^ (-(4 / 3 : ℝ)) * n ^ (-p) := by
      rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_add hn0]
      congr 1; ring
    calc C_cls1 * n ^ (k + 2) * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n)⁻¹ * n ^ (-(k + p + 4))
        ≤ C_cls1 * n ^ (k + 2) * (K_p⁻¹ * n ^ (2 / 3 : ℝ)) * n ^ (-(k + p + 4)) := by gcongr
      _ = (C_cls1 / K_p) * n ^ (-(4 / 3 : ℝ)) * n ^ (-p) := by
          rw [div_eq_mul_inv]; calc C_cls1 * n ^ (k + 2) * (K_p⁻¹ * n ^ (2 / 3 : ℝ)) * n ^ (-(k + p + 4))
              = (C_cls1 * K_p⁻¹) * (n ^ (k + 2) * n ^ (2 / 3 : ℝ) * n ^ (-(k + p + 4))) := by ring
            _ = (C_cls1 * K_p⁻¹) * (n ^ (-(4 / 3 : ℝ)) * n ^ (-p)) := by rw [hpow_comb]
            _ = _ := by ring
      _ ≤ (1 / 2 : ℝ) * n ^ (-p) := mul_le_mul_of_nonneg_right hq_lt.le (Real.rpow_nonneg hn0.le _)
  have htend_t2 : ∀ᶠ n : ℝ in atTop,
      4 * n ^ 2 * Real.exp (-(π * n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) / 6)) ≤
        (1 / 2 : ℝ) * n ^ (-p) := by
    have h13_lim : Tendsto (fun n : ℝ => n ^ (1 / 3 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
    filter_upwards [eventually_ge_atTop (Real.exp 1),
      eventually_ge_atTop (8 : ℝ),
      (h13_lim.const_mul_atTop (by positivity : 0 < π * K_p / 6)).eventually_ge_atTop (p + 3)]
      with n hn_e hn8 hbig
    have hn0 : 0 < n := lt_of_lt_of_le (Real.exp_pos 1) hn_e
    have hlog1 : 1 ≤ Real.log n := by
      have := Real.log_le_log (Real.exp_pos 1) hn_e; rwa [Real.log_exp] at this
    have hn_pow : n * n ^ (-(2 / 3 : ℝ)) = n ^ (1 / 3 : ℝ) := by
      calc n * n ^ (-(2 / 3 : ℝ)) = n ^ (1 : ℝ) * n ^ (-(2 / 3 : ℝ)) := by rw [Real.rpow_one]
        _ = n ^ ((1 : ℝ) + -(2 / 3 : ℝ)) := by rw [Real.rpow_add hn0]
        _ = n ^ (1 / 3 : ℝ) := by norm_num
    have hexp_arg : (p + 3) * Real.log n ≤ π * n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) / 6 := by
      calc (p + 3) * Real.log n ≤ (π * K_p / 6 * n ^ (1 / 3 : ℝ)) * Real.log n :=
            mul_le_mul_of_nonneg_right hbig (by linarith)
        _ = π * (n * n ^ (-(2 / 3 : ℝ))) * K_p * Real.log n / 6 := by rw [hn_pow]; ring
        _ = π * n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) / 6 := by ring
    have hexp_le : Real.exp (-(π * n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) / 6)) ≤
        n ^ (-(p + 3)) := by
      calc Real.exp (-(π * n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) / 6))
          ≤ Real.exp (-(p + 3) * Real.log n) := Real.exp_le_exp.mpr (by linarith)
        _ = n ^ (-(p + 3)) := by rw [Real.rpow_def_of_pos hn0]; congr 1; ring
    have hprod_le : 4 * n ^ 2 * n ^ (-(p + 3)) = 4 * n⁻¹ * n ^ (-p) := by
      calc 4 * n ^ 2 * n ^ (-(p + 3)) = 4 * (n ^ (2 : ℝ) * n ^ (-(p + 3))) := by
            rw [← Real.rpow_natCast n 2]; ring
        _ = 4 * n ^ ((2 : ℝ) + -(p + 3)) := by rw [Real.rpow_add hn0]
        _ = 4 * n ^ ((-1 : ℝ) + -p) := by congr 2; ring
        _ = 4 * (n ^ (-1 : ℝ) * n ^ (-p)) := by rw [Real.rpow_add hn0]
        _ = 4 * n⁻¹ * n ^ (-p) := by rw [Real.rpow_neg_one]; ring
    calc 4 * n ^ 2 * Real.exp (-(π * n * (K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n) / 6))
        ≤ 4 * n ^ 2 * n ^ (-(p + 3)) := by gcongr
      _ = 4 * n⁻¹ * n ^ (-p) := hprod_le
      _ ≤ (1 / 2 : ℝ) * n ^ (-p) := by
          have h4n : 4 * n⁻¹ ≤ 1 / 2 := by
            rw [← div_eq_mul_inv, div_le_iff₀ hn0]
            linarith
          exact mul_le_mul_of_nonneg_right h4n (Real.rpow_nonneg hn0.le _)
  have hsqrt2 : Real.sqrt 2 < 149 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hdiff_pos : 0 < (3 / 2 - Real.sqrt 2) * (xiStar / 2) :=
    mul_pos (by linarith) (half_pos xiStar_pos)
  have hev_delta := htend_delta.eventually (gt_mem_nhds (by
    have := xiStar_pos; positivity : (0 : ℝ) < min ((xiStar / 2) / 100) ((3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4)))
  have hev_nd := htend_n_delta.eventually_ge_atTop (48 * xiStar)
  have hev_Cx := htend_Cx.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < (3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hev_delta.and (hev_nd.and (hev_Cx.and (htend_t1.and htend_t2))))
  let c₀ : ℝ := max (max 40 (n₀ + 1)) (max (N₁ + 1) (Real.exp 1 + 1))
  refine ⟨K_p, 1, c₀, hK_pos, one_pos, (le_max_left _ _).trans (le_max_left _ _), fun {c} hc => ?_⟩
  dsimp only
  have hc40 : 40 ≤ c := ((le_max_left _ _).trans (le_max_left _ _)).trans hc
  have hcn0 : n₀ + 1 ≤ c := ((le_max_right _ _).trans (le_max_left _ _)).trans hc
  have hcN1 : N₁ ≤ c - 1 := by
    have : N₁ + 1 ≤ c := ((le_max_left _ _).trans (le_max_right _ _)).trans hc
    linarith
  have hce : Real.exp 1 ≤ c - 1 := by
    have : Real.exp 1 + 1 ≤ c := ((le_max_right _ _).trans (le_max_right _ _)).trans hc
    linarith
  let n : ℝ := c - 1
  let a : ℝ := n / 12
  let δ : ℝ := K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have ha_ge : (13 / 4 : ℝ) ≤ a := by dsimp [a, n]; linarith
  have ha2 : 2 < a := by linarith
  have hlog_ge1 : 1 ≤ Real.log n := by
    have := Real.log_le_log (Real.exp_pos 1) hce; rwa [Real.log_exp] at this
  have hδ_pos : 0 < δ := by dsimp [δ]; positivity
  have hγ_pos : 0 < spinGamma a := spinGamma_pos ha2
  have hγ_lt1 : spinGamma a < 1 := spinGamma_lt_one ha2
  let bStar : ℝ := spinBStar a
  have hbStar_ge : xiStar / 2 ≤ bStar := by
    have hγ_half : 1 / 2 ≤ spinGamma a := by
      unfold spinGamma
      have : (1 / 4 : ℝ) ≤ 1 - 2 / a := by
        have : 2 / a ≤ 2 / (13 / 4 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha_ge
        linarith
      calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by norm_num
        _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt this
    dsimp [bStar]; unfold spinBStar; nlinarith [xiStar_pos]
  have hbStar_le : bStar ≤ xiStar := by dsimp [bStar]; unfold spinBStar; nlinarith [xiStar_pos]
  obtain ⟨hδ_min, hnd_ge, hCx_sm, ht1_le, ht2_le⟩ := hN₁ n hcN1
  have hδ_lt_b : δ < bStar / 100 := lt_of_lt_of_le (lt_of_lt_of_le hδ_min (min_le_left _ _)) (by linarith)
  have hδ_gap : δ < (3 / 2 - Real.sqrt 2) * (xiStar / 2) / 4 :=
    lt_of_lt_of_le hδ_min (min_le_right _ _)
  have hxi_sub_b : xiStar - bStar ≤ 24 * xiStar / n := by
    have h1γ : 1 - spinGamma a ≤ 2 / a := by
      have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
      have hpos : 0 < 1 + spinGamma a := by linarith
      calc 1 - spinGamma a = (2 / a) / (1 + spinGamma a) := by
            rw [← hdiff, show 1 - spinGamma a ^ 2 = (1 - spinGamma a) * (1 + spinGamma a) by ring,
              mul_div_cancel_right₀ _ hpos.ne']
        _ ≤ (2 / a) / 1 := div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
        _ = 2 / a := div_one _
    have h2a : 2 / a = 24 / n := by dsimp [a]; ring
    calc xiStar - bStar = xiStar * (1 - spinGamma a) := by dsimp [bStar]; unfold spinBStar; ring
      _ ≤ xiStar * (2 / a) := mul_le_mul_of_nonneg_left h1γ xiStar_pos.le
      _ = 24 * xiStar / n := by rw [h2a]; ring
  have hxi_delta : xiStar - δ ≤ bStar - δ / 2 := by
    have : 24 * xiStar / n ≤ δ / 2 := by rw [div_le_iff₀ hn_pos]; linarith
    linarith
  intro x₁ hx₁0 hx₁_ub Φ hΦ hM2
  let E : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧
    (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ (q.1 + q.2) / 2 < xiStar - δ}
  have hE_meas : MeasurableSet E :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isOpen_lt (((continuous_fst.pow 2).add (continuous_snd.pow 2)).div_const 2)
          continuous_const).measurableSet.inter
        (isOpen_lt ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet))
  have hE_pos : E ⊆ {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2} := fun _ hp => ⟨hp.1, hp.2.1⟩
  have hG_int_full : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc (by linarith) hΦ
  have hG_int_E : IntegrableOn (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) E :=
    hG_int_full.integrableOn
  rw [one_mul, ← ENNReal.ofReal_le_ofReal_iff (Real.rpow_nonneg hn_pos.le _),
    ofReal_integral_eq_lintegral_ofReal hG_int_E (Eventually.of_forall fun q =>
      mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _))]
  obtain ⟨_, _, _, _, hDelta_int, hDelta_L1⟩ := (spinS22 hc40).1 hΦ
  have hDelta_le4 : ∫ q : ℝ × ℝ, |spinDeltaA a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤ 4 := by
    have hlam_inv : (spinLambda a)⁻¹ ≤ 1 := by unfold spinLambda; rw [inv_inv]; exact hγ_lt1.le
    have hlam_inv_nn : 0 ≤ (spinLambda a)⁻¹ := by unfold spinLambda; rw [inv_inv]; exact hγ_pos.le
    have hsq : (1 + (spinLambda a)⁻¹) ^ 2 ≤ 4 := by nlinarith
    rw [hM2, mul_one] at hDelta_L1
    exact hDelta_L1.trans hsq
  obtain ⟨⟨hS_int, hS_le, hS_ae⟩, hfold_b, _⟩ := hS22b_main.2 hcn0 hΦ hM2
  have htel := lintegral_spinG_quad_le_tsum ha2 hΦ hE_meas hE_pos
  let D : ℝ := 3 * bStar / 4
  let A_cls1 : Set (ℝ × ℝ) :=
    {y : ℝ × ℝ | 0 < y.1 ∧ 0 < y.2 ∧ (y.1 + y.2) / 2 ≤ bStar - δ / 4 ∧ |(y.1 - y.2) / 2| ≤ D}
  have hA1_meas : MeasurableSet A_cls1 :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      ((isOpen_lt continuous_const continuous_snd).measurableSet.inter
        ((isClosed_le ((continuous_fst.add continuous_snd).div_const 2) continuous_const).measurableSet.inter
          (isClosed_le (((continuous_fst.sub continuous_snd).div_const 2).abs)
            continuous_const).measurableSet))
  have hfold_exp : Real.exp (-κ * n * (δ / 4) ^ ((3 : ℝ) / 2)) ≤ n ^ (-(k + p + 4)) := by
    have hnd : n * δ ^ ((3 : ℝ) / 2) = K_p ^ ((3 : ℝ) / 2) * (Real.log n) ^ ((3 : ℝ) / 2) := by
      dsimp [δ]
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hK_pos.le (by positivity), ← Real.rpow_mul hn_pos.le]
      have h1 : (-(2 / 3 : ℝ)) * ((3 : ℝ) / 2) = -1 := by norm_num
      rw [h1, Real.rpow_neg_one]; field_simp [hn_pos.ne']
    have hlog_pow : Real.log n ≤ (Real.log n) ^ ((3 : ℝ) / 2) := by
      calc Real.log n = (Real.log n) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (Real.log n) ^ ((3 : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hlog_ge1 (by norm_num)
    have hnd_ge : K_p ^ ((3 : ℝ) / 2) * Real.log n ≤ n * δ ^ ((3 : ℝ) / 2) := by
      rw [hnd]; exact mul_le_mul_of_nonneg_left hlog_pow (by positivity)
    have hqtr : (δ / 4) ^ ((3 : ℝ) / 2) = (4 : ℝ) ^ (-(3 / 2 : ℝ)) * δ ^ ((3 : ℝ) / 2) := by
      rw [div_eq_mul_inv, Real.mul_rpow hδ_pos.le (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num), mul_comm]
    have hexp_le : -κ * n * (δ / 4) ^ ((3 : ℝ) / 2) ≤ -(k + p + 4) * Real.log n := by
      rw [hqtr]
      have hrew : -κ * n * ((4 : ℝ) ^ (-(3 / 2 : ℝ)) * δ ^ ((3 : ℝ) / 2)) =
          -(κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (n * δ ^ ((3 : ℝ) / 2))) := by ring
      rw [hrew]
      have : (k + p + 4) * Real.log n ≤ κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (n * δ ^ ((3 : ℝ) / 2)) := by
        calc (k + p + 4) * Real.log n
            ≤ (κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) * K_p ^ ((3 : ℝ) / 2)) * Real.log n :=
              mul_le_mul_of_nonneg_right hK_exp (by linarith)
          _ = κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (K_p ^ ((3 : ℝ) / 2) * Real.log n) := by ring
          _ ≤ κ * (4 : ℝ) ^ (-(3 / 2 : ℝ)) * (n * δ ^ ((3 : ℝ) / 2)) :=
              mul_le_mul_of_nonneg_left hnd_ge (by positivity)
      linarith
    calc Real.exp (-κ * n * (δ / 4) ^ ((3 : ℝ) / 2))
        ≤ Real.exp (-(k + p + 4) * Real.log n) := Real.exp_le_exp.mpr hexp_le
      _ = n ^ (-(k + p + 4)) := by rw [Real.rpow_def_of_pos hn_pos]; congr 1; ring
  have hA1_bound :
      ∫⁻ y in A_cls1, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
        ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) :=
    spinS4_2_1_A1_bound ha2 hn_pos hC0_nn hκ0 hδ_pos hbStar_ge hbStar_le rfl rfl
      hS_int hS_le hS_ae (fun ξ d h1 h2 h3 => by simpa [a, n, bStar, D] using hfold_b ξ d h1 h2 h3)
      hfold_exp
  have hDelta_en :
      ∫⁻ y : ℝ × ℝ, ENNReal.ofReal (|spinDeltaA a Φ y.1 y.2| * spinWc a y.1 * spinWc a y.2) ≤
        ENNReal.ofReal 4 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hDelta_int
      (Eventually.of_forall fun p => mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le p.1))
        (spinWc_nonneg ha2.le p.2))]
    exact ENNReal.ofReal_le_ofReal hDelta_le4
  have hterm_q : ∀ q : ℕ × ℕ,
      ∫⁻ p in E,
        ENNReal.ofReal (|spinDeltaA a Φ (spinLambda a ^ q.1 * p.1) (spinLambda a ^ q.2 * p.2)| *
          spinWc a p.1 * spinWc a p.2) ≤
      ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
        (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) +
         ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 6)))) :=
    spinS4_2_1_q_term ha2 hn_pos hδ_pos hx₁0 hx₁_ub hbStar_ge hxi_delta hCx_sm hδ_gap hΦ
      (by simpa [A_cls1, D, a] using hA1_bound) hDelta_en
  have hjac_le : (1 - spinGamma a)⁻¹ ≤ n := by
    have hdiff : 1 - spinGamma a ^ 2 = 2 / a := by rw [spinGamma_sq ha2.le]; ring
    have hpos : 0 < 1 - spinGamma a := sub_pos.mpr hγ_lt1
    have hle : (1 - spinGamma a)⁻¹ = a * (1 + spinGamma a) / 2 := by
      have ha_ne : a ≠ 0 := by linarith only [ha2]
      have hprod : (1 - spinGamma a) * (a * (1 + spinGamma a) / 2) = 1 := by
        calc (1 - spinGamma a) * (a * (1 + spinGamma a) / 2)
            = a * (1 - spinGamma a ^ 2) / 2 := by ring
          _ = a * (2 / a) / 2 := by rw [hdiff]
          _ = 1 := by field_simp [ha_ne]
      exact inv_eq_of_mul_eq_one_right hprod
    rw [hle]
    have hle_a : a * (1 + spinGamma a) / 2 ≤ a := by
      have h1g : 1 + spinGamma a ≤ 2 := by linarith only [hγ_lt1]
      have ha_nn : 0 ≤ a := by linarith only [ha2]
      linarith only [mul_le_mul_of_nonneg_left h1g ha_nn]
    have ha_le_n : a ≤ n := by dsimp [a]; linarith only [hn_pos]
    exact hle_a.trans ha_le_n
  have hjac_sq : (1 - spinGamma a)⁻¹ * (1 - spinGamma a)⁻¹ ≤ n ^ 2 := by
    have hnn : 0 ≤ (1 - spinGamma a)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hγ_lt1.le)
    simpa [sq] using mul_self_le_mul_self hnn hjac_le
  have htotal :
      ∫⁻ q in E, ENNReal.ofReal (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) ≤
        ENNReal.ofReal (n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4)) +
          4 * Real.exp (-(π * n * δ / 6)))) := by
    calc ∫⁻ q in E, ENNReal.ofReal (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
        ≤ ∑' q : ℕ × ℕ,
            ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2) *
              (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) +
               ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 6)))) :=
          htel.trans (tsum_le_tsum hterm_q)
      _ = (∑' q : ℕ × ℕ, ENNReal.ofReal (spinGamma a ^ q.1 * spinGamma a ^ q.2)) *
            (ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) +
             ENNReal.ofReal (4 * Real.exp (-(π * n * δ / 6)))) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal ((1 - spinGamma a)⁻¹ * (1 - spinGamma a)⁻¹) *
            ENNReal.ofReal (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4)) +
              4 * Real.exp (-(π * n * δ / 6))) := by
          rw [tsum_gamma_pair_s4 hγ_pos.le hγ_lt1, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      _ = ENNReal.ofReal (((1 - spinGamma a)⁻¹ * (1 - spinGamma a)⁻¹) *
            (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4)) + 4 * Real.exp (-(π * n * δ / 6)))) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal (n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4)) +
            4 * Real.exp (-(π * n * δ / 6)))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hjac_sq (add_nonneg (by positivity) (by positivity)))
  refine htotal.trans (ENNReal.ofReal_le_ofReal ?_)
  have hnk : n ^ 2 * n ^ k = n ^ (k + 2) := by
    rw [← Real.rpow_natCast n 2, ← Real.rpow_add hn_pos]; congr 1; ring
  have h1 : n ^ 2 * (C_cls1 * n ^ k * δ⁻¹ * n ^ (-(k + p + 4))) =
      C_cls1 * n ^ (k + 2) * δ⁻¹ * n ^ (-(k + p + 4)) := by rw [← hnk]; ring
  have h2 : n ^ 2 * (4 * Real.exp (-(π * n * δ / 6))) = 4 * n ^ 2 * Real.exp (-(π * n * δ / 6)) := by ring
  rw [mul_add, h1, h2]
  linarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_2_1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_2_1

end FormalResearch.ModularBootstrap.Spin

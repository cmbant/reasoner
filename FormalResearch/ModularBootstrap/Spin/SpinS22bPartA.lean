module

public import FormalResearch.ModularBootstrap.Spin.SpinS22Outward
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit

/-!
# Lemma S2.2′ (`spinnotes:S22b`), Part (a): weighted slit integral bound

Proves Part (a) of **Lemma S2.2′** (`spinning_foundations.tex`, lines 250–272):
for all `c ≥ 40` (`n = c - 1`, `a = n / 12`, `b_* = γ_a ξ_*`, `D = 3 b_* / 4`) and
`Φ ∈ \overline{\mathcal A}_{\rm spin}` with `M_2[Φ] = 1`:

1. `spinWc_mul_ge_exp_slit`: on `|s| ≥ b_*`, `|d| ≤ D`,
   `spinSlitConst0 * (a * exp(12 a L(s))) ≤ w_c(s + d) * w_c(s - d)` with an explicit
   absolute constant `spinSlitConst0 > 0`.
2. `spinS22b_partA`: `IntegrableOn (spinSlitIntegral a Φ) (Icc (-D) D)`,
   `∫ d in Icc (-D) D, spinSlitIntegral a Φ d ≤ 2 * spinSlitConst0⁻¹`, and for a.e.
   `d ∈ Icc (-D) D` the slit integrand `s ↦ a e^{12 a L(s)} |Δ_a G(s + d, s - d)|` is
   integrable on `{s | b_* ≤ |s|}`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Spin

/-- Explicit absolute lower bound constant `c₀ = (1 - e^{-4π · 0.0075})⁴ > 0` for
`w_c(s + d) w_c(s - d) / (a e^{n L(s)})` on `|s| ≥ b_*`, `|d| ≤ 3 b_* / 4`. -/
noncomputable def spinSlitConst0 : ℝ :=
  (1 - Real.exp (-4 * π * 0.0075)) ^ 4

lemma spinSlitConst0_pos : 0 < spinSlitConst0 := by
  unfold spinSlitConst0
  have h1 : Real.exp (-4 * π * 0.0075) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  exact pow_pos (sub_pos.mpr h1) 4

private lemma spinGamma_ge_06 {a : ℝ} (ha : 39 / 12 ≤ a) : (0.6 : ℝ) ≤ spinGamma a := by
  unfold spinGamma
  have ha0 : 0 < a := by linarith
  have hdiv : 2 / a ≤ 2 / (39 / 12 : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by norm_num) ha
  have h1 : (0.6 : ℝ) ^ 2 ≤ 1 - 2 / a := by linarith
  calc (0.6 : ℝ) = Real.sqrt (0.6 ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    _ ≤ Real.sqrt (1 - 2 / a) := Real.sqrt_le_sqrt h1

private lemma spinBStar_ge_003 {a : ℝ} (ha : 39 / 12 ≤ a) : (0.03 : ℝ) ≤ spinBStar a := by
  unfold spinBStar
  have h1 := spinGamma_ge_06 ha
  have h2 := xiStar_gt_005
  nlinarith

private lemma spinCalFc_ge_of_ge {a x r : ℝ} (ha : 2 < a) (hr : 0 < r) (hxr : r ≤ x) :
    (1 - Real.exp (-4 * π * r)) ^ 2 ≤ spinCalFc a x := by
  have ha0 : 0 < a := by linarith
  have hγ_pos : 0 < spinGamma a := by
    unfold spinGamma
    exact Real.sqrt_pos.mpr (by linarith [(div_lt_one ha0).mpr ha])
  have hγ_lt1 : spinGamma a < 1 := by
    unfold spinGamma
    calc Real.sqrt (1 - 2 / a) < Real.sqrt 1 :=
          Real.sqrt_lt_sqrt (by linarith [(div_lt_one ha0).mpr ha]) (by linarith [div_pos two_pos ha0])
      _ = 1 := Real.sqrt_one
  have hγ_sq : spinGamma a ^ 2 = 1 - 2 / a := by
    unfold spinGamma
    exact Real.sq_sqrt (by linarith [(div_lt_one ha0).mpr ha])
  have h1m : a * (1 - spinGamma a) ≥ 1 := by
    have hprod : (1 - spinGamma a) * (1 + spinGamma a) = 2 / a := by linarith [hγ_sq]
    have hsum_pos : 0 < 1 + spinGamma a := by linarith
    have h1 : a * (1 - spinGamma a) = 2 / (1 + spinGamma a) := by
      have h2 : a * (1 - spinGamma a) * (1 + spinGamma a) = 2 := by
        rw [mul_assoc, hprod]; field_simp [ha0.ne']
      exact eq_div_of_mul_eq hsum_pos.ne' h2
    rw [h1, ge_iff_le, one_le_div hsum_pos]
    linarith
  have h1p : a * (1 + spinGamma a) ≥ 1 := by nlinarith
  have hexp_m : Real.exp (-π * (12 * a) * (1 - spinGamma a) * x / 3) ≤ Real.exp (-4 * π * r) := by
    refine Real.exp_le_exp.mpr ?_
    have hEq : -π * (12 * a) * (1 - spinGamma a) * x / 3 =
        -(4 * π * (a * (1 - spinGamma a)) * x) := by ring
    rw [hEq]
    have hmul : 4 * π * r ≤ 4 * π * (a * (1 - spinGamma a)) * x := by
      have : 1 * r ≤ (a * (1 - spinGamma a)) * x :=
        mul_le_mul h1m hxr hr.le (by linarith)
      nlinarith [Real.pi_pos]
    linarith
  have hexp_p : Real.exp (-π * (12 * a) * (1 + spinGamma a) * x / 3) ≤ Real.exp (-4 * π * r) := by
    refine Real.exp_le_exp.mpr ?_
    have hEq : -π * (12 * a) * (1 + spinGamma a) * x / 3 =
        -(4 * π * (a * (1 + spinGamma a)) * x) := by ring
    rw [hEq]
    have hmul : 4 * π * r ≤ 4 * π * (a * (1 + spinGamma a)) * x := by
      have : 1 * r ≤ (a * (1 + spinGamma a)) * x :=
        mul_le_mul h1p hxr hr.le (by linarith)
      nlinarith [Real.pi_pos]
    linarith
  have hnn : 0 ≤ 1 - Real.exp (-4 * π * r) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos]))
  unfold spinCalFc
  rw [sq]
  exact mul_le_mul (by linarith) (by linarith) hnn (by linarith)

/-- Pointwise lower bound on the slits (`spinning_foundations.tex`, proof of Lemma S2.2′(a)):
for `a ≥ 39 / 12`, `|s| ≥ b_*`, `|d| ≤ 3 b_* / 4`,
`spinSlitConst0 * (a * exp(12 a L(s))) ≤ w_c(s + d) * w_c(s - d)`. -/
theorem spinWc_mul_ge_exp_slit {a s d : ℝ} (ha : 39 / 12 ≤ a)
    (hs : spinBStar a ≤ |s|) (hd : |d| ≤ 3 * spinBStar a / 4) :
    spinSlitConst0 * (a * Real.exp (12 * a * spinL s)) ≤ spinWc a (s + d) * spinWc a (s - d) := by
  have ha2 : 2 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hb : (0.03 : ℝ) ≤ spinBStar a := spinBStar_ge_003 ha
  have hsd1 : (0.0075 : ℝ) ≤ |s + d| := by
    have h1 : |s| - |d| ≤ |s + d| := by
      have := abs_sub_abs_le_abs_sub s (-d)
      simpa [sub_neg_eq_add, abs_neg] using this
    linarith
  have hsd2 : (0.0075 : ℝ) ≤ |s - d| := by
    have h1 : |s| - |d| ≤ |s - d| := abs_sub_abs_le_abs_sub s d
    linarith
  have hsum_abs : |s + d| + |s - d| = 2 * |s| := by
    have hd_le_s : |d| ≤ |s| := by linarith
    rcases le_total 0 s with hs0 | hs0
    · rw [abs_of_nonneg hs0] at hd_le_s ⊢
      have h1 : 0 ≤ s + d := by linarith [(abs_le.mp hd_le_s).1]
      have h2 : 0 ≤ s - d := by linarith [(abs_le.mp hd_le_s).2]
      rw [abs_of_nonneg h1, abs_of_nonneg h2]; ring
    · rw [abs_of_nonpos hs0] at hd_le_s ⊢
      have h1 : s + d ≤ 0 := by linarith [(abs_le.mp hd_le_s).2]
      have h2 : s - d ≤ 0 := by linarith [(abs_le.mp hd_le_s).1]
      rw [abs_of_nonpos h1, abs_of_nonpos h2]; ring
  rw [spinWc_factorization ha2.le (s + d), spinWc_factorization ha2.le (s - d)]
  have hF1 := spinCalFc_ge_of_ge ha2 (by norm_num : (0 : ℝ) < 0.0075) hsd1
  have hF2 := spinCalFc_ge_of_ge ha2 (by norm_num : (0 : ℝ) < 0.0075) hsd2
  have hnn : 0 ≤ (1 - Real.exp (-4 * π * 0.0075)) ^ 2 := sq_nonneg _
  have hFprod : spinSlitConst0 ≤ spinCalFc a |s + d| * spinCalFc a |s - d| := by
    unfold spinSlitConst0
    rw [show (1 - Real.exp (-4 * π * 0.0075)) ^ 4 =
        (1 - Real.exp (-4 * π * 0.0075)) ^ 2 * (1 - Real.exp (-4 * π * 0.0075)) ^ 2 by ring]
    exact mul_le_mul hF1 hF2 hnn (hnn.trans hF1)
  have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha0.le
  have hexp : Real.exp (4 * π * a * |s + d|) * Real.exp (4 * π * a * |s - d|) =
      Real.exp (12 * a * spinL s) := by
    rw [← Real.exp_add]
    congr 1
    unfold spinL
    calc 4 * π * a * |s + d| + 4 * π * a * |s - d|
        = 4 * π * a * (|s + d| + |s - d|) := by ring
      _ = 4 * π * a * (2 * |s|) := by rw [hsum_abs]
      _ = 12 * a * (2 * π * |s| / 3) := by ring
  calc spinSlitConst0 * (a * Real.exp (12 * a * spinL s))
      ≤ (spinCalFc a |s + d| * spinCalFc a |s - d|) * (a * Real.exp (12 * a * spinL s)) :=
        mul_le_mul_of_nonneg_right hFprod (by positivity)
    _ = (spinCalFc a |s + d| * spinCalFc a |s - d|) *
          ((Real.sqrt a * Real.sqrt a) * (Real.exp (4 * π * a * |s + d|) * Real.exp (4 * π * a * |s - d|))) := by
        rw [hsq, hexp]
    _ = (Real.sqrt a * Real.exp (4 * π * a * |s + d|) * spinCalFc a |s + d|) *
          (Real.sqrt a * Real.exp (4 * π * a * |s - d|) * spinCalFc a |s - d|) := by ring

/-! ### Linear change of variables `(s, d) ↦ (s + d, s - d)` -/

private noncomputable def sdToUV : ℝ × ℝ ≃ᵐ ℝ × ℝ where
  toFun p := (p.1 + p.2, p.1 - p.2)
  invFun q := ((q.1 + q.2) / 2, (q.1 - q.2) / 2)
  left_inv p := by ext <;> dsimp <;> ring
  right_inv q := by ext <;> dsimp <;> ring
  measurable_toFun := (measurable_fst.add measurable_snd).prodMk (measurable_fst.sub measurable_snd)
  measurable_invFun :=
    ((measurable_fst.add measurable_snd).div_const 2).prodMk
      ((measurable_fst.sub measurable_snd).div_const 2)

private lemma map_volume_shear_fst :
    Measure.map (fun p : ℝ × ℝ => (p.1 + p.2, p.2)) (volume : Measure (ℝ × ℝ)) = volume := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.volume_eq_prod, Measure.prod_apply_symm (measurableSet_preimage (by fun_prop) hs),
    Measure.prod_apply_symm hs]
  refine lintegral_congr fun y => ?_
  have hpre : (fun x : ℝ => (x, y)) ⁻¹' ((fun p : ℝ × ℝ => (p.1 + p.2, p.2)) ⁻¹' s) =
      (fun x : ℝ => x + y) ⁻¹' ((fun x : ℝ => (x, y)) ⁻¹' s) := rfl
  rw [hpre]
  have hmeas : MeasurableSet ((fun x : ℝ => (x, y)) ⁻¹' s) :=
    hs.preimage (measurable_id.prodMk measurable_const)
  rw [← Measure.map_apply (measurable_add_const y) hmeas, map_add_right_eq_self]

private lemma map_volume_shear_snd :
    Measure.map (fun p : ℝ × ℝ => (p.1, p.2 + p.1)) (volume : Measure (ℝ × ℝ)) = volume := by
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.volume_eq_prod, Measure.prod_apply (measurableSet_preimage (by fun_prop) hs),
    Measure.prod_apply hs]
  refine lintegral_congr fun x => ?_
  have hpre : Prod.mk x ⁻¹' ((fun p : ℝ × ℝ => (p.1, p.2 + p.1)) ⁻¹' s) =
      (fun y : ℝ => y + x) ⁻¹' (Prod.mk x ⁻¹' s) := rfl
  rw [hpre]
  have hmeas : MeasurableSet (Prod.mk x ⁻¹' s) := hs.preimage (measurable_const.prodMk measurable_id)
  rw [← Measure.map_apply (measurable_add_const x) hmeas, map_add_right_eq_self]

private lemma map_volume_sdToUV :
    Measure.map sdToUV (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure (ℝ × ℝ)) := by
  let f1 : ℝ × ℝ → ℝ × ℝ := fun p => (p.1 + p.2, p.2)
  let f2 : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, (-2 : ℝ) * p.2)
  let f3 : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, p.2 + p.1)
  have hcomp : (sdToUV : ℝ × ℝ → ℝ × ℝ) = f3 ∘ f2 ∘ f1 := by
    ext p
    · simp [sdToUV, f1, f2, f3]
    · simp [sdToUV, f1, f2, f3]; ring
  have hm1 : Measurable f1 := (measurable_fst.add measurable_snd).prodMk measurable_snd
  have hm2 : Measurable f2 := measurable_fst.prodMk (measurable_const.mul measurable_snd)
  have hm3 : Measurable f3 := measurable_fst.prodMk (measurable_snd.add measurable_fst)
  have hmap2 : Measure.map f2 (volume : Measure (ℝ × ℝ)) =
      ENNReal.ofReal (1 / 2 : ℝ) • (volume : Measure (ℝ × ℝ)) := by
    have hf2 : f2 = Prod.map id ((-2 : ℝ) * ·) := rfl
    rw [hf2, Measure.volume_eq_prod,
      ← Measure.map_prod_map _ _ measurable_id (measurable_const_mul (-2)),
      Measure.map_id, Real.map_volume_mul_left (by norm_num : (-2 : ℝ) ≠ 0),
      Measure.prod_smul_right]
    congr 2; norm_num
  rw [hcomp, ← Measure.map_map hm3 (hm2.comp hm1), ← Measure.map_map hm2 hm1,
    map_volume_shear_fst, hmap2, Measure.map_smul, map_volume_shear_snd]
  exact hm3.aemeasurable

/-- **Lemma S2.2′(a)** (`spinning_foundations.tex`, lines 260, 268–271):
for `c ≥ 40` (`a = (c - 1) / 12`, `D = 3 b_* / 4`) and `Φ ∈ \overline{\mathcal A}_{\rm spin}`
with `M_2[Φ] = 1`:
1. `spinSlitIntegral a Φ` is integrable on `Icc (-D) D`;
2. `∫ d in Icc (-D) D, spinSlitIntegral a Φ d ≤ 2 * spinSlitConst0⁻¹`;
3. for Lebesgue-a.e. `d ∈ Icc (-D) D`, the slit integrand
   `s ↦ a e^{12 a L(s)} |Δ_a G(s + d, s - d)|` is integrable on `{s | b_* ≤ |s|}`. -/
theorem spinS22b_partA {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) (hM2 : spinM2 ((c - 1) / 12) Φ = 1) :
    let a := (c - 1) / 12
    let D := 3 * spinBStar a / 4
    IntegrableOn (spinSlitIntegral a Φ) (Icc (-D) D) ∧
      (∫ d in Icc (-D) D, spinSlitIntegral a Φ d) ≤ 2 * spinSlitConst0⁻¹ ∧
      (∀ᵐ d ∂(volume.restrict (Icc (-D) D)),
        IntegrableOn (fun s : ℝ =>
          a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|)
          {s : ℝ | spinBStar a ≤ |s|}) := by
  intro a D
  have ha : 39 / 12 ≤ a := by dsimp [a]; linarith
  have ha2 : 2 < a := by linarith
  obtain ⟨hΔ_int, hΔ_le⟩ := integrable_and_integral_spinDeltaA_wc ha2 hΦ
  -- Pull back `|Δ_a G| w_c ⊗ w_c` along `sdToUV(s, d) = (s + d, s - d)`
  have hΔ_map : Integrable (fun q : ℝ × ℝ =>
      |spinDeltaA a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
      (Measure.map sdToUV volume) := by
    rw [map_volume_sdToUV]
    exact hΔ_int.smul_measure ENNReal.ofReal_ne_top
  have hpull_int : Integrable (fun p : ℝ × ℝ =>
      |spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2))
      volume :=
    (MeasurePreserving.integrable_comp_emb ⟨sdToUV.measurable, rfl⟩
      sdToUV.measurableEmbedding).mpr hΔ_map
  have hpull_eq : ∫ p : ℝ × ℝ,
      |spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2) =
      (1 / 2 : ℝ) * ∫ q : ℝ × ℝ, |spinDeltaA a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by
    have h := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) sdToUV
      (fun q : ℝ × ℝ => |spinDeltaA a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2)
    rw [map_volume_sdToUV, integral_smul_measure, ENNReal.toReal_ofReal (by norm_num),
      smul_eq_mul] at h
    exact h.symm
  have hΔ_le4 : ∫ q : ℝ × ℝ, |spinDeltaA a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤ 4 := by
    have hγ_pos : 0 < spinGamma a := by
      unfold spinGamma; exact Real.sqrt_pos.mpr (by linarith [(div_lt_one (by linarith : 0 < a)).mpr ha2])
    have hγ_le1 : spinGamma a ≤ 1 := by
      unfold spinGamma
      calc Real.sqrt (1 - 2 / a) ≤ Real.sqrt 1 :=
            Real.sqrt_le_sqrt (by linarith [div_pos two_pos (by linarith : 0 < a)])
        _ = 1 := Real.sqrt_one
    have hlam_inv : (spinLambda a)⁻¹ ≤ 1 := by
      unfold spinLambda; rw [inv_inv]; exact hγ_le1
    have hlam_inv_nn : 0 ≤ (spinLambda a)⁻¹ := by
      unfold spinLambda; rw [inv_inv]; exact hγ_pos.le
    have hsq : (1 + (spinLambda a)⁻¹) ^ 2 ≤ 4 := by nlinarith
    rw [hM2, mul_one] at hΔ_le
    exact hΔ_le.trans hsq
  -- Dominate the slit-box integrand `F(s, d)` on `S × Icc (-D) D`
  let S : Set ℝ := {s : ℝ | spinBStar a ≤ |s|}
  have hS_meas : MeasurableSet S := isClosed_le continuous_const continuous_abs |>.measurableSet
  have hD_meas : MeasurableSet (Icc (-D) D) := measurableSet_Icc
  let F : ℝ × ℝ → ℝ := fun p =>
    a * Real.exp (12 * a * spinL p.1) * |spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)|
  have hF_cont : Continuous F := by
    have hG_cont : ∀ c₁ c₂ : ℝ, Continuous (fun p : ℝ × ℝ =>
        spinG a Φ (c₁ * (p.1 + p.2)) (c₂ * (p.1 - p.2))) := by
      intro c₁ c₂; unfold spinG
      exact hΦ.cont.comp ((continuous_const.mul (continuous_const.mul (continuous_fst.add continuous_snd))).prodMk
        (continuous_const.mul (continuous_const.mul (continuous_fst.sub continuous_snd))))
    have hDa_cont : Continuous (fun p : ℝ × ℝ => spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)) := by
      have heq : (fun p : ℝ × ℝ => spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)) =
          fun p =>
            spinG a Φ (spinLambda a * (p.1 + p.2)) (spinLambda a * (p.1 - p.2)) -
            spinG a Φ ((spinGamma a * spinLambda a) * (p.1 + p.2)) (spinLambda a * (p.1 - p.2)) -
            spinG a Φ (spinLambda a * (p.1 + p.2)) ((spinGamma a * spinLambda a) * (p.1 - p.2)) +
            spinG a Φ ((spinGamma a * spinLambda a) * (p.1 + p.2))
              ((spinGamma a * spinLambda a) * (p.1 - p.2)) := by
        ext p; unfold spinDeltaA spinDa; rw [mul_assoc, mul_assoc]
      rw [heq]
      exact (((hG_cont _ _).sub (hG_cont _ _)).sub (hG_cont _ _)).add (hG_cont _ _)
    have hL_cont : Continuous spinL := by unfold spinL; fun_prop
    exact (continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul (hL_cont.comp continuous_fst)))).mul hDa_cont.abs
  have hF_dom : IntegrableOn F (S ×ˢ Icc (-D) D) volume := by
    have hdom_int : IntegrableOn (fun p : ℝ × ℝ =>
        spinSlitConst0⁻¹ * (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| *
          spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2))) (S ×ˢ Icc (-D) D) volume :=
      (hpull_int.const_mul spinSlitConst0⁻¹).integrableOn
    refine hdom_int.mono' hF_cont.aestronglyMeasurable ?_
    rw [ae_restrict_iff' (hS_meas.prod hD_meas)]
    refine Eventually.of_forall fun p hp => ?_
    have hF_nn : 0 ≤ F p := by dsimp [F]; positivity
    rw [Real.norm_of_nonneg hF_nn]
    have hwc := spinWc_mul_ge_exp_slit ha hp.1 (abs_le.mpr hp.2)
    have hmul := mul_le_mul_of_nonneg_right hwc (abs_nonneg (spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)))
    have hc0 := spinSlitConst0_pos
    have hle : spinSlitConst0 * F p ≤
        |spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2) := by
      dsimp [F]; linarith
    calc F p = spinSlitConst0⁻¹ * (spinSlitConst0 * F p) := by field_simp [hc0.ne']
      _ ≤ spinSlitConst0⁻¹ * (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| *
            spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hc0.le)
  -- Convert `IntegrableOn F (S ×ˢ Icc (-D) D)` to `Integrable F ((volume.restrict S).prod (volume.restrict (Icc (-D) D)))`
  have hprod_meas : (volume.restrict S).prod (volume.restrict (Icc (-D) D)) =
      (volume : Measure (ℝ × ℝ)).restrict (S ×ˢ Icc (-D) D) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hF_prod : Integrable F ((volume.restrict S).prod (volume.restrict (Icc (-D) D))) := by
    rwa [hprod_meas]
  have hF_swap : Integrable (fun p : ℝ × ℝ => F (p.2, p.1))
      ((volume.restrict (Icc (-D) D)).prod (volume.restrict S)) :=
    hF_prod.swap
  have hS_int : IntegrableOn (spinSlitIntegral a Φ) (Icc (-D) D) := by
    have h := hF_swap.integral_prod_left
    exact h
  have hS_ae : ∀ᵐ d ∂(volume.restrict (Icc (-D) D)),
      IntegrableOn (fun s : ℝ =>
        a * Real.exp (12 * a * spinL s) * |spinDeltaA a Φ (s + d) (s - d)|) S :=
    hF_swap.prod_right_ae
  refine ⟨hS_int, ?_, hS_ae⟩
  have hfub : ∫ d in Icc (-D) D, spinSlitIntegral a Φ d =
      ∫ p in S ×ˢ Icc (-D) D, F p := by
    rw [← hprod_meas]
    exact (integral_prod_symm F hF_prod).symm
  rw [hfub]
  have hdom_all : Integrable (fun p : ℝ × ℝ =>
      spinSlitConst0⁻¹ * (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| *
        spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2))) volume :=
    hpull_int.const_mul spinSlitConst0⁻¹
  have hle_set : ∫ p in S ×ˢ Icc (-D) D, F p ≤
      ∫ p in S ×ˢ Icc (-D) D, spinSlitConst0⁻¹ *
        (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) := by
    refine setIntegral_mono_on hF_dom hdom_all.integrableOn (hS_meas.prod hD_meas) fun p hp => ?_
    have hwc := spinWc_mul_ge_exp_slit ha hp.1 (abs_le.mpr hp.2)
    have hmul := mul_le_mul_of_nonneg_right hwc (abs_nonneg (spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)))
    have hc0 := spinSlitConst0_pos
    have hle : spinSlitConst0 * F p ≤
        |spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2) := by
      dsimp [F]; linarith
    calc F p = spinSlitConst0⁻¹ * (spinSlitConst0 * F p) := by field_simp [hc0.ne']
      _ ≤ spinSlitConst0⁻¹ * (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| *
            spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) :=
          mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hc0.le)
  have hle_univ : ∫ p in S ×ˢ Icc (-D) D, spinSlitConst0⁻¹ *
        (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) ≤
      ∫ p : ℝ × ℝ, spinSlitConst0⁻¹ *
        (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) :=
    setIntegral_le_integral hdom_all (Eventually.of_forall fun p =>
      mul_nonneg (inv_nonneg.mpr spinSlitConst0_pos.le)
        (mul_nonneg (mul_nonneg (abs_nonneg _) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)))
  calc ∫ p in S ×ˢ Icc (-D) D, F p
      ≤ ∫ p : ℝ × ℝ, spinSlitConst0⁻¹ *
          (|spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2)) :=
        hle_set.trans hle_univ
    _ = spinSlitConst0⁻¹ * ∫ p : ℝ × ℝ,
          |spinDeltaA a Φ (p.1 + p.2) (p.1 - p.2)| * spinWc a (p.1 + p.2) * spinWc a (p.1 - p.2) :=
        integral_const_mul _ _
    _ = spinSlitConst0⁻¹ * ((1 / 2 : ℝ) * ∫ q : ℝ × ℝ,
          |spinDeltaA a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by rw [hpull_eq]
    _ ≤ spinSlitConst0⁻¹ * ((1 / 2 : ℝ) * 4) := by
        gcongr
        exact inv_nonneg.mpr spinSlitConst0_pos.le
    _ = 2 * spinSlitConst0⁻¹ := by ring

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinWc_mul_ge_exp_slit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinWc_mul_ge_exp_slit

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS22b_partA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS22b_partA

end FormalResearch.ModularBootstrap.Spin

module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_4
public import FormalResearch.ModularBootstrap.Spin.SpinS4_3_3

/-!
# Section 3.4 of `spinning_s4.tex` (`s4:3.4`): local scalar vanishing implies global scalar vanishing

This module proves `SpinS4_3_4` (`spinning_s4.tex`, Theorem 3.4):
if the gap radius satisfies `|x₁ - ξ_*| ≤ C_x n^{-2/3}` under `SpinSlackHyp`, and the rescaled
calibrated profile `spinFProfile` converges to `0` in `L¹([-R, R])` for every fixed `R > 0`,
then the global calibrated `L¹` norm `spinCalNorm` converges to `0`.
-/

@[expose] public section

namespace FormalResearch.ModularBootstrap.Spin

open Filter MeasureTheory Set
open scoped Topology

private lemma spinGcal_re_even {a : ℝ} (ha : 0 ≤ a) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass a Φ) (b : ℝ) :
    (spinGcal a Φ (-b : ℂ)).re = (spinGcal a Φ (b : ℂ)).re := by
  have hcast : (-b : ℂ) = ((-b : ℝ) : ℂ) := by push_cast; rfl
  rw [hcast, spinGcal_re_ofReal ha hΦ (-b), spinGcal_re_ofReal ha hΦ b]
  congr 1
  let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.neg ℝ
  have hmp : Measure.map e (volume : Measure ℝ) = volume := by
    change Measure.map (-·) (volume : Measure ℝ) = volume
    exact Measure.map_neg_eq_self volume
  have heq := integral_map_equiv (μ := (volume : Measure ℝ)) e
    (fun d => spinHbCalReal (-b) d * spinG a Φ (-b + d) (-b - d))
  rw [hmp] at heq
  rw [heq]
  refine integral_congr_ae (Eventually.of_forall fun d => ?_)
  change spinHbCalReal (-b) (-d) * spinG a Φ (-b + -d) (-b - -d) = spinHbCalReal b d * spinG a Φ (b + d) (b - d)
  rw [spinHbCalReal_neg]
  have h1 : -b + -d = -(b + d) := by ring
  have h2 : -b - -d = -(b - d) := by ring
  rw [h1, h2, spinG_d4_neg_left hΦ, spinG_d4_neg_right hΦ]

private lemma spinRhoProjMeasure_toReal_s4_3_4
    {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {F : ℝ × ℝ → ℝ} (hF_meas : Measurable F) (hF_nn : ∀ q, 0 ≤ F q)
    (hF_bd : ∀ q : ℝ × ℝ, |F q| ≤ |spinG ((c - 1) / 12) Φ q.1 q.2|)
    (hF_nl : ∀ x y : ℝ, F (-x, y) = F (x, y))
    (hF_nr : ∀ x y : ℝ, F (x, -y) = F (x, y))
    {E : Set ℝ} (hE : MeasurableSet E) :
    let n := c - 1
    let a := n / 12
    Integrable (fun b : ℝ => a * Real.exp (n * spinL b) * spinCalProjFn F b) volume ∧
      (spinRhoProjMeasure c F E).toReal =
        ∫ b in abs ⁻¹' E, a * Real.exp (n * spinL b) * spinCalProjFn F b := by
  intro n a
  have ha0 : 0 ≤ a := by dsimp [a, n]; linarith
  obtain ⟨hH_int, -, -⟩ := spinCal_adjoint_identity hc hΦ hF_meas hF_bd hF_nl hF_nr
    measurable_const (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num : ∀ x : ℝ, |(1 : ℝ)| ≤ 1)
  have hH_prod : Integrable (fun p : ℝ × ℝ =>
      a * Real.exp (n * spinL p.1) * 1 *
        (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * F (p.1 + p.2, p.1 - p.2)))
      (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
  have hw_int : Integrable (fun b : ℝ =>
      a * Real.exp (n * spinL b) * spinCalProjFn F b) volume := by
    have hL := hH_prod.integral_prod_left
    refine hL.congr (Eventually.of_forall fun b => ?_)
    dsimp only [spinCalProjFn]
    have hre : (fun d => (spinHbCal (b : ℂ) d).re * F (b + d, b - d)) =
        (fun d => spinHbCalReal b d * F (b + d, b - d)) := by
      ext d; rw [spinHbCal_ofReal, Complex.ofReal_re]
    rw [hre, ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun d => ?_)
    ring
  refine ⟨hw_int, ?_⟩
  have hFproj_nn : ∀ b : ℝ, 0 ≤ spinCalProjFn F b := fun b => by
    unfold spinCalProjFn
    refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
    rw [spinHbCal_ofReal, Complex.ofReal_re]
    exact mul_nonneg (spinHbCalReal_nonneg b d) (hF_nn _)
  have hw_nn : ∀ b : ℝ, 0 ≤ a * Real.exp (n * spinL b) * spinCalProjFn F b := fun b =>
    mul_nonneg (mul_nonneg ha0 (Real.exp_pos _).le) (hFproj_nn b)
  unfold spinRhoProjMeasure
  rw [Measure.map_apply measurable_abs hE, withDensity_apply _ (measurable_abs hE)]
  have hmax : (fun b : ℝ => ENNReal.ofReal
      (((c - 1) / 12) * Real.exp ((c - 1) * spinL b) * max (spinCalProjFn F b) 0)) =
      fun b : ℝ => ENNReal.ofReal (a * Real.exp (n * spinL b) * spinCalProjFn F b) := by
    ext b; rw [max_eq_left (hFproj_nn b)]
  rw [hmax]
  have hlin := integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (abs ⁻¹' E))
    (Eventually.of_forall (fun b => hw_nn b))
    hw_int.integrableOn.aestronglyMeasurable
  exact hlin.symm

private lemma spinEtaProjMeasure_toReal_s4_3_4
    {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {F : ℝ × ℝ → ℝ} (hF_meas : Measurable F) (hF_nn : ∀ q, 0 ≤ F q)
    (hF_bd : ∀ q : ℝ × ℝ, |F q| ≤ |spinG ((c - 1) / 12) Φ q.1 q.2|)
    {E : Set ℝ} (hE : MeasurableSet E) :
    let a := (c - 1) / 12
    Integrable (fun p : ℝ × ℝ => F p * spinWc a p.1 * spinWc a p.2) volume ∧
      (spinEtaProjMeasure a F E).toReal =
        ∫ p in spinLongDist ⁻¹' E, F p * spinWc a p.1 * spinWc a p.2 := by
  intro a
  have ha0 : 0 < a := by dsimp [a]; linarith
  have ha2 : 2 ≤ a := by dsimp [a]; linarith
  have hG_int := integrable_spinG_wc ha0 hΦ
  have hWc_cont : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hw_int : Integrable (fun p : ℝ × ℝ => F p * spinWc a p.1 * spinWc a p.2) volume := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hF_meas.mul (hWc_cont.comp continuous_fst).measurable).mul
        (hWc_cont.comp continuous_snd).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hF_nn p),
        abs_of_nonneg (spinWc_nonneg ha2 p.1), abs_of_nonneg (spinWc_nonneg ha2 p.2)]
      have h1 : F p ≤ |spinG a Φ p.1 p.2| := (le_abs_self (F p)).trans (hF_bd p)
      have hw1 := spinWc_nonneg ha2 p.1
      have hw2 := spinWc_nonneg ha2 p.2
      gcongr
  refine ⟨hw_int, ?_⟩
  have hL_meas : Measurable spinLongDist :=
    measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
  unfold spinEtaProjMeasure
  rw [Measure.map_apply hL_meas hE, withDensity_apply _ (hL_meas hE)]
  have hw_nn : ∀ p : ℝ × ℝ, 0 ≤ F p * spinWc a p.1 * spinWc a p.2 := fun p =>
    mul_nonneg (mul_nonneg (hF_nn p) (spinWc_nonneg ha2 p.1)) (spinWc_nonneg ha2 p.2)
  have hmax : (fun p : ℝ × ℝ => ENNReal.ofReal (max (F p) 0 * spinWc a p.1 * spinWc a p.2)) =
      fun p : ℝ × ℝ => ENNReal.ofReal (F p * spinWc a p.1 * spinWc a p.2) := by
    ext p; rw [max_eq_left (hF_nn p)]
  rw [hmax]
  exact (integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict (spinLongDist ⁻¹' E))
    (Eventually.of_forall hw_nn) hw_int.integrableOn.aestronglyMeasurable).symm

private lemma spinGcal_re_sub_ae {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let n := c - 1
    let a := n / 12
    let Gplus := fun q : ℝ × ℝ => max (spinG a Φ q.1 q.2) 0
    let Gminus := fun q : ℝ × ℝ => max (-spinG a Φ q.1 q.2) 0
    ∀ᵐ b : ℝ ∂volume,
      (spinGcal a Φ (b : ℂ)).re = spinCalProjFn Gplus b - spinCalProjFn Gminus b := by
  intro n a Gplus Gminus
  have ha0 : 0 ≤ a := by dsimp [a, n]; linarith
  have ha_pos : 0 < a := by dsimp [a, n]; linarith
  have hG_meas : Measurable (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
    unfold spinG
    exact (hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable
  have hGp_meas : Measurable Gplus := hG_meas.max measurable_const
  have hGm_meas : Measurable Gminus := hG_meas.neg.max measurable_const
  have hGp_bd : ∀ q, |Gplus q| ≤ |spinG a Φ q.1 q.2| := fun q => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
  have hGm_bd : ∀ q, |Gminus q| ≤ |spinG a Φ q.1 q.2| := fun q => by
    rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (neg_le_abs _) (abs_nonneg _)
  have hGp_nl : ∀ x y, Gplus (-x, y) = Gplus (x, y) := fun x y => by
    dsimp [Gplus]; rw [spinG_d4_neg_left hΦ]
  have hGp_nr : ∀ x y, Gplus (x, -y) = Gplus (x, y) := fun x y => by
    dsimp [Gplus]; rw [spinG_d4_neg_right hΦ]
  have hGm_nl : ∀ x y, Gminus (-x, y) = Gminus (x, y) := fun x y => by
    dsimp [Gminus]; rw [spinG_d4_neg_left hΦ]
  have hGm_nr : ∀ x y, Gminus (x, -y) = Gminus (x, y) := fun x y => by
    dsimp [Gminus]; rw [spinG_d4_neg_right hΦ]
  obtain ⟨hHp, -, -⟩ := spinCal_adjoint_identity hc hΦ hGp_meas hGp_bd hGp_nl hGp_nr
    measurable_const (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num : ∀ x : ℝ, |(1 : ℝ)| ≤ 1)
  obtain ⟨hHm, -, -⟩ := spinCal_adjoint_identity hc hΦ hGm_meas hGm_bd hGm_nl hGm_nr
    measurable_const (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num : ∀ x : ℝ, |(1 : ℝ)| ≤ 1)
  have hHp_prod : Integrable (fun p : ℝ × ℝ =>
      a * Real.exp (n * spinL p.1) * 1 *
        (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * Gplus (p.1 + p.2, p.1 - p.2)))
      (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
  have hHm_prod : Integrable (fun p : ℝ × ℝ =>
      a * Real.exp (n * spinL p.1) * 1 *
        (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * Gminus (p.1 + p.2, p.1 - p.2)))
      (volume.prod volume) := by rwa [← Measure.volume_eq_prod]
  filter_upwards [hHp_prod.prod_right_ae, hHm_prod.prod_right_ae] with b hbp hbm
  have hC_pos : 0 < a * Real.exp (n * spinL b) * 1 * (4 * spinCalF xiStar ^ 2) :=
    mul_pos (mul_pos (mul_pos ha_pos (Real.exp_pos _)) one_pos)
      (mul_pos (by norm_num) (pow_pos (spinCalF_pos' xiStar_pos) 2))
  have hbp' : Integrable (fun d : ℝ => spinHbCalReal b d * Gplus (b + d, b - d)) volume := by
    have h := hbp.const_mul (a * Real.exp (n * spinL b) * 1 * (4 * spinCalF xiStar ^ 2))⁻¹
    refine h.congr (Eventually.of_forall fun d => ?_)
    have hCne := hC_pos.ne'
    have hFne := (spinCalF_pos' xiStar_pos).ne'
    dsimp only
    field_simp [hCne, hFne]
  have hbm' : Integrable (fun d : ℝ => spinHbCalReal b d * Gminus (b + d, b - d)) volume := by
    have h := hbm.const_mul (a * Real.exp (n * spinL b) * 1 * (4 * spinCalF xiStar ^ 2))⁻¹
    refine h.congr (Eventually.of_forall fun d => ?_)
    have hCne := hC_pos.ne'
    have hFne := (spinCalF_pos' xiStar_pos).ne'
    dsimp only
    field_simp [hCne, hFne]
  rw [spinGcal_re_ofReal ha0 hΦ b]
  have hsplit : (fun d : ℝ => spinHbCalReal b d * spinG a Φ (b + d) (b - d)) =
      fun d : ℝ =>
        spinHbCalReal b d * Gplus (b + d, b - d) -
          spinHbCalReal b d * Gminus (b + d, b - d) := by
    ext d
    have hg : spinG a Φ (b + d) (b - d) = Gplus (b + d, b - d) - Gminus (b + d, b - d) := by
      dsimp [Gplus, Gminus]; linarith [max_zero_sub_max_neg_zero_eq_self (spinG a Φ (b + d) (b - d))]
    rw [hg, mul_sub]
  rw [hsplit, integral_sub hbp' hbm', mul_sub]
  unfold spinCalProjFn
  have hre_p : (fun d : ℝ => (spinHbCal (b : ℂ) d).re * Gplus (b + d, b - d)) =
      fun d => spinHbCalReal b d * Gplus (b + d, b - d) := by
    ext d; rw [spinHbCal_ofReal, Complex.ofReal_re]
  have hre_m : (fun d : ℝ => (spinHbCal (b : ℂ) d).re * Gminus (b + d, b - d)) =
      fun d => spinHbCalReal b d * Gminus (b + d, b - d) := by
    ext d; rw [spinHbCal_ofReal, Complex.ofReal_re]
  rw [hre_p, hre_m]

private lemma spinCalNorm_le_of_window
    {C_24 C_p C_33 c_exp R₀ C_x R c x₁ : ℝ}
    (hc : 40 ≤ c) (hC24_pos : 0 < C_24) (hCp_pos : 0 < C_p)
    (hC33_pos : 0 < C_33) (hc_exp : 0 < c_exp) (hR₀ : R₀ ≤ R) (hRCx : C_x + 1 ≤ R)
    (hCx : 0 < C_x)
    (hx1_abs : |x₁ - xiStar| ≤ C_x * (c - 1) ^ (-(2 / 3 : ℝ)))
    {Φ : ℝ × ℝ → ℝ} (hslack : SpinSlackHyp c x₁ Φ)
    (hεR : (c - 1) ^ (-(2 / 3 : ℝ)) * R ≤ xiStar / 2)
    (hn1 : 1 ≤ c - 1)
    (hs24 : let n := c - 1; let a := n / 12; let δ_n := n ^ (-(2 / 3 : ℝ)) * Real.log n;
      let Gplus := fun q : ℝ × ℝ => max (spinG a Φ q.1 q.2) 0;
      let Gminus := fun q : ℝ × ℝ => max (-spinG a Φ q.1 q.2) 0;
      (∀ E : Set ℝ, MeasurableSet E →
        |(spinRhoProjMeasure c Gminus E).toReal - (spinEtaProjMeasure a Gminus E).toReal| ≤ C_24 * δ_n) ∧
      (spinRhoProjMeasure c Gplus (Ici 0)).toReal ≤ (spinEtaProjMeasure a Gplus (Ici 0)).toReal + C_24 / n ∧
      (spinEtaProjMeasure a Gminus (Ici 0)).toReal - C_24 * δ_n ≤ (spinRhoProjMeasure c Gminus (Ici 0)).toReal ∧
      (spinRhoProjMeasure c Gminus (Icc 0 (xiStar - xiStar / 2))).toReal ≤
        C_24 * δ_n + C_p * n ^ (-3 : ℝ))
    (hs33 : ∫ p in {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
        spinLongDist q ≤ xiStar - (c - 1) ^ (-(2 / 3 : ℝ)) * R},
      max (-spinG ((c - 1) / 12) Φ p.1 p.2) 0 *
        spinWc ((c - 1) / 12) p.1 * spinWc ((c - 1) / 12) p.2 ≤
        C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) :
    let n := c - 1
    let δ_n := n ^ (-(2 / 3 : ℝ)) * Real.log n
    spinCalNorm c Φ ≤
      n⁻¹ + C_24 / n + 3 * C_24 * δ_n + 2 * C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) +
        4 * ∫ u in Icc (-R) R, |spinFProfile c Φ u| := by
  intro n δ_n
  set a : ℝ := n / 12
  set ε : ℝ := n ^ (-(2 / 3 : ℝ))
  have hn_pos : 0 < n := by linarith
  have ha0 : 0 ≤ a := by dsimp [a]; linarith
  have ha_pos : 0 < a := by dsimp [a]; linarith
  have hε_pos : 0 < ε := Real.rpow_pos_of_pos hn_pos _
  rcases hslack with ⟨hx1_nn, hΦ, hM2, hvac, hgap⟩
  have hG_meas : Measurable (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
    unfold spinG
    exact (hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable
  let Gplus : ℝ × ℝ → ℝ := fun q => max (spinG a Φ q.1 q.2) 0
  let Gminus : ℝ × ℝ → ℝ := fun q => max (-spinG a Φ q.1 q.2) 0
  have hGp_meas : Measurable Gplus := hG_meas.max measurable_const
  have hGm_meas : Measurable Gminus := hG_meas.neg.max measurable_const
  have hGp_nn : ∀ q, 0 ≤ Gplus q := fun q => le_max_right _ _
  have hGm_nn : ∀ q, 0 ≤ Gminus q := fun q => le_max_right _ _
  have hGp_bd : ∀ q, |Gplus q| ≤ |spinG a Φ q.1 q.2| := fun q => by
    rw [abs_of_nonneg (hGp_nn q)]; exact max_le (le_abs_self _) (abs_nonneg _)
  have hGm_bd : ∀ q, |Gminus q| ≤ |spinG a Φ q.1 q.2| := fun q => by
    rw [abs_of_nonneg (hGm_nn q)]; exact max_le (neg_le_abs _) (abs_nonneg _)
  have hGp_nl : ∀ x y, Gplus (-x, y) = Gplus (x, y) := fun x y => by
    dsimp [Gplus]; rw [spinG_d4_neg_left hΦ]
  have hGp_nr : ∀ x y, Gplus (x, -y) = Gplus (x, y) := fun x y => by
    dsimp [Gplus]; rw [spinG_d4_neg_right hΦ]
  have hGm_nl : ∀ x y, Gminus (-x, y) = Gminus (x, y) := fun x y => by
    dsimp [Gminus]; rw [spinG_d4_neg_left hΦ]
  have hGm_nr : ∀ x y, Gminus (x, -y) = Gminus (x, y) := fun x y => by
    dsimp [Gminus]; rw [spinG_d4_neg_right hΦ]
  let wp : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * spinCalProjFn Gplus b
  let wm : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * spinCalProjFn Gminus b
  let z : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * |(spinGcal a Φ (b : ℂ)).re|
  have hwp_pair := spinRhoProjMeasure_toReal_s4_3_4 hc hΦ hGp_meas hGp_nn hGp_bd hGp_nl hGp_nr
    (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))
  have hwm_pair := spinRhoProjMeasure_toReal_s4_3_4 hc hΦ hGm_meas hGm_nn hGm_bd hGm_nl hGm_nr
    (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))
  have hwp_int : Integrable wp volume := hwp_pair.1
  have hwm_int : Integrable wm volume := hwm_pair.1
  have hwp_nn : ∀ b, 0 ≤ wp b := fun b => by
    dsimp [wp]
    refine mul_nonneg (mul_nonneg ha0 (Real.exp_pos _).le) ?_
    unfold spinCalProjFn
    refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
    rw [spinHbCal_ofReal, Complex.ofReal_re]
    exact mul_nonneg (spinHbCalReal_nonneg b d) (hGp_nn _)
  have hwm_nn : ∀ b, 0 ≤ wm b := fun b => by
    dsimp [wm]
    refine mul_nonneg (mul_nonneg ha0 (Real.exp_pos _).le) ?_
    unfold spinCalProjFn
    refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
    rw [spinHbCal_ofReal, Complex.ofReal_re]
    exact mul_nonneg (spinHbCalReal_nonneg b d) (hGm_nn _)
  have hz_ae : ∀ᵐ b : ℝ ∂volume, z b = |wp b - wm b| := by
    filter_upwards [spinGcal_re_sub_ae hc hΦ] with b hb
    dsimp [z, wp, wm]
    rw [hb, ← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg ha0 (Real.exp_pos _).le)]
  have hz_int : Integrable z volume :=
    (hwp_int.sub hwm_int).abs.congr (hz_ae.mono fun _ h => h.symm)
  let K_R : Set ℝ := Icc (xiStar - ε * R) (xiStar + ε * R)
  let E_ext : Set ℝ := Ici 0 \ K_R
  have hKR_meas : MeasurableSet K_R := measurableSet_Icc
  have hEext_meas : MeasurableSet E_ext := measurableSet_Ici.diff hKR_meas
  have hEext_pre_meas : MeasurableSet (abs ⁻¹' E_ext) := hEext_meas.preimage measurable_abs
  have hKR_pre_meas : MeasurableSet (abs ⁻¹' K_R) := hKR_meas.preimage measurable_abs
  have hwm_ext_int : Integrable ((abs ⁻¹' E_ext).indicator fun b => 2 * wm b) volume :=
    (hwm_int.const_mul 2).indicator hEext_pre_meas
  have hz_KR_int : Integrable ((abs ⁻¹' K_R).indicator fun b => 2 * z b) volume :=
    (hz_int.const_mul 2).indicator hKR_pre_meas
  have hrhs_int : Integrable (fun b : ℝ =>
      (wp b - wm b) + (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b +
        (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) volume :=
    ((hwp_int.sub hwm_int).add hwm_ext_int).add hz_KR_int
  have hpoint_ae : ∀ᵐ b : ℝ ∂volume,
      z b ≤ (wp b - wm b) + (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b +
        (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b := by
    filter_upwards [hz_ae] with b hbz
    rw [hbz]
    by_cases hbK : |b| ∈ K_R
    · have hbE : b ∉ abs ⁻¹' E_ext := fun h => h.2 hbK
      have hbK' : b ∈ abs ⁻¹' K_R := hbK
      rw [Set.indicator_of_notMem hbE, Set.indicator_of_mem hbK', add_zero, hbz]
      have h0 : 0 ≤ (wp b - wm b) + |wp b - wm b| := by linarith [neg_le_abs (wp b - wm b)]
      linarith
    · have hbE : b ∈ abs ⁻¹' E_ext := ⟨abs_nonneg b, hbK⟩
      have hbK' : b ∉ abs ⁻¹' K_R := hbK
      rw [Set.indicator_of_mem hbE, Set.indicator_of_notMem hbK', add_zero]
      have htri : |wp b - wm b| ≤ wp b + wm b := by
        calc |wp b - wm b| ≤ |wp b| + |wm b| := abs_sub _ _
          _ = wp b + wm b := by rw [abs_of_nonneg (hwp_nn b), abs_of_nonneg (hwm_nn b)]
      linarith
  have hmain_int : spinCalNorm c Φ ≤
      (∫ b : ℝ, wp b - wm b) + (∫ b : ℝ, (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b) +
        (∫ b : ℝ, (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) := by
    unfold spinCalNorm
    calc ∫ b : ℝ, z b
        ≤ ∫ b : ℝ, (wp b - wm b) + (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b +
            (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b :=
          integral_mono_ae hz_int hrhs_int hpoint_ae
      _ = (∫ b : ℝ, wp b - wm b) + (∫ b : ℝ, (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b) +
            (∫ b : ℝ, (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) := by
          exact (integral_add ((hwp_int.sub hwm_int).add hwm_ext_int) hz_KR_int).trans
            (congrArg (· + _) (integral_add (hwp_int.sub hwm_int) hwm_ext_int))
  -- Bound Term 1: `∫ (wp - wm) = (ρplus (Ici 0)).toReal - (ρminus (Ici 0)).toReal ≤ n⁻¹ + C_24 / n + C_24 * δ_n`
  have hpre_Ici : abs ⁻¹' Ici (0 : ℝ) = Set.univ := by ext b; simp [abs_nonneg b]
  have hρp_eq : (spinRhoProjMeasure c Gplus (Ici 0)).toReal = ∫ b : ℝ, wp b := by
    rw [hwp_pair.2, hpre_Ici, setIntegral_univ]
  have hρm_eq : (spinRhoProjMeasure c Gminus (Ici 0)).toReal = ∫ b : ℝ, wm b := by
    rw [hwm_pair.2, hpre_Ici, setIntegral_univ]
  have hηp_pair := spinEtaProjMeasure_toReal_s4_3_4 hc hΦ hGp_meas hGp_nn hGp_bd
    (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))
  have hηm_pair := spinEtaProjMeasure_toReal_s4_3_4 hc hΦ hGm_meas hGm_nn hGm_bd
    (measurableSet_Ici : MeasurableSet (Ici (0 : ℝ)))
  have hL_Ici : spinLongDist ⁻¹' Ici (0 : ℝ) = Set.univ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
    unfold spinLongDist
    positivity
  have hη_sub : (spinEtaProjMeasure a Gplus (Ici 0)).toReal -
      (spinEtaProjMeasure a Gminus (Ici 0)).toReal ≤ n⁻¹ := by
    rw [hηp_pair.2, hηm_pair.2, hL_Ici, setIntegral_univ, setIntegral_univ,
      ← integral_sub hηp_pair.1 hηm_pair.1]
    have hEq : (fun p : ℝ × ℝ =>
        Gplus p * spinWc a p.1 * spinWc a p.2 - Gminus p * spinWc a p.1 * spinWc a p.2) =
        fun p : ℝ × ℝ => spinG a Φ p.1 p.2 * spinWc a p.1 * spinWc a p.2 := by
      ext p
      have hg : spinG a Φ p.1 p.2 = Gplus p - Gminus p := by
        dsimp [Gplus, Gminus]; linarith [max_zero_sub_max_neg_zero_eq_self (spinG a Φ p.1 p.2)]
      rw [hg]; ring
    rw [hEq, ← neg_le_neg_iff, ← spinPhiVac_eq_spinWc ha_pos Φ]
    linarith [hvac]
  have hterm1 : ∫ b : ℝ, wp b - wm b ≤ n⁻¹ + C_24 / n + C_24 * δ_n := by
    rw [integral_sub hwp_int hwm_int, ← hρp_eq, ← hρm_eq]
    linarith [hs24.2.1, hs24.2.2.1, hη_sub]
  -- Bound Term 2: `2 * (ρminus E_ext).toReal ≤ 2 * C_24 * δ_n + 2 * C_33 * exp(-c_exp * R^(3/2))`
  have hwm_ext_pair := spinRhoProjMeasure_toReal_s4_3_4 hc hΦ hGm_meas hGm_nn hGm_bd hGm_nl hGm_nr
    hEext_meas
  have hηm_ext_pair := spinEtaProjMeasure_toReal_s4_3_4 hc hΦ hGm_meas hGm_nn hGm_bd hEext_meas
  have hEext_split : spinLongDist ⁻¹' E_ext ⊆ spinLongDist ⁻¹' Ico 0 (xiStar - ε * R) ∪
      spinLongDist ⁻¹' Ioi (xiStar + ε * R) := by
    intro p hp
    rcases hp with ⟨hp0, hpnot⟩
    change spinLongDist p ∉ Icc (xiStar - ε * R) (xiStar + ε * R) at hpnot
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hpnot
    rcases hpnot with hlt | hgt
    · left; exact ⟨hp0, hlt⟩
    · right; exact hgt
  have hGm_hi : ∀ p ∈ spinLongDist ⁻¹' Ioi (xiStar + ε * R),
      Gminus p * spinWc a p.1 * spinWc a p.2 = 0 := by
    intro p hp
    have hLgt : xiStar + ε * R < spinLongDist p := hp
    have hx1_lt : x₁ < spinLongDist p := by
      have hx1_ub : x₁ ≤ xiStar + C_x * ε := by linarith [(abs_le.mp hx1_abs).2]
      have hCR : C_x * ε < ε * R := by
        have : C_x < R := by linarith
        nlinarith
      linarith
    have hxi_d : x₁ ^ 2 ≤ ((p.1 + p.2) / 2) ^ 2 + ((p.1 - p.2) / 2) ^ 2 := by
      have hsq : spinLongDist p ^ 2 ≤ ((p.1 + p.2) / 2) ^ 2 + ((p.1 - p.2) / 2) ^ 2 := by
        unfold spinLongDist
        have h1 : (|p.1| + |p.2|) ^ 2 ≤ 2 * (p.1 ^ 2 + p.2 ^ 2) := by
          nlinarith [sq_nonneg (|p.1| - |p.2|), sq_abs p.1, sq_abs p.2]
        nlinarith
      exact (pow_le_pow_left₀ hx1_nn hx1_lt.le 2).trans hsq
    have hG_nn := hgap ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) hxi_d
    have hp1 : (p.1 + p.2) / 2 + (p.1 - p.2) / 2 = p.1 := by ring
    have hp2 : (p.1 + p.2) / 2 - (p.1 - p.2) / 2 = p.2 := by ring
    rw [hp1, hp2] at hG_nn
    have hGm0 : Gminus p = 0 := max_eq_right (by linarith)
    rw [hGm0, zero_mul, zero_mul]
  let S_33 : Set (ℝ × ℝ) := {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
    spinLongDist q ≤ xiStar - ε * R}
  have hS33_meas : MeasurableSet S_33 := by
    have h1 : Measurable (fun q : ℝ × ℝ => (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4) :=
      ((continuous_fst.add continuous_snd).pow 2 |>.div_const 4 |>.add
        ((continuous_fst.sub continuous_snd).pow 2 |>.div_const 4)).measurable
    have h2 : Measurable spinLongDist :=
      measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
    exact (measurableSet_lt h1 measurable_const).inter (measurableSet_le h2 measurable_const)
  have hterm2 : (∫ b : ℝ, (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b) ≤
      2 * C_24 * δ_n + 2 * C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
    have hEq_ind : (∫ b : ℝ, (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b) =
        2 * ∫ b in abs ⁻¹' E_ext, wm b := by
      have h1 : (fun b : ℝ => (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b) =
          fun b => 2 * (abs ⁻¹' E_ext).indicator wm b := by
        ext b; by_cases hb : b ∈ abs ⁻¹' E_ext <;> simp [hb]
      rw [h1, integral_const_mul, integral_indicator hEext_pre_meas]
    rw [hEq_ind, ← hwm_ext_pair.2]
    have h1 := (abs_le.mp (hs24.1 E_ext hEext_meas)).2
    have h2 : (spinEtaProjMeasure a Gminus E_ext).toReal ≤
        C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) := by
      rw [hηm_ext_pair.2]
      have hmL : Measurable spinLongDist :=
        measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
      have hsub_ae : ∫ p in spinLongDist ⁻¹' E_ext, Gminus p * spinWc a p.1 * spinWc a p.2 ≤
          ∫ p in S_33, Gminus p * spinWc a p.1 * spinWc a p.2 := by
        rw [← integral_indicator (hEext_meas.preimage hmL), ← integral_indicator hS33_meas]
        refine integral_mono (hηm_ext_pair.1.indicator (hEext_meas.preimage hmL))
          (hηm_ext_pair.1.indicator hS33_meas) fun p => ?_
        by_cases hp : p ∈ spinLongDist ⁻¹' E_ext
        · rcases hEext_split hp with hp_lo | hp_hi
          · by_cases hpS : p ∈ S_33
            · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpS]
            · have hG_nn : 0 ≤ spinG a Φ p.1 p.2 := by
                have hnot : ¬ (p.1 + p.2) ^ 2 / 4 + (p.1 - p.2) ^ 2 / 4 < x₁ ^ 2 := fun hlt =>
                  hpS ⟨hlt, hp_lo.2.le⟩
                have hge : x₁ ^ 2 ≤ ((p.1 + p.2) / 2) ^ 2 + ((p.1 - p.2) / 2) ^ 2 := by linarith
                have h0 := hgap ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) hge
                have hp1 : (p.1 + p.2) / 2 + (p.1 - p.2) / 2 = p.1 := by ring
                have hp2 : (p.1 + p.2) / 2 - (p.1 - p.2) / 2 = p.2 := by ring
                rwa [hp1, hp2] at h0
              have hGm0 : Gminus p = 0 := max_eq_right (by linarith)
              rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hpS, hGm0, zero_mul, zero_mul]
          · rw [Set.indicator_of_mem hp, hGm_hi p hp_hi]
            exact Set.indicator_nonneg (fun q _ => mul_nonneg (mul_nonneg (hGm_nn q)
              (spinWc_nonneg (by dsimp [a]; linarith) q.1))
              (spinWc_nonneg (by dsimp [a]; linarith) q.2)) p
        · rw [Set.indicator_of_notMem hp]
          exact Set.indicator_nonneg (fun q _ => mul_nonneg (mul_nonneg (hGm_nn q)
            (spinWc_nonneg (by dsimp [a]; linarith) q.1))
            (spinWc_nonneg (by dsimp [a]; linarith) q.2)) p
      exact hsub_ae.trans hs33
    linarith
  -- Bound Term 3: `∫ (abs ⁻¹' K_R).indicator (fun b => 2 * z b) = 4 * ∫ u in Icc (-R) R, |spinFProfile c Φ u|`
  have hKR_pos : 0 < xiStar - ε * R := by linarith [xiStar_pos]
  have hz_even : ∀ b : ℝ, z (-b) = z b := fun b => by
    dsimp [z]
    have hL : spinL (-b) = spinL b := by unfold spinL; rw [abs_neg]
    have hce : ((-b : ℝ) : ℂ) = -(b : ℂ) := by push_cast; rfl
    rw [hL, hce, spinGcal_re_even ha0 hΦ b]
  have hpre_KR : abs ⁻¹' K_R = K_R ∪ (Neg.neg ⁻¹' K_R) := by
    ext b
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_Icc, K_R]
    rcases le_or_gt 0 b with hb | hb
    · rw [abs_of_nonneg hb]
      constructor
      · intro h; left; exact h
      · rintro (h | h); exact h; linarith
    · rw [abs_of_neg hb]
      constructor
      · intro h; right; exact h
      · rintro (h | h); linarith; exact h
  have hdisj_KR : Disjoint K_R (Neg.neg ⁻¹' K_R) := Set.disjoint_left.mpr fun b hb1 hb2 => by
    have h1 : xiStar - ε * R ≤ b := hb1.1
    have h2 : xiStar - ε * R ≤ -b := hb2.1
    linarith
  have hterm3 : (∫ b : ℝ, (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) =
      4 * ∫ u in Icc (-R) R, |spinFProfile c Φ u| := by
    have h1 : (∫ b : ℝ, (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) =
        2 * ∫ b in abs ⁻¹' K_R, z b := by
      have heq : (fun b : ℝ => (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) =
          fun b => 2 * (abs ⁻¹' K_R).indicator z b := by
        ext b; by_cases hb : b ∈ abs ⁻¹' K_R <;> simp [hb]
      rw [heq, integral_const_mul, integral_indicator hKR_pre_meas]
    have hneg_pre : MeasurableSet (Neg.neg ⁻¹' K_R) := hKR_meas.preimage measurable_neg
    have hsplit_int : ∫ b in abs ⁻¹' K_R, z b =
        (∫ b in K_R, z b) + ∫ b in Neg.neg ⁻¹' K_R, z b := by
      rw [← integral_indicator hKR_pre_meas, ← integral_indicator hKR_meas,
        ← integral_indicator hneg_pre, ← integral_add (hz_int.indicator hKR_meas)
        (hz_int.indicator hneg_pre)]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      rw [hpre_KR, Set.indicator_union_of_disjoint hdisj_KR]
    have hneg_eq : ∫ b in Neg.neg ⁻¹' K_R, z b = ∫ b in K_R, z b := by
      rw [← integral_indicator hneg_pre, ← integral_indicator hKR_meas]
      let e : ℝ ≃ᵐ ℝ := MeasurableEquiv.neg ℝ
      have hmp : Measure.map e (volume : Measure ℝ) = volume := by
        change Measure.map (-·) (volume : Measure ℝ) = volume
        exact Measure.map_neg_eq_self volume
      have heq := integral_map_equiv (μ := (volume : Measure ℝ)) e
        (fun b => K_R.indicator z b)
      rw [hmp] at heq
      rw [heq]
      refine integral_congr_ae (Eventually.of_forall fun b => ?_)
      change (Neg.neg ⁻¹' K_R).indicator z b = K_R.indicator z (-b)
      by_cases hb : b ∈ Neg.neg ⁻¹' K_R
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem (show -b ∈ K_R from hb), hz_even b]
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem (show -b ∉ K_R from hb)]
    have hcov : ∫ b in K_R, z b = ∫ u in Icc (-R) R, |spinFProfile c Φ u| := by
      rw [← integral_indicator hKR_meas, ← integral_indicator measurableSet_Icc]
      have hshift : (∫ y : ℝ, K_R.indicator z (xiStar + y)) = ∫ b : ℝ, K_R.indicator z b :=
        integral_add_left_eq_self (K_R.indicator z) xiStar
      have hscale : (∫ u : ℝ, K_R.indicator z (xiStar + ε * u)) =
          ε⁻¹ * ∫ y : ℝ, K_R.indicator z (xiStar + y) := by
        let e₀ : ℝ ≃ᵐ ℝ := MeasurableEquiv.mulLeft₀ ε hε_pos.ne'
        have heq := integral_map_equiv (μ := (volume : Measure ℝ)) e₀
          (fun y => K_R.indicator z (xiStar + y))
        have he₀ : (e₀ : ℝ → ℝ) = fun x => ε * x := rfl
        rw [he₀, Real.map_volume_mul_left hε_pos.ne', integral_smul_measure,
          abs_of_pos (inv_pos.mpr hε_pos), ENNReal.toReal_ofReal (inv_pos.mpr hε_pos).le,
          smul_eq_mul] at heq
        exact heq.symm
      rw [← hshift, show (∫ y : ℝ, K_R.indicator z (xiStar + y)) =
          ε * ∫ u : ℝ, K_R.indicator z (xiStar + ε * u) by
            rw [hscale, ← mul_assoc, mul_inv_cancel₀ hε_pos.ne', one_mul], ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      change ε * K_R.indicator z (xiStar + ε * u) = (Icc (-R) R).indicator (fun u => |spinFProfile c Φ u|) u
      have hmem : xiStar + ε * u ∈ K_R ↔ u ∈ Icc (-R) R := by
        dsimp [K_R]
        simp only [Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨le_of_mul_le_mul_left (by linarith) hε_pos, le_of_mul_le_mul_left (by linarith) hε_pos⟩
        · rintro ⟨h1, h2⟩
          have h1' : ε * (-R) ≤ ε * u := mul_le_mul_of_nonneg_left h1 hε_pos.le
          have h2' : ε * u ≤ ε * R := mul_le_mul_of_nonneg_left h2 hε_pos.le
          constructor <;> linarith
      by_cases hu : u ∈ Icc (-R) R
      · rw [Set.indicator_of_mem (hmem.mpr hu), Set.indicator_of_mem hu]
        unfold spinFProfile
        dsimp [z]
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hε_pos.le,
          abs_of_nonneg (Real.exp_pos _).le]
        ring
      · rw [Set.indicator_of_notMem (mt hmem.mp hu), Set.indicator_of_notMem hu, mul_zero]
    rw [h1, hsplit_int, hneg_eq, hcov]
    ring
  calc spinCalNorm c Φ
      ≤ (∫ b : ℝ, wp b - wm b) + (∫ b : ℝ, (abs ⁻¹' E_ext).indicator (fun b => 2 * wm b) b) +
          (∫ b : ℝ, (abs ⁻¹' K_R).indicator (fun b => 2 * z b) b) := hmain_int
    _ ≤ (n⁻¹ + C_24 / n + C_24 * δ_n) +
          (2 * C_24 * δ_n + 2 * C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) +
          4 * ∫ u in Icc (-R) R, |spinFProfile c Φ u| := by linarith
    _ = n⁻¹ + C_24 / n + 3 * C_24 * δ_n + 2 * C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) +
          4 * ∫ u in Icc (-R) R, |spinFProfile c Φ u| := by ring

/-- **Theorem `s4:3.4` (`SpinS4_3_4`, `spinning_s4.tex`):** local `L^1([-R, R])` vanishing of the
rescaled calibrated profile `spinFProfile` for every fixed `R > 0` forces global `L^1` vanishing of
`spinCalNorm` along any slack-feasible sequence with `c_k → ∞` and `|x_{1,k} - ξ_*| ≤ C_x n_k^{-2/3}`. -/
theorem spinS4_3_4 : SpinS4_3_4 := by
  intro C_x cSeq xSeq ΦSeq hCx hcSeq hseq hloc
  rw [Metric.tendsto_atTop]
  intro η hη
  have hr0_pos : 0 < xiStar / 2 := half_pos xiStar_pos
  have hr0_lt : xiStar / 2 < xiStar := half_lt_self xiStar_pos
  obtain ⟨C_24, C_p, c₀, hC24_pos, hCp_pos, hc₀40, hs24_all⟩ :=
    spinS4_2_4 (p := 3) (r₀ := xiStar / 2) (by norm_num) hr0_pos hr0_lt
  obtain ⟨C_33, c_exp, R₀, hC33_pos, hc_exp, _hR₀_pos, hs33_all⟩ := spinS4_3_3 hCx
  have hRpow : Tendsto (fun R : ℝ => R ^ (3 / 2 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hTexp : Tendsto (fun R : ℝ => 2 * C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => -c_exp * R ^ (3 / 2 : ℝ)) atTop atBot :=
      Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hc_exp) hRpow
    have h2 : Tendsto (fun R : ℝ => Real.exp (-c_exp * R ^ (3 / 2 : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp h1
    simpa using h2.const_mul (2 * C_33)
  have hR_ev : ∀ᶠ R : ℝ in atTop,
      R₀ ≤ R ∧ C_x + 1 ≤ R ∧ 2 * C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) < η / 3 :=
    (eventually_ge_atTop R₀).and
      ((eventually_ge_atTop (C_x + 1)).and (hTexp.eventually (gt_mem_nhds (by linarith))))
  obtain ⟨R, hR₀, hRCx, hT_lt⟩ := hR_ev.exists
  have hR_pos : 0 < R := by linarith
  have hs33_ev := hs33_all hR₀
  have hn_top : Tendsto (fun k => cSeq k - 1) atTop atTop :=
    hcSeq.atTop_add tendsto_const_nhds
  have hinv_tend : Tendsto (fun n : ℝ => n⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hcn_tend : Tendsto (fun n : ℝ => C_24 / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv_tend.const_mul C_24
  have hrpow_tend : Tendsto (fun n : ℝ => n ^ (-(2 / 3 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 3)
  have hδ_tend : Tendsto (fun n : ℝ => n ^ (-(2 / 3 : ℝ)) * Real.log n) atTop (𝓝 0) := by
    have ho : (Real.log) =o[atTop] (fun x : ℝ => x ^ (2 / 3 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)
    have ht := ho.tendsto_div_nhds_zero
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, inv_mul_eq_div]
  have hcomb_tend : Tendsto (fun n : ℝ =>
      n⁻¹ + C_24 / n + 3 * C_24 * (n ^ (-(2 / 3 : ℝ)) * Real.log n)) atTop (𝓝 0) := by
    have h0 := (hinv_tend.add hcn_tend).add (hδ_tend.const_mul (3 * C_24))
    simpa using h0
  have hlocR := hloc R hR_pos
  have hk_c0 : ∀ᶠ k in atTop, c₀ ≤ cSeq k := hcSeq.eventually (eventually_ge_atTop c₀)
  have hk_n1 : ∀ᶠ k in atTop, 1 ≤ cSeq k - 1 := hn_top.eventually (eventually_ge_atTop 1)
  have hk_s33 : ∀ᶠ k in atTop,
      let n' := cSeq k - 1; let c := n' + 1; let ε := n' ^ (-(2 / 3 : ℝ)); let a := n' / 12;
      ∀ {x₁ : ℝ} {Φ : ℝ × ℝ → ℝ}, |x₁ - xiStar| ≤ C_x * ε → SpinSlackHyp c x₁ Φ →
        ∫ p in {q : ℝ × ℝ | (q.1 + q.2) ^ 2 / 4 + (q.1 - q.2) ^ 2 / 4 < x₁ ^ 2 ∧
          spinLongDist q ≤ xiStar - ε * R},
          max (-spinG a Φ p.1 p.2) 0 * spinWc a p.1 * spinWc a p.2 ≤
          C_33 * Real.exp (-c_exp * R ^ (3 / 2 : ℝ)) :=
    hn_top.eventually hs33_ev
  have hk_εR : ∀ᶠ k in atTop, (cSeq k - 1) ^ (-(2 / 3 : ℝ)) * R ≤ xiStar / 2 := by
    have h0 : Tendsto (fun k => (cSeq k - 1) ^ (-(2 / 3 : ℝ)) * R) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (hrpow_tend.mul_const R).comp hn_top
    exact (h0.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < xiStar / 2))).mono
      fun _ h => h.le
  have hk_comb : ∀ᶠ k in atTop,
      (cSeq k - 1)⁻¹ + C_24 / (cSeq k - 1) +
        3 * C_24 * ((cSeq k - 1) ^ (-(2 / 3 : ℝ)) * Real.log (cSeq k - 1)) < η / 3 :=
    (hcomb_tend.comp hn_top).eventually (gt_mem_nhds (by linarith))
  have hk_loc : ∀ᶠ k in atTop, 4 * ∫ u in Icc (-R) R, |spinFProfile (cSeq k) (ΦSeq k) u| < η / 3 := by
    have h0 : Tendsto (fun k => 4 * ∫ u in Icc (-R) R, |spinFProfile (cSeq k) (ΦSeq k) u|)
        atTop (𝓝 0) := by
      simpa using hlocR.const_mul 4
    exact h0.eventually (gt_mem_nhds (by linarith))
  have h_all : ∀ᶠ k in atTop, c₀ ≤ cSeq k ∧ spinCalNorm (cSeq k) (ΦSeq k) < η := by
    filter_upwards [hk_c0, hk_n1, hk_s33, hk_εR, hk_comb, hk_loc] with k hc0 hn1 hs33_k hεR_k hcomb_k hloc_k
    have hc40 : 40 ≤ cSeq k := le_trans hc₀40 hc0
    obtain ⟨hx1_abs, hslack_k⟩ := hseq k
    have hx1_ub : xSeq k ≤ xiStar + C_x * (cSeq k - 1) ^ (-(2 / 3 : ℝ)) := by
      linarith [(abs_le.mp hx1_abs).2]
    have hs24_k := hs24_all hc0 hx1_ub hslack_k
    have hs33_k' := hs33_k hx1_abs (by simpa [sub_add_cancel] using hslack_k)
    have hbd := spinCalNorm_le_of_window hc40 hC24_pos hCp_pos hC33_pos hc_exp hR₀ hRCx hCx
      hx1_abs hslack_k hεR_k hn1 hs24_k hs33_k'
    exact ⟨hc0, by linarith⟩
  rw [eventually_atTop] at h_all
  obtain ⟨K, hK⟩ := h_all
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨hc0_k, hlt_k⟩ := hK k hk
  have ha0 : 0 ≤ (cSeq k - 1) / 12 := by linarith [hc₀40]
  have hnn : 0 ≤ spinCalNorm (cSeq k) (ΦSeq k) := by
    unfold spinCalNorm
    exact integral_nonneg fun b => mul_nonneg (mul_nonneg ha0 (Real.exp_pos _).le) (abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  exact hlt_k

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_3_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_3_4

end FormalResearch.ModularBootstrap.Spin

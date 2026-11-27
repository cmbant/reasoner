module

public import FormalResearch.ModularBootstrap.Spin.SpinS4_2_3

/-!
# SPIN-S4 Lemma `s4:2.4` (Calibrated Projection vs Longitudinal Marginals)

Proves:
1. `spinRhoProjMeasure_toReal` and `spinEtaProjMeasure_toReal`: exact integral
   representations of `spinRhoProjMeasure` and `spinEtaProjMeasure` for measurable sets `E`.
2. **`spinS4_2_4 : SpinS4_2_4`** (`spinning_s4.tex`, Lemma 2.4).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap

/-! ### Measure identities for `ρ_n^±` and `η_n^±` -/

private lemma spinRhoProjMeasure_toReal {c : ℝ} (hc : 40 ≤ c)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass ((c - 1) / 12) Φ)
    {G : ℝ × ℝ → ℝ} (hG_meas : Measurable G)
    (hG_nn : ∀ p : ℝ × ℝ, 0 ≤ G p)
    (hG_bd : ∀ p : ℝ × ℝ, G p ≤ |spinG ((c - 1) / 12) Φ p.1 p.2|)
    (hG_nl : ∀ x y : ℝ, G (-x, y) = G (x, y))
    (hG_nr : ∀ x y : ℝ, G (x, -y) = G (x, y))
    {E : Set ℝ} (hE : MeasurableSet E) :
    let n := c - 1
    let a := n / 12
    (spinRhoProjMeasure c G E).toReal =
      ∫ p : ℝ × ℝ,
        (spinRc1 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * E.indicator 1 (spinLongDist p) +
         spinRc2 a (spinLongDist p) ((|p.1| - |p.2|) / 2) * E.indicator 1 (spinTransDist p)) *
          G p * spinWc a p.1 * spinWc a p.2 := by
  intro n a
  let φ : ℝ → ℝ := E.indicator 1
  have hφ_meas : Measurable φ := measurable_one.indicator hE
  have hφ_bd : ∀ x : ℝ, |φ x| ≤ 1 := fun x => by
    by_cases hx : x ∈ E <;> simp [φ, hx]
  have hG_abs_bd : ∀ p : ℝ × ℝ, |G p| ≤ |spinG a Φ p.1 p.2| := fun p => by
    rw [abs_of_nonneg (hG_nn p)]; exact hG_bd p
  have hadj := spinCal_adjoint_identity hc hΦ hG_meas hG_abs_bd hG_nl hG_nr
    hφ_meas zero_le_one hφ_bd
  let f : ℝ → ℝ := fun b => a * Real.exp (n * spinL b) * spinCalProjFn G b
  have ha0 : 0 < a := by dsimp [a, n]; linarith
  have hf_nn : ∀ b : ℝ, 0 ≤ f b := fun b => by
    have hp1 : 0 ≤ a * Real.exp (n * spinL b) := mul_nonneg ha0.le (Real.exp_pos _).le
    have hp2 : 0 ≤ spinCalProjFn G b := by
      unfold spinCalProjFn
      refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
      rw [spinHbCal_ofReal]
      exact mul_nonneg (spinHbCalReal_nonneg b d) (hG_nn _)
    exact mul_nonneg hp1 hp2
  have hφf_eq : ∀ b : ℝ, φ |b| * f b =
      a * Real.exp (n * spinL b) * φ |b| *
        (4 * spinCalF xiStar ^ 2 * ∫ d : ℝ, spinHbCalReal b d * G (b + d, b - d)) := by
    intro b
    dsimp [f]; unfold spinCalProjFn
    have heq : (∫ d : ℝ, (spinHbCal (b : ℂ) d).re * G (b + d, b - d)) =
        ∫ d : ℝ, spinHbCalReal b d * G (b + d, b - d) :=
      integral_congr_ae (Eventually.of_forall fun d => by dsimp only; rw [spinHbCal_ofReal, Complex.ofReal_re])
    rw [heq]; ring
  have hφf_int : Integrable (fun b : ℝ => φ |b| * f b) := by
    have hprod : Integrable (fun p : ℝ × ℝ =>
        a * Real.exp (n * spinL p.1) * φ |p.1| *
          (4 * spinCalF xiStar ^ 2 * spinHbCalReal p.1 p.2 * G (p.1 + p.2, p.1 - p.2)))
        (volume.prod volume) := by
      rw [← Measure.volume_eq_prod]; exact hadj.1
    have hleft := hprod.integral_prod_left
    have hfun : (fun b : ℝ => ∫ d : ℝ, a * Real.exp (n * spinL b) * φ |b| *
        (4 * spinCalF xiStar ^ 2 * spinHbCalReal b d * G (b + d, b - d))) =
        fun b : ℝ => φ |b| * f b := by
      ext b
      calc ∫ d : ℝ, a * Real.exp (n * spinL b) * φ |b| *
              (4 * spinCalF xiStar ^ 2 * spinHbCalReal b d * G (b + d, b - d))
          = ∫ d : ℝ, (a * Real.exp (n * spinL b) * φ |b| * (4 * spinCalF xiStar ^ 2)) *
              (spinHbCalReal b d * G (b + d, b - d)) := by
            congr 1; ext d; ring
        _ = a * Real.exp (n * spinL b) * φ |b| * (4 * spinCalF xiStar ^ 2) *
              ∫ d : ℝ, spinHbCalReal b d * G (b + d, b - d) :=
            integral_const_mul _ _
        _ = φ |b| * f b := by rw [hφf_eq b]; ring
    rwa [hfun] at hleft
  have hφf_nn : ∀ b : ℝ, 0 ≤ φ |b| * f b := fun b => by
    have hφ0 : 0 ≤ φ |b| := by by_cases hb : |b| ∈ E <;> simp [φ, hb]
    exact mul_nonneg hφ0 (hf_nn b)
  have hrho_eq : spinRhoProjMeasure c G E =
      ∫⁻ b : ℝ, ENNReal.ofReal (φ |b| * f b) := by
    have hmabs : MeasurableSet (abs ⁻¹' E) := continuous_abs.measurable hE
    have hmax : (fun b : ℝ => ENNReal.ofReal (a * Real.exp (n * spinL b) * max (spinCalProjFn G b) 0)) =
        fun b : ℝ => ENNReal.ofReal (f b) := by
      ext b
      have hcp : 0 ≤ spinCalProjFn G b := by
        unfold spinCalProjFn
        refine mul_nonneg (by positivity) (integral_nonneg fun d => ?_)
        rw [spinHbCal_ofReal]; exact mul_nonneg (spinHbCalReal_nonneg b d) (hG_nn _)
      dsimp [f]; rw [max_eq_left hcp]
    unfold spinRhoProjMeasure
    rw [Measure.map_apply continuous_abs.measurable hE,
      withDensity_apply _ hmabs, hmax, ← lintegral_indicator hmabs]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ abs ⁻¹' E
    · have hb' : |b| ∈ E := hb
      simp [φ, hb']
    · have hb' : |b| ∉ E := hb
      simp [φ, hb']
  rw [hrho_eq, ← ofReal_integral_eq_lintegral_ofReal hφf_int (Eventually.of_forall hφf_nn),
    ENNReal.toReal_ofReal (integral_nonneg hφf_nn)]
  calc ∫ b : ℝ, φ |b| * f b
      = ∫ b : ℝ, a * Real.exp (n * spinL b) * φ |b| *
          (4 * spinCalF xiStar ^ 2 * ∫ d : ℝ, spinHbCalReal b d * G (b + d, b - d)) := by
        refine integral_congr_ae (Eventually.of_forall hφf_eq)
    _ = _ := hadj.2.2

private lemma spinEtaProjMeasure_toReal {a : ℝ} (ha : 2 < a)
    {Φ : ℝ × ℝ → ℝ} (hΦ : SpinTestClass a Φ)
    {G : ℝ × ℝ → ℝ} (hG_meas : Measurable G)
    (hG_nn : ∀ p : ℝ × ℝ, 0 ≤ G p)
    (hG_bd : ∀ p : ℝ × ℝ, G p ≤ |spinG a Φ p.1 p.2|)
    {E : Set ℝ} (hE : MeasurableSet E) :
    (spinEtaProjMeasure a G E).toReal =
      ∫ p : ℝ × ℝ, E.indicator 1 (spinLongDist p) * G p * spinWc a p.1 * spinWc a p.2 := by
  have ha0 : 0 < a := by linarith
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  have hWc_meas : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hL_meas : Measurable spinLongDist :=
    measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
  let φ : ℝ → ℝ := E.indicator 1
  have hint : Integrable (fun p : ℝ × ℝ =>
      φ (spinLongDist p) * G p * spinWc a p.1 * spinWc a p.2) := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((((measurable_one.indicator hE).comp hL_meas).mul hG_meas |>.mul
        (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · have hφ1 : |φ (spinLongDist p)| ≤ 1 := by
        by_cases hp : spinLongDist p ∈ E <;> simp [φ, hp]
      have hw1 := spinWc_nonneg ha.le p.1
      have hw2 := spinWc_nonneg ha.le p.2
      have hG0 := hG_nn p
      have hG1 := hG_bd p
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hG0,
        abs_of_nonneg hw1, abs_of_nonneg hw2]
      calc |φ (spinLongDist p)| * G p * spinWc a p.1 * spinWc a p.2
          ≤ 1 * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by ring
  have hnn : ∀ p : ℝ × ℝ, 0 ≤ φ (spinLongDist p) * G p * spinWc a p.1 * spinWc a p.2 := fun p => by
    have hφ0 : 0 ≤ φ (spinLongDist p) := by by_cases hp : spinLongDist p ∈ E <;> simp [φ, hp]
    exact mul_nonneg (mul_nonneg (mul_nonneg hφ0 (hG_nn p)) (spinWc_nonneg ha.le _))
      (spinWc_nonneg ha.le _)
  have heta_eq : spinEtaProjMeasure a G E =
      ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (φ (spinLongDist p) * G p * spinWc a p.1 * spinWc a p.2) := by
    have hmL : MeasurableSet (spinLongDist ⁻¹' E) := hL_meas hE
    have hmax : (fun p : ℝ × ℝ => ENNReal.ofReal (max (G p) 0 * spinWc a p.1 * spinWc a p.2)) =
        fun p : ℝ × ℝ => ENNReal.ofReal (G p * spinWc a p.1 * spinWc a p.2) := by
      ext p; rw [max_eq_left (hG_nn p)]
    unfold spinEtaProjMeasure
    rw [Measure.map_apply hL_meas hE, withDensity_apply _ hmL, hmax, ← lintegral_indicator hmL]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ spinLongDist ⁻¹' E
    · have hp' : spinLongDist p ∈ E := hp
      simp [φ, hp']
    · have hp' : spinLongDist p ∉ E := hp
      simp [φ, hp']
  rw [heta_eq, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn),
    ENNReal.toReal_ofReal (integral_nonneg hnn)]

/-! ### Proof of `s4:2.4` (`SpinS4_2_4`) -/

/-- **`s4:2.4` (`spinning_s4.tex`, Lemma 2.4): comparison of calibrated projection with
longitudinal marginals.** -/
theorem spinS4_2_4 : SpinS4_2_4 := by
  intro C_x p r₀ hp hr0 hr0_lt
  obtain ⟨_c_σ, C_rc, _hcσ, hCrc_pos, hRc_bd⟩ := spinS4_2_2_abs_bound
  obtain ⟨C_2_rc, hC2rc_pos, hRc2_bd⟩ := spinRc2_le_div_n
  obtain ⟨K_2, C_2, c₀₂, hK2_pos, hC2_pos, hc02, h21_all_2⟩ :=
    spinS4_2_1_all_quads (C_x := max C_x 1) (p := 2) (by norm_num)
  obtain ⟨K_p, C_p0, c₀p, hKp_pos, hCp0_pos, hc0p, h21_all_p⟩ :=
    spinS4_2_1_all_quads (C_x := max C_x 1) (by linarith : (0 : ℝ) < p)
  obtain ⟨C_near, c₀_n, hCnear_pos, hc0n, hnear⟩ :=
    spinRc_near_tip_bound K_2 (max C_x 1) hK2_pos (le_max_right C_x 1)
  let c₀ : ℝ := max (max (max c₀₂ c₀p) c₀_n)
    (1 + max (max 39 (max C_rc (2 * C_2_rc))) ((3 * K_p / (r₀ / 2)) ^ 3))
  have hc0_ge40 : 40 ≤ c₀ :=
    le_trans hc02 (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))
  let C : ℝ := max C_rc (16 * C_2 + C_near + 2 * C_2_rc)
  let C_p : ℝ := 4 * C_p0
  refine ⟨C, C_p, c₀, by positivity, by positivity, hc0_ge40, ?_⟩
  intro c x₁ hc n a δ_n hx1_ub Φ hslack
  obtain ⟨hx10, hΦ, hM2, _hvac, hgap⟩ := hslack
  have hc40 : 40 ≤ c := hc0_ge40.trans hc
  have hc02' : c₀₂ ≤ c :=
    (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))).trans hc
  have hc0p' : c₀p ≤ c :=
    (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))).trans hc
  have hc0n' : c₀_n ≤ c := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hc
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hn_max : max 39 ((3 * K_p / (r₀ / 2)) ^ 3) ≤ n := by
    have h1 := (le_max_right (max (max c₀₂ c₀p) c₀_n) _).trans hc
    exact max_le
      (by
        dsimp [n]
        linarith [le_max_left (39 : ℝ) (max C_rc (2 * C_2_rc)),
          le_max_left (max (39 : ℝ) (max C_rc (2 * C_2_rc))) ((3 * K_p / (r₀ / 2)) ^ 3)])
      (by
        dsimp [n]
        linarith [le_max_right (max (39 : ℝ) (max C_rc (2 * C_2_rc))) ((3 * K_p / (r₀ / 2)) ^ 3)])
  have hn39 : 39 ≤ n := (le_max_left _ _).trans hn_max
  have hCrc_n : C_rc / n ≤ 1 := (div_le_one hn_pos).mpr (by
    have h1 := (le_max_right (max (max c₀₂ c₀p) c₀_n) _).trans hc
    have h2 : max C_rc (2 * C_2_rc) ≤ n := by
      dsimp [n]; linarith [le_max_right (39 : ℝ) (max C_rc (2 * C_2_rc)),
        le_max_left (max (39 : ℝ) (max C_rc (2 * C_2_rc))) ((3 * K_p / (r₀ / 2)) ^ 3)]
    exact (le_max_left _ _).trans h2)
  have h2C2rc_n : 2 * (C_2_rc / n) ≤ 1 := by
    have h1 := (le_max_right (max (max c₀₂ c₀p) c₀_n) _).trans hc
    have h2 : 2 * C_2_rc ≤ n := by
      have h3 : max C_rc (2 * C_2_rc) ≤ n := by
        dsimp [n]; linarith [le_max_right (39 : ℝ) (max C_rc (2 * C_2_rc)),
          le_max_left (max (39 : ℝ) (max C_rc (2 * C_2_rc))) ((3 * K_p / (r₀ / 2)) ^ 3)]
      exact (le_max_right _ _).trans h3
    rw [← mul_div_assoc, div_le_one hn_pos]
    exact h2
  have hinv_le : n⁻¹ ≤ δ_n := deltaN_ge_inv hn39
  have hn2_le : n ^ (-2 : ℝ) ≤ δ_n := by
    have : n ^ (-2 : ℝ) ≤ n⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact this.trans hinv_le
  have hδn_nn : 0 ≤ δ_n := le_trans (inv_nonneg.mpr hn_pos.le) hinv_le
  have hKp_r0 : K_p * δ_n ≤ r₀ / 2 := coeff_deltaN_le hKp_pos.le (half_pos hr0) hn_max
  have hx1_ub' : x₁ ≤ xiStar + max C_x 1 * n ^ (-(2 / 3 : ℝ)) :=
    hx1_ub.trans (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hn_pos.le _)) _)
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  have hG_meas : Measurable (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
    unfold spinG
    exact (hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable
  have hWc_meas : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  let Gplus : ℝ × ℝ → ℝ := fun q => max (spinG a Φ q.1 q.2) 0
  let Gminus : ℝ × ℝ → ℝ := fun q => max (-spinG a Φ q.1 q.2) 0
  have hGp_meas : Measurable Gplus := hG_meas.max measurable_const
  have hGm_meas : Measurable Gminus := hG_meas.neg.max measurable_const
  have hGp_nn : ∀ q, 0 ≤ Gplus q := fun q => le_max_right _ _
  have hGm_nn : ∀ q, 0 ≤ Gminus q := fun q => le_max_right _ _
  have hGp_bd : ∀ q, Gplus q ≤ |spinG a Φ q.1 q.2| := fun q => max_le (le_abs_self _) (abs_nonneg _)
  have hGm_bd : ∀ q, Gminus q ≤ |spinG a Φ q.1 q.2| := fun q => max_le (neg_le_abs _) (abs_nonneg _)
  have hGp_nl : ∀ x y, Gplus (-x, y) = Gplus (x, y) := fun x y => by
    dsimp [Gplus]; rw [spinG_d4_neg_left hΦ]
  have hGp_nr : ∀ x y, Gplus (x, -y) = Gplus (x, y) := fun x y => by
    dsimp [Gplus]; rw [spinG_d4_neg_right hΦ]
  have hGm_nl : ∀ x y, Gminus (-x, y) = Gminus (x, y) := fun x y => by
    dsimp [Gminus]; rw [spinG_d4_neg_left hΦ]
  have hGm_nr : ∀ x y, Gminus (x, -y) = Gminus (x, y) := fun x y => by
    dsimp [Gminus]; rw [spinG_d4_neg_right hΦ]
  have hGm_int : Integrable (fun q : ℝ × ℝ => Gminus q * spinWc a q.1 * spinWc a q.2) := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact ((hGm_meas.mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hGm_nn q),
        abs_of_nonneg (spinWc_nonneg ha2.le _), abs_of_nonneg (spinWc_nonneg ha2.le _)]
      have h1 := hGm_bd q
      have hw1 := spinWc_nonneg ha2.le q.1
      have hw2 := spinWc_nonneg ha2.le q.2
      gcongr
  have hGm_int1 : ∫ q : ℝ × ℝ, Gminus q * spinWc a q.1 * spinWc a q.2 ≤ 1 := by
    rw [← hM2, spinM2_eq_spinWc ha0 Φ]
    refine integral_mono hGm_int hG_int fun q => ?_
    have h1 := hGm_bd q
    have hw1 := spinWc_nonneg ha2.le q.1
    have hw2 := spinWc_nonneg ha2.le q.2
    gcongr
  have hGp_int : Integrable (fun q : ℝ × ℝ => Gplus q * spinWc a q.1 * spinWc a q.2) := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact ((hGp_meas.mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hGp_nn q),
        abs_of_nonneg (spinWc_nonneg ha2.le _), abs_of_nonneg (spinWc_nonneg ha2.le _)]
      have h1 := hGp_bd q
      have hw1 := spinWc_nonneg ha2.le q.1
      have hw2 := spinWc_nonneg ha2.le q.2
      gcongr
  have hGp_int1 : ∫ q : ℝ × ℝ, Gplus q * spinWc a q.1 * spinWc a q.2 ≤ 1 := by
    rw [← hM2, spinM2_eq_spinWc ha0 Φ]
    refine integral_mono hGp_int hG_int fun q => ?_
    have h1 := hGp_bd q
    have hw1 := spinWc_nonneg ha2.le q.1
    have hw2 := spinWc_nonneg ha2.le q.2
    gcongr
  have hclause1 : ∀ E : Set ℝ, MeasurableSet E →
      |(spinRhoProjMeasure c Gminus E).toReal - (spinEtaProjMeasure a Gminus E).toReal| ≤
        C * δ_n := by
    intro E hE
    rw [spinRhoProjMeasure_toReal hc40 hΦ hGm_meas hGm_nn hGm_bd hGm_nl hGm_nr hE,
      spinEtaProjMeasure_toReal ha2 hΦ hGm_meas hGm_nn hGm_bd hE]
    let φ : ℝ → ℝ := E.indicator 1
    have hφ_meas : Measurable φ := measurable_one.indicator hE
    have hφ_bd : ∀ x : ℝ, |φ x| ≤ 1 := fun x => by by_cases hx : x ∈ E <;> simp [φ, hx]
    have hL_meas : Measurable spinLongDist :=
      measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
    have hT_meas : Measurable spinTransDist :=
      measurable_const.mul (((measurable_fst.abs).sub (measurable_snd.abs)).abs)
    let diffFn : ℝ × ℝ → ℝ := fun q =>
      ((spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1) * φ (spinLongDist q) +
       spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * (φ (spinTransDist q) - φ (spinLongDist q))) *
        Gminus q * spinWc a q.1 * spinWc a q.2
    have hI1 : Integrable (fun q : ℝ × ℝ =>
        (spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinLongDist q) +
         spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinTransDist q)) *
          Gminus q * spinWc a q.1 * spinWc a q.2) := by
      refine (hG_int.const_mul (1 + C_rc / n)).mono' ?_ (Eventually.of_forall fun q => ?_)
      · exact ((((measurable_spinRc1 a).mul (hφ_meas.comp hL_meas)).add
          ((measurable_spinRc2 a).mul (hφ_meas.comp hT_meas))).mul hGm_meas |>.mul
            (hWc_meas.comp continuous_fst).measurable).mul
            (hWc_meas.comp continuous_snd).measurable |>.aestronglyMeasurable
      · have hbr : |spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinLongDist q) +
            spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinTransDist q)| ≤
            1 + C_rc / n := by
          have hr1 := spinRc1_nonneg ha2.le (spinLongDist q) ((|q.1| - |q.2|) / 2)
          have hr2 := spinRc2_nonneg ha2.le (spinLongDist q) ((|q.1| - |q.2|) / 2)
          have hrc_ub := (abs_le.mp (hRc_bd hc40 q).2.2).2
          rw [← show spinLongDist q = (|q.1| + |q.2|) / 2 by unfold spinLongDist; ring] at hrc_ub
          change spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) ≤ 1 + C_rc / n at hrc_ub
          calc _ ≤ spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * |φ (spinLongDist q)| +
                spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * |φ (spinTransDist q)| := by
                refine (abs_add_le _ _).trans ?_
                rw [abs_mul, abs_mul, abs_of_nonneg hr1, abs_of_nonneg hr2]
            _ ≤ spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * 1 +
                spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * 1 := by
                gcongr <;> exact hφ_bd _
            _ = spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) := by unfold spinRc; ring
            _ ≤ 1 + C_rc / n := hrc_ub
        have hw1 := spinWc_nonneg ha2.le q.1
        have hw2 := spinWc_nonneg ha2.le q.2
        have hGm1 := hGm_bd q
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hGm_nn q),
          abs_of_nonneg hw1, abs_of_nonneg hw2]
        calc _ ≤ (1 + C_rc / n) * |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by gcongr
          _ = (1 + C_rc / n) * (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by ring
    have hI2 : Integrable (fun q : ℝ × ℝ =>
        φ (spinLongDist q) * Gminus q * spinWc a q.1 * spinWc a q.2) := by
      refine hGm_int.mono' ?_ (Eventually.of_forall fun q => ?_)
      · exact ((((hφ_meas.comp hL_meas).mul hGm_meas).mul
          (hWc_meas.comp continuous_fst).measurable).mul
          (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
      · have h1 := hφ_bd (spinLongDist q)
        have hw1 := spinWc_nonneg ha2.le q.1
        have hw2 := spinWc_nonneg ha2.le q.2
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hGm_nn q),
          abs_of_nonneg hw1, abs_of_nonneg hw2]
        calc |φ (spinLongDist q)| * Gminus q * spinWc a q.1 * spinWc a q.2
            ≤ 1 * Gminus q * spinWc a q.1 * spinWc a q.2 := by gcongr
          _ = Gminus q * spinWc a q.1 * spinWc a q.2 := by ring
    have hsub_eq : (∫ q : ℝ × ℝ,
          (spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinLongDist q) +
           spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinTransDist q)) *
            Gminus q * spinWc a q.1 * spinWc a q.2) -
        (∫ q : ℝ × ℝ, φ (spinLongDist q) * Gminus q * spinWc a q.1 * spinWc a q.2) =
        ∫ q : ℝ × ℝ, diffFn q := by
      rw [← integral_sub hI1 hI2]
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      dsimp [diffFn]; unfold spinRc; ring
    have hdiff_int : Integrable diffFn := by
      have heq : diffFn = fun q =>
          ((spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinLongDist q) +
            spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * φ (spinTransDist q)) *
              Gminus q * spinWc a q.1 * spinWc a q.2) -
          (φ (spinLongDist q) * Gminus q * spinWc a q.1 * spinWc a q.2) := by
        ext q; dsimp [diffFn]; unfold spinRc; ring
      rw [heq]; exact hI1.sub hI2
    rw [hsub_eq]
    let δ := K_2 * δ_n
    let E_far : Set (ℝ × ℝ) := {q | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ spinLongDist q < xiStar - δ}
    let E_near : Set (ℝ × ℝ) := {q | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ xiStar - δ ≤ spinLongDist q}
    have hm_far : MeasurableSet E_far := by
      have h1 : Continuous (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) / 2) := by fun_prop
      have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
      exact (isOpen_lt h1 continuous_const).measurableSet.inter
        (isOpen_lt h2 continuous_const).measurableSet
    have hm_near : MeasurableSet E_near := by
      have h1 : Continuous (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) / 2) := by fun_prop
      have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
      exact (isOpen_lt h1 continuous_const).measurableSet.inter
        (isClosed_le continuous_const h2).measurableSet
    have hGm_supp : ∀ q : ℝ × ℝ, q ∉ E_far ∪ E_near → Gminus q = 0 := by
      intro q hq
      have hge : x₁ ^ 2 ≤ (q.1 ^ 2 + q.2 ^ 2) / 2 := by
        by_contra hlt; push_neg at hlt
        rcases lt_or_ge (spinLongDist q) (xiStar - δ) with hL | hL
        · exact hq (Or.inl ⟨hlt, hL⟩)
        · exact hq (Or.inr ⟨hlt, hL⟩)
      have hnonneg : 0 ≤ spinG a Φ q.1 q.2 := by
        have hxid : x₁ ^ 2 ≤ ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 := by linarith
        have h := hgap ((q.1 + q.2) / 2) ((q.1 - q.2) / 2) hxid
        rwa [show (q.1 + q.2) / 2 + (q.1 - q.2) / 2 = q.1 by ring,
          show (q.1 + q.2) / 2 - (q.1 - q.2) / 2 = q.2 by ring] at h
      dsimp [Gminus]; exact max_eq_right (neg_nonpos.mpr hnonneg)
    have hnorm_le : |∫ q : ℝ × ℝ, diffFn q| ≤ ∫ q : ℝ × ℝ, |diffFn q| := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm diffFn
    have hsplit_abs : ∫ q : ℝ × ℝ, |diffFn q| =
        (∫ q in E_far, |diffFn q|) + ∫ q in E_near, |diffFn q| := by
      have hd : Disjoint E_far E_near := Set.disjoint_left.mpr fun q h1 h2 => not_le_of_gt h1.2 h2.2
      have hfull : ∫ q : ℝ × ℝ, |diffFn q| = ∫ q in E_far ∪ E_near, |diffFn q| := by
        rw [← integral_indicator (hm_far.union hm_near)]
        refine integral_congr_ae (Eventually.of_forall fun q => ?_)
        by_cases hq : q ∈ E_far ∪ E_near
        · simp [Set.indicator_of_mem hq]
        · simp [Set.indicator_of_notMem hq, diffFn, hGm_supp q hq]
      rw [hfull, ← integral_indicator (hm_far.union hm_near), ← integral_indicator hm_far,
        ← integral_indicator hm_near,
        ← integral_add (hdiff_int.abs.indicator hm_far) (hdiff_int.abs.indicator hm_near)]
      congr 1; ext q
      by_cases h1 : q ∈ E_far <;> by_cases h2 : q ∈ E_near
      · exact absurd h2 (Set.disjoint_left.mp hd h1)
      · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1,
          Set.indicator_of_notMem h2, add_zero]
      · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1,
          Set.indicator_of_mem h2, zero_add]
      · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
          Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
    have hrc2_bd : ∀ q : ℝ × ℝ, spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) ≤ C_2_rc / n := by
      intro q
      have hd_le_ξ : |(|q.1| - |q.2|) / 2| ≤ spinLongDist q := by
        unfold spinLongDist
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        rcases le_total |q.1| |q.2| with h | h
        · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith [abs_nonneg q.1]
        · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith [abs_nonneg q.2]
      exact hRc2_bd hc40 (spinLongDist q) ((|q.1| - |q.2|) / 2) hd_le_ξ
    have hpt_abs : ∀ q : ℝ × ℝ, |diffFn q| ≤
        (|spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| + 2 * (C_2_rc / n)) *
          (Gminus q * spinWc a q.1 * spinWc a q.2) := by
      intro q
      have hr2_nn := spinRc2_nonneg ha2.le (spinLongDist q) ((|q.1| - |q.2|) / 2)
      have hrc2_q := hrc2_bd q
      have hφ_diff : |φ (spinTransDist q) - φ (spinLongDist q)| ≤ 2 :=
        (abs_sub_le _ 0 _).trans (by
          rw [sub_zero, zero_sub, abs_neg]
          linarith [hφ_bd (spinTransDist q), hφ_bd (spinLongDist q)])
      have hw1 := spinWc_nonneg ha2.le q.1
      have hw2 := spinWc_nonneg ha2.le q.2
      have hfac_bd : |(spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1) * φ (spinLongDist q) +
          spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) *
            (φ (spinTransDist q) - φ (spinLongDist q))| ≤
          |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| + 2 * (C_2_rc / n) := by
        calc _ ≤ |(spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1) * φ (spinLongDist q)| +
              |spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) *
                (φ (spinTransDist q) - φ (spinLongDist q))| := abs_add_le _ _
          _ = |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| * |φ (spinLongDist q)| +
              spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) *
                |φ (spinTransDist q) - φ (spinLongDist q)| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hr2_nn]
          _ ≤ |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| * 1 + (C_2_rc / n) * 2 := by
              gcongr; exact hφ_bd _
          _ = _ := by ring
      dsimp [diffFn]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hGm_nn q), abs_of_nonneg hw1, abs_of_nonneg hw2]
      calc _ ≤ (|spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| + 2 * (C_2_rc / n)) *
              Gminus q * spinWc a q.1 * spinWc a q.2 := by gcongr
        _ = _ := by ring
    have hfar_bd : ∫ q in E_far, |diffFn q| ≤ 16 * C_2 * n ^ (-2 : ℝ) := by
      have h1 : ∀ q ∈ E_far, |diffFn q| ≤ 4 * (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by
        intro q _
        have hrc_abs := (hRc_bd hc40 q).2.2
        rw [← show spinLongDist q = (|q.1| + |q.2|) / 2 by unfold spinLongDist; ring] at hrc_abs
        have hrc_bd1 : |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| ≤ 3 :=
          (abs_sub_le _ 0 _).trans (by rw [sub_zero, zero_sub, abs_neg]; linarith [hrc_abs, hCrc_n])
        have hGm1 := hGm_bd q
        have hw1 := spinWc_nonneg ha2.le q.1
        have hw2 := spinWc_nonneg ha2.le q.2
        calc |diffFn q|
            ≤ (|spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| + 2 * (C_2_rc / n)) *
                (Gminus q * spinWc a q.1 * spinWc a q.2) := hpt_abs q
          _ ≤ (3 + 1) * (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by
              gcongr
          _ = 4 * (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by ring
      have hint1 := setIntegral_mono_on hdiff_int.abs.integrableOn
        (hG_int.const_mul 4).integrableOn hm_far h1
      rw [integral_const_mul] at hint1
      have h21_bd : ∫ q in E_far, |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤
          4 * C_2 * n ^ (-2 : ℝ) := by
        simpa [E_far, δ, δ_n, a, n, mul_assoc] using h21_all_2 hc02' hx10 hx1_ub' hΦ hM2
      linarith
    have hnear_bd : ∫ q in E_near, |diffFn q| ≤ C_near * δ_n + 2 * (C_2_rc / n) := by
      have h1 : ∀ q ∈ E_near, |diffFn q| ≤
          (C_near * δ_n + 2 * (C_2_rc / n)) * (Gminus q * spinWc a q.1 * spinWc a q.2) := by
        intro q hq
        have hn1 := hnear hc0n' hx10 hx1_ub' q hq.1 hq.2
        have hw1 := spinWc_nonneg ha2.le q.1
        have hw2 := spinWc_nonneg ha2.le q.2
        have hGm0 := hGm_nn q
        calc |diffFn q|
            ≤ (|spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) - 1| + 2 * (C_2_rc / n)) *
                (Gminus q * spinWc a q.1 * spinWc a q.2) := hpt_abs q
          _ ≤ (C_near * δ_n + 2 * (C_2_rc / n)) * (Gminus q * spinWc a q.1 * spinWc a q.2) := by
              gcongr
      have hint1 := setIntegral_mono_on hdiff_int.abs.integrableOn
        (hGm_int.const_mul _).integrableOn hm_near h1
      rw [integral_const_mul] at hint1
      have hsub : ∫ q in E_near, Gminus q * spinWc a q.1 * spinWc a q.2 ≤
          ∫ q : ℝ × ℝ, Gminus q * spinWc a q.1 * spinWc a q.2 :=
        setIntegral_le_integral hGm_int (Eventually.of_forall fun q =>
          mul_nonneg (mul_nonneg (hGm_nn q) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _))
      have hcoef_nn : 0 ≤ C_near * δ_n + 2 * (C_2_rc / n) :=
        add_nonneg (mul_nonneg hCnear_pos.le hδn_nn) (mul_nonneg (by norm_num) (div_nonneg hC2rc_pos.le hn_pos.le))
      exact hint1.trans ((mul_le_mul_of_nonneg_left (hsub.trans hGm_int1) hcoef_nn).trans_eq (mul_one _))
    have h16 : 16 * C_2 * n ^ (-2 : ℝ) ≤ 16 * C_2 * δ_n :=
      mul_le_mul_of_nonneg_left hn2_le (by positivity)
    have h2c : 2 * (C_2_rc / n) ≤ 2 * C_2_rc * δ_n := by
      simpa [div_eq_mul_inv, mul_assoc] using mul_le_mul_of_nonneg_left hinv_le (by positivity : 0 ≤ 2 * C_2_rc)
    have hsum_le : C_near * δ_n + 2 * (C_2_rc / n) + 16 * C_2 * n ^ (-2 : ℝ) ≤ C * δ_n := by
      have hC_ge : 16 * C_2 + C_near + 2 * C_2_rc ≤ C := le_max_right _ _
      have h1 : (16 * C_2 + C_near + 2 * C_2_rc) * δ_n ≤ C * δ_n :=
        mul_le_mul_of_nonneg_right hC_ge hδn_nn
      linarith
    linarith [hnorm_le, hsplit_abs, hfar_bd, hnear_bd]
  have hclause2 : (spinRhoProjMeasure c Gplus (Ici 0)).toReal ≤
      (spinEtaProjMeasure a Gplus (Ici 0)).toReal + C / n := by
    rw [spinRhoProjMeasure_toReal hc40 hΦ hGp_meas hGp_nn hGp_bd hGp_nl hGp_nr measurableSet_Ici,
      spinEtaProjMeasure_toReal ha2 hΦ hGp_meas hGp_nn hGp_bd measurableSet_Ici]
    have hI_lhs : (fun q : ℝ × ℝ =>
        (spinRc1 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * (Ici (0 : ℝ)).indicator 1 (spinLongDist q) +
         spinRc2 a (spinLongDist q) ((|q.1| - |q.2|) / 2) * (Ici (0 : ℝ)).indicator 1 (spinTransDist q)) *
          Gplus q * spinWc a q.1 * spinWc a q.2) =
        fun q : ℝ × ℝ => spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) *
          Gplus q * spinWc a q.1 * spinWc a q.2 := by
      ext q
      have hL0 : 0 ≤ spinLongDist q := by unfold spinLongDist; positivity
      have hT0 : 0 ≤ spinTransDist q := by unfold spinTransDist; positivity
      simp only [Set.indicator_of_mem (mem_Ici.mpr hL0), Set.indicator_of_mem (mem_Ici.mpr hT0),
        Pi.one_apply, mul_one]
      unfold spinRc; rfl
    have hI_rhs : (fun q : ℝ × ℝ =>
        (Ici (0 : ℝ)).indicator 1 (spinLongDist q) * Gplus q * spinWc a q.1 * spinWc a q.2) =
        fun q : ℝ × ℝ => Gplus q * spinWc a q.1 * spinWc a q.2 := by
      ext q
      have hL0 : 0 ≤ spinLongDist q := by unfold spinLongDist; positivity
      simp [Set.indicator_of_mem (mem_Ici.mpr hL0)]
    rw [hI_lhs, hI_rhs]
    have hRc_p_int : Integrable (fun q : ℝ × ℝ =>
        spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) *
          Gplus q * spinWc a q.1 * spinWc a q.2) := by
      refine (hG_int.const_mul (1 + C_rc / n)).mono' ?_ (Eventually.of_forall fun q => ?_)
      · exact ((((measurable_spinRc1 a).add (measurable_spinRc2 a)).mul hGp_meas |>.mul
          (hWc_meas.comp continuous_fst).measurable).mul
          (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
      · have hbd := (hRc_bd hc40 q).2.2
        rw [← show spinLongDist q = (|q.1| + |q.2|) / 2 by unfold spinLongDist; ring] at hbd
        change |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2)| ≤ 1 + C_rc / n at hbd
        have hw1 := spinWc_nonneg ha2.le q.1
        have hw2 := spinWc_nonneg ha2.le q.2
        have hGp1 := hGp_bd q
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (hGp_nn q),
          abs_of_nonneg hw1, abs_of_nonneg hw2]
        have h1 : |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2)| ≤ 1 + C_rc / n := hbd
        calc |spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2)| * Gplus q * spinWc a q.1 * spinWc a q.2
            ≤ (1 + C_rc / n) * |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by gcongr
          _ = (1 + C_rc / n) * (|spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) := by ring
    have hpt : ∀ q : ℝ × ℝ,
        spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) * Gplus q * spinWc a q.1 * spinWc a q.2 ≤
        (1 + C_rc / n) * (Gplus q * spinWc a q.1 * spinWc a q.2) := by
      intro q
      have hbd := (abs_le.mp (hRc_bd hc40 q).2.2).2
      rw [← show spinLongDist q = (|q.1| + |q.2|) / 2 by unfold spinLongDist; ring] at hbd
      change spinRc a (spinLongDist q) ((|q.1| - |q.2|) / 2) ≤ 1 + C_rc / n at hbd
      have hGp0 := hGp_nn q
      have hw1 := spinWc_nonneg ha2.le q.1
      have hw2 := spinWc_nonneg ha2.le q.2
      calc _ ≤ (1 + C_rc / n) * Gplus q * spinWc a q.1 * spinWc a q.2 := by gcongr
        _ = (1 + C_rc / n) * (Gplus q * spinWc a q.1 * spinWc a q.2) := by ring
    have hint := integral_mono hRc_p_int (hGp_int.const_mul (1 + C_rc / n)) hpt
    rw [integral_const_mul] at hint
    have hC_rc_le : C_rc / n ≤ C / n := div_le_div_of_nonneg_right (le_max_left _ _) hn_pos.le
    have hI0 : 0 ≤ ∫ q : ℝ × ℝ, Gplus q * spinWc a q.1 * spinWc a q.2 :=
      integral_nonneg fun q => mul_nonneg (mul_nonneg (hGp_nn q) (spinWc_nonneg ha2.le _))
        (spinWc_nonneg ha2.le _)
    have h1C : (1 + C_rc / n) * ∫ q : ℝ × ℝ, Gplus q * spinWc a q.1 * spinWc a q.2 ≤
        (∫ q : ℝ × ℝ, Gplus q * spinWc a q.1 * spinWc a q.2) + C_rc / n := by
      nlinarith [div_nonneg hCrc_pos.le hn_pos.le]
    linarith
  have hclause3 : (spinEtaProjMeasure a Gminus (Ici 0)).toReal - C * δ_n ≤
      (spinRhoProjMeasure c Gminus (Ici 0)).toReal := by
    have h1 := (abs_le.mp (hclause1 (Ici 0) measurableSet_Ici)).1
    linarith
  have hclause4 : (spinRhoProjMeasure c Gminus (Icc 0 (xiStar - r₀))).toReal ≤
      C * δ_n + C_p * n ^ (-p) := by
    have h1 := (abs_le.mp (hclause1 (Icc 0 (xiStar - r₀)) measurableSet_Icc)).2
    have h2 : (spinEtaProjMeasure a Gminus (Icc 0 (xiStar - r₀))).toReal ≤ C_p * n ^ (-p) := by
      rw [spinEtaProjMeasure_toReal ha2 hΦ hGm_meas hGm_nn hGm_bd measurableSet_Icc]
      let E_p : Set (ℝ × ℝ) := {q | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧
        spinLongDist q < xiStar - K_p * δ_n}
      have hmEp : MeasurableSet E_p := by
        have h1 : Continuous (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) / 2) := by fun_prop
        have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
        exact (isOpen_lt h1 continuous_const).measurableSet.inter
          (isOpen_lt h2 continuous_const).measurableSet
      let fn : ℝ × ℝ → ℝ := fun q =>
        (Icc 0 (xiStar - r₀)).indicator (1 : ℝ → ℝ) (spinLongDist q) * Gminus q * spinWc a q.1 * spinWc a q.2
      have hfn_int : Integrable fn := by
        refine hGm_int.mono' ?_ (Eventually.of_forall fun q => ?_)
        · have hL_meas : Measurable spinLongDist :=
            measurable_const.mul ((measurable_fst.abs).add (measurable_snd.abs))
          exact ((((measurable_one.indicator measurableSet_Icc).comp hL_meas).mul hGm_meas |>.mul
            (hWc_meas.comp continuous_fst).measurable).mul
            (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
        · have hind1 : |(Icc 0 (xiStar - r₀)).indicator (1 : ℝ → ℝ) (spinLongDist q)| ≤ 1 := by
            by_cases hq : spinLongDist q ∈ Icc 0 (xiStar - r₀) <;> simp [hq]
          have hGm0 := hGm_nn q
          have hw1 := spinWc_nonneg ha2.le q.1
          have hw2 := spinWc_nonneg ha2.le q.2
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
            abs_of_nonneg hGm0, abs_of_nonneg hw1, abs_of_nonneg hw2]
          calc |(Icc 0 (xiStar - r₀)).indicator (1 : ℝ → ℝ) (spinLongDist q)| * Gminus q * spinWc a q.1 * spinWc a q.2
              ≤ 1 * Gminus q * spinWc a q.1 * spinWc a q.2 := by gcongr
            _ = Gminus q * spinWc a q.1 * spinWc a q.2 := by ring
      have hfn_supp : ∫ q : ℝ × ℝ, fn q = ∫ q in E_p, fn q := by
        rw [← integral_indicator hmEp]
        refine integral_congr_ae (Eventually.of_forall fun q => ?_)
        by_cases hq : q ∈ E_p
        · simp [Set.indicator_of_mem hq]
        · rw [Set.indicator_of_notMem hq]
          by_cases hIcc : spinLongDist q ∈ Icc 0 (xiStar - r₀)
          · have hlt : spinLongDist q < xiStar - K_p * δ_n := by linarith [hIcc.2, hKp_r0]
            have hge : x₁ ^ 2 ≤ (q.1 ^ 2 + q.2 ^ 2) / 2 := by
              by_contra hlt2; push Not at hlt2; exact hq ⟨hlt2, hlt⟩
            have hnonneg : 0 ≤ spinG a Φ q.1 q.2 := by
              have hxid : x₁ ^ 2 ≤ ((q.1 + q.2) / 2) ^ 2 + ((q.1 - q.2) / 2) ^ 2 := by linarith
              have h := hgap ((q.1 + q.2) / 2) ((q.1 - q.2) / 2) hxid
              rwa [show (q.1 + q.2) / 2 + (q.1 - q.2) / 2 = q.1 by ring,
                show (q.1 + q.2) / 2 - (q.1 - q.2) / 2 = q.2 by ring] at h
            have hGm0 : Gminus q = 0 := max_eq_right (neg_nonpos.mpr hnonneg)
            dsimp [fn]; rw [hGm0, mul_zero, zero_mul, zero_mul]
          · dsimp [fn]; simp [Set.indicator_of_notMem hIcc]
      have hpt : ∀ q ∈ E_p, fn q ≤ |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by
        intro q _
        have hind0 : 0 ≤ (Icc 0 (xiStar - r₀)).indicator (1 : ℝ → ℝ) (spinLongDist q) := by
          by_cases hq : spinLongDist q ∈ Icc 0 (xiStar - r₀) <;> simp [hq]
        have hind1 : (Icc 0 (xiStar - r₀)).indicator (1 : ℝ → ℝ) (spinLongDist q) ≤ 1 := by
          by_cases hq : spinLongDist q ∈ Icc 0 (xiStar - r₀) <;> simp [hq]
        have hGm0 := hGm_nn q
        have hGm1 := hGm_bd q
        have hw1 := spinWc_nonneg ha2.le q.1
        have hw2 := spinWc_nonneg ha2.le q.2
        calc fn q
            ≤ 1 * |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by
              dsimp [fn]; gcongr
          _ = |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 := by ring
      rw [hfn_supp]
      have hint := setIntegral_mono_on hfn_int.integrableOn hG_int.integrableOn hmEp hpt
      have h21_bd := h21_all_p hc0p' hx10 hx1_ub' hΦ hM2
      exact hint.trans (by simpa [C_p, E_p, δ_n, a, n, mul_assoc] using h21_bd)
    linarith
  exact ⟨hclause1, hclause2, hclause3, hclause4⟩

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_2_4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_2_4

end FormalResearch.ModularBootstrap.Spin

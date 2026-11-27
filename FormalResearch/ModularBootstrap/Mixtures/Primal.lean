module

public import FormalResearch.ModularBootstrap.Mixtures.ThermalSeparation
public import FormalResearch.ModularBootstrap.Duality.Primal.FixedCharge
public import FormalResearch.ModularBootstrap.Duality.Primal.StripLimit
public import FormalResearch.ModularBootstrap.Duality.Primal.PositiveThreshold
public import FormalResearch.ModularBootstrap.Duality.Primal.Attainment

/-!
# Primal attainment and `ds:primal` for `CommonSource`

Source: `CFT/modular_bootstrap/paper/dual_spectrum.tex` and `dual_spectrum_limit.tex`, Theorem E'
(`ds:primal`, parts (a)–(d)) and `dsl:strip-fixed`, transferred from `C.F.prob : FixedWeightProblem`
via the floor `C.F.d * V_{Q_0} ≤ V_λ` (`FloorData.At.floor`).

* `FixedChargeStripS`, `fixedChargeStripS_of_common`: `dsl:strip-fixed` for every `CommonSource`
  at large charge `c̃ ≥ c₀`.
* `T_V_pos_of_common`: `0 < C.src.T_V c̃` for large charge.
* `theorem_primal_src`: full `ds:primal` (a)–(d) for `CommonSource`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Mixtures

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.FixedWeight
open FormalResearch.ModularBootstrap.WeightAxioms

/-! ### `dsl:strip-fixed` for `CommonSource` -/

/-- Analytic strip and tail input (`dsl:strip-fixed`) for a `ShiftSource`. -/
structure FixedChargeStripS (src : ShiftSource) (cTilde : ℝ) : Prop where
  hc_pos : 0 < cTilde
  bound : ∃ C : ℝ, ∀ g : ℝ → ℝ, TestClass src (cTilde / 12) g → ∀ b : ℂ, |b.im| ≤ 1 / 2 →
    ‖hankelContinuationW src.w cTilde g b‖ ≤ C * src.cardyNorm (cTilde / 12) g
  cont : ∀ g : ℝ → ℝ, TestClass src (cTilde / 12) g →
    ContinuousOn (hankelContinuationW src.w cTilde g) {b : ℂ | |b.im| ≤ 1 / 2}
  diff : ∀ g : ℝ → ℝ, TestClass src (cTilde / 12) g →
    DifferentiableOn ℂ (hankelContinuationW src.w cTilde g) {b : ℂ | |b.im| < 1 / 2}
  tail : ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (src.w - 1) ≤ ε * src.cardyV (cTilde / 12) t

/-- Under a floor `Fl.At a`, any source test lies in the floor problem's test class, with
`Fl.d * Fl.prob.cardyNorm ≤ src.cardyNorm`. -/
lemma testClass_toProb {src : ShiftSource} {Fl : FloorData src} {a : ℝ} (hAt : Fl.At a)
    {g : ℝ → ℝ} (hg : TestClass src a g) :
    Crossing.TestClass Fl.prob a g ∧
      Fl.d * Fl.prob.cardyNorm a g ≤ src.cardyNorm a g := by
  have hint : IntegrableOn (fun t => |g t| * Fl.prob.cardyV a t) (Ioi 0) := by
    have hm : AEStronglyMeasurable (fun t => |g t| * Fl.prob.cardyV a t)
        (volume.restrict (Ioi 0)) :=
      ((hg.cont.abs.mono Ioi_subset_Ici_self).mul
        (continuous_cardyV Fl.prob a).continuousOn).aestronglyMeasurable measurableSet_Ioi
    refine (hg.int_cardy.const_mul Fl.d⁻¹).mono' hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hK0 : 0 ≤ Fl.prob.cardyV a t := Fl.prob.cardyV_nonneg hAt.prob_shift ht0
    have hfl := hAt.floor t ht
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hK0]
    have hd_pos : 0 < Fl.d := Fl.hd
    calc |g t| * Fl.prob.cardyV a t
        = Fl.d⁻¹ * (|g t| * (Fl.d * Fl.prob.cardyV a t)) := by field_simp [hd_pos.ne']
      _ ≤ Fl.d⁻¹ * (|g t| * src.cardyV a t) := by gcongr
  refine ⟨⟨hg.cont, hg.int_lift, hg.fourier_odd, hint⟩, ?_⟩
  unfold FixedWeightProblem.cardyNorm ShiftSource.cardyNorm
  have heq : Fl.d * ∫ t in Ioi (0 : ℝ), |g t| * Fl.prob.cardyV a t =
      ∫ t in Ioi (0 : ℝ), |g t| * (Fl.d * Fl.prob.cardyV a t) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
  rw [heq]
  have hint_l : IntegrableOn (fun t => |g t| * (Fl.d * Fl.prob.cardyV a t)) (Ioi 0) :=
    (hint.const_mul Fl.d).congr (Eventually.of_forall fun t => by ring)
  refine setIntegral_mono_on hint_l hg.int_cardy measurableSet_Ioi fun t ht => ?_
  exact mul_le_mul_of_nonneg_left (hAt.floor t ht) (abs_nonneg _)

/-- **`dsl:strip-fixed` for any `CommonSource`** at sufficiently large charge `c̃ ≥ c₀`. -/
theorem fixedChargeStripS_of_common (C : CommonSource) :
    ∃ c₀ : ℝ, 12 * C.a₀ ≤ c₀ ∧ ∀ {cTilde : ℝ}, c₀ ≤ cTilde → FixedChargeStripS C.src cTilde := by
  obtain ⟨c₁, hc₁⟩ := fixedChargeStrip_of_large C.F.prob
  refine ⟨max (12 * C.a₀) c₁, le_max_left _ _, fun {cTilde} hc => ?_⟩
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith [(le_max_left (12 * C.a₀) c₁).trans hc])
  have S := hc₁ ((le_max_right _ _).trans hc)
  obtain ⟨K, hK⟩ := S.bound
  refine ⟨S.hc_pos, ⟨max K 0 / C.F.d, fun g hg b hb => ?_⟩,
    fun g hg => S.cont g (testClass_toProb hAt hg).1,
    fun g hg => S.diff g (testClass_toProb hAt hg).1,
    fun ε hε => ?_⟩
  · obtain ⟨hg_prob, hnorm⟩ := testClass_toProb hAt hg
    have hM_prob_nn : 0 ≤ C.F.prob.cardyNorm (cTilde / 12) g := by
      unfold FixedWeightProblem.cardyNorm
      exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (abs_nonneg _) (C.F.prob.cardyV_nonneg hAt.prob_shift ht.le)
    have hd_pos : 0 < C.F.d := C.F.hd
    have hM_le : C.F.prob.cardyNorm (cTilde / 12) g ≤
        C.src.cardyNorm (cTilde / 12) g / C.F.d :=
      (le_div_iff₀ hd_pos).mpr (by linarith [mul_comm C.F.d (C.F.prob.cardyNorm (cTilde / 12) g)])
    calc ‖hankelContinuationW C.src.w cTilde g b‖
        = ‖hankelContinuationW C.F.prob.w cTilde g b‖ := rfl
      _ ≤ K * C.F.prob.cardyNorm (cTilde / 12) g := hK g hg_prob b hb
      _ ≤ max K 0 * C.F.prob.cardyNorm (cTilde / 12) g :=
          mul_le_mul_of_nonneg_right (le_max_left K 0) hM_prob_nn
      _ ≤ max K 0 * (C.src.cardyNorm (cTilde / 12) g / C.F.d) :=
          mul_le_mul_of_nonneg_left hM_le (le_max_right K 0)
      _ = max K 0 / C.F.d * C.src.cardyNorm (cTilde / 12) g := by ring
  · obtain ⟨R, hR⟩ := S.tail (ε * C.F.d) (mul_pos hε C.F.hd)
    refine ⟨max R 1, fun t ht => ?_⟩
    have htR : R ≤ t := (le_max_left _ _).trans ht
    have htp : 0 < t := lt_of_lt_of_le one_pos ((le_max_right _ _).trans ht)
    calc t ^ (C.src.w - 1) ≤ (ε * C.F.d) * C.F.prob.cardyV (cTilde / 12) t := hR t htR
      _ = ε * (C.F.d * C.F.prob.cardyV (cTilde / 12) t) := by ring
      _ ≤ ε * C.src.cardyV (cTilde / 12) t :=
          mul_le_mul_of_nonneg_left (hAt.floor t htp) hε.le

/-! ### Montel compactness and `ds:primal` for `CommonSource` -/

lemma cardyNorm_smul_of_nonneg_src (src : ShiftSource) {a c : ℝ} (hc : 0 ≤ c) (g : ℝ → ℝ) :
    src.cardyNorm a (fun t => c * g t) = c * src.cardyNorm a g := by
  unfold ShiftSource.cardyNorm
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [abs_mul, abs_of_nonneg hc]; ring

lemma cardyNorm_pos_of_vac_pos_src {src : ShiftSource} {Fl : FloorData src} {a : ℝ}
    (hAt : Fl.At a) {g : ℝ → ℝ} (hg : TestClass src a g) (hvac : 0 < src.gVac a g) :
    0 < src.cardyNorm a g := by
  by_contra h0
  have hle : src.cardyNorm a g ≤ 0 := not_lt.1 h0
  have hnn_ae : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun t => |g t| * src.cardyV a t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (abs_nonneg _) (hAt.nonneg_V (mem_Ioi.1 ht).le)
  have hzero : ∫ t in Ioi (0 : ℝ), |g t| * src.cardyV a t = 0 :=
    le_antisymm hle (integral_nonneg_of_ae hnn_ae)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn_ae hg.int_cardy).1 hzero
  have hae2 : (fun t => g t * src.cardyV a t) =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [hae] with t ht
    dsimp only [Pi.zero_apply] at ht ⊢
    rcases mul_eq_zero.1 ht with hgt | hVt
    · rw [abs_eq_zero.1 hgt, zero_mul]
    · rw [hVt, mul_zero]
  have hv0 : src.gVac a g = 0 := by
    unfold ShiftSource.gVac
    rw [integral_congr_ae hae2]; simp
  linarith

/-- Montel compactness step on `|Im b| < 1/2` for a normalised `TestClass C.src` sequence. -/
theorem exists_montel_limit_src (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    (S : FixedChargeStripS C.src cTilde) {g : ℕ → ℝ → ℝ}
    (hg : ∀ j, TestClass C.src (cTilde / 12) (g j))
    (hM : ∀ j, C.src.cardyNorm (cTilde / 12) (g j) = 1) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
      TendstoLocallyUniformlyOn (fun k => hankelContinuationW C.src.w cTilde (g (φ k))) G atTop
        openStrip := by
  have _ := hc
  obtain ⟨K, hK⟩ := S.bound
  refine FormalResearch.Montel.montel isOpen_openStrip (fun j => S.diff _ (hg j)) ?_
  intro Kc hKc _
  refine ⟨K, fun j z hz => ?_⟩
  have := hK (g j) (hg j) z (le_of_lt (hKc hz))
  rwa [hM j, mul_one] at this

/-- **Montel limit of a normalised sequence** (`ds:primal`, proof of (a)) for `CommonSource`. -/
theorem exists_primal_limit_src (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    (S : FixedChargeStripS C.src cTilde) {g : ℕ → ℝ → ℝ}
    (hg : ∀ j, TestClass C.src (cTilde / 12) (g j))
    (hM : ∀ j, C.src.cardyNorm (cTilde / 12) (g j) = 1)
    (hv : ∀ j, ∫ t in Ioi (0 : ℝ), g j t * C.src.cardyV (cTilde / 12) t ≤ 0) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) (hneg : ∀ j, ∀ t ≥ R₀, 0 ≤ g j t) :
    ∃ (φ : ℕ → ℕ) (gs : ℝ → ℝ), StrictMono φ ∧ TestClass C.src (cTilde / 12) gs ∧
      (∀ t ≥ R₀, 0 ≤ gs t) ∧
      (∀ R : ℝ, TendstoUniformlyOn (fun k => g (φ k)) gs atTop (Icc 0 R)) ∧
      C.src.cardyNorm (cTilde / 12) gs ≤ 1 ∧ 0 ≤ C.src.gVac (cTilde / 12) gs ∧
      (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧ (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧
      (∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
        ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (gs t : ℂ)) ∧
      (C.src.gVac (cTilde / 12) gs ≤ 0 → C.src.cardyNorm (cTilde / 12) gs = 1 ∧
        Tendsto (fun k => ∫ t in Ioi (0 : ℝ), |g (φ k) t - gs t| * C.src.cardyV (cTilde / 12) t)
          atTop (𝓝 0)) := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  set a : ℝ := cTilde / 12 with ha_def
  set Vt : ℝ → ℝ := fun t => C.src.cardyV a (max t 0) with hVt
  have hVt_cont : Continuous Vt :=
    (C.src.continuous_cardyV a).comp (continuous_id.max continuous_const)
  have hVt0 : ∀ t, 0 ≤ Vt t := fun t => hAt.nonneg_V (le_max_right _ _)
  have hVt_eq : ∀ t, 0 ≤ t → Vt t = C.src.cardyV a t := fun t ht => by simp [hVt, max_eq_left ht]
  have hcongr : ∀ F : ℝ → ℝ, ∫ t in Ioi (0 : ℝ), F t * Vt t = ∫ t in Ioi (0 : ℝ), F t * C.src.cardyV a t :=
    fun F => setIntegral_congr_fun measurableSet_Ioi fun t ht => by rw [hVt_eq t (le_of_lt ht)]
  have hcongrI : ∀ F : ℝ → ℝ, IntegrableOn (fun t => F t * Vt t) (Ioi 0) ↔
      IntegrableOn (fun t => F t * C.src.cardyV a t) (Ioi 0) := fun F =>
    integrableOn_congr_fun (fun t ht => by rw [hVt_eq t (le_of_lt ht)]) measurableSet_Ioi
  have hVt_tail : ∀ ε > 0, ∃ R : ℝ, ∀ t ≥ R, t ^ (C.src.w - 1) ≤ ε * Vt t := fun ε hε => by
    obtain ⟨R, hR⟩ := S.tail ε hε
    refine ⟨max R 0, fun t ht => ?_⟩
    rw [hVt_eq t ((le_max_right _ _).trans ht)]
    exact hR t ((le_max_left _ _).trans ht)
  obtain ⟨φ, hφ, G, hGd, hTLU⟩ := exists_montel_limit_src C hc S hg hM
  obtain ⟨hunifR, hreal⟩ :=
    limit_converges (prob := C.F.prob) S.hc_pos (fun j => (testClass_toProb hAt (hg j)).1) hTLU
  set gs : ℝ → ℝ := limitFn cTilde G with hgs
  have hgs_cont : Continuous gs := continuous_limitFn hGd cTilde
  have hgint : ∀ k, IntegrableOn (fun t => |g (φ k) t| * Vt t) (Ioi 0) := fun k =>
    (hcongrI _).2 (hg (φ k)).int_cardy
  have hgM : ∀ k, ∫ t in Ioi (0 : ℝ), |g (φ k) t| * Vt t = 1 := fun k => by
    rw [hcongr]; exact hM (φ k)
  have hgv : ∀ k, ∫ t in Ioi (0 : ℝ), g (φ k) t * Vt t ≤ 0 := fun k => by
    rw [hcongr]; exact hv (φ k)
  obtain ⟨hsint, hsM, hsv, ⟨t₀, ht₀, hgt₀⟩, hrest⟩ := limit_mass (V := Vt) hVt_cont hVt0
    (g := fun k => g (φ k)) (gs := gs) (R₀ := R₀) (fun k => (hg (φ k)).cont)
    hgs_cont.continuousOn hgint hgM hgv (fun k t ht => hneg (φ k) t ht) hunifR
  obtain ⟨hI, hlim⟩ := l1_tail_limit hVt_cont hVt0 C.src.hw hVt_tail (g := fun k => g (φ k))
    (gs := gs) (fun k => (hg (φ k)).cont) hgs_cont.continuousOn hgint (fun k => (hgM k).le)
    hsint hsM hunifR
  have hpt : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k => g (φ k) t) atTop (𝓝 (gs t)) := fun t ht =>
    (hunifR t).tendsto_at ⟨ht, le_rfl⟩
  have hGi : Integrable (radialLift C.src.w gs) := (integrable_radialLift_iff C.src.hw gs).2 hI
  have htc : TestClass C.src a gs :=
    { cont := hgs_cont.continuousOn
      int_lift := hGi
      fourier_odd := radialLift_fourier_odd_of_limit C.src.hw (fun k => (hg (φ k)).int_lift)
        (fun k => (hg (φ k)).fourier_odd) hGi hlim hpt
      int_cardy := (hcongrI _).1 hsint }
  have hgvac : C.src.gVac a gs = -2 * π * ∫ t in Ioi (0 : ℝ), gs t * C.src.cardyV a t := rfl
  have hMgs : C.src.cardyNorm a gs = ∫ t in Ioi (0 : ℝ), |gs t| * C.src.cardyV a t := rfl
  refine ⟨φ, gs, hφ, htc,
    fun t ht => ge_of_tendsto (hpt t (hR₀.trans ht)) (Eventually.of_forall fun k => hneg (φ k) t ht),
    hunifR, ?_, ?_, ⟨t₀, ht₀, hgt₀⟩, ?_, ⟨G, hGd, hreal⟩, ?_⟩
  · rw [hMgs, ← hcongr]; exact hsM
  · rw [hgvac, ← hcongr]; nlinarith [Real.pi_pos]
  · exact limitFn_zeros_finite S.hc_pos hGd hreal ⟨t₀, ht₀, hgt₀⟩
  · intro hle
    have h0 : 0 ≤ ∫ t in Ioi (0 : ℝ), gs t * Vt t := by
      rw [hcongr]; rw [hgvac] at hle; nlinarith [Real.pi_pos]
    obtain ⟨h1, h2⟩ := hrest h0
    refine ⟨by rw [hMgs, ← hcongr]; exact h1, ?_⟩
    refine h2.congr fun k => ?_
    exact hcongr (fun t => |g (φ k) t - gs t|)

/-- **Positivity of the primal threshold** (`0 < T_V(c̃)`) for `CommonSource` at large charge. -/
theorem T_V_pos_of_common (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    (S : FixedChargeStripS C.src cTilde) :
    0 < C.src.T_V cTilde := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_common C hc one_pos
  obtain ⟨hTV_nn, -, -, -⟩ := T_V_lt_top_of_core S₀
  by_contra hle0
  have hTV0 : C.src.T_V cTilde = 0 := le_antisymm (not_lt.1 hle0) hTV_nn
  have hne : {T : ℝ | 0 < T ∧ ∃ g, C.src.IsFeasible (cTilde / 12) T g}.Nonempty := by
    obtain ⟨-, T, hT, ⟨g, hg⟩, -⟩ := T_V_lt_top_of_core S₀
    exact ⟨T, hT, g, hg⟩
  have hmem : ∀ n : ℕ, ∃ τ : ℝ, 0 < τ ∧ τ < 1 / ((n : ℝ) + 1) ∧
      ∃ g, C.src.IsFeasible (cTilde / 12) τ g := fun n => by
    have hlt : C.src.T_V cTilde < 1 / ((n : ℝ) + 1) := by rw [hTV0]; positivity
    obtain ⟨τ, hτmem, hτlt⟩ := exists_lt_of_csInf_lt hne hlt
    exact ⟨τ, hτmem.1, hτlt, hτmem.2⟩
  choose τ hτpos hτlt g0 hg0 using hmem
  let g : ℕ → ℝ → ℝ := fun n t => (C.src.cardyNorm (cTilde / 12) (g0 n))⁻¹ * g0 n t
  have htc : ∀ n, TestClass C.src (cTilde / 12) (g n) := fun n =>
    testClass_smul_src _ (hg0 n).1
  have hM1 : ∀ n, C.src.cardyNorm (cTilde / 12) (g n) = 1 := fun n => by
    have hMp := cardyNorm_pos_of_vac_pos_src hAt (hg0 n).1 (hg0 n).2.1
    rw [cardyNorm_smul_of_nonneg_src _ (inv_nonneg.2 hMp.le), inv_mul_cancel₀ hMp.ne']
  have hv : ∀ n, ∫ t in Ioi (0 : ℝ), g n t * C.src.cardyV (cTilde / 12) t ≤ 0 := fun n => by
    have hMp := cardyNorm_pos_of_vac_pos_src hAt (hg0 n).1 (hg0 n).2.1
    have hvac_p : 0 < C.src.gVac (cTilde / 12) (g n) := by
      dsimp [g]; rw [gVac_smul_src]; exact mul_pos (inv_pos.2 hMp) (hg0 n).2.1
    change -2 * π * ∫ t in Ioi (0 : ℝ), g n t * C.src.cardyV (cTilde / 12) t > 0 at hvac_p
    nlinarith [Real.pi_pos]
  have hneg1 : ∀ n, ∀ t ≥ (1 : ℝ), 0 ≤ g n t := fun n t ht => by
    have hMp := cardyNorm_pos_of_vac_pos_src hAt (hg0 n).1 (hg0 n).2.1
    have hle1 : τ n ≤ t := by
      have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
      linarith [hτlt n]
    exact mul_nonneg (inv_nonneg.2 hMp.le) ((hg0 n).2.2 t hle1)
  obtain ⟨φ, gs, hφ, hgstc, -, hunif, -, hgs_vac, ⟨t₀, ht₀, hgt₀⟩, -, -, -⟩ :=
    exists_primal_limit_src C hc S htc hM1 hv zero_le_one hneg1
  have hgs_nn : ∀ t : ℝ, 0 < t → 0 ≤ gs t := fun t ht => by
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt ht
    have hpt : Tendsto (fun k => g (φ k) t) atTop (𝓝 (gs t)) :=
      (hunif t).tendsto_at ⟨ht.le, le_rfl⟩
    refine ge_of_tendsto hpt (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
    have hkN : (N : ℝ) + 1 ≤ (φ k : ℝ) + 1 := by
      have : N ≤ φ k := hk.trans (hφ.id_le k)
      exact_mod_cast Nat.add_le_add_right this 1
    have hτ_le : τ (φ k) ≤ t := by
      have h1 : 1 / ((φ k : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) hkN
      linarith [hτlt (φ k), h1, hN]
    have hMp := cardyNorm_pos_of_vac_pos_src hAt (hg0 (φ k)).1 (hg0 (φ k)).2.1
    exact mul_nonneg (inv_nonneg.2 hMp.le) ((hg0 (φ k)).2.2 t hτ_le)
  have hint_pos : 0 < ∫ t in Ioi (0 : ℝ), gs t * C.src.cardyV (cTilde / 12) t := by
    have hcont_f : ContinuousOn (fun t => gs t * C.src.cardyV (cTilde / 12) t) (Ioi 0) :=
      (hgstc.cont.mono Ioi_subset_Ici_self).mul (C.src.continuous_cardyV (cTilde / 12)).continuousOn
    have hnonneg_f : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ gs t * C.src.cardyV (cTilde / 12) t := fun t ht =>
      mul_nonneg (hgs_nn t ht) (hAt.nonneg_V (le_of_lt ht))
    -- By continuity at `t₀` (or near `t₀ + δ > 0`), `gs t > 0` on some interval inside `Ioi 0`
    have hpos_pt : ∃ t₁ : ℝ, 0 < t₁ ∧ gs t₁ ≠ 0 := by
      rcases ht₀.eq_or_lt with rfl | hpos
      · have hcont0 : ContinuousWithinAt gs (Ici 0) 0 := hgstc.cont 0 (le_rfl : (0 : ℝ) ∈ Ici 0)
        obtain ⟨δ, hδ, hmem⟩ := Metric.continuousWithinAt_iff.1 hcont0 (|gs 0| / 2)
          (half_pos (abs_pos.2 hgt₀))
        refine ⟨δ / 2, half_pos hδ, fun hz => ?_⟩
        have h1 := hmem (x := δ / 2) (mem_Ici.mpr (half_pos hδ).le) (by
          rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]; linarith)
        simp only [hz, Real.dist_eq, zero_sub, abs_neg] at h1
        have hpos_abs : 0 < |gs 0| := abs_pos.2 hgt₀
        linarith
      · exact ⟨t₀, hpos, hgt₀⟩
    obtain ⟨t₁, ht₁, hgs1⟩ := hpos_pt
    have hgs1_pos : 0 < gs t₁ := lt_of_le_of_ne (hgs_nn t₁ ht₁) hgs1.symm
    have hV1_pos : 0 < C.src.cardyV (cTilde / 12) t₁ := hAt.pos_V ht₁
    have hgV_hint : IntegrableOn (fun t => gs t * C.src.cardyV (cTilde / 12) t) (Ioi 0) := by
      refine hgstc.int_cardy.mono' (hcont_f.aestronglyMeasurable measurableSet_Ioi) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hAt.nonneg_V ht.le)]
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnonneg_f)) hgV_hint]
    have hcont_at : ContinuousAt (fun t => gs t * C.src.cardyV (cTilde / 12) t) t₁ :=
      (hgstc.cont.continuousAt (Ici_mem_nhds ht₁)).mul
        (C.src.continuous_cardyV (cTilde / 12)).continuousAt
    have hev : ∀ᶠ t in 𝓝 t₁, 0 < gs t * C.src.cardyV (cTilde / 12) t :=
      hcont_at.eventually (Ioi_mem_nhds (mul_pos hgs1_pos hV1_pos))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hev.and (Ioi_mem_nhds ht₁))
    have hIoo_sub : Ioo (t₁ - ε) (t₁ + ε) ⊆
        Function.support (fun t => gs t * C.src.cardyV (cTilde / 12) t) ∩ Ioi 0 := fun t ht => by
      have hd : dist t t₁ < ε := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2]
      exact ⟨(hball hd).1.ne', (hball hd).2⟩
    have hpos_v : 0 < volume (Ioo (t₁ - ε) (t₁ + ε)) := by
      rw [Real.volume_Ioo]; simp; linarith
    exact lt_of_lt_of_le hpos_v (measure_mono hIoo_sub)
  have hv_neg : C.src.gVac (cTilde / 12) gs < 0 := by
    unfold ShiftSource.gVac
    nlinarith [Real.pi_pos]
  linarith

/-- Normalised strictly feasible minimising sequence for `constrainedThresholdS`. -/
lemma exists_normalised_sequence_src (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    {F : Set ℝ} (hne : (constrainedGapsS C.src cTilde F).Nonempty) :
    ∃ (τ : ℕ → ℝ) (g : ℕ → ℝ → ℝ),
      (∀ k, C.src.IsFeasibleOn (cTilde / 12) (F ∪ Ici (τ k)) (g k)) ∧
      Tendsto τ atTop (𝓝 (constrainedThresholdS C.src cTilde F)) ∧
      ∀ k, C.src.cardyNorm (cTilde / 12) (g k) = 1 := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  obtain ⟨u, -, hu, hmem⟩ := exists_seq_tendsto_sInf hne ⟨0, fun t ht => ht.1.le⟩
  choose g0 hg0 using fun k => (hmem k).2
  refine ⟨u, fun k => fun t => (C.src.cardyNorm (cTilde / 12) (g0 k))⁻¹ * g0 k t, fun k => ?_, hu,
    fun k => ?_⟩
  · obtain ⟨htc, hvac, hnn⟩ := hg0 k
    have hM := cardyNorm_pos_of_vac_pos_src hAt htc hvac
    refine ⟨testClass_smul_src _ htc, ?_, fun t ht => mul_nonneg (inv_nonneg.2 hM.le) (hnn t ht)⟩
    rw [gVac_smul_src]; exact mul_pos (inv_pos.2 hM) hvac
  · have hM := cardyNorm_pos_of_vac_pos_src hAt (hg0 k).1 (hg0 k).2.1
    rw [cardyNorm_smul_of_nonneg_src _ (inv_nonneg.2 hM.le), inv_mul_cancel₀ hM.ne']

lemma crossing_ae_zero_src (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    {gs : ℝ → ℝ} (htc : TestClass C.src (cTilde / 12) gs)
    (hvac : C.src.gVac (cTilde / 12) gs = 0)
    {T : ℝ} (hT : ∀ t ≥ T, 0 ≤ gs t)
    (meas : SourceCrossingMeasure C.src (cTilde / 12)) {Y : Set ℝ} (hν : meas.ν Yᶜ = 0)
    (hY : ∀ t ∈ Y, 0 ≤ gs t) : ∀ᵐ t ∂meas.ν, t ∈ Y ∧ gs t = 0 := by
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  obtain ⟨hint, hle⟩ := lemma_fwX_one_sided_src C.src hAt.crossingBounds hAt.pos meas htc (T := T) hT
  rw [IntegrableOn, restrict_Ici_eq_self_src meas] at hint
  rw [restrict_Ici_eq_self_src meas] at hle
  have hmem : ∀ᵐ t ∂meas.ν, t ∈ Y := by
    have : ∀ᵐ y ∂meas.ν, y ∉ Yᶜ := measure_eq_zero_iff_ae_notMem.1 hν
    filter_upwards [this] with y hy using Set.notMem_compl_iff.1 hy
  have hae : 0 ≤ᵐ[meas.ν] gs := hmem.mono fun t ht => hY t ht
  have h0 : ∫ t, gs t ∂meas.ν = 0 := le_antisymm (by linarith) (integral_nonneg_of_ae hae)
  have hz := (integral_eq_zero_iff_of_nonneg_ae hae hint).1 h0
  filter_upwards [hmem, hz] with t h1 h2 using ⟨h1, h2⟩

/-- **Theorem E'** (`ds:primal`, parts (a)–(d)) for `CommonSource` at large charge `c̃ ≥ c₀`. -/
theorem theorem_primal_src (C : CommonSource) {cTilde : ℝ} (hc : 12 * C.a₀ ≤ cTilde)
    (S : FixedChargeStripS C.src cTilde) {F : Set ℝ} (hFc : IsCompact F)
    (hF : F ⊆ Ioi 0) :
    (0 < C.src.T_V cTilde ∧ C.src.T_V cTilde ≤ constrainedThresholdS C.src cTilde F ∧
      (constrainedGapsS C.src cTilde F).Nonempty) ∧
    ∃ gs : ℝ → ℝ,
      (TestClass C.src (cTilde / 12) gs ∧ C.src.cardyNorm (cTilde / 12) gs = 1 ∧
        C.src.gVac (cTilde / 12) gs = 0 ∧
        (∀ t ∈ F ∪ Ici (constrainedThresholdS C.src cTilde F), 0 ≤ gs t) ∧
        (∀ R : ℝ, {t ∈ Icc (0 : ℝ) R | gs t = 0}.Finite) ∧ (∃ t : ℝ, 0 ≤ t ∧ gs t ≠ 0) ∧
        (∃ G : ℂ → ℂ, DifferentiableOn ℂ G openStrip ∧
          ∀ t : ℝ, 0 ≤ t → G (stripCoord cTilde t : ℂ) = (gs t : ℂ))) ∧
      (∀ meas : SourceCrossingMeasure C.src (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThresholdS C.src cTilde F))ᶜ = 0 →
          ∀ᵐ t ∂meas.ν, t ∈ F ∪ Ici (constrainedThresholdS C.src cTilde F) ∧ gs t = 0) ∧
      (∀ meas : SourceCrossingMeasure C.src (cTilde / 12),
        meas.ν (F ∪ Ici (constrainedThresholdS C.src cTilde F))ᶜ = 0 →
          (∃ Z : Set ℝ, (∀ R : ℝ, (Z ∩ Icc 0 R).Finite) ∧ meas.ν Zᶜ = 0) ∧
          0 < meas.ν {constrainedThresholdS C.src cTilde F}) ∧
      (∀ E : Set ℝ, IsCompact E → E ⊆ Ioi 0 → (∀ t ∈ E, 0 < gs t) →
        constrainedThresholdS C.src cTilde (F ∪ E) = constrainedThresholdS C.src cTilde F ∧
        ∀ meas : SourceCrossingMeasure C.src (cTilde / 12),
          meas.ν ((F ∪ E) ∪ Ici (constrainedThresholdS C.src cTilde F))ᶜ = 0 → meas.ν E = 0) := by
  classical
  have hAt : C.F.At (cTilde / 12) := C.at_ (by linarith)
  obtain ⟨β₀, S₀⟩ := SourceDualSetupCore.exists_of_common C hc one_pos
  set TF : ℝ := constrainedThresholdS C.src cTilde F with hTF
  have hTV := T_V_pos_of_common C hc S
  have hE := theorem_E_b_compact_src hAt hFc hF hTV
  obtain ⟨hle, hne⟩ := hE.1
  have hTF0 : 0 < TF := lt_of_lt_of_le hTV hle
  obtain ⟨τ, g, hfeas, hτ, hM⟩ := exists_normalised_sequence_src C hc hne
  have hv : ∀ k, ∫ t in Ioi (0 : ℝ), g k t * C.src.cardyV (cTilde / 12) t ≤ 0 := fun k => by
    have := (hfeas k).2.1
    change -2 * π * ∫ t in Ioi (0 : ℝ), g k t * C.src.cardyV (cTilde / 12) t > 0 at this
    nlinarith [Real.pi_pos]
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hτ.eventually (eventually_le_nhds (by linarith : TF < TF + 1)))
  let τ' := fun k => τ (k + N)
  let g' := fun k => g (k + N)
  have hτ' : Tendsto τ' atTop (𝓝 TF) := hτ.comp (tendsto_add_atTop_nat N)
  have hneg : ∀ k, ∀ t ≥ TF + 1, 0 ≤ g' k t := fun k t ht =>
    (hfeas (k + N)).2.2 t (Or.inr ((hN (k + N) (Nat.le_add_left N k)).trans ht))
  obtain ⟨φ, gs, hφ, htc, -, hunif, -, hvac_nn, ⟨t₀, ht₀, hgt₀⟩, hzero, ⟨G, hGd, hreal⟩, hrest⟩ :=
    exists_primal_limit_src C hc S (fun k => (hfeas (k + N)).1) (fun k => hM (k + N))
      (fun k => hv (k + N)) (by positivity) hneg
  have hpt : ∀ t : ℝ, 0 ≤ t → Tendsto (fun k => g' (φ k) t) atTop (𝓝 (gs t)) := fun t ht =>
    (hunif t).tendsto_at ⟨ht, le_rfl⟩
  have hnn : ∀ t ∈ F ∪ Ici TF, 0 ≤ gs t := fun t ht => by
    rcases ht with htF | htT
    · exact ge_of_tendsto (hpt t (hF htF).le)
        (Eventually.of_forall fun k => (hfeas (φ k + N)).2.2 t (Or.inl htF))
    · by_cases hlt : TF < t
      · obtain ⟨K, hK⟩ := eventually_atTop.1 ((hτ'.comp hφ.tendsto_atTop).eventually
          (eventually_le_nhds hlt))
        refine ge_of_tendsto (hpt t (hTF0.le.trans htT)) (eventually_atTop.2 ⟨K, fun k hk => ?_⟩)
        exact (hfeas (φ k + N)).2.2 t (Or.inr (hK k hk))
      · have heq_t : t = TF := le_antisymm (not_lt.1 hlt) htT
        subst heq_t
        have hpos_t : 0 < TF + 1 := by linarith
        have hgs_Ici : ContinuousWithinAt gs (Ici 0) TF := htc.cont TF hTF0.le
        have hseq_gt : ∀ n : ℕ, 0 ≤ gs (TF + 1 / ((n : ℝ) + 1)) := fun n => by
          have hlt' : TF < TF + 1 / ((n : ℝ) + 1) := by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
          obtain ⟨K, hK⟩ := eventually_atTop.1 ((hτ'.comp hφ.tendsto_atTop).eventually
            (eventually_le_nhds hlt'))
          refine ge_of_tendsto (hpt _ (by linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]))
            (eventually_atTop.2 ⟨K, fun k hk => ?_⟩)
          exact (hfeas (φ k + N)).2.2 _ (Or.inr (hK k hk))
        have htend_s : Tendsto (fun n : ℕ => TF + 1 / ((n : ℝ) + 1)) atTop (𝓝 TF) := by
          simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
        have htend_w : Tendsto (fun n : ℕ => TF + 1 / ((n : ℝ) + 1)) atTop (𝓝[Ici 0] TF) :=
          tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ htend_s
            (Eventually.of_forall fun n => mem_Ici.mpr (by linarith [hTF0, show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]))
        exact ge_of_tendsto (hgs_Ici.tendsto.comp htend_w) (Eventually.of_forall hseq_gt)
  obtain ⟨-, meas_TF, hν_TF⟩ := hE.2.1
  have hvac_le : C.src.gVac (cTilde / 12) gs ≤ 0 := by
    obtain ⟨hint, hle1⟩ := lemma_fwX_one_sided_src C.src hAt.crossingBounds hAt.pos meas_TF htc
      (T := TF) fun t ht => hnn t (Or.inr ht)
    unfold IntegrableOn at hint
    rw [restrict_Ici_eq_self_src meas_TF] at hint hle1
    have hae : 0 ≤ᵐ[meas_TF.ν] gs := by
      have := measure_eq_zero_iff_ae_notMem.1 hν_TF
      exact this.mono fun t ht => hnn t (Set.notMem_compl_iff.1 ht)
    have h0 : 0 ≤ ∫ t, gs t ∂meas_TF.ν := integral_nonneg_of_ae hae
    linarith
  have hvac_eq : C.src.gVac (cTilde / 12) gs = 0 := le_antisymm hvac_le hvac_nn
  obtain ⟨hM1, -⟩ := hrest hvac_le
  refine ⟨⟨hTV, hle, hne⟩, gs, ⟨htc, hM1, hvac_eq, hnn, hzero, ⟨t₀, ht₀, hgt₀⟩, ⟨G, hGd, hreal⟩⟩,
    ?_, ?_, ?_⟩
  · intro meas hν
    exact crossing_ae_zero_src C hc htc hvac_eq (T := TF) (fun t ht => hnn t (Or.inr ht)) meas hν hnn
  · intro meas hν
    have hae := crossing_ae_zero_src C hc htc hvac_eq (T := TF) (fun t ht => hnn t (Or.inr ht))
      meas hν hnn
    have hXpos : F ∪ Ici TF ⊆ Ici 0 := union_subset (fun t ht => (hF ht).le) (fun t ht =>
      le_trans hTF0.le ht)
    refine ⟨⟨{t | 0 ≤ t ∧ gs t = 0}, fun R => ?_, ?_⟩, ?_⟩
    · exact (hzero R).subset fun t ht => ⟨ht.2, ht.1.2⟩
    · refine measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [hae] with t ht
      exact Set.notMem_compl_iff.2 ⟨hXpos ht.1, ht.2⟩
    · by_contra h0
      have h0' : meas.ν {TF} = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)
      set Zf : Set ℝ := {t | 0 ≤ t ∧ gs t = 0} ∩ Icc 0 (TF + 1) ∩ Ioi TF with hZf
      have hZfin : Zf.Finite := (hzero (TF + 1)).subset fun t ht => ⟨ht.1.2, ht.1.1.2⟩
      have hTFn : TF ∉ Zf := fun h => lt_irrefl _ (mem_Ioi.1 h.2)
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hZfin.isClosed.isOpen_compl TF hTFn
      set ε' : ℝ := min ε 1 with hε'
      have hε'pos : 0 < ε' := lt_min hε one_pos
      have hbad : meas.ν {t | ¬ (t ∈ F ∪ Ici TF ∧ gs t = 0)} = 0 := ae_iff.1 hae
      have hIoo : meas.ν (Ioo TF (TF + ε')) = 0 := by
        refine measure_mono_null (fun t ht => ?_) hbad
        rintro ⟨-, hz⟩
        have hmemZ : t ∈ Zf := ⟨⟨⟨by linarith [ht.1], hz⟩, by linarith [ht.1], by
          have := min_le_right ε 1; linarith [ht.2]⟩, ht.1⟩
        have : t ∈ Metric.ball TF ε := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          have := min_le_left ε 1
          constructor <;> linarith [ht.1, ht.2]
        exact hball this hmemZ
      have hν2 : meas.ν (F ∪ Ici (TF + ε'))ᶜ = 0 := by
        refine measure_mono_null (fun t ht => ?_)
          (measure_union_null (measure_union_null hν h0') hIoo)
        have hnF : t ∉ F := fun h => ht (Or.inl h)
        have hlt : t < TF + ε' := lt_of_not_ge fun h => ht (Or.inr h)
        rcases lt_trichotomy t TF with h | h | h
        · refine Or.inl (Or.inl fun hh => ?_)
          rcases hh with hh | hh
          · exact hnF hh
          · exact absurd (mem_Ici.1 hh) (not_le.2 h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr ⟨h, hlt⟩
      have := le_constrainedThresholdS_of_crossingMeasure C.src S₀ hAt.crossingBounds hne meas hν2
      linarith
  · intro E hEc hE hEpos
    have hFEc : IsCompact (F ∪ E) := hFc.union hEc
    have hFE : F ∪ E ⊆ Ioi 0 := union_subset hF hE
    obtain ⟨⟨hle2, hne2⟩, ⟨-, meas', hν'⟩, -, -⟩ :=
      theorem_E_b_compact_src hAt hFEc hFE hTV
    set T' : ℝ := constrainedThresholdS C.src cTilde (F ∪ E) with hT'
    have hgap_sub : constrainedGapsS C.src cTilde (F ∪ E) ⊆ constrainedGapsS C.src cTilde F :=
      fun τ hτ => ⟨hτ.1, by
        obtain ⟨g1, hg1, hg2, hg3⟩ := hτ.2
        exact ⟨g1, hg1, hg2, fun t ht => hg3 t (by
          rcases ht with ht | ht
          · exact Or.inl (Or.inl ht)
          · exact Or.inr ht)⟩⟩
    have hTFT' : TF ≤ T' :=
      csInf_le_csInf ⟨0, fun t ht => ht.1.le⟩ hne2 hgap_sub
    have hnnE : ∀ t ∈ (F ∪ E) ∪ Ici TF, 0 ≤ gs t := fun t ht => by
      rcases ht with (ht | ht) | ht
      · exact hnn t (Or.inl ht)
      · exact (hEpos t ht).le
      · exact hnn t (Or.inr ht)
    have hEnull : ∀ meas : SourceCrossingMeasure C.src (cTilde / 12),
        meas.ν ((F ∪ E) ∪ Ici TF)ᶜ = 0 → meas.ν E = 0 := fun meas hν => by
      have hae := crossing_ae_zero_src C hc htc hvac_eq (T := TF) (fun t ht => hnn t (Or.inr ht)) meas hν hnnE
      refine measure_mono_null (fun t ht => ?_) (ae_iff.1 hae)
      rintro ⟨-, hz⟩
      exact (hEpos t ht).ne' hz
    refine ⟨le_antisymm ?_ hTFT', hEnull⟩
    have hnnE' : ∀ t ∈ (F ∪ E) ∪ Ici T', 0 ≤ gs t := fun t ht => by
      rcases ht with (ht | ht) | ht
      · exact hnn t (Or.inl ht)
      · exact (hEpos t ht).le
      · exact hnn t (Or.inr (le_trans hTFT' ht))
    have hae := crossing_ae_zero_src C hc htc hvac_eq (T := TF) (fun t ht => hnn t (Or.inr ht))
      meas' hν' hnnE'
    have hE0 : meas'.ν E = 0 := by
      refine measure_mono_null (fun t ht => ?_) (ae_iff.1 hae)
      rintro ⟨-, hz⟩
      exact (hEpos t ht).ne' hz
    have hν'' : meas'.ν (F ∪ Ici T')ᶜ = 0 := by
      refine measure_mono_null (fun t ht => ?_) (measure_union_null hν' hE0)
      by_cases hE' : t ∈ E
      · exact Or.inr hE'
      · refine Or.inl fun hh => ht ?_
        rcases hh with (hh | hh) | hh
        · exact Or.inl hh
        · exact absurd hh hE'
        · exact Or.inr hh
    exact le_constrainedThresholdS_of_crossingMeasure C.src S₀ hAt.crossingBounds hne meas' hν''

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.fixedChargeStripS_of_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.fixedChargeStripS_of_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.T_V_pos_of_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.T_V_pos_of_common

/-- info: 'FormalResearch.ModularBootstrap.Mixtures.theorem_primal_src' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Mixtures.theorem_primal_src

end FormalResearch.ModularBootstrap.Mixtures

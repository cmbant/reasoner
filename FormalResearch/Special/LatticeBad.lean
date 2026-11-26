module

public import FormalResearch.Special.LatticeGeom

/-!
# Comparison of fractional parts: the "bad set" estimate of `lem:latticesum` (i)

For `t` `ε`-close to the calibrated phase `t₀` and a weight `φ` with `|φ(s)| ≤ C_φ e^{-κ|s|}`,
`‖∫_{-X}^{X} φ ({t} - {t₀})‖ ≤ C_φ · wconst κ · ε · (1 + 4(M+2ε+1)/m)`, with **no factor `X`**:
where no integer lies between `t(s)` and `t₀(s)` the fractional parts differ by `t - t₀`, and the
exceptional set meets every unit interval in measure `≤ (M+2ε+1)·4ε/m` (`nearInt_meas`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- The weight constant `2 e^κ/(1-e^{-κ})`. -/
noncomputable def wconst (κ : ℝ) : ℝ := 2 * Real.exp κ / (1 - Real.exp (-κ))

lemma fract_diff_le_of_no_int {ε : ℝ} (hε : 0 ≤ ε) {a b : ℝ} (hab : |a - b| ≤ ε)
    (hno : ∀ n : ℤ, ε < |b - n|) : |Int.fract a - Int.fract b| ≤ ε := by
  have hb1 := Int.floor_le b
  have hb2 := Int.lt_floor_add_one b
  have h1 := hno ⌊b⌋
  have h2 := hno (⌊b⌋ + 1)
  push_cast at h2
  rw [abs_of_nonneg (by linarith)] at h1
  rw [abs_of_nonpos (by linarith)] at h2
  have hab' := abs_le.mp hab
  have hfl : ⌊a⌋ = ⌊b⌋ := by
    rw [Int.floor_eq_iff]; constructor <;> linarith
  unfold Int.fract
  rw [hfl]
  have : a - ↑⌊b⌋ - (b - ↑⌊b⌋) = a - b := by ring
  rw [this]; exact hab

lemma abs_fract_sub_le_one (a b : ℝ) : |Int.fract a - Int.fract b| ≤ 1 := by
  have h1 := Int.fract_nonneg a
  have h2 := Int.fract_lt_one a
  have h3 := Int.fract_nonneg b
  have h4 := Int.fract_lt_one b
  rw [abs_le]; constructor <;> linarith

namespace CalPhase

variable {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ}

lemma continuousOn_realPhase (h : CalPhase τ0 X y0 m M K) :
    ContinuousOn (realPhase τ0) (Icc (-(X + 1)) (X + 1)) := fun z hz =>
  (h.hasDerivAt_real (abs_le.mpr hz)).continuousAt.continuousWithinAt

lemma measurableSet_nearInt (h : CalPhase τ0 X y0 m M K) {a : ℝ} (ha : -(X + 1) ≤ a)
    (hb : a + 1 ≤ X + 1) (ε : ℝ) : MeasurableSet (nearInt τ0 ε a) := by
  have hsub : Icc a (a + 1) ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc ha hb
  have : nearInt τ0 ε a = ⋃ n : ℤ, (Icc a (a + 1) ∩ realPhase τ0 ⁻¹' Icc (n - ε) (n + ε)) := by
    ext s
    simp only [nearInt, mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_Icc, abs_le]
    constructor
    · rintro ⟨hs, n, h1, h2⟩; exact ⟨n, hs, by linarith, by linarith⟩
    · rintro ⟨n, hs, h1, h2⟩; exact ⟨hs, n, by linarith, by linarith⟩
  rw [this]
  refine MeasurableSet.iUnion (fun n => IsClosed.measurableSet ?_)
  exact (h.continuousOn_realPhase.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Icc

end CalPhase


/-- The integrand `φ ({t} - {t₀})`. -/
noncomputable def fractDiff (φ : ℝ → ℂ) (τ0 : ℂ → ℂ) (t : ℝ → ℝ) (s : ℝ) : ℂ :=
  φ s * (((Int.fract (t s) : ℝ) : ℂ) - ((Int.fract (realPhase τ0 s) : ℝ) : ℂ))

lemma norm_fractDiff_le_one {φ : ℝ → ℂ} {τ0 : ℂ → ℂ} {t : ℝ → ℝ} (s : ℝ) :
    ‖fractDiff φ τ0 t s‖ ≤ ‖φ s‖ := by
  unfold fractDiff
  rw [norm_mul]
  have : ‖(((Int.fract (t s) : ℝ) : ℂ) - ((Int.fract (realPhase τ0 s) : ℝ) : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_fract_sub_le_one _ _
  calc ‖φ s‖ * _ ≤ ‖φ s‖ * 1 := mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = ‖φ s‖ := mul_one _

lemma norm_fractDiff_le {φ : ℝ → ℂ} {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (h : LevelData τ0 X y0 m M K ε t S) {a s : ℝ} (hs : s ∈ Icc a (a + 1)) (hw : |s| ≤ X + 1) :
    ‖fractDiff φ τ0 t s‖ ≤ ‖φ s‖ * (ε + (CalPhase.nearInt τ0 ε a).indicator (fun _ => (1 : ℝ)) s) := by
  by_cases hA : s ∈ CalPhase.nearInt τ0 ε a
  · rw [Set.indicator_of_mem hA]
    have := norm_fractDiff_le_one (φ := φ) (τ0 := τ0) (t := t) s
    have h0 := h.eps
    nlinarith [norm_nonneg (φ s)]
  · rw [Set.indicator_of_notMem hA, add_zero]
    have hno : ∀ n : ℤ, ε < |realPhase τ0 s - n| := by
      intro n; by_contra hn; push Not at hn
      exact hA ⟨hs, n, hn⟩
    have hd := fract_diff_le_of_no_int h.eps (h.close s hw) hno
    unfold fractDiff
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hd

lemma fractDiff_integrableOn {φ : ℝ → ℂ} {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ}
    {S : Finset ℝ} (h : LevelData τ0 X y0 m M K ε t S) {Cφ κ : ℝ} (hφc : Continuous φ)
    (hκ : 0 ≤ κ) (hC : 0 ≤ Cφ) (hφ : ∀ s : ℝ, ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s|)) :
    IntegrableOn (fractDiff φ τ0 t) (Icc (-(X + 1)) (X + 1)) := by
  have h1 : Measurable (fun s => ((Int.fract (t s) : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp (measurable_fract.comp h.cont.measurable)
  have h2 : AEMeasurable (fun s => ((Int.fract (realPhase τ0 s) : ℝ) : ℂ))
      (volume.restrict (Icc (-(X + 1)) (X + 1))) :=
    Complex.measurable_ofReal.comp_aemeasurable (measurable_fract.comp_aemeasurable
      (h.cal.continuousOn_realPhase.aemeasurable measurableSet_Icc))
  have hm : AEStronglyMeasurable (fractDiff φ τ0 t) (volume.restrict (Icc (-(X + 1)) (X + 1))) := by
    unfold fractDiff
    exact (hφc.aestronglyMeasurable).mul (h1.aemeasurable.sub h2).aestronglyMeasurable
  show Integrable _ (volume.restrict (Icc (-(X + 1)) (X + 1)))
  refine Integrable.of_bound hm Cφ ?_
  refine Filter.Eventually.of_forall (fun s => ?_)
  refine (norm_fractDiff_le_one s).trans ((hφ s).trans ?_)
  have : Real.exp (-κ * |s|) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg s]
  nlinarith

lemma interval_bound {φ : ℝ → ℂ} {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ}
    {S : Finset ℝ} (h : LevelData τ0 X y0 m M K ε t S) {Cφ κ : ℝ} (hφc : Continuous φ)
    (hκ : 0 ≤ κ) (hC : 0 ≤ Cφ) (hφ : ∀ s : ℝ, ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s|))
    {a : ℝ} (ha : -(X + 1) ≤ a) (hb : a + 1 ≤ X + 1) :
    ∫ s in a..(a + 1), ‖fractDiff φ τ0 t s‖ ≤
      Cφ * Real.exp κ * Real.exp (-κ * |a|) * (ε + (M + 2 * ε + 1) * (4 * ε / m)) := by
  set c : ℝ := Cφ * Real.exp κ * Real.exp (-κ * |a|) with hc
  have hc0 : 0 ≤ c := by positivity
  set A := CalPhase.nearInt τ0 ε a with hA
  have hAm : MeasurableSet A := h.cal.measurableSet_nearInt ha hb ε
  have hsub : Icc a (a + 1) ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc ha hb
  have hint := (fractDiff_integrableOn h hφc hκ hC hφ).mono_set hsub
  have hint' : IntervalIntegrable (fun s => ‖fractDiff φ τ0 t s‖) volume a (a + 1) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact hint.norm
  have hind : IntervalIntegrable (fun s => (A.indicator (fun _ => (1 : ℝ)) s)) volume a (a + 1) := by
    refine (intervalIntegrable_const (c := (1 : ℝ))).mono_fun ?_ ?_
    · exact (measurable_const.indicator hAm).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun s => ?_)
      by_cases hs : s ∈ A <;> simp [hs]
  have hg : IntervalIntegrable (fun s => c * (ε + A.indicator (fun _ => (1 : ℝ)) s)) volume a (a + 1) :=
    (intervalIntegrable_const.add hind).const_mul c
  have hmono : ∫ s in a..(a + 1), ‖fractDiff φ τ0 t s‖ ≤
      ∫ s in a..(a + 1), c * (ε + A.indicator (fun _ => (1 : ℝ)) s) := by
    refine intervalIntegral.integral_mono_on (by linarith) hint' hg (fun s hs => ?_)
    have hw : |s| ≤ X + 1 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine (norm_fractDiff_le h hs hw).trans ?_
    have hind0 : 0 ≤ ε + A.indicator (fun _ => (1 : ℝ)) s := by
      have := h.eps
      have : 0 ≤ A.indicator (fun _ => (1 : ℝ)) s := by
        by_cases hs : s ∈ A <;> simp [hs]
      linarith
    apply mul_le_mul_of_nonneg_right _ hind0
    refine (hφ s).trans ?_
    have hsa : |a| - 1 ≤ |s| := by
      have := abs_sub_abs_le_abs_sub a s
      have h2 : |a - s| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
      linarith
    have hex : Real.exp (-κ * |s|) ≤ Real.exp κ * Real.exp (-κ * |a|) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    rw [hc]
    calc Cφ * Real.exp (-κ * |s|) ≤ Cφ * (Real.exp κ * Real.exp (-κ * |a|)) :=
          mul_le_mul_of_nonneg_left hex hC
      _ = _ := by ring
  have hcomp : ∫ s in a..(a + 1), c * (ε + A.indicator (fun _ => (1 : ℝ)) s) =
      c * ε + c * (volume.restrict (Ioc a (a + 1))).real A := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    have hi2 : Integrable (fun s => A.indicator (fun _ => (1 : ℝ)) s) (volume.restrict (Ioc a (a + 1))) := by
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp hind
    rw [MeasureTheory.integral_const_mul, integral_add (integrable_const _) hi2]
    have : (fun s => A.indicator (fun _ => (1 : ℝ)) s) = A.indicator (1 : ℝ → ℝ) := rfl
    rw [this, integral_indicator_one hAm]
    simp
    ring
  have hreal : (volume.restrict (Ioc a (a + 1))).real A ≤ (M + 2 * ε + 1) * (4 * ε / m) := by
    have h1 : (volume.restrict (Ioc a (a + 1))) A ≤ volume A := Measure.restrict_le_self A
    have h2 := h.cal.nearInt_meas h.eps ha hb
    have h3 : (volume.restrict (Ioc a (a + 1))) A ≤ ENNReal.ofReal ((M + 2 * ε + 1) * (4 * ε / m)) :=
      h1.trans h2
    unfold Measure.real
    exact ENNReal.toReal_le_of_le_ofReal (by
      have := h.eps; have := h.cal.hm; have := h.cal.M_pos'
      exact mul_nonneg (by linarith) (by positivity)) h3
  calc _ ≤ _ := hmono
    _ = _ := hcomp
    _ ≤ c * ε + c * ((M + 2 * ε + 1) * (4 * ε / m)) := by
        have := mul_le_mul_of_nonneg_left hreal hc0; linarith
    _ = _ := by rw [hc]; ring

/-- **Comparison of fractional parts** (`lem:latticesum` (i), first step):
`‖∫_{-X}^{X} φ ({t} - {t₀})‖ ≤ C_φ · wconst κ · ε · (1 + 4(M+2ε+1)/m)`, with no factor `X`. -/
theorem fract_diff_integral_le {φ : ℝ → ℂ} {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ}
    {S : Finset ℝ} (h : LevelData τ0 X y0 m M K ε t S) {Cφ κ : ℝ} (hφc : Continuous φ)
    (hκ : 0 < κ) (hC : 0 ≤ Cφ) (hφ : ∀ s : ℝ, ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s|)) :
    ‖∫ s in (-X)..X, fractDiff φ τ0 t s‖ ≤
      Cφ * wconst κ * ε * (1 + 4 * (M + 2 * ε + 1) / m) := by
  have hX := h.cal.hX
  set N : ℕ := ⌈X⌉₊ with hN
  have hN1 : X ≤ N := Nat.le_ceil X
  have hN2 : (N : ℝ) < X + 1 := Nat.ceil_lt_add_one hX.le
  have hsubN : Icc (-(N : ℝ)) N ⊆ Icc (-(X + 1)) (X + 1) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hintN : IntervalIntegrable (fun s => ‖fractDiff φ τ0 t s‖) volume (-(N : ℝ)) N := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
    exact ((fractDiff_integrableOn h hφc hκ.le hC hφ).mono_set hsubN).norm
  have step1 : ‖∫ s in (-X)..X, fractDiff φ τ0 t s‖ ≤ ∫ s in (-X)..X, ‖fractDiff φ τ0 t s‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by linarith)
  have step2 : ∫ s in (-X)..X, ‖fractDiff φ τ0 t s‖ ≤ ∫ s in (-(N : ℝ))..N, ‖fractDiff φ τ0 t s‖ :=
    intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun s => norm_nonneg _)) hintN
  set a : ℕ → ℝ := fun k => -(N : ℝ) + k with ha
  have hadj : ∀ k < 2 * N, IntervalIntegrable (fun s => ‖fractDiff φ τ0 t s‖) volume (a k) (a (k + 1)) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ 2 * N := by exact_mod_cast hk
    refine hintN.mono_set ?_
    rw [uIcc_of_le (by simp [ha]), uIcc_of_le (by linarith)]
    apply Icc_subset_Icc
    · simp [ha]
    · simp only [ha]; push_cast; linarith
  have step3 := intervalIntegral.sum_integral_adjacent_intervals hadj
  have ha0 : a 0 = -(N : ℝ) := by simp [ha]
  have haN : a (2 * N) = N := by simp only [ha]; push_cast; ring
  rw [ha0, haN] at step3
  have step4 : ∀ k ∈ Finset.range (2 * N), ∫ s in (a k)..(a (k + 1)), ‖fractDiff φ τ0 t s‖ ≤
      Cφ * Real.exp κ * Real.exp (-κ * |a k|) * (ε + (M + 2 * ε + 1) * (4 * ε / m)) := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ 2 * N := by exact_mod_cast Finset.mem_range.mp hk
    have h1 := interval_bound h hφc hκ.le hC hφ (a := a k) (by simp only [ha]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      (by simp only [ha]; push_cast; linarith)
    have : a (k + 1) = a k + 1 := by simp only [ha]; push_cast; ring
    rw [this]; exact h1
  have step5 := Finset.sum_le_sum step4
  have step6 : ∑ k ∈ Finset.range (2 * N), Cφ * Real.exp κ * Real.exp (-κ * |a k|) *
      (ε + (M + 2 * ε + 1) * (4 * ε / m)) =
      Cφ * Real.exp κ * (ε + (M + 2 * ε + 1) * (4 * ε / m)) *
        ∑ k ∈ Finset.range (2 * N), Real.exp (-κ * |a k|) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  have step7 := sum_exp_abs_le hκ N
  have hB : 0 ≤ Cφ * Real.exp κ * (ε + (M + 2 * ε + 1) * (4 * ε / m)) := by
    have := h.eps; have := h.cal.hm; have := h.cal.M_pos'
    have : 0 ≤ (M + 2 * ε + 1) * (4 * ε / m) := mul_nonneg (by linarith) (by positivity)
    positivity
  calc ‖∫ s in (-X)..X, fractDiff φ τ0 t s‖ ≤ ∫ s in (-(N : ℝ))..N, ‖fractDiff φ τ0 t s‖ :=
        step1.trans step2
    _ = ∑ k ∈ Finset.range (2 * N), ∫ s in (a k)..(a (k + 1)), ‖fractDiff φ τ0 t s‖ := step3.symm
    _ ≤ _ := step5
    _ = _ := step6
    _ ≤ Cφ * Real.exp κ * (ε + (M + 2 * ε + 1) * (4 * ε / m)) * (2 / (1 - Real.exp (-κ))) :=
        mul_le_mul_of_nonneg_left step7 hB
    _ = Cφ * wconst κ * ε * (1 + 4 * (M + 2 * ε + 1) / m) := by
        unfold wconst; have := h.cal.hm; field_simp

end FormalResearch.Special.Lattice

module

public import FormalResearch.CohnElkies.SaddleGeometry
public import FormalResearch.CohnElkies.ClosedResolvent
public import FormalResearch.CohnElkies.OriginMellinAndS0
public import FormalResearch.Special.AiryClarkLabel
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Pre-Edge Bounds and B-Spline Smoothing-Gain Floor

Formalizes:
* `u1c_o1_upper.tex` Lemmas `O.0` (`u1co:O0`) and `O.1` (`u1co:O1`, `(e2)`): uniform `m`-fold
  B-spline densities, oscillating averaging floor, smoothing-gain floor under Hypothesis (H),
  and an unconditional non-vacuity witness.
* `ce_o1_pre_edge.tex` Section `PE.1` (`cepe:PE1`, `(cepe:dirichlet-floor)`) and `PE.3`
  `(cepe:PE3a)`: Airy Riccati monotonicity and bounds, the two-scale Dirichlet lower bound on
  `(-v_c(t))` with a Dirac non-vacuity witness, and the `X^{-3/2}`-dominated `B_c^*(z)` Hölder
  bound (noting that for density `≤ C X^{-3/2}` the sharp `min X 1` integral bound is `4 C`,
  while for `(1 + X)^{-3/2}` it is `≤ 3 C`).
-/

@[expose] public section

open Complex Filter MeasureTheory Set
open scoped Convolution Real Topology

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Part 1A: Uniform B-spline densities and unit properties -/

/-- Rescaled indicator `m · 1_{[0, 1/m]}` on `ℝ`. -/
noncomputable def bsplineBox (m : ℕ) : ℝ → ℝ :=
  Set.indicator (Icc (0 : ℝ) (m : ℝ)⁻¹) (fun _ => (m : ℝ))

/-- `(k + 1)`-fold convolution iterate of `f` against Lebesgue measure. -/
noncomputable def bsplineConvIter (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => f
  | k + 1 => bsplineConvIter f k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] f

/-- Unit `m`-fold uniform B-spline density `ψ_{m,1} = (m · 1_{[0, 1/m]})^{*m}` for `m ≥ 1`. -/
noncomputable def bsplineUnit (m : ℕ) (t : ℝ) : ℝ :=
  if m = 0 then 0 else bsplineConvIter (bsplineBox m) (m - 1) t

/-- Scaled `m`-fold B-spline density `ψ_m(t) = δ₀⁻¹ ψ_{m,1}(t / δ₀)`. -/
noncomputable def bspline (m : ℕ) (δ₀ t : ℝ) : ℝ := δ₀⁻¹ * bsplineUnit m (t / δ₀)

private lemma bsplineBox_nonneg (m : ℕ) (t : ℝ) : 0 ≤ bsplineBox m t :=
  Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg m) t

private lemma bsplineBox_le_natCast (m : ℕ) (t : ℝ) : bsplineBox m t ≤ m := by
  unfold bsplineBox; by_cases ht : t ∈ Icc (0 : ℝ) (m : ℝ)⁻¹ <;> simp [ht]

private lemma bsplineBox_integrable (m : ℕ) : Integrable (bsplineBox m) :=
  (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (C := (m : ℝ)) (hs := measure_Icc_lt_top.ne))

private lemma bsplineBox_support_subset (m : ℕ) : Function.support (bsplineBox m) ⊆ Icc (0 : ℝ) (m : ℝ)⁻¹ :=
  fun _ ht => by by_contra hnot; apply ht; simp [bsplineBox, hnot]

private lemma bsplineBox_integral_one {m : ℕ} (hm : 1 ≤ m) : ∫ t, bsplineBox m t = 1 := by
  have hm_pos : (0 : ℝ) < m := by positivity
  unfold bsplineBox
  rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
    Measure.real_def, Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal (by positivity)]
  field_simp

private lemma bsplineBox_symm {m : ℕ} (t : ℝ) : bsplineBox m ((m : ℝ)⁻¹ - t) = bsplineBox m t := by
  unfold bsplineBox; by_cases ht : t ∈ Icc (0 : ℝ) (m : ℝ)⁻¹
  · have h' : (m : ℝ)⁻¹ - t ∈ Icc (0 : ℝ) (m : ℝ)⁻¹ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simp only [Set.indicator_of_mem ht, Set.indicator_of_mem h']
  · have h' : (m : ℝ)⁻¹ - t ∉ Icc (0 : ℝ) (m : ℝ)⁻¹ := fun h => ht ⟨by linarith [h.2], by linarith [h.1]⟩
    simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem h']

private lemma bsplineConvIter_nonneg (m k : ℕ) (t : ℝ) : 0 ≤ bsplineConvIter (bsplineBox m) k t := by
  induction k generalizing t with
  | zero => exact bsplineBox_nonneg m t
  | succ k ih =>
      change 0 ≤ (bsplineConvIter (bsplineBox m) k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] bsplineBox m) t
      rw [convolution_mul]; exact integral_nonneg fun s => mul_nonneg (ih s) (bsplineBox_nonneg m (t - s))

private lemma bsplineConvIter_integrable (m k : ℕ) : Integrable (bsplineConvIter (bsplineBox m) k) := by
  induction k with
  | zero => exact bsplineBox_integrable m
  | succ k ih => exact ih.integrable_convolution _ (bsplineBox_integrable m)

private lemma bsplineConvIter_support_subset {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    Function.support (bsplineConvIter (bsplineBox m) k) ⊆ Icc (0 : ℝ) (((k + 1 : ℕ) : ℝ) / m) := by
  induction k with
  | zero => simpa [bsplineConvIter, one_div] using bsplineBox_support_subset m
  | succ k ih =>
      refine (support_convolution_subset _).trans fun t ht => ?_
      rcases Set.mem_add.mp ht with ⟨a, ha, b, hb, rfl⟩
      have ha' := ih ha; have hb' := bsplineBox_support_subset m hb; have hm_ne : (m : ℝ) ≠ 0 := by positivity
      have hsum : (((k + 1 : ℕ) : ℝ) / m) + (m : ℝ)⁻¹ = (((k + 2 : ℕ) : ℝ) / m) := by push_cast; field_simp; ring
      exact ⟨add_nonneg ha'.1 hb'.1, by linarith [ha'.2, hb'.2, hsum]⟩

private lemma bsplineConvIter_integral_one {m : ℕ} (hm : 1 ≤ m) (k : ℕ) : ∫ t, bsplineConvIter (bsplineBox m) k t = 1 := by
  induction k with
  | zero => exact bsplineBox_integral_one hm
  | succ k ih =>
      change ∫ t, (bsplineConvIter (bsplineBox m) k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] bsplineBox m) t = 1
      rw [integral_convolution _ (bsplineConvIter_integrable m k) (bsplineBox_integrable m)]
      simp [ih, bsplineBox_integral_one hm]

private lemma bsplineConvIter_eq_intervalIntegral (m k : ℕ) (t : ℝ) :
    bsplineConvIter (bsplineBox m) (k + 1) t =
      (m : ℝ) * ∫ u in (t - (m : ℝ)⁻¹)..t, bsplineConvIter (bsplineBox m) k u := by
  change (bsplineConvIter (bsplineBox m) k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] bsplineBox m) t = _
  rw [convolution_mul_swap]
  have hind : (fun s => bsplineConvIter (bsplineBox m) k (t - s) * bsplineBox m s) =
      Set.indicator (Icc (0 : ℝ) (m : ℝ)⁻¹) (fun s => (m : ℝ) * bsplineConvIter (bsplineBox m) k (t - s)) := by
    ext s; unfold bsplineBox; by_cases hs : s ∈ Icc (0 : ℝ) (m : ℝ)⁻¹ <;> simp [hs, mul_comm]
  rw [hind, integral_indicator measurableSet_Icc, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_left (fun u => bsplineConvIter (bsplineBox m) k u) t, sub_zero]

private lemma bsplineConvIter_le_natCast {m : ℕ} (hm : 1 ≤ m) (k : ℕ) (t : ℝ) :
    bsplineConvIter (bsplineBox m) k t ≤ m := by
  induction k generalizing t with
  | zero => exact bsplineBox_le_natCast m t
  | succ k _ =>
      rw [bsplineConvIter_eq_intervalIntegral]
      have hint_set : ∫ u in (t - (m : ℝ)⁻¹)..t, bsplineConvIter (bsplineBox m) k u ≤
          ∫ u, bsplineConvIter (bsplineBox m) k u := by
        rw [intervalIntegral.integral_of_le (sub_le_self t (by positivity))]
        exact setIntegral_le_integral (bsplineConvIter_integrable m k) (Eventually.of_forall (bsplineConvIter_nonneg m k))
      rw [bsplineConvIter_integral_one hm k] at hint_set
      exact (mul_le_mul_of_nonneg_left hint_set (Nat.cast_nonneg m)).trans_eq (mul_one _)

private lemma bsplineConvIter_symm {m : ℕ} (k : ℕ) (t : ℝ) :
    bsplineConvIter (bsplineBox m) k (((k + 1 : ℕ) : ℝ) / m - t) = bsplineConvIter (bsplineBox m) k t := by
  induction k generalizing t with
  | zero => simpa [bsplineConvIter, one_div] using bsplineBox_symm t
  | succ k ih =>
      change (bsplineConvIter (bsplineBox m) k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] bsplineBox m)
        (((k + 2 : ℕ) : ℝ) / m - t) = (bsplineConvIter (bsplineBox m) k ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] bsplineBox m) t
      rw [convolution_mul, convolution_mul, ← integral_sub_left_eq_self _ volume (((k + 1 : ℕ) : ℝ) / m)]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      have hdiff : ((k + 2 : ℕ) : ℝ) / m - t - (((k + 1 : ℕ) : ℝ) / m - s) = (m : ℝ)⁻¹ - (t - s) := by
        push_cast; by_cases hm0 : (m : ℝ) = 0 <;> [simp [hm0]; field_simp] <;> ring
      dsimp only; rw [ih s, hdiff, bsplineBox_symm]

private lemma bsplineConvIter_monotoneOn_half {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    MonotoneOn (bsplineConvIter (bsplineBox m) k) (Iic (((k + 1 : ℕ) : ℝ) / (2 * m))) := by
  have hm_pos : (0 : ℝ) < m := by positivity
  induction k with
  | zero =>
      intro t₁ _ t₂ ht₂ h12
      have h2m : (1 : ℝ) / (2 * m) ≤ (m : ℝ)⁻¹ := by rw [one_div, inv_le_inv₀ (by positivity) hm_pos]; linarith
      unfold bsplineConvIter bsplineBox; by_cases h1 : t₁ ∈ Icc (0 : ℝ) (m : ℝ)⁻¹
      · simp [h1, (⟨h1.1.trans h12, (mem_Iic.mp ht₂).trans (by simpa using h2m)⟩ : t₂ ∈ Icc (0 : ℝ) (m : ℝ)⁻¹)]
      · simp only [h1, not_false_eq_true, Set.indicator_of_notMem]; exact Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg m) t₂
  | succ k ih =>
      intro t₁ _ t₂ ht₂ h12
      rw [bsplineConvIter_eq_intervalIntegral, bsplineConvIter_eq_intervalIntegral]
      refine mul_le_mul_of_nonneg_left ?_ hm_pos.le
      set f := bsplineConvIter (bsplineBox m) k; have hf_int : Integrable f := bsplineConvIter_integrable m k
      have hint1 := intervalIntegral.integral_add_adjacent_intervals
        (a := t₁ - (m : ℝ)⁻¹) (b := t₁) (c := t₂) hf_int.intervalIntegrable hf_int.intervalIntegrable
      have hint2 := intervalIntegral.integral_add_adjacent_intervals
        (a := t₁ - (m : ℝ)⁻¹) (b := t₂ - (m : ℝ)⁻¹) (c := t₂) hf_int.intervalIntegrable hf_int.intervalIntegrable
      have hshift : ∫ u in (t₁ - (m : ℝ)⁻¹)..(t₂ - (m : ℝ)⁻¹), f u = ∫ u in t₁..t₂, f (u - (m : ℝ)⁻¹) :=
        (intervalIntegral.integral_comp_sub_right f (m : ℝ)⁻¹ (a := t₁) (b := t₂)).symm
      have hdiff_eq : (∫ u in (t₂ - (m : ℝ)⁻¹)..t₂, f u) - ∫ u in (t₁ - (m : ℝ)⁻¹)..t₁, f u =
          ∫ u in t₁..t₂, (f u - f (u - (m : ℝ)⁻¹)) := by
        rw [intervalIntegral.integral_sub hf_int.intervalIntegrable (hf_int.comp_sub_right (m : ℝ)⁻¹).intervalIntegrable,
          ← hshift]; linarith [hint1, hint2]
      rw [← sub_nonneg, hdiff_eq]
      refine intervalIntegral.integral_nonneg h12 fun u hu => sub_nonneg.mpr ?_
      have hu2 : u ≤ ((k + 2 : ℕ) : ℝ) / (2 * m) := hu.2.trans (mem_Iic.mp ht₂)
      by_cases hu_half : u ≤ ((k + 1 : ℕ) : ℝ) / (2 * m)
      · exact ih (mem_Iic.mpr (by linarith [show (0 : ℝ) ≤ (m : ℝ)⁻¹ by positivity])) (mem_Iic.mpr hu_half) (sub_le_self u (by positivity))
      · set v : ℝ := ((k + 1 : ℕ) : ℝ) / m - u
        have hv_half : v ≤ ((k + 1 : ℕ) : ℝ) / (2 * m) := by
          dsimp [v]; push_cast
          have hgt : ((k : ℝ) + 1) / (2 * m) < u := by exact_mod_cast (not_le.mp hu_half)
          linarith [show ((k : ℝ) + 1) / (2 * m) = (((k : ℝ) + 1) / m) / 2 by ring]
        have huv : u - (m : ℝ)⁻¹ ≤ v := by
          dsimp [v]; have h2u : 2 * (((k + 2 : ℕ) : ℝ) / (2 * m)) = ((k + 1 : ℕ) : ℝ) / m + (m : ℝ)⁻¹ := by push_cast; field_simp; ring
          linarith
        have hsym : f v = f u := bsplineConvIter_symm k u
        rw [← hsym]; exact ih (mem_Iic.mpr (huv.trans hv_half)) (mem_Iic.mpr hv_half) huv

private lemma bsplineConvIter_lower_interval {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    ∀ t ∈ Icc ((k : ℝ) / (4 * m)) ((3 * (k : ℝ) + 4) / (4 * m)),
      (m : ℝ) * (1 / 4 : ℝ) ^ k ≤ bsplineConvIter (bsplineBox m) k t := by
  have hm_pos : (0 : ℝ) < m := by positivity
  induction k with
  | zero =>
      intro t ht; simp only [Nat.cast_zero, zero_div, mul_zero, zero_add, pow_zero, mul_one, bsplineConvIter, bsplineBox] at ht ⊢
      simp [show t ∈ Icc (0 : ℝ) (m : ℝ)⁻¹ from ⟨ht.1, ht.2.trans_eq (by field_simp)⟩]
  | succ k ih =>
      intro t ht; rw [bsplineConvIter_eq_intervalIntegral]
      set a_k : ℝ := (k : ℝ) / (4 * m); set b_k : ℝ := (3 * (k : ℝ) + 4) / (4 * m)
      set L : ℝ := max (t - (m : ℝ)⁻¹) a_k; set R : ℝ := min t b_k
      have ht1 : ((k + 1 : ℕ) : ℝ) / (4 * m) ≤ t := ht.1; have ht2 : t ≤ (3 * ((k + 1 : ℕ) : ℝ) + 4) / (4 * m) := ht.2
      have hinv4 : (m : ℝ)⁻¹ = 4 / (4 * m) := by field_simp
      have hRL : 1 / (4 * (m : ℝ)) ≤ R - L := by
        dsimp [L, R, a_k, b_k]; push_cast at ht1 ht2; rw [le_sub_iff_add_le, add_max]
        refine max_le (le_min ?_ ?_) (le_min ?_ ?_)
        · linarith [show 1 / (4 * (m : ℝ)) ≤ (m : ℝ)⁻¹ by rw [hinv4]; gcongr; norm_num]
        · rw [show 1 / (4 * (m : ℝ)) + (t - (m : ℝ)⁻¹) = t - 3 / (4 * m) by rw [hinv4]; ring]
          linarith [show (3 * ((k : ℝ) + 1) + 4) / (4 * m) - 3 / (4 * m) = (3 * k + 4) / (4 * m) by ring]
        · rw [show 1 / (4 * (m : ℝ)) + (k : ℝ) / (4 * m) = (k + 1) / (4 * m) by ring]; exact ht1
        · rw [show 1 / (4 * (m : ℝ)) + (k : ℝ) / (4 * m) = (k + 1) / (4 * m) by ring]
          exact div_le_div_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      have hLR : L ≤ R := by linarith [show (0 : ℝ) < 1 / (4 * m) by positivity]
      set f := bsplineConvIter (bsplineBox m) k; have hf_int : Integrable f := bsplineConvIter_integrable m k
      have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
        (a := t - (m : ℝ)⁻¹) (b := R) (c := t) hf_int.intervalIntegrable hf_int.intervalIntegrable
      have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
        (a := t - (m : ℝ)⁻¹) (b := L) (c := R) hf_int.intervalIntegrable hf_int.intervalIntegrable
      have hge_LR : ∫ u in L..R, f u ≤ ∫ u in (t - (m : ℝ)⁻¹)..t, f u := by
        have h1 : 0 ≤ ∫ u in R..t, f u := intervalIntegral.integral_nonneg (min_le_left t b_k) fun u _ => bsplineConvIter_nonneg m k u
        have h2 : 0 ≤ ∫ u in (t - (m : ℝ)⁻¹)..L, f u :=
          intervalIntegral.integral_nonneg (le_max_left (t - (m : ℝ)⁻¹) a_k) fun u _ => bsplineConvIter_nonneg m k u
        linarith [hsplit1, hsplit2]
      have hlow_LR : (m : ℝ) * (1 / 4 : ℝ) ^ k * (R - L) ≤ ∫ u in L..R, f u := by
        rw [show (m : ℝ) * (1 / 4 : ℝ) ^ k * (R - L) = ∫ _u in L..R, (m : ℝ) * (1 / 4 : ℝ) ^ k by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]]
        exact intervalIntegral.integral_mono_on hLR intervalIntegrable_const hf_int.intervalIntegrable
          fun u hu => ih u ⟨(le_max_right _ _).trans hu.1, hu.2.trans (min_le_right _ _)⟩
      have hmain : (m : ℝ) * (1 / 4 : ℝ) ^ k * (1 / (4 * m)) ≤ ∫ u in (t - (m : ℝ)⁻¹)..t, f u :=
        (mul_le_mul_of_nonneg_left hRL (by positivity)).trans (hlow_LR.trans hge_LR)
      calc (m : ℝ) * (1 / 4 : ℝ) ^ (k + 1) = (m : ℝ) * ((m : ℝ) * (1 / 4 : ℝ) ^ k * (1 / (4 * m))) := by rw [pow_succ]; field_simp
        _ ≤ (m : ℝ) * ∫ u in (t - (m : ℝ)⁻¹)..t, f u := mul_le_mul_of_nonneg_left hmain hm_pos.le

theorem bsplineUnit_nonneg (m : ℕ) (t : ℝ) : 0 ≤ bsplineUnit m t := by
  unfold bsplineUnit; split_ifs; exacts [le_rfl, bsplineConvIter_nonneg m (m - 1) t]

theorem bsplineUnit_le_natCast {m : ℕ} (hm : 1 ≤ m) (t : ℝ) : bsplineUnit m t ≤ m := by
  have hm0 : m ≠ 0 := by omega
  simp only [bsplineUnit, hm0, ↓reduceIte]; exact bsplineConvIter_le_natCast hm (m - 1) t

theorem bsplineUnit_support {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ∉ Icc (0 : ℝ) 1) : bsplineUnit m t = 0 := by
  have hm0 : m ≠ 0 := by omega
  simp only [bsplineUnit, hm0, ↓reduceIte]; by_contra hne
  have hmem := bsplineConvIter_support_subset hm (m - 1) hne
  rw [Nat.sub_add_cancel hm, div_self (by positivity : (m : ℝ) ≠ 0)] at hmem; exact ht hmem

theorem bsplineUnit_integrable (m : ℕ) : Integrable (bsplineUnit m) := by
  unfold bsplineUnit; split_ifs; exacts [integrable_zero ℝ ℝ volume, bsplineConvIter_integrable m (m - 1)]

theorem bsplineUnit_integral_one {m : ℕ} (hm : 1 ≤ m) : ∫ t, bsplineUnit m t = 1 := by
  have hm0 : m ≠ 0 := by omega
  simp only [bsplineUnit, hm0, ↓reduceIte]; exact bsplineConvIter_integral_one hm (m - 1)

theorem bsplineUnit_setIntegral_one {m : ℕ} (hm : 1 ≤ m) : ∫ t in Icc (0 : ℝ) 1, bsplineUnit m t = 1 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => bsplineUnit_support hm ht), bsplineUnit_integral_one hm]

theorem bsplineUnit_symm (m : ℕ) (t : ℝ) : bsplineUnit m (1 - t) = bsplineUnit m t := by
  by_cases hm : m = 0
  · subst hm; simp [bsplineUnit]
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    simp only [bsplineUnit, hm, ↓reduceIte]
    have h1 : (((m - 1 + 1 : ℕ) : ℝ) / m) = 1 := by rw [Nat.sub_add_cancel hm1, div_self (by positivity : (m : ℝ) ≠ 0)]
    have hsym := bsplineConvIter_symm (m := m) (m - 1) t; rwa [h1] at hsym

theorem bsplineUnit_pos_one_quarter {m : ℕ} (hm : 1 ≤ m) : 0 < bsplineUnit m (1 / 4) := by
  have hm0 : m ≠ 0 := by omega
  have hm_pos : (0 : ℝ) < m := by positivity
  simp only [bsplineUnit, hm0, ↓reduceIte]
  have h1 : ((m - 1 : ℕ) : ℝ) / (4 * m) ≤ 1 / 4 := by
    rw [Nat.cast_sub hm, Nat.cast_one, div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have h2 : (1 / 4 : ℝ) ≤ (3 * ((m - 1 : ℕ) : ℝ) + 4) / (4 * m) := by
    rw [Nat.cast_sub hm, Nat.cast_one, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  exact lt_of_lt_of_le (by positivity) (bsplineConvIter_lower_interval hm (m - 1) (1 / 4) ⟨h1, h2⟩)

theorem bsplineUnit_lower_Icc {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ∈ Icc (1 / 4 : ℝ) (3 / 4)) :
    bsplineUnit m (1 / 4) ≤ bsplineUnit m t := by
  have hm0 : m ≠ 0 := by omega
  have hmono : MonotoneOn (bsplineUnit m) (Iic (1 / 2 : ℝ)) := by
    intro a ha b hb hab; simp only [bsplineUnit, hm0, ↓reduceIte]
    have hhalf : (((m - 1 + 1 : ℕ) : ℝ) / (2 * m)) = 1 / 2 := by rw [Nat.sub_add_cancel hm]; field_simp
    have hmon := bsplineConvIter_monotoneOn_half hm (m - 1); rw [hhalf] at hmon; exact hmon ha hb hab
  rcases le_or_gt t (1 / 2) with ht1 | ht1
  · exact hmono (mem_Iic.mpr (by norm_num)) (mem_Iic.mpr ht1) ht.1
  · rw [← bsplineUnit_symm m t]; exact hmono (mem_Iic.mpr (by norm_num)) (mem_Iic.mpr (by linarith)) (by linarith [ht.2])

lemma bspline_nonneg (m : ℕ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (t : ℝ) : 0 ≤ bspline m δ₀ t :=
  mul_nonneg (inv_nonneg.mpr hδ₀.le) (bsplineUnit_nonneg m _)

lemma bspline_le {m : ℕ} (hm : 1 ≤ m) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (t : ℝ) : bspline m δ₀ t ≤ m / δ₀ := by
  calc bspline m δ₀ t = δ₀⁻¹ * bsplineUnit m (t / δ₀) := rfl
    _ ≤ δ₀⁻¹ * m := mul_le_mul_of_nonneg_left (bsplineUnit_le_natCast hm _) (inv_nonneg.mpr hδ₀.le)
    _ = m / δ₀ := by ring

lemma bspline_aestronglyMeasurable (m : ℕ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) : AEStronglyMeasurable (bspline m δ₀) volume :=
  (((bsplineUnit_integrable m).comp_div hδ₀.ne').const_mul δ₀⁻¹).aestronglyMeasurable

lemma bspline_setIntegral_one {m : ℕ} (hm : 1 ≤ m) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) : ∫ t in Icc (0 : ℝ) δ₀, bspline m δ₀ t = 1 := by
  have hsub : (fun t => δ₀⁻¹ * bsplineUnit m (t / δ₀)) = fun t => δ₀⁻¹ * bsplineUnit m (δ₀⁻¹ * t) := by
    ext t; simp [div_eq_mul_inv, mul_comm]
  unfold bspline
  rw [hsub, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hδ₀.le,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left _ (inv_ne_zero hδ₀.ne'),
    mul_zero, inv_mul_cancel₀ hδ₀.ne', smul_eq_mul, inv_inv, ← mul_assoc, inv_mul_cancel₀ hδ₀.ne', one_mul,
    intervalIntegral.integral_of_le zero_le_one, ← MeasureTheory.integral_Icc_eq_integral_Ioc, bsplineUnit_setIntegral_one hm]

lemma bspline_lower_Icc {m : ℕ} (hm : 1 ≤ m) {δ₀ t : ℝ} (hδ₀ : 0 < δ₀) (ht : t ∈ Icc (δ₀ / 4) (3 * δ₀ / 4)) :
    bsplineUnit m (1 / 4) / δ₀ ≤ bspline m δ₀ t := by
  have hmem : t / δ₀ ∈ Icc (1 / 4 : ℝ) (3 / 4) := ⟨(le_div_iff₀ hδ₀).mpr (by linarith [ht.1]), (div_le_iff₀ hδ₀).mpr (by linarith [ht.2])⟩
  unfold bspline; rw [div_eq_inv_mul]; exact mul_le_mul_of_nonneg_left (bsplineUnit_lower_Icc hm hmem) (inv_nonneg.mpr hδ₀.le)

/-! ### Part 1B: Lemmas `O.0` (`u1co:O0`) and `O.1` (`u1co:O1`) + non-vacuity -/

/-- **Lemma `O.0` (`u1c_o1_upper.tex`, `u1co:O0`)**: B-spline averaging of an oscillating floor. -/
theorem bspline_oscillating_floor {m : ℕ} (hm : 1 ≤ m) {δ₀ x : ℝ}
    (hδ₀_pos : 0 < δ₀) (hδ₀_le : δ₀ ≤ 2) (hx : 3 ≤ x)
    {F : ℝ → ℝ} (hF_nn : ∀ y ∈ Icc (-x) (-x + δ₀), 0 ≤ F y)
    (hF_int : IntegrableOn (fun t => F (-x + t) * bspline m δ₀ t) (Icc 0 δ₀))
    {c_osc ϑ_c : ℝ} (hc_osc : 0 < c_osc) {r : ℝ → ℝ} {ρ : ℝ}
    (hF_osc : ∀ y ∈ Icc (x - 3 * δ₀ / 4) (x - δ₀ / 4),
      r y ^ 2 ≤ ρ ∧ c_osc * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + ϑ_c) + r y) ^ 2 ≤ F (-y))
    (hρ : ρ ≤ (64 * √2)⁻¹ * min (δ₀ ^ 2 * x / 8) 1) :
    (bsplineUnit m (1 / 4) * c_osc / (1024 * √2)) * x ^ (-(3 / 2 : ℝ)) * min 1 (δ₀ ^ 2 * x) ≤
      ∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t := by
  set bm := bsplineUnit m (1 / 4); have hbm_pos : 0 < bm := bsplineUnit_pos_one_quarter hm
  set ya := x - 3 * δ₀ / 4; set yb := x - δ₀ / 4
  have hyab : ya ≤ yb := by dsimp [ya, yb]; linarith
  have hya_ge : x / 2 ≤ ya := by dsimp [ya]; linarith
  have hya_pos : 0 < ya := by linarith
  have hx_pos : 0 < x := by linarith
  have hsub : Icc (δ₀ / 4) (3 * δ₀ / 4) ⊆ Icc 0 δ₀ := fun _ ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hstep1 : ∫ t in Icc (δ₀ / 4) (3 * δ₀ / 4), F (-x + t) * bspline m δ₀ t ≤
      ∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t :=
    setIntegral_mono_set hF_int (ae_restrict_of_forall_mem measurableSet_Icc fun t ht =>
      mul_nonneg (hF_nn (-x + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩) (bspline_nonneg m hδ₀_pos t))
      (Eventually.of_forall fun _ h => hsub h)
  set ϑ : ℝ → ℝ := fun y => (2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + ϑ_c
  set g : ℝ → ℝ := fun y => Real.cos (ϑ y) ^ 2 / 2 - ρ
  have hϑ_cont : ContinuousOn ϑ (Icc ya yb) :=
    (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id
      fun y hy => Or.inl (lt_of_lt_of_le hya_pos hy.1).ne')).add continuousOn_const
  have hcos_cont : ContinuousOn (fun y => Real.cos (ϑ y) ^ 2) (Icc ya yb) := (Real.continuous_cos.comp_continuousOn hϑ_cont).pow 2
  have hg_cont : ContinuousOn g (Icc ya yb) := (hcos_cont.div_const 2).sub continuousOn_const
  have h_ptwise : ∀ t ∈ Icc (δ₀ / 4) (3 * δ₀ / 4),
      (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * g (x - t) ≤ F (-x + t) * bspline m δ₀ t := by
    intro t ht
    have hy_mem : x - t ∈ Icc ya yb := ⟨by dsimp [ya]; linarith [ht.2], by dsimp [yb]; linarith [ht.1]⟩
    have hy_pos : 0 < x - t := lt_of_lt_of_le hya_pos hy_mem.1; obtain ⟨hr_bd, hF_bd⟩ := hF_osc (x - t) hy_mem
    have hpow : x ^ (-(3 / 2 : ℝ)) ≤ (x - t) ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hy_pos (by linarith [ht.1]) (by norm_num)
    have hcos_sq : g (x - t) ≤ (Real.cos (ϑ (x - t)) + r (x - t)) ^ 2 := by
      dsimp [g, ϑ]; nlinarith [sq_nonneg (Real.cos (ϑ (x - t)) + 2 * r (x - t))]
    have hF_low : c_osc * x ^ (-(3 / 2 : ℝ)) * g (x - t) ≤ F (-x + t) := by
      rw [show -x + t = -(x - t) by ring]; refine le_trans ?_ hF_bd
      rcases le_or_gt 0 (g (x - t)) with hg0 | hg0
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hpow hc_osc.le) hcos_sq hg0 (by positivity)
      · exact (mul_neg_of_pos_of_neg (by positivity) hg0).le.trans (by positivity)
    calc (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * g (x - t)
        = (c_osc * x ^ (-(3 / 2 : ℝ)) * g (x - t)) * (bm / δ₀) := by ring
      _ ≤ F (-x + t) * (bm / δ₀) := mul_le_mul_of_nonneg_right hF_low (by positivity)
      _ ≤ F (-x + t) * bspline m δ₀ t := mul_le_mul_of_nonneg_left (bspline_lower_Icc hm hδ₀_pos ht)
          (hF_nn (-x + t) ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hsub_int : IntegrableOn (fun t => (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * g (x - t)) (Icc (δ₀ / 4) (3 * δ₀ / 4)) :=
    (continuousOn_const.mul (hg_cont.comp (continuousOn_const.sub continuousOn_id) fun t ht =>
      ⟨by dsimp [ya]; linarith [ht.2], by dsimp [yb]; linarith [ht.1]⟩)).integrableOn_Icc
  have hstep2 : (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * ∫ y in Icc ya yb, g y ≤
      ∫ t in Icc (δ₀ / 4) (3 * δ₀ / 4), F (-x + t) * bspline m δ₀ t := by
    have hmono := setIntegral_mono_on hsub_int (hF_int.mono_set hsub) measurableSet_Icc h_ptwise
    refine le_trans (le_of_eq ?_) hmono; rw [integral_const_mul]; congr 1; rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    conv_rhs =>
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith : δ₀ / 4 ≤ 3 * δ₀ / 4),
        intervalIntegral.integral_comp_sub_left g x, show x - 3 * δ₀ / 4 = ya from rfl, show x - δ₀ / 4 = yb from rfl,
        intervalIntegral.integral_of_le hyab]
  have hϑ_deriv : ∀ y ∈ uIcc ya yb, HasDerivAt ϑ (√y) y := fun y hy => by
    have hy' : 0 < y := lt_of_lt_of_le hya_pos (by rcases Set.mem_uIcc.mp hy with h | h <;> linarith [h.1])
    refine (((Real.hasDerivAt_rpow_const (Or.inl hy'.ne')).const_mul (2 / 3 : ℝ)).add_const ϑ_c).congr_deriv ?_
    rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by norm_num, Real.sqrt_eq_rpow]; ring
  have hsqrt_cont : ContinuousOn (fun y : ℝ => √y) (uIcc ya yb) := by fun_prop
  have husub : ∫ y in ya..yb, Real.cos (ϑ y) ^ 2 * √y = ∫ θ in ϑ ya..ϑ yb, Real.cos θ ^ 2 :=
    intervalIntegral.integral_comp_mul_deriv hϑ_deriv hsqrt_cont (by fun_prop : Continuous fun θ : ℝ => Real.cos θ ^ 2)
  set L : ℝ := ϑ yb - ϑ ya
  have hL_ge : (δ₀ / 2) * √(x / 2) ≤ L := by
    rw [show L = ∫ y in ya..yb, √y from (intervalIntegral.integral_eq_sub_of_hasDerivAt hϑ_deriv hsqrt_cont.intervalIntegrable).symm,
      show (δ₀ / 2) * √(x / 2) = ∫ _y in ya..yb, √(x / 2) by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]; dsimp [ya, yb]; ring_nf]
    exact intervalIntegral.integral_mono_on hyab intervalIntegrable_const hsqrt_cont.intervalIntegrable
      fun y hy => Real.sqrt_le_sqrt (hya_ge.trans hy.1)
  have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_ge
  have hcos_vartheta : (L / 16) * min (L ^ 2) 1 ≤ ∫ θ in ϑ ya..ϑ yb, Real.cos θ ^ 2 := by
    have hsg := integral_cos_sq_ge (ϑ ya) hL_pos
    rwa [show ϑ ya + L = ϑ yb by dsimp [L]; ring, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : ϑ ya ≤ ϑ yb)] at hsg
  have hcos_int : IntervalIntegrable (fun y => Real.cos (ϑ y) ^ 2) volume ya yb :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyab).mpr hcos_cont.integrableOn_Icc
  have hcos_sqrt_int : IntervalIntegrable (fun y => Real.cos (ϑ y) ^ 2 * √y) volume ya yb :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hyab).mpr (hcos_cont.mul (hsqrt_cont.mono (uIcc_of_le hyab).symm.subset)).integrableOn_Icc
  have hmul_le : ∫ y in ya..yb, Real.cos (ϑ y) ^ 2 * √y ≤ √x * ∫ y in ya..yb, Real.cos (ϑ y) ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hyab hcos_sqrt_int (hcos_int.const_mul √x) fun y hy => ?_
    rw [mul_comm √x]; exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hy.2.trans (by dsimp [yb]; linarith))) (sq_nonneg _)
  set L₀ : ℝ := (δ₀ / 2) * √(x / 2)
  have hL₀_sq : L₀ ^ 2 = δ₀ ^ 2 * x / 8 := by dsimp [L₀]; rw [mul_pow, div_pow, Real.sq_sqrt (by positivity)]; ring
  have hL₀_min : (L₀ / 16) * min (L₀ ^ 2) 1 ≤ (L / 16) * min (L ^ 2) 1 := mul_le_mul (by linarith)
    (le_min ((min_le_left _ _).trans (pow_le_pow_left₀ (by positivity) hL_ge 2)) (min_le_right _ _)) (by positivity) (by positivity)
  have hcos_J_ge : (δ₀ / (32 * √2)) * min (δ₀ ^ 2 * x / 8) 1 ≤ ∫ y in Icc ya yb, Real.cos (ϑ y) ^ 2 := by
    have hlow_sqrt : (δ₀ / (32 * √2)) * min (δ₀ ^ 2 * x / 8) 1 ≤ (√x)⁻¹ * ((L₀ / 16) * min (L₀ ^ 2) 1) := by
      have hmin_nn : 0 ≤ min (δ₀ ^ 2 * x / 8) 1 := le_min (by positivity) zero_le_one
      rw [hL₀_sq, ← mul_assoc]; refine mul_le_mul_of_nonneg_right (le_of_eq ?_) hmin_nn
      dsimp [L₀]; rw [Real.sqrt_div hx_pos.le (2 : ℝ)]; field_simp; norm_num
    have hstep_div : (√x)⁻¹ * ((L / 16) * min (L ^ 2) 1) ≤ ∫ y in ya..yb, Real.cos (ϑ y) ^ 2 := by
      rw [inv_mul_le_iff₀ (Real.sqrt_pos.mpr hx_pos)]; exact hcos_vartheta.trans (husub.symm.trans_le hmul_le)
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hyab]
    exact hlow_sqrt.trans ((mul_le_mul_of_nonneg_left hL₀_min (by positivity)).trans hstep_div)
  have hg_int_val : ∫ y in Icc ya yb, g y = (∫ y in Icc ya yb, Real.cos (ϑ y) ^ 2) / 2 - ρ * (δ₀ / 2) := by
    rw [show g = fun y => Real.cos (ϑ y) ^ 2 / 2 - ρ by rfl,
      integral_sub (hcos_cont.div_const 2).integrableOn_Icc (integrableOn_const (hs := measure_Icc_lt_top.ne)),
      integral_div, setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), show yb - ya = δ₀ / 2 by dsimp [ya, yb]; ring, mul_comm]
  have hρ_int : ρ * (δ₀ / 2) ≤ (δ₀ / (128 * √2)) * min (δ₀ ^ 2 * x / 8) 1 :=
    (mul_le_mul_of_nonneg_right hρ (by positivity)).trans_eq (by ring)
  have hg_ge : (δ₀ / (128 * √2)) * min (δ₀ ^ 2 * x / 8) 1 ≤ ∫ y in Icc ya yb, g y := by
    rw [hg_int_val]
    calc (δ₀ / (128 * √2)) * min (δ₀ ^ 2 * x / 8) 1
        = ((δ₀ / (32 * √2)) * min (δ₀ ^ 2 * x / 8) 1) / 2 - (δ₀ / (128 * √2)) * min (δ₀ ^ 2 * x / 8) 1 := by ring
      _ ≤ (∫ y in Icc ya yb, Real.cos (ϑ y) ^ 2) / 2 - ρ * (δ₀ / 2) := by gcongr
  have hmin_scale : (1 / 8 : ℝ) * min 1 (δ₀ ^ 2 * x) ≤ min (δ₀ ^ 2 * x / 8) 1 := by
    rcases le_or_gt (δ₀ ^ 2 * x / 8) 1 with h | h
    · rw [min_eq_left h]; exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans_eq (by ring)
    · rw [min_eq_right h.le]; exact (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)).trans (by norm_num)
  have hfinal : (bm * c_osc / (1024 * √2)) * x ^ (-(3 / 2 : ℝ)) * min 1 (δ₀ ^ 2 * x) ≤
      (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * ∫ y in Icc ya yb, g y := by
    calc (bm * c_osc / (1024 * √2)) * x ^ (-(3 / 2 : ℝ)) * min 1 (δ₀ ^ 2 * x)
        = (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * ((δ₀ / (128 * √2)) * ((1 / 8 : ℝ) * min 1 (δ₀ ^ 2 * x))) := by field_simp; ring
      _ ≤ (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * ((δ₀ / (128 * √2)) * min (δ₀ ^ 2 * x / 8) 1) := by gcongr
      _ ≤ (bm * c_osc / δ₀) * x ^ (-(3 / 2 : ℝ)) * ∫ y in Icc ya yb, g y := mul_le_mul_of_nonneg_left hg_ge (by positivity)
  exact hfinal.trans (hstep2.trans hstep1)

/-- Scaling constant `β₁ = (π² √3)^{2/3}` (`sign_uncertainty_core.tex`, `u1c_o1_upper.tex`). -/
noncomputable def ceBeta1 : ℝ := (π ^ 2 * √3) ^ (2 / 3 : ℝ)

lemma ceBeta1_pos : 0 < ceBeta1 := by unfold ceBeta1; positivity

lemma ceBeta1_lt_eight : ceBeta1 < 8 := by
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hsq : (π ^ 2 * √3) ^ 2 = π ^ 4 * 3 := by rw [mul_pow, ← pow_mul, Real.sq_sqrt (by norm_num)]
  have hpow3 : ceBeta1 ^ 3 = π ^ 4 * 3 := by
    unfold ceBeta1; rw [← Real.rpow_natCast _ 3, ← Real.rpow_mul (by positivity)]; norm_num; exact hsq
  have h4 : π ^ 4 < (3.15 : ℝ) ^ 4 := pow_lt_pow_left₀ hpi Real.pi_pos.le (by norm_num)
  exact lt_of_pow_lt_pow_left₀ 3 (by norm_num) (by rw [hpow3]; norm_num at h4 ⊢; linarith)

/-- **Hypothesis (H)** constants (`u1c_o1_upper.tex` lines 330–334), independent of `δ`. -/
structure OscFloorSeedData where
  c_lin : ℝ
  c_osc : ℝ
  C_r : ℝ
  y₁ : ℝ
  ϑ_c : ℝ
  c_lin_pos : 0 < c_lin
  c_osc_pos : 0 < c_osc
  C_r_nonneg : 0 ≤ C_r
  y₁_ge : 25 ≤ y₁

/-- **Hypothesis (H)** on a seed `F` at parameter `δ ∈ (0, 1/2]` and threshold `u₀ < 0`. -/
structure SatisfiesH (D : OscFloorSeedData) (F : ℝ → ℝ) (δ u₀ : ℝ) : Prop where
  u₀_neg : u₀ < 0
  locallyIntegrable : LocallyIntegrable F volume
  lin_floor : ∀ y ≥ |u₀|, D.c_lin * δ * (1 + y) ^ (-(3 / 2 : ℝ)) ≤ F (-y)
  osc_floor : ∃ r : ℝ → ℝ, ∀ y ≥ D.y₁,
    |r y| ≤ D.C_r * y ^ (-(1 / 2 : ℝ)) ∧
      D.c_osc * y ^ (-(3 / 2 : ℝ)) * (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + D.ϑ_c) + r y) ^ 2 ≤ F (-y)

private lemma integrableOn_shift_bspline {m : ℕ} (hm : 1 ≤ m) {δ₀ x : ℝ} (hδ₀ : 0 < δ₀)
    {F : ℝ → ℝ} (hF : LocallyIntegrable F volume) : IntegrableOn (fun t => F (-x + t) * bspline m δ₀ t) (Icc 0 δ₀) := by
  have h1 : Integrable ((Icc (-x) (-x + δ₀)).indicator F) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (hF.integrableOn_isCompact isCompact_Icc)
  have h2 : Integrable ((Icc (0 : ℝ) δ₀).indicator (fun t => F (-x + t))) := by
    refine (h1.comp_add_left (-x)).congr (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Icc (0 : ℝ) δ₀
    · have ht' : -x + t ∈ Icc (-x) (-x + δ₀) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      simp only [Set.indicator_of_mem ht, Set.indicator_of_mem ht']
    · have ht' : -x + t ∉ Icc (-x) (-x + δ₀) := fun h => ht ⟨by linarith [h.1], by linarith [h.2]⟩
      simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  have hhm : IntegrableOn (fun t => bspline m δ₀ t * F (-x + t)) (Icc 0 δ₀) :=
    ((integrable_indicator_iff measurableSet_Icc).mp h2).bdd_mul (bspline_aestronglyMeasurable m hδ₀).restrict
      (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_of_nonneg (bspline_nonneg m hδ₀ t)]; exact bspline_le hm hδ₀ t)
  exact hhm.congr_fun (fun _ _ => mul_comm _ _) measurableSet_Icc

/-- **Lemma `O.1` (`u1c_o1_upper.tex`, `u1co:O1`, `(e2)`)**: floor with smoothing gain. -/
theorem bspline_floor_smoothing_gain {m : ℕ} (hm : 1 ≤ m) (D : OscFloorSeedData) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ (F : ℝ → ℝ) (δ u₀ : ℝ), 0 < δ → δ ≤ 1 / 2 → SatisfiesH D F δ u₀ →
      ∀ x ≥ |u₀| + ceBeta1 * δ / 2,
        (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
          ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F (-x + t) * bspline m (ceBeta1 * δ / 2) t := by
  set X_star : ℝ := max (2 * D.y₁ + 4) (max (256 * √2 * D.C_r ^ 2) (32 * (2 : ℝ) ^ (1 / 4 : ℝ) * D.C_r))
  have hX_y₁ : 2 * D.y₁ + 4 ≤ X_star := le_max_left _ _
  have hX_Cr2 : 256 * √2 * D.C_r ^ 2 ≤ X_star := (le_max_left _ _).trans (le_max_right _ _)
  have hX_Cr : 32 * (2 : ℝ) ^ (1 / 4 : ℝ) * D.C_r ≤ X_star := (le_max_right _ _).trans (le_max_right _ _)
  have hX_pos : 0 < X_star := by linarith [D.y₁_ge]
  set bm := bsplineUnit m (1 / 4); have hbm_pos : 0 < bm := bsplineUnit_pos_one_quarter hm
  set c₁ : ℝ := D.c_lin / 2; set c₂ : ℝ := min (D.c_lin / (ceBeta1 * X_star)) (bm * D.c_osc / (2048 * √2))
  have hc₁_pos : 0 < c₁ := half_pos D.c_lin_pos
  have hc₂_pos : 0 < c₂ := lt_min (div_pos D.c_lin_pos (mul_pos ceBeta1_pos hX_pos)) (div_pos (mul_pos hbm_pos D.c_osc_pos) (by positivity))
  refine ⟨c₁, hc₁_pos, c₂, hc₂_pos, fun F δ u₀ hδ_pos hδ_le hH x hx => ?_⟩
  set δ₀ : ℝ := ceBeta1 * δ / 2; have hδ₀_pos : 0 < δ₀ := by dsimp [δ₀]; positivity [ceBeta1_pos]
  have hδ₀_le : δ₀ ≤ 2 := by have := ceBeta1_lt_eight; dsimp [δ₀]; nlinarith
  have hx_nonneg : 0 ≤ x := by linarith [abs_nonneg u₀]
  have hmin_nn : 0 ≤ min 1 (δ₀ ^ 2 * x) := le_min zero_le_one (by positivity)
  have hF_int : IntegrableOn (fun t => F (-x + t) * bspline m δ₀ t) (Icc 0 δ₀) := integrableOn_shift_bspline hm hδ₀_pos hH.locallyIntegrable
  have hF_nn : ∀ y ∈ Icc (-x) (-x + δ₀), 0 ≤ F y := fun y hy => by
    have hlow := hH.lin_floor (-y) (by linarith [hy.2]); rw [neg_neg] at hlow
    exact le_trans (mul_nonneg (mul_nonneg D.c_lin_pos.le hδ_pos.le) (Real.rpow_nonneg (by linarith [hy.2, abs_nonneg u₀]) _)) hlow
  have hlin_avg : D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ)) ≤ ∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t := by
    rw [show D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ)) =
        ∫ t in Icc (0 : ℝ) δ₀, (D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ))) * bspline m δ₀ t by
      rw [integral_const_mul, bspline_setIntegral_one hm hδ₀_pos, mul_one]]
    have h_l_int : IntegrableOn (fun t => (D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ))) * bspline m δ₀ t) (Icc 0 δ₀) :=
      IntegrableOn.of_bound measure_Icc_lt_top ((bspline_aestronglyMeasurable m hδ₀_pos).const_mul _).restrict
        (|D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ))| * (m / δ₀))
        (Eventually.of_forall fun t => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (bspline_nonneg m hδ₀_pos t)]
                                          exact mul_le_mul_of_nonneg_left (bspline_le hm hδ₀_pos t) (abs_nonneg _))
    refine setIntegral_mono_on h_l_int hF_int measurableSet_Icc fun t ht => mul_le_mul_of_nonneg_right ?_ (bspline_nonneg m hδ₀_pos t)
    have hpow : (1 + x) ^ (-(3 / 2 : ℝ)) ≤ (1 + (x - t)) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [ht.2, abs_nonneg u₀]) (by linarith [ht.1]) (by norm_num)
    have hlow := hH.lin_floor (x - t) (by linarith [ht.2]); rw [show -(x - t) = -x + t by ring] at hlow
    exact (mul_le_mul_of_nonneg_left hpow (mul_nonneg D.c_lin_pos.le hδ_pos.le)).trans hlow
  by_cases hcase : x < X_star / δ₀
  · have hmin : min 1 (δ₀ ^ 2 * x) ≤ X_star * δ₀ := (min_le_right 1 _).trans (by have := (lt_div_iff₀' hδ₀_pos).mp hcase; nlinarith [hδ₀_pos.le])
    have hc₂_bd : c₂ * min 1 (δ₀ ^ 2 * x) ≤ (D.c_lin / 2) * δ := by
      calc c₂ * min 1 (δ₀ ^ 2 * x) ≤ (D.c_lin / (ceBeta1 * X_star)) * (X_star * δ₀) :=
            mul_le_mul (min_le_left _ _) hmin hmin_nn (div_pos D.c_lin_pos (mul_pos ceBeta1_pos hX_pos)).le
        _ = (D.c_lin / 2) * δ := by dsimp [δ₀]; field_simp [ceBeta1_pos.ne', hX_pos.ne']
    have hx_1x_nn : 0 ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 (δ₀ ^ 2 * x))
        ≤ (1 + x) ^ (-(3 / 2 : ℝ)) * ((D.c_lin / 2) * δ + (D.c_lin / 2) * δ) := by dsimp [c₁]; exact mul_le_mul_of_nonneg_left (by linarith) hx_1x_nn
      _ = D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ ∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t := hlin_avg
  · have hx_ge : X_star / δ₀ ≤ x := le_of_not_gt hcase
    have hx_ge_half : X_star / 2 ≤ x := le_trans (div_le_div_of_nonneg_left hX_pos.le hδ₀_pos hδ₀_le) hx_ge
    have hx3 : 3 ≤ x := by linarith [D.y₁_ge]
    obtain ⟨r, hr⟩ := hH.osc_floor; set ρ : ℝ := 2 * D.C_r ^ 2 / x
    have hCr_sq : 1024 * √2 * D.C_r ^ 2 ≤ X_star ^ 2 := by
      have hsq : (32 * (2 : ℝ) ^ (1 / 4 : ℝ) * D.C_r) ^ 2 ≤ X_star ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (by positivity) D.C_r_nonneg) hX_Cr 2
      have h2half : ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 = √2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_eq_rpow]; norm_num
      nlinarith [h2half, show (32 * (2 : ℝ) ^ (1 / 4 : ℝ) * D.C_r) ^ 2 = 1024 * ((2 : ℝ) ^ (1 / 4 : ℝ)) ^ 2 * D.C_r ^ 2 by ring]
    have hx_pos : 0 < x := by linarith
    have hρ_bd : ρ ≤ (64 * √2)⁻¹ * min (δ₀ ^ 2 * x / 8) 1 := by
      rw [mul_comm, le_mul_inv_iff₀ (by positivity)]; refine le_min ?_ ?_
      · have hx2 : X_star ^ 2 ≤ δ₀ ^ 2 * x ^ 2 := by
          have := (div_le_iff₀' hδ₀_pos).mp hx_ge; nlinarith [hX_pos.le, mul_nonneg hδ₀_pos.le hx_pos.le]
        dsimp [ρ]; rw [div_mul_eq_mul_div, div_le_div_iff₀ hx_pos (by norm_num)]
        nlinarith [mul_le_mul_of_nonneg_right hCr_sq hx_pos.le, mul_le_mul_of_nonneg_left hx2 (sq_nonneg D.C_r)]
      · dsimp [ρ]; rw [div_mul_eq_mul_div, div_le_one hx_pos]; nlinarith [hX_Cr2, hx_ge_half, Real.sqrt_nonneg 2, sq_nonneg D.C_r]
    have hJ_osc : ∀ y ∈ Icc (x - 3 * δ₀ / 4) (x - δ₀ / 4), r y ^ 2 ≤ ρ ∧ D.c_osc * y ^ (-(3 / 2 : ℝ)) *
        (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ) + D.ϑ_c) + r y) ^ 2 ≤ F (-y) := fun y hy => by
      have hy_pos : 0 < y := by linarith [D.y₁_ge, hy.1]
      obtain ⟨hr_y, hF_y⟩ := hr y (by linarith [hy.1])
      refine ⟨?_, hF_y⟩
      have hsq : r y ^ 2 ≤ (D.C_r * y ^ (-(1 / 2 : ℝ))) ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr_y 2
      have hy_inv : (y ^ (-(1 / 2 : ℝ))) ^ 2 = y⁻¹ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hy_pos.le]; norm_num; rw [Real.rpow_neg_one]
      rw [mul_pow, hy_inv, ← div_eq_mul_inv] at hsq
      exact hsq.trans (by dsimp [ρ]; rw [div_le_div_iff₀ hy_pos hx_pos]; nlinarith [sq_nonneg D.C_r, hy.1])
    have hO0 := bspline_oscillating_floor hm hδ₀_pos hδ₀_le hx3 hF_nn hF_int D.c_osc_pos hJ_osc hρ_bd
    have hpow_1x : (1 + x) ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) := Real.rpow_le_rpow_of_nonpos hx_pos (by linarith) (by norm_num)
    have hO0_1x : (bm * D.c_osc / (1024 * √2)) * (1 + x) ^ (-(3 / 2 : ℝ)) * min 1 (δ₀ ^ 2 * x) ≤
        ∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t :=
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow_1x (div_nonneg (mul_nonneg hbm_pos.le D.c_osc_pos.le) (by positivity))) hmin_nn).trans hO0
    have h1x_nn : 0 ≤ (1 + x) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    have h2m : (1 + x) ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (δ₀ ^ 2 * x)) ≤
        ((bm * D.c_osc / (1024 * √2)) * (1 + x) ^ (-(3 / 2 : ℝ)) * min 1 (δ₀ ^ 2 * x)) / 2 :=
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (min_le_right _ _) hmin_nn) h1x_nn).trans_eq (by ring)
    calc (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 (δ₀ ^ 2 * x))
        = (D.c_lin * δ * (1 + x) ^ (-(3 / 2 : ℝ))) / 2 + (1 + x) ^ (-(3 / 2 : ℝ)) * (c₂ * min 1 (δ₀ ^ 2 * x)) := by dsimp [c₁]; ring
      _ ≤ (∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t) / 2 +
            (∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t) / 2 := by linarith [hlin_avg, hO0_1x, h2m]
      _ = ∫ t in Icc (0 : ℝ) δ₀, F (-x + t) * bspline m δ₀ t := by ring

/-- Unconditional non-vacuity witness instantiating Hypothesis `(H)` and Lemma `O.1`. -/
theorem oscFloorSeed_witness {m : ℕ} (hm : 1 ≤ m) :
    ∃ D : OscFloorSeedData, ∃ F : ℝ → ℝ → ℝ, ∃ c₁ > 0, ∃ c₂ > 0,
      (∀ δ ∈ Ioc (0 : ℝ) (1 / 2), SatisfiesH D (F δ) δ (-1)) ∧
      ∀ δ ∈ Ioc (0 : ℝ) (1 / 2), ∀ x ≥ 1 + ceBeta1 * δ / 2,
        (1 + x) ^ (-(3 / 2 : ℝ)) * (c₁ * δ + c₂ * min 1 ((ceBeta1 * δ / 2) ^ 2 * x)) ≤
          ∫ t in Icc (0 : ℝ) (ceBeta1 * δ / 2), F δ (-x + t) * bspline m (ceBeta1 * δ / 2) t := by
  let D : OscFloorSeedData := ⟨1, 1 / 2, 0, 25, 0, one_pos, by norm_num, le_rfl, le_rfl⟩
  let F : ℝ → ℝ → ℝ := fun δ u => ((Real.cos ((2 / 3 : ℝ) * (max (-u) 0) ^ (3 / 2 : ℝ))) ^ 2 + δ) * (1 + |u|) ^ (-(3 / 2 : ℝ))
  obtain ⟨c₁, hc₁, c₂, hc₂, hgain⟩ := bspline_floor_smoothing_gain hm D
  have hsat : ∀ δ ∈ Ioc (0 : ℝ) (1 / 2), SatisfiesH D (F δ) δ (-1) := fun δ hδ => by
    have hcont : Continuous (F δ) := Continuous.mul
      ((Real.continuous_cos.comp (continuous_const.mul ((continuous_id.neg.max continuous_const).rpow_const fun _ => Or.inr (by norm_num)))).pow 2 |>.add continuous_const)
      ((continuous_const.add continuous_abs).rpow_const fun u => Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg u)).ne')
    refine ⟨by norm_num, hcont.locallyIntegrable, ?_, ⟨fun _ => 0, ?_⟩⟩
    · intro y hy; have hy_pos : 0 ≤ y := le_trans (abs_nonneg _) hy
      dsimp [D, F]; rw [abs_neg, abs_of_nonneg hy_pos, neg_neg, one_mul]
      exact mul_le_mul_of_nonneg_right (by linarith [sq_nonneg (Real.cos ((2 / 3 : ℝ) * (max y 0) ^ (3 / 2 : ℝ)))]) (Real.rpow_nonneg (by linarith) _)
    · intro y hy; have hy_pos : 0 < y := by dsimp [D] at hy; linarith
      refine ⟨by simp [D], ?_⟩; dsimp [D, F]; simp only [add_zero]
      rw [neg_neg, max_eq_left hy_pos.le, abs_neg, abs_of_nonneg hy_pos.le]
      have h23 : (26 / 25 : ℝ) ≤ 2 ^ (2 / 3 : ℝ) := by
        refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) (by positivity) ?_
        rw [← Real.rpow_natCast ((2 : ℝ) ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul (by norm_num)]; norm_num
      have h1y : 1 + y ≤ 2 ^ (2 / 3 : ℝ) * y :=
        (by dsimp [D] at hy; linarith : 1 + y ≤ (26 / 25 : ℝ) * y).trans (mul_le_mul_of_nonneg_right h23 hy_pos.le)
      have hpow : (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) ≤ (1 + y) ^ (-(3 / 2 : ℝ)) := by
        have hle := Real.rpow_le_rpow_of_nonpos (by positivity) h1y (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
        rw [Real.mul_rpow (by positivity) hy_pos.le, ← Real.rpow_mul (by norm_num)] at hle; norm_num at hle; exact hle
      calc (1 / 2 : ℝ) * y ^ (-(3 / 2 : ℝ)) * Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ)) ^ 2
          ≤ (1 + y) ^ (-(3 / 2 : ℝ)) * Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ)) ^ 2 := by gcongr
        _ ≤ (Real.cos ((2 / 3 : ℝ) * y ^ (3 / 2 : ℝ)) ^ 2 + δ) * (1 + y) ^ (-(3 / 2 : ℝ)) := by
            rw [mul_comm]; exact mul_le_mul_of_nonneg_right (by linarith [hδ.1]) (Real.rpow_nonneg (by linarith) _)
  exact ⟨D, F, c₁, hc₁, c₂, hc₂, hsat, fun δ hδ x hx => hgain (F δ) δ (-1) hδ.1 hδ.2 (hsat δ hδ) x (by simpa using hx)⟩

/-! ### Part 2A: Airy Riccati monotonicity (`cepe:PE1`) -/

/-- Logarithmic derivative `r(z) = Ai'(z) / Ai(z)`. -/
noncomputable def airyLogDeriv (z : ℝ) : ℝ := cohnM z

/-- Airy ratio `g_z(t) = Ai(z + t) / Ai(z)`. -/
noncomputable def airyRatio (z t : ℝ) : ℝ := airyAi (z + t) / airyAi z

lemma airyAi_pos_of_gt {z : ℝ} (hz : airyZero 1 < z) : 0 < airyAi z := airyAi_pos_of_gt_first hz

theorem hasDerivAt_airyLogDeriv {z : ℝ} (hz : airyZero 1 < z) :
    HasDerivAt airyLogDeriv (z - airyLogDeriv z ^ 2) z := cohnM_hasDerivAt (airyAi_ne_zero_of_gt hz)

theorem airyAiSq_integrableOn_Ioi (z : ℝ) : IntegrableOn (fun u => airyAi u ^ 2) (Ioi z) := integrableOn_Ioi_airyAi_sq z

theorem airyLogDeriv_deriv_eq_neg_integral {z : ℝ} (hz : airyZero 1 < z) :
    z - airyLogDeriv z ^ 2 = -(∫ u in Ioi z, airyAi u ^ 2) / airyAi z ^ 2 ∧ z - airyLogDeriv z ^ 2 < 0 := by
  have hAi_pos : 0 < airyAi z := airyAi_pos_of_gt hz
  have heq : z - airyLogDeriv z ^ 2 = -(∫ u in Ioi z, airyAi u ^ 2) / airyAi z ^ 2 := by
    rw [integral_Ioi_airyAi_sq z]; unfold airyLogDeriv cohnM; field_simp; ring
  have hpos_int : 0 < ∫ u in Ioi z, airyAi u ^ 2 := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall fun _ => sq_nonneg _) (airyAiSq_integrableOn_Ioi z)]
    have hsub : Ioo (z + 1 / 2) (z + 3 / 2) ⊆ Function.support (fun u => airyAi u ^ 2) ∩ Ioi z :=
      fun u hu => ⟨fun h => (airyAi_pos_of_gt (by linarith [hu.1])).ne' (sq_eq_zero_iff.mp h),
        mem_Ioi.mpr (by linarith [hu.1])⟩
    exact (by rw [Real.volume_Ioo]; simp; norm_num : 0 < volume (Ioo (z + 1 / 2) (z + 3 / 2))).trans_le (measure_mono hsub)
  exact ⟨heq, by rw [heq]; exact div_neg_of_neg_of_pos (neg_neg_of_pos hpos_int) (sq_pos_of_pos hAi_pos)⟩

theorem airyLogDeriv_strictAntiOn : StrictAntiOn airyLogDeriv (Ioi (airyZero 1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi _)
    (fun z hz => (hasDerivAt_airyLogDeriv hz).continuousAt.continuousWithinAt) fun z hz => ?_
  rw [interior_Ioi] at hz; rw [(hasDerivAt_airyLogDeriv hz).deriv]; exact (airyLogDeriv_deriv_eq_neg_integral hz).2

lemma hasDerivAt_airyRatio_z {z t : ℝ} (hz : airyZero 1 < z) (hzt : airyZero 1 < z + t) :
    HasDerivAt (fun u => airyRatio u t) (airyRatio z t * (airyLogDeriv (z + t) - airyLogDeriv z)) z := by
  have h1 : HasDerivAt (fun u => airyAi (u + t)) (airyAi' (z + t)) z := by
    simpa [Function.comp_def] using (hasDerivAt_airyAi (z + t)).comp z ((hasDerivAt_id z).add_const t)
  refine (h1.div (hasDerivAt_airyAi z) (airyAi_ne_zero_of_gt hz)).congr_deriv ?_
  have hAz : airyAi z ≠ 0 := airyAi_ne_zero_of_gt hz; have hAzt : airyAi (z + t) ≠ 0 := airyAi_ne_zero_of_gt hzt
  simp only [airyRatio, airyLogDeriv, cohnM]; field_simp

theorem airyRatio_strictAntiOn {t : ℝ} (ht : 0 < t) : StrictAntiOn (fun z => airyRatio z t) (Ioi (airyZero 1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi _) ?_ fun z hz => ?_
  · intro z hz; exact (hasDerivAt_airyRatio_z (mem_Ioi.mp hz) (by linarith [mem_Ioi.mp hz])).continuousAt.continuousWithinAt
  · rw [interior_Ioi, mem_Ioi] at hz; rw [(hasDerivAt_airyRatio_z hz (by linarith)).deriv]
    exact mul_neg_of_pos_of_neg (div_pos (airyAi_pos_of_gt (by linarith)) (airyAi_pos_of_gt hz))
      (sub_neg.mpr (airyLogDeriv_strictAntiOn hz (by simp only [mem_Ioi]; linarith) (by linarith)))

theorem airyAi'_neg_of_nonneg {z : ℝ} (hz : 0 ≤ z) : airyAi' z < 0 := airyAi'_neg hz

theorem neg_airyLogDeriv_gt_sqrt {z : ℝ} (hz : 0 ≤ z) : √z < -airyLogDeriv z := by
  have hz1 : airyZero 1 < z := lt_of_lt_of_le (airyZero_neg 1) hz
  have hsq : √z ^ 2 < (-airyLogDeriv z) ^ 2 := by rw [Real.sq_sqrt hz, neg_sq]; linarith [(airyLogDeriv_deriv_eq_neg_integral hz1).2]
  exact lt_of_pow_lt_pow_left₀ 2 (neg_pos.mpr (div_neg_of_neg_of_pos (airyAi'_neg hz) (airyAi_pos hz))).le hsq

theorem airyRatio_le_exp {z : ℝ} (hz : 0 ≤ z) {t : ℝ} (ht : 0 ≤ t) : airyRatio z t ≤ Real.exp (-√z * t) := by
  set F : ℝ → ℝ := fun u => Real.exp (√z * u) * airyRatio z u
  have hF_deriv : ∀ u ≥ 0, HasDerivAt F (F u * (√z + airyLogDeriv (z + u))) u := fun u hu => by
    have h1 : HasDerivAt (fun s => Real.exp (√z * s)) (√z * Real.exp (√z * u)) u := by
      simpa [mul_comm] using ((hasDerivAt_id u).const_mul √z).exp
    have h2 : HasDerivAt (fun s => airyRatio z s) (airyAi' (z + u) / airyAi z) u := by
      have ha : HasDerivAt (fun s => airyAi (z + s)) (airyAi' (z + u)) u := by
        simpa [Function.comp_def] using (hasDerivAt_airyAi (z + u)).comp u ((hasDerivAt_id u).const_add z)
      simpa [airyRatio] using ha.div_const (airyAi z)
    have hAi_zu : airyAi (z + u) ≠ 0 := (airyAi_pos (by linarith)).ne'
    refine (h1.mul h2).congr_deriv ?_; dsimp [F, airyRatio, airyLogDeriv, cohnM]; field_simp
  have hF_anti : AntitoneOn F (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun u hu => (hF_deriv u hu).continuousAt.continuousWithinAt)
      (fun u hu => (hF_deriv u (interior_subset hu)).differentiableAt.differentiableWithinAt) fun u hu => ?_
    rw [interior_Ici, mem_Ioi] at hu; rw [(hF_deriv u hu.le).deriv]
    have hF_nn : 0 ≤ F u := mul_nonneg (Real.exp_pos _).le (div_nonneg (airyAi_pos (by linarith)).le (airyAi_pos hz).le)
    have h1 := neg_airyLogDeriv_gt_sqrt (by linarith : 0 ≤ z + u)
    exact mul_nonpos_of_nonneg_of_nonpos hF_nn (by linarith [Real.sqrt_le_sqrt (by linarith : z ≤ z + u)])
  have hFt : F t ≤ F 0 := hF_anti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  have hF0 : F 0 = 1 := by dsimp [F, airyRatio]; rw [mul_zero, Real.exp_zero, one_mul, add_zero, div_self (airyAi_pos hz).ne']
  rw [hF0] at hFt
  calc airyRatio z t = Real.exp (-(√z * t)) * F t := by dsimp [F]; rw [← mul_assoc, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]
    _ ≤ Real.exp (-(√z * t)) * 1 := mul_le_mul_of_nonneg_left hFt (Real.exp_pos _).le
    _ = Real.exp (-√z * t) := by rw [mul_one, neg_mul]

theorem neg_airyLogDeriv_le {z : ℝ} (hz : 0 < z) : -airyLogDeriv z ≤ √(z + 1 / (2 * √z)) := by
  have hz1 : airyZero 1 < z := (airyZero_neg 1).trans hz
  have hderiv := (airyLogDeriv_deriv_eq_neg_integral hz1).1; have hAi_pos : 0 < airyAi z := airyAi_pos hz.le
  have hrat_sq_int : IntegrableOn (fun u => (airyAi u / airyAi z) ^ 2) (Ioi z) :=
    ((airyAiSq_integrableOn_Ioi z).div_const (airyAi z ^ 2)).congr (Eventually.of_forall fun _ => by ring)
  have hrat_int : IntegrableOn (fun t : ℝ => airyRatio z t ^ 2) (Ioi 0) := by
    have h1 : Integrable ((Ioi z).indicator fun u => (airyAi u / airyAi z) ^ 2) :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hrat_sq_int
    refine (integrable_indicator_iff measurableSet_Ioi).mp ((h1.comp_add_left z).congr (Eventually.of_forall fun t => ?_))
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · have ht' : z + t ∈ Ioi z := by rw [mem_Ioi] at ht ⊢; linarith
      simp only [Set.indicator_of_mem ht, Set.indicator_of_mem ht', airyRatio, div_pow]
    · have ht' : z + t ∉ Ioi z := fun h => ht (by rw [mem_Ioi] at h ⊢; linarith)
      simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  have hint_eq : (∫ u in Ioi z, airyAi u ^ 2) / airyAi z ^ 2 = ∫ t in Ioi (0 : ℝ), airyRatio z t ^ 2 := by
    rw [← integral_div, show (fun u => airyAi u ^ 2 / airyAi z ^ 2) = fun u => (airyAi u / airyAi z) ^ 2 by ext; ring,
      ← integral_indicator measurableSet_Ioi, ← integral_add_left_eq_self _ z, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · have ht' : z + t ∈ Ioi z := by rw [mem_Ioi] at ht ⊢; linarith
      simp only [Set.indicator_of_mem ht, Set.indicator_of_mem ht', airyRatio, div_pow]
    · have ht' : z + t ∉ Ioi z := fun h => ht (by rw [mem_Ioi] at h ⊢; linarith)
      simp only [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht']
  rw [neg_div, hint_eq] at hderiv
  have hexp_int : IntegrableOn (fun t : ℝ => Real.exp (-(2 * √z) * t)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_neg_of_pos (by positivity)) 0
  have hint_le : ∫ t in Ioi (0 : ℝ), airyRatio z t ^ 2 ≤ 1 / (2 * √z) := by
    have hmono : ∫ t in Ioi (0 : ℝ), airyRatio z t ^ 2 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(2 * √z) * t) := by
      refine setIntegral_mono_on hrat_int hexp_int measurableSet_Ioi fun t ht => ?_
      calc airyRatio z t ^ 2 ≤ Real.exp (-√z * t) ^ 2 :=
            pow_le_pow_left₀ (div_nonneg (airyAi_pos (by linarith [mem_Ioi.mp ht])).le hAi_pos.le) (airyRatio_le_exp hz.le (le_of_lt ht)) 2
        _ = Real.exp (-(2 * √z) * t) := by rw [← Real.exp_nat_mul]; congr 1; ring
    have hexp_eval : ∫ t in Ioi (0 : ℝ), Real.exp (-(2 * √z) * t) = 1 / (2 * √z) := by
      rw [integral_exp_mul_Ioi (neg_neg_of_pos (by positivity)) 0, mul_zero, Real.exp_zero, neg_div_neg_eq, one_div]
    linarith
  have hneg : 0 ≤ -airyLogDeriv z := (neg_airyLogDeriv_gt_sqrt hz.le).le.trans' (Real.sqrt_nonneg z)
  rw [← Real.sqrt_sq hneg, neg_sq]; exact Real.sqrt_le_sqrt (by linarith)

/-! ### Part 2B: Two-scale Dirichlet floor (`cepe:dirichlet-floor`) -/

/-- Normalized first cardinal mode `φ₁(t) = Ai(a₁ + t) / Ai'(a₁)`. -/
noncomputable def airyPhi1 (t : ℝ) : ℝ := airyAi (airyZero 1 + t) / airyAi' (airyZero 1)

lemma airyPhi1_pos {t : ℝ} (ht : 0 < t) : 0 < airyPhi1 t := div_pos (airyAi_pos_of_gt (by linarith)) airyAi'_first_pos

/-- Smooth resolvent difference `(g_z(t) - g_a(t)) / (1 - q (a - a₁))` with removable value at `z = a = a₁'`. -/
noncomputable def dirichletResolventTerm (t z : ℝ) : ℝ := (z - airyZero 1) * dslope (fun u => airyRatio u t) airyDerivFirstZero z

theorem dirichletResolventTerm_eq_of_ne {t z : ℝ} (hz1 : z ≠ airyZero 1) (hza : z ≠ airyDerivFirstZero) :
    dirichletResolventTerm t z = (airyRatio z t - airyRatio airyDerivFirstZero t) /
        (1 - (z - airyZero 1)⁻¹ * (airyDerivFirstZero - airyZero 1)) := by
  have hz1' : z - airyZero 1 ≠ 0 := sub_ne_zero.mpr hz1; have hza' : z - airyDerivFirstZero ≠ 0 := sub_ne_zero.mpr hza
  have hden : 1 - (z - airyZero 1)⁻¹ * (airyDerivFirstZero - airyZero 1) = (z - airyDerivFirstZero) / (z - airyZero 1) := by field_simp; ring
  unfold dirichletResolventTerm; rw [dslope_of_ne _ hza, slope_def_field, hden]; field_simp

theorem dirichletResolventTerm_self (t : ℝ) :
    dirichletResolventTerm t airyDerivFirstZero =
      (airyDerivFirstZero - airyZero 1) * (airyAi' (airyDerivFirstZero + t) / airyAi airyDerivFirstZero) := by
  set a := airyDerivFirstZero; have haAi : airyAi a ≠ 0 := airyAi_ne_zero_of_gt airyDerivFirstZero_spec.1
  have h1 : HasDerivAt (fun u => airyAi (u + t)) (airyAi' (a + t)) a := by
    simpa [Function.comp_def] using (hasDerivAt_airyAi (a + t)).comp a ((hasDerivAt_id a).add_const t)
  have hd : HasDerivAt (fun u => airyRatio u t) (airyAi' (a + t) / airyAi a) a := by
    refine (h1.div (hasDerivAt_airyAi a) haAi).congr_deriv ?_
    rw [airyDerivFirstZero_spec.2.2, mul_zero, sub_zero, sq, mul_div_mul_right _ _ haAi]
  unfold dirichletResolventTerm; rw [dslope_same, hd.deriv]

lemma dirichletResolventTerm_continuousOn {t : ℝ} (ht : 0 ≤ t) : ContinuousOn (dirichletResolventTerm t) (Ioi (airyZero 1)) := by
  refine (continuousOn_id.sub continuousOn_const).mul ?_; rw [continuousOn_dslope (Ioi_mem_nhds airyDerivFirstZero_spec.1)]
  refine ⟨fun z hz => (hasDerivAt_airyRatio_z (mem_Ioi.mp hz) (by linarith [mem_Ioi.mp hz])).continuousAt.continuousWithinAt,
    (hasDerivAt_airyRatio_z airyDerivFirstZero_spec.1 (by linarith [airyDerivFirstZero_spec.1])).differentiableAt⟩

theorem dirichletResolventTerm_tendsto_self {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun z : ℝ => (airyRatio z t - airyRatio airyDerivFirstZero t) /
        (1 - (z - airyZero 1)⁻¹ * (airyDerivFirstZero - airyZero 1)))
      (𝓝[≠] airyDerivFirstZero) (𝓝 (dirichletResolventTerm t airyDerivFirstZero)) := by
  have ha1 := airyDerivFirstZero_spec.1
  refine ((dirichletResolventTerm_continuousOn ht).continuousAt (Ioi_mem_nhds ha1) |>.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev : ∀ᶠ z in 𝓝[≠] airyDerivFirstZero, z ≠ airyZero 1 ∧ z ≠ airyDerivFirstZero :=
    (Filter.Eventually.mono (nhdsWithin_le_nhds (Ioi_mem_nhds ha1)) fun _ hz => ne_of_gt hz).and self_mem_nhdsWithin
  filter_upwards [hev] with z ⟨hz1, hza⟩; exact dirichletResolventTerm_eq_of_ne hz1 hza

theorem dirichletResolventTerm_nonpos {t z : ℝ} (ht : 0 < t) (hz : airyZero 1 < z) : dirichletResolventTerm t z ≤ 0 := by
  set a := airyDerivFirstZero; have ha1 := airyDerivFirstZero_spec.1; have hz1_pos : 0 < z - airyZero 1 := sub_pos.mpr hz
  by_cases hza : z = a
  · subst hza; unfold dirichletResolventTerm; rw [dslope_same, (hasDerivAt_airyRatio_z ha1 (by linarith)).deriv]
    have hlog : airyLogDeriv (a + t) < airyLogDeriv a := airyLogDeriv_strictAntiOn ha1 (by simp only [mem_Ioi]; linarith) (by linarith)
    exact mul_nonpos_of_nonneg_of_nonpos hz1_pos.le (mul_nonpos_of_nonneg_of_nonpos
      (div_pos (airyAi_pos_of_gt (by linarith)) (airyAi_pos_of_gt ha1)).le (sub_nonpos.mpr hlog.le))
  · unfold dirichletResolventTerm; rw [dslope_of_ne _ hza, slope_def_field]; refine mul_nonpos_of_nonneg_of_nonpos hz1_pos.le ?_
    rcases lt_or_gt_of_ne hza with hlt | hgt
    · exact div_nonpos_of_nonneg_of_nonpos (sub_pos.mpr (airyRatio_strictAntiOn ht hz ha1 hlt)).le (sub_neg.mpr hlt).le
    · exact div_nonpos_of_nonpos_of_nonneg (sub_neg.mpr (airyRatio_strictAntiOn ht ha1 hz hgt)).le (sub_pos.mpr hgt).le

/-- Resolvent integrand as a function of `s ∈ (0, ∞)` with `q = s h`, `z = a₁ + q⁻¹`. -/
noncomputable def dirichletKernel (h t s : ℝ) : ℝ := dirichletResolventTerm t (airyZero 1 + (s * h)⁻¹)

lemma dirichletResolventTerm_boundedOn_Ioi {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Ioi (airyZero 1), |dirichletResolventTerm t z| ≤ M := by
  set a := airyDerivFirstZero; have ha1 : airyZero 1 < a := airyDerivFirstZero_spec.1
  set mid : ℝ := (airyZero 1 + a) / 2; have hmid1 : airyZero 1 < mid := by dsimp [mid]; linarith
  have hmida : mid < a := by dsimp [mid]; linarith
  obtain ⟨z_m, _, hz_m⟩ := (isCompact_Icc (a := mid) (b := a + 1)).exists_isMaxOn ⟨mid, ⟨le_rfl, by linarith⟩⟩
    (((dirichletResolventTerm_continuousOn ht.le).mono (fun z hz => by rw [mem_Ioi]; linarith [hz.1])).abs)
  set q : ℝ → ℝ := dslope airyAi (airyZero 1)
  have hq_cont : ContinuousOn q (Icc (airyZero 1) mid) := by
    refine ContinuousOn.mono ?_ (subset_univ _); rw [continuousOn_dslope univ_mem]
    exact ⟨continuous_airyAi.continuousOn, (hasDerivAt_airyAi (airyZero 1)).differentiableAt⟩
  obtain ⟨z_q, hz_q_mem, hz_q⟩ := (isCompact_Icc (a := airyZero 1) (b := mid)).exists_isMinOn ⟨airyZero 1, ⟨le_rfl, hmid1.le⟩⟩ hq_cont
  have hq_pos : 0 < q z_q := by
    rcases eq_or_lt_of_le hz_q_mem.1 with h0 | h0
    · rw [← h0]; dsimp [q]; rw [dslope_same, deriv_airyAi]; exact airyAi'_first_pos
    · dsimp [q]; rw [dslope_of_ne _ h0.ne', slope_def_field, airyAi_airyZero, sub_zero]; exact div_pos (airyAi_pos_of_gt h0) (sub_pos.mpr h0)
  obtain ⟨z_n, _, hz_n⟩ := (isCompact_Icc (a := airyZero 1) (b := mid)).exists_isMaxOn ⟨airyZero 1, ⟨le_rfl, hmid1.le⟩⟩
    ((continuous_airyAi.comp (continuous_id.add continuous_const)).abs.continuousOn)
  set M_mid : ℝ := |dirichletResolventTerm t z_m|; set M_hi : ℝ := (a + 1 - airyZero 1) * airyRatio a t
  set M_lo : ℝ := (2 / (a - airyZero 1)) * (|airyAi (z_n + t)| / q z_q + (mid - airyZero 1) * airyRatio a t)
  refine ⟨max M_mid (max M_hi M_lo), le_max_of_le_left (abs_nonneg _), fun z hz => ?_⟩
  have hz' : airyZero 1 < z := mem_Ioi.mp hz
  by_cases h1 : z ≤ mid
  · refine le_trans ?_ (le_max_of_le_right (le_max_right _ _))
    have hmem : z ∈ Icc (airyZero 1) mid := ⟨hz'.le, h1⟩
    have hqz : q z = airyAi z / (z - airyZero 1) := by dsimp [q]; rw [dslope_of_ne _ hz'.ne', slope_def_field, airyAi_airyZero, sub_zero]
    have hAi_pos : 0 < airyAi z := airyAi_pos_of_gt hz'
    have hinv_Ai : (z - airyZero 1) / airyAi z ≤ (q z_q)⁻¹ := by
      rw [← one_div, div_le_div_iff₀ hAi_pos hq_pos, one_mul]
      have hmul := mul_le_mul_of_nonneg_right (hz_q hmem) (sub_pos.mpr hz').le
      rw [hqz, div_mul_cancel₀ _ (sub_ne_zero.mpr hz'.ne')] at hmul; linarith
    have h1_bd : |(z - airyZero 1) * airyRatio z t| ≤ |airyAi (z_n + t)| / q z_q := by
      rw [show (z - airyZero 1) * airyRatio z t = airyAi (z + t) * ((z - airyZero 1) / airyAi z) by unfold airyRatio; ring,
        abs_mul, abs_of_nonneg (div_nonneg (sub_pos.mpr hz').le hAi_pos.le)]
      exact (mul_le_mul (hz_n hmem) hinv_Ai (div_nonneg (sub_pos.mpr hz').le hAi_pos.le) (abs_nonneg _)).trans_eq (div_eq_mul_inv _ _).symm
    have hrat_nn : 0 ≤ airyRatio a t := div_nonneg (airyAi_pos_of_gt (by linarith)).le (airyAi_pos_of_gt ha1).le
    have h2_bd : |(z - airyZero 1) * airyRatio a t| ≤ (mid - airyZero 1) * airyRatio a t := by
      rw [abs_of_nonneg (mul_nonneg (sub_pos.mpr hz').le hrat_nn)]; exact mul_le_mul_of_nonneg_right (by linarith) hrat_nn
    have hden_ge : (a - airyZero 1) / 2 ≤ |z - a| := by rw [abs_of_neg (by linarith)]; dsimp [mid] at h1; linarith
    have heq : dirichletResolventTerm t z = ((z - airyZero 1) * airyRatio z t - (z - airyZero 1) * airyRatio a t) / (z - a) := by
      unfold dirichletResolventTerm; rw [dslope_of_ne _ (by linarith : z ≠ a), slope_def_field]; ring
    rw [heq, abs_div]
    calc |(z - airyZero 1) * airyRatio z t - (z - airyZero 1) * airyRatio a t| / |z - a|
        ≤ (|airyAi (z_n + t)| / q z_q + (mid - airyZero 1) * airyRatio a t) / ((a - airyZero 1) / 2) :=
          div_le_div₀ (by positivity) ((abs_sub _ _).trans (add_le_add h1_bd h2_bd)) (by positivity) hden_ge
      _ = M_lo := by dsimp [M_lo]; field_simp [sub_ne_zero.mpr ha1.ne']
  · by_cases h2 : z ≤ a + 1
    · exact (hz_m ⟨by linarith, h2⟩).trans (le_max_left _ _)
    · refine le_trans ?_ (le_max_of_le_right (le_max_left _ _))
      have hrat_nn : 0 ≤ airyRatio a t := div_nonneg (airyAi_pos_of_gt (by linarith)).le (airyAi_pos_of_gt ha1).le
      have hnum : |airyRatio z t - airyRatio a t| ≤ airyRatio a t := by
        have hpos : 0 < airyRatio z t := div_pos (airyAi_pos_of_gt (by linarith)) (airyAi_pos_of_gt hz')
        rw [abs_of_neg (sub_neg.mpr (airyRatio_strictAntiOn ht ha1 hz' (by linarith)))]; linarith
      have hden : (a + 1 - airyZero 1)⁻¹ ≤ 1 - (z - airyZero 1)⁻¹ * (a - airyZero 1) := by
        have hz1_ne : z - airyZero 1 ≠ 0 := sub_ne_zero.mpr hz'.ne'
        have h1' : 1 - (z - airyZero 1)⁻¹ * (a - airyZero 1) = 1 - (a - airyZero 1) / (z - airyZero 1) := by field_simp
        have h3 : (a - airyZero 1) / (z - airyZero 1) ≤ (a - airyZero 1) / (a + 1 - airyZero 1) :=
          div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
        have h4 : 1 - (a - airyZero 1) / (a + 1 - airyZero 1) = (a + 1 - airyZero 1)⁻¹ := by
          field_simp [show a + 1 - airyZero 1 ≠ 0 by linarith]; ring
        linarith
      have hden_pos : 0 < 1 - (z - airyZero 1)⁻¹ * (a - airyZero 1) := lt_of_lt_of_le (inv_pos.mpr (by linarith)) hden
      rw [dirichletResolventTerm_eq_of_ne hz'.ne' (by linarith), abs_div, abs_of_pos hden_pos]
      exact (div_le_div₀ hrat_nn hnum (inv_pos.mpr (by linarith)) hden).trans_eq (by dsimp [M_hi]; rw [div_inv_eq_mul, mul_comm])

lemma dirichletKernel_integrableOn {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h t : ℝ} (hh : 0 < h) (ht : 0 < t) : IntegrableOn (dirichletKernel h t) (Ioi 0) μ := by
  obtain ⟨M, _, hM⟩ := dirichletResolventTerm_boundedOn_Ioi ht
  have hcont : ContinuousOn (dirichletKernel h t) (Ioi 0) :=
    (dirichletResolventTerm_continuousOn ht.le).comp
      (continuousOn_const.add ((continuousOn_id.mul continuousOn_const).inv₀ fun _ hs => mul_ne_zero (mem_Ioi.mp hs).ne' hh.ne'))
      fun _ hs => by rw [mem_Ioi] at hs ⊢; linarith [inv_pos.mpr (mul_pos hs hh)]
  refine IntegrableOn.of_bound ((measure_mono (subset_univ _)).trans_lt (by simp))
    (hcont.aestronglyMeasurable measurableSet_Ioi) M ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  rw [Real.norm_eq_abs]; exact hM _ (by rw [mem_Ioi]; linarith [inv_pos.mpr (mul_pos (mem_Ioi.mp hs) hh)])

/-- Two-scale Dirichlet mixture vector `v_c(t)` (`ce_o1_pre_edge.tex`, `cepe:PE1`). -/
noncomputable def dirichletVector (μ : Measure ℝ) (σ_c η_hat h t : ℝ) : ℝ :=
  σ_c * (∫ s in Ioi (0 : ℝ), dirichletKernel h t s ∂μ) - η_hat * airyPhi1 t

private lemma one_sub_exp_neg_half_ge (x : ℝ) (hx : 0 ≤ x) : (1 / 4 : ℝ) * min x 1 ≤ 1 - Real.exp (-(x / 2)) := by
  set u := x / 2; have hu_nn : 0 ≤ u := by dsimp [u]; positivity
  have h1e : (1 / 2 : ℝ) * min u 1 ≤ 1 - Real.exp (-u) := by
    rcases le_or_gt u 1 with hu1 | hu1
    · rw [min_eq_left hu1, Real.exp_neg]; have hpos : 0 < 1 + u := by linarith
      have he_inv := inv_anti₀ hpos (by linarith [Real.add_one_le_exp u] : 1 + u ≤ Real.exp u)
      have h1u : u / 2 + (1 + u)⁻¹ ≤ 1 := by
        have hmul : (u / 2 + (1 + u)⁻¹) * (1 + u) ≤ 1 * (1 + u) := by
          have : (u / 2 + (1 + u)⁻¹) * (1 + u) = u * (1 + u) / 2 + 1 := by field_simp
          nlinarith [sq_nonneg u, hu_nn]
        exact le_of_mul_le_mul_right hmul hpos
      linarith
    · rw [min_eq_right hu1.le, Real.exp_neg]
      have he_inv : (Real.exp u)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le two_pos (by linarith [Real.add_one_le_exp u])
      linarith
  have hmin_u : (1 / 4 : ℝ) * min x 1 ≤ (1 / 2 : ℝ) * min u 1 := by
    dsimp [u]; rcases le_or_gt x 1 with h1 | h1
    · rw [min_eq_left h1, min_eq_left (by linarith)]; linarith
    · rw [min_eq_right h1.le]; rcases le_or_gt (x / 2) 1 with h2 | h2
      · rw [min_eq_left h2]; linarith
      · rw [min_eq_right h2.le]; norm_num
  exact hmin_u.trans h1e

private lemma one_sub_airyRatio_a_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (0 : ℝ) 1, 1 - airyRatio airyDerivFirstZero t ≤ C * t ^ 2 := by
  set a := airyDerivFirstZero; have haAi_pos : 0 < airyAi a := airyAi_pos_of_gt airyDerivFirstZero_spec.1
  have hcont2 : ContinuousOn (fun u => |(a + u) * airyAi (a + u) / airyAi a|) (Icc (0 : ℝ) 1) :=
    ((continuous_const.add continuous_id).mul (continuous_airyAi.comp (continuous_const.add continuous_id)) |>.div_const _).abs.continuousOn
  obtain ⟨u_m, _, hu_m⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn ⟨0, ⟨le_rfl, zero_le_one⟩⟩ hcont2
  set C₀ : ℝ := |(a + u_m) * airyAi (a + u_m) / airyAi a|; set C : ℝ := max (C₀ / 2) 1
  refine ⟨C, lt_of_lt_of_le one_pos (le_max_right _ _), fun t ht => ?_⟩
  have hf'_deriv : ∀ s : ℝ, HasDerivAt (fun u => airyAi' (a + u) / airyAi a) ((a + s) * airyAi (a + s) / airyAi a) s :=
    fun s => by simpa [Function.comp_def] using ((hasDerivAt_airyAi' (a + s)).comp s ((hasDerivAt_id s).const_add a)).div_const (airyAi a)
  have hf'_bound : ∀ s ∈ Icc (0 : ℝ) 1, -(C₀ * s) ≤ airyAi' (a + s) / airyAi a := fun s hs => by
    have hm := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u => airyAi' (a + u) / airyAi a)
      (fun u _ => (hf'_deriv u).differentiableAt) (fun u hu => by rw [(hf'_deriv u).deriv, Real.norm_eq_abs]; exact hu_m hu)
      (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩ hs
    have h0 : airyAi' (a + 0) / airyAi a = 0 := by rw [add_zero, airyDerivFirstZero_spec.2.2, zero_div]
    rw [h0, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero, abs_of_nonneg hs.1] at hm; linarith [(abs_le.mp hm).1]
  set h_fun : ℝ → ℝ := fun s => C * s ^ 2 + airyRatio a s - 1
  have hh_deriv : ∀ s : ℝ, HasDerivAt h_fun (2 * C * s + airyAi' (a + s) / airyAi a) s := fun s => by
    have hd1 : HasDerivAt (fun u => C * u ^ 2) (2 * C * s) s := ((hasDerivAt_pow 2 s).const_mul C).congr_deriv (by ring)
    have hd2 : HasDerivAt (airyRatio a) (airyAi' (a + s) / airyAi a) s := by
      unfold airyRatio; simpa [Function.comp_def] using
        ((hasDerivAt_airyAi (a + s)).comp s ((hasDerivAt_id s).const_add a)).div_const (airyAi a)
    exact (hd1.add hd2).sub_const 1
  have hh_mono : MonotoneOn h_fun (Icc 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (fun s _ => (hh_deriv s).continuousAt.continuousWithinAt)
      (fun s _ => (hh_deriv s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Icc] at hs; rw [(hh_deriv s).deriv]
    nlinarith [hs.1, hf'_bound s ⟨hs.1.le, hs.2.le⟩, show C₀ ≤ 2 * C by dsimp [C]; linarith [le_max_left (C₀ / 2) 1]]
  have h0_eq : h_fun 0 = 0 := by dsimp [h_fun, airyRatio]; rw [add_zero, div_self haAi_pos.ne']; ring
  have hle := hh_mono ⟨le_rfl, zero_le_one⟩ ht ht.1; rw [h0_eq] at hle; dsimp [h_fun] at hle; linarith

/-- **Two-scale Dirichlet floor (`ce_o1_pre_edge.tex`, `(cepe:dirichlet-floor)`)**. -/
theorem dirichlet_two_scale_floor (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : 0 < μ (Icc (1 : ℝ) 2)) {σ_c η_hat : ℝ} (hσ : 1 / 2 ≤ σ_c) (hη : 0 ≤ η_hat) :
    ∃ b > 0, ∃ t₀ > 0, ∃ h₀ > 0, ∀ {h t : ℝ}, 0 < h → h ≤ h₀ → 0 < t → t ≤ t₀ →
      b * min (t / √h) 1 ≤ -dirichletVector μ σ_c η_hat h t := by
  set a := airyDerivFirstZero; have ha1 : airyZero 1 < a := airyDerivFirstZero_spec.1
  have ha_neg : a < 0 := airyDerivFirstZero_spec.2.1; have ha1_neg : airyZero 1 < 0 := airyZero_neg 1
  have ha1_abs_pos : 0 < |airyZero 1| := abs_pos.mpr ha1_neg.ne
  obtain ⟨C, hC_pos, hga_quad⟩ := one_sub_airyRatio_a_le
  set t₀ : ℝ := min 1 (√(1 / (8 * C))); set h₀ : ℝ := min (1 / (4 * |airyZero 1|)) (1 / (8 * C))
  have ht₀_pos : 0 < t₀ := lt_min one_pos (Real.sqrt_pos.mpr (div_pos one_pos (mul_pos (by norm_num) hC_pos)))
  have hh₀_pos : 0 < h₀ := lt_min (div_pos one_pos (mul_pos (by norm_num) ha1_abs_pos)) (div_pos one_pos (mul_pos (by norm_num) hC_pos))
  have hμ_real_pos : 0 < μ.real (Icc (1 : ℝ) 2) := ENNReal.toReal_pos hμ.ne' (measure_ne_top μ _)
  set b : ℝ := μ.real (Icc (1 : ℝ) 2) / 16
  refine ⟨b, by positivity, t₀, ht₀_pos, h₀, hh₀_pos, fun {h t} hh_pos hh_le ht_pos ht_le => ?_⟩
  have hphi_nn : 0 ≤ η_hat * airyPhi1 t := mul_nonneg hη (airyPhi1_pos ht_pos).le
  have hkern_int : IntegrableOn (dirichletKernel h t) (Ioi 0) μ := dirichletKernel_integrableOn hh_pos ht_pos
  have hsub_icc : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun _ hs => by rw [mem_Ioi]; linarith [hs.1]
  have hmix_ge : ∫ s in Icc (1 : ℝ) 2, (-dirichletKernel h t s) ∂μ ≤ ∫ s in Ioi (0 : ℝ), (-dirichletKernel h t s) ∂μ :=
    setIntegral_mono_set hkern_int.neg (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs =>
      neg_nonneg.mpr (dirichletResolventTerm_nonpos ht_pos (lt_add_of_pos_right _ (inv_pos.mpr (mul_pos (mem_Ioi.mp hs) hh_pos)))))
      (Eventually.of_forall fun _ h => hsub_icc h)
  have hpt_icc : ∀ s ∈ Icc (1 : ℝ) 2, (1 / 8 : ℝ) * min (t / √h) 1 ≤ -dirichletKernel h t s := by
    intro s hs; set q := s * h; set z := airyZero 1 + q⁻¹; have hq_pos : 0 < q := mul_pos (by linarith [hs.1]) hh_pos
    have hh1 : h ≤ 1 / (4 * |airyZero 1|) := hh_le.trans (min_le_left _ _)
    have h4a : 4 * h * |airyZero 1| ≤ 1 := by have := (le_div_iff₀ (mul_pos (by norm_num) ha1_abs_pos)).mp hh1; linarith
    have h4 : -airyZero 1 ≤ 1 / (4 * h) := by rw [← abs_of_neg ha1_neg, le_div_iff₀ (by positivity)]; linarith
    have hz_ge : 1 / (4 * h) ≤ z := by
      have hinv : 1 / (2 * h) ≤ q⁻¹ := by rw [one_div]; exact inv_anti₀ hq_pos (by dsimp [q]; nlinarith [hs.2])
      dsimp [z]; linarith [show 1 / (2 * h) - 1 / (4 * h) = 1 / (4 * h) by ring]
    have hz_pos : 0 < z := lt_of_lt_of_le (by positivity) hz_ge
    have hden_pos : 0 < 1 - (z - airyZero 1)⁻¹ * (a - airyZero 1) := by
      have hq_eq : (z - airyZero 1)⁻¹ = q := by dsimp [z]; rw [add_sub_cancel_left, inv_inv]
      have ha_diff : 0 < a - airyZero 1 ∧ a - airyZero 1 < |airyZero 1| := ⟨sub_pos.mpr ha1, by rw [abs_of_neg ha1_neg]; linarith⟩
      have hs_bd : s * h * (a - airyZero 1) ≤ 2 * h * |airyZero 1| :=
        mul_le_mul (mul_le_mul_of_nonneg_right hs.2 hh_pos.le) ha_diff.2.le ha_diff.1.le (by positivity)
      rw [hq_eq]; dsimp [q]; linarith
    have hden_le : 1 - (z - airyZero 1)⁻¹ * (a - airyZero 1) ≤ 1 := by
      have : 0 ≤ (z - airyZero 1)⁻¹ * (a - airyZero 1) := mul_nonneg (inv_nonneg.mpr (by linarith)) (by linarith); linarith
    have hgz_le : airyRatio z t ≤ Real.exp (-(t / √h / 2)) := by
      have hsqrt_z : 1 / (2 * √h) ≤ √z := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 / (2 * √h)),
          show (1 / (2 * √h)) ^ 2 = 1 / (4 * h) by rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hh_pos.le]; ring]
        exact Real.sqrt_le_sqrt hz_ge
      refine (airyRatio_le_exp hz_pos.le ht_pos.le).trans (Real.exp_le_exp.mpr ?_)
      rw [show -(t / √h / 2) = -(1 / (2 * √h)) * t by ring, neg_mul, neg_mul]
      exact neg_le_neg (mul_le_mul_of_nonneg_right hsqrt_z ht_pos.le)
    have hexp_low : (1 / 4 : ℝ) * min (t / √h) 1 ≤ 1 - airyRatio z t := (one_sub_exp_neg_half_ge (t / √h) (by positivity)).trans (by linarith)
    have hloss : C * t ^ 2 ≤ (1 / 8 : ℝ) * min (t / √h) 1 := by
      have ht0_sq : t₀ ^ 2 ≤ 1 / (8 * C) := by
        have := pow_le_pow_left₀ ht₀_pos.le (min_le_right 1 √(1 / (8 * C))) 2
        rwa [Real.sq_sqrt (div_pos one_pos (mul_pos (by norm_num) hC_pos)).le] at this
      have hh0_bd : h ≤ 1 / (8 * C) := hh_le.trans (min_le_right _ _)
      rcases le_or_gt (t / √h) 1 with h1 | h1
      · rw [min_eq_left h1]; have hts : t ≤ √h := (div_le_one (Real.sqrt_pos.mpr hh_pos)).mp h1
        have hCh : C * h ≤ 1 / 8 := by have := (le_div_iff₀ (mul_pos (by norm_num) hC_pos)).mp hh0_bd; linarith
        calc C * t ^ 2 = C * (t * t) := by ring
          _ ≤ C * (√h * t) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hts ht_pos.le) hC_pos.le
          _ = (C * h) * (t / √h) := by rw [mul_div_assoc', div_eq_mul_inv, mul_assoc, ← div_eq_mul_inv]; field_simp; rw [Real.sq_sqrt hh_pos.le]
          _ ≤ (1 / 8 : ℝ) * (t / √h) := mul_le_mul_of_nonneg_right hCh (by positivity)
      · rw [min_eq_right h1.le]
        have := (le_div_iff₀ (mul_pos (by norm_num) hC_pos)).mp ((pow_le_pow_left₀ ht_pos.le ht_le 2).trans ht0_sq); linarith
    have hdiff_ge : (1 / 8 : ℝ) * min (t / √h) 1 ≤ airyRatio a t - airyRatio z t := by
      linarith [hga_quad t ⟨ht_pos.le, ht_le.trans (min_le_left _ _)⟩]
    have hkern_eq : -dirichletKernel h t s = (airyRatio a t - airyRatio z t) / (1 - (z - airyZero 1)⁻¹ * (a - airyZero 1)) := by
      dsimp [dirichletKernel, a]; rw [dirichletResolventTerm_eq_of_ne (by linarith) (by linarith), ← neg_div, neg_sub]
    rw [hkern_eq]
    calc (1 / 8 : ℝ) * min (t / √h) 1 ≤ airyRatio a t - airyRatio z t := hdiff_ge
      _ = (airyRatio a t - airyRatio z t) / 1 := (div_one _).symm
      _ ≤ (airyRatio a t - airyRatio z t) / (1 - (z - airyZero 1)⁻¹ * (a - airyZero 1)) :=
          div_le_div_of_nonneg_left (by linarith [show 0 ≤ (1 / 8 : ℝ) * min (t / √h) 1 by positivity]) hden_pos hden_le
  have hconst_int : (1 / 8 : ℝ) * min (t / √h) 1 * μ.real (Icc (1 : ℝ) 2) ≤ ∫ s in Icc (1 : ℝ) 2, (-dirichletKernel h t s) ∂μ := by
    rw [show (1 / 8 : ℝ) * min (t / √h) 1 * μ.real (Icc (1 : ℝ) 2) =
      ∫ _s in Icc (1 : ℝ) 2, ((1 / 8 : ℝ) * min (t / √h) 1) ∂μ by rw [setIntegral_const, smul_eq_mul, mul_comm]]
    exact setIntegral_mono_on integrableOn_const (hkern_int.neg.mono_set hsub_icc) measurableSet_Icc hpt_icc
  have hneg_v : -dirichletVector μ σ_c η_hat h t = σ_c * (∫ s in Ioi (0 : ℝ), (-dirichletKernel h t s) ∂μ) + η_hat * airyPhi1 t := by
    unfold dirichletVector; rw [integral_neg]; ring
  rw [hneg_v]
  calc b * min (t / √h) 1 = (1 / 2 : ℝ) * ((1 / 8 : ℝ) * min (t / √h) 1 * μ.real (Icc (1 : ℝ) 2)) := by dsimp [b]; ring
    _ ≤ σ_c * (∫ s in Ioi (0 : ℝ), (-dirichletKernel h t s) ∂μ) := mul_le_mul hσ (hconst_int.trans hmix_ge) (by positivity) (by linarith)
    _ ≤ σ_c * (∫ s in Ioi (0 : ℝ), (-dirichletKernel h t s) ∂μ) + η_hat * airyPhi1 t := le_add_of_nonneg_right hphi_nn

/-- Concrete non-vacuity witness for `dirichlet_two_scale_floor` using `δ_{3/2}`. -/
theorem dirichlet_two_scale_floor_witness :
    ∃ b > 0, ∃ t₀ > 0, ∃ h₀ > 0, ∀ {h t : ℝ}, 0 < h → h ≤ h₀ → 0 < t → t ≤ t₀ →
      b * min (t / √h) 1 ≤ -dirichletVector (Measure.dirac (3 / 2 : ℝ)) 1 0 h t := by
  have hμ : 0 < (Measure.dirac (3 / 2 : ℝ)) (Icc (1 : ℝ) 2) := by
    rw [Measure.dirac_apply' _ measurableSet_Icc]; simp [show (3 / 2 : ℝ) ∈ Icc (1 : ℝ) 2 from ⟨by norm_num, by norm_num⟩]
  exact dirichlet_two_scale_floor (Measure.dirac (3 / 2 : ℝ)) hμ (by norm_num) le_rfl

/-! ### Part 2C: `(cepe:PE3a)` `B_c^*` Hölder bound -/

private lemma integrableOn_rpow_neg_half_Ioc {R : ℝ} (hR : 0 < R) : IntegrableOn (fun X : ℝ => X ^ (-(1 / 2 : ℝ))) (Ioc 0 R) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le).mp (intervalIntegral.intervalIntegrable_rpow' (by norm_num))

private lemma integral_rpow_neg_half_Ioc {R : ℝ} (hR : 0 < R) : ∫ X in Ioc (0 : ℝ) R, X ^ (-(1 / 2 : ℝ)) = 2 * R ^ (1 / 2 : ℝ) := by
  rw [← intervalIntegral.integral_of_le hR.le, _root_.integral_rpow (Or.inl (by norm_num)), Real.zero_rpow (by norm_num)]; norm_num; ring

private lemma integral_rpow_neg_three_halves_Ioi {R : ℝ} (hR : 0 < R) : ∫ X in Ioi R, X ^ (-(3 / 2 : ℝ)) = 2 * R ^ (-(1 / 2 : ℝ)) := by
  rw [integral_Ioi_rpow_of_lt (by norm_num) hR]; norm_num; ring

private lemma pe3a_withDensity_eq_setIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X) (φ : ℝ → E) :
    ∫ X in Ioi (0 : ℝ), φ X ∂(volume.withDensity fun X => ENNReal.ofReal (g X)) = ∫ X in Ioi (0 : ℝ), g X • φ X := by
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hg_meas.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) φ measurableSet_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi fun X hX => by rw [ENNReal.toReal_ofReal (hg_nn X hX)]

private lemma pe3a_withDensity_integrableOn_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → ℝ} (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X) (φ : ℝ → E) :
    IntegrableOn φ (Ioi 0) (volume.withDensity fun X => ENNReal.ofReal (g X)) ↔ IntegrableOn (fun X => g X • φ X) (Ioi 0) volume := by
  unfold IntegrableOn
  rw [restrict_withDensity measurableSet_Ioi,
    integrable_withDensity_iff_integrable_smul₀' hg_meas.ennreal_ofReal (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; rw [ENNReal.toReal_ofReal (hg_nn X hX)]

lemma pe3a_min_integrableOn {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X)
    (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ))) :
    IntegrableOn (fun X : ℝ => min X 1) (Ioi 0) (volume.withDensity fun X => ENNReal.ofReal (g X)) := by
  rw [pe3a_withDensity_integrableOn_iff hg_meas hg_nn]
  have h1 : IntegrableOn (fun X => g X * min X 1) (Ioc 0 1) := by
    refine ((integrableOn_rpow_neg_half_Ioc one_pos).const_mul C).mono'
      ((hg_meas.mono_set Ioc_subset_Ioi_self).aestronglyMeasurable.mul ((continuous_id.min continuous_const).aestronglyMeasurable)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with X hX; have hX0 : 0 < X := hX.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg_nn X hX0) (le_min hX0.le zero_le_one))]
    calc g X * min X 1 ≤ (C * X ^ (-(3 / 2 : ℝ))) * X :=
          mul_le_mul (hg_le X hX0) (min_le_left X 1) (le_min hX0.le zero_le_one) (by positivity)
      _ = C * X ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add_one hX0.ne']; norm_num
  have h2 : IntegrableOn (fun X => g X * min X 1) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) one_pos).const_mul C).mono'
      ((hg_meas.mono_set (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable.mul ((continuous_id.min continuous_const).aestronglyMeasurable)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; have hX_pos : 0 < X := zero_lt_one.trans hX
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg_nn X hX_pos) (le_min hX_pos.le zero_le_one))]
    calc g X * min X 1 ≤ (C * X ^ (-(3 / 2 : ℝ))) * 1 :=
          mul_le_mul (hg_le X hX_pos) (min_le_right X 1) (le_min hX_pos.le zero_le_one) (by positivity)
      _ = C * X ^ (-(3 / 2 : ℝ)) := mul_one _
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]; exact ⟨h1, h2⟩

private lemma pe3a_tail_min_integral_le {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hint : IntegrableOn (fun X => g X * min X 1) (Ioi 1)) (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ))) :
    ∫ X in Ioi (1 : ℝ), g X * min X 1 ≤ 2 * C := by
  calc ∫ X in Ioi (1 : ℝ), g X * min X 1
      ≤ ∫ X in Ioi (1 : ℝ), C * X ^ (-(3 / 2 : ℝ)) := by
        refine setIntegral_mono_on hint ((integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) one_pos).const_mul C)
          measurableSet_Ioi fun X hX => ?_
        have hX_pos : 0 < X := zero_lt_one.trans hX
        exact (mul_le_mul (hg_le X hX_pos) (min_le_right _ _) (le_min hX_pos.le zero_le_one) (by positivity)).trans_eq (mul_one _)
    _ = 2 * C := by rw [integral_const_mul, integral_rpow_neg_three_halves_Ioi one_pos]; norm_num; ring

/-- For density `0 ≤ g X ≤ C * X^{-3/2}` on `(0, ∞)`, `∫_0^∞ min(X, 1) dν ≤ 4 * C`
(sharp bound matching `certify_ce_pf2_pe_constants.py`). -/
theorem pe3a_min_integral_le {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X)
    (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ))) :
    ∫ X in Ioi (0 : ℝ), min X 1 ∂(volume.withDensity fun X => ENNReal.ofReal (g X)) ≤ 4 * C := by
  have hint := (pe3a_withDensity_integrableOn_iff hg_meas hg_nn (fun X => min X 1)).mp (pe3a_min_integrableOn hC hg_meas hg_nn hg_le)
  rw [pe3a_withDensity_eq_setIntegral hg_meas hg_nn]; simp only [smul_eq_mul] at hint ⊢
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  have h1 : ∫ X in Ioc (0 : ℝ) 1, g X * min X 1 ≤ 2 * C := by
    calc ∫ X in Ioc (0 : ℝ) 1, g X * min X 1
        ≤ ∫ X in Ioc (0 : ℝ) 1, C * X ^ (-(1 / 2 : ℝ)) := by
          refine setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) ((integrableOn_rpow_neg_half_Ioc one_pos).const_mul C)
            measurableSet_Ioc fun X hX => ?_
          have hX0 : 0 < X := hX.1
          calc g X * min X 1 ≤ (C * X ^ (-(3 / 2 : ℝ))) * X :=
                mul_le_mul (hg_le X hX0) (min_le_left _ _) (le_min hX0.le zero_le_one) (by positivity)
            _ = C * X ^ (-(1 / 2 : ℝ)) := by rw [mul_assoc, ← Real.rpow_add_one hX0.ne']; norm_num
      _ = 2 * C := by rw [integral_const_mul, integral_rpow_neg_half_Ioc one_pos]; norm_num; ring
  have h2 := pe3a_tail_min_integral_le hC (hint.mono_set (Ioi_subset_Ioi zero_le_one)) hg_le; linarith

/-- Under the stronger decay `0 ≤ g X ≤ C * (1 + X)^{-3/2}` on `(0, ∞)`, `∫_0^∞ min(X, 1) dν ≤ 3 * C`. -/
theorem pe3a_min_integral_one_add_le {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X)
    (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * (1 + X) ^ (-(3 / 2 : ℝ))) :
    ∫ X in Ioi (0 : ℝ), min X 1 ∂(volume.withDensity fun X => ENNReal.ofReal (g X)) ≤ 3 * C := by
  have hg_le' : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ)) := fun X hX =>
    (hg_le X hX).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hX (by linarith) (by norm_num)) hC)
  have hint := (pe3a_withDensity_integrableOn_iff hg_meas hg_nn (fun X => min X 1)).mp (pe3a_min_integrableOn hC hg_meas hg_nn hg_le')
  rw [pe3a_withDensity_eq_setIntegral hg_meas hg_nn]; simp only [smul_eq_mul] at hint ⊢
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi zero_le_one))]
  have h1 : ∫ X in Ioc (0 : ℝ) 1, g X * min X 1 ≤ C := by
    calc ∫ X in Ioc (0 : ℝ) 1, g X * min X 1
        ≤ ∫ _X in Ioc (0 : ℝ) 1, C := by
          refine setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self) (integrableOn_const (hs := measure_Ioc_lt_top.ne))
            measurableSet_Ioc fun X hX => ?_
          have hX0 : 0 < X := hX.1
          have hpow : (1 + X) ^ (-(3 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
          calc g X * min X 1 ≤ (C * (1 + X) ^ (-(3 / 2 : ℝ))) * 1 :=
                mul_le_mul (hg_le X hX0) (min_le_right _ _) (le_min hX0.le zero_le_one) (by positivity)
            _ ≤ C * 1 := mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hC hpow) zero_le_one
            _ = C := mul_one C
      _ = C := by rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_mul]
  have h2 := pe3a_tail_min_integral_le hC (hint.mono_set (Ioi_subset_Ioi zero_le_one)) hg_le'; linarith

lemma norm_one_sub_exp_neg_le {v : ℂ} (hv : 0 ≤ v.re) : ‖1 - Complex.exp (-v)‖ ≤ min ‖v‖ 2 := by
  refine le_min ?_ ?_
  · have hftc : ∫ t in (0 : ℝ)..1, v * Complex.exp (-(t : ℂ) * v) = 1 - Complex.exp (-v) := by
      have hd0 : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => (-1 : ℂ) * Complex.exp (-(s : ℂ) * v))
          (v * Complex.exp (-(t : ℂ) * v)) t := fun t _ => by
        have hlin : HasDerivAt (fun s : ℝ => -(s : ℂ) * v) (-v) t := by
          simpa using (((Complex.ofRealCLM.hasDerivAt).neg).mul_const v : HasDerivAt (fun s : ℝ => -(s : ℂ) * v) (-1 * v) t)
        exact (hlin.cexp.const_mul (-1 : ℂ)).congr_deriv (by ring)
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => -Complex.exp (-(s : ℂ) * v))
          (v * Complex.exp (-(t : ℂ) * v)) t := fun t ht => by simpa only [neg_one_mul] using hd0 t ht
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd ((by fun_prop : Continuous fun t : ℝ =>
        v * Complex.exp (-(t : ℂ) * v)).intervalIntegrable 0 1)]
      simp; ring
    rw [← hftc]
    calc ‖∫ t in (0 : ℝ)..1, v * Complex.exp (-(t : ℂ) * v)‖
        ≤ ∫ t in (0 : ℝ)..1, ‖v * Complex.exp (-(t : ℂ) * v)‖ := intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ _t in (0 : ℝ)..1, ‖v‖ := by
          refine intervalIntegral.integral_mono_on zero_le_one
            ((by fun_prop : Continuous fun t : ℝ => ‖v * Complex.exp (-(t : ℂ) * v)‖).intervalIntegrable 0 1)
            intervalIntegrable_const fun t ht => ?_
          rw [norm_mul, Complex.norm_exp]
          have hre : (-(t : ℂ) * v).re ≤ 0 := by
            simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
            exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hv
          exact mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr hre)
      _ = ‖v‖ := by simp
  · calc ‖1 - Complex.exp (-v)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (-v)‖ := norm_sub_le _ _
      _ = 1 + Real.exp (-v.re) := by rw [norm_one, Complex.norm_exp, Complex.neg_re]
      _ ≤ 2 := by linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)]

private lemma pe3a_arg_re_nonneg {z : ℂ} (hz : 0 ≤ z.re) {X : ℝ} (hX : 0 < X) : 0 ≤ ((ceCs : ℂ) * z * (X : ℂ)).re := by
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, zero_mul]
  exact mul_nonneg (mul_nonneg ceCs_pos.le hz) hX.le

private lemma pe3a_integrand_norm_le_low {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X) (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ)))
    {z : ℂ} (hz : 0 ≤ z.re) {X : ℝ} (hX : 0 < X) :
    ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ ≤ C * ceCs * ‖z‖ * X ^ (-(1 / 2 : ℝ)) := by
  have hbd := (norm_one_sub_exp_neg_le (pe3a_arg_re_nonneg hz hX)).trans (min_le_left _ _)
  rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ceCs_pos, Real.norm_eq_abs, abs_of_pos hX] at hbd
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hg_nn X hX)]
  calc g X * ‖1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ))‖
      ≤ (C * X ^ (-(3 / 2 : ℝ))) * (ceCs * ‖z‖ * X) := by
        rw [show -(ceCs : ℂ) * z * (X : ℂ) = -((ceCs : ℂ) * z * (X : ℂ)) by ring]
        exact mul_le_mul (hg_le X hX) hbd (norm_nonneg _) (by positivity)
    _ = C * ceCs * ‖z‖ * X ^ (-(1 / 2 : ℝ)) := by
        rw [show X ^ (-(1 / 2 : ℝ)) = X ^ (-(3 / 2 : ℝ)) * X by rw [← Real.rpow_add_one hX.ne']; norm_num]; ring

private lemma pe3a_integrand_norm_le_high {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X) (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ)))
    {z : ℂ} (hz : 0 ≤ z.re) {X : ℝ} (hX : 0 < X) :
    ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ ≤ 2 * C * X ^ (-(3 / 2 : ℝ)) := by
  have hbd := (norm_one_sub_exp_neg_le (pe3a_arg_re_nonneg hz hX)).trans (min_le_right _ _)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hg_nn X hX)]
  calc g X * ‖1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ))‖
      ≤ (C * X ^ (-(3 / 2 : ℝ))) * 2 := by
        rw [show -(ceCs : ℂ) * z * (X : ℂ) = -((ceCs : ℂ) * z * (X : ℂ)) by ring]
        exact mul_le_mul (hg_le X hX) hbd (norm_nonneg _) (by positivity)
    _ = 2 * C * X ^ (-(3 / 2 : ℝ)) := by ring

lemma pe3a_holder_integrableOn {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X)
    (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ))) {z : ℂ} (hz : 0 ≤ z.re) :
    IntegrableOn (fun X : ℝ => 1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ))) (Ioi 0)
      (volume.withDensity fun X => ENNReal.ofReal (g X)) := by
  rw [pe3a_withDensity_integrableOn_iff hg_meas hg_nn]
  set φ : ℝ → ℂ := fun X => g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))
  have hφ_meas : AEStronglyMeasurable φ (volume.restrict (Ioi 0)) :=
    hg_meas.aestronglyMeasurable.smul (by fun_prop : Continuous fun X : ℝ => 1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ))).aestronglyMeasurable
  by_cases hz0 : z = 0
  · subst hz0; have hzero : ∀ X : ℝ, (0 : ℂ) = φ X := fun X => by simp [φ]
    exact (integrableOn_zero (μ := volume) (s := Ioi (0 : ℝ))).congr_fun (fun X _ => hzero X) measurableSet_Ioi
  · set R : ℝ := ‖z‖⁻¹; have hR : 0 < R := inv_pos.mpr (norm_pos_iff.mpr hz0)
    have h1 : IntegrableOn φ (Ioc 0 R) := ((integrableOn_rpow_neg_half_Ioc hR).const_mul (C * ceCs * ‖z‖)).mono'
      (hφ_meas.mono_set Ioc_subset_Ioi_self)
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with X hX; exact pe3a_integrand_norm_le_low hC hg_nn hg_le hz hX.1)
    have h2 : IntegrableOn φ (Ioi R) := ((integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) hR).const_mul (2 * C)).mono'
      (hφ_meas.mono_set (Ioi_subset_Ioi hR.le))
      (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with X hX; exact pe3a_integrand_norm_le_high hC hg_nn hg_le hz (hR.trans hX))
    rw [← Ioc_union_Ioi_eq_Ioi hR.le, integrableOn_union]; exact ⟨h1, h2⟩

/-- **Equation `(cepe:PE3a)` (`ce_o1_pre_edge.tex`)**: `|B_c^*(z)| ≤ (2 c_s + 4) C |z|^{1/2}` for `Re z ≥ 0`. -/
theorem pe3a_holder_bound {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hg_meas : AEMeasurable g (volume.restrict (Ioi 0))) (hg_nn : ∀ X ∈ Ioi (0 : ℝ), 0 ≤ g X)
    (hg_le : ∀ X ∈ Ioi (0 : ℝ), g X ≤ C * X ^ (-(3 / 2 : ℝ))) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖∫ X in Ioi (0 : ℝ), (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))
        ∂(volume.withDensity fun X => ENNReal.ofReal (g X))‖ ≤ (2 * ceCs + 4) * C * ‖z‖ ^ (1 / 2 : ℝ) := by
  by_cases hz0 : z = 0
  · subst hz0; simp
  have hint := (pe3a_withDensity_integrableOn_iff hg_meas hg_nn _).mp (pe3a_holder_integrableOn hC hg_meas hg_nn hg_le hz)
  have hint_norm : IntegrableOn (fun X => ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖) (Ioi 0) := hint.norm
  rw [pe3a_withDensity_eq_setIntegral hg_meas hg_nn]
  set R : ℝ := ‖z‖⁻¹; have hz_norm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0; have hR : 0 < R := inv_pos.mpr hz_norm_pos
  have hR_pow1 : R ^ (1 / 2 : ℝ) = ‖z‖ ^ (-(1 / 2 : ℝ)) := by dsimp [R]; rw [Real.inv_rpow hz_norm_pos.le, Real.rpow_neg hz_norm_pos.le]
  have hR_pow2 : R ^ (-(1 / 2 : ℝ)) = ‖z‖ ^ (1 / 2 : ℝ) := by dsimp [R]; rw [Real.inv_rpow hz_norm_pos.le, Real.rpow_neg (by positivity), inv_inv]
  have hnorm_le : ‖∫ X in Ioi (0 : ℝ), g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ ≤
      ∫ X in Ioi (0 : ℝ), ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ := norm_integral_le_integral_norm _
  have hnorm_split : ∫ X in Ioi (0 : ℝ), ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ =
      (∫ X in Ioc 0 R, ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖) +
        ∫ X in Ioi R, ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ := by
    rw [← Ioc_union_Ioi_eq_Ioi hR.le]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi (hint_norm.mono_set Ioc_subset_Ioi_self) (hint_norm.mono_set (Ioi_subset_Ioi hR.le))
  have h1 : ∫ X in Ioc 0 R, ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ ≤ 2 * ceCs * C * ‖z‖ ^ (1 / 2 : ℝ) := by
    calc ∫ X in Ioc 0 R, ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖
        ≤ ∫ X in Ioc 0 R, C * ceCs * ‖z‖ * X ^ (-(1 / 2 : ℝ)) :=
          setIntegral_mono_on (hint_norm.mono_set Ioc_subset_Ioi_self) ((integrableOn_rpow_neg_half_Ioc hR).const_mul (C * ceCs * ‖z‖))
            measurableSet_Ioc fun X hX => pe3a_integrand_norm_le_low hC hg_nn hg_le hz hX.1
      _ = 2 * ceCs * C * (‖z‖ * ‖z‖ ^ (-(1 / 2 : ℝ))) := by rw [integral_const_mul, integral_rpow_neg_half_Ioc hR, hR_pow1]; ring
      _ = 2 * ceCs * C * ‖z‖ ^ (1 / 2 : ℝ) := by
          congr 1; conv_lhs => lhs; rw [← Real.rpow_one ‖z‖]
          rw [← Real.rpow_add hz_norm_pos]; norm_num
  have h2 : ∫ X in Ioi R, ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖ ≤ 4 * C * ‖z‖ ^ (1 / 2 : ℝ) := by
    calc ∫ X in Ioi R, ‖g X • (1 - Complex.exp (-(ceCs : ℂ) * z * (X : ℂ)))‖
        ≤ ∫ X in Ioi R, 2 * C * X ^ (-(3 / 2 : ℝ)) :=
          setIntegral_mono_on (hint_norm.mono_set (Ioi_subset_Ioi hR.le))
            ((integrableOn_Ioi_rpow_of_lt (a := -(3 / 2 : ℝ)) (by norm_num) hR).const_mul (2 * C))
            measurableSet_Ioi fun X hX => pe3a_integrand_norm_le_high hC hg_nn hg_le hz (hR.trans hX)
      _ = 4 * C * ‖z‖ ^ (1 / 2 : ℝ) := by rw [integral_const_mul, integral_rpow_neg_three_halves_Ioi hR, hR_pow2]; ring
  linarith

/-! ### Axiom verification -/

/-- info: 'FormalResearch.CohnElkies.bsplineUnit_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsplineUnit_nonneg
/-- info: 'FormalResearch.CohnElkies.bsplineUnit_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsplineUnit_support
/-- info: 'FormalResearch.CohnElkies.bsplineUnit_setIntegral_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsplineUnit_setIntegral_one
/-- info: 'FormalResearch.CohnElkies.bsplineUnit_symm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsplineUnit_symm
/-- info: 'FormalResearch.CohnElkies.bsplineUnit_lower_Icc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsplineUnit_lower_Icc
/-- info: 'FormalResearch.CohnElkies.bspline_oscillating_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bspline_oscillating_floor
/-- info: 'FormalResearch.CohnElkies.bspline_floor_smoothing_gain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bspline_floor_smoothing_gain
/-- info: 'FormalResearch.CohnElkies.oscFloorSeed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms oscFloorSeed_witness
/-- info: 'FormalResearch.CohnElkies.airyLogDeriv_deriv_eq_neg_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyLogDeriv_deriv_eq_neg_integral
/-- info: 'FormalResearch.CohnElkies.airyRatio_strictAntiOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyRatio_strictAntiOn
/-- info: 'FormalResearch.CohnElkies.airyRatio_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyRatio_le_exp
/-- info: 'FormalResearch.CohnElkies.neg_airyLogDeriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms neg_airyLogDeriv_le
/-- info: 'FormalResearch.CohnElkies.dirichlet_two_scale_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirichlet_two_scale_floor
/-- info: 'FormalResearch.CohnElkies.dirichlet_two_scale_floor_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dirichlet_two_scale_floor_witness
/-- info: 'FormalResearch.CohnElkies.pe3a_min_integral_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pe3a_min_integral_le
/-- info: 'FormalResearch.CohnElkies.pe3a_min_integral_one_add_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pe3a_min_integral_one_add_le
/-- info: 'FormalResearch.CohnElkies.pe3a_holder_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pe3a_holder_bound

end FormalResearch.CohnElkies

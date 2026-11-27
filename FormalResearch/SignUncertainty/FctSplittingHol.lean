/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctSplittingSegment
public import FormalResearch.SignUncertainty.CtOuterParam
public import FormalResearch.SignUncertainty.UctSeedZ

/-!
# Holomorphy of `Ψ_c` and `F`, and zero-freeness of `H_*/G_ε` on the band (`fct:splitting`)

Paper I (`constant_terms_five.tex`), `(fct:A-Psi-def)` ("`Ψ_c` is holomorphic on `S`"), `(fct:F-def)`, and the first lines of the proof of `fct:splitting`
("`Re ζ ∈ [5/16, 7/16]` avoids the zero of `H_*` at `1/2`").

* `ctHG_ne_zero_of_band`: `H_*/G_ε = ctHG ε` has no zero on `0 < Re ζ < 1/2` (the factor `Z_ε` has its only zeros at `Re ζ ∈ 1/2 + ℤ`
  resp. `-1/2 + 2ℤ`, and `ζ^{5/2}(1-ζ)^{5/2}`, `exp(-h)` are zero-free).
* `mellinK0_ne_zero`: `K₀(ζ, ξ) ≠ 0` for `Re ζ < 1`.
* `differentiableOn_segIntegral`: for `f` holomorphic on `S` with `|f(t)| ≤ M|t|^{-1/2}` near `0` (and segment-integrable), `ζ ↦ ζ ∫₀¹ f(sζ) ds`
  `= ∫₀^ζ f` is holomorphic on `S`.  Proof: the truncations `ζ ∫_δ^1 f(sζ) ds` are holomorphic (parameter integral) and converge locally uniformly
  (the tail is `≤ 2 M |ζ|^{1/2} δ^{1/2}`), so the limit is holomorphic (`TendstoLocallyUniformlyOn.differentiableOn`).
* `fctWarpKA_differentiableOn`, `fctPsi_differentiableOn` (**holomorphy of `Ψ_c` on `0 < Re ζ < 1`**), `fctFint_differentiableOn`
  (`F` holomorphic on `{ζ ∈ S | ctHG ε ζ ≠ 0}`, in particular on `0 < Re ζ < 1/2`).

Class: proved.  The hypotheses on `D_{τ₁}` (`fctDcompAt`) are those of `CompData` (holomorphic on `S`, continuous and bounded on `S̄`).
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter

namespace FormalResearch.SignUncertainty

/-! ### Zero-freeness on the band -/

lemma seedA_ne_zero_of_band (ε : ℝ) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1 / 2) : seedA ε ζ ≠ 0 := by
  unfold seedA
  split_ifs with hε
  · intro h
    have h2 : Complex.cos (bArg ζ) = 0 := by
      have : Complex.cos (bArg ζ) ^ 2 = 0 := by
        have h' : (2 : ℂ) * Complex.cos (bArg ζ) ^ 2 = 0 := h
        simpa using h'
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h2
    have hk' : bArg ζ = (((2 * k + 1) * π / 2 : ℝ) : ℂ) := by rw [hk]; push_cast; ring
    have := congrArg Complex.re hk'
    rw [bArg_re, Complex.ofReal_re] at this
    have hπ := Real.pi_pos
    have h3 : (1 : ℝ) / 4 - ζ.re / 2 = (2 * k + 1) / 2 := by
      have : π * (1 / 4 - ζ.re / 2) = π * ((2 * k + 1) / 2) := by nlinarith
      exact mul_left_cancel₀ hπ.ne' this
    rcases le_or_gt 0 k with hk0 | hk0
    · have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith
  · intro h
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp h
    have hk' : (π : ℂ) * ζ = (((2 * k + 1) * π / 2 : ℝ) : ℂ) := by rw [hk]; push_cast; ring
    have := congrArg Complex.re hk'
    rw [Complex.ofReal_re] at this
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at this
    have hπ := Real.pi_pos
    have h3 : ζ.re = k + 1 / 2 := by
      have : π * ζ.re = π * (k + 1 / 2) := by nlinarith
      exact mul_left_cancel₀ hπ.ne' this
    rcases le_or_gt 0 k with hk0 | hk0
    · have : (0 : ℝ) ≤ k := by exact_mod_cast hk0
      linarith
    · have : (k : ℝ) ≤ -1 := by exact_mod_cast (by omega : k ≤ -1)
      linarith

/-- `sincInv (π ζ) ≠ 0` for `0 ≤ Re ζ < 1/2`. -/
lemma sincInv_pi_ne_zero_of_band {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1 / 2) : sincInv (π * ζ) ≠ 0 := by
  unfold sincInv
  refine inv_ne_zero (dslope_sin_ne_zero fun n hn hz => ?_)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have : ζ = n := mul_right_cancel₀ hπ (by rw [mul_comm ζ]; exact hz)
  have hre : ζ.re = n := by rw [this]; simp
  rcases le_or_gt 0 n with hn0 | hn0
  · have : (0 : ℝ) ≤ n := by exact_mod_cast hn0
    have : (n : ℝ) < 1 := by linarith
    have : n < 1 := by exact_mod_cast this
    have : (n : ℝ) = 0 := by exact_mod_cast (by omega : n = 0)
    exact hn (by exact_mod_cast this)
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    linarith

/-- **`H_*/G_ε` is zero-free on `0 ≤ Re ζ < 1/2`, `ζ ≠ 0`** (including the left edge `Re ζ = 0`; at `ζ = 0` the value is Lean's junk `0`). -/
theorem ctHG_ne_zero_of_closed_band (ε : ℝ) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1 / 2) (hζ : ζ ≠ 0) : ctHG ε ζ ≠ 0 := by
  have h1ζ : 1 - ζ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  unfold ctHG
  rw [uctSeedZ_of_le (by linarith)]
  refine div_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) (mul_ne_zero ?_ ?_)
  · unfold seedZL
    exact mul_ne_zero (seedA_ne_zero_of_band ε h0 h1)
      (pow_ne_zero 2 (mul_ne_zero h1ζ (sincInv_pi_ne_zero_of_band h0 h1)))
  · rw [Ne, Complex.cpow_eq_zero_iff]; tauto
  · rw [Ne, Complex.cpow_eq_zero_iff]; tauto

/-- **`H_*/G_ε` is zero-free on `0 < Re ζ < 1/2`** (so on the band `5/16 ≤ Re ζ ≤ 7/16` of `fct:splitting`). -/
theorem ctHG_ne_zero_of_band (ε : ℝ) {ζ : ℂ} (h0 : 0 < ζ.re) (h1 : ζ.re < 1 / 2) : ctHG ε ζ ≠ 0 :=
  ctHG_ne_zero_of_closed_band ε h0.le h1 (fun h => by rw [h] at h0; simp at h0)

/-- The numerator `Z_ε(ζ) e^{-h̄(ζ)}` of `H_*/G_ε` is nonzero on `0 ≤ Re ζ < 1/2` (also at `ζ = 0`). -/
lemma uctSeedZ_mul_exp_ne_zero (ε : ℝ) {ζ : ℂ} (h0 : 0 ≤ ζ.re) (h1 : ζ.re < 1 / 2) :
    uctSeedZ ε ζ * Complex.exp (-outerHbar ζ) ≠ 0 := by
  have h1ζ : 1 - ζ ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [uctSeedZ_of_le (by linarith)]
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  unfold seedZL
  exact mul_ne_zero (seedA_ne_zero_of_band ε h0 h1)
    (pow_ne_zero 2 (mul_ne_zero h1ζ (sincInv_pi_ne_zero_of_band h0 h1)))

/-- `K₀(ζ, ξ) ≠ 0` for `Re ζ < 1`: `K₀ = (1-ζ)^{-1/2} e^{B_c} e^{cΦ_Mel}`. -/
lemma mellinK0_ne_zero (c : ℝ) {ζ : ℂ} (h : ζ.re < 1) (ξ : ℝ) : mellinK0 c ζ ξ ≠ 0 := by
  have h1ζ : 1 - ζ ≠ 0 := fun h' => by
    have := congrArg Complex.re h'; simp at this; linarith
  unfold mellinK0
  refine mul_ne_zero (mul_ne_zero ?_ (Complex.exp_ne_zero _)) (Complex.exp_ne_zero _)
  rw [Ne, Complex.cpow_eq_zero_iff]; tauto

/-! ### Holomorphy of the segment integral `ζ ∫₀¹ f(sζ) ds` -/

lemma mul_mem_strip {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) {w : ℂ} (hw : w ∈ strip) : (s : ℂ) * w ∈ strip := by
  have : ((s : ℂ) * w).re = s * w.re := by simp
  refine ⟨?_, ?_⟩
  · show 0 < ((s : ℂ) * w).re
    rw [this]; exact mul_pos hs0 hw.1
  · show ((s : ℂ) * w).re < 1
    rw [this]; nlinarith [hw.1, hw.2]

/-- **The truncated segment integral is holomorphic**: for `f` holomorphic on `S` and `0 < δ ≤ 1`,
`ζ ↦ ζ ∫_δ^1 f(sζ) ds` is holomorphic on `S` (parameter integral over the compact range `s ∈ [δ, 1]`). -/
lemma differentiableOn_segTail {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f strip) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    DifferentiableOn ℂ (fun ζ : ℂ => ζ * ∫ s in δ..1, f ((s : ℂ) * ζ)) strip := by
  have hI : DifferentiableOn ℂ (fun ζ : ℂ => ∫ s in Ioc δ 1, f ((s : ℂ) * ζ)) strip := by
    refine differentiableOn_integral_param (μ := volume.restrict (Ioc δ 1)) (Φ := fun w s => f ((s : ℂ) * w))
      isOpen_strip ?_ ?_ ?_
    · intro w hw
      have hc : ContinuousOn (fun s : ℝ => f ((s : ℂ) * w)) (Ioc δ 1) := by
        refine hf.continuousOn.comp (by fun_prop) fun s hs => mul_mem_strip (hδ.trans hs.1) hs.2 hw
      exact hc.aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      refine hf.comp (by fun_prop) fun w hw => mul_mem_strip (hδ.trans hs.1) hs.2 hw
    · intro w0 hw0
      obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.mp isOpen_strip w0 hw0
      set r := r' / 2 with hr
      have hrpos : 0 < r := by positivity
      have hcl : Metric.closedBall w0 r ⊆ strip := fun w hw =>
        hball (Metric.closedBall_subset_ball (by linarith) hw)
      set K : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' (Icc δ 1 ×ˢ Metric.closedBall w0 r) with hK
      have hKc : IsCompact K :=
        (isCompact_Icc.prod (isCompact_closedBall w0 r)).image (by fun_prop)
      have hKs : K ⊆ strip := by
        rintro _ ⟨⟨s, w⟩, ⟨hs, hw⟩, rfl⟩
        exact mul_mem_strip (hδ.trans_le hs.1) hs.2 (hcl hw)
      obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hf.continuousOn.mono hKs)
      refine ⟨r, hrpos.trans_le (by linarith), fun _ => B, integrable_const B, ?_⟩
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs w hw
      exact hB _ ⟨(s, w), ⟨⟨hs.1.le, hs.2⟩, Metric.ball_subset_closedBall hw⟩, rfl⟩
  have : (fun ζ : ℂ => ζ * ∫ s in δ..1, f ((s : ℂ) * ζ)) = fun ζ => ζ * ∫ s in Ioc δ 1, f ((s : ℂ) * ζ) := by
    funext ζ; rw [intervalIntegral.integral_of_le hδ1]
  rw [this]
  exact differentiableOn_id.mul hI

/-- The tail of the segment integral: for `y ∈ S`, `‖y‖ ≤ R`, `0 < δ`, `δ R ≤ r`, and `‖f t‖ ≤ M ‖t‖^{-1/2}` for `t ∈ S`, `‖t‖ ≤ r`,
`‖y ∫₀^δ f(sy) ds‖ ≤ 2 M R^{1/2} δ^{1/2}`. -/
lemma segTail_norm_le {f : ℂ → ℂ} {r M R δ : ℝ} (hM : 0 ≤ M)
    (hb : ∀ t : ℂ, t ∈ strip → ‖t‖ ≤ r → ‖f t‖ ≤ M * ‖t‖ ^ (-(1 / 2 : ℝ)))
    {y : ℂ} (hy : y ∈ strip) (hyR : ‖y‖ ≤ R) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδr : δ * R ≤ r) :
    ‖y * ∫ s in (0 : ℝ)..δ, f ((s : ℂ) * y)‖ ≤ 2 * M * Real.sqrt R * Real.sqrt δ := by
  have hy0 : y ≠ 0 := fun h => by have := hy.1; rw [h] at this; simp at this
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hR : 0 < R := hypos.trans_le hyR
  rw [norm_mul]
  have hint : ‖∫ s in (0 : ℝ)..δ, f ((s : ℂ) * y)‖ ≤
      ∫ s in (0 : ℝ)..δ, (M * ‖y‖ ^ (-(1 / 2 : ℝ))) * s ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hδ.le ?_ ?_
    · refine Filter.Eventually.of_forall fun s hs => ?_
      have hsn : ‖(s : ℂ) * y‖ = s * ‖y‖ := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.1.le]
      have hmem := mul_mem_strip hs.1 (hs.2.trans hδ1) hy
      have hsr : s * ‖y‖ ≤ r := by
        calc s * ‖y‖ ≤ δ * R := mul_le_mul hs.2 hyR hypos.le hδ.le
          _ ≤ r := hδr
      have := hb _ hmem (by rw [hsn]; exact hsr)
      rw [hsn, Real.mul_rpow hs.1.le hypos.le] at this
      linarith
    · exact (intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _
  have hval : ∫ s in (0 : ℝ)..δ, (M * ‖y‖ ^ (-(1 / 2 : ℝ))) * s ^ (-(1 / 2 : ℝ)) =
      (M * ‖y‖ ^ (-(1 / 2 : ℝ))) * (2 * Real.sqrt δ) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num))]
    congr 1
    rw [Real.zero_rpow (by norm_num), sub_zero, Real.sqrt_eq_rpow]
    norm_num; ring
  have hyy : ‖y‖ * ‖y‖ ^ (-(1 / 2 : ℝ)) = Real.sqrt ‖y‖ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hypos.le (by norm_num)]; norm_num
  have hsq : Real.sqrt ‖y‖ ≤ Real.sqrt R := Real.sqrt_le_sqrt hyR
  calc ‖y‖ * ‖∫ s in (0 : ℝ)..δ, f ((s : ℂ) * y)‖ ≤ ‖y‖ * ((M * ‖y‖ ^ (-(1 / 2 : ℝ))) * (2 * Real.sqrt δ)) := by
        rw [← hval]; exact mul_le_mul_of_nonneg_left hint hypos.le
    _ = 2 * M * Real.sqrt ‖y‖ * Real.sqrt δ := by rw [← hyy]; ring
    _ ≤ 2 * M * Real.sqrt R * Real.sqrt δ := by gcongr

/-- **Holomorphy of the segment integral** `ζ ↦ ζ ∫₀¹ f(sζ) ds` (`= ∫₀^ζ f`) on `S`: `f` holomorphic on `S`, segment integrable, and `|f(t)| ≤ M |t|^{-1/2}`
for `|t| ≤ r`.  (The truncations are holomorphic, `differentiableOn_segTail`, and converge locally uniformly by `segTail_norm_le`.) -/
theorem differentiableOn_segIntegral {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f strip)
    (hint : ∀ ζ ∈ strip, IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * ζ)) volume 0 1)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hb : ∀ t : ℂ, t ∈ strip → ‖t‖ ≤ r → ‖f t‖ ≤ M * ‖t‖ ^ (-(1 / 2 : ℝ))) :
    DifferentiableOn ℂ (fun ζ : ℂ => ζ * ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ζ)) strip := by
  have hlim : TendstoLocallyUniformlyOn (fun (δ : ℝ) (ζ : ℂ) => ζ * ∫ s in δ..1, f ((s : ℂ) * ζ))
      (fun ζ : ℂ => ζ * ∫ s in (0 : ℝ)..1, f ((s : ℂ) * ζ)) (𝓝[>] (0 : ℝ)) strip := by
    rw [Metric.tendstoLocallyUniformlyOn_iff]
    intro ε hε x hx
    refine ⟨strip ∩ Metric.ball x 1, inter_mem self_mem_nhdsWithin
      (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos)), ?_⟩
    set R : ℝ := ‖x‖ + 1 with hR
    have hRpos : 0 < R := by positivity
    set η : ℝ := min (min 1 (r / R)) ((ε / (2 * M * Real.sqrt R + 1)) ^ 2) with hη
    have hηpos : 0 < η := by
      refine lt_min (lt_min one_pos (by positivity)) (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hηpos] with δ hδ y hy
    obtain ⟨hyS, hyb⟩ := hy
    have hδ0 : 0 < δ := hδ.1
    have hδ1 : δ ≤ 1 := (hδ.2.le.trans (min_le_left _ _)).trans (min_le_left _ _)
    have hδr : δ * R ≤ r := by
      have : δ ≤ r / R := (hδ.2.le.trans (min_le_left _ _)).trans (min_le_right _ _)
      rwa [le_div_iff₀ hRpos] at this
    have hyR : ‖y‖ ≤ R := by
      have h1 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
        calc ‖y‖ = ‖x + (y - x)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have : ‖y - x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hyb
      linarith
    have hdiff : (y * ∫ s in (0 : ℝ)..1, f ((s : ℂ) * y)) - y * ∫ s in δ..1, f ((s : ℂ) * y) =
        y * ∫ s in (0 : ℝ)..δ, f ((s : ℂ) * y) := by
      have h1 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * y)) volume 0 δ :=
        (hint y hyS).mono_set (by rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hδ0.le]; exact Icc_subset_Icc le_rfl hδ1)
      have h2 : IntervalIntegrable (fun s : ℝ => f ((s : ℂ) * y)) volume δ 1 :=
        (hint y hyS).mono_set (by rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le hδ1]; exact Icc_subset_Icc hδ0.le le_rfl)
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
      ring
    rw [dist_eq_norm, hdiff]
    refine lt_of_le_of_lt (segTail_norm_le hM hb hyS hyR hδ0 hδ1 hδr) ?_
    have hsqδ : Real.sqrt δ < ε / (2 * M * Real.sqrt R + 1) := by
      rw [Real.sqrt_lt' (by positivity)]
      exact hδ.2.trans_le (min_le_right _ _)
    have hden : 0 < 2 * M * Real.sqrt R + 1 := by positivity
    rw [lt_div_iff₀ hden] at hsqδ
    nlinarith [Real.sqrt_nonneg δ, mul_nonneg hM (Real.sqrt_nonneg R)]
  refine hlim.differentiableOn ?_ isOpen_strip
  filter_upwards [Ioo_mem_nhdsGT one_pos] with δ hδ
  exact differentiableOn_segTail hf hδ.1 hδ.2.le

/-! ### `K₀ A_ε`, `Ψ_c` and `F` -/

lemma strip_subset_edgeStrip : strip ⊆ edgeStrip := fun t ht => by
  show |t.re| < 1
  rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]

/-- `K₀(·, ξ₁) A_ε` is holomorphic on `S` when `D_{τ₁}` is (`stripG`, `φ_kill`, `H_*/G_ε`, `K₀` are). -/
lemma fctWarpKA_differentiableOn {K4 ε c L1 α : ℝ} (hc : 0 < c) (hD : DifferentiableOn ℂ (fctDcompAt K4 c α) strip) :
    DifferentiableOn ℂ (fctWarpKA K4 ε c L1 α) strip := by
  have hK0 : DifferentiableOn ℂ (fun t : ℂ => mellinK0 c t (fctXi1 L1)) strip :=
    (differentiableOn_mellinK0 hc _).mono strip_subset_edgeStrip
  have hG : DifferentiableOn ℂ stripG strip := differentiableOn_stripG.mono strip_subset_edgeStrip
  have hP : DifferentiableOn ℂ (FctPhiKill.phiKill (c ^ (-(1 / 12 : ℝ)))) strip := by
    refine (FctPhiKill.differentiableOn_phiPQ 8 8 _).mono fun t ht => ?_
    intro h
    have := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.ofReal_re] at this
    linarith [ht.1, Real.rpow_pos_of_pos hc (-(1 / 12 : ℝ))]
  have hH : DifferentiableOn ℂ (ctHG ε) strip := ctHG_differentiableOn ε
  unfold fctWarpKA fctWarpA
  exact hK0.mul (((hG.add (differentiableOn_const _ |>.mul hP)).mul hD).mul hH)

/-- **`Ψ_c` is holomorphic on `S = {0 < Re ζ < 1}`** (`(fct:A-Psi-def)`), for `c > 0` and `D_{τ₁}` holomorphic on `S` and bounded and continuous on `S̄`
(`CompData`).  `K₀Ψ_c = ∫₀^ζ K₀ A_ε`, `|K₀A_ε| ≤ M|t|^{-1/2}` near `0` (`fctWarpKA_near_zero`), `K₀ ≠ 0`. -/
theorem fctPsi_differentiableOn {K4 ε c L1 α : ℝ} (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    DifferentiableOn ℂ (fctPsi K4 ε c L1 α) strip := by
  obtain ⟨r, M, hr, hM, hbd⟩ := fctWarpKA_near_zero (K4 := K4) (ε := ε) (L1 := L1) (α := α) hc hDb
  have hseg := differentiableOn_segIntegral (f := fctWarpKA K4 ε c L1 α) (fctWarpKA_differentiableOn hc hDh)
    (fun ζ hζ => fctWarpKA_segment_integrable hc hDc hDb hζ.1.le hζ.2) hr hM
    (fun t ht hrt => hbd t ht.1.le ht.2 (fun h => by have := ht.1; rw [h] at this; simp at this) hrt)
  have hK0 : DifferentiableOn ℂ (fun t : ℂ => mellinK0 c t (fctXi1 L1)) strip :=
    (differentiableOn_mellinK0 hc _).mono strip_subset_edgeStrip
  have : fctPsi K4 ε c L1 α = fun ζ : ℂ => (mellinK0 c ζ (fctXi1 L1))⁻¹ *
      (ζ * ∫ s in (0 : ℝ)..1, fctWarpKA K4 ε c L1 α ((s : ℂ) * ζ)) := rfl
  rw [this]
  exact hK0.inv (fun ζ hζ => mellinK0_ne_zero c hζ.2 _) |>.mul hseg

/-- **`F = Φ_c - 1` is holomorphic on `{ζ ∈ S | ctHG ε ζ ≠ 0}`** (`(fct:F-def)`; `D_{τ₁} = exp(·) ≠ 0`). -/
theorem fctFint_differentiableOn {K4 ε c L1 α : ℝ} (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    DifferentiableOn ℂ (fctFint K4 ε c L1 α) {ζ : ℂ | ζ ∈ strip ∧ ctHG ε ζ ≠ 0} := by
  have hΨ := (fctPsi_differentiableOn (ε := ε) (L1 := L1) hc hDh hDc hDb)
  unfold fctFint fctPhiC
  refine DifferentiableOn.sub ?_ (differentiableOn_const _)
  have hsub : {ζ : ℂ | ζ ∈ strip ∧ ctHG ε ζ ≠ 0} ⊆ strip := fun ζ hζ => hζ.1
  refine (differentiableOn_const _ |>.mul (hΨ.mono hsub)).div
    ((hDh.mono hsub).mul ((ctHG_differentiableOn ε).mono hsub)) fun ζ hζ => ?_
  exact mul_ne_zero (Complex.exp_ne_zero _) hζ.2

/-- **`F` is holomorphic on `0 < Re ζ < 1/2`** (a fortiori on the band `5/16 ≤ Re ζ ≤ 7/16`), `fct:splitting` (1)-(2). -/
theorem fctFint_differentiableOn_band {K4 ε c L1 α : ℝ} (hc : 0 < c) (hDh : DifferentiableOn ℂ (fctDcompAt K4 c α) strip)
    (hDc : ContinuousOn (fctDcompAt K4 c α) closedStrip)
    (hDb : ∃ B : ℝ, ∀ ζ ∈ closedStrip, ‖fctDcompAt K4 c α ζ‖ ≤ B) :
    DifferentiableOn ℂ (fctFint K4 ε c L1 α) {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1 / 2} :=
  (fctFint_differentiableOn hc hDh hDc hDb).mono fun ζ hζ =>
    ⟨⟨hζ.1, by linarith [hζ.2]⟩, ctHG_ne_zero_of_band ε hζ.1 hζ.2⟩

/-- info: 'FormalResearch.SignUncertainty.ctHG_ne_zero_of_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctHG_ne_zero_of_band

/-- info: 'FormalResearch.SignUncertainty.fctPsi_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctPsi_differentiableOn

/-- info: 'FormalResearch.SignUncertainty.fctFint_differentiableOn_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctFint_differentiableOn_band

end FormalResearch.SignUncertainty

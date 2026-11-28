/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasMollify
public import FormalResearch.SignUncertainty.CtBoasPartition
public import FormalResearch.SignUncertainty.CtBoasSmoothTaper

/-!
# Smooth localized block weights `ω_{j,ε}` (`ct:boas` Steps 3–4)

Defines the smooth near-field cutoff `nearCut`, the partition weights `nearOmega`, and their
`ε = c^{-5/6}` mollifications `nearWeight`:
- `one_sub_boasSf_tail_le`: Gaussian tail bound `1 - 𝔰_far ≤ exp(-20 log c)` for `L ≥ nearB c - 1`;
- `sum_nearOmega_eq`: exact identity `∑_{j < N} nearOmega j = ctTaper * (1 - 𝔰_far) * nearCut`;
- `exists_near_weights`: for `c₁ ≤ c₁₀`, `c ≥ c₀(c₁)`, every `nearWeight j` is `C^∞`, supported in
  `[L_j - ℓ_j/100, L_j + ℓ_j/100] ⊆ (ctLv0 c / 4, nearB c + 1)`, satisfies the `τ₀`-Harnack window
  `0.9 τ_j ≤ τ₀(L) ≤ 1.1 τ_j` and `L - L_j ≤ (2/5) Δ_{3/2}(τ_j)`, has `r`-th derivative bound
  `≤ C_m(r) (c^{5/6})^r`, and `∑_{j < N} |nearWeight j - nearOmega j| ≤ c^{-4/3}`.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies

/-! ### Definitions -/

/-- Upper cutoff `nearB c := log(π² log c) + 2` (`nearB c + 1 = log(π² log c) + 3`). -/
noncomputable def nearB (c : ℝ) : ℝ :=
  Real.log (π ^ 2 * Real.log c) + 2

/-- Smooth window identically `1` on `[ctLv0 c, nearB c - 1]` and `0` outside `[ctLv0 c / 2, nearB c]`. -/
noncomputable def nearCut (c L : ℝ) : ℝ :=
  smoothStep (ctLv0 c / 2) (ctLv0 c) L * (1 - smoothStep (nearB c - 1) (nearB c) L)

/-- Localized unmollified near-field block weight `ω_j = w̃_R · (1 - 𝔰_far) · nearCut · χ_j`. -/
noncomputable def nearOmega (ε c R : ℝ) (j : ℕ) (L : ℝ) : ℝ :=
  ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L *
    partChi (ctLv0 c / 4) j L

/-- Mollification scale `ε_m(c) = c^{-5/6}`. -/
noncomputable def nearEps (c : ℝ) : ℝ := c ^ (-(5 / 6 : ℝ))

/-- Smooth mollified block weight `ω_{j,ε} = ρ_{ε_m} * ω_j`. -/
noncomputable def nearWeight (ε c R : ℝ) (j : ℕ) (L : ℝ) : ℝ :=
  mollConv (nearEps c) (nearOmega ε c R j) L

/-! ### Localized `C^{1,1}` calculus and product helper -/

private structure LipBlock (A B : ℝ) where
  fn : ℝ → ℝ
  drv : ℝ → ℝ
  hd : ∀ x ∈ Icc A B, HasDerivAt fn (drv x) x
  m0 : ℝ
  m1 : ℝ
  m2 : ℝ
  hm0 : ∀ x ∈ Icc A B, |fn x| ≤ m0
  hm1 : ∀ x ∈ Icc A B, |drv x| ≤ m1
  hm2 : ∀ x ∈ Icc A B, ∀ y ∈ Icc A B, |drv x - drv y| ≤ m2 * |x - y|
  nn0 : 0 ≤ m0
  nn1 : 0 ≤ m1
  nn2 : 0 ≤ m2

private noncomputable def LipBlock.mul {A B : ℝ} (g h : LipBlock A B) : LipBlock A B where
  fn := fun x => g.fn x * h.fn x
  drv := fun x => g.drv x * h.fn x + g.fn x * h.drv x
  hd := fun x hx => (g.hd x hx).mul (h.hd x hx)
  m0 := g.m0 * h.m0
  m1 := g.m1 * h.m0 + g.m0 * h.m1
  m2 := g.m2 * h.m0 + 2 * g.m1 * h.m1 + g.m0 * h.m2
  hm0 := fun x hx => by
    rw [abs_mul]; exact mul_le_mul (g.hm0 x hx) (h.hm0 x hx) (abs_nonneg _) g.nn0
  hm1 := fun x hx => by
    calc |g.drv x * h.fn x + g.fn x * h.drv x|
        ≤ |g.drv x * h.fn x| + |g.fn x * h.drv x| := abs_add_le _ _
      _ = |g.drv x| * |h.fn x| + |g.fn x| * |h.drv x| := by simp only [abs_mul]
      _ ≤ g.m1 * h.m0 + g.m0 * h.m1 :=
          add_le_add (mul_le_mul (g.hm1 x hx) (h.hm0 x hx) (abs_nonneg _) g.nn1)
            (mul_le_mul (g.hm0 x hx) (h.hm1 x hx) (abs_nonneg _) g.nn0)
  hm2 := fun x hx y hy => by
    have hglip : |g.fn x - g.fn y| ≤ g.m1 * |x - y| := by
      have hmv := (convex_Icc A B).norm_image_sub_le_of_norm_deriv_le (C := g.m1)
        (fun z hz => (g.hd z hz).differentiableAt)
        (fun z hz => by rw [Real.norm_eq_abs, (g.hd z hz).deriv]; exact g.hm1 z hz) hy hx
      simpa [Real.norm_eq_abs, Real.dist_eq] using hmv
    have hhlip : |h.fn x - h.fn y| ≤ h.m1 * |x - y| := by
      have hmv := (convex_Icc A B).norm_image_sub_le_of_norm_deriv_le (C := h.m1)
        (fun z hz => (h.hd z hz).differentiableAt)
        (fun z hz => by rw [Real.norm_eq_abs, (h.hd z hz).deriv]; exact h.hm1 z hz) hy hx
      simpa [Real.norm_eq_abs, Real.dist_eq] using hmv
    have hid : (g.drv x * h.fn x + g.fn x * h.drv x) - (g.drv y * h.fn y + g.fn y * h.drv y) =
        (g.drv x - g.drv y) * h.fn x + g.drv y * (h.fn x - h.fn y) +
          (g.fn x - g.fn y) * h.drv x + g.fn y * (h.drv x - h.drv y) := by ring
    rw [hid]
    have h12 : |(g.drv x - g.drv y) * h.fn x| ≤ g.m2 * h.m0 * |x - y| := by
      rw [abs_mul]
      exact (mul_le_mul (g.hm2 x hx y hy) (h.hm0 x hx) (abs_nonneg _) (mul_nonneg g.nn2 (abs_nonneg _))).trans_eq
        (by ring)
    have h2 : |g.drv y * (h.fn x - h.fn y)| ≤ g.m1 * h.m1 * |x - y| := by
      rw [abs_mul]
      exact (mul_le_mul (g.hm1 y hy) hhlip (abs_nonneg _) g.nn1).trans_eq (by ring)
    have h3 : |(g.fn x - g.fn y) * h.drv x| ≤ g.m1 * h.m1 * |x - y| := by
      rw [abs_mul]
      exact (mul_le_mul hglip (h.hm1 x hx) (abs_nonneg _) (mul_nonneg g.nn1 (abs_nonneg _))).trans_eq (by ring)
    have h4 : |g.fn y * (h.drv x - h.drv y)| ≤ g.m0 * h.m2 * |x - y| := by
      rw [abs_mul]
      exact (mul_le_mul (g.hm0 y hy) (h.hm2 x hx y hy) (abs_nonneg _) g.nn0).trans_eq (by ring)
    calc _ ≤ |(g.drv x - g.drv y) * h.fn x + g.drv y * (h.fn x - h.fn y) + (g.fn x - g.fn y) * h.drv x| +
            |g.fn y * (h.drv x - h.drv y)| := abs_add_le _ _
      _ ≤ (|(g.drv x - g.drv y) * h.fn x + g.drv y * (h.fn x - h.fn y)| + |(g.fn x - g.fn y) * h.drv x|) +
            |g.fn y * (h.drv x - h.drv y)| := by gcongr; exact abs_add_le _ _
      _ ≤ ((|(g.drv x - g.drv y) * h.fn x| + |g.drv y * (h.fn x - h.fn y)|) + |(g.fn x - g.fn y) * h.drv x|) +
            |g.fn y * (h.drv x - h.drv y)| := by gcongr; exact abs_add_le _ _
      _ ≤ (g.m2 * h.m0 * |x - y| + g.m1 * h.m1 * |x - y| + g.m1 * h.m1 * |x - y|) + g.m0 * h.m2 * |x - y| := by
            gcongr
      _ = (g.m2 * h.m0 + 2 * g.m1 * h.m1 + g.m0 * h.m2) * |x - y| := by ring
  nn0 := mul_nonneg g.nn0 h.nn0
  nn1 := add_nonneg (mul_nonneg g.nn1 h.nn0) (mul_nonneg g.nn0 h.nn1)
  nn2 := add_nonneg (add_nonneg (mul_nonneg g.nn2 h.nn0) (mul_nonneg (mul_nonneg (by norm_num) g.nn1) h.nn1))
    (mul_nonneg g.nn0 h.nn2)

private lemma secDiff_le_of_lipBlock {A B : ℝ} (b : LipBlock A B) {x y : ℝ}
    (hlo : x - |y| ∈ Icc A B) (hhi : x + |y| ∈ Icc A B) :
    |b.fn (x + y) - 2 * b.fn x + b.fn (x - y)| ≤ b.m2 * y ^ 2 := by
  have hc_on : ContinuousOn b.drv (Icc A B) := fun u hu => by
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hm2_pos : 0 < b.m2 + 1 := add_pos_of_nonneg_of_pos b.nn2 zero_lt_one
    refine ⟨ε / (b.m2 + 1), div_pos hε hm2_pos, fun {v} hv hdist => ?_⟩
    rw [Real.dist_eq] at hdist ⊢
    calc |b.drv v - b.drv u| ≤ b.m2 * |v - u| := b.hm2 v hv u hu
      _ ≤ (b.m2 + 1) * |v - u| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ < (b.m2 + 1) * (ε / (b.m2 + 1)) := mul_lt_mul_of_pos_left hdist hm2_pos
      _ = ε := mul_div_cancel₀ ε hm2_pos.ne'
  have nonneg_case : ∀ t : ℝ, 0 ≤ t → t ≤ |y| → |b.fn (x + t) - 2 * b.fn x + b.fn (x - t)| ≤ b.m2 * t ^ 2 := by
    intro t ht hty
    have hmap1 : MapsTo (fun s : ℝ => x + s) (Icc 0 t) (Icc A B) := fun s hs =>
      ⟨by linarith [hlo.1, abs_nonneg y, hs.1], by linarith [hhi.2, hs.2, hty]⟩
    have hmap2 : MapsTo (fun s : ℝ => x - s) (Icc 0 t) (Icc A B) := fun s hs =>
      ⟨by linarith [hlo.1, hs.2, hty], by linarith [hhi.2, abs_nonneg y, hs.1]⟩
    have hc1 : ContinuousOn (fun s => b.drv (x + s)) (Icc 0 t) :=
      hc_on.comp (continuous_const.add continuous_id).continuousOn hmap1
    have hc2 : ContinuousOn (fun s => b.drv (x - s)) (Icc 0 t) :=
      hc_on.comp (continuous_const.sub continuous_id).continuousOn hmap2
    have h1 : b.fn (x + t) - b.fn x = ∫ s in (0 : ℝ)..t, b.drv (x + s) := by
      have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => b.fn (x + s))
        (f' := fun s => b.drv (x + s)) (fun s hs => by
          rw [Set.uIcc_of_le ht] at hs
          exact ((b.hd (x + s) (hmap1 hs)).comp s ((hasDerivAt_id s).const_add x)).congr_deriv (by ring))
        (hc1.intervalIntegrable_of_Icc ht)
      rw [hid]; simp
    have h2 : b.fn x - b.fn (x - t) = ∫ s in (0 : ℝ)..t, b.drv (x - s) := by
      have hid := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => -b.fn (x - s))
        (f' := fun s => b.drv (x - s)) (fun s hs => by
          rw [Set.uIcc_of_le ht] at hs
          exact (((b.hd (x - s) (hmap2 hs)).comp s ((hasDerivAt_id s).const_sub x)).neg).congr_deriv (by ring))
        (hc2.intervalIntegrable_of_Icc ht)
      rw [hid]; simp; ring
    have hid : b.fn (x + t) - 2 * b.fn x + b.fn (x - t) = ∫ s in (0 : ℝ)..t, (b.drv (x + s) - b.drv (x - s)) := by
      rw [show b.fn (x + t) - 2 * b.fn x + b.fn (x - t) = (b.fn (x + t) - b.fn x) - (b.fn x - b.fn (x - t)) by ring, h1, h2]
      exact (intervalIntegral.integral_sub (hc1.intervalIntegrable_of_Icc ht) (hc2.intervalIntegrable_of_Icc ht)).symm
    rw [hid]
    have hbd : ∀ s ∈ Icc (0 : ℝ) t, |b.drv (x + s) - b.drv (x - s)| ≤ b.m2 * (2 * s) := fun s hs => by
      refine (b.hm2 (x + s) (hmap1 hs) (x - s) (hmap2 hs)).trans_eq ?_
      have : x + s - (x - s) = 2 * s := by ring
      rw [this, abs_of_nonneg (by linarith [hs.1])]
    have hint2 : ∫ s in (0 : ℝ)..t, b.m2 * (2 * s) = b.m2 * t ^ 2 := by
      rw [intervalIntegral.integral_const_mul]
      have hsq : ∫ s in (0 : ℝ)..t, (2 * s) = t ^ 2 := by
        have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => s ^ 2)
          (fun s _ => by simpa using hasDerivAt_pow 2 s)
          ((continuous_const.mul continuous_id).intervalIntegrable 0 t)
        simpa using h.trans (by simp)
      rw [hsq]
    have hint_diff : IntervalIntegrable (fun s => |b.drv (x + s) - b.drv (x - s)|) volume 0 t :=
      (hc1.sub hc2).abs.intervalIntegrable_of_Icc ht
    have hint_R : IntervalIntegrable (fun s => b.m2 * (2 * s)) volume 0 t :=
      (continuous_const.mul (continuous_const.mul continuous_id)).intervalIntegrable 0 t
    calc |∫ s in (0 : ℝ)..t, (b.drv (x + s) - b.drv (x - s))|
        ≤ ∫ s in (0 : ℝ)..t, |b.drv (x + s) - b.drv (x - s)| := by
          simpa only [Real.norm_eq_abs] using intervalIntegral.abs_integral_le_integral_abs ht
      _ ≤ ∫ s in (0 : ℝ)..t, b.m2 * (2 * s) :=
          intervalIntegral.integral_mono_on ht hint_diff hint_R hbd
      _ = b.m2 * t ^ 2 := hint2
  rcases le_or_gt 0 y with hy | hy
  · exact nonneg_case y hy (le_abs_self y)
  · have h1 := nonneg_case (-y) (by linarith) (by rw [abs_of_neg hy])
    have e1 : b.fn (x + -y) - 2 * b.fn x + b.fn (x - -y) = b.fn (x + y) - 2 * b.fn x + b.fn (x - y) := by
      rw [sub_neg_eq_add, ← sub_eq_add_neg]; ring
    rw [e1, neg_sq] at h1
    exact h1

/-! ### `1 - 𝔰_far` bounds and Gaussian tail -/

lemma one_sub_boasSf_bounds {c : ℝ} (hc : 1 < c) (L : ℝ) :
    0 ≤ 1 - sFar c (c * (Real.exp L / π ^ 2)) ∧ 1 - sFar c (c * (Real.exp L / π ^ 2)) ≤ 1 := by
  have hW : 0 < farW c := by unfold farW; linarith
  set Δ := c * (Real.exp L / π ^ 2)
  have h0 : 0 ≤ sFar c Δ := sFar_nonneg hc Δ
  have h1 : sFar c Δ ≤ 1 := by
    unfold sFar
    have hall : ∫ x : ℝ, gaussK (farW c) (Δ - x) = 1 := by
      rw [integral_sub_left_eq_self (gaussK (farW c)) volume Δ]; exact integral_gaussK hW
    calc ∫ x in Ioi (farD c), gaussK (farW c) (Δ - x)
        ≤ ∫ x : ℝ, gaussK (farW c) (Δ - x) :=
          setIntegral_le_integral ((integrable_gaussK hW).comp_sub_left Δ)
            (ae_of_all _ fun x => gaussK_nonneg' _ _ hW)
      _ = 1 := hall
  exact ⟨by linarith, by linarith⟩

lemma one_sub_boasSf_tail_le {c : ℝ} (hc : Real.exp 2 ≤ c) {L : ℝ} (hL : nearB c - 1 ≤ L) :
    0 ≤ 1 - sFar c (c * (Real.exp L / π ^ 2)) ∧
      1 - sFar c (c * (Real.exp L / π ^ 2)) ≤ Real.exp (-20 * Real.log c) := by
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]) hc
  have hc0 : 0 < c := by linarith
  have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hc
  have hW : 0 < farW c := by unfold farW; linarith
  have hD : 0 < farD c := farD_pos hc1
  set Δ := c * (Real.exp L / π ^ 2)
  refine ⟨(one_sub_boasSf_bounds hc1 L).1, ?_⟩
  have hΔ_ge : Real.exp 1 * farD c ≤ Δ := by
    have h1 : Real.exp (Real.log (π ^ 2 * Real.log c) + 1) ≤ Real.exp L := by
      apply Real.exp_le_exp.2
      unfold nearB at hL; linarith
    rw [Real.exp_add, Real.exp_log (by positivity)] at h1
    have hpi : 0 < π ^ 2 := by positivity
    calc Real.exp 1 * farD c = c * ((π ^ 2 * Real.log c * Real.exp 1) / π ^ 2) := by
          unfold farD; field_simp
      _ ≤ c * (Real.exp L / π ^ 2) := by gcongr
  have he1 : (2.71 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hsub : 1.71 * farD c ≤ Δ - farD c := by nlinarith [hD]
  have heq : 1 - sFar c Δ = ∫ x in Iic (farD c), gaussK (farW c) (Δ - x) := by
    have hall : ∫ x : ℝ, gaussK (farW c) (Δ - x) = 1 := by
      rw [integral_sub_left_eq_self (gaussK (farW c)) volume Δ]; exact integral_gaussK hW
    have hsplit := integral_add_compl (measurableSet_Iic (a := farD c))
      ((integrable_gaussK hW).comp_sub_left Δ)
    have hcompl : (Iic (farD c))ᶜ = Ioi (farD c) := by ext x; simp
    rw [hall, hcompl] at hsplit
    unfold sFar; linarith
  rw [heq]
  have hg := gaussK_set_le hW (measurableSet_Iic (a := farD c)) Δ (1.71 * farD c)
    (fun x hx => by
      simp only [Set.mem_Iic] at hx
      rw [abs_of_nonneg (by linarith [hD])]
      linarith) (by positivity)
  have hexp_le : (1.71 * farD c) ^ 2 / (4 * farW c ^ 2) ≥ 23 * Real.log c := by
    have e : (1.71 * farD c) ^ 2 / (4 * farW c ^ 2) = 4 * 1.71 ^ 2 * Real.log c ^ 2 := by
      unfold farD farW; field_simp
    rw [e]
    calc 23 * Real.log c ≤ 4 * 1.71 ^ 2 * (2 * Real.log c) := by nlinarith
      _ ≤ 4 * 1.71 ^ 2 * (Real.log c * Real.log c) := by gcongr
      _ = 4 * 1.71 ^ 2 * Real.log c ^ 2 := by ring
  have hsq2 : √2 ≤ Real.exp (Real.log c) := by
    rw [Real.exp_log hc0]
    have : √2 < 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
    have hc2 : 2 ≤ c := le_trans (by
      have := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      linarith [sq_nonneg (Real.exp 1 - 2.7)]) hc
    linarith
  calc ∫ x in Iic (farD c), gaussK (farW c) (Δ - x)
      ≤ √2 * Real.exp (-((1.71 * farD c) ^ 2 / (4 * farW c ^ 2))) := hg
    _ ≤ Real.exp (Real.log c) * Real.exp (-23 * Real.log c) := by
          gcongr
          linarith
    _ = Real.exp (-22 * Real.log c) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-20 * Real.log c) := Real.exp_le_exp.2 (by linarith)

/-! ### `nearCut`, partition sum, `nearWeight` smoothness and error bounds -/

lemma nearCut_bounds (c L : ℝ) : 0 ≤ nearCut c L ∧ nearCut c L ≤ 1 := by
  unfold nearCut
  have h1 := smoothStep_nonneg (ctLv0 c / 2) (ctLv0 c) L
  have h2 := smoothStep_le_one (ctLv0 c / 2) (ctLv0 c) L
  have h3 := smoothStep_nonneg (nearB c - 1) (nearB c) L
  have h4 := smoothStep_le_one (nearB c - 1) (nearB c) L
  exact ⟨mul_nonneg h1 (by linarith), mul_le_of_le_one_left (by linarith) h2 |>.trans (by linarith)⟩

lemma nearCut_eq_zero_of_not_mem {c : ℝ} (hL0 : 0 < ctLv0 c) {L : ℝ}
    (hL : L ∉ Icc (ctLv0 c / 2) (nearB c)) : nearCut c L = 0 := by
  unfold nearCut
  rw [Set.mem_Icc] at hL; push Not at hL
  rcases lt_or_ge L (ctLv0 c / 2) with h | h
  · rw [smoothStep_zero_of_le (by linarith) h.le, zero_mul]
  · rw [smoothStep_one_of_le (by linarith : nearB c - 1 < nearB c) (hL h).le, sub_self, mul_zero]

lemma nearCut_eq_one_of_mem {c : ℝ} (_hL0 : 0 < ctLv0 c) (_hB : ctLv0 c ≤ nearB c - 1)
    {L : ℝ} (hL : L ∈ Icc (ctLv0 c) (nearB c - 1)) : nearCut c L = 1 := by
  unfold nearCut
  rw [smoothStep_one_of_le (by linarith) hL.1, smoothStep_zero_of_le (by linarith) hL.2, sub_zero, mul_one]

lemma sum_nearOmega_eq {ε c R : ℝ} (hL0 : 0 < ctLv0 c) (hL1 : ctLv0 c / 4 ≤ 1)
    (hB : 1 ≤ nearB c) (L : ℝ) :
    ∑ j ∈ Finset.range (partCount (ctLv0 c / 4) (nearB c)), nearOmega ε c R j L =
      ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L := by
  obtain ⟨_, _, _, _, hpart⟩ := part_facts
  have hpart_ab := (hpart (A := ctLv0 c / 4) (B := nearB c) (by positivity) hL1 hB).2.1
  have e : ∑ j ∈ Finset.range (partCount (ctLv0 c / 4) (nearB c)), nearOmega ε c R j L =
      ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L *
        ∑ j ∈ Finset.range (partCount (ctLv0 c / 4) (nearB c)), partChi (ctLv0 c / 4) j L := by
    unfold nearOmega; rw [Finset.mul_sum]
  rw [e]
  by_cases hmem : L ∈ Icc (ctLv0 c / 2) (nearB c)
  · have hmem' : L ∈ Icc (ctLv0 c / 4) (nearB c) := ⟨by linarith [hmem.1], hmem.2⟩
    rw [hpart_ab L hmem', mul_one]
  · rw [nearCut_eq_zero_of_not_mem hL0 hmem, mul_zero, zero_mul]

private lemma nearOmega_continuous {ε c R : ℝ} (_hc0 : 0 < c) (hc1 : 1 < c) (hL0 : 0 < ctLv0 c)
    (htd : ∀ L ∈ Ioi (0 : ℝ), ∃ g : ℝ, HasDerivAt (ctTaper ε c R) g L) (j : ℕ) :
    Continuous (nearOmega ε c R j) := by
  rw [continuous_iff_continuousAt]
  intro L
  rcases lt_or_ge L (ctLv0 c / 2) with hlt | hge
  · have hev : nearOmega ε c R j =ᶠ[𝓝 L] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hlt] with x hx
      unfold nearOmega
      rw [nearCut_eq_zero_of_not_mem hL0 (fun hm => not_le.2 (Set.mem_Iio.1 hx) hm.1), mul_zero, zero_mul]
    exact continuousAt_const.congr hev.symm
  · have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hge
    obtain ⟨g, hg⟩ := htd L hL_pos
    have hc_tap : ContinuousAt (ctTaper ε c R) L := hg.continuousAt
    have hc_sf : ContinuousAt (fun x => 1 - sFar c (c * (Real.exp x / π ^ 2))) L :=
      (hasDerivAt_one_sub_boasSf hc1 L).continuousAt
    have hc_cut : ContinuousAt (nearCut c) L :=
      ((contDiff_smoothStep _ _).continuous.mul
        (continuous_const.sub (contDiff_smoothStep _ _).continuous)).continuousAt
    have hc_chi : ContinuousAt (partChi (ctLv0 c / 4) j) L :=
      ((contDiff_smoothStep _ _).continuous.sub (contDiff_smoothStep _ _).continuous).continuousAt
    exact ((hc_tap.mul hc_sf).mul hc_cut).mul hc_chi

private noncomputable def nearCm2 (a₀ C₁ C₂ S1 S2 K1 K2 : ℝ) : ℝ :=
  let b₀ := a₀ / 16
  let C_s1 := 2 * S1 / a₀ + S1 + 1
  let C_s2 := 4 * S2 / a₀ ^ 2 + 2 * (2 * S1 / a₀) * S1 + S2 + 1
  let C_p1 := K1 / b₀ + K1 + 1
  let C_p2 := K2 / b₀ ^ 2 + K2 + 1
  let C_34_1 := C_s1 + C_p1
  let C_34_2 := C_s2 + 2 * C_s1 * C_p1 + C_p2
  let C_12_1 := C₁ + 85
  let C_12_2 := C₂ + 2 * C₁ * 85 + 600000
  C_12_2 + 2 * C_12_1 * C_34_1 + C_34_2

private lemma nearCm2_nonneg {a₀ C₁ C₂ S1 S2 K1 K2 : ℝ} (ha₀ : 0 < a₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) :
    0 ≤ nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 := by
  unfold nearCm2; positivity

private lemma near_prod_m2_le {A_i B_i c a₀ C₁ C₂ S1 S2 K1 K2 ℓj : ℝ}
    (hc1 : 1 < c) (hL0 : 0 < ctLv0 c) (ha₀ : 0 < a₀) (hℓ0 : 0 < ℓj) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hL0_inv : (ctLv0 c)⁻¹ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ))
    (hℓ_inv : ℓj⁻¹ ≤ (a₀ / 16)⁻¹ * c ^ (2 / 21 : ℝ))
    {hB1 hB2 hB3a hB3b hB4 : LipBlock A_i B_i}
    (hm1 : hB1.m0 = 1 ∧ hB1.m1 = C₁ ∧ hB1.m2 = C₂)
    (hm2 : hB2.m0 = 1 ∧ hB2.m1 = 85 * (1 + Real.log c) ∧ hB2.m2 = 600000 * (1 + Real.log c) ^ 3)
    (hm3a : hB3a.m0 = 1 ∧ hB3a.m1 = 2 * S1 * (ctLv0 c)⁻¹ ∧ hB3a.m2 = 4 * S2 * (ctLv0 c)⁻¹ ^ 2)
    (hm3b : hB3b.m0 = 1 ∧ hB3b.m1 = S1 ∧ hB3b.m2 = S2)
    (hm4 : hB4.m0 = 1 ∧ hB4.m1 = K1 / ℓj ∧ hB4.m2 = K2 / ℓj ^ 2) :
    ((hB1.mul hB2).mul ((hB3a.mul hB3b).mul hB4)).m2 ≤
      nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) := by
  have hc0 : 0 < c := by linarith only [hc1]
  have hlog1 : 1 ≤ 1 + Real.log c := by linarith only [Real.log_pos hc1]
  have hc21_pos : 0 < c ^ (2 / 21 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hc21_ge1 : 1 ≤ c ^ (2 / 21 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hc421 : 1 ≤ c ^ (4 / 21 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  set b₀ := a₀ / 16
  have hb₀_pos : 0 < b₀ := by positivity
  set C_s1 := 2 * S1 / a₀ + S1 + 1
  set C_s2 := 4 * S2 / a₀ ^ 2 + 2 * (2 * S1 / a₀) * S1 + S2 + 1
  set C_p1 := K1 / b₀ + K1 + 1
  set C_p2 := K2 / b₀ ^ 2 + K2 + 1
  set C_34_1 := C_s1 + C_p1
  set C_34_2 := C_s2 + 2 * C_s1 * C_p1 + C_p2
  set C_12_1 := C₁ + 85
  set C_12_2 := C₂ + 2 * C₁ * 85 + 600000
  have hCs1_nn : 0 ≤ C_s1 := by positivity
  have hCs2_nn : 0 ≤ C_s2 := by positivity
  have hCp1_nn : 0 ≤ C_p1 := by positivity
  have hCp2_nn : 0 ≤ C_p2 := by positivity
  have hC341_nn : 0 ≤ C_34_1 := by positivity
  have hC121_nn : 0 ≤ C_12_1 := by positivity
  have hB3_m1 : (hB3a.mul hB3b).m1 ≤ C_s1 * c ^ (2 / 21 : ℝ) := by
    have h1 : 2 * S1 * (ctLv0 c)⁻¹ ≤ 2 * S1 / a₀ * c ^ (2 / 21 : ℝ) :=
      (mul_le_mul_of_nonneg_left hL0_inv (by positivity)).trans_eq (by rw [div_eq_mul_inv]; ring)
    have h2 : S1 ≤ S1 * c ^ (2 / 21 : ℝ) := le_mul_of_one_le_right hS1 hc21_ge1
    calc (hB3a.mul hB3b).m1 = 2 * S1 * (ctLv0 c)⁻¹ * 1 + 1 * S1 := by
          change hB3a.m1 * hB3b.m0 + hB3a.m0 * hB3b.m1 = _; rw [hm3a.1, hm3a.2.1, hm3b.1, hm3b.2.1]
      _ = 2 * S1 * (ctLv0 c)⁻¹ + S1 := by rw [mul_one, one_mul]
      _ ≤ 2 * S1 / a₀ * c ^ (2 / 21 : ℝ) + S1 * c ^ (2 / 21 : ℝ) := add_le_add h1 h2
      _ = (2 * S1 / a₀ + S1) * c ^ (2 / 21 : ℝ) := by ring
      _ ≤ C_s1 * c ^ (2 / 21 : ℝ) := mul_le_mul_of_nonneg_right (by dsimp only [C_s1]; linarith only) hc21_pos.le
  have hB3_m2 : (hB3a.mul hB3b).m2 ≤ C_s2 * c ^ (4 / 21 : ℝ) := by
    have hsq_inv : (ctLv0 c)⁻¹ ^ 2 ≤ a₀⁻¹ ^ 2 * c ^ (4 / 21 : ℝ) := by
      calc (ctLv0 c)⁻¹ ^ 2 ≤ (a₀⁻¹ * c ^ (2 / 21 : ℝ)) ^ 2 := pow_le_pow_left₀ (by positivity) hL0_inv 2
        _ = a₀⁻¹ ^ 2 * c ^ (4 / 21 : ℝ) := by
            rw [mul_pow, ← Real.rpow_natCast (c ^ (2 / 21 : ℝ)) 2, ← Real.rpow_mul hc0.le,
              show (2 / 21 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 21 by norm_num]
    have h1 : 4 * S2 * (ctLv0 c)⁻¹ ^ 2 ≤ (4 * S2 / a₀ ^ 2) * c ^ (4 / 21 : ℝ) :=
      (mul_le_mul_of_nonneg_left hsq_inv (by positivity)).trans_eq (by rw [div_eq_mul_inv, inv_pow]; ring)
    have h2 : 2 * (2 * S1 * (ctLv0 c)⁻¹) * S1 ≤ 2 * (2 * S1 / a₀) * S1 * c ^ (2 / 21 : ℝ) := by
      calc 2 * (2 * S1 * (ctLv0 c)⁻¹) * S1 = (2 * (2 * S1)) * (ctLv0 c)⁻¹ * S1 := by ring
        _ ≤ (2 * (2 * S1)) * (a₀⁻¹ * c ^ (2 / 21 : ℝ)) * S1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL0_inv (by positivity)) hS1
        _ = 2 * (2 * S1 / a₀) * S1 * c ^ (2 / 21 : ℝ) := by rw [div_eq_mul_inv]; ring
    have h2' : 2 * (2 * S1 / a₀) * S1 * c ^ (2 / 21 : ℝ) ≤ 2 * (2 * S1 / a₀) * S1 * c ^ (4 / 21 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)) (by positivity)
    have h3 : S2 ≤ S2 * c ^ (4 / 21 : ℝ) := le_mul_of_one_le_right hS2 hc421
    calc (hB3a.mul hB3b).m2 = 4 * S2 * (ctLv0 c)⁻¹ ^ 2 * 1 + 2 * (2 * S1 * (ctLv0 c)⁻¹) * S1 + 1 * S2 := by
          change hB3a.m2 * hB3b.m0 + 2 * hB3a.m1 * hB3b.m1 + hB3a.m0 * hB3b.m2 = _
          rw [hm3a.1, hm3a.2.1, hm3a.2.2, hm3b.1, hm3b.2.1, hm3b.2.2]
      _ = 4 * S2 * (ctLv0 c)⁻¹ ^ 2 + 2 * (2 * S1 * (ctLv0 c)⁻¹) * S1 + S2 := by rw [mul_one, one_mul]
      _ ≤ (4 * S2 / a₀ ^ 2) * c ^ (4 / 21 : ℝ) + 2 * (2 * S1 / a₀) * S1 * c ^ (4 / 21 : ℝ) + S2 * c ^ (4 / 21 : ℝ) :=
          add_le_add (add_le_add h1 (h2.trans h2')) h3
      _ = (4 * S2 / a₀ ^ 2 + 2 * (2 * S1 / a₀) * S1 + S2) * c ^ (4 / 21 : ℝ) := by ring
      _ ≤ C_s2 * c ^ (4 / 21 : ℝ) := mul_le_mul_of_nonneg_right (by dsimp only [C_s2]; linarith only) (by positivity)
  have h12_1 : (hB1.mul hB2).m1 ≤ C_12_1 * (1 + Real.log c) := by
    have hC1_le : C₁ ≤ C₁ * (1 + Real.log c) := le_mul_of_one_le_right hC₁ hlog1
    calc (hB1.mul hB2).m1 = C₁ * 1 + 1 * (85 * (1 + Real.log c)) := by
          change hB1.m1 * hB2.m0 + hB1.m0 * hB2.m1 = _; rw [hm1.1, hm1.2.1, hm2.1, hm2.2.1]
      _ = C₁ + 85 * (1 + Real.log c) := by rw [mul_one, one_mul]
      _ ≤ C₁ * (1 + Real.log c) + 85 * (1 + Real.log c) := add_le_add hC1_le le_rfl
      _ = C_12_1 * (1 + Real.log c) := by dsimp only [C_12_1]; ring
  have h12_2 : (hB1.mul hB2).m2 ≤ C_12_2 * (1 + Real.log c) ^ 3 := by
    have hlog3_1 : 1 ≤ (1 + Real.log c) ^ 3 := one_le_pow₀ hlog1
    have hlog3_2 : 1 + Real.log c ≤ (1 + Real.log c) ^ 3 := le_self_pow₀ hlog1 (by norm_num)
    have t1 : C₂ * 1 ≤ C₂ * (1 + Real.log c) ^ 3 := by rw [mul_one]; exact le_mul_of_one_le_right hC₂ hlog3_1
    have t2 : 2 * C₁ * (85 * (1 + Real.log c)) ≤ 2 * C₁ * 85 * (1 + Real.log c) ^ 3 := by
      calc 2 * C₁ * (85 * (1 + Real.log c)) = 2 * C₁ * 85 * (1 + Real.log c) := by ring
        _ ≤ 2 * C₁ * 85 * (1 + Real.log c) ^ 3 := mul_le_mul_of_nonneg_left hlog3_2 (by positivity)
    calc (hB1.mul hB2).m2 = C₂ * 1 + 2 * C₁ * (85 * (1 + Real.log c)) + 1 * (600000 * (1 + Real.log c) ^ 3) := by
          change hB1.m2 * hB2.m0 + 2 * hB1.m1 * hB2.m1 + hB1.m0 * hB2.m2 = _
          rw [hm1.1, hm1.2.1, hm1.2.2, hm2.1, hm2.2.1, hm2.2.2]
      _ = C₂ * 1 + 2 * C₁ * (85 * (1 + Real.log c)) + 600000 * (1 + Real.log c) ^ 3 := by rw [one_mul]
      _ ≤ C₂ * (1 + Real.log c) ^ 3 + 2 * C₁ * 85 * (1 + Real.log c) ^ 3 + 600000 * (1 + Real.log c) ^ 3 :=
          add_le_add (add_le_add t1 t2) le_rfl
      _ = C_12_2 * (1 + Real.log c) ^ 3 := by dsimp only [C_12_2]; ring
  have hB4_m1 : hB4.m1 ≤ C_p1 * c ^ (2 / 21 : ℝ) := by
    have h1 : K1 / ℓj ≤ K1 / b₀ * c ^ (2 / 21 : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact (mul_le_mul_of_nonneg_left hℓ_inv hK1).trans_eq (by ring)
    calc hB4.m1 = K1 / ℓj := hm4.2.1
      _ ≤ K1 / b₀ * c ^ (2 / 21 : ℝ) := h1
      _ ≤ (K1 / b₀ + K1 + 1) * c ^ (2 / 21 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hK1]) hc21_pos.le
  have hB4_m2 : hB4.m2 ≤ C_p2 * c ^ (4 / 21 : ℝ) := by
    have hsq : ℓj⁻¹ ^ 2 ≤ b₀⁻¹ ^ 2 * c ^ (4 / 21 : ℝ) := by
      calc ℓj⁻¹ ^ 2 ≤ (b₀⁻¹ * c ^ (2 / 21 : ℝ)) ^ 2 := pow_le_pow_left₀ (inv_nonneg.2 hℓ0.le) hℓ_inv 2
        _ = b₀⁻¹ ^ 2 * c ^ (4 / 21 : ℝ) := by
            rw [mul_pow, ← Real.rpow_natCast (c ^ (2 / 21 : ℝ)) 2, ← Real.rpow_mul hc0.le,
              show (2 / 21 : ℝ) * ((2 : ℕ) : ℝ) = 4 / 21 by norm_num]
    have h1 : K2 / ℓj ^ 2 ≤ K2 / b₀ ^ 2 * c ^ (4 / 21 : ℝ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, ← inv_pow, ← inv_pow]
      exact (mul_le_mul_of_nonneg_left hsq hK2).trans_eq (by ring)
    calc hB4.m2 = K2 / ℓj ^ 2 := hm4.2.2
      _ ≤ K2 / b₀ ^ 2 * c ^ (4 / 21 : ℝ) := h1
      _ ≤ (K2 / b₀ ^ 2 + K2 + 1) * c ^ (4 / 21 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hK2]) (by positivity)
  have h34_1 : ((hB3a.mul hB3b).mul hB4).m1 ≤ C_34_1 * c ^ (2 / 21 : ℝ) := by
    calc ((hB3a.mul hB3b).mul hB4).m1 = (hB3a.mul hB3b).m1 * 1 + 1 * hB4.m1 := by
          change (hB3a.mul hB3b).m1 * hB4.m0 + (hB3a.mul hB3b).m0 * hB4.m1 = _
          rw [hm4.1, show (hB3a.mul hB3b).m0 = 1 from by change hB3a.m0 * hB3b.m0 = 1; rw [hm3a.1, hm3b.1, mul_one]]
      _ = (hB3a.mul hB3b).m1 + hB4.m1 := by rw [mul_one, one_mul]
      _ ≤ C_s1 * c ^ (2 / 21 : ℝ) + C_p1 * c ^ (2 / 21 : ℝ) := add_le_add hB3_m1 hB4_m1
      _ = C_34_1 * c ^ (2 / 21 : ℝ) := by dsimp only [C_34_1]; ring
  have h34_2 : ((hB3a.mul hB3b).mul hB4).m2 ≤ C_34_2 * c ^ (4 / 21 : ℝ) := by
    have hc2_sq : c ^ (2 / 21 : ℝ) * c ^ (2 / 21 : ℝ) = c ^ (4 / 21 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    have h2m : 2 * (hB3a.mul hB3b).m1 * hB4.m1 ≤ 2 * C_s1 * C_p1 * c ^ (4 / 21 : ℝ) := by
      calc 2 * (hB3a.mul hB3b).m1 * hB4.m1
          ≤ 2 * (C_s1 * c ^ (2 / 21 : ℝ)) * (C_p1 * c ^ (2 / 21 : ℝ)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB3_m1 (by norm_num)) hB4_m1 hB4.nn1 (by positivity)
        _ = 2 * C_s1 * C_p1 * (c ^ (2 / 21 : ℝ) * c ^ (2 / 21 : ℝ)) := by ring
        _ = 2 * C_s1 * C_p1 * c ^ (4 / 21 : ℝ) := by rw [hc2_sq]
    calc ((hB3a.mul hB3b).mul hB4).m2 =
          (hB3a.mul hB3b).m2 * 1 + 2 * (hB3a.mul hB3b).m1 * hB4.m1 + 1 * hB4.m2 := by
            change (hB3a.mul hB3b).m2 * hB4.m0 + 2 * (hB3a.mul hB3b).m1 * hB4.m1 + (hB3a.mul hB3b).m0 * hB4.m2 = _
            rw [hm4.1, show (hB3a.mul hB3b).m0 = 1 from by change hB3a.m0 * hB3b.m0 = 1; rw [hm3a.1, hm3b.1, mul_one]]
      _ = (hB3a.mul hB3b).m2 + 2 * (hB3a.mul hB3b).m1 * hB4.m1 + hB4.m2 := by rw [mul_one, one_mul]
      _ ≤ C_s2 * c ^ (4 / 21 : ℝ) + 2 * C_s1 * C_p1 * c ^ (4 / 21 : ℝ) + C_p2 * c ^ (4 / 21 : ℝ) :=
          add_le_add (add_le_add hB3_m2 h2m) hB4_m2
      _ = C_34_2 * c ^ (4 / 21 : ℝ) := by dsimp only [C_34_2]; ring
  have hc_comb : (1 + Real.log c) * c ^ (2 / 21 : ℝ) ≤ (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) :=
    mul_le_mul (le_self_pow₀ hlog1 (by norm_num))
      (Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)) (by positivity) (by positivity)
  have h1_mul : 1 ≤ (1 + Real.log c) ^ 3 := one_le_pow₀ hlog1
  have h1t : (hB1.mul hB2).m2 * 1 ≤ C_12_2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) := by
    calc (hB1.mul hB2).m2 * 1 = (hB1.mul hB2).m2 * 1 := rfl
      _ ≤ (C_12_2 * (1 + Real.log c) ^ 3) * c ^ (4 / 21 : ℝ) :=
          mul_le_mul h12_2 hc421 zero_le_one (by positivity)
      _ = C_12_2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) := by ring
  have h2t : 2 * (hB1.mul hB2).m1 * ((hB3a.mul hB3b).mul hB4).m1 ≤
      2 * C_12_1 * C_34_1 * ((1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) := by
    calc 2 * (hB1.mul hB2).m1 * ((hB3a.mul hB3b).mul hB4).m1
        ≤ 2 * (C_12_1 * (1 + Real.log c)) * (C_34_1 * c ^ (2 / 21 : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h12_1 (by norm_num)) h34_1
            ((hB3a.mul hB3b).mul hB4).nn1 (by positivity)
      _ = 2 * C_12_1 * C_34_1 * ((1 + Real.log c) * c ^ (2 / 21 : ℝ)) := by ring
      _ ≤ 2 * C_12_1 * C_34_1 * ((1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) :=
          mul_le_mul_of_nonneg_left hc_comb (by positivity)
  have h3t : 1 * ((hB3a.mul hB3b).mul hB4).m2 ≤ C_34_2 * ((1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) := by
    calc 1 * ((hB3a.mul hB3b).mul hB4).m2
        ≤ (1 + Real.log c) ^ 3 * (C_34_2 * c ^ (4 / 21 : ℝ)) :=
          mul_le_mul h1_mul h34_2 ((hB3a.mul hB3b).mul hB4).nn2 (by positivity)
      _ = C_34_2 * ((1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) := by ring
  have h120 : (hB1.mul hB2).m0 = 1 := by change hB1.m0 * hB2.m0 = 1; rw [hm1.1, hm2.1, mul_one]
  have h340 : ((hB3a.mul hB3b).mul hB4).m0 = 1 := by
    change (hB3a.m0 * hB3b.m0) * hB4.m0 = 1; rw [hm3a.1, hm3b.1, hm4.1]; norm_num
  calc ((hB1.mul hB2).mul ((hB3a.mul hB3b).mul hB4)).m2
      = (hB1.mul hB2).m2 * 1 + 2 * (hB1.mul hB2).m1 * ((hB3a.mul hB3b).mul hB4).m1 +
          1 * ((hB3a.mul hB3b).mul hB4).m2 := by
            change (hB1.mul hB2).m2 * ((hB3a.mul hB3b).mul hB4).m0 +
              2 * (hB1.mul hB2).m1 * ((hB3a.mul hB3b).mul hB4).m1 +
              (hB1.mul hB2).m0 * ((hB3a.mul hB3b).mul hB4).m2 = _
            rw [h120, h340]
    _ ≤ C_12_2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) +
          2 * C_12_1 * C_34_1 * ((1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) +
          C_34_2 * ((1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) := add_le_add (add_le_add h1t h2t) h3t
    _ = nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) := by
          unfold nearCm2; ring

private lemma near_block_moll_err {ε c R a₀ C₁ C₂ S1 S2 K1 K2 : ℝ} {taperGrad : ℝ → ℝ}
    (hc1 : 1 < c) (hc3 : 3 ≤ c) (ha₀ : 0 < a₀) (hL0 : 0 < ctLv0 c)
    (hL0_inv : (ctLv0 c)⁻¹ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ)) (_hLB : ctLv0 c ≤ nearB c - 1)
    (heps_le : nearEps c ≤ ctLv0 c / 8) (heps_le1 : nearEps c ≤ 1 / 2)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (htap_d : ∀ L ∈ Ioi (0 : ℝ), HasDerivAt (ctTaper ε c R) (taperGrad L) L)
    (htap_bd : ∀ L ∈ Ioi (0 : ℝ), 0 ≤ ctTaper ε c R L ∧ ctTaper ε c R L ≤ 1)
    (htap_gbd : ∀ L, ctLv0 c / 4 ≤ L → |taperGrad L| ≤ C₁)
    (htap_glip : ∀ L₁ L₂, ctLv0 c / 4 ≤ L₁ → ctLv0 c / 4 ≤ L₂ → |taperGrad L₁ - taperGrad L₂| ≤ C₂ * |L₁ - L₂|)
    (hstepD : ∀ {a b : ℝ}, a < b → (∀ x, |deriv (smoothStep a b) x| ≤ S1 / (b - a)) ∧
      (∀ x y, |deriv (smoothStep a b) x - deriv (smoothStep a b) y| ≤ S2 / (b - a) ^ 2 * |x - y|))
    {j : ℕ} (hℓ0 : 0 < min (partGrid (ctLv0 c / 4) (j + 1)) 1)
    (hℓ_inv : (min (partGrid (ctLv0 c / 4) (j + 1)) 1)⁻¹ ≤ (a₀ / 16)⁻¹ * c ^ (2 / 21 : ℝ))
    (hchi_bd : ∀ x, 0 ≤ partChi (ctLv0 c / 4) j x ∧ partChi (ctLv0 c / 4) j x ≤ 1)
    (hchi_d1 : ∀ x, |deriv (partChi (ctLv0 c / 4) j) x| ≤ K1 / min (partGrid (ctLv0 c / 4) (j + 1)) 1)
    (hchi_d2 : ∀ x y, |deriv (partChi (ctLv0 c / 4) j) x - deriv (partChi (ctLv0 c / 4) j) y| ≤
      K2 / min (partGrid (ctLv0 c / 4) (j + 1)) 1 ^ 2 * |x - y|)
    (L : ℝ) :
    |nearWeight ε c R j L - nearOmega ε c R j L| ≤
      (1 / 2) * nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2 := by
  have hc0 : 0 < c := by linarith only [hc1]
  have hlog_nn : 0 ≤ 1 + Real.log c := by linarith only [Real.log_pos hc1]
  have heps_pos : 0 < nearEps c := Real.rpow_pos_of_pos hc0 _
  set A_i := ctLv0 c / 4
  set B_i := nearB c + 1
  have hB_eq : B_i = Real.log (π ^ 2 * Real.log c) + 3 := by dsimp only [B_i, nearB]; ring
  let ℓj := min (partGrid (ctLv0 c / 4) (j + 1)) 1
  let hB1 : LipBlock A_i B_i := {
    fn := ctTaper ε c R, drv := taperGrad,
    hd := fun x hx => htap_d x (show 0 < x by dsimp only [A_i] at hx; linarith only [hL0, hx.1]),
    m0 := 1, m1 := C₁, m2 := C₂,
    hm0 := fun x hx => by
      have hb := htap_bd x (show 0 < x by dsimp only [A_i] at hx; linarith only [hL0, hx.1])
      rw [abs_of_nonneg hb.1]; exact hb.2,
    hm1 := fun x hx => htap_gbd x hx.1,
    hm2 := fun x hx y hy => htap_glip x y hx.1 hy.1,
    nn0 := zero_le_one, nn1 := hC₁, nn2 := hC₂ }
  let hB2 : LipBlock A_i B_i := {
    fn := fun L => 1 - sFar c (c * (Real.exp L / π ^ 2)), drv := sfNegDeriv c,
    hd := fun x _ => hasDerivAt_one_sub_boasSf hc1 x,
    m0 := 1, m1 := 85 * (1 + Real.log c), m2 := 600000 * (1 + Real.log c) ^ 3,
    hm0 := fun x _ => by
      have hb := one_sub_boasSf_bounds hc1 x; rw [abs_of_nonneg hb.1]; exact hb.2,
    hm1 := fun x hx => (sfNegDeriv_bounds hc3 (by linarith only [hx.2, hB_eq])).1,
    hm2 := fun x hx y hy => sfNegDeriv_lip hc3 (by linarith only [hx.2, hB_eq]) (by linarith only [hy.2, hB_eq]),
    nn0 := zero_le_one, nn1 := mul_nonneg (by norm_num) hlog_nn, nn2 := mul_nonneg (by norm_num) (pow_nonneg hlog_nn 3) }
  let hB3a : LipBlock A_i B_i := {
    fn := smoothStep (ctLv0 c / 2) (ctLv0 c), drv := deriv (smoothStep (ctLv0 c / 2) (ctLv0 c)),
    hd := fun x _ => ((contDiff_smoothStep _ _).differentiable (by simp) x).hasDerivAt,
    m0 := 1, m1 := 2 * S1 * (ctLv0 c)⁻¹, m2 := 4 * S2 * (ctLv0 c)⁻¹ ^ 2,
    hm0 := fun x _ => by rw [abs_of_nonneg (smoothStep_nonneg _ _ _)]; exact smoothStep_le_one _ _ _,
    hm1 := fun x _ => by
      have := (hstepD (by linarith only [hL0] : ctLv0 c / 2 < ctLv0 c)).1 x
      refine this.trans_eq ?_; rw [show ctLv0 c - ctLv0 c / 2 = ctLv0 c / 2 by ring]; field_simp,
    hm2 := fun x _ y _ => by
      have := (hstepD (by linarith only [hL0] : ctLv0 c / 2 < ctLv0 c)).2 x y
      refine this.trans_eq ?_; rw [show ctLv0 c - ctLv0 c / 2 = ctLv0 c / 2 by ring]; field_simp; ring,
    nn0 := zero_le_one, nn1 := by positivity, nn2 := by positivity }
  let hB3b : LipBlock A_i B_i := {
    fn := fun L => 1 - smoothStep (nearB c - 1) (nearB c) L,
    drv := fun x => -deriv (smoothStep (nearB c - 1) (nearB c)) x,
    hd := fun x _ => (((contDiff_smoothStep _ _).differentiable (by simp) x).hasDerivAt.const_sub 1),
    m0 := 1, m1 := S1, m2 := S2,
    hm0 := fun x _ => by
      have h1 := smoothStep_nonneg (nearB c - 1) (nearB c) x
      have h2 := smoothStep_le_one (nearB c - 1) (nearB c) x
      rw [abs_of_nonneg (by linarith only [h2])]; linarith only [h1],
    hm1 := fun x _ => by rw [abs_neg]; simpa using (hstepD (by linarith only : nearB c - 1 < nearB c)).1 x,
    hm2 := fun x _ y _ => by
      rw [show -deriv (smoothStep (nearB c - 1) (nearB c)) x -
        -deriv (smoothStep (nearB c - 1) (nearB c)) y =
        -(deriv (smoothStep (nearB c - 1) (nearB c)) x -
          deriv (smoothStep (nearB c - 1) (nearB c)) y) by ring, abs_neg]
      simpa using (hstepD (by linarith only : nearB c - 1 < nearB c)).2 x y,
    nn0 := zero_le_one, nn1 := hS1, nn2 := hS2 }
  let hB4 : LipBlock A_i B_i := {
    fn := partChi (ctLv0 c / 4) j, drv := deriv (partChi (ctLv0 c / 4) j),
    hd := fun x _ => (((contDiff_smoothStep _ _).sub (contDiff_smoothStep _ _)).differentiable (by simp) x).hasDerivAt,
    m0 := 1, m1 := K1 / ℓj, m2 := K2 / ℓj ^ 2,
    hm0 := fun x _ => by rw [abs_of_nonneg (hchi_bd x).1]; exact (hchi_bd x).2,
    hm1 := fun x _ => hchi_d1 x,
    hm2 := fun x _ y _ => hchi_d2 x y,
    nn0 := zero_le_one, nn1 := by positivity, nn2 := by positivity }
  set hprod : LipBlock A_i B_i := (hB1.mul hB2).mul ((hB3a.mul hB3b).mul hB4)
  have hm2_le : hprod.m2 ≤ nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) :=
    near_prod_m2_le (ℓj := ℓj) (hB1 := hB1) (hB2 := hB2) (hB3a := hB3a) (hB3b := hB3b) (hB4 := hB4)
      hc1 hL0 ha₀ hℓ0 hC₁ hC₂ hS1 hS2 hK1 hK2 hL0_inv hℓ_inv
      ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl⟩
  have hfn_eq : hprod.fn = nearOmega ε c R j := by
    funext x; unfold nearOmega nearCut
    dsimp only [hprod, LipBlock.mul, hB1, hB2, hB3a, hB3b, hB4]; ring
  have hsec : ∀ y, |y| ≤ nearEps c →
      |nearOmega ε c R j (L + y) - 2 * nearOmega ε c R j L + nearOmega ε c R j (L - y)| ≤ hprod.m2 * y ^ 2 := by
    intro y hy
    rw [← hfn_eq]
    rcases le_or_gt L (ctLv0 c / 2 - nearEps c) with hlo | hlo
    · have h0 : ∀ t, t ≤ ctLv0 c / 2 → hprod.fn t = 0 := fun t ht => by
        rw [hfn_eq]; unfold nearOmega
        by_cases ht_eq : t < ctLv0 c / 2
        · rw [nearCut_eq_zero_of_not_mem hL0 (fun h => by linarith only [ht_eq, h.1]), mul_zero, zero_mul]
        · have heq : t = ctLv0 c / 2 := le_antisymm ht (not_lt.1 ht_eq)
          subst t; unfold nearCut
          rw [smoothStep_zero_of_le (by linarith only [hL0] : ctLv0 c / 2 < ctLv0 c) le_rfl]
          simp only [mul_zero, zero_mul]
      have ha := abs_le.1 hy
      rw [h0 (L + y) (by linarith only [hlo, ha.2]), h0 L (by linarith only [hlo, heps_pos]),
        h0 (L - y) (by linarith only [hlo, ha.1])]
      norm_num; exact mul_nonneg hprod.nn2 (sq_nonneg y)
    · rcases le_or_gt (nearB c + nearEps c) L with hhi | hhi
      · have h0 : ∀ t, nearB c ≤ t → hprod.fn t = 0 := fun t ht => by
          rw [hfn_eq]; unfold nearOmega
          by_cases ht_eq : nearB c < t
          · rw [nearCut_eq_zero_of_not_mem hL0 (fun h => by linarith only [ht_eq, h.2]), mul_zero, zero_mul]
          · have heq : t = nearB c := le_antisymm (not_lt.1 ht_eq) ht
            subst t; unfold nearCut
            rw [smoothStep_one_of_le (by linarith only : nearB c - 1 < nearB c) le_rfl, sub_self, mul_zero,
              mul_zero, zero_mul]
        have ha := abs_le.1 hy
        rw [h0 (L + y) (by linarith only [hhi, ha.1]), h0 L (by linarith only [hhi, heps_pos]),
          h0 (L - y) (by linarith only [hhi, ha.2])]
        norm_num; exact mul_nonneg hprod.nn2 (sq_nonneg y)
      · have ha := abs_le.1 hy
        exact secDiff_le_of_lipBlock hprod
          ⟨by dsimp only [A_i]; linarith only [hlo, heps_le, hy, abs_nonneg y],
            by dsimp only [B_i]; linarith only [hhi, heps_le1, hy, abs_nonneg y]⟩
          ⟨by dsimp only [A_i]; linarith only [hlo, heps_le, hy, abs_nonneg y],
            by dsimp only [B_i]; linarith only [hhi, heps_le1, hy, abs_nonneg y]⟩
  have hfb : ∀ y, |nearOmega ε c R j y| ≤ 1 := fun y => by
    unfold nearOmega
    by_cases hy0 : y ≤ 0
    · rw [nearCut_eq_zero_of_not_mem hL0 (fun h => by linarith only [hy0, hL0, h.1]), mul_zero, zero_mul, abs_zero]
      exact zero_le_one
    · rw [not_le] at hy0
      have ht := htap_bd y hy0
      have hsf := one_sub_boasSf_bounds hc1 y
      have hcu := nearCut_bounds c y
      have hch := hchi_bd y
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_nonneg hsf.1,
        abs_of_nonneg hcu.1, abs_of_nonneg hch.1]
      have h12 : ctTaper ε c R y * (1 - sFar c (c * (Real.exp y / π ^ 2))) ≤ 1 :=
        (mul_le_of_le_one_left hsf.1 ht.2).trans hsf.2
      have h123 : ctTaper ε c R y * (1 - sFar c (c * (Real.exp y / π ^ 2))) * nearCut c y ≤ 1 :=
        (mul_le_of_le_one_left hcu.1 h12).trans hcu.2
      exact (mul_le_of_le_one_left hch.1 h123).trans hch.2
  have hcont := nearOmega_continuous hc0 hc1 hL0 (fun x hx => ⟨taperGrad x, htap_d x hx⟩) j
  have hsub := mollConv_sub_le heps_pos hprod.nn2 hcont hfb hsec
  calc |nearWeight ε c R j L - nearOmega ε c R j L|
      ≤ 1 / 2 * hprod.m2 * nearEps c ^ 2 := hsub
    _ ≤ 1 / 2 * (nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ)) * nearEps c ^ 2 := by gcongr
    _ = (1 / 2) * nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2 := by ring

/--- **Near-field smooth block package** (`ct:boas` Steps 3–4):
for `c₁ ∈ (0, c₁₀]`, there exist `c₀ ≥ exp 2`, `κ_min > 0`, and derivative constants `C_m(r)`
such that for all `c ≥ c₀`, `ε = ±1`, `R ∈ [c₁² c^{2/3}, 4 c₁² c^{2/3}]`, writing
`N = partCount (ctLv0 c / 4) (nearB c)`:
1. `ctLv0 c ≤ nearB c - 1` and `(N : ℝ) ≤ 250 * Real.log (16 / ctLv0 c) + 200 * nearB c + 810`;
2. `∑_{j < N} nearOmega = ctTaper * (1 - 𝔰_far) * nearCut`;
3. every `nearWeight j` is `C^∞`, `0 ≤ nearWeight j ≤ 1`, supported in
   `[L_j - ℓ_j / 100, L_j + ℓ_j / 100] ⊆ (ctLv0 c / 4, nearB c + 1)`, satisfies the `τ₀`-Harnack
   bounds `0.9 τ_j ≤ τ₀(L) ≤ 1.1 τ_j` and `L - L_j ≤ (2/5) Δ_{3/2}(τ_j)` on its support,
   has `κ_min c^{-2/21} ≤ ℓ_j` and `κ_min c^{-1/21} ≤ τ_j`, and
   `|iteratedDeriv r (nearWeight j) L| ≤ C_m(r) (c^{5/6})^r`;
4. `∑_{j < N} |nearWeight j L - nearOmega j L| ≤ c^{-4/3}` everywhere. -/
theorem exists_near_weights : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → ∃ c₀ κ_min : ℝ, Real.exp 2 ≤ c₀ ∧ 0 < κ_min ∧
      ∃ C_m : ℕ → ℝ, (∀ r : ℕ, 0 ≤ C_m r) ∧
      ∀ {ε c R : ℝ}, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
          let N := partCount (ctLv0 c / 4) (nearB c)
          ctLv0 c ≤ nearB c - 1 ∧
          (N : ℝ) ≤ 250 * Real.log (16 / ctLv0 c) + 200 * nearB c + 810 ∧
          (∀ L, ∑ j ∈ Finset.range N, nearOmega ε c R j L =
            ctTaper ε c R L * (1 - sFar c (c * (Real.exp L / π ^ 2))) * nearCut c L) ∧
          (∀ L, ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| ≤ c ^ (-(4 / 3 : ℝ))) ∧
          (∀ j ∈ Finset.range N,
            let Lj := partGrid (ctLv0 c / 4) (j + 1)
            let ℓj := min Lj 1
            let τj := tau0 Lj
            ctLv0 c / 16 < Lj ∧ Lj ≤ nearB c + 4 ∧ 0 < ℓj ∧
            κ_min * c ^ (-(2 / 21 : ℝ)) ≤ ℓj ∧ κ_min * c ^ (-(1 / 21 : ℝ)) ≤ τj ∧
            0 < τj ∧
            (∀ n : ℕ, ContDiff ℝ n (nearWeight ε c R j)) ∧
            (∀ L, 0 ≤ nearWeight ε c R j L ∧ nearWeight ε c R j L ≤ 1) ∧
            (∀ L, L ∉ Icc (Lj - ℓj / 120) (Lj + ℓj / 120) → nearWeight ε c R j L = 0) ∧
            (∀ L, L ≤ ctLv0 c / 3 → nearWeight ε c R j L = 0) ∧
            (∀ L, nearB c + 1 ≤ L → nearWeight ε c R j L = 0) ∧
            (∀ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100),
              0.9 * τj ≤ tau0 L ∧ tau0 L ≤ 1.1 * τj ∧
              L - Lj ≤ (2 / 5 : ℝ) * (hankelEdgeM (3 * τj / 2) - hankelEdgeM τj)) ∧
            (∀ r : ℕ, ∀ L, |iteratedDeriv r (nearWeight ε c R j) L| ≤ C_m r * (c ^ (5 / 6 : ℝ)) ^ r)) := by
  obtain ⟨c₁₀, hc₁₀, htap⟩ := ctTaper_hasDerivAt_and_lip
  obtain ⟨κ₀, hκ₀, cL, hcL1, hLv0⟩ := ctLv0_facts
  obtain ⟨S1, S2, hS1, hS2, hstepD⟩ := exists_smoothStep_deriv_bounds
  obtain ⟨K1, K2, hK1, hK2, hpart⟩ := part_facts
  refine ⟨c₁₀, hc₁₀, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨C₀, C₁, C₂, c_t, hC₀, hC₁, hC₂, hct3, htap_prop⟩ := htap c₁ hc₁ hle
  set a₀ := (6 / 5 : ℝ) * κ₀ with ha₀
  have ha₀_pos : 0 < a₀ := by positivity
  set b₀ := a₀ / 16 with hb₀
  have hb₀_pos : 0 < b₀ := by positivity
  set C_m2 := nearCm2 a₀ C₁ C₂ S1 S2 K1 K2 with hCm2
  have hC_m2_nn : 0 ≤ C_m2 := nearCm2_nonneg ha₀_pos hC₁ hC₂ hS1 hS2 hK1 hK2
  set C_N' := 250 * (max (Real.log (16 / a₀)) 0 + 1) + 200 * (Real.log (π ^ 2) + 4) + 810 with hCN'
  have hCN'_pos : 0 < C_N' := by
    have : 0 < Real.log (π ^ 2) := Real.log_pos (by nlinarith [Real.pi_gt_three])
    positivity
  set M_tot := (1 / 2) * C_N' * C_m2 + 1 with hMtot
  have hMtot_pos : 0 < M_tot := by positivity
  have hev_eps_l : ∀ᶠ c : ℝ in atTop, c ^ (-(5 / 6 : ℝ)) ≤ b₀ / 600 * c ^ (-(2 / 21 : ℝ)) := by
    have ht : Tendsto (fun c : ℝ => c ^ (-(31 / 42 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    filter_upwards [ht.eventually (Iic_mem_nhds (by positivity : 0 < b₀ / 600)),
      eventually_gt_atTop (0 : ℝ)] with c hc_b hc0
    calc c ^ (-(5 / 6 : ℝ)) = c ^ (-(31 / 42 : ℝ)) * c ^ (-(2 / 21 : ℝ)) := by
          rw [← Real.rpow_add hc0]; norm_num
      _ ≤ (b₀ / 600) * c ^ (-(2 / 21 : ℝ)) :=
          mul_le_mul_of_nonneg_right hc_b (Real.rpow_nonneg hc0.le _)
  have hev_err : ∀ᶠ c : ℝ in atTop, M_tot * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ)) ≤ 1 := by
    have hlin : Tendsto (fun c : ℝ => (1 + Real.log c) ^ 4 / c ^ (1 / 7 : ℝ)) atTop (𝓝 0) := by
      have h1 := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 28)
      have h2 : Tendsto (fun c : ℝ => (1 + Real.log c) / c ^ (1 / 28 : ℝ)) atTop (𝓝 0) := by
        have hadd := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 28)).congr'
          (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx; rw [Real.rpow_neg hx.le, ← one_div])).add
          h1.tendsto_div_nhds_zero
        rw [add_zero] at hadd
        refine hadd.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [add_div]
      have hpow : Tendsto (fun c : ℝ => ((1 + Real.log c) / c ^ (1 / 28 : ℝ)) ^ 4) atTop (𝓝 (0 ^ 4)) :=
        h2.pow 4
      rw [zero_pow (by norm_num)] at hpow
      refine hpow.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [div_pow, ← Real.rpow_natCast (x ^ (1 / 28 : ℝ)) 4, ← Real.rpow_mul hx.le,
        show (1 / 28 : ℝ) * ((4 : ℕ) : ℝ) = 1 / 7 by norm_num]
    have hmul : Tendsto (fun c : ℝ => M_tot * ((1 + Real.log c) ^ 4 / c ^ (1 / 7 : ℝ))) atTop (𝓝 (M_tot * 0)) :=
      tendsto_const_nhds.mul hlin
    rw [mul_zero] at hmul
    filter_upwards [hmul.eventually (Iic_mem_nhds one_pos), eventually_gt_atTop (0 : ℝ)] with c hcb hc0
    calc M_tot * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ))
        = M_tot * ((1 + Real.log c) ^ 4 / c ^ (1 / 7 : ℝ)) := by
          rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, mul_div_assoc]
      _ ≤ 1 := hcb
  have hev_a : ∀ᶠ c : ℝ in atTop, a₀ * c ^ (-(2 / 21 : ℝ)) ≤ 1 ∧ b₀ * c ^ (-(2 / 21 : ℝ)) ≤ 1 := by
    have h1 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 21)).const_mul a₀).eventually
      (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))
    have h2 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 21)).const_mul b₀).eventually
      (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))
    exact h1.and h2
  obtain ⟨c_ev, hc_ev⟩ := ((eventually_ge_atTop (max (Real.exp 2) (max c_t cL))).and
    (hev_eps_l.and (hev_err.and hev_a))).exists_forall_of_atTop
  set κ_min := min b₀ (Real.sqrt (4 / 5 * b₀)) with hκmin
  have hκmin_pos : 0 < κ_min := lt_min hb₀_pos (Real.sqrt_pos.2 (by positivity))
  choose C_m_fn hCm_fn hdrv_fn using abs_iteratedDeriv_mollConv_le
  refine ⟨c_ev, κ_min, (le_max_left _ _).trans (hc_ev c_ev le_rfl).1, hκmin_pos, C_m_fn, hCm_fn, ?_⟩
  intro ε c R hε hc hRlo hRhi
  obtain ⟨hcM, hc_eps, hc_err, hc_a, hc_b⟩ := hc_ev c hc
  have hce2 : Real.exp 2 ≤ c := (le_max_left _ _).trans hcM
  have hc_ct : c_t ≤ c := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hcM
  have hc_L : cL ≤ c := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hcM
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]) hce2
  have hc0 : 0 < c := by linarith
  have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce2
  have hlog1 : 1 ≤ 1 + Real.log c := by linarith
  obtain ⟨hL0, hexpL0, _, hLκ⟩ := hLv0 c hc_L
  have hL0_lb : a₀ * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c := by rw [ha₀]; linarith
  have hL0_le1 : ctLv0 c ≤ 1 := by
    have : Real.exp (ctLv0 c) ≤ 1 + 5e-4 := by linarith
    have := Real.add_one_le_exp (ctLv0 c)
    linarith
  have hL04_le1 : ctLv0 c / 4 ≤ 1 := by linarith
  have hB1 : 1 ≤ nearB c := by
    have h1 : 1 ≤ π ^ 2 * Real.log c := by nlinarith only [Real.pi_gt_three, hlog2]
    have := Real.log_nonneg h1
    unfold nearB; linarith
  have hLB : ctLv0 c ≤ nearB c - 1 := by
    have h1 : 1 ≤ π ^ 2 * Real.log c := by nlinarith only [Real.pi_gt_three, hlog2]
    have := Real.log_nonneg h1
    unfold nearB; linarith
  have hc16_pos : 0 < c ^ (-(2 / 21 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hc21_pos : 0 < c ^ (2 / 21 : ℝ) := Real.rpow_pos_of_pos hc0 _
  have hcp_21 : c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 21 : ℝ) = 1 := by
    rw [← Real.rpow_add hc0]; norm_num
  have hc21_ge1 : 1 ≤ c ^ (2 / 21 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hL0_inv : (ctLv0 c)⁻¹ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ hL0]
    calc (1 : ℝ) = c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 21 : ℝ) := hcp_21.symm
      _ = (a₀⁻¹ * a₀) * (c ^ (-(2 / 21 : ℝ)) * c ^ (2 / 21 : ℝ)) := by field_simp
      _ = a₀⁻¹ * c ^ (2 / 21 : ℝ) * (a₀ * c ^ (-(2 / 21 : ℝ))) := by ring
      _ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ) * ctLv0 c := mul_le_mul_of_nonneg_left hL0_lb (by positivity)
  have hb₀_lb : b₀ * c ^ (-(2 / 21 : ℝ)) ≤ min (ctLv0 c / 16) 1 := by
    rw [hb₀]
    exact le_min (by linarith) hc_b
  have heps_pos : 0 < nearEps c := Real.rpow_pos_of_pos hc0 _
  have heps_le : nearEps c ≤ ctLv0 c / 8 := by
    calc nearEps c ≤ b₀ / 600 * c ^ (-(2 / 21 : ℝ)) := hc_eps
      _ ≤ (a₀ / 16) * c ^ (-(2 / 21 : ℝ)) := by
          rw [hb₀]
          exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) (by norm_num)) (Real.rpow_nonneg hc0.le _)
      _ ≤ ctLv0 c / 16 := by linarith only [hL0_lb]
      _ ≤ ctLv0 c / 8 := by linarith only [hL0]
  have heps_le1 : nearEps c ≤ 1 / 2 := by linarith only [heps_le, hL0_le1]
  have hpart_ab := hpart (A := ctLv0 c / 4) (B := nearB c) (by positivity) hL04_le1 hB1
  obtain ⟨hN_le, hpart_sum, hpart_j⟩ := hpart_ab
  have h416 : 4 / (ctLv0 c / 4) = 16 / ctLv0 c := by ring
  rw [h416] at hN_le
  obtain ⟨-, taperGrad, htap_d, htap_bd, _, _, htap_gbd, htap_glip⟩ := htap_prop hε hc_ct hRlo hRhi
  set N := partCount (ctLv0 c / 4) (nearB c)
  have hN_CN' : (N : ℝ) ≤ C_N' * (1 + Real.log c) := by
    have hlog_16 : Real.log (16 / ctLv0 c) ≤ Real.log (16 / a₀) + Real.log c := by
      have h1 : 16 / ctLv0 c ≤ 16 / a₀ * c ^ (2 / 21 : ℝ) := by
        calc 16 / ctLv0 c = 16 * (ctLv0 c)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ 16 * (a₀⁻¹ * c ^ (2 / 21 : ℝ)) := mul_le_mul_of_nonneg_left hL0_inv (by norm_num)
          _ = 16 / a₀ * c ^ (2 / 21 : ℝ) := by ring
      have h2 : c ^ (2 / 21 : ℝ) ≤ c := by
        simpa using Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num : (2 / 21 : ℝ) ≤ 1)
      have h3 : 16 / ctLv0 c ≤ 16 / a₀ * c := h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      calc Real.log (16 / ctLv0 c) ≤ Real.log (16 / a₀ * c) := Real.log_le_log (by positivity) h3
        _ = Real.log (16 / a₀) + Real.log c := Real.log_mul (by positivity) hc0.ne'
    have hB_le : nearB c ≤ (Real.log (π ^ 2) + 4) * (1 + Real.log c) := by
      have hlog_sub : Real.log (Real.log c) ≤ Real.log c := by
        have := Real.log_le_sub_one_of_pos (by linarith only [hlog2] : 0 < Real.log c)
        linarith only [this]
      have hpi2 : 0 ≤ Real.log (π ^ 2) := Real.log_nonneg (by nlinarith only [Real.pi_gt_three])
      unfold nearB
      rw [Real.log_mul (by positivity) (by linarith only [hlog2] : Real.log c ≠ 0)]
      nlinarith only [hlog2, hlog_sub, hpi2]
    have hlog16' : Real.log (16 / ctLv0 c) ≤ (max (Real.log (16 / a₀)) 0 + 1) * (1 + Real.log c) := by
      calc Real.log (16 / ctLv0 c) ≤ Real.log (16 / a₀) + Real.log c := hlog_16
        _ ≤ max (Real.log (16 / a₀)) 0 + Real.log c := by gcongr; exact le_max_left _ _
        _ ≤ (max (Real.log (16 / a₀)) 0 + 1) * (1 + Real.log c) := by
            nlinarith only [le_max_right (Real.log (16 / a₀)) 0, hlog2]
    have h810 : (810 : ℝ) ≤ 810 * (1 + Real.log c) := by nlinarith only [hlog2]
    calc (N : ℝ) ≤ 250 * Real.log (16 / ctLv0 c) + 200 * nearB c + 810 := hN_le
      _ ≤ 250 * ((max (Real.log (16 / a₀)) 0 + 1) * (1 + Real.log c)) +
            200 * ((Real.log (π ^ 2) + 4) * (1 + Real.log c)) + 810 * (1 + Real.log c) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hlog16' (by norm_num))
            (mul_le_mul_of_nonneg_left hB_le (by norm_num))) h810
      _ = C_N' * (1 + Real.log c) := by rw [hCN']; ring
  have hc3 : 3 ≤ c := hct3.trans hc_ct
  refine ⟨hLB, hN_le, fun L => sum_nearOmega_eq hL0 hL04_le1 hB1 L, ?_, ?_⟩
  · -- Summing mollification error `∑ |nearWeight j L - nearOmega j L| ≤ c^{-4/3}`
    have hper : ∀ j ∈ Finset.range N, ∀ L : ℝ,
        |nearWeight ε c R j L - nearOmega ε c R j L| ≤
          (1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2 := by
      intro j hj L
      obtain ⟨hLj_lo, _, hℓ0, hchi_bd, _, hchi_d1, hchi_d2⟩ := hpart_j j hj
      have hℓ_lb : b₀ * c ^ (-(2 / 21 : ℝ)) ≤ min (partGrid (ctLv0 c / 4) (j + 1)) 1 := by
        rw [hb₀]
        have : a₀ / 16 * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c / 16 := by linarith only [hL0_lb]
        exact le_min (by linarith only [this, hLj_lo]) hc_b
      have hℓ_inv : (min (partGrid (ctLv0 c / 4) (j + 1)) 1)⁻¹ ≤ (a₀ / 16)⁻¹ * c ^ (2 / 21 : ℝ) := by
        rw [← hb₀, inv_eq_one_div, div_le_iff₀ hℓ0]
        calc (1 : ℝ) = b₀⁻¹ * c ^ (2 / 21 : ℝ) * (b₀ * c ^ (-(2 / 21 : ℝ))) := by
              rw [mul_mul_mul_comm, inv_mul_cancel₀ hb₀_pos.ne', mul_comm (c ^ (2 / 21 : ℝ)), hcp_21, mul_one]
          _ ≤ b₀⁻¹ * c ^ (2 / 21 : ℝ) * min (partGrid (ctLv0 c / 4) (j + 1)) 1 :=
              mul_le_mul_of_nonneg_left hℓ_lb (by positivity)
      exact near_block_moll_err hc1 hc3 ha₀_pos hL0 hL0_inv hLB heps_le heps_le1 hC₁ hC₂ hS1 hS2 hK1 hK2
        htap_d htap_bd htap_gbd htap_glip (fun hab => hstepD hab) hℓ0 hℓ_inv hchi_bd hchi_d1 hchi_d2 L
    intro L
    have hsum_le : ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L| ≤
        (N : ℝ) * ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) := by
      calc _ ≤ ∑ _j ∈ Finset.range N,
              ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) :=
            Finset.sum_le_sum fun j hj => hper j hj L
        _ = _ := by simp [nsmul_eq_mul]
    have heps_sq : c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2 = c ^ (-(31 / 21 : ℝ)) := by
      unfold nearEps
      rw [← Real.rpow_natCast (c ^ (-(5 / 6 : ℝ))) 2, ← Real.rpow_mul hc0.le, ← Real.rpow_add hc0]
      norm_num
    have hpow_split : c ^ (-(31 / 21 : ℝ)) = c ^ (-(1 / 7 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    calc ∑ j ∈ Finset.range N, |nearWeight ε c R j L - nearOmega ε c R j L|
        ≤ (N : ℝ) * ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) := hsum_le
      _ ≤ (C_N' * (1 + Real.log c)) *
            ((1 / 2) * C_m2 * (1 + Real.log c) ^ 3 * c ^ (4 / 21 : ℝ) * (nearEps c) ^ 2) :=
          mul_le_mul_of_nonneg_right hN_CN' (by positivity)
      _ = ((1 / 2) * C_N' * C_m2) * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ)) * c ^ (-(4 / 3 : ℝ)) := by
            rw [mul_assoc _ (c ^ (4 / 21 : ℝ)), heps_sq, hpow_split]; ring
      _ ≤ (M_tot * (1 + Real.log c) ^ 4 * c ^ (-(1 / 7 : ℝ))) * c ^ (-(4 / 3 : ℝ)) := by
            have hM : (1 / 2) * C_N' * C_m2 ≤ M_tot := by rw [hMtot]; linarith
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hM (by positivity)) (by positivity))
              (by positivity)
      _ ≤ 1 * c ^ (-(4 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hc_err (by positivity)
      _ = c ^ (-(4 / 3 : ℝ)) := one_mul _
  · -- Per-block properties
    intro j hj
    obtain ⟨hLj_lo, hLj_hi, hℓ0, hchi_bd, hchi_supp, _, _⟩ := hpart_j j hj
    set Lj := partGrid (ctLv0 c / 4) (j + 1)
    set ℓj := min Lj 1
    set τj := tau0 Lj
    have hLj_pos : 0 < Lj := by linarith
    have hℓ_lb : b₀ * c ^ (-(2 / 21 : ℝ)) ≤ ℓj := by
      rw [hb₀]
      have : a₀ / 16 * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c / 16 := by linarith
      exact le_min (by linarith only [this, hLj_lo]) hc_b
    have hκ1 : κ_min * c ^ (-(2 / 21 : ℝ)) ≤ ℓj :=
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hc16_pos.le).trans hℓ_lb
    have hτ_pos : 0 < τj := tau0_pos hLj_pos
    have hτ_lb : κ_min * c ^ (-(1 / 21 : ℝ)) ≤ τj := by
      have hsq : (4 / 5 : ℝ) * ℓj ≤ τj ^ 2 := by
        nlinarith only [min_le_left Lj 1, tau0_sq_ge hLj_pos]
      have hpow_sq : (κ_min * c ^ (-(1 / 21 : ℝ))) ^ 2 ≤ (4 / 5 : ℝ) * ℓj := by
        have h1 : κ_min ^ 2 ≤ (4 / 5 : ℝ) * b₀ := by
          have : κ_min ≤ Real.sqrt (4 / 5 * b₀) := min_le_right _ _
          have := pow_le_pow_left₀ hκmin_pos.le this 2
          rwa [Real.sq_sqrt (by positivity)] at this
        have h2 : (c ^ (-(1 / 21 : ℝ))) ^ 2 = c ^ (-(2 / 21 : ℝ)) := by
          rw [← Real.rpow_natCast (c ^ (-(1 / 21 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
        rw [mul_pow, h2]
        calc κ_min ^ 2 * c ^ (-(2 / 21 : ℝ)) ≤ (4 / 5 * b₀) * c ^ (-(2 / 21 : ℝ)) :=
              mul_le_mul_of_nonneg_right h1 hc16_pos.le
          _ = 4 / 5 * (b₀ * c ^ (-(2 / 21 : ℝ))) := by ring
          _ ≤ 4 / 5 * ℓj := by gcongr
      have hsq_le : (κ_min * c ^ (-(1 / 21 : ℝ))) ^ 2 ≤ τj ^ 2 := hpow_sq.trans hsq
      nlinarith only [hsq_le, mul_nonneg hκmin_pos.le (Real.rpow_nonneg hc0.le (-(1 / 21 : ℝ))), hτ_pos]
    have heps_ℓ : nearEps c ≤ ℓj / 600 := by
      calc nearEps c ≤ b₀ / 600 * c ^ (-(2 / 21 : ℝ)) := hc_eps
        _ = (b₀ * c ^ (-(2 / 21 : ℝ))) / 600 := by ring
        _ ≤ ℓj / 600 := by gcongr
    have hom_supp1 : ∀ y, y ∉ Icc (Lj - ℓj / 150) (Lj + ℓj / 150) → nearOmega ε c R j y = 0 := by
      intro y hy; unfold nearOmega; rw [hchi_supp y hy, mul_zero]
    have hom_supp2 : ∀ y, y ∉ Icc (ctLv0 c / 2) (nearB c) → nearOmega ε c R j y = 0 := by
      intro y hy; unfold nearOmega; rw [nearCut_eq_zero_of_not_mem hL0 hy, mul_zero, zero_mul]
    have hcont := nearOmega_continuous hc0 hc1 hL0 (fun x hx => ⟨taperGrad x, htap_d x hx⟩) j
    have hom_bounds : ∀ y, 0 ≤ nearOmega ε c R j y ∧ nearOmega ε c R j y ≤ 1 := fun y => by
      unfold nearOmega
      by_cases hy0 : y ≤ 0
      · rw [nearCut_eq_zero_of_not_mem hL0 (fun h => by linarith [h.1]), mul_zero, zero_mul]
        exact ⟨le_rfl, zero_le_one⟩
      · rw [not_le] at hy0
        have ht := htap_bd y hy0
        have hsf := one_sub_boasSf_bounds hc1 y
        have hcu := nearCut_bounds c y
        have hch := hchi_bd y
        have h12 : ctTaper ε c R y * (1 - sFar c (c * (Real.exp y / π ^ 2))) ≤ 1 :=
          (mul_le_of_le_one_left hsf.1 ht.2).trans hsf.2
        have h123 : ctTaper ε c R y * (1 - sFar c (c * (Real.exp y / π ^ 2))) * nearCut c y ≤ 1 :=
          (mul_le_of_le_one_left hcu.1 h12).trans hcu.2
        exact ⟨mul_nonneg (mul_nonneg (mul_nonneg ht.1 hsf.1) hcu.1) hch.1,
          (mul_le_of_le_one_left hch.1 h123).trans hch.2⟩
    refine ⟨by linarith only [hLj_lo], hLj_hi, hℓ0, hκ1, hτ_lb, hτ_pos, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact (mollConv_iteratedDeriv_eq heps_pos (by linarith only [hL0, hLB] : ctLv0 c / 2 ≤ nearB c) hcont hom_supp2).1 n
    · intro L
      exact mollConv_bounds heps_pos hcont (fun y => (hom_bounds y).1) (fun y => (hom_bounds y).2) L
    · intro L hL
      exact mollConv_eq_zero_of_support heps_pos hom_supp1 fun h => by
        dsimp only [ℓj] at h heps_ℓ hℓ0
        exact hL ⟨by linarith only [h.1, heps_ℓ, hℓ0], by linarith only [h.2, heps_ℓ, hℓ0]⟩
    · intro L hL
      exact mollConv_eq_zero_of_support heps_pos hom_supp2 fun h => by
        linarith only [hL, h.1, heps_le, hL0]
    · intro L hL
      exact mollConv_eq_zero_of_support heps_pos hom_supp2 fun h => by
        linarith only [hL, h.2, heps_le1]
    · intro L hL
      have hL_pos : 0 < L := by
        have : ℓj ≤ Lj := min_le_left _ _
        linarith only [hL.1, hLj_pos, this]
      have hw : |L - Lj| ≤ min Lj 1 / 100 := abs_le.2 ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
      exact tau0_block_window hL_pos hLj_pos hw
    · intro r L
      have heps_inv : (nearEps c)⁻¹ = c ^ (5 / 6 : ℝ) := by
        unfold nearEps; rw [← Real.rpow_neg hc0.le, neg_neg]
      rw [← heps_inv]
      exact hdrv_fn r heps_pos (by linarith only [hL0, hLB] : ctLv0 c / 2 ≤ nearB c) hcont hom_supp2
        (fun y => by rw [abs_of_nonneg (hom_bounds y).1]; exact (hom_bounds y).2) L

end FormalResearch.SignUncertainty

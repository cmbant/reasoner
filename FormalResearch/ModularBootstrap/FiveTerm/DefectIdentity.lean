module

public import FormalResearch.ModularBootstrap.FiveTerm.HalfDiscCauchyIdentity

/-!
# The defect identity at the level of `H` (FIVE-0; `ctu:common-functional` (1))

For `H` in the Cauchy class (`HalfDiscCauchy.CauchyClass`) the two boundary rays used in the defect
identity are the slit `z = i y` and the arc `z = e^{-iψ} = conj (wPt y)`, `y ∈ (0,1)`.  Here:

* membership of both rays in `closure Ω ∖ {i, -i, 1}` and continuity of `y ↦ H(iy)`, `y ↦ H(e^{-iψ})`;
* `‖1 + (iy)²‖ = 1 - y²` and `‖1 + e^{-2iψ}‖ = 2(1-y²)/(1+y²)`;
* the growth bounds `‖H(iy)‖, ‖H(e^{-iψ})‖ ≤ C (1-y)^{-(1-ε)}` on `(0,1)`;
* the defect integrand `(max(|H(iy)|,|B_H|) - Re B_H)/y²` is `O(1)` at `0`, `O((1-y)^{-(1-ε)})` at `1`,
  hence integrable (`defectInt_integrable`);
* `halfDisc_defect_identity`: `∫ (max(|H(iy)|,|B_H|) - 1)/y² = 1 + (π/2) h₁ + ∫ defect`, the identity
  `ctu:common-defect` after conjugation by `G` (`W|F(iy)| = |H(iy)|`, `W|F(iy)+K F| = |B_H|`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- Points of the closed half-disc `‖z‖ ≤ 1`, `0 ≤ Re z` lie in `closure Ω`. -/
lemma mem_closure_halfDisc {z : ℂ} (h1 : ‖z‖ ≤ 1) (h2 : 0 ≤ z.re) : z ∈ closure halfDisc := by
  have hmap : Tendsto (fun δ : ℝ => ((1 - δ : ℝ) : ℂ) * z + (δ / 2 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hc : Continuous fun δ : ℝ => ((1 - δ : ℝ) : ℂ) * z + (δ / 2 : ℝ) := by fun_prop
    have := hc.tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hmap ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with δ hδ
  have h1' : (0 : ℝ) < 1 - δ := by linarith [hδ.2]
  refine ⟨?_, ?_⟩
  · calc ‖((1 - δ : ℝ) : ℂ) * z + ((δ / 2 : ℝ) : ℂ)‖ ≤ ‖((1 - δ : ℝ) : ℂ) * z‖ + ‖((δ / 2 : ℝ) : ℂ)‖ :=
          norm_add_le _ _
      _ = (1 - δ) * ‖z‖ + δ / 2 := by
          rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg h1'.le,
            Real.norm_of_nonneg (by linarith [hδ.1])]
      _ < 1 := by nlinarith only [mul_le_mul_of_nonneg_left h1 h1'.le, hδ.1, hδ.2]
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith only [mul_nonneg h1'.le h2, hδ.1]

lemma I_mul_mem_cont {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Complex.I * (y : ℂ) ∈ closure halfDisc \ {Complex.I, -Complex.I, 1} := by
  refine ⟨mem_closure_halfDisc (by simp [abs_of_pos hy0, hy1.le]) (by simp), ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.im h; simp at this; linarith
  · intro h; have := congrArg Complex.im h; simp at this; linarith
  · intro h; have := congrArg Complex.re h; simp at this

lemma norm_wPt (y : ℝ) : ‖wPt y‖ = 1 := by
  have h := wPt_mul_conj y
  rw [Complex.mul_conj] at h
  have h2 : Complex.normSq (wPt y) = 1 := by exact_mod_cast h
  have : ‖wPt y‖ ^ 2 = 1 := by rw [Complex.sq_norm, h2]
  nlinarith only [this, norm_nonneg (wPt y)]

lemma wbar_mem_cont {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    starRingEnd ℂ (wPt y) ∈ closure halfDisc \ {Complex.I, -Complex.I, 1} := by
  have hre : 0 < (wPt y).re := by
    rw [re_wPt]; apply div_pos <;> nlinarith
  refine ⟨mem_closure_halfDisc (by rw [Complex.norm_conj, norm_wPt]) (by rw [Complex.conj_re]; exact hre.le), ?_⟩
  simp only [mem_insert_iff, mem_singleton_iff, not_or]
  have him : 0 < (wPt y).im := by rw [im_wPt]; apply div_pos <;> nlinarith
  refine ⟨?_, ?_, ?_⟩
  · intro h; have := congrArg Complex.re h; rw [Complex.conj_re] at this; simp at this; linarith
  · intro h; have := congrArg Complex.re h; rw [Complex.conj_re] at this; simp at this; linarith
  · intro h; have := congrArg Complex.im h; rw [Complex.conj_im] at this; simp at this; linarith

lemma continuous_wPt : Continuous wPt := by
  unfold wPt
  have h1 : Continuous fun y : ℝ => (1 - y ^ 2) / (1 + y ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
  have h2 : Continuous fun y : ℝ => 2 * y / (1 + y ^ 2) :=
    Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)
  exact (Complex.continuous_ofReal.comp h1).add ((Complex.continuous_ofReal.comp h2).mul continuous_const)

lemma norm_one_add_sq_slit {y : ℝ} (hy1 : y < 1) (hy : 0 < y) :
    ‖1 + (Complex.I * (y : ℂ)) ^ 2‖ = 1 - y ^ 2 := by
  have : 1 + (Complex.I * (y : ℂ)) ^ 2 = ((1 - y ^ 2 : ℝ) : ℂ) := by
    rw [mul_pow, Complex.I_sq]; push_cast; ring
  rw [this, Complex.norm_real, Real.norm_of_nonneg (by nlinarith)]

lemma norm_one_add_sq_arc {y : ℝ} (hy1 : y < 1) (hy : 0 < y) :
    ‖1 + (starRingEnd ℂ (wPt y)) ^ 2‖ = 2 * ((1 - y ^ 2) / (1 + y ^ 2)) := by
  have hw1 := wPt_mul_conj y
  have : 1 + (starRingEnd ℂ (wPt y)) ^ 2 =
      starRingEnd ℂ (wPt y) * ((2 * ((1 - y ^ 2) / (1 + y ^ 2)) : ℝ) : ℂ) := by
    have hc : wPt y + starRingEnd ℂ (wPt y) = ((2 * ((1 - y ^ 2) / (1 + y ^ 2)) : ℝ) : ℂ) := by
      rw [Complex.add_conj, re_wPt]
    rw [← hc]
    linear_combination (-1 : ℂ) * hw1
  rw [this, norm_mul, Complex.norm_conj, norm_wPt, one_mul, Complex.norm_real,
    Real.norm_of_nonneg (by apply mul_nonneg (by norm_num); apply div_nonneg <;> nlinarith)]

lemma integrableOn_one_sub_rpow {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun y : ℝ => (1 - y) ^ s) (Ioo (0 : ℝ) 1) := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hs).comp_sub_left (1 : ℝ)
  have h2 : IntervalIntegrable (fun y : ℝ => (1 - y) ^ s) volume 0 1 := by
    simpa using h.symm
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)] at h2
  exact h2

section

variable {H : ℂ → ℂ} {h1 : ℝ}

/-- Growth of `H` on the two boundary rays: `‖H‖ ≤ C (1-y)^{-(1-ε)}`. -/
lemma CauchyClass.ray_growth (hH : CauchyClass H h1) :
    ∃ C ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ C ∧ ∀ y ∈ Ioo (0 : ℝ) 1,
      ‖H (Complex.I * (y : ℂ))‖ ≤ C * (1 - y) ^ (-(1 - ε)) ∧
      ‖H (starRingEnd ℂ (wPt y))‖ ≤ C * (1 - y) ^ (-(1 - ε)) := by
  obtain ⟨Cg, ε, hε0, hε1, hgr⟩ := hH.growth
  refine ⟨max Cg 0, ε, hε0, hε1, le_max_right _ _, fun y hy => ?_⟩
  have hy0 := hy.1
  have hy1 := hy.2
  have h1y : 0 < 1 - y := by linarith
  -- generic step
  have step : ∀ (m t : ℝ), 0 < t → 1 - y ≤ t → m * t ^ (1 - ε) ≤ Cg →
      m ≤ max Cg 0 * (1 - y) ^ (-(1 - ε)) := by
    intro m t ht hty hm
    have e1 : m = (m * t ^ (1 - ε)) * t ^ (-(1 - ε)) := by
      rw [mul_assoc, ← Real.rpow_add ht]; simp
    have e2 : t ^ (-(1 - ε)) ≤ (1 - y) ^ (-(1 - ε)) :=
      Real.rpow_le_rpow_of_nonpos h1y hty (by linarith)
    have e3 : 0 ≤ t ^ (-(1 - ε)) := Real.rpow_nonneg ht.le _
    have hm' : m * t ^ (1 - ε) ≤ max Cg 0 := le_trans hm (le_max_left _ _)
    calc m = (m * t ^ (1 - ε)) * t ^ (-(1 - ε)) := e1
      _ ≤ max Cg 0 * t ^ (-(1 - ε)) := mul_le_mul_of_nonneg_right hm' e3
      _ ≤ max Cg 0 * (1 - y) ^ (-(1 - ε)) :=
          mul_le_mul_of_nonneg_left e2 (le_max_right _ _)
  have hz := I_mul_mem_cont hy0 hy1
  have hw := wbar_mem_cont hy0 hy1
  constructor
  · have hm := hgr (Complex.I * (y : ℂ)) hz.1 (fun h => hz.2 (Or.inl h)) (fun h => hz.2 (Or.inr (Or.inl h)))
      (fun h => hz.2 (Or.inr (Or.inr h)))
    rw [norm_one_add_sq_slit hy1 hy0] at hm
    exact step _ _ (by nlinarith) (by nlinarith) hm
  · have hm := hgr (starRingEnd ℂ (wPt y)) hw.1 (fun h => hw.2 (Or.inl h)) (fun h => hw.2 (Or.inr (Or.inl h)))
      (fun h => hw.2 (Or.inr (Or.inr h)))
    rw [norm_one_add_sq_arc hy1 hy0] at hm
    have hpos : 0 < 2 * ((1 - y ^ 2) / (1 + y ^ 2)) := by
      apply mul_pos (by norm_num); apply div_pos <;> nlinarith
    refine step _ _ hpos ?_ hm
    rw [mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith only [mul_pos h1y (by nlinarith only [hy0, hy1] : 0 < 1 + 2 * y - y ^ 2)]

end

/-- The numerator of the defect integrand, `max(|H(iy)|, |B_H(y)|) - Re B_H(y)`. -/
noncomputable def defectNum (H : ℂ → ℂ) (y : ℝ) : ℝ :=
  max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ - (edgeSum H y).re

/-- The defect integrand `(max(|H(iy)|, |B_H|) - Re B_H)/y²`. -/
noncomputable def defectInt (H : ℂ → ℂ) (y : ℝ) : ℝ := defectNum H y / y ^ 2

lemma defectNum_nonneg (H : ℂ → ℂ) (y : ℝ) : 0 ≤ defectNum H y := by
  unfold defectNum
  have h1 : (edgeSum H y).re ≤ ‖edgeSum H y‖ := Complex.re_le_norm _
  have h2 : ‖edgeSum H y‖ ≤ max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ := le_max_right _ _
  linarith

lemma defectInt_nonneg (H : ℂ → ℂ) {y : ℝ} : 0 ≤ defectInt H y := by
  unfold defectInt; exact div_nonneg (defectNum_nonneg H y) (sq_nonneg y)

section

variable {H : ℂ → ℂ} {h1 : ℝ}

lemma rpow_neg_le_two {y ε : ℝ} (hy : y ≤ 1 / 2) (hε1 : ε ≤ 1) (hε0 : 0 < ε) :
    (1 - y) ^ (-(1 - ε)) ≤ 2 := by
  have h12 : (1 : ℝ) / 2 ≤ 1 - y := by linarith
  have e1 : (1 - y) ^ (-(1 - ε)) ≤ ((1 : ℝ) / 2) ^ (-(1 - ε)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) h12 (by linarith)
  have e2 : ((1 : ℝ) / 2) ^ (1 : ℝ) ≤ ((1 : ℝ) / 2) ^ (1 - ε) :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
  rw [Real.rpow_one] at e2
  have e3 : ((1 : ℝ) / 2) ^ (-(1 - ε)) = (((1 : ℝ) / 2) ^ (1 - ε))⁻¹ := Real.rpow_neg (by norm_num) _
  calc (1 - y) ^ (-(1 - ε)) ≤ ((1 : ℝ) / 2) ^ (-(1 - ε)) := e1
    _ = (((1 : ℝ) / 2) ^ (1 - ε))⁻¹ := e3
    _ ≤ ((1 : ℝ) / 2)⁻¹ := inv_anti₀ (by norm_num) e2
    _ = 2 := by norm_num

lemma defectNum_near_zero (hH : CauchyClass H h1) :
    ∃ C y0 : ℝ, 0 < y0 ∧ y0 ≤ 1 / 2 ∧ ∀ y ∈ Ioo (0 : ℝ) y0, defectNum H y ≤ C * y ^ 2 := by
  obtain ⟨C₁, r, hr, hjet⟩ := hH.jet
  obtain ⟨C, ε, hε0, hε1, hC0, hray⟩ := hH.ray_growth
  set C₁' := max C₁ 0 with hC₁'
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  refine ⟨(C₁' + |h1|) ^ 2 + 8 * C,
    min (min (1 / 2) (r / 2)) (1 / (2 * (C₁' + 1))), by positivity, ?_, ?_⟩
  · exact le_trans (min_le_left _ _) (min_le_left _ _)
  intro y hy
  have hy0 := hy.1
  have hyy := hy.2
  have hy12 : y ≤ 1 / 2 := le_trans hyy.le (le_trans (min_le_left _ _) (min_le_left _ _))
  have hyr : y < r := by
    have := lt_of_lt_of_le hyy (le_trans (min_le_left _ _) (min_le_right _ _)); linarith
  have hyC : y < 1 / (2 * (C₁' + 1)) := lt_of_lt_of_le hyy (min_le_right _ _)
  have hy1 : y < 1 := by linarith
  have hC₁y : C₁' * y ^ 2 ≤ 1 / 2 := by
    have h1' : y * (2 * (C₁' + 1)) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hyC
    nlinarith only [h1', hy0, hy12, hC₁'0]
  set Hy := H (Complex.I * (y : ℂ)) with hHy
  have hz := I_mul_mem_cont hy0 hy1
  have hnorm_Iy : ‖Complex.I * (y : ℂ)‖ = y := by simp [abs_of_pos hy0]
  have hu : ‖Hy - 1 - h1 * (Complex.I * (y : ℂ))‖ ≤ C₁' * y ^ 2 := by
    have := hjet (Complex.I * (y : ℂ)) hz.1 (by rw [hnorm_Iy]; exact hyr)
    rw [hnorm_Iy] at this
    exact le_trans this (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg y))
  have hre_u : (Hy - 1 - h1 * (Complex.I * (y : ℂ))).re = Hy.re - 1 := by
    simp [Complex.mul_re]
  have him_u : (Hy - 1 - h1 * (Complex.I * (y : ℂ))).im = Hy.im - h1 * y := by
    simp [Complex.mul_im]
  have ha1 : |Hy.re - 1| ≤ C₁' * y ^ 2 := by
    rw [← hre_u]; exact le_trans (Complex.abs_re_le_norm _) hu
  have hb1 : |Hy.im - h1 * y| ≤ C₁' * y ^ 2 := by
    rw [← him_u]; exact le_trans (Complex.abs_im_le_norm _) hu
  have ha : 1 / 2 ≤ Hy.re := by
    have := (abs_le.mp ha1).1; linarith
  have hb : |Hy.im| ≤ y * (C₁' + |h1|) := by
    have h3 : |Hy.im| ≤ |Hy.im - h1 * y| + |h1 * y| := by
      have := abs_add_le (Hy.im - h1 * y) (h1 * y); simpa using this
    rw [abs_mul, abs_of_pos hy0] at h3
    nlinarith only [h3, hb1, mul_nonneg (mul_nonneg hC₁'0 hy0.le) (sub_nonneg.2 hy1.le)]
  have hb2 : Hy.im ^ 2 ≤ y ^ 2 * (C₁' + |h1|) ^ 2 := by
    have := sq_le_sq' (by linarith [abs_nonneg Hy.im, neg_abs_le Hy.im] : -(y * (C₁' + |h1|)) ≤ Hy.im)
      (le_trans (le_abs_self _) hb)
    nlinarith only [this]
  -- the norm of `Hy`
  have hHnorm : ‖Hy‖ ≤ Hy.re + Hy.im ^ 2 := by
    by_contra hcon
    push Not at hcon
    have hsq : ‖Hy‖ ^ 2 = Hy.re ^ 2 + Hy.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have h5 : 0 ≤ Hy.re + Hy.im ^ 2 := by nlinarith only [ha, sq_nonneg Hy.im]
    nlinarith only [hcon, hsq, ha, h5, sq_nonneg Hy.im, norm_nonneg Hy]
  -- the edge term
  set c' : ℝ := 2 * y ^ 2 / (1 + y ^ 2) with hc'
  have hc'le : c' ≤ 2 * y ^ 2 := by
    rw [hc', div_le_iff₀ (by positivity)]; nlinarith only [sq_nonneg y, mul_nonneg (sq_nonneg y) (sq_nonneg y)]
  have hc'0 : 0 ≤ c' := by positivity
  set E : ℂ := wPt y * (c' : ℂ) * H (starRingEnd ℂ (wPt y)) with hE
  have hBE : edgeSum H y = Hy + E := rfl
  have hEnorm : ‖E‖ ≤ 4 * C * y ^ 2 := by
    obtain ⟨_, hw⟩ := hray y ⟨hy0, hy1⟩
    have h2 := rpow_neg_le_two (y := y) hy12 hε1 hε0
    rw [hE, norm_mul, norm_mul, norm_wPt, one_mul, Complex.norm_real, Real.norm_of_nonneg hc'0]
    calc c' * ‖H (starRingEnd ℂ (wPt y))‖ ≤ (2 * y ^ 2) * (C * 2) := by
          apply mul_le_mul hc'le (le_trans hw (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _) (by positivity)
      _ = 4 * C * y ^ 2 := by ring
  have hBnorm : ‖edgeSum H y‖ ≤ ‖Hy‖ + ‖E‖ := by rw [hBE]; exact norm_add_le _ _
  have hBre : Hy.re - ‖E‖ ≤ (edgeSum H y).re := by
    rw [hBE, Complex.add_re]
    have := Complex.abs_re_le_norm E
    have := neg_abs_le E.re
    linarith
  have hEnn : 0 ≤ ‖E‖ := norm_nonneg _
  have hmax : max ‖Hy‖ ‖edgeSum H y‖ ≤ ‖Hy‖ + ‖E‖ := max_le (by linarith) hBnorm
  unfold defectNum
  rw [← hHy]
  calc max ‖Hy‖ ‖edgeSum H y‖ - (edgeSum H y).re ≤ (‖Hy‖ + ‖E‖) - (Hy.re - ‖E‖) := by linarith
    _ ≤ (Hy.re + Hy.im ^ 2) + ‖E‖ - (Hy.re - ‖E‖) := by linarith
    _ = Hy.im ^ 2 + 2 * ‖E‖ := by ring
    _ ≤ y ^ 2 * (C₁' + |h1|) ^ 2 + 2 * (4 * C * y ^ 2) := by linarith
    _ = ((C₁' + |h1|) ^ 2 + 8 * C) * y ^ 2 := by ring

end

section

variable {H : ℂ → ℂ} {h1 : ℝ}

lemma continuousOn_slit (hH : CauchyClass H h1) :
    ContinuousOn (fun y : ℝ => H (Complex.I * (y : ℂ))) (Ioo (0 : ℝ) 1) := by
  refine hH.cont.comp (by fun_prop : Continuous fun y : ℝ => Complex.I * (y : ℂ)).continuousOn ?_
  intro y hy; exact I_mul_mem_cont hy.1 hy.2

lemma continuousOn_arc (hH : CauchyClass H h1) :
    ContinuousOn (fun y : ℝ => H (starRingEnd ℂ (wPt y))) (Ioo (0 : ℝ) 1) := by
  refine hH.cont.comp (Complex.continuous_conj.comp continuous_wPt).continuousOn ?_
  intro y hy; exact wbar_mem_cont hy.1 hy.2

lemma continuousOn_edgeSum (hH : CauchyClass H h1) :
    ContinuousOn (fun y : ℝ => edgeSum H y) (Ioo (0 : ℝ) 1) := by
  unfold edgeSum
  refine (continuousOn_slit hH).add ?_
  refine ContinuousOn.mul ?_ (continuousOn_arc hH)
  refine (continuous_wPt.continuousOn).mul ?_
  refine (Complex.continuous_ofReal.comp ?_).continuousOn
  exact Continuous.div (by fun_prop) (by fun_prop) (fun y => by positivity)

lemma continuousOn_defectInt (hH : CauchyClass H h1) : ContinuousOn (defectInt H) (Ioo (0 : ℝ) 1) := by
  unfold defectInt defectNum
  refine ContinuousOn.div ?_ (by fun_prop) (fun y hy => pow_ne_zero 2 hy.1.ne')
  refine ContinuousOn.sub ?_ (Complex.continuous_re.comp_continuousOn (continuousOn_edgeSum hH))
  exact (continuousOn_slit hH).norm.sup (continuousOn_edgeSum hH).norm

/-- The defect integrand is integrable on `(0,1)`. -/
theorem defectInt_integrable (hH : CauchyClass H h1) : IntegrableOn (defectInt H) (Ioo (0 : ℝ) 1) := by
  obtain ⟨C₀, y0, hy0, hy012, hnear⟩ := defectNum_near_zero hH
  obtain ⟨C, ε, hε0, hε1, hC0, hray⟩ := hH.ray_growth
  set Cb := max (max C₀ 0) (5 * C / y0 ^ 2) with hCb
  have hCb0 : 0 ≤ Cb := le_trans (le_max_right _ _) (le_max_left _ _)
  have hbd : ∀ y ∈ Ioo (0 : ℝ) 1, ‖defectInt H y‖ ≤ Cb * (1 - y) ^ (-(1 - ε)) := by
    intro y hy
    have hy0' := hy.1
    have hy1 := hy.2
    have hpow1 : 1 ≤ (1 - y) ^ (-(1 - ε)) := by
      have := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 - y by linarith) (show 1 - y ≤ 1 by linarith)
        (show -(1 - ε) ≤ 0 by linarith)
      simpa using this
    have hpow0 : 0 ≤ (1 - y) ^ (-(1 - ε)) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_of_nonneg (defectInt_nonneg H)]
    by_cases hyy : y < y0
    · have h := hnear y ⟨hy0', hyy⟩
      have : defectInt H y ≤ C₀ := by
        unfold defectInt
        rw [div_le_iff₀ (by positivity)]
        linarith
      calc defectInt H y ≤ C₀ := this
        _ ≤ Cb := le_trans (le_max_left _ _) (le_max_left _ _)
        _ = Cb * 1 := (mul_one _).symm
        _ ≤ Cb * (1 - y) ^ (-(1 - ε)) := mul_le_mul_of_nonneg_left hpow1 hCb0
    · push Not at hyy
      obtain ⟨hs, hw⟩ := hray y hy
      have hc'1 : 2 * y ^ 2 / (1 + y ^ 2) ≤ 1 := by
        rw [div_le_iff₀ (by positivity)]; nlinarith only [hy1, hy0']
      have hE : ‖edgeSum H y - H (Complex.I * (y : ℂ))‖ ≤ ‖H (starRingEnd ℂ (wPt y))‖ := by
        have : edgeSum H y - H (Complex.I * (y : ℂ)) =
            wPt y * ((2 * y ^ 2 / (1 + y ^ 2) : ℝ) : ℂ) * H (starRingEnd ℂ (wPt y)) := by
          unfold edgeSum; ring
        rw [this, norm_mul, norm_mul, norm_wPt, one_mul, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        calc 2 * y ^ 2 / (1 + y ^ 2) * ‖H (starRingEnd ℂ (wPt y))‖ ≤ 1 * ‖H (starRingEnd ℂ (wPt y))‖ :=
              mul_le_mul_of_nonneg_right hc'1 (norm_nonneg _)
          _ = _ := one_mul _
      have hBn : ‖edgeSum H y‖ ≤ ‖H (Complex.I * (y : ℂ))‖ + ‖H (starRingEnd ℂ (wPt y))‖ := by
        calc ‖edgeSum H y‖ = ‖H (Complex.I * (y : ℂ)) + (edgeSum H y - H (Complex.I * (y : ℂ)))‖ := by ring_nf
          _ ≤ ‖H (Complex.I * (y : ℂ))‖ + ‖edgeSum H y - H (Complex.I * (y : ℂ))‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have hnum : defectNum H y ≤ 5 * (C * (1 - y) ^ (-(1 - ε))) := by
        unfold defectNum
        have h1' : (edgeSum H y).re ≥ -‖edgeSum H y‖ := by
          have := neg_abs_le (edgeSum H y).re
          have := Complex.abs_re_le_norm (edgeSum H y)
          linarith
        have h2 : max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ ≤
            ‖H (Complex.I * (y : ℂ))‖ + ‖edgeSum H y‖ := max_le (by linarith [norm_nonneg (edgeSum H y)])
          (by linarith [norm_nonneg (H (Complex.I * (y : ℂ)))])
        linarith [norm_nonneg (H (starRingEnd ℂ (wPt y))), norm_nonneg (H (Complex.I * (y : ℂ)))]
      have hy2 : y0 ^ 2 ≤ y ^ 2 := by nlinarith only [hyy, hy0]
      calc defectInt H y = defectNum H y / y ^ 2 := rfl
        _ ≤ 5 * (C * (1 - y) ^ (-(1 - ε))) / y0 ^ 2 := by
            apply div_le_div₀ (by positivity) hnum (by positivity) hy2
        _ = (5 * C / y0 ^ 2) * (1 - y) ^ (-(1 - ε)) := by ring
        _ ≤ Cb * (1 - y) ^ (-(1 - ε)) := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow0
  have hint : IntegrableOn (fun y : ℝ => Cb * (1 - y) ^ (-(1 - ε))) (Ioo (0 : ℝ) 1) :=
    (integrableOn_one_sub_rpow (by linarith)).const_mul Cb
  refine Integrable.mono' hint ?_ ?_
  · exact (continuousOn_defectInt hH).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy using hbd y hy

/-- **Defect identity at the level of `H`** (`ctu:common-defect`, after conjugation by `G`):
`∫_0^1 (max(|H(iy)|, |B_H(y)|) - 1)/y² dy = 1 + (π/2) h₁ + ∫_0^1 (max(|H(iy)|,|B_H|) - Re B_H)/y² dy`,
all integrands integrable on `(0,1)`, and the defect integrand is nonnegative. -/
theorem halfDisc_defect_identity (hH : CauchyClass H h1) :
    IntegrableOn (fun y : ℝ => (max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ - 1) / y ^ 2) (Ioo (0 : ℝ) 1) ∧
    ∫ y in Ioo (0 : ℝ) 1, (max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ - 1) / y ^ 2 =
      1 + π / 2 * h1 + ∫ y in Ioo (0 : ℝ) 1, defectInt H y := by
  obtain ⟨hint, hval⟩ := halfDisc_cauchy_identity hH
  have hd := defectInt_integrable hH
  have hpt : ∀ y ∈ Ioo (0 : ℝ) 1, (max ‖H (Complex.I * (y : ℂ))‖ ‖edgeSum H y‖ - 1) / y ^ 2 =
      defectInt H y + ((edgeSum H y).re - 1) / y ^ 2 := by
    intro y hy
    unfold defectInt defectNum
    have : (y ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 hy.1.ne'
    field_simp
    ring
  refine ⟨(hd.add hint).congr_fun (fun y hy => (hpt y hy).symm) measurableSet_Ioo, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioo (fun y hy => hpt y hy),
    integral_add (f := defectInt H) (g := fun y => ((edgeSum H y).re - 1) / y ^ 2) hd hint, hval]
  ring

end

end FormalResearch.ModularBootstrap.FiveTerm

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.halfDisc_defect_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.halfDisc_defect_identity

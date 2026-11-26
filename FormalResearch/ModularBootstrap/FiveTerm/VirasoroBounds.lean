module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroOuter
public import FormalResearch.ModularBootstrap.FiveTerm.QBounds

/-!
# `G_outer`: two-sided bounds at `z = 1` and `z = ±i` (FIVE-0 slice 4; `OuterDatum.near_one`, `near_I`)

`‖G(z)‖ = exp(Re h̄_a(s(z))) · ‖1-z‖^{1/2} ‖1+z‖^{-2} ‖Q̂(z)‖^{-1/4}`.  Near `z = 1`: `s(z)` stays in a bounded part of
the strip and `Q̂` is continuous and non-zero.  Near `z = ±i`: `‖Q̂‖ ∈ [1/C_q, C_q]` (`QBounds`), the Poisson bounds
`m ≤ Re h̄_a ≤ (5π/8)|Im s| + β'` and `‖1+z²‖ ≤ 4 e^{-π|Im s|/2}` give the `‖1+z²‖^{-5/4}` growth.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real
open FormalResearch.SignUncertainty.CtOuter
open FormalResearch.ModularBootstrap.FiveTerm.StripOuter

namespace FormalResearch.ModularBootstrap.FiveTerm

lemma norm_gout {z : ℂ} (_hz : z ∈ closure halfDisc \ singPts) :
    ‖Gout z‖ = Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) / ‖1 + z‖ ^ 2 *
      ‖qBd z‖ ^ (-(1 / 4) : ℝ) := by
  have h1 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  have h2 : (-(1 / 4 : ℂ)) = ((-(1 / 4) : ℝ) : ℂ) := by push_cast; ring
  unfold Gout
  rw [norm_mul, norm_div, norm_mul, Complex.norm_exp, norm_pow, h1, h2, Complex.norm_cpow_real,
    Complex.norm_cpow_real]

lemma one_le_norm_one_add {z : ℂ} (hz : z ∈ closure halfDisc) : 1 ≤ ‖1 + z‖ := by
  have h := (closure_halfDisc_subset hz).2
  have : (1 + z).re ≤ ‖1 + z‖ := Complex.re_le_norm _
  simp at this; linarith

lemma norm_one_add_le {z : ℂ} (hz : z ∈ closure halfDisc) : ‖1 + z‖ ≤ 2 := by
  have h := (closure_halfDisc_subset hz).1
  calc ‖1 + z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 2 := by simp; linarith

lemma norm_one_sub_le {z : ℂ} (hz : z ∈ closure halfDisc) : ‖1 - z‖ ≤ 2 := by
  have h := (closure_halfDisc_subset hz).1
  calc ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
    _ ≤ 2 := by simp; linarith

lemma rpow_between {a b x : ℝ} (p : ℝ) (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b) :
    min (a ^ p) (b ^ p) ≤ x ^ p ∧ x ^ p ≤ max (a ^ p) (b ^ p) := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  rcases le_total 0 p with hp | hp
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow ha.le hax hp),
      (Real.rpow_le_rpow hx.le hxb hp).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos hx hxb hp),
      (Real.rpow_le_rpow_of_nonpos ha hax hp).trans (le_max_left _ _)⟩

lemma prod_bounds {E Q D e1 e2 q1 q2 d1 d2 : ℝ} (he1 : 0 < e1) (hq1 : 0 < q1) (hd1 : 0 < d1)
    (hE : e1 ≤ E ∧ E ≤ e2) (hQ : q1 ≤ Q ∧ Q ≤ q2) (hD : d1 ≤ D ∧ D ≤ d2) :
    e1 * q1 / d2 ≤ E * Q / D ∧ E * Q / D ≤ e2 * q2 / d1 := by
  have hD0 : 0 < D := lt_of_lt_of_le hd1 hD.1
  have hEQ : 0 ≤ E * Q := by
    have : 0 ≤ E := he1.le.trans hE.1
    have : 0 ≤ Q := hq1.le.trans hQ.1
    positivity
  have he2 : 0 ≤ e2 := he1.le.trans (hE.1.trans hE.2)
  constructor
  · exact div_le_div₀ hEQ (mul_le_mul hE.1 hQ.1 hq1.le (he1.le.trans hE.1)) hD0 hD.2
  · exact div_le_div₀ (mul_nonneg he2 (hq1.le.trans (hQ.1.trans hQ.2)))
      (mul_le_mul hE.2 hQ.2 (hq1.le.trans hQ.1) he2) hd1 hD.1

lemma sInv_one : sInv 1 = 1 := by
  have := sInv_sTan (s := 1) ⟨by simp, by simp⟩
  rwa [sTan_one] at this

lemma one_mem_closure : (1 : ℂ) ∈ closure halfDisc := by
  have := sTan_mem_closure (s := 1) ⟨by simp, by simp⟩
  rwa [sTan_one] at this

lemma gout_near_one : ∃ C c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ 1 → ‖z - 1‖ < r →
    c * ‖z - 1‖ ^ (1 / 2 : ℝ) ≤ ‖Gout z‖ ∧ ‖Gout z‖ ≤ C * ‖z - 1‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨⟨m, hm⟩, ⟨β, hβ⟩⟩ := exists_aAmp_bounds
  have hpi := Real.pi_pos
  obtain ⟨κ, hκ⟩ := re_hbarA_le amp_aAmp (α := 5 * π / 8) (β := β) (by positivity) hβ
  have hI : (Complex.I : ℂ) ≠ 1 := fun h => by have := congrArg Complex.im h; simp at this
  -- continuity of `sInv` and `qBd` at `1`
  have h1c : (1 : ℂ) ∈ closure halfDisc \ {Complex.I, -Complex.I} := by
    refine ⟨one_mem_closure, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨fun h => hI h.symm, fun h => by have := congrArg Complex.im h; simp at this⟩
  obtain ⟨δ1, hδ1, hS⟩ := Metric.continuousWithinAt_iff.mp (continuousOn_sInv 1 h1c) 1 one_pos
  have hq1 : qBd 1 ≠ 0 := Complex.slitPlane_ne_zero (exists_qBd one_mem_closure
    (fun h => hI h.symm) (fun h => by have := congrArg Complex.im h; simp at this)).1
  have hq1n : 0 < ‖qBd 1‖ := norm_pos_iff.mpr hq1
  obtain ⟨δ2, hδ2, hQ⟩ := Metric.continuousWithinAt_iff.mp (continuousOn_qBd 1 h1c) (‖qBd 1‖ / 2) (by positivity)
  set r : ℝ := min (min δ1 δ2) 1 with hr
  have hrpos : 0 < r := lt_min (lt_min hδ1 hδ2) one_pos
  -- constants
  set e1 : ℝ := Real.exp m with he1
  set e2 : ℝ := Real.exp (5 * π / 8 * 1 + β + 5 * π / 8 * κ) with he2
  set a : ℝ := ‖qBd 1‖ / 2 with ha
  set b : ℝ := 3 * ‖qBd 1‖ / 2 with hb
  have ha0 : 0 < a := by positivity
  set q1 : ℝ := min (a ^ (-(1 / 4) : ℝ)) (b ^ (-(1 / 4) : ℝ)) with hq1def
  set q2 : ℝ := max (a ^ (-(1 / 4) : ℝ)) (b ^ (-(1 / 4) : ℝ)) with hq2def
  have hq1pos : 0 < q1 := lt_min (Real.rpow_pos_of_pos ha0 _) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨e2 * q2 / 1, e1 * q1 / 4, r, by positivity, hrpos, fun z hz hz1 hzr => ?_⟩
  have hzr1 : ‖z - 1‖ < 1 := lt_of_lt_of_le hzr (min_le_right _ _)
  have hzI : z ≠ Complex.I ∧ z ≠ -Complex.I := by
    constructor
    · intro h; subst h
      have : ‖(Complex.I : ℂ) - 1‖ = √2 := by
        rw [Complex.norm_def, Complex.normSq_apply]; norm_num
      rw [this] at hzr1
      have : (1 : ℝ) < √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
    · intro h; subst h
      have : ‖-(Complex.I : ℂ) - 1‖ = √2 := by
        rw [Complex.norm_def, Complex.normSq_apply]; norm_num
      rw [this] at hzr1
      have : (1 : ℝ) < √2 := by
        rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      linarith
  have hzD : z ∈ closure halfDisc \ singPts := by
    refine ⟨hz, fun h => ?_⟩
    simp only [singPts, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    tauto
  have hzd : z ∈ closure halfDisc \ {Complex.I, -Complex.I} := sing_subset hzD
  have hdist1 : dist z 1 < δ1 := by
    rw [dist_eq_norm]; exact lt_of_lt_of_le hzr ((min_le_left _ _).trans (min_le_left _ _))
  have hdist2 : dist z 1 < δ2 := by
    rw [dist_eq_norm]; exact lt_of_lt_of_le hzr ((min_le_left _ _).trans (min_le_right _ _))
  have hsz := hS hzd hdist1
  have hqz := hQ hzd hdist2
  rw [sInv_one] at hsz
  rw [dist_eq_norm] at hsz hqz
  have him : |(sInv z).im| ≤ 1 := by
    have : (sInv z).im = (sInv z - 1).im := by simp
    rw [this]; exact (Complex.abs_im_le_norm _).trans hsz.le
  have hstrip := sInv_mem_closedStrip' hzD
  have hE1 : e1 ≤ Real.exp (hbarA aAmp (sInv z)).re := Real.exp_le_exp.mpr (re_hbarA_ge amp_aAmp hm hstrip)
  have hE2 : Real.exp (hbarA aAmp (sInv z)).re ≤ e2 := by
    apply Real.exp_le_exp.mpr
    have := hκ _ hstrip
    have h3 : 5 * π / 8 * |(sInv z).im| ≤ 5 * π / 8 * 1 := mul_le_mul_of_nonneg_left him (by positivity)
    linarith
  have hqn1 : a ≤ ‖qBd z‖ := by
    have := norm_sub_norm_le (qBd 1) (qBd z)
    rw [norm_sub_rev] at this
    linarith
  have hqn2 : ‖qBd z‖ ≤ b := by
    have := norm_sub_norm_le (qBd z) (qBd 1)
    linarith
  have hQb := rpow_between (-(1 / 4) : ℝ) ha0 hqn1 hqn2
  have hD := one_le_norm_one_add hz
  have hD2 := norm_one_add_le hz
  have hDD : (1 : ℝ) ≤ ‖1 + z‖ ^ 2 ∧ ‖1 + z‖ ^ 2 ≤ 4 := by
    constructor
    · nlinarith
    · nlinarith [norm_nonneg (1 + z)]
  have hpb := prod_bounds (E := Real.exp (hbarA aAmp (sInv z)).re)
    (Q := ‖qBd z‖ ^ (-(1 / 4) : ℝ)) (D := ‖1 + z‖ ^ 2) (e1 := e1) (e2 := e2) (q1 := q1) (q2 := q2)
    (d1 := 1) (d2 := 4) (Real.exp_pos _) hq1pos one_pos ⟨hE1, hE2⟩ hQb hDD
  rw [norm_gout hzD, norm_sub_rev z 1]
  have hN : 0 ≤ ‖1 - z‖ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  have hgeq : Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) / ‖1 + z‖ ^ 2 *
      ‖qBd z‖ ^ (-(1 / 4) : ℝ) =
      (Real.exp (hbarA aAmp (sInv z)).re * ‖qBd z‖ ^ (-(1 / 4) : ℝ) / ‖1 + z‖ ^ 2) * ‖1 - z‖ ^ (1 / 2 : ℝ) := by
    ring
  rw [hgeq]
  constructor
  · exact mul_le_mul_of_nonneg_right hpb.1 hN
  · exact mul_le_mul_of_nonneg_right hpb.2 hN

lemma norm_qBd_bounds_near_I {z : ℂ} (hz : z ∈ closure halfDisc) (h1 : z ≠ Complex.I)
    (h2 : z ≠ -Complex.I) (hr : ‖z - Complex.I‖ < 1 / 12 ∨ ‖z + Complex.I‖ < 1 / 12) :
    1 / Cq ≤ ‖qBd z‖ ∧ ‖qBd z‖ ≤ Cq := by
  obtain ⟨_, ht⟩ := exists_qBd hz h1 h2
  have hne : (𝓝[halfDisc] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hz
  have hn : Tendsto (fun w => ‖qHat w‖) (𝓝[halfDisc] z) (𝓝 ‖qBd z‖) := ht.norm
  set U : Set ℂ := {w | ‖w - Complex.I‖ < 1 / 12 ∨ ‖w + Complex.I‖ < 1 / 12} with hU
  have hUo : IsOpen U := by
    have h1 : IsOpen {w : ℂ | ‖w - Complex.I‖ < 1 / 12} :=
      isOpen_lt (f := fun w : ℂ => ‖w - Complex.I‖) (g := fun _ => (1 / 12 : ℝ)) (by fun_prop) continuous_const
    have h2 : IsOpen {w : ℂ | ‖w + Complex.I‖ < 1 / 12} :=
      isOpen_lt (f := fun w : ℂ => ‖w + Complex.I‖) (g := fun _ => (1 / 12 : ℝ)) (by fun_prop) continuous_const
    exact h1.union h2
  have hzU : z ∈ U := hr
  have hev : ∀ᶠ w in 𝓝[halfDisc] z, 1 / Cq ≤ ‖qHat w‖ ∧ ‖qHat w‖ ≤ Cq := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hUo.mem_nhds hzU), self_mem_nhdsWithin] with w hwU hwH
    exact qHat_bounds_near_I hwH hwU
  exact ⟨ge_of_tendsto hn (hev.mono fun w h => h.1), le_of_tendsto hn (hev.mono fun w h => h.2)⟩

lemma exp_mul_le_rpow {t N : ℝ} (hN : 0 < N) (h : N ≤ 4 * Real.exp (-(π * t / 2))) :
    Real.exp (5 * π / 8 * t) ≤ 4 ^ (5 / 4 : ℝ) * N ^ (-(5 / 4) : ℝ) := by
  have hpos : 0 < Real.exp (-(π * t / 2)) := Real.exp_pos _
  have h1 : Real.exp (π * t / 2) ≤ 4 * N⁻¹ := by
    rw [Real.exp_neg] at h
    have : Real.exp (π * t / 2) * N ≤ 4 := by
      have e := Real.exp_pos (π * t / 2)
      calc Real.exp (π * t / 2) * N ≤ Real.exp (π * t / 2) * (4 * (Real.exp (π * t / 2))⁻¹) :=
            mul_le_mul_of_nonneg_left h e.le
        _ = 4 := by field_simp
    rw [le_mul_inv_iff₀ hN] ; exact this
  have h2 : Real.exp (5 * π / 8 * t) = (Real.exp (π * t / 2)) ^ (5 / 4 : ℝ) := by
    rw [← Real.exp_mul]; congr 1; ring
  rw [h2]
  calc (Real.exp (π * t / 2)) ^ (5 / 4 : ℝ) ≤ (4 * N⁻¹) ^ (5 / 4 : ℝ) :=
        Real.rpow_le_rpow (Real.exp_pos _).le h1 (by norm_num)
    _ = 4 ^ (5 / 4 : ℝ) * N ^ (-(5 / 4) : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), Real.inv_rpow hN.le, Real.rpow_neg hN.le]

lemma gout_near_I : ∃ C c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ z ∈ closure halfDisc, z ≠ Complex.I → z ≠ -Complex.I →
    (‖z - Complex.I‖ < r ∨ ‖z + Complex.I‖ < r) →
    c ≤ ‖Gout z‖ ∧ ‖Gout z‖ ≤ C * ‖1 + z ^ 2‖ ^ (-(5 / 4 : ℝ)) := by
  obtain ⟨⟨m, hm⟩, ⟨β, hβ⟩⟩ := exists_aAmp_bounds
  have hpi := Real.pi_pos
  obtain ⟨κ, hκ⟩ := re_hbarA_le amp_aAmp (α := 5 * π / 8) (β := β) (by positivity) hβ
  have hCq := Cq_pos
  have hsq2 : (1 : ℝ) < √2 := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set e1 : ℝ := Real.exp m * (11 / 12) ^ (1 / 2 : ℝ) with he1
  set n2 : ℝ := (2 : ℝ) ^ (1 / 2 : ℝ) with hn2
  set q1 : ℝ := min ((1 / Cq) ^ (-(1 / 4) : ℝ)) (Cq ^ (-(1 / 4) : ℝ)) with hq1
  set q2 : ℝ := max ((1 / Cq) ^ (-(1 / 4) : ℝ)) (Cq ^ (-(1 / 4) : ℝ)) with hq2
  have hq1pos : 0 < q1 :=
    lt_min (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos hCq _)
  have hn1pos : 0 < (11 / 12 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨Real.exp (β + 5 * π / 8 * κ) * 4 ^ (5 / 4 : ℝ) * n2 * q2, e1 * q1 / 4, 1 / 12,
    by positivity, by norm_num, fun z hz hzI hzI' hr => ?_⟩
  have hz1 : z ≠ 1 := by
    intro h; subst h
    have h1 : ‖(1 : ℂ) - Complex.I‖ = √2 := by rw [Complex.norm_def, Complex.normSq_apply]; norm_num
    have h2 : ‖(1 : ℂ) + Complex.I‖ = √2 := by rw [Complex.norm_def, Complex.normSq_apply]; norm_num
    rcases hr with h | h <;> [rw [h1] at h; rw [h2] at h] <;> linarith
  have hzD : z ∈ closure halfDisc \ singPts := by
    refine ⟨hz, fun h => ?_⟩
    simp only [singPts, Set.mem_insert_iff, Set.mem_singleton_iff] at h
    tauto
  have hre : z.re < 1 / 12 := by
    rcases hr with h | h
    · have := Complex.re_le_norm (z - Complex.I); simp at this; linarith
    · have := Complex.re_le_norm (z + Complex.I); simp at this; linarith
  have hstrip := sInv_mem_closedStrip' hzD
  have hN : 0 < ‖1 + z ^ 2‖ := by
    rw [norm_one_add_sq_eq]
    exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzI)) (norm_pos_iff.mpr (fun h => hzI' (eq_neg_of_add_eq_zero_left h)))
  have hsz : sTan (sInv z) = z := sTan_sInv hzI hzI'
  have hE1 : Real.exp m ≤ Real.exp (hbarA aAmp (sInv z)).re :=
    Real.exp_le_exp.mpr (re_hbarA_ge amp_aAmp hm hstrip)
  have hE2 : Real.exp (hbarA aAmp (sInv z)).re ≤
      Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) := by
    have := hκ _ hstrip
    have hb : ‖1 + sTan (sInv z) ^ 2‖ ≤ 4 * Real.exp (-(π * |(sInv z).im| / 2)) :=
      norm_one_add_sTan_sq_le hstrip
    rw [hsz] at hb
    have := exp_mul_le_rpow hN hb
    calc Real.exp (hbarA aAmp (sInv z)).re ≤ Real.exp (5 * π / 8 * |(sInv z).im| + (β + 5 * π / 8 * κ)) :=
          Real.exp_le_exp.mpr (by linarith [hκ _ hstrip])
      _ = Real.exp (5 * π / 8 * |(sInv z).im|) * Real.exp (β + 5 * π / 8 * κ) := Real.exp_add _ _
      _ ≤ (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * Real.exp (β + 5 * π / 8 * κ) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = _ := by ring
  -- the factor ‖1 - z‖^{1/2}
  have hsub1 : 11 / 12 ≤ ‖1 - z‖ := by
    have : (1 - z).re ≤ ‖1 - z‖ := Complex.re_le_norm _
    simp at this; linarith
  have hsub2 := norm_one_sub_le hz
  have hNb := rpow_between (1 / 2 : ℝ) (by norm_num : (0 : ℝ) < 11 / 12) hsub1 hsub2
  have hN1 : (11 / 12 : ℝ) ^ (1 / 2 : ℝ) ≤ ‖1 - z‖ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 11 / 12) hsub1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    exact this
  have hN2 : ‖1 - z‖ ^ (1 / 2 : ℝ) ≤ n2 :=
    Real.rpow_le_rpow (norm_nonneg _) hsub2 (by norm_num)
  have hqb := norm_qBd_bounds_near_I hz hzI hzI' (by
    rcases hr with h | h
    · left; linarith
    · right; linarith)
  have hQb := rpow_between (-(1 / 4) : ℝ) (by positivity : 0 < 1 / Cq) hqb.1 hqb.2
  have hD := one_le_norm_one_add hz
  have hD2 := norm_one_add_le hz
  have hDD : (1 : ℝ) ≤ ‖1 + z‖ ^ 2 ∧ ‖1 + z‖ ^ 2 ≤ 4 := by
    constructor
    · nlinarith
    · nlinarith [norm_nonneg (1 + z)]
  have hEN1 : Real.exp m * (11 / 12) ^ (1 / 2 : ℝ) ≤
      Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) :=
    mul_le_mul hE1 hN1 hn1pos.le (Real.exp_pos _).le
  have hEN2 : Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) ≤
      Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * n2 :=
    mul_le_mul hE2 hN2 (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  have hpb := prod_bounds (E := Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ))
    (Q := ‖qBd z‖ ^ (-(1 / 4) : ℝ)) (D := ‖1 + z‖ ^ 2) (e1 := e1)
    (e2 := Real.exp (β + 5 * π / 8 * κ) * (4 ^ (5 / 4 : ℝ) * ‖1 + z ^ 2‖ ^ (-(5 / 4) : ℝ)) * n2)
    (q1 := q1) (q2 := q2) (d1 := 1) (d2 := 4) (by positivity) hq1pos one_pos ⟨hEN1, hEN2⟩ hQb hDD
  rw [norm_gout hzD]
  have hgeq : Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ) / ‖1 + z‖ ^ 2 *
      ‖qBd z‖ ^ (-(1 / 4) : ℝ) =
      (Real.exp (hbarA aAmp (sInv z)).re * ‖1 - z‖ ^ (1 / 2 : ℝ)) * ‖qBd z‖ ^ (-(1 / 4) : ℝ) /
        ‖1 + z‖ ^ 2 := by ring
  rw [hgeq]
  constructor
  · exact hpb.1
  · refine hpb.2.trans (le_of_eq ?_)
    ring

end FormalResearch.ModularBootstrap.FiveTerm

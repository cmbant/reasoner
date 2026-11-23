/-
Copyright (c) 2026 FormalResearch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FormalResearch
-/
module

public import FormalResearch.ModularBootstrap.Upper.Window.Product
public import FormalResearch.ModularBootstrap.Upper.Comb.ZeroLaw
public import FormalResearch.ModularBootstrap.Upper.Holes.Peano

/-!
# Continuum WKB Potential (`FQ_A`) and Quantile Comparison

This module supplies the continuum potential tools shared by Lemma W (`ut:W`) and
Lemma ID (`ut:ID`) of `upper_transfer.tex`:

* `continuumFQ A σ := -3 * ∫ s in 0..A, s^(1/2) * log |σ - s|` and `continuumAK K := (K + 1/4)^(2/3)`;
* exact closed-form evaluation of `continuumFQ A σ` and `-2 * ∫ a in 1/4..aEnd, log |σ - Φ_a|`
  via the unified antiderivative `continuumAnti σ`;
* Step 1 of Lemma ID (`continuumFQ_sub_lobe_asymptotic`): subtracting the lobe term
  `2π σ_-^{3/2}` leaves `continuumFQ A 0 + 6 √A σ - 3 σ^2 A^(-1/2) + O(A^(-3/2))`;
* Step 3 of Lemma ID (`continuumFQ_AK_add_sum_phiQuantile_bound`, `sum_log_site_shift_neg_bound`):
  comparison between `continuumFQ (continuumAK K) (-a)` and `∑_{k=1}^K 2 log(a + s_k)`
  for large negative window parameter `σ = -a` (`a → +∞`).
-/

namespace FormalResearch.ModularBootstrap.Upper.Window

open Real MeasureTheory Filter Topology intervalIntegral
open FormalResearch.ModularBootstrap.Upper.Comb
open FormalResearch.ModularBootstrap.Upper.Holes

@[expose] public section

/-- Continuum WKB log-potential `FQ_A(σ) = -3 ∫_0^A s^{1/2} log|σ - s| ds`. -/
noncomputable def continuumFQ (A σ : ℝ) : ℝ :=
  -3 * ∫ s in (0 : ℝ)..A, s ^ (1 / 2 : ℝ) * Real.log |σ - s|

/-- Upper integration cutoff `A_K = (K + 1/4)^{2/3} = Φ_{K + 1/2}` matching the midpoint rule. -/
noncomputable def continuumAK (K : ℕ) : ℝ :=
  ((K : ℝ) + 1 / 4) ^ (2 / 3 : ℝ)

lemma continuumAK_nonneg (K : ℕ) : 0 ≤ continuumAK K := by
  unfold continuumAK
  positivity

lemma continuumAK_pos (K : ℕ) : 0 < continuumAK K := by
  unfold continuumAK
  positivity

lemma sqrt_continuumAK (K : ℕ) :
    Real.sqrt (continuumAK K) = ((K : ℝ) + 1 / 4) ^ (1 / 3 : ℝ) := by
  unfold continuumAK
  have hk : (0 : ℝ) ≤ (K : ℝ) + 1 / 4 := by positivity
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hk]
  norm_num

/-- Unified antiderivative of `-6 * t^2 * log |σ - t^2|` on `t ∈ [0, ∞)` normalized by
`continuumAnti σ 0 = 0`. -/
noncomputable def continuumAnti (σ t : ℝ) : ℝ :=
  if σ = 0 then
    -4 * t ^ 3 * Real.log t + (4 / 3 : ℝ) * t ^ 3
  else if σ < 0 then
    -2 * t ^ 3 * Real.log (t ^ 2 - σ) + (4 / 3 : ℝ) * t ^ 3 + 4 * σ * t
      + 4 * (-σ) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-σ))
  else
    -2 * (t ^ 3 - Real.sqrt σ ^ 3) * Real.log |t - Real.sqrt σ|
      - 2 * (t ^ 3 + Real.sqrt σ ^ 3) * Real.log (t + Real.sqrt σ)
      + (4 / 3 : ℝ) * t ^ 3 + 4 * σ * t

lemma continuumAnti_zero_arg (σ : ℝ) : continuumAnti σ 0 = 0 := by
  unfold continuumAnti
  split_ifs with h0 hneg
  · simp
  · simp
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_sub, abs_neg,
      zero_add, mul_zero, add_zero]
    rw [abs_of_nonneg (Real.sqrt_nonneg σ)]
    ring

lemma continuousOn_continuumAnti (σ : ℝ) : ContinuousOn (continuumAnti σ) (Set.Ici 0) := by
  unfold continuumAnti
  split_ifs with h0 hneg
  · have h1 : Continuous fun t : ℝ => (-4 * t ^ 2) * (t * Real.log t) :=
      (by fun_prop : Continuous fun t : ℝ => -4 * t ^ 2).mul Real.continuous_mul_log
    have h2 : Continuous fun t : ℝ => (-4 * t ^ 2) * (t * Real.log t) + (4 / 3 : ℝ) * t ^ 3 :=
      h1.add (by fun_prop)
    exact (h2.congr (fun t => by ring)).continuousOn
  · have hpos : ∀ t : ℝ, t ^ 2 - σ ≠ 0 := fun t => by nlinarith [sq_nonneg t]
    have hc : Continuous fun t : ℝ =>
        -2 * t ^ 3 * Real.log (t ^ 2 - σ) + (4 / 3 : ℝ) * t ^ 3 + 4 * σ * t
          + 4 * (-σ) ^ (3 / 2 : ℝ) * Real.arctan (t / Real.sqrt (-σ)) := by
      refine ((((by fun_prop : Continuous fun t : ℝ => -2 * t ^ 3).mul
        ((by fun_prop : Continuous fun t : ℝ => t ^ 2 - σ).log hpos)).add
        (by fun_prop)).add (by fun_prop)).add ?_
      exact continuous_const.mul (Real.continuous_arctan.comp ((continuous_id).div_const _))
    exact hc.continuousOn
  · have hσ : 0 < σ := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm h0)
    set b := Real.sqrt σ
    have hb : 0 < b := Real.sqrt_pos.mpr hσ
    have hlog1 : Continuous fun t : ℝ => (t ^ 3 - b ^ 3) * Real.log |t - b| := by
      have hp : Continuous fun t : ℝ => t ^ 2 + t * b + b ^ 2 :=
        ((continuous_id.pow 2).add (continuous_id.mul continuous_const)).add continuous_const
      have hsub_c : Continuous fun t : ℝ => t - b := continuous_id.sub continuous_const
      have h1 : Continuous fun t : ℝ => (t ^ 2 + t * b + b ^ 2) * ((t - b) * Real.log (t - b)) :=
        hp.mul (Real.continuous_mul_log.comp hsub_c)
      exact h1.congr (fun t => by rw [Real.log_abs]; ring)
    have hlog2 : ContinuousOn (fun t : ℝ => (t ^ 3 + b ^ 3) * Real.log (t + b)) (Set.Ici 0) := by
      have hp1 : Continuous fun t : ℝ => t ^ 3 + b ^ 3 := (continuous_id.pow 3).add continuous_const
      have hp2 : Continuous fun t : ℝ => t + b := continuous_id.add continuous_const
      refine hp1.continuousOn.mul (ContinuousOn.log hp2.continuousOn fun t ht => ?_)
      have ht0 : 0 ≤ t := Set.mem_Ici.mp ht
      linarith
    have h1 : ContinuousOn (fun t : ℝ => (-2 * (t ^ 3 - b ^ 3)) * Real.log |t - b|) (Set.Ici 0) :=
      hlog1.continuousOn.const_mul (-2 : ℝ) |>.congr (fun t _ => by ring)
    have h2 : ContinuousOn (fun t : ℝ => 2 * (t ^ 3 + b ^ 3) * Real.log (t + b)) (Set.Ici 0) :=
      hlog2.const_mul (2 : ℝ) |>.congr (fun t _ => by ring)
    have hpoly : ContinuousOn (fun t : ℝ => (4 / 3 : ℝ) * t ^ 3) (Set.Ici 0) :=
      (continuous_const.mul (continuous_id.pow 3)).continuousOn
    have hlin : ContinuousOn (fun t : ℝ => 4 * σ * t) (Set.Ici 0) :=
      (continuous_const.mul continuous_id).continuousOn
    exact ((h1.sub h2).add hpoly).add hlin

lemma hasDerivAt_continuumAnti {σ t : ℝ} (ht_pos : 0 < t) (ht_ne : t ^ 2 ≠ σ) :
    HasDerivAt (continuumAnti σ) (-6 * t ^ 2 * Real.log |σ - t ^ 2|) t := by
  unfold continuumAnti
  split_ifs with h0 hneg
  · subst h0
    have ht0 : t ≠ 0 := ht_pos.ne'
    have hlog : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log ht0
    have hpow3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
      simpa using (hasDerivAt_pow 3 t)
    have h1 := (hpow3.const_mul (-4 : ℝ)).mul hlog
    have h2 := hpow3.const_mul (4 / 3 : ℝ)
    have hsum := h1.add h2
    convert hsum using 1
    rw [zero_sub, abs_neg, abs_of_pos (sq_pos_of_pos ht_pos), Real.log_pow]
    push_cast
    field_simp [ht0]
    ring
  · have hpos : 0 < t ^ 2 - σ := by nlinarith [sq_nonneg t]
    have hpow3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
      simpa using (hasDerivAt_pow 3 t)
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2 - σ) (2 * t) t := by
      simpa using ((hasDerivAt_pow 2 t).sub_const σ)
    have hlog : HasDerivAt (fun x : ℝ => Real.log (x ^ 2 - σ)) ((t ^ 2 - σ)⁻¹ * (2 * t)) t := by
      simpa [Function.comp_def] using (Real.hasDerivAt_log hpos.ne').comp t hsq
    have harctan : HasDerivAt (fun x : ℝ => Real.arctan (x / Real.sqrt (-σ)))
        ((1 + (t / Real.sqrt (-σ)) ^ 2)⁻¹ * (1 / Real.sqrt (-σ))) t := by
      have hdiv : HasDerivAt (fun x : ℝ => x / Real.sqrt (-σ)) (1 / Real.sqrt (-σ)) t := by
        simpa using (hasDerivAt_id t).div_const (Real.sqrt (-σ))
      simpa [Function.comp_def] using (Real.hasDerivAt_arctan (t / Real.sqrt (-σ))).comp t hdiv
    have hcomb := (((((hpow3.const_mul (-2 : ℝ)).mul hlog).add
      (hpow3.const_mul (4 / 3 : ℝ))).add
      ((hasDerivAt_id t).const_mul (4 * σ))).add
      (harctan.const_mul (4 * (-σ) ^ (3 / 2 : ℝ))))
    refine hcomb.congr_deriv ?_
    have hσ_pos : 0 < -σ := neg_pos.mpr hneg
    have hsq_sqrt : Real.sqrt (-σ) ^ 2 = -σ := Real.sq_sqrt hσ_pos.le
    have hpow32 : (-σ) ^ (3 / 2 : ℝ) = (-σ) * Real.sqrt (-σ) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hσ_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
    rw [abs_of_neg (by linarith : σ - t ^ 2 < 0), neg_sub, hpow32]
    have hsqrt_ne : Real.sqrt (-σ) ≠ 0 := (Real.sqrt_pos.mpr hσ_pos).ne'
    have hden1 : 1 + (t / Real.sqrt (-σ)) ^ 2 = (t ^ 2 - σ) / (-σ) := by
      field_simp [hsqrt_ne]
      rw [hsq_sqrt]
      ring
    rw [hden1]
    field_simp [hpos.ne', hsqrt_ne]
    ring
  · have hσ : 0 < σ := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm h0)
    set b := Real.sqrt σ
    have hb : 0 < b := Real.sqrt_pos.mpr hσ
    have hb2 : b ^ 2 = σ := Real.sq_sqrt hσ.le
    have htb_ne : t - b ≠ 0 := by
      intro h
      apply ht_ne
      have : t = b := sub_eq_zero.mp h
      rw [this, hb2]
    have htb_pos : 0 < t + b := by linarith
    have hpow3 : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
      simpa using (hasDerivAt_pow 3 t)
    have hlog1 : HasDerivAt (fun x : ℝ => Real.log |x - b|) (t - b)⁻¹ t := by
      have hderiv : HasDerivAt (fun x : ℝ => Real.log (x - b)) (t - b)⁻¹ t := by
        simpa [Function.comp_def] using
          (Real.hasDerivAt_log htb_ne).comp t ((hasDerivAt_id t).sub_const b)
      refine hderiv.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)
      exact Real.log_abs _
    have hlog2 : HasDerivAt (fun x : ℝ => Real.log (x + b)) (t + b)⁻¹ t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log htb_pos.ne').comp t ((hasDerivAt_id t).add_const b)
    have h1 := ((hpow3.sub_const (b ^ 3)).const_mul (-2 : ℝ)).mul hlog1
    have h2 := ((hpow3.add_const (b ^ 3)).const_mul (2 : ℝ)).mul hlog2
    have hcomb := ((h1.sub h2).add (hpow3.const_mul (4 / 3 : ℝ))).add
      ((hasDerivAt_id t).const_mul (4 * σ))
    refine hcomb.congr_deriv ?_
    have habs : |σ - t ^ 2| = |t - b| * (t + b) := by
      rw [abs_sub_comm, show t ^ 2 - σ = (t - b) * (t + b) by rw [← hb2]; ring,
        abs_mul, abs_of_pos htb_pos]
    rw [habs, Real.log_mul (abs_ne_zero.mpr htb_ne) htb_pos.ne']
    field_simp [htb_ne, htb_pos.ne']
    rw [← hb2]
    ring

lemma intervalIntegrable_log_abs_sub (σ a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.log |σ - s|) volume a b := by
  have heq : (fun s : ℝ => Real.log |σ - s|) = fun s : ℝ => Real.log (s - σ) := by
    ext s; rw [abs_sub_comm, Real.log_abs]
  rw [heq]
  simpa using (intervalIntegral.intervalIntegrable_log' (a := a - σ) (b := b - σ)).comp_sub_right σ

lemma intervalIntegrable_rpow_half_mul_log_abs (σ a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => s ^ (1 / 2 : ℝ) * Real.log |σ - s|) volume a b := by
  have hc : Continuous fun s : ℝ => s ^ (1 / 2 : ℝ) :=
    continuous_id.rpow_const (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have aux : ∀ u v : ℝ, u ≤ v →
      IntervalIntegrable (fun s : ℝ => s ^ (1 / 2 : ℝ) * Real.log |σ - s|) volume u v := by
    intro u v huv
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le huv]
    have hlog := (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mp
      (intervalIntegrable_log_abs_sub σ u v)
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := fun s : ℝ => s ^ (1 / 2 : ℝ)) hc.continuousOn (s := Set.Icc u v)
    refine MeasureTheory.Integrable.bdd_mul (c := M) hlog hc.aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hM s ⟨hs.1.le, hs.2⟩
  rcases le_total a b with hab | hba
  · exact aux a b hab
  · exact (aux b a hba).symm

lemma continuumFQ_eq_continuumAnti {A σ : ℝ} (hA : 0 ≤ A) :
    continuumFQ A σ = continuumAnti σ (Real.sqrt A) := by
  have hcomp_cont : ContinuousOn (fun s : ℝ => continuumAnti σ (Real.sqrt s)) (Set.Icc 0 A) :=
    (continuousOn_continuumAnti σ).comp Real.continuous_sqrt.continuousOn
      (fun s _ => Real.sqrt_nonneg s)
  have hint : IntervalIntegrable (fun s : ℝ => -3 * (s ^ (1 / 2 : ℝ) * Real.log |σ - s|))
      volume 0 A :=
    (intervalIntegrable_rpow_half_mul_log_abs σ 0 A).const_mul (-3)
  have hderiv_off : ∀ s ∈ Set.Ioo (0 : ℝ) A, s ≠ σ →
      HasDerivAt (fun x : ℝ => continuumAnti σ (Real.sqrt x))
        (-3 * (s ^ (1 / 2 : ℝ) * Real.log |σ - s|)) s := by
    intro s hs hsne
    have hs_pos : 0 < s := hs.1
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt s)) s := Real.hasDerivAt_sqrt hs_pos.ne'
    have hanti := hasDerivAt_continuumAnti (σ := σ) (Real.sqrt_pos.mpr hs_pos) (by
      rw [Real.sq_sqrt hs_pos.le]; exact hsne)
    have hcomp := hanti.comp s hsqrt
    refine hcomp.congr_deriv ?_
    have hsr : s ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hs_pos _).ne'
    have hsq : (s ^ (1 / 2 : ℝ)) ^ 2 = s := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs_pos.le]; norm_num
    rw [Real.sq_sqrt hs_pos.le, Real.sqrt_eq_rpow]
    field_simp [hsr]
    rw [hsq]
    ring
  have hftc_interval : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ A → (∀ s ∈ Set.Ioo u v, s ≠ σ) →
      ∫ s in u..v, (-3 * (s ^ (1 / 2 : ℝ) * Real.log |σ - s|)) =
        continuumAnti σ (Real.sqrt v) - continuumAnti σ (Real.sqrt u) := by
    intro u v hu huv hv hno
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
      (hcomp_cont.mono (Set.Icc_subset_Icc hu hv))
      (fun s hs => hderiv_off s ⟨lt_of_le_of_lt hu hs.1, lt_of_lt_of_le hs.2 hv⟩ (hno s hs))
      (hint.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hu, by linarith⟩))
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hv⟩))))
  unfold continuumFQ
  rw [← intervalIntegral.integral_const_mul]
  by_cases hσ_mem : σ ∈ Set.Ioo (0 : ℝ) A
  · have h1 := hftc_interval 0 σ le_rfl hσ_mem.1.le hσ_mem.2.le (fun _ hs => hs.2.ne)
    have h2 := hftc_interval σ A hσ_mem.1.le hσ_mem.2.le le_rfl (fun _ hs => hs.1.ne')
    have hint1 : IntervalIntegrable (fun s : ℝ => -3 * (s ^ (1 / 2 : ℝ) * Real.log |σ - s|))
        volume 0 σ :=
      (intervalIntegrable_rpow_half_mul_log_abs σ 0 σ).const_mul (-3)
    have hint2 : IntervalIntegrable (fun s : ℝ => -3 * (s ^ (1 / 2 : ℝ) * Real.log |σ - s|))
        volume σ A :=
      (intervalIntegrable_rpow_half_mul_log_abs σ σ A).const_mul (-3)
    have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    rw [← hadd, h1, h2, Real.sqrt_zero, continuumAnti_zero_arg]
    ring
  · have hno : ∀ s ∈ Set.Ioo (0 : ℝ) A, s ≠ σ := fun s hs h => hσ_mem (h ▸ hs)
    rw [hftc_interval 0 A le_rfl hA le_rfl hno, Real.sqrt_zero, continuumAnti_zero_arg, sub_zero]

lemma continuumFQ_zero {A : ℝ} (hA : 0 ≤ A) :
    continuumFQ A 0 = -2 * A ^ (3 / 2 : ℝ) * Real.log A + (4 / 3 : ℝ) * A ^ (3 / 2 : ℝ) := by
  rw [continuumFQ_eq_continuumAnti hA]
  unfold continuumAnti
  simp only [↓reduceIte]
  rcases eq_or_lt_of_le hA with rfl | hA_pos
  · simp
  · have hsqrt3 : Real.sqrt A ^ 3 = A ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA]
      norm_num
    have hlog_sqrt : Real.log (Real.sqrt A) = (1 / 2 : ℝ) * Real.log A := by
      rw [Real.sqrt_eq_rpow, Real.log_rpow hA_pos]
    rw [hsqrt3, hlog_sqrt]
    ring

lemma continuumFQ_neg {A σ : ℝ} (hA : 0 ≤ A) (hσ : σ < 0) :
    continuumFQ A σ = -2 * A ^ (3 / 2 : ℝ) * Real.log (A - σ) + (4 / 3 : ℝ) * A ^ (3 / 2 : ℝ)
      + 4 * σ * Real.sqrt A + 4 * (-σ) ^ (3 / 2 : ℝ) * Real.arctan (Real.sqrt A / Real.sqrt (-σ)) := by
  rw [continuumFQ_eq_continuumAnti hA]
  unfold continuumAnti
  simp only [hσ.ne, ↓reduceIte, hσ, Real.sq_sqrt hA]
  have hsqrt3 : Real.sqrt A ^ 3 = A ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  rw [hsqrt3]

lemma continuumFQ_pos {A σ : ℝ} (hA : 0 ≤ A) (hσ : 0 < σ) :
    continuumFQ A σ =
      -2 * (A ^ (3 / 2 : ℝ) - σ ^ (3 / 2 : ℝ)) * Real.log |Real.sqrt A - Real.sqrt σ|
        - 2 * (A ^ (3 / 2 : ℝ) + σ ^ (3 / 2 : ℝ)) * Real.log (Real.sqrt A + Real.sqrt σ)
        + (4 / 3 : ℝ) * A ^ (3 / 2 : ℝ) + 4 * σ * Real.sqrt A := by
  rw [continuumFQ_eq_continuumAnti hA]
  unfold continuumAnti
  simp only [hσ.ne', ↓reduceIte, not_lt_of_gt hσ]
  have hsqrtA : Real.sqrt A ^ 3 = A ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA]
    norm_num
  have hsqrtS : Real.sqrt σ ^ 3 = σ ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hσ.le]
    norm_num
  rw [hsqrtA, hsqrtS]

lemma intervalIntegrable_log_abs_phiQuantile (σ aEnd : ℝ) (ha : (1 / 4 : ℝ) ≤ aEnd) :
    IntervalIntegrable (fun a : ℝ => Real.log |σ - phiQuantile a|) volume (1 / 4) aEnd := by
  rcases lt_trichotomy σ 0 with hσ_neg | rfl | hσ_pos
  · refine ContinuousOn.intervalIntegrable_of_Icc ha ?_
    refine ContinuousOn.log ?_ ?_
    · exact (Continuous.continuousOn (continuous_abs.comp (continuous_const.sub
        ((continuous_id.sub continuous_const).rpow_const
          (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))))))
    · intro a ha_mem
      have hphi : 0 ≤ phiQuantile a := by
        unfold phiQuantile; exact Real.rpow_nonneg (sub_nonneg.mpr ha_mem.1) _
      exact ne_of_gt (abs_pos.mpr (by linarith))
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    have hlog : IntegrableOn (fun a : ℝ => (2 / 3 : ℝ) * Real.log (a - 1 / 4))
        (Set.Ioc (1 / 4) aEnd) volume := by
      have hi := (intervalIntegral.intervalIntegrable_log'
        (a := (0 : ℝ)) (b := aEnd - 1 / 4)).comp_sub_right (1 / 4 : ℝ)
      have hi' : IntervalIntegrable (fun x : ℝ => (2 / 3 : ℝ) * Real.log (x - 1 / 4))
          volume (1 / 4) aEnd := by
        simpa [zero_add, sub_add_cancel] using hi.const_mul (2 / 3 : ℝ)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hi'
    refine hlog.congr_fun (fun a ha_mem => ?_) measurableSet_Ioc
    have ha_pos : 0 < a - 1 / 4 := sub_pos.mpr ha_mem.1
    have hphi : 0 < phiQuantile a := by unfold phiQuantile; exact Real.rpow_pos_of_pos ha_pos _
    rw [zero_sub, abs_neg, abs_of_pos hphi]
    unfold phiQuantile
    rw [Real.log_rpow ha_pos]
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha]
    set b := Real.sqrt σ
    have hb : 0 < b := Real.sqrt_pos.mpr hσ_pos
    have hb2 : b ^ 2 = σ := Real.sq_sqrt hσ_pos.le
    set aStar : ℝ := 1 / 4 + b ^ 3
    let q : ℝ → ℝ := fun a =>
      let t := (a - 1 / 4) ^ (1 / 3 : ℝ)
      Real.log ((t + b) / (t ^ 2 + t * b + b ^ 2))
    have hq_cont : ContinuousOn q (Set.Icc (1 / 4) aEnd) := by
      have ht_cont : Continuous fun a : ℝ => (a - 1 / 4) ^ (1 / 3 : ℝ) :=
        (continuous_id.sub continuous_const).rpow_const
          (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))
      refine ContinuousOn.log ?_ ?_
      · refine ContinuousOn.div (ht_cont.continuousOn.add continuousOn_const) ?_ ?_
        · exact ((ht_cont.continuousOn.pow 2).add
            (ht_cont.continuousOn.mul continuousOn_const)).add continuousOn_const
        · intro a ha_mem
          have ht_nn : 0 ≤ (a - 1 / 4) ^ (1 / 3 : ℝ) :=
            Real.rpow_nonneg (sub_nonneg.mpr ha_mem.1) _
          nlinarith [sq_pos_of_pos hb]
      · intro a ha_mem
        have ht_nn : 0 ≤ (a - 1 / 4) ^ (1 / 3 : ℝ) :=
          Real.rpow_nonneg (sub_nonneg.mpr ha_mem.1) _
        have hden : 0 < ((a - 1 / 4) ^ (1 / 3 : ℝ)) ^ 2 + (a - 1 / 4) ^ (1 / 3 : ℝ) * b + b ^ 2 := by
          nlinarith [sq_pos_of_pos hb]
        exact (div_pos (by linarith) hden).ne'
    have hint_log : IntegrableOn (fun a : ℝ => Real.log |a - aStar|)
        (Set.Ioc (1 / 4) aEnd) volume := by
      have hi : IntervalIntegrable (fun a : ℝ => Real.log |a - aStar|) volume (1 / 4) aEnd := by
        simpa only [abs_sub_comm] using intervalIntegrable_log_abs_sub aStar (1 / 4) aEnd
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp hi
    have hint_q : IntegrableOn q (Set.Ioc (1 / 4) aEnd) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ha).mp (hq_cont.intervalIntegrable_of_Icc ha)
    refine (hint_log.add hint_q).congr_fun_ae ?_
    have hae_ne : ∀ᵐ a ∂(volume.restrict (Set.Ioc (1 / 4) aEnd)), a ≠ aStar :=
      ae_restrict_of_ae (compl_mem_ae_iff.mpr volume_singleton)
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hae_ne] with a ha_mem ha_ne
    have ha_gt : 0 < a - 1 / 4 := sub_pos.mpr ha_mem.1
    set t := (a - 1 / 4) ^ (1 / 3 : ℝ)
    have ht_pos : 0 < t := Real.rpow_pos_of_pos ha_gt _
    have ht3 : t ^ 3 = a - 1 / 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha_gt.le]
      norm_num
    have ht2 : t ^ 2 = phiQuantile a := by
      unfold phiQuantile
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha_gt.le]
      norm_num
    have hden_pos : 0 < t ^ 2 + t * b + b ^ 2 := by nlinarith
    have hnum_pos : 0 < t + b := by linarith
    have hid : |σ - phiQuantile a| = |a - aStar| * ((t + b) / (t ^ 2 + t * b + b ^ 2)) := by
      rw [abs_sub_comm, ← ht2, ← hb2, show t ^ 2 - b ^ 2 = (t - b) * (t + b) by ring,
        abs_mul, abs_of_pos hnum_pos]
      have haid : a - aStar = (t - b) * (t ^ 2 + t * b + b ^ 2) := by
        dsimp [aStar]; linarith [ht3]
      rw [haid, abs_mul, abs_of_pos hden_pos]
      field_simp [hden_pos.ne']
    dsimp [q]
    rw [hid, Real.log_mul (abs_ne_zero.mpr (sub_ne_zero.mpr ha_ne)) (div_pos hnum_pos hden_pos).ne']

/-- Quantile form of `continuumFQ`: `-2 ∫_{1/4}^{aEnd} log|σ - Φ_a| da = continuumAnti σ ((aEnd - 1/4)^(1/3))`. -/
lemma integral_log_abs_phiQuantile_eq {σ aEnd : ℝ} (ha : (1 / 4 : ℝ) ≤ aEnd) :
    -2 * ∫ a in (1 / 4 : ℝ)..aEnd, Real.log |σ - phiQuantile a| =
      continuumAnti σ ((aEnd - 1 / 4) ^ (1 / 3 : ℝ)) := by
  let g : ℝ → ℝ := fun a => (a - 1 / 4) ^ (1 / 3 : ℝ)
  have hg_cont : ContinuousOn g (Set.Icc (1 / 4) aEnd) :=
    ((continuous_id.sub continuous_const).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 1 / 3))).continuousOn
  have hcomp_cont : ContinuousOn (fun a => continuumAnti σ (g a)) (Set.Icc (1 / 4) aEnd) :=
    (continuousOn_continuumAnti σ).comp hg_cont
      (fun a ha_mem => Real.rpow_nonneg (sub_nonneg.mpr ha_mem.1) _)
  have hint : IntervalIntegrable (fun a => -2 * Real.log |σ - phiQuantile a|) volume (1 / 4) aEnd :=
    (intervalIntegrable_log_abs_phiQuantile σ aEnd ha).const_mul (-2)
  have hderiv_off : ∀ a ∈ Set.Ioo (1 / 4 : ℝ) aEnd, phiQuantile a ≠ σ →
      HasDerivAt (fun x => continuumAnti σ (g x)) (-2 * Real.log |σ - phiQuantile a|) a := by
    intro a ha_mem hne
    have ha_gt : 0 < a - 1 / 4 := sub_pos.mpr ha_mem.1
    have hg_pos : 0 < g a := Real.rpow_pos_of_pos ha_gt _
    have hg2 : g a ^ 2 = phiQuantile a := by
      dsimp [g]; unfold phiQuantile
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha_gt.le]
      norm_num
    have hg_deriv : HasDerivAt g (1 * (1 / 3 : ℝ) * (a - 1 / 4) ^ ((1 / 3 : ℝ) - 1)) a :=
      ((hasDerivAt_id a).sub_const (1 / 4 : ℝ)).rpow_const (Or.inl ha_gt.ne')
    have hanti := hasDerivAt_continuumAnti (σ := σ) hg_pos (by rw [hg2]; exact hne)
    have hcomp := hanti.comp a hg_deriv
    refine hcomp.congr_deriv ?_
    rw [hg2]
    have hmul : (a - 1 / 4) ^ (2 / 3 : ℝ) * (a - 1 / 4) ^ ((1 / 3 : ℝ) - 1) = 1 := by
      rw [← Real.rpow_add ha_gt]
      norm_num
    calc -6 * phiQuantile a * Real.log |σ - phiQuantile a| *
          (1 * (1 / 3 : ℝ) * (a - 1 / 4) ^ ((1 / 3 : ℝ) - 1))
        = -2 * Real.log |σ - phiQuantile a| *
            ((a - 1 / 4) ^ (2 / 3 : ℝ) * (a - 1 / 4) ^ ((1 / 3 : ℝ) - 1)) := by
          unfold phiQuantile; ring
      _ = -2 * Real.log |σ - phiQuantile a| := by rw [hmul, mul_one]
  have hftc_sub : ∀ u v : ℝ, 1 / 4 ≤ u → u ≤ v → v ≤ aEnd →
      (∀ a ∈ Set.Ioo u v, phiQuantile a ≠ σ) →
      ∫ a in u..v, (-2 * Real.log |σ - phiQuantile a|) =
        continuumAnti σ (g v) - continuumAnti σ (g u) := by
    intro u v hu huv hv hno
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
      (hcomp_cont.mono (Set.Icc_subset_Icc hu hv))
      (fun a ha_i => hderiv_off a ⟨lt_of_le_of_lt hu ha_i.1, lt_of_lt_of_le ha_i.2 hv⟩ (hno a ha_i))
      (hint.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hu, by linarith⟩))
        (Set.mem_uIcc.mpr (Or.inl ⟨by linarith, hv⟩))))
  rw [← intervalIntegral.integral_const_mul]
  have hg_start : g (1 / 4) = 0 := by dsimp [g]; norm_num
  by_cases hσ_pos : 0 < σ
  · set aStar : ℝ := 1 / 4 + σ ^ (3 / 2 : ℝ)
    have hStar_gt : 1 / 4 < aStar := by
      dsimp [aStar]; linarith [Real.rpow_pos_of_pos hσ_pos (3 / 2 : ℝ)]
    have phi_eq_iff : ∀ a ≥ 1 / 4, phiQuantile a = σ ↔ a = aStar := by
      intro a ha_ge
      constructor
      · intro h
        have h1 : ((a - 1 / 4) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) = σ ^ (3 / 2 : ℝ) := by
          unfold phiQuantile at h; rw [h]
        rw [← Real.rpow_mul (sub_nonneg.mpr ha_ge)] at h1
        norm_num at h1
        dsimp [aStar]; linarith
      · intro h; subst h; unfold phiQuantile; dsimp [aStar]
        rw [add_sub_cancel_left, ← Real.rpow_mul hσ_pos.le]
        norm_num
    by_cases hmem : aStar ∈ Set.Ioo (1 / 4 : ℝ) aEnd
    · have h1 := hftc_sub (1 / 4) aStar le_rfl hmem.1.le hmem.2.le
        (fun a ha_i h => (phi_eq_iff a ha_i.1.le).mp h |> fun heq => ha_i.2.ne heq)
      have h2 := hftc_sub aStar aEnd hmem.1.le hmem.2.le le_rfl
        (fun a ha_i h => (phi_eq_iff a (by linarith [hmem.1, ha_i.1])).mp h |> fun heq => ha_i.1.ne' heq)
      have hint1 : IntervalIntegrable (fun a => -2 * Real.log |σ - phiQuantile a|)
          volume (1 / 4) aStar :=
        (intervalIntegrable_log_abs_phiQuantile σ aStar hmem.1.le).const_mul (-2)
      have hint2 : IntervalIntegrable (fun a => -2 * Real.log |σ - phiQuantile a|)
          volume aStar aEnd :=
        hint.mono_set (Set.uIcc_subset_uIcc (Set.mem_uIcc.mpr (Or.inl ⟨hmem.1.le, hmem.2.le⟩))
          Set.right_mem_uIcc)
      have hadd := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
      rw [← hadd, h1, h2, hg_start, continuumAnti_zero_arg]
      ring
    · have hno : ∀ a ∈ Set.Ioo (1 / 4 : ℝ) aEnd, phiQuantile a ≠ σ := by
        intro a ha_i h
        exact hmem ((phi_eq_iff a ha_i.1.le).mp h ▸ ha_i)
      rw [hftc_sub (1 / 4) aEnd le_rfl ha le_rfl hno, hg_start, continuumAnti_zero_arg, sub_zero]
  · have hno : ∀ a ∈ Set.Ioo (1 / 4 : ℝ) aEnd, phiQuantile a ≠ σ := by
      intro a ha_i h
      have hphi_pos : 0 < phiQuantile a := by
        unfold phiQuantile
        exact Real.rpow_pos_of_pos (sub_pos.mpr ha_i.1) _
      linarith [not_lt.mp hσ_pos]
    rw [hftc_sub (1 / 4) aEnd le_rfl ha le_rfl hno, hg_start, continuumAnti_zero_arg, sub_zero]

lemma continuumFQ_AK_eq (K : ℕ) (σ : ℝ) :
    continuumFQ (continuumAK K) σ =
      -2 * ∫ a in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), Real.log |σ - phiQuantile a| := by
  have hk : (1 / 4 : ℝ) ≤ (K : ℝ) + 1 / 2 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  rw [continuumFQ_eq_continuumAnti (continuumAK_nonneg K),
    integral_log_abs_phiQuantile_eq hk, sqrt_continuumAK]
  ring_nf

/-! ### Elementary Taylor inequalities and Step 1 (`continuumFQ_sub_lobe_asymptotic`) -/

lemma abs_log_one_add_le_two_mul {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |Real.log (1 + t)| ≤ 2 * |t| := by
  have hlt := abs_le.mp ht
  have hpos : 0 < 1 + t := by linarith
  rcases le_total 0 t with ht_nn | ht_np
  · rw [abs_of_nonneg (Real.log_nonneg (by linarith)), abs_of_nonneg ht_nn]
    linarith [Real.log_le_sub_one_of_pos hpos]
  · rw [abs_of_nonpos (Real.log_nonpos hpos.le (by linarith)), abs_of_nonpos ht_np]
    have hinv : -Real.log (1 + t) = Real.log (1 + (-t) / (1 + t)) := by
      rw [← Real.log_inv]
      congr 1
      field_simp [hpos.ne']
      ring
    rw [hinv]
    have h1 : 0 < 1 + (-t) / (1 + t) := by
      have : 0 ≤ (-t) / (1 + t) := div_nonneg (by linarith) hpos.le
      linarith
    have hsub := Real.log_le_sub_one_of_pos h1
    have hdiv : (-t) / (1 + t) ≤ 2 * (-t) := by
      rw [div_le_iff₀ hpos]
      nlinarith
    linarith

private lemma abs_log_one_add_sub_le {x : ℝ} (hx0 : 0 ≤ x) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ x ^ 3 / 3 := by
  let F : ℝ → ℝ := fun t => Real.log (1 + t) - (t - t ^ 2 / 2)
  have hcont : ContinuousOn F (Set.Icc 0 x) := by
    refine ContinuousOn.sub ?_ (Continuous.continuousOn (by fun_prop))
    exact ContinuousOn.log (Continuous.continuousOn (by fun_prop)) (fun t ht => by linarith [ht.1])
  have hderiv : ∀ t ∈ Set.Ioo 0 x, HasDerivAt F (t ^ 2 / (1 + t)) t := by
    intro t ht
    have ht1 : 1 + t ≠ 0 := by linarith [ht.1]
    have hd1 : HasDerivAt (fun y => Real.log (1 + y)) ((1 + t)⁻¹ * 1) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log ht1).comp t ((hasDerivAt_id t).const_add 1)
    have hd2 : HasDerivAt (fun y : ℝ => y - y ^ 2 / 2) (1 - t) t := by
      have hsub := (hasDerivAt_id t).sub ((hasDerivAt_pow 2 t).div_const 2)
      refine hsub.congr_deriv ?_
      ring
    refine (hd1.sub hd2).congr_deriv ?_
    field_simp [ht1]; ring
  have hint : IntervalIntegrable (fun t => t ^ 2 / (1 + t)) volume 0 x := by
    refine ContinuousOn.intervalIntegrable_of_Icc hx0 ?_
    exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) (fun t ht => by linarith [ht.1])
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hcont hderiv hint
  have hF0 : F 0 = 0 := by simp [F]
  rw [hF0, sub_zero] at hftc
  have hnonneg : 0 ≤ F x := by
    rw [← hftc]
    exact intervalIntegral.integral_nonneg hx0 (fun t ht => div_nonneg (sq_nonneg t) (by linarith [ht.1]))
  have hupper : F x ≤ x ^ 3 / 3 := by
    rw [← hftc]
    have hle : ∫ t in (0 : ℝ)..x, t ^ 2 / (1 + t) ≤ ∫ t in (0 : ℝ)..x, t ^ 2 := by
      refine intervalIntegral.integral_mono_on hx0 hint
        ((by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 x) ?_
      intro t ht
      exact div_le_self (sq_nonneg t) (by linarith [ht.1])
    have hint_sq : ∫ t in (0 : ℝ)..x, t ^ 2 = x ^ 3 / 3 := by
      rw [integral_pow]; norm_num
    linarith [hle, hint_sq]
  rw [abs_of_nonneg hnonneg]
  exact hupper

private lemma abs_neg_log_one_sub_sub_le {y : ℝ} (hy0 : 0 ≤ y) (hy_half : y ≤ 1 / 2) :
    |-Real.log (1 - y) - (y + y ^ 2 / 2)| ≤ 2 * y ^ 3 / 3 := by
  let G : ℝ → ℝ := fun t => -Real.log (1 - t) - (t + t ^ 2 / 2)
  have hcont : ContinuousOn G (Set.Icc 0 y) := by
    refine ContinuousOn.sub ?_ (Continuous.continuousOn (by fun_prop))
    refine ContinuousOn.neg (ContinuousOn.log (Continuous.continuousOn (by fun_prop)) ?_)
    intro t ht; linarith [ht.2, hy_half]
  have hderiv : ∀ t ∈ Set.Ioo 0 y, HasDerivAt G (t ^ 2 / (1 - t)) t := by
    intro t ht
    have ht1 : 1 - t ≠ 0 := by linarith [ht.2, hy_half]
    have hd1 : HasDerivAt (fun z => Real.log (1 - z)) ((1 - t)⁻¹ * (-1)) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log ht1).comp t ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
    have hd2 : HasDerivAt (fun z : ℝ => z + z ^ 2 / 2) (1 + t) t := by
      have hadd := (hasDerivAt_id t).add ((hasDerivAt_pow 2 t).div_const 2)
      refine hadd.congr_deriv ?_
      ring
    refine (hd1.neg.sub hd2).congr_deriv ?_
    field_simp [ht1]; ring
  have hint : IntervalIntegrable (fun t => t ^ 2 / (1 - t)) volume 0 y := by
    refine ContinuousOn.intervalIntegrable_of_Icc hy0 ?_
    exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) (fun t ht => by linarith [ht.2, hy_half])
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hy0 hcont hderiv hint
  have hG0 : G 0 = 0 := by simp [G]
  rw [hG0, sub_zero] at hftc
  have hnonneg : 0 ≤ G y := by
    rw [← hftc]
    exact intervalIntegral.integral_nonneg hy0 (fun t ht =>
      div_nonneg (sq_nonneg t) (by linarith [ht.2, hy_half]))
  have hupper : G y ≤ 2 * y ^ 3 / 3 := by
    rw [← hftc]
    have hle : ∫ t in (0 : ℝ)..y, t ^ 2 / (1 - t) ≤ ∫ t in (0 : ℝ)..y, 2 * t ^ 2 := by
      refine intervalIntegral.integral_mono_on hy0 hint
        ((by fun_prop : Continuous fun t : ℝ => 2 * t ^ 2).intervalIntegrable 0 y) ?_
      intro t ht
      have hden : (1 / 2 : ℝ) ≤ 1 - t := by linarith [ht.2, hy_half]
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg t]
    have hint_sq : ∫ t in (0 : ℝ)..y, 2 * t ^ 2 = 2 * y ^ 3 / 3 := by
      rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring
    linarith [hle, hint_sq]
  rw [abs_of_nonneg hnonneg]
  exact hupper

private lemma abs_log_one_sub_div_one_add_add_le {u : ℝ} (hu0 : 0 ≤ u) (hu_half : u ≤ 1 / 2) :
    |Real.log ((1 - u) / (1 + u)) + 2 * u| ≤ 8 / 9 * u ^ 3 := by
  let H : ℝ → ℝ := fun t => Real.log (1 - t) - Real.log (1 + t) + 2 * t
  have hcont : ContinuousOn H (Set.Icc 0 u) := by
    refine ((ContinuousOn.log (Continuous.continuousOn (by fun_prop))
      (fun t ht => by linarith [ht.2, hu_half])).sub
      (ContinuousOn.log (Continuous.continuousOn (by fun_prop))
      (fun t ht => by linarith [ht.1]))).add (Continuous.continuousOn (by fun_prop))
  have hderiv : ∀ t ∈ Set.Ioo 0 u, HasDerivAt H (-2 * t ^ 2 / (1 - t ^ 2)) t := by
    intro t ht
    have hm : 1 - t ≠ 0 := by linarith [ht.2, hu_half]
    have hp : 1 + t ≠ 0 := by linarith [ht.1]
    have hsq : 1 - t ^ 2 ≠ 0 := by nlinarith [ht.1, ht.2, hu_half]
    have hd1 : HasDerivAt (fun z => Real.log (1 - z)) ((1 - t)⁻¹ * (-1)) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log hm).comp t ((hasDerivAt_const t 1).sub (hasDerivAt_id t))
    have hd2 : HasDerivAt (fun z => Real.log (1 + z)) ((1 + t)⁻¹ * 1) t := by
      simpa [Function.comp_def] using
        (Real.hasDerivAt_log hp).comp t ((hasDerivAt_id t).const_add 1)
    have hd3 : HasDerivAt (fun z : ℝ => 2 * z) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
    refine ((hd1.sub hd2).add hd3).congr_deriv ?_
    field_simp [hm, hp, hsq]; ring
  have hint : IntervalIntegrable (fun t => -2 * t ^ 2 / (1 - t ^ 2)) volume 0 u := by
    refine ContinuousOn.intervalIntegrable_of_Icc hu0 ?_
    exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (by fun_prop)) (fun t ht => by nlinarith [ht.1, ht.2, hu_half])
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0 hcont hderiv hint
  have hH0 : H 0 = 0 := by simp [H]
  rw [hH0, sub_zero] at hftc
  have hdiv_eq : H u = Real.log ((1 - u) / (1 + u)) + 2 * u := by
    dsimp [H]
    rw [Real.log_div (by linarith) (by linarith)]
  rw [← hdiv_eq, ← hftc]
  have hnorm : ‖∫ t in (0 : ℝ)..u, -2 * t ^ 2 / (1 - t ^ 2)‖ ≤ ∫ t in (0 : ℝ)..u, 8 / 3 * t ^ 2 := by
    refine intervalIntegral.norm_integral_le_of_norm_le hu0
      (Eventually.of_forall fun t ht => ?_)
      ((by fun_prop : Continuous fun t : ℝ => 8 / 3 * t ^ 2).intervalIntegrable 0 u)
    have ht1 : 0 ≤ t := ht.1.le
    have ht2 : t ≤ 1 / 2 := ht.2.trans hu_half
    have hden : (3 / 4 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < 1 - t ^ 2),
      abs_mul, abs_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0), neg_neg, abs_of_nonneg (sq_nonneg t)]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg t]
  have hint_sq : ∫ t in (0 : ℝ)..u, 8 / 3 * t ^ 2 = 8 / 9 * u ^ 3 := by
    rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring
  rw [Real.norm_eq_abs] at hnorm
  linarith [hnorm, hint_sq]

private lemma abs_arctan_sub_self_le {u : ℝ} (hu0 : 0 ≤ u) :
    |Real.arctan u - u| ≤ u ^ 3 / 3 := by
  let K : ℝ → ℝ := fun t => t - Real.arctan t
  have hderiv : ∀ t : ℝ, HasDerivAt K (t ^ 2 / (1 + t ^ 2)) t := by
    intro t
    have hd := (hasDerivAt_id t).sub (Real.hasDerivAt_arctan t)
    refine hd.congr_deriv ?_
    have h1 : 1 + t ^ 2 ≠ 0 := by positivity
    field_simp [h1]; ring
  have hint : IntervalIntegrable (fun t => t ^ 2 / (1 + t ^ 2)) volume 0 u :=
    (Continuous.div (by fun_prop) (by fun_prop) (fun t => by positivity)).intervalIntegrable 0 u
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  have hK0 : K 0 = 0 := by simp [K]
  rw [hK0, sub_zero] at hftc
  have hnn : 0 ≤ K u := by
    rw [← hftc]
    exact intervalIntegral.integral_nonneg hu0 (fun t _ => div_nonneg (sq_nonneg t) (by positivity))
  have hup : K u ≤ u ^ 3 / 3 := by
    rw [← hftc]
    have hle : ∫ t in (0 : ℝ)..u, t ^ 2 / (1 + t ^ 2) ≤ ∫ t in (0 : ℝ)..u, t ^ 2 := by
      refine intervalIntegral.integral_mono_on hu0 hint
        ((by fun_prop : Continuous fun t : ℝ => t ^ 2).intervalIntegrable 0 u) ?_
      intro t _
      exact div_le_self (sq_nonneg t) (by linarith [sq_nonneg t])
    have hs : ∫ t in (0 : ℝ)..u, t ^ 2 = u ^ 3 / 3 := by
      rw [integral_pow]; norm_num
    linarith [hle, hs]
  rw [abs_sub_comm, abs_of_nonneg hnn]
  exact hup

private lemma arctan_add_arctan_inv_eq {y : ℝ} (hy : 0 < y) :
    Real.arctan y + Real.arctan y⁻¹ = π / 2 := by
  let L : ℝ → ℝ := fun t => Real.arctan t + Real.arctan t⁻¹
  have hderiv : ∀ t ∈ Set.uIcc 1 y, HasDerivAt L 0 t := by
    intro t ht
    have ht_pos : 0 < t := by
      rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hinv : HasDerivAt (fun z : ℝ => z⁻¹) (-(t ^ 2)⁻¹) t := hasDerivAt_inv ht_pos.ne'
    have hd2 : HasDerivAt (fun z : ℝ => Real.arctan z⁻¹) ((1 + (t⁻¹) ^ 2)⁻¹ * (-(t ^ 2)⁻¹)) t := by
      simpa [Function.comp_def] using (Real.hasDerivAt_arctan t⁻¹).comp t hinv
    refine ((Real.hasDerivAt_arctan t).add hd2).congr_deriv ?_
    have h1 : 1 + t ^ 2 ≠ 0 := by positivity
    have h2 : 1 + (t⁻¹) ^ 2 ≠ 0 := by positivity
    field_simp [ht_pos.ne', h1, h2]
    ring
  have hconst := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hconst
  have h1 : L 1 = π / 2 := by
    dsimp [L]; rw [inv_one, Real.arctan_one]; ring
  linarith [hconst, h1]

/-- **Lemma ID, Step 1** (`ut:ID`): after subtracting the lobe term `2π σ_-^{3/2}`,
`continuumFQ A σ` has the uniform large-`A` expansion
`continuumFQ A 0 + 6 √A σ - 3 σ^2 A^{-1/2} + O(|σ|^3 A^{-3/2})`. -/
theorem continuumFQ_sub_lobe_asymptotic (σ A : ℝ) (hA : max (4 * |σ|) 1 ≤ A) :
    |continuumFQ A σ - 2 * π * (max (-σ) 0) ^ (3 / 2 : ℝ) -
      (continuumFQ A 0 + 6 * Real.sqrt A * σ - 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ)))|
      ≤ 4 * |σ| ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
  have hA_pos : 0 < A := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) hA)
  have hA_4σ : 4 * |σ| ≤ A := le_trans (le_max_left _ _) hA
  have hA_half : A ^ (-(1 / 2 : ℝ)) = (Real.sqrt A)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hA_pos.le]
  have hA_32 : A ^ (-(3 / 2 : ℝ)) = (A ^ (3 / 2 : ℝ))⁻¹ := by
    rw [Real.rpow_neg hA_pos.le]
  rcases lt_trichotomy σ 0 with hσ_neg | rfl | hσ_pos
  · set a : ℝ := -σ
    have ha_pos : 0 < a := neg_pos.mpr hσ_neg
    have hmax : max (-σ) 0 = a := max_eq_left ha_pos.le
    have habs : |σ| = a := abs_of_neg hσ_neg
    rw [hmax, habs]
    have hlog_eq : Real.log (A - σ) = Real.log A + Real.log (1 + a / A) := by
      have hid : A - σ = A * (1 + a / A) := by
        dsimp [a]; field_simp [hA_pos.ne']; ring
      rw [hid, Real.log_mul hA_pos.ne' (by positivity)]
    have hy : 0 < Real.sqrt A / Real.sqrt a :=
      div_pos (Real.sqrt_pos.mpr hA_pos) (Real.sqrt_pos.mpr ha_pos)
    have harc_id : Real.arctan (Real.sqrt A / Real.sqrt (-σ)) =
        π / 2 - Real.arctan (Real.sqrt (a / A)) := by
      have hinv : (Real.sqrt A / Real.sqrt a)⁻¹ = Real.sqrt (a / A) := by
        rw [inv_div, Real.sqrt_div ha_pos.le]
      have harc := arctan_add_arctan_inv_eq hy
      rw [hinv] at harc
      change Real.arctan (Real.sqrt A / Real.sqrt a) = π / 2 - Real.arctan (Real.sqrt (a / A))
      linarith
    have hu_nn : 0 ≤ Real.sqrt (a / A) := Real.sqrt_nonneg _
    have hx_nn : 0 ≤ a / A := div_nonneg ha_pos.le hA_pos.le
    have h1 := abs_log_one_add_sub_le hx_nn
    have h2 := abs_arctan_sub_self_le hu_nn
    set E1 := Real.log (1 + a / A) - (a / A - (a / A) ^ 2 / 2)
    set E2 := Real.arctan (Real.sqrt (a / A)) - Real.sqrt (a / A)
    have hpow_A : A ^ (3 / 2 : ℝ) * (a / A) = a * Real.sqrt A := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hA_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      field_simp [hA_pos.ne']
    have hpow_A2 : A ^ (3 / 2 : ℝ) * ((a / A) ^ 2 / 2) = a ^ 2 / 2 * A ^ (-(1 / 2 : ℝ)) := by
      rw [hA_half, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hA_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      field_simp [hA_pos.ne', (Real.sqrt_pos.mpr hA_pos).ne']
      rw [Real.sq_sqrt hA_pos.le]
    have ha32_mul : a ^ (3 / 2 : ℝ) * Real.sqrt (a / A) = a ^ 2 * A ^ (-(1 / 2 : ℝ)) := by
      rw [hA_half, Real.sqrt_div ha_pos.le,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ha_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      have hsq : Real.sqrt a * Real.sqrt a = a := Real.mul_self_sqrt ha_pos.le
      field_simp [(Real.sqrt_pos.mpr hA_pos).ne']
      nlinarith [hsq]
    have hmain : continuumFQ A σ - 2 * π * a ^ (3 / 2 : ℝ) -
        (continuumFQ A 0 + 6 * Real.sqrt A * σ - 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ))) =
        -2 * A ^ (3 / 2 : ℝ) * E1 - 4 * a ^ (3 / 2 : ℝ) * E2 := by
      rw [continuumFQ_neg hA_pos.le hσ_neg, continuumFQ_zero hA_pos.le, hlog_eq, harc_id]
      have hE1 : Real.log (1 + a / A) = (a / A - (a / A) ^ 2 / 2) + E1 := by dsimp [E1]; ring
      have hE2 : Real.arctan (Real.sqrt (a / A)) = Real.sqrt (a / A) + E2 := by dsimp [E2]; ring
      rw [hE1, hE2]
      have hσ_eq : σ = -a := by dsimp [a]; ring
      rw [hσ_eq]
      calc (-2 * A ^ (3 / 2 : ℝ) * (Real.log A + (a / A - (a / A) ^ 2 / 2 + E1))
            + 4 / 3 * A ^ (3 / 2 : ℝ) + 4 * (-a) * Real.sqrt A
            + 4 * (- -a) ^ (3 / 2 : ℝ) * (π / 2 - (Real.sqrt (a / A) + E2)))
            - 2 * π * a ^ (3 / 2 : ℝ)
            - (-2 * A ^ (3 / 2 : ℝ) * Real.log A + 4 / 3 * A ^ (3 / 2 : ℝ)
              + 6 * Real.sqrt A * (-a) - 3 * (-a) ^ 2 * A ^ (-(1 / 2 : ℝ)))
          = -2 * (A ^ (3 / 2 : ℝ) * (a / A)) + 2 * (A ^ (3 / 2 : ℝ) * ((a / A) ^ 2 / 2))
            + 2 * a * Real.sqrt A - 4 * (a ^ (3 / 2 : ℝ) * Real.sqrt (a / A))
            + 3 * a ^ 2 * A ^ (-(1 / 2 : ℝ))
            - 2 * A ^ (3 / 2 : ℝ) * E1 - 4 * a ^ (3 / 2 : ℝ) * E2 := by
              rw [neg_neg]; ring
        _ = -2 * A ^ (3 / 2 : ℝ) * E1 - 4 * a ^ (3 / 2 : ℝ) * E2 := by
              rw [hpow_A, hpow_A2, ha32_mul]; ring
    rw [hmain]
    have hA_cube : A ^ (3 / 2 : ℝ) * (a / A) ^ 3 = a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
      rw [hA_32]
      have hA3 : A ^ (3 / 2 : ℝ) * A ^ (3 / 2 : ℝ) = A ^ 3 := by
        rw [← Real.rpow_add hA_pos]; norm_num
      field_simp [hA_pos.ne', (Real.rpow_pos_of_pos hA_pos _).ne']
      nlinarith [hA3]
    have hbd1 : |2 * A ^ (3 / 2 : ℝ) * E1| ≤ 2 / 3 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.rpow_pos_of_pos hA_pos _)]
      calc 2 * A ^ (3 / 2 : ℝ) * |E1|
          ≤ 2 * A ^ (3 / 2 : ℝ) * ((a / A) ^ 3 / 3) := by gcongr
        _ = 2 / 3 * (A ^ (3 / 2 : ℝ) * (a / A) ^ 3) := by ring
        _ = 2 / 3 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by rw [hA_cube]; ring
    have hbd2 : |4 * a ^ (3 / 2 : ℝ) * E2| ≤ 4 / 3 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (Real.rpow_pos_of_pos ha_pos _)]
      have hu3 : Real.sqrt (a / A) ^ 3 = a ^ (3 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg ha_pos.le hA_pos.le),
          Real.div_rpow ha_pos.le hA_pos.le, div_eq_mul_inv, hA_32]
        norm_num
      have ha3 : a ^ (3 / 2 : ℝ) * a ^ (3 / 2 : ℝ) = a ^ 3 := by
        rw [← Real.rpow_add ha_pos]; norm_num
      calc 4 * a ^ (3 / 2 : ℝ) * |E2|
          ≤ 4 * a ^ (3 / 2 : ℝ) * (Real.sqrt (a / A) ^ 3 / 3) := by gcongr
        _ = 4 / 3 * (a ^ (3 / 2 : ℝ) * a ^ (3 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) := by rw [hu3]; ring
        _ = 4 / 3 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by rw [ha3]
    calc |-2 * A ^ (3 / 2 : ℝ) * E1 - 4 * a ^ (3 / 2 : ℝ) * E2|
        ≤ |2 * A ^ (3 / 2 : ℝ) * E1| + |4 * a ^ (3 / 2 : ℝ) * E2| := by
          simpa [neg_mul] using abs_sub (- (2 * A ^ (3 / 2 : ℝ) * E1)) (4 * a ^ (3 / 2 : ℝ) * E2)
      _ ≤ 2 / 3 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) + 4 / 3 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) := add_le_add hbd1 hbd2
      _ ≤ 4 * a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
          have : 0 ≤ a ^ 3 * A ^ (-(3 / 2 : ℝ)) := by positivity
          linarith
  · rw [continuumFQ_zero hA_pos.le]
    norm_num
  · have hmax : max (-σ) 0 = 0 := max_eq_right (by linarith)
    have habs : |σ| = σ := abs_of_pos hσ_pos
    rw [hmax, habs, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0), mul_zero, sub_zero]
    set u : ℝ := Real.sqrt (σ / A)
    have hu_pos : 0 < u := Real.sqrt_pos.mpr (div_pos hσ_pos hA_pos)
    have hu_half : u ≤ 1 / 2 := by
      dsimp [u]
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      rw [div_le_iff₀ hA_pos]
      linarith
    have hu2 : u ^ 2 = σ / A := Real.sq_sqrt (div_nonneg hσ_pos.le hA_pos.le)
    have hσA_half : σ / A ≤ 1 / 2 := by
      rw [div_le_iff₀ hA_pos]; linarith
    have hsqrt_σ : Real.sqrt σ = u * Real.sqrt A := by
      dsimp [u]; rw [Real.sqrt_div hσ_pos.le, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hA_pos).ne']
    have hsub_pos : 0 < Real.sqrt A - Real.sqrt σ := by
      rw [hsqrt_σ]; nlinarith [Real.sqrt_pos.mpr hA_pos]
    have hlog_sub : Real.log |Real.sqrt A - Real.sqrt σ| =
        (1 / 2 : ℝ) * Real.log A + Real.log (1 - u) := by
      rw [abs_of_pos hsub_pos, hsqrt_σ,
        show Real.sqrt A - u * Real.sqrt A = Real.sqrt A * (1 - u) by ring,
        Real.log_mul (Real.sqrt_pos.mpr hA_pos).ne' (by linarith),
        Real.sqrt_eq_rpow, Real.log_rpow hA_pos]
    have hlog_add : Real.log (Real.sqrt A + Real.sqrt σ) =
        (1 / 2 : ℝ) * Real.log A + Real.log (1 + u) := by
      rw [hsqrt_σ, show Real.sqrt A + u * Real.sqrt A = Real.sqrt A * (1 + u) by ring,
        Real.log_mul (Real.sqrt_pos.mpr hA_pos).ne' (by linarith),
        Real.sqrt_eq_rpow, Real.log_rpow hA_pos]
    have h1m_pos : 0 < 1 - u := by linarith
    have h1p_pos : 0 < 1 + u := by linarith
    have hlog_sum : Real.log (1 - u) + Real.log (1 + u) = Real.log (1 - u ^ 2) := by
      rw [← Real.log_mul h1m_pos.ne' h1p_pos.ne']
      congr 1; ring
    have hlog_diff : Real.log (1 - u) - Real.log (1 + u) = Real.log ((1 - u) / (1 + u)) := by
      rw [Real.log_div h1m_pos.ne' h1p_pos.ne']
    have h1 := abs_neg_log_one_sub_sub_le (div_nonneg hσ_pos.le hA_pos.le) hσA_half
    have h2 := abs_log_one_sub_div_one_add_add_le hu_pos.le hu_half
    set F1 := -Real.log (1 - σ / A) - (σ / A + (σ / A) ^ 2 / 2)
    set F2 := Real.log ((1 - u) / (1 + u)) + 2 * u
    have hpow_A : A ^ (3 / 2 : ℝ) * (σ / A) = σ * Real.sqrt A := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hA_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      field_simp [hA_pos.ne']
    have hpow_A2 : A ^ (3 / 2 : ℝ) * ((σ / A) ^ 2 / 2) = σ ^ 2 / 2 * A ^ (-(1 / 2 : ℝ)) := by
      rw [hA_half, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hA_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      field_simp [hA_pos.ne', (Real.sqrt_pos.mpr hA_pos).ne']
      rw [Real.sq_sqrt hA_pos.le]
    have hσ32_mul : σ ^ (3 / 2 : ℝ) * u = σ ^ 2 * A ^ (-(1 / 2 : ℝ)) := by
      rw [hA_half]; dsimp [u]; rw [Real.sqrt_div hσ_pos.le,
        show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hσ_pos, Real.rpow_one,
        ← Real.sqrt_eq_rpow]
      have hsq : Real.sqrt σ ^ 2 = σ := Real.sq_sqrt hσ_pos.le
      field_simp [(Real.sqrt_pos.mpr hA_pos).ne']
      exact hsq
    have hmain : continuumFQ A σ -
        (continuumFQ A 0 + 6 * Real.sqrt A * σ - 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ))) =
        2 * A ^ (3 / 2 : ℝ) * F1 + 2 * σ ^ (3 / 2 : ℝ) * F2 := by
      rw [continuumFQ_pos hA_pos.le hσ_pos, continuumFQ_zero hA_pos.le, hlog_sub, hlog_add]
      have hid1 : Real.log (1 - u) + Real.log (1 + u) = -((σ / A + (σ / A) ^ 2 / 2) + F1) := by
        rw [hlog_sum, hu2]; dsimp [F1]; ring
      have hid2 : Real.log (1 - u) - Real.log (1 + u) = -2 * u + F2 := by
        rw [hlog_diff]; dsimp [F2]; ring
      have hstep1 : (-2 * (A ^ (3 / 2 : ℝ) - σ ^ (3 / 2 : ℝ)) * ((1 / 2 : ℝ) * Real.log A + Real.log (1 - u))
            - 2 * (A ^ (3 / 2 : ℝ) + σ ^ (3 / 2 : ℝ)) * ((1 / 2 : ℝ) * Real.log A + Real.log (1 + u))
            + 4 / 3 * A ^ (3 / 2 : ℝ) + 4 * σ * Real.sqrt A)
            - (-2 * A ^ (3 / 2 : ℝ) * Real.log A + 4 / 3 * A ^ (3 / 2 : ℝ)
              + 6 * Real.sqrt A * σ - 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ)))
          = -2 * A ^ (3 / 2 : ℝ) * (Real.log (1 - u) + Real.log (1 + u))
            + 2 * σ ^ (3 / 2 : ℝ) * (Real.log (1 - u) - Real.log (1 + u))
            - 2 * σ * Real.sqrt A + 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ)) := by ring
      rw [hstep1, hid1, hid2]
      have hstep2 : -2 * A ^ (3 / 2 : ℝ) * (-((σ / A + (σ / A) ^ 2 / 2) + F1))
            + 2 * σ ^ (3 / 2 : ℝ) * (-2 * u + F2)
            - 2 * σ * Real.sqrt A + 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ))
          = 2 * (A ^ (3 / 2 : ℝ) * (σ / A)) + 2 * (A ^ (3 / 2 : ℝ) * ((σ / A) ^ 2 / 2))
            - 4 * (σ ^ (3 / 2 : ℝ) * u) - 2 * σ * Real.sqrt A + 3 * σ ^ 2 * A ^ (-(1 / 2 : ℝ))
            + 2 * A ^ (3 / 2 : ℝ) * F1 + 2 * σ ^ (3 / 2 : ℝ) * F2 := by ring
      rw [hstep2, hpow_A, hpow_A2, hσ32_mul]
      ring
    rw [hmain]
    have hA_cube : A ^ (3 / 2 : ℝ) * (σ / A) ^ 3 = σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
      rw [hA_32]
      have hA3 : (A ^ (3 / 2 : ℝ)) ^ 2 = A ^ 3 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hA_pos.le]; norm_num
      field_simp [hA_pos.ne', (Real.rpow_pos_of_pos hA_pos _).ne']
      exact hA3
    have hbd1 : |2 * A ^ (3 / 2 : ℝ) * F1| ≤ 4 / 3 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.rpow_pos_of_pos hA_pos _)]
      calc 2 * A ^ (3 / 2 : ℝ) * |F1|
          ≤ 2 * A ^ (3 / 2 : ℝ) * (2 * (σ / A) ^ 3 / 3) := by gcongr
        _ = 4 / 3 * (A ^ (3 / 2 : ℝ) * (σ / A) ^ 3) := by ring
        _ = 4 / 3 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by rw [hA_cube]; ring
    have hbd2 : |2 * σ ^ (3 / 2 : ℝ) * F2| ≤ 16 / 9 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_pos (Real.rpow_pos_of_pos hσ_pos _)]
      have hu3 : u ^ 3 = σ ^ (3 / 2 : ℝ) * A ^ (-(3 / 2 : ℝ)) := by
        dsimp [u]
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hσ_pos.le hA_pos.le),
          Real.div_rpow hσ_pos.le hA_pos.le, div_eq_mul_inv, hA_32]
        norm_num
      have hσ3 : σ ^ (3 / 2 : ℝ) * σ ^ (3 / 2 : ℝ) = σ ^ 3 := by
        rw [← Real.rpow_add hσ_pos]; norm_num
      calc 2 * σ ^ (3 / 2 : ℝ) * |F2|
          ≤ 2 * σ ^ (3 / 2 : ℝ) * (8 / 9 * u ^ 3) := by gcongr
        _ = 16 / 9 * (σ ^ (3 / 2 : ℝ) * σ ^ (3 / 2 : ℝ)) * A ^ (-(3 / 2 : ℝ)) := by rw [hu3]; ring
        _ = 16 / 9 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by rw [hσ3]
    calc |2 * A ^ (3 / 2 : ℝ) * F1 + 2 * σ ^ (3 / 2 : ℝ) * F2|
        ≤ |2 * A ^ (3 / 2 : ℝ) * F1| + |2 * σ ^ (3 / 2 : ℝ) * F2| := abs_add_le _ _
      _ ≤ 4 / 3 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) + 16 / 9 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) :=
          add_le_add hbd1 hbd2
      _ ≤ 4 * σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by
          have : 0 ≤ σ ^ 3 * A ^ (-(3 / 2 : ℝ)) := by positivity
          linarith

/-! ### Step 3 Continuum vs Midpoint Comparison (`σ = -a < 0`) -/

private lemma summable_nat_rpow_neg_four_thirds :
    Summable (fun k : ℕ => (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
  have hs := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 4 / 3)
  refine hs.congr (fun k => ?_)
  rw [Real.rpow_neg (Nat.cast_nonneg k)]

private lemma abs_phi_log_second_deriv_le {a x : ℝ} (ha : 0 < a) (hx : (1 / 2 : ℝ) ≤ x) :
    |( -(2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) *
        (a + 3 * (x - 1 / 4) ^ (2 / 3 : ℝ)) / (a + (x - 1 / 4) ^ (2 / 3 : ℝ)) ^ 2 )| ≤
      (2 / 3 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) / a := by
  have hx_gt : 0 < x - 1 / 4 := by linarith
  set r := (x - 1 / 4) ^ (2 / 3 : ℝ)
  have hr_nn : 0 ≤ r := Real.rpow_nonneg hx_gt.le _
  have hu_nn : 0 ≤ (x - 1 / 4) ^ (-(4 / 3 : ℝ)) := Real.rpow_nonneg hx_gt.le _
  have hden_pos : 0 < a + r := by linarith
  have hnum_nn : 0 ≤ (2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + 3 * r) := by positivity
  rw [show -(2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + 3 * r) =
      -((2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + 3 * r)) by ring,
    abs_div, abs_neg, abs_of_nonneg hnum_nn, abs_of_pos (sq_pos_of_pos hden_pos)]
  rw [div_le_div_iff₀ (sq_pos_of_pos hden_pos) ha]
  have hbound : a + 3 * r ≤ 3 * (a + r) := by linarith
  have hsq : a * (a + r) ≤ (a + r) ^ 2 := by nlinarith
  calc (2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + 3 * r) * a
      ≤ (2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (3 * (a + r)) * a := by gcongr
    _ = (2 / 3 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a * (a + r)) := by ring
    _ ≤ (2 / 3 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + r) ^ 2 := by gcongr

private lemma midpoint_peano_log_phi_step {a : ℝ} (ha : (1 : ℝ) ≤ a) {k : ℕ} (hk : 1 ≤ k) :
    |(∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) -
        Real.log (a + phiQuantile k)| ≤
      ((1 / 12 : ℝ) * (4 : ℝ) ^ (4 / 3 : ℝ) / a) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
  have ha_pos : 0 < a := by linarith
  have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  let g : ℝ → ℝ := fun x => Real.log (a + (x - 1 / 4) ^ (2 / 3 : ℝ))
  let g' : ℝ → ℝ := fun x =>
    ((2 / 3 : ℝ) * (x - 1 / 4) ^ (-(1 / 3 : ℝ))) / (a + (x - 1 / 4) ^ (2 / 3 : ℝ))
  let g'' : ℝ → ℝ := fun x =>
    -(2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) *
      (a + 3 * (x - 1 / 4) ^ (2 / 3 : ℝ)) / (a + (x - 1 / 4) ^ (2 / 3 : ℝ)) ^ 2
  have hx_mem_pos : ∀ x ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), 0 < x - 1 / 4 := by
    intro x hx; linarith [hx.1, hk_ge1]
  have hden_pos : ∀ x ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2),
      0 < a + (x - 1 / 4) ^ (2 / 3 : ℝ) := by
    intro x hx
    exact add_pos ha_pos (Real.rpow_pos_of_pos (hx_mem_pos x hx) _)
  have hg : ∀ x ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), HasDerivAt g (g' x) x := by
    intro x hx
    have hx_gt := hx_mem_pos x hx
    have hpow : HasDerivAt (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ))
        (1 * (2 / 3 : ℝ) * (x - 1 / 4) ^ ((2 / 3 : ℝ) - 1)) x :=
      ((hasDerivAt_id x).sub_const (1 / 4 : ℝ)).rpow_const (Or.inl hx_gt.ne')
    have hsum : HasDerivAt (fun y : ℝ => a + (y - 1 / 4) ^ (2 / 3 : ℝ))
        ((2 / 3 : ℝ) * (x - 1 / 4) ^ (-(1 / 3 : ℝ))) x := by
      convert (hasDerivAt_const x a).add hpow using 1
      norm_num
    have hlog := (Real.hasDerivAt_log (hden_pos x hx).ne').comp x hsum
    refine hlog.congr_deriv ?_
    dsimp [g']; ring
  have hg' : ∀ x ∈ Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2), HasDerivAt g' (g'' x) x := by
    intro x hx
    have hx_gt := hx_mem_pos x hx
    have hd_pos := hden_pos x hx
    have hpow_num : HasDerivAt (fun y : ℝ => (y - 1 / 4) ^ (-(1 / 3 : ℝ)))
        (1 * (-(1 / 3 : ℝ)) * (x - 1 / 4) ^ ((-(1 / 3 : ℝ)) - 1)) x :=
      ((hasDerivAt_id x).sub_const (1 / 4 : ℝ)).rpow_const (Or.inl hx_gt.ne')
    have hnum : HasDerivAt (fun y : ℝ => (2 / 3 : ℝ) * (y - 1 / 4) ^ (-(1 / 3 : ℝ)))
        (-(2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ))) x := by
      refine (hpow_num.const_mul (2 / 3 : ℝ)).congr_deriv ?_
      have hexp : (-(1 / 3 : ℝ)) - 1 = -(4 / 3 : ℝ) := by norm_num
      rw [hexp]
      ring
    have hpow_den : HasDerivAt (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ))
        (1 * (2 / 3 : ℝ) * (x - 1 / 4) ^ ((2 / 3 : ℝ) - 1)) x :=
      ((hasDerivAt_id x).sub_const (1 / 4 : ℝ)).rpow_const (Or.inl hx_gt.ne')
    have hden : HasDerivAt (fun y : ℝ => a + (y - 1 / 4) ^ (2 / 3 : ℝ))
        ((2 / 3 : ℝ) * (x - 1 / 4) ^ (-(1 / 3 : ℝ))) x := by
      refine ((hasDerivAt_const x a).add hpow_den).congr_deriv ?_
      have hexp : (2 / 3 : ℝ) - 1 = -(1 / 3 : ℝ) := by norm_num
      rw [hexp]
      ring
    refine (hnum.div hden hd_pos.ne').congr_deriv ?_
    have hexp : (x - 1 / 4) ^ (-(1 / 3 : ℝ)) * (x - 1 / 4) ^ (-(1 / 3 : ℝ)) =
        (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (x - 1 / 4) ^ (2 / 3 : ℝ) := by
      rw [← Real.rpow_add hx_gt, ← Real.rpow_add hx_gt]
      norm_num
    dsimp [g'']
    have hnum_eq : -(2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + (x - 1 / 4) ^ (2 / 3 : ℝ)) -
        2 / 3 * (x - 1 / 4) ^ (-(1 / 3 : ℝ)) * (2 / 3 * (x - 1 / 4) ^ (-(1 / 3 : ℝ))) =
        -(2 / 9 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) * (a + 3 * (x - 1 / 4) ^ (2 / 3 : ℝ)) := by
      have hid : 2 / 3 * (x - 1 / 4) ^ (-(1 / 3 : ℝ)) * (2 / 3 * (x - 1 / 4) ^ (-(1 / 3 : ℝ))) =
          4 / 9 * ((x - 1 / 4) ^ (-(1 / 3 : ℝ)) * (x - 1 / 4) ^ (-(1 / 3 : ℝ))) := by ring
      rw [hid, hexp]
      ring
    rw [← hnum_eq]
  have hg''_cont : ContinuousOn g'' (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) := by
    have hpow1 : ContinuousOn (fun y : ℝ => (y - 1 / 4) ^ (-(4 / 3 : ℝ)))
        (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
      ContinuousOn.rpow_const (continuous_id.sub continuous_const).continuousOn
        (fun x hx => Or.inl (hx_mem_pos x hx).ne')
    have hpow2 : ContinuousOn (fun y : ℝ => (y - 1 / 4) ^ (2 / 3 : ℝ))
        (Set.Icc ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2)) :=
      ContinuousOn.rpow_const (continuous_id.sub continuous_const).continuousOn
        (fun x hx => Or.inl (hx_mem_pos x hx).ne')
    refine (((continuousOn_const.mul hpow1).mul
      (continuousOn_const.add (continuousOn_const.mul hpow2))).div
      ((continuousOn_const.add hpow2).pow 2)) (fun x hx => sq_pos_of_pos (hden_pos x hx) |>.ne')
  have hpeano := midpoint_peano_eq hg hg' hg''_cont
  have hleft : (∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) -
      Real.log (a + phiQuantile k) =
      ∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
        ((1 / 2 : ℝ) * (1 / 2 - |x - (k : ℝ)|) ^ 2) * g'' x := by
    have heq_int : ∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), Real.log (a + phiQuantile x) =
        ∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), g x := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rfl
    rw [heq_int]
    exact hpeano
  rw [hleft]
  set M : ℝ := ((1 / 12 : ℝ) * (4 : ℝ) ^ (4 / 3 : ℝ) / a) * (k : ℝ) ^ (-(4 / 3 : ℝ))
  have hk_cont : Continuous (fun x : ℝ => (1 / 2 : ℝ) * (1 / 2 - |x - (k : ℝ)|) ^ 2) :=
    continuous_const.mul
      ((continuous_const.sub (continuous_abs.comp (continuous_id.sub continuous_const))).pow 2)
  have hle_interval : (k : ℝ) - 1 / 2 ≤ (k : ℝ) + 1 / 2 := by linarith
  have hint_M : IntervalIntegrable (fun _ : ℝ => M) volume ((k : ℝ) - 1 / 2) ((k : ℝ) + 1 / 2) :=
    intervalIntegrable_const
  have hnorm : ‖∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2),
      ((1 / 2 : ℝ) * (1 / 2 - |x - (k : ℝ)|) ^ 2) * g'' x‖ ≤
      ∫ _ in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), M := by
    refine intervalIntegral.norm_integral_le_of_norm_le hle_interval
      (Eventually.of_forall fun x hx => ?_) hint_M
    have hkx : |x - (k : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hker_nn : 0 ≤ (1 / 2 : ℝ) * (1 / 2 - |x - (k : ℝ)|) ^ 2 := by positivity
    have hker_le : (1 / 2 : ℝ) * (1 / 2 - |x - (k : ℝ)|) ^ 2 ≤ 1 / 8 := by
      have hsub_nn : 0 ≤ 1 / 2 - |x - (k : ℝ)| := by linarith
      have hsub_le : 1 / 2 - |x - (k : ℝ)| ≤ 1 / 2 := by linarith [abs_nonneg (x - (k : ℝ))]
      nlinarith
    have hx_quarter : (k : ℝ) / 4 ≤ x - 1 / 4 := by linarith [hx.1, hk_ge1]
    have hrpow_mono : (x - 1 / 4) ^ (-(4 / 3 : ℝ)) ≤ ((k : ℝ) / 4) ^ (-(4 / 3 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hx_quarter (by norm_num)
    have hrpow_id : ((k : ℝ) / 4) ^ (-(4 / 3 : ℝ)) =
        (4 : ℝ) ^ (4 / 3 : ℝ) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
      rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by norm_num),
        Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
        neg_neg, mul_comm]
    have hg''_bd := abs_phi_log_second_deriv_le (x := x) ha_pos (by linarith [hx.1, hk_ge1])
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hker_nn]
    calc (1 / 2 : ℝ) * (1 / 2 - |x - (k : ℝ)|) ^ 2 * |g'' x|
        ≤ (1 / 8 : ℝ) * ((2 / 3 : ℝ) * (x - 1 / 4) ^ (-(4 / 3 : ℝ)) / a) :=
          mul_le_mul hker_le hg''_bd (abs_nonneg _) (by norm_num)
      _ ≤ (1 / 8 : ℝ) * ((2 / 3 : ℝ) * (((k : ℝ) / 4) ^ (-(4 / 3 : ℝ))) / a) := by gcongr
      _ = M := by rw [hrpow_id]; dsimp [M]; ring
  rw [Real.norm_eq_abs, intervalIntegral.integral_const, smul_eq_mul] at hnorm
  linarith [hnorm]

/-- Midpoint Peano comparison on `[1/4, K + 1/2]` for `σ = -a` (`a ≥ 1`). -/
theorem continuumFQ_AK_add_sum_phiQuantile_bound :
    ∃ C > 0, ∀ a ≥ (1 : ℝ), ∀ K : ℕ,
      |continuumFQ (continuumAK K) (-a) +
        (∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + phiQuantile k)) +
        (1 / 2 : ℝ) * Real.log a| ≤ C / a := by
  let S43 : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(4 / 3 : ℝ))
  have hS43_pos : 0 < S43 := by
    have h1 : (0 : ℝ) < (1 : ℕ) ^ (-(4 / 3 : ℝ)) := by simp
    exact lt_of_lt_of_le h1 (summable_nat_rpow_neg_four_thirds.le_tsum 1
      (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _))
  let C0 : ℝ := (1 / 6 : ℝ) * (4 : ℝ) ^ (4 / 3 : ℝ)
  refine ⟨1 + C0 * S43, by positivity, fun a ha K => ?_⟩
  have ha_pos : 0 < a := by linarith
  have hk_le : (1 / 4 : ℝ) ≤ (K : ℝ) + 1 / 2 := by
    linarith [Nat.cast_nonneg (α := ℝ) K]
  have hint_fn_of : ∀ u v : ℝ, (1 / 4 : ℝ) ≤ u → u ≤ v →
      IntervalIntegrable (fun x : ℝ => Real.log (a + phiQuantile x)) volume u v := by
    intro u v hu huv
    refine ContinuousOn.intervalIntegrable_of_Icc huv ?_
    refine ContinuousOn.log ?_ ?_
    · have hphi_cont : ContinuousOn phiQuantile (Set.Icc u v) :=
        ((continuous_id.sub continuous_const).rpow_const
          (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))).continuousOn
      exact continuousOn_const.add hphi_cont
    · intro x hx
      have hphi : 0 ≤ phiQuantile x := by
        unfold phiQuantile; exact Real.rpow_nonneg (by linarith [hx.1, hu]) _
      linarith
  have hint_left : IntervalIntegrable (fun x : ℝ => Real.log (a + phiQuantile x))
      volume (1 / 4) (1 / 2) := hint_fn_of (1 / 4) (1 / 2) le_rfl (by norm_num)
  have hint_right : IntervalIntegrable (fun x : ℝ => Real.log (a + phiQuantile x))
      volume (1 / 2) ((K : ℝ) + 1 / 2) :=
    hint_fn_of (1 / 2) ((K : ℝ) + 1 / 2) (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) K])
  have hfq : continuumFQ (continuumAK K) (-a) =
      -2 * ∫ x in (1 / 4 : ℝ)..((K : ℝ) + 1 / 2), Real.log (a + phiQuantile x) := by
    rw [continuumFQ_AK_eq K (-a)]
    congr 1
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx_ge : (1 / 4 : ℝ) ≤ x := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · linarith
    have hphi : 0 ≤ phiQuantile x := by
      unfold phiQuantile; exact Real.rpow_nonneg (sub_nonneg.mpr hx_ge) _
    rw [abs_of_neg (by linarith : -a - phiQuantile x < 0)]
    ring_nf
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint_left hint_right
  have hleft_bd : |(-2 * ∫ x in (1 / 4 : ℝ)..(1 / 2), Real.log (a + phiQuantile x)) +
      (1 / 2 : ℝ) * Real.log a| ≤ 1 / a := by
    have hconst : (1 / 2 : ℝ) * Real.log a = 2 * ∫ _ in (1 / 4 : ℝ)..(1 / 2), Real.log a := by
      simp [intervalIntegral.integral_const]; ring
    have hsub : (-2 * ∫ x in (1 / 4 : ℝ)..(1 / 2), Real.log (a + phiQuantile x)) +
        (1 / 2 : ℝ) * Real.log a =
        -2 * ∫ x in (1 / 4 : ℝ)..(1 / 2), (Real.log (a + phiQuantile x) - Real.log a) := by
      rw [hconst, intervalIntegral.integral_sub hint_left intervalIntegrable_const]; ring
    rw [hsub, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
    have hnorm : ‖∫ x in (1 / 4 : ℝ)..(1 / 2), (Real.log (a + phiQuantile x) - Real.log a)‖ ≤
        ∫ _ in (1 / 4 : ℝ)..(1 / 2), (1 / a) := by
      refine intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
        (Eventually.of_forall fun x hx => ?_) intervalIntegrable_const
      have hphi_nn : 0 ≤ phiQuantile x := by
        unfold phiQuantile; exact Real.rpow_nonneg (by linarith [hx.1]) _
      have hphi_le : phiQuantile x ≤ 1 := by
        unfold phiQuantile
        exact Real.rpow_le_one (by linarith [hx.1]) (by linarith [hx.2]) (by norm_num)
      have hid : Real.log (a + phiQuantile x) - Real.log a = Real.log (1 + phiQuantile x / a) := by
        rw [← Real.log_div (by linarith) ha_pos.ne']
        congr 1; field_simp [ha_pos.ne']
      have hpos1 : 0 < 1 + phiQuantile x / a :=
        add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hphi_nn ha_pos.le)
      rw [Real.norm_eq_abs, hid, abs_of_nonneg (Real.log_nonneg (by linarith [div_nonneg hphi_nn ha_pos.le]))]
      have hle := Real.log_le_sub_one_of_pos hpos1
      linarith [div_le_div_of_nonneg_right hphi_le ha_pos.le]
    rw [Real.norm_eq_abs] at hnorm
    have hct : ∫ _ in (1 / 4 : ℝ)..(1 / 2), (1 / a) = (1 / 4 : ℝ) * (1 / a) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    nlinarith [hnorm, hct, div_nonneg (by norm_num : (0 : ℝ) ≤ 1) ha_pos.le]
  have hright_bd : ∀ M : ℕ, (M ≤ K) →
      |(-2 * ∫ x in (1 / 2 : ℝ)..((M : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) +
        ∑ k ∈ Finset.Icc 1 M, 2 * Real.log (a + phiQuantile k)| ≤
        (C0 / a) * ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro M hMK
    induction M with
    | zero => simp
    | succ M ih =>
      have hM_le : M ≤ K := Nat.le_of_succ_le hMK
      have h_ih := ih hM_le
      have hIcc : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
        ext x; simp [Finset.mem_Icc]; omega
      have hnot : (M + 1) ∉ Finset.Icc 1 M := by simp [Finset.mem_Icc]
      have hint_M1 : IntervalIntegrable (fun x : ℝ => Real.log (a + phiQuantile x))
          volume (1 / 2) ((M : ℝ) + 1 / 2) :=
        hint_fn_of (1 / 2) ((M : ℝ) + 1 / 2) (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) M])
      have hint_step : IntervalIntegrable (fun x : ℝ => Real.log (a + phiQuantile x))
          volume ((M : ℝ) + 1 / 2) (((M + 1 : ℕ) : ℝ) + 1 / 2) :=
        hint_fn_of ((M : ℝ) + 1 / 2) (((M + 1 : ℕ) : ℝ) + 1 / 2)
          (by linarith [Nat.cast_nonneg (α := ℝ) M]) (by push_cast; linarith)
      have hsplit_M := intervalIntegral.integral_add_adjacent_intervals hint_M1 hint_step
      have hstep := midpoint_peano_log_phi_step ha (k := M + 1) (by omega)
      have hmid_eq1 : ((M + 1 : ℕ) : ℝ) - 1 / 2 = (M : ℝ) + 1 / 2 := by push_cast; ring
      rw [hmid_eq1] at hstep
      have hstep' : |(∫ x in ((M : ℝ) + 1 / 2)..(((M + 1 : ℕ) : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) -
          Real.log (a + phiQuantile ((M : ℝ) + 1))| ≤
          ((1 / 12 : ℝ) * (4 : ℝ) ^ (4 / 3 : ℝ) / a) * ((M + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hstep
      have heq_comb : (-2 * ∫ x in (1 / 2 : ℝ)..(((M + 1 : ℕ) : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) +
          ∑ k ∈ Finset.Icc 1 (M + 1), 2 * Real.log (a + phiQuantile k) =
          ((-2 * ∫ x in (1 / 2 : ℝ)..((M : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) +
            ∑ k ∈ Finset.Icc 1 M, 2 * Real.log (a + phiQuantile k)) +
          (-2 * ((∫ x in ((M : ℝ) + 1 / 2)..(((M + 1 : ℕ) : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) -
            Real.log (a + phiQuantile ((M : ℝ) + 1)))) := by
        rw [← hsplit_M, hIcc, Finset.sum_insert hnot]
        push_cast
        ring
      rw [heq_comb, hIcc, Finset.sum_insert hnot]
      calc |_ + _|
          ≤ |(-2 * ∫ x in (1 / 2 : ℝ)..((M : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) +
              ∑ k ∈ Finset.Icc 1 M, 2 * Real.log (a + phiQuantile k)| +
            |-2 * ((∫ x in ((M : ℝ) + 1 / 2)..(((M + 1 : ℕ) : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) -
              Real.log (a + phiQuantile ((M : ℝ) + 1)))| := abs_add_le _ _
        _ ≤ (C0 / a) * ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (-(4 / 3 : ℝ)) +
            2 * (((1 / 12 : ℝ) * (4 : ℝ) ^ (4 / 3 : ℝ) / a) * ((M + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ))) := by
              refine add_le_add h_ih ?_
              rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
              exact mul_le_mul_of_nonneg_left hstep' (by norm_num)
        _ = (C0 / a) * (((M + 1 : ℕ) : ℝ) ^ (-(4 / 3 : ℝ)) +
              ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (-(4 / 3 : ℝ))) := by
            dsimp [C0]; ring
  have hsum_le : ∑ k ∈ Finset.Icc 1 K, (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ S43 :=
    summable_nat_rpow_neg_four_thirds.sum_le_tsum (Finset.Icc 1 K)
      (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
  have hrb := le_trans (hright_bd K le_rfl)
    (mul_le_mul_of_nonneg_left hsum_le (by positivity))
  have hfull_eq : continuumFQ (continuumAK K) (-a) +
      (∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + phiQuantile k)) + (1 / 2 : ℝ) * Real.log a =
      ((-2 * ∫ x in (1 / 4 : ℝ)..(1 / 2), Real.log (a + phiQuantile x)) + (1 / 2 : ℝ) * Real.log a) +
      ((-2 * ∫ x in (1 / 2 : ℝ)..((K : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) +
        ∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + phiQuantile k)) := by
    rw [hfq, ← hsplit]; ring
  rw [hfull_eq]
  calc |_ + _|
      ≤ |(-2 * ∫ x in (1 / 4 : ℝ)..(1 / 2), Real.log (a + phiQuantile x)) + (1 / 2 : ℝ) * Real.log a| +
        |(-2 * ∫ x in (1 / 2 : ℝ)..((K : ℝ) + 1 / 2), Real.log (a + phiQuantile x)) +
          ∑ k ∈ Finset.Icc 1 K, 2 * Real.log (a + phiQuantile k)| := abs_add_le _ _
    _ ≤ 1 / a + (C0 / a) * S43 := add_le_add hleft_bd hrb
    _ = (1 + C0 * S43) / a := by ring

/-- Perturbation of `∑_{k=1}^K 2 log(a + s_k)` vs `∑_{k=1}^K 2 log(a + phiQuantile k)` for `a` large
when `|s_k - phiQuantile k| ≤ Cδ * k^{-4/3}`. -/
theorem sum_log_site_shift_neg_bound {sNode : ℕ → ℝ} {Cδ : ℝ} (hCδ : 0 < Cδ)
    (hshift : ∀ k : ℕ, 1 ≤ k → |sNode k - phiQuantile k| ≤ Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ))) :
    ∃ C > 0, ∀ a ≥ max (2 * Cδ) 1, ∀ K : ℕ,
      |∑ k ∈ Finset.Icc 1 K, (2 * Real.log (a + sNode k) - 2 * Real.log (a + phiQuantile k))| ≤ C / a := by
  let S43 : ℝ := ∑' k : ℕ, (k : ℝ) ^ (-(4 / 3 : ℝ))
  have hS43_pos : 0 < S43 := by
    have h1 : (0 : ℝ) < (1 : ℕ) ^ (-(4 / 3 : ℝ)) := by simp
    exact lt_of_lt_of_le h1 (summable_nat_rpow_neg_four_thirds.le_tsum 1
      (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _))
  refine ⟨4 * Cδ * S43, by positivity, fun a ha K => ?_⟩
  have ha1 : 1 ≤ a := le_trans (le_max_right _ _) ha
  have ha2C : 2 * Cδ ≤ a := le_trans (le_max_left _ _) ha
  have ha_pos : 0 < a := by linarith
  have hterm : ∀ k ∈ Finset.Icc 1 K,
      |2 * Real.log (a + sNode k) - 2 * Real.log (a + phiQuantile k)| ≤
        (4 * Cδ / a) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hphi_nn : 0 ≤ phiQuantile k := by
      unfold phiQuantile; exact Real.rpow_nonneg (by linarith) _
    have hden_pos : 0 < a + phiQuantile k := by linarith
    have hk43_le1 : (k : ℝ) ^ (-(4 / 3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hk_ge1 (by norm_num)
    set t : ℝ := (sNode k - phiQuantile k) / (a + phiQuantile k)
    have ht_le : |t| ≤ Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ)) / a := by
      dsimp [t]
      rw [abs_div, abs_of_pos hden_pos]
      calc |sNode k - phiQuantile k| / (a + phiQuantile k)
          ≤ (Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ))) / (a + phiQuantile k) :=
            div_le_div_of_nonneg_right (hshift k hk1) hden_pos.le
        _ ≤ (Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ))) / a :=
            div_le_div_of_nonneg_left (by positivity) ha_pos (by linarith)
    have ht_half : |t| ≤ 1 / 2 := by
      calc |t| ≤ Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ)) / a := ht_le
        _ ≤ (Cδ * 1) / a :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk43_le1 hCδ.le) ha_pos.le
        _ ≤ (Cδ * 1) / (2 * Cδ) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) ha2C
        _ = 1 / 2 := by field_simp [hCδ.ne']
    have hs_pos : 0 < a + sNode k := by
      have hlow := (abs_le.mp ht_half).1
      have ht_eq : a + sNode k = (a + phiQuantile k) * (1 + t) := by
        dsimp [t]; field_simp [hden_pos.ne']; ring
      rw [ht_eq]
      exact mul_pos hden_pos (by linarith)
    have hid : 2 * Real.log (a + sNode k) - 2 * Real.log (a + phiQuantile k) =
        2 * Real.log (1 + t) := by
      rw [show 2 * Real.log (a + sNode k) - 2 * Real.log (a + phiQuantile k) =
          2 * (Real.log (a + sNode k) - Real.log (a + phiQuantile k)) by ring,
        ← Real.log_div hs_pos.ne' hden_pos.ne']
      congr 2; dsimp [t]; field_simp [hden_pos.ne']; ring
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc 2 * |Real.log (1 + t)| ≤ 2 * (2 * |t|) :=
          mul_le_mul_of_nonneg_left (abs_log_one_add_le_two_mul ht_half) (by norm_num)
      _ ≤ 4 * (Cδ * (k : ℝ) ^ (-(4 / 3 : ℝ)) / a) := by linarith [ht_le]
      _ = (4 * Cδ / a) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := by ring
  calc |∑ k ∈ Finset.Icc 1 K, (2 * Real.log (a + sNode k) - 2 * Real.log (a + phiQuantile k))|
      ≤ ∑ k ∈ Finset.Icc 1 K, |2 * Real.log (a + sNode k) - 2 * Real.log (a + phiQuantile k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Icc 1 K, (4 * Cδ / a) * (k : ℝ) ^ (-(4 / 3 : ℝ)) := Finset.sum_le_sum hterm
    _ = (4 * Cδ / a) * ∑ k ∈ Finset.Icc 1 K, (k : ℝ) ^ (-(4 / 3 : ℝ)) := by
        rw [← Finset.mul_sum]
    _ ≤ (4 * Cδ / a) * S43 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact summable_nat_rpow_neg_four_thirds.sum_le_tsum (Finset.Icc 1 K)
          (fun k _ => Real.rpow_nonneg (Nat.cast_nonneg k) _)
    _ = 4 * Cδ * S43 / a := by ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.continuumFQ_sub_lobe_asymptotic' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuumFQ_sub_lobe_asymptotic

/-- info: 'FormalResearch.ModularBootstrap.Upper.Window.continuumFQ_AK_add_sum_phiQuantile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuumFQ_AK_add_sum_phiQuantile_bound

end

end FormalResearch.ModularBootstrap.Upper.Window

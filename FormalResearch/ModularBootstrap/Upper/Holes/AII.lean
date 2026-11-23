module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Deriv

/-!
# Analytic Region-II Eight-Neighbour Hole Floor (Lemma `A_II`)

Formalizes Lemma `A_II` (`rem:analyticII`) of `CFT/modular_bootstrap/paper/remainder.tex`
(lines 181--215):

* `hAII`: the eight-neighbour (and general-$j$) hole model function
  $h_j(v) = \sum_{k=0}^{j-1} \log\bigl(((v - k - \tfrac12)^2 + \tfrac1{16})((v + k + \tfrac12)^2 + \tfrac1{16})\bigr) - 2\int_{-j}^{j}\log|v-w|\,dw$
  for $|v| \le \frac12$.
* `hAII_neg`: symmetry $h_j(-v) = h_j(v)$.
* `hAII_min_at_half`: for $j = 1$ and $j = 4$, the minimum of $h_j$ on $[-\frac12, \frac12]$
  is attained at $v = \pm\frac12$.
* `muFour`: $\mu_4 = \frac14 e^{h_4(1/2)}$.
* `muFour_eq_closed`: exact closed form
  $\mu_4 = \frac{e^{16}}{4} \frac{\prod_{i=-3}^{4}(i^2 + \frac1{16})}{(9/2)^9 (7/2)^7}$.
* `muFour_gt`: exact rational bound $\mu_4 > \frac{7}{10}$ (the paper's $\mu_4 > 0.700$),
  proved from $e > \sum_{m=0}^7 \frac{1}{m!} = \frac{685}{252}$ and `norm_num`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

/-- Hole model function $h_j(v)$ at $\eta = \frac14$ (`remainder.tex`, `rem:analyticII`). -/
noncomputable def hAII (j : ℕ) (v : ℝ) : ℝ :=
  (∑ k ∈ Finset.range j,
    Real.log (((v - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
      ((v + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2))) -
  2 * ∫ w in (-(j : ℝ))..(j : ℝ), Real.log |v - w|

/-- Closed form of the hole model function $h_j(v)$ for $|v| < j$. -/
noncomputable def hAIIClosed (j : ℕ) (v : ℝ) : ℝ :=
  (∑ k ∈ Finset.range j,
    Real.log (((v - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
      ((v + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2))) -
  2 * (((j : ℝ) + v) * Real.log ((j : ℝ) + v) + ((j : ℝ) - v) * Real.log ((j : ℝ) - v) -
    2 * (j : ℝ))

private lemma integral_log_zero_to (a : ℝ) :
    ∫ x in (0 : ℝ)..a, Real.log x = a * Real.log a - a := by
  simp

private lemma intervalIntegrable_log_abs_sub (v a b : ℝ) :
    IntervalIntegrable (fun w : ℝ => Real.log |v - w|) volume a b := by
  simpa only [Function.comp_def, Real.log_abs, sub_sub_cancel] using
    ((intervalIntegral.intervalIntegrable_log' (a := v - b) (b := v - a)).comp_sub_left v).symm

private lemma integral_log_abs_sub_eq {j : ℕ} (hj : 1 ≤ j) {v : ℝ} (hv : |v| < (j : ℝ)) :
    ∫ w in (-(j : ℝ))..(j : ℝ), Real.log |v - w| =
      ((j : ℝ) + v) * Real.log ((j : ℝ) + v) + ((j : ℝ) - v) * Real.log ((j : ℝ) - v) -
        2 * (j : ℝ) := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hv1 : -(j : ℝ) < v := by linarith [(abs_lt.mp hv).1]
  have hv2 : v < (j : ℝ) := (abs_lt.mp hv).2
  have hi1 : IntervalIntegrable (fun w : ℝ => Real.log |v - w|) volume (-(j : ℝ)) v :=
    intervalIntegrable_log_abs_sub v (-(j : ℝ)) v
  have hi2 : IntervalIntegrable (fun w : ℝ => Real.log |v - w|) volume v (j : ℝ) :=
    intervalIntegrable_log_abs_sub v v (j : ℝ)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hL : ∫ w in (-(j : ℝ))..v, Real.log |v - w| =
      ((j : ℝ) + v) * Real.log ((j : ℝ) + v) - ((j : ℝ) + v) := by
    have hcongr : ∫ w in (-(j : ℝ))..v, Real.log |v - w| =
        ∫ w in (-(j : ℝ))..v, Real.log (v - w) := by
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [Set.uIcc_of_le hv1.le] at hw
      rw [abs_of_nonneg (sub_nonneg.mpr hw.2)]
    rw [hcongr, intervalIntegral.integral_comp_sub_left (fun u => Real.log u) v,
      sub_self, sub_neg_eq_add, add_comm v (j : ℝ), integral_log_zero_to ((j : ℝ) + v)]
  have hR : ∫ w in v..(j : ℝ), Real.log |v - w| =
      ((j : ℝ) - v) * Real.log ((j : ℝ) - v) - ((j : ℝ) - v) := by
    have hcongr : ∫ w in v..(j : ℝ), Real.log |v - w| =
        ∫ w in v..(j : ℝ), Real.log (w - v) := by
      refine intervalIntegral.integral_congr fun w hw => ?_
      rw [Set.uIcc_of_le hv2.le] at hw
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hw.1)]
    rw [hcongr, intervalIntegral.integral_comp_sub_right (fun u => Real.log u) v,
      sub_self, integral_log_zero_to ((j : ℝ) - v)]
  rw [hsplit, hL, hR]
  ring

lemma hAII_eq_closed {j : ℕ} (hj : 1 ≤ j) {v : ℝ} (hv : |v| < (j : ℝ)) :
    hAII j v = hAIIClosed j v := by
  unfold hAII hAIIClosed
  rw [integral_log_abs_sub_eq hj hv]

/-- Symmetry $h_j(-v) = h_j(v)$ (`remainder.tex`, `rem:analyticII`). -/
theorem hAII_neg (j : ℕ) (v : ℝ) : hAII j (-v) = hAII j v := by
  unfold hAII
  have hsum : ∑ k ∈ Finset.range j,
      Real.log (((-v - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
        ((-v + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)) =
      ∑ k ∈ Finset.range j,
      Real.log (((v - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
        ((v + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    have h1 : (-v - (k : ℝ) - 1 / 2) ^ 2 = (v + (k : ℝ) + 1 / 2) ^ 2 := by ring
    have h2 : (-v + (k : ℝ) + 1 / 2) ^ 2 = (v - (k : ℝ) - 1 / 2) ^ 2 := by ring
    rw [h1, h2, mul_comm]
  have hint : ∫ w in (-(j : ℝ))..(j : ℝ), Real.log |-v - w| =
      ∫ w in (-(j : ℝ))..(j : ℝ), Real.log |v - w| := by
    have h := intervalIntegral.integral_comp_neg (fun w => Real.log |v - w|)
      (a := -(j : ℝ)) (b := (j : ℝ))
    simp only [neg_neg] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun w _ => ?_
    rw [show -v - w = -(v + w) by ring, abs_neg, sub_neg_eq_add]
  rw [hsum, hint]

private noncomputable def rTermAII (k : ℕ) (t : ℝ) : ℝ :=
  let a := (k : ℝ) + 1 / 2
  let w := t + 1 / 16 - a ^ 2
  w / (w ^ 2 + a ^ 2 / 4)

private lemma hasDerivAt_rTermAII (k : ℕ) (t : ℝ) :
    HasDerivAt (rTermAII k)
      ((((k : ℝ) + 1 / 2) ^ 2 / 4 - (t + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2) /
        (((t + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2 + ((k : ℝ) + 1 / 2) ^ 2 / 4) ^ 2)) t := by
  have ha_pos : 0 < ((k : ℝ) + 1 / 2) ^ 2 / 4 := by positivity
  have hden_pos : 0 < (t + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2 + ((k : ℝ) + 1 / 2) ^ 2 / 4 := by
    positivity
  have hw : HasDerivAt (fun s : ℝ => s + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) 1 t := by
    simpa using (((hasDerivAt_id t).add_const (1 / 16 : ℝ)).sub_const (((k : ℝ) + 1 / 2) ^ 2))
  have hden : HasDerivAt
      (fun s : ℝ => (s + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2 + ((k : ℝ) + 1 / 2) ^ 2 / 4)
      (2 * (t + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2)) t :=
    ((hw.pow 2).add_const (((k : ℝ) + 1 / 2) ^ 2 / 4)).congr_deriv (by
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one])
  have hd := hw.div hden hden_pos.ne'
  refine hd.congr_deriv ?_
  ring

private lemma log_sum_term_deriv (k : ℕ) (v : ℝ) :
    HasDerivAt
      (fun x : ℝ =>
        Real.log (((x - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
          ((x + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)))
      (4 * v * rTermAII k (v ^ 2)) v := by
  set a : ℝ := (k : ℝ) + 1 / 2
  have hm_pos : ∀ x : ℝ, 0 < (x - a) ^ 2 + (1 / 4 : ℝ) ^ 2 := fun x => by positivity
  have hp_pos : ∀ x : ℝ, 0 < (x + a) ^ 2 + (1 / 4 : ℝ) ^ 2 := fun x => by positivity
  have h1 : HasDerivAt (fun x : ℝ => (x - a) ^ 2 + (1 / 4 : ℝ) ^ 2) (2 * (v - a)) v :=
    ((((hasDerivAt_id v).sub_const a).pow 2).add_const ((1 / 4 : ℝ) ^ 2)).congr_deriv (by
      simp [id_eq])
  have h2 : HasDerivAt (fun x : ℝ => (x + a) ^ 2 + (1 / 4 : ℝ) ^ 2) (2 * (v + a)) v :=
    ((((hasDerivAt_id v).add_const a).pow 2).add_const ((1 / 4 : ℝ) ^ 2)).congr_deriv (by
      simp [id_eq])
  have hprod : HasDerivAt
      (fun x : ℝ => ((x - a) ^ 2 + (1 / 4 : ℝ) ^ 2) * ((x + a) ^ 2 + (1 / 4 : ℝ) ^ 2))
      ((2 * (v - a)) * ((v + a) ^ 2 + (1 / 4 : ℝ) ^ 2) +
        ((v - a) ^ 2 + (1 / 4 : ℝ) ^ 2) * (2 * (v + a))) v := h1.mul h2
  have hp_prod : 0 < ((v - a) ^ 2 + (1 / 4 : ℝ) ^ 2) * ((v + a) ^ 2 + (1 / 4 : ℝ) ^ 2) :=
    mul_pos (hm_pos v) (hp_pos v)
  have hlog := hprod.log hp_prod.ne'
  refine (hlog.congr_of_eventuallyEq (Eventually.of_forall fun x => ?_)).congr_deriv ?_
  · show Real.log (((x - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
        ((x + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)) =
      Real.log (((x - a) ^ 2 + (1 / 4 : ℝ) ^ 2) * ((x + a) ^ 2 + (1 / 4 : ℝ) ^ 2))
    dsimp [a]; congr 2 <;> ring
  · unfold rTermAII
    dsimp [a]
    have hden1 : ((v - (k + 1 / 2)) ^ 2 + (1 / 4 : ℝ) ^ 2) * ((v + (k + 1 / 2)) ^ 2 + (1 / 4 : ℝ) ^ 2) ≠ 0 := by
      positivity
    have hden2 : (v ^ 2 + 1 / 16 - (k + 1 / 2) ^ 2) ^ 2 + (k + 1 / 2) ^ 2 / 4 ≠ 0 := by
      positivity
    field_simp [hden1, hden2]
    ring

private lemma hasDerivAt_hAII {j : ℕ} (hj : 1 ≤ j) {v : ℝ} (hv : |v| < (j : ℝ)) :
    HasDerivAt (hAII j)
      (4 * v * (∑ k ∈ Finset.range j, rTermAII k (v ^ 2)) -
        2 * Real.log (((j : ℝ) + v) / ((j : ℝ) - v))) v := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hp : 0 < (j : ℝ) + v := by linarith [(abs_lt.mp hv).1]
  have hm : 0 < (j : ℝ) - v := by linarith [(abs_lt.mp hv).2]
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ k ∈ Finset.range j,
        Real.log (((x - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
          ((x + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)))
      (∑ k ∈ Finset.range j, 4 * v * rTermAII k (v ^ 2)) v :=
    HasDerivAt.fun_sum fun k _ => log_sum_term_deriv k v
  have hL1 : HasDerivAt (fun x : ℝ => ((j : ℝ) + x) * Real.log ((j : ℝ) + x))
      (Real.log ((j : ℝ) + v) + 1) v := by
    have hlin : HasDerivAt (fun x : ℝ => (j : ℝ) + x) 1 v := (hasDerivAt_id v).const_add _
    have hlog := hlin.log hp.ne'
    have hm1 := hlin.mul hlog
    refine hm1.congr_deriv ?_
    field_simp [hp.ne']
  have hL2 : HasDerivAt (fun x : ℝ => ((j : ℝ) - x) * Real.log ((j : ℝ) - x))
      (-Real.log ((j : ℝ) - v) - 1) v := by
    have hlin : HasDerivAt (fun x : ℝ => (j : ℝ) - x) (-1) v := (hasDerivAt_id v).const_sub _
    have hlog := hlin.log hm.ne'
    have hm2 := hlin.mul hlog
    refine hm2.congr_deriv ?_
    field_simp [hm.ne']
    ring
  have hL3 : HasDerivAt (fun x : ℝ =>
      2 * (((j : ℝ) + x) * Real.log ((j : ℝ) + x) + ((j : ℝ) - x) * Real.log ((j : ℝ) - x) -
        2 * (j : ℝ)))
      (2 * Real.log (((j : ℝ) + v) / ((j : ℝ) - v))) v := by
    have h1 := ((hL1.add hL2).sub_const (2 * (j : ℝ))).const_mul 2
    refine h1.congr_deriv ?_
    rw [Real.log_div hp.ne' hm.ne']
    ring
  have hev : hAII j =ᶠ[𝓝 v] hAIIClosed j := by
    have ho : IsOpen {x : ℝ | |x| < (j : ℝ)} := isOpen_lt continuous_abs continuous_const
    filter_upwards [ho.mem_nhds hv] with x hx
    exact hAII_eq_closed hj hx
  exact ((hsum.sub hL3).congr_of_eventuallyEq hev).congr_deriv (by
    change (∑ k ∈ Finset.range j, 4 * v * rTermAII k (v ^ 2)) -
      2 * Real.log (((j : ℝ) + v) / ((j : ℝ) - v)) = _
    rw [← Finset.mul_sum])

private lemma two_mul_div_le_log_div {j : ℕ} (hj : 1 ≤ j) {v : ℝ} (hv0 : 0 ≤ v) (hvj : v < (j : ℝ)) :
    2 * v / (j : ℝ) ≤ Real.log (((j : ℝ) + v) / ((j : ℝ) - v)) := by
  have hj_pos : (0 : ℝ) < j := by exact_mod_cast hj
  let g : ℝ → ℝ := fun x => Real.log (((j : ℝ) + x) / ((j : ℝ) - x)) - 2 * x / (j : ℝ)
  have hcont : ContinuousOn g (Icc 0 v) := by
    refine (ContinuousOn.log ?_ fun x hx => ?_).sub
      (ContinuousOn.div_const (continuousOn_const.mul continuousOn_id) _)
    · refine ContinuousOn.div (continuousOn_const.add continuousOn_id)
        (continuousOn_const.sub continuousOn_id) fun x hx => ?_
      linarith [hx.2]
    · have hx1 : 0 < (j : ℝ) + x := by linarith [hx.1]
      have hx2 : 0 < (j : ℝ) - x := by linarith [hx.2]
      exact (div_pos hx1 hx2).ne'
  have hderiv_g : ∀ x ∈ Ioo 0 v,
      HasDerivAt g (2 * x ^ 2 / ((j : ℝ) * ((j : ℝ) ^ 2 - x ^ 2))) x := by
    intro x hx
    have hx1 : 0 < (j : ℝ) + x := by linarith [hx.1]
    have hx2 : 0 < (j : ℝ) - x := by linarith [hx.2]
    have h1 : HasDerivAt (fun t => Real.log (((j : ℝ) + t) / ((j : ℝ) - t)))
        (2 * (j : ℝ) / ((j : ℝ) ^ 2 - x ^ 2)) x := by
      have hlin1 : HasDerivAt (fun t => (j : ℝ) + t) 1 x := (hasDerivAt_id x).const_add _
      have hlin2 : HasDerivAt (fun t => (j : ℝ) - t) (-1) x := (hasDerivAt_id x).const_sub _
      have hd := (hlin1.div hlin2 hx2.ne').log (div_pos hx1 hx2).ne'
      refine hd.congr_deriv ?_
      have hden : (j : ℝ) ^ 2 - x ^ 2 ≠ 0 := by nlinarith
      change (1 * ((j : ℝ) - x) - ((j : ℝ) + x) * -1) / ((j : ℝ) - x) ^ 2 / (((j : ℝ) + x) / ((j : ℝ) - x)) =
        2 * (j : ℝ) / ((j : ℝ) ^ 2 - x ^ 2)
      field_simp [hx1.ne', hx2.ne', hden]
      ring
    have h2 : HasDerivAt (fun t => 2 * t / (j : ℝ)) (2 / (j : ℝ)) x := by
      simpa using ((hasDerivAt_id x).const_mul 2).div_const (j : ℝ)
    refine (h1.sub h2).congr_deriv ?_
    have hden : (j : ℝ) ^ 2 - x ^ 2 ≠ 0 := by nlinarith [hx.1, hx.2]
    field_simp [hj_pos.ne', hden]
    ring
  have hm := monotoneOn_of_deriv_nonneg (convex_Icc 0 v) hcont
    (fun x hx => (hderiv_g x (by simpa [interior_Icc] using hx)).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      have hx' : x ∈ Ioo 0 v := by simpa [interior_Icc] using hx
      rw [(hderiv_g x hx').deriv]
      have hden : 0 < (j : ℝ) ^ 2 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      positivity)
  have h0 := hm (left_mem_Icc.mpr hv0) (right_mem_Icc.mpr hv0) hv0
  dsimp [g] at h0
  simp only [add_zero, sub_zero, div_self hj_pos.ne', Real.log_one, mul_zero, zero_div] at h0
  linarith

private lemma rTermAII_sum_lt {j : ℕ} (hj : j = 1 ∨ j = 4) {t : ℝ} (ht1 : t ≤ 1 / 4) :
    ∑ k ∈ Finset.range j, rTermAII k t < 1 / (j : ℝ) := by
  rcases le_or_gt t (3 / 16) with ht_lo | ht_hi
  · have hr_nonpos : ∀ k : ℕ, rTermAII k t ≤ 0 := by
      intro k
      unfold rTermAII
      apply div_nonpos_of_nonpos_of_nonneg
      · have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      · positivity
    have hsum_le : ∑ k ∈ Finset.range j, rTermAII k t ≤ 0 :=
      Finset.sum_nonpos fun k _ => hr_nonpos k
    have hj_pos : (0 : ℝ) < j := by rcases hj with rfl | rfl <;> norm_num
    exact hsum_le.trans_lt (div_pos one_pos hj_pos)
  · have hr0_deriv : ∀ s ∈ Icc (3 / 16 : ℝ) (1 / 4),
        (13 : ℝ) < ((((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4 -
          (s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2) /
          (((s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2 +
            (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4) ^ 2) := by
      intro s hs
      have hw0 : 0 ≤ s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 := by
        simp only [Nat.cast_zero, zero_add]; linarith [hs.1]
      have hw1 : s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 ≤ 1 / 16 := by
        simp only [Nat.cast_zero, zero_add]; linarith [hs.2]
      have hnum : (15 / 256 : ℝ) ≤ (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4 -
          (s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2 := by
        simp only [Nat.cast_zero, zero_add]; nlinarith
      have hden_pos : 0 < (((s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2 +
          (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4) ^ 2) := by positivity
      have hden_le : (((s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2 +
          (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4) ^ 2) ≤ (17 / 256 : ℝ) ^ 2 := by
        have h1 : (s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2 +
            (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4 ≤ 17 / 256 := by
          simp only [Nat.cast_zero, zero_add]; norm_num at hw0 hw1 ⊢; nlinarith
        nlinarith
      have hdiv : (15 / 256 : ℝ) / (17 / 256 : ℝ) ^ 2 ≤
          ((((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4 - (s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2) /
          (((s + 1 / 16 - (((0 : ℕ) : ℝ) + 1 / 2) ^ 2) ^ 2 +
            (((0 : ℕ) : ℝ) + 1 / 2) ^ 2 / 4) ^ 2) :=
        div_le_div₀ (by linarith) hnum hden_pos hden_le
      linarith [show (13 : ℝ) < (15 / 256 : ℝ) / (17 / 256 : ℝ) ^ 2 by norm_num]
    have hrk_deriv : ∀ k : ℕ, 1 ≤ k → ∀ s ∈ Icc (3 / 16 : ℝ) (1 / 4),
        -(1 : ℝ) < ((((k : ℝ) + 1 / 2) ^ 2 / 4 - (s + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2) /
          (((s + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2 + ((k : ℝ) + 1 / 2) ^ 2 / 4) ^ 2)) := by
      intro k hk s hs
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      set a := (k : ℝ) + 1 / 2
      set w := s + 1 / 16 - a ^ 2
      have hw_le : w ≤ -(31 / 16) := by
        dsimp [w, a]; nlinarith [hs.2]
      have hw2 : (31 / 16 : ℝ) ^ 2 ≤ w ^ 2 := by nlinarith
      have hden_pos : 0 < (w ^ 2 + a ^ 2 / 4) ^ 2 := by positivity
      have ha_nn : 0 ≤ a ^ 2 / 4 := by positivity
      have h1 : -(w ^ 2 + a ^ 2 / 4) ≤ a ^ 2 / 4 - w ^ 2 := by linarith
      have h2 : -(1 : ℝ) / (w ^ 2 + a ^ 2 / 4) ≤ (a ^ 2 / 4 - w ^ 2) / (w ^ 2 + a ^ 2 / 4) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) hden_pos]
        nlinarith [show (0 : ℝ) < w ^ 2 + a ^ 2 / 4 by positivity]
      have h3 : -(1 : ℝ) < -(1 : ℝ) / (w ^ 2 + a ^ 2 / 4) := by
        rw [neg_div, neg_lt_neg_iff, div_lt_one (by positivity)]
        linarith
      exact h3.trans_le h2
    have hsum_deriv : ∀ s : ℝ, HasDerivAt (fun x => ∑ k ∈ Finset.range j, rTermAII k x)
        (∑ k ∈ Finset.range j,
          (((k : ℝ) + 1 / 2) ^ 2 / 4 - (s + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2) /
            (((s + 1 / 16 - ((k : ℝ) + 1 / 2) ^ 2) ^ 2 + ((k : ℝ) + 1 / 2) ^ 2 / 4) ^ 2)) s :=
      fun s => HasDerivAt.fun_sum fun k _ => hasDerivAt_rTermAII k s
    have hsum_mono : MonotoneOn (fun s => ∑ k ∈ Finset.range j, rTermAII k s) (Icc (3 / 16 : ℝ) (1 / 4)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _)
        (continuous_iff_continuousAt.mpr fun s => (hsum_deriv s).continuousAt).continuousOn
        (fun s _ => (hsum_deriv s).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          rw [interior_Icc] at hs
          rw [(hsum_deriv s).deriv]
          have hs' : s ∈ Icc (3 / 16 : ℝ) (1 / 4) := ⟨hs.1.le, hs.2.le⟩
          rcases hj with rfl | rfl
          · simp only [Finset.sum_range_one]
            exact le_trans (by norm_num) (hr0_deriv s hs').le
          · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
            have h0 := hr0_deriv s hs'
            have h1 := hrk_deriv 1 (by norm_num) s hs'
            have h2 := hrk_deriv 2 (by norm_num) s hs'
            have h3 := hrk_deriv 3 (by norm_num) s hs'
            linarith)
    have h_le_at_quarter := hsum_mono ⟨ht_hi.le, ht1⟩ ⟨by norm_num, le_rfl⟩ ht1
    refine h_le_at_quarter.trans_lt ?_
    rcases hj with rfl | rfl
    · simp only [Finset.sum_range_one, Nat.cast_one]
      unfold rTermAII
      norm_num
    · simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, Nat.cast_ofNat]
      unfold rTermAII
      norm_num

/-- **Lemma `A_II`, minimum at $v = \pm\frac12$** (`remainder.tex`, `rem:analyticII`):
for $j = 1$ and $j = 4$, $h_j$ attains its minimum on $[-\frac12, \frac12]$ at $v = \pm\frac12$. -/
theorem hAII_min_at_half {j : ℕ} (hj : j = 1 ∨ j = 4) {v : ℝ} (hv : |v| ≤ 1 / 2) :
    hAII j (1 / 2) ≤ hAII j v ∧ hAII j (-(1 / 2)) ≤ hAII j v := by
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have h_anti : AntitoneOn (hAII j) (Icc (0 : ℝ) (1 / 2)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 (1 / 2)) ?_ ?_ ?_
    · intro x hx
      have hx_lt : |x| < (j : ℝ) := by
        rw [abs_of_nonneg hx.1]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        linarith [hx.2]
      exact (hasDerivAt_hAII hj1 hx_lt).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_lt : |x| < (j : ℝ) := by
        rw [abs_of_nonneg hx.1.le]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        linarith [hx.2]
      exact (hasDerivAt_hAII hj1 hx_lt).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx_lt : |x| < (j : ℝ) := by
        rw [abs_of_nonneg hx.1.le]
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        linarith [hx.2]
      rw [(hasDerivAt_hAII hj1 hx_lt).deriv]
      have hxj : x < (j : ℝ) := by
        have : (1 : ℝ) ≤ j := by exact_mod_cast hj1
        linarith [hx.2]
      have hlog := two_mul_div_le_log_div hj1 hx.1.le hxj
      have hx_sq : x ^ 2 ≤ 1 / 4 := by nlinarith [hx.1, hx.2]
      have hsum := rTermAII_sum_lt hj (t := x ^ 2) hx_sq
      have hmul : 4 * x * (∑ k ∈ Finset.range j, rTermAII k (x ^ 2)) ≤ 4 * x * (1 / (j : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum.le (by linarith [hx.1])
      have h4 : 4 * x * (1 / (j : ℝ)) = 2 * (2 * x / (j : ℝ)) := by ring
      linarith
  have h_abs : hAII j (1 / 2) ≤ hAII j |v| :=
    h_anti ⟨abs_nonneg v, hv⟩ ⟨by norm_num, le_rfl⟩ hv
  have h_eq : hAII j |v| = hAII j v := by
    rcases le_or_gt 0 v with hv0 | hv0
    · rw [abs_of_nonneg hv0]
    · rw [abs_of_neg hv0, hAII_neg]
  rw [h_eq] at h_abs
  refine ⟨h_abs, ?_⟩
  rw [hAII_neg]
  exact h_abs

/-- The eight-neighbour hole floor $\mu_4 = \frac14 e^{h_4(1/2)}$ (`remainder.tex`, `rem:analyticII`). -/
noncomputable def muFour : ℝ := (1 / 4 : ℝ) * Real.exp (hAII 4 (1 / 2))

/-- **Lemma `A_II`, exact closed form (A-II.1)** (`remainder.tex`, `rem:analyticII`):
$\mu_4 = \frac{e^{16}}{4} \frac{\prod_{i=-3}^4 (i^2 + \frac1{16})}{(9/2)^9 (7/2)^7}$. -/
theorem muFour_eq_closed :
    muFour = (Real.exp 16 / 4) *
      (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) /
      ((9 / 2 : ℝ) ^ 9 * (7 / 2 : ℝ) ^ 7) := by
  unfold muFour
  rw [hAII_eq_closed (by norm_num) (by norm_num)]
  unfold hAIIClosed
  have hsum_eq :
      ∑ k ∈ Finset.range 4,
        Real.log (((1 / 2 - (k : ℝ) - 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2) *
          ((1 / 2 + (k : ℝ) + 1 / 2) ^ 2 + (1 / 4 : ℝ) ^ 2)) =
      ∑ i ∈ Finset.Icc (-3 : ℤ) 4, Real.log ((i : ℝ) ^ 2 + 1 / 16) := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    have hIcc : Finset.Icc (-3 : ℤ) 4 = {-3, -2, -1, 0, 1, 2, 3, 4} := by decide
    rw [hIcc]
    simp only [Finset.mem_insert, Finset.mem_singleton, Int.reduceNeg,
      Int.reduceEq, or_self, not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
    have hlog_mul : ∀ a b : ℝ, 0 < a → 0 < b → Real.log (a * b) = Real.log a + Real.log b :=
      fun a b ha hb => Real.log_mul ha.ne' hb.ne'
    rw [hlog_mul _ _ (by positivity) (by positivity),
      hlog_mul _ _ (by positivity) (by positivity),
      hlog_mul _ _ (by positivity) (by positivity),
      hlog_mul _ _ (by positivity) (by positivity)]
    push_cast
    norm_num
    ring
  have hprod_pos : ∀ i ∈ Finset.Icc (-3 : ℤ) 4, (i : ℝ) ^ 2 + 1 / 16 ≠ 0 := by
    intro i _; positivity
  rw [hsum_eq, ← Real.log_prod hprod_pos]
  have hexp_sub : Real.exp (Real.log (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) -
      2 * (((4 : ℝ) + 1 / 2) * Real.log ((4 : ℝ) + 1 / 2) +
        ((4 : ℝ) - 1 / 2) * Real.log ((4 : ℝ) - 1 / 2) - 2 * (4 : ℝ))) =
      (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) * Real.exp 16 /
        ((9 / 2 : ℝ) ^ 9 * (7 / 2 : ℝ) ^ 7) := by
    have hp1 : (0 : ℝ) < ∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16) :=
      Finset.prod_pos fun i _ => by positivity
    have hrew : Real.log (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) -
        2 * (((4 : ℝ) + 1 / 2) * Real.log ((4 : ℝ) + 1 / 2) +
          ((4 : ℝ) - 1 / 2) * Real.log ((4 : ℝ) - 1 / 2) - 2 * (4 : ℝ)) =
        Real.log (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) + 16 -
          (9 * Real.log (9 / 2) + 7 * Real.log (7 / 2)) := by
      ring
    rw [hrew, Real.exp_sub, Real.exp_add, Real.exp_log hp1, Real.exp_add,
      show (9 : ℝ) * Real.log (9 / 2) = Real.log ((9 / 2 : ℝ) ^ (9 : ℕ)) by
        rw [Real.log_pow]; norm_num,
      show (7 : ℝ) * Real.log (7 / 2) = Real.log ((7 / 2 : ℝ) ^ (7 : ℕ)) by
        rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity), Real.exp_log (by positivity)]
  push_cast
  rw [hexp_sub]
  ring

/-- **Lemma `A_II`, rational lower bound** (`remainder.tex`, `rem:analyticII`):
$\mu_4 > \frac{7}{10}$ (exact rational form of $\mu_4 > 0.700$), proved via
$e > \sum_{m=0}^7 \frac{1}{m!} = \frac{685}{252}$ and exact integer arithmetic. -/
theorem muFour_gt : (7 / 10 : ℝ) < muFour := by
  rw [muFour_eq_closed]
  have he_gt : (685 / 252 : ℝ) < Real.exp 1 := by
    have h9 := Real.sum_le_exp_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1) 9
    rw [Finset.sum_range_succ] at h9
    have hterm : (0 : ℝ) < (1 : ℝ) ^ 8 / ((8 : ℕ).factorial : ℝ) := by positivity
    have hval : ∑ m ∈ Finset.range 8, (1 : ℝ) ^ m / (m.factorial : ℝ) = 685 / 252 := by
      simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
      norm_num [Nat.factorial]
    linarith
  have he16 : ((685 / 252 : ℝ) ^ 16) < Real.exp 16 := by
    have hpow := pow_lt_pow_left₀ he_gt (by positivity) (by norm_num : 16 ≠ 0)
    rwa [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] at hpow
  have hprod_val :
      (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) /
        (4 * ((9 / 2 : ℝ) ^ 9 * (7 / 2 : ℝ) ^ 7)) =
      (6597717010625 / 83638991394577317888 : ℝ) := by
    have hIcc : Finset.Icc (-3 : ℤ) 4 = {-3, -2, -1, 0, 1, 2, 3, 4} := by decide
    rw [hIcc]
    simp only [Finset.mem_insert, Finset.mem_singleton, Int.reduceNeg,
      Int.reduceEq, or_self, not_false_eq_true, Finset.prod_insert, Finset.prod_singleton]
    norm_num
  have hrhs_eq :
      (Real.exp 16 / 4) * (∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) /
        ((9 / 2 : ℝ) ^ 9 * (7 / 2 : ℝ) ^ 7) =
      Real.exp 16 * ((∏ i ∈ Finset.Icc (-3 : ℤ) 4, ((i : ℝ) ^ 2 + 1 / 16)) /
        (4 * ((9 / 2 : ℝ) ^ 9 * (7 / 2 : ℝ) ^ 7))) := by ring
  rw [hrhs_eq, hprod_val]
  have hrat : (7 / 10 : ℝ) < (685 / 252 : ℝ) ^ 16 * (6597717010625 / 83638991394577317888 : ℝ) := by
    norm_num
  exact hrat.trans (mul_lt_mul_of_pos_right he16 (by norm_num))

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hAII_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hAII_neg

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.hAII_min_at_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.hAII_min_at_half

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.muFour_eq_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.muFour_eq_closed

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.muFour_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.muFour_gt

end FormalResearch.ModularBootstrap.Upper.Holes

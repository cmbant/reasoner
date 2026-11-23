module

public import FormalResearch.ModularBootstrap.Upper.Comb.Riesz
public import FormalResearch.ModularBootstrap.Upper.Comb.Tip
public import FormalResearch.ModularBootstrap.Upper.Comb.EdgePhase
public import Mathlib.Analysis.Convex.Deriv

/-!
# Peano Kernels, Log-Comb Calculus, and Infinite Product Expansion for K4--K6

Shared analytic infrastructure for Lemmas K4, K5, and K6 (`cmb:K4`--`cmb:K6` in
`CFT/modular_bootstrap/paper/comb_estimates.tex`):

* `midpoint_peano_eq`, `midpoint_peano_ge`, `midpoint_peano_le`, `midpoint_concave_telescope`:
  midpoint Peano kernel identity $\int_{k-1/2}^{k+1/2} g - g(k) = \int \frac12(\frac12 - |t-k|)^2 g''$
  and concave telescoping bound.
* `trapezoid_peano_eq`, `trapezoid_peano_le`, `trapezoid_nonpos_of_second_nonpos`:
  trapezoid Peano kernel identity $g(a) + g(a+1) - 2\int_a^{a+1} g = \int_a^{a+1} (t-a)(a+1-t) g''$.
* `chiDeriv_div_le`, `siteGap_ge_half_chiDeriv`, `chiDeriv_le_two_siteGap`, `chiDeriv_le_five_siteGap`:
  spacing comparisons for $\chi'_a$ and $\ell_k$ from Lemma K0(b).
* `phiVar`, `phiVarDeriv`, `phiVarSecond`: $\varphi(a) = f_x(\chi_a)$ and its first two
  derivatives, together with sign and upper/lower curvature bounds.
* `pairModQ`, `refComb_norm_log_eq_tsum`, `summable_phiVar`, `DK_limit`:
  convergent log-modulus series of $B^{(f)}(x)$ and continuum limit $D_K^{(f)}(x)$.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Real BigOperators

namespace FormalResearch.ModularBootstrap.Upper.Holes

open FormalResearch.ModularBootstrap.Upper.Comb

/-! ### Section 1: Midpoint and Trapezoid Peano Kernels -/

/-- Midpoint Peano kernel identity: for $C^2$ functions $g$ on $[k - 1/2, k + 1/2]$,
$\int_{k-1/2}^{k+1/2} g(t)\,dt - g(k) = \int_{k-1/2}^{k+1/2} \frac12(\frac12 - |t - k|)^2 g''(t)\,dt$. -/
theorem midpoint_peano_eq {g g' g'' : ℝ → ℝ} {k : ℝ}
    (hg : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g' (g'' t) t)
    (hg'' : ContinuousOn g'' (Icc (k - 1 / 2) (k + 1 / 2))) :
    (∫ t in (k - 1 / 2)..(k + 1 / 2), g t) - g k =
      ∫ t in (k - 1 / 2)..(k + 1 / 2), ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * g'' t := by
  have hg_cont : ContinuousOn g (Icc (k - 1 / 2) (k + 1 / 2)) := fun t ht =>
    (hg t ht).continuousAt.continuousWithinAt
  have hint_g1 : IntervalIntegrable g volume (k - 1 / 2) k :=
    (hg_cont.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hint_g2 : IntervalIntegrable g volume k (k + 1 / 2) :=
    (hg_cont.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hk_cont : Continuous (fun t : ℝ => (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) :=
    continuous_const.mul ((continuous_const.sub (continuous_abs.comp (continuous_id.sub continuous_const))).pow 2)
  have hint_k : ContinuousOn (fun t : ℝ => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * g'' t)
      (Icc (k - 1 / 2) (k + 1 / 2)) := hk_cont.continuousOn.mul hg''
  have hint_k1 : IntervalIntegrable (fun t : ℝ => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * g'' t)
      volume (k - 1 / 2) k :=
    (hint_k.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hint_k2 : IntervalIntegrable (fun t : ℝ => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * g'' t)
      volume k (k + 1 / 2) :=
    (hint_k.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
  let FL : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (t - (k - 1 / 2)) ^ 2 * g' t - (t - (k - 1 / 2)) * g t
  have hFL_deriv : ∀ t ∈ Icc (k - 1 / 2) k,
      HasDerivAt FL ((1 / 2 : ℝ) * (t - (k - 1 / 2)) ^ 2 * g'' t - g t) t := by
    intro t ht
    have ht' : t ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨ht.1, by linarith [ht.2]⟩
    have hlin : HasDerivAt (fun s => s - (k - 1 / 2)) 1 t := (hasDerivAt_id t).sub_const _
    have hsq : HasDerivAt (fun s => (1 / 2 : ℝ) * (s - (k - 1 / 2)) ^ 2) (t - (k - 1 / 2)) t := by
      have h := ((hlin.pow 2).const_mul (1 / 2 : ℝ))
      refine h.congr_deriv ?_; simp
    have h1 := hsq.mul (hg' t ht')
    have h2 := hlin.mul (hg t ht')
    exact (h1.sub h2).congr_deriv (by ring)
  have hL_eq : ∫ t in (k - 1 / 2)..k, ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 * g'' t - g t) =
      FL k - FL (k - 1 / 2) := by
    have hcongr : ∫ t in (k - 1 / 2)..k, ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 * g'' t - g t) =
        ∫ t in (k - 1 / 2)..k, ((1 / 2 : ℝ) * (t - (k - 1 / 2)) ^ 2 * g'' t - g t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith : k - 1 / 2 ≤ k)] at ht
      have habs : |t - k| = k - t := by rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)]
      rw [habs]; ring_nf
    rw [hcongr]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hFL_deriv t (by simpa [Set.uIcc_of_le (by linarith : k - 1 / 2 ≤ k)] using ht))
      (by
        have hc : ContinuousOn (fun t => (1 / 2 : ℝ) * (t - (k - 1 / 2)) ^ 2 * g'' t - g t)
            (Icc (k - 1 / 2) k) :=
          ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).continuousOn.mul
            (hg''.mono (Icc_subset_Icc_right (by linarith)))).sub
            (hg_cont.mono (Icc_subset_Icc_right (by linarith)))
        exact hc.intervalIntegrable_of_Icc (by linarith))
  let FR : ℝ → ℝ := fun t => (1 / 2 : ℝ) * (k + 1 / 2 - t) ^ 2 * g' t + (k + 1 / 2 - t) * g t
  have hFR_deriv : ∀ t ∈ Icc k (k + 1 / 2),
      HasDerivAt FR ((1 / 2 : ℝ) * (k + 1 / 2 - t) ^ 2 * g'' t - g t) t := by
    intro t ht
    have ht' : t ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [ht.1], ht.2⟩
    have hlin : HasDerivAt (fun s => k + 1 / 2 - s) (-1) t := (hasDerivAt_id t).const_sub _
    have hsq : HasDerivAt (fun s => (1 / 2 : ℝ) * (k + 1 / 2 - s) ^ 2) (-(k + 1 / 2 - t)) t := by
      have h := ((hlin.pow 2).const_mul (1 / 2 : ℝ))
      refine h.congr_deriv ?_; simp
    have h1 := hsq.mul (hg' t ht')
    have h2 := hlin.mul (hg t ht')
    exact (h1.add h2).congr_deriv (by ring)
  have hR_eq : ∫ t in k..(k + 1 / 2), ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 * g'' t - g t) =
      FR (k + 1 / 2) - FR k := by
    have hcongr : ∫ t in k..(k + 1 / 2), ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 * g'' t - g t) =
        ∫ t in k..(k + 1 / 2), ((1 / 2 : ℝ) * (k + 1 / 2 - t) ^ 2 * g'' t - g t) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith : k ≤ k + 1 / 2)] at ht
      have habs : |t - k| = t - k := abs_of_nonneg (sub_nonneg.mpr ht.1)
      rw [habs]; ring_nf
    rw [hcongr]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hFR_deriv t (by simpa [Set.uIcc_of_le (by linarith : k ≤ k + 1 / 2)] using ht))
      (by
        have hc : ContinuousOn (fun t => (1 / 2 : ℝ) * (k + 1 / 2 - t) ^ 2 * g'' t - g t)
            (Icc k (k + 1 / 2)) :=
          ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).continuousOn.mul
            (hg''.mono (Icc_subset_Icc_left (by linarith)))).sub
            (hg_cont.mono (Icc_subset_Icc_left (by linarith)))
        exact hc.intervalIntegrable_of_Icc (by linarith))
  have h_sum_split := intervalIntegral.integral_add_adjacent_intervals
    (hint_k1.sub hint_g1) (hint_k2.sub hint_g2)
  have h_diff : ∫ t in (k - 1 / 2)..(k + 1 / 2),
      ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 * g'' t - g t) = -g k := by
    rw [← h_sum_split, hL_eq, hR_eq]
    dsimp [FL, FR]
    ring
  rw [intervalIntegral.integral_sub (hint_k1.trans hint_k2) (hint_g1.trans hint_g2)] at h_diff
  linarith

private lemma midpoint_peano_kernel_integral (k : ℝ) :
    ∫ t in (k - 1 / 2)..(k + 1 / 2), (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 = 1 / 24 := by
  have hc : Continuous (fun t : ℝ => (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) :=
    continuous_const.mul ((continuous_const.sub (continuous_abs.comp (continuous_id.sub continuous_const))).pow 2)
  have h1 : ∫ t in (k - 1 / 2)..k, (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 = 1 / 48 := by
    have hcongr : ∫ t in (k - 1 / 2)..k, (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 =
        ∫ t in (k - 1 / 2)..k, (1 / 2 : ℝ) * (t - (k - 1 / 2)) ^ 2 := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith : k - 1 / 2 ≤ k)] at ht
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr ht.2)]; ring_nf
    rw [hcongr]
    have hd : ∀ t ∈ uIcc (k - 1 / 2) k,
        HasDerivAt (fun s => (1 / 6 : ℝ) * (s - (k - 1 / 2)) ^ 3) ((1 / 2 : ℝ) * (t - (k - 1 / 2)) ^ 2) t := by
      intro t _
      have h := (((hasDerivAt_id t).sub_const (k - 1 / 2)).pow 3).const_mul (1 / 6 : ℝ)
      refine h.congr_deriv ?_; simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).intervalIntegrable _ _)]
    norm_num
  have h2 : ∫ t in k..(k + 1 / 2), (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 = 1 / 48 := by
    have hcongr : ∫ t in k..(k + 1 / 2), (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2 =
        ∫ t in k..(k + 1 / 2), (1 / 2 : ℝ) * (k + 1 / 2 - t) ^ 2 := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le (by linarith : k ≤ k + 1 / 2)] at ht
      rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]; ring_nf
    rw [hcongr]
    have hd : ∀ t ∈ uIcc k (k + 1 / 2),
        HasDerivAt (fun s => -(1 / 6 : ℝ) * (k + 1 / 2 - s) ^ 3) ((1 / 2 : ℝ) * (k + 1 / 2 - t) ^ 2) t := by
      intro t _
      have h := (((hasDerivAt_id t).const_sub (k + 1 / 2)).pow 3).const_mul (-(1 / 6 : ℝ))
      refine h.congr_deriv ?_; simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).intervalIntegrable _ _)]
    norm_num
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (k - 1 / 2) k) (hc.intervalIntegrable k (k + 1 / 2)), h1, h2]
  norm_num

/-- Midpoint Peano lower bound: $g(k) - \int_{k-1/2}^{k+1/2} g \ge -\frac{1}{24} M$
whenever $g''(t) \le M$ on $[k - 1/2, k + 1/2]$. -/
theorem midpoint_peano_ge {g g' g'' : ℝ → ℝ} {k M : ℝ}
    (hg : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g' (g'' t) t)
    (hg'' : ContinuousOn g'' (Icc (k - 1 / 2) (k + 1 / 2)))
    (hM : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), g'' t ≤ M) :
    -(1 / 24 : ℝ) * M ≤ g k - ∫ t in (k - 1 / 2)..(k + 1 / 2), g t := by
  have heq := midpoint_peano_eq hg hg' hg''
  have hk_cont : Continuous (fun t : ℝ => (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) :=
    continuous_const.mul ((continuous_const.sub (continuous_abs.comp (continuous_id.sub continuous_const))).pow 2)
  have hint1 : IntervalIntegrable (fun t => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * g'' t)
      volume (k - 1 / 2) (k + 1 / 2) :=
    (hk_cont.continuousOn.mul hg'').intervalIntegrable_of_Icc (by linarith)
  have hint2 : IntervalIntegrable (fun t => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * M)
      volume (k - 1 / 2) (k + 1 / 2) :=
    (hk_cont.mul continuous_const).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : k - 1 / 2 ≤ k + 1 / 2)
    hint1 hint2 fun t ht => mul_le_mul_of_nonneg_left (hM t ht) (by positivity)
  rw [intervalIntegral.integral_mul_const, midpoint_peano_kernel_integral] at hmono
  linarith

/-- Midpoint Peano upper bound: $g(k) - \int_{k-1/2}^{k+1/2} g \le \frac{1}{24} M$
whenever $-g''(t) \le M$ on $[k - 1/2, k + 1/2]$. -/
theorem midpoint_peano_le {g g' g'' : ℝ → ℝ} {k M : ℝ}
    (hg : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g' (g'' t) t)
    (hg'' : ContinuousOn g'' (Icc (k - 1 / 2) (k + 1 / 2)))
    (hM : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), -g'' t ≤ M) :
    g k - ∫ t in (k - 1 / 2)..(k + 1 / 2), g t ≤ (1 / 24 : ℝ) * M := by
  have heq := midpoint_peano_eq hg hg' hg''
  have hk_cont : Continuous (fun t : ℝ => (1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) :=
    continuous_const.mul ((continuous_const.sub (continuous_abs.comp (continuous_id.sub continuous_const))).pow 2)
  have hint1 : IntervalIntegrable (fun t => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * (-M))
      volume (k - 1 / 2) (k + 1 / 2) :=
    (hk_cont.mul continuous_const).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun t => ((1 / 2 : ℝ) * (1 / 2 - |t - k|) ^ 2) * g'' t)
      volume (k - 1 / 2) (k + 1 / 2) :=
    (hk_cont.continuousOn.mul hg'').intervalIntegrable_of_Icc (by linarith)
  have hmono := intervalIntegral.integral_mono_on (by linarith : k - 1 / 2 ≤ k + 1 / 2)
    hint1 hint2 fun t ht => mul_le_mul_of_nonneg_left (by linarith [hM t ht]) (by positivity)
  rw [intervalIntegral.integral_mul_const, midpoint_peano_kernel_integral] at hmono
  linarith

/-- Concave midpoint telescoping bound: if $g$ is $C^1$ with $g'$ antitone on $[k-1/2, k+1/2]$,
then $0 \le 2 g(k) - 2 \int_{k-1/2}^{k+1/2} g \le \frac14 (g'(k - 1/2) - g'(k + 1/2))$. -/
theorem midpoint_concave_telescope {g g' : ℝ → ℝ} {k : ℝ}
    (hg : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), HasDerivAt g (g' t) t)
    (hg'_anti : AntitoneOn g' (Icc (k - 1 / 2) (k + 1 / 2))) :
    0 ≤ 2 * g k - 2 * ∫ t in (k - 1 / 2)..(k + 1 / 2), g t ∧
      2 * g k - 2 * ∫ t in (k - 1 / 2)..(k + 1 / 2), g t ≤
        (1 / 4 : ℝ) * (g' (k - 1 / 2) - g' (k + 1 / 2)) := by
  have hg_cont : ContinuousOn g (Icc (k - 1 / 2) (k + 1 / 2)) := fun t ht =>
    (hg t ht).continuousAt.continuousWithinAt
  have h_upper : ∀ t ∈ Icc (k - 1 / 2) (k + 1 / 2), g t - g k ≤ (t - k) * g' k := by
    intro t ht
    rcases le_or_gt t k with htk | hkt
    · let h : ℝ → ℝ := fun s => g s - g k - (s - k) * g' k
      have hcont_h : ContinuousOn h (Icc t k) :=
        ((hg_cont.mono (Icc_subset_Icc ht.1 (by linarith : k ≤ k + 1 / 2))).sub
          (continuousOn_const (c := g k))).sub
          (((continuous_id.sub continuous_const).mul continuous_const).continuousOn)
      have hderiv_h : ∀ s ∈ Ioo t k, HasDerivAt h (g' s - g' k) s := fun s hs => by
        have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
        have hlin : HasDerivAt (fun u => (u - k) * g' k) (g' k) s := by
          simpa using ((hasDerivAt_id s).sub_const k).mul_const (g' k)
        exact ((hg s hs').sub_const (g k)).sub hlin
      have hm := monotoneOn_of_deriv_nonneg (convex_Icc t k) hcont_h
        (fun s hs => by
          rw [interior_Icc] at hs
          exact (hderiv_h s hs).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          rw [interior_Icc] at hs
          have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
          rw [(hderiv_h s hs).deriv]
          have hge := hg'_anti hs' ⟨by linarith, by linarith⟩ hs.2.le
          linarith)
      have h0 := hm (left_mem_Icc.mpr htk) (right_mem_Icc.mpr htk) htk
      dsimp [h] at h0; simp only [sub_self, zero_mul] at h0; linarith
    · let h : ℝ → ℝ := fun s => g s - g k - (s - k) * g' k
      have hcont_h : ContinuousOn h (Icc k t) :=
        ((hg_cont.mono (Icc_subset_Icc (by linarith : k - 1 / 2 ≤ k) ht.2)).sub
          (continuousOn_const (c := g k))).sub
          (((continuous_id.sub continuous_const).mul continuous_const).continuousOn)
      have hderiv_h : ∀ s ∈ Ioo k t, HasDerivAt h (g' s - g' k) s := fun s hs => by
        have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩
        have hlin : HasDerivAt (fun u => (u - k) * g' k) (g' k) s := by
          simpa using ((hasDerivAt_id s).sub_const k).mul_const (g' k)
        exact ((hg s hs').sub_const (g k)).sub hlin
      have hm := antitoneOn_of_deriv_nonpos (convex_Icc k t) hcont_h
        (fun s hs => by
          rw [interior_Icc] at hs
          exact (hderiv_h s hs).differentiableAt.differentiableWithinAt)
        (fun s hs => by
          rw [interior_Icc] at hs
          have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩
          rw [(hderiv_h s hs).deriv]
          have hle := hg'_anti ⟨by linarith, by linarith⟩ hs' hs.1.le
          linarith)
      have h0 := hm (left_mem_Icc.mpr hkt.le) (right_mem_Icc.mpr hkt.le) hkt.le
      dsimp [h] at h0; simp only [sub_self, zero_mul] at h0; linarith
  have hint_g : IntervalIntegrable g volume (k - 1 / 2) (k + 1 / 2) :=
    hg_cont.intervalIntegrable_of_Icc (by linarith)
  have hint_lin : IntervalIntegrable (fun t => g k + (t - k) * g' k) volume (k - 1 / 2) (k + 1 / 2) :=
    (continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable _ _
  have hmono_ub := intervalIntegral.integral_mono_on (by linarith : k - 1 / 2 ≤ k + 1 / 2)
    hint_g hint_lin fun t ht => by linarith [h_upper t ht]
  have hval_lin : ∫ t in (k - 1 / 2)..(k + 1 / 2), (g k + (t - k) * g' k) = g k := by
    have hd : ∀ t ∈ uIcc (k - 1 / 2) (k + 1 / 2),
        HasDerivAt (fun s => s * g k + ((s - k) ^ 2 / 2) * g' k) (g k + (t - k) * g' k) t := by
      intro t _
      have h1 : HasDerivAt (fun s => s * g k) (g k) t := by
        simpa using (hasDerivAt_id t).mul_const (g k)
      have h2 := ((((hasDerivAt_id t).sub_const k).pow 2).div_const 2).mul_const (g' k)
      exact (h1.add h2).congr_deriv (by simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_lin]
    ring
  rw [hval_lin] at hmono_ub
  refine ⟨by linarith, ?_⟩
  have h_L : ∀ t ∈ Icc (k - 1 / 2) k, (t - k) * g' (k - 1 / 2) ≤ g t - g k := by
    intro t ht
    let h : ℝ → ℝ := fun s => g s - g k - (s - k) * g' (k - 1 / 2)
    have hcont_h : ContinuousOn h (Icc t k) :=
      ((hg_cont.mono (Icc_subset_Icc ht.1 (by linarith : k ≤ k + 1 / 2))).sub
        (continuousOn_const (c := g k))).sub
        (((continuous_id.sub continuous_const).mul continuous_const).continuousOn)
    have hderiv_h : ∀ s ∈ Ioo t k, HasDerivAt h (g' s - g' (k - 1 / 2)) s := fun s hs => by
      have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
      have hlin : HasDerivAt (fun u => (u - k) * g' (k - 1 / 2)) (g' (k - 1 / 2)) s := by
        simpa using ((hasDerivAt_id s).sub_const k).mul_const (g' (k - 1 / 2))
      exact ((hg s hs').sub_const (g k)).sub hlin
    have hm := antitoneOn_of_deriv_nonpos (convex_Icc t k) hcont_h
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (hderiv_h s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [ht.1, hs.1], by linarith [hs.2]⟩
        rw [(hderiv_h s hs).deriv]
        have hle := hg'_anti ⟨le_rfl, by linarith⟩ hs' hs'.1
        linarith)
    have h0 := hm (left_mem_Icc.mpr ht.2) (right_mem_Icc.mpr ht.2) ht.2
    dsimp [h] at h0; simp only [sub_self, zero_mul] at h0; linarith
  have h_R : ∀ t ∈ Icc k (k + 1 / 2), (t - k) * g' (k + 1 / 2) ≤ g t - g k := by
    intro t ht
    let h : ℝ → ℝ := fun s => g s - g k - (s - k) * g' (k + 1 / 2)
    have hcont_h : ContinuousOn h (Icc k t) :=
      ((hg_cont.mono (Icc_subset_Icc (by linarith : k - 1 / 2 ≤ k) ht.2)).sub
        (continuousOn_const (c := g k))).sub
        (((continuous_id.sub continuous_const).mul continuous_const).continuousOn)
    have hderiv_h : ∀ s ∈ Ioo k t, HasDerivAt h (g' s - g' (k + 1 / 2)) s := fun s hs => by
      have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩
      have hlin : HasDerivAt (fun u => (u - k) * g' (k + 1 / 2)) (g' (k + 1 / 2)) s := by
        simpa using ((hasDerivAt_id s).sub_const k).mul_const (g' (k + 1 / 2))
      exact ((hg s hs').sub_const (g k)).sub hlin
    have hm := monotoneOn_of_deriv_nonneg (convex_Icc k t) hcont_h
      (fun s hs => by
        rw [interior_Icc] at hs
        exact (hderiv_h s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => by
        rw [interior_Icc] at hs
        have hs' : s ∈ Icc (k - 1 / 2) (k + 1 / 2) := ⟨by linarith [hs.1], by linarith [ht.2, hs.2]⟩
        rw [(hderiv_h s hs).deriv]
        have hge := hg'_anti hs' ⟨by linarith, le_rfl⟩ hs'.2
        linarith)
    have h0 := hm (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1) ht.1
    dsimp [h] at h0; simp only [sub_self, zero_mul] at h0; linarith
  have hint_gL : IntervalIntegrable g volume (k - 1 / 2) k :=
    (hg_cont.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hint_gR : IntervalIntegrable g volume k (k + 1 / 2) :=
    (hg_cont.mono (Icc_subset_Icc_left (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hint_lL : IntervalIntegrable (fun t => g k + (t - k) * g' (k - 1 / 2)) volume (k - 1 / 2) k :=
    (continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable _ _
  have hint_lR : IntervalIntegrable (fun t => g k + (t - k) * g' (k + 1 / 2)) volume k (k + 1 / 2) :=
    (continuous_const.add ((continuous_id.sub continuous_const).mul continuous_const)).intervalIntegrable _ _
  have hmL := intervalIntegral.integral_mono_on (by linarith : k - 1 / 2 ≤ k) hint_lL hint_gL
    fun t ht => by linarith [h_L t ht]
  have hmR := intervalIntegral.integral_mono_on (by linarith : k ≤ k + 1 / 2) hint_lR hint_gR
    fun t ht => by linarith [h_R t ht]
  have hvL : ∫ t in (k - 1 / 2)..k, (g k + (t - k) * g' (k - 1 / 2)) =
      (1 / 2 : ℝ) * g k - (1 / 8 : ℝ) * g' (k - 1 / 2) := by
    have hd : ∀ t ∈ uIcc (k - 1 / 2) k,
        HasDerivAt (fun s => s * g k + ((s - k) ^ 2 / 2) * g' (k - 1 / 2)) (g k + (t - k) * g' (k - 1 / 2)) t := by
      intro t _
      have h1 : HasDerivAt (fun s => s * g k) (g k) t := by
        simpa using (hasDerivAt_id t).mul_const (g k)
      have h2 := ((((hasDerivAt_id t).sub_const k).pow 2).div_const 2).mul_const (g' (k - 1 / 2))
      exact (h1.add h2).congr_deriv (by simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_lL]; ring
  have hvR : ∫ t in k..(k + 1 / 2), (g k + (t - k) * g' (k + 1 / 2)) =
      (1 / 2 : ℝ) * g k + (1 / 8 : ℝ) * g' (k + 1 / 2) := by
    have hd : ∀ t ∈ uIcc k (k + 1 / 2),
        HasDerivAt (fun s => s * g k + ((s - k) ^ 2 / 2) * g' (k + 1 / 2)) (g k + (t - k) * g' (k + 1 / 2)) t := by
      intro t _
      have h1 : HasDerivAt (fun s => s * g k) (g k) t := by
        simpa using (hasDerivAt_id t).mul_const (g k)
      have h2 := ((((hasDerivAt_id t).sub_const k).pow 2).div_const 2).mul_const (g' (k + 1 / 2))
      exact (h1.add h2).congr_deriv (by simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]; ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint_lR]; ring
  rw [hvL] at hmL; rw [hvR] at hmR
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_gL hint_gR]
  linarith

/-- Trapezoid Peano kernel identity: for $C^2$ functions $g$ on $[a, a + 1]$,
$g(a) + g(a + 1) - 2 \int_a^{a+1} g(t)\,dt = \int_a^{a+1} (t - a)(a + 1 - t) g''(t)\,dt$. -/
theorem trapezoid_peano_eq {g g' g'' : ℝ → ℝ} {a : ℝ}
    (hg : ∀ t ∈ Icc a (a + 1), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc a (a + 1), HasDerivAt g' (g'' t) t)
    (hg'' : ContinuousOn g'' (Icc a (a + 1))) :
    g a + g (a + 1) - 2 * ∫ t in a..(a + 1), g t =
      ∫ t in a..(a + 1), (t - a) * (a + 1 - t) * g'' t := by
  have hg_cont : ContinuousOn g (Icc a (a + 1)) := fun t ht =>
    (hg t ht).continuousAt.continuousWithinAt
  have hk_cont : Continuous (fun t : ℝ => (t - a) * (a + 1 - t)) :=
    (continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)
  have hint_g : IntervalIntegrable g volume a (a + 1) :=
    hg_cont.intervalIntegrable_of_Icc (by linarith)
  have hint_k : IntervalIntegrable (fun t => (t - a) * (a + 1 - t) * g'' t) volume a (a + 1) :=
    (hk_cont.continuousOn.mul hg'').intervalIntegrable_of_Icc (by linarith)
  let FT : ℝ → ℝ := fun t => (t - a) * (a + 1 - t) * g' t - (2 * a + 1 - 2 * t) * g t
  have hFT_deriv : ∀ t ∈ Icc a (a + 1),
      HasDerivAt FT ((t - a) * (a + 1 - t) * g'' t + 2 * g t) t := by
    intro t ht
    have h1 : HasDerivAt (fun s => (s - a) * (a + 1 - s)) (2 * a + 1 - 2 * t) t := by
      have hd := ((hasDerivAt_id t).sub_const a).mul ((hasDerivAt_id t).const_sub (a + 1))
      refine hd.congr_deriv ?_; simp; ring
    have h2 : HasDerivAt (fun s => 2 * a + 1 - 2 * s) (-2) t := by
      have hd := (hasDerivAt_const t (2 * a + 1)).sub ((hasDerivAt_id t).const_mul 2)
      refine hd.congr_deriv ?_; simp
    exact ((h1.mul (hg' t ht)).sub (h2.mul (hg t ht))).congr_deriv (by ring)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hFT_deriv t (by simpa [Set.uIcc_of_le (by linarith : a ≤ a + 1)] using ht))
    (hint_k.add (hint_g.const_mul 2))
  rw [intervalIntegral.integral_add hint_k (hint_g.const_mul 2),
    intervalIntegral.integral_const_mul] at hftc
  have h_end : FT (a + 1) - FT a = g a + g (a + 1) := by dsimp [FT]; ring
  linarith

private lemma trapezoid_peano_kernel_integral (a : ℝ) :
    ∫ t in a..(a + 1), (t - a) * (a + 1 - t) = 1 / 6 := by
  have hsub := intervalIntegral.integral_comp_sub_right (fun u : ℝ => u * (1 - u)) a
    (a := a) (b := a + 1)
  have heq : (fun t : ℝ => (t - a) * (a + 1 - t)) = fun t => (t - a) * (1 - (t - a)) := by
    ext t; ring
  rw [heq, hsub, sub_self, show a + 1 - a = 1 by ring]
  have hd : ∀ u ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s ^ 2 / 2 - s ^ 3 / 3) (u * (1 - u)) u := by
    intro u _
    have h1 := ((hasDerivAt_pow 2 u).div_const 2)
    have h2 := ((hasDerivAt_pow 3 u).div_const 3)
    exact (h1.sub h2).congr_deriv (by simp; ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.mul (continuous_const.sub continuous_id)).intervalIntegrable 0 1)]
  norm_num

/-- Trapezoid Peano upper bound: $g(a) + g(a+1) - 2\int_a^{a+1} g \le \frac16 M$
whenever $g''(t) \le M$ on $[a, a + 1]$. -/
theorem trapezoid_peano_le {g g' g'' : ℝ → ℝ} {a M : ℝ}
    (hg : ∀ t ∈ Icc a (a + 1), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc a (a + 1), HasDerivAt g' (g'' t) t)
    (hg'' : ContinuousOn g'' (Icc a (a + 1)))
    (hM : ∀ t ∈ Icc a (a + 1), g'' t ≤ M) :
    g a + g (a + 1) - 2 * ∫ t in a..(a + 1), g t ≤ (1 / 6 : ℝ) * M := by
  rw [trapezoid_peano_eq hg hg' hg'']
  have hk_cont : Continuous (fun t : ℝ => (t - a) * (a + 1 - t)) :=
    (continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id)
  have hint1 : IntervalIntegrable (fun t => (t - a) * (a + 1 - t) * g'' t) volume a (a + 1) :=
    (hk_cont.continuousOn.mul hg'').intervalIntegrable_of_Icc (by linarith)
  have hint2 : IntervalIntegrable (fun t => (t - a) * (a + 1 - t) * M) volume a (a + 1) :=
    (hk_cont.mul continuous_const).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : a ≤ a + 1) hint1 hint2 fun t ht =>
    mul_le_mul_of_nonneg_left (hM t ht) (mul_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr ht.2))
  rw [intervalIntegral.integral_mul_const, trapezoid_peano_kernel_integral] at hmono
  exact hmono

theorem trapezoid_nonpos_of_second_nonpos {g g' g'' : ℝ → ℝ} {a : ℝ}
    (hg : ∀ t ∈ Icc a (a + 1), HasDerivAt g (g' t) t)
    (hg' : ∀ t ∈ Icc a (a + 1), HasDerivAt g' (g'' t) t)
    (hg'' : ContinuousOn g'' (Icc a (a + 1)))
    (h0 : ∀ t ∈ Icc a (a + 1), g'' t ≤ 0) :
    g a + g (a + 1) - 2 * ∫ t in a..(a + 1), g t ≤ 0 := by
  simpa using trapezoid_peano_le hg hg' hg'' h0

/-! ### Section 2: `chiDeriv` spacing comparison from Lemma K0(b) -/

private lemma continuousAt_rhoUDeriv_of_gt {y : ℝ} (hy : xiStar < y) : ContinuousAt rhoUDeriv y := by
  have hpi := Real.pi_pos
  have hs : 1 < Real.sinh (π * y) := by
    rw [← sinh_pi_mul_xiStar]; exact Real.sinh_lt_sinh.mpr (by nlinarith)
  have hsq : 0 < Real.sinh (π * y) ^ 2 - 1 := by nlinarith
  have hsh : ContinuousAt (fun t : ℝ => Real.sinh (π * t)) y :=
    Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
  have hch : ContinuousAt (fun t : ℝ => Real.cosh (π * t)) y :=
    Real.continuous_cosh.continuousAt.comp (continuousAt_const.mul continuousAt_id)
  have hden : ContinuousAt (fun t : ℝ => √(Real.sinh (π * t) ^ 2 - 1)) y :=
    ((hsh.pow 2).sub continuousAt_const).sqrt
  exact continuousAt_const.mul (hch.div hden (Real.sqrt_ne_zero'.mpr hsq))

lemma chiDeriv_pos {c' a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) : 0 < chiDeriv c' a := by
  unfold chiDeriv
  exact div_pos two_pos (mul_pos hc' (rhoU_pos (xiStar_lt_chiQuantile hc' ha)))

lemma tendsto_chiQuantile_atTop {c' : ℝ} (hc' : 0 < c') :
    Tendsto (chiQuantile c') atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro M
  set M' := max M xiStar
  refine ⟨max 1 (c' * cumulN M' + 1 / 4), fun a ha => ?_⟩
  have ha14 : 1 / 4 ≤ a := by linarith [(le_max_left 1 _).trans ha]
  have hspec := chiQuantile_spec hc' ha14
  have hle_cum : cumulN M' ≤ cumulN (chiQuantile c' a) := by
    have hmul : c' * cumulN M' ≤ c' * cumulN (chiQuantile c' a) := by
      linarith [(le_max_right 1 _).trans ha, hspec.2]
    exact le_of_mul_le_mul_left hmul hc'
  exact (le_max_left M xiStar).trans
    ((cumulN_strictMonoOn.le_iff_le (le_max_right M xiStar) hspec.1).mp hle_cum)

/-- From K0(b) $|(\log \chi')'(t)| \le 1/(t - 1/4)$: for $1/4 < a \le b$,
$\chi'_a / \chi'_b \le (b - 1/4) / (a - 1/4)$. -/
theorem chiDeriv_div_le {c' a b : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a) (hab : a ≤ b) :
    chiDeriv c' a / chiDeriv c' b ≤ (b - 1 / 4) / (a - 1 / 4) := by
  have h_log_le : Real.log (chiDeriv c' a) - Real.log (chiDeriv c' b) ≤
      Real.log (b - 1 / 4) - Real.log (a - 1 / 4) := by
    have hcont_l : ContinuousOn (fun t => Real.log (chiDeriv c' t)) (Icc a b) := fun t ht =>
      ((hasDerivAt_chiQuantile hc' (lt_of_lt_of_le ha ht.1)).2.continuousAt.log
        (chiDeriv_pos hc' (lt_of_lt_of_le ha ht.1)).ne').continuousWithinAt
    have hderiv_l : ∀ t ∈ Icc a b,
        HasDerivAt (fun s => Real.log (chiDeriv c' s)) (chiSecond c' t / chiDeriv c' t) t := by
      intro t ht
      have ht14 := lt_of_lt_of_le ha ht.1
      exact (hasDerivAt_chiQuantile hc' ht14).2.log (chiDeriv_pos hc' ht14).ne'
    have hcont_d1 : ContinuousOn (fun t => -chiSecond c' t / chiDeriv c' t) (Icc a b) := by
      intro t ht
      have ht14 := lt_of_lt_of_le ha ht.1
      have hχ := xiStar_lt_chiQuantile hc' ht14
      have hχ_c : ContinuousAt (chiQuantile c') t := (hasDerivAt_chiQuantile hc' ht14).1.continuousAt
      have hcd_c : ContinuousAt (chiDeriv c') t := (hasDerivAt_chiQuantile hc' ht14).2.continuousAt
      have hρ_c : ContinuousAt (fun s => rhoU (chiQuantile c' s)) t :=
        (hasDerivAt_rhoU hχ).continuousAt.comp hχ_c
      have hρ'_c : ContinuousAt (fun s => rhoUDeriv (chiQuantile c' s)) t :=
        (continuousAt_rhoUDeriv_of_gt hχ).comp hχ_c
      have hsec_c : ContinuousAt (chiSecond c') t :=
        ((hcd_c.pow 2).neg).mul (hρ'_c.div hρ_c (rhoU_pos hχ).ne')
      exact (hsec_c.neg.div hcd_c (chiDeriv_pos hc' ht14).ne').continuousWithinAt
    have hftc1 : Real.log (chiDeriv c' b) - Real.log (chiDeriv c' a) =
        ∫ t in a..b, chiSecond c' t / chiDeriv c' t := by
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hderiv_l t (by simpa [Set.uIcc_of_le hab] using ht)) ?_).symm
      have hc'2 : ContinuousOn (fun t => chiSecond c' t / chiDeriv c' t) (Icc a b) :=
        hcont_d1.neg.congr fun t _ => by simp [Pi.neg_apply, neg_div]
      exact hc'2.intervalIntegrable_of_Icc hab
    have hftc2 : Real.log (b - 1 / 4) - Real.log (a - 1 / 4) =
        ∫ t in a..b, (1 / (t - 1 / 4) : ℝ) := by
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => Real.log (s - 1 / 4))
        (fun t ht => ?_) ?_).symm
      · rw [Set.uIcc_of_le hab] at ht
        have ht14 : 0 < t - 1 / 4 := by linarith [ht.1]
        simpa [one_div] using ((hasDerivAt_id t).sub_const (1 / 4 : ℝ)).log ht14.ne'
      · refine (continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => ?_).intervalIntegrable_of_Icc hab
        dsimp; linarith [ht.1]
    rw [← neg_sub (Real.log (chiDeriv c' b)) (Real.log (chiDeriv c' a)), hftc1,
      ← intervalIntegral.integral_neg, hftc2]
    refine intervalIntegral.integral_mono_on hab ?_ ?_ fun t ht => ?_
    · have hc'2 : ContinuousOn (fun t => -(chiSecond c' t / chiDeriv c' t)) (Icc a b) :=
        hcont_d1.congr fun t _ => by ring
      exact hc'2.intervalIntegrable_of_Icc hab
    · refine (continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => ?_).intervalIntegrable_of_Icc hab
      dsimp; linarith [ht.1]
    · have ht14 := lt_of_lt_of_le ha ht.1
      have hbd := abs_logDeriv_chiDeriv_le hc' ht14
      exact (neg_le_abs _).trans hbd
  have hca := chiDeriv_pos hc' ha
  have hcb := chiDeriv_pos hc' (ha.trans_le hab)
  rw [← Real.log_div hca.ne' hcb.ne', ← Real.log_div (by linarith) (by linarith)] at h_log_le
  exact (Real.log_le_log_iff (div_pos hca hcb) (div_pos (by linarith) (by linarith))).mp h_log_le

/-- On cell $[f, f + 1]$ for $f \ge 1$, $\ell_f \ge \frac{1}{2} \chi'_f$. -/
theorem siteGap_ge_half_chiDeriv {c' : ℝ} (hc' : 0 < c') {f : ℕ} (hf : 1 ≤ f) :
    (1 / 2 : ℝ) * chiDeriv c' f ≤ siteGap c' f := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hf14 : 1 / 4 < (f : ℝ) := by linarith
  have hcont_chi : ContinuousOn (chiDeriv c') (Icc (f : ℝ) ((f : ℝ) + 1)) := fun t ht =>
    (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
  have hgap_int : siteGap c' f = ∫ t in (f : ℝ)..((f : ℝ) + 1), chiDeriv c' t := by
    unfold siteGap
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_).symm
    · rw [Set.uIcc_of_le (by linarith : (f : ℝ) ≤ (f : ℝ) + 1)] at ht
      exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1
    · exact hcont_chi.intervalIntegrable_of_Icc (by linarith)
  have h_pt : ∀ t ∈ Icc (f : ℝ) ((f : ℝ) + 1),
      chiDeriv c' f * ((f : ℝ) - 1 / 4) / (t - 1 / 4) ≤ chiDeriv c' t := by
    intro t ht
    have hdiv := chiDeriv_div_le hc' hf14 ht.1
    have hct := chiDeriv_pos hc' (hf14.trans_le ht.1)
    have ht14 : 0 < t - 1 / 4 := by linarith [ht.1]
    have hf_pos : 0 < (f : ℝ) - 1 / 4 := by linarith
    rw [div_le_div_iff₀ hct hf_pos] at hdiv
    rw [div_le_iff₀ ht14]
    linarith
  have h_int_lb : ∫ t in (f : ℝ)..((f : ℝ) + 1), chiDeriv c' f * ((f : ℝ) - 1 / 4) / (t - 1 / 4) ≤
      siteGap c' f := by
    rw [hgap_int]
    refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ h_pt
    · refine (continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => ?_).intervalIntegrable_of_Icc (by linarith)
      dsimp; linarith [ht.1]
    · exact hcont_chi.intervalIntegrable_of_Icc (by linarith)
  have h_eval : ∫ t in (f : ℝ)..((f : ℝ) + 1), chiDeriv c' f * ((f : ℝ) - 1 / 4) / (t - 1 / 4) =
      chiDeriv c' f * ((f : ℝ) - 1 / 4) * Real.log (((f : ℝ) + 3 / 4) / ((f : ℝ) - 1 / 4)) := by
    have hd : ∀ t ∈ uIcc (f : ℝ) ((f : ℝ) + 1),
        HasDerivAt (fun s => chiDeriv c' f * ((f : ℝ) - 1 / 4) * Real.log (s - 1 / 4))
          (chiDeriv c' f * ((f : ℝ) - 1 / 4) / (t - 1 / 4)) t := by
      intro t ht
      rw [Set.uIcc_of_le (by linarith : (f : ℝ) ≤ (f : ℝ) + 1)] at ht
      have hlog := ((hasDerivAt_id t).sub_const (1 / 4 : ℝ)).log (by linarith [ht.1] : t - 1 / 4 ≠ 0)
      refine (hlog.const_mul (chiDeriv c' f * ((f : ℝ) - 1 / 4))).congr_deriv ?_
      simp; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
      ((continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => by
        dsimp; linarith [ht.1]).intervalIntegrable_of_Icc (by linarith))]
    rw [← mul_sub, ← Real.log_div (by linarith) (by linarith)]
    ring_nf
  rw [h_eval] at h_int_lb
  have h_log_ge : 1 / 2 ≤ ((f : ℝ) - 1 / 4) * Real.log (((f : ℝ) + 3 / 4) / ((f : ℝ) - 1 / 4)) := by
    have hlog_ge_step : 1 / ((f : ℝ) + 3 / 4) ≤ Real.log (((f : ℝ) + 3 / 4) / ((f : ℝ) - 1 / 4)) := by
      -- `1 - 1/x ≤ log x` for `x = (f + 3/4) / (f - 1/4) > 1`
      have hx_pos : 0 < ((f : ℝ) + 3 / 4) / ((f : ℝ) - 1 / 4) := by positivity
      have h1 := Real.one_sub_inv_le_log_of_pos hx_pos
      have hid : 1 - (((f : ℝ) + 3 / 4) / ((f : ℝ) - 1 / 4))⁻¹ = 1 / ((f : ℝ) + 3 / 4) := by
        field_simp [(by linarith : (f : ℝ) + 3 / 4 ≠ 0), (by linarith : (f : ℝ) - 1 / 4 ≠ 0)]
        ring
      linarith
    rcases eq_or_lt_of_le hf1 with hf_eq | hf_gt
    · rw [← hf_eq]
      -- At f = 1: (3/4) * log(7/3) ≥ (3/4) * (2*(2/5)) = 3/5 ≥ 1/2
      have h73 : (4 / 5 : ℝ) ≤ Real.log ((1 + 3 / 4 : ℝ) / (1 - 1 / 4)) := by
        have hpos : 0 < ((1 + 3 / 4 : ℝ) / (1 - 1 / 4)) := by norm_num
        have h_eq : ((1 + 3 / 4 : ℝ) / (1 - 1 / 4)) = 7 / 3 := by norm_num
        rw [h_eq]
        -- `log(7/3) ≥ 4/5` iff `exp(4/5) ≤ 7/3`; `exp(4/5) = (exp 4)^(1/5)`, use `(1 + x/4)^4` or `exp(1) < 2.72`
        have hexp : Real.exp (4 / 5 : ℝ) ≤ 7 / 3 := by
          have he : Real.exp 1 < 272 / 100 := by
            have := Real.exp_one_lt_d9; linarith
          have he4 : Real.exp 4 < (272 / 100 : ℝ) ^ 4 := by
            have h := pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num : 4 ≠ 0)
            rwa [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] at h
          have hpow5 : Real.exp (4 / 5 : ℝ) ^ 5 = Real.exp 4 := by
            rw [← Real.exp_nat_mul]; norm_num
          have hrat : (272 / 100 : ℝ) ^ 4 ≤ (7 / 3 : ℝ) ^ 5 := by norm_num
          by_contra hlt
          push Not at hlt
          have h5 := pow_le_pow_left₀ (by norm_num) hlt.le 5
          linarith
        have hlog := Real.log_le_log (Real.exp_pos _) hexp
        rwa [Real.log_exp] at hlog
      nlinarith
    · have hf2 : (2 : ℝ) ≤ f := by
        have h2 : 2 ≤ f := by
          by_contra hlt
          have : f = 1 := by omega
          rw [this] at hf_gt; norm_num at hf_gt
        exact_mod_cast h2
      have hmul : 1 / 2 ≤ ((f : ℝ) - 1 / 4) * (1 / ((f : ℝ) + 3 / 4)) := by
        rw [mul_one_div, le_div_iff₀ (by linarith)]
        linarith
      exact hmul.trans (mul_le_mul_of_nonneg_left hlog_ge_step (by linarith))
  have hcf := chiDeriv_pos hc' hf14
  calc (1 / 2 : ℝ) * chiDeriv c' f = chiDeriv c' f * (1 / 2) := by ring
    _ ≤ chiDeriv c' f * (((f : ℝ) - 1 / 4) * Real.log (((f : ℝ) + 3 / 4) / ((f : ℝ) - 1 / 4))) :=
        mul_le_mul_of_nonneg_left h_log_ge hcf.le
    _ ≤ siteGap c' f := by linarith [h_int_lb]

/-- For $n \ge 3$, $\chi'_n \le 2 \ell_n$. -/
theorem chiDeriv_le_two_siteGap {c' : ℝ} (hc' : 0 < c') {n : ℕ} (hn : 3 ≤ n) :
    chiDeriv c' n ≤ 2 * siteGap c' n := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hcont_chi : ContinuousOn (chiDeriv c') (Icc (n : ℝ) ((n : ℝ) + 1)) := fun t ht =>
    (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
  have hgap_int : siteGap c' n = ∫ t in (n : ℝ)..((n : ℝ) + 1), chiDeriv c' t := by
    unfold siteGap
    refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_).symm
    · rw [Set.uIcc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at ht
      exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1
    · exact hcont_chi.intervalIntegrable_of_Icc (by linarith)
  have h_pt : ∀ t ∈ Icc (n : ℝ) ((n : ℝ) + 1), (1 / 2 : ℝ) * chiDeriv c' n ≤ chiDeriv c' t := by
    intro t ht
    have hn14 : 1 / 4 < (n : ℝ) := by linarith
    have hdiv := chiDeriv_div_le hc' hn14 ht.1
    have hratio : ((t - 1 / 4) / ((n : ℝ) - 1 / 4)) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith [ht.2]
    have hct := chiDeriv_pos hc' (hn14.trans_le ht.1)
    have hle := hdiv.trans hratio
    rw [div_le_iff₀ hct] at hle
    linarith
  have h_lb : ∫ t in (n : ℝ)..((n : ℝ) + 1), (1 / 2 : ℝ) * chiDeriv c' n ≤ siteGap c' n := by
    rw [hgap_int]
    refine intervalIntegral.integral_mono_on (by linarith) (intervalIntegrable_const) ?_ h_pt
    exact hcont_chi.intervalIntegrable_of_Icc (by linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h_lb
  linarith

/-- For $k \ge 2$ and $a \in [k - 1/2, k + 1]$, $\chi'_a \le 3 \chi'_{k+1/2} \le 6 \ell_k$. -/
theorem chiDeriv_le_six_siteGap {c' : ℝ} (hc' : 0 < c') {k : ℕ} (hk : 2 ≤ k) {a : ℝ}
    (ha1 : (k : ℝ) - 1 / 2 ≤ a) (ha2 : a ≤ (k : ℝ) + 1) :
    chiDeriv c' a ≤ 3 * chiDeriv c' ((k : ℝ) + 1 / 2) ∧
      chiDeriv c' ((k : ℝ) + 1 / 2) ≤ 2 * siteGap c' k := by
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have ha14 : 1 / 4 < a := by linarith
  have hk12 : 1 / 4 < (k : ℝ) + 1 / 2 := by linarith
  have h1 : chiDeriv c' a ≤ 3 * chiDeriv c' ((k : ℝ) + 1 / 2) := by
    rcases le_or_gt a ((k : ℝ) + 1 / 2) with hle | hgt
    · have hdiv := chiDeriv_div_le hc' ha14 hle
      have hratio : ((k : ℝ) + 1 / 2 - 1 / 4) / (a - 1 / 4) ≤ 3 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      have hle' := hdiv.trans hratio
      rw [div_le_iff₀ (chiDeriv_pos hc' hk12)] at hle'
      exact hle'
    · have hanti := (chiDeriv_strictAntiOn hc' hk12 ha14 hgt).le
      linarith [chiDeriv_pos hc' hk12]
  have h2 : chiDeriv c' ((k : ℝ) + 1 / 2) ≤ 2 * siteGap c' k := by
    have hcont : ContinuousOn (chiDeriv c') (Icc (k : ℝ) ((k : ℝ) + 1)) := fun t ht =>
      (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).2.continuousAt.continuousWithinAt
    have hgap_int : siteGap c' k = ∫ t in (k : ℝ)..((k : ℝ) + 1), chiDeriv c' t := by
      unfold siteGap
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_).symm
      · rw [Set.uIcc_of_le (by linarith : (k : ℝ) ≤ (k : ℝ) + 1)] at ht
        exact (hasDerivAt_chiQuantile hc' (by linarith [ht.1])).1
      · exact hcont.intervalIntegrable_of_Icc (by linarith)
    have hsplit : (∫ t in (k : ℝ)..((k : ℝ) + 1 / 2), chiDeriv c' t) +
        (∫ t in ((k : ℝ) + 1 / 2)..((k : ℝ) + 1), chiDeriv c' t) =
        ∫ t in (k : ℝ)..((k : ℝ) + 1), chiDeriv c' t :=
      intervalIntegral.integral_add_adjacent_intervals
        ((hcont.mono (Icc_subset_Icc_right (by linarith : (k : ℝ) + 1 / 2 ≤ (k : ℝ) + 1))).intervalIntegrable_of_Icc (by linarith))
        ((hcont.mono (Icc_subset_Icc_left (by linarith : (k : ℝ) ≤ (k : ℝ) + 1 / 2))).intervalIntegrable_of_Icc (by linarith))
    have h_half1 : (1 / 2 : ℝ) * chiDeriv c' ((k : ℝ) + 1 / 2) ≤
        ∫ t in (k : ℝ)..((k : ℝ) + 1 / 2), chiDeriv c' t := by
      have hm := intervalIntegral.integral_mono_on (by linarith : (k : ℝ) ≤ (k : ℝ) + 1 / 2)
        (intervalIntegrable_const (μ := volume))
        ((hcont.mono (Icc_subset_Icc_right (by linarith : (k : ℝ) + 1 / 2 ≤ (k : ℝ) + 1))).intervalIntegrable_of_Icc (by linarith))
        fun t ht => by
          rcases eq_or_lt_of_le ht.2 with rfl | hlt
          · exact le_rfl
          · exact (chiDeriv_strictAntiOn hc' (Set.mem_Ioi.mpr (by linarith [ht.1])) hk12 hlt).le
      rw [intervalIntegral.integral_const, smul_eq_mul] at hm
      linarith
    have h_half2 : 0 ≤ ∫ t in ((k : ℝ) + 1 / 2)..((k : ℝ) + 1), chiDeriv c' t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        (chiDeriv_pos hc' (hk12.trans_le ht.1)).le
    linarith
  exact ⟨h1, h2⟩

/-! ### Section 3: `phiVar` calculus and curvature bounds -/

/-- Rescaled real log-Blaschke factor $\varphi(a) = f_x(\chi_a) = \log|T_{\chi_a}(x)|$. -/
noncomputable def phiVar (c' x a : ℝ) : ℝ := realLogT x (chiQuantile c' a)

/-- First derivative $\varphi'(a) = \partial_y f_x(\chi_a)\,\chi'_a$. -/
noncomputable def phiVarDeriv (c' x a : ℝ) : ℝ := realLogTDeriv x (chiQuantile c' a) * chiDeriv c' a

/-- Second derivative $\varphi''(a) = \partial_y^2 f_x(\chi_a)\,(\chi'_a)^2 + \partial_y f_x(\chi_a)\,\chi''_a$. -/
noncomputable def phiVarSecond (c' x a : ℝ) : ℝ :=
  realLogTSecond x (chiQuantile c' a) * chiDeriv c' a ^ 2 +
    realLogTDeriv x (chiQuantile c' a) * chiSecond c' a

lemma phiVar_hasDerivAt {c' x a : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) (ha : 1 / 4 < a)
    (hne : chiQuantile c' a ≠ x) :
    HasDerivAt (phiVar c' x) (phiVarDeriv c' x a) a ∧
      HasDerivAt (phiVarDeriv c' x) (phiVarSecond c' x a) a := by
  have hχ_pos : 0 ≤ chiQuantile c' a := xiStar_pos.le.trans (chiQuantile_spec hc' ha.le).1
  obtain ⟨hd1_f, hd2_f⟩ := realLogT_hasDerivAt hx hχ_pos hne
  obtain ⟨hd1_χ, hd2_χ⟩ := hasDerivAt_chiQuantile hc' ha
  refine ⟨?_, ?_⟩
  · exact hd1_f.comp a hd1_χ
  · have hcomp2 : HasDerivAt (fun t => realLogTDeriv x (chiQuantile c' t))
        (realLogTSecond x (chiQuantile c' a) * chiDeriv c' a) a := hd2_f.comp a hd1_χ
    exact (hcomp2.mul hd2_χ).congr_deriv (by unfold phiVarSecond; ring)

lemma continuousOn_phiVarSecond {c' x a b : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) (ha : 1 / 4 < a)
    (hab : a ≤ b) (hne : ∀ t ∈ Icc a b, chiQuantile c' t ≠ x) :
    ContinuousOn (phiVarSecond c' x) (Icc a b) := by
  intro t ht
  have ht14 := lt_of_lt_of_le ha ht.1
  have hχ := xiStar_lt_chiQuantile hc' ht14
  have hχ_nn : 0 ≤ chiQuantile c' t := xiStar_pos.le.trans hχ.le
  have hχ_c : ContinuousAt (chiQuantile c') t := (hasDerivAt_chiQuantile hc' ht14).1.continuousAt
  have hcd_c : ContinuousAt (chiDeriv c') t := (hasDerivAt_chiQuantile hc' ht14).2.continuousAt
  have hρ_c : ContinuousAt (fun s => rhoU (chiQuantile c' s)) t :=
    (hasDerivAt_rhoU hχ).continuousAt.comp hχ_c
  have hρ'_c : ContinuousAt (fun s => rhoUDeriv (chiQuantile c' s)) t :=
    (continuousAt_rhoUDeriv_of_gt hχ).comp hχ_c
  have hsec_c : ContinuousAt (chiSecond c') t :=
    ((hcd_c.pow 2).neg).mul (hρ'_c.div hρ_c (rhoU_pos hχ).ne')
  have hd_f_c : ContinuousAt (fun s => realLogTDeriv x (chiQuantile c' s)) t :=
    (realLogT_hasDerivAt hx hχ_nn (hne t ht)).2.continuousAt.comp hχ_c
  have h_sec_f_c : ContinuousAt (fun s => realLogTSecond x (chiQuantile c' s)) t := by
    have hcomb_c : ∀ {z : ℝ}, 0 < z → ContinuousAt combHSecond z := by
      intro z hz
      have hsh : Real.sinh (π * z) ≠ 0 := (Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hz)).ne'
      unfold combHSecond
      exact ((continuousAt_const.mul (Real.continuous_cosh.continuousAt.comp
        (continuousAt_const.mul continuousAt_id))).div
        ((Real.continuous_sinh.continuousAt.comp (continuousAt_const.mul continuousAt_id)).pow 2)
        (pow_ne_zero 2 hsh))
    have h_abs_c : ContinuousAt (fun s => combHSecond |x - chiQuantile c' s|) t := by
      have hsub : ContinuousAt (fun s => x - chiQuantile c' s) t := continuousAt_const.sub hχ_c
      have habs : ContinuousAt (fun s => |x - chiQuantile c' s|) t := hsub.abs
      exact ContinuousAt.comp (f := fun s => |x - chiQuantile c' s|)
        (hcomb_c (abs_pos.mpr (sub_ne_zero.mpr (hne t ht).symm))) habs
    have h_add_c : ContinuousAt (fun s => combHSecond (x + chiQuantile c' s)) t :=
      (hcomb_c (by linarith [xiStar_pos, hχ])).comp (continuousAt_const.add hχ_c)
    exact h_abs_c.add h_add_c
  exact ((h_sec_f_c.mul (hcd_c.pow 2)).add (hd_f_c.mul hsec_c)).continuousWithinAt

/-- When $\chi_a > x \ge 0$, $\varphi'(a) > 0$ and $\varphi''(a) < 0$. -/
lemma phiVar_deriv_sign_of_gt {c' x a : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) (ha : 1 / 4 < a)
    (hgt : x < chiQuantile c' a) :
    0 < phiVarDeriv c' x a ∧ phiVarSecond c' x a < 0 := by
  have hχ_nn : 0 ≤ chiQuantile c' a := xiStar_pos.le.trans (chiQuantile_spec hc' ha.le).1
  have hbd := realLogT_deriv_bounds hx hχ_nn hgt.ne'
  have hcd := chiDeriv_pos hc' ha
  have hcs := chiSecond_neg hc' ha
  have hf1 : 0 < realLogTDeriv x (chiQuantile c' a) := (hbd.2.2 hgt).1
  have hf2 : realLogTSecond x (chiQuantile c' a) < 0 := hbd.1
  refine ⟨mul_pos hf1 hcd, ?_⟩
  unfold phiVarSecond
  have t1 : realLogTSecond x (chiQuantile c' a) * chiDeriv c' a ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hf2 (sq_pos_of_pos hcd)
  have t2 : realLogTDeriv x (chiQuantile c' a) * chiSecond c' a < 0 :=
    mul_neg_of_pos_of_neg hf1 hcs
  linarith

/-- Curvature upper bound for $\chi_a < x$:
$(\varphi''(a))_+ \le \frac{2}{x - \xi_*} \frac{(\chi'_a)^2}{r_a}$ (`comb_estimates.tex`, line 168). -/
theorem phiVarSecond_le_G {c' x a : ℝ} (hc' : 0 < c') (ha : 1 / 4 < a)
    (hlt : chiQuantile c' a < x) :
    phiVarSecond c' x a ≤ (2 / (x - xiStar)) * (chiDeriv c' a ^ 2 / siteRadius c' a) := by
  have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha
  have hr_pos : 0 < siteRadius c' a := sub_pos.mpr hχ_gt
  have hd_pos : 0 < x - chiQuantile c' a := sub_pos.mpr hlt
  have hs_pos : 0 < x - xiStar := by linarith
  obtain ⟨_, _, hH, _⟩ := combH_bounds
  have hH_d := hH (x - chiQuantile c' a) hd_pos
  have hH_s := hH (x + chiQuantile c' a) (by linarith [xiStar_pos])
  have h_sec_le : realLogTSecond x (chiQuantile c' a) ≤ -combHDeriv (x - chiQuantile c' a) / (x - chiQuantile c' a) := by
    unfold realLogTSecond
    rw [abs_of_pos hd_pos]
    linarith [hH_d.2.2.1, hH_s.2.2.2.1]
  have h_abs_d : |realLogTDeriv x (chiQuantile c' a)| ≤ combHDeriv (x - chiQuantile c' a) := by
    have hx_nn : 0 ≤ x := by linarith [xiStar_pos]
    have hχ_nn : 0 ≤ chiQuantile c' a := xiStar_pos.le.trans hχ_gt.le
    have h_nonpos := ((realLogT_deriv_bounds hx_nn hχ_nn hlt.ne).2.1 hlt).1
    rw [abs_of_nonpos h_nonpos]
    simp only [realLogTDeriv, hlt, ite_true]
    linarith [hH_s.1]
  have h_cs_abs : |chiSecond c' a| ≤ chiDeriv c' a ^ 2 / siteRadius c' a := by
    have hld := (logDeriv_rhoU_bounds hr_pos).2
    have hld_pos := (logDeriv_rhoU_bounds hr_pos).1
    have heq : xiStar + siteRadius c' a = chiQuantile c' a := by unfold siteRadius; ring
    rw [heq] at hld hld_pos
    unfold chiSecond
    rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) hld_pos.le)]
    calc chiDeriv c' a ^ 2 * (rhoUDeriv (chiQuantile c' a) / rhoU (chiQuantile c' a))
        ≤ chiDeriv c' a ^ 2 * (1 / siteRadius c' a) := mul_le_mul_of_nonneg_left hld (sq_nonneg _)
      _ = chiDeriv c' a ^ 2 / siteRadius c' a := by ring
  have h_phi_le : phiVarSecond c' x a ≤
      combHDeriv (x - chiQuantile c' a) * chiDeriv c' a ^ 2 *
        (1 / siteRadius c' a - 1 / (x - chiQuantile c' a)) := by
    unfold phiVarSecond
    have t1 : realLogTSecond x (chiQuantile c' a) * chiDeriv c' a ^ 2 ≤
        (-combHDeriv (x - chiQuantile c' a) / (x - chiQuantile c' a)) * chiDeriv c' a ^ 2 :=
      mul_le_mul_of_nonneg_right h_sec_le (sq_nonneg _)
    have t2 : realLogTDeriv x (chiQuantile c' a) * chiSecond c' a ≤
        |realLogTDeriv x (chiQuantile c' a)| * |chiSecond c' a| :=
      (le_abs_self _).trans (abs_mul _ _).le
    have t3 : |realLogTDeriv x (chiQuantile c' a)| * |chiSecond c' a| ≤
        combHDeriv (x - chiQuantile c' a) * (chiDeriv c' a ^ 2 / siteRadius c' a) :=
      mul_le_mul h_abs_d h_cs_abs (abs_nonneg _) hH_d.1.le
    linarith [show (-combHDeriv (x - chiQuantile c' a) / (x - chiQuantile c' a)) * chiDeriv c' a ^ 2 +
        combHDeriv (x - chiQuantile c' a) * (chiDeriv c' a ^ 2 / siteRadius c' a) =
        combHDeriv (x - chiQuantile c' a) * chiDeriv c' a ^ 2 *
          (1 / siteRadius c' a - 1 / (x - chiQuantile c' a)) by ring]
  rcases le_or_gt (x - chiQuantile c' a) (siteRadius c' a) with hdr | hdr
  · have h_nonpos : 1 / siteRadius c' a - 1 / (x - chiQuantile c' a) ≤ 0 := by
      have := one_div_le_one_div_of_le hd_pos hdr
      linarith
    have h_le0 : phiVarSecond c' x a ≤ 0 :=
      h_phi_le.trans (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hH_d.1.le (sq_nonneg _)) h_nonpos)
    exact h_le0.trans (by positivity)
  · have hs_lt : x - xiStar < 2 * (x - chiQuantile c' a) := by
      unfold siteRadius at hdr; linarith
    have h_hd_le : combHDeriv (x - chiQuantile c' a) ≤ 2 / (x - xiStar) := by
      calc combHDeriv (x - chiQuantile c' a) ≤ (x - chiQuantile c' a)⁻¹ := hH_d.2.1
        _ = 1 / (x - chiQuantile c' a) := (one_div _).symm
        _ ≤ 2 / (x - xiStar) := by
            rw [div_le_div_iff₀ hd_pos hs_pos]; linarith
    have h_sub_le : 1 / siteRadius c' a - 1 / (x - chiQuantile c' a) ≤ 1 / siteRadius c' a := by
      linarith [one_div_pos.mpr hd_pos]
    have h_sub_nn : 0 ≤ 1 / siteRadius c' a - 1 / (x - chiQuantile c' a) := by
      have := one_div_le_one_div_of_le hr_pos hdr.le; linarith
    calc phiVarSecond c' x a
        ≤ combHDeriv (x - chiQuantile c' a) * chiDeriv c' a ^ 2 *
            (1 / siteRadius c' a - 1 / (x - chiQuantile c' a)) := h_phi_le
      _ ≤ (2 / (x - xiStar)) * chiDeriv c' a ^ 2 * (1 / siteRadius c' a) :=
          mul_le_mul (mul_le_mul_of_nonneg_right h_hd_le (sq_nonneg _)) h_sub_le h_sub_nn
            (mul_nonneg (by positivity) (sq_nonneg _))
      _ = (2 / (x - xiStar)) * (chiDeriv c' a ^ 2 / siteRadius c' a) := by ring

/-- Lower curvature bound for $\chi_a < x$: $-\varphi''(a) \le C (\chi'_a)^2 / (x - \chi_a)^2$
(`comb_estimates.tex`, line 192). -/
theorem neg_phiVarSecond_le_of_lt :
    ∃ C > 0, ∀ {c' x a : ℝ}, 0 < c' → 1 / 4 < a → chiQuantile c' a < x →
      -phiVarSecond c' x a ≤ C * chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2 := by
  obtain ⟨CH, hCH, hH, _⟩ := combH_bounds
  refine ⟨2 * CH, by positivity, fun {c' x a} hc' ha hlt => ?_⟩
  have hχ_gt : xiStar < chiQuantile c' a := xiStar_lt_chiQuantile hc' ha
  have hx_nn : 0 ≤ x := by linarith [xiStar_pos]
  have hχ_nn : 0 ≤ chiQuantile c' a := xiStar_pos.le.trans hχ_gt.le
  have hd_pos : 0 < x - chiQuantile c' a := sub_pos.mpr hlt
  have hsum_pos : 0 < x + chiQuantile c' a := by linarith [xiStar_pos]
  have hf_neg : realLogTDeriv x (chiQuantile c' a) ≤ 0 :=
    ((realLogT_deriv_bounds hx_nn hχ_nn hlt.ne).2.1 hlt).1
  have hcs_neg : chiSecond c' a < 0 := chiSecond_neg hc' ha
  have hprod_nn : 0 ≤ realLogTDeriv x (chiQuantile c' a) * chiSecond c' a :=
    mul_nonneg_of_nonpos_of_nonpos hf_neg hcs_neg.le
  have hsec1 := (hH (x - chiQuantile c' a) hd_pos).2.2.2.2
  have hsec2 := (hH (x + chiQuantile c' a) hsum_pos).2.2.2.2
  have hsec1_neg : combHSecond (x - chiQuantile c' a) < 0 := (hH (x - chiQuantile c' a) hd_pos).2.2.2.1
  have hsec2_neg : combHSecond (x + chiQuantile c' a) < 0 := (hH (x + chiQuantile c' a) hsum_pos).2.2.2.1
  have h_abs_sum : -realLogTSecond x (chiQuantile c' a) ≤ 2 * CH / (x - chiQuantile c' a) ^ 2 := by
    have h1 : -combHSecond (x - chiQuantile c' a) ≤ CH / (x - chiQuantile c' a) ^ 2 := by
      rwa [abs_of_neg hsec1_neg] at hsec1
    have h2 : -combHSecond (x + chiQuantile c' a) ≤ CH / (x - chiQuantile c' a) ^ 2 := by
      rw [abs_of_neg hsec2_neg] at hsec2
      have hsq : (x - chiQuantile c' a) ^ 2 ≤ (x + chiQuantile c' a) ^ 2 := by nlinarith
      exact hsec2.trans (div_le_div_of_nonneg_left hCH.le (sq_pos_of_pos hd_pos) hsq)
    calc -(realLogTSecond x (chiQuantile c' a))
        = -combHSecond (x - chiQuantile c' a) + -combHSecond (x + chiQuantile c' a) := by
            unfold realLogTSecond; rw [abs_of_pos hd_pos]; ring
      _ ≤ CH / (x - chiQuantile c' a) ^ 2 + CH / (x - chiQuantile c' a) ^ 2 := add_le_add h1 h2
      _ = 2 * CH / (x - chiQuantile c' a) ^ 2 := by ring
  unfold phiVarSecond
  calc -(realLogTSecond x (chiQuantile c' a) * chiDeriv c' a ^ 2 +
        realLogTDeriv x (chiQuantile c' a) * chiSecond c' a)
      ≤ (-realLogTSecond x (chiQuantile c' a)) * chiDeriv c' a ^ 2 := by linarith
    _ ≤ (2 * CH / (x - chiQuantile c' a) ^ 2) * chiDeriv c' a ^ 2 :=
        mul_le_mul_of_nonneg_right h_abs_sum (sq_nonneg _)
    _ = 2 * CH * chiDeriv c' a ^ 2 / (x - chiQuantile c' a) ^ 2 := by ring

/-! ### Section 4: `pairModQ`, `refComb` log expansion, and `D_K^{(f)}` limit -/

/-- Pair modulus $q_k(x) = |T_{\chi_k + i\varepsilon_k}(x) T_{\chi_k - i\varepsilon_k}(x)|$
where $\varepsilon_k = \eta_0 \ell_k$. -/
noncomputable def pairModQ (c' η₀ x : ℝ) (k : ℕ) : ℝ :=
  blaschkePairQ (chiQuantile c' k) (η₀ * siteGap c' k) x

/-- Cell predicate $\chi_n \le x < \chi_{n+1}$. -/
def inCell (c' : ℝ) (n : ℕ) (x : ℝ) : Prop :=
  chiQuantile c' n ≤ x ∧ x < chiQuantile c' (n + 1 : ℕ)

lemma pairModQ_le_one {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {k : ℕ} (hk : 1 ≤ k) :
    pairModQ c' η₀ x k ≤ 1 := by
  unfold pairModQ blaschkePairQ
  have hgk : siteGap c' k ≤ siteGap c' 1 := by
    rcases eq_or_lt_of_le hk with rfl | hgt
    · exact le_rfl
    · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      have heq : (k - 1) + 1 = k := by omega
      simpa [heq] using hanti
  have hgk_nn : 0 ≤ siteGap c' k := by
    unfold siteGap
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ha1 : (k : ℝ) ∈ Ici (1 / 4) := Set.mem_Ici.mpr (by linarith)
    have hb1 : (k : ℝ) + 1 ∈ Ici (1 / 4) := Set.mem_Ici.mpr (by linarith)
    exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn ha1 hb1 (by linarith))
  have hε : |η₀ * siteGap c' k| ≤ 1 / 4 := by
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgk_nn)]
    nlinarith
  exact norm_pair_blaschkeT_le_one (chiQuantile c' k) (η₀ * siteGap c' k) hε (by simp)

lemma pairModQ_pos {c' η₀ x : ℝ} (hc' : 0 < c') (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) {n k : ℕ} (hk : 1 ≤ k) (hx : inCell c' n x)
    (hnz : 0 < η₀ ∨ x ≠ chiQuantile c' n) :
    0 < pairModQ c' η₀ x k := by
  unfold pairModQ
  rw [blaschkePairQ_eq]
  have hgk : siteGap c' k ≤ siteGap c' 1 := by
    rcases eq_or_lt_of_le hk with rfl | hgt
    · exact le_rfl
    · have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ k - 1 by omega)
      have heq : (k - 1) + 1 = k := by omega
      simpa [heq] using hanti
  have hgk_pos : 0 < siteGap c' k := by
    unfold siteGap
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have ha1 : (k : ℝ) ∈ Ici (1 / 4) := Set.mem_Ici.mpr (by linarith)
    have hb1 : (k : ℝ) + 1 ∈ Ici (1 / 4) := Set.mem_Ici.mpr (by linarith)
    exact sub_pos.mpr (chiQuantile_strictMonoOn hc' ha1 hb1 (by linarith))
  have hε_nn : 0 ≤ η₀ * siteGap c' k := mul_nonneg hη₀0 hgk_pos.le
  have hε_le : η₀ * siteGap c' k ≤ 1 / 8 := by nlinarith
  have hS_lt : Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 ≤ 1 / 2 := by
    have hpi := Real.pi_pos
    have h1 : |Real.sin (π * (η₀ * siteGap c' k) / 2)| ≤ 1 / 2 := by
      rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith))]
      exact (Real.sin_le (by positivity)).trans (by nlinarith [Real.pi_lt_d4])
    nlinarith [sq_abs (Real.sin (π * (η₀ * siteGap c' k) / 2)),
      abs_nonneg (Real.sin (π * (η₀ * siteGap c' k) / 2))]
  have hden1 : 0 < Real.cosh (π * (x - chiQuantile c' k) / 2) ^ 2 -
      Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
    have := Real.one_le_cosh (π * (x - chiQuantile c' k) / 2); nlinarith
  have hden2 : 0 < Real.cosh (π * (x + chiQuantile c' k) / 2) ^ 2 -
      Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
    have := Real.one_le_cosh (π * (x + chiQuantile c' k) / 2); nlinarith
  have hχk_pos : 0 < chiQuantile c' k := by
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact xiStar_pos.trans (xiStar_lt_chiQuantile hc' (by linarith))
  have hx_nn : 0 ≤ x := by
    have hχn_nn : 0 ≤ chiQuantile c' n := by
      rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · have h0 : chiQuantile c' ((0 : ℕ) : ℝ) = xiStar := by
          unfold chiQuantile
          split_ifs with h
          · exact absurd h.2 (by norm_num)
          · rfl
        rw [h0]; exact xiStar_pos.le
      · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        exact xiStar_pos.le.trans (chiQuantile_spec hc' (by linarith)).1
    exact hχn_nn.trans hx.1
  have hnum2 : 0 < Real.sinh (π * (x + chiQuantile c' k) / 2) ^ 2 +
      Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
    have hsh : 0 < Real.sinh (π * (x + chiQuantile c' k) / 2) :=
      Real.sinh_pos_iff.mpr (by positivity [Real.pi_pos])
    positivity
  have hnum1 : 0 < Real.sinh (π * (x - chiQuantile c' k) / 2) ^ 2 +
      Real.sin (π * (η₀ * siteGap c' k) / 2) ^ 2 := by
    by_cases hkn : k = n
    · subst hkn
      rcases hnz with hη | hne
      · have hε_pos : 0 < π * (η₀ * siteGap c' k) / 2 := by positivity [Real.pi_pos]
        have hε_lt_pi : π * (η₀ * siteGap c' k) / 2 < π := by nlinarith [Real.pi_pos]
        have hS_pos : 0 < Real.sin (π * (η₀ * siteGap c' k) / 2) :=
          Real.sin_pos_of_pos_of_lt_pi hε_pos hε_lt_pi
        positivity
      · have hsh : Real.sinh (π * (x - chiQuantile c' k) / 2) ≠ 0 :=
          Real.sinh_ne_zero.mpr (by have := Real.pi_pos; positivity [sub_ne_zero.mpr hne])
        positivity
    · have hne : x ≠ chiQuantile c' k := by
        rcases lt_or_gt_of_ne hkn with hlt | hgt
        · have hk_le : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hlt.le
          have hk_lt : (k : ℝ) < (n : ℝ) := by exact_mod_cast hlt
          have h14k : (1 / 4 : ℝ) ≤ (k : ℝ) := by
            have : (1 : ℝ) ≤ k := by exact_mod_cast hk
            linarith
          have h14n : (1 / 4 : ℝ) ≤ (n : ℝ) := by linarith
          have hχ_lt := chiQuantile_strictMonoOn hc' h14k h14n hk_lt
          linarith [hx.1]
        · have hk_ge : ((n + 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hgt
          have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have h14n1 : (1 / 4 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
          have h14k : (1 / 4 : ℝ) ≤ (k : ℝ) := h14n1.trans hk_ge
          have hχ_le := (chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr h14n1) (Set.mem_Ici.mpr h14k) hk_ge
          linarith [hx.2]
      have hsh : Real.sinh (π * (x - chiQuantile c' k) / 2) ≠ 0 :=
        Real.sinh_ne_zero.mpr (by have := Real.pi_pos; positivity [sub_ne_zero.mpr hne])
      positivity
  exact mul_pos (div_pos hnum1 hden1) (div_pos hnum2 hden2)

/-- Convergent log-modulus series for $B^{(f)}(x)$ when every factor is nonzero. -/
theorem refComb_norm_log_eq_tsum {c' η₀ x : ℝ} (hc' : 0 < c') (hx : 0 ≤ x)
    {f : ℕ} (hf : 1 ≤ f) (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4) (hgap : siteGap c' 1 ≤ 1 / 2)
    (hf_ne : chiQuantile c' f ≠ x)
    (hq_pos : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m)) :
    Summable (fun m : ℕ => Real.log (pairModQ c' η₀ x (f + 1 + m))) ∧
      Real.log ‖refComb c' f η₀ (x : ℂ)‖ =
        phiVar c' x f + ∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)) := by
  let χ := fun m : ℕ => chiQuantile c' (f + 1 + m : ℕ)
  let ε := fun m : ℕ => η₀ * siteGap c' (f + 1 + m)
  let P : ℕ → ℂ := fun m =>
    blaschkeT ((χ m : ℂ) + (ε m : ℂ) * Complex.I) (x : ℂ) *
      blaschkeT ((χ m : ℂ) - (ε m : ℂ) * Complex.I) (x : ℂ)
  have hχ_nn : ∀ m : ℕ, 0 ≤ χ m := fun m => by
    have ha : (1 / 4 : ℝ) ≤ (f + 1 + m : ℕ) := by
      have : (1 : ℝ) ≤ (f + 1 + m : ℕ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
      linarith
    exact xiStar_pos.le.trans (chiQuantile_spec hc' ha).1
  have hε_bd : ∀ m : ℕ, |ε m| ≤ 1 / 8 := fun m => by
    have hgk : siteGap c' (f + 1 + m) ≤ siteGap c' 1 := by
      have hanti := (siteGap_strictAnti hc').antitone (show 0 ≤ f + m by omega)
      have heq : (f + m) + 1 = f + 1 + m := by omega
      simpa [heq] using hanti
    have hgk_nn : 0 ≤ siteGap c' (f + 1 + m) := by
      unfold siteGap
      have hfm : (1 : ℝ) ≤ ((f + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f + 1 + m)
      have ha1 : ((f + 1 + m : ℕ) : ℝ) ∈ Ici (1 / 4) := Set.mem_Ici.mpr (by linarith)
      have hb1 : ((f + 1 + m : ℕ) : ℝ) + 1 ∈ Ici (1 / 4) := Set.mem_Ici.mpr (by linarith)
      exact sub_nonneg.mpr ((chiQuantile_strictMonoOn hc').monotoneOn ha1 hb1 (by linarith))
    rw [abs_of_nonneg (mul_nonneg hη₀0 hgk_nn)]
    change η₀ * siteGap c' (f + 1 + m) ≤ 1 / 8
    nlinarith
  have hsum := summable_exp_neg_pi_chiQuantile hc' f
  have hhasProd := (comb_pairProd_hasProdLocallyUniformlyOn χ ε hχ_nn hε_bd hsum).hasProd
    (by simp : (x : ℂ) ∈ {b : ℂ | |b.im| < 7 / 8})
  have hnorm_P : ∀ m : ℕ, ‖P m‖ = pairModQ c' η₀ x (f + 1 + m) := fun m => rfl
  -- Show `‖∏' m, P m‖ > 0` by comparing tail factors with `1`
  have htail_tend : Tendsto (fun m : ℕ => 32 * Real.exp (π * x) * Real.exp (-π * χ m)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsum.tendsto_atTop_zero.const_mul (32 * Real.exp (π * x))
  have hχ_tend : Tendsto χ atTop atTop :=
    (tendsto_chiQuantile_atTop hc').comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).comp
        (tendsto_atTop_atTop.mpr fun N => ⟨N, fun m hm => by omega⟩))
  obtain ⟨M₁, hM₁⟩ := (hχ_tend.eventually_ge_atTop (x + 2)).exists_forall_of_atTop
  obtain ⟨M₂, hM₂⟩ := (htail_tend.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)).exists_forall_of_atTop
  set M := max M₁ M₂
  have hP_sub : ∀ m ≥ M, ‖P m - 1‖ ≤ 32 * Real.exp (π * x) * Real.exp (-π * χ m) := by
    intro m hm
    have hx_le : |(x : ℂ).re| ≤ x := by simp [abs_of_nonneg hx]
    exact blaschkeT_pair_sub_one_le (hε_bd m) (hχ_nn m) hx hx_le
      ((hM₁ m ((le_max_left _ _).trans hm)).trans' (by linarith))
  have hlog_ge : ∀ m ≥ M, -64 * Real.exp (π * x) * Real.exp (-π * χ m) ≤ Real.log ‖P m‖ := by
    intro m hm
    have hsub := hP_sub m hm
    have hle_half : ‖P m - 1‖ ≤ 1 / 2 := hsub.trans (hM₂ m ((le_max_right _ _).trans hm))
    have hnorm_lb : 1 - ‖P m - 1‖ ≤ ‖P m‖ := by
      have htri : ‖(1 : ℂ)‖ - ‖P m‖ ≤ ‖1 - P m‖ := norm_sub_norm_le 1 (P m)
      rw [norm_one, norm_sub_rev] at htri
      linarith
    have hlog1 : -2 * ‖P m - 1‖ ≤ Real.log (1 - ‖P m - 1‖) := by
      set u := ‖P m - 1‖
      have hu0 : 0 ≤ u := norm_nonneg _
      have hu1 : 0 < 1 - u := by linarith
      have hlog_inv : -Real.log (1 - u) = Real.log (1 + u / (1 - u)) := by
        rw [← Real.log_inv]; congr 1; field_simp [hu1.ne']; ring
      have h1 : Real.log (1 + u / (1 - u)) ≤ u / (1 - u) :=
        (Real.log_le_sub_one_of_pos (by positivity)).trans_eq (by ring)
      have h2 : u / (1 - u) ≤ 2 * u := by
        rw [div_le_iff₀ hu1]; nlinarith
      linarith
    have hPm_pos : 0 < ‖P m‖ := by rw [hnorm_P]; exact hq_pos m
    calc -64 * Real.exp (π * x) * Real.exp (-π * χ m)
        ≤ -2 * ‖P m - 1‖ := by linarith
      _ ≤ Real.log (1 - ‖P m - 1‖) := hlog1
      _ ≤ Real.log ‖P m‖ := Real.log_le_log (by linarith) hnorm_lb
  set S_tail := 64 * Real.exp (π * x) * ∑' m : ℕ, Real.exp (-π * χ m)
  have hprod_M_pos : 0 < ∏ m ∈ Finset.range M, ‖P m‖ :=
    Finset.prod_pos fun m _ => by rw [hnorm_P]; exact hq_pos m
  have hprod_lb : ∀ K ≥ M,
      (∏ m ∈ Finset.range M, ‖P m‖) * Real.exp (-S_tail) ≤ ‖∏ m ∈ Finset.range K, P m‖ := by
    intro K hK
    rw [norm_prod, ← Finset.prod_range_mul_prod_Ico (fun m => ‖P m‖) hK]
    have h_ico_pos : ∀ m ∈ Finset.Ico M K, 0 < ‖P m‖ := fun m _ => by
      rw [hnorm_P]; exact hq_pos m
    have h_ico_eq : ∏ m ∈ Finset.Ico M K, ‖P m‖ =
        Real.exp (∑ m ∈ Finset.Ico M K, Real.log ‖P m‖) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun m hm => (Real.exp_log (h_ico_pos m hm)).symm
    have h_sum_ge : -S_tail ≤ ∑ m ∈ Finset.Ico M K, Real.log ‖P m‖ := by
      have h1 : ∑ m ∈ Finset.Ico M K, (-64 * Real.exp (π * x) * Real.exp (-π * χ m)) ≤
          ∑ m ∈ Finset.Ico M K, Real.log ‖P m‖ :=
        Finset.sum_le_sum fun m hm => hlog_ge m (Finset.mem_Ico.mp hm).1
      have h2 : ∑ m ∈ Finset.Ico M K, (64 * Real.exp (π * x) * Real.exp (-π * χ m)) ≤ S_tail := by
        have hsum_scaled : Summable (fun m => 64 * Real.exp (π * x) * Real.exp (-π * χ m)) := by
          simpa only [mul_assoc] using hsum.mul_left (64 * Real.exp (π * x))
        have hle := hsum_scaled.sum_le_tsum (Finset.Ico M K) fun m _ => by positivity
        refine hle.trans_eq ?_
        dsimp [S_tail]; rw [← tsum_mul_left]
      have h3 : ∑ m ∈ Finset.Ico M K, (-64 * Real.exp (π * x) * Real.exp (-π * χ m)) =
          -∑ m ∈ Finset.Ico M K, (64 * Real.exp (π * x) * Real.exp (-π * χ m)) := by
        rw [← Finset.sum_neg_distrib]; congr 1; ext m; ring
      linarith
    rw [h_ico_eq]
    gcongr
  have hnorm_tend : Tendsto (fun s : Finset ℕ => ‖∏ m ∈ s, P m‖) atTop (𝓝 ‖∏' m : ℕ, P m‖) :=
    continuous_norm.continuousAt.tendsto.comp hhasProd
  have hrange : Tendsto Finset.range atTop atTop :=
    tendsto_atTop_atTop.mpr fun s =>
      ⟨s.sup id + 1, fun n hn m hm => Finset.mem_range.mpr (lt_of_le_of_lt (Finset.le_sup (f := id) hm) hn)⟩
  have htprod_pos : 0 < ‖∏' m : ℕ, P m‖ := by
    have h_seq : Tendsto (fun K : ℕ => ‖∏ m ∈ Finset.range K, P m‖) atTop (𝓝 ‖∏' m : ℕ, P m‖) :=
      hnorm_tend.comp hrange
    have hge := ge_of_tendsto h_seq (by
      filter_upwards [eventually_ge_atTop M] with K hK
      exact hprod_lb K hK)
    exact lt_of_lt_of_le (mul_pos hprod_M_pos (Real.exp_pos _)) hge
  have hlog_seq : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range K, Real.log ‖P m‖) atTop
      (𝓝 (Real.log ‖∏' m : ℕ, P m‖)) := by
    have h_cont : Tendsto (fun K : ℕ => Real.log ‖∏ m ∈ Finset.range K, P m‖) atTop
        (𝓝 (Real.log ‖∏' m : ℕ, P m‖)) :=
      (Real.continuousAt_log htprod_pos.ne').tendsto.comp
        (hnorm_tend.comp hrange)
    refine h_cont.congr fun K => ?_
    rw [norm_prod, Real.log_prod (fun m _ => by rw [hnorm_P]; exact (hq_pos m).ne')]
  have h_log_nonpos : ∀ m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)) ≤ 0 := fun m => by
    have h_le1 : ‖P m‖ ≤ 1 :=
      norm_pair_blaschkeT_le_one (χ m) (ε m) ((hε_bd m).trans (by norm_num)) (by simp)
    rw [← hnorm_P]
    exact Real.log_nonpos (norm_nonneg _) h_le1
  have h_summable : Summable (fun m : ℕ => Real.log (pairModQ c' η₀ x (f + 1 + m))) := by
    have h_neg_sum : Summable (fun m : ℕ => -Real.log (pairModQ c' η₀ x (f + 1 + m))) := by
      have h_bdd : ∃ C : ℝ, ∀ K : ℕ, ∑ m ∈ Finset.range K, (-Real.log (pairModQ c' η₀ x (f + 1 + m))) ≤ C := by
        refine ⟨-Real.log ‖∏' m : ℕ, P m‖ + 1, fun K => ?_⟩
        have h_inc : Monotone (fun N : ℕ => ∑ m ∈ Finset.range N, (-Real.log ‖P m‖)) :=
          monotone_nat_of_le_succ fun N => by
            rw [Finset.sum_range_succ, hnorm_P]
            linarith [h_log_nonpos N]
        have h_lim : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, (-Real.log ‖P m‖)) atTop
            (𝓝 (-Real.log ‖∏' m : ℕ, P m‖)) := by
          simpa only [Finset.sum_neg_distrib] using hlog_seq.neg
        exact (h_inc.ge_of_tendsto h_lim K).trans (by linarith)
      obtain ⟨C, hC⟩ := h_bdd
      exact summable_of_sum_range_le (fun m => by linarith [h_log_nonpos m]) hC
    exact h_neg_sum.neg.congr fun m => neg_neg _
  have h_tsum_eq : ∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)) = Real.log ‖∏' m : ℕ, P m‖ :=
    tendsto_nhds_unique (h_summable.hasSum.tendsto_sum_nat) hlog_seq
  have hTf_pos : 0 < ‖blaschkeT (chiQuantile c' f : ℂ) (x : ℂ)‖ := by
    have hχf_pos : 0 < chiQuantile c' f := by
      have hf1 : (1 / 4 : ℝ) < (f : ℝ) := by
        have : (1 : ℝ) ≤ f := by exact_mod_cast hf
        linarith
      exact xiStar_pos.trans (xiStar_lt_chiQuantile hc' hf1)
    have h_eq : blaschkeT (chiQuantile c' f : ℂ) (x : ℂ) =
        ((Real.tanh (π * (x - chiQuantile c' f) / 2) *
          Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
      unfold blaschkeT
      have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' f : ℂ)) / 2) =
          ((Real.tanh (π * (x - chiQuantile c' f) / 2) : ℝ) : ℂ) := by
        have h1 : Complex.tanh ((π * (x - chiQuantile c' f) / 2 : ℝ) : ℂ) =
            ((Real.tanh (π * (x - chiQuantile c' f) / 2) : ℝ) : ℂ) := by
          rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
            ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
        rw [← h1]; congr 1; push_cast; ring
      have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' f : ℂ)) / 2) =
          ((Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
        have h1 : Complex.tanh ((π * (x + chiQuantile c' f) / 2 : ℝ) : ℂ) =
            ((Real.tanh (π * (x + chiQuantile c' f) / 2) : ℝ) : ℂ) := by
          rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
            ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
        rw [← h1]; congr 1; push_cast; ring
      rw [hc1, hc2, ← Complex.ofReal_mul]
    rw [h_eq, Complex.norm_real, Real.norm_eq_abs, abs_pos]
    have ht1 : Real.tanh (π * (x - chiQuantile c' f) / 2) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
      exact ⟨Real.sinh_ne_zero.mpr (by have := Real.pi_pos; positivity [sub_ne_zero.mpr hf_ne.symm]),
        (Real.cosh_pos _).ne'⟩
    have ht2 : Real.tanh (π * (x + chiQuantile c' f) / 2) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
      exact ⟨(Real.sinh_pos_iff.mpr (by have := Real.pi_pos; positivity)).ne',
        (Real.cosh_pos _).ne'⟩
    exact mul_ne_zero ht1 ht2
  refine ⟨h_summable, ?_⟩
  unfold refComb phiVar realLogT
  rw [norm_mul, Real.log_mul hTf_pos.ne' htprod_pos.ne', h_tsum_eq]

/-- Unconditional summability of $\varphi(k) = f_x(\chi_k)$ for $x \ge 0$ and $c' > 0$
(assuming $\ell_1 \le 1/2$). -/
theorem summable_phiVar {c' x : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) (hgap : siteGap c' 1 ≤ 1 / 2) :
    Summable (fun k : ℕ => phiVar c' x k) := by
  obtain ⟨n₀, hn₀⟩ := ((tendsto_chiQuantile_atTop hc').comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop x |>.exists
  set f0 := max n₀ 1
  have hf0_ge : 1 ≤ f0 := le_max_right n₀ 1
  have hf0_gt : x < chiQuantile c' f0 := by
    rcases eq_or_lt_of_le (le_max_left n₀ 1) with heq | _
    · dsimp [f0]; rw [← heq]; exact hn₀
    · rcases Nat.eq_zero_or_pos n₀ with hn0 | hnpos
      · have hchi0 : chiQuantile c' 0 = xiStar := by
          unfold chiQuantile
          split_ifs with h
          · exact absurd h.2 (by norm_num)
          · rfl
        have hlt_xi : x < xiStar := by simpa [hn0, hchi0] using hn₀
        have hf0_1 : f0 = 1 := by simp [f0, hn0]
        rw [hf0_1]
        exact hlt_xi.trans (xiStar_lt_chiQuantile hc' (by norm_num))
      · have hn1 : (1 : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hnpos
        have hf1 : (1 : ℝ) ≤ (f0 : ℝ) := by exact_mod_cast hf0_ge
        have hle : (n₀ : ℝ) ≤ (f0 : ℝ) := by exact_mod_cast le_max_left n₀ 1
        exact (hn₀ : x < chiQuantile c' n₀).trans_le
          ((chiQuantile_strictMonoOn hc').monotoneOn
            (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hle)
  have hf_ne : chiQuantile c' f0 ≠ x := hf0_gt.ne'
  have hq_pos : ∀ m : ℕ, 0 < pairModQ c' 0 x (f0 + 1 + m) := by
    intro m
    unfold pairModQ
    simp only [zero_mul, blaschkePairQ_zero_eps]
    have hgt : x < chiQuantile c' (f0 + 1 + m : ℕ) := by
      have hf1 : (1 : ℝ) ≤ (f0 : ℝ) := by exact_mod_cast hf0_ge
      have hle : ((f0 : ℕ) : ℝ) ≤ ((f0 + 1 + m : ℕ) : ℝ) := by
        exact_mod_cast (by omega : f0 ≤ f0 + 1 + m)
      exact hf0_gt.trans_le ((chiQuantile_strictMonoOn hc').monotoneOn
        (Set.mem_Ici.mpr (by linarith)) (Set.mem_Ici.mpr (by linarith)) hle)
    have hχ_pos : 0 < chiQuantile c' (f0 + 1 + m : ℕ) := by
      have h14 : (1 / 4 : ℝ) < ((f0 + 1 + m : ℕ) : ℝ) := by
        have : (1 : ℝ) ≤ ((f0 + 1 + m : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ f0 + 1 + m)
        linarith
      exact xiStar_pos.trans (xiStar_lt_chiQuantile hc' h14)
    have ht1 : Real.tanh (π * (x - chiQuantile c' (f0 + 1 + m : ℕ)) / 2) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
      exact ⟨Real.sinh_ne_zero.mpr (by have := Real.pi_pos; nlinarith), (Real.cosh_pos _).ne'⟩
    have ht2 : Real.tanh (π * (x + chiQuantile c' (f0 + 1 + m : ℕ)) / 2) ≠ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh, div_ne_zero_iff]
      exact ⟨(Real.sinh_pos_iff.mpr (by have := Real.pi_pos; positivity)).ne', (Real.cosh_pos _).ne'⟩
    exact sq_pos_of_ne_zero (mul_ne_zero ht1 ht2)
  have hsum_q := (refComb_norm_log_eq_tsum hc' hx hf0_ge le_rfl (by norm_num)
    hgap hf_ne hq_pos).1
  have h_eq : (fun m : ℕ => Real.log (pairModQ c' 0 x (f0 + 1 + m))) =
      fun m : ℕ => 2 * phiVar c' x ((f0 + 1 + m : ℕ) : ℝ) := by
    ext m
    unfold pairModQ phiVar realLogT blaschkeT
    simp only [zero_mul, blaschkePairQ_zero_eps]
    have hc1 : Complex.tanh ((π : ℂ) * ((x : ℂ) - (chiQuantile c' (f0 + 1 + m : ℕ) : ℂ)) / 2) =
        ((Real.tanh (π * (x - chiQuantile c' (f0 + 1 + m : ℕ)) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x - chiQuantile c' (f0 + 1 + m : ℕ)) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x - chiQuantile c' (f0 + 1 + m : ℕ)) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    have hc2 : Complex.tanh ((π : ℂ) * ((x : ℂ) + (chiQuantile c' (f0 + 1 + m : ℕ) : ℂ)) / 2) =
        ((Real.tanh (π * (x + chiQuantile c' (f0 + 1 + m : ℕ)) / 2) : ℝ) : ℂ) := by
      have h1 : Complex.tanh ((π * (x + chiQuantile c' (f0 + 1 + m : ℕ)) / 2 : ℝ) : ℂ) =
          ((Real.tanh (π * (x + chiQuantile c' (f0 + 1 + m : ℕ)) / 2) : ℝ) : ℂ) := by
        rw [Complex.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
          ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, Complex.ofReal_div]
      rw [← h1]; congr 1; push_cast; ring
    rw [hc1, hc2, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs,
      ← sq_abs (Real.tanh _ * Real.tanh _), Real.log_pow]
    push_cast; rfl
  rw [h_eq] at hsum_q
  have hsum_half : Summable (fun m : ℕ => phiVar c' x ((m + (f0 + 1) : ℕ) : ℝ)) := by
    refine (hsum_q.mul_left (1 / 2 : ℝ)).congr fun m => ?_
    calc (1 / 2 : ℝ) * (2 * phiVar c' x ((f0 + 1 + m : ℕ) : ℝ))
        = phiVar c' x ((f0 + 1 + m : ℕ) : ℝ) := by ring
      _ = phiVar c' x ((m + (f0 + 1) : ℕ) : ℝ) := by congr 2; omega
  exact (summable_nat_add_iff (f0 + 1)).mp hsum_half

/-- Continuum limit $D_K^{(f)}(x) \to \log|B^{(f)}(x)| + c' L(x) - c' P^{(f)}(x)$ as $K \to \infty$
(`comb_estimates.tex`, line 154). -/
theorem DK_limit {c' η₀ x : ℝ} (hc' : 0 < c') (hx_xi : xiStar ≤ x)
    {f n : ℕ} (hf : 1 ≤ f) (hn : f + 1 ≤ n) (hη₀0 : 0 ≤ η₀) (hη₀1 : η₀ ≤ 1 / 4)
    (hgap : siteGap c' 1 ≤ 1 / 2) (hx_cell : inCell c' n x)
    (hnz : 0 < η₀ ∨ x ≠ chiQuantile c' n) :
    Tendsto (fun K : ℕ =>
      phiVar c' x f + (∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k)) -
        2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a)
      atTop (𝓝 (Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x - c' * combPf c' f x)) := by
  have hx0 : 0 ≤ x := xiStar_pos.le.trans hx_xi
  have hf_lt_x : chiQuantile c' f < x := by
    have hf14 : (1 / 4 : ℝ) ≤ (f : ℝ) := by
      have : (1 : ℝ) ≤ f := by exact_mod_cast hf
      linarith
    have hfn : (f : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : f < n)
    have hfn14 : (1 / 4 : ℝ) ≤ (n : ℝ) := hf14.trans hfn.le
    exact (chiQuantile_strictMonoOn hc' (Set.mem_Ici.mpr hf14) (Set.mem_Ici.mpr hfn14) hfn).trans_le hx_cell.1
  have hq_pos : ∀ m : ℕ, 0 < pairModQ c' η₀ x (f + 1 + m) := fun m =>
    pairModQ_pos hc' hη₀0 hη₀1 hgap (by omega) hx_cell hnz
  obtain ⟨hsum_q, hlog_B⟩ := refComb_norm_log_eq_tsum hc' hx0 hf hη₀0 hη₀1 hgap hf_lt_x.ne hq_pos
  have hsum_tend : Tendsto (fun K : ℕ =>
      phiVar c' x f + ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k))
      atTop (𝓝 (Real.log ‖refComb c' f η₀ (x : ℂ)‖)) := by
    rw [hlog_B]
    refine tendsto_const_nhds.add ?_
    have hts := hsum_q.hasSum.tendsto_sum_nat
    have h_shift : ∀ K ≥ f,
        ∑ k ∈ Finset.Icc (f + 1) K, Real.log (pairModQ c' η₀ x k) =
          ∑ m ∈ Finset.range (K - f), Real.log (pairModQ c' η₀ x (f + 1 + m)) := by
      intro K hK
      have h_eq : Finset.Icc (f + 1) K = (Finset.range (K - f)).image (fun m => f + 1 + m) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨k - (f + 1), by omega, by omega⟩
        · rintro ⟨m, hm, rfl⟩; omega
      rw [h_eq, Finset.sum_image (fun a _ b _ h => by omega)]
    have hts2 : Tendsto (fun K : ℕ => ∑ m ∈ Finset.range (K - f),
        Real.log (pairModQ c' η₀ x (f + 1 + m))) atTop
        (𝓝 (∑' m : ℕ, Real.log (pairModQ c' η₀ x (f + 1 + m)))) :=
      hts.comp (tendsto_atTop_atTop.mpr fun N => ⟨N + f, fun K hK => by omega⟩)
    exact hts2.congr' (by filter_upwards [eventually_ge_atTop f] with K hK; exact (h_shift K hK).symm)
  obtain ⟨_, hint_14, _, _, hriesz⟩ := riesz_real_identities hc' hx0 f hf
  have h_riesz_f := (hriesz hx_xi).2
  have hint_f : IntegrableOn (phiVar c' x) (Ioi (f : ℝ)) volume := by
    refine hint_14.mono_set (Ioi_subset_Ioi ?_)
    have : (1 : ℝ) ≤ f := by exact_mod_cast hf
    linarith
  have h_int_tend : Tendsto (fun K : ℕ => 2 * ∫ a in (f : ℝ)..((K : ℝ) + 1 / 2), phiVar c' x a)
      atTop (𝓝 (-c' * slitL x + c' * combPf c' f x)) := by
    rw [← h_riesz_f]
    refine tendsto_const_nhds.mul ?_
    have htop : Tendsto (fun K : ℕ => (K : ℝ) + 1 / 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    exact intervalIntegral_tendsto_integral_Ioi (f : ℝ) hint_f htop
  rw [show Real.log ‖refComb c' f η₀ (x : ℂ)‖ + c' * slitL x - c' * combPf c' f x =
      Real.log ‖refComb c' f η₀ (x : ℂ)‖ - (-c' * slitL x + c' * combPf c' f x) by ring]
  exact hsum_tend.sub h_int_tend

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.midpoint_peano_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.midpoint_peano_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.trapezoid_peano_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.trapezoid_peano_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.chiDeriv_div_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.chiDeriv_div_le

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.phiVarSecond_le_G' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.phiVarSecond_le_G

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.refComb_norm_log_eq_tsum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.refComb_norm_log_eq_tsum

/-- info: 'FormalResearch.ModularBootstrap.Upper.Holes.DK_limit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Upper.Holes.DK_limit

end FormalResearch.ModularBootstrap.Upper.Holes

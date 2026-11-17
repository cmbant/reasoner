module

public import Mathlib

/-!
# Fejér–Riesz inequality on the disc (elementary proof)

Generic complex analysis, no Airy content.  **Proved.**

`FormalResearch.Hardy.fejerRiesz_disc`: if `h` is holomorphic on the open unit disc and continuous on its closure
(`DiffContOnCl ℂ h (ball 0 1)`), then

`∫_{-1}^{1} ‖h(x)‖ dx ≤ (1/2) ∫_{-π}^{π} ‖h(e^{iθ})‖ dθ`.

This is the classical Fejér–Riesz inequality for `H¹` (Duren, *Theory of H^p spaces*, Thm 3.13) in the case of a function
continuous on the closed disc.  It is not in Mathlib (no Hardy spaces).  The proof is the original Fejér–Riesz argument,
with no Hilbert inequality and no Parseval identity:

1. *Fixed radius `s < 1` with no zero of `h` on `|z| = s`* (`fr_radius`): `MeromorphicOn.extract_zeros_poles` writes
   `h = P g` on `|z| ≤ s` with `P = ∏ (z - w)^{m_w}` (finitely many zeros `w`, all in the open disc) and `g` zero-free.
   With `P̃ = ∏ ((s² - w̄ z)/s)^{m_w}` one has `|P| ≤ |P̃|` on `|z| ≤ s` and `|P| = |P̃|` on `|z| = s` (the identity
   `|s² - w̄z|² - s²|z - w|² = (s² - |w|²)(s² - |z|²)`); so `H₁ = g P̃` is zero-free with `|h| ≤ |H₁|`, equality on the circle.
2. *Zero-free case* (`fr_zeroFree`): `H₁ = r²` with `r` holomorphic (`exists_sq_eq_ball`), `Q(z) = r(z) \overline{r(\bar z)}` is
   holomorphic with `Q(x) = |H₁(x)|` for real `x`; a primitive `F` of `Q` gives `∫_{-s}^s |H₁| = F(s) - F(-s)` and, along the
   upper semicircle, `= -∫_0^π Q(se^{iθ}) i s e^{iθ} dθ`, which is `≤ (s/2)∫_{-π}^{π}|H₁(se^{iθ})|dθ` by `ab ≤ (a²+b²)/2`.
3. `s → 1` along good radii (all but finitely many radii in a compact range are good), by dominated convergence
   (uniform continuity on the closed disc).
-/

@[expose] public section

open Complex Metric Set Filter Topology MeasureTheory intervalIntegral MeromorphicOn
open scoped Real

namespace FormalResearch.Hardy

/-- identity: for `|w| < s`, `|z| ≤ s`: `s² |z - w|² ≤ |s² - conj w z|²`. -/
lemma sq_norm_sub_le_blaschke {s : ℝ} {w z : ℂ} (hw : ‖w‖ ≤ s) (hz : ‖z‖ ≤ s) :
    s ^ 2 * ‖z - w‖ ^ 2 ≤ ‖(s : ℂ) ^ 2 - (starRingEnd ℂ) w * z‖ ^ 2 := by
  have key : ‖(s : ℂ) ^ 2 - (starRingEnd ℂ) w * z‖ ^ 2 - s ^ 2 * ‖z - w‖ ^ 2
      = (s ^ 2 - ‖w‖ ^ 2) * (s ^ 2 - ‖z‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have h1 : 0 ≤ s ^ 2 - ‖w‖ ^ 2 := by nlinarith [norm_nonneg w]
  have h2 : 0 ≤ s ^ 2 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
  nlinarith [mul_nonneg h1 h2]

lemma sq_norm_sub_eq_blaschke {s : ℝ} {w z : ℂ} (hz : ‖z‖ = s) :
    s ^ 2 * ‖z - w‖ ^ 2 = ‖(s : ℂ) ^ 2 - (starRingEnd ℂ) w * z‖ ^ 2 := by
  have : ‖(s : ℂ) ^ 2 - (starRingEnd ℂ) w * z‖ ^ 2 - s ^ 2 * ‖z - w‖ ^ 2
      = (s ^ 2 - ‖w‖ ^ 2) * (s ^ 2 - ‖z‖ ^ 2) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, ← Complex.ofReal_pow, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hz] at this
  nlinarith


lemma exists_zeroFree_majorant {s : ℝ} (hs : 0 < s) {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 s)) (hsph : ∀ z ∈ sphere (0 : ℂ) s, h z ≠ 0) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (closedBall 0 s) ∧ (∀ z ∈ closedBall (0 : ℂ) s, H z ≠ 0) ∧
      (∀ z ∈ closedBall (0 : ℂ) s, ‖h z‖ ≤ ‖H z‖) ∧ (∀ z ∈ sphere (0 : ℂ) s, ‖h z‖ = ‖H z‖) := by
  classical
  set U : Set ℂ := closedBall 0 s with hU
  have hmer : MeromorphicOn h U := hh.meromorphicOn
  have hconn : IsPreconnected U := (convex_closedBall (0 : ℂ) s).isPreconnected
  have hsU : (s : ℂ) ∈ U := by simp [hU, abs_of_pos hs]
  have hsS : (s : ℂ) ∈ sphere (0 : ℂ) s := by simp [abs_of_pos hs]
  have hord : ∀ u : U, meromorphicOrderAt h u ≠ ⊤ := by
    rintro ⟨u, hu⟩
    refine hmer.meromorphicOrderAt_ne_top_of_isPreconnected hconn hsU hu ?_
    rw [(hh s hsU).meromorphicOrderAt_eq]
    have : analyticOrderAt h s = 0 := (hh s hsU).analyticOrderAt_eq_zero.2 (hsph _ hsS)
    simp [this]
  have hfin : (divisor h U).support.Finite := (divisor h U).finiteSupport (isCompact_closedBall 0 s)
  obtain ⟨g, hg, hg0, hgeq⟩ := hmer.extract_zeros_poles hord hfin
  set D := divisor h U with hD
  have hDnn : 0 ≤ D := hh.divisor_nonneg
  set S : Finset ℂ := hfin.toFinset with hS
  have hSsub : ∀ u ∈ S, ‖u‖ < s ∧ 0 < D u := by
    intro u hu
    have hu' : u ∈ D.support := by simpa [hS] using hu
    have huU : u ∈ U := D.supportWithinDomain hu'
    have hDu : D u ≠ 0 := hu'
    have hDpos : 0 < D u := lt_of_le_of_ne (hDnn u) (Ne.symm hDu)
    have hz : h u = 0 := by
      by_contra hne
      have : analyticOrderAt h u = 0 := (hh u huU).analyticOrderAt_eq_zero.2 hne
      have h2 : D u = 0 := by
        rw [hD, divisor_apply hmer huU, (hh u huU).meromorphicOrderAt_eq, this]; simp
      exact hDu h2
    refine ⟨?_, hDpos⟩
    have hle : ‖u‖ ≤ s := by simpa [hU] using huU
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd hz (hsph u (by simpa [mem_sphere_zero_iff_norm, abs_of_pos hs] using heq))
  set m : ℂ → ℕ := fun u => (D u).toNat with hm
  have hmD : ∀ u ∈ S, (D u : ℤ) = (m u : ℤ) := fun u hu => by
    simp [hm, Int.toNat_of_nonneg (hDnn u)]
  have hprod : ∀ z : ℂ, (∏ᶠ u, (fun x : ℂ => x - u) ^ D u) z = ∏ u ∈ S, (z - u) ^ m u := by
    intro z
    have hsub : Function.mulSupport (fun u : ℂ => (fun x : ℂ => x - u) ^ D u) ⊆ ↑S := by
      intro u hu
      have : D u ≠ 0 := by
        intro h0
        apply hu
        simp [h0]
      simpa [hS] using this
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, Finset.prod_apply]
    refine Finset.prod_congr rfl fun u hu => ?_
    simp only [Pi.pow_apply]
    rw [hmD u hu, zpow_natCast]
  have hSan : ∀ u ∈ S, AnalyticOnNhd ℂ (fun z : ℂ => (z - u) ^ m u) U := fun u _ z _ => by fun_prop
  have hFan : AnalyticOnNhd ℂ (fun z : ℂ => (∏ u ∈ S, (z - u) ^ m u) * g z) U := by
    intro z hz
    have h1 : AnalyticAt ℂ (fun z : ℂ => ∏ u ∈ S, (z - u) ^ m u) z :=
      Finset.analyticAt_fun_prod S fun u _ => by fun_prop
    exact h1.mul (hg z hz)
  have h0U : (0 : ℂ) ∈ U := by simp [hU, hs.le]
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), h z = (∏ u ∈ S, (z - u) ^ m u) * g z := by
    have h1 := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hgeq 0 h0U
    have h2 : U ∈ 𝓝[≠] (0 : ℂ) := mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds 0 hs)
    have h3 := Filter.inter_mem h1 h2
    refine Filter.Eventually.frequently ?_
    filter_upwards [h3] with z hz
    rcases hz with ⟨hz1, hz2⟩
    rcases hz1 with hz1 | hz1
    · have : h z = ((∏ᶠ u, (fun x : ℂ => x - u) ^ D u) • g) z := hz1
      rw [this]
      show (∏ᶠ u, (fun x : ℂ => x - u) ^ D u) z • g z = _
      rw [smul_eq_mul, hprod]
    · exact absurd hz2 hz1
  have hpt : ∀ z ∈ U, h z = (∏ u ∈ S, (z - u) ^ m u) * g z :=
    fun z hz => hh.eqOn_of_preconnected_of_frequently_eq hFan hconn h0U hfreq hz
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hfac : ∀ u ∈ S, ∀ z ∈ U, ((s : ℂ) ^ 2 - (starRingEnd ℂ) u * z) ≠ 0 := by
    intro u hu z hz hzero
    have hu1 := (hSsub u hu).1
    have hz1 : ‖z‖ ≤ s := by simpa [hU] using hz
    have h1 : ‖(starRingEnd ℂ) u * z‖ = ‖u‖ * ‖z‖ := by rw [norm_mul, Complex.norm_conj]
    have h2 : (starRingEnd ℂ) u * z = (s : ℂ) ^ 2 := by linear_combination -hzero
    have h3 : ‖(starRingEnd ℂ) u * z‖ = s ^ 2 := by
      rw [h2]; simp [abs_of_pos hs]
    rw [h1] at h3
    nlinarith [norm_nonneg u, norm_nonneg z]
  refine ⟨fun z => g z * ∏ u ∈ S, (((s : ℂ) ^ 2 - (starRingEnd ℂ) u * z) / s) ^ m u, ?_, ?_, ?_, ?_⟩
  · intro z hz
    refine (hg z hz).mul ?_
    exact Finset.analyticAt_fun_prod S fun u _ => by fun_prop
  · intro z hz
    refine mul_ne_zero (hg0 ⟨z, hz⟩) (Finset.prod_ne_zero_iff.2 fun u hu => ?_)
    exact pow_ne_zero _ (div_ne_zero (hfac u hu z hz) hs0)
  · intro z hz
    rw [hpt z hz, norm_mul, norm_mul, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [norm_prod, norm_prod]
    refine Finset.prod_le_prod₀ (fun u _ => ?_) (fun u hu => ?_)
    · exact norm_nonneg _
    rw [norm_pow, norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have hz1 : ‖z‖ ≤ s := by simpa [hU] using hz
    have hu1 := (hSsub u hu).1.le
    have := sq_norm_sub_le_blaschke hu1 hz1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, le_div_iff₀ hs]
    have h4 : (‖z - u‖ * s) ^ 2 ≤ ‖(s : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by nlinarith
    exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).1 h4
  · intro z hz
    have hz1 : ‖z‖ = s := by simpa [mem_sphere_zero_iff_norm, abs_of_pos hs] using hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    rw [hpt z hzU, norm_mul, norm_mul, mul_comm]
    congr 1
    rw [norm_prod, norm_prod]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [norm_pow, norm_pow]
    congr 1
    have := sq_norm_sub_eq_blaschke (w := u) hz1
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hs.le, eq_div_iff hs.ne']
    have h4 : (‖z - u‖ * s) ^ 2 = ‖(s : ℂ) ^ 2 - (starRingEnd ℂ) u * z‖ ^ 2 := by nlinarith
    exact (sq_eq_sq₀ (by positivity) (norm_nonneg _)).1 h4


/-- A zero-free holomorphic function on a disc has a holomorphic square root. -/
lemma exists_sq_eq_ball {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 R))
    (hne : ∀ w ∈ ball (0 : ℂ) R, g w ≠ 0) :
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r (ball 0 R) ∧ ∀ w ∈ ball (0 : ℂ) R, r w ^ 2 = g w := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR
  have hq : DifferentiableOn ℂ (fun w => deriv g w / g w) (ball 0 R) :=
    (hg.deriv isOpen_ball).div hg hne
  obtain ⟨L, hL0, hL⟩ := (hq.isExactOn_ball).with_val_at 0 (Complex.log (g 0))
  have hLd : DifferentiableOn ℂ L (ball 0 R) := fun w hw => (hL w hw).differentiableAt.differentiableWithinAt
  have hu : DifferentiableOn ℂ (fun w => cexp (L w) / g w) (ball 0 R) := hLd.cexp.div hg hne
  have hderiv : (ball (0 : ℂ) R).EqOn (deriv (fun w => cexp (L w) / g w)) 0 := by
    intro w hw
    have h1 : HasDerivAt L (deriv g w / g w) w := hL w hw
    have h2 : HasDerivAt g (deriv g w) w := (hg.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
    have h3 := (h1.cexp).div h2 (hne w hw)
    have h4 : deriv (fun w => cexp (L w) / g w) w = _ := h3.deriv
    rw [h4]
    have := hne w hw
    simp only [Pi.zero_apply]
    field_simp
    ring
  have hconst : ∀ w ∈ ball (0 : ℂ) R, cexp (L w) = g w := by
    intro w hw
    have hw' := (Metric.isOpen_ball : IsOpen (ball (0 : ℂ) R)).is_const_of_deriv_eq_zero
      (convex_ball _ _).isPreconnected hu hderiv hw h0
    simp only [hL0, Complex.exp_log (hne 0 h0)] at hw'
    have := hne 0 h0
    have hgw := hne w hw
    field_simp at hw'
    rw [hw']
  refine ⟨fun w => cexp (L w / 2), ?_, fun w hw => ?_⟩
  · exact (hLd.div_const 2).cexp
  · rw [← Complex.exp_nat_mul]
    have : ((2 : ℕ) : ℂ) * (L w / 2) = L w := by push_cast; ring
    rw [this, hconst w hw]

/-- A function holomorphic and zero-free near a compact ball is so on a larger open ball. -/
lemma exists_larger_ball {s : ℝ} (hs : 0 < s) {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H (closedBall 0 s))
    (hne : ∀ z ∈ closedBall (0 : ℂ) s, H z ≠ 0) :
    ∃ s' : ℝ, s < s' ∧ DifferentiableOn ℂ H (ball 0 s') ∧ ∀ z ∈ ball (0 : ℂ) s', H z ≠ 0 := by
  set W : Set ℂ := {z | AnalyticAt ℂ H z ∧ H z ≠ 0} with hW
  have hWn : ∀ z ∈ closedBall (0 : ℂ) s, W ∈ 𝓝 z := by
    intro z hz
    have h1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ H w := (hH z hz).eventually_analyticAt
    have h2 : ∀ᶠ w in 𝓝 z, H w ≠ 0 := (hH z hz).continuousAt.eventually_ne (hne z hz)
    filter_upwards [h1, h2] with w hw1 hw2 using ⟨hw1, hw2⟩
  have hsub : closedBall (0 : ℂ) s ⊆ interior W := fun z hz => mem_interior_iff_mem_nhds.2 (hWn z hz)
  obtain ⟨δ, hδ, hthick⟩ := (isCompact_closedBall (0 : ℂ) s).exists_thickening_subset_open
    isOpen_interior hsub
  have hb : ball (0 : ℂ) (s + δ) ⊆ W := by
    intro z hz
    refine interior_subset (hthick ?_)
    rw [Metric.mem_thickening_iff]
    have hz' : ‖z‖ < s + δ := by simpa using hz
    by_cases hzs : ‖z‖ ≤ s
    · exact ⟨z, by simpa using hzs, by simpa using hδ⟩
    · have hzs := not_le.1 hzs
      refine ⟨((s / ‖z‖ : ℝ) : ℂ) * z, ?_, ?_⟩
      · have hzpos : 0 < ‖z‖ := by linarith
        simp only [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]
        field_simp
        exact le_refl _
      · have hzpos : 0 < ‖z‖ := by linarith
        rw [dist_eq_norm]
        have : z - ((s / ‖z‖ : ℝ) : ℂ) * z = ((1 - s / ‖z‖ : ℝ) : ℂ) * z := by push_cast; ring
        rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
        · have : (1 - s / ‖z‖) * ‖z‖ = ‖z‖ - s := by field_simp
          rw [this]; linarith
        · have : s / ‖z‖ ≤ 1 := by rw [div_le_one hzpos]; exact hzs.le
          linarith
  refine ⟨s + δ, by linarith, ?_, fun z hz => (hb hz).2⟩
  exact fun z hz => (hb hz).1.differentiableAt.differentiableWithinAt


lemma norm_circleMap_zero_pos {s : ℝ} (hs : 0 < s) (θ : ℝ) : ‖circleMap 0 s θ‖ = s := by
  rw [norm_circleMap_zero, abs_of_pos hs]

lemma conj_circleMap (s θ : ℝ) :
    starRingEnd ℂ (circleMap 0 s θ) = circleMap 0 s (-θ) := by
  simp [circleMap, ← Complex.exp_conj, mul_comm, Complex.conj_ofReal]

/-- Fejér–Riesz at a fixed radius for a zero-free function. -/
lemma fr_zeroFree {s s' : ℝ} (hs : 0 < s) (hss : s < s') {H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (ball 0 s')) (hne : ∀ z ∈ ball (0 : ℂ) s', H z ≠ 0) :
    ∫ x in (-s)..s, ‖H (x : ℂ)‖ ≤ (s / 2) * ∫ θ in (-π)..π, ‖H (circleMap 0 s θ)‖ := by
  obtain ⟨r, hr, hr2⟩ := exists_sq_eq_ball (by linarith) hH hne
  set rr : ℂ → ℂ := fun z => starRingEnd ℂ (r (starRingEnd ℂ z)) with hrr
  have hrrd : DifferentiableOn ℂ rr (ball 0 s') := by
    intro z hz
    have hz' : starRingEnd ℂ z ∈ ball (0 : ℂ) s' := by simpa using hz
    have := (hr.differentiableAt (isOpen_ball.mem_nhds hz')).conj_conj
    simp only [Complex.conj_conj] at this
    exact this.differentiableWithinAt
  set Q : ℂ → ℂ := fun z => r z * rr z with hQ
  have hQd : DifferentiableOn ℂ Q (ball 0 s') := hr.mul hrrd
  obtain ⟨F, hF⟩ := hQd.isExactOn_ball
  have hball : ∀ z : ℂ, ‖z‖ ≤ s → z ∈ ball (0 : ℂ) s' := fun z hz => by
    rw [mem_ball_zero_iff]; linarith
  -- real axis
  have hnr : ∀ z ∈ ball (0 : ℂ) s', ‖r z‖ ^ 2 = ‖H z‖ := fun z hz => by
    rw [← norm_pow, hr2 z hz]
  have hQreal : ∀ x : ℝ, |x| ≤ s → Q (x : ℂ) = ((‖H (x : ℂ)‖ : ℝ) : ℂ) := by
    intro x hx
    have hxb : (x : ℂ) ∈ ball (0 : ℂ) s' := hball _ (by simpa using hx)
    simp only [hQ, hrr, Complex.conj_ofReal]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hnr _ hxb]
  -- FTC on the diameter
  have hdiam : ∫ x in (-s)..s, Q (x : ℂ) = F (s : ℂ) - F ((-s : ℝ) : ℂ) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => F (x : ℂ)) (f' := fun x : ℝ => Q (x : ℂ))
      (fun x hx => ?_) ?_
    · rw [Set.uIcc_of_le (by linarith)] at hx
      exact (hF _ (hball _ (by simpa [abs_le] using hx))).comp_ofReal
    · refine (hQd.continuousOn.comp Complex.continuous_ofReal.continuousOn ?_).intervalIntegrable
      intro x hx
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact hball _ (by simpa [abs_le] using hx)
  -- FTC on the upper semicircle
  have harc : ∫ θ in (0 : ℝ)..π, (circleMap 0 s θ * I) * Q (circleMap 0 s θ) =
      F (circleMap 0 s π) - F (circleMap 0 s 0) := by
    refine integral_eq_sub_of_hasDerivAt (f := fun θ : ℝ => F (circleMap 0 s θ))
      (f' := fun θ : ℝ => (circleMap 0 s θ * I) * Q (circleMap 0 s θ)) (fun θ _ => ?_) ?_
    · have := (hF (circleMap 0 s θ) (hball _ (norm_circleMap_zero_pos hs θ).le)).scomp θ
        (hasDerivAt_circleMap 0 s θ)
      rw [smul_eq_mul] at this
      exact this
    · refine Continuous.intervalIntegrable ?_ _ _
      have hc : Continuous (circleMap 0 s) := continuous_circleMap 0 s
      have hQc : Continuous (fun θ : ℝ => Q (circleMap 0 s θ)) :=
        hQd.continuousOn.comp_continuous hc (fun θ => hball _ (norm_circleMap_zero_pos hs θ).le)
      exact (hc.mul continuous_const).mul hQc
  have hπ : circleMap 0 s π = ((-s : ℝ) : ℂ) := by simp [circleMap]
  have h0 : circleMap 0 s 0 = (s : ℂ) := by simp [circleMap]
  rw [hπ, h0] at harc
  -- continuity of the circle integrands
  have hc : Continuous (circleMap 0 s) := continuous_circleMap 0 s
  have hcb : ∀ θ, circleMap 0 s θ ∈ ball (0 : ℂ) s' := fun θ => hball _ (norm_circleMap_zero_pos hs θ).le
  have hHc : Continuous (fun θ : ℝ => ‖H (circleMap 0 s θ)‖) :=
    (hH.continuousOn.comp_continuous hc hcb).norm
  have hHc' : Continuous (fun θ : ℝ => ‖H (circleMap 0 s (-θ))‖) :=
    (hH.continuousOn.comp_continuous (hc.comp continuous_neg) (fun θ => hcb _)).norm
  -- the real integral
  set I₀ : ℝ := ∫ x in (-s)..s, ‖H (x : ℂ)‖ with hI₀
  have hI₀nn : 0 ≤ I₀ := intervalIntegral.integral_nonneg (by linarith) (fun _ _ => norm_nonneg _)
  have hcast : (I₀ : ℂ) = -(∫ θ in (0 : ℝ)..π, (circleMap 0 s θ * I) * Q (circleMap 0 s θ)) := by
    rw [harc, hI₀, ← intervalIntegral.integral_ofReal]
    have : ∫ x in (-s)..s, ((‖H (x : ℂ)‖ : ℝ) : ℂ) = ∫ x in (-s)..s, Q (x : ℂ) := by
      refine intervalIntegral.integral_congr (fun x hx => ?_)
      rw [Set.uIcc_of_le (by linarith)] at hx
      exact (hQreal x (abs_le.2 hx)).symm
    rw [this, hdiam]; ring
  have h1 : I₀ = ‖∫ θ in (0 : ℝ)..π, (circleMap 0 s θ * I) * Q (circleMap 0 s θ)‖ := by
    have := congrArg norm hcast
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg hI₀nn] at this
    exact this
  have h2 : ‖∫ θ in (0 : ℝ)..π, (circleMap 0 s θ * I) * Q (circleMap 0 s θ)‖ ≤
      ∫ θ in (0 : ℝ)..π, (s / 2) * (‖H (circleMap 0 s θ)‖ + ‖H (circleMap 0 s (-θ))‖) := by
    refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
    refine intervalIntegral.integral_mono_on Real.pi_pos.le ?_ ?_ (fun θ _ => ?_)
    · refine Continuous.intervalIntegrable ?_ _ _
      have hQc : Continuous (fun θ : ℝ => Q (circleMap 0 s θ)) :=
        hQd.continuousOn.comp_continuous hc (fun θ => hcb θ)
      exact ((hc.mul continuous_const).mul hQc).norm
    · exact (continuous_const.mul (hHc.add hHc')).intervalIntegrable _ _
    · have hn1 : ‖circleMap 0 s θ‖ = s := norm_circleMap_zero_pos hs θ
      have hn2 : ‖rr (circleMap 0 s θ)‖ = ‖r (circleMap 0 s (-θ))‖ := by
        simp only [hrr, Complex.norm_conj, conj_circleMap]
      simp only [hQ, norm_mul, hn1, Complex.norm_I, mul_one, hn2]
      have e1 := hnr _ (hcb θ)
      have e2 := hnr _ (hcb (-θ))
      nlinarith [sq_nonneg (‖r (circleMap 0 s θ)‖ - ‖r (circleMap 0 s (-θ))‖), hs]
  have h3 : ∫ θ in (0 : ℝ)..π, (s / 2) * (‖H (circleMap 0 s θ)‖ + ‖H (circleMap 0 s (-θ))‖) =
      (s / 2) * ∫ θ in (-π)..π, ‖H (circleMap 0 s θ)‖ := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hHc.intervalIntegrable _ _)
      (hHc'.intervalIntegrable _ _), intervalIntegral.integral_comp_neg (fun θ => ‖H (circleMap 0 s θ)‖)]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hHc.intervalIntegrable (-π) 0)
      (hHc.intervalIntegrable 0 π)]
    simp only [neg_zero]
    ring
  linarith

/-- **Fejér–Riesz at a fixed radius**, for `h` holomorphic near `|z| ≤ s` without zeros on `|z| = s`. -/
lemma fr_radius {s : ℝ} (hs : 0 < s) {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 s))
    (hsph : ∀ z ∈ sphere (0 : ℂ) s, h z ≠ 0) :
    ∫ x in (-s)..s, ‖h (x : ℂ)‖ ≤ (s / 2) * ∫ θ in (-π)..π, ‖h (circleMap 0 s θ)‖ := by
  obtain ⟨H, hHan, hHne, hle, heq⟩ := exists_zeroFree_majorant hs hh hsph
  obtain ⟨s', hss', hHd, hHne'⟩ := exists_larger_ball hs hHan hHne
  have key := fr_zeroFree hs hss' hHd hHne'
  have hmem : ∀ x : ℝ, x ∈ Set.uIcc (-s) s → (x : ℂ) ∈ closedBall (0 : ℂ) s := fun x hx => by
    rw [Set.uIcc_of_le (by linarith)] at hx
    simpa [abs_le] using hx
  have hmemc : ∀ θ : ℝ, circleMap 0 s θ ∈ closedBall (0 : ℂ) s := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere 0 hs.le θ)
  have hcont : ∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall 0 s) →
      IntervalIntegrable (fun x : ℝ => ‖g (x : ℂ)‖) volume (-s) s := fun g hg =>
    ((hg.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun x hx => hmem x
      (by rw [Set.uIcc_of_le (by linarith)]; exact hx))).norm).intervalIntegrable_of_Icc (by linarith)
  have h1 : ∫ x in (-s)..s, ‖h (x : ℂ)‖ ≤ ∫ x in (-s)..s, ‖H (x : ℂ)‖ := by
    refine intervalIntegral.integral_mono_on (by linarith) (hcont h hh) (hcont H hHan) fun x hx => ?_
    exact hle _ (hmem x (by rw [Set.uIcc_of_le (by linarith)]; exact hx))
  have h2 : ∫ θ in (-π)..π, ‖H (circleMap 0 s θ)‖ = ∫ θ in (-π)..π, ‖h (circleMap 0 s θ)‖ := by
    refine intervalIntegral.integral_congr fun θ _ => ?_
    exact (heq _ (circleMap_mem_sphere 0 hs.le θ)).symm
  rw [← h2]
  exact h1.trans key

/-- The set of moduli of zeros in a closed disc `|z| ≤ t < 1` of a function holomorphic on the unit disc and not
identically zero is finite. -/
lemma finite_zero_norms {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (ball 0 1)) (hne : ∃ z ∈ ball (0 : ℂ) 1, h z ≠ 0)
    {t : ℝ} (ht : t < 1) :
    {r : ℝ | ∃ z : ℂ, ‖z‖ = r ∧ ‖z‖ ≤ t ∧ h z = 0}.Finite := by
  classical
  obtain ⟨z₀, hz₀, hz₀ne⟩ := hne
  set U : Set ℂ := closedBall 0 t with hU
  have hUb : U ⊆ ball 0 1 := fun z hz => by
    simp only [hU, mem_closedBall, dist_zero_right] at hz
    simp only [mem_ball, dist_zero_right]; linarith
  have hmer : MeromorphicOn h U := (hh.mono hUb).meromorphicOn
  have hmerB : MeromorphicOn h (ball 0 1) := hh.meromorphicOn
  have hord : ∀ u ∈ U, meromorphicOrderAt h u ≠ ⊤ := by
    intro u hu
    refine hmerB.meromorphicOrderAt_ne_top_of_isPreconnected (convex_ball (0 : ℂ) 1).isPreconnected hz₀
      (hUb hu) ?_
    rw [(hh z₀ hz₀).meromorphicOrderAt_eq]
    have : analyticOrderAt h z₀ = 0 := (hh z₀ hz₀).analyticOrderAt_eq_zero.2 hz₀ne
    simp [this]
  have hfin : (divisor h U).support.Finite := (divisor h U).finiteSupport (isCompact_closedBall 0 t)
  refine (hfin.image (fun z : ℂ => ‖z‖)).subset ?_
  rintro r ⟨z, rfl, hzt, hz0⟩
  refine ⟨z, ?_, rfl⟩
  have hzU : z ∈ U := by simpa [hU] using hzt
  have han := hh z (hUb hzU)
  have : analyticOrderAt h z ≠ 0 := fun h0 => by
    have := (han.analyticOrderAt_eq_zero).1 h0
    exact this hz0
  simp only [Function.mem_support, ne_eq, divisor_apply hmer hzU, han.meromorphicOrderAt_eq]
  have hne' : meromorphicOrderAt h z ≠ ⊤ := hord z hzU
  rw [han.meromorphicOrderAt_eq] at hne'
  intro h0
  apply this
  generalize analyticOrderAt h z = n at hne' h0 ⊢
  induction n using ENat.recTopCoe with
  | top => exact absurd rfl hne'
  | coe n => simpa using h0

/-- **Fejér–Riesz inequality on the unit disc** for `h` holomorphic in the open disc and continuous on the closed disc. -/
theorem fejerRiesz_disc {h : ℂ → ℂ} (hh : DiffContOnCl ℂ h (ball 0 1)) :
    ∫ x in (-1 : ℝ)..1, ‖h (x : ℂ)‖ ≤ (1 / 2) * ∫ θ in (-π)..π, ‖h (circleMap 0 1 θ)‖ := by
  classical
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hcont : ContinuousOn h (closedBall 0 1) := hcl ▸ hh.continuousOn
  have han : AnalyticOnNhd ℂ h (ball 0 1) := hh.differentiableOn.analyticOnNhd isOpen_ball
  by_cases hz : ∀ z ∈ ball (0 : ℂ) 1, h z = 0
  · have h0 : ∀ z ∈ closedBall (0 : ℂ) 1, h z = 0 := by
      intro z hz'
      have : EqOn h 0 (ball (0 : ℂ) 1) := fun w hw => hz w hw
      exact this.of_subset_closure hcont continuousOn_const ball_subset_closedBall
        (by rw [closure_ball 0 one_ne_zero]) hz'

    have e1 : ∀ x : ℝ, x ∈ Set.uIcc (-1 : ℝ) 1 → ‖h (x : ℂ)‖ = 0 := fun x hx => by
      rw [Set.uIcc_of_le (by norm_num)] at hx
      rw [h0 _ (by simpa [abs_le] using hx)]; simp
    have e2 : ∀ θ : ℝ, ‖h (circleMap 0 1 θ)‖ = 0 := fun θ => by
      rw [h0 _ (sphere_subset_closedBall (circleMap_mem_sphere 0 zero_le_one θ))]; simp
    rw [intervalIntegral.integral_congr e1]
    simp [e2]
  push Not at hz
  -- good radii
  have hgood : ∀ k : ℕ, ∃ s : ℝ, 1 - 1 / ((k : ℝ) + 1) < s ∧ s < 1 - 1 / ((k : ℝ) + 2) ∧
      ∀ z : ℂ, ‖z‖ = s → h z ≠ 0 := by
    intro k
    have hk2 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hk3 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have hab : 1 - 1 / ((k : ℝ) + 1) < 1 - 1 / ((k : ℝ) + 2) := by
      have : 1 / ((k : ℝ) + 2) < 1 / ((k : ℝ) + 1) := one_div_lt_one_div_of_lt hk2 (by linarith)
      linarith
    have ht : 1 - 1 / ((k : ℝ) + 2) < 1 := by
      have : 0 < 1 / ((k : ℝ) + 2) := by positivity
      linarith
    have hF := finite_zero_norms han hz ht
    obtain ⟨s, hs, hsF⟩ := (Set.Ioo_infinite hab).exists_notMem_finite hF
    refine ⟨s, hs.1, hs.2, fun z hzs hz0 => hsF ⟨z, hzs, ?_, hz0⟩⟩
    rw [hzs]; exact hs.2.le
  choose s hs1 hs2 hsg using hgood
  have hspos : ∀ k, 0 < s k := fun k => by
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    linarith [hs1 k]
  have hslt : ∀ k, s k < 1 := fun k => by
    have : 0 < 1 / ((k : ℝ) + 2) := by positivity
    linarith [hs2 k]
  have hstend : Tendsto s atTop (𝓝 1) := by
    have h1 : Tendsto (fun k : ℕ => 1 - 1 / ((k : ℝ) + 1)) atTop (𝓝 1) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds (fun k => (hs1 k).le)
      (fun k => (hslt k).le)
  -- the inequalities at each radius
  have hineq : ∀ k, ∫ x in (-(s k))..(s k), ‖h (x : ℂ)‖ ≤
      (s k / 2) * ∫ θ in (-π)..π, ‖h (circleMap 0 (s k) θ)‖ := by
    intro k
    have hb : closedBall (0 : ℂ) (s k) ⊆ ball 0 1 := fun z hz => by
      simp only [mem_closedBall, dist_zero_right] at hz
      simp only [mem_ball, dist_zero_right]; linarith [hslt k]
    refine fr_radius (hspos k) (han.mono hb) (fun z hzs => hsg k z ?_)
    simpa [mem_sphere_zero_iff_norm] using hzs
  -- bound of h on the closed disc
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn hcont
  -- convergence of the circle integrals
  have hC : Tendsto (fun k => ∫ θ in (-π)..π, ‖h (circleMap 0 (s k) θ)‖) atTop
      (𝓝 (∫ θ in (-π)..π, ‖h (circleMap 0 1 θ)‖)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun k => ?_
      exact (hcont.comp_continuous (continuous_circleMap 0 (s k)) (fun θ =>
        by simpa [mem_closedBall, norm_circleMap_zero, abs_of_pos (hspos k)] using (hslt k).le)).norm.aestronglyMeasurable
    · refine Eventually.of_forall fun k => Eventually.of_forall fun θ _ => ?_
      have := hM (circleMap 0 (s k) θ)
        (by simpa [mem_closedBall, norm_circleMap_zero, abs_of_pos (hspos k)] using (hslt k).le)
      simpa using this
    · exact intervalIntegrable_const
    · refine Eventually.of_forall fun θ _ => ?_
      have hcr : Continuous (fun r : ℝ => circleMap 0 r θ) := by unfold circleMap; fun_prop
      have hc : Tendsto (fun k => circleMap 0 (s k) θ) atTop (𝓝 (circleMap 0 1 θ)) :=
        (hcr.tendsto 1).comp hstend
      refine (((hcont (circleMap 0 1 θ) (by simp [mem_closedBall, norm_circleMap_zero])).tendsto.comp
        (tendsto_nhdsWithin_iff.2 ⟨hc, Eventually.of_forall fun k => ?_⟩)).norm)
      simpa [mem_closedBall, norm_circleMap_zero, abs_of_pos (hspos k)] using (hslt k).le
  -- convergence of the diameter integrals
  have hA : Tendsto (fun k => ∫ x in (-(s k))..(s k), ‖h (x : ℂ)‖) atTop
      (𝓝 (∫ x in (-1 : ℝ)..1, ‖h (x : ℂ)‖)) := by
    have hmem : ∀ k, ∀ y : ℝ, y ∈ Set.uIoc (-1 : ℝ) 1 → ((s k * y : ℝ) : ℂ) ∈ closedBall (0 : ℂ) 1 := by
      intro k y hy
      rw [Set.uIoc_of_le (by norm_num)] at hy
      simp only [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        abs_of_pos (hspos k)]
      have : |y| ≤ 1 := abs_le.2 ⟨hy.1.le, hy.2⟩
      nlinarith [hslt k, hspos k, abs_nonneg y]
    have hA' : Tendsto (fun k => ∫ y in (-1 : ℝ)..1, ‖h ((s k * y : ℝ) : ℂ)‖) atTop
        (𝓝 (∫ y in (-1 : ℝ)..1, ‖h (y : ℂ)‖)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_ ?_ ?_
      · refine Eventually.of_forall fun k => ?_
        have hct : ContinuousOn (fun y : ℝ => ‖h ((s k * y : ℝ) : ℂ)‖) (Set.uIoc (-1 : ℝ) 1) :=
          (hcont.comp (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).continuousOn
            (hmem k)).norm
        exact hct.aestronglyMeasurable measurableSet_uIoc
      · refine Eventually.of_forall fun k => Eventually.of_forall fun y hy => ?_
        simpa using hM _ (hmem k y hy)
      · exact intervalIntegrable_const
      · refine Eventually.of_forall fun y hy => ?_
        have hyb : (y : ℂ) ∈ closedBall (0 : ℂ) 1 := by
          rw [Set.uIoc_of_le (by norm_num)] at hy
          simp [abs_le, hy.1.le, hy.2]
        have hc : Tendsto (fun k => ((s k * y : ℝ) : ℂ)) atTop (𝓝 (y : ℂ)) := by
          have : Tendsto (fun k => s k * y) atTop (𝓝 (1 * y)) := hstend.mul_const y
          have h2 := (Complex.continuous_ofReal.tendsto _).comp this
          simpa [Function.comp_def] using h2
        exact ((hcont (y : ℂ) hyb).tendsto.comp (tendsto_nhdsWithin_iff.2
          ⟨hc, Eventually.of_forall fun k => hmem k y hy⟩)).norm
    have hscale : ∀ k, ∫ x in (-(s k))..(s k), ‖h (x : ℂ)‖ =
        s k * ∫ y in (-1 : ℝ)..1, ‖h ((s k * y : ℝ) : ℂ)‖ := by
      intro k
      have := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
        (fun x : ℝ => ‖h (x : ℂ)‖) (hspos k).ne'
      rw [this]
      simp [smul_eq_mul, (hspos k).ne']
    simp_rw [hscale]
    simpa using hstend.mul hA'

  have hlim := (hstend.div_const 2).mul hC
  exact le_of_tendsto_of_tendsto hA hlim (Eventually.of_forall hineq) |>.trans (by simp)


/-- info: 'FormalResearch.Hardy.fejerRiesz_disc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hardy.fejerRiesz_disc

end FormalResearch.Hardy

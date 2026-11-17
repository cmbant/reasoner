module

public import FormalResearch.Special.BarnesDigamma

/-!
# The logarithm of Barnes' `G`: Weierstrass series and its derivative

For `Re z > -1` put
`barnesTerm k z = (k+1) log(1 + z/(k+1)) - z + z²/(2(k+1))` (principal logarithm; `1 + z/(k+1)` has
positive real part) and `barnesLogSeries z = ∑_{k ≥ 0} barnesTerm k z`.  This is the logarithm of
the Weierstrass product of DLMF 5.17.3,
`G(1+z) = (2π)^{z/2} e^{-z(z+1)/2 - γ z²/2} ∏_{k≥1} (1+z/k)^k e^{-z+z²/(2k)}`.

* `summable_barnesTerm`, `hasDerivAt_barnesLogSeries` : the series converges for `Re z > -1`
  and may be differentiated termwise (Weierstrass M-test on `{δ-1 < Re z, |z| < R}`);
* `barnesLogSeries_deriv` : its derivative is `z (ψ(1+z) + γ)`, using Gauss' series
  `digamma_eq_series`.

Not formalised here: convergence of the product on all of `ℂ` (the entire extension is obtained in
`BarnesG` from the functional equation instead).
-/

@[expose] public section

namespace FormalResearch.Special.Barnes

open Filter Topology Set Complex

local notation "γ" => Real.eulerMascheroniConstant

/-- Terms of the logarithmic Weierstrass series of Barnes' `G(1+z)`. -/
noncomputable def barnesTerm (k : ℕ) (z : ℂ) : ℂ :=
  ((k : ℂ) + 1) * Complex.log (1 + z / ((k : ℂ) + 1)) - z + z ^ 2 / (2 * ((k : ℂ) + 1))

lemma barnesTerm_zero (k : ℕ) : barnesTerm k 0 = 0 := by simp [barnesTerm]

private lemma natcast_succ_ne (k : ℕ) : ((k : ℂ) + 1) ≠ 0 := by
  exact_mod_cast Nat.succ_ne_zero k

lemma one_add_div_mem_slitPlane (k : ℕ) {z : ℂ} (hz : -1 < z.re) :
    (1 + z / ((k : ℂ) + 1)) ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have h : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [h, Complex.add_re, Complex.div_ofReal_re]
  simp only [Complex.one_re]
  have : -1 ≤ z.re / ((k : ℝ) + 1) * 1 + 0 := by
    rw [mul_one, add_zero, le_div_iff₀ hk]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h2 : z.re / ((k : ℝ) + 1) > -1 := by
    rw [gt_iff_lt, lt_div_iff₀ hk]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  linarith

lemma hasDerivAt_barnesTerm (k : ℕ) {z : ℂ} (hz : -1 < z.re) :
    HasDerivAt (barnesTerm k) (z ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + z))) z := by
  have hk := natcast_succ_ne k
  have hne : ((k : ℂ) + 1 + z) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have h1 : HasDerivAt (fun z : ℂ => 1 + z / ((k : ℂ) + 1)) (1 / ((k : ℂ) + 1)) z :=
    ((hasDerivAt_id z).div_const _).const_add 1
  have h2 := (h1.clog (one_add_div_mem_slitPlane k hz)).const_mul ((k : ℂ) + 1)
  have h3 := (h2.sub (hasDerivAt_id z)).add ((hasDerivAt_pow 2 z).div_const (2 * ((k : ℂ) + 1)))
  refine (h3.congr_deriv ?_)
  have hne' : (1 + z / ((k : ℂ) + 1)) ≠ 0 := by
    intro h
    have : (1 + z / ((k : ℂ) + 1)) ∈ slitPlane := one_add_div_mem_slitPlane k hz
    exact (slitPlane_ne_zero this) h
  field_simp
  ring

lemma norm_barnesTerm_deriv_le {δ R : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {z : ℂ}
    (hz : δ - 1 < z.re) (hzR : ‖z‖ < R) (k : ℕ) :
    ‖z ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + z))‖ ≤ R ^ 2 / δ * (1 / ((k : ℝ) + 1) ^ 2) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkp : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h1 : ((k : ℝ) + 1) ≤ ‖(k : ℂ) + 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); simp
  have h2 : δ * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + 1 + z‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]
    nlinarith
  rw [norm_div, norm_mul, norm_pow]
  have hR : 0 ≤ R := le_trans (norm_nonneg _) hzR.le
  calc ‖z‖ ^ 2 / (‖(k : ℂ) + 1‖ * ‖(k : ℂ) + 1 + z‖)
      ≤ R ^ 2 / (((k : ℝ) + 1) * (δ * ((k : ℝ) + 1))) := by
        refine div_le_div₀ (by positivity) ?_ (by positivity) (mul_le_mul h1 h2 (by positivity)
          (le_trans hkp.le h1))
        exact pow_le_pow_left₀ (norm_nonneg _) hzR.le 2
    _ = R ^ 2 / δ * (1 / ((k : ℝ) + 1) ^ 2) := by field_simp

/-- The domain `Re z > -1`. -/
def lhp1 : Set ℂ := {z | -1 < z.re}

/-- Termwise differentiation of the Weierstrass series and summability, on `Re z > -1`. -/
theorem barnes_series_calculus {z : ℂ} (hz : -1 < z.re) :
    Summable (fun k : ℕ => barnesTerm k z) ∧
    HasDerivAt (fun w => ∑' k : ℕ, barnesTerm k w)
      (∑' k : ℕ, z ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + z))) z := by
  set δ : ℝ := min (1 / 2) ((z.re + 1) / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  have hδ2 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  set R : ℝ := ‖z‖ + 1
  set U : Set ℂ := {w | δ - 1 < w.re ∧ ‖w‖ < R}
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)
  have hUc : Convex ℝ U := by
    have : U = {w : ℂ | δ - 1 < w.re} ∩ Metric.ball 0 R := by ext w; simp [U]
    rw [this]; exact (convex_halfSpace_re_gt _).inter (convex_ball _ _)
  have hzU : z ∈ U := ⟨by have := min_le_right (1 / 2 : ℝ) ((z.re + 1) / 2); linarith, by simp [R]⟩
  have h0U : (0 : ℂ) ∈ U := ⟨by simp; linarith, by simp [R]; positivity⟩
  have hUm1 : ∀ w ∈ U, -1 < w.re := fun w hw => by have := hw.1; linarith
  have hsum : Summable (fun k : ℕ => R ^ 2 / δ * (1 / ((k : ℝ) + 1) ^ 2)) := by
    refine Summable.mul_left _ ?_
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hder : ∀ (k : ℕ), ∀ y ∈ U, HasDerivAt (barnesTerm k)
      (y ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + y))) y :=
    fun k y hy => hasDerivAt_barnesTerm k (hUm1 y hy)
  have hbd : ∀ (k : ℕ), ∀ y ∈ U, ‖y ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + y))‖ ≤
      R ^ 2 / δ * (1 / ((k : ℝ) + 1) ^ 2) :=
    fun k y hy => norm_barnesTerm_deriv_le hδ0 hδ1 hy.1 hy.2 k
  have h0sum : Summable (fun k : ℕ => barnesTerm k 0) := by simp [barnesTerm_zero]
  exact ⟨summable_of_summable_hasDerivAt_of_isPreconnected hsum hUo hUc.isPreconnected hder hbd
      h0U h0sum hzU,
    hasDerivAt_tsum_of_isPreconnected hsum hUo hUc.isPreconnected hder hbd h0U h0sum hzU⟩

/-- The logarithmic Weierstrass series. -/
noncomputable def barnesLogSeries (z : ℂ) : ℂ := ∑' k : ℕ, barnesTerm k z

theorem summable_barnesTerm {z : ℂ} (hz : -1 < z.re) : Summable (fun k : ℕ => barnesTerm k z) :=
  (barnes_series_calculus hz).1

/-- `(∑_k barnesTerm k)' (z) = z (ψ(1+z) + γ)`. -/
theorem hasDerivAt_barnesLogSeries {z : ℂ} (hz : -1 < z.re) :
    HasDerivAt barnesLogSeries (z * (digamma (1 + z) + γ)) z := by
  have h := (barnes_series_calculus hz).2
  have hre : 0 < (1 + z).re := by simp; linarith
  have hd := digamma_eq_series hre
  have hk : ∀ k : ℕ, z ^ 2 / (((k : ℂ) + 1) * ((k : ℂ) + 1 + z)) =
      z * ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + z))) := by
    intro k
    have hk1 := natcast_succ_ne k
    have hne : ((k : ℂ) + 1 + z) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
      linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hne2 : ((k : ℂ) + (1 + z)) ≠ 0 := by rw [← add_assoc]; exact hne
    field_simp
    ring
  simp_rw [hk] at h
  rw [tsum_mul_left] at h
  have : digamma (1 + z) + γ = ∑' k : ℕ, ((1 : ℂ) / ((k : ℂ) + 1) - 1 / ((k : ℂ) + (1 + z))) := by
    rw [hd]; ring
  rw [this]
  exact h

end FormalResearch.Special.Barnes

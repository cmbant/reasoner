module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerKernel

/-!
# Auxiliary bounds for `(F2)`

Compact bounds for `τ'`, `τ''`, `τ'''`, a uniform lower bound for `τ'` on `[a, ∞)` and for the difference
quotient `D(x, y) = (τ(x) - τ(y))/(x - y)`, and the divergence `τ → ∞`.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

lemma hasDerivAt_langerTau_pos {y : ℝ} (hy : 0 < y) : HasDerivAt langerTau (deriv langerTau y) y :=
  (((contDiffOn_langerTau 1).differentiableOn one_ne_zero).differentiableAt
    (Ioi_mem_nhds hy)).hasDerivAt

lemma hasDerivAt_deriv_langerTau {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv langerTau) (deriv (deriv langerTau) y) y :=
  ((contDiffOn_deriv_langerTau.differentiableOn one_ne_zero).differentiableAt
    (Ioi_mem_nhds hy)).hasDerivAt

lemma contDiffOn_deriv2_langerTau : ContDiffOn ℝ 1 (deriv (deriv langerTau)) (Ioi 0) :=
  ((contDiffOn_langerTau 3).deriv_of_isOpen isOpen_Ioi (by norm_num : ((2 : ℕ) : WithTop ℕ∞) + 1 ≤ ((3 : ℕ) : WithTop ℕ∞))
    |>.deriv_of_isOpen isOpen_Ioi (by norm_num))

lemma hasDerivAt_deriv2_langerTau {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (deriv langerTau)) (deriv (deriv (deriv langerTau)) y) y :=
  ((contDiffOn_deriv2_langerTau.differentiableOn one_ne_zero).differentiableAt
    (Ioi_mem_nhds hy)).hasDerivAt

lemma continuousOn_deriv3_langerTau : ContinuousOn (deriv (deriv (deriv langerTau))) (Ioi 0) :=
  contDiffOn_deriv2_langerTau.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

/-- `|τ'|, |τ''|, |τ'''| ≤ C` on every compact `[a, b] ⊂ (0, ∞)`. -/
theorem langerTau_deriv_bound_compact3 {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, |deriv langerTau x| ≤ C ∧ |deriv (deriv langerTau) x| ≤ C ∧
      |deriv (deriv (deriv langerTau)) x| ≤ C := by
  obtain ⟨C1, h1⟩ := langerTau_deriv_bound_compact (b := b) ha
  have hsub : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  obtain ⟨C3, h3⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuousOn_deriv3_langerTau.mono hsub)
  refine ⟨max C1 C3, fun x hx => ?_⟩
  have a3 : |deriv (deriv (deriv langerTau)) x| ≤ C3 := by simpa using h3 x hx
  exact ⟨(h1 x hx).1.trans (le_max_left _ _), (h1 x hx).2.trans (le_max_left _ _),
    a3.trans (le_max_right _ _)⟩

/-- `τ' ≥ c` on `[a, ∞)` for every `a > 0`. -/
theorem langerTau_deriv_ge_const_of {a : ℝ} (ha : 0 < a) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, a ≤ x → c ≤ deriv langerTau x := by
  have hxs := xiStar_pos
  rcases le_or_gt xiStar a with hle | hlt
  · exact ⟨4 / 5, by norm_num, fun x hx => langerTau_deriv_ge (hle.trans hx)⟩
  · have hsub : Icc a xiStar ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
    obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := a) (b := xiStar)).exists_isMinOn
      (nonempty_Icc.2 hlt.le) (continuousOn_deriv_langerTau.mono hsub)
    have hpos : 0 < deriv langerTau x0 := deriv_langerTau_pos (hsub hx0)
    refine ⟨min (4 / 5) (deriv langerTau x0), lt_min (by norm_num) hpos, fun x hx => ?_⟩
    rcases le_total x xiStar with h | h
    · exact (min_le_right _ _).trans (hmin (⟨hx, h⟩ : x ∈ Icc a xiStar))
    · exact (min_le_left _ _).trans (langerTau_deriv_ge h)

/-- Mean-value lower bound: if `τ' ≥ c` on `[a, ∞)` then `τ(y) - τ(x) ≥ c (y - x)` for `a ≤ x ≤ y`. -/
lemma langerTau_sub_ge {a c x y : ℝ} (ha : 0 < a) (hc : ∀ z : ℝ, a ≤ z → c ≤ deriv langerTau z)
    (hax : a ≤ x) (hxy : x ≤ y) : c * (y - x) ≤ langerTau y - langerTau x := by
  rcases hxy.eq_or_lt with h | h
  · rw [h]; simp
  · have hcont : ContinuousOn langerTau (Icc x y) :=
      (contDiffOn_langerTau 0).continuousOn.mono fun z hz => lt_of_lt_of_le ha (hax.trans hz.1)
    have hder : ∀ z ∈ Ioo x y, HasDerivAt langerTau (deriv langerTau z) z := fun z hz =>
      hasDerivAt_langerTau_pos (lt_of_lt_of_le ha (hax.trans hz.1.le))
    obtain ⟨z, hz, hz2⟩ := exists_hasDerivAt_eq_slope langerTau (deriv langerTau) h hcont hder
    have := hc z (hax.trans hz.1.le)
    rw [hz2, le_div_iff₀ (sub_pos.2 h)] at this
    linarith

lemma langerD_ge {a c x y : ℝ} (ha : 0 < a) (hc : ∀ z : ℝ, a ≤ z → c ≤ deriv langerTau z)
    (hax : a ≤ x) (hay : a ≤ y) : c ≤ langerD x y := by
  by_cases hxy : y = x
  · subst hxy; rw [langerD_diag]; exact hc _ hax
  · rw [langerD_of_ne hxy]
    rcases lt_or_gt_of_ne hxy with h | h
    · have := langerTau_sub_ge ha hc hay h.le
      rw [le_div_iff₀ (by linarith)]; nlinarith
    · have := langerTau_sub_ge ha hc hax h.le
      rw [le_div_iff_of_neg (by linarith)]; nlinarith

/-- `τ → ∞`. -/
lemma exists_langerTau_ge (B : ℝ) : ∃ Y : ℝ, xiStar < Y ∧ ∀ y : ℝ, Y ≤ y → B ≤ langerTau y := by
  have h1 : Tendsto (fun y : ℝ => (cumulN y / kTip) ^ (2 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp
      (tendsto_cumulN_atTop.atTop_div_const kTip_pos)
  obtain ⟨Y, hY⟩ := (eventually_atTop.1 (h1.eventually_ge_atTop B))
  refine ⟨max Y (xiStar + 1), by simp, fun y hy => ?_⟩
  have hy' : xiStar < y := lt_of_lt_of_le (by linarith [le_max_right Y (xiStar + 1)]) hy
  rw [langerTau_eq_of_gt hy']
  exact hY y ((le_max_left _ _).trans hy)

end FormalResearch.ModularBootstrap.Upper.Ramped

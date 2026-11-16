module

public import FormalResearch.Special.AiryParametrixLanger
public import FormalResearch.Special.AiryParametrixUniformLattice

/-!
# Discrete-to-Airy limit, step 1: the smooth data of a simple turn on a closed window

Part of the wiring module `DiscreteAiryLimit*` (the composition of the D2A machinery M1-M7b into one abstract
discrete-to-Airy theorem, see `DiscreteAiryLimit`).

Given the *simple-turn data* `u ∈ C³`, `u(c₀) = 1`, `u'(c₀) > 0`, `A ∈ C²`, `A(c₀) > 0` (P3 `A:804-818`,
W1 `est:266-282`), the Langer coordinate `ζ = langerZeta u c₀` and amplitude `g = langerAmp u A c₀` of
`LangerCoordinate`/`AiryParametrixLanger`, `dal_turn_data` packages, on one closed window `[c₀ - r, c₀ + r]`, everything the
lattice arguments need:

* `r > 0` and an open `U ⊇ [c₀ - r, c₀ + r]` on which `ζ ∈ C³`, `A, g ∈ C²` and the amplitude relation
  `g² A ζ' Sh(ζ ζ'²) = 1` and the eikonal relation `Ch(ζ ζ'²) = u` hold (`langer_hrel`);
* uniform bounds `0 < c₁ ≤ ζ' ≤ c₂`, `0 < g_min ≤ g ≤ g_max`, `0 < A_min ≤ A ≤ A_max` on the window;
* Lipschitz constants `L_A, L_g, L_u` of `A, g, u` on the window.

Proved (compactness plus the mean-value inequality).  Constants are existential.
-/

@[expose] public section

open Set Filter Topology Metric

namespace FormalResearch.Special

/-- A `C¹` function on an open set is Lipschitz on a compact interval inside it. -/
lemma dal_lip_Icc {f : ℝ → ℝ} {V : Set ℝ} (hV : IsOpen V) {a b : ℝ} (hab : Icc a b ⊆ V)
    (hf : ContDiffOn ℝ 1 f V) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |f x - f y| ≤ L * |x - y| := by
  have hd : ContinuousOn (deriv f) V := hf.continuousOn_deriv_of_isOpen hV (by norm_num)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hd.mono hab)
  have hdiff : ∀ x ∈ Icc a b, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds (hab hx))
  refine ⟨max C 0, le_max_right _ _, fun x hx y hy => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Icc a b) (C := max C 0) hdiff
    (fun z hz => (hC z hz).trans (le_max_left _ _)) (convex_Icc a b) hy hx
  simpa [Real.norm_eq_abs] using this

/-- A continuous positive function on a nonempty compact interval is bounded between two positive constants. -/
lemma dal_pos_bounds {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hpos : ∀ x ∈ Icc a b, 0 < f x) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ x ∈ Icc a b, lo ≤ f x ∧ f x ≤ hi := by
  have hne : (Icc a b).Nonempty := ⟨a, left_mem_Icc.2 hab⟩
  obtain ⟨x1, hx1, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨x2, hx2, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  refine ⟨f x1, f x2, hpos x1 hx1, hmin hx2, fun x hx => ⟨hmin hx, hmax hx⟩⟩

/-- The *window data* of a simple turn: constants and uniform bounds of `ζ, g, A, u` on `[c₀ - r, c₀ + r]`. -/
structure DalTurnWin (ζ g A u : ℝ → ℝ) (c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu : ℝ) : Prop where
  r_pos : 0 < r
  c1_pos : 0 < c1
  c1_le : c1 ≤ c2
  gmin_pos : 0 < gmin
  gmin_le : gmin ≤ gmax
  Amin_pos : 0 < Amin
  Amin_le : Amin ≤ Amax
  LA_nonneg : 0 ≤ LA
  Lg_nonneg : 0 ≤ Lg
  Lu_nonneg : 0 ≤ Lu
  zeta0 : ζ c0 = 0
  u0 : u c0 = 1
  der : ∀ q ∈ Icc (c0 - r) (c0 + r),
    HasDerivAt ζ (deriv ζ q) q ∧ c1 ≤ deriv ζ q ∧ deriv ζ q ≤ c2
  gb : ∀ q ∈ Icc (c0 - r) (c0 + r), gmin ≤ g q ∧ g q ≤ gmax
  Ab : ∀ q ∈ Icc (c0 - r) (c0 + r), Amin ≤ A q ∧ A q ≤ Amax
  lip : ∀ x ∈ Icc (c0 - r) (c0 + r), ∀ y ∈ Icc (c0 - r) (c0 + r),
    |A x - A y| ≤ LA * |x - y| ∧ |g x - g y| ≤ Lg * |x - y| ∧ |u x - u y| ≤ Lu * |x - y|

/-- **Smooth data of a simple turn on a closed window** (any prescribed maximal half-width `r₀`).
See the module docstring. -/
theorem dal_turn_data {u A : ℝ → ℝ} {c0 : ℝ} (hu : ContDiffAt ℝ 3 u c0) (h1 : u c0 = 1)
    (h2 : 0 < deriv u c0) (hA : ContDiffAt ℝ 2 A c0) (hA0 : 0 < A c0) {r0 : ℝ} (hr0 : 0 < r0) :
    ∃ (r c1 c2 gmin gmax Amin Amax LA Lg Lu : ℝ) (U : Set ℝ),
      DalTurnWin (langerZeta u c0) (langerAmp u A c0) A u c0 r c1 c2 gmin gmax Amin Amax LA Lg Lu ∧
      r ≤ r0 ∧ IsOpen U ∧ Icc (c0 - r) (c0 + r) ⊆ U ∧
      ContDiffOn ℝ 3 (langerZeta u c0) U ∧ ContDiffOn ℝ 2 A U ∧ ContDiffOn ℝ 2 (langerAmp u A c0) U ∧
      (∀ q ∈ U, langerAmp u A c0 q ^ 2 * A q * deriv (langerZeta u c0) q *
          (2 * deriv langerCosh (langerZeta u c0 q * deriv (langerZeta u c0) q ^ 2)) = 1) ∧
      (∀ q ∈ U, langerCosh (langerZeta u c0 q * deriv (langerZeta u c0) q ^ 2) = u q) := by
  obtain ⟨U, hU, hcU, hζ, hAU, hgU, hall⟩ := langer_hrel hu h1 h2 hA hA0
  have hz0 : langerZeta u c0 c0 = 0 := by
    unfold langerZeta; exact langerZetaOf_zero _ _
  obtain ⟨ρ, hρ, hρU⟩ := Metric.isOpen_iff.1 hU c0 hcU
  have hev : ∀ᶠ y in 𝓝 c0, ContDiffAt ℝ 3 u y := hu.eventually (by simp)
  obtain ⟨ε, hε, hεu⟩ := Metric.eventually_nhds_iff_ball.1 hev
  set r : ℝ := min (min ρ ε) r0 / 2 with hr
  have hr0' : 0 < r := by have := lt_min (lt_min hρ hε) hr0; rw [hr]; linarith
  have hrρ : r < ρ := by
    have := (min_le_left (min ρ ε) r0).trans (min_le_left ρ ε); rw [hr]; linarith
  have hrε : r < ε := by
    have := (min_le_left (min ρ ε) r0).trans (min_le_right ρ ε); rw [hr]; linarith
  have hrr0 : r ≤ r0 := by
    have := min_le_right (min ρ ε) r0; rw [hr]; linarith
  have hsub : Icc (c0 - r) (c0 + r) ⊆ U := fun x hx => hρU (by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2])
  have hsubε : Icc (c0 - r) (c0 + r) ⊆ ball c0 ε := fun x hx => by
    rw [mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  have hle : c0 - r ≤ c0 + r := by linarith
  have hdζ : ContinuousOn (deriv (langerZeta u c0)) U := hζ.continuousOn_deriv_of_isOpen hU (by norm_num)
  have hgc : ContinuousOn (langerAmp u A c0) U := hgU.continuousOn
  have hAc : ContinuousOn A U := hAU.continuousOn
  obtain ⟨c1, c2, hc1, hc12, hcb⟩ := dal_pos_bounds hle (hdζ.mono hsub)
    (fun x hx => (hall x (hsub hx)).2.2.1)
  obtain ⟨gmin, gmax, hg1, hg12, hgb⟩ := dal_pos_bounds hle (hgc.mono hsub)
    (fun x hx => (hall x (hsub hx)).2.1)
  obtain ⟨Amin, Amax, hA1, hA12, hAb⟩ := dal_pos_bounds hle (hAc.mono hsub)
    (fun x hx => (hall x (hsub hx)).1)
  obtain ⟨LA, hLA, hLAb⟩ := dal_lip_Icc hU hsub (hAU.of_le (by norm_num))
  obtain ⟨Lg, hLg, hLgb⟩ := dal_lip_Icc hU hsub (hgU.of_le (by norm_num))
  have hBu : IsOpen (ball c0 ε) := isOpen_ball
  have huB : ContDiffOn ℝ 1 u (ball c0 ε) := fun y hy =>
    ((hεu y hy).contDiffWithinAt).of_le (by norm_num)
  obtain ⟨Lu, hLu, hLub⟩ := dal_lip_Icc hBu hsubε huB
  refine ⟨r, c1, c2, gmin, gmax, Amin, Amax, LA, Lg, Lu, U, ⟨hr0', hc1, hc12, hg1, hg12, hA1, hA12,
    hLA, hLg, hLu, hz0, h1, ?_, hgb, hAb, ?_⟩, hrr0, hU, hsub, hζ, hAU, hgU,
    fun q hq => (hall q hq).2.2.2.1, fun q hq => (hall q hq).2.2.2.2⟩
  · intro q hq
    have hqU := hsub hq
    have hdiff : DifferentiableAt ℝ (langerZeta u c0) q :=
      (hζ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hqU)
    exact ⟨hdiff.hasDerivAt, (hcb q hq).1, (hcb q hq).2⟩
  · intro x hx y hy
    exact ⟨hLAb x hx y hy, hLgb x hx y hy, hLub x hx y hy⟩

/-- info: 'FormalResearch.Special.dal_turn_data' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dal_turn_data

end FormalResearch.Special

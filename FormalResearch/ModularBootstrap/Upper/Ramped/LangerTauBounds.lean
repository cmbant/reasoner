module

public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerTauDeriv

/-!
# `(F1)`: bounds on `τ'` and `τ''`

`remainder.tex`, Proposition 1.2(2), input `(F1)` (Langer coordinate):

* `langerTau_deriv_ge_const`: `c_τ ≤ τ'` on `[ξ_*/2, ∞)`;
* `langerTau_deriv_bound_compact`: `|τ'|, |τ''| ≤ C` on every compact `[a, b] ⊂ (0, ∞)` (`τ ∈ C²`);
* `langerTau_large`: for every `r₁ > 0` and `y ≥ ξ_* + r₁` (the paper takes `r₁ = 0.63`):
  `τ(y) > 0`, `τ'(y) ≤ C τ(y)/(1+y)` and `|τ''(y)| ≤ C τ(y)/(1+y)²`.

Note that `τ'` is *not* bounded on `[ξ_*/2, ∞)`: `τ ≍ y^{4/3}` (`τ'/τ ≍ 1/y`), so the upper bound `τ' ≤ C` holds
on compacts only.
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set Metric
open scoped Real Interval

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap Upper.Comb

/-! ### Compact bounds -/

lemma continuousOn_deriv_langerTau : ContinuousOn (deriv langerTau) (Ioi 0) :=
  (contDiffOn_langerTau 2).continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)

lemma contDiffOn_deriv_langerTau : ContDiffOn ℝ 1 (deriv langerTau) (Ioi 0) :=
  (contDiffOn_langerTau 2).deriv_of_isOpen isOpen_Ioi (by norm_num)

lemma continuousOn_deriv2_langerTau : ContinuousOn (deriv (deriv langerTau)) (Ioi 0) :=
  contDiffOn_deriv_langerTau.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl

theorem langerTau_deriv_bound_compact {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, |deriv langerTau x| ≤ C ∧ |deriv (deriv langerTau) x| ≤ C := by
  have hsub : Icc a b ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le ha hx.1
  obtain ⟨C1, h1⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuousOn_deriv_langerTau.mono hsub)
  obtain ⟨C2, h2⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (continuousOn_deriv2_langerTau.mono hsub)
  refine ⟨max C1 C2, fun x hx => ?_⟩
  have a1 : |deriv langerTau x| ≤ C1 := by simpa using h1 x hx
  have a2 : |deriv (deriv langerTau) x| ≤ C2 := by simpa using h2 x hx
  exact ⟨a1.trans (le_max_left _ _), a2.trans (le_max_right _ _)⟩

theorem langerTau_deriv_ge_const : ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, xiStar / 2 ≤ x → c ≤ deriv langerTau x := by
  have hxs := xiStar_pos
  have hsub : Icc (xiStar / 2) xiStar ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le (by linarith) hx.1
  obtain ⟨x0, hx0, hmin⟩ := (isCompact_Icc (a := xiStar / 2) (b := xiStar)).exists_isMinOn
    (nonempty_Icc.2 (by linarith)) (continuousOn_deriv_langerTau.mono hsub)
  have hpos : 0 < deriv langerTau x0 := deriv_langerTau_pos (hsub hx0)
  refine ⟨min (4 / 5) (deriv langerTau x0), lt_min (by norm_num) hpos, fun x hx => ?_⟩
  rcases le_total x xiStar with h | h
  · exact (min_le_right _ _).trans (hmin (⟨hx, h⟩ : x ∈ Icc (xiStar / 2) xiStar))
  · exact (min_le_left _ _).trans (langerTau_deriv_ge h)

/-! ### Large `y` -/

lemma rhoU_le_linear {r : ℝ} (hr : 0 ≤ r) : rhoU (xiStar + r) ≤ (3 * kTip / 2 + 4 / 3) * (1 + r) := by
  have hk := kTip_pos
  have hsq := (rhoU_sq_bounds hr).2
  have hs : √r ^ 2 = r := Real.sq_sqrt hr
  have hs0 := Real.sqrt_nonneg r
  have hsr : √r ≤ (1 + r) / 2 := by nlinarith [sq_nonneg (√r - 1)]
  have hB : rhoU (xiStar + r) ≤ 3 * kTip * √r + 4 / 3 * r := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg hk.le hs0, mul_nonneg (mul_nonneg hk.le hs0) hr]
  nlinarith

lemma langerG_bounds {N ρ p u A C1 P1 : ℝ} (hu : 0 < u) (hA : 0 < A) (hN : u ^ 2 ≤ 3 * A ^ 2 * N)
    (hρ0 : 0 < ρ) (hρ : ρ ≤ C1 * u) (hp0 : 0 ≤ p) (hp : p ≤ P1) :
    ρ / (3 * N) ≤ C1 * A ^ 2 / u ∧
      |p / (3 * N) - ρ ^ 2 / (6 * N ^ 2)| ≤ (P1 * A ^ 2 + 3 / 2 * C1 ^ 2 * A ^ 4) / u ^ 2 := by
  have hNp : 0 < N := by
    by_contra h; push Not at h; nlinarith [sq_nonneg A, sq_nonneg u, mul_nonneg (sq_nonneg A) (neg_nonneg.2 h)]
  have hC1 : 0 ≤ C1 := by
    by_contra h; push Not at h; nlinarith
  have hP1 : 0 ≤ P1 := hp0.trans hp
  have hu2 : 0 < u ^ 2 := by positivity
  have h1 : ρ / (3 * N) ≤ C1 * A ^ 2 / u := by
    rw [div_le_div_iff₀ (by positivity) hu]
    nlinarith [mul_le_mul_of_nonneg_left hN hC1]
  have h2 : p / (3 * N) ≤ P1 * A ^ 2 / u ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hu2]
    nlinarith [mul_le_mul_of_nonneg_left hN hP1, mul_le_mul_of_nonneg_right hp hu2.le]
  have h3 : ρ ^ 2 / (6 * N ^ 2) ≤ 3 / 2 * C1 ^ 2 * A ^ 4 / u ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) hu2]
    have hu4 : u ^ 4 ≤ 9 * A ^ 4 * N ^ 2 := by
      have := mul_le_mul hN hN (by positivity) (by positivity)
      nlinarith
    have hρ2 : ρ ^ 2 ≤ C1 ^ 2 * u ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hρ2 hu2.le, mul_le_mul_of_nonneg_left hu4 (sq_nonneg C1)]
  have hpos1 : 0 ≤ p / (3 * N) := by positivity
  have hpos2 : 0 ≤ ρ ^ 2 / (6 * N ^ 2) := by positivity
  refine ⟨h1, ?_⟩
  rw [abs_le]
  have : (P1 * A ^ 2 + 3 / 2 * C1 ^ 2 * A ^ 4) / u ^ 2 =
      P1 * A ^ 2 / u ^ 2 + 3 / 2 * C1 ^ 2 * A ^ 4 / u ^ 2 := by ring
  constructor <;> linarith

/-- Large-`y` regime of `(F1)`: `τ'/τ ≲ 1/(1+y)` and `|τ''|/τ ≲ 1/(1+y)²` for `y ≥ ξ_* + r₁`. -/
theorem langerTau_large {r1 : ℝ} (hr1 : 0 < r1) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, xiStar + r1 ≤ y →
      0 < langerTau y ∧ deriv langerTau y ≤ C * langerTau y / (1 + y) ∧
        |deriv (deriv langerTau) y| ≤ C * langerTau y / (1 + y) ^ 2 := by
  have hk := kTip_pos
  have hxs := xiStar_pos
  set A0 : ℝ := (1 + xiStar) / r1 + 1 with hA0
  have hA0p : 0 < A0 := by positivity
  set C1 : ℝ := 3 * kTip / 2 + 4 / 3 with hC1
  set P1 : ℝ := rhoUDeriv (xiStar + r1) with hP1
  have hP1p : 0 ≤ P1 := by
    have := rhoUDeriv_ge (y := xiStar + r1) (by linarith); linarith
  set K1 : ℝ := C1 * A0 ^ 2 with hK1
  set K2 : ℝ := P1 * A0 ^ 2 + 3 / 2 * C1 ^ 2 * A0 ^ 4 with hK2
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨K1 + K1 ^ 2 + K2 + 1, by positivity, fun y hy => ?_⟩
  have hyx : xiStar < y := by linarith
  set r := y - xiStar with hr
  have hrr : r1 ≤ r := by rw [hr]; linarith
  have hr0 : 0 < r := lt_of_lt_of_le hr1 hrr
  have hτ := langerTau_pos_of_gt hyx
  have hu : 0 < 1 + y := by linarith
  have hy' : xiStar + r = y := by rw [hr]; ring
  have hu1 : 1 + y ≤ A0 * r := by
    have : (1 + xiStar) ≤ (1 + xiStar) / r1 * r := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hr1]; nlinarith
    rw [hA0]; nlinarith
  have hN3 : r ^ 2 / 3 ≤ cumulN y := by
    have := cumulN_ge_sq_div_three hr0.le; rwa [hy'] at this
  have hN : (1 + y) ^ 2 ≤ 3 * A0 ^ 2 * cumulN y := by
    have h2 : (1 + y) ^ 2 ≤ (A0 * r) ^ 2 := by gcongr
    nlinarith
  have hρ0 := rhoU_pos hyx
  have hρ : rhoU y ≤ C1 * (1 + y) := by
    have := rhoU_le_linear hr0.le
    rw [hy'] at this
    refine this.trans ?_
    have : 1 + r ≤ 1 + y := by rw [hr]; linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have hp0 : 0 ≤ rhoUDeriv y := by
    have := rhoUDeriv_ge hyx; linarith
  have hp : rhoUDeriv y ≤ P1 := by
    rcases (show xiStar + r1 ≤ y from hy).eq_or_lt with h | h
    · rw [← h]
    · exact (rhoUDeriv_strictAntiOn (by show xiStar < xiStar + r1; linarith)
        (by show xiStar < y; exact hyx) h).le
  obtain ⟨hG, hG'⟩ := langerG_bounds hu hA0p hN hρ0 hρ hp0 hp
  refine ⟨hτ, ?_, ?_⟩
  · rw [deriv_langerTau_eq hyx]
    have : langerTau y * langerG y ≤ langerTau y * (K1 / (1 + y)) :=
      mul_le_mul_of_nonneg_left hG hτ.le
    refine this.trans ?_
    rw [mul_div_assoc']
    apply div_le_div_of_nonneg_right _ hu.le
    have h := mul_nonneg (by positivity : 0 ≤ K1 ^ 2 + K2 + 1) hτ.le
    linarith
  · rw [deriv2_langerTau_eq hyx, abs_mul, abs_of_pos hτ]
    have hG0 : 0 ≤ langerG y := by
      unfold langerG; exact div_nonneg hρ0.le (by linarith [cumulN_pos hyx])
    have hGsq : langerG y ^ 2 ≤ K1 ^ 2 / (1 + y) ^ 2 := by
      rw [← div_pow]; exact pow_le_pow_left₀ hG0 hG 2
    have hdiff : |langerG y ^ 2 + langerG' y| ≤ (K1 ^ 2 + K2) / (1 + y) ^ 2 := by
      have e : (K1 ^ 2 + K2) / (1 + y) ^ 2 = K1 ^ 2 / (1 + y) ^ 2 + K2 / (1 + y) ^ 2 := by ring
      rw [e]
      have : |langerG' y| ≤ K2 / (1 + y) ^ 2 := hG'
      calc |langerG y ^ 2 + langerG' y| ≤ |langerG y ^ 2| + |langerG' y| := abs_add_le _ _
        _ ≤ _ := by rw [abs_of_nonneg (sq_nonneg _)]; linarith
    calc langerTau y * |langerG y ^ 2 + langerG' y| ≤ langerTau y * ((K1 ^ 2 + K2) / (1 + y) ^ 2) :=
          mul_le_mul_of_nonneg_left hdiff hτ.le
      _ ≤ (K1 + K1 ^ 2 + K2 + 1) * langerTau y / (1 + y) ^ 2 := by
          rw [mul_div_assoc']
          apply div_le_div_of_nonneg_right _ (by positivity)
          have h := mul_nonneg (by positivity : 0 ≤ K1 + 1) hτ.le
          linarith

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.langerTau_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms langerTau_large

end FormalResearch.ModularBootstrap.Upper.Ramped

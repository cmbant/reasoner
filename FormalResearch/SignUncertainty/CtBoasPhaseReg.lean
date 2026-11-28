/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFarPhase
public import FormalResearch.SignUncertainty.CtBoasPhaseBlock
public import FormalResearch.SignUncertainty.FctTau0Comp
public import FormalResearch.SignUncertainty.CtBoasLmin

/-!
# Higher-order symbol bounds for `τ₀`, `Φ(L) = Φ_Ph(τ₀(L); L)` and `boasX` (`ct:boas` Steps 3–4)

Proves:
- `tau0_iteratedDeriv_bound`: `|τ₀^{(r)}(L)| ≤ C_τ(r) τ₀(L) lamL(L)^r` on `(0, ∞)` (`lamL L = max 1 L⁻¹`);
- `phi_hasDerivAt` & `phi_contDiffOn`: `L ↦ Φ_Ph(τ₀(L); L)` is `C^∞` on `(0, ∞)` with derivative `τ₀`;
- `boasX_deriv_and_symbol`: for `c ≥ c_x`, `ε = ±1`, and `L ≥ ctLv0 c / 4`,
  `boasX c ε` is `C^∞` on `(0, ∞)`, `0.85 c τ₀(L) ≤ (boasX c ε)'(L) ≤ 1.15 c τ₀(L)`, and
  `|∂_L^r (boasX c ε)(L)| ≤ C_X(r) c τ₀(L) lamL(L)^{r-1}` for all `r ≥ 1`.

Class: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.CtOuter FormalResearch.SignUncertainty.FctSym

/-! ### Higher derivatives of `τ₀` via `τ₀' = τ₀ · (τ₀'/τ₀)` -/

theorem tau0_iteratedDeriv_bound (r : ℕ) :
    ∃ C_τ : ℝ, 0 ≤ C_τ ∧ ∀ x : ℝ, 0 < x → |iteratedDeriv r tau0 x| ≤ C_τ * tau0 x * lamL x ^ r := by
  obtain ⟨A, hA0, hA⟩ := tau0_logDeriv_symbol
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    cases r with
    | zero =>
      refine ⟨1, zero_le_one, fun x hx => ?_⟩
      simp only [iteratedDeriv_zero, pow_zero, mul_one, one_mul]
      rw [abs_of_pos (tau0_pos hx)]
    | succ n =>
      choose C ih0 ihB using ih
      let C_fn : ℕ → ℝ := fun k => if hk : k ≤ n then C k (Nat.lt_succ_of_le hk) else 0
      have hC_nn : ∀ k ≤ n, 0 ≤ C_fn k := fun k hk => by
        dsimp only [C_fn]; simp only [hk, ↓reduceDIte]; exact ih0 k (Nat.lt_succ_of_le hk)
      refine ⟨∑ k ∈ range (n + 1), (Nat.choose n k : ℝ) * C_fn k * A (n - k),
        Finset.sum_nonneg fun k hk => by
          have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hC_nn k hk')) (hA0 _), ?_⟩
      intro x hx
      let logD : ℝ → ℝ := fun y => deriv tau0 y / tau0 y
      have hev : deriv tau0 =ᶠ[𝓝 x] fun y => tau0 y * logD y := by
        filter_upwards [Ioi_mem_nhds hx] with y hy
        have hpos : tau0 y ≠ 0 := (tau0_pos hy).ne'
        dsimp only [logD]; rw [mul_div_cancel₀ _ hpos]
      have hcd_τ : ContDiffAt ℝ n tau0 x :=
        (contDiffOn_tau0.contDiffAt (Ioi_mem_nhds hx)).of_le (by simp)
      have hd_τ : ContDiffOn ℝ n (deriv tau0) (Ioi 0) := by
        have hs := (contDiffOn_tau0.of_le (by simp : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ∞))
        rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at hs
        exact hs.2.2
      have hcd_log : ContDiffAt ℝ n logD x :=
        (hd_τ.contDiffAt (Ioi_mem_nhds hx)).div hcd_τ (tau0_pos hx).ne'
      rw [iteratedDeriv_succ', hev.iteratedDeriv_eq n]
      have hleib := iteratedDeriv_mul (x := x) (n := n) hcd_τ hcd_log
      change iteratedDeriv n (fun y => tau0 y * logD y) x = _ at hleib
      rw [hleib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have h1 : |iteratedDeriv k tau0 x| ≤ C_fn k * tau0 x * lamL x ^ k := by
        dsimp only [C_fn]; simp only [hk', ↓reduceDIte]; exact ihB k (Nat.lt_succ_of_le hk') x hx
      have h2 : |iteratedDeriv (n - k) logD x| ≤ A (n - k) * lamL x ^ (n - k + 1) :=
        hA (n - k) x hx
      have hpow : lamL x ^ k * lamL x ^ (n - k + 1) = lamL x ^ (n + 1) := by
        rw [← pow_add]; congr 1; omega
      have hCnn := hC_nn k hk'
      have hτx : 0 < tau0 x := tau0_pos hx
      have hlam := lamL_nonneg x
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ Nat.choose n k)]
      calc (Nat.choose n k : ℝ) * |iteratedDeriv k tau0 x| * |iteratedDeriv (n - k) logD x|
          ≤ (Nat.choose n k : ℝ) * (C_fn k * tau0 x * lamL x ^ k) * (A (n - k) * lamL x ^ (n - k + 1)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _) (by positivity)
        _ = (Nat.choose n k : ℝ) * C_fn k * A (n - k) * tau0 x * (lamL x ^ k * lamL x ^ (n - k + 1)) := by ring
        _ = (Nat.choose n k : ℝ) * C_fn k * A (n - k) * tau0 x * lamL x ^ (n + 1) := by rw [hpow]

/-! ### `HasDerivAt` and `C^∞` regularity for `Φ(L) = edgePhi L (tau0 L)` -/

lemma phi_hasDerivAt {L₀ : ℝ} (hL₀ : 0 < L₀) :
    HasDerivAt (fun L => edgePhi L (tau0 L)) (tau0 L₀) L₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcont : ContinuousAt tau0 L₀ := (contDiffOn_tau0.continuousOn).continuousAt (Ioi_mem_nhds hL₀)
  have hten : Tendsto (fun L => |tau0 L - tau0 L₀|) (𝓝[≠] L₀) (𝓝 0) := by
    have hca : ContinuousAt (fun L => |tau0 L - tau0 L₀|) L₀ := (hcont.sub continuousAt_const).abs
    have ht := hca.tendsto
    rw [sub_self, abs_zero] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hten
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hL₀), self_mem_nhdsWithin] with L hL hne
  have hne' : L - L₀ ≠ 0 := sub_ne_zero.2 hne
  rw [slope_def_field, Real.norm_eq_abs]
  show |((edgePhi L (tau0 L) - edgePhi L₀ (tau0 L₀)) / (L - L₀)) - tau0 L₀| ≤ |tau0 L - tau0 L₀|
  have e : (edgePhi L (tau0 L) - edgePhi L₀ (tau0 L₀)) / (L - L₀) - tau0 L₀ =
      (edgePhi L (tau0 L) - edgePhi L₀ (tau0 L₀) - tau0 L₀ * (L - L₀)) / (L - L₀) := by
    field_simp
  rw [e, abs_div, div_le_iff₀ (abs_pos.2 hne')]
  exact abs_phi_taylor_le hL hL₀

lemma phi_contDiffOn (n : ℕ) : ContDiffOn ℝ n (fun L => edgePhi L (tau0 L)) (Ioi 0) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun L hL => (phi_hasDerivAt hL).continuousAt.continuousWithinAt
  | succ n _ =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
    refine ⟨fun L hL => (phi_hasDerivAt hL).differentiableAt.differentiableWithinAt,
      fun hn => by simp at hn, ?_⟩
    have hcongr : EqOn (deriv (fun L => edgePhi L (tau0 L))) tau0 (Ioi 0) := fun L hL =>
      (phi_hasDerivAt hL).deriv
    exact (contDiffOn_tau0.of_le (by simp)).congr hcongr

/-! ### Derivatives and symbol bounds for `boasX` -/

lemma boasX_contDiffOn {c ε : ℝ} (hε : ε = 1 ∨ ε = -1) (n : ℕ) :
    ContDiffOn ℝ n (boasX c ε) (Ioi 0) := by
  have h1 : ContDiffOn ℝ n (fun L => c * edgePhi L (tau0 L)) (Ioi 0) :=
    contDiffOn_const.mul (phi_contDiffOn n)
  have h2 : ContDiffOn ℝ n (fun L => outerTheta ε (tau0 L)) (Ioi 0) := by
    have hcd_θ : ContDiff ℝ n (outerTheta ε) := by
      rcases hε with rfl | rfl <;> exact (contDiff_outerTheta _).of_le le_top
    exact hcd_θ.contDiffOn.comp (contDiffOn_tau0.of_le (WithTop.coe_le_coe.2 le_top)) (Set.mapsTo_univ _ _)
  exact h1.sub h2

lemma deriv_tau0_mul_le {x : ℝ} (hx : 0 < x) :
    0 < deriv tau0 x ∧ deriv tau0 x ≤ (1 + tau0 x ^ 2) / tau0 x := by
  have ht0 := tau0_pos hx
  have hd := deriv_tau0 hx
  have hm := CtOuter.mPrime_pos ht0
  have hth := theta_ge ht0
  have hpi : (6 : ℝ) ≤ π ^ 2 := by nlinarith only [Real.pi_gt_three]
  refine ⟨by rw [hd]; exact inv_pos.2 hm, ?_⟩
  rw [hd, inv_eq_one_div, div_le_div_iff₀ hm ht0, one_mul]
  have h1 : tau0 x ^ 2 * (6 + (π * tau0 x) ^ 2) ≤ (π * tau0 x) ^ 2 * (1 + tau0 x ^ 2) := by
    nlinarith only [hpi, sq_nonneg (tau0 x)]
  have h2 : tau0 x ^ 2 ≤ (π * tau0 x) ^ 2 / (6 + (π * tau0 x) ^ 2) * (1 + tau0 x ^ 2) := by
    have hp : 0 < 6 + (π * tau0 x) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ hp]
    exact h1
  have h3 : tau0 x ^ 2 ≤ tau0 x * mPrime (tau0 x) * (1 + tau0 x ^ 2) :=
    h2.trans (mul_le_mul_of_nonneg_right hth (by positivity))
  nlinarith only [ht0, h3]

theorem boasX_deriv_and_symbol : ∃ c_x : ℝ, 3 ≤ c_x ∧
    (∀ {c ε : ℝ}, c_x ≤ c → (ε = 1 ∨ ε = -1) → ∀ L : ℝ, ctLv0 c / 4 ≤ L →
      0 < L ∧ HasDerivAt (boasX c ε) (deriv (boasX c ε) L) L ∧
      (0.85 : ℝ) * c * tau0 L ≤ deriv (boasX c ε) L ∧ deriv (boasX c ε) L ≤ (1.15 : ℝ) * c * tau0 L) ∧
    (∀ r : ℕ, 1 ≤ r → ∃ C_X : ℝ, 0 ≤ C_X ∧
      ∀ {c ε : ℝ}, c_x ≤ c → (ε = 1 ∨ ε = -1) → ∀ L : ℝ, ctLv0 c / 4 ≤ L →
        |iteratedDeriv r (boasX c ε) L| ≤ C_X * c * tau0 L * lamL L ^ (r - 1)) := by
  obtain ⟨κ₀, hκ₀, cL, hcL1, hLv0⟩ := ctLv0_facts
  obtain ⟨Cp, hCp⟩ := theta_deriv_poly (ε := 1) (Or.inr rfl) one_pos
  obtain ⟨Cm, hCm⟩ := theta_deriv_poly (ε := -1) (Or.inl rfl) one_pos
  set Cθ1 := max (max Cp Cm) 0 with hCθ1
  set a₀ := (3 / 10 : ℝ) * κ₀ with ha₀
  have ha₀_pos : 0 < a₀ := by positivity
  set b₀ := Real.sqrt (4 / 5 * a₀) with hb₀
  have hb₀_pos : 0 < b₀ := Real.sqrt_pos.2 (by positivity)
  have hev1 : ∀ᶠ c : ℝ in atTop, Cθ1 / (b₀ ^ 2 * c ^ (19 / 21 : ℝ)) ≤ 0.15 := by
    have ht : Tendsto (fun c : ℝ => (Cθ1 / b₀ ^ 2) * c ^ (-(19 / 21 : ℝ))) atTop (𝓝 ((Cθ1 / b₀ ^ 2) * 0)) :=
      tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by norm_num))
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 0.15)),
      eventually_gt_atTop (0 : ℝ)] with c hc hc0
    rw [Real.rpow_neg hc0.le, ← div_eq_mul_inv, div_div] at hc
    exact hc
  have hev2 : ∀ᶠ c : ℝ in atTop, a₀ * c ^ (-(2 / 21 : ℝ)) ≤ 1 ∧ max 1 (a₀⁻¹ * c ^ (2 / 21 : ℝ)) ≤ c := by
    have h1 := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2 / 21)).const_mul a₀).eventually
      (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))
    have h2 : Tendsto (fun c : ℝ => a₀⁻¹ * c ^ (2 / 21 : ℝ) / c) atTop (𝓝 0) := by
      have ht : Tendsto (fun c : ℝ => a₀⁻¹ * c ^ (-(19 / 21 : ℝ))) atTop (𝓝 (a₀⁻¹ * 0)) :=
        tendsto_const_nhds.mul (tendsto_rpow_neg_atTop (by norm_num))
      rw [mul_zero] at ht
      refine ht.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc0
      calc a₀⁻¹ * c ^ (-(19 / 21 : ℝ)) = a₀⁻¹ * (c ^ (2 / 21 : ℝ) * c ^ (-1 : ℝ)) := by
            rw [← Real.rpow_add hc0]; norm_num
        _ = a₀⁻¹ * c ^ (2 / 21 : ℝ) / c := by rw [Real.rpow_neg_one c, ← div_eq_mul_inv, mul_div_assoc]
    have h3 := (h2.eventually (Iic_mem_nhds one_pos)).and (eventually_ge_atTop (1 : ℝ))
    filter_upwards [h1, h3, eventually_gt_atTop (0 : ℝ)] with c hc1 ⟨hc2, hc3⟩ hc0
    refine ⟨hc1, max_le hc3 ?_⟩
    rwa [div_le_one hc0] at hc2
  obtain ⟨c_x, hc_x⟩ := ((eventually_ge_atTop (max 3 cL)).and (hev1.and hev2)).exists_forall_of_atTop
  refine ⟨c_x, (le_max_left _ _).trans (hc_x c_x le_rfl).1, ?_, ?_⟩
  · -- First derivative bounds on `L ≥ ctLv0 c / 4`
    intro c ε hc hε L hL
    obtain ⟨hcM, hc_err, hc_a, hc_lam⟩ := hc_x c hc
    have hc3 : 3 ≤ c := (le_max_left _ _).trans hcM
    have hc0 : 0 < c := by linarith
    have hc_L : cL ≤ c := (le_max_right _ _).trans hcM
    obtain ⟨hL0, _, _, hLκ⟩ := hLv0 c hc_L
    have hL_lb : a₀ * c ^ (-(2 / 21 : ℝ)) ≤ L := by rw [ha₀]; linarith only [hL, hLκ]
    have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lb
    have hτ_pos : 0 < tau0 L := tau0_pos hL_pos
    have hτ_lb : b₀ * c ^ (-(1 / 21 : ℝ)) ≤ tau0 L := by
      have hmin : a₀ * c ^ (-(2 / 21 : ℝ)) ≤ min L 1 := le_min hL_lb hc_a
      have hsq : (4 / 5 : ℝ) * min L 1 ≤ tau0 L ^ 2 := by
        nlinarith only [min_le_left L 1, tau0_sq_ge hL_pos]
      have hb_sq : (b₀ * c ^ (-(1 / 21 : ℝ))) ^ 2 ≤ tau0 L ^ 2 := by
        rw [mul_pow, hb₀, Real.sq_sqrt (by positivity), ← Real.rpow_natCast (c ^ (-(1 / 21 : ℝ))) 2,
          ← Real.rpow_mul hc0.le, show (-(1 / 21 : ℝ)) * ((2 : ℕ) : ℝ) = -(2 / 21) by norm_num]
        calc (4 / 5 * a₀) * c ^ (-(2 / 21 : ℝ)) = (4 / 5) * (a₀ * c ^ (-(2 / 21 : ℝ))) := by ring
          _ ≤ (4 / 5) * min L 1 := mul_le_mul_of_nonneg_left hmin (by norm_num)
          _ ≤ tau0 L ^ 2 := hsq
      nlinarith only [hb_sq, hτ_pos, hb₀_pos, Real.rpow_nonneg hc0.le (-(1 / 21 : ℝ))]
    have hcd_θ : ContDiff ℝ 1 (outerTheta ε) := by
      rcases hε with rfl | rfl <;> exact (contDiff_outerTheta _).of_le le_top
    have hd_θ : HasDerivAt (outerTheta ε) (deriv (outerTheta ε) (tau0 L)) (tau0 L) :=
      (hcd_θ.differentiable one_ne_zero (tau0 L)).hasDerivAt
    have hd_τ : HasDerivAt tau0 (deriv tau0 L) L :=
      ((contDiffOn_tau0.differentiableOn (by simp) L hL_pos).differentiableAt (Ioi_mem_nhds hL_pos)).hasDerivAt
    have hd_X : HasDerivAt (boasX c ε) (c * tau0 L - deriv (outerTheta ε) (tau0 L) * deriv tau0 L) L := by
      unfold boasX
      exact ((phi_hasDerivAt hL_pos).const_mul c).sub (hd_θ.comp L hd_τ)
    have hθ_bd : |deriv (outerTheta ε) (tau0 L)| ≤ Cθ1 / (1 + tau0 L ^ 2) := by
      have h1 : |iteratedDeriv 1 (outerTheta ε) (tau0 L)| ≤ Cθ1 / (1 + |tau0 L|) ^ 2 := by
        rcases hε with rfl | rfl
        · refine (hCp (tau0 L)).trans (div_le_div_of_nonneg_right ((le_max_left _ _).trans (le_max_left _ _)) (by positivity))
        · refine (hCm (tau0 L)).trans (div_le_div_of_nonneg_right ((le_max_right _ _).trans (le_max_left _ _)) (by positivity))
      rw [iteratedDeriv_one, abs_of_pos hτ_pos] at h1
      have hsq : 1 + tau0 L ^ 2 ≤ (1 + tau0 L) ^ 2 := by nlinarith only [hτ_pos]
      exact h1.trans (div_le_div_of_nonneg_left (by positivity) (by positivity) hsq)
    have hτd := deriv_tau0_mul_le hL_pos
    have herr : |deriv (outerTheta ε) (tau0 L) * deriv tau0 L| ≤ 0.15 * c * tau0 L := by
      have hmul : |deriv (outerTheta ε) (tau0 L) * deriv tau0 L| ≤ Cθ1 / tau0 L := by
        rw [abs_mul, abs_of_pos hτd.1]
        calc |deriv (outerTheta ε) (tau0 L)| * deriv tau0 L
            ≤ (Cθ1 / (1 + tau0 L ^ 2)) * ((1 + tau0 L ^ 2) / tau0 L) :=
              mul_le_mul hθ_bd hτd.2 hτd.1.le (by positivity)
          _ = Cθ1 / tau0 L := by field_simp
      have htau_sq : b₀ ^ 2 * c ^ (-(2 / 21 : ℝ)) ≤ tau0 L ^ 2 := by
        have := pow_le_pow_left₀ (by positivity) hτ_lb 2
        rwa [mul_pow, ← Real.rpow_natCast (c ^ (-(1 / 21 : ℝ))) 2, ← Real.rpow_mul hc0.le,
          show (-(1 / 21 : ℝ)) * ((2 : ℕ) : ℝ) = -(2 / 21) by norm_num] at this
      have hratio : Cθ1 / (c * tau0 L ^ 2) ≤ 0.15 := by
        have hden : b₀ ^ 2 * c ^ (19 / 21 : ℝ) ≤ c * tau0 L ^ 2 := by
          have : c * (c ^ (-(2 / 21 : ℝ))) = c ^ (19 / 21 : ℝ) := by
            calc c * c ^ (-(2 / 21 : ℝ)) = c ^ (1 : ℝ) * c ^ (-(2 / 21 : ℝ)) := by rw [Real.rpow_one]
              _ = c ^ (19 / 21 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
          calc b₀ ^ 2 * c ^ (19 / 21 : ℝ) = c * (b₀ ^ 2 * c ^ (-(2 / 21 : ℝ))) := by rw [← this]; ring
            _ ≤ c * tau0 L ^ 2 := mul_le_mul_of_nonneg_left htau_sq hc0.le
        exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans hc_err
      calc |deriv (outerTheta ε) (tau0 L) * deriv tau0 L| ≤ Cθ1 / tau0 L := hmul
        _ = (Cθ1 / (c * tau0 L ^ 2)) * (c * tau0 L) := by field_simp
        _ ≤ 0.15 * (c * tau0 L) := mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = 0.15 * c * tau0 L := by ring
    refine ⟨hL_pos, ?_, ?_, ?_⟩
    · rw [hd_X.deriv]; exact hd_X
    · rw [hd_X.deriv]; linarith only [(abs_le.1 herr).2]
    · rw [hd_X.deriv]; linarith only [(abs_le.1 herr).1]
  · -- Higher derivatives for `r ≥ 1`
    intro r hr
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hr)
    obtain ⟨Cτ, hCτ0, hCτ⟩ := tau0_iteratedDeriv_bound m
    obtain ⟨A, hA0, hA⟩ := comp_tau0_shift
    choose Cp hCp using fun j : ℕ => theta_deriv_poly (ε := 1) (Or.inr rfl) (Nat.succ_pos j)
    choose Cm hCm using fun j : ℕ => theta_deriv_poly (ε := -1) (Or.inl rfl) (Nat.succ_pos j)
    let P : ℕ → ℝ := fun j => max (max (Cp j) (Cm j)) 0
    have hP0 : ∀ j, 0 ≤ P j := fun j => le_max_right _ _
    choose Cτ_s hCτs0 hCτs using
      fun k : ℕ => tau0_iteratedDeriv_bound (k + 1)
    let Cθ_m : ℕ → ℝ := fun k => chainM P (fun j => (j : ℝ)) A 1 k 0
    have hCθ_nn : ∀ k, 0 ≤ Cθ_m k := fun k => chainM_nonneg hP0 k 0
    have hC_sum_nn : 0 ≤ Cτ + ∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k) :=
      add_nonneg hCτ0 (Finset.sum_nonneg fun k _ =>
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCθ_nn k)) (hCτs0 (m - k)))
    refine ⟨Cτ + ∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k), hC_sum_nn, ?_⟩
    intro c ε hc hε L hL
    obtain ⟨hcM, _, hc_a, hc_lam⟩ := hc_x c hc
    have hc0 : 0 < c := by linarith only [(le_max_left _ _).trans hcM]
    have hc_L : cL ≤ c := (le_max_right _ _).trans hcM
    obtain ⟨_, _, _, hLκ⟩ := hLv0 c hc_L
    have hL_lb : a₀ * c ^ (-(2 / 21 : ℝ)) ≤ L := by rw [ha₀]; linarith only [hL, hLκ]
    have hL_pos : 0 < L := lt_of_lt_of_le (by positivity) hL_lb
    have hlam_le_c : lamL L ≤ c := by
      have hinv : L⁻¹ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ) := by
        rw [inv_eq_one_div, div_le_iff₀ hL_pos]
        have hcp : c ^ (2 / 21 : ℝ) * c ^ (-(2 / 21 : ℝ)) = 1 := by rw [← Real.rpow_add hc0]; norm_num
        calc (1 : ℝ) = a₀⁻¹ * c ^ (2 / 21 : ℝ) * (a₀ * c ^ (-(2 / 21 : ℝ))) := by
              rw [mul_mul_mul_comm, inv_mul_cancel₀ ha₀_pos.ne', hcp, mul_one]
          _ ≤ a₀⁻¹ * c ^ (2 / 21 : ℝ) * L := mul_le_mul_of_nonneg_left hL_lb (by positivity)
      exact (max_le (le_max_left _ _) (hinv.trans (le_max_right _ _))).trans hc_lam
    -- Rewrite `iteratedDeriv (m + 1) (boasX c ε) L` via `deriv` on `Ioi 0`
    have hcd_θ : ContDiff ℝ ∞ (outerTheta ε) := by
      rcases hε with rfl | rfl <;> exact (contDiff_outerTheta _).of_le (by simp)
    have hcd_θd : ContDiff ℝ ∞ (deriv (outerTheta ε)) := by
      have hω : ContDiff ℝ (∞ + 1) (outerTheta ε) := by
        rcases hε with rfl | rfl <;> exact (contDiff_outerTheta _).of_le le_top
      exact hω.deriv'
    have hcomp_deriv : deriv (boasX c ε) =ᶠ[𝓝 L] fun y => c * tau0 y - deriv (outerTheta ε) (tau0 y) * deriv tau0 y := by
      filter_upwards [Ioi_mem_nhds hL_pos] with y hy
      have hdθ : HasDerivAt (outerTheta ε) (deriv (outerTheta ε) (tau0 y)) (tau0 y) :=
        (hcd_θ.differentiable (by simp) (tau0 y)).hasDerivAt
      have hdτ : HasDerivAt tau0 (deriv tau0 y) y :=
        ((contDiffOn_tau0.differentiableOn (by simp) y hy).differentiableAt (Ioi_mem_nhds hy)).hasDerivAt
      unfold boasX
      exact (((phi_hasDerivAt hy).const_mul c).sub (hdθ.comp y hdτ)).deriv
    rw [iteratedDeriv_succ', hcomp_deriv.iteratedDeriv_eq m]
    have hcd_τm : ContDiffAt ℝ m tau0 L :=
      (contDiffOn_tau0.contDiffAt (Ioi_mem_nhds hL_pos)).of_le (by simp)
    have hcd_1 : ContDiffAt ℝ m (fun y => c * tau0 y) L :=
      contDiffAt_const.mul hcd_τm
    have hcd_2a : ContDiffAt ℝ m (fun y => deriv (outerTheta ε) (tau0 y)) L :=
      (hcd_θd.of_le (by simp)).contDiffAt.comp L hcd_τm
    have hcd_2b : ContDiffAt ℝ m (deriv tau0) L := by
      have hs := (contDiffOn_tau0.of_le (by simp : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ ∞))
      rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at hs
      exact hs.2.2.contDiffAt (Ioi_mem_nhds hL_pos)
    have hsmul : iteratedDeriv m (fun y => c * tau0 y) L = c * iteratedDeriv m tau0 L := by
      simp [iteratedDeriv_const_smul (𝕜 := ℝ) c hcd_τm]
    rw [iteratedDeriv_fun_sub hcd_1 (hcd_2a.mul hcd_2b), hsmul, iteratedDeriv_fun_mul hcd_2a hcd_2b]
    -- bound second term via `comp_tau0_shift` at `x₀ = L, s = 0`
    have hbase : ∀ j x, L ≤ x → |tau0 (x - 0) ^ j * iteratedDeriv j (deriv (outerTheta ε)) (tau0 (x - 0))| ≤ P j * 1 := by
      intro j x hx
      rw [sub_zero, ← iteratedDeriv_succ', mul_one]
      have hx0 : 0 < x := lt_of_lt_of_le hL_pos hx
      have hτx := tau0_pos hx0
      have hbd : |iteratedDeriv (j + 1) (outerTheta ε) (tau0 x)| ≤ P j / (1 + tau0 x) ^ (j + 2) := by
        rcases hε with rfl | rfl
        · have h1 := hCp j (tau0 x); rw [abs_of_pos hτx] at h1
          exact h1.trans (div_le_div_of_nonneg_right ((le_max_left (Cp j) (Cm j)).trans (le_max_left _ _)) (by positivity))
        · have h1 := hCm j (tau0 x); rw [abs_of_pos hτx] at h1
          exact h1.trans (div_le_div_of_nonneg_right ((le_max_right (Cp j) (Cm j)).trans (le_max_left _ _)) (by positivity))
      rw [abs_mul, abs_pow, abs_of_pos hτx]
      have hpow_le : tau0 x ^ j ≤ (1 + tau0 x) ^ (j + 2) :=
        (pow_le_pow_left₀ hτx.le (by linarith only) j).trans
          (pow_le_pow_right₀ (by linarith only [hτx]) (by omega))
      calc tau0 x ^ j * |iteratedDeriv (j + 1) (outerTheta ε) (tau0 x)|
          ≤ tau0 x ^ j * (P j / (1 + tau0 x) ^ (j + 2)) := mul_le_mul_of_nonneg_left hbd (by positivity)
        _ = P j * (tau0 x ^ j / (1 + tau0 x) ^ (j + 2)) := by ring
        _ ≤ P j * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).2 hpow_le) (hP0 j)
        _ = P j := mul_one _
    have hθ_comp : ∀ k : ℕ, |iteratedDeriv k (fun y => deriv (outerTheta ε) (tau0 y)) L| ≤ Cθ_m k * lamL L ^ k := by
      intro k
      have hg_cd : ContDiffOn ℝ ∞ (deriv (outerTheta ε)) (Ioi 0) :=
        hcd_θd.contDiffOn
      have := hA hL_pos (by rw [abs_zero]; exact (half_pos hL_pos).le) hg_cd hP0 (fun _ _ => zero_le_one) hbase k L le_rfl
      simpa [Cθ_m, sub_zero, mul_one] using this
    have hτd_bd : ∀ k : ℕ, |iteratedDeriv k (deriv tau0) L| ≤ Cτ_s k * tau0 L * lamL L ^ (k + 1) := fun k => by
      rw [← iteratedDeriv_succ']
      exact hCτs k L hL_pos
    have hsum_bd : |∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) *
        iteratedDeriv k (fun y => deriv (outerTheta ε) (tau0 y)) L * iteratedDeriv (m - k) (deriv tau0) L| ≤
        (∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k)) * c * tau0 L * lamL L ^ m := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hpow : lamL L ^ k * lamL L ^ (m - k + 1) = lamL L ^ (m + 1) := by
        rw [← pow_add]; congr 1; omega
      have hlam_c : lamL L ^ (m + 1) ≤ c * lamL L ^ m := by
        rw [pow_succ']
        exact mul_le_mul_of_nonneg_right hlam_le_c (pow_nonneg (lamL_nonneg L) m)
      have hCθk := hCθ_nn k
      have hCτmk := hCτs0 (m - k)
      have hlam := lamL_nonneg L
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ Nat.choose m k)]
      calc (Nat.choose m k : ℝ) * |iteratedDeriv k (fun y => deriv (outerTheta ε) (tau0 y)) L| *
            |iteratedDeriv (m - k) (deriv tau0) L|
          ≤ (Nat.choose m k : ℝ) * (Cθ_m k * lamL L ^ k) * (Cτ_s (m - k) * tau0 L * lamL L ^ (m - k + 1)) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hθ_comp k) (Nat.cast_nonneg _)) (hτd_bd (m - k)) (abs_nonneg _) (by positivity)
        _ = (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k) * tau0 L * lamL L ^ (m + 1) := by
            rw [← hpow]; ring
        _ ≤ (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k) * tau0 L * (c * lamL L ^ m) :=
            mul_le_mul_of_nonneg_left hlam_c (mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCθ_nn k)) (hCτs0 (m - k))) (tau0_pos hL_pos).le)
        _ = (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k) * c * tau0 L * lamL L ^ m := by ring
    have h1_bd : |c * iteratedDeriv m tau0 L| ≤ Cτ * c * tau0 L * lamL L ^ m := by
      rw [abs_mul, abs_of_pos hc0]
      exact (mul_le_mul_of_nonneg_left (hCτ L hL_pos) hc0.le).trans_eq (by ring)
    calc |c * iteratedDeriv m tau0 L - ∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) *
            iteratedDeriv k (fun y => deriv (outerTheta ε) (tau0 y)) L * iteratedDeriv (m - k) (deriv tau0) L|
        ≤ |c * iteratedDeriv m tau0 L| + |∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) *
            iteratedDeriv k (fun y => deriv (outerTheta ε) (tau0 y)) L * iteratedDeriv (m - k) (deriv tau0) L| :=
          abs_sub _ _
      _ ≤ Cτ * c * tau0 L * lamL L ^ m +
            (∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k)) * c * tau0 L * lamL L ^ m :=
          add_le_add h1_bd hsum_bd
      _ = (Cτ + ∑ k ∈ range (m + 1), (Nat.choose m k : ℝ) * Cθ_m k * Cτ_s (m - k)) * c * tau0 L * lamL L ^ m := by
          ring

end FormalResearch.SignUncertainty

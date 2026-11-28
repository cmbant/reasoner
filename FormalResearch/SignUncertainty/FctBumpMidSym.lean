/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctBumpPhysBounds
public import FormalResearch.SignUncertainty.FctNSymbol
public import FormalResearch.SignUncertainty.FctQTSym

/-!
# Tight middle-band symbol bound for `p₁ = χ(·/3δ) γ (O - F)` (`fct:bump-sym-check` on `[3δ/2, 3δ]`)

Proves `physDiff_mid_symW`: for `K4 ≥ 1`, `hwarp : FctWarpZeroStmt T1 alpha`, `hχ : IsCutoff χ`, on
`S = Icc (3 / 2 * physDelta c) (3 * physDelta c)`, the main difference piece
`p₁(x) = χ(x / (3 * physDelta c)) * physGamma c (physShift ε c) x * (O x - F x)` satisfies
`SymW (Icc (3 / 2 * physDelta c) (3 * physDelta c)) (fun _ => C_diff * c ^ (-(1 / 4 : ℝ))) K_diff p₁`
for `c ≥ c₀(K4)` (with `C_diff, K_diff, c₀` independent of `K1`).

The extra factor `c⁻¹` relative to the global `(1/2, 3/2)` symbol weight comes from:
* `mid_vacP_eq` reducing `Q` to `e^{-K₄ t⁴ + α t²} (e^{-Δ}(1 + Δ))` (`t = τ₀(x - s) ≤ 2 τ₁`),
  where `K₄ t⁴ + |α| t² = O_{K₄}(c⁻¹)` and `e^{-Δ}(1 + Δ) - 1 = O_{K₄}(τ₁⁶) = O_{K₄}(c^{-3/2})`;
* `block_small` + `sqrtG` giving `|1 - L₁ φ_kill(iτ₀(x - s); a) / (x - s)| - 1 = O(x³) = O(c^{-3/2})`.

Combined with `F(x) = O(δ^{-3/2}) = O(c^{3/4})`, this yields `O_{K₄}(c^{-1/4})` (`≪ c^{+1/4}`), so
`bump_weighted_local` on `[3δ/4, 3δ]` produces an `O_{K₄}(c^{-7/4})` error (`≪ η₀ I_fl ~ K₀ c^{-19/12}`).

Class: proved.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Finset
open scoped Real ContDiff
open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym
open FormalResearch.SignUncertainty.FctCompD FormalResearch.SignUncertainty.FctMoment

namespace FormalResearch.SignUncertainty

private lemma iteratedDeriv_comp_const_mul' (k : ℕ) (f : ℝ → ℝ) (a : ℝ) :
    ∀ x : ℝ, iteratedDeriv k (fun t => f (a * t)) x = a ^ k * iteratedDeriv k f (a * x) := by
  induction k with
  | zero => intro x; simp
  | succ k ih =>
    intro x
    rw [iteratedDeriv_succ, show iteratedDeriv k (fun t => f (a * t)) =
        fun t => a ^ k * iteratedDeriv k f (a * t) from funext ih,
      deriv_const_mul_field']
    dsimp only
    rw [deriv_comp_mul_left a (iteratedDeriv k f) x, ← iteratedDeriv_succ, pow_succ]
    ring

/-- Any `IsCutoff χ` has uniform derivative bounds `|iteratedDeriv r χ s| ≤ Kχ r` on `ℝ`. -/
lemma isCutoff_deriv_bound {χ : ℝ → ℝ} (hχ : IsCutoff χ) :
    ∃ Kχ : ℕ → ℝ, (∀ r, 0 ≤ Kχ r) ∧ ∀ r : ℕ, ∀ s : ℝ, |iteratedDeriv r χ s| ≤ Kχ r := by
  have hb : ∀ r : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℝ, |iteratedDeriv r χ s| ≤ M := fun r => by
    have hc : ContinuousOn (iteratedDeriv r χ) (Icc (1 / 2 : ℝ) 1) :=
      ((hχ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedDeriv r
        (WithTop.coe_le_coe.mpr le_top)).continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨max (max M 1) 0, le_max_right _ _, fun s => ?_⟩
    rcases le_or_gt s (1 / 2) with hs0 | hs0
    · cases r with
      | zero =>
        simp only [iteratedDeriv_zero]
        rw [hχ.zero s hs0, abs_zero]
        exact le_max_right _ _
      | succ k =>
        by_cases hlt : s < 1 / 2
        · have hev : χ =ᶠ[𝓝 s] (0 : ℝ → ℝ) :=
            Filter.eventually_of_mem (Iio_mem_nhds hlt) fun y hy => hχ.zero y hy.le
          rw [hev.iteratedDeriv_eq (k + 1), iteratedDeriv_const_zero, abs_zero]
          exact le_max_right _ _
        · have hs_eq : s = 1 / 2 := le_antisymm hs0 (not_lt.mp hlt)
          rw [hs_eq]
          have h1 : |iteratedDeriv (k + 1) χ (1 / 2)| ≤ M := by
            simpa [Real.norm_eq_abs] using hM (1 / 2) ⟨le_rfl, by norm_num⟩
          exact h1.trans ((le_max_left _ _).trans (le_max_left _ _))
    · rcases le_or_gt s 1 with hs1 | hs1
      · have h1 : |iteratedDeriv r χ s| ≤ M := by
          simpa [Real.norm_eq_abs] using hM s ⟨hs0.le, hs1⟩
        exact h1.trans ((le_max_left _ _).trans (le_max_left _ _))
      · have hev : χ =ᶠ[𝓝 s] (1 : ℝ → ℝ) :=
          Filter.eventually_of_mem (Ioi_mem_nhds hs1) fun y hy => hχ.one y hy.le
        rw [hev.iteratedDeriv_eq r]
        cases r with
        | zero =>
          simp only [iteratedDeriv_zero, Pi.one_apply, abs_one]
          exact (le_max_right _ _).trans (le_max_left _ _)
        | succ k =>
          rw [show (1 : ℝ → ℝ) = fun _ => (1 : ℝ) from rfl, iteratedDeriv_succ']
          simp only [deriv_const', iteratedDeriv_const_zero, abs_zero]
          exact le_max_right _ _
  choose Kχ hK0 hK using hb
  exact ⟨Kχ, hK0, hK⟩

/-- Dilated cutoff `x ↦ χ (x / (3 * δ))` belongs to `SymW (Ici (3 / 2 * δ)) (fun _ => 1) Kχ`. -/
lemma cutoff_dil_symW {χ : ℝ → ℝ} (hχ : IsCutoff χ) {Kχ : ℕ → ℝ} (hKχ0 : ∀ r, 0 ≤ Kχ r)
    (hKχ : ∀ r : ℕ, ∀ s : ℝ, |iteratedDeriv r χ s| ≤ Kχ r) {δ : ℝ} (hδ : 0 < δ) :
    SymW (Ici (3 / 2 * δ)) (fun _ => 1) Kχ (fun x => χ (x / (3 * δ))) where
  pos _ hx := lt_of_lt_of_le (by positivity) hx
  smooth := ⟨univ, isOpen_univ, subset_univ _,
    (hχ.smooth.comp (contDiff_id.div_const (3 * δ))).contDiffOn⟩
  K_nonneg := hKχ0
  w_nonneg _ _ := zero_le_one
  bound r x hx := by
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
    have hmul_eq : (fun y : ℝ => χ (y / (3 * δ))) = fun y => χ ((3 * δ)⁻¹ * y) := by
      funext y; rw [div_eq_inv_mul]
    rw [hmul_eq, iteratedDeriv_comp_const_mul']
    cases r with
    | zero =>
      simp only [pow_zero, one_mul, inv_one, mul_one]
      exact hKχ 0 ((3 * δ)⁻¹ * x)
    | succ k =>
      rcases le_or_gt x (3 * δ) with hle | hgt
      · rw [abs_mul, abs_pow, abs_of_pos (inv_pos.mpr (by positivity))]
        have hinv : ((3 * δ)⁻¹) ^ (k + 1) ≤ (x ^ (k + 1))⁻¹ := by
          rw [← inv_pow]
          exact pow_le_pow_left₀ (inv_nonneg.mpr (by positivity)) (inv_anti₀ hx0 hle) (k + 1)
        calc |iteratedDeriv (k + 1) χ ((3 * δ)⁻¹ * x)| * ((3 * δ)⁻¹) ^ (k + 1)
            ≤ Kχ (k + 1) * (x ^ (k + 1))⁻¹ := by
              rw [mul_comm]
              exact mul_le_mul (hKχ (k + 1) _) hinv (by positivity) (hKχ0 _)
          _ = Kχ (k + 1) * 1 * (x ^ (k + 1))⁻¹ := by ring
      · have hev : (fun y => χ (y / (3 * δ))) =ᶠ[𝓝 x] (1 : ℝ → ℝ) := by
          filter_upwards [Ioi_mem_nhds hgt] with y hy
          exact hχ.one _ (by rw [le_div_iff₀ (by positivity)]; linarith only [hy.out])
        have hz : iteratedDeriv (k + 1) (fun y => χ (y / (3 * δ))) x = 0 := by
          rw [hev.iteratedDeriv_eq (k + 1), show (1 : ℝ → ℝ) = fun _ => (1 : ℝ) from rfl,
            iteratedDeriv_succ']
          simp
        rw [hmul_eq, iteratedDeriv_comp_const_mul'] at hz
        rw [hz, abs_zero]
        exact mul_nonneg (mul_nonneg (hKχ0 _) zero_le_one) (inv_nonneg.mpr (pow_nonneg hx0.le _))

/-- `vacP` on `(0, 2 * τ₁]` reduces cleanly to `e^{-K₄ t⁴ + α t²} e^{-Δ} (1 + Δ)`. -/
private lemma mid_vacP_eq :
    ∃ τc : ℝ, 0 < τc ∧ ∀ {K4 c α τ₁ t : ℝ}, 1 ≤ K4 → 0 < c → 0 < τ₁ → τ₁ ≤ τc → τ₁ ^ 4 * c = 1 →
      |α| ≤ τ₁ ^ 2 → 0 < t → t ≤ 2 * τ₁ →
      vacP StripKernelChoice.star K4 c α τ₁ (uctM t) = uctIfl (uctM t) *
        (Real.exp (-(K4 * t ^ 4) + α * t ^ 2) *
          (Real.exp (-stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t) *
            (1 + stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t))) := by
  obtain ⟨τc, hτc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpart1⟩ :=
    fct_comp_D_part1 StripKernelChoice.star
  refine ⟨τc, hτc, fun {K4 c α τ₁ t} hK4 hc0 hτ₁pos hτc' hτ₁_four hα_bd htpos ht2 => ?_⟩
  obtain ⟨⟨_, _, _, _, _, _⟩, _, _, _, _, hinner, _⟩ :=
    hpart1 hK4 hc0 hτ₁pos hτc' hτ₁_four hα_bd
  have hin := ((hinner t (by rw [abs_of_pos htpos]; exact ht2)).2.2.2.2.2 htpos.ne').2.2
  have hr0 := stripR0_pos StripKernelChoice.star htpos
  have hu_pos := uctM_pos htpos
  have hv := vacP_eq StripKernelChoice.star K4 c α τ₁ hu_pos
  have htau_id : tau0 (uctM t) = t := by
    rw [show uctM t = ceEll (Real.pi * t / 2) from rfl, tau0_ceEll htpos]
  rw [htau_id] at hv
  rw [hv]
  have hratio : stripIosc StripKernelChoice.star (uctM t) / uctIfl (uctM t) = stripR0 StripKernelChoice.star t :=
    (stripR0_eq_div htpos).symm
  rw [hratio] at hin
  set Δ := stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) t
  have hexp : stripR0 StripKernelChoice.star t * Real.exp (vTotal StripKernelChoice.star K4 c α τ₁ t) * (1 + Δ) =
      Real.exp (-(K4 * t ^ 4) + α * t ^ 2) * (Real.exp (-Δ) * (1 + Δ)) := by
    rw [hin, show -Real.log (stripR0 StripKernelChoice.star t) - K4 * t ^ 4 - Δ + α * t ^ 2 =
      -Real.log (stripR0 StripKernelChoice.star t) + ((-(K4 * t ^ 4) + α * t ^ 2) + -Δ) by ring,
      Real.exp_add, Real.exp_add, Real.exp_neg, Real.exp_log hr0]
    field_simp
  have hqd : vacQD StripKernelChoice.star K4 c α τ₁ t + 1 =
      stripR0 StripKernelChoice.star t * Real.exp (vTotal StripKernelChoice.star K4 c α τ₁ t) * (1 + Δ) := by
    unfold vacQD; ring
  rw [hqd, hexp]

/-- Polynomial derivatives `|t^j ∂_t^j (-K₄ t⁴ + α t²)| ≤ 24 (K₄ t⁴ + |α| t²)` for `t ≥ 0`. -/
private lemma poly42_deriv_bound (K4 α : ℝ) (hK4 : 0 ≤ K4) (j : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |t ^ j * iteratedDeriv j (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) t| ≤
      24 * (K4 * t ^ 4 + |α| * t ^ 2) := by
  have h0 : 0 ≤ K4 * t ^ 4 := by positivity
  have h1 : 0 ≤ |α| * t ^ 2 := by positivity
  have hd1_fn : deriv (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) = fun u => -(4 * K4 * u ^ 3) + 2 * α * u := by
    funext u
    have hp : HasDerivAt (fun w : ℝ => -(K4 * w ^ 4) + α * w ^ 2) (-(K4 * (4 * u ^ 3)) + α * (2 * u)) u :=
      (((hasDerivAt_pow 4 u).const_mul K4).neg).add (by simpa using (hasDerivAt_pow 2 u).const_mul α)
    rw [hp.deriv]; ring
  have hd2_fn : iteratedDeriv 2 (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) = fun u => -(12 * K4 * u ^ 2) + 2 * α := by
    funext u
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', hd1_fn, iteratedDeriv_one]
    have hp2 : HasDerivAt (fun w : ℝ => -(4 * K4 * w ^ 3) + 2 * α * w) (-(4 * K4 * (3 * u ^ 2)) + 2 * α * 1) u :=
      (((hasDerivAt_pow 3 u).const_mul (4 * K4)).neg).add ((hasDerivAt_id u).const_mul (2 * α))
    rw [hp2.deriv]; ring
  have hd3_fn : iteratedDeriv 3 (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) = fun u => -(24 * K4 * u) := by
    funext u
    rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ, hd2_fn]
    have hp3 : HasDerivAt (fun w : ℝ => -(12 * K4 * w ^ 2) + 2 * α) (-(12 * K4 * (2 * u)) + 0) u :=
      (((hasDerivAt_pow 2 u).const_mul (12 * K4)).neg).add_const (2 * α)
    rw [hp3.deriv]; ring
  have hd4_fn : iteratedDeriv 4 (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) = fun _ => -(24 * K4) := by
    funext u
    rw [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_succ, hd3_fn]
    have hp4 : HasDerivAt (fun w : ℝ => -(24 * K4 * w)) (-(24 * K4 * 1)) u :=
      ((hasDerivAt_id u).const_mul (24 * K4)).neg
    rw [hp4.deriv]; ring
  match j with
  | 0 =>
    simp only [pow_zero, one_mul, iteratedDeriv_zero]
    have hα : |α * t ^ 2| = |α| * t ^ 2 := by rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
    calc |-(K4 * t ^ 4) + α * t ^ 2| ≤ |-(K4 * t ^ 4)| + |α * t ^ 2| := abs_add_le _ _
      _ = K4 * t ^ 4 + |α| * t ^ 2 := by rw [abs_neg, abs_of_nonneg h0, hα]
      _ ≤ 24 * (K4 * t ^ 4 + |α| * t ^ 2) := by linarith only [h0, h1]
  | 1 =>
    rw [iteratedDeriv_one, pow_one, hd1_fn,
      show t * (-(4 * K4 * t ^ 3) + 2 * α * t) = -(4 * K4 * t ^ 4) + 2 * α * t ^ 2 by ring]
    have hα : |2 * α * t ^ 2| = 2 * |α| * t ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg (sq_nonneg t)]
    calc |-(4 * K4 * t ^ 4) + 2 * α * t ^ 2| ≤ |-(4 * K4 * t ^ 4)| + |2 * α * t ^ 2| := abs_add_le _ _
      _ = 4 * K4 * t ^ 4 + 2 * |α| * t ^ 2 := by rw [abs_neg, abs_of_nonneg (by linarith only [h0]), hα]
      _ ≤ 24 * (K4 * t ^ 4 + |α| * t ^ 2) := by linarith only [h0, h1]
  | 2 =>
    rw [hd2_fn, show t ^ 2 * (-(12 * K4 * t ^ 2) + 2 * α) = -(12 * K4 * t ^ 4) + 2 * α * t ^ 2 by ring]
    have hα : |2 * α * t ^ 2| = 2 * |α| * t ^ 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num), abs_of_nonneg (sq_nonneg t)]
    calc |-(12 * K4 * t ^ 4) + 2 * α * t ^ 2| ≤ |-(12 * K4 * t ^ 4)| + |2 * α * t ^ 2| := abs_add_le _ _
      _ = 12 * K4 * t ^ 4 + 2 * |α| * t ^ 2 := by rw [abs_neg, abs_of_nonneg (by linarith only [h0]), hα]
      _ ≤ 24 * (K4 * t ^ 4 + |α| * t ^ 2) := by linarith only [h0, h1]
  | 3 =>
    rw [hd3_fn, show t ^ 3 * -(24 * K4 * t) = -(24 * K4 * t ^ 4) by ring, abs_neg,
      abs_of_nonneg (by linarith only [h0])]
    linarith only [h0, h1]
  | 4 =>
    rw [hd4_fn, show t ^ 4 * -(24 * K4) = -(24 * K4 * t ^ 4) by ring, abs_neg,
      abs_of_nonneg (by linarith only [h0])]
    linarith only [h0, h1]
  | k + 5 =>
    have hd5 : iteratedDeriv (k + 1 + 4) (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) t = 0 := by
      rw [iteratedDeriv_add, hd4_fn, iteratedDeriv_const]
      simp [Nat.succ_ne_zero k]
    have hzero : iteratedDeriv (k + 5) (fun u : ℝ => -(K4 * u ^ 4) + α * u ^ 2) t = 0 := by
      simpa [show k + 5 = k + 1 + 4 by omega] using hd5
    rw [hzero, mul_zero, abs_zero]
    positivity

/-- Factor A: `exp(-K₄ t⁴ + α t²) - 1` on `[3δ/2, 3δ]` has weight `CA(K₄) * c⁻¹` (`CA` independent of `K₁`). -/
private lemma mid_factorA_symW {K4 : ℝ} (hK4 : 1 ≤ K4) {T1 alpha : ℝ → ℝ → ℝ}
    (hwarp : FctWarpZeroStmt T1 alpha) :
    ∃ (c₀ CA : ℝ) (KA : ℕ → ℝ), 2 ≤ c₀ ∧ 0 ≤ CA ∧ (∀ r, 0 ≤ KA r) ∧
      ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        SymW (Icc (3 / 2 * physDelta c) (3 * physDelta c)) (fun _ => CA * c⁻¹) KA
          (fun x => Real.exp (-(K4 * tau0 (x - physShift ε c) ^ 4) + alpha ε c * tau0 (x - physShift ε c) ^ 2) - 1) := by
  obtain ⟨Cw, cw, hw⟩ := hwarp
  obtain ⟨Kα, cα, hαf⟩ : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).2⟩
  have hKα0 : 0 ≤ Kα := by
    have := hαf 1 (max cα 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cα 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (alpha 1 (max cα 1))]
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 (fun ε c hε hc => (hw ε c hε hc).1)
  obtain ⟨c₁, hc₁1, hc₁⟩ := FctSym.exists_rpow_neg_le (p := 1 / 4) (η := (1 / 20 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨c₂, hc₂1, hc₂⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2) (η := 1 / (6 * (|a₁| + 1))) (by norm_num)
    (one_div_pos.mpr (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg a₁) one_pos)))
  obtain ⟨A, hA0, hcomp⟩ := comp_tau0_shift
  set CA0 : ℝ := 16 * K4 + 4 * Kα + 1 with hCA0
  have hCA0_pos : 0 < CA0 := by positivity
  have hck_ex : ∃ c_k : ℝ, 2 ≤ c_k ∧ ∀ c : ℝ, c_k ≤ c → CA0 * c⁻¹ ≤ 1 := by
    refine ⟨max 2 (CA0 + 1), le_max_left _ _, fun c hc => ?_⟩
    have hcpos : 0 < c := by linarith [le_max_left 2 (CA0 + 1) |>.trans hc]
    rw [mul_inv_le_iff₀ hcpos]; linarith [le_max_right 2 (CA0 + 1) |>.trans hc]
  obtain ⟨c_k, hck2, hck⟩ := hck_ex
  set Kraw : ℕ → ℝ := fun r => chainM (fun _ => 24) (fun j => (j : ℝ)) A 1 r 0
  have hKraw0 : ∀ r, 0 ≤ Kraw r := fun r => chainM_nonneg (fun _ => by norm_num) r 0
  set KA : ℕ → ℝ := compK (Kraw 0 * Real.exp (Kraw 0 * 1)) (fun _ => Real.exp (Kraw 0 * 1) + 1)
    (fun k => Kraw (k + 1)) 1
  refine ⟨max (max (max cs cα) (max c₁ c₂)) c_k, CA0, KA,
    (le_max_right _ _).trans' hck2, hCA0_pos.le,
    fun r => chainM_nonneg (fun _ => by positivity) _ _, ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨hcs', hcα'⟩, ⟨hc1', hc2'⟩⟩, hck'⟩ := hc
  obtain ⟨hδ0, hδ1, hs_le, -, -, -, -, hδ_hi, h6δ⟩ := hsc ε c hε hcs'
  have hc2 : 2 ≤ c := hck2.trans hck'
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_le : τ₁ ≤ 1 / 20 := hc₁ c hc1'
  have h31 : 31 / 10 * uctM τ₁ < uctM (2 * τ₁) := uctM_two_gt_31 hτ₁pos (by linarith only [hτ₁_le])
  have h6δ' : 6 * δ ≤ 1 := by
    have h1 := hc₂ c hc2'
    calc 6 * δ ≤ 6 * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by norm_num)
      _ ≤ 6 * (|a₁| * (1 / (6 * (|a₁| + 1)))) := by
          have := Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))
          gcongr; exact le_abs_self a₁
      _ ≤ 1 := by rw [mul_one_div, mul_div_assoc', div_le_one (by positivity)]; nlinarith [abs_nonneg a₁]
  set S := Icc (3 / 2 * δ) (3 * δ)
  set g : ℝ → ℝ := fun u => -(K4 * u ^ 4) + alpha ε c * u ^ 2
  have hg_cd : ContDiffOn ℝ ∞ g (Ioi 0) :=
    (((contDiffOn_id.pow 4).const_mul K4).neg).add ((contDiffOn_id.pow 2).const_mul (alpha ε c))
  set om : ℝ → ℝ := fun x => K4 * tau0 (x - s) ^ 4 + |alpha ε c| * tau0 (x - s) ^ 2
  have hom_nn : ∀ x, 3 / 2 * δ ≤ x → 0 ≤ om x := fun x _ => by positivity
  have hbd_all : ∀ (j : ℕ) (x : ℝ), 3 / 2 * δ ≤ x →
      |tau0 (x - s) ^ j * iteratedDeriv j g (tau0 (x - s))| ≤ 24 * om x := by
    intro j x hx
    have hxs : 0 < x - s := by linarith only [(abs_le.mp hs_le).2, hx, hδ0]
    exact poly42_deriv_bound K4 (alpha ε c) (by linarith only [hK4]) j (tau0_pos hxs).le
  have hcomp_s := hcomp (x₀ := 3 / 2 * δ) (s := s) (g := g) (om := om) (P := fun _ => 24)
    (by positivity) hs_le hg_cd (fun _ => by norm_num) hom_nn hbd_all
  have hsym_f : SymW S (fun _ => CA0 * c⁻¹) Kraw (fun y => g (tau0 (y - s))) :=
    { pos := fun x hx => lt_of_lt_of_le (by positivity) hx.1
      smooth := by
        refine ⟨Ioi s, isOpen_Ioi, fun x hx => by
          show s < x; linarith only [(abs_le.mp hs_le).2, hx.1, hδ0], ?_⟩
        exact (hg_cd.comp (contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const)
          (fun y hy => sub_pos.mpr hy)) (fun y hy => tau0_pos (sub_pos.mpr hy))).mono (subset_refl _)
      K_nonneg := hKraw0
      w_nonneg := fun _ _ => mul_nonneg hCA0_pos.le (inv_nonneg.mpr hc0.le)
      bound := fun r x hx => by
        have hxs : 0 < x - s := by linarith only [(abs_le.mp hs_le).2, hx.1, hδ0]
        have hu_lt : x - s < uctM (2 * τ₁) := by
          have h1 : x - s ≤ 3 * δ + 3 / 4 * δ := by linarith only [(abs_le.mp hs_le).1, hx.2]
          change 31 / 10 * uctM τ₁ < uctM (2 * τ₁) at h31
          change δ = uctM τ₁ at *
          linarith only [uctM_pos hτ₁pos, h1, h31]
        have ht2 : tau0 (x - s) ≤ 2 * τ₁ := (tau0_lt_of_lt (by positivity) hxs hu_lt).le
        have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
          rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
        have hτ₁_four : τ₁ ^ 4 = c⁻¹ := by
          rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 4, ← Real.rpow_mul hc0.le,
            show (-(1 / 4 : ℝ)) * (4 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
        have ht4_le : tau0 (x - s) ^ 4 ≤ 16 * c⁻¹ := by
          have := pow_le_pow_left₀ (tau0_pos hxs).le ht2 4
          calc tau0 (x - s) ^ 4 ≤ (2 * τ₁) ^ 4 := this
            _ = 16 * τ₁ ^ 4 := by ring
            _ = 16 * c⁻¹ := by rw [hτ₁_four]
        have ht2_le : tau0 (x - s) ^ 2 ≤ 4 * c ^ (-(1 / 2 : ℝ)) := by
          have := pow_le_pow_left₀ (tau0_pos hxs).le ht2 2
          calc tau0 (x - s) ^ 2 ≤ (2 * τ₁) ^ 2 := this
            _ = 4 * τ₁ ^ 2 := by ring
            _ = 4 * c ^ (-(1 / 2 : ℝ)) := by rw [hτ₁_sq]
        have hα_le : |alpha ε c| * tau0 (x - s) ^ 2 ≤ 4 * Kα * c⁻¹ := by
          have hαb := hαf ε c hε hcα'
          have hc23_le : c ^ (-(2 / 3 : ℝ)) ≤ c ^ (-(1 / 2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
          have hc12_sq : c ^ (-(1 / 2 : ℝ)) * c ^ (-(1 / 2 : ℝ)) = c⁻¹ := by
            rw [← Real.rpow_add hc0]; norm_num [Real.rpow_neg_one]
          calc |alpha ε c| * tau0 (x - s) ^ 2
              ≤ (Kα * c ^ (-(2 / 3 : ℝ))) * (4 * c ^ (-(1 / 2 : ℝ))) :=
                mul_le_mul hαb ht2_le (sq_nonneg _) (mul_nonneg hKα0 (Real.rpow_nonneg hc0.le _))
            _ ≤ (Kα * c ^ (-(1 / 2 : ℝ))) * (4 * c ^ (-(1 / 2 : ℝ))) := by gcongr
            _ = 4 * Kα * c⁻¹ := by rw [← hc12_sq]; ring
        have hom_le : om x ≤ CA0 * c⁻¹ := by
          have hK4_mul : K4 * tau0 (x - s) ^ 4 ≤ 16 * K4 * c⁻¹ := by nlinarith only [ht4_le, hK4]
          have hc0' : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
          dsimp only [om, CA0]
          nlinarith only [hK4_mul, hα_le, hc0']
        have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
        have hx1 : x ≤ 1 := by linarith only [hx.2, h6δ']
        have hlam : lamL x ^ r = (x ^ r)⁻¹ := by
          unfold lamL
          rw [max_eq_right (one_le_inv_iff₀.mpr ⟨hx0, hx1⟩), inv_pow]
        have hraw := hcomp_s r x hx.1
        rw [hlam] at hraw
        exact hraw.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hom_le (hKraw0 r)) (inv_nonneg.mpr (pow_nonneg hx0.le _))) }
  have hexp := symW_exp_sub_one (B := 1) hsym_f (fun x _ => hck c hck')
  exact hexp.congr (U := Ioi s) isOpen_Ioi
    (fun x hx => by show s < x; linarith only [(abs_le.mp hs_le).2, hx.1, hδ0])
    (fun x _ => rfl)

/-- Helper: if `f ∈ SymW S (fun _ => w0) Kf`, `Ψ ∘ f ∈ SymW S (fun _ => w0) KΨ`, `deriv Φ = Ψ` on `U`,
and `|Φ(f x)| ≤ Kf 0 ^ 2 * w0 ^ 2`, then `Φ ∘ f ∈ SymW S (fun _ => w0 ^ 2) ...`. -/
private lemma symW_comp_quad_deriv {S : Set ℝ} {w0 : ℝ} (hw0 : 0 ≤ w0)
    {Kf KΨ : ℕ → ℝ} {f Φ Ψ : ℝ → ℝ}
    (hf : SymW S (fun _ => w0) Kf f) (hΨf : SymW S (fun _ => w0) KΨ (fun x => Ψ (f x)))
    {U : Set ℝ} (hU : IsOpen U) (hSU : S ⊆ U)
    (hΦcd : ContDiffOn ℝ ∞ (fun x => Φ (f x)) U)
    (hder : ∀ x ∈ U, deriv (fun y => Φ (f y)) x = Ψ (f x) * deriv f x)
    (h0 : ∀ x ∈ S, |Φ (f x)| ≤ Kf 0 ^ 2 * w0 ^ 2) :
    SymW S (fun _ => w0 ^ 2)
      (fun r => max (Kf 0 ^ 2) (∑ i ∈ range r, ((r - 1).choose i : ℝ) * KΨ i * Kf (r - i)))
      (fun x => Φ (f x)) where
  pos := hf.pos
  smooth := ⟨U, hU, hSU, hΦcd⟩
  K_nonneg _ := le_max_of_le_left (sq_nonneg _)
  w_nonneg _ _ := sq_nonneg w0
  bound r x hx := by
    have hx0 : 0 < x := hf.pos x hx
    cases r with
    | zero =>
      simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one]
      exact (h0 x hx).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg w0))
    | succ k =>
      obtain ⟨U1, hU1, hSU1, hfU1⟩ := hf.smooth
      obtain ⟨U2, hU2, hSU2, hΨU2⟩ := hΨf.smooth
      have hU0 : U ∩ U1 ∈ 𝓝 x := (hU.inter hU1).mem_nhds ⟨hSU hx, hSU1 hx⟩
      have hev : deriv (fun y => Φ (f y)) =ᶠ[𝓝 x] fun y => Ψ (f y) * deriv f y :=
        Filter.eventually_of_mem hU0 fun y hy => hder y hy.1
      rw [iteratedDeriv_succ', hev.iteratedDeriv_eq]
      have hcdΨ : ContDiffAt ℝ k (fun y => Ψ (f y)) x :=
        (hΨU2.contDiffAt (hU2.mem_nhds (hSU2 hx))).of_le (by exact_mod_cast le_top)
      have hcdf' : ContDiffAt ℝ k (deriv f) x := by
        have hcd1 : ContDiffOn ℝ ∞ (deriv f) U1 := hfU1.deriv_of_isOpen hU1 (m := 0) (by simp)
        exact (hcd1.contDiffAt (hU1.mem_nhds (hSU1 hx))).of_le (by exact_mod_cast le_top)
      rw [iteratedDeriv_fun_mul hcdΨ hcdf']
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Nat.succ_sub_one, Finset.sum_mul, Finset.sum_mul]
      have hterm : ∀ i ∈ range (k + 1),
          |(k.choose i : ℝ) * iteratedDeriv i (fun y => Ψ (f y)) x * iteratedDeriv (k - i) (deriv f) x| ≤
          ((k.choose i : ℝ) * KΨ i * Kf (k + 1 - i)) * w0 ^ 2 * (x ^ (k + 1))⁻¹ := by
        intro i hi
        have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [abs_mul, abs_mul, Nat.abs_cast]
        have a1 := hΨf.bound i x hx
        have hd_eq : iteratedDeriv (k - i) (deriv f) x = iteratedDeriv (k - i + 1) f x := by
          rw [← iteratedDeriv_succ']
        have a2 := hf.bound (k - i + 1) x hx
        rw [← hd_eq] at a2
        have hsub : k - i + 1 = k + 1 - i := by omega
        rw [hsub] at a2
        have hmul := mul_le_mul a1 a2 (abs_nonneg _) (le_trans (abs_nonneg _) a1)
        have hinv : (x ^ i)⁻¹ * (x ^ (k + 1 - i))⁻¹ = (x ^ (k + 1))⁻¹ := by
          rw [← mul_inv, ← pow_add, show i + (k + 1 - i) = k + 1 by omega]
        calc (k.choose i : ℝ) * |iteratedDeriv i (fun y => Ψ (f y)) x| * |iteratedDeriv (k - i) (deriv f) x|
            ≤ (k.choose i : ℝ) * ((KΨ i * w0 * (x ^ i)⁻¹) * (Kf (k + 1 - i) * w0 * (x ^ (k + 1 - i))⁻¹)) :=
              mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg _)
          _ = ((k.choose i : ℝ) * KΨ i * Kf (k + 1 - i)) * w0 ^ 2 * ((x ^ i)⁻¹ * (x ^ (k + 1 - i))⁻¹) := by ring
          _ = _ := by rw [hinv]
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg w0))
        (inv_nonneg.mpr (pow_nonneg hx0.le _))

/-- Factor B: `e^{-Δ} (1 + Δ) - 1` on `[3δ/2, 3δ]` has weight `CB(K₄) * c⁻¹` (`CB` independent of `K₁`). -/
private lemma mid_factorB_symW {K4 : ℝ} (hK4 : 1 ≤ K4) {T1 alpha : ℝ → ℝ → ℝ}
    (hwarp : FctWarpZeroStmt T1 alpha) :
    ∃ (c₀ CB : ℝ) (KB : ℕ → ℝ), 2 ≤ c₀ ∧ 0 ≤ CB ∧ (∀ r, 0 ≤ KB r) ∧
      ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        SymW (Icc (3 / 2 * physDelta c) (3 * physDelta c)) (fun _ => CB * c⁻¹) KB
          (fun x => Real.exp (-stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
              (tau0 (x - physShift ε c))) *
            (1 + stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 (c ^ (-(1 / 4 : ℝ)))))
              (tau0 (x - physShift ε c))) - 1) := by
  obtain ⟨Cw, cw, hw⟩ := hwarp
  obtain ⟨Kα, cα, hαf⟩ : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).2⟩
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 (fun ε c hε hc => (hw ε c hε hc).1)
  obtain ⟨lam, hlam, hlam1, hlamb⟩ := tau0_three_quarter_ge
  obtain ⟨τc, KD, CwD, hτc, hτc100, hCwD0, hKD0, hD⟩ := deltaCurv_symW StripKernelChoice.star K4 hK4 hlam
  obtain ⟨A, hA0, hcomp⟩ := comp_tau0_shift
  obtain ⟨c₁, hc₁1, hc₁⟩ := FctSym.exists_rpow_neg_le (p := 1 / 4)
    (η := min τc (1 / 20)) (by norm_num) (lt_min hτc (by norm_num))
  obtain ⟨c₂, hc₂1, hc₂⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2) (η := 1 / (6 * (|a₁| + 1))) (by norm_num)
    (one_div_pos.mpr (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg a₁) one_pos)))
  obtain ⟨c_al, hc_al1, hc_al⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6) (η := 1 / (|Kα| + 1)) (by norm_num) (by positivity)
  set Kf : ℕ → ℝ := fun r => chainM KD (fun j => (j : ℝ)) A 1 r 0
  have hKf0 : ∀ r, 0 ≤ Kf r := fun r => chainM_nonneg hKD0 r 0
  have hΨ_bd : ∀ j : ℕ, ∃ P : ℝ, 0 ≤ P ∧ ∀ y ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
      |iteratedDeriv j (fun y : ℝ => -y * Real.exp (-y)) y| ≤ P := fun j => by
    have hc : ContinuousOn (iteratedDeriv j (fun y : ℝ => -y * Real.exp (-y))) (Icc (-(1 / 2) : ℝ) (1 / 2)) :=
      (((contDiff_id.neg.mul (Real.contDiff_exp.comp contDiff_id.neg)).of_le
        (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr le_top)).continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    exact ⟨max M 0, le_max_right _ _, fun y hy => (Real.norm_eq_abs _ ▸ hM y hy).trans (le_max_left _ _)⟩
  choose P hP0 hP using hΨ_bd
  set KΨ : ℕ → ℝ := compK (2 * Kf 0) P (fun k => Kf (k + 1)) 1
  set KB : ℕ → ℝ := fun r => max (Kf 0 ^ 2) (∑ i ∈ range r, ((r - 1).choose i : ℝ) * KΨ i * Kf (r - i))
  set c_w : ℝ := max 2 ((max (Kf 0 * CwD) CwD + 2) ^ 2)
  have hcw2 : 2 ≤ c_w := le_max_left _ _
  refine ⟨max (max (max cs cα) (max c₁ c₂)) (max c_al c_w), CwD ^ 2, KB,
    (le_max_right _ _).trans' hcw2 |>.trans (le_max_right _ _) |>.trans (le_refl _), sq_nonneg CwD,
    fun _ => le_max_of_le_left (sq_nonneg _), ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨hcs', hcα'⟩, ⟨hc1', hc2'⟩⟩, ⟨hcal', hcw'⟩⟩ := hc
  obtain ⟨hδ0, -, hs_le, -, -, -, -, hδ_hi, h6δ⟩ := hsc ε c hε hcs'
  have hc2 : 2 ≤ c := hcw2.trans hcw'
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_bd : τ₁ ≤ min τc (1 / 20) := hc₁ c hc1'
  have hτc' : τ₁ ≤ τc := hτ₁_bd.trans (min_le_left _ _)
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_bd.trans (min_le_right _ _)
  have hτ₁_four : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 4, ← Real.rpow_mul hc0.le,
        show (-(1 / 4 : ℝ)) * (4 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]; field_simp
  have hα_le : |alpha ε c| ≤ τ₁ ^ 2 := by
    have h1 := hαf ε c hε hcα'
    have h2 : c ^ (-(1 / 6 : ℝ)) ≤ 1 / (|Kα| + 1) := hc_al c hcal'
    have h23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
    have hk : Kα * c ^ (-(1 / 6 : ℝ)) ≤ 1 := by
      have hK_pos : 0 < |Kα| + 1 := by positivity
      calc Kα * c ^ (-(1 / 6 : ℝ)) ≤ |Kα| * (1 / (|Kα| + 1)) :=
            mul_le_mul (le_abs_self Kα) h2 (Real.rpow_nonneg hc0.le _) (by positivity)
        _ ≤ 1 := by rw [mul_one_div, div_le_one hK_pos]; linarith only [abs_nonneg Kα]
    rw [hτ₁_sq]
    calc |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) := h1
      _ = (Kα * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h23]; ring
      _ ≤ 1 * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hc0.le _)
      _ = c ^ (-(1 / 2 : ℝ)) := one_mul _
  have hD0 := hD hc0 hτ₁pos hτc' hτ₁_four hα_le
  set θ := fctThetaD (v0 StripKernelChoice.star K4 τ₁)
  have hθ_cd : ContDiff ℝ ∞ θ := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hpart1⟩ :=
      fct_comp_D_part1 StripKernelChoice.star
    exact (hpart1 hK4 hc0 hτ₁pos (hτc'.trans (by linarith [hτc100])) hτ₁_four hα_le).2.2.1.1
  have hg_cd : ContDiffOn ℝ ∞ (stripDeltaCurv c θ) (Ioi 0) := deltaCurv_contDiffOn hθ_cd
  have hlam_t : ∀ x : ℝ, 3 / 2 * δ ≤ x → lam * τ₁ ≤ tau0 (x - s) := fun x hx => by
    have hxs34 : 3 / 4 * δ ≤ x - s := by linarith only [(abs_le.mp hs_le).2, hx, hδ0]
    have hlt := hlamb τ₁ hτ₁pos (by linarith only [hτ₁_20])
    change lam * τ₁ ≤ tau0 (3 / 4 * δ) at hlt
    exact hlt.trans (tau0_mono (by positivity) hxs34)
  have hbd_all : ∀ (j : ℕ) (x : ℝ), 3 / 2 * δ ≤ x →
      |tau0 (x - s) ^ j * iteratedDeriv j (stripDeltaCurv c θ) (tau0 (x - s))| ≤ KD j * (CwD * τ₁ ^ 3) := by
    intro j x hx
    have ht := hlam_t x hx
    have ht0 : 0 < tau0 (x - s) := lt_of_lt_of_le (by positivity) ht
    have hraw := hD0.raw_bound j ht
    have hw_le : CwD * τ₁ ^ 3 * ((1 + tau0 (x - s)) ^ 8)⁻¹ ≤ CwD * τ₁ ^ 3 := by
      have h18 : (1 : ℝ) ≤ (1 + tau0 (x - s)) ^ 8 := one_le_pow₀ (by linarith only [ht0])
      have hinv : ((1 + tau0 (x - s)) ^ 8)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h18
      calc CwD * τ₁ ^ 3 * ((1 + tau0 (x - s)) ^ 8)⁻¹ ≤ CwD * τ₁ ^ 3 * 1 :=
            mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = _ := mul_one _
    exact hraw.trans (mul_le_mul_of_nonneg_left hw_le (hKD0 j))
  have hcomp_s := hcomp (x₀ := 3 / 2 * δ) (s := s) (g := stripDeltaCurv c θ) (om := fun _ => CwD * τ₁ ^ 3)
    (P := KD) (by positivity) hs_le hg_cd hKD0 (fun _ _ => by positivity) hbd_all
  have h6δ' : 6 * δ ≤ 1 := by
    have h1 := hc₂ c hc2'
    calc 6 * δ ≤ 6 * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by norm_num)
      _ ≤ 6 * (|a₁| * (1 / (6 * (|a₁| + 1)))) := by
          have := Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))
          gcongr; exact le_abs_self a₁
      _ ≤ 1 := by rw [mul_one_div, mul_div_assoc', div_le_one (by positivity)]; nlinarith [abs_nonneg a₁]
  set S := Icc (3 / 2 * δ) (3 * δ)
  set f : ℝ → ℝ := fun y => stripDeltaCurv c θ (tau0 (y - s))
  set w0 : ℝ := CwD * τ₁ ^ 3
  have hw0_nn : 0 ≤ w0 := by positivity
  have hw0_le1 : w0 ≤ 1 := by
    have hcw_b : (max (Kf 0 * CwD) CwD + 2) ^ 2 ≤ c := (le_max_right _ _).trans hcw'
    have hsq1 : CwD ≤ c ^ (1 / 2 : ℝ) := by
      have hsq : CwD ^ 2 ≤ c := by
        have h1 : CwD ≤ max (Kf 0 * CwD) CwD + 2 := (le_max_right _ _).trans (by linarith)
        exact (pow_le_pow_left₀ hCwD0 h1 2).trans hcw_b
      calc CwD = Real.sqrt (CwD ^ 2) := (Real.sqrt_sq hCwD0).symm
        _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hsq
        _ = c ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c
    have hc12 : c ^ (1 / 2 : ℝ) * τ₁ ^ 3 ≤ 1 := by
      have hτ3 : τ₁ ^ 3 = c ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 3, ← Real.rpow_mul hc0.le]; norm_num
      rw [hτ3, ← Real.rpow_add hc0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    calc w0 = CwD * τ₁ ^ 3 := rfl
      _ ≤ c ^ (1 / 2 : ℝ) * τ₁ ^ 3 := mul_le_mul_of_nonneg_right hsq1 (by positivity)
      _ ≤ 1 := hc12
  have hKfCw_le : Kf 0 * w0 ≤ 1 / 2 := by
    have hcw_b : (max (Kf 0 * CwD) CwD + 2) ^ 2 ≤ c := (le_max_right _ _).trans hcw'
    have h1 : Kf 0 * CwD ≤ c ^ (1 / 2 : ℝ) / 2 := by
      have hle : 2 * (Kf 0 * CwD) ≤ max (Kf 0 * CwD) CwD + 2 := by
        have hm : Kf 0 * CwD ≤ max (Kf 0 * CwD) CwD := le_max_left _ _
        linarith only [hm, mul_nonneg (hKf0 0) hCwD0]
      have hsq : (2 * (Kf 0 * CwD)) ^ 2 ≤ c :=
        (pow_le_pow_left₀ (by positivity) hle 2).trans hcw_b
      have hrt : 2 * (Kf 0 * CwD) ≤ c ^ (1 / 2 : ℝ) := by
        calc 2 * (Kf 0 * CwD) = Real.sqrt ((2 * (Kf 0 * CwD)) ^ 2) := (Real.sqrt_sq (by positivity)).symm
          _ ≤ Real.sqrt c := Real.sqrt_le_sqrt hsq
          _ = c ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow c
      linarith only [hrt]
    have hc12 : c ^ (1 / 2 : ℝ) * τ₁ ^ 3 ≤ 1 := by
      have hτ3 : τ₁ ^ 3 = c ^ (-(3 / 4 : ℝ)) := by
        rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 3, ← Real.rpow_mul hc0.le]; norm_num
      rw [hτ3, ← Real.rpow_add hc0]
      exact Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
    calc Kf 0 * w0 = (Kf 0 * CwD) * τ₁ ^ 3 := by ring
      _ ≤ (c ^ (1 / 2 : ℝ) / 2) * τ₁ ^ 3 := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (c ^ (1 / 2 : ℝ) * τ₁ ^ 3) / 2 := by ring
      _ ≤ 1 / 2 := by linarith only [hc12]
  have hsym_f : SymW S (fun _ => w0) Kf f :=
    { pos := fun x hx => lt_of_lt_of_le (by positivity) hx.1
      smooth := ⟨Ioi s, isOpen_Ioi, fun x hx => by show s < x; linarith only [(abs_le.mp hs_le).2, hx.1, hδ0],
        hg_cd.comp (contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const)
          (fun y hy => sub_pos.mpr hy)) (fun y hy => tau0_pos (sub_pos.mpr hy))⟩
      K_nonneg := hKf0
      w_nonneg := fun _ _ => hw0_nn
      bound := fun r x hx => by
        have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
        have hx1 : x ≤ 1 := by linarith only [hx.2, h6δ']
        have hlam : lamL x ^ r = (x ^ r)⁻¹ := by
          unfold lamL; rw [max_eq_right (one_le_inv_iff₀.mpr ⟨hx0, hx1⟩), inv_pow]
        have hraw := hcomp_s r x hx.1
        rw [hlam] at hraw
        exact hraw }
  have hf_half : ∀ x ∈ S, |f x| ≤ 1 / 2 := fun x hx => by
    have := hsym_f.bound 0 x hx
    simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at this
    exact this.trans hKfCw_le
  set Ψ : ℝ → ℝ := fun y => -y * Real.exp (-y)
  set Φ : ℝ → ℝ := fun y => Real.exp (-y) * (1 + y) - 1
  have hΨ_sym : SymW S (fun _ => w0) KΨ (fun x => Ψ (f x)) := by
    refine SymW.comp_smooth hsym_f isOpen_univ (contDiff_id.neg.mul (Real.contDiff_exp.comp contDiff_id.neg)).contDiffOn
      (fun _ _ => mem_univ _) (fun j x hx => hP j _ (abs_le.mp (hf_half x hx))) hP0 (fun _ _ => hw0_le1)
      (by have := hKf0 0; positivity) (fun x hx => ?_)
    have hfx := abs_le.mp (hf_half x hx)
    have h1 : Real.exp (-f x) ≤ 2 := (Real.exp_le_exp.mpr (by linarith only [hfx.1])).trans
      (by have := Real.exp_one_lt_d9.le
          have : (1 / 2 : ℝ) ≤ 1 := by norm_num
          exact (Real.exp_le_exp.mpr this).trans (by norm_num))
    have h0' := hsym_f.bound 0 x hx
    simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at h0'
    calc |Ψ (f x)| = |f x| * Real.exp (-f x) := by
          dsimp only [Ψ]; rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _)]
      _ ≤ (Kf 0 * w0) * 2 := mul_le_mul h0' h1 (Real.exp_pos _).le (mul_nonneg (hKf0 0) hw0_nn)
      _ = 2 * Kf 0 * w0 := by ring
  have hU_oi : IsOpen (Ioi s) := isOpen_Ioi
  have hSU_oi : S ⊆ Ioi s := fun x hx => by show s < x; linarith only [(abs_le.mp hs_le).2, hx.1, hδ0]
  have hf_oi : ContDiffOn ℝ ∞ f (Ioi s) :=
    hg_cd.comp (contDiffOn_tau0.comp (contDiffOn_id.sub contDiffOn_const) (fun y hy => sub_pos.mpr hy))
      (fun y hy => tau0_pos (sub_pos.mpr hy))
  have hΦ_cd : ContDiffOn ℝ ∞ (fun x => Φ (f x)) (Ioi s) :=
    (((Real.contDiff_exp.comp contDiff_id.neg).mul (contDiff_const.add contDiff_id)).sub contDiff_const).comp_contDiffOn hf_oi
  have hder : ∀ x ∈ Ioi s, deriv (fun y => Φ (f y)) x = Ψ (f x) * deriv f x := fun x hx => by
    have hd_f : HasDerivAt f (deriv f x) x := ((hf_oi.differentiableOn (by simp)).differentiableAt (hU_oi.mem_nhds hx)).hasDerivAt
    have hd_Φ : HasDerivAt Φ (Ψ (f x)) (f x) := by
      have h1 : HasDerivAt (fun y => Real.exp (-y)) (-Real.exp (-f x)) (f x) := by
        simpa using (Real.hasDerivAt_exp (-f x)).comp (f x) ((hasDerivAt_id (f x)).neg)
      have h2 : HasDerivAt (fun y : ℝ => 1 + y) 1 (f x) := (hasDerivAt_id (f x)).const_add 1
      refine ((h1.mul h2).sub_const (1 : ℝ)).congr_deriv ?_
      dsimp only [Ψ]; ring
    exact (hd_Φ.comp x hd_f).deriv
  have h0_Φ : ∀ x ∈ S, |Φ (f x)| ≤ Kf 0 ^ 2 * w0 ^ 2 := fun x hx => by
    have hfx := abs_le.mp (hf_half x hx)
    have hfy : |Φ (f x)| ≤ f x ^ 2 := by
      have h1 : Real.exp (-f x) * (1 + f x) ≤ 1 := by
        have hle := Real.add_one_le_exp (f x)
        have hm := mul_le_mul_of_nonneg_left hle (Real.exp_pos (-f x)).le
        rwa [Real.exp_neg, inv_mul_cancel_left₀ (Real.exp_pos _).ne'] at hm
      have h2 : 1 - f x ^ 2 ≤ Real.exp (-f x) * (1 + f x) := by
        have hle := Real.add_one_le_exp (-f x)
        have hp : 0 ≤ 1 + f x := by linarith only [hfx.1]
        have hm := mul_le_mul_of_nonneg_right hle hp
        have : (-f x + 1) * (1 + f x) = 1 - f x ^ 2 := by ring
        linarith only [hm, this]
      rw [abs_le]; constructor <;> linarith only [h1, h2]
    have h0' := hsym_f.bound 0 x hx
    simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at h0'
    calc |Φ (f x)| ≤ f x ^ 2 := hfy
      _ = |f x| ^ 2 := (sq_abs _).symm
      _ ≤ (Kf 0 * w0) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0' 2
      _ = Kf 0 ^ 2 * w0 ^ 2 := by ring
  have hΦ_sym := symW_comp_quad_deriv hw0_nn hsym_f hΨ_sym hU_oi hSU_oi hΦ_cd hder h0_Φ
  have hw0_sq : w0 ^ 2 ≤ CwD ^ 2 * c⁻¹ := by
    have hτ₁6_le : τ₁ ^ 6 ≤ c⁻¹ := by
      have hτ₁_le1 : τ₁ ≤ 1 := by linarith only [hτ₁_20]
      have hτ₁_4 : τ₁ ^ 4 = c⁻¹ := (inv_eq_of_mul_eq_one_left hτ₁_four).symm
      have h6 : τ₁ ^ 6 = τ₁ ^ 4 * τ₁ ^ 2 := by ring
      have h21 : τ₁ ^ 2 ≤ 1 := pow_le_one₀ hτ₁pos.le hτ₁_le1
      nlinarith only [h6, h21, hτ₁_4, pow_nonneg hτ₁pos.le 4]
    calc w0 ^ 2 = CwD ^ 2 * τ₁ ^ 6 := by dsimp only [w0]; ring
      _ ≤ CwD ^ 2 * c⁻¹ := mul_le_mul_of_nonneg_left hτ₁6_le (sq_nonneg CwD)
  exact hΦ_sym.of_le (fun _ _ => hw0_sq) (fun _ => le_rfl)

/-- Factor C: `‖u - L₁ φ_kill(a, i τ₀ u)‖ / u - 1` on `[3δ/2, 3δ]` has weight `CC * c⁻¹` (`CC` independent of `K₁`). -/
private lemma mid_factorC_symW {T1 alpha : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) :
    ∃ (c₀ CC : ℝ) (KC : ℕ → ℝ), 2 ≤ c₀ ∧ 0 ≤ CC ∧ (∀ r, 0 ≤ KC r) ∧
      ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        SymW (Icc (3 / 2 * physDelta c) (3 * physDelta c)) (fun _ => CC * c⁻¹) KC
          (fun x => ‖((x - physShift ε c : ℝ) : ℂ) -
            (physL1 T1 ε c : ℂ) * vacPhi (c ^ (-(1 / 12 : ℝ))) (x - physShift ε c)‖ /
              (x - physShift ε c) - 1) := by
  obtain ⟨Cw, cw, hw⟩ := hwarp
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).1⟩
  obtain ⟨KL, cL, hcL1, hL⟩ := physL1_le T1 hT1
  have hKL0 : 0 ≤ KL := by
    have := hL 1 (max cL 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cL 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (physL1 T1 1 (max cL 1))]
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨Θ, hΘ0, Kbs, hbs⟩ := block_small
  obtain ⟨C₁, hC₁0, hC₁⟩ := phiKill_norm_le
  set Kpq : ℕ → ℝ := Kmul Kbs (SymW.Kpow (-1))
  have hKbs0 : ∀ r, 0 ≤ Kbs r := fun r =>
    (hbs { L := Complex.reCLM, a := 1, s := 0, x₀ := 1 / 4, L₁ := 0 }
      ⟨fun z => Complex.abs_re_le_norm z, one_pos, le_rfl, by norm_num, by norm_num, by simp⟩).K_nonneg r
  have hKpq0 : ∀ r, 0 ≤ Kpq r := Kmul_nonneg hKbs0 (SymW.Kpow_nonneg (-1))
  set M_base : ℝ := KL * Θ * (3 * |a₁| + 1) ^ 3
  have hMb0 : 0 ≤ M_base := by positivity
  set CC : ℝ := 2 * M_base + 2 * (M_base * M_base)
  have hCC0 : 0 ≤ CC := by positivity
  set Kw : ℕ → ℝ := fun r => (Kpq r + Kmul Kpq Kpq r) + Kmul Kpq Kpq r
  have hKw0 : ∀ r, 0 ≤ Kw r := fun r =>
    add_nonneg (add_nonneg (hKpq0 r) (Kmul_nonneg hKpq0 hKpq0 r)) (Kmul_nonneg hKpq0 hKpq0 r)
  choose Bj hBj0 hBj using sqrtG_bounds
  set KC : ℕ → ℝ := compK (max (Kw 0) 0) Bj (fun k => Kw (k + 1)) 1
  obtain ⟨c_d, hcd1, hcd⟩ := FctSym.exists_rpow_neg_le (p := 1 / 2)
    (η := 1 / (6 * (|a₁| + 1))) (by norm_num)
    (one_div_pos.mpr (mul_pos (by norm_num) (add_pos_of_nonneg_of_pos (abs_nonneg a₁) one_pos)))
  obtain ⟨c_p, hcp1, hcp⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6)
    (η := 3 * a₀ / (80 * (KL + 1) * (C₁ + 1))) (by norm_num) (by positivity)
  have hc_w_ex : ∃ c_w : ℝ, 2 ≤ c_w ∧ ∀ c : ℝ, c_w ≤ c → CC * c⁻¹ ≤ 1 := by
    refine ⟨max 2 (CC + 1), le_max_left _ _, fun c hc => ?_⟩
    have hcpos : 0 < c := by linarith [le_max_left 2 (CC + 1) |>.trans hc]
    rw [mul_inv_le_iff₀ hcpos]; linarith [le_max_right 2 (CC + 1) |>.trans hc]
  obtain ⟨c_w, hcw2, hcw⟩ := hc_w_ex
  refine ⟨max (max cs cL) (max c_d (max c_p c_w)), CC, KC,
    (le_max_right _ _).trans' ((le_max_right _ _).trans' hcw2) |>.trans (le_refl _),
    hCC0, fun _ => chainM_nonneg (fun _ => by positivity) _ _, ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨hcs', hcL'⟩, ⟨hcd', ⟨hcp', hcw'⟩⟩⟩ := hc
  obtain ⟨hδ0, -, hs_le, -, -, -, hδ_lo, hδ_hi, _⟩ := hsc ε c hε hcs'
  have hc2 : 2 ≤ c := hcw2.trans hcw'
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set L1 := physL1 T1 ε c
  set a : ℝ := c ^ (-(1 / 12 : ℝ))
  have ha0 : 0 < a := Real.rpow_pos_of_pos hc0 _
  have ha1 : a ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 (by norm_num)
  have h6δ : 6 * δ ≤ 1 := by
    have h1 := hc₂_bd : c ^ (-(1 / 2 : ℝ)) ≤ 1 / (6 * (|a₁| + 1)) := hcd c hcd'
    calc 6 * δ ≤ 6 * (a₁ * c ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hδ_hi (by norm_num)
      _ ≤ 6 * (|a₁| * (1 / (6 * (|a₁| + 1)))) := by
          have := Real.rpow_nonneg hc0.le (-(1 / 2 : ℝ))
          gcongr; exact le_abs_self a₁
      _ ≤ 1 := by rw [mul_one_div, mul_div_assoc', div_le_one (by positivity)]; nlinarith [abs_nonneg a₁]
  set S := Icc (3 / 2 * δ) (3 * δ)
  have hS_sub : S ⊆ Icc (3 / 2 * δ) (1 / 2) := fun x hx => ⟨hx.1, by linarith only [hx.2, h6δ]⟩
  have hS_ci : S ⊆ Ici (3 / 2 * δ) := fun _ hx => hx.1
  have ha8 : a ^ 8 = c ^ (-(2 / 3 : ℝ)) := by
    rw [← Real.rpow_natCast (c ^ (-(1 / 12 : ℝ))) 8, ← Real.rpow_mul hc0.le]; norm_num
  have hL1_abs : |L1| ≤ KL * a ^ 8 := by rw [ha8]; exact hL ε c hε hcL'
  have hp_sym : ∀ (Lf : ℂ →L[ℝ] ℝ), (∀ z, |Lf z| ≤ ‖z‖) →
      SymW S (fun _ => M_base * c⁻¹) Kpq (fun x => L1 * Lf (phiKill a ((tau0 (x - s) : ℂ) * Complex.I)) / (x - s)) := by
    intro Lf hLf
    set q : NPar := { L := Lf, a := a, s := s, x₀ := 3 / 2 * δ, L₁ := L1 }
    have hq_hyp : NHyp q := ⟨hLf, ha0, ha1, by positivity, by linarith only [h6δ], hs_le⟩
    have hblk := (hbs q hq_hyp).mono_set hS_sub
    have hinv := (usym_inv_shift.2 q hq_hyp).mono_set hS_ci
    have hprod := (hblk.smul L1).mul hinv
    have hcongr := hprod.congr (U := Ioi s) isOpen_Ioi
      (fun x hx => by show s < x; linarith only [(abs_le.mp hs_le).2, hx.1, hδ0])
      (fun x hx => by
        have hxs : x - s ≠ 0 := (sub_pos.mpr hx).ne'
        simp only [Real.rpow_neg_one, one_mul, q]
        rw [div_eq_mul_inv])
    refine hcongr.of_le (fun x hx => ?_) (fun _ => le_rfl)
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    have ha8_pos : 0 < a ^ 8 := by positivity
    have hx3_bd : x ^ 3 ≤ (3 * |a₁| + 1) ^ 3 * c ^ (-(3 / 2 : ℝ)) := by
      have hx_le : x ≤ (3 * |a₁| + 1) * c ^ (-(1 / 2 : ℝ)) := by
        have h1 : x ≤ 3 * a₁ * c ^ (-(1 / 2 : ℝ)) := by linarith only [hx.2, hδ_hi]
        have h2 : 3 * a₁ * c ^ (-(1 / 2 : ℝ)) ≤ (3 * |a₁| + 1) * c ^ (-(1 / 2 : ℝ)) := by
          gcongr; linarith only [le_abs_self a₁]
        exact h1.trans h2
      have hpow3 := pow_le_pow_left₀ hx0.le hx_le 3
      have hc32 : (c ^ (-(1 / 2 : ℝ))) ^ 3 = c ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      rw [mul_pow, hc32] at hpow3
      exact hpow3
    have hc32_1 : c ^ (-(3 / 2 : ℝ)) ≤ c⁻¹ := by
      rw [← Real.rpow_neg_one c]
      exact Real.rpow_le_rpow_of_exponent_le hc1 (by norm_num)
    calc (|L1| * (Θ * (a ^ 8)⁻¹ * x ^ 4)) * (|(1 : ℝ)| * x ^ (-1 : ℝ))
        = |L1| * (Θ * (a ^ 8)⁻¹ * x ^ 3) := by rw [abs_one, one_mul, Real.rpow_neg_one]; field_simp
      _ ≤ (KL * a ^ 8) * (Θ * (a ^ 8)⁻¹ * x ^ 3) := by gcongr
      _ = KL * Θ * x ^ 3 := by field_simp
      _ ≤ KL * Θ * ((3 * |a₁| + 1) ^ 3 * c ^ (-(3 / 2 : ℝ))) := by gcongr
      _ ≤ KL * Θ * ((3 * |a₁| + 1) ^ 3 * c⁻¹) := by gcongr
      _ = M_base * c⁻¹ := by dsimp only [M_base]; ring
  have p_re := hp_sym Complex.reCLM Complex.abs_re_le_norm
  have p_im := hp_sym Complex.imCLM Complex.abs_im_le_norm
  set f_re : ℝ → ℝ := fun x => L1 * Complex.reCLM (phiKill a ((tau0 (x - s) : ℂ) * Complex.I)) / (x - s)
  set f_im : ℝ → ℝ := fun x => L1 * Complex.imCLM (phiKill a ((tau0 (x - s) : ℂ) * Complex.I)) / (x - s)
  have hm1 := (p_re.smul (-2 : ℝ)).of_le (w' := fun _ => CC * c⁻¹) (fun _ _ => by
    have : |(-2 : ℝ)| = 2 := by norm_num
    rw [this]; dsimp only [CC]; nlinarith [mul_nonneg hMb0 hMb0, inv_nonneg.mpr hc0.le]) (fun _ => le_rfl)
  have hm2 := (p_re.mul p_re).of_le (w' := fun _ => CC * c⁻¹) (fun _ _ => by
    have hcc : c⁻¹ * c⁻¹ ≤ c⁻¹ := by
      have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      nlinarith [inv_nonneg.mpr hc0.le]
    dsimp only [CC]
    calc (M_base * c⁻¹) * (M_base * c⁻¹) = (M_base * M_base) * (c⁻¹ * c⁻¹) := by ring
      _ ≤ (M_base * M_base) * c⁻¹ := mul_le_mul_of_nonneg_left hcc (mul_nonneg hMb0 hMb0)
      _ ≤ (2 * M_base + 2 * (M_base * M_base)) * c⁻¹ := by
          nlinarith [mul_nonneg hMb0 hMb0, inv_nonneg.mpr hc0.le]) (fun _ => le_rfl)
  have hm3 := (p_im.mul p_im).of_le (w' := fun _ => CC * c⁻¹) (fun _ _ => by
    have hcc : c⁻¹ * c⁻¹ ≤ c⁻¹ := by
      have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      nlinarith [inv_nonneg.mpr hc0.le]
    dsimp only [CC]
    calc (M_base * c⁻¹) * (M_base * c⁻¹) = (M_base * M_base) * (c⁻¹ * c⁻¹) := by ring
      _ ≤ (M_base * M_base) * c⁻¹ := mul_le_mul_of_nonneg_left hcc (mul_nonneg hMb0 hMb0)
      _ ≤ (2 * M_base + 2 * (M_base * M_base)) * c⁻¹ := by
          nlinarith [mul_nonneg hMb0 hMb0, inv_nonneg.mpr hc0.le]) (fun _ => le_rfl)
  have hw_sym := (hm1.add hm2).add hm3
  have hpq_small : ∀ (Lf : ℂ →L[ℝ] ℝ), (∀ z, |Lf z| ≤ ‖z‖) → ∀ x ∈ S,
      |L1 * Lf (phiKill a ((tau0 (x - s) : ℂ) * Complex.I)) / (x - s)| ≤ 1 / 30 := by
    intro Lf hLf x hx
    have hxs : 3 / 4 * δ ≤ x - s := by linarith only [(abs_le.mp hs_le).2, hx.1, hδ0]
    have hu0 : 0 < x - s := by linarith only [hxs, hδ0]
    have hL1c := hL ε c hε hcL'
    have hcp' := hcp c hcp'
    have h23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hkl_bd : KL * c ^ (-(1 / 6 : ℝ)) ≤ 3 * a₀ / (80 * (C₁ + 1)) := by
      have hk1 : KL ≤ KL + 1 := by linarith
      calc KL * c ^ (-(1 / 6 : ℝ)) ≤ (KL + 1) * (3 * a₀ / (80 * (KL + 1) * (C₁ + 1))) :=
            mul_le_mul hk1 hcp' (Real.rpow_nonneg hc0.le _) (by positivity)
        _ = 3 * a₀ / (80 * (C₁ + 1)) := by field_simp
    have hL1_lo : |L1| * C₁ ≤ 1 / 30 * (3 / 4 * δ) := by
      have hC_rat : C₁ / (C₁ + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith only [hC₁0]
      calc |L1| * C₁ ≤ (KL * c ^ (-(2 / 3 : ℝ))) * C₁ := mul_le_mul_of_nonneg_right hL1c hC₁0
        _ = (KL * c ^ (-(1 / 6 : ℝ))) * C₁ * c ^ (-(1 / 2 : ℝ)) := by rw [h23]; ring
        _ ≤ (3 * a₀ / (80 * (C₁ + 1))) * C₁ * c ^ (-(1 / 2 : ℝ)) := by gcongr
        _ = 1 / 30 * (3 / 4 * (a₀ * c ^ (-(1 / 2 : ℝ)))) * (C₁ / (C₁ + 1)) := by ring
        _ ≤ 1 / 30 * (3 / 4 * (a₀ * c ^ (-(1 / 2 : ℝ)))) * 1 := mul_le_mul_of_nonneg_left hC_rat (by positivity)
        _ ≤ 1 / 30 * (3 / 4 * δ) := by rw [mul_one]; gcongr
    rw [abs_div, abs_mul, abs_of_pos hu0, div_le_iff₀ hu0]
    have hpk := (hLf _).trans (hC₁ a (tau0 (x - s)) ha0)
    calc |L1| * |Lf (phiKill a ((tau0 (x - s) : ℂ) * Complex.I))|
        ≤ |L1| * C₁ := mul_le_mul_of_nonneg_left hpk (abs_nonneg _)
      _ ≤ 1 / 30 * (3 / 4 * δ) := hL1_lo
      _ ≤ 1 / 30 * (x - s) := by gcongr
  have hw_half : ∀ x ∈ S, |-2 * f_re x + f_re x * f_re x + f_im x * f_im x| ≤ 1 / 2 := fun x hx => by
    have hr := abs_le.mp (hpq_small Complex.reCLM Complex.abs_re_le_norm x hx)
    have hi := abs_le.mp (hpq_small Complex.imCLM Complex.abs_im_le_norm x hx)
    rw [abs_le]; constructor <;> nlinarith [hr.1, hr.2, hi.1, hi.2, sq_nonneg (f_re x), sq_nonneg (f_im x)]
  have hcomp := SymW.comp_smooth hw_sym isOpen_Ioi contDiffOn_sqrtG
    (fun x hx => by show -1 < _; linarith only [(abs_le.mp (hw_half x hx)).1])
    (fun j x hx => hBj j _ (abs_le.mp (hw_half x hx))) hBj0 (fun _ _ => hcw c hcw')
    (le_max_right _ _) (fun x hx => by
      have h1 : |sqrtG (-2 * f_re x + f_re x * f_re x + f_im x * f_im x)| ≤
          |-2 * f_re x + f_re x * f_re x + f_im x * f_im x| :=
        abs_sqrtG_le (by linarith only [(abs_le.mp (hw_half x hx)).1])
      have h2 := hw_sym.bound 0 x hx
      simp only [iteratedDeriv_zero, pow_zero, inv_one, mul_one] at h2
      exact h1.trans (h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hCC0 (inv_nonneg.mpr hc0.le)))))
  exact hcomp.congr (U := Ioi s) isOpen_Ioi
    (fun x hx => by show s < x; linarith only [(abs_le.mp hs_le).2, hx.1, hδ0])
    (fun x hx => by
      have hu : 0 < x - s := sub_pos.mpr hx
      exact (norm_sub_div_eq hu (vacPhi a (x - s))).symm)

/-- Combine `fA`, `fB`, `fC` (`O/F = (1+fA)(1+fB)(1+fC)`) into `SymW [3δ/2, 3δ] (C * c⁻¹)`. -/
private lemma prod_sub_one_symW {S : Set ℝ} {CA CB CC c : ℝ} {KA KB KC : ℕ → ℝ} {fA fB fC : ℝ → ℝ}
    (hc1 : 1 ≤ c) (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCC : 0 ≤ CC)
    (hCA1 : CA * c⁻¹ ≤ 1) (hCB1 : CB * c⁻¹ ≤ 1) (hCC1 : CC * c⁻¹ ≤ 1)
    (hA : SymW S (fun _ => CA * c⁻¹) KA fA)
    (hB : SymW S (fun _ => CB * c⁻¹) KB fB)
    (hC : SymW S (fun _ => CC * c⁻¹) KC fC) :
    SymW S (fun _ => (CA + CB + CC + CA * CB + CA * CC + CB * CC + CA * CB * CC) * c⁻¹)
      (fun r => (Kmul KA (Kmul KB KC) r + (Kmul KA KB r + Kmul KA KC r + Kmul KB KC r)) + (KA r + KB r + KC r))
      (fun x => (1 + fA x) * (1 + fB x) * (1 + fC x) - 1) := by
  have hc0 : 0 < c := by linarith only [hc1]
  have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.mpr hc0.le
  set M_tot : ℝ := CA + CB + CC + CA * CB + CA * CC + CB * CC + CA * CB * CC
  have le_M : ∀ X : ℝ, 0 ≤ X → X * c⁻¹ ≤ (X * c⁻¹) → True := fun _ _ _ => trivial
  have hABC := ((hA.mul (hB.mul hC)).of_le (w' := fun _ => M_tot * c⁻¹) (fun _ _ => by
    have h1 : (CA * c⁻¹) * ((CB * c⁻¹) * (CC * c⁻¹)) = (CA * CB * CC) * c⁻¹ * (c⁻¹ * c⁻¹) := by ring
    have h2 : c⁻¹ * c⁻¹ ≤ 1 := by
      have : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
      nlinarith only [this, hc_inv]
    have h3 : (CA * CB * CC) * c⁻¹ * (c⁻¹ * c⁻¹) ≤ (CA * CB * CC) * c⁻¹ * 1 :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [h1]
    have h4 : (CA * CB * CC) * c⁻¹ ≤ M_tot * c⁻¹ := by
      dsimp only [M_tot]
      have hp : 0 ≤ (CA + CB + CC + CA * CB + CA * CC + CB * CC) * c⁻¹ := by positivity
      linarith only [hp]
    linarith only [h3, h4]) (fun _ => le_rfl))
  have mk_pair : ∀ {X Y : ℝ} {KX KY : ℕ → ℝ} {f g : ℝ → ℝ}, 0 ≤ X → 0 ≤ Y →
      X * Y ≤ M_tot →
      SymW S (fun _ => X * c⁻¹) KX f → SymW S (fun _ => Y * c⁻¹) KY g →
      SymW S (fun _ => M_tot * c⁻¹) (Kmul KX KY) (fun x => f x * g x) := by
    intro X Y KX KY f g hX hY hXY hf hg
    refine (hf.mul hg).of_le (fun _ _ => ?_) (fun _ => le_rfl)
    have h1 : (X * c⁻¹) * (Y * c⁻¹) = (X * Y) * c⁻¹ * c⁻¹ := by ring
    have h2 : c⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hc1
    have h3 : (X * Y) * c⁻¹ * c⁻¹ ≤ (X * Y) * c⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [h1]
    have h4 : (X * Y) * c⁻¹ ≤ M_tot * c⁻¹ := mul_le_mul_of_nonneg_right hXY hc_inv
    linarith only [h3, h4]
  have hAB := mk_pair hCA hCB (by dsimp only [M_tot]; nlinarith [mul_nonneg hCA hCC, mul_nonneg hCB hCC, mul_nonneg (mul_nonneg hCA hCB) hCC]) hA hB
  have hAC := mk_pair hCA hCC (by dsimp only [M_tot]; nlinarith [mul_nonneg hCA hCB, mul_nonneg hCB hCC, mul_nonneg (mul_nonneg hCA hCB) hCC]) hA hC
  have hBC := mk_pair hCB hCC (by dsimp only [M_tot]; nlinarith [mul_nonneg hCA hCB, mul_nonneg hCA hCC, mul_nonneg (mul_nonneg hCA hCB) hCC]) hB hC
  have mk_one : ∀ {X : ℝ} {KX : ℕ → ℝ} {f : ℝ → ℝ}, X ≤ M_tot →
      SymW S (fun _ => X * c⁻¹) KX f → SymW S (fun _ => M_tot * c⁻¹) KX f := fun hXM hf =>
    hf.of_le (fun _ _ => mul_le_mul_of_nonneg_right hXM hc_inv) (fun _ => le_rfl)
  have hA' := mk_one (by dsimp only [M_tot]; nlinarith [mul_nonneg hCA hCB, mul_nonneg hCA hCC, mul_nonneg hCB hCC, mul_nonneg (mul_nonneg hCA hCB) hCC]) hA
  have hB' := mk_one (by dsimp only [M_tot]; nlinarith [mul_nonneg hCA hCB, mul_nonneg hCA hCC, mul_nonneg hCB hCC, mul_nonneg (mul_nonneg hCA hCB) hCC]) hB
  have hC' := mk_one (by dsimp only [M_tot]; nlinarith [mul_nonneg hCA hCB, mul_nonneg hCA hCC, mul_nonneg hCB hCC, mul_nonneg (mul_nonneg hCA hCB) hCC]) hC
  have htot := (hABC.add ((hAB.add hAC).add hBC)).add ((hA'.add hB').add hC')
  have htot' := htot.of_le (fun _ _ => by ring_nf; rfl) (fun _ => le_rfl)
  refine (htot.congr (U := univ) isOpen_univ (subset_univ _) (fun x _ => by ring)).of_le (fun _ _ => ?_) (fun _ => le_rfl)
  linarith only

/-- **Middle-band symbol bound for `p₁`**: on `[3δ/2, 3δ]`, `p₁` has weight `C_diff(K₄) * c^{-1/4}` (`C_diff` independent of `K₁`). -/
theorem physDiff_mid_symW {χ : ℝ → ℝ} (hχ : IsCutoff χ) {K4 : ℝ} (hK4 : 1 ≤ K4)
    {T1 alpha : ℝ → ℝ → ℝ} (hwarp : FctWarpZeroStmt T1 alpha) :
    ∃ (c₀ C_diff : ℝ) (K_diff : ℕ → ℝ), 2 ≤ c₀ ∧ 0 ≤ C_diff ∧ (∀ r, 0 ≤ K_diff r) ∧
      ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        SymW (Icc (3 / 2 * physDelta c) (3 * physDelta c)) (fun _ => C_diff * c ^ (-(1 / 4 : ℝ))) K_diff
          (fun x => χ (x / (3 * physDelta c)) * physGamma c (physShift ε c) x *
            (physOscDatum StripKernelChoice.star K4 T1 alpha ε c x -
              physF (physShift ε c) (physL1 T1 ε c) x)) := by
  obtain ⟨Kχ, hKχ0, hKχ⟩ := isCutoff_deriv_bound hχ
  obtain ⟨Cw, cw, hw⟩ := hwarp
  have hT1 : ∃ C c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |T1 ε c - ctDelta5 ε c| ≤ C * c⁻¹ :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).1⟩
  have hα : ∃ Kα c₀ : ℝ, ∀ ε c : ℝ, (ε = 1 ∨ ε = -1) → c₀ ≤ c → |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) :=
    ⟨Cw, cw, fun ε c hε hc => (hw ε c hε hc).2⟩
  obtain ⟨Kα, cα, hαf⟩ := hα
  have hKα0 : 0 ≤ Kα := by
    have := hαf 1 (max cα 1) (Or.inl rfl) (le_max_left _ _)
    have h0 : 0 < (max cα 1) ^ (-(2 / 3 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    by_contra hneg
    have := mul_neg_of_neg_of_pos (not_le.mp hneg) h0
    linarith [abs_nonneg (alpha 1 (max cα 1))]
  obtain ⟨cs, a₀, a₁, hcs, ha₀, hsc⟩ := physDatum_scales T1 hT1
  obtain ⟨cA, CA, KA, hcA2, hCA0, hKA0, hFA⟩ := mid_factorA_symW hK4 hwarp
  obtain ⟨cB, CB, KB, hcB2, hCB0, hKB0, hFB⟩ := mid_factorB_symW hK4 hwarp
  obtain ⟨cC, CC, KC, hcC2, hCC0, hKC0, hFC⟩ := mid_factorC_symW hwarp
  obtain ⟨τc, hτc, hvacP_inner⟩ := mid_vacP_eq
  obtain ⟨c_tau, hc_tau1, hc_tau⟩ := FctSym.exists_rpow_neg_le (p := 1 / 4)
    (η := min τc (1 / 20)) (by norm_num) (lt_min hτc (by norm_num))
  obtain ⟨c_al, hc_al1, hc_al⟩ := FctSym.exists_rpow_neg_le (p := 1 / 6) (η := 1 / (Kα + 1)) (by norm_num) (by positivity)
  set CR : ℝ := CA + CB + CC + CA * CB + CA * CC + CB * CC + CA * CB * CC
  have hCR0 : 0 ≤ CR := by positivity
  have hc_R_ex : ∃ c_R : ℝ, 2 ≤ c_R ∧ ∀ c : ℝ, c_R ≤ c → CA * c⁻¹ ≤ 1 ∧ CB * c⁻¹ ≤ 1 ∧ CC * c⁻¹ ≤ 1 := by
    refine ⟨max 2 (CA + CB + CC + 1), le_max_left _ _, fun c hc => ?_⟩
    have hcpos : 0 < c := by linarith [le_max_left 2 (CA + CB + CC + 1) |>.trans hc]
    have hc_bd : CA + CB + CC ≤ c := by linarith [le_max_right 2 (CA + CB + CC + 1) |>.trans hc]
    refine ⟨?_, ?_, ?_⟩ <;> rw [mul_inv_le_iff₀ hcpos] <;> linarith only [hCA0, hCB0, hCC0, hc_bd]
  obtain ⟨c_R, hcR2, hcR⟩ := hc_R_ex
  set CF : ℝ := |uctAlphaFl| * (3 / 2 * a₀) ^ (-(3 / 2 : ℝ))
  have hCF0 : 0 ≤ CF := by positivity
  set C_diff : ℝ := 2 * CF * CR
  have hCdiff0 : 0 ≤ C_diff := by positivity
  set KR : ℕ → ℝ := fun r => (Kmul KA (Kmul KB KC) r + (Kmul KA KB r + Kmul KA KC r + Kmul KB KC r)) +
    (KA r + KB r + KC r)
  set KF_k : ℕ → ℝ := Kmul (fun r => Kone r + Kpow (-1) r) (Kpow (-(3 / 2)))
  set K_diff : ℕ → ℝ := Kmul (Kmul Kχ Kgam) (Kmul KF_k KR)
  refine ⟨max (max (max cs cα) (max cA (max cB cC))) (max (max c_tau c_al) c_R), C_diff, K_diff,
    (le_max_right _ _).trans' ((le_max_right _ _).trans' hcR2) |>.trans (le_refl _),
    hCdiff0, Kmul_nonneg (Kmul_nonneg hKχ0 fun r => add_nonneg (Kone_nonneg r) (Kpow_nonneg (-3) r))
      (Kmul_nonneg (Kmul_nonneg (fun r => add_nonneg (Kone_nonneg r) (Kpow_nonneg (-1) r)) (Kpow_nonneg (-(3 / 2))))
        fun r => add_nonneg (add_nonneg (Kmul_nonneg hKA0 (Kmul_nonneg hKB0 hKC0) r)
          (add_nonneg (add_nonneg (Kmul_nonneg hKA0 hKB0 r) (Kmul_nonneg hKA0 hKC0 r)) (Kmul_nonneg hKB0 hKC0 r)))
          (add_nonneg (add_nonneg (hKA0 r) (hKB0 r)) (hKC0 r))), ?_⟩
  intro ε c hε hc
  simp only [max_le_iff] at hc
  obtain ⟨⟨⟨hcs', hcα'⟩, ⟨hcA', ⟨hcB', hcC'⟩⟩⟩, ⟨⟨hct', hcal'⟩, hcR'⟩⟩ := hc
  obtain ⟨hδ0, hδ1, hs_le, hL1_le, hLs_le, hsmall, hδ_lo, hδ_hi, h6δ⟩ := hsc ε c hε hcs'
  have hc2 : 2 ≤ c := hcR2.trans hcR'
  have hc0 : 0 < c := by linarith only [hc2]
  have hc1 : 1 ≤ c := by linarith only [hc2]
  set δ := physDelta c
  set s := physShift ε c
  set L1 := physL1 T1 ε c
  set S := Icc (3 / 2 * δ) (3 * δ)
  have hS_ci : S ⊆ Ici (3 / 2 * δ) := fun _ hx => hx.1
  have hχ_sym := (cutoff_dil_symW hχ hKχ0 hKχ hδ0).mono_set hS_ci
  have hγ_sym := (physGamma_sym hδ0 hs_le hsmall).mono_set hS_ci
  have hF_sym0 := (physF_sym hδ0 hs_le hL1_le hLs_le).mono_set hS_ci
  have hF_sym : SymW S (fun _ => CF * c ^ (3 / 4 : ℝ)) KF_k (physF s L1) := by
    refine hF_sym0.of_le (fun x hx => ?_) (fun _ => le_rfl)
    have hx1 : x ≤ 1 := by linarith only [hx.2, h6δ]
    have hpw : pw |uctAlphaFl| (3 / 2) (3 / 2) x = |uctAlphaFl| * x ^ (-(3 / 2 : ℝ)) := by
      unfold pw; simp [hx1]
    have hx_lo : 3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ)) ≤ x := by
      have h1 : 3 / 2 * (a₀ * c ^ (-(1 / 2 : ℝ))) ≤ 3 / 2 * δ := mul_le_mul_of_nonneg_left hδ_lo (by norm_num)
      linarith only [h1, hx.1]
    have hpow : x ^ (-(3 / 2 : ℝ)) ≤ (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hx_lo (by norm_num)
    have hsep : (3 / 2 * a₀ * c ^ (-(1 / 2 : ℝ))) ^ (-(3 / 2 : ℝ)) =
        (3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * c ^ (3 / 4 : ℝ) := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul hc0.le, show (-(1 / 2 : ℝ)) * (-(3 / 2 : ℝ)) = 3 / 4 by norm_num]
    rw [hpw, hsep]
    calc |uctAlphaFl| * ((3 / 2 * a₀) ^ (-(3 / 2 : ℝ)) * c ^ (3 / 4 : ℝ)) = CF * c ^ (3 / 4 : ℝ) := by
          dsimp only [CF]; ring
  obtain ⟨hCA1, hCB1, hCC1⟩ := hcR c hcR'
  have hR_sym := prod_sub_one_symW hc1 hCA0 hCB0 hCC0 hCA1 hCB1 hCC1
    (hFA ε c hε hcA') (hFB ε c hε hcB') (hFC ε c hε hcC')
  have htot := ((hχ_sym.mul hγ_sym).mul (hF_sym.mul hR_sym)).of_le (w' := fun _ => C_diff * c ^ (-(1 / 4 : ℝ))) (fun _ _ => by
    have hc_pow : c ^ (3 / 4 : ℝ) * c⁻¹ = c ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_neg_one c, ← Real.rpow_add hc0]; norm_num
    calc (1 * 2) * (CF * c ^ (3 / 4 : ℝ) * (CR * c⁻¹)) = (2 * CF * CR) * (c ^ (3 / 4 : ℝ) * c⁻¹) := by ring
      _ = C_diff * c ^ (-(1 / 4 : ℝ)) := by dsimp only [C_diff]; rw [hc_pow]) (fun _ => le_rfl)
  -- Show `physOscDatum - physF = physF * ((1+fA)(1+fB)(1+fC) - 1)` on an open neighborhood of `S`:
  set τ₁ : ℝ := c ^ (-(1 / 4 : ℝ))
  have hτ₁pos : 0 < τ₁ := Real.rpow_pos_of_pos hc0 _
  have hτ₁_bd : τ₁ ≤ min τc (1 / 20) := hc_tau c hct'
  have hτc' : τ₁ ≤ τc := hτ₁_bd.trans (min_le_left _ _)
  have hτ₁_20 : τ₁ ≤ 1 / 20 := hτ₁_bd.trans (min_le_right _ _)
  have hτ₁_four : τ₁ ^ 4 * c = 1 := by
    have : τ₁ ^ 4 = c⁻¹ := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 4, ← Real.rpow_mul hc0.le,
        show (-(1 / 4 : ℝ)) * (4 : ℕ) = -1 by norm_num, Real.rpow_neg_one]
    rw [this]; field_simp
  have hα_bd : |alpha ε c| ≤ τ₁ ^ 2 := by
    have h1 := hαf ε c hε hcα'
    have h2 : c ^ (-(1 / 6 : ℝ)) ≤ 1 / (Kα + 1) := hc_al c hcal'
    have h23 : c ^ (-(2 / 3 : ℝ)) = c ^ (-(1 / 6 : ℝ)) * c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_add hc0]; norm_num
    have hτ₁_sq : τ₁ ^ 2 = c ^ (-(1 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast (c ^ (-(1 / 4 : ℝ))) 2, ← Real.rpow_mul hc0.le]; norm_num
    have hk : Kα * c ^ (-(1 / 6 : ℝ)) ≤ 1 := by
      calc Kα * c ^ (-(1 / 6 : ℝ)) ≤ Kα * (1 / (Kα + 1)) :=
            mul_le_mul_of_nonneg_left h2 hKα0
        _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith only [hKα0]
    rw [hτ₁_sq]
    calc |alpha ε c| ≤ Kα * c ^ (-(2 / 3 : ℝ)) := h1
      _ = (Kα * c ^ (-(1 / 6 : ℝ))) * c ^ (-(1 / 2 : ℝ)) := by rw [h23]; ring
      _ ≤ 1 * c ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hc0.le _)
      _ = c ^ (-(1 / 2 : ℝ)) := one_mul _
  have h31 : 31 / 10 * uctM τ₁ < uctM (2 * τ₁) := uctM_two_gt_31 hτ₁pos hτ₁_20
  have hU_open : IsOpen (Ioo (max s L1) (uctM (2 * τ₁) + s)) := isOpen_Ioo
  have hS_sub_U : S ⊆ Ioo (max s L1) (uctM (2 * τ₁) + s) := by
    intro x hx
    refine ⟨max_lt (by linarith only [(abs_le.mp hs_le).2, hx.1, hδ0])
        (by linarith only [(abs_le.mp hL1_le).2, hx.1, hδ0]), ?_⟩
    have h1 : x - s ≤ 3 * δ + 3 / 4 * δ := by linarith only [(abs_le.mp hs_le).1, hx.2]
    change 31 / 10 * uctM τ₁ < uctM (2 * τ₁) at h31
    change δ = uctM τ₁ at *
    linarith only [uctM_pos hτ₁pos, h1, h31]
  refine htot.congr hU_open hS_sub_U (fun x hx => ?_)
  have hxs_pos : 0 < x - s := sub_pos.mpr ((le_max_left s L1).trans_lt hx.1)
  have hxL1_pos : 0 < x - L1 := sub_pos.mpr ((le_max_right s L1).trans_lt hx.1)
  have htpos : 0 < tau0 (x - s) := tau0_pos hxs_pos
  have ht2 : tau0 (x - s) ≤ 2 * τ₁ :=
    (tau0_lt_of_lt (by positivity) hxs_pos (by linarith only [hx.2])).le
  have hmu : uctM (tau0 (x - s)) = x - s := ceEll_tau0 hxs_pos
  have hv := hvacP_inner hK4 hc0 hτ₁pos hτc' hτ₁_four hα_bd htpos ht2
  rw [hmu] at hv
  have hu0 : x - s ≠ 0 := hxs_pos.ne'
  show χ (x / (3 * δ)) * physGamma c s x *
      (physF s L1 x * ((1 + (Real.exp (-(K4 * tau0 (x - s) ^ 4) + alpha ε c * tau0 (x - s) ^ 2) - 1)) *
        (1 + (Real.exp (-stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) (tau0 (x - s))) *
          (1 + stripDeltaCurv c (fctThetaD (v0 StripKernelChoice.star K4 τ₁)) (tau0 (x - s))) - 1)) *
        (1 + (‖((x - s : ℝ) : ℂ) - (L1 : ℂ) * vacPhi (c ^ (-(1 / 12 : ℝ))) (x - s)‖ / (x - s) - 1)) - 1)) =
    χ (x / (3 * δ)) * physGamma c s x *
      (physOscDatum StripKernelChoice.star K4 T1 alpha ε c x - physF s L1 x)
  unfold physOscDatum physOsc physF
  dsimp only [δ, s, L1, τ₁] at hv ⊢
  rw [hv]
  field_simp

/-- info: 'FormalResearch.SignUncertainty.physDiff_mid_symW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms physDiff_mid_symW

end FormalResearch.SignUncertainty
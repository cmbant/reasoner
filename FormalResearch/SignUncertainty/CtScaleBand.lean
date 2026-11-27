module

public import FormalResearch.SignUncertainty.HankelBootData
public import FormalResearch.SignUncertainty.CtBoasMBounds
public import FormalResearch.Analysis.VanDerCorput
public import FormalResearch.ModularBootstrap.StripBand.BandReduction
public import FormalResearch.ModularBootstrap.StripBand.BandReductionBV
public import FormalResearch.Complex.StripPoisson

/-!
# Scale-`r` strip-band reduction `ct:Wbound` (`constant_terms_lower.tex` `ct:dyadic` (1) Step 1a)

For every scale `r ∈ [256, R_J]` (`R_J ∈ [10⁻⁴ c^{2/3}, 10⁻⁴ c^{2/3} + 1]`) and every
`ζ₀ = ρ e^{iψ}` in the scale-`r` annulus `ρ_r / 3 ≤ ‖ζ₀‖ ≤ 2 ρ_r` (`ρ_r = 2 κ c^{-1/3} √r`) with
`cos ψ > 0`, decomposes `H₀(ζ₀) = ∫ Q(τ) H₀(iτ) dτ` via the three-piece cutoff
`1 = (1 - χ₀) + χ₁ + χ₂` (`χ₀ = χ(· / δ₀)`, `ψ_r = χ(· / (4 ρ_r))`, `χ₁ = χ₀ (1 - ψ_r)`,
`χ₂ = ψ_r`) and proves `(ct:Wbound)`:
`‖W̃_c(ζ₀)‖ ≤ C * (r^{-3/2} + r^{-7/4} ∫_{[ξ(u_T), ξ(-min(1028 r, R_J))]} (-ũ) dm_+ + r^{-3/4}(B₂(r) + B₂(R_J))) / cos ψ`.

Main declarations:
* `hankel_scale_band_reduction`: `(ct:Wbound)` at any scale `r ∈ [256, R_J]`.
* `hankel_scale_band_reduction_B1`: same statement written with `hankelBootB1` at `r̃ = min(1028 r, R_J)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real ENNReal Interval

open FormalResearch.Analysis
open FormalResearch.StripPoisson
open FormalResearch.ModularBootstrap.StripBand
open FormalResearch.CohnElkies

namespace FormalResearch.SignUncertainty

section Helpers

private lemma continuous_tebAmp0 (c : ℝ) : Continuous (tebAmp0 c) := by
  have hre : ∀ τ : ℝ, ((τ : ℂ) * Complex.I) ∈ {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} := fun τ => by
    simp
  exact (tebPrefactor_continuousOn c).comp_continuous
    (Complex.continuous_ofReal.mul continuous_const) hre

private lemma rpow_mul_exp_neg_sq_le_scale {p q : ℝ} {x : ℝ} (hx : 1 ≤ x) :
    x ^ p * Real.exp (-x ^ 2) ≤ (Nat.factorial (Nat.ceil ((p + q) / 2)) : ℝ) * x ^ (-q) := by
  set m := Nat.ceil ((p + q) / 2)
  have hm : (p + q) / 2 ≤ m := Nat.le_ceil _
  have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hexp : (x ^ 2) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp (x ^ 2) :=
    (Finset.single_le_sum (f := fun i => (x ^ 2) ^ i / (Nat.factorial i : ℝ))
      (fun i _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_self m))).trans
      (Real.sum_le_exp_of_nonneg (sq_nonneg x) (m + 1))
  have hexp_inv : Real.exp (-x ^ 2) ≤ (Nat.factorial m : ℝ) * x ^ (-2 * (m : ℝ)) := by
    rw [Real.exp_neg]
    have hpow : x ^ (2 * (m : ℝ)) = (x ^ 2) ^ m := by
      rw [← Real.rpow_natCast (x ^ 2) m, ← Real.rpow_natCast x 2, ← Real.rpow_mul hx_pos.le]
      ring_nf
    have hexp' : x ^ (2 * (m : ℝ)) / (Nat.factorial m : ℝ) ≤ Real.exp (x ^ 2) := hpow ▸ hexp
    have h1 : (Real.exp (x ^ 2))⁻¹ ≤ (x ^ (2 * (m : ℝ)) / (Nat.factorial m : ℝ))⁻¹ :=
      inv_anti₀ (by positivity) hexp'
    rw [show (-2 * (m : ℝ)) = -(2 * (m : ℝ)) by ring, Real.rpow_neg hx_pos.le]
    calc (Real.exp (x ^ 2))⁻¹ ≤ (x ^ (2 * (m : ℝ)) / (Nat.factorial m : ℝ))⁻¹ := h1
      _ = (Nat.factorial m : ℝ) * (x ^ (2 * (m : ℝ)))⁻¹ := by rw [inv_div, mul_comm, div_eq_mul_inv]
  calc x ^ p * Real.exp (-x ^ 2)
      ≤ x ^ p * ((Nat.factorial m : ℝ) * x ^ (-2 * (m : ℝ))) := by gcongr
    _ = (Nat.factorial m : ℝ) * (x ^ p * x ^ (-2 * (m : ℝ))) := by ring
    _ = (Nat.factorial m : ℝ) * x ^ (p - 2 * (m : ℝ)) := by
        rw [← Real.rpow_add hx_pos, show p - 2 * (m : ℝ) = p + -2 * (m : ℝ) by ring]
    _ ≤ (Nat.factorial m : ℝ) * x ^ (-q) := by
        gcongr; linarith

private lemma integrable_one_add_abs_rpow_mul_exp_neg_sq {p : ℝ} (hp : 0 ≤ p) :
    Integrable (fun τ : ℝ => (1 + |τ|) ^ p * Real.exp (-τ ^ 2)) := by
  let g : ℝ → ℝ := fun τ => (1 + |τ|) ^ p * Real.exp (-τ ^ 2)
  have hg_cont : Continuous g := by
    refine Continuous.mul ((continuous_const.add continuous_abs).rpow_const fun τ => ?_)
      (Real.continuous_exp.comp (continuous_neg.comp (continuous_pow 2)))
    left; show 1 + |τ| ≠ 0; linarith [abs_nonneg τ]
  have h_top : IntegrableOn g (Ioi 1) := by
    set m := Nat.ceil ((p + 2) / 2)
    have hm_int : IntegrableOn (fun τ : ℝ => (2 : ℝ) ^ p * (Nat.factorial m : ℝ) * τ ^ (-2 : ℝ))
        (Ioi 1) :=
      ((integrableOn_Ioi_rpow_iff (s := (-2 : ℝ)) zero_lt_one).mpr (by norm_num)).const_mul _
    refine hm_int.mono' (hg_cont.aestronglyMeasurable.mono_measure Measure.restrict_le_self) ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun τ (hτ : 1 < τ) => ?_
    have h1 : 1 ≤ τ := hτ.le
    have hg_nn : 0 ≤ g τ := mul_nonneg (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hg_nn]
    have h1τ : (1 + |τ|) ^ p ≤ (2 : ℝ) ^ p * τ ^ p := by
      rw [abs_of_pos (lt_of_lt_of_le zero_lt_one h1), ← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hp
    have hr := rpow_mul_exp_neg_sq_le_scale (p := p) (q := 2) h1
    dsimp [g]
    calc (1 + |τ|) ^ p * Real.exp (-τ ^ 2)
        ≤ (2 : ℝ) ^ p * τ ^ p * Real.exp (-τ ^ 2) := by gcongr
      _ = (2 : ℝ) ^ p * (τ ^ p * Real.exp (-τ ^ 2)) := by ring
      _ ≤ (2 : ℝ) ^ p * ((Nat.factorial m : ℝ) * τ ^ (-2 : ℝ)) := by gcongr
      _ = (2 : ℝ) ^ p * (Nat.factorial m : ℝ) * τ ^ (-2 : ℝ) := by ring
  have h_bot : IntegrableOn g (Iio (-1)) := by
    have hpre : Neg.neg ⁻¹' Ioi (1 : ℝ) = Iio (-1) := by ext x; simp
    have h_neg := h_top.comp_neg
    change IntegrableOn (fun x => g (-x)) (Neg.neg ⁻¹' Ioi 1) volume at h_neg
    rw [hpre] at h_neg
    exact h_neg.congr_fun (fun τ _ => by dsimp [g]; simp [abs_neg]) measurableSet_Iio
  have h_mid : IntegrableOn g (Icc (-1) 1) := hg_cont.continuousOn.integrableOn_Icc
  have h_univ : (univ : Set ℝ) ⊆ Iio (-1) ∪ Icc (-1) 1 ∪ Ioi 1 := fun x _ => by
    rcases lt_or_ge x (-1) with h1 | h1
    · left; left; exact h1
    · rcases le_or_gt x 1 with h2 | h2
      · left; right; exact ⟨h1, h2⟩
      · right; exact h2
  exact integrableOn_univ.mp (((h_bot.union h_mid).union h_top).mono_set h_univ)

private lemma one_add_rpow_nine_exp_le (s : ℝ) (hs : 0 ≤ s) :
    (1 + s) ^ (9 : ℝ) * Real.exp (-s ^ 2) ≤ 2 ^ 9 * (Nat.factorial 6 : ℝ) := by
  rcases le_or_gt s 1 with hs1 | hs1
  · have h1 : (1 + s) ^ (9 : ℝ) ≤ (2 : ℝ) ^ (9 : ℝ) :=
      Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have h2 : Real.exp (-s ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
    have h3 : (2 : ℝ) ^ (9 : ℝ) = (2 : ℝ) ^ (9 : ℕ) := by norm_num
    have hfac : (1 : ℝ) ≤ (Nat.factorial 6 : ℝ) := by norm_num [Nat.factorial]
    calc (1 + s) ^ (9 : ℝ) * Real.exp (-s ^ 2) ≤ (2 : ℝ) ^ (9 : ℝ) * 1 :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = (2 : ℝ) ^ 9 * 1 := by rw [h3]
      _ ≤ (2 : ℝ) ^ 9 * (Nat.factorial 6 : ℝ) := by gcongr
  · have h1s : 1 + s ≤ 2 * s := by linarith
    have hpow : (1 + s) ^ (9 : ℝ) ≤ 2 ^ 9 * s ^ (9 : ℝ) := by
      have := Real.rpow_le_rpow (by linarith) h1s (show (0 : ℝ) ≤ 9 by norm_num)
      rw [Real.mul_rpow zero_le_two hs] at this
      simpa [show (2 : ℝ) ^ (9 : ℝ) = 2 ^ 9 by norm_num] using this
    have hexp := rpow_mul_exp_neg_sq_le_scale (p := 9) (q := 0) hs1.le
    have hceil : Nat.ceil (((9 : ℝ) + 0) / 2) = 5 := by norm_num
    rw [hceil, neg_zero, Real.rpow_zero, mul_one] at hexp
    have hfac : (Nat.factorial 5 : ℝ) ≤ (Nat.factorial 6 : ℝ) := by
      exact_mod_cast Nat.factorial_le (by norm_num)
    calc (1 + s) ^ (9 : ℝ) * Real.exp (-s ^ 2)
        ≤ (2 ^ 9 * s ^ (9 : ℝ)) * Real.exp (-s ^ 2) :=
          mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
      _ = 2 ^ 9 * (s ^ (9 : ℝ) * Real.exp (-s ^ 2)) := by ring
      _ ≤ 2 ^ 9 * (Nat.factorial 5 : ℝ) := mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 2 ^ 9 * (Nat.factorial 6 : ℝ) := by gcongr

private lemma outer_rpow_poly_exp_le {s : ℝ} (hs : 0 < s) :
    (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) / min (s ^ 2) 1 ≤
      2 ^ 9 * (Nat.factorial 6 : ℝ) * s ^ (-(3 / 2 : ℝ)) := by
  have hs_le_fac : (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) ≤ s ^ (1 / 2 : ℝ) * (1 + s) ^ (2 : ℝ) := by
    have h1 : s ^ (-2 : ℝ) * s ^ (5 / 2 : ℝ) = s ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hs]; norm_num
    have h2 : s ^ (5 / 2 : ℝ) = s ^ (1 / 2 : ℝ) * s ^ (2 : ℝ) := by
      rw [← Real.rpow_add hs]; norm_num
    have hsq : 1 + s ^ (2 : ℝ) ≤ (1 + s) ^ (2 : ℝ) := by
      norm_cast; nlinarith [hs.le]
    calc (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ)
        = s ^ (5 / 2 : ℝ) + s ^ (-2 : ℝ) * s ^ (5 / 2 : ℝ) := by ring
      _ = s ^ (1 / 2 : ℝ) * (1 + s ^ (2 : ℝ)) := by rw [h1, h2]; ring
      _ ≤ s ^ (1 / 2 : ℝ) * (1 + s) ^ (2 : ℝ) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg hs.le _)
  have hcomb : (1 + s) ^ (2 : ℝ) * (1 + s) ^ (7 : ℝ) = (1 + s) ^ (9 : ℝ) := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  rcases le_or_gt s 1 with hs1 | hs1
  · have hmin : min (s ^ 2) 1 = s ^ 2 := min_eq_left (by nlinarith)
    have hsr : s ^ (1 / 2 : ℝ) / s ^ 2 = s ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast s 2, ← Real.rpow_sub hs]; norm_num
    have hexp := one_add_rpow_nine_exp_le s hs.le
    calc (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) / min (s ^ 2) 1
        ≤ (s ^ (1 / 2 : ℝ) * (1 + s) ^ (2 : ℝ)) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) / s ^ 2 := by
          rw [hmin]; gcongr
      _ = (s ^ (1 / 2 : ℝ) / s ^ 2) * ((1 + s) ^ (9 : ℝ) * Real.exp (-s ^ 2)) := by
          rw [← hcomb]; ring
      _ ≤ s ^ (-(3 / 2 : ℝ)) * (2 ^ 9 * (Nat.factorial 6 : ℝ)) := by
          rw [hsr]; exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hs.le _)
      _ = _ := by ring
  · have hmin : min (s ^ 2) 1 = 1 := min_eq_right (by nlinarith)
    have h1s : 1 + s ≤ 2 * s := by linarith
    have hpow : (1 + s) ^ (9 : ℝ) ≤ 2 ^ 9 * s ^ (9 : ℝ) := by
      have := Real.rpow_le_rpow (by linarith) h1s (show (0 : ℝ) ≤ 9 by norm_num)
      rw [Real.mul_rpow zero_le_two hs.le] at this
      simpa [show (2 : ℝ) ^ (9 : ℝ) = 2 ^ 9 by norm_num] using this
    have hexp := rpow_mul_exp_neg_sq_le_scale (p := 19 / 2) (q := 3 / 2) hs1.le
    have hceil : Nat.ceil (((19 / 2 : ℝ) + 3 / 2) / 2) = 6 := by norm_num
    rw [hceil] at hexp
    have h19 : s ^ (1 / 2 : ℝ) * s ^ (9 : ℝ) = s ^ (19 / 2 : ℝ) := by
      rw [← Real.rpow_add hs]; norm_num
    calc (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) / min (s ^ 2) 1
        ≤ (s ^ (1 / 2 : ℝ) * (1 + s) ^ (2 : ℝ)) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) / 1 := by
          rw [hmin]; gcongr
      _ = s ^ (1 / 2 : ℝ) * (1 + s) ^ (9 : ℝ) * Real.exp (-s ^ 2) := by
          rw [div_one, ← hcomb]; ring
      _ ≤ s ^ (1 / 2 : ℝ) * (2 ^ 9 * s ^ (9 : ℝ)) * Real.exp (-s ^ 2) := by gcongr
      _ = 2 ^ 9 * (s ^ (19 / 2 : ℝ) * Real.exp (-s ^ 2)) := by rw [← h19]; ring
      _ ≤ 2 ^ 9 * ((Nat.factorial 6 : ℝ) * s ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by ring

private lemma outer_saddle_factor_le {τ : ℝ} (hτ : 0 < τ) :
    (1 + τ ^ (-2 : ℝ)) * τ ^ (5 / 2 : ℝ) * (1 + τ) ^ (7 : ℝ) * Real.exp (-τ ^ 2) /
        Real.sqrt (τ / (1 + τ ^ 3)) ≤
      2 ^ 10 * (Nat.factorial 7 : ℝ) := by
  have h1τ : Real.sqrt (1 + τ ^ 3) ≤ (1 + τ) ^ (3 / 2 : ℝ) := by
    have hle : 1 + τ ^ 3 ≤ (1 + τ) ^ 3 := by
      have : (1 + τ) ^ 3 = 1 + 3 * τ + 3 * τ ^ 2 + τ ^ 3 := by ring
      nlinarith [hτ.le, sq_nonneg τ]
    calc Real.sqrt (1 + τ ^ 3) ≤ Real.sqrt ((1 + τ) ^ 3) := Real.sqrt_le_sqrt hle
      _ = (1 + τ) ^ (3 / 2 : ℝ) := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (1 + τ) 3, ← Real.rpow_mul (by linarith)]
          norm_num
  have hτ_comb : (1 + τ ^ (-2 : ℝ)) * τ ^ (5 / 2 : ℝ) / Real.sqrt τ =
      (1 + τ ^ (2 : ℝ)) := by
    have hs : Real.sqrt τ = τ ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow τ
    have h1 : τ ^ (-2 : ℝ) * τ ^ (5 / 2 : ℝ) = τ ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hτ]; norm_num
    have h2 : τ ^ (5 / 2 : ℝ) = τ ^ (1 / 2 : ℝ) * τ ^ (2 : ℝ) := by
      rw [← Real.rpow_add hτ]; norm_num
    rw [hs]
    have hpos : τ ^ (1 / 2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hτ _).ne'
    calc (1 + τ ^ (-2 : ℝ)) * τ ^ (5 / 2 : ℝ) / τ ^ (1 / 2 : ℝ)
        = (τ ^ (1 / 2 : ℝ) * (1 + τ ^ (2 : ℝ))) / τ ^ (1 / 2 : ℝ) := by
            congr 1; rw [add_mul, one_mul, h1, h2]; ring
      _ = 1 + τ ^ (2 : ℝ) := mul_div_cancel_left₀ _ hpos
  have hsq : 1 + τ ^ (2 : ℝ) ≤ (1 + τ) ^ (2 : ℝ) := by
    norm_cast; nlinarith [hτ.le]
  have hcomb : (1 + τ) ^ (2 : ℝ) * (1 + τ) ^ (7 : ℝ) * (1 + τ) ^ (3 / 2 : ℝ) =
      (1 + τ) ^ (21 / 2 : ℝ) := by
    rw [← Real.rpow_add (by linarith), ← Real.rpow_add (by linarith)]; norm_num
  have hpow11 : (1 + τ) ^ (21 / 2 : ℝ) ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) * Real.exp (τ ^ 2) := by
    rcases le_or_gt τ 1 with hτ1 | hτ1
    · have hp1 : (1 + τ) ^ (21 / 2 : ℝ) ≤ (2 : ℝ) ^ (21 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
      have hp2 : (2 : ℝ) ^ (21 / 2 : ℝ) ≤ 2 ^ 11 := by
        calc (2 : ℝ) ^ (21 / 2 : ℝ) ≤ (2 : ℝ) ^ (11 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
          _ = 2 ^ 11 := by norm_num
      have hexp1 : (1 : ℝ) ≤ Real.exp (τ ^ 2) := Real.one_le_exp (sq_nonneg _)
      have hnum : (2 : ℝ) ^ 11 ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) := by norm_num [Nat.factorial]
      calc (1 + τ) ^ (21 / 2 : ℝ) ≤ 2 ^ 11 := hp1.trans hp2
        _ ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) := hnum
        _ ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) * Real.exp (τ ^ 2) :=
            le_mul_of_one_le_right (by positivity) hexp1
    · have h1τ' : 1 + τ ≤ 2 * τ := by linarith
      have hp : (1 + τ) ^ (21 / 2 : ℝ) ≤ 2 ^ (21 / 2 : ℝ) * τ ^ (21 / 2 : ℝ) := by
        have := Real.rpow_le_rpow (by linarith) h1τ' (show (0 : ℝ) ≤ 21 / 2 by norm_num)
        rwa [Real.mul_rpow zero_le_two hτ.le] at this
      have hexp := rpow_mul_exp_neg_sq_le_scale (p := 21 / 2) (q := 0) hτ1.le
      have hceil : Nat.ceil (((21 / 2 : ℝ) + 0) / 2) = 6 := by norm_num
      rw [hceil, neg_zero, Real.rpow_zero, mul_one] at hexp
      have hp_fac : (2 : ℝ) ^ (21 / 2 : ℝ) ≤ 2 ^ 11 := by
        calc (2 : ℝ) ^ (21 / 2 : ℝ) ≤ (2 : ℝ) ^ (11 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num)
          _ = 2 ^ 11 := by norm_num
      have hexp_pos : 0 < Real.exp (-τ ^ 2) := Real.exp_pos _
      have h2fac : (2 : ℝ) ^ 11 * (Nat.factorial 6 : ℝ) ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) := by
        norm_num [Nat.factorial]
      have hmul : (1 + τ) ^ (21 / 2 : ℝ) * Real.exp (-τ ^ 2) ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) :=
        calc (1 + τ) ^ (21 / 2 : ℝ) * Real.exp (-τ ^ 2)
            ≤ (2 ^ (21 / 2 : ℝ) * τ ^ (21 / 2 : ℝ)) * Real.exp (-τ ^ 2) :=
              mul_le_mul_of_nonneg_right hp hexp_pos.le
          _ = (2 : ℝ) ^ (21 / 2 : ℝ) * (τ ^ (21 / 2 : ℝ) * Real.exp (-τ ^ 2)) := by ring
          _ ≤ 2 ^ 11 * (Nat.factorial 6 : ℝ) :=
              mul_le_mul hp_fac hexp (by positivity) (by positivity)
          _ ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) := h2fac
      calc (1 + τ) ^ (21 / 2 : ℝ)
          = ((1 + τ) ^ (21 / 2 : ℝ) * Real.exp (-τ ^ 2)) * Real.exp (τ ^ 2) := by
              rw [mul_assoc, ← Real.exp_add]; simp
        _ ≤ 2 ^ 10 * (Nat.factorial 7 : ℝ) * Real.exp (τ ^ 2) :=
              mul_le_mul_of_nonneg_right hmul (Real.exp_pos _).le
  have hsqrt_div : Real.sqrt (τ / (1 + τ ^ 3)) = Real.sqrt τ / Real.sqrt (1 + τ ^ 3) :=
    Real.sqrt_div hτ.le _
  have hnum_eq : (1 + τ ^ (-2 : ℝ)) * τ ^ (5 / 2 : ℝ) * (1 + τ) ^ (7 : ℝ) * Real.exp (-τ ^ 2) /
      Real.sqrt (τ / (1 + τ ^ 3)) =
      ((1 + τ ^ (-2 : ℝ)) * τ ^ (5 / 2 : ℝ) / Real.sqrt τ) *
        ((1 + τ) ^ (7 : ℝ) * Real.sqrt (1 + τ ^ 3)) * Real.exp (-τ ^ 2) := by
    rw [hsqrt_div, div_div_eq_mul_div]; ring
  rw [hnum_eq, hτ_comb]
  have h1 : (1 + τ ^ (2 : ℝ)) * ((1 + τ) ^ (7 : ℝ) * Real.sqrt (1 + τ ^ 3)) ≤
      (1 + τ) ^ (21 / 2 : ℝ) := by
    calc (1 + τ ^ (2 : ℝ)) * ((1 + τ) ^ (7 : ℝ) * Real.sqrt (1 + τ ^ 3))
        ≤ (1 + τ) ^ (2 : ℝ) * ((1 + τ) ^ (7 : ℝ) * (1 + τ) ^ (3 / 2 : ℝ)) := by gcongr
      _ = (1 + τ) ^ (21 / 2 : ℝ) := by rw [← hcomb]; ring
  calc (1 + τ ^ (2 : ℝ)) * ((1 + τ) ^ (7 : ℝ) * Real.sqrt (1 + τ ^ 3)) * Real.exp (-τ ^ 2)
      ≤ (1 + τ) ^ (21 / 2 : ℝ) * Real.exp (-τ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ ≤ (2 ^ 10 * (Nat.factorial 7 : ℝ) * Real.exp (τ ^ 2)) * Real.exp (-τ ^ 2) :=
        mul_le_mul_of_nonneg_right hpow11 (Real.exp_pos _).le
    _ = 2 ^ 10 * (Nat.factorial 7 : ℝ) := by
        rw [mul_assoc, ← Real.exp_add]; simp

/-- Top-down dyadic sum for block bounds `G * s^(1/2)` on `[a, b]` (`0 < a ≤ b`). -/
private lemma dyadic_sum_rpow_half_le {a b G : ℝ} (ha : 0 < a) (hab : a ≤ b) (hG : 0 ≤ G)
    (F : ℝ → ℂ) (hF_int : IntervalIntegrable F volume a b)
    (hblock : ∀ s u v, 0 < s → a ≤ u → u ≤ v → v ≤ b → s ≤ u → v ≤ 2 * s →
      ‖∫ τ in u..v, F τ‖ ≤ G * s ^ (1 / 2 : ℝ)) :
    ‖∫ τ in a..b, F τ‖ ≤ 4 * G * b ^ (1 / 2 : ℝ) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) one_lt_two
  have hbn : b ≤ (2 : ℝ) ^ n * a := by
    have h1 := (div_le_iff₀ ha).mp hn.le
    simpa [mul_comm] using h1
  clear hn
  suffices h : ∀ (m : ℕ) (b' : ℝ), a ≤ b' → b' ≤ (2 : ℝ) ^ m * a → b' ≤ b →
      ‖∫ τ in a..b', F τ‖ ≤ 4 * G * b' ^ (1 / 2 : ℝ) from
    h n b hab hbn le_rfl
  intro m
  induction m with
  | zero =>
    intro b' hab' hb'_le _
    rw [pow_zero, one_mul] at hb'_le
    have : a = b' := le_antisymm hab' hb'_le
    subst this
    simp only [intervalIntegral.integral_same, norm_zero]
    have : 0 ≤ a ^ (1 / 2 : ℝ) := Real.rpow_nonneg ha.le _
    positivity
  | succ m ih =>
    intro b' hab' hb'_le hb'_b
    have hb'_pos : 0 < b' := lt_of_lt_of_le ha hab'
    rcases le_or_gt b' (2 * a) with hb'2a | h2ab'
    · have h1 := hblock a a b' ha le_rfl hab' hb'_b le_rfl hb'2a
      have hpow : a ^ (1 / 2 : ℝ) ≤ b' ^ (1 / 2 : ℝ) := Real.rpow_le_rpow ha.le hab' (by norm_num)
      have : G * a ^ (1 / 2 : ℝ) ≤ 4 * G * b' ^ (1 / 2 : ℝ) := by
        nlinarith [Real.rpow_nonneg ha.le (1 / 2 : ℝ), Real.rpow_nonneg hb'_pos.le (1 / 2 : ℝ)]
      exact h1.trans this
    · set mid := b' / 2 with hmid_def
      have hamid : a ≤ mid := by linarith only [h2ab', hmid_def]
      have hmidb' : mid ≤ b' := by linarith only [hb'_pos, hmid_def]
      have hmid_pos : 0 < mid := lt_of_lt_of_le ha hamid
      have hmid_le : mid ≤ (2 : ℝ) ^ m * a := by
        have hpow : (2 : ℝ) ^ (m + 1) * a = 2 * ((2 : ℝ) ^ m * a) := by ring
        linarith only [hb'_le, hpow, hmid_def]
      have hI1 : IntervalIntegrable F volume a mid :=
        hF_int.mono_set (by
          rw [uIcc_of_le hamid, uIcc_of_le hab]
          exact Icc_subset_Icc le_rfl (hmidb'.trans hb'_b))
      have hI2 : IntervalIntegrable F volume mid b' :=
        hF_int.mono_set (by
          rw [uIcc_of_le hmidb', uIcc_of_le hab]
          exact Icc_subset_Icc hamid hb'_b)
      have hsplit : ∫ τ in a..b', F τ = (∫ τ in a..mid, F τ) + ∫ τ in mid..b', F τ :=
        (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
      have ih1 := ih mid hamid hmid_le (hmidb'.trans hb'_b)
      have hbl := hblock mid mid b' hmid_pos hamid hmidb' hb'_b le_rfl (by linarith only [hmid_def])
      have hmid_pow : mid ^ (1 / 2 : ℝ) = (1 / Real.sqrt 2) * b' ^ (1 / 2 : ℝ) := by
        rw [hmid_def, div_eq_mul_inv, Real.mul_rpow hb'_pos.le (by positivity),
          Real.inv_rpow zero_le_two, Real.sqrt_eq_rpow]
        ring
      have hcoeff : 5 * (1 / Real.sqrt 2) ≤ 4 := by
        have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 zero_lt_two
        rw [mul_one_div, div_le_iff₀ hs2]
        nlinarith [Real.sq_sqrt zero_le_two, mul_nonneg (sub_nonneg.2 hs2.le) (sub_nonneg.2 hs2.le)]
      have hbr_nn : 0 ≤ b' ^ (1 / 2 : ℝ) := Real.rpow_nonneg hb'_pos.le _
      calc ‖∫ τ in a..b', F τ‖
          ≤ ‖∫ τ in a..mid, F τ‖ + ‖∫ τ in mid..b', F τ‖ := by rw [hsplit]; exact norm_add_le _ _
        _ ≤ 4 * G * mid ^ (1 / 2 : ℝ) + G * mid ^ (1 / 2 : ℝ) := add_le_add ih1 hbl
        _ = (5 * (1 / Real.sqrt 2)) * (G * b' ^ (1 / 2 : ℝ)) := by rw [hmid_pow]; ring
        _ ≤ 4 * (G * b' ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hG hbr_nn)
        _ = 4 * G * b' ^ (1 / 2 : ℝ) := by ring

/-- Bottom-up dyadic sum for block bounds `G * s^(-3/2)` on `[a, b]` (`0 < a ≤ b`). -/
private lemma dyadic_sum_rpow_neg_three_halves_le {a b G : ℝ} (ha : 0 < a) (hab : a ≤ b) (hG : 0 ≤ G)
    (F : ℝ → ℂ) (hF_int : IntervalIntegrable F volume a b)
    (hblock : ∀ s u v, 0 < s → a ≤ u → u ≤ v → v ≤ b → s ≤ u → v ≤ 2 * s →
      ‖∫ τ in u..v, F τ‖ ≤ G * s ^ (-(3 / 2 : ℝ))) :
    ‖∫ τ in a..b, F τ‖ ≤ 2 * G * a ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (b / a) one_lt_two
  have hbn : b ≤ (2 : ℝ) ^ n * a := by
    have h1 := (div_le_iff₀ ha).mp hn.le
    simpa [mul_comm] using h1
  clear hn
  suffices h : ∀ (m : ℕ) (a' : ℝ), a ≤ a' → a' ≤ b → b ≤ (2 : ℝ) ^ m * a' →
      ‖∫ τ in a'..b, F τ‖ ≤ 2 * G * a' ^ (-(3 / 2 : ℝ)) from
    h n a le_rfl hab hbn
  intro m
  induction m with
  | zero =>
    intro a' haa' ha'b hb_le
    rw [pow_zero, one_mul] at hb_le
    have : a' = b := le_antisymm ha'b hb_le
    subst this
    simp only [intervalIntegral.integral_same, norm_zero]
    have ha'_pos : 0 < a' := lt_of_lt_of_le ha haa'
    have : 0 ≤ a' ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg ha'_pos.le _
    positivity
  | succ m ih =>
    intro a' haa' ha'b hb_le
    have ha'_pos : 0 < a' := lt_of_lt_of_le ha haa'
    rcases le_or_gt b (2 * a') with hb2a | h2ab
    · have h1 := hblock a' a' b ha'_pos haa' ha'b le_rfl le_rfl hb2a
      have : 0 ≤ a' ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg ha'_pos.le _
      linarith [mul_nonneg hG this]
    · set mid := 2 * a' with hmid_def
      have hamid : a' ≤ mid := by linarith only [ha'_pos]
      have hmid_pos : 0 < mid := by positivity
      have hmid_le : b ≤ (2 : ℝ) ^ m * mid := by
        have hpow : (2 : ℝ) ^ (m + 1) * a' = (2 : ℝ) ^ m * (2 * a') := by ring
        linarith only [hb_le, hpow, hmid_def]
      have hI1 : IntervalIntegrable F volume a' mid :=
        hF_int.mono_set (by
          rw [uIcc_of_le hamid, uIcc_of_le hab]
          exact Icc_subset_Icc haa' h2ab.le)
      have hI2 : IntervalIntegrable F volume mid b :=
        hF_int.mono_set (by
          rw [uIcc_of_le h2ab.le, uIcc_of_le hab]
          exact Icc_subset_Icc (haa'.trans hamid) le_rfl)
      have hsplit : ∫ τ in a'..b, F τ = (∫ τ in a'..mid, F τ) + ∫ τ in mid..b, F τ :=
        (intervalIntegral.integral_add_adjacent_intervals hI1 hI2).symm
      have hbl := hblock a' a' mid ha'_pos haa' hamid h2ab.le le_rfl le_rfl
      have ih2 := ih mid (haa'.trans hamid) h2ab.le hmid_le
      have hmid_pow : mid ^ (-(3 / 2 : ℝ)) = (2 : ℝ) ^ (-(3 / 2 : ℝ)) * a' ^ (-(3 / 2 : ℝ)) := by
        rw [hmid_def, Real.mul_rpow zero_le_two ha'_pos.le]
      have h2r : (2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 := by
        have h1 : (2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
          calc (2 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ))
              = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by norm_num
            _ = (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by rw [← Real.rpow_add zero_lt_two]; norm_num
        rw [h1]
        exact Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by norm_num)
      have hap_nn : 0 ≤ a' ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg ha'_pos.le _
      have hGn : 0 ≤ G * a' ^ (-(3 / 2 : ℝ)) := mul_nonneg hG hap_nn
      calc ‖∫ τ in a'..b, F τ‖
          ≤ ‖∫ τ in a'..mid, F τ‖ + ‖∫ τ in mid..b, F τ‖ := by rw [hsplit]; exact norm_add_le _ _
        _ ≤ G * a' ^ (-(3 / 2 : ℝ)) + 2 * G * mid ^ (-(3 / 2 : ℝ)) := add_le_add hbl ih2
        _ = (1 + 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ))) * (G * a' ^ (-(3 / 2 : ℝ))) := by
            rw [hmid_pow]; ring
        _ ≤ (1 + 1) * (G * a' ^ (-(3 / 2 : ℝ))) := mul_le_mul_of_nonneg_right (by linarith [h2r]) hGn
        _ = 2 * G * a' ^ (-(3 / 2 : ℝ)) := by ring

private lemma one_sub_tebCutoff_eVariationOn_le {δ a b : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hab : a ≤ b) :
    eVariationOn (fun τ : ℝ => ((1 - tebCutoff δ τ : ℝ) : ℂ)) (Icc a b) ≤ ENNReal.ofReal 1 := by
  rw [eVariationOn_ofReal (fun τ => 1 - tebCutoff δ τ)]
  have hneg : eVariationOn (fun τ => 1 - tebCutoff δ τ) (Icc a b) =
      eVariationOn (fun τ => -(1 - tebCutoff δ τ)) (Icc a b) := by
    simp only [eVariationOn, edist_neg_neg]
  rw [hneg]
  have hm : MonotoneOn (fun τ => -(1 - tebCutoff δ τ)) (Icc a b) := fun x hx y hy hxy => by
    have h1 := tebCutoff_monotoneOn_Ici δ hδ (ha.trans hx.1) (ha.trans hy.1) hxy
    linarith
  have hev := hm.eVariationOn_eq (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  rw [inter_self] at hev
  rw [hev]
  exact ENNReal.ofReal_le_ofReal (by linarith [tebCutoff_nonneg δ a, tebCutoff_le_one δ b])

private lemma cos_pi_re_abs_lt_one {σ₀ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    |Real.cos (π * σ₀)| < 1 := by
  have hpiσ_pos : 0 < π * σ₀ := mul_pos Real.pi_pos h0
  have hpiσ_le : π * σ₀ ≤ π := mul_le_of_le_one_right Real.pi_pos.le h1.le
  have hpiσ_lt : π * σ₀ < π := mul_lt_of_lt_one_right Real.pi_pos h1
  have hlt : Real.cos (π * σ₀) < Real.cos 0 :=
    Real.strictAntiOn_cos ⟨le_rfl, Real.pi_pos.le⟩ ⟨hpiσ_pos.le, hpiσ_le⟩ hpiσ_pos
  have hgt : Real.cos π < Real.cos (π * σ₀) :=
    Real.strictAntiOn_cos ⟨hpiσ_pos.le, hpiσ_le⟩ ⟨Real.pi_pos.le, le_rfl⟩ hpiσ_lt
  rw [Real.cos_zero] at hlt
  rw [Real.cos_pi] at hgt
  exact abs_lt.2 ⟨hgt, hlt⟩

private lemma stripPoissonQ_hasDerivAt' {σ₀ η₀ ε τ : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    HasDerivAt (stripPoissonQ σ₀ η₀ ε)
      (-π * Real.sinh (π * (τ - η₀)) / (Real.cosh (π * (τ - η₀)) - Real.cos (π * σ₀)) *
          stripPoissonP σ₀ (τ - η₀) +
        ε * (-π * Real.sinh (π * (τ + η₀)) / (Real.cosh (π * (τ + η₀)) + Real.cos (π * σ₀)) *
          stripPoissonP1 σ₀ (τ + η₀))) τ := by
  have hcos := abs_lt.1 (cos_pi_re_abs_lt_one h0 h1)
  have hd_p : ∀ s : ℝ, HasDerivAt (stripPoissonP σ₀)
      (-π * Real.sinh (π * s) / (Real.cosh (π * s) - Real.cos (π * σ₀)) * stripPoissonP σ₀ s) s := by
    intro s
    have hden : Real.cosh (π * s) - Real.cos (π * σ₀) ≠ 0 := by
      have := Real.one_le_cosh (π * s); linarith [hcos.2]
    have hinner : HasDerivAt (fun x => Real.cosh (π * x) - Real.cos (π * σ₀))
        (π * Real.sinh (π * s)) s := by
      have hmul : HasDerivAt (fun x : ℝ => π * x) π s := by
        simpa using (hasDerivAt_id s).const_mul π
      have hc := (Real.hasDerivAt_cosh (π * s)).comp s hmul
      simpa [mul_comm] using hc.sub_const (Real.cos (π * σ₀))
    have hinv := (hasDerivAt_const s ((1 / 2 : ℝ) * Real.sin (π * σ₀))).div hinner hden
    refine hinv.congr_deriv ?_
    unfold stripPoissonP; field_simp [hden]; ring
  have hd_p1 : ∀ s : ℝ, HasDerivAt (stripPoissonP1 σ₀)
      (-π * Real.sinh (π * s) / (Real.cosh (π * s) + Real.cos (π * σ₀)) * stripPoissonP1 σ₀ s) s := by
    intro s
    have hden : Real.cosh (π * s) + Real.cos (π * σ₀) ≠ 0 := by
      have := Real.one_le_cosh (π * s); linarith [hcos.1]
    have hinner : HasDerivAt (fun x => Real.cosh (π * x) + Real.cos (π * σ₀))
        (π * Real.sinh (π * s)) s := by
      have hmul : HasDerivAt (fun x : ℝ => π * x) π s := by
        simpa using (hasDerivAt_id s).const_mul π
      have hc := (Real.hasDerivAt_cosh (π * s)).comp s hmul
      simpa [mul_comm] using hc.add_const (Real.cos (π * σ₀))
    have hinv := (hasDerivAt_const s ((1 / 2 : ℝ) * Real.sin (π * σ₀))).div hinner hden
    refine hinv.congr_deriv ?_
    unfold stripPoissonP1; field_simp [hden]; ring
  have hp := ((hd_p (τ - η₀)).comp τ ((hasDerivAt_id τ).sub_const η₀)).congr_deriv (mul_one _)
  have hp1 := (((hd_p1 (τ + η₀)).comp τ ((hasDerivAt_id τ).add_const η₀)).congr_deriv (mul_one _)).const_mul ε
  unfold stripPoissonQ
  exact (hp.add hp1).congr_deriv (by ring)

private lemma stripPoissonQ_continuous {σ₀ η₀ ε : ℝ} (h0 : 0 < σ₀) (h1 : σ₀ < 1) :
    Continuous (stripPoissonQ σ₀ η₀ ε) :=
  continuous_iff_continuousAt.2 fun τ => (stripPoissonQ_hasDerivAt' h0 h1 (τ := τ)).continuousAt

private lemma stripPoissonQ_block_bv_le {σ₀ η₀ ε sgn s : ℝ} (h0 : 0 < σ₀) (h4 : σ₀ ≤ 0.04)
    (hε : |ε| ≤ 1) (hsgn : |sgn| = 1) (hs : 2 * √(σ₀ ^ 2 + η₀ ^ 2) ≤ s) :
    let qJ := 4 * σ₀ * (1 + s ^ (-2 : ℝ)) * Real.exp (-π * s / 4)
    (∀ τ ∈ Icc s (2 * s), ‖(stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ qJ) ∧
    eVariationOn (fun τ : ℝ => (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)) (Icc s (2 * s)) ≤
      ENNReal.ofReal (2 * π * (s + 2) * qJ) := by
  intro qJ
  have h1 : σ₀ < 1 := by linarith
  have hs_pos : 0 < s := lt_of_lt_of_le (by positivity) hs
  obtain ⟨hq_cal, hderiv_int⟩ := integral_abs_deriv_stripPoissonQ_block_le h0 h4 hε hs (η₀ := η₀)
  have hnorm : ∀ τ ∈ Icc s (2 * s), ‖(stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ qJ := by
    intro τ hτ
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (stripPoissonQ_abs_le h0 h1 η₀ hε (sgn * τ)).trans ?_
    refine hq_cal (sgn * τ) ?_ ?_ <;>
      rw [abs_mul, hsgn, one_mul, abs_of_pos (lt_of_lt_of_le hs_pos hτ.1)]
    · exact hτ.1
    · exact hτ.2
  refine ⟨hnorm, ?_⟩
  rw [eVariationOn_ofReal (fun τ => stripPoissonQ σ₀ η₀ ε (sgn * τ))]
  have hcos := abs_lt.1 (cos_pi_re_abs_lt_one h0 h1)
  have hderiv_cont : Continuous (deriv (stripPoissonQ σ₀ η₀ ε)) := by
    have heq : deriv (stripPoissonQ σ₀ η₀ ε) = fun t : ℝ =>
        -π * Real.sinh (π * (t - η₀)) / (Real.cosh (π * (t - η₀)) - Real.cos (π * σ₀)) *
            stripPoissonP σ₀ (t - η₀) +
          ε * (-π * Real.sinh (π * (t + η₀)) / (Real.cosh (π * (t + η₀)) + Real.cos (π * σ₀)) *
            stripPoissonP1 σ₀ (t + η₀)) := by
      ext t; exact (stripPoissonQ_hasDerivAt' h0 h1 (τ := t)).deriv
    rw [heq]
    have hdp : ∀ t : ℝ, Real.cosh (π * (t - η₀)) - Real.cos (π * σ₀) ≠ 0 := fun t => by
      have := Real.one_le_cosh (π * (t - η₀)); linarith [hcos.2]
    have hdp1 : ∀ t : ℝ, Real.cosh (π * (t + η₀)) + Real.cos (π * σ₀) ≠ 0 := fun t => by
      have := Real.one_le_cosh (π * (t + η₀)); linarith [hcos.1]
    unfold stripPoissonP stripPoissonP1
    fun_prop (disch := first | exact hdp _ | exact hdp1 _)
  have hsgn_cases : sgn = 1 ∨ sgn = -1 := abs_eq zero_le_one |>.mp hsgn
  have hd_Q : ∀ t : ℝ, HasDerivAt (stripPoissonQ σ₀ η₀ ε) (deriv (stripPoissonQ σ₀ η₀ ε) t) t := by
    intro t
    have hd := stripPoissonQ_hasDerivAt' h0 h1 (η₀ := η₀) (ε := ε) (τ := t)
    rwa [← hd.deriv] at hd
  have hint_pos : IntervalIntegrable (fun τ => sgn * deriv (stripPoissonQ σ₀ η₀ ε) (sgn * τ)) volume s (2 * s) :=
    (continuous_const.mul (hderiv_cont.comp (continuous_const.mul continuous_id))).intervalIntegrable s (2 * s)
  have hev := eVariationOn_le_integral_abs_deriv (by linarith : s ≤ 2 * s)
    (fun x _ => by
      have hx := (hd_Q (sgn * x)).comp x (by simpa using (hasDerivAt_id x).const_mul sgn)
      refine hx.congr_deriv ?_; ring)
    hint_pos
  have hint_eq : ∫ t in s..(2 * s), |sgn * deriv (stripPoissonQ σ₀ η₀ ε) (sgn * t)| ≤
      2 * π * (s + 2) * qJ := by
    have h1eq : (fun t => |sgn * deriv (stripPoissonQ σ₀ η₀ ε) (sgn * t)|) =
        fun t => |deriv (stripPoissonQ σ₀ η₀ ε) (sgn * t)| := by
      ext t; rw [abs_mul, hsgn, one_mul]
    rw [h1eq]
    have hnn1 : 0 ≤ ∫ τ in s..(2 * s), |deriv (stripPoissonQ σ₀ η₀ ε) τ| :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
    have hnn2 : 0 ≤ ∫ τ in (-2 * s)..(-s), |deriv (stripPoissonQ σ₀ η₀ ε) τ| :=
      intervalIntegral.integral_nonneg (by linarith) fun _ _ => abs_nonneg _
    rcases hsgn_cases with rfl | rfl
    · simp only [one_mul]; linarith
    · have heq : (fun t : ℝ => |deriv (stripPoissonQ σ₀ η₀ ε) (-1 * t)|) =
          fun t : ℝ => |deriv (stripPoissonQ σ₀ η₀ ε) (-t)| := by ext t; simp
      rw [heq, intervalIntegral.integral_comp_neg (a := s) (b := 2 * s)
        (fun τ => |deriv (stripPoissonQ σ₀ η₀ ε) τ|), show -(2 * s) = -2 * s by ring]
      linarith
  exact hev.trans (ENNReal.ofReal_le_ofReal hint_eq)

/-- Block BV bound for `τ ↦ tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ)` on `[s, 2s]`. -/
private lemma tebAmp0_mul_edgeAmp_block_bv_le {c sgn s : ℝ} (hc : 3e6 ≤ c) (hsgn : |sgn| = 1)
    (hs : 0 < s) :
    let Mamp := 8704 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2)
    BoundedVariationOn (fun τ => tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ)) (Icc s (2 * s)) ∧
    eVariationOn (fun τ => tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ)) (Icc s (2 * s)) ≤
      ENNReal.ofReal Mamp ∧
    (∀ τ ∈ Icc s (2 * s),
      ‖tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ)‖ +
        (eVariationOn (fun t => tebAmp0 c (sgn * t) * hankelEdgeAmp c (sgn * t)) (Icc s (2 * s))).toReal ≤
        Mamp) := by
  intro Mamp
  have hc0 : 0 < c := by linarith
  have hs_le : s ≤ 2 * s := by linarith
  obtain ⟨hamp_all, hamp_bv⟩ := tebAmp0_block_bv_le hc0.le hsgn hs
  set B := 272 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (9 / 2 : ℝ) * Real.exp (-s ^ 2)
  have hB_nn : 0 ≤ B := by dsimp [B]; positivity
  have hf1_bd : ∀ τ ∈ Icc s (2 * s), ‖tebAmp0 c (sgn * τ)‖ ≤ B := fun τ hτ => by
    have := hamp_all τ hτ
    have htv_nn : 0 ≤ (eVariationOn (fun t => tebAmp0 c (sgn * t)) (Icc s (2 * s))).toReal :=
      ENNReal.toReal_nonneg
    dsimp [B]; linarith
  have hf1_bv : eVariationOn (fun τ => tebAmp0 c (sgn * τ)) (Icc s (2 * s)) ≤ ENNReal.ofReal B := by
    have hτs := hamp_all s ⟨le_rfl, hs_le⟩
    have htv_le : (eVariationOn (fun t => tebAmp0 c (sgn * t)) (Icc s (2 * s))).toReal ≤ B := by
      have := norm_nonneg (tebAmp0 c (sgn * s))
      dsimp [B]; linarith
    exact (ENNReal.ofReal_toReal hamp_bv).symm ▸ ENNReal.ofReal_le_ofReal htv_le
  set Ka := (8 : ℝ) * (1 + s) ^ (1 / 2 : ℝ)
  have hKa_nn : 0 ≤ Ka := by dsimp [Ka]; positivity
  have ha0_both : ∀ τ ∈ Icc s (2 * s),
      ‖hankelEdgeAmp c (sgn * τ)‖ ≤ Ka ∧ ‖(sgn : ℂ) * hankelEdgeAmp' c (sgn * τ)‖ ≤ Ka := by
    intro τ hτ
    have habs : |sgn * τ| ≤ 2 * s := by
      rw [abs_mul, hsgn, one_mul, abs_of_pos (lt_of_lt_of_le hs hτ.1)]
      exact hτ.2
    have hle : (1 + |sgn * τ|) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) * (1 + s) ^ (1 / 2 : ℝ) := by
      rw [← Real.mul_rpow zero_le_two (by linarith)]
      exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
    have hbd := hankelEdgeAmp_bound (by linarith : 1 ≤ c) (sgn * τ)
    have h2_le : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 :=
      (Real.rpow_le_rpow_of_exponent_le one_le_two (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq (Real.rpow_one 2)
    have hK_ub : 4 * (1 + |sgn * τ|) ^ (1 / 2 : ℝ) ≤ Ka := by
      dsimp [Ka]
      calc 4 * (1 + |sgn * τ|) ^ (1 / 2 : ℝ) ≤ 4 * ((2 : ℝ) ^ (1 / 2 : ℝ) * (1 + s) ^ (1 / 2 : ℝ)) := by
            gcongr
        _ ≤ 4 * (2 * (1 + s) ^ (1 / 2 : ℝ)) := by gcongr
        _ = 8 * (1 + s) ^ (1 / 2 : ℝ) := by ring
    exact ⟨(by linarith [norm_nonneg (hankelEdgeAmp' c (sgn * τ))]), by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hsgn, one_mul]
      linarith [norm_nonneg (hankelEdgeAmp c (sgn * τ))]⟩
  have hf2_bd : ∀ τ ∈ Icc s (2 * s), ‖hankelEdgeAmp c (sgn * τ)‖ ≤ Ka := fun τ hτ => (ha0_both τ hτ).1
  have hf2_deriv : ∀ τ ∈ Icc s (2 * s),
      HasDerivAt (fun t => hankelEdgeAmp c (sgn * t)) ((sgn : ℂ) * hankelEdgeAmp' c (sgn * τ)) τ := by
    intro τ _
    have hsgn_d : HasDerivAt (fun t : ℝ => (sgn : ℝ) * t) sgn τ := by
      simpa using (hasDerivAt_id τ).const_mul sgn
    have hc_d := (hankelEdgeAmp_hasDerivAt hc0 (sgn * τ)).scomp τ hsgn_d
    refine hc_d.congr_deriv ?_; simp [Complex.real_smul]
  have hf2_bv : eVariationOn (fun t => hankelEdgeAmp c (sgn * t)) (Icc s (2 * s)) ≤
      ENNReal.ofReal (Ka * (2 * s - s)) :=
    eVariationOn_le_of_hasDerivAt_le hs_le hKa_nn hf2_deriv (fun τ hτ => (ha0_both τ hτ).2)
  have hf2_bv' : eVariationOn (fun t => hankelEdgeAmp c (sgn * t)) (Icc s (2 * s)) ≤
      ENNReal.ofReal (Ka * (1 + s)) :=
    hf2_bv.trans (ENNReal.ofReal_le_ofReal (by
      have : 2 * s - s ≤ 1 + s := by linarith
      exact mul_le_mul_of_nonneg_left this hKa_nn))
  have hf2_bd' : ∀ τ ∈ Icc s (2 * s), ‖hankelEdgeAmp c (sgn * τ)‖ ≤ Ka * (1 + s) := fun τ hτ =>
    (hf2_bd τ hτ).trans (le_mul_of_one_le_right hKa_nn (by linarith))
  have hmul := bv_norm_add_tv_mul hB_nn (by positivity) hB_nn (by positivity) hf1_bd hf2_bd' hf1_bv hf2_bv'
  have hexp_M : Mamp = (B + B) * (Ka * (1 + s) + Ka * (1 + s)) := by
    have hpow : (1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ (1 / 2 : ℝ) * (1 + s) = (1 + s) ^ (6 : ℝ) := by
      have h1 : (1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ (1 / 2 : ℝ) = (1 + s) ^ (5 : ℝ) := by
        rw [← Real.rpow_add (by linarith)]; norm_num
      have h2 : (1 + s) ^ (5 : ℝ) * (1 + s) = (1 + s) ^ (6 : ℝ) := by
        calc (1 + s) ^ (5 : ℝ) * (1 + s)
            = (1 + s) ^ (5 : ℝ) * (1 + s) ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = (1 + s) ^ (6 : ℝ) := by rw [← Real.rpow_add (by linarith)]; norm_num
      rw [h1, h2]
    dsimp [Mamp, B, Ka]
    calc 8704 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2)
        = 8704 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) *
            ((1 + s) ^ (9 / 2 : ℝ) * (1 + s) ^ (1 / 2 : ℝ) * (1 + s)) * Real.exp (-s ^ 2) := by
            rw [hpow]
      _ = _ := by ring
  refine ⟨hmul.1, hmul.2.1.trans (ENNReal.ofReal_le_ofReal (by
    rw [hexp_M]; nlinarith [mul_nonneg hB_nn (by positivity : 0 ≤ Ka * (1 + s))])), ?_⟩
  intro τ hτ
  exact (hmul.2.2 τ hτ).trans_eq hexp_M.symm

/-- Common Hankel edge phase setup (`van_der_corput_{first,second}_comp` with `w = id`) for `sgn = ±1`. -/
private lemma hankel_phase_bounds {sgn ξ : ℝ} (hsgn : sgn = 1 ∨ sgn = -1) (_hξ : 0 < ξ) :
    let φ : ℝ → ℝ := fun y => -sgn * edgePhi (hankelBandMu ξ) y
    let φ' : ℝ → ℝ := fun y => sgn * (hankelEdgeM y - hankelBandMu ξ)
    let φ'' : ℝ → ℝ := fun y => sgn * hankelEdgeM' y
    (∀ y ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' y) y) ∧
    (∀ y ∈ Ioi (0 : ℝ), HasDerivAt φ' (φ'' y) y) ∧
    (MonotoneOn φ' (Ioi 0) ∨ AntitoneOn φ' (Ioi 0)) ∧
    (∀ τ, 2 * hankelBandTau0 ξ < τ → (1 / 32 : ℝ) * min (τ ^ 2) 1 ≤ |φ' τ|) ∧
    (∀ τ, 0 < τ → τ < hankelBandTau0 ξ / 2 →
      (1 / 32 : ℝ) * min (hankelBandTau0 ξ ^ 2) 1 ≤ |φ' τ|) ∧
    (0 < hankelBandTau0 ξ → ∀ τ, hankelBandTau0 ξ / 2 ≤ τ → τ ≤ 2 * hankelBandTau0 ξ →
      (1 / 32 : ℝ) * hankelBandTau0 ξ / (1 + hankelBandTau0 ξ ^ 3) ≤ |φ'' τ|) := by
  intro φ φ' φ''
  have hsgn_abs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hφ : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' y) y := fun y hy => by
    have hd := (hankelEdgePhi_hasDerivAt (hankelBandMu ξ) hy).const_mul (-sgn)
    refine hd.congr_deriv ?_; simp [φ']; ring
  have hφ' : ∀ y ∈ Ioi (0 : ℝ), HasDerivAt φ' (φ'' y) y := fun y hy => by
    have hd := ((hankelEdgeM_hasDerivAt hy).sub_const (hankelBandMu ξ)).const_mul sgn
    exact hd.congr_deriv (by simp [φ''])
  have hφ'_mono : MonotoneOn φ' (Ioi 0) ∨ AntitoneOn φ' (Ioi 0) := by
    rcases hsgn with rfl | rfl
    · left
      intro a ha b hb hab
      have hm := hankelEdgeM_strictMonoOn.monotoneOn ha.le hb.le hab
      dsimp [φ']; linarith
    · right
      intro a ha b hb hab
      have hm := hankelEdgeM_strictMonoOn.monotoneOn ha.le hb.le hab
      dsimp [φ']; linarith
  have h_abs_φ' : ∀ τ > 0, |φ' τ| = |hankelEdgeM τ - hankelBandMu ξ| := fun τ _ => by
    dsimp [φ']; rw [abs_mul, hsgn_abs, one_mul]
  have h_upper : ∀ τ, 2 * hankelBandTau0 ξ < τ → (1 / 32 : ℝ) * min (τ ^ 2) 1 ≤ |φ' τ| := by
    intro τ hτ
    have hτ_pos : 0 < τ := lt_of_le_of_lt (mul_nonneg zero_le_two (hankelBandTau0_nonneg ξ)) hτ
    rw [h_abs_φ' τ hτ_pos]
    have hm_step : (3 / 16 : ℝ) * min (τ ^ 2) 1 ≤ hankelEdgeM τ - hankelEdgeM (τ / 2) :=
      hankelEdgeM_step hτ_pos
    have hm_diff : hankelEdgeM τ - hankelEdgeM (τ / 2) ≤ hankelEdgeM τ - hankelBandMu ξ := by
      rcases le_or_gt (hankelBandMu ξ) 0 with hμ | hμ
      · have h0le : hankelEdgeM 0 ≤ hankelEdgeM (τ / 2) :=
          hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith : 0 ≤ τ / 2))
            (by linarith : 0 ≤ τ / 2)
        rw [hankelEdgeM_zero] at h0le; linarith
      · have hm_lt : hankelEdgeM (hankelBandTau0 ξ) ≤ hankelEdgeM (τ / 2) :=
          hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (hankelBandTau0_nonneg ξ))
            (mem_Ici.2 (by linarith : 0 ≤ τ / 2)) (by linarith : hankelBandTau0 ξ ≤ τ / 2)
        rw [hankelBandTau0_root hμ] at hm_lt; linarith
    have hmin_nn : 0 ≤ min (τ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    calc (1 / 32 : ℝ) * min (τ ^ 2) 1 ≤ (3 / 16 : ℝ) * min (τ ^ 2) 1 :=
          mul_le_mul_of_nonneg_right (by norm_num) hmin_nn
      _ ≤ hankelEdgeM τ - hankelBandMu ξ := hm_step.trans hm_diff
      _ ≤ |hankelEdgeM τ - hankelBandMu ξ| := le_abs_self _
  have h_lower : ∀ τ, 0 < τ → τ < hankelBandTau0 ξ / 2 →
      (1 / 32 : ℝ) * min (hankelBandTau0 ξ ^ 2) 1 ≤ |φ' τ| := by
    intro τ hτ hτ_lt
    rw [h_abs_φ' τ hτ]
    have hτ0_pos : 0 < hankelBandTau0 ξ := by linarith
    have hμ_pos : 0 < hankelBandMu ξ := by
      by_contra hle
      have h0 := hankelBandTau0_zero (not_lt.mp hle)
      linarith
    have hm_eq : hankelEdgeM (hankelBandTau0 ξ) = hankelBandMu ξ := hankelBandTau0_root hμ_pos
    have hm_lt : hankelEdgeM τ ≤ hankelEdgeM (hankelBandTau0 ξ / 2) :=
      hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 hτ.le)
        (mem_Ici.2 (by linarith : 0 ≤ hankelBandTau0 ξ / 2)) hτ_lt.le
    have hm_step : (3 / 16 : ℝ) * min (hankelBandTau0 ξ ^ 2) 1 ≤
        hankelEdgeM (hankelBandTau0 ξ) - hankelEdgeM (hankelBandTau0 ξ / 2) :=
      hankelEdgeM_step hτ0_pos
    have hmin_nn : 0 ≤ min (hankelBandTau0 ξ ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
    calc (1 / 32 : ℝ) * min (hankelBandTau0 ξ ^ 2) 1 ≤
          (3 / 16 : ℝ) * min (hankelBandTau0 ξ ^ 2) 1 :=
          mul_le_mul_of_nonneg_right (by norm_num) hmin_nn
      _ ≤ hankelBandMu ξ - hankelEdgeM τ := by linarith
      _ ≤ |hankelEdgeM τ - hankelBandMu ξ| := by rw [abs_sub_comm]; exact le_abs_self _
  have h_mid : 0 < hankelBandTau0 ξ → ∀ τ, hankelBandTau0 ξ / 2 ≤ τ → τ ≤ 2 * hankelBandTau0 ξ →
      (1 / 32 : ℝ) * hankelBandTau0 ξ / (1 + hankelBandTau0 ξ ^ 3) ≤ |φ'' τ| := by
    intro hτ0_pos τ hτ_lo hτ_hi
    have hτ_pos : 0 < τ := lt_of_lt_of_le (half_pos hτ0_pos) hτ_lo
    have hφ''_eq : |φ'' τ| = hankelEdgeM' τ := by
      dsimp [φ'']
      rw [abs_mul, hsgn_abs, one_mul, abs_of_nonneg]
      have := hankelEdgeM_slope hτ_pos
      have h0 : 0 ≤ (1 / 2 : ℝ) * τ / (1 + τ ^ 3) := by positivity
      exact h0.trans this
    rw [hφ''_eq]
    have hslope := hankelEdgeM_slope hτ_pos
    have hden1 : 1 + τ ^ 3 ≤ 8 * (1 + hankelBandTau0 ξ ^ 3) := by
      have hpow : τ ^ 3 ≤ (2 * hankelBandTau0 ξ) ^ 3 := pow_le_pow_left₀ hτ_pos.le hτ_hi 3
      linarith [show (2 * hankelBandTau0 ξ) ^ 3 = 8 * hankelBandTau0 ξ ^ 3 by ring]
    have hden_pos : 0 < 1 + τ ^ 3 := by positivity
    have hfrac : hankelBandTau0 ξ / (16 * (1 + hankelBandTau0 ξ ^ 3)) ≤ τ / (1 + τ ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) hden_pos]
      nlinarith
    calc (1 / 32 : ℝ) * hankelBandTau0 ξ / (1 + hankelBandTau0 ξ ^ 3)
        = (1 / 2 : ℝ) * (hankelBandTau0 ξ / (16 * (1 + hankelBandTau0 ξ ^ 3))) := by
          field_simp; ring
      _ ≤ (1 / 2 : ℝ) * (τ / (1 + τ ^ 3)) := by gcongr
      _ = (1 / 2 : ℝ) * τ / (1 + τ ^ 3) := by ring
      _ ≤ hankelEdgeM' τ := hslope
  exact ⟨hφ, hφ', hφ'_mono, h_upper, h_lower, h_mid⟩

end Helpers

section ChartComparison

/-- At scale `r ∈ (0, R_J]` (`R_J ≤ 10⁻⁴ c^{2/3} + 1`, `c ≥ 3·10⁶`), every `ξ ≤ hankelXi c (-r)`
satisfies `hankelBandTau0 ξ < 2 * rhoR hankelBandParams c r`. -/
private lemma tau0_lt_two_rhoR_of_xi_le {c R_J r ξ : ℝ} (hc : 3e6 ≤ c)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr : 0 < r) (hr_RJ : r ≤ R_J) (hξ : ξ ≤ hankelXi c (-r)) :
    hankelBandTau0 ξ < 2 * rhoR hankelBandParams c r := by
  have hc0 : 0 < c := by linarith
  have hK := langerScale_pos hc0
  have hk := hankelLangerKappa_bounds
  have hk3 := hankelLangerKappa_cube
  have hρ_pos : 0 < 2 * rhoR hankelBandParams c r := by
    show 0 < 2 * (hankelBandParams.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r)
    have := hankelBandParams.hκ_ζ
    positivity
  rcases le_or_gt (hankelBandMu ξ) 0 with hμ0 | hμ0
  · rw [hankelBandTau0_zero hμ0]; exact hρ_pos
  · have hξ0 : 0 < ξ := by
      by_contra hneg
      unfold hankelBandMu at hμ0
      rw [ite_eq_right hneg] at hμ0
      exact lt_irrefl _ hμ0
    have hrA : |-r| ≤ langerRadius c := by
      rw [abs_neg, abs_of_pos hr]
      exact hr_RJ.trans (hRJ_ub.trans (hankelBand_radius_ge_one hc))
    have hwr_bds := hankelXi_w_bounds hc0 hrA (by linarith)
    set wr := Real.pi ^ 2 * hankelXi c (-r) - 1
    have hU := hankelBootU_xi hc0 hrA
    have hyw : (chartY etaC (wr : ℂ)).re = -r / langerScale c := by
      unfold hankelBandU at hU
      have : langerScale c * (chartY etaC (wr : ℂ)).re = -r := hU
      rw [eq_div_iff hK.ne', mul_comm]; exact this
    have hyn : ‖(wr : ℂ)‖ ≤ 1e-3 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwr_bds.1]
      linarith [hwr_bds.2.1]
    have hnormY := norm_chartY_add_le langerEta_etaC hyn
    have hreY : |(chartY etaC (wr : ℂ)).re + wr| ≤ 1.9e-3 * wr := by
      have h1 := (Complex.abs_re_le_norm (chartY etaC (wr : ℂ) + (wr : ℂ))).trans hnormY
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hwr_bds.1] at h1
      simpa using h1
    rw [hyw] at hreY
    rw [neg_div] at hreY
    have hwr_le : wr ≤ 1.002 * r / langerScale c := by
      have h1 := (abs_le.1 hreY).2
      have h2 : 0.9981 * wr ≤ r / langerScale c := by linarith
      rw [le_div_iff₀ hK]
      have h3 := mul_le_mul_of_nonneg_left h2 hK.le
      have : 0.9981 * (wr * langerScale c) ≤ r := by
        calc 0.9981 * (wr * langerScale c) = langerScale c * (0.9981 * wr) := by ring
          _ ≤ langerScale c * (r / langerScale c) := h3
          _ = r := mul_div_cancel₀ r hK.ne'
      nlinarith [hr.le]
    have hμ_eq : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by
      unfold hankelBandMu; rw [ite_eq_left hξ0]
    have hμ_le_wr : hankelBandMu ξ ≤ wr := by
      rw [hμ_eq]
      have h1 : Real.log (Real.pi ^ 2 * ξ) ≤ Real.log (Real.pi ^ 2 * hankelXi c (-r)) :=
        Real.log_le_log (by positivity) (by nlinarith [Real.pi_pos])
      have h2 := Real.log_le_sub_one_of_pos (show 0 < Real.pi ^ 2 * hankelXi c (-r) by linarith [hwr_bds.1])
      exact h1.trans h2
    have hμ_small : hankelBandMu ξ < 3 / 16 := by
      linarith [hμ_le_wr, hwr_bds.2.1]
    set τ₀ := hankelBandTau0 ξ
    have hτ₀_nn : 0 ≤ τ₀ := hankelBandTau0_nonneg ξ
    have hτ₀_sq : τ₀ ^ 2 ≤ 0.01 := by
      have hs := hankelBandTau0_sq_le hμ0.le hμ_small
      linarith [hμ_le_wr, hwr_bds.2.1]
    have hm_root : hankelEdgeM τ₀ = hankelBandMu ξ := hankelBandTau0_root hμ0
    have hmlog := hankelEdgeM_sub_log_mono le_rfl hτ₀_nn
    simp only [hankelEdgeM_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero,
      Real.log_one, sub_zero, hm_root] at hmlog
    have hlog_lb : τ₀ ^ 2 / (1 + τ₀ ^ 2) ≤ Real.log (1 + τ₀ ^ 2) := by
      have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + τ₀ ^ 2 by positivity)
      refine le_trans ?_ h1
      rw [div_le_iff₀ (by positivity)]
      have : (1 - (1 + τ₀ ^ 2)⁻¹) * (1 + τ₀ ^ 2) = τ₀ ^ 2 := by field_simp; ring
      linarith
    have hτ₀_sq_le_μ : τ₀ ^ 2 ≤ 2.025 * hankelBandMu ξ := by
      have h1 : τ₀ ^ 2 / 1.01 ≤ τ₀ ^ 2 / (1 + τ₀ ^ 2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith [hτ₀_sq])
      have h2 : τ₀ ^ 2 / 2.02 ≤ 1 / 2 * Real.log (1 + τ₀ ^ 2) := by
        calc τ₀ ^ 2 / 2.02 = (1 / 2 : ℝ) * (τ₀ ^ 2 / 1.01) := by ring
          _ ≤ (1 / 2 : ℝ) * (τ₀ ^ 2 / (1 + τ₀ ^ 2)) := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ ≤ (1 / 2 : ℝ) * Real.log (1 + τ₀ ^ 2) := mul_le_mul_of_nonneg_left hlog_lb (by norm_num)
      have h3 : τ₀ ^ 2 / 2.02 ≤ hankelBandMu ξ := by linarith
      calc τ₀ ^ 2 = 2.02 * (τ₀ ^ 2 / 2.02) := by ring
        _ ≤ 2.02 * hankelBandMu ξ := mul_le_mul_of_nonneg_left h3 (by norm_num)
        _ ≤ 2.025 * hankelBandMu ξ := mul_le_mul_of_nonneg_right (by norm_num) hμ0.le
    have hτ₀_sq_r : τ₀ ^ 2 ≤ 2.03 * r / langerScale c := by
      have h1 : τ₀ ^ 2 ≤ 2.025 * (1.002 * r / langerScale c) := by
        calc τ₀ ^ 2 ≤ 2.025 * hankelBandMu ξ := hτ₀_sq_le_μ
          _ ≤ 2.025 * wr := by gcongr
          _ ≤ 2.025 * (1.002 * r / langerScale c) := by gcongr
      have h2 : 2.025 * (1.002 * r / langerScale c) ≤ 2.03 * r / langerScale c := by
        calc 2.025 * (1.002 * r / langerScale c) = (2.025 * 1.002) * (r / langerScale c) := by ring
          _ ≤ 2.03 * (r / langerScale c) := mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hr.le hK.le)
          _ = 2.03 * r / langerScale c := by ring
      exact h1.trans h2
    have hsq_lt : τ₀ ^ 2 < (2 * rhoR hankelBandParams c r) ^ 2 := by
      have hρ_eq : 2 * rhoR hankelBandParams c r = 4 * langerKappa * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r := by
        show 2 * (hankelBandParams.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) = _
        have : hankelBandParams.κ_ζ = 2 * langerKappa := rfl
        rw [this]; ring
      have hc23 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = (c ^ (2 / 3 : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_neg hc0.le]; norm_num
      have hρ_sq : (2 * rhoR hankelBandParams c r) ^ 2 =
          16 * langerKappa ^ 3 * (r / langerScale c) := by
        rw [hρ_eq, mul_pow, mul_pow, mul_pow, hc23, Real.sq_sqrt hr.le]
        have hKdef : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
        rw [hKdef]
        have hk0 : langerKappa ≠ 0 := langerKappa_pos.ne'
        have hc23_pos : c ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
        field_simp; ring
      have hpi2 : Real.pi ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
      have hk3_lb : 4.8 < 16 * langerKappa ^ 3 := by
        rw [hk3, show (16 : ℝ) * (3 / Real.pi ^ 2) = 48 / Real.pi ^ 2 by ring, lt_div_iff₀ (by positivity)]
        nlinarith
      have h203 : 2.03 * (r / langerScale c) < 16 * langerKappa ^ 3 * (r / langerScale c) :=
        mul_lt_mul_of_pos_right (by linarith) (div_pos hr hK)
      rw [hρ_sq]
      linarith [show 2.03 * r / langerScale c = 2.03 * (r / langerScale c) by ring]
    by_contra hle
    have := pow_le_pow_left₀ hρ_pos.le (not_lt.1 hle) 2
    linarith

/-- If `1028 * r ≤ R_J` and `hankelBandTau0 ξ < 32 * rhoR`, then `ξ ≤ hankelXi c (-1028 * r)`. -/
private lemma xi_le_1028r_of_tau0_lt {c R_J r ξ : ℝ} (hc : 3e6 ≤ c)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr : 0 < r) (h1028 : 1028 * r ≤ R_J)
    (hτ_lt : hankelBandTau0 ξ < 32 * rhoR hankelBandParams c r) :
    ξ ≤ hankelXi c (-1028 * r) := by
  have hc0 : 0 < c := by linarith
  have hK := langerScale_pos hc0
  have hk := hankelLangerKappa_bounds
  have hk3 := hankelLangerKappa_cube
  have hrA : |-(1028 * r)| ≤ langerRadius c := by
    rw [abs_neg, abs_of_pos (by positivity)]
    exact h1028.trans (hRJ_ub.trans (hankelBand_radius_ge_one hc))
  have hw1_bds := hankelXi_w_bounds hc0 hrA (by linarith)
  set ξ₁ := hankelXi c (-(1028 * r))
  set w₁ := Real.pi ^ 2 * ξ₁ - 1
  have hU := hankelBootU_xi hc0 hrA
  have hyw : (chartY etaC (w₁ : ℂ)).re = -(1028 * r) / langerScale c := by
    unfold hankelBandU at hU
    have h1 : langerScale c * (chartY etaC (w₁ : ℂ)).re = -(1028 * r) := hU
    rw [eq_div_iff hK.ne']; linarith
  have hyn : ‖(w₁ : ℂ)‖ ≤ 1e-3 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw1_bds.1]
    linarith [hw1_bds.2.1]
  have hnormY := norm_chartY_add_le langerEta_etaC hyn
  have hreY : |(chartY etaC (w₁ : ℂ)).re + w₁| ≤ 1.9e-3 * w₁ := by
    have h1 := (Complex.abs_re_le_norm (chartY etaC (w₁ : ℂ) + (w₁ : ℂ))).trans hnormY
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw1_bds.1] at h1
    simpa using h1
  rw [hyw, neg_div] at hreY
  have hw1_ge : 1028 * r / (1.0019 * langerScale c) ≤ w₁ := by
    have h1 := (abs_le.1 hreY).1
    have h2 : (1028 * r) / langerScale c ≤ 1.0019 * w₁ := by linarith
    rw [div_le_iff₀ (by positivity)]
    have h3 := mul_le_mul_of_nonneg_left h2 hK.le
    have : langerScale c * ((1028 * r) / langerScale c) = 1028 * r := mul_div_cancel₀ _ hK.ne'
    linarith
  have hlog_ge : 1025 * r / langerScale c ≤ Real.log (Real.pi ^ 2 * ξ₁) := by
    have hpi_eq : Real.pi ^ 2 * ξ₁ = 1 + w₁ := by simp [w₁]
    rw [hpi_eq]
    have h1w_pos : 0 < 1 + w₁ := by linarith [hw1_bds.1]
    have hlog1 := Real.one_sub_inv_le_log_of_pos h1w_pos
    have hfrac : w₁ / (1 + w₁) = 1 - (1 + w₁)⁻¹ := by field_simp [h1w_pos.ne']; ring
    have h2 : w₁ / 1.0005 ≤ w₁ / (1 + w₁) :=
      div_le_div_of_nonneg_left hw1_bds.1 h1w_pos (by linarith [hw1_bds.2.1])
    have h3 : 1025 * r / langerScale c ≤ (1028 * r / (1.0019 * langerScale c)) / 1.0005 := by
      calc 1025 * r / langerScale c = 1025 * (r / langerScale c) := by ring
        _ ≤ (1028 / (1.0019 * 1.0005)) * (r / langerScale c) :=
            mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hr.le hK.le)
        _ = (1028 * r / (1.0019 * langerScale c)) / 1.0005 := by ring
    have h4 : (1028 * r / (1.0019 * langerScale c)) / 1.0005 ≤ w₁ / 1.0005 :=
      div_le_div_of_nonneg_right hw1_ge (by norm_num)
    linarith [h3, h4, h2, hfrac, hlog1]
  have hξ_eq_neg : hankelXi c (-1028 * r) = ξ₁ := by
    dsimp [ξ₁]; congr 1; ring
  rw [hξ_eq_neg]
  by_contra hlt
  have hξ_gt : ξ₁ < ξ := not_le.1 hlt
  have hξ₁_pos : 0 < ξ₁ := hankelXi_pos hc0 hrA
  have hξ_pos : 0 < ξ := hξ₁_pos.trans hξ_gt
  have hμ_gt : 1025 * r / langerScale c < hankelBandMu ξ := by
    unfold hankelBandMu; rw [ite_eq_left hξ_pos]
    have := Real.log_lt_log (by positivity) (show Real.pi ^ 2 * ξ₁ < Real.pi ^ 2 * ξ by
      exact mul_lt_mul_of_pos_left hξ_gt (by positivity))
    linarith
  have hμ_pos : 0 < hankelBandMu ξ := lt_of_le_of_lt (by positivity) hμ_gt
  set τ₀ := hankelBandTau0 ξ
  have hτ₀_nn : 0 ≤ τ₀ := hankelBandTau0_nonneg ξ
  have hm_root : hankelEdgeM τ₀ = hankelBandMu ξ := hankelBandTau0_root hμ_pos
  have hm_ub := hankelEdgeM_le_sq hτ₀_nn
  rw [hm_root] at hm_ub
  have hτ₀_sq_gt : 4100 * langerKappa ^ 2 * c ^ (-(2 / 3 : ℝ)) * r < τ₀ ^ 2 := by
    have hKdef : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
    have hc23 : c ^ (-(2 / 3 : ℝ)) = (c ^ (2 / 3 : ℝ))⁻¹ := Real.rpow_neg hc0.le _
    have h1 : 12 / Real.pi ^ 2 * (1025 * r / langerScale c) < τ₀ ^ 2 := by
      have hlt_pi : 1025 * r / langerScale c < Real.pi ^ 2 / 12 * τ₀ ^ 2 := hμ_gt.trans_le hm_ub
      have hpi2_pos : 0 < Real.pi ^ 2 := by positivity
      calc 12 / Real.pi ^ 2 * (1025 * r / langerScale c)
          < 12 / Real.pi ^ 2 * (Real.pi ^ 2 / 12 * τ₀ ^ 2) := mul_lt_mul_of_pos_left hlt_pi (by positivity)
        _ = τ₀ ^ 2 := by field_simp [hpi2_pos.ne']
    have h2 : 12 / Real.pi ^ 2 * (1025 * r / langerScale c) =
        4100 * langerKappa ^ 2 * c ^ (-(2 / 3 : ℝ)) * r := by
      have h12 : 12 / Real.pi ^ 2 = 4 * langerKappa ^ 3 := by
        rw [hk3]; field_simp; ring
      rw [h12, hKdef, hc23]
      have hk0 : langerKappa ≠ 0 := langerKappa_pos.ne'
      have hc23_pos : c ^ (2 / 3 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
      field_simp; ring
    linarith
  have hρ_sq : (32 * rhoR hankelBandParams c r) ^ 2 =
      4096 * langerKappa ^ 2 * c ^ (-(2 / 3 : ℝ)) * r := by
    have hρ_eq : 32 * rhoR hankelBandParams c r = 64 * langerKappa * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r := by
      show 32 * (hankelBandParams.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) = _
      have : hankelBandParams.κ_ζ = 2 * langerKappa := rfl
      rw [this]; ring
    have hc23 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    rw [hρ_eq, mul_pow, mul_pow, mul_pow, hc23, Real.sq_sqrt hr.le]; ring
  have hsq_lt : (32 * rhoR hankelBandParams c r) ^ 2 < τ₀ ^ 2 := by
    have h4 : 0 < langerKappa ^ 2 * c ^ (-(2 / 3 : ℝ)) * r := by
      have := langerKappa_pos; positivity
    linarith [hρ_sq, hτ₀_sq_gt]
  have hpow := pow_lt_pow_left₀ hτ_lt hτ₀_nn two_ne_zero
  linarith

end ChartComparison

section ThreePieces

/-- Core piece `(1 - χ₀)` on `|τ| ≤ 4 δ₀`: bounded by `C_core_scale * r^(-1/2) / cos ψ`. -/
private lemma core_piece_scale_bound {c ε : ℝ} {f : ℝ → ℝ} (hc : 3e6 ≤ c) (hε : ε = 1 ∨ ε = -1)
    (hf : IsHankelEigenfn c ε f) (hmass : hankelMass c f = 1)
    {r : ℝ} (hr : 256 ≤ r) {ζ₀ : ℂ} {ψ : ℝ}
    (hζ₀_lo : rhoR hankelBandParams c r / 3 ≤ ‖ζ₀‖) (hζ₀_hi : ‖ζ₀‖ ≤ 0.035)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ) (hcos_pos : 0 < Real.cos ψ)
    (hcore_int : Integrable (fun τ : ℝ =>
      ((1 - tebCutoff (hankelBandParams.A_0 * c ^ (-(1 / 3 : ℝ))) τ : ℝ) : ℂ) *
        (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I)))) :
    let P := hankelBandParams
    ‖∫ τ : ℝ, ((1 - tebCutoff (P.A_0 * c ^ (-(1 / 3 : ℝ))) τ : ℝ) : ℂ) *
        (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))‖ ≤
      ((8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) *
          (3 / P.κ_ζ) / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) := by
  intro P
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith
  have hσ₀ : 0 < ζ₀.re := by
    have hρr : 0 < rhoR P c r := by
      show 0 < P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
      have := P.hκ_ζ; positivity
    rw [hcos_eq]; exact mul_pos (lt_of_lt_of_le (by positivity) hζ₀_lo) hcos_pos
  have hσ₀_le : ζ₀.re ≤ 0.04 := (Complex.re_le_norm _).trans (hζ₀_hi.trans (by norm_num))
  have hσ₁ : ζ₀.re < 1 := by linarith
  set δ := P.A_0 * c ^ (-(1 / 3 : ℝ))
  have hδ_pos : 0 < δ := by dsimp [δ]; have := P.hA_0; positivity
  have hε_abs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 / ζ₀.re := fun τ =>
    (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im hε_abs τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
  let coreFn : ℝ → ℂ := fun τ => ((1 - tebCutoff δ τ : ℝ) : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))
  have hsupp : ∫ τ : ℝ, coreFn τ = ∫ τ in Icc (-4 * δ) (4 * δ), coreFn τ := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_
    have hgt : 4 * δ ≤ |τ| := by
      by_contra hlt
      have hlt' := abs_lt.mp (not_le.mp hlt)
      exact hτ ⟨by linarith, by linarith⟩
    dsimp [coreFn]
    rw [tebCutoff_eq_one hδ_pos hgt, sub_self, Complex.ofReal_zero, zero_mul, zero_mul]
  have hpt : ∀ τ ∈ Icc (-4 * δ) (4 * δ), ‖coreFn τ‖ ≤
      (1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W := by
    intro τ hτ
    have habs : |τ| ≤ 4 * δ := abs_le.mpr ⟨by linarith [hτ.1], hτ.2⟩
    have h1χ : |1 - tebCutoff δ τ| ≤ 1 := abs_le.mpr
      ⟨by linarith [tebCutoff_le_one δ τ], by linarith [tebCutoff_nonneg δ τ]⟩
    have hA0 : ‖tebAmp0 c τ‖ ≤ (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) := by
      have hδ_le : δ ≤ P.A_0 := by
        dsimp [δ]
        have hc_le : c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        nlinarith [P.hA_0]
      have habs_A : |τ| ≤ 4 * P.A_0 := habs.trans (by linarith)
      have h1 := norm_tebAmp0_le hc0.le (τ := τ)
      have hτ52 : |τ| ^ (5 / 2 : ℝ) ≤ (4 * δ) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) habs (by norm_num)
      have h1τ52 : (1 + |τ|) ^ (5 / 2 : ℝ) ≤ (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith [abs_nonneg τ]) (by linarith) (by norm_num)
      have hexp1 : Real.exp (-τ ^ 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg τ])
      have hc_cancel : c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) = (4 * P.A_0) ^ (5 / 2 : ℝ) := by
        dsimp [δ]
        rw [show 4 * (P.A_0 * c ^ (-(1 / 3 : ℝ))) = (4 * P.A_0) * c ^ (-(1 / 3 : ℝ)) by ring]
        rw [Real.mul_rpow (by have := P.hA_0; positivity) (Real.rpow_nonneg hc0.le _),
          ← Real.rpow_mul hc0.le]
        have hexp : -(1 / 3 : ℝ) * (5 / 2 : ℝ) = -(5 / 6 : ℝ) := by norm_num
        rw [hexp, ← mul_assoc, mul_comm (c ^ (5 / 6 : ℝ)), mul_assoc, ← Real.rpow_add hc0]
        simp
      have hcτ : c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) ≤ c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hτ52 (Real.rpow_nonneg hc0.le _)
      have hcτ1 : c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) ≤
          c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) :=
        mul_le_mul hcτ h1τ52 (Real.rpow_nonneg (by linarith [abs_nonneg τ]) _)
          (mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg (by positivity) _))
      calc ‖tebAmp0 c τ‖
          ≤ c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2) := h1
        _ ≤ (c ^ (5 / 6 : ℝ) * (4 * δ) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ)) * 1 :=
            mul_le_mul hcτ1 hexp1 (Real.exp_pos _).le
              (mul_nonneg (mul_nonneg (Real.rpow_nonneg hc0.le _) (Real.rpow_nonneg (by positivity) _))
                (Real.rpow_nonneg (by have := P.hA_0; positivity) _))
        _ = (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) := by rw [hc_cancel, mul_one]
    have hW : ‖hankelWtS c ε f ((τ : ℂ) * Complex.I)‖ ≤ P.C_W * (1 + 4 * P.A_0) ^ P.M := by
      have hδ_le : δ ≤ P.A_0 := by
        dsimp [δ]
        have hc_le : c ^ (-(1 / 3 : ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
        nlinarith [P.hA_0]
      have habs_A : |τ| ≤ 4 * P.A_0 := habs.trans (by linarith)
      have hre : ((τ : ℂ) * Complex.I).re = 0 := by simp
      have hb := hankelWtS_norm_le hc32 hf hε hre.ge (by linarith)
      rw [hmass, one_mul] at hb
      have hexp2 : Real.exp (1 / (6 * c)) ≤ 2 := hankelBand_exp_le_two (by linarith)
      have hnorm : ‖(τ : ℂ) * Complex.I‖ = |τ| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      rw [hnorm] at hb
      have hpow : (1 + |τ|) ^ P.M ≤ (1 + 4 * P.A_0) ^ P.M :=
        Real.rpow_le_rpow (by linarith [abs_nonneg τ]) (by linarith) P.hM
      have h2 : Real.exp (1 / (6 * c)) * (1 + |τ|) ^ (1 / 2 : ℝ) ≤ P.C_W * (1 + 4 * P.A_0) ^ P.M := by
        have hCw : P.C_W = 2 := rfl
        have hM : P.M = 1 / 2 := rfl
        rw [hCw, hM]
        exact mul_le_mul hexp2 hpow (by positivity) (by norm_num)
      exact hb.trans h2
    have h1pow : (1 + 4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ P.M =
        (1 + 4 * P.A_0) ^ (P.M + 5 / 2) := by
      rw [← Real.rpow_add (by have := P.hA_0; positivity)]; ring_nf
    dsimp [coreFn]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have h12 : |1 - tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 * (1 / ζ₀.re) :=
      mul_le_mul h1χ (hQ_bd τ) (abs_nonneg _) zero_le_one
    have h34 : ‖tebAmp0 c τ‖ * ‖hankelWtS c ε f ((τ : ℂ) * Complex.I)‖ ≤
        ((4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ)) * (P.C_W * (1 + 4 * P.A_0) ^ P.M) :=
      mul_le_mul hA0 hW (norm_nonneg _) (by have := P.hA_0; positivity)
    calc |1 - tebCutoff δ τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ| *
          (‖tebAmp0 c τ‖ * ‖hankelWtS c ε f ((τ : ℂ) * Complex.I)‖)
        ≤ (1 * (1 / ζ₀.re)) *
            (((4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (5 / 2 : ℝ)) *
              (P.C_W * (1 + 4 * P.A_0) ^ P.M)) :=
          mul_le_mul h12 h34 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) *
            ((1 + 4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ P.M) * P.C_W := by ring
      _ = (1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W := by
          rw [h1pow]
  have hnorm_le : ‖∫ τ in Icc (-4 * δ) (4 * δ), coreFn τ‖ ≤
      (volume.real (Icc (-4 * δ) (4 * δ))) *
        ((1 / ζ₀.re) * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) :=
    (norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-4 * δ) (4 * δ))
      measure_Icc_lt_top hpt).trans_eq (mul_comm _ _)
  have hvol : volume.real (Icc (-4 * δ) (4 * δ)) = 8 * δ := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have h_δ : ‖∫ τ : ℝ, coreFn τ‖ ≤
      (8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W / ζ₀.re) *
        c ^ (-(1 / 3 : ℝ)) := by
    rw [hsupp]
    refine hnorm_le.trans_eq ?_
    rw [hvol]; dsimp [δ]; ring
  have hr_pos : 0 < r := by linarith
  have hσ₀_lb : (P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r * Real.cos ψ ≤ ζ₀.re := by
    rw [hcos_eq]
    have h1 : rhoR P c r / 3 = (P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r := by
      show (P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) / 3 = _; ring
    rw [← h1]
    exact mul_le_mul_of_nonneg_right hζ₀_lo hcos_pos.le
  have hcσ_le : c ^ (-(1 / 3 : ℝ)) / ζ₀.re ≤ (3 / P.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ)) := by
    have hκ := P.hκ_ζ
    have hsqrt : Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr_pos]; norm_num
    rw [div_le_iff₀ hσ₀]
    calc c ^ (-(1 / 3 : ℝ))
        = (3 / P.κ_ζ) / Real.cos ψ * ((P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * (Real.sqrt r * r ^ (-(1 / 2 : ℝ))) * Real.cos ψ) := by
          rw [hsqrt]; field_simp
      _ = ((3 / P.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ))) *
            ((P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r * Real.cos ψ) := by ring
      _ ≤ ((3 / P.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ))) * ζ₀.re := by gcongr
  set C_core := 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W
  have hC_nn : 0 ≤ C_core := by dsimp [C_core]; have := P.hA_0; have := P.hC_W; positivity
  calc ‖∫ τ : ℝ, coreFn τ‖
      ≤ C_core * (c ^ (-(1 / 3 : ℝ)) / ζ₀.re) := h_δ.trans_eq (by dsimp [C_core]; ring)
    _ ≤ C_core * ((3 / P.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left hcσ_le hC_nn
    _ = _ := by dsimp [C_core]; ring

private lemma inner_half_bv {c ε sgn σ₀ η₀ r : ℝ} (hc : 3e6 ≤ c)
    (hσ₀ : 0 < σ₀) (hσ₀_le : σ₀ ≤ 0.04) (hε : |ε| ≤ 1) (hsgn : sgn = 1 ∨ sgn = -1) (hr : 0 < r) :
    let P := hankelBandParams
    let δ₀ := P.A_0 * c ^ (-(1 / 3 : ℝ))
    let ρr := rhoR P c r
    let χ₁ : ℝ → ℝ := fun τ => tebCutoff δ₀ τ * (1 - tebCutoff (4 * ρr) τ)
    let h₁ : ℝ → ℂ := fun τ => (χ₁ τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
      (tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ))
    ∀ s > 0, BoundedVariationOn h₁ (Icc s (2 * s)) ∧
      (∀ τ ∈ Icc s (2 * s), ‖h₁ τ‖ + (eVariationOn h₁ (Icc s (2 * s))).toReal ≤
        (16 * 8704) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) *
          Real.exp (-s ^ 2)) := by
  intro P δ₀ ρr χ₁ h₁ s hs
  have hc0 : 0 < c := by linarith only [hc]
  have h1 : σ₀ < 1 := by linarith only [hσ₀_le]
  have hδ_pos : 0 < δ₀ := by dsimp [δ₀]; have := P.hA_0; positivity
  have hρr_pos : 0 < ρr := by
    show 0 < P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
    have := P.hκ_ζ; positivity
  have hsgn_abs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ σ₀ η₀ ε τ| ≤ 1 / σ₀ := fun τ =>
    (stripPoissonQ_abs_le hσ₀ h1 η₀ hε τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le η₀ τ)
  have hs_le : s ≤ 2 * s := by linarith only [hs]
  have hf1_bd : ∀ τ ∈ Icc s (2 * s), ‖(tebCutoff δ₀ τ : ℂ)‖ ≤ 1 := fun τ _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [tebCutoff_nonneg δ₀ τ], tebCutoff_le_one δ₀ τ⟩
  have hf1_bv : eVariationOn (fun τ => (tebCutoff δ₀ τ : ℂ)) (Icc s (2 * s)) ≤ ENNReal.ofReal 1 := by
    rw [eVariationOn_ofReal]; exact tebCutoff_eVariationOn_le hδ_pos hs.le hs_le
  have hf2_bd : ∀ τ ∈ Icc s (2 * s), ‖((1 - tebCutoff (4 * ρr) τ : ℝ) : ℂ)‖ ≤ 1 := fun τ _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [tebCutoff_le_one (4 * ρr) τ], by linarith only [tebCutoff_nonneg (4 * ρr) τ]⟩
  have hf2_bv : eVariationOn (fun τ => ((1 - tebCutoff (4 * ρr) τ : ℝ) : ℂ)) (Icc s (2 * s)) ≤ ENNReal.ofReal 1 :=
    one_sub_tebCutoff_eVariationOn_le (by positivity) hs.le hs_le
  have h12 := bv_norm_add_tv_mul zero_le_one zero_le_one zero_le_one zero_le_one
    hf1_bd hf2_bd hf1_bv hf2_bv
  have hf12_bd : ∀ τ ∈ Icc s (2 * s), ‖(χ₁ τ : ℂ)‖ ≤ 1 := fun τ hτ => by
    have : (χ₁ τ : ℂ) = (tebCutoff δ₀ τ : ℂ) * ((1 - tebCutoff (4 * ρr) τ : ℝ) : ℂ) := by
      dsimp [χ₁]; push_cast; ring
    rw [this, norm_mul]
    exact (mul_le_mul (hf1_bd τ hτ) (hf2_bd τ hτ) (norm_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have hf12_bv : eVariationOn (fun τ => (χ₁ τ : ℂ)) (Icc s (2 * s)) ≤ ENNReal.ofReal 2 := by
    have : (fun τ => (χ₁ τ : ℂ)) = fun τ => (tebCutoff δ₀ τ : ℂ) * ((1 - tebCutoff (4 * ρr) τ : ℝ) : ℂ) := by
      ext τ; dsimp [χ₁]; push_cast; ring
    rw [this]; exact h12.2.1.trans (ENNReal.ofReal_le_ofReal (by norm_num))
  have hQ_s_bd : ∀ τ ∈ Icc s (2 * s), ‖(stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ 1 / σ₀ := fun τ _ => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hQ_bd _
  have hQ_tv : eVariationOn (fun τ => (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)) (Icc s (2 * s)) ≤
      ENNReal.ofReal (1 / σ₀) := by
    rw [eVariationOn_ofReal (fun τ => stripPoissonQ σ₀ η₀ ε (sgn * τ))]
    have hQ_all := eVariationOn_stripPoissonQ_le hσ₀ hσ₀_le η₀ hε
    rcases hsgn with rfl | rfl
    · simpa using (eVariationOn.mono _ (subset_univ _)).trans hQ_all
    · have hcomp := eVariationOn_comp_neg (stripPoissonQ σ₀ η₀ ε)
      have hsub : eVariationOn (fun τ => stripPoissonQ σ₀ η₀ ε (-1 * τ)) (Icc s (2 * s)) ≤
          eVariationOn (fun τ => stripPoissonQ σ₀ η₀ ε (-τ)) univ := by
        simpa using eVariationOn.mono (fun τ => stripPoissonQ σ₀ η₀ ε (-τ)) (subset_univ _)
      exact hsub.trans (hcomp.trans hQ_all)
  have h123 := bv_norm_add_tv_mul zero_le_one (by positivity) (by norm_num) (by positivity)
    hf12_bd hQ_s_bd hf12_bv hQ_tv
  have hf123_bd : ∀ τ ∈ Icc s (2 * s),
      ‖(χ₁ τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ 1 * (1 / σ₀) := fun τ hτ => by
    rw [norm_mul]; exact mul_le_mul (hf12_bd τ hτ) (hQ_s_bd τ hτ) (norm_nonneg _) zero_le_one
  have hf123_bv : eVariationOn (fun τ => (χ₁ τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ))
      (Icc s (2 * s)) ≤ ENNReal.ofReal (3 / σ₀) :=
    h123.2.1.trans (ENNReal.ofReal_le_ofReal (by ring_nf; linarith only [div_pos zero_lt_one hσ₀]))
  obtain ⟨hamp_bv, hamp_ev, hamp_all⟩ := tebAmp0_mul_edgeAmp_block_bv_le hc hsgn_abs hs
  set Mamp := 8704 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2)
  have hMamp_nn : 0 ≤ Mamp := by dsimp [Mamp]; positivity
  have hamp_bd : ∀ τ ∈ Icc s (2 * s),
      ‖tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ)‖ ≤ Mamp := fun τ hτ => by
    have := hamp_all τ hτ
    have htv : 0 ≤ (eVariationOn (fun t => tebAmp0 c (sgn * t) * hankelEdgeAmp c (sgn * t))
        (Icc s (2 * s))).toReal := ENNReal.toReal_nonneg
    dsimp [Mamp] at *; linarith only [this, htv]
  have htot := bv_norm_add_tv_mul (by positivity) hMamp_nn (by positivity) hMamp_nn
    hf123_bd hamp_bd hf123_bv hamp_ev
  have heq_h1 : (fun τ => (χ₁ τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
      (tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ))) = h₁ := rfl
  refine ⟨heq_h1 ▸ htot.1, fun τ hτ => ?_⟩
  have hb := htot.2.2 τ hτ
  have h4mul : (1 * (1 / σ₀) + 3 / σ₀) * (Mamp + Mamp) =
      (8 * 8704) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2) := by
    dsimp [Mamp]; ring
  have h8_le : (8 * 8704 : ℝ) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2) ≤
      (16 * 8704) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2) := by
    have : 0 ≤ (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2) := by positivity
    linarith only [this]
  linarith only [hb, h4mul, h8_le]

/-- Inner oscillatory piece `χ₁ = χ₀ (1 - ψ_r)` on `Ioi 0` for `sgn = ±1` and `ξ > 0`. -/
private lemma inner_half_osc_bound {c ε sgn σ₀ η₀ r ξ : ℝ} (hc : 3e6 ≤ c)
    (hσ₀ : 0 < σ₀) (hσ₀_le : σ₀ ≤ 0.04) (hε : |ε| ≤ 1) (hsgn : sgn = 1 ∨ sgn = -1)
    (hξ : 0 < ξ) (hr : 256 ≤ r) (hρ_ub : 2 * rhoR hankelBandParams c r ≤ 0.035) :
    let P := hankelBandParams
    let δ₀ := P.A_0 * c ^ (-(1 / 3 : ℝ))
    let ρr := rhoR P c r
    let C_in : ℝ := 27380416512
    let χ₁ : ℝ → ℝ := fun τ => tebCutoff δ₀ τ * (1 - tebCutoff (4 * ρr) τ)
    let F₁ : ℝ → ℂ := fun τ => (χ₁ τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
      tebAmp0 c (sgn * τ) * hankelBandK c (sgn * τ) ξ
    IntegrableOn F₁ (Ioi 0) ∧
    ‖∫ τ in Ioi (0 : ℝ), F₁ τ‖ ≤
      C_in * (1 / σ₀) * c ^ (5 / 6 : ℝ) *
        (c⁻¹ * ρr ^ (1 / 2 : ℝ) +
          c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 *
            (if δ₀ < hankelBandTau0 ξ ∧ hankelBandTau0 ξ < 32 * ρr then 1 else 0)) := by
  intro P δ₀ ρr C_in χ₁ F₁
  have hc0 : 0 < c := by linarith
  have h1 : σ₀ < 1 := by linarith
  have hδ_pos : 0 < δ₀ := by dsimp [δ₀]; have := P.hA_0; positivity
  have hρr_pos : 0 < ρr := by
    show 0 < P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
    have := P.hκ_ζ; positivity
  have h16ρ_le : 16 * ρr ≤ 1 := by linarith
  have ha_le_b : 2 * δ₀ ≤ 16 * ρr := by
    have hk := hankelLangerKappa_bounds
    have hA0_le : P.A_0 ≤ 8 := by
      show Real.sqrt (32 / langerKappa) ≤ 8
      exact Real.sqrt_le_iff.2 ⟨by norm_num, by rw [div_le_iff₀ langerKappa_pos]; linarith⟩
    have hκ_ge : 1 ≤ P.κ_ζ := by show 1 ≤ 2 * langerKappa; linarith
    have hsqrt_ge : 16 ≤ Real.sqrt r := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; norm_num [hr]
    have hc_nn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    dsimp [δ₀, ρr]
    have hκr : 16 ≤ P.κ_ζ * Real.sqrt r := by
      calc (16 : ℝ) = 1 * 16 := by ring
        _ ≤ P.κ_ζ * Real.sqrt r := mul_le_mul hκ_ge hsqrt_ge (by norm_num) P.hκ_ζ.le
    calc 2 * (P.A_0 * c ^ (-(1 / 3 : ℝ)))
        = (2 * P.A_0) * c ^ (-(1 / 3 : ℝ)) := by ring
      _ ≤ 16 * c ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (by linarith) hc_nn
      _ ≤ (P.κ_ζ * Real.sqrt r) * c ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right hκr hc_nn
      _ ≤ 16 * ((P.κ_ζ * Real.sqrt r) * c ^ (-(1 / 3 : ℝ))) := by
          have : 0 ≤ (P.κ_ζ * Real.sqrt r) * c ^ (-(1 / 3 : ℝ)) := by positivity
          linarith
      _ = 16 * (P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) := by ring
  have hsgn_abs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ σ₀ η₀ ε τ| ≤ 1 / σ₀ := fun τ =>
    (stripPoissonQ_abs_le hσ₀ h1 η₀ hε τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le η₀ τ)
  let h₁ : ℝ → ℂ := fun τ => (χ₁ τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
    (tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ))
  let φ : ℝ → ℝ := fun y => -sgn * edgePhi (hankelBandMu ξ) y
  let φ' : ℝ → ℝ := fun y => sgn * (hankelEdgeM y - hankelBandMu ξ)
  let φ'' : ℝ → ℝ := fun y => sgn * hankelEdgeM' y
  have hF₁_eq : ∀ τ : ℝ, F₁ τ = h₁ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ)) := by
    intro τ
    dsimp [F₁, h₁, φ, hankelBandK, hankelBandPhi]
    have hμ_eq : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by
      unfold hankelBandMu; rw [ite_eq_left hξ]
    have hodd : edgePhi (hankelBandMu ξ) (sgn * τ) = sgn * edgePhi (hankelBandMu ξ) τ := by
      rcases hsgn with rfl | rfl
      · simp
      · simp [hankelEdgePhi_odd]
    rw [← hμ_eq, hodd]
    have hexp_eq : Complex.exp ((c : ℂ) * ((0 : ℂ) - Complex.I * ((sgn * edgePhi (hankelBandMu ξ) τ : ℝ) : ℂ))) =
        Complex.exp (Complex.I * (c : ℂ) * ((-sgn * edgePhi (hankelBandMu ξ) τ : ℝ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [hexp_eq]; ring
  have hh₁_cont : Continuous h₁ := by
    have hχ : Continuous χ₁ := (tebCutoff_continuous δ₀).mul (continuous_const.sub (tebCutoff_continuous (4 * ρr)))
    have hQ : Continuous (stripPoissonQ σ₀ η₀ ε) := stripPoissonQ_continuous hσ₀ h1
    exact ((Complex.continuous_ofReal.comp hχ).mul
      (Complex.continuous_ofReal.comp (hQ.comp (continuous_const.mul continuous_id)))).mul
      ((continuous_tebAmp0 c).comp (continuous_const.mul continuous_id) |>.mul
        ((hankelEdgeAmp_continuous hc0).comp (continuous_const.mul continuous_id)))
  have hF₁_cont : Continuous F₁ := by
    have h_eq : F₁ = fun τ => h₁ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ)) :=
      funext hF₁_eq
    rw [h_eq]
    have hφ_cont : Continuous φ :=
      continuous_const.mul (continuous_iff_continuousAt.2 fun τ => (hasDerivAt_edgePhi _ τ).continuousAt)
    exact (hh₁_cont.mul continuous_const).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hφ_cont)))
  have hsupp_hi : ∀ τ : ℝ, 16 * ρr ≤ τ → F₁ τ = 0 := fun τ hτ => by
    have h1 := tebCutoff_eq_one (by positivity : 0 < 4 * ρr) (by
      rw [abs_of_nonneg (by linarith : 0 ≤ τ)]; linarith)
    simp [F₁, χ₁, h1]
  have hsupp_lo : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 2 * δ₀ → F₁ τ = 0 := fun τ hτ0 hτ => by
    have h0 := tebCutoff_eq_zero hδ_pos (by rw [abs_of_nonneg hτ0]; exact hτ)
    simp [F₁, χ₁, h0]
  have hEq_ind : EqOn F₁ ((Icc (2 * δ₀) (16 * ρr)).indicator F₁) (Ioi 0) := fun τ hτ => by
    by_cases hm : τ ∈ Icc (2 * δ₀) (16 * ρr)
    · rw [Set.indicator_of_mem hm]
    · rw [Set.indicator_of_notMem hm]
      rcases le_or_gt τ (2 * δ₀) with hlo | hlo
      · exact hsupp_lo τ hτ.le hlo
      · have hhi : 16 * ρr < τ := by
          by_contra hle; exact hm ⟨hlo.le, not_lt.1 hle⟩
        exact hsupp_hi τ hhi.le
  have hInt : IntegrableOn F₁ (Ioi 0) := by
    have hIcc : IntegrableOn F₁ (Icc (2 * δ₀) (16 * ρr)) := hF₁_cont.continuousOn.integrableOn_Icc
    have hind : Integrable ((Icc (2 * δ₀) (16 * ρr)).indicator F₁) :=
      (integrable_indicator_iff measurableSet_Icc).2 hIcc
    exact hind.integrableOn.congr_fun (fun τ hτ => (hEq_ind hτ).symm) measurableSet_Ioi
  refine ⟨hInt, ?_⟩
  have hInt_eq : ∫ τ in Ioi (0 : ℝ), F₁ τ = ∫ τ in (2 * δ₀)..(16 * ρr), F₁ τ := by
    have h1 : ∫ τ in Ioi (0 : ℝ), F₁ τ = ∫ τ in Icc (2 * δ₀) (16 * ρr), F₁ τ := by
      have hinter : Ioi (0 : ℝ) ∩ Icc (2 * δ₀) (16 * ρr) = Icc (2 * δ₀) (16 * ρr) :=
        Set.inter_eq_right.2 (fun τ (hτ : τ ∈ Icc (2 * δ₀) (16 * ρr)) => lt_of_lt_of_le (by positivity) hτ.1)
      rw [setIntegral_congr_fun measurableSet_Ioi hEq_ind,
        setIntegral_indicator measurableSet_Icc, hinter]
    rw [h1, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha_le_b]
  rw [hInt_eq]
  have hh₁_bv := @inner_half_bv c ε sgn σ₀ η₀ r hc hσ₀ hσ₀_le hε hsgn (by linarith only [hr] : 0 < r)
  obtain ⟨hφ, hφ', hφ'_mono, h_upper, h_lower, h_mid⟩ := hankel_phase_bounds hsgn hξ
  have hφ'_cont : ContinuousOn φ' (Ioi 0) :=
    fun y hy => (hφ' y hy).continuousAt.continuousWithinAt
  have hh₁_le_bound : ∀ s > 0, s ≤ 1 →
      ∀ τ ∈ Icc s (2 * s), ‖h₁ τ‖ + (eVariationOn h₁ (Icc s (2 * s))).toReal ≤
        16 * 8704 * 64 * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) := by
    intro s hs hs1 τ hτ
    have h1 := (hh₁_bv s hs).2 τ hτ
    have h1s6 : (1 + s) ^ (6 : ℝ) ≤ 64 := by
      calc (1 + s) ^ (6 : ℝ) ≤ (2 : ℝ) ^ (6 : ℝ) := Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
        _ = 64 := by norm_num
    have hexp1 : Real.exp (-s ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg s])
    have h2 : (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2) ≤ 64 * 1 :=
      mul_le_mul h1s6 hexp1 (Real.exp_pos _).le (by positivity)
    calc ‖h₁ τ‖ + (eVariationOn h₁ (Icc s (2 * s))).toReal
        ≤ (16 * 8704) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * ((1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2)) := by
          linarith [h1]
      _ ≤ (16 * 8704) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (64 * 1) := by gcongr
      _ = _ := by ring
  have hvdc1 : ∀ s u v lam : ℝ, 0 < s → s ≤ u → u ≤ v → v ≤ 16 * ρr → v ≤ 2 * s → 0 < lam →
      (∀ τ ∈ Icc u v, lam ≤ |φ' τ|) →
      ‖∫ τ in u..v, F₁ τ‖ ≤
        (3 * 16 * 8704 * 64 * (1 / σ₀) * c ^ (-(1 / 6 : ℝ)) / lam) * s ^ (5 / 2 : ℝ) := by
    intro s u v lam hs hsu huv hv16 hv2s hlam hlb
    have hs1 : s ≤ 1 := by linarith
    have hsub : Icc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hs (hsu.trans hτ.1)
    have hsub_s : Icc u v ⊆ Icc s (2 * s) := Icc_subset_Icc hsu hv2s
    have hbv_s := (hh₁_bv s hs).1
    have hbv_uv : BoundedVariationOn h₁ (Icc u v) := hbv_s.mono hsub_s
    have htv_uv : (eVariationOn h₁ (Icc u v)).toReal ≤ (eVariationOn h₁ (Icc s (2 * s))).toReal :=
      ENNReal.toReal_mono hbv_s (eVariationOn.mono h₁ hsub_s)
    set B := 16 * 8704 * 64 * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ)
    have hvdc := van_der_corput_first_comp (w := id) (w' := fun _ => 1)
      (M := B - (eVariationOn h₁ (Icc s (2 * s))).toReal)
      huv hc0 hlam (fun x _ => hasDerivAt_id x) continuousOn_const (fun _ _ => zero_le_one)
      (fun y hy => hφ y (hsub hy)) (hφ'_cont.mono hsub)
      (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub)) (fun ha => Or.inr (ha.mono hsub)))
      hlb hh₁_cont.continuousOn hbv_uv
      (fun τ hτ => by linarith [hh₁_le_bound s hs hs1 τ (hsub_s hτ)])
    have hF_rw : (fun x => h₁ x * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ x : ℂ))) = F₁ :=
      funext fun τ => (hF₁_eq τ).symm
    change ‖∫ τ in u..v, h₁ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ))‖ ≤ _ at hvdc
    rw [hF_rw] at hvdc
    have hc_comb : c ^ (5 / 6 : ℝ) / c = c ^ (-(1 / 6 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
    calc ‖∫ τ in u..v, F₁ τ‖
        ≤ 3 * ((B - (eVariationOn h₁ (Icc s (2 * s))).toReal) + (eVariationOn h₁ (Icc u v)).toReal) / (c * lam) := hvdc
      _ ≤ 3 * B / (c * lam) := by gcongr; linarith
      _ = (3 * 16 * 8704 * 64 * (1 / σ₀) * (c ^ (5 / 6 : ℝ) / c) / lam) * s ^ (5 / 2 : ℝ) := by
          dsimp [B]; ring
      _ = _ := by rw [hc_comb]
  set a := 2 * δ₀
  set b := 16 * ρr
  set τ₀ := hankelBandTau0 ξ
  have hτ₀_nn : 0 ≤ τ₀ := hankelBandTau0_nonneg ξ
  set x₁ := min b (max a (τ₀ / 2))
  set x₂ := min b (max a (2 * τ₀))
  have ha_le_x1 : a ≤ x₁ := le_min ha_le_b (le_max_left _ _)
  have hx1_le_x2 : x₁ ≤ x₂ := min_le_min_left b (max_le_max_left a (by linarith))
  have hx2_le_b : x₂ ≤ b := min_le_left _ _
  have hsplit3 : ∫ τ in a..b, F₁ τ =
      (∫ τ in a..x₁, F₁ τ) + (∫ τ in x₁..x₂, F₁ τ) + (∫ τ in x₂..b, F₁ τ) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (hF₁_cont.intervalIntegrable (μ := volume) a x₁) (hF₁_cont.intervalIntegrable (μ := volume) x₁ x₂)
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (hF₁_cont.intervalIntegrable (μ := volume) a x₂) (hF₁_cont.intervalIntegrable (μ := volume) x₂ b)
    rw [← h1] at h2; exact h2.symm
  set G₁ : ℝ := 3 * 16 * 8704 * 64 * (1 / σ₀) * c ^ (-(1 / 6 : ℝ))
  have hG₁_nn : 0 ≤ G₁ := by dsimp [G₁]; positivity
  have hlow_bd : ‖∫ τ in a..x₁, F₁ τ‖ ≤ 4 * (32 * G₁) * b ^ (1 / 2 : ℝ) := by
    rcases eq_or_lt_of_le ha_le_x1 with heq | hlt_ax1
    · rw [← heq, intervalIntegral.integral_same, norm_zero]; positivity
    · have hx1_le_half : x₁ ≤ τ₀ / 2 := by
        have h1 : a < max a (τ₀ / 2) := lt_of_lt_of_le hlt_ax1 (min_le_right _ _)
        have h2 : max a (τ₀ / 2) = τ₀ / 2 := by
          rcases max_choice a (τ₀ / 2) with h | h
          · rw [h] at h1; exact absurd h1 (lt_irrefl _)
          · exact h
        exact (min_le_right _ _).trans_eq h2
      have hτ₀_pos : 0 < τ₀ := by linarith [show 0 < a by positivity]
      have hsum := dyadic_sum_rpow_half_le (by positivity : 0 < a) ha_le_x1
        (show 0 ≤ 32 * G₁ by linarith [hG₁_nn]) F₁
        (hF₁_cont.intervalIntegrable a x₁) (fun s u v hs hau huv hvx hsu hv2s => by
          have hvb : v ≤ b := hvx.trans (min_le_left _ _)
          have hs1 : s ≤ 1 := by linarith
          have hs_le_half : s ≤ τ₀ / 2 := by linarith [hvx.trans hx1_le_half]
          have hs2_le : s ^ 2 ≤ min (τ₀ ^ 2) 1 :=
            le_min (pow_le_pow_left₀ hs.le (by linarith) 2) (by nlinarith)
          have hlam_pos : 0 < (1 / 32 : ℝ) * s ^ 2 := by positivity
          have hlb : ∀ τ ∈ Icc u v, (1 / 32 : ℝ) * s ^ 2 ≤ |φ' τ| := fun τ hτ => by
            have hτ_pos : 0 < τ := lt_of_lt_of_le hs (hsu.trans hτ.1)
            rcases eq_or_lt_of_le (hτ.2.trans (hvx.trans hx1_le_half)) with heq | hlt
            · have hcont : ContinuousAt (fun t => |φ' t|) τ :=
                (hφ'_cont τ hτ_pos).abs.continuousAt (isOpen_Ioi.mem_nhds hτ_pos)
              have hev : ∀ᶠ t in 𝓝[<] τ, (1 / 32 : ℝ) * min (τ₀ ^ 2) 1 ≤ |φ' t| := by
                filter_upwards [self_mem_nhdsWithin,
                  nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hτ_pos)] with t ht1 ht2
                exact h_lower t ht2 (by rw [← heq]; exact mem_Iio.1 ht1)
              exact (mul_le_mul_of_nonneg_left hs2_le (by norm_num)).trans
                (ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev)
            · calc (1 / 32 : ℝ) * s ^ 2 ≤ (1 / 32 : ℝ) * min (τ₀ ^ 2) 1 :=
                    mul_le_mul_of_nonneg_left hs2_le (by norm_num)
                _ ≤ |φ' τ| := h_lower τ hτ_pos hlt
          have h1 := hvdc1 s u v ((1 / 32 : ℝ) * s ^ 2) hs hsu huv hvb hv2s hlam_pos hlb
          have hsr : s ^ (5 / 2 : ℝ) / s ^ 2 = s ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast s 2, ← Real.rpow_sub hs]; norm_num
          calc ‖∫ τ in u..v, F₁ τ‖
              ≤ (G₁ / ((1 / 32 : ℝ) * s ^ 2)) * s ^ (5 / 2 : ℝ) := h1
            _ = (32 * G₁) * (s ^ (5 / 2 : ℝ) / s ^ 2) := by ring
            _ = (32 * G₁) * s ^ (1 / 2 : ℝ) := by rw [hsr])
      have hb_pow : x₁ ^ (1 / 2 : ℝ) ≤ b ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by linarith) (min_le_left _ _) (by norm_num)
      exact hsum.trans (mul_le_mul_of_nonneg_left hb_pow (by linarith [hG₁_nn]))
  have hup_bd : ‖∫ τ in x₂..b, F₁ τ‖ ≤ 4 * (32 * G₁) * b ^ (1 / 2 : ℝ) := by
    rcases eq_or_lt_of_le hx2_le_b with heq | hlt_x2b
    · rw [heq, intervalIntegral.integral_same, norm_zero]; positivity
    · have hx2_ge : 2 * τ₀ ≤ x₂ := by
        have hlt : max a (2 * τ₀) < b := by
          by_contra hle
          have : x₂ = b := min_eq_left (not_lt.1 hle)
          linarith
        show 2 * τ₀ ≤ min b (max a (2 * τ₀))
        rw [min_eq_right hlt.le]
        exact le_max_right _ _
      have hx2_pos : 0 < x₂ := lt_of_lt_of_le (by positivity) (ha_le_x1.trans hx1_le_x2)
      exact dyadic_sum_rpow_half_le hx2_pos hx2_le_b (show 0 ≤ 32 * G₁ by linarith [hG₁_nn]) F₁
        (hF₁_cont.intervalIntegrable x₂ b) (fun s u v hs hxu huv hvb hsu hv2s => by
          have hs1 : s ≤ 1 := by linarith
          have hlam_pos : 0 < (1 / 32 : ℝ) * s ^ 2 := by positivity
          have hlb : ∀ τ ∈ Icc u v, (1 / 32 : ℝ) * s ^ 2 ≤ |φ' τ| := fun τ hτ => by
            have hτ_pos : 0 < τ := lt_of_lt_of_le hs (hsu.trans hτ.1)
            have hτ_le1 : τ ≤ 1 := by linarith [hτ.2, hvb]
            have hs2_τ : s ^ 2 ≤ min (τ ^ 2) 1 :=
              le_min (pow_le_pow_left₀ hs.le (hsu.trans hτ.1) 2) (by nlinarith)
            rcases eq_or_lt_of_le (hx2_ge.trans (hxu.trans hτ.1)) with heq | hlt
            · have hcont : ContinuousAt (fun t => |φ' t|) τ :=
                (hφ'_cont τ hτ_pos).abs.continuousAt (isOpen_Ioi.mem_nhds hτ_pos)
              have hev : ∀ᶠ t in 𝓝[>] τ, (1 / 32 : ℝ) * min (t ^ 2) 1 ≤ |φ' t| := by
                filter_upwards [self_mem_nhdsWithin] with t ht
                exact h_upper t (by rw [heq]; exact mem_Ioi.1 ht)
              have hlim : ContinuousAt (fun t => (1 / 32 : ℝ) * min (t ^ 2) 1) τ := by fun_prop
              have hle_τ := le_of_tendsto_of_tendsto (hlim.tendsto.mono_left nhdsWithin_le_nhds)
                (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
              exact (mul_le_mul_of_nonneg_left hs2_τ (by norm_num)).trans hle_τ
            · calc (1 / 32 : ℝ) * s ^ 2 ≤ (1 / 32 : ℝ) * min (τ ^ 2) 1 :=
                    mul_le_mul_of_nonneg_left hs2_τ (by norm_num)
                _ ≤ |φ' τ| := h_upper τ hlt
          have h1 := hvdc1 s u v ((1 / 32 : ℝ) * s ^ 2) hs hsu huv hvb hv2s hlam_pos hlb
          have hsr : s ^ (5 / 2 : ℝ) / s ^ 2 = s ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_natCast s 2, ← Real.rpow_sub hs]; norm_num
          calc ‖∫ τ in u..v, F₁ τ‖
              ≤ (G₁ / ((1 / 32 : ℝ) * s ^ 2)) * s ^ (5 / 2 : ℝ) := h1
            _ = (32 * G₁) * (s ^ (5 / 2 : ℝ) / s ^ 2) := by ring
            _ = (32 * G₁) * s ^ (1 / 2 : ℝ) := by rw [hsr])
  have hmid_bd : ‖∫ τ in x₁..x₂, F₁ τ‖ ≤
      128 * (16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 *
        (if δ₀ < τ₀ ∧ τ₀ < 32 * ρr then 1 else 0) := by
    by_cases hcond : δ₀ < τ₀ ∧ τ₀ < 32 * ρr
    · rw [ite_eq_left hcond, mul_one]
      have hτ₀_pos : 0 < τ₀ := lt_trans hδ_pos hcond.1
      have hρ2 : 2 * ρr ≤ 0.035 := hρ_ub
      have hτ₀_le1 : τ₀ ≤ 1 := by linarith only [hcond.2, hρ2]
      have hx1_ge : τ₀ / 2 ≤ x₁ := le_min (by linarith only [hcond.2]) (le_max_right _ _)
      have hx2_le : x₂ ≤ 2 * τ₀ := (min_le_right _ _).trans (max_le (by linarith only [hcond.1]) le_rfl)
      set m := min x₂ (max x₁ τ₀)
      have hx1_m : x₁ ≤ m := le_min hx1_le_x2 (le_max_left _ _)
      have hm_x2 : m ≤ x₂ := min_le_left _ _
      have hsplit_m : ∫ τ in x₁..x₂, F₁ τ = (∫ τ in x₁..m, F₁ τ) + ∫ τ in m..x₂, F₁ τ :=
        (intervalIntegral.integral_add_adjacent_intervals
          (hF₁_cont.intervalIntegrable x₁ m) (hF₁_cont.intervalIntegrable m x₂)).symm
      have hvdc2_sub : ∀ {u v s : ℝ}, 0 < s → s ≤ 1 → τ₀ / 2 ≤ u → u ≤ v → v ≤ 2 * τ₀ →
          s ≤ u → v ≤ 2 * s → s ≤ τ₀ →
          ‖∫ τ in u..v, F₁ τ‖ ≤
            64 * (16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 := by
        intro u v s hs hs1 hu_lo huv hv_hi hsu hv2s hs_le_τ₀
        have hsub : Icc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le (half_pos hτ₀_pos) (hu_lo.trans hτ.1)
        have hsub_s : Icc u v ⊆ Icc s (2 * s) := Icc_subset_Icc hsu hv2s
        have hbv_s := (hh₁_bv s hs).1
        have hbv_uv : BoundedVariationOn h₁ (Icc u v) := hbv_s.mono hsub_s
        have htv_uv : (eVariationOn h₁ (Icc u v)).toReal ≤ (eVariationOn h₁ (Icc s (2 * s))).toReal :=
          ENNReal.toReal_mono hbv_s (eVariationOn.mono h₁ hsub_s)
        set B := 16 * 8704 * 64 * (1 / σ₀) * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ)
        have hlam_pos : 0 < (1 / 64 : ℝ) * τ₀ := by positivity
        have hlam_le : ∀ y ∈ Icc u v, (1 / 64 : ℝ) * τ₀ ≤ |φ'' y| := fun y hy => by
          have h1 : (1 / 64 : ℝ) * τ₀ ≤ (1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3) := by
            rw [le_div_iff₀ (by positivity)]
            have hcube : τ₀ ^ 3 ≤ 1 := by
              calc τ₀ ^ 3 ≤ 1 ^ 3 := pow_le_pow_left₀ hτ₀_pos.le hτ₀_le1 3
                _ = 1 := one_pow 3
            have hadd : 1 + τ₀ ^ 3 ≤ 2 := by linarith only [hcube]
            calc (1 / 64 : ℝ) * τ₀ * (1 + τ₀ ^ 3) ≤ (1 / 64 : ℝ) * τ₀ * 2 :=
                  mul_le_mul_of_nonneg_left hadd (by positivity)
              _ = (1 / 32 : ℝ) * τ₀ := by ring
          exact h1.trans (h_mid hτ₀_pos y (hu_lo.trans hy.1) (hy.2.trans hv_hi))
        have hvdc := van_der_corput_second_comp (w := id) (w' := fun _ => 1)
          (M := B - (eVariationOn h₁ (Icc s (2 * s))).toReal)
          huv hc0 hlam_pos (fun x _ => hasDerivAt_id x) continuousOn_const (fun _ _ => zero_le_one)
          (fun y hy => hφ y (hsub hy)) (fun y hy => hφ' y (hsub hy))
          (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub)) (fun ha => Or.inr (ha.mono hsub)))
          hlam_le hh₁_cont.continuousOn hbv_uv
          (fun τ hτ => le_sub_iff_add_le.2 (hh₁_le_bound s hs hs1 τ (hsub_s hτ)))
        have hF_rw : (fun x => h₁ x * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ x : ℂ))) = F₁ :=
          funext fun τ => (hF₁_eq τ).symm
        change ‖∫ τ in u..v, h₁ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ))‖ ≤ _ at hvdc
        rw [hF_rw] at hvdc
        have hs52 : s ^ (5 / 2 : ℝ) ≤ τ₀ ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow hs.le hs_le_τ₀ (by norm_num)
        have hden : Real.sqrt (c * ((1 / 64 : ℝ) * τ₀)) = (1 / 8 : ℝ) * (c ^ (1 / 2 : ℝ) * τ₀ ^ (1 / 2 : ℝ)) := by
          rw [show c * ((1 / 64 : ℝ) * τ₀) = (1 / 8 : ℝ) ^ 2 * (c * τ₀) by ring,
            Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num), Real.sqrt_mul hc0.le,
            Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
        have hc_comb : c ^ (5 / 6 : ℝ) / c ^ (1 / 2 : ℝ) = c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
          rw [div_eq_mul_inv, Real.rpow_neg hc0.le]
        have hτ_comb : τ₀ ^ (5 / 2 : ℝ) / τ₀ ^ (1 / 2 : ℝ) = τ₀ ^ 2 := by
          rw [← Real.rpow_sub hτ₀_pos]; norm_num
        calc ‖∫ τ in u..v, F₁ τ‖
            ≤ 8 * ((B - (eVariationOn h₁ (Icc s (2 * s))).toReal) + (eVariationOn h₁ (Icc u v)).toReal) /
                Real.sqrt (c * ((1 / 64 : ℝ) * τ₀)) := hvdc
          _ ≤ 8 * B / Real.sqrt (c * ((1 / 64 : ℝ) * τ₀)) := by gcongr; linarith only [htv_uv]
          _ ≤ 8 * (16 * 8704 * 64 * (1 / σ₀) * c ^ (5 / 6 : ℝ) * τ₀ ^ (5 / 2 : ℝ)) /
                ((1 / 8 : ℝ) * (c ^ (1 / 2 : ℝ) * τ₀ ^ (1 / 2 : ℝ))) := by
              rw [hden]
              refine div_le_div_of_nonneg_right ?_ (by positivity)
              dsimp [B]; gcongr
          _ = 64 * (16 * 8704 * 64) * (1 / σ₀) * (c ^ (5 / 6 : ℝ) / c ^ (1 / 2 : ℝ)) *
                (τ₀ ^ (5 / 2 : ℝ) / τ₀ ^ (1 / 2 : ℝ)) := by ring
          _ = 64 * (16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 := by
              rw [hc_comb, hτ_comb]; ring
      have h_left : ‖∫ τ in x₁..m, F₁ τ‖ ≤
          64 * (16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 := by
        rcases le_or_gt τ₀ x₁ with hτx | hxτ
        · have hm_eq : m = x₁ := by
            show min x₂ (max x₁ τ₀) = x₁
            rw [max_eq_left hτx, min_eq_right hx1_le_x2]
          rw [hm_eq, intervalIntegral.integral_same, norm_zero]; positivity
        · have hm_le : m ≤ τ₀ := (min_le_right _ _).trans (max_le hxτ.le le_rfl)
          exact hvdc2_sub (half_pos hτ₀_pos) (by linarith only [hτ₀_le1, hτ₀_pos]) hx1_ge hx1_m
            (hm_le.trans (by linarith only [hτ₀_pos])) hx1_ge (by linarith only [hm_le])
            (by linarith only [hτ₀_pos])
      have h_right : ‖∫ τ in m..x₂, F₁ τ‖ ≤
          64 * (16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 := by
        rcases le_or_gt x₂ τ₀ with hxτ | hτx
        · have hm_eq : m = x₂ := by
            show min x₂ (max x₁ τ₀) = x₂
            exact min_eq_left (hxτ.trans (le_max_right _ _))
          rw [hm_eq, intervalIntegral.integral_same, norm_zero]; positivity
        · have hm_ge : τ₀ ≤ m := le_min hτx.le (le_max_right _ _)
          exact hvdc2_sub hτ₀_pos hτ₀_le1 (by linarith only [hm_ge, hτ₀_pos]) hm_x2 hx2_le hm_ge hx2_le le_rfl
      calc ‖∫ τ in x₁..x₂, F₁ τ‖
          ≤ ‖∫ τ in x₁..m, F₁ τ‖ + ‖∫ τ in m..x₂, F₁ τ‖ := by rw [hsplit_m]; exact norm_add_le _ _
        _ ≤ _ := by linarith only [h_left, h_right]
    · rw [ite_eq_right hcond, mul_zero]
      have hx_eq : x₁ = x₂ := by
        have hnot : ¬ (δ₀ < τ₀ ∧ τ₀ < 32 * ρr) := hcond
        rcases le_or_gt τ₀ δ₀ with hle | hgt
        · have hx1 : x₁ = a := by
            show min b (max a (τ₀ / 2)) = a
            rw [max_eq_left (by linarith only [hle, show a = 2 * δ₀ from rfl, hτ₀_nn]),
              min_eq_right ha_le_b]
          have hx2 : x₂ = a := by
            show min b (max a (2 * τ₀)) = a
            rw [max_eq_left (by linarith only [hle, show a = 2 * δ₀ from rfl]),
              min_eq_right ha_le_b]
          rw [hx1, hx2]
        · have hge : 32 * ρr ≤ τ₀ := not_lt.1 fun hlt => hnot ⟨hgt, hlt⟩
          have hx1 : x₁ = b :=
            min_eq_left (le_trans (by linarith only [hge, show b = 16 * ρr from rfl]) (le_max_right a (τ₀ / 2)))
          have hx2 : x₂ = b :=
            min_eq_left (le_trans (by linarith only [hge, show b = 16 * ρr from rfl, hρr_pos]) (le_max_right a (2 * τ₀)))
          rw [hx1, hx2]
      rw [hx_eq, intervalIntegral.integral_same, norm_zero]
  have hb_pow : b ^ (1 / 2 : ℝ) = 4 * ρr ^ (1 / 2 : ℝ) := by
    dsimp [b]; rw [Real.mul_rpow (by norm_num) hρr_pos.le]
    have h16 : (16 : ℝ) ^ (1 / 2 : ℝ) = 4 := by
      rw [← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [h16]
  have htri : ‖∫ τ in a..b, F₁ τ‖ ≤
      ‖∫ τ in a..x₁, F₁ τ‖ + ‖∫ τ in x₁..x₂, F₁ τ‖ + ‖∫ τ in x₂..b, F₁ τ‖ := by
    rw [hsplit3]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have h1_nn : 0 ≤ c⁻¹ * ρr ^ (1 / 2 : ℝ) := by positivity
  have h2_nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 *
      (if δ₀ < τ₀ ∧ τ₀ < 32 * ρr then 1 else 0) := by split_ifs <;> positivity
  have hc_comb' : c ^ (-(1 / 6 : ℝ)) = c ^ (5 / 6 : ℝ) * c⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
  have htot1 : 4 * (32 * G₁) * b ^ (1 / 2 : ℝ) + 4 * (32 * G₁) * b ^ (1 / 2 : ℝ) =
      (1024 * 3 * 16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) := by
    rw [hb_pow]; dsimp [G₁]; rw [hc_comb']; ring
  have hC_ge1 : (1024 * 3 * 16 * 8704 * 64 : ℝ) ≤ C_in := by dsimp [C_in]; norm_num
  have hC_ge2 : (128 * 16 * 8704 * 64 : ℝ) ≤ C_in := by dsimp [C_in]; norm_num
  calc ‖∫ τ in a..b, F₁ τ‖
      ≤ ‖∫ τ in a..x₁, F₁ τ‖ + ‖∫ τ in x₁..x₂, F₁ τ‖ + ‖∫ τ in x₂..b, F₁ τ‖ := htri
    _ ≤ 4 * (32 * G₁) * b ^ (1 / 2 : ℝ) +
          128 * (16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 *
            (if δ₀ < τ₀ ∧ τ₀ < 32 * ρr then 1 else 0) +
          4 * (32 * G₁) * b ^ (1 / 2 : ℝ) :=
        add_le_add (add_le_add hlow_bd hmid_bd) hup_bd
    _ = (1024 * 3 * 16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) +
          (128 * 16 * 8704 * 64) * (1 / σ₀) * c ^ (5 / 6 : ℝ) *
            (c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 * (if δ₀ < τ₀ ∧ τ₀ < 32 * ρr then 1 else 0)) := by
          linarith [htot1]
    _ ≤ C_in * (1 / σ₀) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) +
          C_in * (1 / σ₀) * c ^ (5 / 6 : ℝ) *
            (c ^ (-(1 / 2 : ℝ)) * τ₀ ^ 2 * (if δ₀ < τ₀ ∧ τ₀ < 32 * ρr then 1 else 0)) := by
          refine add_le_add ?_ ?_
          · gcongr
          · gcongr
    _ = _ := by ring

/-- Outer oscillatory piece `χ₂ = ψ_r` (`tebCutoff (4 * ρr)`) on `Ioi 0` for `sgn = ±1` and `ξ > 0`. -/
private lemma outer_half_osc_bound {c ε sgn σ₀ η₀ r ξ : ℝ} (hc : 3e6 ≤ c)
    (hσ₀ : 0 < σ₀) (hσ₀_le : σ₀ ≤ 0.04) (hε : |ε| ≤ 1) (hsgn : sgn = 1 ∨ sgn = -1)
    (hξ : 0 < ξ) (hr : 256 ≤ r) (hnorm_ub : ‖(σ₀ : ℂ) + (η₀ : ℂ) * Complex.I‖ ≤ 2 * rhoR hankelBandParams c r) :
    let P := hankelBandParams
    let ρr := rhoR P c r
    let C_out : ℝ := 3e15
    let ψ_r : ℝ → ℝ := tebCutoff (4 * ρr)
    let F₂ : ℝ → ℂ := fun τ => (ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
      tebAmp0 c (sgn * τ) * hankelBandK c (sgn * τ) ξ
    IntegrableOn F₂ (Ioi 0) ∧
    ‖∫ τ in Ioi (0 : ℝ), F₂ τ‖ ≤
      C_out * σ₀ * c ^ (5 / 6 : ℝ) *
        (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)) +
          c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < hankelBandTau0 ξ then 1 else 0)) := by
  intro P ρr C_out ψ_r F₂
  have hc0 : 0 < c := by linarith
  have h1 : σ₀ < 1 := by linarith
  have hρr_pos : 0 < ρr := by
    show 0 < P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
    have := P.hκ_ζ; positivity
  have h_norm_sq : √(σ₀ ^ 2 + η₀ ^ 2) = ‖(σ₀ : ℂ) + (η₀ : ℂ) * Complex.I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply, ← sq]
  have h4ρ_ge : 2 * √(σ₀ ^ 2 + η₀ ^ 2) ≤ 4 * ρr := by
    rw [h_norm_sq]; linarith
  have hsgn_abs : |sgn| = 1 := by rcases hsgn with rfl | rfl <;> norm_num
  have hQ_bd : ∀ τ : ℝ, |stripPoissonQ σ₀ η₀ ε τ| ≤ 1 / σ₀ := fun τ =>
    (stripPoissonQ_abs_le hσ₀ h1 η₀ hε τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le η₀ τ)
  let h₂ : ℝ → ℂ := fun τ => (ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
    (tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ))
  let φ : ℝ → ℝ := fun y => -sgn * edgePhi (hankelBandMu ξ) y
  let φ' : ℝ → ℝ := fun y => sgn * (hankelEdgeM y - hankelBandMu ξ)
  let φ'' : ℝ → ℝ := fun y => sgn * hankelEdgeM' y
  have hF₂_eq : ∀ τ : ℝ, F₂ τ = h₂ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ)) := by
    intro τ
    dsimp [F₂, h₂, φ, hankelBandK, hankelBandPhi]
    have hμ_eq : hankelBandMu ξ = Real.log (Real.pi ^ 2 * ξ) := by
      unfold hankelBandMu; rw [ite_eq_left hξ]
    have hodd : edgePhi (hankelBandMu ξ) (sgn * τ) = sgn * edgePhi (hankelBandMu ξ) τ := by
      rcases hsgn with rfl | rfl
      · simp
      · simp [hankelEdgePhi_odd]
    rw [← hμ_eq, hodd]
    have hexp_eq : Complex.exp ((c : ℂ) * ((0 : ℂ) - Complex.I * ((sgn * edgePhi (hankelBandMu ξ) τ : ℝ) : ℂ))) =
        Complex.exp (Complex.I * (c : ℂ) * ((-sgn * edgePhi (hankelBandMu ξ) τ : ℝ) : ℂ)) := by
      congr 1; push_cast; ring
    rw [hexp_eq]; ring
  have hh₂_cont : Continuous h₂ := by
    have hQ : Continuous (stripPoissonQ σ₀ η₀ ε) := stripPoissonQ_continuous hσ₀ h1
    exact ((Complex.continuous_ofReal.comp (tebCutoff_continuous (4 * ρr))).mul
      (Complex.continuous_ofReal.comp (hQ.comp (continuous_const.mul continuous_id)))).mul
      ((continuous_tebAmp0 c).comp (continuous_const.mul continuous_id) |>.mul
        ((hankelEdgeAmp_continuous hc0).comp (continuous_const.mul continuous_id)))
  have hF₂_cont : Continuous F₂ := by
    have h_eq : F₂ = fun τ => h₂ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ)) :=
      funext hF₂_eq
    rw [h_eq]
    have hφ_cont : Continuous φ :=
      continuous_const.mul (continuous_iff_continuousAt.2 fun τ => (hasDerivAt_edgePhi _ τ).continuousAt)
    exact (hh₂_cont.mul continuous_const).mul
      (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hφ_cont)))
  have hInt : IntegrableOn F₂ (Ioi 0) := by
    let dom : ℝ → ℝ := fun τ => (1 / σ₀) * 4 * c ^ (5 / 6 : ℝ) * ((1 + |τ|) ^ (11 / 2 : ℝ) * Real.exp (-τ ^ 2))
    have hdom_int : Integrable dom :=
      (integrable_one_add_abs_rpow_mul_exp_neg_sq (by norm_num : (0 : ℝ) ≤ 11 / 2)).const_mul _
    refine (Integrable.mono' hdom_int hF₂_cont.aestronglyMeasurable ?_).integrableOn
    refine Eventually.of_forall fun τ => ?_
    dsimp [F₂]
    have hψ : |ψ_r τ| ≤ 1 := abs_le.2 ⟨by linarith [tebCutoff_nonneg (4 * ρr) τ], tebCutoff_le_one (4 * ρr) τ⟩
    have hQ := hQ_bd (sgn * τ)
    have hamp := norm_tebAmp0_le hc0.le (τ := sgn * τ)
    have hK_bd : ‖hankelBandK c (sgn * τ) ξ‖ ≤ 4 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
      rw [norm_hankelBandK hc0]
      have h1 := hankelEdgeAmp_bound (by linarith : 1 ≤ c) (sgn * τ)
      rw [abs_mul, hsgn_abs, one_mul] at h1
      linarith [norm_nonneg (hankelEdgeAmp' c (sgn * τ))]
    have hpow : |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) ≤
        (1 + |τ|) ^ (11 / 2 : ℝ) := by
      have h1 : |τ| ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (by linarith) (by norm_num)
      have h2 : (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) =
          (1 + |τ|) ^ (11 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith [abs_nonneg τ]), ← Real.rpow_add (by linarith [abs_nonneg τ])]
        norm_num
      calc |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)
          ≤ (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
        _ = (1 + |τ|) ^ (11 / 2 : ℝ) := h2
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
    have hsq_sgn : (sgn * τ) ^ 2 = τ ^ 2 := by
      rw [mul_pow, ← sq_abs sgn, hsgn_abs, one_pow, one_mul]
    rw [abs_mul, hsgn_abs, one_mul, hsq_sgn] at hamp
    have h12 : |ψ_r τ| * |stripPoissonQ σ₀ η₀ ε (sgn * τ)| ≤ 1 * (1 / σ₀) :=
      mul_le_mul hψ hQ (abs_nonneg _) zero_le_one
    have h34 : ‖tebAmp0 c (sgn * τ)‖ * ‖hankelBandK c (sgn * τ) ξ‖ ≤
        (c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) *
          (4 * (1 + |τ|) ^ (1 / 2 : ℝ)) :=
      mul_le_mul hamp hK_bd (norm_nonneg _) (by positivity)
    calc |ψ_r τ| * |stripPoissonQ σ₀ η₀ ε (sgn * τ)| *
          ‖tebAmp0 c (sgn * τ)‖ * ‖hankelBandK c (sgn * τ) ξ‖
        = (|ψ_r τ| * |stripPoissonQ σ₀ η₀ ε (sgn * τ)|) *
            (‖tebAmp0 c (sgn * τ)‖ * ‖hankelBandK c (sgn * τ) ξ‖) := by ring
      _ ≤ (1 * (1 / σ₀)) *
            ((c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) *
              (4 * (1 + |τ|) ^ (1 / 2 : ℝ))) :=
          mul_le_mul h12 h34 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (1 / σ₀) * 4 * c ^ (5 / 6 : ℝ) *
            ((|τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)) *
              Real.exp (-τ ^ 2)) := by ring
      _ ≤ (1 / σ₀) * 4 * c ^ (5 / 6 : ℝ) * ((1 + |τ|) ^ (11 / 2 : ℝ) * Real.exp (-τ ^ 2)) := by
          gcongr
  refine ⟨hInt, ?_⟩
  have h_eq_Ioi : ∫ τ in Ioi (0 : ℝ), F₂ τ = ∫ τ in Ioi (8 * ρr), F₂ τ := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    by_cases hτ : 0 < τ
    · by_cases hτ8 : 8 * ρr < τ
      · rw [Set.indicator_of_mem hτ, Set.indicator_of_mem hτ8]
      · have hzero : tebCutoff (4 * ρr) τ = 0 :=
          tebCutoff_eq_zero (by positivity) (by rw [abs_of_pos hτ]; linarith [not_lt.1 hτ8])
        rw [Set.indicator_of_mem hτ, Set.indicator_of_notMem hτ8]
        simp [F₂, ψ_r, hzero]
    · have h8 : ¬ (8 * ρr < τ) := fun h => hτ (lt_trans (by positivity) h)
      rw [Set.indicator_of_notMem hτ, Set.indicator_of_notMem h8]
  rw [h_eq_Ioi]
  set C_bv : ℝ := 240 * 8704
  have hh₂_bv : ∀ s : ℝ, 4 * ρr ≤ s → BoundedVariationOn h₂ (Icc s (2 * s)) ∧
      (∀ τ ∈ Icc s (2 * s), ‖h₂ τ‖ + (eVariationOn h₂ (Icc s (2 * s))).toReal ≤
        C_bv * σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
          (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2)) := by
    intro s hs_ge
    have hs : 0 < s := lt_of_lt_of_le (by positivity) hs_ge
    have hs_le : s ≤ 2 * s := by linarith
    have hf1_bd : ∀ τ ∈ Icc s (2 * s), ‖(ψ_r τ : ℂ)‖ ≤ 1 := fun τ _ => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [tebCutoff_nonneg (4 * ρr) τ], tebCutoff_le_one (4 * ρr) τ⟩
    have hf1_bv : eVariationOn (fun τ => (ψ_r τ : ℂ)) (Icc s (2 * s)) ≤ ENNReal.ofReal 1 := by
      rw [eVariationOn_ofReal]; exact tebCutoff_eVariationOn_le (by positivity) hs.le hs_le
    obtain ⟨hq_norm, hq_bv⟩ := stripPoissonQ_block_bv_le hσ₀ hσ₀_le hε hsgn_abs (h4ρ_ge.trans hs_ge)
    set qJ := 4 * σ₀ * (1 + s ^ (-2 : ℝ)) * Real.exp (-π * s / 4)
    have hqJ_nn : 0 ≤ qJ := by dsimp [qJ]; positivity
    have h2π_bd : 2 * π * (s + 2) ≤ 14 * (1 + s) := by
      have := Real.pi_lt_d2; nlinarith [hs.le]
    have hq_norm' : ∀ τ ∈ Icc s (2 * s), ‖(stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ qJ := hq_norm
    have hq_bv' : eVariationOn (fun τ : ℝ => (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)) (Icc s (2 * s)) ≤
        ENNReal.ofReal (14 * (1 + s) * qJ) :=
      hq_bv.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h2π_bd hqJ_nn))
    have hq_norm_s : ∀ τ ∈ Icc s (2 * s), ‖(stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ (1 + s) * qJ :=
      fun τ hτ => (hq_norm' τ hτ).trans (le_mul_of_one_le_left hqJ_nn (by linarith))
    have h12 := bv_norm_add_tv_mul zero_le_one (by positivity) zero_le_one (by positivity)
      hf1_bd hq_norm_s hf1_bv hq_bv'
    have hf12_bd : ∀ τ ∈ Icc s (2 * s),
        ‖(ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ (1 + s) * qJ := fun τ hτ => by
      rw [norm_mul]
      calc ‖(ψ_r τ : ℂ)‖ * ‖(stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖
          ≤ 1 * ((1 + s) * qJ) := mul_le_mul (hf1_bd τ hτ) (hq_norm_s τ hτ) (norm_nonneg _) zero_le_one
        _ = (1 + s) * qJ := one_mul _
    have h12_tv_le : eVariationOn (fun τ => (ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ))
        (Icc s (2 * s)) ≤ ENNReal.ofReal (15 * (1 + s) * qJ) :=
      h12.2.1.trans (ENNReal.ofReal_le_ofReal (by
        have : 1 * (14 * (1 + s) * qJ) + (1 + s) * qJ * 1 = 15 * (1 + s) * qJ := by ring
        linarith))
    have hexp_pi : Real.exp (-π * s / 4) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, hs.le])
    have hqJ_le : qJ ≤ 4 * σ₀ * (1 + s ^ (-2 : ℝ)) := by
      dsimp [qJ]; exact mul_le_of_le_one_right (by positivity) hexp_pi
    have hf12_bd'' : ∀ τ ∈ Icc s (2 * s),
        ‖(ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ)‖ ≤ 60 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ)) :=
      fun τ hτ => (hf12_bd τ hτ).trans (by
        calc (1 + s) * qJ ≤ (1 + s) * (4 * σ₀ * (1 + s ^ (-2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hqJ_le (by linarith)
          _ = 4 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ)) := by ring
          _ ≤ 60 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ)) := by
              have : 0 ≤ σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ)) := by positivity
              linarith)
    have h12_tv' : eVariationOn (fun τ => (ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ))
        (Icc s (2 * s)) ≤ ENNReal.ofReal (60 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ))) :=
      h12_tv_le.trans (ENNReal.ofReal_le_ofReal (by
        calc 15 * (1 + s) * qJ ≤ 15 * (1 + s) * (4 * σ₀ * (1 + s ^ (-2 : ℝ))) :=
              mul_le_mul_of_nonneg_left hqJ_le (by positivity)
          _ = 60 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ)) := by ring))
    obtain ⟨hamp_bv, hamp_ev, hamp_all⟩ := tebAmp0_mul_edgeAmp_block_bv_le hc hsgn_abs hs
    set Mamp := 8704 * c ^ (5 / 6 : ℝ) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (6 : ℝ) * Real.exp (-s ^ 2)
    have hMamp_nn : 0 ≤ Mamp := by dsimp [Mamp]; positivity
    have hamp_bd : ∀ τ ∈ Icc s (2 * s),
        ‖tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ)‖ ≤ Mamp := fun τ hτ => by
      have := hamp_all τ hτ
      have htv : 0 ≤ (eVariationOn (fun t => tebAmp0 c (sgn * t) * hankelEdgeAmp c (sgn * t))
          (Icc s (2 * s))).toReal := ENNReal.toReal_nonneg
      dsimp [Mamp] at *; linarith
    have htot := bv_norm_add_tv_mul (by positivity) hMamp_nn (by positivity) hMamp_nn
      hf12_bd'' hamp_bd h12_tv' hamp_ev
    have heq_h2 : (fun τ => (ψ_r τ : ℂ) * (stripPoissonQ σ₀ η₀ ε (sgn * τ) : ℂ) *
        (tebAmp0 c (sgn * τ) * hankelEdgeAmp c (sgn * τ))) = h₂ := rfl
    refine ⟨heq_h2 ▸ htot.1, fun τ hτ => ?_⟩
    have hb := htot.2.2 τ hτ
    have h1s7 : (1 + s) * (1 + s) ^ (6 : ℝ) = (1 + s) ^ (7 : ℝ) := by
      calc (1 + s) * (1 + s) ^ (6 : ℝ)
          = (1 + s) ^ (1 : ℝ) * (1 + s) ^ (6 : ℝ) := by rw [Real.rpow_one]
        _ = (1 + s) ^ (7 : ℝ) := by rw [← Real.rpow_add (by linarith)]; norm_num
    have h_nn_rhs : 0 ≤ σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
        (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) := by positivity
    calc ‖h₂ τ‖ + (eVariationOn h₂ (Icc s (2 * s))).toReal
        ≤ (60 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ)) + 60 * σ₀ * (1 + s) * (1 + s ^ (-2 : ℝ))) *
            (Mamp + Mamp) := hb
      _ = (240 * 8704) * (σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
            ((1 + s) * (1 + s) ^ (6 : ℝ)) * Real.exp (-s ^ 2)) := by dsimp [Mamp]; ring
      _ = (240 * 8704) * (σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
            (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2)) := by rw [h1s7]
      _ ≤ C_bv * (σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
            (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2)) :=
          mul_le_mul_of_nonneg_right (by dsimp [C_bv]; norm_num) h_nn_rhs
      _ = _ := by ring
  obtain ⟨hφ, hφ', hφ'_mono, h_upper, h_lower, h_mid⟩ := hankel_phase_bounds hsgn hξ
  have hφ'_cont : ContinuousOn φ' (Ioi 0) :=
    fun y hy => (hφ' y hy).continuousAt.continuousWithinAt
  have hvdc1_out : ∀ s u v lam : ℝ, 4 * ρr ≤ s → s ≤ u → u ≤ v → v ≤ 2 * s → 0 < lam →
      (∀ τ ∈ Icc u v, lam ≤ |φ' τ|) →
      ‖∫ τ in u..v, F₂ τ‖ ≤
        (3 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ)) / lam) *
          (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) := by
    intro s u v lam hs_ge hsu huv hv2s hlam hlb
    have hs : 0 < s := lt_of_lt_of_le (by positivity) hs_ge
    have hsub : Icc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hs (hsu.trans hτ.1)
    have hsub_s : Icc u v ⊆ Icc s (2 * s) := Icc_subset_Icc hsu hv2s
    have hbv_s := (hh₂_bv s hs_ge).1
    have hbv_uv : BoundedVariationOn h₂ (Icc u v) := hbv_s.mono hsub_s
    have htv_uv : (eVariationOn h₂ (Icc u v)).toReal ≤ (eVariationOn h₂ (Icc s (2 * s))).toReal :=
      ENNReal.toReal_mono hbv_s (eVariationOn.mono h₂ hsub_s)
    set B := C_bv * σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
      (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2)
    have hvdc := van_der_corput_first_comp (w := id) (w' := fun _ => 1)
      (M := B - (eVariationOn h₂ (Icc s (2 * s))).toReal)
      huv hc0 hlam (fun x _ => hasDerivAt_id x) continuousOn_const (fun _ _ => zero_le_one)
      (fun y hy => hφ y (hsub hy)) (hφ'_cont.mono hsub)
      (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub)) (fun ha => Or.inr (ha.mono hsub)))
      hlb hh₂_cont.continuousOn hbv_uv
      (fun τ hτ => by linarith [(hh₂_bv s hs_ge).2 τ (hsub_s hτ)])
    have hF_rw : (fun x => h₂ x * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ x : ℂ))) = F₂ :=
      funext fun τ => (hF₂_eq τ).symm
    change ‖∫ τ in u..v, h₂ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ))‖ ≤ _ at hvdc
    rw [hF_rw] at hvdc
    have hc_comb : c ^ (5 / 6 : ℝ) / c = c ^ (-(1 / 6 : ℝ)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
    calc ‖∫ τ in u..v, F₂ τ‖
        ≤ 3 * ((B - (eVariationOn h₂ (Icc s (2 * s))).toReal) + (eVariationOn h₂ (Icc u v)).toReal) / (c * lam) := hvdc
      _ ≤ 3 * B / (c * lam) := by gcongr; linarith
      _ = (3 * C_bv * σ₀ * (c ^ (5 / 6 : ℝ) / c) / lam) *
            (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) := by
          dsimp [B]; ring
      _ = _ := by rw [hc_comb]
  set a := 8 * ρr
  set τ₀ := hankelBandTau0 ξ
  have ha_pos : 0 < a := by positivity
  set C_f : ℝ := 96 * C_bv * 2 ^ 9 * (Nat.factorial 6 : ℝ)
  set C_s : ℝ := 128 * C_bv * 2 ^ 10 * (Nat.factorial 7 : ℝ)
  have hfin_bd : ∀ B : ℝ, a ≤ B →
      ‖∫ τ in a..B, F₂ τ‖ ≤
        C_out * σ₀ * c ^ (5 / 6 : ℝ) *
          (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)) + c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0)) := by
    intro B haB
    set x₁ := min B (max a (τ₀ / 2))
    set x₂ := min B (max a (2 * τ₀))
    have ha_le_x1 : a ≤ x₁ := le_min haB (le_max_left _ _)
    have hx1_le_x2 : x₁ ≤ x₂ := min_le_min_left B (max_le_max_left a (by linarith [hankelBandTau0_nonneg ξ]))
    have hx2_le_B : x₂ ≤ B := min_le_left _ _
    have hsplit3 : ∫ τ in a..B, F₂ τ =
        (∫ τ in a..x₁, F₂ τ) + (∫ τ in x₁..x₂, F₂ τ) + (∫ τ in x₂..B, F₂ τ) := by
      have h1 := intervalIntegral.integral_add_adjacent_intervals
        (hF₂_cont.intervalIntegrable (μ := volume) a x₁) (hF₂_cont.intervalIntegrable (μ := volume) x₁ x₂)
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hF₂_cont.intervalIntegrable (μ := volume) a x₂) (hF₂_cont.intervalIntegrable (μ := volume) x₂ B)
      rw [← h1] at h2; exact h2.symm
    set G₂ := C_f * σ₀ * c ^ (-(1 / 6 : ℝ))
    have hG₂_nn : 0 ≤ G₂ := by dsimp [G₂, C_f, C_bv]; positivity
    have hlow_bd : ‖∫ τ in a..x₁, F₂ τ‖ ≤ 2 * G₂ * a ^ (-(3 / 2 : ℝ)) := by
      rcases eq_or_lt_of_le ha_le_x1 with heq | hlt_ax1
      · rw [← heq, intervalIntegral.integral_same, norm_zero]; positivity
      · have hx1_le_half : x₁ ≤ τ₀ / 2 := by
          have h1 : a < max a (τ₀ / 2) := lt_of_lt_of_le hlt_ax1 (min_le_right _ _)
          have h2 : max a (τ₀ / 2) = τ₀ / 2 := by
            rcases max_choice a (τ₀ / 2) with h | h
            · rw [h] at h1; exact absurd h1 (lt_irrefl _)
            · exact h
          exact (min_le_right _ _).trans_eq h2
        have hτ₀_pos : 0 < τ₀ := by linarith [ha_pos]
        exact dyadic_sum_rpow_neg_three_halves_le ha_pos ha_le_x1 hG₂_nn F₂
          (hF₂_cont.intervalIntegrable a x₁) (fun s u v hs hau huv hvx hsu hv2s => by
            have hs_ge : 4 * ρr ≤ s := by linarith [hau]
            have hmin_le : min (s ^ 2) 1 ≤ min (τ₀ ^ 2) 1 := by
              have hs_τ₀ : s ≤ τ₀ := by linarith [hvx.trans hx1_le_half]
              exact min_le_min_right 1 (pow_le_pow_left₀ hs.le hs_τ₀ 2)
            have hlam_pos : 0 < (1 / 32 : ℝ) * min (s ^ 2) 1 := by
              rcases le_total (s ^ 2) 1 <;> positivity
            have hlb : ∀ τ ∈ Icc u v, (1 / 32 : ℝ) * min (s ^ 2) 1 ≤ |φ' τ| := fun τ hτ => by
              have hτ_pos : 0 < τ := lt_of_lt_of_le hs (hsu.trans hτ.1)
              rcases eq_or_lt_of_le (hτ.2.trans (hvx.trans hx1_le_half)) with heq | hlt
              · have hcont : ContinuousAt (fun t => |φ' t|) τ :=
                  (hφ'_cont τ hτ_pos).abs.continuousAt (isOpen_Ioi.mem_nhds hτ_pos)
                have hev : ∀ᶠ t in 𝓝[<] τ, (1 / 32 : ℝ) * min (τ₀ ^ 2) 1 ≤ |φ' t| := by
                  filter_upwards [self_mem_nhdsWithin,
                    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hτ_pos)] with t ht1 ht2
                  exact h_lower t ht2 (by rw [← heq]; exact mem_Iio.1 ht1)
                exact (mul_le_mul_of_nonneg_left hmin_le (by norm_num)).trans
                  (ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev)
              · calc (1 / 32 : ℝ) * min (s ^ 2) 1 ≤ (1 / 32 : ℝ) * min (τ₀ ^ 2) 1 :=
                      mul_le_mul_of_nonneg_left hmin_le (by norm_num)
                  _ ≤ |φ' τ| := h_lower τ hτ_pos hlt
            have h1 := hvdc1_out s u v ((1 / 32 : ℝ) * min (s ^ 2) 1) hs_ge hsu huv hv2s hlam_pos hlb
            have hop := outer_rpow_poly_exp_le hs
            have hC_nn : 0 ≤ 96 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ)) := by dsimp [C_bv]; positivity
            calc ‖∫ τ in u..v, F₂ τ‖
                ≤ (96 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ))) *
                    ((1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) /
                      min (s ^ 2) 1) := by refine h1.trans_eq ?_; ring
              _ ≤ (96 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ))) *
                    (2 ^ 9 * (Nat.factorial 6 : ℝ) * s ^ (-(3 / 2 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hop hC_nn
              _ = G₂ * s ^ (-(3 / 2 : ℝ)) := by dsimp [G₂, C_f]; ring)
    have hup_bd : ‖∫ τ in x₂..B, F₂ τ‖ ≤ 2 * G₂ * a ^ (-(3 / 2 : ℝ)) := by
      rcases eq_or_lt_of_le hx2_le_B with heq | hlt_x2B
      · rw [heq, intervalIntegral.integral_same, norm_zero]; positivity
      · have hx2_ge : 2 * τ₀ ≤ x₂ := by
          have hlt : max a (2 * τ₀) < B := by
            by_contra hle
            have : x₂ = B := min_eq_left (not_lt.1 hle)
            linarith
          show 2 * τ₀ ≤ min B (max a (2 * τ₀))
          rw [min_eq_right hlt.le]
          exact le_max_right _ _
        have hx2_pos : 0 < x₂ := lt_of_lt_of_le ha_pos (ha_le_x1.trans hx1_le_x2)
        have hsum := dyadic_sum_rpow_neg_three_halves_le hx2_pos hx2_le_B hG₂_nn F₂
          (hF₂_cont.intervalIntegrable x₂ B) (fun s u v hs hxu huv hvB hsu hv2s => by
            have hs_ge : 4 * ρr ≤ s := by linarith [ha_le_x1.trans hx1_le_x2, hxu]
            have hlam_pos : 0 < (1 / 32 : ℝ) * min (s ^ 2) 1 := by
              rcases le_total (s ^ 2) 1 <;> positivity
            have hlb : ∀ τ ∈ Icc u v, (1 / 32 : ℝ) * min (s ^ 2) 1 ≤ |φ' τ| := fun τ hτ => by
              have hτ_pos : 0 < τ := lt_of_lt_of_le hs (hsu.trans hτ.1)
              have hs2_τ : min (s ^ 2) 1 ≤ min (τ ^ 2) 1 :=
                min_le_min_right 1 (pow_le_pow_left₀ hs.le (hsu.trans hτ.1) 2)
              rcases eq_or_lt_of_le (hx2_ge.trans (hxu.trans hτ.1)) with heq | hlt
              · have hcont : ContinuousAt (fun t => |φ' t|) τ :=
                  (hφ'_cont τ hτ_pos).abs.continuousAt (isOpen_Ioi.mem_nhds hτ_pos)
                have hev : ∀ᶠ t in 𝓝[>] τ, (1 / 32 : ℝ) * min (t ^ 2) 1 ≤ |φ' t| := by
                  filter_upwards [self_mem_nhdsWithin] with t ht
                  exact h_upper t (by rw [heq]; exact mem_Ioi.1 ht)
                have hlim : ContinuousAt (fun t => (1 / 32 : ℝ) * min (t ^ 2) 1) τ := by fun_prop
                have hle_τ := le_of_tendsto_of_tendsto (hlim.tendsto.mono_left nhdsWithin_le_nhds)
                  (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
                exact (mul_le_mul_of_nonneg_left hs2_τ (by norm_num)).trans hle_τ
              · calc (1 / 32 : ℝ) * min (s ^ 2) 1 ≤ (1 / 32 : ℝ) * min (τ ^ 2) 1 :=
                      mul_le_mul_of_nonneg_left hs2_τ (by norm_num)
                  _ ≤ |φ' τ| := h_upper τ hlt
            have h1 := hvdc1_out s u v ((1 / 32 : ℝ) * min (s ^ 2) 1) hs_ge hsu huv hv2s hlam_pos hlb
            have hop := outer_rpow_poly_exp_le hs
            have hC_nn : 0 ≤ 96 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ)) := by dsimp [C_bv]; positivity
            calc ‖∫ τ in u..v, F₂ τ‖
                ≤ (96 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ))) *
                    ((1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) /
                      min (s ^ 2) 1) := by refine h1.trans_eq ?_; ring
              _ ≤ (96 * C_bv * σ₀ * c ^ (-(1 / 6 : ℝ))) *
                    (2 ^ 9 * (Nat.factorial 6 : ℝ) * s ^ (-(3 / 2 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hop hC_nn
              _ = G₂ * s ^ (-(3 / 2 : ℝ)) := by dsimp [G₂, C_f]; ring)
        have hax2 : x₂ ^ (-(3 / 2 : ℝ)) ≤ a ^ (-(3 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos ha_pos (ha_le_x1.trans hx1_le_x2) (by norm_num)
        exact hsum.trans (mul_le_mul_of_nonneg_left hax2 (by positivity))
    have hmid_bd : ‖∫ τ in x₁..x₂, F₂ τ‖ ≤
        2 * C_s * σ₀ * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0) := by
      by_cases hcond : 4 * ρr < τ₀
      · rw [ite_eq_left hcond, mul_one]
        have hτ₀_pos : 0 < τ₀ := lt_trans (by positivity) hcond
        by_cases hB : B < τ₀ / 2
        · have hx1 : x₁ = B := min_eq_left (le_trans hB.le (le_max_right _ _))
          have hx2 : x₂ = B := min_eq_left (le_trans (by linarith only [hB, hτ₀_pos]) (le_max_right _ _))
          rw [hx1, hx2, intervalIntegral.integral_same, norm_zero]
          have hC_s_nn : 0 ≤ C_s := by dsimp [C_s, C_bv]; positivity
          positivity
        · have hB_ge : τ₀ / 2 ≤ B := not_lt.1 hB
          have hx1_ge : τ₀ / 2 ≤ x₁ := le_min hB_ge (le_max_right _ _)
          have hx2_le : x₂ ≤ 2 * τ₀ := (min_le_right _ _).trans (max_le (by dsimp [a]; linarith only [hcond]) le_rfl)
          set m := min x₂ (max x₁ τ₀)
          have hx1_m : x₁ ≤ m := le_min hx1_le_x2 (le_max_left _ _)
          have hm_x2 : m ≤ x₂ := min_le_left _ _
          have hsplit_m : ∫ τ in x₁..x₂, F₂ τ = (∫ τ in x₁..m, F₂ τ) + ∫ τ in m..x₂, F₂ τ :=
            (intervalIntegral.integral_add_adjacent_intervals
              (hF₂_cont.intervalIntegrable (μ := volume) x₁ m)
              (hF₂_cont.intervalIntegrable (μ := volume) m x₂)).symm
          have hvdc2_out : ∀ {u v s : ℝ}, 4 * ρr ≤ s → τ₀ / 2 ≤ u → u ≤ v → v ≤ 2 * τ₀ →
              s ≤ u → v ≤ 2 * s → (1 + τ₀ ^ 3 ≤ 8 * (1 + s ^ 3) ∧ s ≤ τ₀) →
              ‖∫ τ in u..v, F₂ τ‖ ≤ C_s * σ₀ * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
            intro u v s hs_ge hu_lo huv hv_hi hsu hv2s ⟨hden1, hs_le⟩
            have hs : 0 < s := lt_of_lt_of_le (by positivity) hs_ge
            have hsub : Icc u v ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le (half_pos hτ₀_pos) (hu_lo.trans hτ.1)
            have hsub_s : Icc u v ⊆ Icc s (2 * s) := Icc_subset_Icc hsu hv2s
            have hbv_s := (hh₂_bv s hs_ge).1
            have hbv_uv : BoundedVariationOn h₂ (Icc u v) := hbv_s.mono hsub_s
            have htv_uv : (eVariationOn h₂ (Icc u v)).toReal ≤ (eVariationOn h₂ (Icc s (2 * s))).toReal :=
              ENNReal.toReal_mono hbv_s (eVariationOn.mono h₂ hsub_s)
            set B' := C_bv * σ₀ * c ^ (5 / 6 : ℝ) * (1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) *
              (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2)
            have hlam_pos : 0 < (1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3) := by positivity
            have hvdc := van_der_corput_second_comp (w := id) (w' := fun _ => 1)
              (M := B' - (eVariationOn h₂ (Icc s (2 * s))).toReal)
              huv hc0 hlam_pos (fun x _ => hasDerivAt_id x) continuousOn_const (fun _ _ => zero_le_one)
              (fun y hy => hφ y (hsub hy)) (fun y hy => hφ' y (hsub hy))
              (Or.elim hφ'_mono (fun hm => Or.inl (hm.mono hsub)) (fun ha => Or.inr (ha.mono hsub)))
              (fun y hy => h_mid hτ₀_pos y (hu_lo.trans hy.1) (hy.2.trans hv_hi))
              hh₂_cont.continuousOn hbv_uv
              (fun τ hτ => le_sub_iff_add_le.2 ((hh₂_bv s hs_ge).2 τ (hsub_s hτ)))
            have hF_rw : (fun x => h₂ x * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ x : ℂ))) = F₂ :=
              funext fun τ => (hF₂_eq τ).symm
            change ‖∫ τ in u..v, h₂ τ * (1 : ℂ) * Complex.exp (Complex.I * (c : ℂ) * (φ τ : ℂ))‖ ≤ _ at hvdc
            rw [hF_rw] at hvdc
            have hτ_gt_s : (1 / 8 : ℝ) * (s / (1 + s ^ 3)) ≤ τ₀ / (1 + τ₀ ^ 3) := by
              rw [show (1 / 8 : ℝ) * (s / (1 + s ^ 3)) = (s / 8) / (1 + s ^ 3) by ring,
                div_le_div_iff₀ (by positivity) (by positivity)]
              have h1 : s * (1 + τ₀ ^ 3) ≤ s * (8 * (1 + s ^ 3)) := mul_le_mul_of_nonneg_left hden1 hs.le
              have h2 : s * (8 * (1 + s ^ 3)) ≤ 8 * τ₀ * (1 + s ^ 3) := by
                nlinarith [pow_pos hs 3]
              calc (s / 8) * (1 + τ₀ ^ 3) = (s * (1 + τ₀ ^ 3)) / 8 := by ring
                _ ≤ (s * (8 * (1 + s ^ 3))) / 8 := div_le_div_of_nonneg_right h1 (by norm_num)
                _ ≤ (8 * τ₀ * (1 + s ^ 3)) / 8 := div_le_div_of_nonneg_right h2 (by norm_num)
                _ = τ₀ * (1 + s ^ 3) := by ring
            have hlam_lb : (1 / 256 : ℝ) * (s / (1 + s ^ 3)) ≤ (1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3) := by
              calc (1 / 256 : ℝ) * (s / (1 + s ^ 3))
                  = (1 / 32 : ℝ) * ((1 / 8 : ℝ) * (s / (1 + s ^ 3))) := by ring
                _ ≤ (1 / 32 : ℝ) * (τ₀ / (1 + τ₀ ^ 3)) := mul_le_mul_of_nonneg_left hτ_gt_s (by norm_num)
                _ = (1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3) := by ring
            have hden_sqrt : (1 / 16 : ℝ) * Real.sqrt (c * (s / (1 + s ^ 3))) ≤
                Real.sqrt (c * ((1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3))) := by
              rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 16), ← Real.sqrt_mul (by norm_num)]
              apply Real.sqrt_le_sqrt
              have : (1 / 16 : ℝ) ^ 2 * (c * (s / (1 + s ^ 3))) ≤
                  c * ((1 / 256 : ℝ) * (s / (1 + s ^ 3))) := by ring_nf; rfl
              exact this.trans (mul_le_mul_of_nonneg_left hlam_lb hc0.le)
            have hden_eq : (1 / 16 : ℝ) * Real.sqrt (c * (s / (1 + s ^ 3))) =
                (1 / 16 : ℝ) * (c ^ (1 / 2 : ℝ) * Real.sqrt (s / (1 + s ^ 3))) := by
              rw [Real.sqrt_mul hc0.le, Real.sqrt_eq_rpow]
            have hc_comb : c ^ (5 / 6 : ℝ) / c ^ (1 / 2 : ℝ) = c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
              rw [div_eq_mul_inv, Real.rpow_neg hc0.le]
            have hos := outer_saddle_factor_le hs
            have h_pref_nn : 0 ≤ 128 * C_bv * σ₀ * (c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ))) := by
              dsimp [C_bv]; positivity
            calc ‖∫ τ in u..v, F₂ τ‖
                ≤ 8 * ((B' - (eVariationOn h₂ (Icc s (2 * s))).toReal) + (eVariationOn h₂ (Icc u v)).toReal) /
                    Real.sqrt (c * ((1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3))) := hvdc
              _ ≤ 8 * B' / Real.sqrt (c * ((1 / 32 : ℝ) * τ₀ / (1 + τ₀ ^ 3))) := by gcongr; linarith only [htv_uv]
              _ ≤ 8 * B' / ((1 / 16 : ℝ) * (c ^ (1 / 2 : ℝ) * Real.sqrt (s / (1 + s ^ 3)))) := by
                  refine div_le_div_of_nonneg_left (by dsimp [B', C_bv]; positivity) (by positivity) ?_
                  rw [← hden_eq]; exact hden_sqrt
              _ = (128 * C_bv * σ₀ * (c ^ (5 / 6 : ℝ) / c ^ (1 / 2 : ℝ))) *
                    ((1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) /
                      Real.sqrt (s / (1 + s ^ 3))) := by dsimp [B']; ring
              _ = (128 * C_bv * σ₀ * (c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)))) *
                    ((1 + s ^ (-2 : ℝ)) * s ^ (5 / 2 : ℝ) * (1 + s) ^ (7 : ℝ) * Real.exp (-s ^ 2) /
                      Real.sqrt (s / (1 + s ^ 3))) := by rw [hc_comb]
              _ ≤ (128 * C_bv * σ₀ * (c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)))) * (2 ^ 10 * (Nat.factorial 7 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hos h_pref_nn
              _ = C_s * σ₀ * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by dsimp [C_s]; ring
          have h_left : ‖∫ τ in x₁..m, F₂ τ‖ ≤ C_s * σ₀ * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
            rcases le_or_gt τ₀ x₁ with hτx | hxτ
            · have hm_eq : m = x₁ := by
                show min x₂ (max x₁ τ₀) = x₁
                rw [max_eq_left hτx]; exact min_eq_right hx1_le_x2
              rw [hm_eq, intervalIntegral.integral_same, norm_zero]; dsimp [C_s, C_bv]; positivity
            · have hτ8 : 4 * ρr ≤ τ₀ / 2 := by
                have hax : a ≤ x₁ := ha_le_x1
                linarith only [hax, hxτ, show a = 8 * ρr from rfl]
              have hm_le : m ≤ τ₀ := (min_le_right _ _).trans (max_le hxτ.le le_rfl)
              refine hvdc2_out hτ8 hx1_ge hx1_m (hm_le.trans (by linarith only [hτ₀_pos]))
                hx1_ge (by linarith only [hm_le]) ⟨?_, by linarith only [hτ₀_pos]⟩
              have : 1 + τ₀ ^ 3 = 1 + 8 * (τ₀ / 2) ^ 3 := by ring
              linarith only [this]
          have h_right : ‖∫ τ in m..x₂, F₂ τ‖ ≤ C_s * σ₀ * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) := by
            rcases le_or_gt x₂ τ₀ with hxτ | hτx
            · have hm_eq : m = x₂ := by
                show min x₂ (max x₁ τ₀) = x₂
                exact min_eq_left (hxτ.trans (le_max_right _ _))
              rw [hm_eq, intervalIntegral.integral_same, norm_zero]; dsimp [C_s, C_bv]; positivity
            · have hm_ge : τ₀ ≤ m := le_min hτx.le (le_max_right _ _)
              refine hvdc2_out hcond.le (by linarith only [hm_ge, hτ₀_pos]) hm_x2 hx2_le hm_ge hx2_le ⟨?_, le_rfl⟩
              linarith only [pow_nonneg hτ₀_pos.le 3]
          calc ‖∫ τ in x₁..x₂, F₂ τ‖
              ≤ ‖∫ τ in x₁..m, F₂ τ‖ + ‖∫ τ in m..x₂, F₂ τ‖ := by rw [hsplit_m]; exact norm_add_le _ _
            _ ≤ _ := by linarith only [h_left, h_right]
      · rw [ite_eq_right hcond, mul_zero]
        have hx_eq : x₁ = x₂ := by
          have hle : τ₀ ≤ 4 * ρr := not_lt.1 hcond
          have hx1 : x₁ = a := by
            show min B (max a (τ₀ / 2)) = a
            rw [max_eq_left (by linarith), min_eq_right haB]
          have hx2 : x₂ = a := by
            show min B (max a (2 * τ₀)) = a
            rw [max_eq_left (by linarith), min_eq_right haB]
          rw [hx1, hx2]
        rw [hx_eq, intervalIntegral.integral_same, norm_zero]
    have ha_pow : a ^ (-(3 / 2 : ℝ)) ≤ ρr ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hρr_pos (by dsimp [a]; linarith) (by norm_num)
    have htri : ‖∫ τ in a..B, F₂ τ‖ ≤
        ‖∫ τ in a..x₁, F₂ τ‖ + ‖∫ τ in x₁..x₂, F₂ τ‖ + ‖∫ τ in x₂..B, F₂ τ‖ := by
      rw [hsplit3]; exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hc_comb' : c ^ (-(1 / 6 : ℝ)) = c ^ (5 / 6 : ℝ) * c⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hc0]; norm_num
    have hCf_le : 4 * C_f ≤ C_out := by
      dsimp [C_f, C_bv, C_out]; norm_num [Nat.factorial]
    have hCs_le : 2 * C_s ≤ C_out := by
      dsimp [C_s, C_bv, C_out]; norm_num [Nat.factorial]
    have h1_nn : 0 ≤ c⁻¹ * ρr ^ (-(3 / 2 : ℝ)) := by positivity
    have h2_nn : 0 ≤ c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0) := by split_ifs <;> positivity
    calc ‖∫ τ in a..B, F₂ τ‖
        ≤ ‖∫ τ in a..x₁, F₂ τ‖ + ‖∫ τ in x₁..x₂, F₂ τ‖ + ‖∫ τ in x₂..B, F₂ τ‖ := htri
      _ ≤ 2 * G₂ * a ^ (-(3 / 2 : ℝ)) +
            2 * C_s * σ₀ * c ^ (5 / 6 : ℝ) * c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0) +
            2 * G₂ * a ^ (-(3 / 2 : ℝ)) := add_le_add (add_le_add hlow_bd hmid_bd) hup_bd
      _ ≤ 4 * C_f * σ₀ * c ^ (-(1 / 6 : ℝ)) * ρr ^ (-(3 / 2 : ℝ)) +
            2 * C_s * σ₀ * c ^ (5 / 6 : ℝ) * (c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0)) := by
          have h4 : 2 * G₂ * a ^ (-(3 / 2 : ℝ)) + 2 * G₂ * a ^ (-(3 / 2 : ℝ)) ≤
              4 * G₂ * ρr ^ (-(3 / 2 : ℝ)) := by
            have h1 := mul_le_mul_of_nonneg_left ha_pow hG₂_nn
            linarith only [h1]
          dsimp [G₂] at h4 ⊢
          linarith only [h4]
      _ = 4 * C_f * σ₀ * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) +
            2 * C_s * σ₀ * c ^ (5 / 6 : ℝ) * (c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0)) := by
          rw [hc_comb']; ring
      _ ≤ C_out * σ₀ * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) +
            C_out * σ₀ * c ^ (5 / 6 : ℝ) * (c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0)) := by
          have h01 : 0 ≤ σ₀ * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) :=
            mul_nonneg (mul_nonneg hσ₀.le (Real.rpow_nonneg hc0.le _)) h1_nn
          have h02 : 0 ≤ σ₀ * c ^ (5 / 6 : ℝ) * (c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0)) :=
            mul_nonneg (mul_nonneg hσ₀.le (Real.rpow_nonneg hc0.le _)) h2_nn
          have t1 : (4 * C_f) * (σ₀ * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)))) ≤
              C_out * (σ₀ * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_right hCf_le h01
          have t2 : (2 * C_s) * (σ₀ * c ^ (5 / 6 : ℝ) * (c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0))) ≤
              C_out * (σ₀ * c ^ (5 / 6 : ℝ) * (c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < τ₀ then 1 else 0))) :=
            mul_le_mul_of_nonneg_right hCs_le h02
          linarith only [t1, t2]
      _ = _ := by ring
  have hInt_a : IntegrableOn F₂ (Ioi a) := hInt.mono_set (Ioi_subset_Ioi (by positivity))
  have htend := (intervalIntegral_tendsto_integral_Ioi a hInt_a tendsto_id).norm
  exact le_of_tendsto htend (eventually_atTop.2 ⟨a, fun B hB => hfin_bd B hB⟩)

end ThreePieces

section Assembly

private lemma integral_real_eq_pos_add_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Integrable g) :
    ∫ τ : ℝ, g τ = (∫ τ in Ioi (0 : ℝ), g τ) + ∫ τ in Ioi (0 : ℝ), g (-τ) := by
  have h1 := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hg
  have hcompl : ∫ τ in (Ioi (0 : ℝ))ᶜ, g τ = ∫ τ in Ioi (0 : ℝ), g (-τ) := by
    rw [compl_Ioi]
    have h0 := integral_comp_neg_Ioi (0 : ℝ) g
    rw [neg_zero] at h0
    exact h0.symm
  rw [← h1, hcompl, add_comm]

private lemma scale_J_norm_le {c ε ξ M : ℝ} {ζ₀ : ℂ} {wt : ℝ → ℝ}
    (hc : 3e6 ≤ c) (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1)
    (hQ_pt : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 / ζ₀.re)
    (hwt_cont : Continuous wt) (hwt_even : ∀ τ : ℝ, wt (-τ) = wt τ) (hwt_bd : ∀ τ : ℝ, |wt τ| ≤ 1)
    (hpos : ‖∫ τ in Ioi (0 : ℝ), (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε (1 * τ) : ℂ) *
      tebAmp0 c (1 * τ) * hankelBandK c (1 * τ) ξ‖ ≤ M)
    (hneg : ‖∫ τ in Ioi (0 : ℝ), (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε (-1 * τ) : ℂ) *
      tebAmp0 c (-1 * τ) * hankelBandK c (-1 * τ) ξ‖ ≤ M) :
    ‖∫ τ : ℝ, (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
      tebAmp0 c τ * hankelBandK c τ ξ‖ ≤ 2 * M := by
  have hc0 : 0 < c := by linarith only [hc]
  have hE : Continuous (fun τ => hankelBandPhi τ ξ) := by
    have : (fun τ => hankelBandPhi τ ξ) = fun τ => Real.log (Real.pi ^ 2 * ξ) * τ + edgePhi 0 τ :=
      funext fun τ => hankelBandPhi_eq τ ξ
    rw [this]; exact (continuous_const.mul continuous_id).add continuous_edgePhi_zero
  have hKc : Continuous (fun τ => hankelBandK c τ ξ) := by
    unfold hankelBandK
    exact ((hankelEdgeAmp_continuous hc0).mul continuous_const).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (continuous_const.sub (continuous_const.mul (Complex.continuous_ofReal.comp hE)))))
  have hJ_cont : Continuous (fun τ : ℝ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
      tebAmp0 c τ * hankelBandK c τ ξ) :=
    ((Complex.continuous_ofReal.comp hwt_cont).mul
      (Complex.continuous_ofReal.comp (stripPoissonQ_continuous hσ₀ hσ₁))).mul
      (continuous_tebAmp0 c) |>.mul hKc
  have hF_dom : Integrable (fun τ : ℝ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
      tebAmp0 c τ * hankelBandK c τ ξ) := by
    have hK_bd : ∀ τ, ‖hankelBandK c τ ξ‖ ≤ 4 * (1 + |τ|) ^ (1 / 2 : ℝ) := fun τ => by
      rw [norm_hankelBandK hc0]
      have := hankelEdgeAmp_bound (by linarith only [hc] : 1 ≤ c) τ
      linarith only [this, norm_nonneg (hankelEdgeAmp' c τ)]
    let dom : ℝ → ℝ := fun τ => (1 / ζ₀.re) * 4 * c ^ (5 / 6 : ℝ) *
      ((1 + |τ|) ^ (11 / 2 : ℝ) * Real.exp (-τ ^ 2))
    have hdom_int : Integrable dom :=
      (integrable_one_add_abs_rpow_mul_exp_neg_sq (by norm_num : (0 : ℝ) ≤ 11 / 2)).const_mul _
    refine hdom_int.mono' hJ_cont.aestronglyMeasurable (ae_of_all _ fun τ => ?_)
    have hamp := norm_tebAmp0_le hc0.le (τ := τ)
    have hpow : |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) ≤
        (1 + |τ|) ^ (11 / 2 : ℝ) := by
      have h1 : |τ| ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (by linarith only) (by norm_num)
      have h2 : (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) =
          (1 + |τ|) ^ (11 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith only [abs_nonneg τ]),
          ← Real.rpow_add (by linarith only [abs_nonneg τ])]
        norm_num
      calc |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)
          ≤ (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
        _ = _ := h2
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      mul_assoc (|wt τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ|)]
    have h12 : |wt τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 * (1 / ζ₀.re) :=
      mul_le_mul (hwt_bd τ) (hQ_pt τ) (abs_nonneg _) zero_le_one
    have h34 : ‖tebAmp0 c τ‖ * ‖hankelBandK c τ ξ‖ ≤
        (c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) *
          (4 * (1 + |τ|) ^ (1 / 2 : ℝ)) := mul_le_mul hamp (hK_bd τ) (norm_nonneg _) (by positivity)
    calc |wt τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ| * (‖tebAmp0 c τ‖ * ‖hankelBandK c τ ξ‖)
        ≤ (1 * (1 / ζ₀.re)) * ((c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) *
            (4 * (1 + |τ|) ^ (1 / 2 : ℝ))) :=
          mul_le_mul h12 h34 (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
      _ = (1 / ζ₀.re) * 4 * c ^ (5 / 6 : ℝ) *
            ((|τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)) * Real.exp (-τ ^ 2)) := by ring
      _ ≤ dom τ := by dsimp [dom]; gcongr
  rw [integral_real_eq_pos_add_neg hF_dom]
  have hneg_eq : (fun τ : ℝ => (wt (-τ) : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε (-τ) : ℂ) *
        tebAmp0 c (-τ) * hankelBandK c (-τ) ξ) =
      fun τ : ℝ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε (-1 * τ) : ℂ) *
        tebAmp0 c (-1 * τ) * hankelBandK c (-1 * τ) ξ := by
    ext τ; rw [hwt_even τ]; simp only [neg_one_mul]
  have hpos_eq : (fun τ : ℝ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
        tebAmp0 c τ * hankelBandK c τ ξ) =
      fun τ : ℝ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε (1 * τ) : ℂ) *
        tebAmp0 c (1 * τ) * hankelBandK c (1 * τ) ξ := by
    ext τ; simp only [one_mul]
  rw [hneg_eq, hpos_eq]
  calc ‖(∫ τ in Ioi (0 : ℝ), _) + ∫ τ in Ioi (0 : ℝ), _‖
      ≤ ‖∫ τ in Ioi (0 : ℝ), _‖ + ‖∫ τ in Ioi (0 : ℝ), _‖ := norm_add_le _ _
    _ ≤ M + M := add_le_add hpos hneg
    _ = 2 * M := by ring

/-- Universal constant `C_Y'` in `(ct:Wbound)` (`constant_terms_lower.tex` `ct:dyadic` (1) Step 1a). -/
noncomputable def hankelScaleBandC : ℝ := 1e20

lemma hankelScaleBandC_pos : 0 < hankelScaleBandC := by unfold hankelScaleBandC; norm_num

private lemma inner_dm_pos_bound {c u_T R_J r : ℝ} {f : ℝ → ℝ} {ζ₀ : ℂ} {J₁ : ℝ → ℂ}
    (hc : 3e6 ≤ c) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hσ₀ : 0 < ζ₀.re) (hfinP : IsFiniteMeasure (hankelDmPos c f))
    (hdmPos_le : (hankelDmPos c f univ).toReal ≤ 1)
    (hJ₁_pos_int : IntegrableOn J₁ (Ioi 0) (hankelDmPos c f))
    (hJ₁_pt : ∀ ξ ∈ Ioi (0 : ℝ), ‖J₁ ξ‖ ≤
      2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) *
        (c⁻¹ * rhoR hankelBandParams c r ^ (1 / 2 : ℝ) +
          c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 *
            (if hankelBandParams.A_0 * c ^ (-(1 / 3 : ℝ)) < hankelBandTau0 ξ ∧
                hankelBandTau0 ξ < 32 * rhoR hankelBandParams c r then 1 else 0))) :
    ‖∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmPos c f‖ ≤
      2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) *
        (c⁻¹ * rhoR hankelBandParams c r ^ (1 / 2 : ℝ) +
          hankelBandParams.C_τ * c ^ (-(7 / 6 : ℝ)) *
            ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-min (1028 * r) R_J)),
              (-hankelBandU c ξ) ∂hankelDmPos c f +
          1024 * hankelBandParams.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r * hankelBootB2 c f R_J) := by
  let P := hankelBandParams
  have hc0 : 0 < c := by linarith only [hc]
  have hr0 : 0 < r := by linarith only [hr_lb]
  set δ₀ := P.A_0 * c ^ (-(1 / 3 : ℝ))
  set ρr := rhoR P c r
  set r_til := min (1028 * r) R_J
  have hr_til_pos : 0 < r_til := lt_min (by positivity) (lt_of_lt_of_le hr0 hr_RJ)
  have hr_til_RJ : r_til ≤ R_J := min_le_right _ _
  have hRJ_A : R_J ≤ langerRadius c := hRJ_ub.trans (hankelBand_radius_ge_one hc)
  have hr_til_A : r_til ≤ langerRadius c := hr_til_RJ.trans hRJ_A
  have hu_abs : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hr_til_u : -r_til ≤ u_T := by
    show -min (1028 * r) R_J ≤ u_T
    rcases le_total (1028 * r) R_J with h | h
    · rw [min_eq_left h]; linarith only [hr_lb, hu3]
    · rw [min_eq_right h]; linarith only [hr_lb, hr_RJ, hu3]
  have hr_til_neg_A : |-r_til| ≤ langerRadius c := by
    rw [abs_neg, abs_of_pos hr_til_pos]; exact hr_til_A
  have hmonoξ : hankelXi c u_T ≤ hankelXi c (-r_til) :=
    le_of_mul_le_mul_left (hankel_phi_anti hc0 hr_til_neg_A hu_abs hr_til_u) hc0
  have hRJ_neg_A : |-R_J| ≤ langerRadius c := by
    rw [abs_neg, abs_of_pos (lt_of_lt_of_le hr0 hr_RJ)]; exact hRJ_A
  have hmonoξ_RJ : hankelXi c (-r_til) ≤ hankelXi c (-R_J) :=
    le_of_mul_le_mul_left (hankel_phi_anti hc0 hRJ_neg_A hr_til_neg_A (by linarith only [hr_til_RJ])) hc0
  have hξT_pos : 0 < hankelXi c u_T := hankelXi_pos hc0 hu_abs
  let C_J1 : ℝ := 2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ)
  have hC_J1_pos : 0 < C_J1 := by positivity
  let bandSet := Icc (hankelXi c u_T) (hankelXi c (-r_til))
  let tailSet := Ici (hankelXi c (-R_J))
  let uFn : ℝ → ℝ := fun ξ => -hankelBandU c ξ
  let f₁ : ℝ → ℝ := fun _ => C_J1 * (c⁻¹ * ρr ^ (1 / 2 : ℝ))
  let f₂ : ℝ → ℝ := fun ξ => C_J1 * (P.C_τ * c ^ (-(7 / 6 : ℝ))) * bandSet.indicator uFn ξ
  let f₃ : ℝ → ℝ := fun ξ => C_J1 * (1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r) *
    tailSet.indicator (fun _ => (1 : ℝ)) ξ
  have hf₁_int : IntegrableOn f₁ (Ioi 0) (hankelDmPos c f) :=
    integrableOn_const (hs := (measure_lt_top (hankelDmPos c f) _).ne)
  have hT_wb := hankelXi_w_bounds hc0 hu_abs hu0
  have hr_wb := hankelXi_w_bounds hc0 hr_til_neg_A (by linarith only [hr_til_pos])
  have huFn_contOn : ContinuousOn uFn bandSet := by
    intro ξ hξ
    have hpi_sq_nn : 0 ≤ Real.pi ^ 2 := sq_nonneg Real.pi
    have hle1 : Real.pi ^ 2 * hankelXi c u_T ≤ Real.pi ^ 2 * ξ :=
      mul_le_mul_of_nonneg_left hξ.1 hpi_sq_nn
    have hle2 : Real.pi ^ 2 * ξ ≤ Real.pi ^ 2 * hankelXi c (-r_til) :=
      mul_le_mul_of_nonneg_left hξ.2 hpi_sq_nn
    have hw_lo : 0 ≤ Real.pi ^ 2 * ξ - 1 := by linarith only [hle1, hT_wb.1]
    have hw_hi : Real.pi ^ 2 * ξ - 1 ≤ 5e-4 := by linarith only [hle2, hr_wb.2.1]
    exact (hankelBandU_continuousAt hw_lo hw_hi).continuousWithinAt.neg
  have hf₂_int : IntegrableOn f₂ (Ioi 0) (hankelDmPos c f) := by
    have hband_int : IntegrableOn uFn bandSet (hankelDmPos c f) := huFn_contOn.integrableOn_Icc
    have hind_int : Integrable (bandSet.indicator uFn) (hankelDmPos c f) :=
      (integrable_indicator_iff measurableSet_Icc).2 hband_int
    exact (hind_int.const_mul _).integrableOn
  have hf₃_int : IntegrableOn f₃ (Ioi 0) (hankelDmPos c f) := by
    have hind_int : Integrable (tailSet.indicator (fun _ => (1 : ℝ))) (hankelDmPos c f) :=
      (integrable_indicator_iff measurableSet_Ici).2
        (integrableOn_const (hs := (measure_lt_top (hankelDmPos c f) _).ne))
    exact (hind_int.const_mul _).integrableOn
  have hc_pow : c ^ (-(1 / 2 : ℝ)) * (c ^ (-(2 / 3 : ℝ))) = c ^ (-(7 / 6 : ℝ)) := by
    rw [← Real.rpow_add hc0]; norm_num
  have hρ_sq : (32 * ρr) ^ 2 = 1024 * P.κ_ζ ^ 2 * c ^ (-(2 / 3 : ℝ)) * r := by
    have hdef : ρr = P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r := rfl
    rw [hdef]
    have h1 : (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
    have h2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr0.le
    calc (32 * (P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r)) ^ 2
        = 1024 * P.κ_ζ ^ 2 * (c ^ (-(1 / 3 : ℝ))) ^ 2 * Real.sqrt r ^ 2 := by ring
      _ = 1024 * P.κ_ζ ^ 2 * c ^ (-(2 / 3 : ℝ)) * r := by rw [h1, h2]
  have hae : ∀ᵐ ξ ∂(hankelDmPos c f).restrict (Ioi 0), ‖J₁ ξ‖ ≤ f₁ ξ + f₂ ξ + f₃ ξ := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun ξ hξ_pos => ?_
    have hj := hJ₁_pt ξ hξ_pos
    dsimp only [f₁, f₂, f₃]
    have hτ0_nn : 0 ≤ hankelBandTau0 ξ := hankelBandTau0_nonneg ξ
    have hCτ_pos : 0 < P.C_τ * c ^ (-(2 / 3 : ℝ)) := by have := P.hC_τ; positivity
    have hband_nn : 0 ≤ bandSet.indicator uFn ξ := by
      refine Set.indicator_nonneg (fun y hy => ?_) ξ
      have htb := hankelBandTau0_band hc hu0 hu3 hr_til_pos.le hr_til_A hy
      exact nonneg_of_mul_nonneg_right ((sq_nonneg (hankelBandTau0 y)).trans htb) hCτ_pos
    have htail_nn : 0 ≤ tailSet.indicator (fun _ => (1 : ℝ)) ξ :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) ξ
    have h_term : c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 *
          (if δ₀ < hankelBandTau0 ξ ∧ hankelBandTau0 ξ < 32 * ρr then 1 else 0) ≤
        P.C_τ * c ^ (-(7 / 6 : ℝ)) * bandSet.indicator uFn ξ +
        1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r * tailSet.indicator (fun _ => (1 : ℝ)) ξ := by
      by_cases hcond : δ₀ < hankelBandTau0 ξ ∧ hankelBandTau0 ξ < 32 * ρr
      · rw [ite_eq_left hcond, mul_one]
        have hu_le : hankelXi c u_T ≤ ξ := by
          by_contra hlt; push Not at hlt
          exact not_lt.2 (hankelBandTau0_below hc hu0 hu3 hlt) hcond.1
        rcases le_total (1028 * r) R_J with hcase | hcase
        · have hr_til_eq : r_til = 1028 * r := min_eq_left hcase
          have hξ_hi : ξ ≤ hankelXi c (-r_til) := by
            rw [hr_til_eq]
            exact (xi_le_1028r_of_tau0_lt hc hRJ_ub hr0 hcase hcond.2).trans_eq (by congr 1; ring)
          have hmem : ξ ∈ bandSet := ⟨hu_le, hξ_hi⟩
          have htb := hankelBandTau0_band hc hu0 hu3 hr_til_pos.le hr_til_A hmem
          rw [Set.indicator_of_mem hmem]
          have hle1 : c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 ≤ P.C_τ * c ^ (-(7 / 6 : ℝ)) * uFn ξ := by
            calc c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2
                ≤ c ^ (-(1 / 2 : ℝ)) * (P.C_τ * c ^ (-(2 / 3 : ℝ)) * uFn ξ) :=
                    mul_le_mul_of_nonneg_left htb (Real.rpow_nonneg hc0.le _)
              _ = P.C_τ * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ))) * uFn ξ := by ring
              _ = _ := by rw [hc_pow]
          have htail_0 : 0 ≤ 1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r *
              tailSet.indicator (fun _ => (1 : ℝ)) ξ :=
            mul_nonneg (mul_nonneg (by positivity) hr0.le) htail_nn
          exact le_add_of_le_of_nonneg hle1 htail_0
        · have hr_til_eq : r_til = R_J := min_eq_right hcase
          rcases le_or_gt ξ (hankelXi c (-R_J)) with hxi | hxi
          · have hmem : ξ ∈ bandSet := ⟨hu_le, by rw [hr_til_eq]; exact hxi⟩
            have htb := hankelBandTau0_band hc hu0 hu3 hr_til_pos.le hr_til_A hmem
            rw [Set.indicator_of_mem hmem]
            have hle1 : c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 ≤ P.C_τ * c ^ (-(7 / 6 : ℝ)) * uFn ξ := by
              calc c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2
                  ≤ c ^ (-(1 / 2 : ℝ)) * (P.C_τ * c ^ (-(2 / 3 : ℝ)) * uFn ξ) :=
                      mul_le_mul_of_nonneg_left htb (Real.rpow_nonneg hc0.le _)
                _ = P.C_τ * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ))) * uFn ξ := by ring
                _ = _ := by rw [hc_pow]
            have htail_0 : 0 ≤ 1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r *
                tailSet.indicator (fun _ => (1 : ℝ)) ξ :=
              mul_nonneg (mul_nonneg (by positivity) hr0.le) htail_nn
            exact le_add_of_le_of_nonneg hle1 htail_0
          · have hmem : ξ ∈ tailSet := hxi.le
            rw [Set.indicator_of_mem hmem, mul_one]
            have hsq_le : hankelBandTau0 ξ ^ 2 ≤ (32 * ρr) ^ 2 :=
              pow_le_pow_left₀ hτ0_nn hcond.2.le 2
            have hle2 : c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 ≤
                1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r := by
              calc c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2
                  ≤ c ^ (-(1 / 2 : ℝ)) * (32 * ρr) ^ 2 :=
                      mul_le_mul_of_nonneg_left hsq_le (Real.rpow_nonneg hc0.le _)
                _ = 1024 * P.κ_ζ ^ 2 * (c ^ (-(1 / 2 : ℝ)) * c ^ (-(2 / 3 : ℝ))) * r := by
                    rw [hρ_sq]; ring
                _ = _ := by rw [hc_pow]
            have hband_0 : 0 ≤ P.C_τ * c ^ (-(7 / 6 : ℝ)) * bandSet.indicator uFn ξ :=
              mul_nonneg (mul_nonneg P.hC_τ.le (Real.rpow_nonneg hc0.le _)) hband_nn
            exact le_add_of_nonneg_of_le hband_0 hle2
      · rw [ite_eq_right hcond, mul_zero]
        have h1 : 0 ≤ P.C_τ * c ^ (-(7 / 6 : ℝ)) * bandSet.indicator uFn ξ :=
          mul_nonneg (mul_nonneg P.hC_τ.le (Real.rpow_nonneg hc0.le _)) hband_nn
        have h2 : 0 ≤ 1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r *
            tailSet.indicator (fun _ => (1 : ℝ)) ξ :=
          mul_nonneg (mul_nonneg (by positivity) hr0.le) htail_nn
        exact add_nonneg h1 h2
    have hpt : ‖J₁ ξ‖ ≤ C_J1 * (c⁻¹ * ρr ^ (1 / 2 : ℝ) +
        P.C_τ * c ^ (-(7 / 6 : ℝ)) * bandSet.indicator uFn ξ +
        1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r * tailSet.indicator (fun _ => (1 : ℝ)) ξ) :=
      hj.trans (mul_le_mul_of_nonneg_left (by linarith only [h_term]) hC_J1_pos.le)
    calc ‖J₁ ξ‖ ≤ _ := hpt
      _ = C_J1 * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) +
          C_J1 * (P.C_τ * c ^ (-(7 / 6 : ℝ))) * bandSet.indicator uFn ξ +
          C_J1 * (1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r) *
            tailSet.indicator (fun _ => (1 : ℝ)) ξ := by ring
  have hsum_int : IntegrableOn (fun ξ => f₁ ξ + f₂ ξ + f₃ ξ) (Ioi 0) (hankelDmPos c f) :=
    (hf₁_int.add hf₂_int).add hf₃_int
  have hρr_nn : 0 ≤ ρr := by
    show 0 ≤ P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
    have := P.hκ_ζ; positivity
  have hf₁_bd : ∫ ξ in Ioi (0 : ℝ), f₁ ξ ∂hankelDmPos c f ≤ C_J1 * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) := by
    dsimp [f₁]; rw [setIntegral_const, smul_eq_mul]
    have hmeas : (hankelDmPos c f).real (Ioi 0) ≤ (hankelDmPos c f univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top (hankelDmPos c f) univ) (measure_mono (subset_univ _))
    exact mul_le_of_le_one_left (mul_nonneg hC_J1_pos.le (mul_nonneg (inv_nonneg.2 hc0.le) (Real.rpow_nonneg hρr_nn _)))
      (hmeas.trans hdmPos_le)
  have hf₂_bd : ∫ ξ in Ioi (0 : ℝ), f₂ ξ ∂hankelDmPos c f ≤
      C_J1 * (P.C_τ * c ^ (-(7 / 6 : ℝ))) * ∫ ξ in bandSet, uFn ξ ∂hankelDmPos c f := by
    dsimp [f₂]; rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_J1_pos.le (by have := P.hC_τ; positivity))
    have hband_sub : bandSet ⊆ Ioi (0 : ℝ) := fun ξ hξ => lt_of_lt_of_le hξT_pos hξ.1
    rw [setIntegral_indicator measurableSet_Icc, inter_eq_self_of_subset_right hband_sub]
  have hf₃_bd : ∫ ξ in Ioi (0 : ℝ), f₃ ξ ∂hankelDmPos c f ≤
      C_J1 * (1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r) * hankelBootB2 c f R_J := by
    dsimp [f₃]; rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_J1_pos.le (by positivity))
    have htail_sub : tailSet ⊆ Ioi (0 : ℝ) := fun ξ hξ =>
      lt_of_lt_of_le (lt_of_lt_of_le (lt_of_lt_of_le hξT_pos hmonoξ) hmonoξ_RJ) hξ
    rw [setIntegral_indicator measurableSet_Ici, inter_eq_self_of_subset_right htail_sub,
      setIntegral_const, smul_eq_mul, mul_one]
    rfl
  calc ‖∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmPos c f‖
      ≤ ∫ ξ in Ioi (0 : ℝ), ‖J₁ ξ‖ ∂hankelDmPos c f := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ in Ioi (0 : ℝ), (f₁ ξ + f₂ ξ + f₃ ξ) ∂hankelDmPos c f :=
        integral_mono_ae hJ₁_pos_int.norm hsum_int hae
    _ = (∫ ξ in Ioi (0 : ℝ), f₁ ξ ∂hankelDmPos c f) +
        (∫ ξ in Ioi (0 : ℝ), f₂ ξ ∂hankelDmPos c f) +
        (∫ ξ in Ioi (0 : ℝ), f₃ ξ ∂hankelDmPos c f) := by
        have ha1 := integral_add (hf₁_int.add hf₂_int) hf₃_int
        have ha2 := integral_add hf₁_int hf₂_int
        simp only [Pi.add_apply] at ha1 ha2
        rw [ha1, ha2]
    _ ≤ _ := by
        have := add_le_add (add_le_add hf₁_bd hf₂_bd) hf₃_bd
        linarith only [this]

private lemma outer_dm_pos_bound {c u_T R_J r : ℝ} {f : ℝ → ℝ} {ζ₀ : ℂ} {J₂ : ℝ → ℂ}
    (hc : 3e6 ≤ c) (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hσ₀ : 0 < ζ₀.re) (hfinP : IsFiniteMeasure (hankelDmPos c f))
    (hdmPos_le : (hankelDmPos c f univ).toReal ≤ 1)
    (hJ₂_pos_int : IntegrableOn J₂ (Ioi 0) (hankelDmPos c f))
    (hJ₂_pt : ∀ ξ ∈ Ioi (0 : ℝ), ‖J₂ ξ‖ ≤
      2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) *
        (c⁻¹ * rhoR hankelBandParams c r ^ (-(3 / 2 : ℝ)) +
          c ^ (-(1 / 2 : ℝ)) * (if 4 * rhoR hankelBandParams c r < hankelBandTau0 ξ then 1 else 0))) :
    ‖∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmPos c f‖ ≤
      2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) *
        (c⁻¹ * rhoR hankelBandParams c r ^ (-(3 / 2 : ℝ)) + c ^ (-(1 / 2 : ℝ)) * hankelBootB2 c f r) := by
  let P := hankelBandParams
  have hc0 : 0 < c := by linarith only [hc]
  have hr0 : 0 < r := by linarith only [hr_lb]
  set ρr := rhoR P c r
  have hu_abs : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
  have hξT_pos : 0 < hankelXi c u_T := hankelXi_pos hc0 hu_abs
  have hrA_r : |-r| ≤ langerRadius c := by
    rw [abs_neg, abs_of_pos hr0]
    exact hr_RJ.trans (hRJ_ub.trans (hankelBand_radius_ge_one hc))
  have hξr_lt : hankelXi c u_T ≤ hankelXi c (-r) :=
    le_of_mul_le_mul_left (hankel_phi_anti hc0 hrA_r hu_abs (by linarith only [hr_lb, hu3])) hc0
  let C_J2 : ℝ := 2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ)
  let tailSet_r := Ici (hankelXi c (-r))
  let g₁ : ℝ → ℝ := fun _ => C_J2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)))
  let g₂ : ℝ → ℝ := fun ξ => C_J2 * c ^ (-(1 / 2 : ℝ)) * tailSet_r.indicator (fun _ => (1 : ℝ)) ξ
  have hg₁_int : IntegrableOn g₁ (Ioi 0) (hankelDmPos c f) :=
    integrableOn_const (hs := (measure_lt_top (hankelDmPos c f) _).ne)
  have hg₂_int : IntegrableOn g₂ (Ioi 0) (hankelDmPos c f) := by
    have hind_int : Integrable (tailSet_r.indicator (fun _ => (1 : ℝ))) (hankelDmPos c f) :=
      (integrable_indicator_iff measurableSet_Ici).2
        (integrableOn_const (hs := (measure_lt_top (hankelDmPos c f) _).ne))
    exact (hind_int.const_mul _).integrableOn
  have hρr_nn : 0 ≤ ρr := by
    show 0 ≤ P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
    have := P.hκ_ζ; positivity
  have hae : ∀ᵐ ξ ∂(hankelDmPos c f).restrict (Ioi 0), ‖J₂ ξ‖ ≤ g₁ ξ + g₂ ξ := by
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine ae_of_all _ fun ξ hξ_pos => ?_
    have hj := hJ₂_pt ξ hξ_pos
    dsimp [g₁, g₂]
    have hind_le : (if 4 * ρr < hankelBandTau0 ξ then (1 : ℝ) else 0) ≤
        tailSet_r.indicator (fun _ => (1 : ℝ)) ξ := by
      by_cases hcond : 4 * ρr < hankelBandTau0 ξ
      · rw [ite_eq_left hcond]
        have hmem : ξ ∈ tailSet_r := by
          by_contra hlt
          have hlt' : ξ < hankelXi c (-r) := lt_of_not_ge hlt
          have hτ := tau0_lt_two_rhoR_of_xi_le hc hRJ_ub hr0 hr_RJ hlt'.le
          change hankelBandTau0 ξ < 2 * ρr at hτ
          linarith only [hcond, hτ, hρr_nn]
        rw [Set.indicator_of_mem hmem]
      · rw [ite_eq_right hcond]
        exact Set.indicator_nonneg (fun _ _ => zero_le_one) ξ
    calc ‖J₂ ξ‖ ≤ C_J2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)) +
          c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < hankelBandTau0 ξ then 1 else 0)) := hj
      _ ≤ C_J2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)) +
          c ^ (-(1 / 2 : ℝ)) * tailSet_r.indicator (fun _ => (1 : ℝ)) ξ) := by gcongr
      _ = _ := by ring
  have hC_J2_nn : 0 ≤ C_J2 := by dsimp [C_J2]; positivity
  have hg₁_bd : ∫ ξ in Ioi (0 : ℝ), g₁ ξ ∂hankelDmPos c f ≤ C_J2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) := by
    dsimp [g₁]; rw [setIntegral_const, smul_eq_mul]
    have hmeas : (hankelDmPos c f).real (Ioi 0) ≤ (hankelDmPos c f univ).toReal :=
      ENNReal.toReal_mono (measure_ne_top (hankelDmPos c f) univ) (measure_mono (subset_univ _))
    exact mul_le_of_le_one_left (mul_nonneg hC_J2_nn (mul_nonneg (inv_nonneg.2 hc0.le) (Real.rpow_nonneg hρr_nn _)))
      (hmeas.trans hdmPos_le)
  have hg₂_bd : ∫ ξ in Ioi (0 : ℝ), g₂ ξ ∂hankelDmPos c f ≤
      C_J2 * c ^ (-(1 / 2 : ℝ)) * hankelBootB2 c f r := by
    dsimp [g₂]; rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC_J2_nn (by positivity))
    have htail_sub : tailSet_r ⊆ Ioi (0 : ℝ) := fun ξ hξ =>
      lt_of_lt_of_le (lt_of_lt_of_le hξT_pos hξr_lt) hξ
    rw [setIntegral_indicator measurableSet_Ici, inter_eq_self_of_subset_right htail_sub,
      setIntegral_const, smul_eq_mul, mul_one]
    rfl
  calc ‖∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmPos c f‖
      ≤ ∫ ξ in Ioi (0 : ℝ), ‖J₂ ξ‖ ∂hankelDmPos c f := norm_integral_le_integral_norm _
    _ ≤ ∫ ξ in Ioi (0 : ℝ), (g₁ ξ + g₂ ξ) ∂hankelDmPos c f :=
        integral_mono_ae hJ₂_pos_int.norm (hg₁_int.add hg₂_int) hae
    _ = (∫ ξ in Ioi (0 : ℝ), g₁ ξ ∂hankelDmPos c f) +
        (∫ ξ in Ioi (0 : ℝ), g₂ ξ ∂hankelDmPos c f) := integral_add hg₁_int hg₂_int
    _ ≤ C_J2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) + C_J2 * c ^ (-(1 / 2 : ℝ)) * hankelBootB2 c f r :=
        add_le_add hg₁_bd hg₂_bd
    _ = _ := by ring

private lemma hankel_H_strip_bound {c ε : ℝ} {f : ℝ → ℝ} (hc32 : 3 / 2 < c)
    (hε : ε = 1 ∨ ε = -1) (hf : IsHankelEigenfn c ε f) (hmass : hankelMass c f = 1) :
    ∃ M : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖tebPrefactor c ζ * hankelWtS c ε f ζ‖ ≤ M := by
  have hc0 : 0 < c := by linarith only [hc32]
  refine ⟨c ^ (5 / 6 : ℝ) * 2 ^ 6 * 2 * (2 ^ 9 * (Nat.factorial 6 : ℝ)), fun ζ h0 h1 => ?_⟩
  have hpf := norm_tebPrefactor_le c hc0.le h0 h1
  have hW := hankelWtS_norm_le hc32 hf hε h0 h1
  rw [hmass, one_mul] at hW
  have hexp2 : Real.exp (1 / (6 * c)) ≤ 2 := hankelBand_exp_le_two (by linarith only [hc32])
  have hnorm_le : ‖ζ‖ ≤ 1 + |ζ.im| := by
    have hre := Complex.re_add_im ζ
    have htri : ‖ζ‖ ≤ ‖(ζ.re : ℂ)‖ + ‖(ζ.im : ℂ) * Complex.I‖ := by
      calc ‖ζ‖ = ‖(ζ.re : ℂ) + (ζ.im : ℂ) * Complex.I‖ := by rw [hre]
        _ ≤ _ := norm_add_le _ _
    calc ‖ζ‖ ≤ ‖(ζ.re : ℂ)‖ + ‖(ζ.im : ℂ) * Complex.I‖ := htri
      _ ≤ 1 + |ζ.im| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]; linarith only [h1]
  have hζ1 : ‖ζ * (1 - ζ)‖ ≤ 2 * (1 + |ζ.im|) ^ 2 := by
    have h1ζ : ‖1 - ζ‖ ≤ 2 + |ζ.im| := by
      calc ‖1 - ζ‖ ≤ ‖(1 : ℂ)‖ + ‖ζ‖ := norm_sub_le _ _
        _ ≤ 2 + |ζ.im| := by rw [norm_one]; linarith only [hnorm_le]
    have h1ζ' : ‖1 - ζ‖ ≤ 2 * (1 + |ζ.im|) := h1ζ.trans (by linarith only [abs_nonneg ζ.im])
    rw [norm_mul]
    calc ‖ζ‖ * ‖1 - ζ‖ ≤ (1 + |ζ.im|) * (2 * (1 + |ζ.im|)) :=
          mul_le_mul hnorm_le h1ζ' (norm_nonneg _) (by positivity)
      _ = 2 * (1 + |ζ.im|) ^ 2 := by ring
  have hpf1 : ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) ≤ 2 ^ (5 / 2 : ℝ) * (1 + |ζ.im|) ^ (5 : ℝ) := by
    have hsq : ((1 + |ζ.im|) ^ 2) ^ (5 / 2 : ℝ) = (1 + |ζ.im|) ^ (5 : ℝ) := by
      rw [← Real.rpow_natCast (1 + |ζ.im|) 2, ← Real.rpow_mul (by linarith only [abs_nonneg ζ.im])]; norm_num
    calc ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) ≤ (2 * (1 + |ζ.im|) ^ 2) ^ (5 / 2 : ℝ) :=
          Real.rpow_le_rpow (norm_nonneg _) hζ1 (by norm_num)
      _ = 2 ^ (5 / 2 : ℝ) * ((1 + |ζ.im|) ^ 2) ^ (5 / 2 : ℝ) :=
          Real.mul_rpow zero_le_two (sq_nonneg _)
      _ = 2 ^ (5 / 2 : ℝ) * (1 + |ζ.im|) ^ (5 : ℝ) := by rw [hsq]
  have hW1 : (1 + ‖ζ‖) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) * (1 + |ζ.im|) ^ (1 / 2 : ℝ) := by
    have : 1 + ‖ζ‖ ≤ 2 * (1 + |ζ.im|) := by linarith only [hnorm_le, abs_nonneg ζ.im]
    rw [← Real.mul_rpow zero_le_two (by linarith only [abs_nonneg ζ.im])]
    exact Real.rpow_le_rpow (by positivity) this (by norm_num)
  have h2pow : (2 : ℝ) ^ (5 / 2 : ℝ) * 2 ^ (1 / 2 : ℝ) ≤ 2 ^ 6 := by
    rw [← Real.rpow_add zero_lt_two]; norm_num
  have hcomb : (1 + |ζ.im|) ^ (5 : ℝ) * (1 + |ζ.im|) ^ (1 / 2 : ℝ) = (1 + |ζ.im|) ^ (11 / 2 : ℝ) := by
    rw [← Real.rpow_add (by linarith only [abs_nonneg ζ.im])]; norm_num
  have h9 : (1 + |ζ.im|) ^ (11 / 2 : ℝ) * Real.exp (-ζ.im ^ 2) ≤ 2 ^ 9 * (Nat.factorial 6 : ℝ) := by
    have hle : (1 + |ζ.im|) ^ (11 / 2 : ℝ) ≤ (1 + |ζ.im|) ^ (9 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [abs_nonneg ζ.im]) (by norm_num)
    calc (1 + |ζ.im|) ^ (11 / 2 : ℝ) * Real.exp (-ζ.im ^ 2)
        ≤ (1 + |ζ.im|) ^ (9 : ℝ) * Real.exp (-|ζ.im| ^ 2) := by
            rw [sq_abs]; exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
      _ ≤ 2 ^ 9 * (Nat.factorial 6 : ℝ) := one_add_rpow_nine_exp_le |ζ.im| (abs_nonneg _)
  rw [norm_mul]
  calc ‖tebPrefactor c ζ‖ * ‖hankelWtS c ε f ζ‖
      ≤ (c ^ (5 / 6 : ℝ) * ‖ζ * (1 - ζ)‖ ^ (5 / 2 : ℝ) * Real.exp (-ζ.im ^ 2)) *
          (Real.exp (1 / (6 * c)) * (1 + ‖ζ‖) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hpf hW (norm_nonneg _) (by positivity)
    _ ≤ (c ^ (5 / 6 : ℝ) * (2 ^ (5 / 2 : ℝ) * (1 + |ζ.im|) ^ (5 : ℝ)) * Real.exp (-ζ.im ^ 2)) *
          (2 * (2 ^ (1 / 2 : ℝ) * (1 + |ζ.im|) ^ (1 / 2 : ℝ))) := by
        gcongr
    _ = c ^ (5 / 6 : ℝ) * ((2 : ℝ) ^ (5 / 2 : ℝ) * 2 ^ (1 / 2 : ℝ)) * 2 *
          ((1 + |ζ.im|) ^ (11 / 2 : ℝ) * Real.exp (-ζ.im ^ 2)) := by rw [← hcomb]; ring
    _ ≤ c ^ (5 / 6 : ℝ) * 2 ^ 6 * 2 * (2 ^ 9 * (Nat.factorial 6 : ℝ)) := by gcongr

private lemma hankel_scale_combine {r ψ I_band B2_r B2_RJ n_H n_core n_in n_out n_pf : ℝ}
    (hr_lb : 256 ≤ r) (hcos_pos : 0 < Real.cos ψ)
    (hband_nn : 0 ≤ I_band) (hB2_r_nn : 0 ≤ B2_r) (hB2_RJ_nn : 0 ≤ B2_RJ)
    (hn_H_nn : 0 ≤ n_H) (h_tri : n_H ≤ n_core + n_in + n_out)
    (hCore_bd : n_core ≤
      8 * hankelBandParams.A_0 * (4 * hankelBandParams.A_0) ^ (5 / 2 : ℝ) *
        (1 + 4 * hankelBandParams.A_0) ^ (hankelBandParams.M + 5 / 2) *
        hankelBandParams.C_W * (3 / hankelBandParams.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ)))
    (hInner_bd : n_in ≤
      (4 * 27380416512 * (3 / hankelBandParams.κ_ζ ^ (1 / 2 : ℝ)) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
      (2 * 27380416512 * (3 / hankelBandParams.κ_ζ) * hankelBandParams.C_τ / Real.cos ψ) *
        r ^ (-(1 / 2 : ℝ)) * I_band +
      (2 * 27380416512 * (3 / hankelBandParams.κ_ζ) * 1024 * hankelBandParams.κ_ζ ^ 2 / Real.cos ψ) *
        r ^ (1 / 2 : ℝ) * B2_RJ)
    (hOuter_bd : n_out ≤
      (8 * 3e15 / hankelBandParams.κ_ζ ^ (1 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ)) +
      (4 * 3e15 * hankelBandParams.κ_ζ) * r ^ (1 / 2 : ℝ) * B2_r)
    (hpf_lb' : (1 / 128 : ℝ) * r ^ (5 / 4 : ℝ) ≤ n_pf) :
    n_H / n_pf ≤ hankelScaleBandC *
      (r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * I_band + r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) /
      Real.cos ψ := by
  let P := hankelBandParams
  have hr0 : 0 < r := by linarith only [hr_lb]
  have hcos_le1 : Real.cos ψ ≤ 1 := Real.cos_le_one ψ
  have h_inv_cos_ge1 : 1 ≤ 1 / Real.cos ψ := (one_le_div hcos_pos).mpr hcos_le1
  have hk_bd := hankelLangerKappa_bounds
  have hκ_ge1 : 1 ≤ P.κ_ζ := by show 1 ≤ 2 * langerKappa; linarith only [hk_bd.1]
  have hκ_le14 : P.κ_ζ ≤ 1.4 := by show 2 * langerKappa ≤ 1.4; linarith only [hk_bd.2]
  have hκ_pos : 0 < P.κ_ζ := P.hκ_ζ
  have hA0_le8 : P.A_0 ≤ 8 := by
    have h1 : 32 / langerKappa ≤ 64 := by
      rw [div_le_iff₀ langerKappa_pos]; linarith only [hk_bd.1]
    calc P.A_0 = Real.sqrt (32 / langerKappa) := rfl
      _ ≤ Real.sqrt 64 := Real.sqrt_le_sqrt h1
      _ = 8 := by norm_num
  have hA0_nonneg : 0 ≤ P.A_0 := P.hA_0.le
  have hCW_eq : P.C_W = 2 := rfl
  have hM_eq : P.M = 1 / 2 := rfl
  have hCτ_le22 : P.C_τ ≤ 22 := by
    show 11 / langerKappa ≤ 22
    rw [div_le_iff₀ langerKappa_pos]; linarith only [hk_bd.1]
  have h_core_coeff : (8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) *
      (3 / P.κ_ζ) ≤ 1e12 := by
    have h4A : (4 * P.A_0) ^ (5 / 2 : ℝ) ≤ 32 ^ (3 : ℝ) := by
      calc (4 * P.A_0) ^ (5 / 2 : ℝ) ≤ (32 : ℝ) ^ (5 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by linarith only [hA0_le8]) (by norm_num)
        _ ≤ 32 ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    have h14A : (1 + 4 * P.A_0) ^ (P.M + 5 / 2) = (1 + 4 * P.A_0) ^ (3 : ℝ) := by rw [hM_eq]; norm_num
    have h14A_bd : (1 + 4 * P.A_0) ^ (3 : ℝ) ≤ 33 ^ (3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by linarith only [hA0_le8]) (by norm_num)
    have h3κ : 3 / P.κ_ζ ≤ 3 := div_le_self (by norm_num) hκ_ge1
    rw [hCW_eq, h14A]
    calc 8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (3 : ℝ) * 2 * (3 / P.κ_ζ)
        ≤ 8 * 8 * 32 ^ (3 : ℝ) * 33 ^ (3 : ℝ) * 2 * 3 := by gcongr
      _ ≤ 1e12 := by norm_num
  have hκ12_ge1 : 1 ≤ P.κ_ζ ^ (1 / 2 : ℝ) := Real.one_le_rpow hκ_ge1 (by norm_num)
  have hr_32_le : r ^ (-(1 / 2 : ℝ)) ≤ r ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hr_lb]) (by norm_num)
  have h_core_step : (8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) *
      (3 / P.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ)) ≤
      (1e12 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right h_core_coeff (by positivity : 0 ≤ r ^ (-(1 / 2 : ℝ)) / Real.cos ψ)
    calc _ = ((8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W) *
          (3 / P.κ_ζ)) * (r ^ (-(1 / 2 : ℝ)) / Real.cos ψ) := by ring
      _ ≤ 1e12 * (r ^ (-(1 / 2 : ℝ)) / Real.cos ψ) := h1
      _ ≤ 1e12 * (r ^ (-(1 / 4 : ℝ)) / Real.cos ψ) := by gcongr
      _ = _ := by ring
  have hCτ_nn : 0 ≤ P.C_τ := P.hC_τ.le
  have h_in1 : 4 * 27380416512 * (3 / P.κ_ζ ^ (1 / 2 : ℝ)) ≤ 4e11 := by
    have h1 : 3 / P.κ_ζ ^ (1 / 2 : ℝ) ≤ 3 := div_le_self (by norm_num) hκ12_ge1
    calc 4 * 27380416512 * (3 / P.κ_ζ ^ (1 / 2 : ℝ)) ≤ 4 * 27380416512 * 3 := by gcongr
      _ ≤ 4e11 := by norm_num
  have h_in2 : 2 * 27380416512 * (3 / P.κ_ζ) * P.C_τ ≤ 4e12 := by
    have h1 : 3 / P.κ_ζ ≤ 3 := div_le_self (by norm_num) hκ_ge1
    calc 2 * 27380416512 * (3 / P.κ_ζ) * P.C_τ ≤ 2 * 27380416512 * 3 * 22 := by gcongr
      _ ≤ 4e12 := by norm_num
  have h_in3 : 2 * 27380416512 * (3 / P.κ_ζ) * 1024 * P.κ_ζ ^ 2 ≤ 4e14 := by
    have h1 : 3 / P.κ_ζ ≤ 3 := div_le_self (by norm_num) hκ_ge1
    have h2 : P.κ_ζ ^ 2 ≤ 1.4 ^ 2 := by nlinarith only [hκ_le14, hκ_ge1]
    calc 2 * 27380416512 * (3 / P.κ_ζ) * 1024 * P.κ_ζ ^ 2
        ≤ 2 * 27380416512 * 3 * 1024 * 1.4 ^ 2 := by gcongr
      _ ≤ 4e14 := by norm_num
  have h_out1 : (8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ)) ≤ 3e16 / Real.cos ψ := by
    have h1 : 8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ) ≤ 3e16 := by
      calc 8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ) ≤ 8 * 3e15 / 1 := by gcongr
        _ ≤ 3e16 := by norm_num
    calc 8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ) ≤ 3e16 * 1 := by linarith only [h1]
      _ ≤ 3e16 * (1 / Real.cos ψ) := mul_le_mul_of_nonneg_left h_inv_cos_ge1 (by norm_num)
      _ = 3e16 / Real.cos ψ := by ring
  have h_out2 : 4 * 3e15 * P.κ_ζ ≤ 2e16 / Real.cos ψ := by
    have h1 : 4 * 3e15 * P.κ_ζ ≤ 2e16 := by linarith only [hκ_le14]
    calc 4 * 3e15 * P.κ_ζ ≤ 2e16 * 1 := by linarith only [h1]
      _ ≤ 2e16 * (1 / Real.cos ψ) := mul_le_mul_of_nonneg_left h_inv_cos_ge1 (by norm_num)
      _ = 2e16 / Real.cos ψ := by ring
  have hH_bd_norm : n_H ≤
      ((1e12 + 4e11 + 3e16) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
      (4e12 / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) * I_band +
      ((2e16 + 4e14) / Real.cos ψ) * r ^ (1 / 2 : ℝ) * (B2_r + B2_RJ) := by
    have hCore_bd' : n_core ≤
        8 * P.A_0 * (4 * P.A_0) ^ (5 / 2 : ℝ) * (1 + 4 * P.A_0) ^ (P.M + 5 / 2) * P.C_W *
          (3 / P.κ_ζ) / Real.cos ψ * r ^ (-(1 / 2 : ℝ)) := hCore_bd
    have hInner1 : n_in ≤
        (4e11 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
        (4e12 / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) * I_band +
        (4e14 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ := by
      refine hInner_bd.trans ?_
      have h1 : (4 * 27380416512 * (3 / P.κ_ζ ^ (1 / 2 : ℝ)) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) ≤
          (4e11 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) := by gcongr
      have h2 : (2 * 27380416512 * (3 / P.κ_ζ) * P.C_τ / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) * I_band ≤
          (4e12 / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) * I_band := by gcongr
      have h3 : (2 * 27380416512 * (3 / P.κ_ζ) * 1024 * P.κ_ζ ^ 2 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ ≤
          (4e14 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ := by gcongr
      linarith only [h1, h2, h3]
    have hOuter1 : n_out ≤
        (3e16 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
        (2e16 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_r := by
      refine hOuter_bd.trans ?_
      have h1 : (8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ)) ≤
          (3e16 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) := by gcongr
      have h2 : (4 * 3e15 * P.κ_ζ) * r ^ (1 / 2 : ℝ) * B2_r ≤
          (2e16 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_r := by gcongr
      linarith only [h1, h2]
    have hB2_mix : (4e14 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ +
        (2e16 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_r ≤
        ((2e16 + 4e14) / Real.cos ψ) * r ^ (1 / 2 : ℝ) * (B2_r + B2_RJ) := by
      have h_pos1 : 0 ≤ (2e16 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ := by positivity
      have h_pos2 : 0 ≤ (4e14 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_r := by positivity
      have heq : ((2e16 + 4e14) / Real.cos ψ) * r ^ (1 / 2 : ℝ) * (B2_r + B2_RJ) =
          (4e14 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ +
          (2e16 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_r +
          (2e16 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_RJ +
          (4e14 / Real.cos ψ) * r ^ (1 / 2 : ℝ) * B2_r := by ring
      rw [heq]; linarith only [h_pos1, h_pos2]
    have hsum_r : ((1e12 + 4e11 + 3e16) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) =
        (1e12 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
        (4e11 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
        (3e16 / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) := by ring
    rw [hsum_r]
    linarith only [h_tri, hCore_bd', h_core_step, hInner1, hOuter1, hB2_mix]
  have hr_exp1 : r ^ (-(1 / 4 : ℝ)) / r ^ (5 / 4 : ℝ) = r ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_sub hr0]; norm_num
  have hr_exp2 : r ^ (-(1 / 2 : ℝ)) / r ^ (5 / 4 : ℝ) = r ^ (-(7 / 4 : ℝ)) := by
    rw [← Real.rpow_sub hr0]; norm_num
  have hr_exp3 : r ^ (1 / 2 : ℝ) / r ^ (5 / 4 : ℝ) = r ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_sub hr0]; norm_num
  calc n_H / n_pf
      ≤ n_H / ((1 / 128 : ℝ) * r ^ (5 / 4 : ℝ)) :=
        div_le_div_of_nonneg_left hn_H_nn (by positivity) hpf_lb'
    _ ≤ (((1e12 + 4e11 + 3e16) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
          (4e12 / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) * I_band +
          ((2e16 + 4e14) / Real.cos ψ) * r ^ (1 / 2 : ℝ) * (B2_r + B2_RJ)) /
          ((1 / 128 : ℝ) * r ^ (5 / 4 : ℝ)) := by gcongr
    _ = ((128 * (1e12 + 4e11 + 3e16)) * (r ^ (-(1 / 4 : ℝ)) / r ^ (5 / 4 : ℝ)) +
          (128 * 4e12) * (r ^ (-(1 / 2 : ℝ)) / r ^ (5 / 4 : ℝ)) * I_band +
          (128 * (2e16 + 4e14)) * (r ^ (1 / 2 : ℝ) / r ^ (5 / 4 : ℝ)) * (B2_r + B2_RJ)) / Real.cos ψ := by ring
    _ = ((128 * (1e12 + 4e11 + 3e16)) * r ^ (-(3 / 2 : ℝ)) +
          (128 * 4e12) * r ^ (-(7 / 4 : ℝ)) * I_band +
          (128 * (2e16 + 4e14)) * r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) / Real.cos ψ := by
        rw [hr_exp1, hr_exp2, hr_exp3]
    _ ≤ hankelScaleBandC *
          (r ^ (-(3 / 2 : ℝ)) + r ^ (-(7 / 4 : ℝ)) * I_band + r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) /
          Real.cos ψ := by
        unfold hankelScaleBandC
        have h_r1 : (128 * (1e12 + 4e11 + 3e16) : ℝ) ≤ 1e20 := by norm_num
        have h_r2 : (128 * 4e12 : ℝ) ≤ 1e20 := by norm_num
        have h_r3 : (128 * (2e16 + 4e14) : ℝ) ≤ 1e20 := by norm_num
        have hr1_nn : 0 ≤ r ^ (-(3 / 2 : ℝ)) := (Real.rpow_pos_of_pos hr0 _).le
        have hr2_nn : 0 ≤ r ^ (-(7 / 4 : ℝ)) * I_band := mul_nonneg (Real.rpow_pos_of_pos hr0 _).le hband_nn
        have hr3_nn : 0 ≤ r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ) :=
          mul_nonneg (Real.rpow_pos_of_pos hr0 _).le (add_nonneg hB2_r_nn hB2_RJ_nn)
        have t1 := mul_le_mul_of_nonneg_right h_r1 hr1_nn
        have t2 : (128 * 4e12) * (r ^ (-(7 / 4 : ℝ)) * I_band) ≤ 1e20 * (r ^ (-(7 / 4 : ℝ)) * I_band) :=
          mul_le_mul_of_nonneg_right h_r2 hr2_nn
        have t3 : (128 * (2e16 + 4e14)) * (r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) ≤
            1e20 * (r ^ (-(3 / 4 : ℝ)) * (B2_r + B2_RJ)) :=
          mul_le_mul_of_nonneg_right h_r3 hr3_nn
        exact div_le_div_of_nonneg_right (by linarith only [t1, t2, t3]) hcos_pos.le

private lemma hankel_scale_fubini {c ε : ℝ} {f : ℝ → ℝ} {ζ₀ : ℂ}
    (hc : 3e6 ≤ c) (hf : IsHankelEigenfn c ε f)
    (hσ₀ : 0 < ζ₀.re) (hσ₁ : ζ₀.re < 1)
    (hQ_pt : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 / ζ₀.re)
    (hfinP : IsFiniteMeasure (hankelDmPos c f)) (hfinN : IsFiniteMeasure (hankelDmNeg c f))
    (wt : ℝ → ℝ) (hwt_cont : Continuous wt) (hwt_bd : ∀ τ, |wt τ| ≤ 1) :
    let J : ℝ → ℂ := fun ξ => ∫ τ : ℝ, (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
      tebAmp0 c τ * hankelBandK c τ ξ
    ((∫ τ : ℝ, (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
        (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))) =
      (∫ ξ in Ioi (0 : ℝ), J ξ ∂hankelDmPos c f) - ∫ ξ in Ioi (0 : ℝ), J ξ ∂hankelDmNeg c f) ∧
    Integrable J (hankelDmPos c f) ∧ Integrable J (hankelDmNeg c f) := by
  intro J
  have hc0 : 0 < c := by linarith only [hc]
  have hc32 : 3 / 2 < c := by linarith only [hc]
  let g0 : ℝ → ℂ := fun τ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * tebAmp0 c τ
  let G : ℝ → ℝ → ℂ := fun τ ξ => g0 τ * hankelBandK c τ ξ
  have hg0_cont : Continuous g0 :=
    ((Complex.continuous_ofReal.comp hwt_cont).mul
      (Complex.continuous_ofReal.comp (stripPoissonQ_continuous hσ₀ hσ₁))).mul (continuous_tebAmp0 c)
  have hG_meas : Measurable (Function.uncurry G) :=
    (hg0_cont.measurable.comp measurable_fst).mul (hankelBandK_measurable hc0)
  have hg0_bd : ∀ τ : ℝ, ‖g0 τ‖ ≤ (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) *
      ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2)) := fun τ => by
    dsimp [g0]
    have hamp := norm_tebAmp0_le hc0.le (τ := τ)
    have h1τ : |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 : ℝ) := by
      have h1 : |τ| ^ (5 / 2 : ℝ) ≤ (1 + |τ|) ^ (5 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (by linarith only) (by norm_num)
      have h1τ_pos : 0 < 1 + |τ| := by linarith only [abs_nonneg τ]
      calc |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ)
          ≤ (1 + |τ|) ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) := by gcongr
        _ = (1 + |τ|) ^ (5 : ℝ) := by rw [← Real.rpow_add h1τ_pos]; norm_num
    have h12 : |wt τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 * (1 / ζ₀.re) :=
      mul_le_mul (hwt_bd τ) (hQ_pt τ) (abs_nonneg _) zero_le_one
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |wt τ| * |stripPoissonQ ζ₀.re ζ₀.im ε τ| * ‖tebAmp0 c τ‖
        ≤ (1 * (1 / ζ₀.re)) *
            (c ^ (5 / 6 : ℝ) * |τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ) * Real.exp (-τ ^ 2)) :=
          mul_le_mul h12 hamp (norm_nonneg _) (by positivity)
      _ = (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * (|τ| ^ (5 / 2 : ℝ) * (1 + |τ|) ^ (5 / 2 : ℝ)) * Real.exp (-τ ^ 2) := by ring
      _ ≤ (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * (1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2) := by gcongr
      _ = _ := by ring
  have hG_int_of : ∀ (dm : Measure ℝ), IsFiniteMeasure dm → dm (Iic 0) = 0 →
      Integrable (Function.uncurry G) (volume.prod dm) := by
    intro dm hfin _
    let dom : ℝ → ℝ := fun τ => (1 / ζ₀.re) * 4 * c ^ (5 / 6 : ℝ) *
      ((1 + |τ|) ^ (11 / 2 : ℝ) * Real.exp (-τ ^ 2))
    have hdom_int : Integrable dom :=
      (integrable_one_add_abs_rpow_mul_exp_neg_sq (by norm_num : (0 : ℝ) ≤ 11 / 2)).const_mul _
    exact (Integrable.comp_fst (ν := dm) hdom_int).mono' hG_meas.aestronglyMeasurable (ae_of_all _ fun ⟨τ, ξ⟩ => by
      dsimp [Function.uncurry, G, dom]
      rw [norm_mul, norm_hankelBandK hc0]
      have hK_bd : ‖hankelEdgeAmp c τ‖ ≤ 4 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
        have := hankelEdgeAmp_bound (by linarith only [hc] : 1 ≤ c) τ
        linarith only [this, norm_nonneg (hankelEdgeAmp' c τ)]
      have h1pow : (1 + |τ|) ^ (5 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ) = (1 + |τ|) ^ (11 / 2 : ℝ) := by
        rw [← Real.rpow_add (by linarith only [abs_nonneg τ])]; norm_num
      calc ‖g0 τ‖ * ‖hankelEdgeAmp c τ‖
          ≤ ((1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * ((1 + |τ|) ^ (5 : ℝ) * Real.exp (-τ ^ 2))) *
              (4 * (1 + |τ|) ^ (1 / 2 : ℝ)) := mul_le_mul (hg0_bd τ) hK_bd (norm_nonneg _) (by positivity)
        _ = (1 / ζ₀.re) * 4 * c ^ (5 / 6 : ℝ) *
              (((1 + |τ|) ^ (5 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)) * Real.exp (-τ ^ 2)) := by ring
        _ = _ := by rw [h1pow])
  have hGP := hG_int_of (hankelDmPos c f) hfinP (hankelDmPos_Iic c f)
  have hGN := hG_int_of (hankelDmNeg c f) hfinN (hankelDmNeg_Iic c f)
  have hJ_P : Integrable J (hankelDmPos c f) := hGP.integral_prod_right
  have hJ_N : Integrable J (hankelDmNeg c f) := hGN.integral_prod_right
  have h_eq : (fun τ : ℝ => (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
        (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))) =
      fun τ : ℝ => (∫ ξ : ℝ, G τ ξ ∂hankelDmPos c f) - ∫ ξ : ℝ, G τ ξ ∂hankelDmNeg c f := by
    ext τ
    have hsub := hankelDm_integral_sub hc0 hf (B := 4 * (1 + |τ|) ^ (1 / 2 : ℝ))
      (K := fun ξ => hankelBandK c τ ξ)
      (((hankelBandK_measurable hc0).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (fun ξ _ => by
        rw [norm_hankelBandK hc0]
        have := hankelEdgeAmp_bound (by linarith only [hc] : 1 ≤ c) τ
        linarith only [this, norm_nonneg (hankelEdgeAmp' c τ)])
    have hW_eq := hankelBand_W_edge hc32 hf τ
    have hint_eq : (∫ ξ : ℝ, hankelBandK c τ ξ ∂hankelDmPos c f) -
        ∫ ξ : ℝ, hankelBandK c τ ξ ∂hankelDmNeg c f = hankelWtS c ε f ((τ : ℂ) * Complex.I) :=
      hW_eq.symm
    rw [← hint_eq]
    dsimp [G, g0]
    rw [integral_const_mul, integral_const_mul]; ring
  have hIoi_eq : ∀ (dm : Measure ℝ), dm (Iic 0) = 0 → Integrable J dm →
      ∫ ξ : ℝ, J ξ ∂dm = ∫ ξ in Ioi (0 : ℝ), J ξ ∂dm := by
    intro dm hsupp hint_dm
    have h1 := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint_dm
    have hcompl : ∫ ξ in (Ioi (0 : ℝ))ᶜ, J ξ ∂dm = 0 := by
      rw [compl_Ioi, Measure.restrict_eq_zero.2 hsupp, integral_zero_measure]
    rw [hcompl, add_zero] at h1; exact h1.symm
  refine ⟨?_, hJ_P, hJ_N⟩
  have hswP : (∫ τ : ℝ, ∫ ξ : ℝ, G τ ξ ∂hankelDmPos c f) =
      ∫ ξ : ℝ, J ξ ∂hankelDmPos c f := by
    simpa [Function.uncurry, G, J] using integral_integral_swap hGP
  have hswN : (∫ τ : ℝ, ∫ ξ : ℝ, G τ ξ ∂hankelDmNeg c f) =
      ∫ ξ : ℝ, J ξ ∂hankelDmNeg c f := by
    simpa [Function.uncurry, G, J] using integral_integral_swap hGN
  have h_int_sub : (∫ τ : ℝ, (∫ ξ : ℝ, G τ ξ ∂hankelDmPos c f) - ∫ ξ : ℝ, G τ ξ ∂hankelDmNeg c f) =
      (∫ τ : ℝ, ∫ ξ : ℝ, G τ ξ ∂hankelDmPos c f) - ∫ τ : ℝ, ∫ ξ : ℝ, G τ ξ ∂hankelDmNeg c f :=
    integral_sub hGP.integral_prod_left hGN.integral_prod_left
  rw [h_eq, h_int_sub, hswP, hswN,
    hIoi_eq _ (hankelDmPos_Iic c f) hJ_P, hIoi_eq _ (hankelDmNeg_Iic c f) hJ_N]

/-- **Step 1a (`ct:Wbound`, `constant_terms_lower.tex` `ct:dyadic` (1))**: scale-`r` strip-band
reduction at any scale `r ∈ [256, R_J]` (`R_J ∈ [10⁻⁴ c^{2/3}, 10⁻⁴ c^{2/3} + 1]`).

Proves that for every `ζ₀` in the annulus `ρ_r / 3 ≤ ‖ζ₀‖ ≤ 2 ρ_r` (`ζ₀.re = ‖ζ₀‖ * cos ψ > 0`),
`‖hankelWtS c ε f ζ₀‖ ≤ hankelScaleBandC * (r^{-3/2} + r^{-7/4} ∫_{[ξ(u_T), ξ(-r̃)]} (-ũ) dm_+ + r^{-3/4}(B₂(r) + B₂(R_J))) / cos ψ`,
where `r̃ = min (1028 * r) R_J`. -/
theorem hankel_scale_band_reduction {c ε T u_T R_J r : ℝ} {f : ℝ → ℝ}
    (hc : 3e6 ≤ c) (hε : ε = 1 ∨ ε = -1) (hf : IsHankelEigenfn c ε f) (hmass : hankelMass c f = 1)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hT : c * hankelXi c u_T = T)
    (htail : ∀ Δ : ℝ, T ≤ Δ → 0 ≤ f Δ)
    (_hRJ_lb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    {ζ₀ : ℂ} {ψ : ℝ}
    (hζ₀_lo : rhoR hankelBandParams c r / 3 ≤ ‖ζ₀‖)
    (hζ₀_hi : ‖ζ₀‖ ≤ 2 * rhoR hankelBandParams c r)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ)
    (hcos_pos : 0 < Real.cos ψ) :
    ‖hankelWtS c ε f ζ₀‖ ≤ hankelScaleBandC *
      (r ^ (-(3 / 2 : ℝ)) +
        r ^ (-(7 / 4 : ℝ)) *
          ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-min (1028 * r) R_J)),
            (-hankelBandU c ξ) ∂(hankelDmPos c f) +
        r ^ (-(3 / 4 : ℝ)) * (hankelBootB2 c f r + hankelBootB2 c f R_J)) / Real.cos ψ := by
  let P := hankelBandParams
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith
  have hr0 : 0 < r := by linarith
  have hρ_ub : 2 * rhoR P c r ≤ 0.035 := hankelBand_rho_le hc (hr_RJ.trans hRJ_ub)
  have hζ₀_max : ‖ζ₀‖ ≤ 0.035 := hζ₀_hi.trans hρ_ub
  set ρr := rhoR P c r
  have hρr_pos : 0 < ρr := by
    show 0 < P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r
    have := P.hκ_ζ; positivity
  have hζ₀_pos : 0 < ‖ζ₀‖ := lt_of_lt_of_le (by positivity) hζ₀_lo
  have hσ₀ : 0 < ζ₀.re := by rw [hcos_eq]; exact mul_pos hζ₀_pos hcos_pos
  have hσ₀_le : ζ₀.re ≤ 0.04 := (Complex.re_le_norm _).trans (hζ₀_max.trans (by norm_num))
  have hσ₁ : ζ₀.re < 1 := by linarith
  have hε_abs : |ε| ≤ 1 := by rcases hε with rfl | rfl <;> norm_num
  -- Strip Poisson representation of `H ζ₀ = tebPrefactor c ζ₀ * hankelWtS c ε f ζ₀`
  let H : ℂ → ℂ := fun ζ => tebPrefactor c ζ * hankelWtS c ε f ζ
  have hH_cont : ContinuousOn H {ζ : ℂ | 0 ≤ ζ.re ∧ ζ.re ≤ 1} :=
    (tebPrefactor_continuousOn c).mul (hankelWtS_continuousOn hc32 hf)
  have hH_holo : DifferentiableOn ℂ H {ζ : ℂ | 0 < ζ.re ∧ ζ.re < 1} :=
    (tebPrefactor_differentiableOn c).mul (hankelWtS_differentiableOn hc32 hf)
  have hH_symm : ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → H (1 - ζ) = (ε : ℂ) * H ζ := fun ζ h0 h1 => by
    dsimp [H]; rw [tebPrefactor_symm, hankelWtS_one_sub hc32 hf hε h0 h1]; ring
  have hH_bd : ∃ M : ℝ, ∀ ζ : ℂ, 0 ≤ ζ.re → ζ.re ≤ 1 → ‖H ζ‖ ≤ M :=
    hankel_H_strip_bound hc32 hε hf hmass
  obtain ⟨M_bd, hM_bd⟩ := hH_bd
  obtain ⟨hQH_int, hH_rep⟩ := stripPoisson_representation_symm hH_cont hH_holo hM_bd hH_symm hσ₀ hσ₁
  set δ₀ := P.A_0 * c ^ (-(1 / 3 : ℝ))
  let χ₁ : ℝ → ℝ := fun τ => tebCutoff δ₀ τ * (1 - tebCutoff (4 * ρr) τ)
  let ψ_r : ℝ → ℝ := tebCutoff (4 * ρr)
  let coreFn : ℝ → ℂ := fun τ => ((1 - tebCutoff δ₀ τ : ℝ) : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))
  let innerFn : ℝ → ℂ := fun τ => (χ₁ τ : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))
  let outerFn : ℝ → ℂ := fun τ => (ψ_r τ : ℂ) *
    (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))
  have hδ4_le : 4 * δ₀ ≤ 8 * ρr := by
    have hk := hankelLangerKappa_bounds
    have hA0_le : P.A_0 ≤ 8 := by
      show Real.sqrt (32 / langerKappa) ≤ 8
      exact Real.sqrt_le_iff.2 ⟨by norm_num, by rw [div_le_iff₀ langerKappa_pos]; linarith only [hk.1]⟩
    have hκ_ge : 1 ≤ P.κ_ζ := by show 1 ≤ 2 * langerKappa; linarith only [hk.1]
    have hsqrt_ge : 16 ≤ Real.sqrt r := by
      rw [Real.le_sqrt (by norm_num) hr0.le]; linarith only [hr_lb]
    have hc_nn : 0 ≤ c ^ (-(1 / 3 : ℝ)) := Real.rpow_nonneg hc0.le _
    have hκr : 16 ≤ P.κ_ζ * Real.sqrt r := by
      calc (16 : ℝ) = 1 * 16 := by ring
        _ ≤ P.κ_ζ * Real.sqrt r := mul_le_mul hκ_ge hsqrt_ge (by norm_num) P.hκ_ζ.le
    calc 4 * δ₀ = (4 * P.A_0) * c ^ (-(1 / 3 : ℝ)) := by dsimp [δ₀]; ring
      _ ≤ 32 * c ^ (-(1 / 3 : ℝ)) := mul_le_mul_of_nonneg_right (by linarith only [hA0_le]) hc_nn
      _ ≤ (2 * (P.κ_ζ * Real.sqrt r)) * c ^ (-(1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hκr]) hc_nn
      _ ≤ 8 * (P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) := by
          have : 0 ≤ (P.κ_ζ * Real.sqrt r) * c ^ (-(1 / 3 : ℝ)) := by positivity
          linarith only [this]
  have hpart : ∀ τ : ℝ, ((1 - tebCutoff δ₀ τ : ℝ) : ℂ) + (χ₁ τ : ℂ) + (ψ_r τ : ℂ) = 1 := fun τ => by
    have hreal : (1 - tebCutoff δ₀ τ) + χ₁ τ + ψ_r τ = 1 := by
      dsimp [χ₁, ψ_r]
      rcases le_or_gt |τ| (8 * ρr) with hle | hgt
      · have h0 : tebCutoff (4 * ρr) τ = 0 :=
          tebCutoff_eq_zero (by positivity) (by linarith only [hle])
        rw [h0]; ring
      · have h1 : tebCutoff δ₀ τ = 1 :=
          tebCutoff_eq_one (by dsimp [δ₀]; have := P.hA_0; positivity) (hδ4_le.trans hgt.le)
        rw [h1]; ring
    exact_mod_cast hreal
  have hsum_fn : (fun τ => coreFn τ + innerFn τ + outerFn τ) =
      fun τ => (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I) := by
    ext τ
    have hp := hpart τ
    calc coreFn τ + innerFn τ + outerFn τ
        = (((1 - tebCutoff δ₀ τ : ℝ) : ℂ) + (χ₁ τ : ℂ) + (ψ_r τ : ℂ)) *
            ((stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
              (tebPrefactor c ((τ : ℂ) * Complex.I) * hankelWtS c ε f ((τ : ℂ) * Complex.I))) := by
            dsimp [coreFn, innerFn, outerFn]; unfold tebAmp0; ring
      _ = 1 * ((stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
            (tebPrefactor c ((τ : ℂ) * Complex.I) * hankelWtS c ε f ((τ : ℂ) * Complex.I))) := by rw [hp]
      _ = (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I) := by
            dsimp [H]; rw [one_mul]
  have hinner_int : Integrable innerFn := by
    have hcont_χ₁ : Continuous χ₁ :=
      (tebCutoff_continuous δ₀).mul (continuous_const.sub (tebCutoff_continuous (4 * ρr)))
    have h1 := hQH_int.bdd_mul (Complex.continuous_ofReal.comp hcont_χ₁).aestronglyMeasurable
      (ae_of_all _ fun τ => by
        dsimp only [Function.comp_def, χ₁]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul
          (abs_le.2 ⟨by linarith [tebCutoff_nonneg δ₀ τ], tebCutoff_le_one δ₀ τ⟩)
          (abs_le.2 ⟨by linarith [tebCutoff_le_one (4 * ρr) τ], by linarith [tebCutoff_nonneg (4 * ρr) τ]⟩)
          (abs_nonneg _) zero_le_one |>.trans_eq (mul_one 1))
    have heq : (fun τ => (Complex.ofReal ∘ χ₁) τ *
        ((stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I))) = innerFn := by
      ext τ; dsimp [innerFn, H, Function.comp_def]; unfold tebAmp0; ring
    rwa [heq] at h1
  have houter_int : Integrable outerFn := by
    have h1 := hQH_int.bdd_mul (Complex.continuous_ofReal.comp (tebCutoff_continuous (4 * ρr))).aestronglyMeasurable
      (ae_of_all _ fun τ => by
        dsimp only [Function.comp_def]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [tebCutoff_nonneg (4 * ρr) τ], tebCutoff_le_one (4 * ρr) τ⟩)
    have heq : (fun τ => (Complex.ofReal ∘ ψ_r) τ *
        ((stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I))) = outerFn := by
      ext τ; dsimp [outerFn, ψ_r, H, Function.comp_def]; unfold tebAmp0; ring
    rwa [heq] at h1
  have hcore_int : Integrable coreFn := by
    have hsub : coreFn = fun τ => (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) * H ((τ : ℂ) * Complex.I) -
        (innerFn τ + outerFn τ) := by
      ext τ; have h1 := congrFun hsum_fn τ; exact eq_sub_of_add_eq (by linear_combination h1)
    rw [hsub]; exact hQH_int.sub (hinner_int.add houter_int)
  have hH_split : H ζ₀ = (∫ τ : ℝ, coreFn τ) + (∫ τ : ℝ, innerFn τ) + ∫ τ : ℝ, outerFn τ := by
    have h1 : ∫ τ : ℝ, (coreFn τ + innerFn τ + outerFn τ) =
        (∫ τ : ℝ, coreFn τ) + (∫ τ : ℝ, innerFn τ) + ∫ τ : ℝ, outerFn τ := by
      have ha1 := integral_add (hcore_int.add hinner_int) houter_int
      have ha2 := integral_add hcore_int hinner_int
      simp only [Pi.add_apply] at ha1 ha2
      rw [ha1, ha2]
    rw [hH_rep, ← hsum_fn]; exact h1
  -- Core bound
  have hCore_bd := core_piece_scale_bound hc hε hf hmass hr_lb hζ₀_lo hζ₀_max hcos_eq hcos_pos hcore_int
  -- Setup Fubini for inner & outer via `hankelDmPos`, `hankelDmNeg`
  have hfinP := isFiniteMeasure_hankelDmPos hc0 hf
  have hfinN := isFiniteMeasure_hankelDmNeg hc0 hf
  have hdm_tv : (hankelDmPos c f univ).toReal + (hankelDmNeg c f univ).toReal ≤ 1 :=
    (hankelDm_tv hc0 hf).trans_le (le_of_eq hmass)
  have hdmPos_le : (hankelDmPos c f univ).toReal ≤ 1 := by
    linarith [ENNReal.toReal_nonneg (a := hankelDmNeg c f univ), hdm_tv]
  have hdmNeg_le : (hankelDmNeg c f univ).toReal ≤ 1 := by
    linarith [ENNReal.toReal_nonneg (a := hankelDmPos c f univ), hdm_tv]
  have hT_eq : hankelXi c u_T = T / c := by
    rw [← hT, mul_div_cancel_left₀ _ hc0.ne']
  have hdm_neg_tail : hankelDmNeg c f (Ici (hankelXi c u_T)) = 0 :=
    hankelDmNeg_tail hc0 (fun Δ hΔ => htail Δ (hT ▸ hΔ))
  have hQ_pt : ∀ τ : ℝ, |stripPoissonQ ζ₀.re ζ₀.im ε τ| ≤ 1 / ζ₀.re := fun τ =>
    (stripPoissonQ_abs_le hσ₀ hσ₁ ζ₀.im hε_abs τ).trans (stripPoissonCalQ_le hσ₀ hσ₀_le ζ₀.im τ)
  have hfubini : ∀ (wt : ℝ → ℝ) (hwt_cont : Continuous wt) (hwt_bd : ∀ τ, |wt τ| ≤ 1),
      let J : ℝ → ℂ := fun ξ => ∫ τ : ℝ, (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
        tebAmp0 c τ * hankelBandK c τ ξ
      ((∫ τ : ℝ, (wt τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
          (tebAmp0 c τ * hankelWtS c ε f ((τ : ℂ) * Complex.I))) =
        (∫ ξ in Ioi (0 : ℝ), J ξ ∂hankelDmPos c f) - ∫ ξ in Ioi (0 : ℝ), J ξ ∂hankelDmNeg c f) ∧
      Integrable J (hankelDmPos c f) ∧ Integrable J (hankelDmNeg c f) :=
    hankel_scale_fubini hc hf hσ₀ hσ₁ hQ_pt hfinP hfinN
  -- Apply `hfubini` to `innerFn`
  have hχ₁_cont : Continuous χ₁ :=
    (tebCutoff_continuous δ₀).mul (continuous_const.sub (tebCutoff_continuous (4 * ρr)))
  have hχ₁_bd : ∀ τ, |χ₁ τ| ≤ 1 := fun τ => by
    dsimp [χ₁]; rw [abs_mul]
    exact (mul_le_mul (abs_le.2 ⟨by linarith [tebCutoff_nonneg δ₀ τ], tebCutoff_le_one δ₀ τ⟩)
      (abs_le.2 ⟨by linarith [tebCutoff_le_one (4 * ρr) τ], by linarith [tebCutoff_nonneg (4 * ρr) τ]⟩)
      (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have hInner_fub := hfubini χ₁ hχ₁_cont hχ₁_bd
  -- Apply `hfubini` to `outerFn`
  have hψr_bd : ∀ τ, |ψ_r τ| ≤ 1 := fun τ =>
    abs_le.2 ⟨by linarith [tebCutoff_nonneg (4 * ρr) τ], tebCutoff_le_one (4 * ρr) τ⟩
  have hOuter_fub := hfubini ψ_r (tebCutoff_continuous (4 * ρr)) hψr_bd
  -- Helpful scale factor conversions:
  have hσ₀_lb : (P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r * Real.cos ψ ≤ ζ₀.re := by
    rw [hcos_eq]
    have h1 : rhoR P c r / 3 = (P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r := by
      show (P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) / 3 = _; ring
    rw [← h1]
    exact mul_le_mul_of_nonneg_right hζ₀_lo hcos_pos.le
  have hκ_pos : 0 < P.κ_ζ := P.hκ_ζ
  have hρ_c_comb : c ^ (5 / 6 : ℝ) * ρr ^ (5 / 2 : ℝ) = P.κ_ζ ^ (5 / 2 : ℝ) * r ^ (5 / 4 : ℝ) := by
    have hdef : ρr = (P.κ_ζ * Real.sqrt r) * c ^ (-(1 / 3 : ℝ)) := by
      show P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r = _; ring
    rw [hdef, Real.mul_rpow (by positivity) (Real.rpow_nonneg hc0.le _),
      Real.mul_rpow hκ_pos.le (Real.sqrt_nonneg _), ← Real.rpow_mul hc0.le,
      Real.sqrt_eq_rpow, ← Real.rpow_mul hr0.le]
    have h1 : -(1 / 3 : ℝ) * (5 / 2 : ℝ) = -(5 / 6 : ℝ) := by norm_num
    have h2 : (1 / 2 : ℝ) * (5 / 2 : ℝ) = 5 / 4 := by norm_num
    rw [h1, h2]
    calc c ^ (5 / 6 : ℝ) * (P.κ_ζ ^ (5 / 2 : ℝ) * r ^ (5 / 4 : ℝ) * c ^ (-(5 / 6 : ℝ)))
        = (c ^ (5 / 6 : ℝ) * c ^ (-(5 / 6 : ℝ))) * (P.κ_ζ ^ (5 / 2 : ℝ) * r ^ (5 / 4 : ℝ)) := by ring
      _ = 1 * (P.κ_ζ ^ (5 / 2 : ℝ) * r ^ (5 / 4 : ℝ)) := by rw [← Real.rpow_add hc0]; simp
      _ = _ := one_mul _
  have hr_54_pos : 0 < r ^ (5 / 4 : ℝ) := Real.rpow_pos_of_pos hr0 _
  have hr_32_le : r ^ (-(1 / 2 : ℝ)) ≤ r ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hpf_lb : (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) *
      r ^ (5 / 4 : ℝ) ≤ ‖tebPrefactor c ζ₀‖ := by
    have hρmin : 0 < ρr / 3 := by positivity
    have hpf := norm_tebPrefactor_ge_on_annulus hc0 hρmin hζ₀_lo hζ₀_max
    have hdiv : (ρr / 3) ^ (5 / 2 : ℝ) = (1 / 3 : ℝ) ^ (5 / 2 : ℝ) * ρr ^ (5 / 2 : ℝ) := by
      rw [div_eq_mul_inv, mul_comm, Real.mul_rpow (by norm_num) hρr_pos.le, ← one_div]
    have h13 : (1 / 3 : ℝ) ^ (5 / 2 : ℝ) = (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * P.κ_ζ ^ (-(5 / 2 : ℝ)) := by
      have hκ_nn : 0 ≤ P.κ_ζ := hκ_pos.le
      have hκ3_eq : (3 / P.κ_ζ)⁻¹ = P.κ_ζ * (1 / 3 : ℝ) := by rw [inv_div]; ring
      rw [hκ3_eq, Real.mul_rpow hκ_nn (by norm_num), mul_comm (P.κ_ζ ^ (5 / 2 : ℝ)),
        mul_assoc, ← Real.rpow_add hκ_pos]
      simp
    calc (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) * r ^ (5 / 4 : ℝ)
        = ((3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * P.κ_ζ ^ (-(5 / 2 : ℝ))) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) *
            (P.κ_ζ ^ (5 / 2 : ℝ) * r ^ (5 / 4 : ℝ)) := by
          have : P.κ_ζ ^ (-(5 / 2 : ℝ)) * P.κ_ζ ^ (5 / 2 : ℝ) = 1 := by
            rw [← Real.rpow_add hκ_pos]; simp
          calc (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) * r ^ (5 / 4 : ℝ)
              = (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * 1 * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) * r ^ (5 / 4 : ℝ) := by ring
            _ = (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * (P.κ_ζ ^ (-(5 / 2 : ℝ)) * P.κ_ζ ^ (5 / 2 : ℝ)) *
                  (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) * r ^ (5 / 4 : ℝ) := by rw [this]
            _ = _ := by ring
      _ = (1 / 3 : ℝ) ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) *
            (P.κ_ζ ^ (5 / 2 : ℝ) * r ^ (5 / 4 : ℝ)) := by rw [← h13]
      _ = c ^ (5 / 6 : ℝ) * ((ρr / 3) ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)) := by
          rw [← hρ_c_comb, hdiv]; ring
      _ ≤ ‖tebPrefactor c ζ₀‖ := hpf
  -- Let `C_pf_r := (3 / P.κ_ζ)⁻¹ ^ (5/2) * 0.965^(5/2) * exp(-0.04)`
  set C_pf_r : ℝ := (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04)
  have hC_pf_lb : (1 / 128 : ℝ) ≤ C_pf_r := by
    have hk := hankelLangerKappa_bounds
    have h3κ : (P.κ_ζ / 3) ≥ 1 / 3 := by
      show 1 / 3 ≤ 2 * langerKappa / 3; linarith
    have hpow : (1 / 3 : ℝ) ^ (5 / 2 : ℝ) ≤ (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) := by
      rw [inv_div]; exact Real.rpow_le_rpow (by norm_num) h3κ (by norm_num)
    have h13 : (1 / 27 : ℝ) ≤ (1 / 3 : ℝ) ^ (5 / 2 : ℝ) := by
      calc (1 / 27 : ℝ) = (1 / 3 : ℝ) ^ (3 : ℝ) := by norm_num
        _ ≤ (1 / 3 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have h0965 : (1 / 2 : ℝ) ≤ (0.965 : ℝ) ^ (5 / 2 : ℝ) := by
      calc (1 / 2 : ℝ) ≤ (0.965 : ℝ) ^ (3 : ℝ) := by norm_num
        _ ≤ (0.965 : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num)
    have hexp004 : (1 / 2 : ℝ) ≤ Real.exp (-0.04) := by
      have h1 : (0.96 : ℝ) ≤ 1 - 0.04 := by norm_num
      have h2 := Real.add_one_le_exp (-0.04 : ℝ)
      linarith
    dsimp [C_pf_r]
    calc (1 / 128 : ℝ) ≤ (1 / 27 : ℝ) * (1 / 2) * (1 / 2) := by norm_num
      _ ≤ (3 / P.κ_ζ)⁻¹ ^ (5 / 2 : ℝ) * (0.965 : ℝ) ^ (5 / 2 : ℝ) * Real.exp (-0.04) :=
          mul_le_mul (mul_le_mul (h13.trans hpow) h0965 (by norm_num) (by positivity))
            hexp004 (by norm_num) (by positivity)
  -- Bound the inner integral `∫ innerFn` via `inner_half_osc_bound`:
  have hInner_bd : ‖∫ τ : ℝ, innerFn τ‖ ≤
      (4 * 27380416512 * (3 / P.κ_ζ ^ (1 / 2 : ℝ)) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
      (2 * 27380416512 * (3 / P.κ_ζ) * P.C_τ / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) *
        ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-min (1028 * r) R_J)),
          (-hankelBandU c ξ) ∂hankelDmPos c f +
      (2 * 27380416512 * (3 / P.κ_ζ) * 1024 * P.κ_ζ ^ 2 / Real.cos ψ) * r ^ (1 / 2 : ℝ) *
        hankelBootB2 c f R_J := by
    let J₁ : ℝ → ℂ := fun ξ => ∫ τ : ℝ, (χ₁ τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
      tebAmp0 c τ * hankelBandK c τ ξ
    have hJ₁_pt : ∀ ξ ∈ Ioi (0 : ℝ), ‖J₁ ξ‖ ≤
        2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) *
          (c⁻¹ * ρr ^ (1 / 2 : ℝ) +
            c ^ (-(1 / 2 : ℝ)) * hankelBandTau0 ξ ^ 2 *
              (if δ₀ < hankelBandTau0 ξ ∧ hankelBandTau0 ξ < 32 * ρr then 1 else 0)) := by
      intro ξ hξ
      have hpos := @inner_half_osc_bound c ε 1 ζ₀.re ζ₀.im r ξ hc hσ₀ hσ₀_le hε_abs (Or.inl rfl) hξ hr_lb hρ_ub
      have hneg := @inner_half_osc_bound c ε (-1) ζ₀.re ζ₀.im r ξ hc hσ₀ hσ₀_le hε_abs (Or.inr rfl) hξ hr_lb hρ_ub
      have h_even_1 : ∀ τ : ℝ, χ₁ (-τ) = χ₁ τ := fun τ => by
        dsimp [χ₁]; rw [tebCutoff_even, tebCutoff_even]
      exact (scale_J_norm_le hc hσ₀ hσ₁ hQ_pt hχ₁_cont h_even_1 hχ₁_bd hpos.2 hneg.2).trans_eq (by ring)
    -- Integrate `J₁` over `dmPos` and `dmNeg`:
    have hu_abs : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
    set r_til := min (1028 * r) R_J
    have hr_til_pos : 0 < r_til := lt_min (by positivity) (lt_of_lt_of_le hr0 hr_RJ)
    have hr_til_RJ : r_til ≤ R_J := min_le_right _ _
    have hr_til_A : r_til ≤ langerRadius c := hr_til_RJ.trans (hRJ_ub.trans (hankelBand_radius_ge_one hc))
    have hRJ_A : R_J ≤ langerRadius c := hRJ_ub.trans (hankelBand_radius_ge_one hc)
    have hRu : -R_J ≤ u_T := by
      have h1 := hankel_rpow23_ge hc
      have h2 : (2 : ℝ) ≤ R_J := by nlinarith
      linarith
    have hr_til_u : -r_til ≤ u_T := by
      show -min (1028 * r) R_J ≤ u_T
      rcases le_total (1028 * r) R_J with h | h
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right h]; exact hRu
    have hr_til_neg_A : |-r_til| ≤ langerRadius c := by
      rw [abs_neg, abs_of_pos hr_til_pos]; exact hr_til_A
    have hmonoξ : hankelXi c u_T ≤ hankelXi c (-r_til) := by
      exact le_of_mul_le_mul_left (hankel_phi_anti hc0 hr_til_neg_A hu_abs hr_til_u) hc0
    have hRJ_neg_A : |-R_J| ≤ langerRadius c := by
      rw [abs_neg, abs_of_pos (lt_of_lt_of_le hr0 hr_RJ)]; exact hRJ_A
    have hmonoξ_RJ : hankelXi c (-r_til) ≤ hankelXi c (-R_J) := by
      exact le_of_mul_le_mul_left (hankel_phi_anti hc0 hRJ_neg_A hr_til_neg_A (by linarith)) hc0
    have hξT_pos : 0 < hankelXi c u_T := hankelXi_pos hc0 hu_abs
    -- Bound on `dmNeg`: since `dmNeg (Ici T) = 0`, ae `ξ < hankelXi c u_T`, so `τ₀ ≤ δ₀`, indicator vanishes
    have hneg_bd : ‖∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmNeg c f‖ ≤
        2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) := by
      have hae : ∀ᵐ ξ ∂(hankelDmNeg c f).restrict (Ioi 0),
          ‖J₁ ξ‖ ≤ 2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) := by
        rw [ae_restrict_iff' measurableSet_Ioi]
        have hlt : ∀ᵐ ξ ∂hankelDmNeg c f, ξ < hankelXi c u_T := by
          rw [ae_iff]; simp only [not_lt]; exact hdm_neg_tail
        filter_upwards [hlt] with ξ hξ_lt hξ_pos
        have hτ := hankelBandTau0_below hc hu0 hu3 hξ_lt
        have hj := hJ₁_pt ξ hξ_pos
        have hnot : ¬ (δ₀ < hankelBandTau0 ξ ∧ hankelBandTau0 ξ < 32 * ρr) :=
          fun hc1 => not_lt.2 hτ hc1.1
        rw [ite_eq_right hnot, mul_zero, add_zero] at hj
        exact hj
      have hconst_int : IntegrableOn
          (fun _ : ℝ => 2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)))
          (Ioi 0) (hankelDmNeg c f) := integrableOn_const (hs := (measure_lt_top (hankelDmNeg c f) _).ne)
      -- We know `J₁` is integrable on `hankelDmNeg c f` from `hfubini`
      have hJ₁_neg_int : IntegrableOn J₁ (Ioi 0) (hankelDmNeg c f) := hInner_fub.2.2.integrableOn
      calc ‖∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmNeg c f‖
          ≤ ∫ ξ in Ioi (0 : ℝ), ‖J₁ ξ‖ ∂hankelDmNeg c f := norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Ioi (0 : ℝ),
              (2 * 27380416512 * (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)))
              ∂hankelDmNeg c f := integral_mono_ae hJ₁_neg_int.norm hconst_int hae
        _ ≤ _ := by
            rw [setIntegral_const, smul_eq_mul]
            have hmeas : (hankelDmNeg c f).real (Ioi 0) ≤ (hankelDmNeg c f univ).toReal :=
              ENNReal.toReal_mono (measure_ne_top (hankelDmNeg c f) univ) (measure_mono (subset_univ _))
            exact mul_le_of_le_one_left (by positivity) (hmeas.trans hdmNeg_le)
    -- Bound on `dmPos`:
    have hpos_bd := inner_dm_pos_bound hc hu0 hu3 hr_lb hr_RJ hRJ_ub hσ₀ hfinP hdmPos_le
      hInner_fub.2.1.integrableOn hJ₁_pt
    -- Combine `hpos_bd` and `hneg_bd` via `hInner_fub.1`, converting `1 / ζ₀.re * c^(5/6)` to `r`:
    have hinv_re : (1 / ζ₀.re) * c ^ (5 / 6 : ℝ) ≤ (3 / P.κ_ζ / Real.cos ψ) * c ^ (7 / 6 : ℝ) * r ^ (-(1 / 2 : ℝ)) := by
      have h1 : 1 / ζ₀.re ≤ (3 / P.κ_ζ) * c ^ (1 / 3 : ℝ) * r ^ (-(1 / 2 : ℝ)) / Real.cos ψ := by
        rw [one_div, inv_le_iff_one_le_mul₀' hσ₀]
        have hc13 : c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; simp
        have hr12 : Real.sqrt r * r ^ (-(1 / 2 : ℝ)) = 1 := by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr0]; simp
        calc (1 : ℝ) = ((P.κ_ζ / 3) * (3 / P.κ_ζ)) * (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) *
              (Real.sqrt r * r ^ (-(1 / 2 : ℝ))) * (Real.cos ψ / Real.cos ψ) := by
              rw [hc13, hr12]; field_simp
          _ = ((P.κ_ζ / 3) * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r * Real.cos ψ) *
                ((3 / P.κ_ζ) * c ^ (1 / 3 : ℝ) * r ^ (-(1 / 2 : ℝ)) / Real.cos ψ) := by ring
          _ ≤ ζ₀.re * ((3 / P.κ_ζ) * c ^ (1 / 3 : ℝ) * r ^ (-(1 / 2 : ℝ)) / Real.cos ψ) := by
              exact mul_le_mul_of_nonneg_right hσ₀_lb (by positivity)
      have hc76 : c ^ (1 / 3 : ℝ) * c ^ (5 / 6 : ℝ) = c ^ (7 / 6 : ℝ) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc (1 / ζ₀.re) * c ^ (5 / 6 : ℝ)
          ≤ ((3 / P.κ_ζ) * c ^ (1 / 3 : ℝ) * r ^ (-(1 / 2 : ℝ)) / Real.cos ψ) * c ^ (5 / 6 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (3 / P.κ_ζ / Real.cos ψ) * (c ^ (1 / 3 : ℝ) * c ^ (5 / 6 : ℝ)) * r ^ (-(1 / 2 : ℝ)) := by ring
        _ = _ := by rw [hc76]
    have hc_inv_ρ : c ^ (7 / 6 : ℝ) * r ^ (-(1 / 2 : ℝ)) * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) =
        P.κ_ζ ^ (1 / 2 : ℝ) * r ^ (-(1 / 4 : ℝ)) := by
      have hρ_def : ρr = P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * r ^ (1 / 2 : ℝ) := by
        show P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r = _; rw [Real.sqrt_eq_rpow]
      rw [hρ_def, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hκ_pos.le (by positivity), ← Real.rpow_mul hc0.le, ← Real.rpow_mul hr0.le]
      have h1 : -(1 / 3 : ℝ) * (1 / 2 : ℝ) = -(1 / 6 : ℝ) := by norm_num
      have h2 : (1 / 2 : ℝ) * (1 / 2 : ℝ) = 1 / 4 := by norm_num
      rw [h1, h2]
      have hc0_eq : c ^ (7 / 6 : ℝ) * c⁻¹ * c ^ (-(1 / 6 : ℝ)) = 1 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      have hr0_eq : r ^ (-(1 / 2 : ℝ)) * r ^ (1 / 4 : ℝ) = r ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hr0]; norm_num
      calc c ^ (7 / 6 : ℝ) * r ^ (-(1 / 2 : ℝ)) * (c⁻¹ * (P.κ_ζ ^ (1 / 2 : ℝ) * c ^ (-(1 / 6 : ℝ)) * r ^ (1 / 4 : ℝ)))
          = P.κ_ζ ^ (1 / 2 : ℝ) * (c ^ (7 / 6 : ℝ) * c⁻¹ * c ^ (-(1 / 6 : ℝ))) *
              (r ^ (-(1 / 2 : ℝ)) * r ^ (1 / 4 : ℝ)) := by ring
        _ = _ := by rw [hc0_eq, hr0_eq, mul_one]
    have hc_cancel : c ^ (7 / 6 : ℝ) * c ^ (-(7 / 6 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc0]; simp
    have hr_12_sq : r ^ (-(1 / 2 : ℝ)) * r = r ^ (1 / 2 : ℝ) := by
      have hr1 : r ^ (-(1 / 2 : ℝ)) * r = r ^ (-(1 / 2 : ℝ)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      rw [hr1, ← Real.rpow_add hr0]; norm_num
    have hκ_pow : (3 / P.κ_ζ) * P.κ_ζ ^ (1 / 2 : ℝ) = 3 / P.κ_ζ ^ (1 / 2 : ℝ) := by
      rw [div_mul_eq_mul_div, div_eq_div_iff hκ_pos.ne' (Real.rpow_pos_of_pos hκ_pos _).ne']
      conv_lhs => rw [mul_assoc, ← Real.rpow_add hκ_pos]
      norm_num
    have hband_nn : 0 ≤ ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f := by
      refine setIntegral_nonneg measurableSet_Icc fun ξ hξ => ?_
      have htb := hankelBandTau0_band hc hu0 hu3 hr_til_pos.le hr_til_A hξ
      have hCτ_pos : 0 < P.C_τ * c ^ (-(2 / 3 : ℝ)) := by have := P.hC_τ; positivity
      exact nonneg_of_mul_nonneg_right ((sq_nonneg (hankelBandTau0 ξ)).trans htb) hCτ_pos
    have hB2_RJ_nn : 0 ≤ hankelBootB2 c f R_J := hankelBootB2_nonneg c f R_J
    have hκ_pos' : 0 < P.κ_ζ := P.hκ_ζ
    have hCτ_pos' : 0 < P.C_τ := P.hC_τ
    calc ‖∫ τ : ℝ, innerFn τ‖
        = ‖(∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmPos c f) - ∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmNeg c f‖ := by
            rw [hInner_fub.1]
      _ ≤ ‖∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmPos c f‖ + ‖∫ ξ in Ioi (0 : ℝ), J₁ ξ ∂hankelDmNeg c f‖ :=
            norm_sub_le _ _
      _ ≤ 2 * 27380416512 * ((1 / ζ₀.re) * c ^ (5 / 6 : ℝ)) *
            (2 * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) +
              P.C_τ * c ^ (-(7 / 6 : ℝ)) *
                ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f +
              1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r * hankelBootB2 c f R_J) := by
            linarith only [hpos_bd, hneg_bd]
      _ ≤ 2 * 27380416512 * ((3 / P.κ_ζ / Real.cos ψ) * c ^ (7 / 6 : ℝ) * r ^ (-(1 / 2 : ℝ))) *
            (2 * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) +
              P.C_τ * c ^ (-(7 / 6 : ℝ)) *
                ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f +
              1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r * hankelBootB2 c f R_J) := by
            have hrhs_nn : 0 ≤ 2 * (c⁻¹ * ρr ^ (1 / 2 : ℝ)) +
                P.C_τ * c ^ (-(7 / 6 : ℝ)) *
                  ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f +
                1024 * P.κ_ζ ^ 2 * c ^ (-(7 / 6 : ℝ)) * r * hankelBootB2 c f R_J :=
              add_nonneg (add_nonneg (mul_nonneg zero_le_two (mul_nonneg (inv_nonneg.2 hc0.le)
                (Real.rpow_nonneg hρr_pos.le _))) (mul_nonneg (mul_nonneg hCτ_pos'.le
                  (Real.rpow_nonneg hc0.le _)) hband_nn))
                (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
                  (Real.rpow_nonneg hc0.le _)) hr0.le) hB2_RJ_nn)
            have h1 := mul_le_mul_of_nonneg_left hinv_re (by norm_num : (0 : ℝ) ≤ 2 * 27380416512)
            exact mul_le_mul_of_nonneg_right (by linarith only [h1]) hrhs_nn
      _ = 2 * 27380416512 * (3 / P.κ_ζ / Real.cos ψ) *
            (2 * (c ^ (7 / 6 : ℝ) * r ^ (-(1 / 2 : ℝ)) * (c⁻¹ * ρr ^ (1 / 2 : ℝ))) +
              P.C_τ * (c ^ (7 / 6 : ℝ) * c ^ (-(7 / 6 : ℝ))) * r ^ (-(1 / 2 : ℝ)) *
                ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f +
              1024 * P.κ_ζ ^ 2 * (c ^ (7 / 6 : ℝ) * c ^ (-(7 / 6 : ℝ))) * (r ^ (-(1 / 2 : ℝ)) * r) *
                hankelBootB2 c f R_J) := by ring
      _ = (4 * 27380416512 * ((3 / P.κ_ζ) * P.κ_ζ ^ (1 / 2 : ℝ)) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
            (2 * 27380416512 * (3 / P.κ_ζ) * P.C_τ / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) *
              ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f +
            (2 * 27380416512 * (3 / P.κ_ζ) * 1024 * P.κ_ζ ^ 2 / Real.cos ψ) * r ^ (1 / 2 : ℝ) *
              hankelBootB2 c f R_J := by
            rw [hc_inv_ρ, hc_cancel, hr_12_sq]; ring
      _ = (4 * 27380416512 * (3 / P.κ_ζ ^ (1 / 2 : ℝ)) / Real.cos ψ) * r ^ (-(1 / 4 : ℝ)) +
            (2 * 27380416512 * (3 / P.κ_ζ) * P.C_τ / Real.cos ψ) * r ^ (-(1 / 2 : ℝ)) *
              ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f +
            (2 * 27380416512 * (3 / P.κ_ζ) * 1024 * P.κ_ζ ^ 2 / Real.cos ψ) * r ^ (1 / 2 : ℝ) *
              hankelBootB2 c f R_J := by rw [hκ_pow]
  -- Bound the outer integral `∫ outerFn` via `outer_half_osc_bound`:
  have hOuter_bd : ‖∫ τ : ℝ, outerFn τ‖ ≤
      (8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ)) +
      (4 * 3e15 * P.κ_ζ) * r ^ (1 / 2 : ℝ) * hankelBootB2 c f r := by
    let J₂ : ℝ → ℂ := fun ξ => ∫ τ : ℝ, (ψ_r τ : ℂ) * (stripPoissonQ ζ₀.re ζ₀.im ε τ : ℂ) *
      tebAmp0 c τ * hankelBandK c τ ξ
    have hJ₂_pt : ∀ ξ ∈ Ioi (0 : ℝ), ‖J₂ ξ‖ ≤
        2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) *
          (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)) + c ^ (-(1 / 2 : ℝ)) * (if 4 * ρr < hankelBandTau0 ξ then 1 else 0)) := by
      intro ξ hξ
      have hζ₀_eq : (ζ₀.re : ℂ) + (ζ₀.im : ℂ) * Complex.I = ζ₀ := Complex.re_add_im ζ₀
      have hζ₀_hi' : ‖(ζ₀.re : ℂ) + (ζ₀.im : ℂ) * Complex.I‖ ≤ 2 * rhoR hankelBandParams c r := by
        rw [hζ₀_eq]; exact hζ₀_hi
      have hpos := outer_half_osc_bound hc hσ₀ hσ₀_le hε_abs (Or.inl rfl) hξ hr_lb hζ₀_hi'
      have hneg := outer_half_osc_bound hc hσ₀ hσ₀_le hε_abs (Or.inr rfl) hξ hr_lb hζ₀_hi'
      exact (scale_J_norm_le hc hσ₀ hσ₁ hQ_pt (tebCutoff_continuous (4 * ρr))
        (tebCutoff_even (4 * ρr)) hψr_bd hpos.2 hneg.2).trans_eq (by ring)
    have hu_abs : |u_T| ≤ langerRadius c := hankelBoot_abs_uT hc hu0 hu3
    have hξT_pos : 0 < hankelXi c u_T := hankelXi_pos hc0 hu_abs
    have hrA_r : |-r| ≤ langerRadius c := by
      rw [abs_neg, abs_of_pos hr0]
      exact hr_RJ.trans (hRJ_ub.trans (hankelBand_radius_ge_one hc))
    have hξr_lt : hankelXi c u_T ≤ hankelXi c (-r) :=
      le_of_mul_le_mul_left (hankel_phi_anti hc0 hrA_r hu_abs (by linarith only [hr_lb, hu3])) hc0
    have hneg_bd2 : ‖∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmNeg c f‖ ≤
        2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) := by
      have hae : ∀ᵐ ξ ∂(hankelDmNeg c f).restrict (Ioi 0),
          ‖J₂ ξ‖ ≤ 2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) := by
        rw [ae_restrict_iff' measurableSet_Ioi]
        have hlt : ∀ᵐ ξ ∂hankelDmNeg c f, ξ < hankelXi c u_T := by
          rw [ae_iff]; simp only [not_lt]; exact hdm_neg_tail
        filter_upwards [hlt] with ξ hξ_lt hξ_pos
        have hτ := tau0_lt_two_rhoR_of_xi_le hc hRJ_ub hr0 hr_RJ (hξ_lt.le.trans hξr_lt)
        change hankelBandTau0 ξ < 2 * ρr at hτ
        have hnot : ¬ (4 * ρr < hankelBandTau0 ξ) := by linarith only [hτ, hρr_pos]
        have hj := hJ₂_pt ξ hξ_pos
        rw [ite_eq_right hnot, mul_zero, add_zero] at hj
        exact hj
      have hconst_int : IntegrableOn
          (fun _ : ℝ => 2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))))
          (Ioi 0) (hankelDmNeg c f) := integrableOn_const (hs := (measure_lt_top (hankelDmNeg c f) _).ne)
      calc ‖∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmNeg c f‖
          ≤ ∫ ξ in Ioi (0 : ℝ), ‖J₂ ξ‖ ∂hankelDmNeg c f := norm_integral_le_integral_norm _
        _ ≤ ∫ _ in Ioi (0 : ℝ),
              (2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))))
              ∂hankelDmNeg c f := integral_mono_ae hOuter_fub.2.2.integrableOn.norm hconst_int hae
        _ ≤ _ := by
            rw [setIntegral_const, smul_eq_mul]
            have hmeas : (hankelDmNeg c f).real (Ioi 0) ≤ (hankelDmNeg c f univ).toReal :=
              ENNReal.toReal_mono (measure_ne_top (hankelDmNeg c f) univ) (measure_mono (subset_univ _))
            have hnn : 0 ≤ 2 * 3e15 * ζ₀.re * c ^ (5 / 6 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) :=
              mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hσ₀.le) (Real.rpow_nonneg hc0.le _))
                (mul_nonneg (inv_nonneg.2 hc0.le) (Real.rpow_nonneg hρr_pos.le _))
            exact mul_le_of_le_one_left hnn (hmeas.trans hdmNeg_le)
    have hpos_bd2 := outer_dm_pos_bound hc hu0 hu3 hr_lb hr_RJ hRJ_ub hσ₀ hfinP hdmPos_le
      hOuter_fub.2.1.integrableOn hJ₂_pt
    have hre_c : ζ₀.re * c ^ (5 / 6 : ℝ) ≤ 2 * P.κ_ζ * c ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) := by
      have h1 : ζ₀.re ≤ 2 * P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * r ^ (1 / 2 : ℝ) := by
        calc ζ₀.re ≤ ‖ζ₀‖ := Complex.re_le_norm ζ₀
          _ ≤ 2 * ρr := hζ₀_hi
          _ = 2 * P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * r ^ (1 / 2 : ℝ) := by
              show 2 * (P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r) = _; rw [Real.sqrt_eq_rpow]; ring
      have hc12 : c ^ (-(1 / 3 : ℝ)) * c ^ (5 / 6 : ℝ) = c ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hc0]; norm_num
      calc ζ₀.re * c ^ (5 / 6 : ℝ)
          ≤ (2 * P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * r ^ (1 / 2 : ℝ)) * c ^ (5 / 6 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = 2 * P.κ_ζ * (c ^ (-(1 / 3 : ℝ)) * c ^ (5 / 6 : ℝ)) * r ^ (1 / 2 : ℝ) := by ring
        _ = _ := by rw [hc12]
    have hc_out_1 : c ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) =
        P.κ_ζ ^ (-(3 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ)) := by
      have hρ_def : ρr = P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * r ^ (1 / 2 : ℝ) := by
        show P.κ_ζ * c ^ (-(1 / 3 : ℝ)) * Real.sqrt r = _; rw [Real.sqrt_eq_rpow]
      rw [hρ_def, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow hκ_pos.le (by positivity), ← Real.rpow_mul hc0.le, ← Real.rpow_mul hr0.le]
      have h1 : -(1 / 3 : ℝ) * -(3 / 2 : ℝ) = 1 / 2 := by norm_num
      have h2 : (1 / 2 : ℝ) * -(3 / 2 : ℝ) = -(3 / 4 : ℝ) := by norm_num
      rw [h1, h2]
      have hc0_eq : c ^ (1 / 2 : ℝ) * c⁻¹ * c ^ (1 / 2 : ℝ) = 1 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
      have hr0_eq : r ^ (1 / 2 : ℝ) * r ^ (-(3 / 4 : ℝ)) = r ^ (-(1 / 4 : ℝ)) := by
        rw [← Real.rpow_add hr0]; norm_num
      calc c ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) * (c⁻¹ * (P.κ_ζ ^ (-(3 / 2 : ℝ)) * c ^ (1 / 2 : ℝ) * r ^ (-(3 / 4 : ℝ))))
          = P.κ_ζ ^ (-(3 / 2 : ℝ)) * (c ^ (1 / 2 : ℝ) * c⁻¹ * c ^ (1 / 2 : ℝ)) *
              (r ^ (1 / 2 : ℝ) * r ^ (-(3 / 4 : ℝ))) := by ring
        _ = _ := by rw [hc0_eq, hr0_eq, mul_one]
    have hc_out_2 : c ^ (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hc0]; simp
    have hκ_out : P.κ_ζ * P.κ_ζ ^ (-(3 / 2 : ℝ)) = 1 / P.κ_ζ ^ (1 / 2 : ℝ) := by
      have h1 : P.κ_ζ * P.κ_ζ ^ (-(3 / 2 : ℝ)) = P.κ_ζ ^ (1 : ℝ) * P.κ_ζ ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_one]
      rw [h1, ← Real.rpow_add hκ_pos, one_div, ← Real.rpow_neg hκ_pos.le]; norm_num
    have hB2_r_nn : 0 ≤ hankelBootB2 c f r := hankelBootB2_nonneg c f r
    calc ‖∫ τ : ℝ, outerFn τ‖
        = ‖(∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmPos c f) - ∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmNeg c f‖ := by
            rw [hOuter_fub.1]
      _ ≤ ‖∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmPos c f‖ + ‖∫ ξ in Ioi (0 : ℝ), J₂ ξ ∂hankelDmNeg c f‖ :=
            norm_sub_le _ _
      _ ≤ 2 * 3e15 * (ζ₀.re * c ^ (5 / 6 : ℝ)) *
            (2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) + c ^ (-(1 / 2 : ℝ)) * hankelBootB2 c f r) := by
            linarith only [hpos_bd2, hneg_bd2]
      _ ≤ 2 * 3e15 * (2 * P.κ_ζ * c ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ)) *
            (2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) + c ^ (-(1 / 2 : ℝ)) * hankelBootB2 c f r) := by
            have hrhs : 0 ≤ 2 * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ))) + c ^ (-(1 / 2 : ℝ)) * hankelBootB2 c f r :=
              add_nonneg (mul_nonneg zero_le_two (mul_nonneg (inv_nonneg.2 hc0.le) (Real.rpow_nonneg hρr_pos.le _)))
                (mul_nonneg (Real.rpow_nonneg hc0.le _) hB2_r_nn)
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hre_c (by norm_num)) hrhs
      _ = 4 * 3e15 * P.κ_ζ *
            (2 * (c ^ (1 / 2 : ℝ) * r ^ (1 / 2 : ℝ) * (c⁻¹ * ρr ^ (-(3 / 2 : ℝ)))) +
              (c ^ (1 / 2 : ℝ) * c ^ (-(1 / 2 : ℝ))) * r ^ (1 / 2 : ℝ) * hankelBootB2 c f r) := by ring
      _ = 8 * 3e15 * (P.κ_ζ * P.κ_ζ ^ (-(3 / 2 : ℝ))) * r ^ (-(1 / 4 : ℝ)) +
            (4 * 3e15 * P.κ_ζ) * r ^ (1 / 2 : ℝ) * hankelBootB2 c f r := by
            rw [hc_out_1, hc_out_2]; ring
      _ = (8 * 3e15 / P.κ_ζ ^ (1 / 2 : ℝ)) * r ^ (-(1 / 4 : ℝ)) +
            (4 * 3e15 * P.κ_ζ) * r ^ (1 / 2 : ℝ) * hankelBootB2 c f r := by
            rw [hκ_out]; ring
  -- Combine Core, Inner, Outer and divide by `‖tebPrefactor c ζ₀‖ ≥ (1 / 128) * r^(5/4)`:
  set r_til := min (1028 * r) R_J
  have hr_til_pos : 0 < r_til := lt_min (by positivity) (lt_of_lt_of_le hr0 hr_RJ)
  have hr_til_RJ : r_til ≤ R_J := min_le_right _ _
  have hr_til_A : r_til ≤ langerRadius c := hr_til_RJ.trans (hRJ_ub.trans (hankelBand_radius_ge_one hc))
  have hband_nn : 0 ≤ ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂hankelDmPos c f := by
    refine setIntegral_nonneg measurableSet_Icc fun ξ hξ => ?_
    have htb := hankelBandTau0_band hc hu0 hu3 hr_til_pos.le hr_til_A hξ
    have hCτ_pos : 0 < P.C_τ * c ^ (-(2 / 3 : ℝ)) := by have := P.hC_τ; positivity
    exact nonneg_of_mul_nonneg_right ((sq_nonneg (hankelBandTau0 ξ)).trans htb) hCτ_pos
  have hB2_r_nn : 0 ≤ hankelBootB2 c f r := hankelBootB2_nonneg c f r
  have hB2_RJ_nn : 0 ≤ hankelBootB2 c f R_J := hankelBootB2_nonneg c f R_J
  have h_tri : ‖H ζ₀‖ ≤ ‖∫ τ : ℝ, coreFn τ‖ + ‖∫ τ : ℝ, innerFn τ‖ + ‖∫ τ : ℝ, outerFn τ‖ := by
    rw [hH_split]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hpf_pos : 0 < ‖tebPrefactor c ζ₀‖ := lt_of_lt_of_le (by positivity) hpf_lb
  have hpf_lb' : (1 / 128 : ℝ) * r ^ (5 / 4 : ℝ) ≤ ‖tebPrefactor c ζ₀‖ :=
    (mul_le_mul_of_nonneg_right hC_pf_lb hr_54_pos.le).trans hpf_lb
  have hW_eq_div : ‖hankelWtS c ε f ζ₀‖ = ‖H ζ₀‖ / ‖tebPrefactor c ζ₀‖ := by
    dsimp [H]; rw [norm_mul, mul_div_cancel_left₀ _ hpf_pos.ne']
  rw [hW_eq_div]
  exact hankel_scale_combine hr_lb hcos_pos hband_nn hB2_r_nn hB2_RJ_nn (norm_nonneg _)
    h_tri hCore_bd hInner_bd hOuter_bd hpf_lb'

/-- Corollary of `hankel_scale_band_reduction` rewriting the band integral via `hankelBootB1`
at `r̃ = min (1028 * r) R_J`. -/
theorem hankel_scale_band_reduction_B1 {c ε T u_T R_J r : ℝ} {f : ℝ → ℝ}
    (hc : 3e6 ≤ c) (hε : ε = 1 ∨ ε = -1) (hf : IsHankelEigenfn c ε f) (hmass : hankelMass c f = 1)
    (hu0 : u_T ≤ 0) (hu3 : -3 ≤ u_T) (hT : c * hankelXi c u_T = T)
    (htail : ∀ Δ : ℝ, T ≤ Δ → 0 ≤ f Δ)
    (hRJ_lb : (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) ≤ R_J)
    (hRJ_ub : R_J ≤ (1 / 100 : ℝ) ^ 2 * c ^ (2 / 3 : ℝ) + 1)
    (hr_lb : 256 ≤ r) (hr_RJ : r ≤ R_J)
    {ζ₀ : ℂ} {ψ : ℝ}
    (hζ₀_lo : rhoR hankelBandParams c r / 3 ≤ ‖ζ₀‖)
    (hζ₀_hi : ‖ζ₀‖ ≤ 2 * rhoR hankelBandParams c r)
    (hcos_eq : ζ₀.re = ‖ζ₀‖ * Real.cos ψ)
    (hcos_pos : 0 < Real.cos ψ) :
    let r_til := min (1028 * r) R_J
    ‖hankelWtS c ε f ζ₀‖ ≤ hankelScaleBandC *
      (r ^ (-(3 / 2 : ℝ)) +
        r ^ (-(7 / 4 : ℝ)) * r_til * hankelBootB1 c f r_til u_T +
        r ^ (-(3 / 4 : ℝ)) * (hankelBootB2 c f r + hankelBootB2 c f R_J)) / Real.cos ψ := by
  intro r_til
  have hr_til_pos : 0 < r_til := lt_min (by positivity) (lt_of_lt_of_le (by linarith) hr_RJ)
  have hB1 : ∫ ξ in Icc (hankelXi c u_T) (hankelXi c (-r_til)), (-hankelBandU c ξ) ∂(hankelDmPos c f) =
      r_til * hankelBootB1 c f r_til u_T := by
    unfold hankelBootB1
    rw [mul_inv_cancel_left₀ hr_til_pos.ne']
  rw [mul_assoc, ← hB1]
  exact hankel_scale_band_reduction hc hε hf hmass hu0 hu3 hT htail hRJ_lb hRJ_ub hr_lb hr_RJ
    hζ₀_lo hζ₀_hi hcos_eq hcos_pos

/-- info: 'FormalResearch.SignUncertainty.hankel_scale_band_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_scale_band_reduction

/-- info: 'FormalResearch.SignUncertainty.hankel_scale_band_reduction_B1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankel_scale_band_reduction_B1

end Assembly

end FormalResearch.SignUncertainty

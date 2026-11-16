module

public import FormalResearch.Special.JacobiMehlerHeine

/-!
# Mehler–Heine formula with a rate

`mehlerHeine_rate`: for `α > -1`, real `β`, `R ≥ 0` there are `C, N` with

  `‖n^{-α} P_n^{(α,β)}(cos(z/n)) - mhLimit α z‖ ≤ C/n`  for `n ≥ N`, `‖z‖ ≤ R`

(`mhLimit α z = ∑ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1)) = (z/2)^{-α} J_α(z)`, see
`FormalResearch/Special/JacobiMehlerHeine.lean`); `mehlerHeine_rate_isBigO` is the `IsBigO` form
along `𝓟 (closedBall 0 R) ×ˢ atTop`, the order-one remainder in the sense of
`FormalResearch.Asymptotics.HasExpansionAlong`.  The constants `C, N` are not explicit.

## Method

* exact factorisation `mhCoeff = (1/(ℓ! Γ(α+ℓ+1))) · P · W · G` (`mhCoeff_eq`) with
  `P = (n+γ)_ℓ/n^ℓ = ∏_{j<ℓ}(1 + (γ+j)/n)`, `W = n!/((n-ℓ)! n^ℓ) = ∏_{j<ℓ}(1 - j/n)` and
  `G = n^{-α}Γ(n+α+1)/Γ(n+1)`, so that `mhCoeff - A_ℓ = A_ℓ (P W G - 1)`;
* `|P - 1| ≤ exp(ℓ(|γ|+ℓ)/n) - 1` (`mhP_sub_one_le`), `1 - ℓ(ℓ-1)/(2n) ≤ W ≤ 1`
  (`mhW_bounds`), `|G - 1| ≤ c/n` (`mhG_bound`, from `GammaRatio.gamma_ratio_two_term`);
* for `2ℓ(|γ|+ℓ) ≤ n` these give `|mhCoeff - A_ℓ| ≤ A_ℓ (4ℓ(|γ|+ℓ)+ℓ²+c)/n`
  (`mhCoeff_sub_le_small`); in the complementary range `|mhCoeff| + A_ℓ ≤ 2B_ℓ` with the majorant of
  `abs_mhCoeff_le` already carries a factor `ℓ(|γ|+ℓ)/n` (`mhCoeff_sub_le`);
* `|n sin(z/(2n)) - z/2| ≤ max(R,1)²/n`, and the rate version of the uniform Tannery theorem
  (`FormalResearch.Asymptotics.norm_sum_sub_tsum_le_of_rate`; the tail `ℓ > n` of the limit series is
  bounded by `(1/n) ∑ ℓ M_ℓ`).
-/

@[expose] public section

open Polynomial Filter Topology

namespace FormalResearch.Special

/-- `exp x ≤ 1 + 2x` for `0 ≤ x ≤ 1`. -/
lemma exp_le_one_add_two_mul {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : Real.exp x ≤ 1 + 2 * x := by
  have := Real.exp_bound' h0 h1 (n := 1) one_pos
  simp at this
  linarith

/-! ### The three factors of `mhCoeff` -/

/-- `(n+γ)_ℓ / n^ℓ`. -/
noncomputable def mhP (γ : ℝ) (n ℓ : ℕ) : ℝ :=
  (ascPochhammer ℝ ℓ).eval ((n : ℝ) + γ) / (n : ℝ) ^ ℓ

/-- `n!/((n-ℓ)! n^ℓ) = n (n-1) ⋯ (n-ℓ+1) / n^ℓ`. -/
noncomputable def mhW (n ℓ : ℕ) : ℝ := (n.descFactorial ℓ : ℝ) / (n : ℝ) ^ ℓ

/-- `n^{-α} Γ(n+α+1)/Γ(n+1)`. -/
noncomputable def mhG (α : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-α) * (Real.Gamma ((n : ℝ) + α + 1) / Real.Gamma ((n : ℝ) + 1))

/-- The exact factorisation `mhCoeff = (1/(ℓ! Γ(α+ℓ+1))) · P · W · G`. -/
lemma mhCoeff_eq (α β : ℝ) (hα : -1 < α) {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ ≤ n) :
    mhCoeff α β n ℓ = mhLimitCoeff α ℓ * mhP (α + β + 1) n ℓ * mhW n ℓ * mhG α n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hapos : 0 < α + ℓ + 1 := by
    have : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _; linarith
  have hG1 := Real.Gamma_pos_of_pos hapos
  have key := gamma_add_nat_eq (α + ℓ + 1) hapos (n - ℓ)
  have e1 : α + ℓ + 1 + ((n - ℓ : ℕ) : ℝ) = (n : ℝ) + α + 1 := by
    rw [Nat.cast_sub hℓ]; ring
  rw [e1] at key
  have hGn : 0 < Real.Gamma ((n : ℝ) + 1) := Real.Gamma_pos_of_pos (by positivity)
  have hGnf : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
  have hfac : ((n - ℓ).factorial : ℝ) * (n.descFactorial ℓ : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hℓ
  have hf1 : (ℓ.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero ℓ
  have hf2 : ((n - ℓ).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hf3 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  unfold mhCoeff mhLimitCoeff mhP mhW mhG
  rw [show (n : ℝ) + (α + β + 1) = (n : ℝ) + (α + β + 1) from rfl]
  have hR : (ascPochhammer ℝ (n - ℓ)).eval (α + ℓ + 1) =
      Real.Gamma ((n : ℝ) + α + 1) / Real.Gamma (α + ℓ + 1) := by
    rw [key]; field_simp
  rw [hR, hGnf, ← hfac]
  have hnl : (0 : ℝ) < (n : ℝ) ^ ℓ := by positivity
  have hn2 : (0 : ℝ) < (n : ℝ) ^ (2 * ℓ) := by positivity
  rw [pow_mul']
  have hdf : (n.descFactorial ℓ : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hfac
    exact hf3 hfac.symm
  field_simp

lemma cast_mul_pred_nonneg (ℓ : ℕ) : (0 : ℝ) ≤ (ℓ : ℝ) * ((ℓ : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ ℓ := by exact_mod_cast h
    exact mul_nonneg (by linarith) (by linarith)

/-- `W = n!/((n-ℓ)! n^ℓ)` lies in `[1 - ℓ(ℓ-1)/(2n), 1]` for `ℓ ≤ n`. -/
lemma mhW_bounds {n : ℕ} (hn : 1 ≤ n) (ℓ : ℕ) (hℓ : ℓ ≤ n) :
    1 - (ℓ : ℝ) * ((ℓ : ℝ) - 1) / (2 * n) ≤ mhW n ℓ ∧ mhW n ℓ ≤ 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  induction ℓ with
  | zero => simp [mhW]
  | succ ℓ ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hℓn : (ℓ : ℝ) ≤ n := by exact_mod_cast (show ℓ ≤ n by omega)
    have hrec : mhW n (ℓ + 1) = mhW n ℓ * (1 - (ℓ : ℝ) / n) := by
      unfold mhW
      rw [Nat.descFactorial_succ, pow_succ, Nat.cast_mul, Nat.cast_sub (by omega)]
      field_simp
    have hb0 : 0 ≤ 1 - (ℓ : ℝ) / n := by
      rw [sub_nonneg, div_le_one hnpos]; exact hℓn
    have hW0 : 0 ≤ mhW n ℓ := by
      unfold mhW; positivity
    have ha0 : 0 ≤ (ℓ : ℝ) * ((ℓ : ℝ) - 1) / (2 * n) :=
      div_nonneg (cast_mul_pred_nonneg ℓ) (by positivity)
    rw [hrec]
    refine ⟨?_, ?_⟩
    · have h3 : (1 - (ℓ : ℝ) * ((ℓ : ℝ) - 1) / (2 * n)) * (1 - (ℓ : ℝ) / n) ≤
          mhW n ℓ * (1 - (ℓ : ℝ) / n) := mul_le_mul_of_nonneg_right h1 hb0
      have h4 : (ℓ : ℝ) * ((ℓ : ℝ) - 1) / (2 * n) * ((ℓ : ℝ) / n) ≥ 0 := by
        have : 0 ≤ (ℓ : ℝ) / n := by positivity
        positivity
      have h5 : ((ℓ + 1 : ℕ) : ℝ) * (((ℓ + 1 : ℕ) : ℝ) - 1) / (2 * n) =
          (ℓ : ℝ) * ((ℓ : ℝ) - 1) / (2 * n) + (ℓ : ℝ) / n := by
        push_cast; field_simp; ring
      rw [h5]
      nlinarith
    · calc mhW n ℓ * (1 - (ℓ : ℝ) / n) ≤ 1 * 1 :=
          mul_le_mul h2 (by have : 0 ≤ (ℓ : ℝ) / n := by positivity
                            linarith) hb0 zero_le_one
        _ = 1 := one_mul 1

/-- `|P_ℓ - 1| ≤ exp(ℓ(|γ|+ℓ)/n) - 1`. -/
lemma mhP_sub_one_le (γ : ℝ) {n : ℕ} (hn : 1 ≤ n) (ℓ : ℕ) :
    |mhP γ n ℓ - 1| ≤ Real.exp ((ℓ : ℝ) * (|γ| + ℓ) / n) - 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  induction ℓ with
  | zero => simp [mhP]
  | succ ℓ ih =>
    set u : ℝ := (γ + ℓ) / n with hu
    have hrec : mhP γ n (ℓ + 1) = mhP γ n ℓ * (1 + u) := by
      unfold mhP
      rw [ascPochhammer_succ_eval, pow_succ, hu]
      field_simp
      ring
    have hu' : |u| ≤ (|γ| + ℓ) / n := by
      rw [hu, abs_div, abs_of_pos hnpos]
      gcongr
      refine (abs_add_le _ _).trans ?_
      simp
    have e1 : mhP γ n (ℓ + 1) - 1 = (mhP γ n ℓ - 1) * (1 + u) + u := by rw [hrec]; ring
    set x : ℝ := (ℓ : ℝ) * (|γ| + ℓ) / n with hx
    have hx' : x + |u| ≤ ((ℓ + 1 : ℕ) : ℝ) * (|γ| + ((ℓ + 1 : ℕ) : ℝ)) / n := by
      have : x + (|γ| + ℓ) / n ≤ ((ℓ + 1 : ℕ) : ℝ) * (|γ| + ((ℓ + 1 : ℕ) : ℝ)) / n := by
        rw [hx, ← add_div]
        gcongr
        push_cast
        nlinarith [abs_nonneg γ, (Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
      linarith
    have hxe : Real.exp x * Real.exp |u| ≤
        Real.exp (((ℓ + 1 : ℕ) : ℝ) * (|γ| + ((ℓ + 1 : ℕ) : ℝ)) / n) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 hx'
    have h1u : |1 + u| ≤ 1 + |u| := (abs_add_le _ _).trans (by simp)
    have hex0 : 0 ≤ Real.exp x - 1 := by
      have := (abs_nonneg _).trans ih; exact this
    rw [e1]
    calc |(mhP γ n ℓ - 1) * (1 + u) + u|
        ≤ |mhP γ n ℓ - 1| * |1 + u| + |u| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul]
      _ ≤ (Real.exp x - 1) * (1 + |u|) + |u| :=
          add_le_add (mul_le_mul ih h1u (abs_nonneg _) hex0) le_rfl
      _ = Real.exp x * (1 + |u|) - 1 := by ring
      _ ≤ Real.exp x * Real.exp |u| - 1 := by
          have := Real.add_one_le_exp |u|
          have h := Real.exp_pos x
          nlinarith
      _ ≤ _ := by linarith

/-- `G_n = n^{-α} Γ(n+α+1)/Γ(n+1) = 1 + O(1/n)` (from the two-term Gamma-ratio expansion). -/
lemma mhG_bound (α : ℝ) :
    ∃ cg : ℝ, 0 ≤ cg ∧ ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → |mhG α n - 1| ≤ cg / n ∧ mhG α n ≤ 2 := by
  have h := GammaRatio.gamma_ratio_two_term (α + 1) 1
  obtain ⟨c, hc⟩ := h.bound
  have hc' := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hc
  rw [eventually_atTop] at hc'
  obtain ⟨N0, hN0⟩ := hc'
  set c1 : ℝ := (α + 1 - 1) * (α + 1 + 1 - 1) / 2 with hc1
  refine ⟨|c1| + |c|, by positivity, max (max N0 1) ⌈|c1| + |c|⌉₊, by omega, ?_⟩
  intro n hn
  have hnN0 : N0 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hnc : |c1| + |c| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hb := hN0 n hnN0
  simp only [norm_mul, Real.norm_eq_abs] at hb
  have hαe : α + 1 - 1 = α := by ring
  rw [hαe] at hb
  have hpos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnpos _
  rw [abs_of_pos hpos, abs_pow, abs_inv, abs_of_pos hnpos] at hb
  have hmul : mhG α n - 1 - c1 / n =
      (n : ℝ) ^ (-α) * (Real.Gamma ((n : ℝ) + (α + 1)) / Real.Gamma ((n : ℝ) + 1) -
        (n : ℝ) ^ α * (1 + c1 * (n : ℝ)⁻¹)) := by
    unfold mhG
    rw [show (n : ℝ) + α + 1 = (n : ℝ) + (α + 1) by ring, Real.rpow_neg hnpos.le]
    field_simp
    ring
  have h1 : |mhG α n - 1 - c1 / n| ≤ |c| / (n : ℝ) ^ 2 := by
    rw [hmul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hnpos (-α))]
    calc (n : ℝ) ^ (-α) * |Real.Gamma ((n : ℝ) + (α + 1)) / Real.Gamma ((n : ℝ) + 1) -
          (n : ℝ) ^ α * (1 + c1 * (n : ℝ)⁻¹)|
        ≤ (n : ℝ) ^ (-α) * (c * ((n : ℝ) ^ α * ((n : ℝ)⁻¹) ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (Real.rpow_pos_of_pos hnpos _).le
      _ ≤ (n : ℝ) ^ (-α) * (|c| * ((n : ℝ) ^ α * ((n : ℝ)⁻¹) ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self c) (by positivity))
            (Real.rpow_pos_of_pos hnpos _).le
      _ = |c| / (n : ℝ) ^ 2 := by
          rw [Real.rpow_neg hnpos.le]
          field_simp
  have h2 : |mhG α n - 1| ≤ (|c1| + |c|) / n := by
    have h3 : |mhG α n - 1| ≤ |mhG α n - 1 - c1 / n| + |c1 / n| := by
      calc |mhG α n - 1| = |(mhG α n - 1 - c1 / n) + c1 / n| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h4 : |c1 / n| = |c1| / n := by rw [abs_div, abs_of_pos hnpos]
    have h5 : |c| / (n : ℝ) ^ 2 ≤ |c| / n := by
      have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      apply div_le_div_of_nonneg_left (abs_nonneg c) hnpos
      nlinarith
    rw [add_div]
    linarith
  refine ⟨h2, ?_⟩
  have : (|c1| + |c|) / n ≤ 1 := by rw [div_le_one hnpos]; exact hnc
  linarith [le_abs_self (mhG α n - 1)]

lemma mhG_pos (α : ℝ) (hα : -1 < α) {n : ℕ} (hn : 1 ≤ n) : 0 < mhG α n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 := Real.Gamma_pos_of_pos (show 0 < (n : ℝ) + 1 by positivity)
  unfold mhG
  have h : 0 < (n : ℝ) + α + 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have := Real.Gamma_pos_of_pos h
  positivity

/-- Regime `2ℓ(|γ|+ℓ) ≤ n`: `|mhCoeff - A_ℓ| ≤ A_ℓ (4ℓ(|γ|+ℓ) + ℓ² + c_g)/n`. -/
lemma mhCoeff_sub_le_small (α β : ℝ) (hα : -1 < α) {cg : ℝ} {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ ≤ n)
    (hg : |mhG α n - 1| ≤ cg / n) (hg2 : mhG α n ≤ 2)
    (hsmall : 2 * ((ℓ : ℝ) * (|α + β + 1| + ℓ)) ≤ n) :
    |mhCoeff α β n ℓ - mhLimitCoeff α ℓ| ≤
      mhLimitCoeff α ℓ * (4 * ((ℓ : ℝ) * (|α + β + 1| + ℓ)) + (ℓ : ℝ) ^ 2 + cg) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set γ := α + β + 1 with hγ
  set A := mhLimitCoeff α ℓ with hA
  have hA0 : 0 ≤ A := by
    have : 0 < Real.Gamma (α + ℓ + 1) :=
      Real.Gamma_pos_of_pos (by have : (0:ℝ) ≤ ℓ := Nat.cast_nonneg _; linarith)
    rw [hA, mhLimitCoeff]; positivity
  have hg0 := mhG_pos α hα hn
  obtain ⟨hW1, hW2⟩ := mhW_bounds hn ℓ hℓ
  have hW0 : 0 ≤ mhW n ℓ := by unfold mhW; positivity
  set x : ℝ := (ℓ : ℝ) * (|γ| + ℓ) / n with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ hnpos]; linarith
  have hP : |mhP γ n ℓ - 1| ≤ 2 * x := by
    refine (mhP_sub_one_le γ hn ℓ).trans ?_
    have := exp_le_one_add_two_mul hx0 (by linarith)
    linarith
  have hWm : |mhW n ℓ - 1| ≤ (ℓ : ℝ) ^ 2 / (2 * n) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    have : (ℓ : ℝ) * ((ℓ : ℝ) - 1) / (2 * n) ≤ (ℓ : ℝ) ^ 2 / (2 * n) := by
      gcongr
      nlinarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
    linarith
  have hmain : mhCoeff α β n ℓ - A =
      A * ((mhP γ n ℓ - 1) * mhW n ℓ * mhG α n + (mhW n ℓ - 1) * mhG α n + (mhG α n - 1)) := by
    rw [mhCoeff_eq α β hα hn hℓ]
    ring
  rw [hmain, abs_mul, abs_of_nonneg hA0]
  have hsum : |(mhP γ n ℓ - 1) * mhW n ℓ * mhG α n + (mhW n ℓ - 1) * mhG α n + (mhG α n - 1)| ≤
      (4 * ((ℓ : ℝ) * (|γ| + ℓ)) + (ℓ : ℝ) ^ 2 + cg) / n := by
    refine (abs_add_three _ _ _).trans ?_
    have t1 : |(mhP γ n ℓ - 1) * mhW n ℓ * mhG α n| ≤ 2 * x * 1 * 2 := by
      rw [abs_mul, abs_mul, abs_of_nonneg hW0, abs_of_pos hg0]
      exact mul_le_mul (mul_le_mul hP hW2 hW0 (by linarith)) hg2 hg0.le (by positivity)
    have t2 : |(mhW n ℓ - 1) * mhG α n| ≤ (ℓ : ℝ) ^ 2 / (2 * n) * 2 := by
      rw [abs_mul, abs_of_pos hg0]
      exact mul_le_mul hWm hg2 hg0.le (by positivity)
    have e : (4 * ((ℓ : ℝ) * (|γ| + ℓ)) + (ℓ : ℝ) ^ 2 + cg) / n =
        2 * x * 1 * 2 + (ℓ : ℝ) ^ 2 / (2 * n) * 2 + cg / n := by
      rw [hx]; field_simp; ring
    rw [e]
    linarith [hg]
  calc A * |_| ≤ A * ((4 * ((ℓ : ℝ) * (|γ| + ℓ)) + (ℓ : ℝ) ^ 2 + cg) / n) :=
        mul_le_mul_of_nonneg_left hsum hA0
    _ = _ := by ring

lemma mhLimitCoeff_nonneg (α : ℝ) (hα : -1 < α) (ℓ : ℕ) : 0 ≤ mhLimitCoeff α ℓ := by
  have : 0 < Real.Gamma (α + ℓ + 1) :=
    Real.Gamma_pos_of_pos (by have : (0:ℝ) ≤ ℓ := Nat.cast_nonneg _; linarith)
  rw [mhLimitCoeff]; positivity

/-- The majorant of `abs_mhCoeff_le` also bounds the limit coefficients, `ℓ ≥ 1`. -/
lemma mhLimitCoeff_le (α β : ℝ) (hα : -1 < α) {ℓ : ℕ} (hℓ1 : 1 ≤ ℓ) :
    mhLimitCoeff α ℓ ≤
      Real.exp α * (Real.exp 1 * (2 + |α + β + 1|)) ^ ℓ / (ℓ.factorial : ℝ) := by
  have h := (tendsto_mhCoeff α β hα ℓ).abs
  have hA : |1 / ((ℓ.factorial : ℝ) * Real.Gamma (α + ℓ + 1))| = mhLimitCoeff α ℓ :=
    abs_of_nonneg (mhLimitCoeff_nonneg α hα ℓ)
  rw [hA] at h
  refine le_of_tendsto h ?_
  filter_upwards [eventually_ge_atTop (max ℓ 1)] with n hn
  exact abs_mhCoeff_le α β hα (le_trans (le_max_right _ _) hn) hℓ1 (le_trans (le_max_left _ _) hn)

/-- **Coefficient rate** for `ℓ ≥ 1`: `|mhCoeff - A_ℓ| ≤ B_ℓ (4ℓ(|γ|+ℓ) + ℓ² + c_g)/n`, with the
majorant `B_ℓ = e^α (e(2+|γ|))^ℓ/ℓ!`, whenever `|G_n - 1| ≤ c_g/n`, `G_n ≤ 2`. -/
lemma mhCoeff_sub_le (α β : ℝ) (hα : -1 < α) {cg : ℝ} (hcg : 0 ≤ cg) {n ℓ : ℕ} (hn : 1 ≤ n)
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ n) (hg : |mhG α n - 1| ≤ cg / n) (hg2 : mhG α n ≤ 2) :
    |mhCoeff α β n ℓ - mhLimitCoeff α ℓ| ≤
      Real.exp α * (Real.exp 1 * (2 + |α + β + 1|)) ^ ℓ / (ℓ.factorial : ℝ) *
        (4 * ((ℓ : ℝ) * (|α + β + 1| + ℓ)) + (ℓ : ℝ) ^ 2 + cg) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set γ := α + β + 1 with hγ
  set B : ℝ := Real.exp α * (Real.exp 1 * (2 + |γ|)) ^ ℓ / (ℓ.factorial : ℝ) with hB
  have hA := mhLimitCoeff_le α β hα hℓ1
  have hA0 := mhLimitCoeff_nonneg α hα ℓ
  have hm := abs_mhCoeff_le α β hα hn hℓ1 hℓ
  have hκ : 0 ≤ 4 * ((ℓ : ℝ) * (|γ| + ℓ)) + (ℓ : ℝ) ^ 2 + cg := by positivity
  by_cases hs : 2 * ((ℓ : ℝ) * (|γ| + ℓ)) ≤ n
  · refine (mhCoeff_sub_le_small α β hα hn hℓ hg hg2 hs).trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA hκ) hnpos.le
  · rw [not_le] at hs
    have h1 : |mhCoeff α β n ℓ - mhLimitCoeff α ℓ| ≤ 2 * B := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hA0]
      linarith
    have hB0 : 0 ≤ B := hA0.trans hA
    refine h1.trans ?_
    have h2 : 2 * B ≤ B * (4 * ((ℓ : ℝ) * (|γ| + ℓ))) / n := by
      rw [le_div_iff₀ hnpos]
      nlinarith
    refine h2.trans ?_
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by nlinarith [sq_nonneg (ℓ : ℝ)]) hB0) hnpos.le

/-- **Coefficient rate** for `ℓ = 0`: `|mhCoeff - A_0| ≤ A_0 c_g/n`. -/
lemma mhCoeff_zero_sub_le (α β : ℝ) (hα : -1 < α) {cg : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hg : |mhG α n - 1| ≤ cg / n) :
    |mhCoeff α β n 0 - mhLimitCoeff α 0| ≤ mhLimitCoeff α 0 * cg / n := by
  have hA0 := mhLimitCoeff_nonneg α hα 0
  rw [mhCoeff_eq α β hα hn (Nat.zero_le n)]
  have : mhP (α + β + 1) n 0 = 1 := by simp [mhP]
  have hW : mhW n 0 = 1 := by simp [mhW]
  rw [this, hW]
  have e : mhLimitCoeff α 0 * 1 * 1 * mhG α n - mhLimitCoeff α 0 =
      mhLimitCoeff α 0 * (mhG α n - 1) := by ring
  rw [e, abs_mul, abs_of_nonneg hA0, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hg hA0

lemma cast_le_four_pow (ℓ : ℕ) : (ℓ : ℝ) ≤ 4 ^ ℓ := by
  have h : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have : (ℓ : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast h.le
  refine this.trans ?_
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) ℓ

lemma cast_sq_le_four_pow (ℓ : ℕ) : (ℓ : ℝ) ^ 2 ≤ 4 ^ ℓ := by
  have h : ℓ < 2 ^ ℓ := Nat.lt_two_pow_self
  have : (ℓ : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast h.le
  calc (ℓ : ℝ) ^ 2 ≤ ((2 : ℝ) ^ ℓ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) this 2
    _ = 4 ^ ℓ := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- **Mehler–Heine with a rate.** For `α > -1`, real `β` and `R ≥ 0` there are `C` and `N` with
`‖n^{-α} P_n^{(α,β)}(cos(z/n)) - ∑_ℓ (-1)^ℓ (z/2)^{2ℓ}/(ℓ! Γ(α+ℓ+1))‖ ≤ C/n`
for all `n ≥ N` and all `‖z‖ ≤ R`.  (`C` is not explicit.) -/
theorem mehlerHeine_rate (α β : ℝ) (hα : -1 < α) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(((n : ℝ) ^ (-α) : ℝ) : ℂ) * Polynomial.aeval (Complex.cos (z / n)) (jacobi α β n) -
        mhLimit α z‖ ≤ C / n := by
  obtain ⟨cg, hcg0, Ng, hNg1, hg⟩ := mhG_bound α
  set S : ℝ := max R 1 with hS
  have hS1 : 1 ≤ S := le_max_right _ _
  have hRS : R ≤ S := le_max_left _ _
  set γ : ℝ := α + β + 1 with hγ
  set c0 : ℝ := Real.exp 1 * (2 + |γ|) with hc0
  set c : ℝ := c0 * S ^ 2 with hc
  have hc0pos : 0 ≤ c0 := by positivity
  have hcpos : 0 ≤ c := by positivity
  set K0 : ℝ := 4 * |γ| + 5 + cg + 2 * S ^ 2 with hK0
  have hK0pos : 0 ≤ K0 := by positivity
  set A0 : ℝ := mhLimitCoeff α 0 with hA0
  set M : ℕ → ℝ := fun ℓ => Real.exp α * (c ^ ℓ / (ℓ.factorial : ℝ)) with hMdef
  set D : ℕ → ℝ := fun ℓ => K0 * Real.exp α * ((4 * c) ^ ℓ / (ℓ.factorial : ℝ)) +
    (if ℓ = 0 then A0 * cg else 0) with hDdef
  have hM0 : ∀ ℓ, 0 ≤ M ℓ := fun ℓ => by simp only [hMdef]; positivity
  have hM : Summable M := (Real.summable_pow_div_factorial c).mul_left _
  have hMl : Summable fun ℓ : ℕ => (ℓ : ℝ) * M ℓ := by
    refine Summable.of_nonneg_of_le (fun ℓ => mul_nonneg (Nat.cast_nonneg _) (hM0 ℓ))
      (fun ℓ => ?_) (((Real.summable_pow_div_factorial (2 * c)).mul_left (Real.exp α)))
    simp only [hMdef]
    have h2 : (ℓ : ℝ) ≤ 2 ^ ℓ := by exact_mod_cast (Nat.lt_two_pow_self (n := ℓ)).le
    have hf : (0 : ℝ) < ℓ.factorial := by exact_mod_cast Nat.factorial_pos ℓ
    calc (ℓ : ℝ) * (Real.exp α * (c ^ ℓ / ℓ.factorial))
        ≤ 2 ^ ℓ * (Real.exp α * (c ^ ℓ / ℓ.factorial)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = Real.exp α * ((2 * c) ^ ℓ / ℓ.factorial) := by rw [mul_pow 2 c ℓ]; ring
  have hD0 : ∀ ℓ, 0 ≤ D ℓ := fun ℓ => by
    simp only [hDdef]
    have : 0 ≤ A0 * cg := mul_nonneg (mhLimitCoeff_nonneg α hα 0) hcg0
    split_ifs <;> positivity
  have hD : Summable D := by
    refine Summable.add ((Real.summable_pow_div_factorial (4 * c)).mul_left (K0 * Real.exp α)) ?_
    exact (hasSum_ite_eq 0 (A0 * cg)).summable
  -- the limit terms are dominated by `M`
  have hG : ∀ ℓ, 1 ≤ ℓ → ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(-1 : ℂ) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ)‖ ≤ M ℓ := by
    intro ℓ hℓ z hz
    have hz' : ‖z‖ ≤ R := by simpa using hz
    have hzS : ‖z / 2‖ ≤ S := by
      rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg z]
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_real,
      Real.norm_eq_abs, norm_pow, abs_of_nonneg (mhLimitCoeff_nonneg α hα ℓ)]
    calc mhLimitCoeff α ℓ * ‖z / 2‖ ^ (2 * ℓ)
        ≤ (Real.exp α * c0 ^ ℓ / (ℓ.factorial : ℝ)) * S ^ (2 * ℓ) :=
          mul_le_mul (mhLimitCoeff_le α β hα hℓ) (pow_le_pow_left₀ (norm_nonneg _) hzS _)
            (by positivity) (by positivity)
      _ = M ℓ := by
          simp only [hMdef, hc]
          rw [pow_mul, mul_pow c0]
          ring
  -- the difference of the terms
  have hdiff : ∀ n : ℕ, (R + 1 ≤ n) → ∀ ℓ : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ‖(-1 : ℂ) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) * ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ) -
        (-1 : ℂ) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ)‖ ≤
      |mhCoeff α β n ℓ - mhLimitCoeff α ℓ| * S ^ (2 * ℓ) +
        mhLimitCoeff α ℓ * ((2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n)) := by
    intro n hn ℓ z hz'
    set u : ℂ := (n : ℂ) * Complex.sin (z / (2 * n)) with hudef
    set A := mhLimitCoeff α ℓ with hA
    have hu' : ‖u‖ ≤ S := (mh_norm_u_le hn hz').trans hRS
    have hzS : ‖z / 2‖ ≤ S := by
      rw [norm_div, Complex.norm_ofNat]; linarith [norm_nonneg z]
    have key := FormalResearch.Asymptotics.norm_pow_sub_pow_le' hu' hzS hS1 (2 * ℓ)
    have e : (-1 : ℂ) ^ ℓ * (mhCoeff α β n ℓ : ℂ) * u ^ (2 * ℓ) -
        (-1 : ℂ) ^ ℓ * (A : ℂ) * (z / 2) ^ (2 * ℓ) =
        (-1 : ℂ) ^ ℓ * (((mhCoeff α β n ℓ - A : ℝ) : ℂ) * u ^ (2 * ℓ) +
          (A : ℂ) * (u ^ (2 * ℓ) - (z / 2) ^ (2 * ℓ))) := by
      push_cast; ring
    have hA0 : 0 ≤ A := mhLimitCoeff_nonneg α hα ℓ
    have hn1 : (1 : ℝ) ≤ n := by linarith
    rw [e, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu' _) (abs_nonneg _)
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
      have h3 := mh_norm_u_sub_le hn hz'
      have h4 : ((2 * ℓ : ℕ) : ℝ) * S ^ (2 * ℓ) * ‖u - z / 2‖ ≤
          (2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n) := by
        push_cast
        gcongr
      exact mul_le_mul_of_nonneg_left (key.trans h4) hA0
  -- the rate for each term
  have hF : ∀ n : ℕ, max (max Ng 1) ⌈R + 1⌉₊ ≤ n → ∀ ℓ ∈ Finset.range (n + 1),
      ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖(-1 : ℂ) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) * ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ) -
        (-1 : ℂ) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ)‖ ≤ D ℓ / n := by
    intro n hn ℓ hℓ z hz
    have hn' : R + 1 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)
    have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
    have hNg : Ng ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
    have hz' : ‖z‖ ≤ R := by simpa using hz
    have hℓn : ℓ ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hℓ)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    obtain ⟨hg1, hg2⟩ := hg n hNg
    refine (hdiff n hn' ℓ z hz').trans ?_
    rcases Nat.eq_zero_or_pos ℓ with h0 | hℓ1
    · subst h0
      have h1 := mhCoeff_zero_sub_le α β hα hn1 hg1
      have e1 : |mhCoeff α β n 0 - mhLimitCoeff α 0| * S ^ (2 * 0) +
          mhLimitCoeff α 0 * ((2 * ((0 : ℕ) : ℝ)) * S ^ (2 * 0) * (S ^ 2 / n)) =
          |mhCoeff α β n 0 - mhLimitCoeff α 0| := by simp
      rw [e1]
      refine h1.trans ?_
      have hD0e : D 0 = K0 * Real.exp α * ((4 * c) ^ 0 / ((0 : ℕ).factorial : ℝ)) + A0 * cg := by
        simp [hDdef]
      rw [hD0e]
      refine div_le_div_of_nonneg_right ?_ hnpos.le
      have : 0 ≤ K0 * Real.exp α * ((4 * c) ^ 0 / ((0 : ℕ).factorial : ℝ)) := by positivity
      linarith
    · have hm := mhCoeff_sub_le α β hα hcg0 hn1 hℓ1 hℓn hg1 hg2
      have hAB := mhLimitCoeff_le α β hα hℓ1
      have hA0' := mhLimitCoeff_nonneg α hα ℓ
      set B : ℝ := Real.exp α * c0 ^ ℓ / (ℓ.factorial : ℝ) with hB
      set κ : ℝ := 4 * ((ℓ : ℝ) * (|γ| + ℓ)) + (ℓ : ℝ) ^ 2 + cg with hκ
      have hSl : 0 ≤ S ^ (2 * ℓ) := by positivity
      have hBS : B * S ^ (2 * ℓ) = M ℓ := by
        simp only [hMdef, hB, hc]
        rw [pow_mul, mul_pow c0]
        ring
      have hκK : κ + 2 * (ℓ : ℝ) * S ^ 2 ≤ K0 * 4 ^ ℓ := by
        have h1 := cast_le_four_pow ℓ
        have h2 := cast_sq_le_four_pow ℓ
        have h3 : (1 : ℝ) ≤ 4 ^ ℓ := one_le_pow₀ (by norm_num)
        have h4 : 0 ≤ |γ| := abs_nonneg γ
        simp only [hκ, hK0]
        nlinarith [mul_le_mul_of_nonneg_left h1 h4, mul_le_mul_of_nonneg_left h1 (sq_nonneg S),
          mul_le_mul_of_nonneg_left h3 hcg0]
      have hstep : |mhCoeff α β n ℓ - mhLimitCoeff α ℓ| * S ^ (2 * ℓ) +
          mhLimitCoeff α ℓ * ((2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n)) ≤
          (B * S ^ (2 * ℓ) * (κ + 2 * (ℓ : ℝ) * S ^ 2)) / n := by
        have t1 : |mhCoeff α β n ℓ - mhLimitCoeff α ℓ| * S ^ (2 * ℓ) ≤ B * κ / n * S ^ (2 * ℓ) :=
          mul_le_mul_of_nonneg_right hm hSl
        have t2 : mhLimitCoeff α ℓ * ((2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n)) ≤
            B * ((2 * (ℓ : ℝ)) * S ^ (2 * ℓ) * (S ^ 2 / n)) :=
          mul_le_mul_of_nonneg_right hAB (by positivity)
        refine (add_le_add t1 t2).trans (le_of_eq ?_)
        field_simp
      refine hstep.trans ?_
      rw [hBS]
      refine div_le_div_of_nonneg_right ?_ hnpos.le
      have hDl : D ℓ = K0 * Real.exp α * ((4 * c) ^ ℓ / (ℓ.factorial : ℝ)) := by
        simp [hDdef, hℓ1.ne']
      rw [hDl]
      calc M ℓ * (κ + 2 * (ℓ : ℝ) * S ^ 2) ≤ M ℓ * (K0 * 4 ^ ℓ) :=
            mul_le_mul_of_nonneg_left hκK (hM0 ℓ)
        _ = K0 * Real.exp α * ((4 * c) ^ ℓ / (ℓ.factorial : ℝ)) := by
            simp only [hMdef]; rw [mul_pow 4 c ℓ]; ring
  have hmain := fun (n : ℕ) (hn1 : 1 ≤ n) (hnN : max (max Ng 1) ⌈R + 1⌉₊ ≤ n) (z : ℂ)
      (hz : z ∈ Metric.closedBall (0 : ℂ) R) => FormalResearch.Asymptotics.norm_sum_sub_tsum_le_of_rate
    (n := n) (z := z) (Fn := fun (n : ℕ) (ℓ : ℕ) (z : ℂ) => (-1 : ℂ) ^ ℓ * ((mhCoeff α β n ℓ : ℝ) : ℂ) *
        ((n : ℂ) * Complex.sin (z / (2 * n))) ^ (2 * ℓ))
    (G := fun ℓ z => (-1 : ℂ) ^ ℓ * ((mhLimitCoeff α ℓ : ℝ) : ℂ) * (z / 2) ^ (2 * ℓ))
    (K := Metric.closedBall 0 R) hM hM0 hMl hD hD0 1 (max (max Ng 1) ⌈R + 1⌉₊)
    (fun ℓ hℓ z hz => hG ℓ hℓ z hz) hF hn1 hnN (by simpa using hn1) hz
  refine ⟨(∑' ℓ, D ℓ) + ∑' ℓ : ℕ, (ℓ : ℝ) * M ℓ, max (max Ng 1) ⌈R + 1⌉₊, fun n hn z hz => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  rw [mh_aeval α β hn1 z, mhLimit]
  exact hmain n hn1 hn z (by simpa using hz)

/-- `IsBigO` form of `mehlerHeine_rate`: the remainder is `O(1/n)` uniformly on `‖z‖ ≤ R`. -/
theorem mehlerHeine_rate_isBigO (α β : ℝ) (hα : -1 < α) {R : ℝ} (hR : 0 ≤ R) :
    (fun p : ℂ × ℕ => (((p.2 : ℝ) ^ (-α) : ℝ) : ℂ) *
        Polynomial.aeval (Complex.cos (p.1 / p.2)) (jacobi α β p.2) - mhLimit α p.1) =O[
      𝓟 (Metric.closedBall (0 : ℂ) R) ×ˢ atTop] fun p => ((p.2 : ℝ))⁻¹ := by
  obtain ⟨C, N, h⟩ := mehlerHeine_rate α β hα hR
  refine Asymptotics.IsBigO.of_bound C ?_
  have hmem : Metric.closedBall (0 : ℂ) R ×ˢ Set.Ici N ∈
      𝓟 (Metric.closedBall (0 : ℂ) R) ×ˢ (atTop : Filter ℕ) :=
    prod_mem_prod (mem_principal_self _) (mem_atTop N)
  filter_upwards [hmem] with p hp
  obtain ⟨hp1, hp2⟩ := hp
  have := h p.2 hp2 p.1 (by simpa using hp1)
  rw [Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  rw [div_eq_mul_inv C (p.2 : ℝ)] at this
  exact this

/-! ### Axiom check -/

/-- info: 'FormalResearch.Special.mehlerHeine_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_rate

/-- info: 'FormalResearch.Special.mehlerHeine_rate_isBigO' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.mehlerHeine_rate_isBigO

end FormalResearch.Special

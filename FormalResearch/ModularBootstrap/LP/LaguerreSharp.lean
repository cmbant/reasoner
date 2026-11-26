module

public import FormalResearch.ModularBootstrap.LP.Moments

/-!
# Sharp Laguerre constant `(2 + w)/(2π)` for `ds:mom`

Improves `lagP_oddFam` in `LP/Moments.lean` from `C = (1 + w)/π` to the paper's sharp constant
`C_w = (2 + w)/(2π)` (`dual_spectrum_limit.tex`, Lemma LP-M).

* `abs_lagP_le` in `LP/Laguerre.lean` already gives `|P_k(t)| ≤ (t + (3+w)k/(4π))^k`, and
  `(3+w)/(4π) ≤ (2+w)/(2π)` for `w > 0`.
* `lagP_lower_sharp` sharpens `lagP_lower` from `t ≥ 2(n+w)/π` to `t ≥ (2+w)n/π` by the same
  three-term-recurrence ratio induction (`seq_ratio_sharp`).
* `lagP_oddFam_sharp` combines both into `OddFam ((2 + w) / (2 * π)) (lagPC w)`.
* With it, `ds_mom (lagP_oddFam_sharp hw)` is `ds:mom` for Laguerre in the paper's constant; its
  conclusion is the statement of `ds_mom_laguerre` (the constant does not appear there), so no second
  copy is stated. The paper's clause itself is `DsMomLaguerreConst` in `LP/Statements`.
-/

@[expose] public section

open MeasureTheory Set Real

namespace FormalResearch.ModularBootstrap.LP

section SharpBounds

variable {w x : ℝ} {s : ℕ → ℝ}

/-- Sharper ratio lower bound: for `n ≥ 1` and `x ≥ 4(2+w)n`, `s_j ≥ 0` and `x/2 * s_j ≤ s_{j+1}`
for all `j + 1 ≤ n`. -/
private lemma seq_ratio_sharp (hw : 0 < w) (h0 : s 0 = 1) (h1 : s 1 = x - w)
    (hrec : ∀ k : ℕ, s (k + 2) =
      (x - (2 * ((k : ℝ) + 1) + w)) * s (k + 1) - ((k : ℝ) + 1) * ((k : ℝ) + w) * s k)
    {n : ℕ} (hn : 1 ≤ n) (hx : 4 * (2 + w) * n ≤ x) :
    ∀ j : ℕ, j + 1 ≤ n → 0 ≤ s j ∧ x / 2 * s j ≤ s (j + 1) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hxpos : 0 < x := by nlinarith
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨by rw [h0]; exact zero_le_one, ?_⟩
    rw [h0, h1]
    nlinarith
  | succ j ih =>
    intro hj
    obtain ⟨hs0, hs1⟩ := ih (by omega)
    have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast (by omega : j + 1 ≤ n)
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hsj1 : 0 ≤ s (j + 1) := by nlinarith
    refine ⟨hsj1, ?_⟩
    rw [hrec j]
    have h2 : x * s j ≤ 2 * s (j + 1) := by nlinarith
    have hA : 2 * (n : ℝ) + w ≤ x / 2 - (2 * ((j : ℝ) + 1) + w) := by nlinarith
    have hx8 : 8 * (n : ℝ) ≤ x := by nlinarith
    have hB : ((j : ℝ) + 1) * ((j : ℝ) + w) ≤ n * (n + w) := by nlinarith
    have hC : 0 ≤ x ^ 2 / 2 - (2 * ((j : ℝ) + 1) + w) * x - 2 * (((j : ℝ) + 1) * ((j : ℝ) + w)) := by
      have hmul : 8 * (n : ℝ) * (2 * (n : ℝ) + w) ≤ x * (x / 2 - (2 * ((j : ℝ) + 1) + w)) :=
        mul_le_mul hx8 hA (by positivity) (by positivity)
      nlinarith
    have hcoef : 0 ≤ ((j : ℝ) + 1) * ((j : ℝ) + w) := by positivity
    have key : 0 ≤ x * ((x - (2 * ((j : ℝ) + 1) + w)) * s (j + 1)
        - ((j : ℝ) + 1) * ((j : ℝ) + w) * s j - x / 2 * s (j + 1)) := by
      have e : x * ((x - (2 * ((j : ℝ) + 1) + w)) * s (j + 1)
        - ((j : ℝ) + 1) * ((j : ℝ) + w) * s j - x / 2 * s (j + 1))
          = (x ^ 2 / 2 - (2 * ((j : ℝ) + 1) + w) * x) * s (j + 1)
            - ((j : ℝ) + 1) * ((j : ℝ) + w) * (x * s j) := by ring
      rw [e]
      nlinarith [mul_nonneg hC hsj1, mul_le_mul_of_nonneg_left h2 hcoef]
    have := nonneg_of_mul_nonneg_right key hxpos
    linarith

private lemma seq_lower_sharp (hw : 0 < w) (h0 : s 0 = 1) (h1 : s 1 = x - w)
    (hrec : ∀ k : ℕ, s (k + 2) =
      (x - (2 * ((k : ℝ) + 1) + w)) * s (k + 1) - ((k : ℝ) + 1) * ((k : ℝ) + w) * s k)
    (n : ℕ) (hx : 4 * (2 + w) * n ≤ x) : (x / 2) ^ n ≤ s n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [h0]
  · have hxpos : 0 < x := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have key : ∀ j : ℕ, j ≤ n → (x / 2) ^ j ≤ s j := by
      intro j
      induction j with
      | zero => intro _; simp [h0]
      | succ j ih =>
        intro hj
        have ih' := ih (by omega)
        obtain ⟨_, hr⟩ := seq_ratio_sharp hw h0 h1 hrec hn hx j hj
        rw [pow_succ, mul_comm]
        calc x / 2 * (x / 2) ^ j ≤ x / 2 * s j := by gcongr
          _ ≤ s (j + 1) := hr
    exact key n le_rfl

end SharpBounds

/-- **Sharp lower bound for large `t`**: for `w > 0` and `t ≥ (2 + w) n / π`,
`(t / 2)^n ≤ P_n(t)`. -/
theorem lagP_lower_sharp {w : ℝ} (hw : 0 < w) (n : ℕ) {t : ℝ} (ht : (2 + w) * n / π ≤ t) :
    (t / 2) ^ n ≤ lagP w n t := by
  have hπ : 0 < π := Real.pi_pos
  have hx : 4 * (2 + w) * n ≤ 4 * π * t := by
    rw [div_le_iff₀ hπ] at ht
    nlinarith
  have := seq_lower_sharp hw (s := fun k => lagM w k (4 * π * t)) (x := 4 * π * t)
    (by simp) (by simp [lagM_one]) (fun k => lagM_rec w _ k) n hx
  unfold lagP
  rw [le_div_iff₀ (by positivity)]
  calc (t / 2) ^ n * (4 * π) ^ n = (4 * π * t / 2) ^ n := by
        rw [← mul_pow]; congr 1; ring
    _ ≤ _ := this

/-- The monic Laguerre polynomials at weight `w > 0` satisfy `OddFam` with the paper's sharp
constant `C_w = (2 + w) / (2π)`. -/
theorem lagP_oddFam_sharp {w : ℝ} (hw : 0 < w) : OddFam ((2 + w) / (2 * π)) (lagPC w) where
  C_pos := by positivity
  upper k _ t ht := by
    have h := abs_lagP_le hw k ht
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e : (3 + w) * (k : ℝ) / (4 * π) ≤ (2 + w) / (2 * π) * k := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_pos, mul_nonneg hk0 hw.le]
    simp only [lagPC_apply]
    exact h.trans (pow_le_pow_left₀ (by positivity) (by linarith) k)
  lower k _ t ht := by
    simp only [lagPC_apply]
    refine lagP_lower_sharp hw k (le_trans ?_ ht)
    rw [mul_assoc, show 2 * ((2 + w) / (2 * π) * (k : ℝ)) = (2 + w) * k / π by field_simp]

/-- info: 'FormalResearch.ModularBootstrap.LP.lagP_lower_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.lagP_lower_sharp

/-- info: 'FormalResearch.ModularBootstrap.LP.lagP_oddFam_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.LP.lagP_oddFam_sharp

end FormalResearch.ModularBootstrap.LP

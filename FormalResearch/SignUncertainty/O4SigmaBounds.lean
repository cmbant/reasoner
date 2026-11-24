module

public import FormalResearch.CohnElkies.CubicNormalFormBridge

/-!
# Sharp two-sided bounds for `o4Sigma0` (`u1co:O4`, paper (ii))

For `L ∈ (0, 0.002]` let `σ₀(L) = o4Sigma0 L = τ₀(L) / θ₀(L)`, where `τ₀(L) = tau0 L` is the positive saddle
of `ceEll (π τ / 2) = L` and `θ₀² = 12 α̃ / π²` with `α̃ = edgeAlphaTilde L`.  The main result is

`1 - L / 8 ≤ σ₀(L) ≤ 1 + 0.606 L`,

which is the sharp form of paper bound (ii) of `u1c_estimate_proofs.tex` (around line 308).  The earlier
bounds `o4Sigma0_ge`, `o4Sigma0_le` only give `[0.9997, 1.003]`.

Proof outline (`x := π τ₀ / 2`, so `ceEll x = L`):

* Lower bound: `(2√3/π)√L < τ₀` (`tau0_gt_sqrt`) and `α̃ ≤ L (1 + L / 4)` (`edgeKappa0_bounds`) give
  `σ₀² (1 + L / 4) > 1`, hence `(1 - L/8)² (1 + L/4) ≤ 1` yields `1 - L/8 ≤ σ₀`.
* Upper bound: the Taylor remainder `ceHth x ≤ (2/15) x⁴` for `0 < x ≤ 1` (`ceHth_le_of_le_one`) gives
  `x²/3 - (2/15) x⁴ ≤ L`; with `τ₀ ≤ 1.105 √L` (`tau0_bounds`) and `α̃ ≥ L` (`edgeKappa0_bounds`) this
  gives `σ₀² ≤ 1 + 1.212 L`, hence `σ₀ ≤ 1 + 0.606 L`.

**Formalised (proved, unconditional):** `o4Sigma0_sharp`, both inequalities for every `L ∈ (0, 0.002]`.
The inputs are the already formalised `tau0_bounds`, `tau0_gt_sqrt`, `edgeKappa0_bounds`, `ceHth_le_of_le_one`,
`ceEll_tau0` and the algebraic parameter lemmas of `CubicNormalFormBridge`.

**Not formalised here:** the paper's remarks about the sharpness of the constants (`1/8` and `0.606` are
not claimed optimal), and any statement beyond the interval `(0, 0.002]`.
-/

@[expose] public section

open Metric Set Filter Topology
open scoped Real

namespace FormalResearch.CohnElkies

/-- `ceEll x = x²/3 - h_th(x)` (the definition of `ceHth`, with `log(x / tanh x) = -log(tanh x / x)`). -/
lemma o4_ceEll_eq_sub_ceHth (x : ℝ) : ceEll x = x ^ 2 / 3 - ceHth x := by
  unfold ceEll ceHth
  rw [show Real.tanh x / x = (x / Real.tanh x)⁻¹ by rw [inv_div], Real.log_inv]
  ring

/-- info: 'FormalResearch.CohnElkies.o4_ceEll_eq_sub_ceHth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o4_ceEll_eq_sub_ceHth

/-- Upper bound `ℓ(x) ≥ x²/3 - (2/15) x⁴` on `0 < x ≤ 1`. -/
lemma o4_ceEll_upper {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    x ^ 2 / 3 - 2 / 15 * x ^ 4 ≤ ceEll x := by
  rw [o4_ceEll_eq_sub_ceHth]
  linarith [ceHth_le_of_le_one hx0 hx1]

/-- info: 'FormalResearch.CohnElkies.o4_ceEll_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o4_ceEll_upper

/-- `σ₀² θ₀² = τ₀²` and `θ₀² ≥ (12/π²) L`, so `σ₀²(12/π²)L ≤ τ₀²`. -/
lemma o4_sigma0_sq_mul_theta {L : ℝ} (hL0 : 0 < L) :
    o4Sigma0 L ^ 2 * o4Theta0Sq L = tau0 L ^ 2 := by
  rw [← o4Theta0_sq hL0, ← o4Sigma0_mul hL0]
  ring

/-- info: 'FormalResearch.CohnElkies.o4_sigma0_sq_mul_theta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o4_sigma0_sq_mul_theta

/-- **Lower bound:** `1 - L/8 ≤ o4Sigma0 L` for `0 < L ≤ 0.002`. -/
lemma o4Sigma0_sharp_lower {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    1 - L / 8 ≤ o4Sigma0 L := by
  have hτ := tau0_pos hL0
  have hκ := edgeKappa0_bounds hL0 hL2
  have hα : edgeAlphaTilde L ≤ L * (1 + L / 4) := by
    have := hκ.2; unfold edgeKappa0 at this
    rw [div_le_iff₀ hL0] at this; linarith
  have hg := tau0_gt_sqrt hL0 hτ (ceEll_tau0 hL0)
  have hpi := Real.pi_pos
  have hk : 0 < 12 / π ^ 2 * L := by positivity
  have hτ2 : 12 / π ^ 2 * L < tau0 L ^ 2 := by
    have h0 : 0 ≤ (2 * Real.sqrt 3 / π) * Real.sqrt L := by positivity
    have := pow_lt_pow_left₀ hg h0 (by norm_num : (2 : ℕ) ≠ 0)
    calc (12 / π ^ 2) * L = ((2 * Real.sqrt 3 / π) * Real.sqrt L) ^ 2 := by
          rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sq_sqrt hL0.le]; ring
      _ < _ := this
  have hθ : o4Theta0Sq L ≤ 12 / π ^ 2 * (L * (1 + L / 4)) := by
    unfold o4Theta0Sq; exact mul_le_mul_of_nonneg_left hα (by positivity)
  have hs2 : 0 ≤ o4Sigma0 L ^ 2 := sq_nonneg _
  have h1 : 12 / π ^ 2 * L < o4Sigma0 L ^ 2 * (12 / π ^ 2 * (L * (1 + L / 4))) := by
    calc 12 / π ^ 2 * L < tau0 L ^ 2 := hτ2
      _ = o4Sigma0 L ^ 2 * o4Theta0Sq L := (o4_sigma0_sq_mul_theta hL0).symm
      _ ≤ o4Sigma0 L ^ 2 * (12 / π ^ 2 * (L * (1 + L / 4))) := mul_le_mul_of_nonneg_left hθ hs2
  have h1' : 12 / π ^ 2 * L * 1 < 12 / π ^ 2 * L * (o4Sigma0 L ^ 2 * (1 + L / 4)) := by
    linarith [h1, show 12 / π ^ 2 * L * (o4Sigma0 L ^ 2 * (1 + L / 4)) =
      o4Sigma0 L ^ 2 * (12 / π ^ 2 * (L * (1 + L / 4))) by ring]
  have h2 : 1 < o4Sigma0 L ^ 2 * (1 + L / 4) := lt_of_mul_lt_mul_left h1' hk.le
  have h3 : (1 - L / 8) ^ 2 * (1 + L / 4) ≤ 1 := by
    nlinarith [mul_nonneg (sq_nonneg L) (show (0 : ℝ) ≤ 1 - L by linarith)]
  have h4 : (1 - L / 8) ^ 2 ≤ o4Sigma0 L ^ 2 :=
    le_of_mul_le_mul_right (h3.trans h2.le) (by positivity)
  exact le_of_pow_le_pow_left₀ two_ne_zero (o4Sigma0_pos hL0).le h4

/-- info: 'FormalResearch.CohnElkies.o4Sigma0_sharp_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o4Sigma0_sharp_lower

/-- **Upper bound:** `o4Sigma0 L ≤ 1 + 0.606 L` for `0 < L ≤ 0.002`. -/
lemma o4Sigma0_sharp_upper {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    o4Sigma0 L ≤ 1 + 0.606 * L := by
  obtain ⟨hτ05, hτsq, -⟩ := tau0_bounds hL0 hL2
  have hτ := tau0_pos hL0
  have hκ := edgeKappa0_bounds hL0 hL2
  have hα : L ≤ edgeAlphaTilde L := by
    have := hκ.1; unfold edgeKappa0 at this
    rw [lt_div_iff₀ hL0] at this; linarith
  have hpi_lo : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hpi_hi : π < 3.1416 := Real.pi_lt_d4
  have hpi := Real.pi_pos
  -- the saddle point `x = π τ₀ / 2` lies in `(0, 1]`
  have hx0 : 0 < π * tau0 L / 2 := div_pos (mul_pos hpi hτ) two_pos
  have hx1 : π * tau0 L / 2 ≤ 1 := by
    have := mul_le_mul hpi_hi.le hτ05.le hτ.le (by norm_num)
    linarith
  have h1 := o4_ceEll_upper hx0 hx1
  rw [ceEll_tau0 hL0] at h1
  -- `12 L + (8/5) x⁴ ≥ π² τ₀²`
  have hB : π ^ 2 * tau0 L ^ 2 ≤ 12 * L + 8 / 5 * (π * tau0 L / 2) ^ 4 := by
    nlinarith [h1]
  -- `τ₀² ≤ 1.105² L`
  have hτ2le : tau0 L ^ 2 ≤ 1.105 ^ 2 * L := by
    have h := pow_le_pow_left₀ hτ.le hτsq 2
    rw [mul_pow, Real.sq_sqrt hL0.le] at h
    exact h
  -- `x⁴ ≤ 9.09 L²`
  have hC : (π * tau0 L / 2) ^ 4 ≤ 9.09 * L ^ 2 := by
    have hx4 : (π * tau0 L / 2) ^ 4 = π ^ 4 * (tau0 L ^ 2) ^ 2 / 16 := by ring
    have hπ4 : π ^ 4 ≤ 97.5 := by
      have := pow_le_pow_left₀ hpi.le hpi_hi.le 4
      norm_num at this ⊢; linarith
    have hτ4 : (tau0 L ^ 2) ^ 2 ≤ (1.105 ^ 2 * L) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hτ2le 2
    have hprod : π ^ 4 * (tau0 L ^ 2) ^ 2 ≤ 97.5 * (1.105 ^ 2 * L) ^ 2 :=
      mul_le_mul hπ4 hτ4 (by positivity) (by norm_num)
    rw [hx4]
    norm_num at hprod ⊢
    nlinarith [hprod]
  -- `σ₀² · 12 L ≤ π² τ₀²` (from `θ₀² ≥ (12/π²) L`)
  have hθlow : 12 / π ^ 2 * L ≤ o4Theta0Sq L := by
    unfold o4Theta0Sq; exact mul_le_mul_of_nonneg_left hα (by positivity)
  have hA : o4Sigma0 L ^ 2 * (12 / π ^ 2 * L) ≤ tau0 L ^ 2 := by
    rw [← o4_sigma0_sq_mul_theta hL0]
    exact mul_le_mul_of_nonneg_left hθlow (sq_nonneg _)
  have hA' : o4Sigma0 L ^ 2 * (12 * L) ≤ π ^ 2 * tau0 L ^ 2 := by
    have e : π ^ 2 * (o4Sigma0 L ^ 2 * (12 / π ^ 2 * L)) = o4Sigma0 L ^ 2 * (12 * L) := by
      field_simp
    calc o4Sigma0 L ^ 2 * (12 * L) = π ^ 2 * (o4Sigma0 L ^ 2 * (12 / π ^ 2 * L)) := e.symm
      _ ≤ π ^ 2 * tau0 L ^ 2 := mul_le_mul_of_nonneg_left hA (by positivity)
  have hs : o4Sigma0 L ^ 2 ≤ 1 + 1.212 * L := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.mpr hc) (show (0 : ℝ) < 12 * L by positivity)]
  have hfin : o4Sigma0 L ^ 2 ≤ (1 + 0.606 * L) ^ 2 := by
    nlinarith [sq_nonneg L]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hfin

/-- info: 'FormalResearch.CohnElkies.o4Sigma0_sharp_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o4Sigma0_sharp_upper

/-- **Sharp two-sided bounds for `o4Sigma0`** (paper bound (ii) of `u1c_estimate_proofs.tex`):
for `0 < L ≤ 0.002`, `1 - L / 8 ≤ σ₀(L) ≤ 1 + 0.606 L`. -/
theorem o4Sigma0_sharp {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) :
    1 - L / 8 ≤ o4Sigma0 L ∧ o4Sigma0 L ≤ 1 + 0.606 * L :=
  ⟨o4Sigma0_sharp_lower hL0 hL2, o4Sigma0_sharp_upper hL0 hL2⟩

/-- info: 'FormalResearch.CohnElkies.o4Sigma0_sharp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.o4Sigma0_sharp

end FormalResearch.CohnElkies

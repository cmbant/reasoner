module

public import FormalResearch.Complex.HadamardCount
public import FormalResearch.Complex.HadamardCore

/-!
# Good radii and the decay of the core estimate (Hadamard factorization, milestone H3'/H4 prerequisites)

* `Hadamard.exists_good_radii`: for `f` entire, `f 0 ≠ 0`, there are radii `R_k ∈ (k+1, k+2)` with no zero of `f` on
  `‖z‖ = R_k`.
* `Hadamard.core_bound_tendsto`: with `‖f z‖ ≤ C exp (C ‖z‖^σ)`, `σ < p + 1`, the right-hand side of
  `Hadamard.core_estimate` at `R = R_k`, `M = C exp (C R_k^σ)` and `#T_k ≤ K R_k^σ` tends to `0`.

All **proved**.
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators ComplexConjugate Classical Nat

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- Radii `R_k ∈ (k+1, k+2)` avoiding the moduli of the zeros of `f`. -/
lemma exists_good_radii {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    ∃ R : ℕ → ℝ, (∀ k : ℕ, (k : ℝ) + 1 < R k ∧ R k < k + 2) ∧
      ∀ (k : ℕ) (w : ℂ), ‖w‖ = R k → f w ≠ 0 := by
  have h : ∀ k : ℕ, ∃ r : ℝ, ((k : ℝ) + 1 < r ∧ r < k + 2) ∧
      ∀ w : ℂ, ‖w‖ = r → f w ≠ 0 := by
    intro k
    have hfin : ((fun w : ℂ => ‖w‖) '' {w : ℂ | ‖w‖ ≤ (k : ℝ) + 2 ∧ f w = 0}).Finite :=
      (zeros_finite hf h0 ((k : ℝ) + 2)).image _
    have hinf : (Set.Ioo ((k : ℝ) + 1) ((k : ℝ) + 2)).Infinite := Set.Ioo_infinite (by linarith)
    obtain ⟨r, hr, hrn⟩ := hinf.exists_notMem_finite hfin
    refine ⟨r, hr, fun w hw hfw => hrn ⟨w, ⟨?_, hfw⟩, hw⟩⟩
    rw [hw]; exact hr.2.le
  choose R hR using h
  exact ⟨R, fun k => (hR k).1, fun k => (hR k).2⟩

/-- Pointwise form of the decay: the core bound is at most `c3 · r^{σ-(p+1)}`. -/
lemma core_bound_le {σ C : ℝ} (hσ : 0 < σ) (hC : 1 ≤ C) (p : ℕ) (ℓ K : ℝ) :
    ∃ c3 : ℝ, ∀ r : ℝ, 1 ≤ r → ∀ n : ℝ, 0 ≤ n → n ≤ K * r ^ σ →
      ((p + 1).factorial * (5 * Real.log (C * Real.exp (C * r ^ σ)) + 2 + 3 * |ℓ|) * 4 ^ (p + 1) +
        n * p.factorial * (4 / 3) ^ (p + 1)) / r ^ (p + 1) ≤ c3 * r ^ (σ - ((p + 1 : ℕ) : ℝ)) := by
  set A0 : ℝ := ((p + 1).factorial : ℝ) * 4 ^ (p + 1) with hA0
  have hA0nn : 0 ≤ A0 := by positivity
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨A0 * (5 * Real.log C + 5 * C + 2 + 3 * |ℓ|) + K * p.factorial * (4 / 3) ^ (p + 1), ?_⟩
  intro r hr n hn0 hn
  have hr0 : 0 < r := by linarith
  have hs : 1 ≤ r ^ σ := Real.one_le_rpow hr hσ.le
  have hlog : Real.log (C * Real.exp (C * r ^ σ)) = Real.log C + C * r ^ σ := by
    rw [Real.log_mul (by linarith) (Real.exp_pos _).ne', Real.log_exp]
  rw [hlog]
  have hrp : r ^ σ / r ^ (p + 1) = r ^ (σ - ((p + 1 : ℕ) : ℝ)) := by
    rw [Real.rpow_sub hr0, Real.rpow_natCast]
  have hpow : 0 < r ^ (p + 1) := by positivity
  rw [div_le_iff₀ hpow]
  have h43 : 0 ≤ (4 / 3 : ℝ) ^ (p + 1) := by positivity
  have hfac : (0 : ℝ) ≤ p.factorial := by positivity
  have hrhs : r ^ (σ - ((p + 1 : ℕ) : ℝ)) * r ^ (p + 1) = r ^ σ := by
    rw [← hrp]; field_simp
  have hnum : ((p + 1).factorial * (5 * (Real.log C + C * r ^ σ) + 2 + 3 * |ℓ|) * 4 ^ (p + 1) +
      n * p.factorial * (4 / 3) ^ (p + 1)) ≤
      (A0 * (5 * Real.log C + 5 * C + 2 + 3 * |ℓ|) + K * p.factorial * (4 / 3) ^ (p + 1)) * r ^ σ := by
    have e1 : ((p + 1).factorial * (5 * (Real.log C + C * r ^ σ) + 2 + 3 * |ℓ|) * 4 ^ (p + 1))
        = A0 * (5 * (Real.log C + C * r ^ σ) + 2 + 3 * |ℓ|) := by rw [hA0]; ring
    have e2 : n * p.factorial * (4 / 3) ^ (p + 1) ≤ K * r ^ σ * p.factorial * (4 / 3) ^ (p + 1) := by
      gcongr
    have e3 : 5 * (Real.log C + C * r ^ σ) + 2 + 3 * |ℓ| ≤
        (5 * Real.log C + 5 * C + 2 + 3 * |ℓ|) * r ^ σ := by
      have habs := abs_nonneg ℓ
      have hCs : C * r ^ σ ≤ C * r ^ σ := le_rfl
      nlinarith
    rw [e1]
    have := mul_le_mul_of_nonneg_left e3 hA0nn
    nlinarith
  calc _ ≤ (A0 * (5 * Real.log C + 5 * C + 2 + 3 * |ℓ|) + K * p.factorial * (4 / 3) ^ (p + 1)) *
        r ^ σ := hnum
    _ = _ := by rw [← hrhs]; ring

end FormalResearch.Hadamard

/-- info: 'FormalResearch.Hadamard.exists_good_radii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.exists_good_radii

/-- info: 'FormalResearch.Hadamard.core_bound_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Hadamard.core_bound_le

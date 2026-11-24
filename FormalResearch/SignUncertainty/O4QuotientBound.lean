module

public import FormalResearch.SignUncertainty.O4QuotientAssembly
public import FormalResearch.SignUncertainty.O4RhoSeries

/-!
# `O4QuotientBound L` for `0 < L ≤ 0.002` (`u1co:O4`, `[O4C (B)]`)

Combines the Taylor series of `Φ_L` with the `2/n` coefficient bound (`edgePhiC_trunc_tail`), the Horner form `ρ₁₃` of the box
certificate (`rho13_eq`, whose coefficients are the exact rationals `o4Coef_eq_rat_n`), and the kernel-checked box certificate
(`o4QuotientBound_of_trunc`).

**Formalised (proved, unconditional):** `o4QuotientBound : 0 < L → L ≤ 0.002 → O4QuotientBound L`.  The inputs are the Taylor
series (`edgePhiC_series`), the sharp bounds on `σ₀` (`o4Sigma0_sharp`) and `α̃` (`edgeKappa0_bounds`), the exact
reduction to the quarter arc (`o4QuotientBound_of_quarter`) and the 12,800 interval boxes of `O4CertRun01 … O4CertRun10`.

Status: proved.
-/

@[expose] public section

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies Complex
open FormalResearch.SignUncertainty.O4Cert

theorem rho13_eq (τ : ℂ) :
    rho13 τ = ∑ n ∈ Finset.Icc 2 13, ((-1 : ℂ) ^ n * ((o4Coef n * Real.pi ^ (2 * n) : ℝ) : ℂ)) * τ ^ (2 * n + 1) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show Finset.Icc 2 13 = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} by decide]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  rw [o4Coef_eq_rat_2, o4Coef_eq_rat_3, o4Coef_eq_rat_4, o4Coef_eq_rat_5, o4Coef_eq_rat_6, o4Coef_eq_rat_7,
    o4Coef_eq_rat_8, o4Coef_eq_rat_9, o4Coef_eq_rat_10, o4Coef_eq_rat_11, o4Coef_eq_rat_12, o4Coef_eq_rat_13]
  unfold rho13 csReal csData
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  push_cast
  field_simp
  ring

theorem trunc_error_le (L : ℝ) {τ : ℂ} (hτ : ‖τ‖ ≤ (1 + 0.606 * 0.002) / 4) :
    ‖edgePhiC L τ - ((L : ℂ) * τ - (Real.pi : ℂ) ^ 2 / 36 * τ ^ 3 + rho13 τ)‖ ≤ (tailR : ℝ) / SC := by
  have h := edgePhiC_trunc_tail L hτ (by norm_num)
  have e : edgePhiC L τ - ((L : ℂ) * τ - (Real.pi : ℂ) ^ 2 / 36 * τ ^ 3 + rho13 τ) =
      edgePhiC L τ - ((L : ℂ) * τ - (Real.pi : ℂ) ^ 2 * τ ^ 3 / 36 +
        ∑ n ∈ Finset.Icc 2 13, ((-1 : ℂ) ^ n * ((o4Coef n * Real.pi ^ (2 * n) : ℝ) : ℂ)) * τ ^ (2 * n + 1)) := by
    rw [rho13_eq]; ring
  rw [e]
  refine h.trans ?_
  norm_num [tailR, SC]

/-- **`[O4C (B)]`**: `‖𝓕‖ ≤ 0.13` on `D(0, 0.25)` away from the removable singularities, for every `L ∈ (0, 0.002]`. -/
theorem o4QuotientBound {L : ℝ} (hL0 : 0 < L) (hL2 : L ≤ 0.002) : O4QuotientBound L :=
  o4QuotientBound_of_trunc hL0 hL2 fun _ hτ => trunc_error_le L hτ

/-- info: 'FormalResearch.SignUncertainty.o4QuotientBound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms o4QuotientBound

end FormalResearch.SignUncertainty

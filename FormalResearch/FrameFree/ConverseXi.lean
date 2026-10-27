import FormalResearch.FrameFree.ConverseM4
import FormalResearch.FrameFree.XiInvUnconditional

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The converse `ξ̄_inv ≤ -log N` from an achiral projected branch, and `M₄^{⊗(m+1)}` unconditionally

* `xiBarLE_of_achiral` : an achiral projected branch of weight `N` (`Converse.AchiralBranch ψ N`) gives
  `XiBarLE ψ (-log N)` (proved; the input is `pe_ge_of_achiral : P_e(k) ≥ N^k/4`, a Schur-Weyl projector argument).
* `blocks_hasXiInv` : `ξ_inv(M₄^{⊗(m+1)}) = (m+1) log 2`, unconditional (for `M₄` itself see
  `AchiralCritical.m4_hasXiInv_log_two`).
* `m4_xi_inv''`, `blocks_xi_inv''` : the same exponents together with the `C_K` values and gaps; only the `C_K`
  part uses `h49 : FKΘ M4v ≤ 4/9`.
-/

namespace FormalResearch.FrameFree.XiInv

open Filter Topology
open FormalResearch.FrameFree.NQubit FormalResearch.FrameFree.Helstrom
open FormalResearch.FrameFree FormalResearch.FrameFree.Converse

theorem xiBarLE_of_achiral {n : ℕ} {ψ : Ψ n} {N : ℝ} (h : AchiralBranch ψ N) : XiBarLE ψ (-Real.log N) := by
  intro ε hε
  have hN : 0 < N := h.1
  filter_upwards [eventually_ge_atTop (⌈Real.log 4 / ε⌉₊ + 1)] with k hk
  have hk0 : (0 : ℝ) < k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    linarith
  have hP := pe_ge_of_achiral h k
  have hpos : 0 < N ^ k / 4 := by positivity
  have hlog : Real.log (N ^ k / 4) ≤ Real.log (Pe k ψ) := Real.log_le_log hpos hP
  rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hlog
  have h4 : Real.log 4 ≤ ε * k := by
    have h1 : Real.log 4 / ε ≤ k := by
      have := Nat.le_ceil (Real.log 4 / ε)
      have h2 : ((⌈Real.log 4 / ε⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
      push_cast at h2
      linarith
    rwa [div_le_iff₀ hε, mul_comm] at h1
  have : -(1 / (k : ℝ)) * Real.log (Pe k ψ) ≤ -(1 / (k : ℝ)) * (k * Real.log N - Real.log 4) :=
    mul_le_mul_of_nonpos_left hlog (by have : 0 < 1 / (k : ℝ) := by positivity
                                       linarith)
  refine this.trans ?_
  have : -(1 / (k : ℝ)) * (k * Real.log N - Real.log 4) = -Real.log N + Real.log 4 / k := by
    field_simp
    ring
  rw [this]
  have : Real.log 4 / k ≤ ε := by rw [div_le_iff₀ hk0]; linarith
  linarith

/-- **`thm:m4exponent`**, converse discharged: `ξ_inv(M₄) = log 2` and, given `F_K(M₄) ≤ 4/9`, the `C_K`
value and gap. -/
theorem m4_xi_inv'' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) :
    HasXiInv Ceilings.M4v (Real.log 2) ∧ CK Ceilings.M4v = Real.log (9 / 4) ∧
      Real.log 2 < CK Ceilings.M4v ∧ CK Ceilings.M4v - Real.log 2 = Real.log (9 / 8) ∧
      0.1452 < 1 - Real.log 2 / CK Ceilings.M4v ∧ 1 - Real.log 2 / CK Ceilings.M4v < 0.1453 := by
  refine m4_xi_inv' h49 ?_
  have := xiBarLE_of_achiral achiralBranch_M4v
  rwa [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub, neg_neg] at this

/-- **`ξ_inv(M₄^{⊗(m+1)}) = (m+1) log 2`**, unconditional: the support rate gives `≥` (`F_C = 2^{-(m+1)}`), the
achiral branch of weight `2^{-(m+1)}` gives `≤`. -/
theorem blocks_hasXiInv (m : ℕ) : HasXiInv (Ceilings.M4pow m) ((m + 1) * Real.log 2) := by
  have hF := M4Support.FCΘ_M4pow_eq_half_pow m
  have e : -Real.log ((1 / 2 : ℝ) ^ (m + 1)) = (m + 1) * Real.log 2 := by
    rw [Real.log_pow, one_div, Real.log_inv]; push_cast; ring
  refine hasXiInv_of_xiBarLE (Ceilings.nsq_M4pow m) (by rw [hF]; positivity) (by rw [hF, e]) ?_
  have := xiBarLE_of_achiral (achiralBranch_M4pow m)
  rwa [e] at this

/-- **`cor:calgeom-spin1extensive` (a)**, converse discharged: `ξ_inv(M₄^{⊗(m+1)}) = (m+1) log 2`
(`blocks_hasXiInv`) and, given `F_K(M₄) ≤ 4/9`, the gap `C_K - ξ_inv = (m+1) log (9/8)`. -/
theorem blocks_xi_inv'' (h49 : FKΘ Ceilings.M4v ≤ 4 / 9) (m : ℕ) :
    HasXiInv (Ceilings.M4pow m) ((m + 1) * Real.log 2) ∧
      CK (Ceilings.M4pow m) - (m + 1) * Real.log 2 = (m + 1) * Real.log (9 / 8) := by
  refine blocks_xi_inv' h49 m ?_
  have := xiBarLE_of_achiral (achiralBranch_M4pow m)
  have e : -Real.log ((1 / 2 : ℝ) ^ (m + 1)) = (m + 1) * Real.log 2 := by
    rw [Real.log_pow, one_div, Real.log_inv]; push_cast; ring
  rwa [e] at this

end FormalResearch.FrameFree.XiInv

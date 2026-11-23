module

public import FormalResearch.ModularBootstrap.WeightAxioms.BesselGeneral

/-!
# The Bessel function `J_p` for natural `p`: power-series form, bound and derivative

Source: `CFT/modular_bootstrap/paper/upper_transfer.tex`, section `fw:s1` ("Differentiation of the
Bessel kernel"); plan item A3, order `p`.

For natural `p`, `J_p(x) = (x/2)^p S_p(-x²/4)` with `S_p = besselSC p` the regularised Bessel series
(`besselJ_nat_eq`, from the definition `Complex.besselJ`), and `J_p(x) = i^p I_p(-i x)`
(`besselJ_eq_I_besselIC`).  Consequently:

* `norm_besselJ_nat_le_one`: `|J_p(x)| ≤ 1` for real `x`, from Bessel's integral for `I_p`;
* `hasDerivAt_besselSC`: `S_p' = S_{p+1}`;
* `besselJ_kernel_eq`: `(s/t)^{p/2} J_p(4π√(s t)) = (2π s)^p S_p(-4π² s t)` for `s ≥ 0`, `t > 0`, which is
  entire in `t`;
* `hasDerivAt_besselKernel`: `∂_t [(2π s)^p S_p(-4π² s t)] = -2π (2π s)^{p+1} S_{p+1}(-4π² s t)`, i.e.
  `∂_t [(s/t)^{p/2} J_p(4π√(s t))] = -2π (s/t)^{(p+1)/2} J_{p+1}(4π√(s t))`.

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Nat

namespace FormalResearch.ModularBootstrap.Upper.Hankel

open FormalResearch.ModularBootstrap.WeightAxioms

/-- `J_p(x) = (x/2)^p S_p(-x²/4)` for natural `p`. -/
theorem besselJ_nat_eq (p : ℕ) (x : ℂ) :
    Complex.besselJ (p : ℂ) x = (x / 2) ^ p * besselSC p (-(x ^ 2 / 4)) := by
  rw [Complex.besselJ_def]
  simp only [Complex.cpow_natCast]
  congr 1
  unfold besselSC
  rw [show ((p + 1 : ℕ) : ℂ) = (p : ℂ) + 1 by push_cast; ring]
  congr 1
  ring

/-- `J_p(x) = i^p I_p(-i x)`. -/
theorem besselJ_eq_I_besselIC (p : ℕ) (x : ℂ) :
    Complex.besselJ (p : ℂ) x = I ^ p * besselIC p (-I * x) := by
  rw [besselJ_nat_eq]
  unfold besselIC
  rw [← mul_assoc, ← mul_pow]
  have e1 : I * (-I * x / 2) = x / 2 := by
    have : I * (-I) = 1 := by simp
    calc I * (-I * x / 2) = (I * (-I)) * x / 2 := by ring
      _ = _ := by rw [this]; ring
  have e2 : (-I * x) ^ 2 / 4 = -(x ^ 2 / 4) := by
    have : (-I * x) ^ 2 = -(x ^ 2) := by
      rw [mul_pow, neg_sq, Complex.I_sq]; ring
    rw [this]; ring
  rw [e1, e2]

/-- `|J_p(x)| ≤ 1` for real `x`. -/
theorem norm_besselJ_nat_le_one (p : ℕ) (x : ℝ) : ‖Complex.besselJ (p : ℂ) (x : ℂ)‖ ≤ 1 := by
  rw [besselJ_eq_I_besselIC, besselIC_eq_integral, norm_mul, norm_pow, Complex.norm_I, one_pow,
    one_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hb : ‖∫ θ in (0 : ℝ)..π, Complex.exp (-I * (x : ℂ) * (Real.cos θ : ℝ)) *
      (Real.cos (p * θ) : ℝ)‖ ≤ 1 * |π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun θ _ => ?_)
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have : (-I * (x : ℂ) * ((Real.cos θ : ℝ) : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]
    exact Real.abs_cos_le_one _
  rw [sub_zero, abs_of_pos Real.pi_pos, one_mul] at hb
  calc π⁻¹ * ‖∫ θ in (0 : ℝ)..π, Complex.exp (-I * (x : ℂ) * (Real.cos θ : ℝ)) *
        (Real.cos (p * θ) : ℝ)‖ ≤ π⁻¹ * π := by gcongr
    _ = 1 := inv_mul_cancel₀ Real.pi_pos.ne'

/-! ### The derivative `S_p' = S_{p+1}` -/

lemma hasDerivAt_besselSC (n : ℕ) (y : ℂ) : HasDerivAt (besselSC n) (besselSC (n + 1) y) y := by
  set R : ℝ := ‖y‖ + 1 with hR
  have hRpos : 0 < R := by positivity
  let g : ℕ → ℂ → ℂ := fun k z => z ^ k / ((k ! : ℂ) * ((k + n)! : ℂ))
  let g' : ℕ → ℂ → ℂ := fun k z => ((k : ℂ) * z ^ (k - 1)) / ((k ! : ℂ) * ((k + n)! : ℂ))
  have hg : ∀ k z, z ∈ ball (0 : ℂ) R → HasDerivAt (g k) (g' k z) z := by
    intro k z _
    exact (hasDerivAt_pow k z).div_const _
  let u : ℕ → ℝ := fun k => R ^ (k - 1) / ((k - 1)! : ℝ)
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    simpa [u] using Real.summable_pow_div_factorial R
  have hg' : ∀ k z, z ∈ ball (0 : ℂ) R → ‖g' k z‖ ≤ u k := by
    intro k z hz
    have hzR : ‖z‖ ≤ R := by simpa using (mem_ball_zero_iff.mp hz).le
    rcases k with _ | k
    · simp only [g', u]; simp
    · simp only [g', u, Nat.add_sub_cancel]
      have hf : ((k + 1)! : ℂ) = ((k + 1 : ℕ) : ℂ) * (k ! : ℂ) := by
        rw [Nat.factorial_succ]; push_cast; ring
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have e : (((k + 1 : ℕ) : ℂ) * z ^ k) / (((k + 1)! : ℂ) * (((k + 1) + n)! : ℂ)) =
          z ^ k / ((k ! : ℂ) * (((k + 1) + n)! : ℂ)) := by
        rw [hf]
        have : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
        have : (((k + 1) + n)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
        field_simp
      rw [e, norm_div, norm_pow, norm_mul]
      have h1 : (1 : ℝ) ≤ ‖(((k + 1) + n)! : ℂ)‖ := by
        rw [Complex.norm_natCast]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
      have h2 : ‖(k ! : ℂ)‖ = (k ! : ℝ) := by rw [Complex.norm_natCast]
      rw [h2]
      have hkf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
      calc ‖z‖ ^ k / ((k ! : ℝ) * ‖(((k + 1) + n)! : ℂ)‖) ≤ ‖z‖ ^ k / ((k ! : ℝ) * 1) := by
            gcongr
        _ ≤ R ^ k / (k ! : ℝ) := by
            rw [mul_one]; gcongr
  have hy : y ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hsum0 : Summable fun k => g k y := by
    refine Summable.of_norm_bounded (g := fun k => ‖y‖ ^ k / (k ! : ℝ))
      (Real.summable_pow_div_factorial ‖y‖) fun k => ?_
    simp only [g]
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have : (1 : ℝ) ≤ ((k + n)! : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hkf : (0 : ℝ) < k ! := by exact_mod_cast Nat.factorial_pos k
    calc ‖y‖ ^ k / ((k ! : ℝ) * ((k + n)! : ℝ)) ≤ ‖y‖ ^ k / ((k ! : ℝ) * 1) := by gcongr
      _ = _ := by rw [mul_one]
  have key := hasDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected
    hg hg' hy hsum0 hy
  have hfun : (fun z => ∑' k, g k z) = besselSC n := by
    funext z; exact (besselSC_eq_tsum n z).symm
  rw [hfun] at key
  refine key.congr_deriv ?_
  have hsg : Summable fun k => g' k y :=
    Summable.of_norm_bounded hu fun k => hg' k y hy
  rw [hsg.tsum_eq_zero_add, besselSC_eq_tsum]
  have h0 : g' 0 y = 0 := by simp [g']
  rw [h0, zero_add]
  refine tsum_congr fun k => ?_
  simp only [g']
  have hf : ((k + 1)! : ℂ) = ((k + 1 : ℕ) : ℂ) * (k ! : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hidx : k + 1 + n = k + (n + 1) := by ring
  rw [Nat.add_sub_cancel, hf, hidx]
  have : (k ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos k).ne'
  have : ((k + (n + 1))! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  field_simp

/-! ### The kernel `(s/t)^{p/2} J_p(4π√(s t))` -/

/-- The kernel identity: for `s ≥ 0`, `t > 0`,
`(√(s/t))^p J_p(4π√(s t)) = (2π s)^p S_p(-4π² s t)`. -/
theorem besselJ_kernel_eq (p : ℕ) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    (((√(s / t)) ^ p : ℝ) : ℂ) * Complex.besselJ (p : ℂ) ((4 * π * √(s * t) : ℝ) : ℂ) =
      (2 * π * (s : ℂ)) ^ p * besselSC p (-(4 * (π : ℂ) ^ 2 * (s : ℂ) * (t : ℂ))) := by
  rw [besselJ_nat_eq]
  have hst : 0 ≤ s * t := by positivity
  have hsq : ((√(s * t) : ℝ) : ℂ) ^ 2 = ((s * t : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt hst
  have e1 : (((4 * π * √(s * t) : ℝ) : ℂ) ^ 2 / 4) = 4 * (π : ℂ) ^ 2 * (s : ℂ) * (t : ℂ) := by
    push_cast
    have : ((√(s * t) : ℝ) : ℂ) ^ 2 = (s : ℂ) * (t : ℂ) := by rw [hsq]; push_cast; ring
    calc (4 * (π : ℂ) * ((√(s * t) : ℝ) : ℂ)) ^ 2 / 4
        = 4 * (π : ℂ) ^ 2 * ((√(s * t) : ℝ) : ℂ) ^ 2 := by ring
      _ = _ := by rw [this]; ring
  rw [e1]
  have hprod : √(s / t) * √(s * t) = s := by
    rw [← Real.sqrt_mul (by positivity)]
    have : s / t * (s * t) = s ^ 2 := by field_simp
    rw [this, Real.sqrt_sq hs]
  have e2 : (((√(s / t)) ^ p : ℝ) : ℂ) * (((4 * π * √(s * t) : ℝ) : ℂ) / 2) ^ p =
      (2 * π * (s : ℂ)) ^ p := by
    push_cast
    rw [← mul_pow]
    congr 1
    have : (((√(s / t) : ℝ)) : ℂ) * ((√(s * t) : ℝ) : ℂ) = (s : ℂ) := by
      exact_mod_cast hprod
    calc ((√(s / t) : ℝ) : ℂ) * (4 * (π : ℂ) * ((√(s * t) : ℝ) : ℂ) / 2)
        = 2 * (π : ℂ) * (((√(s / t) : ℝ) : ℂ) * ((√(s * t) : ℝ) : ℂ)) := by ring
      _ = _ := by rw [this]
  rw [← mul_assoc, e2]

/-- `∂_t [(2π s)^p S_p(-4π² s t)] = -2π (2π s)^{p+1} S_{p+1}(-4π² s t)` (real `t`). -/
theorem hasDerivAt_besselKernel (p : ℕ) (s t : ℝ) :
    HasDerivAt (fun t : ℝ => (2 * π * (s : ℂ)) ^ p * besselSC p (-(4 * (π : ℂ) ^ 2 * (s : ℂ) * (t : ℂ))))
      (-(2 * (π : ℂ)) * ((2 * π * (s : ℂ)) ^ (p + 1) *
        besselSC (p + 1) (-(4 * (π : ℂ) ^ 2 * (s : ℂ) * (t : ℂ))))) t := by
  have hlin : HasDerivAt (fun ξ : ℂ => -(4 * (π : ℂ) ^ 2 * (s : ℂ) * ξ))
      (-(4 * (π : ℂ) ^ 2 * (s : ℂ))) (t : ℂ) := by
    exact (((hasDerivAt_id (t : ℂ)).const_mul (4 * (π : ℂ) ^ 2 * (s : ℂ))).neg).congr_deriv (by ring)
  have hS := (hasDerivAt_besselSC p (-(4 * (π : ℂ) ^ 2 * (s : ℂ) * (t : ℂ)))).scomp (t : ℂ) hlin
  have h2 := (hS.const_mul ((2 * π * (s : ℂ)) ^ p)).comp_ofReal
  refine h2.congr_deriv ?_
  simp only [smul_eq_mul]
  ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.norm_besselJ_nat_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_besselJ_nat_le_one

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.besselJ_kernel_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms besselJ_kernel_eq

/-- info: 'FormalResearch.ModularBootstrap.Upper.Hankel.hasDerivAt_besselKernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_besselKernel

end FormalResearch.ModularBootstrap.Upper.Hankel

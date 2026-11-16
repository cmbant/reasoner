module

public import FormalResearch.Complex.HadamardDefect

/-!
# Hadamard's factorization theorem for entire functions of finite order with `f 0 ≠ 0` (milestone H4)

Statement formalised (Hadamard 1893; Boas, *Entire functions*, Thm 2.7.1; Titchmarsh, *The theory of functions*, 8.24;
Conway, VII.5.1): let `f` be entire with `f 0 ≠ 0` and `‖f z‖ ≤ C exp (C ‖z‖^σ)` for some `σ > 0`, and let `a` be any
`Listing` of its (nonzero) zeros with multiplicity.  If `p : ℕ` satisfies `σ < p + 1` (for instance `p = ⌊σ⌋`, so
`p` is the integer part of the order; for non-integer `σ` this is the genus of the Hadamard theorem) then

* `Σ_i ‖a_i‖^{-(p+1)} < ∞` (H2, `Hadamard.Listing.canonData`), and
* there is a polynomial `P` of degree `≤ p` with `P 0 = 0` such that for all `z`
  `f z = f 0 · exp (P z) · ∏'_i E_p (z / a_i)`   (`Hadamard.hadamard_of_ne_zero`),

the product converging locally uniformly (`Hadamard.hasProd_E`).  The classical form "`f = z^m e^{P} ∏ E_p(z/a_n)`" with
a zero at the origin is `Hadamard.hadamard` in `HadamardGeneral`.

Proof (new route, no lower bound for canonical products): `Hadamard.iteratedDeriv_defect_eq_zero` shows that
`f'/f - Σ_i (z/a_i)^p/(z - a_i)` has vanishing `p`-th derivative on the connected open set `{f ≠ 0}`, hence is a polynomial
`Q` of degree `< p`; since `Σ_i (z/a_i)^p/(z-a_i)` is the logarithmic derivative of the canonical product,
`f e^{-∫Q}/Φ` has zero derivative there, hence is constant.  All **proved**.
-/

@[expose] public section

open Complex Filter Topology Finset Metric Set
open scoped BigOperators ComplexConjugate Classical Nat

namespace FormalResearch.Hadamard

variable {ι : Type*}

/-- The zero set of a nonzero entire function is countable. -/
lemma countable_zeros {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    {w : ℂ | f w = 0}.Countable := by
  have : {w : ℂ | f w = 0} = ⋃ n : ℕ, {w : ℂ | ‖w‖ ≤ (n : ℝ) ∧ f w = 0} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hw; obtain ⟨n, hn⟩ := exists_nat_ge ‖w‖; exact ⟨n, hn, hw⟩
    · rintro ⟨n, _, hw⟩; exact hw
  rw [this]
  exact Set.countable_iUnion fun n => (zeros_finite hf h0 n).countable

lemma isPreconnected_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) :
    IsPreconnected {w : ℂ | f w ≠ 0} := by
  have hcount := countable_zeros hf h0
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]; norm_num
  have := (hcount.isPathConnected_compl_of_one_lt_rank hrank).isConnected.isPreconnected
  have e : {w : ℂ | f w ≠ 0} = {w : ℂ | f w = 0}ᶜ := by ext w; simp
  rw [e]; exact this

section main

variable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (h0 : f 0 ≠ 0) {a : ι → ℂ} (L : Listing f a)
  {C σ : ℝ} (hC : 1 ≤ C) (hb : ∀ z, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ ^ σ)) (hσ : 0 < σ)
  {p : ℕ} (hp : σ < p + 1)
include hf h0 L hC hb hσ hp

/-- **Hadamard factorization, `f 0 ≠ 0`.** -/
theorem hadamard_of_ne_zero :
    ∃ c : ℕ → ℂ, ∀ z : ℂ, f z = f 0 * cexp (∑ k ∈ range p, (c k / ((k : ℂ) + 1)) * z ^ (k + 1)) *
      canonProd p a z := by
  have CD : CanonData p a := L.canonData hf h0 hC hb hσ.le hp
  set U : Set ℂ := {w | f w ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun hf.continuous continuous_const
  have hUc : IsPreconnected U := isPreconnected_ne_zero hf h0
  have hUa : ∀ w ∈ U, ∀ i, w ≠ a i := fun w hw i h => hw (h ▸ L.f_a hf h0 i)
  have h0U : (0 : ℂ) ∈ U := h0
  -- the sum is holomorphic on `U`
  have hLamS : DifferentiableOn ℂ (fun w => ∑' i, term p (a i) w) U := by
    have hlim := (tendstoLocallyUniformlyOn_partial CD).mono (Set.subset_univ U)
    exact hlim.differentiableOn (Eventually.of_forall fun t w hw =>
      (DifferentiableAt.fun_sum fun i _ =>
        differentiableAt_term p (hUa w hw i)).differentiableWithinAt) hUo
  have hq : DifferentiableOn ℂ (logDeriv f) U := by
    have h1 : logDeriv f = fun w => deriv f w / f w := by funext w; rw [logDeriv_apply]
    rw [h1]
    exact (hf.differentiableOn.deriv isOpen_univ |>.mono (Set.subset_univ U)).div
      (hf.differentiableOn.mono (Set.subset_univ U)) (fun w hw => hw)
  have hG : DifferentiableOn ℂ (fun w => logDeriv f w - ∑' i, term p (a i) w) U := hq.sub hLamS
  obtain ⟨c, hc⟩ := exists_poly_of_iteratedDeriv_eq_zero hUo hUc p _ hG
    (fun z hz => iteratedDeriv_defect_eq_zero hf h0 L hC hb hσ hp hz)
  refine ⟨c, ?_⟩
  have hΦd : Differentiable ℂ (canonProd p a) := differentiable_canonProd CD
  set Φ := canonProd p a with hΦ
  set P : ℂ → ℂ := fun w => ∑ k ∈ range p, (c k / ((k : ℂ) + 1)) * w ^ (k + 1) with hP
  have hPd : ∀ w, HasDerivAt P (∑ k ∈ range p, c k * w ^ k) w := by
    intro w
    refine HasDerivAt.fun_sum (fun k _ => ?_)
    have h1 := (hasDerivAt_pow (k + 1) w).const_mul (c k / ((k : ℂ) + 1))
    convert h1 using 1
    have hk : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    field_simp
  have hΦne : ∀ w ∈ U, Φ w ≠ 0 := fun w hw => canonProd_ne_zero CD (fun i h => hUa w hw i h)
  have hΦlog : ∀ w ∈ U, logDeriv Φ w = ∑' i, term p (a i) w := fun w hw => by
    rw [hΦ, logDeriv_canonProd CD (hUa w hw)]; rfl
  set D : ℂ → ℂ := fun w => f w * cexp (-(P w)) / Φ w with hD
  have hDd : DifferentiableOn ℂ D U := by
    intro w hw
    have h1 : DifferentiableAt ℂ (fun w => f w * cexp (-(P w))) w :=
      (hf w).mul (((hPd w).neg).cexp.differentiableAt)
    exact (h1.div (hΦd w) (hΦne w hw)).differentiableWithinAt
  have hD' : U.EqOn (deriv D) 0 := by
    intro w hw
    have hf' : HasDerivAt f (deriv f w) w := (hf w).hasDerivAt
    have hE : HasDerivAt (fun w => cexp (-(P w)))
        (cexp (-(P w)) * (-(∑ k ∈ range p, c k * w ^ k))) w := ((hPd w).neg).cexp
    have hΦ' : HasDerivAt Φ (deriv Φ w) w := (hΦd w).hasDerivAt
    have hDa := (hf'.mul hE).div hΦ' (hΦne w hw)
    have hDw : deriv D w = _ := hDa.deriv
    have hfw : f w ≠ 0 := hw
    have e1 : deriv f w = f w * (∑' i, term p (a i) w + ∑ k ∈ range p, c k * w ^ k) := by
      have h := hc w hw
      rw [logDeriv_apply] at h
      have h1 : deriv f w / f w = ∑' i, term p (a i) w + ∑ k ∈ range p, c k * w ^ k := by
        linear_combination h
      rw [div_eq_iff hfw] at h1
      rw [h1]; ring
    have e2 : deriv Φ w = Φ w * ∑' i, term p (a i) w := by
      have h := hΦlog w hw
      rw [logDeriv_apply] at h
      rw [div_eq_iff (hΦne w hw)] at h
      rw [h]; ring
    rw [hDw, e1, e2]
    simp only [Pi.mul_apply, Pi.zero_apply]
    rw [div_eq_zero_iff]
    left
    ring
  have hconst := fun w (hw : w ∈ U) =>
    hUo.is_const_of_deriv_eq_zero hUc hDd hD' hw h0U
  have hP0 : P 0 = 0 := by simp [hP]
  have hΦ0 : Φ 0 = 1 := by simp [hΦ, canonProd, E_zero_arg]
  have heqU : ∀ w ∈ U, f w = f 0 * cexp (P w) * Φ w := by
    intro w hw
    have h1 := hconst w hw
    simp only [hD, hP0, hΦ0, neg_zero, Complex.exp_zero, mul_one, div_one] at h1
    have hne := hΦne w hw
    have hexp : cexp (-(P w)) * cexp (P w) = 1 := by rw [← Complex.exp_add]; simp
    field_simp at h1
    calc f w = f w * (cexp (-(P w)) * cexp (P w)) := by rw [hexp, mul_one]
      _ = (f w * cexp (-(P w))) * cexp (P w) := by ring
      _ = Φ w * f 0 * cexp (P w) := by rw [h1]
      _ = _ := by ring
  have hdense : Dense {w : ℂ | f w = 0}ᶜ := Set.Countable.dense_compl ℝ (countable_zeros hf h0)
  have hcont : Continuous fun z => f 0 * cexp (P z) * Φ z := by
    have hPc : Continuous P := by
      refine continuous_finsetSum _ fun k _ => ?_
      fun_prop
    have := continuous_canonProd CD
    fun_prop
  have hext : f = fun z => f 0 * cexp (P z) * Φ z :=
    Continuous.ext_on hdense hf.continuous hcont (fun w hw => heqU w (by simpa [hU] using hw))
  exact fun z => congrFun hext z

end main

end FormalResearch.Hadamard

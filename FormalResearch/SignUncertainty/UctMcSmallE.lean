module

public import FormalResearch.SignUncertainty.UctMcSmallBd
public import FormalResearch.SignUncertainty.CtDualIdBinet

/-!
# `SmallBd` for `e^{B_c(iτ)}` (F2a, `uct:Mc-small`)

From `ct_dual_id_part1` (`|∂_τ^r B_c(iτ)| ≤ C_r/c`): for `c ≥ 2` and `p ≥ 1/c`, `τ ↦ exp(B_c(iτ))` satisfies `SmallBd · p K`
with `K` independent of `c` (`smallBd_binet`).
-/

@[expose] public section

open Filter Topology Set

namespace FormalResearch.SignUncertainty

open FormalResearch.Asymptotics

lemma binetDiff_zero (c : ℝ) : binetDiff c 0 = 0 := by
  unfold binetDiff; simp

theorem smallBd_binet : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, 2 ≤ c → ∀ p : ℝ, 1 / c ≤ p →
    SmallBd (fun τ : ℝ => Complex.exp (binetDiff c ((τ : ℂ) * Complex.I))) p K := by
  obtain ⟨hdec, hdiff, -⟩ := ct_dual_id_part1
  obtain ⟨C1, h1⟩ := hdec 1 le_rfl
  obtain ⟨C2, h2⟩ := hdec 2 (by norm_num)
  obtain ⟨C3, h3⟩ := hdec 3 (by norm_num)
  set B : ℝ := max (max C1 C2) (max C3 0) with hB
  have hB0 : 0 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have hB1 : C1 ≤ B := (le_max_left _ _).trans (le_max_left _ _)
  have hB2 : C2 ≤ B := (le_max_right _ _).trans (le_max_left _ _)
  have hB3 : C3 ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  set Λ : ℝ := Real.exp (B / 10) with hΛ
  have hΛ1 : 1 ≤ Λ := Real.one_le_exp (by positivity)
  refine ⟨(B + 3 * B ^ 2 + B ^ 3 + 1) * Λ, by positivity, fun c hc p hp => ?_⟩
  have hc0 : 0 < c := by linarith
  have hcinv : 1 / c ≤ 1 := by rw [div_le_one hc0]; linarith
  have hp0 : 0 ≤ p := le_trans (by positivity) hp
  set g : ℝ → ℂ := fun τ => binetDiff c (Complex.I * (τ : ℂ)) with hg
  have hfun : (fun τ : ℝ => Complex.exp (binetDiff c ((τ : ℂ) * Complex.I))) = fun τ => Complex.exp (g τ) := by
    funext τ; simp only [hg, mul_comm]
  rw [hfun]
  have hgd : ContDiff ℝ 3 g := by
    have hG := hdiff c hc
    have hU : IsOpen {τ : ℂ | -1 < τ.im} := isOpen_lt continuous_const Complex.continuous_im
    have : ContDiffOn ℝ 3 (fun τ : ℂ => binetDiff c (Complex.I * τ)) {τ : ℂ | -1 < τ.im} :=
      ((hG.contDiffOn hU).restrict_scalars ℝ).of_le (by exact_mod_cast le_top)
    exact this.comp_contDiff (Complex.ofRealCLM.contDiff) (fun x => by simp)
  obtain ⟨g0, g1, g2⟩ := cd3_diffs hgd
  have b1 : ∀ τ, ‖deriv g τ‖ ≤ B / c := fun τ => by
    have := h1 c hc τ
    rw [iteratedDeriv_one] at this
    refine this.trans ?_
    rw [div_le_div_iff₀ (by positivity) hc0]
    have : (1 + |τ|) ^ (1 + 1) ≥ 1 := one_le_pow₀ (by linarith [abs_nonneg τ])
    nlinarith [mul_nonneg hB0 hc0.le, mul_le_mul_of_nonneg_left hB1 hc0.le]
  have b2 : ∀ τ, ‖deriv (deriv g) τ‖ ≤ B / c := fun τ => by
    have := h2 c hc τ
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    refine this.trans ?_
    rw [div_le_div_iff₀ (by positivity) hc0]
    have : (1 + |τ|) ^ (2 + 1) ≥ 1 := one_le_pow₀ (by linarith [abs_nonneg τ])
    nlinarith [mul_nonneg hB0 hc0.le, mul_le_mul_of_nonneg_left hB2 hc0.le]
  have b3 : ∀ τ, ‖deriv (deriv (deriv g)) τ‖ ≤ B / c := fun τ => by
    have := h3 c hc τ
    rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_one] at this
    refine this.trans ?_
    rw [div_le_div_iff₀ (by positivity) hc0]
    have : (1 + |τ|) ^ (3 + 1) ≥ 1 := one_le_pow₀ (by linarith [abs_nonneg τ])
    nlinarith [mul_nonneg hB0 hc0.le, mul_le_mul_of_nonneg_left hB3 hc0.le]
  have gz : g 0 = 0 := by simp [hg, binetDiff_zero]
  have bg : ∀ τ, ‖g τ‖ ≤ B / c * |τ| := fun τ => by
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := univ) (C := B / c) (fun x _ => g0 x)
      (fun x _ => b1 x) convex_univ (mem_univ 0) (mem_univ τ)
    rw [gz, sub_zero, sub_zero, Real.norm_eq_abs] at this
    exact this
  have hBc : B / c ≤ B / 2 := div_le_div_of_nonneg_left hB0 (by norm_num) hc
  have hEn : ∀ τ : ℝ, |τ| ≤ 1 / 5 → ‖Complex.exp (g τ)‖ ≤ Λ := fun τ hτ => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((bg τ).trans ?_))
    have : B / c * |τ| ≤ B / 2 * (1 / 5) := mul_le_mul hBc hτ (abs_nonneg τ) (by positivity)
    linarith
  -- derivatives of exp ∘ g
  have e1 : deriv (fun τ => Complex.exp (g τ)) = fun τ => Complex.exp (g τ) * deriv g τ := by
    funext τ; exact ((g0 τ).hasDerivAt.cexp).deriv
  have e2 : deriv (deriv (fun τ => Complex.exp (g τ))) =
      fun τ => Complex.exp (g τ) * (deriv g τ * deriv g τ + deriv (deriv g) τ) := by
    rw [e1]; funext τ
    have h := ((g0 τ).hasDerivAt.cexp).mul (g1 τ).hasDerivAt
    have h' : HasDerivAt (fun τ => Complex.exp (g τ) * deriv g τ)
        (Complex.exp (g τ) * (deriv g τ * deriv g τ + deriv (deriv g) τ)) τ := by
      convert h using 1; ring
    exact h'.deriv
  have e3 : deriv (deriv (deriv (fun τ => Complex.exp (g τ)))) =
      fun τ => Complex.exp (g τ) * (deriv g τ * (deriv g τ * deriv g τ) + 3 * (deriv g τ * deriv (deriv g) τ) +
        deriv (deriv (deriv g)) τ) := by
    rw [e2]; funext τ
    have ha := ((g0 τ).hasDerivAt.cexp)
    have hb := ((g1 τ).hasDerivAt.mul (g1 τ).hasDerivAt).add (g2 τ).hasDerivAt
    have h := ha.mul hb
    have h' : HasDerivAt (fun τ => Complex.exp (g τ) * (deriv g τ * deriv g τ + deriv (deriv g) τ))
        (Complex.exp (g τ) * (deriv g τ * (deriv g τ * deriv g τ) + 3 * (deriv g τ * deriv (deriv g) τ) +
          deriv (deriv (deriv g)) τ)) τ := by
      convert h using 1; simp only [Pi.add_apply, Pi.mul_apply]; ring
    exact h'.deriv
  refine ⟨(hgd.cexp), fun τ hτ => ?_⟩
  have hEn' := hEn τ hτ
  have hτ0 := abs_nonneg τ
  have n1 := b1 τ
  have n2 := b2 τ
  have n3 := b3 τ
  have hBcpos : 0 ≤ B / c := by positivity
  have hBp : B / c ≤ B * p := by
    calc B / c = B * (1 / c) := by ring
      _ ≤ B * p := mul_le_mul_of_nonneg_left hp hB0
  have hBc1 : B / c ≤ B := by
    calc B / c = B * (1 / c) := by ring
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hcinv hB0
      _ = B := mul_one B
  have hKΛ : 0 ≤ (B + 3 * B ^ 2 + B ^ 3 + 1) * Λ := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- value: MVT for exp ∘ g
    have hE0 : Complex.exp (g 0) = 1 := by rw [gz]; simp
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun τ => Complex.exp (g τ)) (s := Icc (-|τ|) |τ|)
      (C := Λ * (B / c)) (fun x _ => (g0 x).cexp)
      (fun x hx => by
        rw [e1]
        simp only [norm_mul]
        have hx' : |x| ≤ 1 / 5 := (abs_le.mpr ⟨hx.1, hx.2⟩ : |x| ≤ |τ|).trans hτ
        exact mul_le_mul (hEn x hx') (b1 x) (norm_nonneg _) (by positivity) |>.trans_eq (by ring))
      (convex_Icc _ _) (by simp [abs_nonneg] : (0 : ℝ) ∈ Icc (-|τ|) |τ|)
      (by constructor <;> linarith [neg_abs_le τ, le_abs_self τ] : τ ∈ Icc (-|τ|) |τ|)
    rw [hE0, sub_zero, Real.norm_eq_abs] at this
    have h0' : ‖Complex.exp (g τ) - 1‖ ≤ Λ * (B / c) * |τ| := by simpa using this
    have : Λ * (B / c) * |τ| ≤ (B + 3 * B ^ 2 + B ^ 3 + 1) * Λ * (p * |τ|) := by
      have h4 : B / c ≤ (B + 3 * B ^ 2 + B ^ 3 + 1) * p := by
        have : B * p ≤ (B + 3 * B ^ 2 + B ^ 3 + 1) * p := by
          apply mul_le_mul_of_nonneg_right _ hp0; nlinarith [sq_nonneg B, pow_nonneg hB0 3]
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h4 (le_trans zero_le_one hΛ1), mul_nonneg hp0 hτ0]
    nlinarith [mul_nonneg (mul_nonneg hKΛ hp0) hτ0, mul_nonneg hKΛ (sq_nonneg τ)]
  · rw [e1]; simp only [norm_mul]
    have h1' := mul_le_mul hEn' (n1.trans hBp) (norm_nonneg _) (by positivity)
    have h2' : Λ * (B * p) ≤ (B + 3 * B ^ 2 + B ^ 3 + 1) * Λ * (p + |τ|) := by
      have : 0 ≤ Λ * p := by positivity
      nlinarith [mul_nonneg this (sq_nonneg B), mul_nonneg this (pow_nonneg hB0 3), mul_nonneg hKΛ hτ0, mul_nonneg this hB0,
        mul_nonneg (le_trans zero_le_one hΛ1) (mul_nonneg hB0 hτ0)]
    linarith
  · rw [e2]
    simp only [norm_mul]
    have hs : ‖deriv g τ * deriv g τ + deriv (deriv g) τ‖ ≤ B ^ 2 + B := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
      have := mul_le_mul (n1.trans hBc1) (n1.trans hBc1) (norm_nonneg _) hB0
      nlinarith [n2.trans hBc1]
    have := mul_le_mul hEn' hs (norm_nonneg _) (by positivity)
    nlinarith
  · rw [e3]
    simp only [norm_mul]
    have hs : ‖deriv g τ * (deriv g τ * deriv g τ) + 3 * (deriv g τ * deriv (deriv g) τ) + deriv (deriv (deriv g)) τ‖ ≤
        B ^ 3 + 3 * B ^ 2 + B := by
      have h3' : ‖(3 : ℂ)‖ = 3 := by simp
      refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl le_rfl)) le_rfl) |>.trans ?_
      rw [norm_mul, norm_mul, norm_mul, norm_mul, h3']
      have a1 := n1.trans hBc1
      have a2 := n2.trans hBc1
      have a3 := n3.trans hBc1
      have n1' := norm_nonneg (deriv g τ)
      have n2' := norm_nonneg (deriv (deriv g) τ)
      have t1 := mul_le_mul a1 (mul_le_mul a1 a1 n1' hB0) (by positivity) hB0
      have t2 := mul_le_mul a1 a2 n2' hB0
      nlinarith [t1, t2, a3]
    have := mul_le_mul hEn' hs (norm_nonneg _) (by positivity)
    nlinarith

/-- info: 'FormalResearch.SignUncertainty.smallBd_binet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms smallBd_binet

end FormalResearch.SignUncertainty

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Small-`τ` bounds with two scales: the class `SmallBd` (F2a helper for `uct:Mc-small`)

`SmallBd f p K`: `f : ℝ → ℂ` is `C³` and on `|τ| ≤ 1/5`
`|f - 1| ≤ K(p|τ| + τ²)`, `|f'| ≤ K(p + |τ|)`, `|f''|, |f'''| ≤ K`.  The class is closed under products
(`SmallBd.mul`, for `0 ≤ p ≤ 1`, constant `20(K+1)(L+1)`).  `Uct Mc-small` is `SmallBd (M_c) (c^{-2/3}) K`.
-/

@[expose] public section

open Filter Topology

namespace FormalResearch.SignUncertainty

def SmallBd (f : ℝ → ℂ) (p K : ℝ) : Prop :=
  ContDiff ℝ 3 f ∧ ∀ τ : ℝ, |τ| ≤ 1 / 5 → ‖f τ - 1‖ ≤ K * (p * |τ| + τ ^ 2) ∧ ‖deriv f τ‖ ≤ K * (p + |τ|) ∧
    ‖deriv (deriv f) τ‖ ≤ K ∧ ‖deriv (deriv (deriv f)) τ‖ ≤ K

lemma cd3_diffs {f : ℝ → ℂ} (hf : ContDiff ℝ 3 f) :
    Differentiable ℝ f ∧ Differentiable ℝ (deriv f) ∧ Differentiable ℝ (deriv (deriv f)) := by
  have h3 : ContDiff ℝ ((2 : ℕ) + 1) f := by exact hf
  obtain ⟨d0, -, d1⟩ := (contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h3
  have h2 : ContDiff ℝ ((1 : ℕ) + 1) (deriv f) := by exact d1
  obtain ⟨d1', -, d2⟩ := (contDiff_succ_iff_deriv (𝕜 := ℝ)).mp h2
  exact ⟨d0, d1', d2.differentiable (by norm_num)⟩

lemma leibniz3 {f g : ℝ → ℂ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g) (τ : ℝ) :
    deriv (fun t => f t * g t) τ = deriv f τ * g τ + f τ * deriv g τ ∧
    deriv (deriv (fun t => f t * g t)) τ =
      deriv (deriv f) τ * g τ + 2 * (deriv f τ * deriv g τ) + f τ * deriv (deriv g) τ ∧
    deriv (deriv (deriv (fun t => f t * g t))) τ =
      deriv (deriv (deriv f)) τ * g τ + 3 * (deriv (deriv f) τ * deriv g τ) +
        3 * (deriv f τ * deriv (deriv g) τ) + f τ * deriv (deriv (deriv g)) τ := by
  obtain ⟨f0, f1, f2⟩ := cd3_diffs hf
  obtain ⟨g0, g1, g2⟩ := cd3_diffs hg
  have hd1 : deriv (fun t => f t * g t) = fun t => deriv f t * g t + f t * deriv g t := by
    funext t; exact deriv_mul (f0 t) (g0 t)
  have hd2 : deriv (deriv (fun t => f t * g t)) =
      fun t => deriv (deriv f) t * g t + 2 * (deriv f t * deriv g t) + f t * deriv (deriv g) t := by
    rw [hd1]; funext t
    have e2 := HasDerivAt.mul (f1 t).hasDerivAt (g0 t).hasDerivAt
    have e3 := HasDerivAt.mul (f0 t).hasDerivAt (g1 t).hasDerivAt
    have h : HasDerivAt (fun t => deriv f t * g t + f t * deriv g t)
        (deriv (deriv f) t * g t + deriv f t * deriv g t + (deriv f t * deriv g t + f t * deriv (deriv g) t)) t :=
      e2.add e3
    rw [h.deriv]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hd1]
  · rw [hd2]
  · rw [hd2]
    have e1 := HasDerivAt.mul (f2 τ).hasDerivAt (g0 τ).hasDerivAt
    have e2 := HasDerivAt.mul (f1 τ).hasDerivAt (g1 τ).hasDerivAt
    have e3 := HasDerivAt.mul (f0 τ).hasDerivAt (g2 τ).hasDerivAt
    have e5 : HasDerivAt (fun t => deriv (deriv f) t * g t + 2 * (deriv f t * deriv g t) + f t * deriv (deriv g) t)
        (deriv (deriv (deriv f)) τ * g τ + deriv (deriv f) τ * deriv g τ +
          2 * (deriv (deriv f) τ * deriv g τ + deriv f τ * deriv (deriv g) τ) +
          (deriv f τ * deriv (deriv g) τ + f τ * deriv (deriv (deriv g)) τ)) τ :=
      (e1.add (e2.const_mul 2)).add e3
    rw [e5.deriv]; ring

lemma SmallBd.mul {f g : ℝ → ℂ} {p K L : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hf : SmallBd f p K) (hg : SmallBd g p L) :
    SmallBd (fun t => f t * g t) p (20 * (K + 1) * (L + 1)) := by
  refine ⟨hf.1.mul hg.1, fun τ hτ => ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := hf.2 τ hτ
  obtain ⟨b0, b1, b2, b3⟩ := hg.2 τ hτ
  obtain ⟨l1, l2, l3⟩ := leibniz3 hf.1 hg.1 τ
  have hK : 0 ≤ K := by
    have := hf.2 0 (by simp)
    simp only [abs_zero, mul_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    have h := this.2.2.1
    exact (norm_nonneg _).trans h
  have hL : 0 ≤ L := by
    have := hg.2 0 (by simp)
    exact (norm_nonneg _).trans this.2.2.1
  have hτ0 : 0 ≤ |τ| := abs_nonneg τ
  have hτ2 : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
  have hx : 0 ≤ p * |τ| + τ ^ 2 := by positivity
  have hxs : p * |τ| + τ ^ 2 ≤ 1 := by nlinarith
  have hy : 0 ≤ p + |τ| := by positivity
  have hys : p + |τ| ≤ 2 := by linarith
  have nf : ‖f τ‖ ≤ 1 + K := by
    have : ‖f τ‖ ≤ ‖f τ - 1‖ + 1 := by
      have := norm_add_le (f τ - 1) 1; simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hxs hK]
  have ng : ‖g τ‖ ≤ 1 + L := by
    have : ‖g τ‖ ≤ ‖g τ - 1‖ + 1 := by
      have := norm_add_le (g τ - 1) 1; simpa using this
    nlinarith [mul_le_mul_of_nonneg_left hxs hL]
  have nf1 : ‖deriv f τ‖ ≤ 2 * K := by nlinarith [mul_le_mul_of_nonneg_left hys hK]
  have ng1 : ‖deriv g τ‖ ≤ 2 * L := by nlinarith [mul_le_mul_of_nonneg_left hys hL]
  have hnf : 0 ≤ ‖f τ‖ := norm_nonneg _
  have hng : 0 ≤ ‖g τ‖ := norm_nonneg _
  have hnf1 : 0 ≤ ‖deriv f τ‖ := norm_nonneg _
  have hng1 : 0 ≤ ‖deriv g τ‖ := norm_nonneg _
  have hKL : 0 ≤ (K + 1) * (L + 1) := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : f τ * g τ - 1 = (f τ - 1) * g τ + (g τ - 1) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    have := mul_le_mul a0 ng hng (by positivity)
    nlinarith [mul_nonneg hx hKL, mul_nonneg hx hK, mul_nonneg hx hL]
  · rw [l1]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have c1 := mul_le_mul a1 ng hng (by positivity)
    have c2 := mul_le_mul nf b1 (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hy hKL, mul_nonneg hy hK, mul_nonneg hy hL]
  · rw [l2]
    refine (norm_add_le _ _).trans ((add_le_add_left (norm_add_le _ _) _).trans ?_)
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    simp only [norm_mul, h2]
    have c1 := mul_le_mul a2 ng hng hK
    have c2 := mul_le_mul nf1 ng1 hng1 (by positivity)
    have c3 := mul_le_mul nf b2 (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hK hL]
  · rw [l3]
    refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl) |>.trans ?_
    have h3 : ‖(3 : ℂ)‖ = 3 := by simp
    simp only [norm_mul, h3]
    have c1 := mul_le_mul a3 ng hng hK
    have hf2 : ‖deriv (deriv f) τ‖ ≤ K := a2
    have c2 := mul_le_mul hf2 ng1 hng1 hK
    have c3 := mul_le_mul nf1 b2 (norm_nonneg _) (by positivity)
    have c4 := mul_le_mul nf b3 (norm_nonneg _) (by positivity)
    nlinarith [mul_nonneg hK hL]

/-- info: 'FormalResearch.SignUncertainty.SmallBd.mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SmallBd.mul

end FormalResearch.SignUncertainty

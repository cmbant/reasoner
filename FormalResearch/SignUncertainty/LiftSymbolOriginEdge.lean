module

public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.CohnElkies.HighBandUniform

/-!
# The lift symbol at the origin and at the edge `c^{1/3}`

Two evaluations of the lift symbol `W = liftSymbol X δ₀ m` at the two points of the edge
representation `f(0) = W(c^{1/3}) + σ W(0)` (`MellinLiftTail.lean`).

* `liftSymbol_zero_eq`: for a `HasU2` seed, `W(0) = k ∫ X` (the B-spline multiplier is `1` at `0`).
* `liftSymbol_edge_bound`: for the one-level seeds `airySeedU2 a b c₀` with `|a|, |b|, |c₀| ≤ R`, the window
  `δ₀ = ceBeta1 K liftEps c / 2` with `K ≥ 1` and `c ≥ 2`, the edge value satisfies
  `‖W(c^{1/3})‖ ≤ C K^{-m} c^{-5/6}`, with `C` depending only on `m` and `R`.

At the edge the multiplier argument is `c_s δ₀ c^{1/3} / m = π² K / (2m)` (`ceCs_mul_ceBeta1`,
`liftEps c · c^{1/3} = 1`), so `|M_ψ(c^{1/3})| ≤ (2m/(π² K))^m`, using `|bsplineE1 x| ≤ 1/x` for real `x > 0`.
The twisted Laplace transform at `c_s c^{1/3}` is bounded by the `U.2` right-half-plane bound
`C ‖1 + w‖^{-5/2} ≤ C c^{-5/6}`, applied to the three basis seeds and combined linearly.

Status: proved, unconditional.  Not formalised: the identification of `W(c^{1/3})` and `W(0)` with the
values of a Hankel eigenfunction (the representation `exists_hankelEigenfn_lift` is not restated here).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- At the origin the lift symbol is the integral of the seed: `W(0) = k ∫ X`. -/
theorem liftSymbol_zero_eq {X : ℝ → ℝ} (hX : HasU2 X) (δ₀ : ℝ) (m : ℕ) :
    liftSymbol X δ₀ m 0 = ((ceK * ∫ u : ℝ, X u : ℝ) : ℂ) := by
  have hint : ∫ u : ℝ, (X u : ℂ) * Complex.exp ((0 : ℂ) * (u : ℂ)) = ((∫ u : ℝ, X u : ℝ) : ℂ) := by
    simp only [zero_mul, Complex.exp_zero, mul_one]
    exact integral_ofReal
  unfold liftSymbol liftMultiplier airyTwistedLaplaceC
  simp only [mul_zero, bsplineE1_zero, one_pow, one_mul, zero_div, neg_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_div, Complex.exp_zero, hint]
  push_cast
  ring

/-- `|bsplineE1 x| ≤ 1 / x` for real `x > 0`. -/
theorem norm_bsplineE1_ofReal_le {x : ℝ} (hx : 0 < x) : ‖bsplineE1 (x : ℂ)‖ ≤ 1 / x := by
  have hne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hval : bsplineE1 (x : ℂ) = ((1 - Real.exp (-x)) / x : ℝ) := by
    rw [bsplineE1, if_neg hne]
    push_cast
    rfl
  have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 := Real.exp_pos (-x)
  have h3 : |1 - Real.exp (-x)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hx]
  exact div_le_div_of_nonneg_right h3 hx.le

/-- A right-half-plane bound `C ‖1 + w‖^{-5/2}` at the real edge `w = c^{1/3}` gives `C c^{-5/6}`. -/
theorem airyTwistedLaplaceC_edge_bound {X : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ C * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    {c : ℝ} (hc : 0 < c) :
    ‖airyTwistedLaplaceC X ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤ C * c ^ (-(5 / 6 : ℝ)) := by
  have ht : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have h := hb ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) (by simpa using ht.le)
  have hn : ‖1 + ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ = 1 + c ^ (1 / 3 : ℝ) := by
    rw [show (1 + ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) = ((1 + c ^ (1 / 3 : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [hn] at h
  have hpow : (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) ≤ (c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  have hc56 : (c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) = c ^ (-(5 / 6 : ℝ)) := by
    rw [← Real.rpow_mul hc.le]
    norm_num
  calc _ ≤ C * (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) := h
    _ ≤ C * (c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hpow hC
    _ = C * c ^ (-(5 / 6 : ℝ)) := by rw [hc56]

/-- **Edge bound for the one-level seeds.**  For `|a|, |b|, |c₀| ≤ R`, `K ≥ 1`, `c ≥ 2` and the window
`δ₀ = ceBeta1 K liftEps c / 2`, the lift symbol at the edge `c^{1/3}` satisfies
`‖W(c^{1/3})‖ ≤ C K^{-m} c^{-5/6}`, with `C = (2m/π²)^m (R+1)(C₁+C₂+C₃)`. -/
theorem liftSymbol_edge_bound {m : ℕ} (hm : 1 ≤ m) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C > 0, ∀ {a b c₀ : ℝ}, |a| ≤ R → |b| ≤ R → |c₀| ≤ R → ∀ {K c : ℝ}, 1 ≤ K → 2 ≤ c →
      ‖liftSymbol (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m (((c ^ (1 / 3 : ℝ) : ℝ)) : ℂ)‖ ≤
        C * K ^ (-(m : ℝ)) * c ^ (-(5 / 6 : ℝ)) := by
  obtain ⟨C₁, hC₁, h₁⟩ := (hasU2_airySeedU2 1 0 0).rhp
  obtain ⟨C₂, hC₂, h₂⟩ := (hasU2_airySeedU2 0 1 0).rhp
  obtain ⟨C₃, hC₃, h₃⟩ := (hasU2_airySeedU2 0 0 1).rhp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨(2 * m / Real.pi ^ 2) ^ m * ((R + 1) * (C₁ + C₂ + C₃)),
    mul_pos (pow_pos (div_pos (mul_pos two_pos hm0) (pow_pos Real.pi_pos 2)) m)
      (mul_pos (by linarith) (by linarith)), fun {a b c₀} ha hb hc {K c} hK hc2 => ?_⟩
  have hK0 : 0 < K := by linarith
  have hc0 : 0 < c := by linarith
  have ht : 0 < c ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hc0 _
  -- the scalar identities at the edge
  have hcε : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by
    rw [liftEps, ← Real.rpow_add hc0]
    norm_num
  have hx : ceCs * (ceBeta1 * K * liftEps c / 2) / m * c ^ (1 / 3 : ℝ) = Real.pi ^ 2 * K / (2 * m) := by
    calc ceCs * (ceBeta1 * K * liftEps c / 2) / m * c ^ (1 / 3 : ℝ)
        = (ceCs * ceBeta1) * K * (liftEps c * c ^ (1 / 3 : ℝ)) / (2 * m) := by ring
      _ = Real.pi ^ 2 * K / (2 * m) := by rw [ceCs_mul_ceBeta1, hcε]; ring
  -- the multiplier at the edge
  have hM : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ ≤
      (2 * m / Real.pi ^ 2) ^ m * K ^ (-(m : ℝ)) := by
    unfold liftMultiplier
    rw [show ((ceCs * (ceBeta1 * K * liftEps c / 2) / m : ℝ) : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) =
        ((Real.pi ^ 2 * K / (2 * m) : ℝ) : ℂ) by rw [← hx]; push_cast; ring]
    have hxpos : 0 < Real.pi ^ 2 * K / (2 * m) :=
      div_pos (mul_pos (pow_pos Real.pi_pos 2) hK0) (mul_pos two_pos hm0)
    rw [norm_pow]
    calc ‖bsplineE1 ((Real.pi ^ 2 * K / (2 * m) : ℝ) : ℂ)‖ ^ m ≤ (1 / (Real.pi ^ 2 * K / (2 * m))) ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_bsplineE1_ofReal_le hxpos) m
      _ = (2 * m / Real.pi ^ 2) ^ m * K ^ (-(m : ℝ)) := by
          rw [one_div_div, Real.rpow_neg hK0.le, Real.rpow_natCast]
          ring
  -- the twisted Laplace transform at the edge
  have hy0 : 0 ≤ ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)).re := by
    simpa using mul_nonneg ceCs_pos.le ht.le
  have hT : ‖airyTwistedLaplaceC (airySeedU2 a b c₀) ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤
      (R + 1) * (C₁ + C₂ + C₃) * c ^ (-(5 / 6 : ℝ)) := by
    rw [airyTwistedLaplaceC_airySeedU2_lin a b c₀ hy0]
    have e1 := airyTwistedLaplaceC_edge_bound hC₁.le h₁ hc0
    have e2 := airyTwistedLaplaceC_edge_bound hC₂.le h₂ hc0
    have e3 := airyTwistedLaplaceC_edge_bound hC₃.le h₃ hc0
    have n1 : ‖(a : ℂ) * airyTwistedLaplaceC (airySeedU2 1 0 0) ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤
        R * (C₁ * c ^ (-(5 / 6 : ℝ))) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul ha e1 (norm_nonneg _) hR
    have n2 : ‖(b : ℂ) * airyTwistedLaplaceC (airySeedU2 0 1 0) ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤
        R * (C₂ * c ^ (-(5 / 6 : ℝ))) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hb e2 (norm_nonneg _) hR
    have n3 : ‖(c₀ : ℂ) * airyTwistedLaplaceC (airySeedU2 0 0 1) ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖ ≤
        R * (C₃ * c ^ (-(5 / 6 : ℝ))) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]; exact mul_le_mul hc e3 (norm_nonneg _) hR
    have hsplit : (R + 1) * (C₁ + C₂ + C₃) * c ^ (-(5 / 6 : ℝ)) =
        R * (C₁ * c ^ (-(5 / 6 : ℝ))) + R * (C₂ * c ^ (-(5 / 6 : ℝ))) + R * (C₃ * c ^ (-(5 / 6 : ℝ))) +
          (C₁ + C₂ + C₃) * c ^ (-(5 / 6 : ℝ)) := by ring
    have hpos : 0 ≤ (C₁ + C₂ + C₃) * c ^ (-(5 / 6 : ℝ)) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hc0.le _)
    calc _ ≤ _ := norm_add₃_le
      _ ≤ R * (C₁ * c ^ (-(5 / 6 : ℝ))) + R * (C₂ * c ^ (-(5 / 6 : ℝ))) + R * (C₃ * c ^ (-(5 / 6 : ℝ))) := by
          linarith [n1, n2, n3]
      _ ≤ (R + 1) * (C₁ + C₂ + C₃) * c ^ (-(5 / 6 : ℝ)) := by linarith [hsplit, hpos]
  unfold liftSymbol
  rw [norm_mul]
  calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)‖ *
        ‖airyTwistedLaplaceC (airySeedU2 a b c₀) ((ceCs : ℂ) * ((c ^ (1 / 3 : ℝ) : ℝ) : ℂ))‖
      ≤ ((2 * m / Real.pi ^ 2) ^ m * K ^ (-(m : ℝ))) * ((R + 1) * (C₁ + C₂ + C₃) * c ^ (-(5 / 6 : ℝ))) :=
        mul_le_mul hM hT (norm_nonneg _)
          (mul_nonneg (pow_nonneg (by positivity) m) (Real.rpow_nonneg hK0.le _))
    _ = (2 * m / Real.pi ^ 2) ^ m * ((R + 1) * (C₁ + C₂ + C₃)) * K ^ (-(m : ℝ)) * c ^ (-(5 / 6 : ℝ)) := by ring

/-- info: 'FormalResearch.SignUncertainty.liftSymbol_zero_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftSymbol_zero_eq
/-- info: 'FormalResearch.SignUncertainty.norm_bsplineE1_ofReal_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms norm_bsplineE1_ofReal_le
/-- info: 'FormalResearch.SignUncertainty.airyTwistedLaplaceC_edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airyTwistedLaplaceC_edge_bound
/-- info: 'FormalResearch.SignUncertainty.liftSymbol_edge_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftSymbol_edge_bound

end FormalResearch.SignUncertainty

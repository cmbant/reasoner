module

public import FormalResearch.SignUncertainty.MiddleBandIbp
public import FormalResearch.SignUncertainty.MiddleBandNumerics
public import FormalResearch.SignUncertainty.MiddleBandPowers

/-!
# Pointwise-bound corollary of the two-IBP estimate, and its power-law instance (`GT.2a`, more 2)

`cubic_two_ibp` (`MiddleBandIbp`) uses constant bounds `B0, B1, B2, p`. The far and outer zones need
`x`-dependent bounds. This module gives those versions.

* `cubic_two_ibp_pw`: the same estimate as `cubic_two_ibp` with pointwise amplitude bounds
  `b0, b1, b2` and a pointwise lower bound `p` on `|ψ'|`. The proof is that of `two_ibp_phase_abs`
  (not the suprema of `cubic_two_ibp`): the integrand is bounded pointwise on `Icc α β` and the
  bound is integrated with `integral_mono_of_nonneg`. Classes: proved. The integrability of the
  bound is a hypothesis `hint`.
* `cubic_two_ibp_power`: the power-law instance `|a^{(r)}(x)| ≤ B x^{-5/2-r}` on `[α, β]` (`0 < α`),
  `p(x) = q x²`. The integrand becomes `B C x^{-17/2}` pointwise, with
  `C = 1/q² + π²/(2q³) + π²/(6q³) + π⁴/(12q⁴)`, and `∫_{[α,β]} x^{-17/2} ≤ ∫_{(α,∞)} = (2/15) α^{-15/2}`
  (`mb_tail_pow`). The constant `(2/15) α^{-15/2} B C` was checked by hand and is the one stated.
  Classes: proved. The integrability of the bound on `[α, β]` is proved (not assumed), since it equals
  `B C x^{-17/2}` there and `x^{-17/2}` is integrable on `[α, ∞)`.

Restatements of Mathlib: `mb_tail_pow` (imported from `MiddleBandPowers`) and the integral
inequalities `integral_mono_of_nonneg`, `setIntegral_mono_set`.

Import note: the brief lists `MiddleBandIbp` and `MiddleBandNumerics`; `MiddleBandPowers` is also
imported because `cubic_two_ibp_power` uses `mb_tail_pow`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Real

namespace FormalResearch.SignUncertainty

/-- Pointwise-bound version of `cubic_two_ibp`: amplitude bounds `‖a‖ ≤ b0`, `‖a'‖ ≤ b1`, `‖a''‖ ≤ b2`
on `[α, β]`, lower bound `0 < p ≤ |ψ'|` on `[α, β]`, for `ψ(x) = a0 x - π² x³/36`, and integrability of
the bound on `[α, β]`. Classes: proved. -/
theorem cubic_two_ibp_pw {a : ℝ → ℂ} {a0 α β : ℝ} (hαβ : α ≤ β) (ha : ContDiff ℝ 2 a)
    (hsupp : ∀ x, x ∉ Set.Icc α β → a x = 0) {b0 b1 b2 p : ℝ → ℝ}
    (hb0 : ∀ x ∈ Set.Icc α β, ‖a x‖ ≤ b0 x) (hb1 : ∀ x ∈ Set.Icc α β, ‖deriv a x‖ ≤ b1 x)
    (hb2 : ∀ x ∈ Set.Icc α β, ‖deriv (deriv a) x‖ ≤ b2 x)
    (hp : ∀ x ∈ Set.Icc α β, 0 < p x ∧ p x ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|)
    (hint : MeasureTheory.IntegrableOn (fun x => b2 x / p x ^ 2 + 3 * b1 x * (Real.pi ^ 2 * |x| / 6) / p x ^ 3
        + b0 x * (Real.pi ^ 2 / 6) / p x ^ 3 + 3 * b0 x * (Real.pi ^ 2 * x / 6) ^ 2 / p x ^ 4)
        (Set.Icc α β)) :
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      ∫ x in Set.Icc α β, (b2 x / p x ^ 2 + 3 * b1 x * (Real.pi ^ 2 * |x| / 6) / p x ^ 3
        + b0 x * (Real.pi ^ 2 / 6) / p x ^ 3 + 3 * b0 x * (Real.pi ^ 2 * x / 6) ^ 2 / p x ^ 4) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hda : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdda : Continuous (deriv (deriv a)) := hda.continuous_deriv le_rfl
  have hint2 : IntegrableOn (deriv (deriv a)) (Set.Icc α β) := hdda.integrableOn_Icc
  have ha2 : ∀ x ∉ (∅ : Set ℝ), DifferentiableAt ℝ (deriv a) x := fun x _ =>
    hda.differentiable (by norm_num) x
  have hψ3 : ContDiff ℝ 3 (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) := by fun_prop
  have hne : ∀ x ∈ Set.Icc α β, deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x ≠ 0 := by
    intro x hx h
    rw [mb_psi_deriv] at h
    have h2 := (hp x hx).2
    rw [h, abs_zero] at h2
    linarith [(hp x hx).1]
  have hmain := two_ibp_phase_abs hαβ ha1 ∅ Set.countable_empty ha2 hint2 hsupp hψ3 hne
  have hpt : ∀ x ∈ Set.Icc α β,
      ‖deriv (deriv a) x‖ / deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3)) x| /
          |deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3))) x| /
          |deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3)) x ^ 2 /
          deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x ^ 4
        ≤ b2 x / p x ^ 2 + 3 * b1 x * (Real.pi ^ 2 * |x| / 6) / p x ^ 3
          + b0 x * (Real.pi ^ 2 / 6) / p x ^ 3 + 3 * b0 x * (Real.pi ^ 2 * x / 6) ^ 2 / p x ^ 4 := by
    intro x hx
    rw [mb_psi_deriv, mb_psi_deriv2, mb_psi_deriv3]
    obtain ⟨hpx, hpD⟩ := hp x hx
    have hb0x := hb0 x hx
    have hb1x := hb1 x hx
    have hb2x := hb2 x hx
    have hb0n : 0 ≤ b0 x := le_trans (norm_nonneg _) hb0x
    have hb1n : 0 ≤ b1 x := le_trans (norm_nonneg _) hb1x
    have hb2n : 0 ≤ b2 x := le_trans (norm_nonneg _) hb2x
    have hpos2 : 0 < p x ^ 2 := pow_pos hpx 2
    have hpos3 : 0 < p x ^ 3 := pow_pos hpx 3
    have hpos4 : 0 < p x ^ 4 := pow_pos hpx 4
    have hdsq : p x ^ 2 ≤ (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 2 := by
      have h2 : p x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 2 := pow_le_pow_left₀ hpx.le hpD 2
      rwa [sq_abs] at h2
    have hab3 : p x ^ 3 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 3 := pow_le_pow_left₀ hpx.le hpD 3
    have hab4 : p x ^ 4 ≤ (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 4 := by
      have h4 : p x ^ 4 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 4 := pow_le_pow_left₀ hpx.le hpD 4
      rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4)] at h4
    have habs2 : |-(Real.pi ^ 2 * x / 6)| = Real.pi ^ 2 * |x| / 6 := by
      rw [abs_neg, abs_div, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi ^ 2)]
      norm_num
    have habs3 : |-(Real.pi ^ 2 / 6)| = Real.pi ^ 2 / 6 := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 6)]
    rw [habs2, habs3, neg_sq]
    have t1 : ‖deriv (deriv a) x‖ / (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 2 ≤ b2 x / p x ^ 2 :=
      div_le_div₀ hb2n hb2x hpos2 hdsq
    have t2 : 3 * ‖deriv a x‖ * (Real.pi ^ 2 * |x| / 6) / |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 3
        ≤ 3 * b1 x * (Real.pi ^ 2 * |x| / 6) / p x ^ 3 :=
      div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hb1n) (by positivity))
        (by gcongr) hpos3 hab3
    have t3 : ‖a x‖ * (Real.pi ^ 2 / 6) / |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 3
        ≤ b0 x * (Real.pi ^ 2 / 6) / p x ^ 3 :=
      div_le_div₀ (mul_nonneg hb0n (by positivity)) (by gcongr) hpos3 hab3
    have t4 : 3 * ‖a x‖ * (Real.pi ^ 2 * x / 6) ^ 2 / (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 4
        ≤ 3 * b0 x * (Real.pi ^ 2 * x / 6) ^ 2 / p x ^ 4 :=
      div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hb0n) (by positivity))
        (by gcongr) hpos4 hab4
    linarith
  have hBnn : ∀ x ∈ Set.Icc α β, 0 ≤ b2 x / p x ^ 2 + 3 * b1 x * (Real.pi ^ 2 * |x| / 6) / p x ^ 3
        + b0 x * (Real.pi ^ 2 / 6) / p x ^ 3 + 3 * b0 x * (Real.pi ^ 2 * x / 6) ^ 2 / p x ^ 4 := by
    intro x hx
    have hb0n : 0 ≤ b0 x := le_trans (norm_nonneg _) (hb0 x hx)
    have hb1n : 0 ≤ b1 x := le_trans (norm_nonneg _) (hb1 x hx)
    have hb2n : 0 ≤ b2 x := le_trans (norm_nonneg _) (hb2 x hx)
    have hpx := (hp x hx).1
    have hp2 : 0 < p x ^ 2 := pow_pos hpx 2
    have hp3 : 0 < p x ^ 3 := pow_pos hpx 3
    have hp4 : 0 < p x ^ 4 := pow_pos hpx 4
    positivity
  refine hmain.trans ?_
  refine integral_mono_of_nonneg ?_ hint ?_
  · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x _ => by
      beta_reduce
      positivity)
  · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x hx => hpt x hx)

/-- Power-law instance of `cubic_two_ibp_pw`: with `|a^{(r)}(x)| ≤ B x^{-5/2-r}` on `[α, β]`,
`0 < α`, and `p(x) = q x²` (so `|ψ'| ≥ q x²`), the integral is at most
`(2/15) α^{-15/2} B C`, `C = 1/q² + π²/(2q³) + π²/(6q³) + π⁴/(12q⁴)`. Classes: proved. -/
theorem cubic_two_ibp_power {a : ℝ → ℂ} {a0 α β B q : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hB : 0 ≤ B)
    (hq : 0 < q) (ha : ContDiff ℝ 2 a)
    (hsupp : ∀ x, x ∉ Set.Icc α β → a x = 0)
    (hb0 : ∀ x ∈ Set.Icc α β, ‖a x‖ ≤ B * x ^ (-(5 / 2 : ℝ)))
    (hb1 : ∀ x ∈ Set.Icc α β, ‖deriv a x‖ ≤ B * x ^ (-(7 / 2 : ℝ)))
    (hb2 : ∀ x ∈ Set.Icc α β, ‖deriv (deriv a) x‖ ≤ B * x ^ (-(9 / 2 : ℝ)))
    (hp : ∀ x ∈ Set.Icc α β, q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|) :
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      (2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) := by
  have hxpos : ∀ x ∈ Set.Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα (Set.mem_Icc.1 hx).1
  -- the integrand is `B C x^{-17/2}` pointwise on `[α, β]`
  have hGid : ∀ x ∈ Set.Icc α β,
      (B * x ^ (-(9 / 2 : ℝ))) / (q * x ^ 2) ^ 2
        + 3 * (B * x ^ (-(7 / 2 : ℝ))) * (Real.pi ^ 2 * |x| / 6) / (q * x ^ 2) ^ 3
        + (B * x ^ (-(5 / 2 : ℝ))) * (Real.pi ^ 2 / 6) / (q * x ^ 2) ^ 3
        + 3 * (B * x ^ (-(5 / 2 : ℝ))) * (Real.pi ^ 2 * x / 6) ^ 2 / (q * x ^ 2) ^ 4
        = B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
          + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) * x ^ (-(17 / 2 : ℝ)) := by
    intro x hx
    have hx0 : 0 < x := hxpos x hx
    have hxne : x ≠ 0 := hx0.ne'
    have hqne : q ≠ 0 := hq.ne'
    have e9 : x ^ (-(9 / 2 : ℝ)) = x ^ (-(17 / 2 : ℝ)) * x ^ (4 : ℕ) := by
      rw [show (-(9 / 2 : ℝ)) = -(17 / 2 : ℝ) + ((4 : ℕ) : ℝ) by norm_num, Real.rpow_add hx0,
        Real.rpow_natCast]
    have e7 : x ^ (-(7 / 2 : ℝ)) = x ^ (-(17 / 2 : ℝ)) * x ^ (5 : ℕ) := by
      rw [show (-(7 / 2 : ℝ)) = -(17 / 2 : ℝ) + ((5 : ℕ) : ℝ) by norm_num, Real.rpow_add hx0,
        Real.rpow_natCast]
    have e5 : x ^ (-(5 / 2 : ℝ)) = x ^ (-(17 / 2 : ℝ)) * x ^ (6 : ℕ) := by
      rw [show (-(5 / 2 : ℝ)) = -(17 / 2 : ℝ) + ((6 : ℕ) : ℝ) by norm_num, Real.rpow_add hx0,
        Real.rpow_natCast]
    rw [e9, e7, e5, abs_of_pos hx0]
    field_simp
    ring
  have hpow_Ici : IntegrableOn (fun x : ℝ => x ^ (-(17 / 2 : ℝ))) (Set.Ici α) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hα
  have hpow_int : IntegrableOn (fun x : ℝ => x ^ (-(17 / 2 : ℝ))) (Set.Icc α β) :=
    hpow_Ici.mono_set Set.Icc_subset_Ici_self
  have hint : IntegrableOn (fun x => (B * x ^ (-(9 / 2 : ℝ))) / (q * x ^ 2) ^ 2
        + 3 * (B * x ^ (-(7 / 2 : ℝ))) * (Real.pi ^ 2 * |x| / 6) / (q * x ^ 2) ^ 3
        + (B * x ^ (-(5 / 2 : ℝ))) * (Real.pi ^ 2 / 6) / (q * x ^ 2) ^ 3
        + 3 * (B * x ^ (-(5 / 2 : ℝ))) * (Real.pi ^ 2 * x / 6) ^ 2 / (q * x ^ 2) ^ 4)
        (Set.Icc α β) := by
    refine IntegrableOn.congr_fun
      (f := fun x => B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
          + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) * x ^ (-(17 / 2 : ℝ)))
      ((hpow_int.const_mul _)) (fun x hx => (hGid x hx).symm) measurableSet_Icc
  have hpw := cubic_two_ibp_pw (a := a) (a0 := a0) (α := α) (β := β) hαβ ha hsupp
    (b0 := fun x => B * x ^ (-(5 / 2 : ℝ))) (b1 := fun x => B * x ^ (-(7 / 2 : ℝ)))
    (b2 := fun x => B * x ^ (-(9 / 2 : ℝ))) (p := fun x => q * x ^ 2) hb0 hb1 hb2
    (fun x hx => ⟨mul_pos hq (pow_pos (hxpos x hx) 2), hp x hx⟩) hint
  have hC : 0 ≤ 1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3) + Real.pi ^ 2 / (6 * q ^ 3)
      + Real.pi ^ 4 / (12 * q ^ 4) := by
    have t1 : 0 ≤ 1 / q ^ 2 := div_nonneg zero_le_one (pow_pos hq 2).le
    have t2 : 0 ≤ Real.pi ^ 2 / (2 * q ^ 3) :=
      div_nonneg (by positivity) (mul_pos (by norm_num) (pow_pos hq 3)).le
    have t3 : 0 ≤ Real.pi ^ 2 / (6 * q ^ 3) :=
      div_nonneg (by positivity) (mul_pos (by norm_num) (pow_pos hq 3)).le
    have t4 : 0 ≤ Real.pi ^ 4 / (12 * q ^ 4) :=
      div_nonneg (by positivity) (mul_pos (by norm_num) (pow_pos hq 4)).le
    linarith
  have hBC : 0 ≤ B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
      + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) := mul_nonneg hB hC
  -- the tail integral over `[α, β]` of `x^{-17/2}`, bounded by the integral over `[α, ∞)`
  have hT : ∫ x in Set.Icc α β, x ^ (-(17 / 2 : ℝ)) ≤ (2 / 15) * α ^ (-(15 / 2 : ℝ)) := by
    have hfi := hpow_Ici
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici α)] (fun x : ℝ => x ^ (-(17 / 2 : ℝ))) :=
      (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x hx =>
        Real.rpow_nonneg (by have := Set.mem_Ici.1 hx; linarith) _)
    calc ∫ x in Set.Icc α β, x ^ (-(17 / 2 : ℝ))
        ≤ ∫ x in Set.Ici α, x ^ (-(17 / 2 : ℝ)) :=
          setIntegral_mono_set hfi hnn (ae_of_all _ fun x (hx : x ∈ Set.Icc α β) =>
            Set.Icc_subset_Ici_self hx)
      _ = ∫ x in Set.Ioi α, x ^ (-(17 / 2 : ℝ)) := by rw [integral_Ici_eq_integral_Ioi]
      _ = α ^ (1 - 17 / 2 : ℝ) / (17 / 2 - 1) := mb_tail_pow hα (by norm_num)
      _ = (2 / 15) * α ^ (-(15 / 2 : ℝ)) := by
          rw [show (1 - 17 / 2 : ℝ) = -(15 / 2) by norm_num]
          ring
  have hI : ∫ x in Set.Icc α β, B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
      + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) * x ^ (-(17 / 2 : ℝ))
      ≤ (2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) := by
    rw [integral_const_mul]
    calc _ ≤ B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
          + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) * ((2 / 15) * α ^ (-(15 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hT hBC
      _ = _ := by ring
  have hEq : ∫ x in Set.Icc α β, (B * x ^ (-(9 / 2 : ℝ))) / (q * x ^ 2) ^ 2
        + 3 * (B * x ^ (-(7 / 2 : ℝ))) * (Real.pi ^ 2 * |x| / 6) / (q * x ^ 2) ^ 3
        + (B * x ^ (-(5 / 2 : ℝ))) * (Real.pi ^ 2 / 6) / (q * x ^ 2) ^ 3
        + 3 * (B * x ^ (-(5 / 2 : ℝ))) * (Real.pi ^ 2 * x / 6) ^ 2 / (q * x ^ 2) ^ 4
      = ∫ x in Set.Icc α β, B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
          + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) * x ^ (-(17 / 2 : ℝ)) :=
    setIntegral_congr_fun measurableSet_Icc (fun x hx => hGid x hx)
  exact hpw.trans (hEq.le.trans hI)

/-- info: 'FormalResearch.SignUncertainty.cubic_two_ibp_pw' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_two_ibp_pw

/-- info: 'FormalResearch.SignUncertainty.cubic_two_ibp_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_two_ibp_power

end FormalResearch.SignUncertainty

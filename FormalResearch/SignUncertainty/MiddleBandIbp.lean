module

public import FormalResearch.CohnElkies.TwoIBPPhase
public import FormalResearch.SignUncertainty.MiddleBandNumerics

/-!
# Two integrations by parts for either sign of the phase derivative (GT.2a G1)

`FormalResearch.CohnElkies.two_ibp_phase` assumes `0 < ψ'` on `[u, v]`. Here the same bound is
proved when `ψ'` is nonzero on `[u, v]` of either sign, with the absolute values `|ψ'|` in the
denominators (`two_ibp_phase_abs`).

Proof sketch.
1. A continuous `ψ'` with no zero on `[u, v]` has constant sign there (`mbi_sign`, via
   `intermediate_value_uIcc`). Classes: proved.
2. If `ψ' > 0`, `two_ibp_phase` applies, and `|ψ'| = ψ'` turns its denominators into `|ψ'|`
   (`mbi_abs_pos`). Classes: proved.
3. If `ψ' < 0`, apply step 2 to `b = star ∘ a` and `ψ̃ = -ψ`, whose derivative `-ψ'` is positive.
   `∫ a e^{iψ}` is the conjugate of `∫ b e^{iψ̃}`, so the norms agree. The integrand terms agree
   pointwise because `|-ψ'| = |ψ'|`, and the even powers are unchanged (`mbi_abs_neg`).
   `deriv (deriv b)` equals `star (deriv (deriv a))` only off the countable set `s`, which is
   null, so that identity holds almost everywhere. Classes: proved.

`cubic_two_ibp` specialises to `ψ(x) = a0 x - π² x³/36`, with `ψ' = a0 - π² x²/12`,
`ψ'' = -π² x/6`, `ψ''' = -π²/6`; the derivative identities are those of
`FormalResearch.SignUncertainty.MiddleBandNumerics` (`mb_psi_deriv`, `mb_psi_deriv2`,
`mb_psi_deriv3`). Classes: proved, unconditionally in the stated hypotheses.

`cubic_two_ibp` has constant amplitude and phase bounds on `[α, β]`: it suits zones where `ψ'` is
roughly constant (shoulders). Zones where `|ψ'|` grows (far, outer) use `two_ibp_phase_abs`
directly with pointwise bounds.

Negative regression: the bound needs `ψ' ≠ 0` on `[u, v]`, which `cubic_two_ibp` supplies as
`p ≤ |ψ'|` on `[α, β]`. Without a lower bound the integrand has a pole at a zero of `ψ'`, and that
zone is treated separately (`gt2a_vdc_stationary.md`).

Used without proof here: `two_ibp_phase` (the case `ψ' > 0`, from the imported module),
`integral_conj`, `intermediate_value_uIcc`, and `div_le_div₀`.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-- A continuous function with no zero on `[u, v]` has constant sign there. Classes: proved. -/
lemma mbi_sign {f : ℝ → ℝ} {u v : ℝ} (hc : Continuous f) (hne : ∀ x ∈ Icc u v, f x ≠ 0) :
    (∀ x ∈ Icc u v, 0 < f x) ∨ (∀ x ∈ Icc u v, f x < 0) := by
  by_cases h : ∃ x ∈ Icc u v, 0 < f x
  · left
    obtain ⟨x0, hx0, hpos⟩ := h
    intro x hx
    rcases lt_or_gt_of_ne (hne x hx) with hneg | hp
    · exfalso
      have hsub : uIcc x0 x ⊆ Icc u v := Set.uIcc_subset_Icc hx0 hx
      obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc hc.continuousOn
        (Set.mem_uIcc.2 (Or.inr ⟨hneg.le, hpos.le⟩))
      exact hne y (hsub hy) hy0
    · exact hp
  · right
    intro x hx
    rcases lt_or_gt_of_ne (hne x hx) with hn | hp
    · exact hn
    · exact absurd ⟨x, hx, hp⟩ h

/-- The two integrations by parts when `ψ' > 0` on `[u, v]`, with the denominators written as
`|ψ'|`. Classes: proved (from `two_ibp_phase`). -/
theorem mbi_abs_pos {a : ℝ → ℂ} {ψ : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (ha : ContDiff ℝ 1 a) (s : Set ℝ) (hs : s.Countable)
    (ha2 : ∀ x ∉ s, DifferentiableAt ℝ (deriv a) x)
    (hint : IntegrableOn (deriv (deriv a)) (Set.Icc u v))
    (hsupp : ∀ x, x ∉ Set.Icc u v → a x = 0)
    (hψ : ContDiff ℝ 3 ψ) (hψ' : ∀ x ∈ Set.Icc u v, 0 < deriv ψ x) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      ∫ x in Set.Icc u v, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) := by
  refine (FormalResearch.CohnElkies.two_ibp_phase huv ha s hs ha2 hint hsupp hψ hψ').trans
    (le_of_eq ?_)
  refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  rw [abs_of_pos (hψ' x hx)]

/-- The case `ψ' < 0` on `[u, v]`, by conjugation and the reflected phase `-ψ`. Classes: proved. -/
theorem mbi_abs_neg {a : ℝ → ℂ} {ψ : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (ha : ContDiff ℝ 1 a) (s : Set ℝ) (hs : s.Countable)
    (ha2 : ∀ x ∉ s, DifferentiableAt ℝ (deriv a) x)
    (hint : IntegrableOn (deriv (deriv a)) (Set.Icc u v))
    (hsupp : ∀ x, x ∉ Set.Icc u v → a x = 0)
    (hψ : ContDiff ℝ 3 ψ) (hψ' : ∀ x ∈ Set.Icc u v, deriv ψ x < 0) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      ∫ x in Set.Icc u v, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) := by
  have hbc : ContDiff ℝ 1 (fun x => star (a x)) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp ha
  have hdb : ∀ x, HasDerivAt (fun y => star (a y)) (star (deriv a x)) x := fun x => by
    have hA : HasDerivAt a (deriv a x) x := (ha.differentiable (by norm_num) x).hasDerivAt
    exact HasDerivAt.star hA
  have hdb_fun : deriv (fun y => star (a y)) = fun x => star (deriv a x) :=
    funext fun x => (hdb x).deriv
  have hb1 : ∀ x, deriv (fun y => star (a y)) x = star (deriv a x) := fun x => (hdb x).deriv
  -- off the countable set `s` the second derivative of `b` is the conjugate
  have hae_vol : ∀ᵐ x ∂volume, x ∈ Icc u v →
      deriv (deriv fun y => star (a y)) x = star (deriv (deriv a) x) := by
    filter_upwards [hs.ae_notMem volume] with x hx _
    rw [hdb_fun]
    have hB : HasDerivAt (deriv a) (deriv (deriv a) x) x :=
      DifferentiableAt.hasDerivAt (ha2 x hx)
    exact (HasDerivAt.star hB).deriv
  have hae : deriv (deriv fun y => star (a y)) =ᵐ[volume.restrict (Icc u v)]
      fun x => star (deriv (deriv a) x) := by
    filter_upwards [ae_restrict_of_ae (hs.ae_notMem volume)] with x hx
    rw [hdb_fun]
    have hB : HasDerivAt (deriv a) (deriv (deriv a) x) x :=
      DifferentiableAt.hasDerivAt (ha2 x hx)
    exact (HasDerivAt.star hB).deriv
  have hstar_int : IntegrableOn (fun x => star (deriv (deriv a) x)) (Icc u v) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hint
  have hint_b : IntegrableOn (deriv (deriv fun y => star (a y))) (Icc u v) :=
    Integrable.congr hstar_int hae.symm
  have ha2_b : ∀ x ∉ s, DifferentiableAt ℝ (deriv fun y => star (a y)) x := by
    intro x hx
    rw [hdb_fun]
    exact DifferentiableAt.star (ha2 x hx)
  have hsupp_b : ∀ x, x ∉ Icc u v → star (a x) = 0 := fun x hx => by
    simp [hsupp x hx]
  have hψn : ContDiff ℝ 3 (fun x => -ψ x) := hψ.neg
  have hd1 : deriv (fun x => -ψ x) = fun x => -deriv ψ x := deriv.neg' (f := ψ)
  have hd2 : deriv (deriv (fun x => -ψ x)) = fun x => -deriv (deriv ψ) x := by
    rw [hd1]; exact deriv.neg' (f := deriv ψ)
  have hd3 : deriv (deriv (deriv (fun x => -ψ x))) = fun x => -deriv (deriv (deriv ψ)) x := by
    rw [hd2]; exact deriv.neg' (f := deriv (deriv ψ))
  have hpos_n : ∀ x ∈ Icc u v, 0 < deriv (fun x => -ψ x) x := by
    intro x hx
    rw [hd1]
    show 0 < -deriv ψ x
    linarith [hψ' x hx]
  have H := mbi_abs_pos (a := fun x => star (a x)) (ψ := fun x => -ψ x) huv hbc s hs ha2_b
    hint_b hsupp_b hψn hpos_n
  -- the phase integral is the conjugate of the original one
  have hpt : ∀ x, star (a x * Complex.exp (Complex.I * (ψ x : ℂ))) =
      star (a x) * Complex.exp (Complex.I * ((-ψ x : ℝ) : ℂ)) := by
    intro x
    have he : star (Complex.exp (Complex.I * (ψ x : ℂ))) =
        Complex.exp (Complex.I * ((-ψ x : ℝ) : ℂ)) := by
      show (starRingEnd ℂ) _ = _
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
      ring
    rw [star_mul', he]
  have hconj : ∫ x, star (a x * Complex.exp (Complex.I * (ψ x : ℂ))) =
      star (∫ x, a x * Complex.exp (Complex.I * (ψ x : ℂ))) := integral_conj
  -- pointwise identities between the two integrands on `[u, v]`
  have e1 : ∀ x, deriv (fun x => -ψ x) x = -deriv ψ x := fun x => by rw [hd1]
  have e2 : ∀ x, deriv (deriv (fun x => -ψ x)) x = -deriv (deriv ψ) x := fun x => by rw [hd2]
  have e3 : ∀ x, deriv (deriv (deriv (fun x => -ψ x))) x = -deriv (deriv (deriv ψ)) x :=
    fun x => by rw [hd3]
  have hRHS : (∫ x in Icc u v, (‖deriv (deriv fun y => star (a y)) x‖ /
        deriv (fun x => -ψ x) x ^ 2
        + 3 * ‖deriv (fun y => star (a y)) x‖ * |deriv (deriv (fun x => -ψ x)) x| /
          |deriv (fun x => -ψ x) x| ^ 3
        + ‖star (a x)‖ * |deriv (deriv (deriv (fun x => -ψ x))) x| /
          |deriv (fun x => -ψ x) x| ^ 3
        + 3 * ‖star (a x)‖ * deriv (deriv (fun x => -ψ x)) x ^ 2 /
          deriv (fun x => -ψ x) x ^ 4)) =
      ∫ x in Icc u v, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) := by
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hae_vol] with x hx hxI
    rw [hx hxI, hb1 x, e1 x, e2 x, e3 x]
    simp only [norm_star, abs_neg]
    ring
  calc ‖∫ x, a x * Complex.exp (Complex.I * (ψ x : ℂ))‖
      = ‖∫ x, star (a x * Complex.exp (Complex.I * (ψ x : ℂ)))‖ := by rw [hconj, norm_star]
    _ = ‖∫ x, star (a x) * Complex.exp (Complex.I * ((-ψ x : ℝ) : ℂ))‖ := by simp only [hpt]
    _ ≤ _ := H
    _ = _ := hRHS

/-- Two integrations by parts against `e^{iψ}` with `ψ' ≠ 0` of either sign on `[u, v]`
(`GT.2a G1`). Let `a ∈ C¹` vanish off `[u, v]`, with `a'` differentiable off a countable set `s`,
`a''` integrable on `[u, v]`, and `ψ ∈ C³` with `ψ' ≠ 0` on `[u, v]`. Then `|∫ a e^{iψ}|` is at most
the integral over `[u, v]` of
`|a''|/ψ'² + 3|a'||ψ''|/|ψ'|³ + |a||ψ'''|/|ψ'|³ + 3|a|ψ''²/ψ'⁴`.
Classes: proved (from `two_ibp_phase` and the constant sign of `ψ'`). -/
theorem two_ibp_phase_abs {a : ℝ → ℂ} {ψ : ℝ → ℝ} {u v : ℝ} (huv : u ≤ v)
    (ha : ContDiff ℝ 1 a) (s : Set ℝ) (hs : s.Countable)
    (ha2 : ∀ x ∉ s, DifferentiableAt ℝ (deriv a) x)
    (hint : IntegrableOn (deriv (deriv a)) (Set.Icc u v))
    (hsupp : ∀ x, x ∉ Set.Icc u v → a x = 0)
    (hψ : ContDiff ℝ 3 ψ) (hψ' : ∀ x ∈ Set.Icc u v, deriv ψ x ≠ 0) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      ∫ x in Set.Icc u v, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) := by
  have hψc : Continuous (deriv ψ) := hψ.continuous_deriv (by norm_num)
  rcases mbi_sign hψc hψ' with hp | hn
  · exact mbi_abs_pos huv ha s hs ha2 hint hsupp hψ hp
  · exact mbi_abs_neg huv ha s hs ha2 hint hsupp hψ hn

/-- Cubic-phase corollary of `two_ibp_phase_abs`, with `ψ(x) = a0 x - π² x³/36`. Assume
`|a| ≤ B0`, `|a'| ≤ B1`, `|a''| ≤ B2` everywhere, a lower bound `p ≤ |ψ'|` on `[α, β]` (this is
the nonvanishing hypothesis), and `|ψ''| ≤ M2` on `[α, β]`, `|ψ'''| ≤ M3`. Classes: proved. -/
theorem cubic_two_ibp {a : ℝ → ℂ} {a0 : ℝ} {α β B0 B1 B2 p M2 M3 : ℝ} (hαβ : α ≤ β)
    (ha : ContDiff ℝ 2 a) (hsupp : ∀ x, x ∉ Set.Icc α β → a x = 0)
    (hB0 : ∀ x, ‖a x‖ ≤ B0) (hB1 : ∀ x, ‖deriv a x‖ ≤ B1) (hB2 : ∀ x, ‖deriv (deriv a) x‖ ≤ B2)
    (hp : 0 < p) (hψ' : ∀ x ∈ Set.Icc α β, p ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|)
    (hM2 : ∀ x ∈ Set.Icc α β, |Real.pi ^ 2 * x / 6| ≤ M2) (hM3 : Real.pi ^ 2 / 6 ≤ M3) :
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      (β - α) * (B2 / p ^ 2 + 3 * B1 * M2 / p ^ 3 + B0 * M3 / p ^ 3 + 3 * B0 * M2 ^ 2 / p ^ 4) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hda : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdda : Continuous (deriv (deriv a)) := hda.continuous_deriv le_rfl
  have hint : IntegrableOn (deriv (deriv a)) (Set.Icc α β) := hdda.integrableOn_Icc
  have ha2 : ∀ x ∉ (∅ : Set ℝ), DifferentiableAt ℝ (deriv a) x := fun x _ =>
    hda.differentiable (by norm_num) x
  have hψ3 : ContDiff ℝ 3 (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) := by fun_prop
  have hne : ∀ x ∈ Set.Icc α β, deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x ≠ 0 := by
    intro x hx
    rw [mb_psi_deriv]
    intro h
    have hd := hψ' x hx
    rw [h, abs_zero] at hd
    linarith
  have hmain := two_ibp_phase_abs hαβ ha1 ∅ Set.countable_empty ha2 hint hsupp hψ3 hne
  refine hmain.trans ?_
  have hM2n : 0 ≤ M2 := le_trans (abs_nonneg _) (hM2 α ⟨le_rfl, hαβ⟩)
  have hB2n : 0 ≤ B2 := le_trans (norm_nonneg _) (hB2 α)
  have hB1n : 0 ≤ B1 := le_trans (norm_nonneg _) (hB1 α)
  have hB0n : 0 ≤ B0 := le_trans (norm_nonneg _) (hB0 α)
  have hpt : ∀ x ∈ Set.Icc α β,
      ‖deriv (deriv a) x‖ / deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3)) x| /
          |deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3))) x| /
          |deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3)) x ^ 2 /
          deriv (fun x : ℝ => a0 * x - Real.pi ^ 2 / 36 * x ^ 3) x ^ 4
        ≤ B2 / p ^ 2 + 3 * B1 * M2 / p ^ 3 + B0 * M3 / p ^ 3 + 3 * B0 * M2 ^ 2 / p ^ 4 := by
    intro x hx
    rw [mb_psi_deriv, mb_psi_deriv2, mb_psi_deriv3]
    have hd := hψ' x hx
    have hdsq : p ^ 2 ≤ (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 2 := by
      have h2 : p ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 2 := pow_le_pow_left₀ hp.le hd 2
      rwa [sq_abs] at h2
    have hab3 : p ^ 3 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 3 := pow_le_pow_left₀ hp.le hd 3
    have hab4 : p ^ 4 ≤ (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 4 := by
      have h4 : p ^ 4 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 4 := pow_le_pow_left₀ hp.le hd 4
      rwa [Even.pow_abs (⟨2, rfl⟩ : Even 4)] at h4
    have hpos2 : 0 < p ^ 2 := pow_pos hp 2
    have hpos3 : 0 < p ^ 3 := pow_pos hp 3
    have hpos4 : 0 < p ^ 4 := pow_pos hp 4
    have hM2x := hM2 x hx
    have hpsi2 : |-(Real.pi ^ 2 * x / 6)| ≤ M2 := by rw [abs_neg]; exact hM2x
    have t1 : ‖deriv (deriv a) x‖ / (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 2 ≤ B2 / p ^ 2 :=
      div_le_div₀ hB2n (hB2 x) hpos2 hdsq
    have t2 : 3 * ‖deriv a x‖ * |-(Real.pi ^ 2 * x / 6)| / |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 3
        ≤ 3 * B1 * M2 / p ^ 3 := by
      refine div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hB1n) hM2n) ?_ hpos3 hab3
      have := mul_le_mul (hB1 x) hpsi2 (abs_nonneg _) hB1n
      linarith
    have t3 : ‖a x‖ * |-(Real.pi ^ 2 / 6)| / |a0 - Real.pi ^ 2 * x ^ 2 / 12| ^ 3
        ≤ B0 * M3 / p ^ 3 := by
      refine div_le_div₀ (mul_nonneg hB0n (le_trans (by positivity) hM3)) ?_ hpos3 hab3
      have h6 : |-(Real.pi ^ 2 / 6)| = Real.pi ^ 2 / 6 := by
        rw [abs_neg, abs_of_nonneg (by positivity)]
      rw [h6]
      exact mul_le_mul (hB0 x) hM3 (by positivity) hB0n
    have t4 : 3 * ‖a x‖ * (-(Real.pi ^ 2 * x / 6)) ^ 2 / (a0 - Real.pi ^ 2 * x ^ 2 / 12) ^ 4
        ≤ 3 * B0 * M2 ^ 2 / p ^ 4 := by
      refine div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) hB0n) (sq_nonneg _)) ?_ hpos4 hab4
      have hsq : (-(Real.pi ^ 2 * x / 6)) ^ 2 ≤ M2 ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hM2x 2
        rw [sq_abs] at h
        rwa [neg_sq]
      have h1 : ‖a x‖ * (-(Real.pi ^ 2 * x / 6)) ^ 2 ≤ B0 * M2 ^ 2 :=
        mul_le_mul (hB0 x) hsq (by positivity) hB0n
      linarith
    linarith
  have hK : ∫ _ in Icc α β, (B2 / p ^ 2 + 3 * B1 * M2 / p ^ 3 + B0 * M3 / p ^ 3
      + 3 * B0 * M2 ^ 2 / p ^ 4) =
      (β - α) * (B2 / p ^ 2 + 3 * B1 * M2 / p ^ 3 + B0 * M3 / p ^ 3 + 3 * B0 * M2 ^ 2 / p ^ 4) := by
    rw [setIntegral_const, Real.volume_real_Icc_of_le hαβ, smul_eq_mul]
  rw [← hK]
  refine integral_mono_of_nonneg ?_ continuous_const.integrableOn_Icc ?_
  · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x _ => by
      beta_reduce
      positivity)
  · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun x hx => hpt x hx)

/-! `#print axioms` guards. -/

/-- info: 'FormalResearch.SignUncertainty.mbi_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbi_sign

/-- info: 'FormalResearch.SignUncertainty.mbi_abs_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbi_abs_pos

/-- info: 'FormalResearch.SignUncertainty.mbi_abs_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mbi_abs_neg

/-- info: 'FormalResearch.SignUncertainty.two_ibp_phase_abs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_ibp_phase_abs

/-- info: 'FormalResearch.SignUncertainty.cubic_two_ibp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_two_ibp


end FormalResearch.SignUncertainty

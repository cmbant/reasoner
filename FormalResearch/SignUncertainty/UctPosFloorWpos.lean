module

public import FormalResearch.SignUncertainty.UctPosFloorTail
public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.SignUncertainty.ConvSourceTune
public import FormalResearch.CohnElkies.MainOuterBound

/-!
# `uct:pos-floor` (3): pre-edge positivity and relative bounds of `W_pos` (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:pos-floor` (3), `(uct:Wpos-preedge)`.
`W_pos(w) = M_{ψ,c}(w) S̃_pos(i c_s w)` is `liftSymbol uctSpos δ₀ 4 w` (`M_{ψ,c}` is `liftMultiplier δ₀ 4`); the lift parameter `c` enters only
through the spline width `δ₀`, so the statement is uniform in `δ₀ > 0` (the paper's "for all `c ≥ 2` and all `δ₀ > 0`").

* `uct_pos_pre_edge_gen`: for every order `m ≥ 1`, `|W(w)| ≤ C_pos W(x)` on `Re w ≥ x/2` and the Cauchy variation bound (the order `m = 4` of the paper is the case
  used in `uct_pos_floor_pre_edge`; `C_pos = 2^m 2^{5/2} C_*/c₂` is independent of `δ₀`).
* `uct_pos_floor_pre_edge` (headline): positivity of `W_pos(x)` on `x ≥ 0` (real, `> 0`), the decay `|W_pos(w)| ≤ C (1 + Re w)^{-5/2}` on `Re w ≥ 0`, and
  `(uct:Wpos-preedge)`.  The ingredients are the floor `airyTwistedLaplace_uctSpos_floor` (`UctPosFloorTail`), the `U.2` decay of the seed (`HasU2.rhp`),
  `|E₁(ζ)| ≤ E₁(Re ζ)` and `E₁(σ/2) ≤ 2 E₁(σ)` for the B-spline kernel `E₁`, and the Cauchy estimate `local_variation_right`.

Class: proved.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-! ### The real B-spline kernel `E₁(σ) = ∫₀¹ e^{-σ s} ds` -/

/-- Real form of the B-spline kernel `E₁(σ) = (1 - e^{-σ}) / σ = ∫₀¹ e^{-σ s} ds`. -/
noncomputable def uctE1r (σ : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, Real.exp (-σ * s)

lemma uctE1r_cast (σ : ℝ) : bsplineE1 (σ : ℂ) = (uctE1r σ : ℂ) := by
  rw [bsplineE1_eq_integral, bsplineKernel, uctE1r, ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [pow_zero, one_mul]
  rw [Complex.ofReal_exp]; push_cast; rfl

lemma norm_bsplineE1_le_uctE1r (ζ : ℂ) : ‖bsplineE1 ζ‖ ≤ uctE1r ζ.re := by
  rw [bsplineE1_eq_integral, bsplineKernel, uctE1r]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s _ => ?_
  · exact (by fun_prop : Continuous fun s : ℝ => ‖(s : ℂ) ^ 0 * Complex.exp (-ζ * (s : ℂ))‖).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-ζ.re * s)).intervalIntegrable 0 1
  · simp [Complex.norm_exp, Complex.mul_re]

lemma uctE1r_anti {σ τ : ℝ} (h : σ ≤ τ) : uctE1r τ ≤ uctE1r σ := by
  unfold uctE1r
  refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ fun s hs => Real.exp_le_exp.mpr ?_
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-τ * s)).intervalIntegrable 0 1
  · exact (by fun_prop : Continuous fun s : ℝ => Real.exp (-σ * s)).intervalIntegrable 0 1
  · nlinarith only [mul_nonneg (sub_nonneg.mpr h) hs.1]

lemma uctE1r_pos (σ : ℝ) : 0 < uctE1r σ :=
  intervalIntegral.intervalIntegral_pos_of_pos ((by fun_prop : Continuous fun s : ℝ => Real.exp (-σ * s)).intervalIntegrable 0 1)
    (fun s => Real.exp_pos _) one_pos

lemma uctE1r_mul (σ : ℝ) : uctE1r σ * σ = 1 - Real.exp (-σ) := by
  have h := bsplineE1_mul_self_eq (σ : ℂ)
  rw [uctE1r_cast] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

lemma uctE1r_half {σ : ℝ} (hσ : 0 < σ) : uctE1r (σ / 2) ≤ 2 * uctE1r σ := by
  have h1 := uctE1r_mul (σ / 2)
  have h2 := uctE1r_mul σ
  have h3 : Real.exp (-σ) ≤ Real.exp (-(σ / 2)) := Real.exp_le_exp.mpr (by linarith)
  have h4 : uctE1r (σ / 2) * (σ / 2) ≤ (2 * uctE1r σ) * (σ / 2) := by linarith
  exact le_of_mul_le_mul_right h4 (by positivity)

/-! ### The multiplier `M_ψ` -/

lemma norm_liftMultiplier_le_pow (δ₀ : ℝ) (m : ℕ) (w : ℂ) :
    ‖liftMultiplier δ₀ m w‖ ≤ uctE1r (ceCs * δ₀ / m * w.re) ^ m := by
  unfold liftMultiplier
  rw [norm_pow]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ m
  have := norm_bsplineE1_le_uctE1r (((ceCs * δ₀ / m : ℝ) : ℂ) * w)
  simpa [Complex.re_ofReal_mul] using this

/-- On the real axis, `W_pos(x) = E₁(c_s δ₀ x / m)^m · S̃_pos(i c_s x)` is a real number. -/
lemma liftSymbol_uctSpos_ofReal (δ₀ : ℝ) (m : ℕ) (x : ℝ) :
    liftSymbol uctSpos δ₀ m (x : ℂ) =
      (((uctE1r (ceCs * δ₀ / m * x)) ^ m * airyTwistedLaplace uctSpos (ceCs * x) : ℝ) : ℂ) := by
  unfold liftSymbol liftMultiplier
  have h1 : (((ceCs * δ₀ / m : ℝ) : ℂ) * (x : ℂ)) = ((ceCs * δ₀ / m * x : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, uctE1r_cast, airyTwistedLaplaceC_ofReal]; push_cast; ring

lemma hasU2_uctSpos : HasU2 uctSpos := hasU2_airySeedU2 (-1 / 4) 1 1

/-! ### Relative bounds -/

/-- Relative bound `|W_pos(w)| ≤ C_pos W_pos(x)` on `Re w ≥ x/2` and the local variation bound, for each spline order `m ≥ 1`, with
`C_pos` independent of the width `δ₀ > 0`. -/
theorem uct_pos_pre_edge_gen {m : ℕ} (hm : 0 < m) : ∃ Cpos : ℝ, 0 < Cpos ∧ ∀ δ₀ : ℝ, 0 < δ₀ → ∀ x : ℝ, 0 < x →
    (∀ w : ℂ, x / 2 ≤ w.re → ‖liftSymbol uctSpos δ₀ m w‖ ≤ Cpos * (liftSymbol uctSpos δ₀ m (x : ℂ)).re) ∧
      ∀ y : ℝ, |y| ≤ x / 4 → ‖liftSymbol uctSpos δ₀ m ((x : ℂ) + (y : ℂ) * Complex.I) - liftSymbol uctSpos δ₀ m (x : ℂ)‖ ≤
        4 * Cpos * (|y| / x) * (liftSymbol uctSpos δ₀ m (x : ℂ)).re := by
  obtain ⟨Cs, hCs, hrhp⟩ := hasU2_uctSpos.rhp
  obtain ⟨c2, hc2, hfl⟩ := airyTwistedLaplace_uctSpos_floor
  have hcs := ceCs_pos
  refine ⟨2 ^ m * (2 ^ (5 / 2 : ℝ) * Cs / c2), by positivity, fun δ₀ hδ x hx => ?_⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℝ := ceCs * δ₀ / m with ha
  have ha0 : 0 < a := by positivity
  have hWre : (liftSymbol uctSpos δ₀ m (x : ℂ)).re = uctE1r (a * x) ^ m * airyTwistedLaplace uctSpos (ceCs * x) := by
    rw [liftSymbol_uctSpos_ofReal, Complex.ofReal_re]
  have hfx := hfl x hx.le
  have hmain : ∀ w : ℂ, x / 2 ≤ w.re → ‖liftSymbol uctSpos δ₀ m w‖ ≤
      (2 ^ m * (2 ^ (5 / 2 : ℝ) * Cs / c2)) * (liftSymbol uctSpos δ₀ m (x : ℂ)).re := by
    intro w hw
    have hw0 : 0 ≤ w.re := by linarith
    -- the multiplier
    have hM : ‖liftMultiplier δ₀ m w‖ ≤ 2 ^ m * uctE1r (a * x) ^ m := by
      refine (norm_liftMultiplier_le_pow δ₀ m w).trans ?_
      have h1 : uctE1r (a * w.re) ≤ uctE1r (a * x / 2) := uctE1r_anti (by nlinarith only [ha0, hw])
      have h2 : uctE1r (a * x / 2) ≤ 2 * uctE1r (a * x) := uctE1r_half (by positivity)
      calc uctE1r (ceCs * δ₀ / m * w.re) ^ m ≤ (2 * uctE1r (a * x)) ^ m :=
            pow_le_pow_left₀ (uctE1r_pos _).le (h1.trans h2) m
        _ = _ := by rw [mul_pow]
    -- the seed transform
    have hS : ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖ ≤ 2 ^ (5 / 2 : ℝ) * Cs / c2 * airyTwistedLaplace uctSpos (ceCs * x) := by
      have h1 := hrhp w hw0
      have h2 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (1 + x / 2) ^ (-(5 / 2 : ℝ)) := by
        have : 1 + x / 2 ≤ ‖1 + w‖ := by
          have := Complex.re_le_norm (1 + w)
          simp only [Complex.add_re, Complex.one_re] at this
          linarith
        exact Real.rpow_le_rpow_of_nonpos (by linarith) this (by norm_num)
      have h3 : (1 + x / 2) ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
        have h4 : (1 + x / 2) ^ (-(5 / 2 : ℝ)) ≤ (2⁻¹ * (1 + x)) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        have h6 : ((2 : ℝ)⁻¹) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [Real.mul_rpow (by norm_num) (by linarith), h6] at h4
        exact h4
      have h5 : (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace uctSpos (ceCs * x) / c2 := by
        rw [le_div_iff₀ hc2]; linarith
      calc ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖ ≤ Cs * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := h1
        _ ≤ Cs * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (h2.trans h3) hCs.le
        _ ≤ Cs * (2 ^ (5 / 2 : ℝ) * (airyTwistedLaplace uctSpos (ceCs * x) / c2)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 (by positivity)) hCs.le
        _ = _ := by ring
    have hlw : ‖liftSymbol uctSpos δ₀ m w‖ = ‖liftMultiplier δ₀ m w‖ * ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖ := by
      unfold liftSymbol; rw [norm_mul]
    rw [hlw, hWre]
    calc ‖liftMultiplier δ₀ m w‖ * ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖
        ≤ (2 ^ m * uctE1r (a * x) ^ m) * (2 ^ (5 / 2 : ℝ) * Cs / c2 * airyTwistedLaplace uctSpos (ceCs * x)) :=
          mul_le_mul hM hS (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (uctE1r_pos _).le _))
      _ = _ := by ring
  refine ⟨hmain, fun y hy => ?_⟩
  have hv := local_variation_right (liftSymbol_differentiableOn hasU2_uctSpos δ₀ m) hx
    (B := (2 ^ m * (2 ^ (5 / 2 : ℝ) * Cs / c2)) * (liftSymbol uctSpos δ₀ m (x : ℂ)).re)
    (fun w hw _ => hmain w hw) y hy
  calc _ ≤ _ := hv
    _ = _ := by field_simp

/-- **`uct:pos-floor` (3)** (pre-edge positivity and relative bounds).  With `W_pos = liftSymbol uctSpos δ₀ 4` (`W_pos(w) = M_{ψ,c}(w) S̃_pos(i c_s w)`,
`m = 4`), for every spline width `δ₀ > 0` (so for every `c`): `W_pos(x) > 0` for real `x ≥ 0`; `|W_pos(w)| ≤ C (1 + Re w)^{-5/2}` on `Re w ≥ 0`; and with `C_pos`
independent of `δ₀`, `|W_pos(w)| ≤ C_pos W_pos(x)` on `Re w ≥ x/2` and `|W_pos(x+iy) - W_pos(x)| ≤ 4 C_pos (|y|/x) W_pos(x)` for `|y| ≤ x/4`, `x > 0`
(`(uct:Wpos-preedge)`).  Positivity is stated as `0 < Re W_pos(x)` and `Im W_pos(x) = 0` (`W_pos(x)` is a positive real number).  No hypotheses. -/
theorem uct_pos_floor_pre_edge : ∃ C : ℝ, 0 < C ∧ ∃ Cpos : ℝ, 0 < Cpos ∧ ∀ δ₀ : ℝ, 0 < δ₀ →
    (∀ x : ℝ, 0 ≤ x → 0 < (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re ∧ (liftSymbol uctSpos δ₀ 4 (x : ℂ)).im = 0) ∧
      (∀ w : ℂ, 0 ≤ w.re → ‖liftSymbol uctSpos δ₀ 4 w‖ ≤ C * (1 + w.re) ^ (-(5 / 2 : ℝ))) ∧
      ∀ x : ℝ, 0 < x →
        (∀ w : ℂ, x / 2 ≤ w.re → ‖liftSymbol uctSpos δ₀ 4 w‖ ≤ Cpos * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re) ∧
          ∀ y : ℝ, |y| ≤ x / 4 → ‖liftSymbol uctSpos δ₀ 4 ((x : ℂ) + (y : ℂ) * Complex.I) - liftSymbol uctSpos δ₀ 4 (x : ℂ)‖ ≤
            4 * Cpos * (|y| / x) * (liftSymbol uctSpos δ₀ 4 (x : ℂ)).re := by
  obtain ⟨Cs, hCs, hrhp⟩ := hasU2_uctSpos.rhp
  obtain ⟨Cpos, hCpos, hgen⟩ := uct_pos_pre_edge_gen (m := 4) (by norm_num)
  refine ⟨Cs, hCs, Cpos, hCpos, fun δ₀ hδ => ⟨fun x hx => ⟨?_, liftSymbol_im_eq_zero_of_real _ _ _ _⟩, fun w hw => ?_, fun x hx => hgen δ₀ hδ x hx⟩⟩
  · rw [liftSymbol_uctSpos_ofReal, Complex.ofReal_re]
    exact mul_pos (pow_pos (uctE1r_pos _) _) (airyTwistedLaplace_uctSpos_pos _ (mul_nonneg ceCs_pos.le hx))
  · have h1 : ‖liftSymbol uctSpos δ₀ 4 w‖ = ‖liftMultiplier δ₀ 4 w‖ * ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖ := by
      unfold liftSymbol; rw [norm_mul]
    have h2 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (1 + w.re) ^ (-(5 / 2 : ℝ)) := by
      have : 1 + w.re ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simpa using this
      exact Real.rpow_le_rpow_of_nonpos (by linarith) this (by norm_num)
    rw [h1]
    calc ‖liftMultiplier δ₀ 4 w‖ * ‖airyTwistedLaplaceC uctSpos ((ceCs : ℂ) * w)‖
        ≤ 1 * (Cs * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (norm_liftMultiplier_le_one hδ.le 4 hw) (hrhp w hw) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (Cs * (1 + w.re) ^ (-(5 / 2 : ℝ))) := by gcongr
      _ = _ := one_mul _

/-- info: 'FormalResearch.SignUncertainty.uct_pos_pre_edge_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_pre_edge_gen

/-- info: 'FormalResearch.SignUncertainty.uct_pos_floor_pre_edge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uct_pos_floor_pre_edge

end FormalResearch.SignUncertainty

module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFarField
public import FormalResearch.SignUncertainty.CtBoasBlocks
public import FormalResearch.SignUncertainty.CtPhaseFar
public import FormalResearch.SignUncertainty.CtOuterPart3Plus

/-!
# `ct:boas-ineq`: the far-tail phase of the concrete band phase `X = Ξ - θ_ε ∘ τ₀`

`constant_terms_lower.tex`, proof of `ct:boas` Step 1: for `Δ > ½ c log c`,
`Ξ(L) - θ_ε(τ₀(L)) = 2πΔ - πc/4 + (3+ε)π/4 + O(Δe^{-2π²Δ/c} + (1+τ₀²)e^{-πτ₀})`, from `ct:phase-far-lem`
(`ct_phase_far_Delta`) and `ct:outer`(3) (`ct_outer_part3`).

* `boasX c ε L = c Φ_Ph(τ₀(L); L) - θ_ε(τ₀(L))`, `Φ_Ph = edgePhi`, `τ₀ = 0` for `L ≤ 0` (so `X` is defined on all of `ℝ`);
* `boas_far_phase`: the hypothesis `hphase` of `boas_far_field` for `X = boasX c ε`, with the explicit
  `E_ph = boasPhaseEps c C_θ = K(D/2)e^{-π² log c} + C_θ(1 + τ₁²)e^{-πτ₁}`, `τ₁ = π log c - 1`
  (`K = phaseFarK`; this is `O(c^{1-π²} log c + (log c)² c^{-π²}) = O(c^{-8.8} log c)`);
* `boas_far_field_hankel`: `far` for the concrete `X`, with `E_ph` from `ct:outer`(3).

**Proved**, unconditional (`c > 1`, `log c ≥ 2`).
-/

@[expose] public section

open MeasureTheory Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies
open FormalResearch.SignUncertainty.CtPhaseFar

/-- The band phase `X(L) = c Φ_Ph(τ₀(L); L) - θ_ε(τ₀(L))` (`ct:boas-ineq`); `τ₀ = 0` for `L ≤ 0`. -/
noncomputable def boasX (c ε L : ℝ) : ℝ :=
  c * edgePhi L (tau0 L) - CtOuter.outerTheta ε (tau0 L)

/-- `E_ph = K(D/2)e^{-2π²(D/2)/c} + C_θ(1 + τ₁²)e^{-πτ₁}`, `τ₁ = π log c - 1`, `K = phaseFarK`, `D = c log c`. -/
noncomputable def boasPhaseEps (c Cθ : ℝ) : ℝ :=
  phaseFarK * (farD c / 2) * Real.exp (-(2 * π ^ 2 * (farD c / 2) / c)) +
    Cθ * ((1 + (π * Real.log c - 1) ^ 2) * Real.exp (-π * (π * Real.log c - 1)))

/-- `t e^{-at}` is nonincreasing on `t ≥ 1/a`. -/
lemma mul_exp_neg_antitone {a s t : ℝ} (ha : 0 < a) (hs : 1 / a ≤ s) (hst : s ≤ t) :
    t * Real.exp (-(a * t)) ≤ s * Real.exp (-(a * s)) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have has : 1 ≤ a * s := by rwa [div_le_iff₀ ha, mul_comm] at hs
  have h1 : 1 + a * (t - s) ≤ Real.exp (a * (t - s)) := by linarith [Real.add_one_le_exp (a * (t - s))]
  have h2 : t ≤ s * Real.exp (a * (t - s)) := by nlinarith [mul_le_mul_of_nonneg_left h1 hs0.le]
  calc t * Real.exp (-(a * t)) ≤ (s * Real.exp (a * (t - s))) * Real.exp (-(a * t)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = s * Real.exp (-(a * s)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `(1 + t²)e^{-πt}` is nonincreasing. -/
lemma sq_exp_antitone {s t : ℝ} (hst : s ≤ t) :
    (1 + t ^ 2) * Real.exp (-π * t) ≤ (1 + s ^ 2) * Real.exp (-π * s) := by
  obtain ⟨u, hu0, rfl⟩ : ∃ u, 0 ≤ u ∧ t = s + u := ⟨t - s, by linarith, by ring⟩
  have hπ3 : 3 < π := Real.pi_gt_three
  have hq := Real.quadratic_le_exp_of_nonneg (mul_nonneg Real.pi_pos.le hu0)
  have e1 : (π * u) ^ 2 / 2 - u ^ 2 = u ^ 2 * (π ^ 2 / 2 - 1) := by ring
  have h1 : 1 + u + u ^ 2 ≤ Real.exp (π * u) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ π - 1) hu0,
      mul_nonneg (sq_nonneg u) (by nlinarith : 0 ≤ π ^ 2 / 2 - 1)]
  have h2 : 1 + (s + u) ^ 2 ≤ (1 + s ^ 2) * (1 + u + u ^ 2) := by
    nlinarith [mul_nonneg hu0 (sq_nonneg (s - 1)), mul_nonneg (sq_nonneg s) (sq_nonneg u)]
  calc (1 + (s + u) ^ 2) * Real.exp (-π * (s + u))
      ≤ ((1 + s ^ 2) * Real.exp (π * u)) * Real.exp (-π * (s + u)) :=
        mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity)))
          (Real.exp_pos _).le
    _ = (1 + s ^ 2) * Real.exp (-π * s) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-- `K x e^{-2π²x} ≤ 1` for `x ≥ 1`, `K = phaseFarK`. -/
lemma phaseFarK_mul_le_one {x : ℝ} (hx : 1 ≤ x) : phaseFarK * x * Real.exp (-(2 * π ^ 2 * x)) ≤ 1 := by
  have hπ3 : 3 < π := Real.pi_gt_three
  have hπ4 : π < 3.15 := Real.pi_lt_d2
  have h1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : x * Real.exp (-(2 * π ^ 2 * x)) ≤ Real.exp (-15 + (-2)) := by
    calc x * Real.exp (-(2 * π ^ 2 * x)) ≤ Real.exp x * Real.exp (-(2 * π ^ 2 * x)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = Real.exp (x - 2 * π ^ 2 * x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-15 + (-2)) := by
          apply Real.exp_le_exp.2
          have hπ2 : 9 < π ^ 2 := by nlinarith
          nlinarith [mul_nonneg (sub_nonneg.2 hx) (by linarith : 0 ≤ 2 * π ^ 2 - 1)]
  have h3 : (16 * π) * Real.exp 2 * Real.exp (-17) ≤ 1 := by
    have e15 : (72 : ℝ) ≤ Real.exp 15 := by
      have h := Real.add_one_le_exp (7.5 : ℝ)
      have : Real.exp 15 = Real.exp 7.5 * Real.exp 7.5 := by rw [← Real.exp_add]; norm_num
      rw [this]; nlinarith
    have : Real.exp 2 * Real.exp (-17) = (Real.exp 15)⁻¹ := by
      rw [← Real.exp_add, ← Real.exp_neg]; norm_num
    rw [mul_assoc, this, ← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith
  unfold phaseFarK
  calc 16 * π * Real.exp 2 * x * Real.exp (-(2 * π ^ 2 * x))
      = (16 * π) * Real.exp 2 * (x * Real.exp (-(2 * π ^ 2 * x))) := by ring
    _ ≤ (16 * π) * Real.exp 2 * Real.exp (-15 + (-2)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (16 * π) * Real.exp 2 * Real.exp (-17) := by norm_num
    _ ≤ 1 := h3

/-- **The far-tail phase** (`ct:boas` Step 1, `ct:phase-far-lem` and `ct:outer`(3)): if `θ_ε(τ) = -(3+ε)π/4 + O((1+τ²)e^{-πτ})`
for `τ ≥ 1` with constant `C_θ` (`hCθ`, from `ct_outer_part3`), `c > 1`, `log c ≥ 2`, then for every `L` with
`Δ(L) = c e^L/π² > ½ c log c`,
`|X(L) - (2πΔ - πc/4 + (3+ε)π/4)| ≤ E_ph` (`boasPhaseEps c C_θ`), `X = boasX c ε`. -/
theorem boas_far_phase {c ε Cθ : ℝ} (hc : 1 < c) (hlogc : 2 ≤ Real.log c)
    (hCθ : ∀ τ : ℝ, 1 ≤ τ → |CtOuter.outerTheta ε τ + (3 + ε) * π / 4| ≤
      Cθ * ((1 + τ ^ 2) * Real.exp (-π * τ))) :
    ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) →
      |boasX c ε L - (2 * π * (c * (Real.exp L / π ^ 2)) - π * c / 4 + (3 + ε) * π / 4)| ≤
        boasPhaseEps c Cθ := by
  intro L hL
  have hc0 : 0 < c := by linarith
  have hpi : (0 : ℝ) < π ^ 2 := by positivity
  have hπ3 : 3 < π := Real.pi_gt_three
  set Δ : ℝ := c * (Real.exp L / π ^ 2) with hΔ
  set x : ℝ := Δ / c with hx
  have hxe : x = Real.exp L / π ^ 2 := by rw [hx, hΔ]; field_simp
  have hD : farD c = c * Real.log c := rfl
  -- `x ≥ log c / 2 ≥ 1`
  have hx2 : Real.log c / 2 < x := by
    have : c * (Real.log c / 2) < c * x := by rw [hx]; field_simp; rw [hD] at hL; linarith
    exact lt_of_mul_lt_mul_left this hc0.le
  have hx1 : 1 ≤ x := by linarith
  have hexpL : Real.exp L = π ^ 2 * x := by rw [hxe]; field_simp
  have hLpos : 0 < L := by
    by_contra h
    have h1 := Real.exp_le_one_iff.2 (not_lt.1 h)
    nlinarith
  have hlogL : Real.log (π ^ 2 * (Δ / c)) = L := by rw [← hx, ← hexpL, Real.log_exp]
  have hτ0 := tau0_pos hLpos
  have hm : hankelEdgeM (tau0 L) = Real.log (π ^ 2 * (Δ / c)) := by
    rw [hlogL]; exact hankelEdgeM_tau0 hLpos
  have hΔc : c ≤ Δ := by
    have : c * 1 ≤ c * x := mul_le_mul_of_nonneg_left hx1 hc0.le
    rw [hΔ, hxe] at *; linarith
  obtain ⟨h1, h2⟩ := ct_phase_far_Delta hc0 hΔc hτ0 hm
  rw [hlogL] at h2
  have e1 : 2 * π * Δ / c = 2 * π * x := by rw [hx]; ring
  have e2 : 2 * π ^ 2 * Δ / c = 2 * π ^ 2 * x := by rw [hx]; ring
  rw [e1, ← hx, e2] at h1
  have hK1 := phaseFarK_mul_le_one hx1
  -- `τ₀ ≥ π log c - 1 ≥ 1`
  have hτ1 : π * Real.log c - 1 ≤ tau0 L := by
    have := (abs_le.1 h1).1
    nlinarith [Real.pi_pos]
  have hτ1' : 1 ≤ π * Real.log c - 1 := by nlinarith
  have hτ01 : 1 ≤ tau0 L := hτ1'.trans hτ1
  have hCθ0 : 0 ≤ Cθ := by
    have h0 := (abs_nonneg _).trans (hCθ 1 le_rfl)
    have : 0 < (1 + (1 : ℝ) ^ 2) * Real.exp (-π * 1) := by positivity
    exact (mul_nonneg_iff_of_pos_right this).1 h0
  have hθ := hCθ (tau0 L) hτ01
  have hθ' : Cθ * ((1 + tau0 L ^ 2) * Real.exp (-π * tau0 L)) ≤
      Cθ * ((1 + (π * Real.log c - 1) ^ 2) * Real.exp (-π * (π * Real.log c - 1))) :=
    mul_le_mul_of_nonneg_left (sq_exp_antitone hτ1) hCθ0
  -- the exponential term of the phase
  have hlow : 1 / (2 * π ^ 2 / c) ≤ farD c / 2 := by
    have : 1 / (2 * π ^ 2 / c) = c / (2 * π ^ 2) := by field_simp
    rw [this, div_le_iff₀ (by positivity), hD]
    have h5 : 1 ≤ Real.log c * π ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h5 hc0.le]
  have hanti := mul_exp_neg_antitone (a := 2 * π ^ 2 / c) (by positivity) hlow hL.le
  have e3 : ∀ t : ℝ, 2 * π ^ 2 / c * t = 2 * π ^ 2 * t / c := fun t => by ring
  simp only [e3] at hanti
  have hK2 : phaseFarK * Δ * Real.exp (-(2 * π ^ 2 * Δ / c)) ≤
      phaseFarK * (farD c / 2) * Real.exp (-(2 * π ^ 2 * (farD c / 2) / c)) := by
    have hKpos : 0 ≤ phaseFarK := by unfold phaseFarK; positivity
    calc phaseFarK * Δ * Real.exp (-(2 * π ^ 2 * Δ / c)) = phaseFarK * (Δ * Real.exp (-(2 * π ^ 2 * Δ / c))) := by ring
      _ ≤ phaseFarK * ((farD c / 2) * Real.exp (-(2 * π ^ 2 * (farD c / 2) / c))) :=
          mul_le_mul_of_nonneg_left hanti hKpos
      _ = _ := by ring
  have hdecomp : boasX c ε L - (2 * π * Δ - π * c / 4 + (3 + ε) * π / 4) =
      (c * edgePhi L (tau0 L) - (2 * π * Δ - π * c / 4)) -
        (CtOuter.outerTheta ε (tau0 L) + (3 + ε) * π / 4) := by
    unfold boasX; ring
  rw [hdecomp]
  calc |(c * edgePhi L (tau0 L) - (2 * π * Δ - π * c / 4)) -
        (CtOuter.outerTheta ε (tau0 L) + (3 + ε) * π / 4)|
      ≤ |c * edgePhi L (tau0 L) - (2 * π * Δ - π * c / 4)| +
        |CtOuter.outerTheta ε (tau0 L) + (3 + ε) * π / 4| := abs_sub _ _
    _ ≤ boasPhaseEps c Cθ := by unfold boasPhaseEps; linarith

/-- **`far` for the concrete band phase** (`boas_far_field` with `X = boasX c ε` and `E_ph = boasPhaseEps c C_θ`):
`C_θ` is the constant of `ct:outer`(3) for `θ_ε(τ) = -(3+ε)π/4 + O((1+τ²)e^{-πτ})`.  Hypotheses as in `boas_far_field`
except `hphase`, which `boas_far_phase` supplies (`c > 1`, `log c ≥ 2`). -/
theorem boas_far_field_hankel {c ε T Cθ : ℝ} (hc : 1 < c) (hlogc : 2 ≤ Real.log c) (hε : ε = -1 ∨ ε = 1)
    (hCθ : ∀ τ : ℝ, 1 ≤ τ → |CtOuter.outerTheta ε τ + (3 + ε) * π / 4| ≤
      Cθ * ((1 + τ ^ 2) * Real.exp (-π * τ)))
    {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) (hM : hankelMass c f = 1) (hT : T ≤ farD c / 2)
    {wt sf : ℝ → ℝ} {Lmin : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hwm : Measurable wt) (hsfm : Measurable sf) (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1)
    (hsf : ∀ L, sf L = sFar c (c * (Real.exp L / π ^ 2)))
    (hwt1 : ∀ L, farD c / 2 < c * (Real.exp L / π ^ 2) → wt L = 1)
    (hLmin : c * (Real.exp Lmin / π ^ 2) ≤ farD c / 2) (hXm : Measurable (boasX c ε)) :
    -boasFarEps c n (boasPhaseEps c Cθ) ≤
      ∫ L in Ici Lmin, wt L * sf L * (hankelHL c f L * boasKernel (boasX c ε) L) := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hEph : 0 ≤ boasPhaseEps c Cθ := by
    have hCθ0 : 0 ≤ Cθ := by
      have h0 := (abs_nonneg _).trans (hCθ 1 le_rfl)
      have : 0 < (1 + (1 : ℝ) ^ 2) * Real.exp (-π * 1) := by positivity
      exact (mul_nonneg_iff_of_pos_right this).1 h0
    have hD : 0 ≤ farD c := (farD_pos hc).le
    unfold boasPhaseEps phaseFarK
    positivity
  exact boas_far_field hc hε2 hf hM hT hn hXm hwm hsfm hw hsf hwt1 hLmin hEph (boas_far_phase hc hlogc hCθ)

/-- **`ct:outer`(3), unified form** `θ_ε(τ) = -(3+ε)π/4 + O((1+τ²)e^{-πτ})` for `ε = ±1`, `τ ≥ 1` (the form consumed
by `boas_far_phase`), from `ct_outer_part3`. -/
theorem ct_outer_theta_asymp : ∃ Cθ : ℝ, ∀ ε : ℝ, (ε = -1 ∨ ε = 1) → ∀ τ : ℝ, 1 ≤ τ →
    |CtOuter.outerTheta ε τ + (3 + ε) * π / 4| ≤ Cθ * ((1 + τ ^ 2) * Real.exp (-π * τ)) := by
  obtain ⟨⟨C, hC⟩, _⟩ := CtOuter.ct_outer_part3
  refine ⟨C, fun ε hε τ hτ => ?_⟩
  obtain ⟨h1, h2⟩ := hC τ hτ
  rcases hε with rfl | rfl
  · have : (3 + (-1 : ℝ)) * π / 4 = π / 2 := by ring
    rw [this]; exact h1
  · have : (3 + (1 : ℝ)) * π / 4 = π := by ring
    rw [this]; exact h2

/-- info: 'FormalResearch.SignUncertainty.ct_outer_theta_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_theta_asymp

/-- info: 'FormalResearch.SignUncertainty.boas_far_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_far_phase

/-- info: 'FormalResearch.SignUncertainty.boas_far_field_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_far_field_hankel

end FormalResearch.SignUncertainty

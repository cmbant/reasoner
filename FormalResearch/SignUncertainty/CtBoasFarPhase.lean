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

open MeasureTheory Set Filter Topology Finset
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

/-- `c^k e^{-αc} ≤ 1` for large `c`. -/
lemma eventually_rpow_mul_exp_le (k α : ℝ) (hα : 0 < α) :
    ∀ᶠ c : ℝ in atTop, c ^ k * Real.exp (-(α * c)) ≤ 1 := by
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero k α hα
  have := h.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [this] with c hc
  have : -α * c = -(α * c) := by ring
  rw [this] at hc
  exact hc.le

/-- `log c ≤ c^δ` for large `c`. -/
lemma eventually_log_le_rpow (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ c : ℝ in atTop, Real.log c ≤ c ^ δ := by
  have h2 : 0 < δ / 2 := by linarith
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((2 / δ) ^ (2 / δ))] with c hc1 hc2
  have hc0 : 0 < c := by linarith
  have h1 := Real.log_le_rpow_div hc0.le h2
  have h3 : 2 / δ ≤ c ^ (δ / 2) := by
    have := Real.rpow_le_rpow (by positivity) hc2 (by positivity : (0 : ℝ) ≤ δ / 2)
    rwa [← Real.rpow_mul (by positivity), show 2 / δ * (δ / 2) = 1 by field_simp, Real.rpow_one] at this
  have h4 : c ^ δ = c ^ (δ / 2) * c ^ (δ / 2) := by
    rw [← Real.rpow_add hc0]; ring_nf
  have h5 : c ^ (δ / 2) / (δ / 2) ≤ c ^ δ := by
    rw [div_le_iff₀ h2, h4]
    have h0 : 0 ≤ c ^ (δ / 2) := by positivity
    have h6 : 1 ≤ c ^ (δ / 2) * (δ / 2) := by
      have := mul_le_mul_of_nonneg_right h3 h2.le
      rwa [show 2 / δ * (δ / 2) = 1 by field_simp] at this
    nlinarith [mul_le_mul_of_nonneg_left h6 h0]
  linarith

/-- `exp(-(log c)^2) ≤ c^{-k}` once `log c ≥ k`. -/
lemma exp_neg_log_sq_le {c k : ℝ} (hc : 1 < c) (hk : k ≤ Real.log c) :
    Real.exp (-(Real.log c) ^ 2) ≤ c ^ (-k) := by
  have hc0 : 0 < c := by linarith
  rw [Real.rpow_def_of_pos hc0]
  apply Real.exp_le_exp.2
  have := Real.log_pos hc
  nlinarith

lemma exp_neg_four_log_sq_le {c k : ℝ} (hc : 1 < c) (hk : k ≤ Real.log c) :
    Real.exp (-(4 * Real.log c ^ 2)) ≤ c ^ (-k) := by
  have hc0 : 0 < c := by linarith
  rw [Real.rpow_def_of_pos hc0]
  apply Real.exp_le_exp.2
  have := Real.log_pos hc
  nlinarith

lemma farE2_le {c : ℝ} (hc : 1 < c) (hk : 2 ≤ Real.log c) : farE2 c ≤ 2 * c ^ (-(2 : ℝ)) := by
  unfold farE2
  have h := exp_neg_four_log_sq_le hc hk
  have : √2 ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have h0 := Real.exp_pos (-(4 * Real.log c ^ 2))
  nlinarith

/-- `E_ph = O(c^{-2})`. -/
lemma eventually_phaseEps_le (Cθ : ℝ) : ∀ᶠ c : ℝ in atTop, boasPhaseEps c Cθ ≤ c ^ (-(2 : ℝ)) := by
  have hK := (by unfold phaseFarK; positivity : 0 ≤ phaseFarK)
  have h5 := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 5)).eventually_ge_atTop (phaseFarK + 605 * |Cθ|)
  filter_upwards [eventually_ge_atTop (Real.exp 6), h5] with c hc h5
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (6 : ℝ)]) hc
  have hc0 : 0 < c := by linarith
  have hs1 : 1 ≤ Real.log c := by
    have := Real.log_le_log (Real.exp_pos 6) hc
    rw [Real.log_exp] at this; linarith
  set s := Real.log c with hs
  have hπ9 : 9 < π ^ 2 := by nlinarith [Real.pi_gt_three]
  have hπ10 : π ^ 2 < 10 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hexp : Real.exp (-(π ^ 2 * s)) ≤ c ^ (-(9 : ℝ)) := by
    rw [Real.rpow_def_of_pos hc0]
    apply Real.exp_le_exp.2
    rw [← hs]; nlinarith
  have hc9 : 0 < c ^ (-(9 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hsc : s ≤ c := by have := Real.log_le_sub_one_of_pos hc0; linarith
  unfold boasPhaseEps
  have hD : farD c / 2 = c * s / 2 := by unfold farD; ring
  have hex1 : 2 * π ^ 2 * (farD c / 2) / c = π ^ 2 * s := by rw [hD]; field_simp
  rw [hex1]
  have hT1 : phaseFarK * (farD c / 2) * Real.exp (-(π ^ 2 * s)) ≤ phaseFarK * s * c ^ (-(8 : ℝ)) := by
    have e8 : c * c ^ (-(9 : ℝ)) = c ^ (-(8 : ℝ)) := by
      rw [← Real.rpow_one_add' hc0.le (by norm_num)]; norm_num
    rw [hD]
    calc phaseFarK * (c * s / 2) * Real.exp (-(π ^ 2 * s)) ≤ phaseFarK * (c * s / 2) * c ^ (-(9 : ℝ)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ phaseFarK * s * (c * c ^ (-(9 : ℝ))) := by nlinarith [mul_nonneg (mul_nonneg hK (by linarith : (0 : ℝ) ≤ s)) (mul_nonneg hc0.le hc9.le)]
      _ = _ := by rw [e8]
  have hT2 : Cθ * ((1 + (π * s - 1) ^ 2) * Real.exp (-π * (π * s - 1))) ≤ 605 * |Cθ| * s ^ 2 * c ^ (-(9 : ℝ)) := by
    have he : Real.exp (-π * (π * s - 1)) = Real.exp (-(π ^ 2 * s)) * Real.exp π := by
      rw [← Real.exp_add]; congr 1; ring
    have hexpπ : Real.exp π ≤ 55 := by
      have h1 : Real.exp π ≤ Real.exp 4 := Real.exp_le_exp.2 (by linarith [Real.pi_lt_d2])
      have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
      have h3 := Real.exp_one_lt_d9
      have h4 : Real.exp 1 ^ 4 ≤ (2.7182818286 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le h3.le 4
      nlinarith
    have hq : 1 + (π * s - 1) ^ 2 ≤ 11 * s ^ 2 := by
      have h1 : (π * s - 1) ^ 2 ≤ π ^ 2 * s ^ 2 := by nlinarith [Real.pi_gt_three, hs1]
      have h2 : π ^ 2 * s ^ 2 ≤ 10 * s ^ 2 := by nlinarith [sq_nonneg s]
      nlinarith [sq_nonneg s]
    have hq0 : 0 ≤ 1 + (π * s - 1) ^ 2 := by positivity
    calc Cθ * ((1 + (π * s - 1) ^ 2) * Real.exp (-π * (π * s - 1))) ≤ |Cθ| * ((11 * s ^ 2) * (c ^ (-(9 : ℝ)) * 55)) := by
          refine (le_abs_self _).trans ?_
          rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 + (π * s - 1) ^ 2) * Real.exp (-π * (π * s - 1)))]
          refine mul_le_mul_of_nonneg_left (mul_le_mul hq ?_ (Real.exp_pos _).le (by positivity)) (abs_nonneg _)
          rw [he]
          exact mul_le_mul hexp hexpπ (Real.exp_pos _).le hc9.le
      _ = 605 * |Cθ| * s ^ 2 * c ^ (-(9 : ℝ)) := by ring
  have e7 : c * c ^ (-(8 : ℝ)) = c ^ (-(7 : ℝ)) := by
    rw [← Real.rpow_one_add' hc0.le (by norm_num)]; norm_num
  have e7' : c ^ 2 * c ^ (-(9 : ℝ)) = c ^ (-(7 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hc0]; norm_num
  have e52 : c ^ (5 : ℝ) * c ^ (-(7 : ℝ)) = c ^ (-(2 : ℝ)) := by
    rw [← Real.rpow_add hc0]; norm_num
  have h8 : 0 < c ^ (-(8 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have h7 : 0 < c ^ (-(7 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hs2 : s ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by linarith) hsc 2
  have a1 : phaseFarK * s * c ^ (-(8 : ℝ)) ≤ phaseFarK * c ^ (-(7 : ℝ)) := by
    rw [← e7]
    nlinarith [mul_le_mul_of_nonneg_left hsc (mul_nonneg hK h8.le)]
  have a2 : 605 * |Cθ| * s ^ 2 * c ^ (-(9 : ℝ)) ≤ 605 * |Cθ| * c ^ (-(7 : ℝ)) := by
    rw [← e7']
    have : 0 ≤ 605 * |Cθ| * c ^ (-(9 : ℝ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hs2 this]
  have h5' : (phaseFarK + 605 * |Cθ|) * c ^ (-(7 : ℝ)) ≤ c ^ (-(2 : ℝ)) := by
    rw [← e52]; exact mul_le_mul_of_nonneg_right h5 h7.le
  nlinarith

/-- **The `far` error is `O(c^{-2})`** (`ct:boas` Step 1, the choice `n = ⌈c²⌉`): `boasFarEps c ⌈c²⌉ (E_ph) ≤ 60 c^{-2}`. -/
lemma eventually_farEps_le (Cθ : ℝ) :
    ∀ᶠ c : ℝ in atTop, boasFarEps c ⌈c ^ 2⌉₊ (boasPhaseEps c Cθ) ≤ 60 * c ^ (-(2 : ℝ)) := by
  filter_upwards [eventually_ge_atTop (Real.exp 6), eventually_phaseEps_le Cθ,
    eventually_rpow_mul_exp_le 6 (1 / 4) (by norm_num)] with c hc hph hE
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.add_one_le_exp (6 : ℝ)]) hc
  have hc0 : 0 < c := by linarith
  have hc4 : 4 ≤ c := by linarith [Real.add_one_le_exp (6 : ℝ)]
  have hs6 : 6 ≤ Real.log c := by
    have := Real.log_le_log (Real.exp_pos 6) hc
    rwa [Real.log_exp] at this
  set s := Real.log c with hs
  have hsc : s ≤ c := by have := Real.log_le_sub_one_of_pos hc0; linarith
  set n := ⌈c ^ 2⌉₊ with hn
  have hn1 : c ^ 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hn2 : (n : ℝ) ≤ 2 * c ^ 2 := by
    have := Nat.ceil_lt_add_one (by positivity : 0 ≤ c ^ 2)
    nlinarith
  have hn0 : 0 < (n : ℝ) := lt_of_lt_of_le (by positivity) hn1
  have hcm2 : c ^ (-(2 : ℝ)) = (c ^ 2)⁻¹ := by
    rw [Real.rpow_neg hc0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hcm2' : 0 < c ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos hc0 _
  have hmon : ∀ a b : ℝ, a ≤ b → c ^ a ≤ c ^ b := fun a b hab => Real.rpow_le_rpow_of_exponent_le hc1.le hab
  have E1 : farE1 c ≤ 2 * c ^ (-(6 : ℝ)) := by
    unfold farE1
    have h := exp_neg_log_sq_le hc1 hs6
    have : √2 ≤ 2 := by
      rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have h0 := Real.exp_pos (-(Real.log c) ^ 2)
    nlinarith
  have E2 := farE2_le hc1 (by linarith)
  have hc6 : c ^ (-(6 : ℝ)) ≤ c ^ (-(2 : ℝ)) := hmon _ _ (by norm_num)
  have hc6' : c ^ 2 * c ^ (-(6 : ℝ)) ≤ c ^ (-(2 : ℝ)) := by
    have : c ^ 2 * c ^ (-(6 : ℝ)) = c ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hc0]; norm_num
    rw [this]; exact hmon _ _ (by norm_num)
  have hE1pos : 0 ≤ farE1 c := by unfold farE1; positivity
  have A1 : (n : ℝ) * (2 * farE1 c) ≤ 8 * c ^ (-(2 : ℝ)) := by
    have : (n : ℝ) * (2 * farE1 c) ≤ (2 * c ^ 2) * (2 * (2 * c ^ (-(6 : ℝ)))) :=
      mul_le_mul hn2 (by linarith) (by positivity) (by positivity)
    nlinarith
  have A2 : 2 / (n : ℝ) ≤ 2 * c ^ (-(2 : ℝ)) := by
    rw [hcm2, div_le_iff₀ hn0]
    have h1 : 2 * (c ^ 2)⁻¹ * c ^ 2 ≤ 2 * (c ^ 2)⁻¹ * (n : ℝ) := mul_le_mul_of_nonneg_left hn1 (by positivity)
    have h2 : 2 * (c ^ 2)⁻¹ * c ^ 2 = 2 := by field_simp
    linarith only [h1, h2]
  have hW1 : 1 ≤ farW c := by unfold farW; linarith
  have hWd : farW c = c / 4 := rfl
  have hterm : ∀ k ∈ Finset.Ico 2 n, ((k : ℝ) ^ (-c) +
      2 * farD c * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
          √(2 * π / (2 * π ^ 2 * farW c ^ 2))))) ≤ 5 * c ^ 2 * Real.exp (-(c / 4)) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.1 hk).1
    have hk0 : (0 : ℝ) < k := by linarith
    have hex4 : 0 < Real.exp (-(c / 4)) := Real.exp_pos _
    have a1 : (k : ℝ) ^ (-c) ≤ Real.exp (-(c / 4)) := by
      have h1 : (k : ℝ) ^ (-c) ≤ (2 : ℝ) ^ (-c) := Real.rpow_le_rpow_of_nonpos (by norm_num) hk2 (by linarith)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have := Real.log_two_gt_d9
      nlinarith
    have a2 : (3 * (k : ℝ) / 4) ^ (-c) ≤ Real.exp (-(c / 4)) := by
      have h1 : (3 * (k : ℝ) / 4) ^ (-c) ≤ (3 / 2 : ℝ) ^ (-c) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at h1
      refine h1.trans (Real.exp_le_exp.2 ?_)
      have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
      norm_num at this
      nlinarith
    have hWp : 0 < farW c := by linarith
    have s1 : √(π / (2 * π ^ 2 * farW c ^ 2)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three, mul_le_mul hW1 hW1 zero_le_one hWp.le]
    have s2 : √(2 * π / (2 * π ^ 2 * farW c ^ 2)) ≤ 1 := by
      rw [Real.sqrt_le_one]
      rw [div_le_one (by positivity)]
      nlinarith [Real.pi_gt_three, mul_le_mul hW1 hW1 zero_le_one hWp.le]
    have a3 : Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) ≤ Real.exp (-(c / 4)) := by
      apply Real.exp_le_exp.2
      have hk4 : (1 / 2 : ℝ) ≤ (k : ℝ) / 4 := by linarith only [hk2]
      have hk4' : (1 / 4 : ℝ) ≤ ((k : ℝ) / 4) ^ 2 := by nlinarith only [hk4]
      have hW2 : farW c ≤ farW c ^ 2 := by nlinarith only [hW1]
      have hπ2 : 4 ≤ π ^ 2 := by nlinarith only [Real.pi_gt_three]
      have h4 : π ^ 2 * farW c ^ 2 * (1 / 4) ≤ π ^ 2 * farW c ^ 2 * ((k : ℝ) / 4) ^ 2 :=
        mul_le_mul_of_nonneg_left hk4' (by positivity)
      have h3 : farW c ^ 2 ≤ π ^ 2 * farW c ^ 2 * (1 / 4) := by nlinarith only [sq_nonneg (farW c), hπ2]
      have h5 : c / 4 = farW c := rfl
      have e : -(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2 = -(π ^ 2 * farW c ^ 2 * ((k : ℝ) / 4) ^ 2) := by ring
      rw [e]
      linarith only [h4, h3, hW2, h5]
    have hD : farD c ≤ c * c := by
      unfold farD; exact mul_le_mul_of_nonneg_left hsc hc0.le
    have hD0 : 0 ≤ farD c := by unfold farD; positivity
    have b1 : (3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) ≤ Real.exp (-(c / 4)) * 1 :=
      mul_le_mul a2 s1 (Real.sqrt_nonneg _) hex4.le
    have b2 : 1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) * √(2 * π / (2 * π ^ 2 * farW c ^ 2)) ≤
        1 * Real.exp (-(c / 4)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left a3 zero_le_one) s2 (Real.sqrt_nonneg _) (by positivity)
    have hsum : (3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) * √(2 * π / (2 * π ^ 2 * farW c ^ 2)) ≤
        2 * Real.exp (-(c / 4)) := by linarith
    have hc2 : (1 : ℝ) ≤ c ^ 2 := by nlinarith only [hc1]
    have hfin : 1 + 4 * farD c ≤ 5 * c ^ 2 := by nlinarith only [hD, hc2]
    refine (add_le_add a1 (mul_le_mul_of_nonneg_left hsum (by positivity))).trans ?_
    have e : Real.exp (-(c / 4)) + 2 * farD c * (2 * Real.exp (-(c / 4))) =
        (1 + 4 * farD c) * Real.exp (-(c / 4)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hfin hex4.le
  have A3 : 2 * ∑ k ∈ Finset.Ico 2 n, ((k : ℝ) ^ (-c) +
      2 * farD c * (((3 * (k : ℝ) / 4) ^ (-c) * √(π / (2 * π ^ 2 * farW c ^ 2)) +
        1 * Real.exp (-(2 * π ^ 2 * farW c ^ 2) * ((k : ℝ) / 4) ^ 2 / 2) *
          √(2 * π / (2 * π ^ 2 * farW c ^ 2))))) ≤ 20 * c ^ (-(2 : ℝ)) := by
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [nsmul_eq_mul, Nat.card_Ico] at hsum
    have hcard : ((n - 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n 2
    have hex0 : 0 < 5 * c ^ 2 * Real.exp (-(c / 4)) := by positivity
    have h1 : (((n - 2 : ℕ) : ℝ)) * (5 * c ^ 2 * Real.exp (-(c / 4))) ≤ (2 * c ^ 2) * (5 * c ^ 2 * Real.exp (-(c / 4))) :=
      mul_le_mul_of_nonneg_right (hcard.trans hn2) hex0.le
    have hE' : c ^ 6 * Real.exp (-(c / 4)) ≤ 1 := by
      have := hE
      rwa [show (1 / 4 : ℝ) * c = c / 4 by ring, show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    have h2 : c ^ 4 * Real.exp (-(c / 4)) ≤ c ^ (-(2 : ℝ)) := by
      have e : c ^ 4 * Real.exp (-(c / 4)) = c ^ (-(2 : ℝ)) * (c ^ 6 * Real.exp (-(c / 4))) := by
        rw [hcm2]; field_simp
      rw [e]
      calc c ^ (-(2 : ℝ)) * (c ^ 6 * Real.exp (-(c / 4))) ≤ c ^ (-(2 : ℝ)) * 1 :=
            mul_le_mul_of_nonneg_left hE' hcm2'.le
        _ = _ := mul_one _
    have e2 : (2 * c ^ 2) * (5 * c ^ 2 * Real.exp (-(c / 4))) = 10 * (c ^ 4 * Real.exp (-(c / 4))) := by ring
    linarith only [hsum, h1, h2, e2]
  unfold boasFarEps
  linarith only [A1, A2, A3, E1, E2, hph, hc6, hE1pos]

/-- info: 'FormalResearch.SignUncertainty.ct_outer_theta_asymp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_theta_asymp

/-- info: 'FormalResearch.SignUncertainty.boas_far_phase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_far_phase

/-- info: 'FormalResearch.SignUncertainty.boas_far_field_hankel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_far_field_hankel

/-- info: 'FormalResearch.SignUncertainty.eventually_farEps_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms eventually_farEps_le

end FormalResearch.SignUncertainty

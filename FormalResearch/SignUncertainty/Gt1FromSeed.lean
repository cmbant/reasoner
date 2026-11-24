module

public import FormalResearch.SignUncertainty.MiddleBandTransfer
public import FormalResearch.CohnElkies.AirySymbolTransfer

/-!
# `GT.1` from the seed: `Gt1Bounds` for the weighted Airy symbol

For an abstract real-axis seed `AiryTailSymbolSeed x₀ χ S M` and a spline parameter `δ₀ ∈ [0, 2]`, the weighted symbol
`W = airyWeightedSymbol δ₀ m seed.F` satisfies `Gt1Bounds (C * (S + M)) W` with a constant `C > 0` depending only on `m`, `x₀` and
the cutoff `χ` (`gt1Bounds_of_seed`).  The proof takes the high-frequency bounds `gt1_high_freq` (orders `0, …, 3`) and the
low-frequency bounds `gt1_low_freq`, sums their five constants, and reads the derivative chain of `W` off its `C³` regularity on
`Ioi 0` and `Iio 0` (`gt1_deriv_chain`).  The assembly into `Gt1Bounds` is `gt1Bounds_of_bounds`.

Non-vacuity: `gt1Bounds_zero_symbol` (the zero seed symbol is zero, so it satisfies `Gt1Bounds 0`) and `gt1Bounds_seed_witness`
(the class of seeds of `airyTailSymbolSeed_nonvacuous` is inhabited, and its symbols satisfy the bound with `S = M = 0`).

Status: proved.  No extra hypothesis is needed: `0 ≤ S` and `0 ≤ M` follow from the seed fields.  Not formalised here: the
that the three basis seeds `f₁, g₁, g₁'` are `AiryTailSymbolSeed`s (`Gt1BasisInput m` of `Gt1Interface.lean`); the identification of `liftW` with
`airyWeightedSymbol` is `Gt1Identify.lean` and the composition `Gt1LiftSeed.lean`.
-/

@[expose] public section

open Set

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Derivative chain of a `C³` function on an open set `U`, at a point `s ∈ U`: `∂W`, `∂²W`, `∂³W` are the derivatives that
`Gt1Bounds` uses. -/
theorem gt1_deriv_chain {W : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (hW : ContDiffOn ℝ (3 : ℕ) W U) {s : ℝ} (hs : s ∈ U) :
    HasDerivAt W (deriv W s) s ∧ HasDerivAt (deriv W) (deriv (deriv W) s) s ∧
      HasDerivAt (deriv (deriv W)) (deriv (deriv (deriv W)) s) s := by
  have h2 : ContDiffOn ℝ (2 : ℕ) (deriv W) U := hW.deriv_of_isOpen hU (by norm_num)
  have h1 : ContDiffOn ℝ (1 : ℕ) (deriv (deriv W)) U := h2.deriv_of_isOpen hU (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact ((hW.contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  · exact ((h2.contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt
  · exact ((h1.contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)).hasDerivAt

/-- Assembly of `Gt1Bounds` from its pieces, stated with the exponents produced by `gt1_low_freq` and `gt1_high_freq`. -/
theorem gt1Bounds_of_bounds {W : ℝ → ℂ} {A : ℝ} (hsm : ContDiffOn ℝ (3 : ℕ) W (Ioi 0) ∧ ContDiffOn ℝ (3 : ℕ) W (Iio 0))
    (hl : ∀ j : ℕ, 1 ≤ j → j ≤ 3 → ∀ v : ℝ, v ≠ 0 → |v| ≤ 1 → ‖iteratedDeriv j W v‖ ≤ A * |v| ^ ((1 / 2 : ℝ) - (j : ℝ)))
    (hh : ∀ j : ℕ, j ≤ 3 → ∀ v : ℝ, 1 ≤ |v| → ‖iteratedDeriv j W v‖ ≤ A * |v| ^ (-(5 / 2 : ℝ) - (j : ℝ)))
    (h0 : ‖W 0‖ ≤ A) (hH : ∀ v : ℝ, 0 < |v| → |v| ≤ 1 → ‖W v - W 0‖ ≤ A * |v| ^ (1 / 2 : ℝ)) : Gt1Bounds A W := by
  have i1 : iteratedDeriv 1 W = deriv W := iteratedDeriv_one
  have i2 : iteratedDeriv 2 W = deriv (deriv W) := by rw [iteratedDeriv_succ, i1]
  have i3 : iteratedDeriv 3 W = deriv (deriv (deriv W)) := by rw [iteratedDeriv_succ, i2]
  have i0 : iteratedDeriv 0 W = W := iteratedDeriv_zero
  refine ⟨deriv W, deriv (deriv W), deriv (deriv (deriv W)), ?_, ?_, ?_, h0, hH⟩
  · intro s hs
    rcases lt_or_gt_of_ne hs with h | h
    · exact gt1_deriv_chain isOpen_Iio hsm.2 (mem_Iio.mpr h)
    · exact gt1_deriv_chain isOpen_Ioi hsm.1 (mem_Ioi.mpr h)
  · intro s hs0 hs1
    have hs : s ≠ 0 := abs_pos.mp hs0
    have a1 := hl 1 (by norm_num) (by norm_num) s hs hs1
    have a2 := hl 2 (by norm_num) (by norm_num) s hs hs1
    have a3 := hl 3 (by norm_num) (by norm_num) s hs hs1
    rw [i1] at a1
    rw [i2] at a2
    rw [i3] at a3
    have e1 : (1 / 2 : ℝ) - ((1 : ℕ) : ℝ) = -(1 / 2 : ℝ) := by norm_num
    have e2 : (1 / 2 : ℝ) - ((2 : ℕ) : ℝ) = -(3 / 2 : ℝ) := by norm_num
    have e3 : (1 / 2 : ℝ) - ((3 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
    rw [e1] at a1
    rw [e2] at a2
    rw [e3] at a3
    exact ⟨a1, a2, a3⟩
  · intro s hs1
    have b0 := hh 0 (by norm_num) s hs1
    have b1 := hh 1 (by norm_num) s hs1
    have b2 := hh 2 (by norm_num) s hs1
    have b3 := hh 3 (by norm_num) s hs1
    rw [i0] at b0
    rw [i1] at b1
    rw [i2] at b2
    rw [i3] at b3
    have f0 : -(5 / 2 : ℝ) - ((0 : ℕ) : ℝ) = -(5 / 2 : ℝ) := by norm_num
    have f1 : -(5 / 2 : ℝ) - ((1 : ℕ) : ℝ) = -(7 / 2 : ℝ) := by norm_num
    have f2 : -(5 / 2 : ℝ) - ((2 : ℕ) : ℝ) = -(9 / 2 : ℝ) := by norm_num
    have f3 : -(5 / 2 : ℝ) - ((3 : ℕ) : ℝ) = -(11 / 2 : ℝ) := by norm_num
    rw [f0] at b0
    rw [f1] at b1
    rw [f2] at b2
    rw [f3] at b3
    exact ⟨b0, b1, b2, b3⟩

/-- **`GT.1` from the seed.**  There is a constant `C > 0`, depending only on `m`, `x₀` and `χ`, such that for every seed and every
`δ₀ ∈ [0, 2]` the weighted Airy symbol satisfies `Gt1Bounds (C * (S + M))`. -/
theorem gt1Bounds_of_seed (m : ℕ) (hm : 3 ≤ m) {x₀ : ℝ} (hx₀ : 1 ≤ x₀) (χ : AiryCutoff) :
    ∃ C : ℝ, 0 < C ∧ ∀ {S M δ₀ : ℝ} (seed : AiryTailSymbolSeed x₀ χ S M), δ₀ ∈ Set.Icc (0 : ℝ) 2 →
      Gt1Bounds (C * (S + M)) (airyWeightedSymbol δ₀ m seed.F) := by
  obtain ⟨C0, hC0, hhi0⟩ := gt1_high_freq m 0 hm (by norm_num) hx₀ χ
  obtain ⟨C1, hC1, hhi1⟩ := gt1_high_freq m 1 hm (by norm_num) hx₀ χ
  obtain ⟨C2, hC2, hhi2⟩ := gt1_high_freq m 2 hm (by norm_num) hx₀ χ
  obtain ⟨C3, hC3, hhi3⟩ := gt1_high_freq m 3 hm (by norm_num) hx₀ χ
  obtain ⟨Cl, hCl, hlo⟩ := gt1_low_freq m hm hx₀ χ
  refine ⟨C0 + C1 + C2 + C3 + Cl, by positivity, fun {S M δ₀} seed hδ => ?_⟩
  -- `0 ≤ S` from the order-0 Schwartz bound at `u = 0`; `0 ≤ M` from the order-0 symbol bound at `x₀ + 1`
  have hS : 0 ≤ S := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (seed.schwartz_bd 0 (by norm_num) 0)
  have hM : 0 ≤ M :=
    le_trans (mul_nonneg (Real.rpow_nonneg (by linarith) _) (norm_nonneg _)) (seed.sym_bd 0 (by norm_num) (x₀ + 1) (by linarith)).1
  have hSM : 0 ≤ S + M := add_nonneg hS hM
  have hC0' : C0 ≤ C0 + C1 + C2 + C3 + Cl := by linarith
  have hC1' : C1 ≤ C0 + C1 + C2 + C3 + Cl := by linarith
  have hC2' : C2 ≤ C0 + C1 + C2 + C3 + Cl := by linarith
  have hC3' : C3 ≤ C0 + C1 + C2 + C3 + Cl := by linarith
  have hCl' : Cl ≤ C0 + C1 + C2 + C3 + Cl := by linarith
  have key : ∀ B : ℝ, B ≤ C0 + C1 + C2 + C3 + Cl → ∀ (e v : ℝ),
      B * (S + M) * |v| ^ e ≤ (C0 + C1 + C2 + C3 + Cl) * (S + M) * |v| ^ e := fun B hB e v =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hSM) (Real.rpow_nonneg (abs_nonneg v) e)
  obtain ⟨hcl_sm, hcl_w0, hcl_h, hcl_j⟩ := hlo seed hδ
  have hb0 := (hhi0 seed hδ).2.2
  have hb1 := (hhi1 seed hδ).2.2
  have hb2 := (hhi2 seed hδ).2.2
  have hb3 := (hhi3 seed hδ).2.2
  refine gt1Bounds_of_bounds ⟨(hcl_j 3 (by norm_num) (by norm_num)).1, (hcl_j 3 (by norm_num) (by norm_num)).2.1⟩
    (fun j hj1 hj3 v hv hv1 => le_trans ((hcl_j j hj1 hj3).2.2 v hv hv1) (key Cl hCl' _ _))
    (fun j hj3 v hv1 => ?_) (le_trans hcl_w0 (mul_le_mul_of_nonneg_right hCl' hSM))
    (fun v _ hv1 => le_trans (hcl_h v hv1) (key Cl hCl' _ _))
  interval_cases j
  · exact le_trans (hb0 v hv1) (key C0 hC0' _ _)
  · exact le_trans (hb1 v hv1) (key C1 hC1' _ _)
  · exact le_trans (hb2 v hv1) (key C2 hC2' _ _)
  · exact le_trans (hb3 v hv1) (key C3 hC3' _ _)

/-- Non-vacuity: the zero seed symbol is the zero function, which satisfies `Gt1Bounds 0`. -/
theorem gt1Bounds_zero_symbol (m : ℕ) (δ₀ : ℝ) : Gt1Bounds 0 (airyWeightedSymbol δ₀ m (fun _ => 0)) := by
  have h : airyWeightedSymbol δ₀ m (fun _ => 0) = fun _ => 0 := by
    funext v
    simp [airyWeightedSymbol, FormalResearch.Special.airyFtilde, FormalResearch.Special.airyFhat]
  rw [h]
  exact gt1Bounds_zero le_rfl

/-- Non-vacuity of the seed class: some seed of `airyTailSymbolSeed_nonvacuous` (with `S = M = 0`) gives `Gt1Bounds` for its symbol,
for every `δ₀ ∈ [0, 2]`. -/
theorem gt1Bounds_seed_witness (m : ℕ) (hm : 3 ≤ m) {δ₀ : ℝ} (hδ : δ₀ ∈ Set.Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ seed : AiryTailSymbolSeed 1 AiryCutoff.standard 0 0,
      Gt1Bounds (C * (0 + 0)) (airyWeightedSymbol δ₀ m seed.F) := by
  obtain ⟨C, hC, h⟩ := gt1Bounds_of_seed m hm (le_refl (1 : ℝ)) AiryCutoff.standard
  obtain ⟨w⟩ := airyTailSymbolSeed_nonvacuous
  exact ⟨C, hC, w, h w hδ⟩

/-- info: 'FormalResearch.SignUncertainty.gt1_deriv_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1_deriv_chain
/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_of_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_of_bounds
/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_of_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_of_seed
/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_zero_symbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_zero_symbol
/-- info: 'FormalResearch.SignUncertainty.gt1Bounds_seed_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms gt1Bounds_seed_witness

end FormalResearch.SignUncertainty

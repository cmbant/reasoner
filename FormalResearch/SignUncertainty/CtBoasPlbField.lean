module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasFrozen
public import FormalResearch.SignUncertainty.CtBoasTent

/-!
# `ct:boas-ineq`: the field `P_lb` of `BoasInputs` for the concrete Hankel setting

`constant_terms_lower.tex`, proof of `ct:boas` Steps 3-4, `ct:P-lb`.  The assembly `boas_ineq_assembled` consumes, for every
block `j` and every `L₀` with `Ω_near χ_j(L₀) > 0`, the frozen-kernel window bound
`-Pb ≤ ∫ G_{W_j}(L - L₀) h(L) T_{L₀}(L) dL` with `T_{L₀}(L) = 1 - 2 sin(X(L₀) + ν(L₀)(L - L₀))`.  Here

* `h = hankelHL c f` (the log-density of `dm`), `ν = cτ₀` (`boasNu`), `X` arbitrary (the bound does not see `X`);
* `χ_j = tent (tentNode a) j`, block centre `L_j = x_{j+1}`, `W_j = N_j/(cτ_j)`, `N_j² = 10⁶(1 + L_j) log c`,
  `τ_j = τ₀(L_j)` (`boasW`);
* `hankel_frozen_P_lb` (`CtBoasFrozen`) with `φ = π/2 + X(L₀) - ν(L₀)L₀` (the identity `1 - 2 sin s = 1 + 2 cos(s + π/2)`),
  the Harnack ratio `τ_j/3 ≤ τ₀(L₀) ≤ 3τ_j` of `tentBlock_tau0_ratio`, and the block position `L₀ ∈ (x_j, x_{j+2})`.

`Pb` is any uniform bound of the explicit `hankelFrozenPb` over the blocks (`hPb`); that `Pb ≤ C c^{-4}√(log c)` is the
numerical bookkeeping of `ct:P-lb` and is not done here.  **Proved**; the hypotheses are the regime inequalities of
`hankel_frozen_P_lb`, `c^{-1/3} ≤ a`, `x_{J+1} ≤ log c`, `L_T ≤ a` and the explicit `Pb` bound.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtBoasWindow FormalResearch.CohnElkies

/-- The frequency `ν(L) = cτ₀(L)` of the frozen kernel (`ct:P-lb`, `ω₀ = cτ₀(L₀)`); `τ₀ = 0` for `L ≤ 0`, so this is
the extension of `cτ₀` by `0` to all of `ℝ`. -/
noncomputable def boasNu (c : ℝ) (L : ℝ) : ℝ := c * tau0 L

/-- The Gaussian width `W_j = N_j/(c τ₀(L_j))`, `N_j² = 10⁶(1 + L_j) log c`, `L_j = x_{j+1}` the centre of block `j` of
the node grid `x = tentNode a` (`ct:boas` Step 3, `C_N = 10⁶`). -/
noncomputable def boasW (c a : ℝ) (j : ℕ) : ℝ :=
  √(1000000 * (1 + tentNode a (j + 1)) * Real.log c) / (c * tau0 (tentNode a (j + 1)))

/-- `1 - 2 sin(X(L₀) + ν(L₀)(L - L₀)) = 1 + 2 cos(ν(L₀) L + φ)`, `φ = π/2 + X(L₀) - ν(L₀) L₀`. -/
lemma boasFrozenKernel_eq_cos (X ν : ℝ → ℝ) (L0 L : ℝ) :
    boasFrozenKernel X ν L0 L = 1 + 2 * Real.cos (ν L0 * L + (π / 2 + X L0 - ν L0 * L0)) := by
  unfold boasFrozenKernel
  have : ν L0 * L + (π / 2 + X L0 - ν L0 * L0) = (X L0 + ν L0 * (L - L0)) + π / 2 := by ring
  rw [this, Real.cos_add_pi_div_two]; ring

/-- **`P_lb` for the concrete Hankel setting** (`ct:P-lb`, the field `P_lb` of `BoasInputs` for `h = hankelHL c f`,
`ν = boasNu c`, `W = boasW c a`, `χ = tent (tentNode a)`).  For every block `j < J` and every `L₀` with
`ω_j(L₀) = w̃(L₀)(1 - 𝔰_far(L₀))χ_j(L₀) > 0`, `-Pb ≤ ∫ G_{W_j}(L - L₀) h(L) T_{L₀}(L) dL`, where `Pb` bounds the explicit
`hankelFrozenPb` (`hPb`).  The conclusion does not depend on `X`, `wt`, `sf`. -/
theorem boas_P_lb_field {c ε T : ℝ} (hc3 : 3 ≤ c)
    (hF1 : 156000000000 * Real.log c ^ 2 ≤ (c ^ (1 / 3 : ℝ)) ^ 3)
    (hF2 : 8320 * Real.log c ≤ c ^ (1 / 3 : ℝ))
    {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) (hε : ε = 1 ∨ ε = -1)
    {a LT : ℝ} (ha : 0 < a) (hlo : c ^ (-(1 / 3) : ℝ) ≤ a) {J : ℕ}
    (hhi : tentNode a (J + 1) ≤ Real.log c)
    (hLT : ∀ L, LT ≤ L → T ≤ c * (Real.exp L / π ^ 2)) (hLTa : LT ≤ a) {n : ℕ} (hn : 2 ≤ n) {Pb : ℝ}
    (hPb : ∀ j < J, ∀ L0 ∈ Icc (tentNode a (j + 1) - tentDelta a j) (tentNode a (j + 1) + tentDelta a j),
      hankelFrozenPb c (hankelMass c f) (boasW c a j) LT L0 n ≤ Pb)
    (X wt sf : ℝ → ℝ) :
    ∀ j < J, ∀ L0, 0 < wt L0 * (1 - sf L0) * tent (tentNode a) j L0 →
      -Pb ≤ ∫ L, gaussK (boasW c a j) (L - L0) * hankelHL c f L * boasFrozenKernel X (boasNu c) L0 L := by
  intro j hj L0 hpos
  have hχ : tent (tentNode a) j L0 ≠ 0 := fun h0 => by rw [h0] at hpos; simp at hpos
  have hx := tentNode_strictMono ha
  have hsupp := tentNode_block_support ha j L0 hχ
  -- position of `L₀` in the node grid
  have hLj0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hδ := tentDelta_pos ha j
  have hL0a : a < L0 := by
    have h1 : tentNode a j < L0 := by
      by_contra h; exact hχ (tent_of_le hx (not_lt.1 h))
    have h2 : a ≤ tentNode a j := by
      have := hx.monotone (Nat.zero_le j); simpa [tentNode] using this
    linarith
  have hL0b : L0 ≤ Real.log c := by
    have h1 : L0 < tentNode a (j + 2) := by
      by_contra h; exact hχ (tent_of_ge hx (not_lt.1 h))
    have h2 : tentNode a (j + 2) ≤ tentNode a (J + 1) := hx.monotone (by omega)
    linarith
  have hL0 : 0 < L0 := by linarith
  have hδ36 : tentDelta a j ≤ 1 / 36 := by
    unfold tentDelta; have := min_le_right (tentNode a (j + 1)) 1; linarith
  have hδ' : tentDelta a j ≤ min (tentNode a (j + 1)) 1 / 36 := le_refl _
  -- Harnack ratio
  have hLjQ : tentNode a (j + 1) ∈ Icc (tentNode a (j + 1) - 3 * tentDelta a j) (tentNode a (j + 1) + 3 * tentDelta a j) :=
    ⟨by linarith, by linarith⟩
  have hL0Q : L0 ∈ Icc (tentNode a (j + 1) - 3 * tentDelta a j) (tentNode a (j + 1) + 3 * tentDelta a j) :=
    ⟨by linarith [hsupp.1], by linarith [hsupp.2]⟩
  obtain ⟨_, _, hr1, hr2⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl hL0Q hLjQ
  have hm : hankelEdgeM (tau0 L0) = L0 := hankelEdgeM_tau0 hL0
  have hc0 : 0 < c := by linarith
  have hlogc : 0 < Real.log c := Real.log_pos (by linarith)
  have hle : (1 : ℝ) ≤ 1 := le_rfl
  have hP := hankel_frozen_P_lb hc3 hF1 hF2 hf hε (τ0 := tau0 L0) (τj := tau0 (tentNode a (j + 1)))
    (Lj := tentNode a (j + 1)) (tau0_pos hL0) hr1 hr2 hLj0.le
    (by rw [hm]; linarith [hsupp.2]) (by rw [hm]; linarith [hsupp.1]) (by rw [hm]; linarith) (by rw [hm]; exact hL0b)
    hn (π / 2 + X L0 - boasNu c L0 * L0) (Np2 := 1000000 * (1 + tentNode a (j + 1)) * Real.log c)
    (W := boasW c a j) rfl rfl (LT := LT) hLT (by rw [hm]; linarith)
  rw [hm] at hP
  have hPb' := hPb j hj L0 hsupp
  have hint : ∫ L, gaussK (boasW c a j) (L - L0) * hankelHL c f L * boasFrozenKernel X (boasNu c) L0 L =
      ∫ x, gaussK (boasW c a j) (x - L0) * hankelHL c f x *
        (1 + 2 * Real.cos (c * tau0 L0 * x + (π / 2 + X L0 - boasNu c L0 * L0))) := by
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    simp only []
    rw [boasFrozenKernel_eq_cos]
    rfl
  rw [hint]
  linarith

/-- info: 'FormalResearch.SignUncertainty.boas_P_lb_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_P_lb_field

end FormalResearch.SignUncertainty

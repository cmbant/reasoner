module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasPhaseBlock
public import FormalResearch.SignUncertainty.CtBoasTent
public import FormalResearch.SignUncertainty.CtOuterPart3Plus

/-!
# `ct:boas-ineq`: the field `freeze` of `BoasInputs` for the concrete Hankel setting (Step 5)

`constant_terms_lower.tex`, proof of `ct:boas` Step 5, "Estimate of `D_j` on the whole line": for the block weight
`ω_j = Ω_near χ_j` (`Ω_near = w̃(1 - 𝔰_far)`), `K = 1 - 2 sin X`, `T_{L₀}(L) = 1 - 2 sin(X(L₀) + ν(L₀)(L - L₀))`,

`|ω_j(L) K(L) - ω_j(L₀) T_{L₀}(L)| ≤ 1_{Q_j}(L)(A_j|L - L₀| + B_j(L - L₀)²) + K_{d,j}(L - L₀)²`  for all `L, L₀ ∈ ℝ`,

with `A_j = 3M_j' + 2S_jC_l`, `B_j = 2S_jC_q` and `K_{d,j} = 6/δ_j²` (a Chebyshev tail for the far pairs `|L - L₀| > δ_j`).

* `boas_freeze_block`: the abstract block statement.  Inputs: the support `χ_j ⊂ [L_j - δ_j, L_j + δ_j]`, `Q_j ⊇ [L_j - 3δ_j, L_j + 3δ_j]`,
  `ω_j ∈ [0,1]`, the Lipschitz bound `|ω_j(L) - ω_j(L')| ≤ M_j'|L - L'|` on `Q_j` (`ct:Bj-pointwise` (c), (d), `ct:taper-harnack`),
  `ω_j ≤ S_j` on `Q_j`, and the frozen-phase bound `|X(L₀) + ν(L₀)(L - L₀) - X(L)| ≤ C_l|L - L₀| + C_q(L - L₀)²` on `Q_j`;
* `boas_freeze_field`: for `X = boasX c ε`, `ν = boasNu c`, the tent partition and `Q_j = tentQ`, with the phase bound supplied by
  `boas_phase_block` (`ct:outer`(3) for `|θ_ε'| ≤ C_θ(1+|t|)^{-2}` and the Harnack ratio `tentBlock_tau0_ratio`); the remaining
  inputs are the Lipschitz bound and the supremum of `ω_j`, both consequences of `ct:taper-harnack` and `ct:sigma-prime`.

**Proved** from those named hypotheses.
-/

@[expose] public section

open Set MeasureTheory
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- `K_{d,j} = 6/δ_j²`, the Chebyshev cost of the far pairs `|L - L₀| > δ_j` (`|D_j| ≤ 6`). -/
noncomputable def boasKd (a : ℝ) (j : ℕ) : ℝ := 6 / tentDelta a j ^ 2

/-- **The freezing bound on one block** (abstract; see the module docstring). -/
theorem boas_freeze_block {X ν wt sf χj : ℝ → ℝ} {Q : Set ℝ} {Lj δ Mp S Cl Cq : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ L, χj L ≠ 0 → L ∈ Icc (Lj - δ) (Lj + δ))
    (hQ : Icc (Lj - 3 * δ) (Lj + 3 * δ) ⊆ Q)
    (hχ : ∀ L, 0 ≤ χj L ∧ χj L ≤ 1) (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1) (hsf : ∀ L, 0 ≤ sf L ∧ sf L ≤ 1)
    (hMp : 0 ≤ Mp) (hS : 0 ≤ S) (hCl : 0 ≤ Cl) (hCq : 0 ≤ Cq)
    (hlip : ∀ L ∈ Q, ∀ L0 ∈ Q, |wt L * (1 - sf L) * χj L - wt L0 * (1 - sf L0) * χj L0| ≤ Mp * |L - L0|)
    (hSup : ∀ L ∈ Q, wt L * (1 - sf L) * χj L ≤ S)
    (hph : ∀ L ∈ Q, ∀ L0 ∈ Q, |X L0 + ν L0 * (L - L0) - X L| ≤ Cl * |L - L0| + Cq * (L - L0) ^ 2) :
    ∀ L L0, |wt L * (1 - sf L) * χj L * boasKernel X L -
        wt L0 * (1 - sf L0) * χj L0 * boasFrozenKernel X ν L0 L| ≤
      Q.indicator (fun L => (3 * Mp + 2 * S * Cl) * |L - L0| + (2 * S * Cq) * (L - L0) ^ 2) L +
        6 / δ ^ 2 * (L - L0) ^ 2 := by
  intro L L0
  set ω : ℝ → ℝ := fun L => wt L * (1 - sf L) * χj L with hω
  have hω0 : ∀ L, 0 ≤ ω L := fun L =>
    mul_nonneg (mul_nonneg (hw L).1 (sub_nonneg.2 (hsf L).2)) (hχ L).1
  have hω1 : ∀ L, ω L ≤ 1 := fun L => by
    have h1 : wt L * (1 - sf L) ≤ 1 := by
      nlinarith [(hw L).1, (hw L).2, (hsf L).1, (hsf L).2]
    calc ω L = (wt L * (1 - sf L)) * χj L := rfl
      _ ≤ 1 * 1 := mul_le_mul h1 (hχ L).2 (hχ L).1 zero_le_one
      _ = 1 := by norm_num
  have hKb := abs_boasKernel_le X L
  have hTb := abs_boasFrozenKernel_le X ν L0 L
  have hKe : ω L * boasKernel X L = wt L * (1 - sf L) * χj L * boasKernel X L := rfl
  have hRnn : 0 ≤ Q.indicator (fun L => (3 * Mp + 2 * S * Cl) * |L - L0| + (2 * S * Cq) * (L - L0) ^ 2) L := by
    apply Set.indicator_nonneg
    intro x _
    positivity
  have hKd : 0 ≤ 6 / δ ^ 2 * (L - L0) ^ 2 := by positivity
  rcases lt_or_ge δ |L - L0| with hfar | hnear
  · -- far pairs: `|D| ≤ 6 ≤ K_d (L - L0)²`
    have h1 : |ω L * boasKernel X L| ≤ 3 := by
      rw [abs_mul, abs_of_nonneg (hω0 L)]
      calc ω L * |boasKernel X L| ≤ 1 * 3 := mul_le_mul (hω1 L) hKb (abs_nonneg _) zero_le_one
        _ = 3 := by norm_num
    have h2 : |ω L0 * boasFrozenKernel X ν L0 L| ≤ 3 := by
      rw [abs_mul, abs_of_nonneg (hω0 L0)]
      calc ω L0 * |boasFrozenKernel X ν L0 L| ≤ 1 * 3 := mul_le_mul (hω1 L0) hTb (abs_nonneg _) zero_le_one
        _ = 3 := by norm_num
    have h3 : 6 ≤ 6 / δ ^ 2 * (L - L0) ^ 2 := by
      have : δ ^ 2 ≤ (L - L0) ^ 2 := by
        rw [← sq_abs (L - L0)]; exact pow_le_pow_left₀ hδ.le hfar.le 2
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    calc |ω L * boasKernel X L - ω L0 * boasFrozenKernel X ν L0 L|
        ≤ |ω L * boasKernel X L| + |ω L0 * boasFrozenKernel X ν L0 L| := abs_sub _ _
      _ ≤ _ := by linarith
  · by_cases hz : χj L = 0 ∧ χj L0 = 0
    · have e1 : ω L = 0 := by simp [hω, hz.1]
      have e2 : ω L0 = 0 := by simp [hω, hz.2]
      show |ω L * boasKernel X L - ω L0 * boasFrozenKernel X ν L0 L| ≤ _
      rw [e1, e2]; simp only [zero_mul, sub_zero, abs_zero]; linarith
    · -- near pairs with `ω ≠ 0` somewhere: both points lie in `I_j^* ⊂ Q_j`
      have hboth : L ∈ Icc (Lj - 3 * δ) (Lj + 3 * δ) ∧ L0 ∈ Icc (Lj - 3 * δ) (Lj + 3 * δ) := by
        have hab := abs_le.1 hnear
        rw [not_and_or] at hz
        rcases hz with hz | hz
        · have hs := hsupp L hz
          exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
        · have hs := hsupp L0 hz
          exact ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩
      have hLQ : L ∈ Q := hQ hboth.1
      have hL0Q : L0 ∈ Q := hQ hboth.2
      rw [Set.indicator_of_mem hLQ]
      have hd := hlip L hLQ L0 hL0Q
      have hS0 := hSup L0 hL0Q
      have hphase := hph L hLQ L0 hL0Q
      have hKT : |boasKernel X L - boasFrozenKernel X ν L0 L| ≤ 2 * (Cl * |L - L0| + Cq * (L - L0) ^ 2) := by
        have e : boasKernel X L - boasFrozenKernel X ν L0 L =
            2 * (Real.sin (X L0 + ν L0 * (L - L0)) - Real.sin (X L)) := by
          unfold boasKernel boasFrozenKernel; ring
        rw [e, abs_mul, abs_two]
        have := Real.abs_sin_sub_sin_le (X L0 + ν L0 * (L - L0)) (X L)
        have := this.trans hphase
        linarith
      have hsplit : ω L * boasKernel X L - ω L0 * boasFrozenKernel X ν L0 L =
          (ω L - ω L0) * boasKernel X L + ω L0 * (boasKernel X L - boasFrozenKernel X ν L0 L) := by ring
      show |ω L * boasKernel X L - ω L0 * boasFrozenKernel X ν L0 L| ≤ _
      rw [hsplit]
      have t1 : |(ω L - ω L0) * boasKernel X L| ≤ 3 * (Mp * |L - L0|) := by
        rw [abs_mul]
        calc |ω L - ω L0| * |boasKernel X L| ≤ (Mp * |L - L0|) * 3 :=
              mul_le_mul hd hKb (abs_nonneg _) (by positivity)
          _ = 3 * (Mp * |L - L0|) := by ring
      have t2 : |ω L0 * (boasKernel X L - boasFrozenKernel X ν L0 L)| ≤
          S * (2 * (Cl * |L - L0| + Cq * (L - L0) ^ 2)) := by
        rw [abs_mul, abs_of_nonneg (hω0 L0)]
        exact mul_le_mul hS0 hKT (abs_nonneg _) hS
      calc |(ω L - ω L0) * boasKernel X L + ω L0 * (boasKernel X L - boasFrozenKernel X ν L0 L)|
          ≤ |(ω L - ω L0) * boasKernel X L| + |ω L0 * (boasKernel X L - boasFrozenKernel X ν L0 L)| :=
            abs_add_le _ _
        _ ≤ _ := by nlinarith [hKd]

/-- info: 'FormalResearch.SignUncertainty.boas_freeze_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_freeze_block

/-- The block Lipschitz constant `Λ_j = 27(1 + τ_j²)/τ_j` of `τ₀` on `I_j^{**}`, `τ_j = τ₀(L_j)`, `L_j = x_{j+1}`. -/
noncomputable def boasLam (a : ℝ) (j : ℕ) : ℝ :=
  27 * (1 + tau0 (tentNode a (j + 1)) ^ 2) / tau0 (tentNode a (j + 1))

/-- `C_l = Λ_j C_θ/(1 + τ_j/3)²`, the linear coefficient of the frozen phase on block `j`. -/
noncomputable def boasCl (Cθ a : ℝ) (j : ℕ) : ℝ :=
  boasLam a j * (Cθ / (1 + tau0 (tentNode a (j + 1)) / 3) ^ 2)

/-- `C_q = cΛ_j`, the quadratic coefficient of the frozen phase on block `j`. -/
noncomputable def boasCq (c a : ℝ) (j : ℕ) : ℝ := c * boasLam a j

lemma boasLam_pos {a : ℝ} (ha : 0 < a) (j : ℕ) : 0 < boasLam a j := by
  have := tau0_pos (tentNode_pos ha (j + 1))
  unfold boasLam; positivity

/-- **The field `freeze` of `BoasInputs`** (`ct:boas` Step 5), for `X = boasX c ε`, `ν = boasNu c`, `χ = tent (tentNode a)`,
`Q = tentQ a`, `A_j = 3M_j' + 2S_jC_l`, `B_j = 2S_jC_q`, `K_{d,j} = 6/δ_j²` (`boasKd`).  Hypotheses: `ct:outer`(3)
(`hθ' : |θ_ε'| ≤ C_θ(1+|t|)^{-2}`), the Lipschitz bound `hlip` of the block weight `ω_j = w̃(1 - 𝔰_far)χ_j` on `Q_j`
with constant `M_j'` and its supremum `S_j` (`hSup`) (`ct:Bj-pointwise`(c), (d), `ct:taper-harnack`, `ct:sigma-prime`). -/
theorem boas_freeze_field {c ε Cθ a : ℝ} {J : ℕ} (hc : 0 ≤ c) (hCθ0 : 0 ≤ Cθ) (ha : 0 < a)
    (hθ' : ∀ t : ℝ, |deriv (CtOuter.outerTheta ε) t| ≤ Cθ / (1 + |t|) ^ 2)
    {wt sf : ℝ → ℝ} (hw : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1) (hsf : ∀ L, 0 ≤ sf L ∧ sf L ≤ 1)
    {Mp S : ℕ → ℝ} (hMp : ∀ j < J, 0 ≤ Mp j) (hS : ∀ j < J, 0 ≤ S j)
    (hlip : ∀ j < J, ∀ L ∈ tentQ a j, ∀ L0 ∈ tentQ a j,
      |wt L * (1 - sf L) * tent (tentNode a) j L - wt L0 * (1 - sf L0) * tent (tentNode a) j L0| ≤
        Mp j * |L - L0|)
    (hSup : ∀ j < J, ∀ L ∈ tentQ a j, wt L * (1 - sf L) * tent (tentNode a) j L ≤ S j) :
    ∀ j < J, ∀ L L0,
      |wt L * (1 - sf L) * tent (tentNode a) j L * boasKernel (boasX c ε) L -
          wt L0 * (1 - sf L0) * tent (tentNode a) j L0 *
            boasFrozenKernel (boasX c ε) (boasNu c) L0 L| ≤
        (tentQ a j).indicator (fun L => (3 * Mp j + 2 * S j * boasCl Cθ a j) * |L - L0| +
          (2 * S j * boasCq c a j) * (L - L0) ^ 2) L + boasKd a j * (L - L0) ^ 2 := by
  intro j hj
  have hx := tentNode_strictMono ha
  have hLj0 : 0 < tentNode a (j + 1) := tentNode_pos ha _
  have hδ := tentDelta_pos ha j
  have hr : 0 < tau0 (tentNode a (j + 1)) := tau0_pos hLj0
  have hLam := boasLam_pos ha j
  have hCl : 0 ≤ boasCl Cθ a j := by
    unfold boasCl; exact mul_nonneg hLam.le (by positivity)
  have hCq : 0 ≤ boasCq c a j := mul_nonneg hc hLam.le
  have hLjQ : tentNode a (j + 1) ∈ tentQ a j := by
    unfold tentQ; exact ⟨by linarith, by linarith⟩
  have key := boas_freeze_block (X := boasX c ε) (ν := boasNu c) (wt := wt) (sf := sf)
    (χj := tent (tentNode a) j) (Q := tentQ a j) (Lj := tentNode a (j + 1)) (δ := tentDelta a j)
    (Mp := Mp j) (S := S j) (Cl := boasCl Cθ a j) (Cq := boasCq c a j) hδ
    (fun L hL => tentNode_block_support ha j L hL) (subset_refl _)
    (fun L => ⟨tent_nonneg hx j L, tent_le_one _ j L⟩) hw hsf (hMp j hj) (hS j hj) hCl hCq
    (hlip j hj) (hSup j hj) ?_
  · intro L L0
    have := key L L0
    unfold boasKd
    exact this
  · intro L hL L0 hL0
    obtain ⟨_, hL1, hLr1, hLr2⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl
      hLjQ hL
    obtain ⟨_, hL01, hL0r1, hL0r2⟩ := tentBlock_tau0_ratio (Lj := tentNode a (j + 1)) (δ := tentDelta a j) hLj0 rfl
      hLjQ hL0
    have := boas_phase_block (c := c) (ε := ε) (Cθ := Cθ) (r := tau0 (tentNode a (j + 1))) (L := L) (L0 := L0)
      hc hCθ0 hr hθ' hL1 hL01 hLr1 hLr2 hL0r1 hL0r2
    unfold boasCl boasCq boasLam
    exact this

/-- **`ct:outer`(3), derivative bound in the form of `boas_freeze_field`**: `|θ_ε'(t)| ≤ C_θ(1+|t|)^{-2}` for `ε = ±1`,
all `t`, from `ct_outer_part3`. -/
theorem ct_outer_theta_deriv_bound : ∃ Cθ : ℝ, 0 ≤ Cθ ∧ ∀ ε : ℝ, (ε = -1 ∨ ε = 1) → ∀ t : ℝ,
    |deriv (CtOuter.outerTheta ε) t| ≤ Cθ / (1 + |t|) ^ 2 := by
  obtain ⟨_, h⟩ := CtOuter.ct_outer_part3
  obtain ⟨C1, h1⟩ := (h (-1) (Or.inl rfl) 1 le_rfl).2
  obtain ⟨C2, h2⟩ := (h 1 (Or.inr rfl) 1 le_rfl).2
  refine ⟨max |C1| |C2|, le_trans (abs_nonneg _) (le_max_left _ _), fun ε hε t => ?_⟩
  have hp : 0 < (1 + |t|) ^ 2 := by positivity
  rcases hε with rfl | rfl
  · have := h1 t
    rw [iteratedDeriv_one] at this
    refine this.trans (div_le_div_of_nonneg_right ((le_abs_self C1).trans (le_max_left _ _)) hp.le)
  · have := h2 t
    rw [iteratedDeriv_one] at this
    refine this.trans (div_le_div_of_nonneg_right ((le_abs_self C2).trans (le_max_right _ _)) hp.le)

/-- info: 'FormalResearch.SignUncertainty.ct_outer_theta_deriv_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ct_outer_theta_deriv_bound

/-- info: 'FormalResearch.SignUncertainty.boas_freeze_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_freeze_field

end FormalResearch.SignUncertainty

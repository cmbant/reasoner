module

public import Mathlib
public import FormalResearch.JB.JBThmB
public import FormalResearch.JacobiEigenvectors.TheoremB.Statements

/-!
# Paper J, Theorem B from `prop:thb-inputs` (L3.B)

Source: Paper J, `thmB.tex`, Theorem `thm:B` (`eq:thmB`) and its proof by `thm:thb-onestep` (`FormalResearch.JB.jb_onestep`).

`thmB_of_propThbInputs : PropThbInputs CP TB spl → ThmB CP spl`.  The constants `cs, N₀, C_ε, c_ε` of `PropThbInputs` are fixed before `μ` (F-B2),
so the constants `C, h₁` of the one-step reduction (`jb_onestep`, `small_scalars` with `K_ε = 0`) depend only on `cs`, `L`, `C_ε`, `c_ε`; the radius
`h_m = min (h₁, 1/(C+1), h_{N₀})` is therefore uniform in `μ ∈ K`.  The restriction to `N ≥ N₀` is automatic for `h ≤ h_{N₀} = L/(N₀+1)`.

**Differences from the paper**: `thm_B_conditional` (`JB/JBThmB.lean`) is stated for one family at one `μ`; its proof is repeated here in the uniform form
`onestep_uniform` (all `N`, one `OneStepInputs` each, constants depending on `cs`, `L`, `C_ε`, `c_ε` only).  **Not formalised**: nothing beyond `PropThbInputs`
(Layer 3 assembly, item L3.5 of `PLAN.md`).
-/

@[expose] public section

namespace FormalResearch.JacobiEigenvectors.TheoremB

open Finset FormalResearch.JacobiEigenvectors.Setting FormalResearch.JacobiEigenvectors.Charts FormalResearch.JacobiEigenvectors.TheoremA
open FormalResearch.JB
open scoped Matrix.Norms.L2Operator MatrixOrder Matrix

/-- The uniform one-step reduction: for fixed constants `cs, C_ε, c_ε` there are `C ≥ 0` and `h₁ > 0` such that every `OneStepInputs cs (N+1) m h`, `h = L/(N+1) ≤ h₁`,
with `ε5 ≤ C_ε e^{-c_ε/h}`, has `‖G0 - U‖ ≤ C h^m` and, when this is `< 1`, an orthogonal polar factor within `2 ‖G0 - U‖` of `U`. -/
theorem onestep_uniform (cs : OneStepConsts) {m : ℕ} (hm : 1 ≤ m) {L : ℝ} (hL : 0 < L) (Cε cε : ℝ) (hcε : 0 < cε) :
    ∃ C h₁ : ℝ, 0 ≤ C ∧ 0 < h₁ ∧ ∀ (N : ℕ) (I : OneStepInputs cs (N + 1) m (stepSize L N)),
      stepSize L N ≤ h₁ → I.ε5 ≤ Cε * Real.exp (-cε / stepSize L N) →
      ‖I.G0 - I.U‖ ≤ C * stepSize L N ^ m ∧
        (‖I.G0 - I.U‖ < 1 →
          (I.G0 * (CFC.sqrt (I.G0ᵀ * I.G0))⁻¹)ᵀ * (I.G0 * (CFC.sqrt (I.G0ᵀ * I.G0))⁻¹) = 1 ∧
            ‖I.G0 * (CFC.sqrt (I.G0ᵀ * I.G0))⁻¹ - I.U‖ ≤ 2 * ‖I.G0 - I.U‖) := by
  obtain ⟨Cstar, hC⟩ := jb_onestep cs m
  obtain ⟨h₁, hh₁, hsm⟩ := small_scalars cs hm hL Cε cε 0 hcε
  have hCn := cs.C_nonneg
  have hsL : 0 ≤ √L := Real.sqrt_nonneg _
  have hC0 : 0 ≤ max Cstar 0 + 2 * cs.C * √L := by
    have : 0 ≤ max Cstar 0 := le_max_right _ _
    have : 0 ≤ 2 * cs.C * √L := by positivity
    linarith
  refine ⟨max Cstar 0 + 2 * cs.C * √L, h₁, hC0, hh₁, fun N I hN hε5 => ?_⟩
  have hpos := stepSize_pos hL N
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := hsm _ hpos hN
  have hD := card_eq_div hL N
  have hsmall : I.Small := by
    refine ⟨s1, ?_, s3, s4, s5, ?_⟩
    · rw [hD]; exact s2
    · rw [hD]
      calc 2 * (L / stepSize L N) * I.ε5
          ≤ 2 * (L / stepSize L N) * (Cε * (1 / stepSize L N) ^ 0 * Real.exp (-cε / stepSize L N)) := by
            gcongr; simpa using hε5
        _ ≤ _ := s6
  obtain ⟨-, r2, r3⟩ := hC (N + 1) (stepSize L N) I hsmall
  refine ⟨?_, r3⟩
  have e1 : √(((N + 1 : ℕ) : ℝ)) * (cs.C * stepSize L N ^ (m + 1) * Real.log (1 / stepSize L N)) ≤
      2 * cs.C * √L * stepSize L N ^ m := by
    rw [hD]; exact sqrt_mul_eta_le m hL hpos hCn
  have hhm : 0 ≤ stepSize L N ^ m := by positivity
  calc ‖I.G0 - I.U‖ ≤ Cstar * stepSize L N ^ m +
        √(((N + 1 : ℕ) : ℝ)) * (cs.C * stepSize L N ^ (m + 1) * Real.log (1 / stepSize L N)) := r2
    _ ≤ max Cstar 0 * stepSize L N ^ m + 2 * cs.C * √L * stepSize L N ^ m := by
        gcongr
        exact le_max_left _ _
    _ = (max Cstar 0 + 2 * cs.C * √L) * stepSize L N ^ m := by ring

theorem stepSize_le_imp {L : ℝ} (hL : 0 < L) {N N0 : ℕ} (h : stepSize L N ≤ stepSize L N0) : N0 ≤ N := by
  by_contra hlt
  replace hlt := Nat.not_le.1 hlt
  have : stepSize L N0 < stepSize L N := by
    unfold stepSize
    apply div_lt_div_of_pos_left hL (by positivity)
    have : (N : ℝ) + 1 < (N0 : ℝ) + 1 := by exact_mod_cast Nat.succ_lt_succ hlt
    exact_mod_cast this
  linarith

variable {Par : Type*} [TopologicalSpace Par]
variable {F : SymbolFamily Par} {K : Set Par} {Kidx : ℕ} {t0 : ℝ} {m q : ℕ} {U V : ℝ → ℝ → ℝ} {cPC CPC : ℝ}

/-- **Theorem B** (`thm:B`) from `prop:thb-inputs`: `PropThbInputs CP TB spl → ThmB CP spl`.  Proved (given the `PropThbInputs` hypothesis); the radius `h_m` and the constant `C` do not depend on `μ ∈ K`. -/
theorem thmB_of_propThbInputs (CP : ChartPair (F := F) (K := K) (Kidx := Kidx) (t0 := t0) (m := m) (q := q) (U := U) (V := V) (cPC := cPC) (CPC := CPC))
    (TB : TransferBundle CP) (spl : Fin CP.CI0.nb → ℝ) (hI : PropThbInputs CP TB spl) : ThmB CP spl := by
  intro hm hK hq hKc hH hD hs
  obtain ⟨cs, N0, Cε, cε, hcε, H⟩ := hI hm hK hq hKc hH hD hs
  obtain ⟨C, h₁, hC0, hh₁, key⟩ := onestep_uniform cs hm F.L_pos Cε cε hcε
  have hN0pos := stepSize_pos F.L_pos N0
  set hp : ℝ := min (min h₁ (1 / (C + 1))) (stepSize F.L N0) with hpdef
  have hp0 : 0 < hp := lt_min (lt_min hh₁ (by positivity)) hN0pos
  have hp1 : hp ≤ 1 / (C + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hc1 : hp * (C + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 hp1
  have hp1' : hp ≤ 1 := by nlinarith
  have hpm : hp ^ m ≤ hp := pow_le_of_le_one hp0.le hp1' (by omega)
  have hlt1 : C * hp ^ m < 1 := by nlinarith
  refine ⟨C, hp, hp0, hlt1, fun μ hμ N hN ht Xs Um hE => ?_⟩
  have hNN0 : N0 ≤ N := stepSize_le_imp F.L_pos (hN.trans (min_le_right _ _))
  have hNh₁ : stepSize F.L N ≤ h₁ := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  obtain ⟨I, hU, hG0, -, hε⟩ := H μ hμ N hNN0 ht Xs Um hE
  obtain ⟨r1, r2⟩ := key N I hNh₁ hε
  have hpos := stepSize_pos F.L_pos N
  have hhm : stepSize F.L N ^ m ≤ hp ^ m := pow_le_pow_left₀ hpos.le hN m
  have hlt : C * stepSize F.L N ^ m < 1 := by nlinarith
  have hs0 : 0 ≤ stepSize F.L N ^ m := by positivity
  obtain ⟨o1, o2⟩ := r2 (r1.trans_lt hlt)
  rw [hG0, hU] at r1 o2
  rw [hG0] at o1
  have e : F.step N = stepSize F.L N := rfl
  refine ⟨r1, o1, ?_⟩
  rw [e]
  linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremB.thmB_of_propThbInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremB.thmB_of_propThbInputs

end FormalResearch.JacobiEigenvectors.TheoremB

end

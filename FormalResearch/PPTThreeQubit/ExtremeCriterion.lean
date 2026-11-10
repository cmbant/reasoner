module

public import Mathlib
public import FormalResearch.PPTThreeQubit.PartialTranspose
public import FormalResearch.MatrixAnalysis.ExtremeCriterion

/-!
# The supported-face criterion for fully-PPT three-qubit states

Source: `QI/hidden_entanglement/ppt_three_qubit/appendix_family.tex` (proof of `cor:ppt3-extreme6`)
and `appendix_surface.tex` (proof of `cor:ppt3-extreme5`).  The generic criterion (for any finite family
of cut maps) is `MatrixAnalysis.ExtremeCriterion`; here it is instantiated with the three partial
transposes `cutPT`: `fullyPPT3` is the set of fully-PPT states,

* `ppt3_extreme_iff`: a fully-PPT state is extreme iff its face-direction space is `ℝ σ`;
* `ppt3_extreme_of_sandwich`: the form used in the paper, for `σ = B X B†` with `B` injective.
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix
open FormalResearch.MatrixAnalysis.ExtremeCriterion
open scoped ComplexOrder

noncomputable section

/-! ### Three qubits -/

/-- The three single-qubit partial transposes `T_A, T_B, T_C` as real-linear maps. -/
def cutPT : Fin 3 → Matrix (Fin 8) (Fin 8) ℂ →ₗ[ℝ] Matrix (Fin 8) (Fin 8) ℂ :=
  ![{ toFun := ptA, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl },
    { toFun := ptB, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl },
    { toFun := ptC, map_add' := fun _ _ => by ext; rfl, map_smul' := fun _ _ => by ext; rfl }]

/-- The set of three-qubit fully-PPT states: `ρ ≥ 0`, `tr ρ = 1`, `ρ^{T_c} ≥ 0` for `c = A, B, C`. -/
def fullyPPT3 : Set (Matrix (Fin 8) (Fin 8) ℂ) := fullyPPT cutPT

theorem mem_fullyPPT3_iff (ρ : Matrix (Fin 8) (Fin 8) ℂ) :
    ρ ∈ fullyPPT3 ↔
      ρ.PosSemidef ∧ ρ.trace = 1 ∧ (ptA ρ).PosSemidef ∧ (ptB ρ).PosSemidef ∧ (ptC ρ).PosSemidef := by
  unfold fullyPPT3 fullyPPT
  simp only [Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.isValue]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, -⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5, fun i => i.elim0⟩

theorem cutPT_isHermitian (c : Fin 3) (ρ : Matrix (Fin 8) (Fin 8) ℂ) (h : ρ.IsHermitian) :
    (cutPT c ρ).IsHermitian := by
  fin_cases c
  · show (ptA ρ)ᴴ = ptA ρ
    ext i j
    have := congrFun (congrFun h.eq (⟨4 * (j.val / 4) + i.val % 4, by omega⟩ : Fin 8))
      (⟨4 * (i.val / 4) + j.val % 4, by omega⟩ : Fin 8)
    simpa [ptA, conjTranspose_apply] using this
  · show (ptB ρ)ᴴ = ptB ρ
    ext i j
    have := congrFun (congrFun h.eq
      (⟨4 * (i.val / 4) + 2 * (j.val / 2 % 2) + i.val % 2, by omega⟩ : Fin 8))
      (⟨4 * (j.val / 4) + 2 * (i.val / 2 % 2) + j.val % 2, by omega⟩ : Fin 8)
    simpa [ptB, conjTranspose_apply] using this
  · show (ptC ρ)ᴴ = ptC ρ
    ext i j
    have := congrFun (congrFun h.eq (⟨2 * (i.val / 2) + j.val % 2, by omega⟩ : Fin 8))
      (⟨2 * (j.val / 2) + i.val % 2, by omega⟩ : Fin 8)
    simpa [ptC, conjTranspose_apply] using this

/-- **Supported-face criterion for three qubits.**  A fully-PPT three-qubit state `σ` is an extreme
point of the fully-PPT set iff every Hermitian `D` with `ker σ ⊆ ker D` and
`ker σ^{T_c} ⊆ ker D^{T_c}` (`c = A, B, C`) is a multiple of `σ`. -/
theorem ppt3_extreme_iff {σ : Matrix (Fin 8) (Fin 8) ℂ} (hσ : σ ∈ fullyPPT3) :
    σ ∈ fullyPPT3.extremePoints ℝ ↔
      ∀ D : Matrix (Fin 8) (Fin 8) ℂ, D.IsHermitian → (∀ k, σ *ᵥ k = 0 → D *ᵥ k = 0) →
        (∀ k, (ptA σ) *ᵥ k = 0 → (ptA D) *ᵥ k = 0) →
        (∀ k, (ptB σ) *ᵥ k = 0 → (ptB D) *ᵥ k = 0) →
        (∀ k, (ptC σ) *ᵥ k = 0 → (ptC D) *ᵥ k = 0) → ∃ a : ℂ, D = a • σ := by
  rw [fullyPPT3, mem_extremePoints_iff_faceDirection cutPT cutPT_isHermitian hσ]
  constructor
  · intro h D hD h0 hA hB hC
    refine h D ⟨hD, h0, fun c => ?_⟩
    fin_cases c
    · exact hA
    · exact hB
    · exact hC
  · intro h D ⟨hD, h0, hc⟩
    exact h D hD h0 (hc 0) (hc 1) (hc 2)

/-- `[GIM]` for three qubits in the form used for `cor:ppt3-extreme6` and `cor:ppt3-extreme5`:
`σ = B X B†` with `B : 8 × m` injective; `S_A, S_B, S_C` vectors in the kernels of the three partial
transposes of `σ`.  If the only Hermitian `Y` with `(B Y B†)^{T_c} k = 0` for `k ∈ S_c`
(`c = A, B, C`) are multiples of `X`, then `σ` is an extreme fully-PPT state. -/
theorem ppt3_extreme_of_sandwich {m : Type*} [Fintype m] [DecidableEq m]
    {σ : Matrix (Fin 8) (Fin 8) ℂ} (hσ : σ ∈ fullyPPT3) (B : Matrix (Fin 8) m ℂ)
    (X : Matrix m m ℂ) (hσB : σ = B * X * Bᴴ) (hB : Function.Injective B.mulVec)
    (SA SB SC : Set (Fin 8 → ℂ))
    (hSA : ∀ k ∈ SA, (ptA σ) *ᵥ k = 0) (hSB : ∀ k ∈ SB, (ptB σ) *ᵥ k = 0)
    (hSC : ∀ k ∈ SC, (ptC σ) *ᵥ k = 0)
    (hnull : ∀ Y : Matrix m m ℂ, Y.IsHermitian →
      (∀ k ∈ SA, (ptA (B * Y * Bᴴ)) *ᵥ k = 0) → (∀ k ∈ SB, (ptB (B * Y * Bᴴ)) *ᵥ k = 0) →
      (∀ k ∈ SC, (ptC (B * Y * Bᴴ)) *ᵥ k = 0) → ∃ a : ℂ, Y = a • X) :
    σ ∈ fullyPPT3.extremePoints ℝ := by
  refine mem_extremePoints_of_sandwich cutPT hσ B X hσB hB ![SA, SB, SC] ?_ ?_
  · intro c; fin_cases c
    · exact hSA
    · exact hSB
    · exact hSC
  · intro Y hY h
    exact hnull Y hY (h 0) (h 1) (h 2)

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_extreme_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_extreme_iff

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_extreme_of_sandwich' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_extreme_of_sandwich

end

end FormalResearch.PPTThreeQubit

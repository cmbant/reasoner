import FormalResearch.FourQubitEntropy.SevenQubitIcoState

/-!
# Sectors of the icosahedral state and the flat-phase companions (`prop:flatphaseLU`)

`ResearchNotes/QI/seven_qubit_entanglement/balanced_purity.tex`, `prop:flatphaseLU` (QB-3): write
`Ψico = A + B` with `A` supported on the sectors `(s, w) = (0, 2), (1, 0)` and `B` on `(0, 6), (1, 4)`,
where `s` is the special bit and `w` the Hamming weight of the six ordinary bits. For every real `θ`
the "flat-phase companion" `e^{iθ} A + e^{-iθ} B` is the image of `Ψico` under the *diagonal* local
unitary `diag(1, e^{-iθ}) ⊗ diag(1, e^{-iθ/2})^{⊗ 6}` up to the global phase `e^{2iθ}`.

Everything is proved for the whole real family `icosahedralState α β` (not only `Ψico`).

* `coeff_support`: the coefficient tensors vanish outside the four sectors (support of `ψ_x`);
* `localApply`: the action of a product of single-qubit matrices on a tensor; `localApply_diag`
  specialises it to diagonal matrices;
* `flatPhase_companion_LU`: the proposition, pointwise on all 128 basis amplitudes.
-/

open Complex

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

/-- Hamming weight of the six ordinary bits (`w` in the sector label). -/
def ordWeight (z : BitString) : ℕ := tailWeight (tail z)

/-- Sectors `(s, w) = (0, 2), (1, 0)` (the support of `A`). -/
def inA (z : BitString) : Bool :=
  (!z 0 && decide (ordWeight z = 2)) || (z 0 && decide (ordWeight z = 0))

/-- Sectors `(s, w) = (0, 6), (1, 4)` (the support of `B`). -/
def inB (z : BitString) : Bool :=
  (!z 0 && decide (ordWeight z = 6)) || (z 0 && decide (ordWeight z = 4))

/-- Both coefficient tensors vanish outside the four sectors. -/
theorem coeff_support :
    ∀ z : BitString, inA z = false → inB z = false →
      alphaCoefficient z = 0 ∧ betaCoefficient z = 0 := by
  decide +kernel

/-- The sectors of `A` and `B` are disjoint. -/
theorem inA_inB_disjoint : ∀ z : BitString, ¬ (inA z = true ∧ inB z = true) := by
  decide +kernel

/-- The complex-valued tensor of `icosahedralState α β`. -/
noncomputable def icosC (alpha beta : ℝ) (z : BitString) : ℂ :=
  ((icosahedralState alpha beta z : ℝ) : ℂ)

/-- The part `A` of the state (sectors `(0,2)`, `(1,0)`). -/
noncomputable def partA (alpha beta : ℝ) (z : BitString) : ℂ :=
  if inA z = true then icosC alpha beta z else 0

/-- The part `B` of the state (sectors `(0,6)`, `(1,4)`). -/
noncomputable def partB (alpha beta : ℝ) (z : BitString) : ℂ :=
  if inB z = true then icosC alpha beta z else 0

/-- `Ψ = A + B`: the state is supported on the four sectors. -/
theorem icosC_eq_partA_add_partB (alpha beta : ℝ) (z : BitString) :
    icosC alpha beta z = partA alpha beta z + partB alpha beta z := by
  unfold partA partB
  by_cases hA : inA z = true
  · have hB : inB z ≠ true := fun hB => inA_inB_disjoint z ⟨hA, hB⟩
    simp [hA, hB]
  · by_cases hB : inB z = true
    · simp [hA, hB]
    · have hA' : inA z = false := by simpa using hA
      have hB' : inB z = false := by simpa using hB
      obtain ⟨h1, h2⟩ := coeff_support z hA' hB'
      simp [hA, hB, icosC, icosahedralState, h1, h2]

/-! ### Local operators -/

/-- The action of `⊗ᵢ Uᵢ` (single-qubit matrices `Uᵢ a b`, row `a`, column `b`) on a tensor. -/
def localApply (U : Fin 7 → Bool → Bool → ℂ) (ψ : BitString → ℂ) (z : BitString) : ℂ :=
  ∑ y : BitString, (∏ i, U i (z i) (y i)) * ψ y

/-- The diagonal single-qubit matrix with diagonal entries `d i false`, `d i true`. -/
def diagMat (d : Fin 7 → Bool → ℂ) : Fin 7 → Bool → Bool → ℂ :=
  fun i a b => if a = b then d i a else 0

theorem localApply_diag (d : Fin 7 → Bool → ℂ) (ψ : BitString → ℂ) (z : BitString) :
    localApply (diagMat d) ψ z = (∏ i, d i (z i)) * ψ z := by
  unfold localApply
  rw [Finset.sum_eq_single z]
  · simp [diagMat]
  · intro y _ hy
    have : ∃ i, z i ≠ y i := by
      by_contra h
      push Not at h
      exact hy (funext fun i => (h i).symm)
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [diagMat, hi]), zero_mul]
  · intro h; exact absurd (Finset.mem_univ z) h

/-- The diagonal entries `1, e^{-iθ}` on the special qubit and `1, e^{-iθ/2}` on the six ordinary
qubits. -/
noncomputable def flatPhaseD (θ : ℝ) (i : Fin 7) (a : Bool) : ℂ :=
  cexp (if a then (if i = 0 then -(I * θ) else -(I * θ) / 2) else 0)

/-- Each diagonal entry is a phase (so the local operators are unitary). -/
theorem flatPhaseD_norm (θ : ℝ) (i : Fin 7) (a : Bool) : ‖flatPhaseD θ i a‖ = 1 := by
  unfold flatPhaseD
  rw [Complex.norm_exp]
  split_ifs <;> simp

/-- The product of the phases on a basis string is `exp(-iθ (s + w/2))`. -/
theorem flatPhase_prod (θ : ℝ) (z : BitString) :
    ∏ i, flatPhaseD θ i (z i) =
      cexp (-(I * θ) * ((if z 0 = true then 1 else 0) + (ordWeight z : ℂ) / 2)) := by
  unfold flatPhaseD
  rw [← Complex.exp_sum, Fin.sum_univ_succ]
  congr 1
  have hw : (ordWeight z : ℂ) = ∑ x : Fin 6, (if z x.succ = true then 1 else 0 : ℂ) := by
    simp only [ordWeight, tailWeight, tail, Nat.cast_sum]
    exact Finset.sum_congr rfl fun i _ => by by_cases hz : z i.succ = true <;> simp [hz]
  rw [hw]
  have h : ∀ i : Fin 6, (if z i.succ = true then (if (i.succ : Fin 7) = 0 then -(I * θ) else
      -(I * θ) / 2) else 0) = -(I * θ) / 2 * (if z i.succ = true then 1 else 0) := by
    intro i
    have : (i.succ : Fin 7) ≠ 0 := Fin.succ_ne_zero i
    by_cases hz : z i.succ = true <;> simp [hz, this]
  simp only [h, ← Finset.mul_sum]
  generalize (∑ x : Fin 6, (if z x.succ = true then 1 else 0 : ℂ)) = S
  by_cases h0 : z 0 = true
  · simp only [h0, ↓reduceIte]; simp; ring
  · simp only [h0, ↓reduceIte, Bool.false_eq_true]; ring

/-- **`prop:flatphaseLU`.** For every real `θ`, `e^{iθ} A + e^{-iθ} B` equals `e^{2iθ}` times the image
of `Ψ` under the diagonal local unitary `diag(1, e^{-iθ}) ⊗ diag(1, e^{-iθ/2})^{⊗6}`; pointwise on
all basis amplitudes, for every `α, β`. -/
theorem flatPhase_companion_LU (θ alpha beta : ℝ) (z : BitString) :
    cexp (I * θ) * partA alpha beta z + cexp (-(I * θ)) * partB alpha beta z =
      cexp (2 * (I * θ)) *
        localApply (diagMat (flatPhaseD θ)) (icosC alpha beta) z := by
  rw [localApply_diag, flatPhase_prod]
  by_cases hA : inA z = true
  · have hB : inB z ≠ true := fun hB => inA_inB_disjoint z ⟨hA, hB⟩
    have hE : ((if z 0 = true then 1 else 0 : ℂ) + (ordWeight z : ℂ) / 2) = 1 := by
      simp only [inA, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hA
      rcases hA with ⟨h0, hw⟩ | ⟨h0, hw⟩ <;> simp [h0, hw]
    have hB' : inB z = false := by simpa using hB
    simp only [partA, partB, hA, hB', Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, hE]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · by_cases hB : inB z = true
    · have hE : ((if z 0 = true then 1 else 0 : ℂ) + (ordWeight z : ℂ) / 2) = 3 := by
        simp only [inB, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq]
          at hB
        rcases hB with ⟨h0, hw⟩ | ⟨h0, hw⟩ <;> simp [h0, hw] <;> norm_num
      have hA' : inA z = false := by simpa using hA
      simp only [partA, partB, hA', hB, Bool.false_eq_true, ↓reduceIte, mul_zero, zero_add, hE]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      ring
    · have hA' : inA z = false := by simpa using hA
      have hB' : inB z = false := by simpa using hB
      obtain ⟨h1, h2⟩ := coeff_support z hA' hB'
      simp [partA, partB, hA, hB, icosC, icosahedralState, h1, h2]

end FormalResearch.FourQubitEntropy.SevenQubitIco

module

public import FormalResearch.PPTThreeQubit.SwapSymmetric
public import FormalResearch.MatrixAnalysis.TraceDistance

/-!
# Distance to the biseparable states: the symmetrisation corollary

Source: `QI/hidden_entanglement/ppt_three_qubit/family.tex` (`cor:ppt3-symmetrisation`).

* `traceDist ρ σ = ½ ‖ρ - σ‖₁` (the trace norm `MatrixAnalysis.tnorm` of a Hermitian matrix) and
  `bsDist ρ`, the infimum of `traceDist ρ σ` over unit-trace biseparable `σ`;
* `bsDist_le_cyclic`: the cyclic form `¼‖ρ - SρS‖₁` for the transpositions `S_AC`, `S_AB`;
* `bsDist_le_permAvg`: `eq:ppt3-asymmetry-upper`; `bsDist_le_swap_average`: the pinching bound of
  `eq:ppt3-pinch` in the Hermitian form `¼‖ρ - S_BC ρ S_BC‖₁`.

`Pinching.lean` proves `eq:ppt3-pinch` with the paper's non-Hermitian `‖P₃ρP₁‖₁`;
`KernelQuantCuts.lean` instantiates the generic `MatrixAnalysis.kernel_quant_matrix` with the cut-product
maps (`kernel_quant_cutProduct`, `kernel_quant_distance`).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix FormalResearch.MatrixAnalysis
open FormalResearch.MatrixAnalysis (IsEffect)
open scoped ComplexOrder

noncomputable section

/-! ### Distance to the biseparable states -/

/-- The trace distance `½‖ρ - σ‖₁`. -/
def traceDist (ρ σ : Matrix (Fin 8) (Fin 8) ℂ) : ℝ := (1 / 2) * tnorm (ρ - σ)

/-- The distance `D(ρ, BS)` from the set of unit-trace biseparable states. -/
def bsDist (ρ : Matrix (Fin 8) (Fin 8) ℂ) : ℝ :=
  sInf {d | ∃ σ, IsBiseparable σ ∧ σ.trace = 1 ∧ d = traceDist ρ σ}

theorem bsDist_le {ρ σ : Matrix (Fin 8) (Fin 8) ℂ} (h : IsBiseparable σ) (ht : σ.trace = 1) :
    bsDist ρ ≤ traceDist ρ σ := by
  refine csInf_le ⟨0, ?_⟩ ⟨σ, h, ht, rfl⟩
  rintro _ ⟨τ, -, -, rfl⟩
  unfold traceDist
  have := tnorm_nonneg (ρ - τ)
  positivity

/-- Biseparable unit-trace states exist (a product state). -/
theorem exists_biseparable_state : ∃ σ : Matrix (Fin 8) (Fin 8) ℂ, IsBiseparable σ ∧ σ.trace = 1 := by
  refine ⟨vecMulVec (Pi.single 0 1) (star (Pi.single 0 1 : Fin 8 → ℂ)), ⟨1, fun _ => Pi.single 0 1, ?_, ?_⟩, ?_⟩
  · intro _
    left
    refine ⟨Pi.single 0 1, Pi.single 0 1, fun i => ?_⟩
    fin_cases i <;> simp [Fin.ext_iff]
  · simp
  · simp [Matrix.trace, vecMulVec_apply, Pi.single_apply]

/-- A lower bound on every `traceDist ρ σ` with `σ` biseparable of unit trace bounds `bsDist`. -/
theorem le_bsDist {ρ : Matrix (Fin 8) (Fin 8) ℂ} {c : ℝ}
    (h : ∀ σ, IsBiseparable σ → σ.trace = 1 → c ≤ traceDist ρ σ) : c ≤ bsDist ρ := by
  obtain ⟨σ₀, h0, t0⟩ := exists_biseparable_state
  refine le_csInf ⟨_, σ₀, h0, t0, rfl⟩ ?_
  rintro _ ⟨σ, hσ, ht, rfl⟩
  exact h σ hσ ht

/-! ### `cor:ppt3-symmetrisation`: distance bounds -/

theorem trace_submatrix_perm {f : Fin 8 → Fin 8} (hf : Function.Bijective f)
    (M : Matrix (Fin 8) (Fin 8) ℂ) : (M.submatrix f f).trace = M.trace := by
  simp only [Matrix.trace, Matrix.diag, submatrix_apply]
  exact hf.sum_comp (fun i => M i i)

theorem trace_permAvg (ρ : Matrix (Fin 8) (Fin 8) ℂ) : (permAvg ρ).trace = ρ.trace := by
  have h1 : Function.Bijective cycShift := by decide
  have h2 : Function.Bijective (cycShift ∘ cycShift) := by decide
  have h3 : Function.Bijective swapBC := by decide
  have h4 : Function.Bijective swapAC := by decide
  have h5 : Function.Bijective swapAB := by decide
  unfold permAvg
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, trace_submatrix_perm h1, trace_submatrix_perm h2, trace_submatrix_perm h3,
    trace_submatrix_perm h4, trace_submatrix_perm h5]
  simp only [Complex.real_smul]
  push_cast
  ring

/-- **`eq:ppt3-asymmetry-upper`.**  For a fully-PPT state `ρ`, `D(ρ, BS) ≤ ½‖ρ - 𝒮(ρ)‖₁`, where
`𝒮 = permAvg` is the permutation average (biseparable by `isBiseparable_permAvg`). -/
theorem bsDist_le_permAvg {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hA : (ptA ρ).PosSemidef) (hB : (ptB ρ).PosSemidef) (hC : (ptC ρ).PosSemidef)
    (ht : ρ.trace = 1) : bsDist ρ ≤ (1 / 2) * tnorm (ρ - permAvg ρ) := by
  have := bsDist_le (ρ := ρ) (isBiseparable_permAvg hρ hA hB hC) (by rw [trace_permAvg, ht])
  simpa [traceDist] using this

/-- **`eq:ppt3-pinch`, Hermitian form.**  For a state `ρ` that is PPT at `A|BC`,
`D(ρ, BS) ≤ ¼‖ρ - S_BC ρ S_BC‖₁`; the state `(ρ + S_BC ρ S_BC)/2` is the pinching with the triplet and
singlet projectors of `BC` (`isBiseparable_swap_average`), and `¼‖ρ - S_BC ρ S_BC‖₁ = ‖P₃ ρ P₁‖₁`
for the (non-Hermitian) trace norm of the paper, an identity that is not formalised here. -/
theorem bsDist_le_swap_average {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptA ρ).PosSemidef) (ht : ρ.trace = 1) :
    bsDist ρ ≤ (1 / 4) * tnorm (ρ - ρ.submatrix swapBC swapBC) := by
  have h3 : Function.Bijective swapBC := by decide
  have hb := isBiseparable_swap_average hρ hT
  have htr : ((1 / 2 : ℝ) • (ρ + ρ.submatrix swapBC swapBC)).trace = 1 := by
    rw [Matrix.trace_smul, Matrix.trace_add, trace_submatrix_perm h3, ht]
    simp only [Complex.real_smul]; push_cast; ring
  have hle := bsDist_le (ρ := ρ) hb htr
  have hD : (ρ - ρ.submatrix swapBC swapBC).IsHermitian := hρ.1.sub (hρ.1.submatrix _)
  have e : ρ - (1 / 2 : ℝ) • (ρ + ρ.submatrix swapBC swapBC) =
      (1 / 2 : ℝ) • (ρ - ρ.submatrix swapBC swapBC) := by module
  unfold traceDist at hle
  rw [e, tnorm_real_smul hD (by norm_num)] at hle
  linarith

/-- info: 'FormalResearch.PPTThreeQubit.bsDist_le_permAvg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsDist_le_permAvg

/-- info: 'FormalResearch.PPTThreeQubit.bsDist_le_swap_average' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsDist_le_swap_average

/-- For a cyclically invariant `ρ`, the conjugations by the three transpositions agree. -/
theorem submatrix_swapAC_of_cyclic {ρ : Matrix (Fin 8) (Fin 8) ℂ}
    (hc : ∀ i j, ρ (cycShift i) (cycShift j) = ρ i j) :
    ρ.submatrix swapAC swapAC = ρ.submatrix swapBC swapBC := by
  have e : ∀ i, swapAC i = cycShift (swapBC i) := by decide
  ext i j
  simp only [submatrix_apply, e, hc]

theorem submatrix_swapAB_of_cyclic {ρ : Matrix (Fin 8) (Fin 8) ℂ}
    (hc : ∀ i j, ρ (cycShift i) (cycShift j) = ρ i j) :
    ρ.submatrix swapAB swapAB = ρ.submatrix swapBC swapBC := by
  have e : ∀ i, swapAB i = cycShift (cycShift (swapBC i)) := by decide
  ext i j
  simp only [submatrix_apply, e, hc]

/-- **`eq:ppt3-asymmetry-upper`, cyclic case.**  If `ρ` is cyclically invariant and PPT at `A|BC`, then
for the transposition `S = S_BC` (equally `S_AC`, `S_AB`, by `submatrix_swapAC_of_cyclic`,
`submatrix_swapAB_of_cyclic`), `D(ρ, BS) ≤ ¼‖ρ - S ρ S‖₁`.  This is `bsDist_le_swap_average`. -/
theorem bsDist_le_cyclic {ρ : Matrix (Fin 8) (Fin 8) ℂ} (hρ : ρ.PosSemidef)
    (hT : (ptA ρ).PosSemidef) (ht : ρ.trace = 1) :
    (∀ i j, ρ (cycShift i) (cycShift j) = ρ i j) →
      bsDist ρ ≤ (1 / 4) * tnorm (ρ - ρ.submatrix swapAC swapAC) ∧
      bsDist ρ ≤ (1 / 4) * tnorm (ρ - ρ.submatrix swapAB swapAB) := by
  intro hc
  rw [submatrix_swapAC_of_cyclic hc, submatrix_swapAB_of_cyclic hc]
  exact ⟨bsDist_le_swap_average hρ hT ht, bsDist_le_swap_average hρ hT ht⟩

/-- info: 'FormalResearch.PPTThreeQubit.bsDist_le_cyclic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bsDist_le_cyclic

end

end FormalResearch.PPTThreeQubit

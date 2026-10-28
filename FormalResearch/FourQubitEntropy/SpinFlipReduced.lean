import FormalResearch.FourQubitEntropy.SpinFlipPurity

/-!
# The swap-form purity equals `tr ρ_S²` for the explicit partial trace

`purC ψ S` of `SpinFlipPurity.lean` is defined by the two-copy swap expectation `⟨ψ⊗ψ|F_S|ψ⊗ψ⟩`.  Here
`rdm ψ S = Tr_{Sᶜ} |ψ⟩⟨ψ|` is the reduced density matrix on `S` (rows and columns indexed by
configurations of the qubits in `S`), and `purC_eq_trace`/`purity_eq_trace` show
`purC ψ S = tr (ρ_S²)`.  Hence every purity statement of `SpinFlipPurity`, `SpinFlipOmega` and
`SpinFlipDouble` is a statement about the honest reduced states.  Claim class: **proved**.
-/

open scoped ComplexConjugate BigOperators
open FormalResearch.FrameFree.NQubit

namespace FormalResearch.FourQubitEntropy.SpinFlip

variable {n : ℕ}

/-- Configurations of the qubits in `S`. -/
abbrev CfgOn (S : Finset (Fin n)) := {i // i ∈ S} → Fin 2
/-- Configurations of the qubits outside `S`. -/
abbrev CfgOff (S : Finset (Fin n)) := {i // i ∉ S} → Fin 2

/-- Glue a configuration on `S` and one off `S` into a configuration of all `n` qubits. -/
def glue (S : Finset (Fin n)) (x : CfgOn S) (t : CfgOff S) : Cfg n :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else t ⟨i, h⟩

/-- `Cfg n ≃ (configs on S) × (configs off S)`. -/
def glueEquiv (S : Finset (Fin n)) : CfgOn S × CfgOff S ≃ Cfg n where
  toFun p := glue S p.1 p.2
  invFun X := (fun i => X i.1, fun i => X i.1)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · funext ⟨i, hi⟩; simp [glue, hi]
    · funext ⟨i, hi⟩; simp [glue, hi]
  right_inv X := by
    funext i; by_cases h : i ∈ S <;> simp [glue, h]

/-- The reduced density matrix `ρ_S = Tr_{Sᶜ} |ψ⟩⟨ψ|`. -/
noncomputable def rdm (ψ : Ψ n) (S : Finset (Fin n)) : Matrix (CfgOn S) (CfgOn S) ℂ :=
  fun x y => ∑ t : CfgOff S, ψ (glue S x t) * conj (ψ (glue S y t))

theorem sw_glue (S : Finset (Fin n)) (x y : CfgOn S) (t t' : CfgOff S) :
    sw S (glue S x t) (glue S y t') = glue S y t := by
  funext i; by_cases h : i ∈ S <;> simp [sw, glue, h]

theorem sum_cfg_glue (S : Finset (Fin n)) (F : Cfg n → ℂ) :
    ∑ X, F X = ∑ x : CfgOn S, ∑ t : CfgOff S, F (glue S x t) := by
  rw [← (glueEquiv S).sum_comp, Fintype.sum_prod_type]; rfl

/-- **`tr ρ_S²` for the explicit partial trace equals the swap form.** -/
theorem purC_eq_trace (ψ : Ψ n) (S : Finset (Fin n)) :
    purC ψ S = ((rdm ψ S) * (rdm ψ S)).trace := by
  unfold purC
  simp only [sum_cfg_glue S, sw_glue]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, rdm, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
  ring

theorem purity_eq_trace (ψ : Ψ n) (S : Finset (Fin n)) :
    (purity ψ S : ℂ) = ((rdm ψ S) * (rdm ψ S)).trace := by
  rw [← purC_eq]; exact purC_eq_trace ψ S

/-- `tr ρ_S² = 2^{-|S|} Σ_{supp P ⊆ S} ⟨P⟩²` for the explicit reduced density matrix
(`lem:odd-sector`, first formula; `Σ` over Pauli words supported in `S`). -/
theorem trace_rdm_sq (ψ : Ψ n) (S : Finset (Fin n)) :
    ((rdm ψ S) * (rdm ψ S)).trace = (((∑ a ∈ wsupp S, pw ψ a) / 2 ^ S.card : ℝ) : ℂ) := by
  rw [← purC_eq_trace, purC_eq_real]

end FormalResearch.FourQubitEntropy.SpinFlip

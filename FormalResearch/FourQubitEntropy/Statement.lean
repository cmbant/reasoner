import Mathlib

/-!
# Statements about a four-qubit vector

Definitions in ordinary Mathlib terms: reduced matrices, the moment quantities `P`, `T`,
`F = 17 n P - 12 T - 12 n³`, and the squared unnormalised Bloch vectors `W₁`.

A vector is `ψ : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ`, `ψ a b c d` being the amplitude of
`|a b c d⟩` on qubits `1,2,3,4`.
-/

open scoped ComplexConjugate

namespace FormalResearch.FourQubitEntropy

/-- A (not necessarily normalised) four-qubit vector. -/
abbrev Psi := Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ

/-- Two-qubit matrices, rows and columns indexed by pairs of qubit values. -/
abbrev Mat4 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- `n = ‖ψ‖²`. -/
noncomputable def normSqPsi (ψ : Psi) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, Complex.normSq (ψ a b c d)

/-- Unnormalised reduced matrix `tr_{34} |ψ⟩⟨ψ|` on qubits `1,2`. -/
noncomputable def red12 (ψ : Psi) : Mat4 :=
  Matrix.of fun i j => ∑ c, ∑ d, ψ i.1 i.2 c d * conj (ψ j.1 j.2 c d)

/-- Unnormalised reduced matrix on qubits `1,3`. -/
noncomputable def red13 (ψ : Psi) : Mat4 :=
  Matrix.of fun i j => ∑ b, ∑ d, ψ i.1 b i.2 d * conj (ψ j.1 b j.2 d)

/-- Unnormalised reduced matrix on qubits `1,4`. -/
noncomputable def red14 (ψ : Psi) : Mat4 :=
  Matrix.of fun i j => ∑ b, ∑ c, ψ i.1 b c i.2 * conj (ψ j.1 b c j.2)

/-- `P = Σ_j tr R_{1j}²`. -/
noncomputable def purity (ψ : Psi) : ℝ :=
  (Matrix.trace (red12 ψ * red12 ψ)).re + (Matrix.trace (red13 ψ * red13 ψ)).re
    + (Matrix.trace (red14 ψ * red14 ψ)).re

/-- `T = Σ_j tr R_{1j}³`. -/
noncomputable def cubicMoment (ψ : Psi) : ℝ :=
  (Matrix.trace (red12 ψ * red12 ψ * red12 ψ)).re
    + (Matrix.trace (red13 ψ * red13 ψ * red13 ψ)).re
    + (Matrix.trace (red14 ψ * red14 ψ * red14 ψ)).re

/-- The sextic `F = 17 n P - 12 T - 12 n³`. -/
noncomputable def sexticF (ψ : Psi) : ℝ :=
  17 * normSqPsi ψ * purity ψ - 12 * cubicMoment ψ - 12 * normSqPsi ψ ^ 3

/-! ### Bloch vectors -/

/-- The Pauli matrices. -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def pauliY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The one-qubit operator `σ` acting on qubit `i` (`0,1,2,3` for qubits `1,2,3,4`). -/
def actOn (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Psi) : Psi := fun a b c d =>
  match i with
  | 0 => ∑ t, σ a t * ψ t b c d
  | 1 => ∑ t, σ b t * ψ a t c d
  | 2 => ∑ t, σ c t * ψ a b t d
  | 3 => ∑ t, σ d t * ψ a b c t

/-- `⟨ψ|σ^{(i)}|ψ⟩`. -/
noncomputable def expectation (i : Fin 4) (σ : Matrix (Fin 2) (Fin 2) ℂ) (ψ : Psi) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, conj (ψ a b c d) * actOn i σ ψ a b c d

/-- `W₁ = Σ_i Σ_{σ ∈ {X,Y,Z}} ⟨ψ|σ^{(i)}|ψ⟩²`, the squared unnormalised Bloch vectors. -/
noncomputable def blochSq (ψ : Psi) : ℝ :=
  ∑ i : Fin 4, ((expectation i pauliX ψ).re ^ 2 + (expectation i pauliY ψ).re ^ 2
    + (expectation i pauliZ ψ).re ^ 2)

end FormalResearch.FourQubitEntropy

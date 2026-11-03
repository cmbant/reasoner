module

public import ThreeCopyQutritWerner.Imports

@[expose] public section


/-!
# Three-copy qutrit Werner states: model definitions

Definitions for the manuscript formalized here (see `paper/README.md`), in the qutrit case
`d = 3`, three copies.

This module contains definitions only. `Challenge.lean` repeats them verbatim (from
`noncomputable section` on).

Conventions (manuscript Section 2):

* a three-site operator is a complex matrix indexed by `a × b × c`; it need not
  be Hermitian or normal;
* partial traces are unnormalized;
* `frobSq` is the squared Frobenius norm;
* the Werner state is `ρ_{d,α} = (I - α F_d) / (d (d - α))` with
  `F_d (u ⊗ v) = v ⊗ u`;
* the partial transpose acts on the second tensor factor;
* a test vector on `A₁A₂A₃ | B₁B₂B₃` is the row-first vectorization of a matrix
  with rows indexed by Alice's three sites and columns by Bob's.
-/

noncomputable section

open scoped BigOperators ComplexOrder

namespace ThreeCopyQutritWerner

/-- Squared Frobenius (Hilbert–Schmidt) norm `‖M‖_F² = ∑ᵢⱼ |Mᵢⱼ|²`. -/
def frobSq {m n : Type*} [Fintype m] [Fintype n] (M : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

section Invariants

variable {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]

/-- Unnormalized partial trace over site 1. -/
def ptrace₁ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (b × c) (b × c) ℂ :=
  fun y y' => ∑ i, C (i, y) (i, y')

/-- Unnormalized partial trace over site 2. -/
def ptrace₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × c) (a × c) ℂ :=
  fun x x' => ∑ j, C (x.1, j, x.2) (x'.1, j, x'.2)

/-- Unnormalized partial trace over site 3. -/
def ptrace₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix (a × b) (a × b) ℂ :=
  fun x x' => ∑ k, C (x.1, x.2, k) (x'.1, x'.2, k)

/-- Unnormalized partial trace over sites 1 and 2. -/
def ptrace₁₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix c c ℂ :=
  fun k k' => ∑ i, ∑ j, C (i, j, k) (i, j, k')

/-- Unnormalized partial trace over sites 1 and 3. -/
def ptrace₁₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix b b ℂ :=
  fun j j' => ∑ i, ∑ k, C (i, j, k) (i, j', k)

/-- Unnormalized partial trace over sites 2 and 3. -/
def ptrace₂₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : Matrix a a ℂ :=
  fun i i' => ∑ j, ∑ k, C (i, j, k) (i', j, k)

/-- `N = ‖C‖_F²` (manuscript eq. (2)). -/
def invN (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := frobSq C

/-- `A = ∑ᵢ ‖Trᵢ C‖_F²` (manuscript eq. (2)). -/
def invA (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  frobSq (ptrace₁ C) + frobSq (ptrace₂ C) + frobSq (ptrace₃ C)

/-- `B = ∑_{i<j} ‖Tr_{ij} C‖_F²` (manuscript eq. (2)). -/
def invB (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  frobSq (ptrace₁₂ C) + frobSq (ptrace₁₃ C) + frobSq (ptrace₂₃ C)

/-- `T₀ = |Tr C|²` (manuscript eq. (2)). -/
def invT (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := Complex.normSq C.trace

/-- `q_α(C) = N - α A + α² B - α³ T₀` (manuscript eq. (3)). -/
def energy (α : ℝ) (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - α * invA C + α ^ 2 * invB C - α ^ 3 * invT C

/-- The endpoint form `q(C) = q_{1/2}(C)` (manuscript eq. (3)). -/
def endpointEnergy (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := energy (1 / 2) C

/-- `R(C) = N - T₀ / 2` (manuscript eq. (7)). -/
def formR (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ := invN C - invT C / 2

/-- `S(C) = N - (A + B) / 6 + T₀ / 4` (manuscript eq. (7)). -/
def formS (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (invA C + invB C) / 6 + invT C / 4

/-- Grouped two-factor form at the cut `1 | 23` (manuscript eq. (8), `i = 1`). -/
def cutForm₁ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (frobSq (ptrace₁ C) + frobSq (ptrace₂₃ C)) / 2 + invT C / 4

/-- Grouped two-factor form at the cut `2 | 13` (manuscript eq. (8), `i = 2`). -/
def cutForm₂ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (frobSq (ptrace₂ C) + frobSq (ptrace₁₃ C)) / 2 + invT C / 4

/-- Grouped two-factor form at the cut `3 | 12` (manuscript eq. (8), `i = 3`). -/
def cutForm₃ (C : Matrix (a × b × c) (a × b × c) ℂ) : ℝ :=
  invN C - (frobSq (ptrace₃ C) + frobSq (ptrace₁₂ C)) / 2 + invT C / 4

/-- Three-site tensor product `M₁ ⊗ M₂ ⊗ M₃`. -/
def tensor₃ (M₁ : Matrix a a ℂ) (M₂ : Matrix b b ℂ) (M₃ : Matrix c c ℂ) :
    Matrix (a × b × c) (a × b × c) ℂ :=
  fun x y => M₁ x.1 y.1 * M₂ x.2.1 y.2.1 * M₃ x.2.2 y.2.2

end Invariants

/-- The sharp curve `f(α) = (1 - 2α)(1 - α)²` (manuscript eq. (4)). -/
def sharpCurve (α : ℝ) : ℝ := (1 - 2 * α) * (1 - α) ^ 2

section Werner

/-- The flip operator `F (u ⊗ v) = v ⊗ u` on two copies of `ℂ^d`. -/
def swapOp (d : Type*) [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- The unnormalized projector `Ω = |Ω⟩⟨Ω|`, where `|Ω⟩ = ∑ⱼ |jj⟩`. -/
def omegaOp (d : Type*) [DecidableEq d] : Matrix (d × d) (d × d) ℂ :=
  fun x y => if x.1 = x.2 ∧ y.1 = y.2 then 1 else 0

/-- Partial transpose on the second tensor factor. -/
def partialTranspose {m n : Type*} (M : Matrix (m × n) (m × n) ℂ) :
    Matrix (m × n) (m × n) ℂ :=
  fun x y => M (x.1, y.2) (y.1, x.2)

/-- The Werner state `ρ_{d,α} = (I - α F_d) / (d (d - α))` (manuscript eq. (1)).
The manuscript's parameter range is `-1 ≤ α ≤ 1`; the definition is total. -/
def werner (d : ℕ) (α : ℝ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (((d : ℂ) * ((d : ℂ) - (α : ℂ)))⁻¹) •
    ((1 : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) - (α : ℂ) • swapOp (Fin d))

/-- Three tensor copies `M ⊗ M ⊗ M` of a bipartite operator on `A ⊗ B`,
regrouped along the cut `A₁A₂A₃ | B₁B₂B₃`. -/
def tripleCopy {m n : Type*} (M : Matrix (m × n) (m × n) ℂ) :
    Matrix ((m × m × m) × (n × n × n)) ((m × m × m) × (n × n × n)) ℂ :=
  fun x y =>
    M (x.1.1, x.2.1) (y.1.1, y.2.1) * M (x.1.2.1, x.2.2.1) (y.1.2.1, y.2.2.1) *
      M (x.1.2.2, x.2.2.2) (y.1.2.2, y.2.2.2)

/-- Row-first vectorization of a coefficient matrix: `(vec C) (x, y) = C x y`. -/
def vec {A B : Type*} (C : Matrix A B ℂ) : A × B → ℂ := fun p => C p.1 p.2

/-- The sesquilinear expectation `⟨ψ, M ψ⟩ = ∑ₓᵧ conj(ψ x) M x y ψ y`. -/
def expectation {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) (ψ : ι → ℂ) : ℂ :=
  ∑ x, ∑ y, star (ψ x) * M x y * ψ y

/-- `ψ` is a sum of at most `r` product vectors across the cut `A | B`,
i.e. it has Schmidt rank at most `r`. -/
def SchmidtRankLE {A B : Type*} (r : ℕ) (ψ : A × B → ℂ) : Prop :=
  ∃ (u : Fin r → A → ℂ) (v : Fin r → B → ℂ), ∀ x y, ψ (x, y) = ∑ k, u k x * v k y

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A bipartite operator has negative partial transpose (is NPT) when its
partial transpose is not positive semidefinite. -/
def IsNPT (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ¬ (partialTranspose ρ).PosSemidef

/-- One-copy Schmidt-rank-two detection: some vector of Schmidt rank at most two has
negative expectation in `ρ^Γ`.  This is the criterion, not the operational notion;
`IsOneCopyFilterDistillable` below is the operational notion, and the two are proved
equivalent for Hermitian `ρ` in `Distillation.lean`. -/
def IsOneCopyRankTwoDetectable (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ ψ : m × n → ℂ, SchmidtRankLE 2 ψ ∧ (expectation (partialTranspose ρ) ψ).re < 0

/-- Three-copy Schmidt-rank-two detection: some vector of Schmidt rank at most two across
`A₁A₂A₃ | B₁B₂B₃` has negative expectation in `(ρ^{⊗3})^Γ`.  This is the criterion;
`IsThreeCopyFilterDistillable` below is the operational notion, proved equivalent for
Hermitian `ρ` in `Distillation.lean`. -/
def IsThreeCopyRankTwoDetectable (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ ψ : (m × m × m) × (n × n × n) → ℂ, SchmidtRankLE 2 ψ ∧
    (expectation (partialTranspose (tripleCopy ρ)) ψ).re < 0

end Werner

section StatementBase

/-! ### Further definitions used by the endpoint statements

Collected here so that the statement base contains definitions only. -/

/-- Two-site tensor product `M ⊗ N`. -/
def tensor₂ {ι κ : Type*} [Fintype ι] [Fintype κ] (M : Matrix ι ι ℂ) (N : Matrix κ κ ℂ) :
    Matrix (ι × κ) (ι × κ) ℂ :=
  fun x y => M x.1 y.1 * N x.2 y.2

/-- Unnormalized partial trace of a two-site operator over its first site. -/
def ptraceL {b c : Type*} [Fintype b] [Fintype c] (X : Matrix (b × c) (b × c) ℂ) :
    Matrix c c ℂ :=
  fun k k' => ∑ j, X (j, k) (j, k')

/-- Unnormalized partial trace of a two-site operator over its second site. -/
def ptraceR {b c : Type*} [Fintype b] [Fintype c] (X : Matrix (b × c) (b × c) ℂ) :
    Matrix b b ℂ :=
  fun j j' => ∑ k, X (j, k) (j', k)

/-- The rank-one operator `|χ⟩⟨η|`. -/
def ketBra {ι : Type*} (χ η : ι → ℂ) : Matrix ι ι ℂ :=
  fun y y' => χ y * (starRingEnd ℂ) (η y')

/-- The inner product `⟨u, v⟩ = ∑ₓ conj(u x) v x`, conjugate-linear in the first slot. -/
def braket {ι : Type*} [Fintype ι] (u v : ι → ℂ) : ℂ :=
  ∑ x, (starRingEnd ℂ) (u x) * v x

/-- The squared norm `‖u‖² = ∑ₓ |u x|²`. -/
def vecNormSq {ι : Type*} [Fintype ι] (u : ι → ℂ) : ℝ :=
  ∑ x, Complex.normSq (u x)

/-- The locally filtered operator `(A ⊗ B) ρ (A ⊗ B)†` on two qubits. -/
def localFilter {m n : Type*} [Fintype m] [Fintype n] (A : Matrix (Fin 2) m ℂ)
    (B : Matrix (Fin 2) n ℂ) (ρ : Matrix (m × n) (m × n) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => ∑ p : m × n, ∑ q : m × n,
    A x.1 p.1 * B x.2 p.2 * ρ p q * star (A y.1 q.1) * star (B y.2 q.2)

/-- One-copy distillability, operational form: some local filter onto two
qubits yields an operator whose partial transpose is not positive semidefinite. -/
def IsOneCopyFilterDistillable {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ (A : Matrix (Fin 2) m ℂ) (B : Matrix (Fin 2) n ℂ), IsNPT (localFilter A B ρ)

/-- Three-copy distillability, operational form: some local filter of `ρ^{⊗3}`
across `A₁A₂A₃ | B₁B₂B₃` onto two qubits yields an NPT operator. -/
def IsThreeCopyFilterDistillable {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ (A : Matrix (Fin 2) (m × m × m) ℂ) (B : Matrix (Fin 2) (n × n × n) ℂ),
    IsNPT (localFilter A B (tripleCopy ρ))

/-- The shape of manuscript eq. (5) up to a permutation of the sites:
`C = z (P_E ⊗ |u⟩⟨u| ⊗ |v⟩⟨v|)` with `P_E = |f₁⟩⟨f₁| + |f₂⟩⟨f₂|` for an orthonormal pair,
unit vectors `u`, `v`, and `|z|² = 1/2` (that is, `z = e^{iθ}/√2`). -/
def IsInteriorMinimizerShape {a b c : Type*} [Fintype a] [Fintype b] [Fintype c]
    (C : Matrix (a × b × c) (a × b × c) ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 / 2 ∧
    ((∃ (f₁ f₂ : a → ℂ) (u : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        C = z • tensor₃ (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra u u) (ketBra v v)) ∨
      (∃ (u : a → ℂ) (f₁ f₂ : b → ℂ) (v : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        C = z • tensor₃ (ketBra u u) (ketBra f₁ f₁ + ketBra f₂ f₂) (ketBra v v)) ∨
      (∃ (u : a → ℂ) (v : b → ℂ) (f₁ f₂ : c → ℂ), vecNormSq f₁ = 1 ∧ vecNormSq f₂ = 1 ∧
        braket f₁ f₂ = 0 ∧ vecNormSq u = 1 ∧ vecNormSq v = 1 ∧
        C = z • tensor₃ (ketBra u u) (ketBra v v) (ketBra f₁ f₁ + ketBra f₂ f₂)))

/-- `|00⟩ + |11⟩` (unnormalized); the maximally entangled state is `Φ = (|00⟩ + |11⟩)/√2`. -/
def omegaVec₂ : Fin 2 × Fin 2 → ℂ := fun x => if x.1 = x.2 then 1 else 0

/-- `Re ⟨Φ, σ Φ⟩` for `Φ = (|00⟩ + |11⟩)/√2`: the overlap of a two-qubit operator with the
maximally entangled state (real for Hermitian `σ`). -/
def maxEntOverlap (σ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) : ℝ :=
  (expectation σ omegaVec₂).re / 2

/-- The output `Σ_k (A_k ⊗ B_k) ρ^{⊗3} (A_k ⊗ B_k)†` of a separable operation on three
copies of `ρ`, with values in two-qubit operators. -/
def sepOutput {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] {K : ℕ}
    (A : Fin K → Matrix (Fin 2) (m × m × m) ℂ) (B : Fin K → Matrix (Fin 2) (n × n × n) ℂ)
    (ρ : Matrix (m × n) (m × n) ℂ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ k, localFilter (A k) (B k) (tripleCopy ρ)

/-- The qutrit endpoint inequality, manuscript Theorem 2.1 at `d = 3`, `α = 1/2`:
`q(C) ≥ 0` for every complex `27 × 27` matrix of rank at most two (claim T2.1a). -/
def QutritEndpointInequality : Prop :=
  ∀ C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ,
    C.rank ≤ 2 → 0 ≤ endpointEnergy C

open scoped Kronecker in
/-- A bipartite operator is separable when it is a finite nonnegative combination of tensor
products of positive semidefinite operators (used for the `d = 2` remark on Theorem 2.1). -/
def IsBipartiteSeparable {m n : Type*} [Fintype m] [Fintype n]
    (ρ : Matrix (m × n) (m × n) ℂ) : Prop :=
  ∃ (K : ℕ) (p : Fin K → ℝ) (A : Fin K → Matrix m m ℂ) (B : Fin K → Matrix n n ℂ),
    (∀ k, 0 ≤ p k) ∧ (∀ k, (A k).PosSemidef) ∧ (∀ k, (B k).PosSemidef) ∧
      ρ = ∑ k, ((p k : ℝ) : ℂ) • (A k ⊗ₖ B k)

open scoped Kronecker Matrix in
/-- `embedPair J ρ = (J ⊗ J) ρ (J ⊗ J)†` for `J : ℂ³ → ℂᵈ` (the embedding of eq. (27)). -/
def embedPair {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ)
    (ρ : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (J ⊗ₖ J) * ρ * (J ⊗ₖ J)ᴴ

/-- `noisyFamily J p = p (J ⊗ J) ρ_{3,1/2} (J ⊗ J)† + (1 - p) I/d²`, the family of eq. (27) with
the qutrit seed (manuscript Corollary 6.2). -/
def noisyFamily {d : ℕ} (J : Matrix (Fin d) (Fin 3) ℂ) (p : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (p : ℂ) • embedPair J (werner 3 (1 / 2)) + (((1 - p) / (d : ℝ) ^ 2 : ℝ) : ℂ) • 1

end StatementBase

section StatementBaseRevision4

/-! Definitions for the families of Theorem 5.1 and for the certificate soundness argument of
Section 4.1. -/

open scoped Matrix Kronecker

/-- The skew matrix `[[0, 1], [-1, 0]]` of Theorem 5.1, written `ε` here. -/
def epsMat : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `J₂ = ε ⊗ ε`. -/
def epsJ₂ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := epsMat ⊗ₖ epsMat

/-- `J₃ = ε ⊗ ε ⊗ ε`. -/
def epsJ₃ : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  epsMat ⊗ₖ (epsMat ⊗ₖ epsMat)

/-- `B₂(U) = U ε Uᵀ J₂⁻¹ / √2` for `U : ℂ² → (ℂ²)^{⊗2}` (plain transpose). -/
def binaryB₂ (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ * epsJ₂⁻¹)

/-- `B₃(U) = U ε Uᵀ J₃⁻¹ / √2` for `U : ℂ² → (ℂ²)^{⊗3}` (plain transpose). -/
def binaryB₃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2 × Fin 2 × Fin 2) ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (U * epsMat * Uᵀ * epsJ₃⁻¹)

/-- Family II: `|a⟩⟨b| ⊗ V B₂(U) V†` with `V = V₂ ⊗ V₃` (sites 2, 3). -/
def familyII (a b : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  tensor₂ (ketBra a b) ((V₂ ⊗ₖ V₃) * binaryB₂ U * (V₂ ⊗ₖ V₃)ᴴ)

/-- Family III: `V B₃(U) V†` with `V = V₁ ⊗ V₂ ⊗ V₃`. -/
def familyIII (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ)
    (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ) :
    Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  (V₁ ⊗ₖ (V₂ ⊗ₖ V₃)) * binaryB₃ U * (V₁ ⊗ₖ (V₂ ⊗ₖ V₃))ᴴ

/-- `(j, i, k) ↦ (i, j, k)`: the index equivalence that puts site 2 in front. -/
def siteEquiv₂ {a b c : Type*} : b × a × c ≃ a × b × c where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun y := (y.2.1, y.1, y.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- `(k, i, j) ↦ (i, j, k)`: the index equivalence that puts site 3 in front. -/
def siteEquiv₃ {a b c : Type*} : c × a × b ≃ a × b × c where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun y := (y.2.2, y.1, y.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Family I with site 1 active: `(P_E/√2) ⊗ |χ⟩⟨η|`. -/
def familyIMat (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ) :
    Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ :=
  tensor₂ ((((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (ketBra f₁ f₁ + ketBra f₂ f₂)) (ketBra χ η)

/-- The union of Theorem 5.1: families I and II with the active site at any of the three
positions, family III, each multiplied by a unit phase.  (Family III is closed under site
permutations through its parameters; the other site permutations of families I and II are
absorbed by `χ, η`, resp. by `U`, `V₂`, `V₃`.) -/
abbrev IsQutritZeroFamilyMember
    (C : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) : Prop :=
  ∃ z : ℂ, Complex.normSq z = 1 ∧
    ∃ D : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ, C = z • D ∧
      ((∃ (f₁ f₂ : Fin 3 → ℂ) (χ η : Fin 3 × Fin 3 → ℂ), vecNormSq f₁ = 1 ∧
          vecNormSq f₂ = 1 ∧ braket f₁ f₂ = 0 ∧ vecNormSq χ = 1 ∧ vecNormSq η = 1 ∧
          (D = familyIMat f₁ f₂ χ η ∨
            D = (familyIMat f₁ f₂ χ η).submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
            D = (familyIMat f₁ f₂ χ η).submatrix siteEquiv₃.symm siteEquiv₃.symm)) ∨
        (∃ (a b : Fin 3 → ℂ) (U : Matrix (Fin 2 × Fin 2) (Fin 2) ℂ)
            (V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ), vecNormSq a = 1 ∧ vecNormSq b = 1 ∧
          Uᴴ * U = 1 ∧ V₂ᴴ * V₂ = 1 ∧ V₃ᴴ * V₃ = 1 ∧
          (D = familyII a b U V₂ V₃ ∨
            D = (familyII a b U V₂ V₃).submatrix siteEquiv₂.symm siteEquiv₂.symm ∨
            D = (familyII a b U V₂ V₃).submatrix siteEquiv₃.symm siteEquiv₃.symm)) ∨
        (∃ (U : Matrix (Fin 2 × Fin 2 × Fin 2) (Fin 2) ℂ) (V₁ V₂ V₃ : Matrix (Fin 3) (Fin 2) ℂ),
          Uᴴ * U = 1 ∧ V₁ᴴ * V₁ = 1 ∧ V₂ᴴ * V₂ = 1 ∧ V₃ᴴ * V₃ = 1 ∧
          D = familyIII U V₁ V₂ V₃))

/-- The source bivector `p = (x ⊗ y - y ⊗ x)/√2` of `X = [x, y]`, as a skew matrix. -/
def bivecMat {n : Type*} [Fintype n] (X : Matrix n (Fin 2) ℂ) : Matrix n n ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • (X * epsMat * Xᵀ)

/-- Transpose of the last two factors of `(r × b) × c` (the manuscript's `Γ₁₂₃₄` when `b` and
`c` are the two minor pairs). -/
def minorTranspose {r b c : Type*} (M : Matrix ((r × b) × c) ((r × b) × c) ℂ) :
    Matrix ((r × b) × c) ((r × b) × c) ℂ :=
  fun x y => M ((x.1.1, y.1.2), y.2) ((y.1.1, x.1.2), x.2)

/-- `T ⊗ I ⊗ I` on `(r × b) × c`: `T` on the first factor, the identity on `b` and `c`. -/
def liftRowCol {r b c : Type*} [DecidableEq b] [DecidableEq c] (T : Matrix r r ℂ) :
    Matrix ((r × b) × c) ((r × b) × c) ℂ :=
  fun x y => T x.1.1 y.1.1 * (1 : Matrix b b ℂ) x.1.2 y.1.2 * (1 : Matrix c c ℂ) x.2 y.2

/-- The six registers `(((row, col), (p₁, p₂)), (p₃, p₄))`, each a copy of `(ℂ³)^{⊗3}` indexed
by `Fin 3 × Fin 3 × Fin 3`. -/
abbrev SixRegisters :=
  (((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3)) ×
    ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))) ×
    ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))

/-- `T = ∏ᵢ (I - Ωᵢ/2)` on `(row, col)`, as `(15/2)³ (ρ_{3,1/2}^{⊗3})^Γ`
(`ρ_{d,α}^Γ = (I - α Ω)/(d (d - α))` and `d (d - α) = 15/2`). -/
def endpointOperator :
    Matrix ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3))
      ((Fin 3 × Fin 3 × Fin 3) × (Fin 3 × Fin 3 × Fin 3)) ℂ :=
  ((15 / 2 : ℂ) ^ 3) • partialTranspose (tripleCopy (werner 3 (1 / 2)))

/-- The feature `z_h = vec C ⊗ p ⊗ p` (`P` is the bivector `p` as a matrix). -/
def featureH (C P : Matrix (Fin 3 × Fin 3 × Fin 3) (Fin 3 × Fin 3 × Fin 3) ℂ) :
    SixRegisters → ℂ :=
  fun x => vec C x.1.1 * vec P x.1.2 * vec P x.2

/-- `T ⊗ I` on the six registers (the identity on the four minor registers). -/
def sixRegisterOperator : Matrix SixRegisters SixRegisters ℂ := liftRowCol endpointOperator

end StatementBaseRevision4

section StatementBaseRevision6

/-! Definitions for the two-factor cut forms of eq. (11). -/

/-- The grouped two-factor form of manuscript eq. (8) for an operator on `L ⊗ R`. -/
def cutForm {L R : Type*} [Fintype L] [Fintype R] (X : Matrix (L × R) (L × R) ℂ) : ℝ :=
  frobSq X - (frobSq (ptraceL X) + frobSq (ptraceR X)) / 2 + Complex.normSq X.trace / 4

/-- `‖P(X)‖² = ‖Tr_L X‖_F² + ‖Tr_R X‖_F²`. -/
def ptraceNormSq {L R : Type*} [Fintype L] [Fintype R] (X : Matrix (L × R) (L × R) ℂ) : ℝ :=
  frobSq (ptraceL X) + frobSq (ptraceR X)

/-- `e(u, v) = ‖u‖²‖v‖² + |⟨v, u⟩|² - ‖P(u v†)‖²`: four times the squared norm of `u ⊗ v` antisymmetrized
in the `L` parts and in the `R` parts of two replicas (Appendix A). -/
def biDefect {L R : Type*} [Fintype L] [Fintype R] (u v : L × R → ℂ) : ℝ :=
  vecNormSq u * vecNormSq v + Complex.normSq (braket v u) - ptraceNormSq (ketBra u v)

end StatementBaseRevision6

end ThreeCopyQutritWerner

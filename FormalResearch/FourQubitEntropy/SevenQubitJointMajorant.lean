import FormalResearch.FourQubitEntropy.SevenQubitEigenCap497Pure

/-!
# `prop:seven-joint-entropy-target`, matrix part (conditional on the scalar majorant AH-6)

Source: `ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_joint.tex`,
`prop:seven-joint-entropy-target` (matrix inequality
`tr f(R) ≤ ∑_{k+l≤5} h_{kl} tr(R^k R̃^l)`), together with the scalar input
`lem:seven-joint-scalar-majorant` (verified interval certificate AH-6).

Entropies are in nats: `f = Real.negMulLog`.

## What is proved and what is assumed

* **Hypothesis (not proved here): `ScalarMajorant H cap`.**  `H(λ,μ) ≥ (f(λ)+f(μ))/2` on
  `[0,cap]²`.  For the paper's explicit degree-five polynomial and `cap = 497/1000` this is the
  interval-certified lemma AH-6 (Arb arithmetic, binary subdivision); it is **not** formalized, and
  nothing in this file depends on the particular coefficients of `H`.
* **Proved (no hypothesis beyond `ScalarMajorant`).**
  * `doubly_stochastic_majorant`: for a doubly stochastic `w`,
    `(∑ f(x_i) + ∑ f(y_j))/2 ≤ ∑_{ij} w_ij H(x_i, y_j)`.
  * `overlap_row_sum`, `overlap_col_sum`: `w_ij = |(U* V)_ij|²` is doubly stochastic for unitary `U,V`.
  * `trace_pow_pow`: `∑_{ij} w_ij x_i^k y_j^l = Re tr(R^k S^l)` for `R = U diag(x) U*`,
    `S = V diag(y) V*` (no commutation of `R`, `S` is used).
  * `entropy_le_polyTrace`: for `H` a polynomial `∑ h_kl λ^k μ^l`,
    `∑ f(x_i) ≤ ∑_{kl} h_kl Re tr(R^k S^l)` whenever `y` is a rearrangement-free "same entropy sum"
    partner of `x` (`∑ f(y_j) = ∑ f(x_i)`), all entries in `[0,cap]`.
  * `entropy_le_polyTrace_herm`: the same for Hermitian PSD `R, S` with the same eigenvalue multiset
    (the abstract form of "`S` is a unitary conjugate of `Rᵀ`"), eigenvalues of `R` at most `cap`
    (the operator-norm bound `‖R‖ ≤ cap` for PSD `R`).
  * `entropy_le_polyTrace_spinFlip`: the concrete three-qubit statement, with `S = spinFlip3 R`
    (`Y^{⊗3} Rᵀ Y^{⊗3}`, `SevenQubitSpectralPair`).  The spin flip is a unitary conjugate of `Rᵀ`
    with the spectrum of `R` (proved in `SevenQubitSpectralPairCore.flip_conj`).
  * `cutEntropy_le_polyTrace` and `meanEntropy3_le_jointP5`: for a seven-qubit unit vector, every
    triple cut with spectrum in `[0,cap]` satisfies `S(ρ_T) ≤ 𝒫(ρ_T)`, and
    `E₃(ψ) ≤ 𝒫₅(ψ) := (1/35) ∑_{|T|=3} 𝒫(ρ_T)`.
* **Not formalized:** the homogenization to a permutation-invariant five-copy moment functional;
  the equality `𝒫₅(φ_s) = E_*` on the seven candidates (`lem:seven-adaptive-joint-spinflip`
  is only partly in `SevenQubitAdaptiveSpinFlip`).
-/

open scoped ComplexConjugate Matrix ComplexOrder
open Finset Real

namespace FormalResearch.FourQubitEntropy.SevenQubitConseq

namespace JointMajorant

open FormalResearch.FourQubitEntropy.SevenQubitSpectralPair
open FormalResearch.FourQubitEntropy.SevenQubitIco

/-! ### The scalar hypothesis -/

/-- **Scalar majorant (hypothesis).**  `H(λ,μ) ≥ (f(λ)+f(μ))/2` on `[0,cap]²`, `f = negMulLog`.
For the paper's explicit degree-five `H` and `cap = 497/1000` this is AH-6, which is an interval
certificate and is not proved in Lean. -/
def ScalarMajorant (H : ℝ → ℝ → ℝ) (cap : ℝ) : Prop :=
  ∀ x y : ℝ, 0 ≤ x → x ≤ cap → 0 ≤ y → y ≤ cap →
    (Real.negMulLog x + Real.negMulLog y) / 2 ≤ H x y

/-- The bivariate polynomial `∑_{(k,l) ∈ K} h_{kl} λ^k μ^l`. -/
def polyH (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (x y : ℝ) : ℝ :=
  ∑ p ∈ K, h p.1 p.2 * x ^ p.1 * y ^ p.2

/-- The index set `{k + l ≤ 5}` of the paper's degree-five polynomial. -/
def degFive : Finset (ℕ × ℕ) := (range 6 ×ˢ range 6).filter fun p => p.1 + p.2 ≤ 5

/-! ### Doubly stochastic averaging -/

section Abstract

variable {ι : Type*} [Fintype ι]

/-- Averaging a pointwise majorant against a doubly stochastic matrix. -/
theorem doubly_stochastic_majorant (H : ℝ → ℝ → ℝ) (w : ι → ι → ℝ) (hw0 : ∀ i j, 0 ≤ w i j)
    (hr : ∀ i, ∑ j, w i j = 1) (hc : ∀ j, ∑ i, w i j = 1) (x y : ι → ℝ)
    (hH : ∀ i j, (Real.negMulLog (x i) + Real.negMulLog (y j)) / 2 ≤ H (x i) (y j)) :
    (∑ i, Real.negMulLog (x i) + ∑ j, Real.negMulLog (y j)) / 2 ≤
      ∑ i, ∑ j, w i j * H (x i) (y j) := by
  have h1 : ∑ i, ∑ j, w i j * ((Real.negMulLog (x i) + Real.negMulLog (y j)) / 2) ≤
      ∑ i, ∑ j, w i j * H (x i) (y j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (hH i j) (hw0 i j)
  have h2 : ∑ i, ∑ j, w i j * ((Real.negMulLog (x i) + Real.negMulLog (y j)) / 2) =
      (∑ i, Real.negMulLog (x i) + ∑ j, Real.negMulLog (y j)) / 2 := by
    have e1 : ∑ i, ∑ j, w i j * (Real.negMulLog (x i) / 2) = ∑ i, Real.negMulLog (x i) / 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_mul, hr i, one_mul]
    have e2 : ∑ i, ∑ j, w i j * (Real.negMulLog (y j) / 2) = ∑ j, Real.negMulLog (y j) / 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul, hc j, one_mul]
    have e3 : ∑ i, ∑ j, w i j * ((Real.negMulLog (x i) + Real.negMulLog (y j)) / 2) =
        ∑ i, ∑ j, w i j * (Real.negMulLog (x i) / 2) +
          ∑ i, ∑ j, w i j * (Real.negMulLog (y j) / 2) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e3, e1, e2, ← Finset.sum_div, ← Finset.sum_div]
    ring
  rw [← h2]; exact h1

/-! ### The overlap weights -/

variable [DecidableEq ι]

/-- Row sums of `|W_ij|²` are `1` when `W W* = 1`. -/
theorem row_sum_of_mul_star {W : Matrix ι ι ℂ} (h : W * star W = 1) (i : ι) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have := congrFun (congrFun h i) i
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def,
    Complex.mul_conj] at this
  exact_mod_cast this

/-- Column sums of `|W_ij|²` are `1` when `W* W = 1`. -/
theorem col_sum_of_star_mul {W : Matrix ι ι ℂ} (h : star W * W = 1) (j : ι) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have := congrFun (congrFun h j) j
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq, Complex.star_def] at this
  have h2 : ∑ i, (Complex.normSq (W i j) : ℂ) = 1 := by
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
  exact_mod_cast h2

/-- `w_ij = |(U* V)_ij|²` has rows summing to `1` when `U* U = 1` and `V V* = 1`. -/
theorem overlap_row_sum {U V : Matrix ι ι ℂ} (hU : star U * U = 1) (hV' : V * star V = 1)
    (i : ι) : ∑ j, Complex.normSq ((star U * V) i j) = 1 := by
  refine row_sum_of_mul_star ?_ i
  rw [StarMul.star_mul, star_star]
  calc star U * V * (star V * U) = star U * (V * star V) * U := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hV', Matrix.mul_one, hU]

/-- `w_ij = |(U* V)_ij|²` has columns summing to `1` when `U U* = 1` and `V* V = 1`. -/
theorem overlap_col_sum {U V : Matrix ι ι ℂ} (hU' : U * star U = 1) (hV : star V * V = 1)
    (j : ι) : ∑ i, Complex.normSq ((star U * V) i j) = 1 := by
  refine col_sum_of_star_mul ?_ j
  rw [StarMul.star_mul, star_star]
  calc star V * U * (star U * V) = star V * (U * star U) * V := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hU', Matrix.mul_one, hV]

/-- Powers of a unitarily diagonalised matrix: `(U diag(x) U*)^k = U diag(x^k) U*`. -/
theorem pow_factor {U : Matrix ι ι ℂ} (hU : star U * U = 1) (hU' : U * star U = 1) (x : ι → ℝ)
    (k : ℕ) :
    (U * Matrix.diagonal (fun i => (x i : ℂ)) * star U) ^ k =
      U * Matrix.diagonal (fun i => ((x i ^ k : ℝ) : ℂ)) * star U := by
  induction k with
  | zero =>
    simp only [pow_zero, Complex.ofReal_one]
    rw [show (Matrix.diagonal fun _ : ι => (1 : ℂ)) = 1 from Matrix.diagonal_one,
      Matrix.mul_one, hU']
  | succ k ih =>
    rw [pow_succ, ih]
    calc U * Matrix.diagonal (fun i => ((x i ^ k : ℝ) : ℂ)) * star U *
          (U * Matrix.diagonal (fun i => (x i : ℂ)) * star U)
        = U * (Matrix.diagonal (fun i => ((x i ^ k : ℝ) : ℂ)) * (star U * U) *
            Matrix.diagonal (fun i => (x i : ℂ))) * star U := by simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal (fun i => ((x i ^ (k + 1) : ℝ) : ℂ)) * star U := by
        rw [hU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]
        congr 2
        ext i
        simp [pow_succ]

/-- **Joint trace moments.**  For `R = U diag(x) U*` and `S = V diag(y) V*` with `U`, `V` unitary,
`∑_{ij} |(U*V)_ij|² x_i^k y_j^l = Re tr(R^k S^l)` (indeed `tr(R^k S^l)` is real).  No commutation of
`R` and `S` is used. -/
theorem trace_pow_pow {U V : Matrix ι ι ℂ} (hU : star U * U = 1) (hU' : U * star U = 1)
    (hV : star V * V = 1) (hV' : V * star V = 1) (x y : ι → ℝ) (k l : ℕ) :
    ((U * Matrix.diagonal (fun i => (x i : ℂ)) * star U) ^ k *
        (V * Matrix.diagonal (fun i => (y i : ℂ)) * star V) ^ l).trace =
      ((∑ i, ∑ j, x i ^ k * y j ^ l * Complex.normSq ((star U * V) i j) : ℝ) : ℂ) := by
  rw [pow_factor hU hU' x k, pow_factor hV hV' y l]
  exact trace_form U V (fun i => x i ^ k) (fun j => y j ^ l)

/-- **Generic joint majorant, spectral form.**  For unitaries `U, V` and spectra `x, y` in `[0,cap]`
with the same entropy sum, a scalar majorant `H` gives
`∑ f(x_i) ≤ ∑_{ij} |(U*V)_ij|² H(x_i, y_j)`. -/
theorem entropy_le_joint_sum (H : ℝ → ℝ → ℝ) (cap : ℝ) (hH : ScalarMajorant H cap)
    {U V : Matrix ι ι ℂ} (hU : star U * U = 1) (hU' : U * star U = 1)
    (hV : star V * V = 1) (hV' : V * star V = 1) (x y : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxc : ∀ i, x i ≤ cap) (hy0 : ∀ j, 0 ≤ y j) (hyc : ∀ j, y j ≤ cap)
    (hsum : ∑ j, Real.negMulLog (y j) = ∑ i, Real.negMulLog (x i)) :
    ∑ i, Real.negMulLog (x i) ≤
      ∑ i, ∑ j, Complex.normSq ((star U * V) i j) * H (x i) (y j) := by
  have := doubly_stochastic_majorant H (fun i j => Complex.normSq ((star U * V) i j))
    (fun i j => Complex.normSq_nonneg _) (overlap_row_sum hU hV') (overlap_col_sum hU' hV) x y
    (fun i j => hH _ _ (hx0 i) (hxc i) (hy0 j) (hyc j))
  rw [hsum] at this
  linarith

/-- **Joint majorant, polynomial form (matrix part of `prop:seven-joint-entropy-target`).**
For `R = U diag(x) U*`, `S = V diag(y) V*` (unitary `U, V`), spectra in `[0,cap]` with the same
entropy sum, and `ScalarMajorant (polyH K h) cap`,
`∑ f(x_i) ≤ ∑_{(k,l)∈K} h_{kl} Re tr(R^k S^l)`. -/
theorem entropy_le_polyTrace (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (cap : ℝ)
    (hH : ScalarMajorant (polyH K h) cap)
    {U V : Matrix ι ι ℂ} (hU : star U * U = 1) (hU' : U * star U = 1)
    (hV : star V * V = 1) (hV' : V * star V = 1) (x y : ι → ℝ)
    (hx0 : ∀ i, 0 ≤ x i) (hxc : ∀ i, x i ≤ cap) (hy0 : ∀ j, 0 ≤ y j) (hyc : ∀ j, y j ≤ cap)
    (hsum : ∑ j, Real.negMulLog (y j) = ∑ i, Real.negMulLog (x i)) :
    ∑ i, Real.negMulLog (x i) ≤
      ∑ p ∈ K, h p.1 p.2 *
        ((U * Matrix.diagonal (fun i => (x i : ℂ)) * star U) ^ p.1 *
          (V * Matrix.diagonal (fun i => (y i : ℂ)) * star V) ^ p.2).trace.re := by
  refine (entropy_le_joint_sum (polyH K h) cap hH hU hU' hV hV' x y hx0 hxc hy0 hyc hsum).trans
    (le_of_eq ?_)
  have e : ∀ p : ℕ × ℕ,
      (((U * Matrix.diagonal (fun i => (x i : ℂ)) * star U) ^ p.1 *
          (V * Matrix.diagonal (fun i => (y i : ℂ)) * star V) ^ p.2).trace).re =
        ∑ i, ∑ j, x i ^ p.1 * y j ^ p.2 * Complex.normSq ((star U * V) i j) := fun p => by
    rw [trace_pow_pow hU hU' hV hV' x y p.1 p.2, Complex.ofReal_re]
  have e2 : ∀ i j : ι, Complex.normSq ((star U * V) i j) *
      (∑ p ∈ K, h p.1 p.2 * x i ^ p.1 * y j ^ p.2) =
      ∑ p ∈ K, h p.1 p.2 * (x i ^ p.1 * y j ^ p.2 * Complex.normSq ((star U * V) i j)) :=
    fun i j => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
  simp only [e, polyH, e2, Finset.mul_sum]
  calc ∑ i, ∑ j, ∑ p ∈ K, h p.1 p.2 * (x i ^ p.1 * y j ^ p.2 * Complex.normSq ((star U * V) i j))
      = ∑ i, ∑ p ∈ K, ∑ j, h p.1 p.2 * (x i ^ p.1 * y j ^ p.2 *
          Complex.normSq ((star U * V) i j)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ p ∈ K, ∑ i, ∑ j, h p.1 p.2 * (x i ^ p.1 * y j ^ p.2 *
          Complex.normSq ((star U * V) i j)) := Finset.sum_comm

end Abstract

/-! ### Hermitian PSD matrices with equal spectra -/

section Hermitian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Matrix part of `prop:seven-joint-entropy-target`, abstract form.**  Let `R, S` be Hermitian
positive semidefinite with the same eigenvalue multiset (e.g. `S` a unitary conjugate of `Rᵀ`), and
every eigenvalue of `R` at most `cap` (that is `‖R‖ ≤ cap`).  Under the scalar hypothesis
`ScalarMajorant (polyH K h) cap` (AH-6),
`tr f(R) ≤ ∑_{(k,l)∈K} h_{kl} Re tr(R^k S^l)`.  Commutation of `R` and `S` is not required. -/
theorem entropy_le_polyTrace_herm (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (cap : ℝ)
    (hH : ScalarMajorant (polyH K h) cap)
    {R S : Matrix ι ι ℂ} (hR : R.PosSemidef) (hS : S.PosSemidef)
    (hspec : Multiset.map hR.isHermitian.eigenvalues Finset.univ.val =
      Multiset.map hS.isHermitian.eigenvalues Finset.univ.val)
    (hcap : ∀ i, hR.isHermitian.eigenvalues i ≤ cap) :
    ∑ i, Real.negMulLog (hR.isHermitian.eigenvalues i) ≤
      ∑ p ∈ K, h p.1 p.2 * (R ^ p.1 * S ^ p.2).trace.re := by
  have hmem : ∀ j, ∃ i, hR.isHermitian.eigenvalues i = hS.isHermitian.eigenvalues j := by
    intro j
    have : hS.isHermitian.eigenvalues j ∈
        Multiset.map hS.isHermitian.eigenvalues Finset.univ.val :=
      Multiset.mem_map_of_mem _ (Finset.mem_univ j)
    rw [← hspec] at this
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.1 this
    exact ⟨i, hi⟩
  have hsum : ∑ j, Real.negMulLog (hS.isHermitian.eigenvalues j) =
      ∑ i, Real.negMulLog (hR.isHermitian.eigenvalues i) := by
    have e1 : ∀ g : ι → ℝ, ∑ j, Real.negMulLog (g j) =
        ((Multiset.map g Finset.univ.val).map Real.negMulLog).sum := by
      intro g; rw [Multiset.map_map]; rfl
    rw [e1, e1, hspec]
  have hU : star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self _
  have hU' : (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hR.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := Unitary.coe_mul_star_self _
  have hV : star (hS.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      (hS.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := Unitary.coe_star_mul_self _
  have hV' : (hS.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      star (hS.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := Unitary.coe_mul_star_self _
  have := entropy_le_polyTrace K h cap hH hU hU' hV hV' hR.isHermitian.eigenvalues
    hS.isHermitian.eigenvalues (hR.eigenvalues_nonneg) hcap (hS.eigenvalues_nonneg)
    (fun j => by obtain ⟨i, hi⟩ := hmem j; rw [← hi]; exact hcap i) hsum
  rw [← eigen_decomp R hR.isHermitian, ← eigen_decomp S hS.isHermitian] at this
  exact this

end Hermitian

/-! ### Three qubits: the spin flip -/

/-- **Matrix part of `prop:seven-joint-entropy-target`, three-qubit form.**  For a positive
semidefinite `8 × 8` matrix `R` with all eigenvalues at most `cap` (`‖R‖ ≤ cap`) and the three-qubit
spin flip `R̃ = Y^{⊗3} Rᵀ Y^{⊗3}`, under `ScalarMajorant (polyH K h) cap` (AH-6),
`tr f(R) ≤ ∑ h_{kl} Re tr(R^k R̃^l)`.  The spin flip is a unitary conjugate of `Rᵀ` with the
spectrum of `R` (`SevenQubitSpectralPair.flip_conj`, `unitary_conj`), proved, not assumed. -/
theorem entropy_le_polyTrace_spinFlip (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (cap : ℝ)
    (hH : ScalarMajorant (polyH K h) cap) {R : Mat3} (hR : R.PosSemidef)
    (hcap : ∀ i, hR.isHermitian.eigenvalues i ≤ cap) :
    ∑ i, Real.negMulLog (hR.isHermitian.eigenvalues i) ≤
      ∑ p ∈ K, h p.1 p.2 * (R ^ p.1 * spinFlip3 R ^ p.2).trace.re := by
  obtain ⟨hV, hV'⟩ := unitary_conj R hR.isHermitian
  have hU : star (hR.isHermitian.eigenvectorUnitary : Mat3) *
      (hR.isHermitian.eigenvectorUnitary : Mat3) = 1 := Unitary.coe_star_mul_self _
  have hU' : (hR.isHermitian.eigenvectorUnitary : Mat3) *
      star (hR.isHermitian.eigenvectorUnitary : Mat3) = 1 := Unitary.coe_mul_star_self _
  have := entropy_le_polyTrace K h cap hH hU hU' hV hV' hR.isHermitian.eigenvalues
    hR.isHermitian.eigenvalues hR.eigenvalues_nonneg hcap hR.eigenvalues_nonneg hcap rfl
  rw [← eigen_decomp R hR.isHermitian, flip_conj R hR.isHermitian] at this
  exact this

/-! ### Seven-qubit marginals -/

/-- The joint polynomial functional `𝒫(R) = ∑ h_{kl} Re tr(R^k R̃^l)` on three-qubit matrices. -/
noncomputable def jointP (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (R : Mat3) : ℝ :=
  ∑ p ∈ K, h p.1 p.2 * (R ^ p.1 * spinFlip3 R ^ p.2).trace.re

/-- The averaged joint functional `𝒫₅(ψ) = (1/35) ∑_{|T|=3} 𝒫(ρ_T)` of a seven-qubit vector. -/
noncomputable def jointP5 (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (ψ : BitString → ℂ) : ℝ :=
  (∑ m ∈ tripleMasks, jointP K h (redMatPsi (maskCut 3 4 m) ψ)) / 35

/-- Per-cut matrix inequality `S(ρ_T) ≤ 𝒫(ρ_T)`, given the eigenvalue cap of that cut. -/
theorem cutEntropy_le_jointP (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (cap : ℝ)
    (hH : ScalarMajorant (polyH K h) cap) (c : Cut 3 4) (ψ : BitString → ℂ)
    (hcap : ∀ x, (redMatPsi_isHermitian c ψ).eigenvalues x ≤ cap) :
    cutEntropy c ψ ≤ jointP K h (redMatPsi c ψ) :=
  entropy_le_polyTrace_spinFlip K h cap hH (redMatPsi_posSemidef c ψ) hcap

/-- **`prop:seven-joint-entropy-target`, entropy part, conditional on AH-6.**  If every
three-qubit marginal of `ψ` has all eigenvalues at most `cap`, then `E₃(ψ) ≤ 𝒫₅(ψ)`. -/
theorem meanEntropy3_le_jointP5 (K : Finset (ℕ × ℕ)) (h : ℕ → ℕ → ℝ) (cap : ℝ)
    (hH : ScalarMajorant (polyH K h) cap) (ψ : BitString → ℂ)
    (hcap : ∀ m ∈ tripleMasks, ∀ x, (redMatPsi_isHermitian (maskCut 3 4 m) ψ).eigenvalues x ≤ cap) :
    meanEntropy3 ψ ≤ jointP5 K h ψ := by
  unfold meanEntropy3 jointP5
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun m hm => ?_) (by norm_num)
  exact cutEntropy_le_jointP K h cap hH _ ψ (hcap m hm)

end JointMajorant

end FormalResearch.FourQubitEntropy.SevenQubitConseq

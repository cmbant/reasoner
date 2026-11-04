module

public import FormalResearch.NQubit.Reduced.MeanPurity
public import FormalResearch.NQubit.Entropy.PuritySlope

/-!
# Cut entropies of pure `n`-qubit states

The reduced state `ρ_S = rdm ψ S` is a density matrix (`rdm_posSemidef`, `rdm_trace`, with `tr ρ_S² = Σ λ²` for
its Hermitian eigenvalues, `rdm_eig_sq`).  `cutEntropyBits ψ S` is the von Neumann entropy of `ρ_S` in bits,
computed from the eigenvalues, and `meanEntropy ψ k = C(n,k)⁻¹ Σ_{|S|=k} cutEntropyBits ψ S`.

The sharp entropy–purity slope `NQubit.Entropy.entropy_purity_slope_bits` (`d = 2^k`) and averaging give

  `meanEntropy ψ k ≤ k - c_{2^k} (2^k meanRdmPurity ψ k - 1)`   (`meanEntropy_le`)

for every unit `ψ` and `2 ≤ k ≤ n`, with `c_d = (d-1) log₂(d-1)/(d(d-2))` (`NQubit.Entropy.slopeBits`).
-/

@[expose] public section


open Real Finset
open scoped ComplexConjugate Matrix ComplexOrder
open FormalResearch.NQubit.Pauli

namespace FormalResearch.NQubit.Reduced

variable {n : ℕ}

/-! ### The reduced state is a density matrix -/

/-- `tr A² = Σ λ²` for a Hermitian matrix. -/
theorem trace_sq_eq_sum_eigenvalues {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ∑ i, ((hA.eigenvalues i : ℝ) : ℂ) ^ 2 := by
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set D : Matrix ι ι ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hspec : A = U * D * Uᴴ := by
    have := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at this
    exact this
  have hUU : Uᴴ * U = 1 := by
    have := Unitary.coe_star_mul_self hA.eigenvectorUnitary
    rw [Matrix.star_eq_conjTranspose] at this
    exact this
  have hAA : A * A = U * (D * D) * Uᴴ := by
    calc A * A = (U * D * Uᴴ) * (U * D * Uᴴ) := by rw [← hspec]
      _ = U * (D * (Uᴴ * U) * D) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * (D * D) * Uᴴ := by rw [hUU]; simp [Matrix.mul_assoc]
  rw [hAA, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  simp [hD, Matrix.trace, pow_two]

/-- `ρ_S = M Mᴴ` for the cut coefficient matrix `M x t = ψ(x ⊔ t)`. -/
theorem rdm_eq_mul (ψ : Ψ n) (S : Finset (Fin n)) :
    rdm ψ S = (Matrix.of fun (x : CfgOn S) (t : CfgOff S) => ψ (glue S x t)) *
      (Matrix.of fun (x : CfgOn S) (t : CfgOff S) => ψ (glue S x t))ᴴ := by
  ext x y
  simp [rdm, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem rdm_posSemidef (ψ : Ψ n) (S : Finset (Fin n)) : (rdm ψ S).PosSemidef := by
  rw [rdm_eq_mul]; exact Matrix.posSemidef_self_mul_conjTranspose _

theorem rdm_isHermitian (ψ : Ψ n) (S : Finset (Fin n)) : (rdm ψ S).IsHermitian :=
  (rdm_posSemidef ψ S).isHermitian

theorem rdm_trace (ψ : Ψ n) (hψ : nsq ψ = 1) (S : Finset (Fin n)) : (rdm ψ S).trace = 1 := by
  have h := sum_cfg_glue S (fun X => ((Complex.normSq (ψ X) : ℝ) : ℂ))
  have e : (rdm ψ S).trace = ∑ x : CfgOn S, ∑ t : CfgOff S,
      ((Complex.normSq (ψ (glue S x t)) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag_apply, rdm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun t _ => ?_
    rw [Complex.mul_conj]
  rw [e, ← h, ← Complex.ofReal_sum]
  unfold nsq at hψ
  rw [hψ]; simp

/-- The eigenvalues of `ρ_S` form a probability vector. -/
theorem rdm_eig_nonneg (ψ : Ψ n) (S : Finset (Fin n)) (i : CfgOn S) :
    0 ≤ (rdm_isHermitian ψ S).eigenvalues i :=
  (rdm_posSemidef ψ S).eigenvalues_nonneg i

theorem rdm_eig_sum (ψ : Ψ n) (hψ : nsq ψ = 1) (S : Finset (Fin n)) :
    ∑ i, (rdm_isHermitian ψ S).eigenvalues i = 1 := by
  have h := (rdm_isHermitian ψ S).trace_eq_sum_eigenvalues
  rw [rdm_trace ψ hψ S] at h
  have := congrArg Complex.re h
  simpa using this.symm

theorem rdm_eig_sq (ψ : Ψ n) (S : Finset (Fin n)) :
    ∑ i, (rdm_isHermitian ψ S).eigenvalues i ^ 2 = (Matrix.trace (rdm ψ S * rdm ψ S)).re := by
  rw [trace_sq_eq_sum_eigenvalues (rdm_isHermitian ψ S)]
  simp [← Complex.ofReal_pow, ← Complex.ofReal_sum]

theorem card_cfgOn' (S : Finset (Fin n)) : Fintype.card (CfgOn S) = 2 ^ S.card := by
  simp [CfgOn]

/-! ### Entropies -/

/-- The von Neumann entropy in bits of `ρ_S = rdm ψ S`, from its Hermitian eigenvalues. -/
noncomputable def cutEntropyBits (ψ : Ψ n) (S : Finset (Fin n)) : ℝ :=
  (∑ i, negMulLog ((rdm_isHermitian ψ S).eigenvalues i)) / log 2

/-- `E_k(ψ) = C(n,k)⁻¹ Σ_{|S|=k} S(ρ_S)` (bits). -/
noncomputable def meanEntropy (ψ : Ψ n) (k : ℕ) : ℝ :=
  (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k, cutEntropyBits ψ S) / (Nat.choose n k : ℝ)

theorem slopeBits_nonneg {d : ℝ} (hd : 3 ≤ d) : 0 ≤ NQubit.Entropy.slopeBits d := by
  unfold NQubit.Entropy.slopeBits
  have : 0 ≤ Real.logb 2 (d - 1) := Real.logb_nonneg (by norm_num) (by linarith)
  apply div_nonneg (mul_nonneg (by linarith) this) (mul_nonneg (by linarith) (by linarith))

/-- **Per-cut slope** (the sharp slope for `d = 2^k`): for a unit vector and `|S| = k ≥ 2`,
`S(ρ_S) ≤ k - c_{2^k} (2^k tr ρ_S² - 1)`. -/
theorem cutEntropyBits_le (ψ : Ψ n) (hψ : nsq ψ = 1) (S : Finset (Fin n)) {k : ℕ}
    (hS : S.card = k) (hk : 2 ≤ k) :
    cutEntropyBits ψ S ≤ k - NQubit.Entropy.slopeBits ((2 : ℝ) ^ k) *
      ((2 : ℝ) ^ k * (Matrix.trace (rdm ψ S * rdm ψ S)).re - 1) := by
  have hcard : Fintype.card (CfgOn S) = 2 ^ k := by rw [card_cfgOn', hS]
  have hd : 3 ≤ 2 ^ k := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h := NQubit.Entropy.entropy_purity_slope_bits hd hcard _ (rdm_eig_nonneg ψ S)
    (rdm_eig_sum ψ hψ S)
  rw [rdm_eig_sq] at h
  push_cast at h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
  unfold cutEntropyBits
  linarith

/-- **`E_k ≤ k - c_{2^k}(2^k π_k - 1)`** for every unit vector `ψ` of `n` qubits and `2 ≤ k ≤ n`
(from the sharp entropy–purity slope `entropy_purity_slope_bits`). -/
theorem meanEntropy_le (ψ : Ψ n) (hψ : nsq ψ = 1) {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    meanEntropy ψ k ≤ k - NQubit.Entropy.slopeBits ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k * meanRdmPurity ψ k - 1) := by
  set T := (Finset.univ : Finset (Fin n)).powersetCard k
  have hC : (0 : ℝ) < Nat.choose n k := by exact_mod_cast Nat.choose_pos hkn
  have hT : (T.card : ℝ) = Nat.choose n k := by
    simp [T, Finset.card_powersetCard]
  set c := NQubit.Entropy.slopeBits ((2 : ℝ) ^ k)
  have hsum : ∑ S ∈ T, cutEntropyBits ψ S ≤
      ∑ S ∈ T, ((k : ℝ) - c * ((2 : ℝ) ^ k * (Matrix.trace (rdm ψ S * rdm ψ S)).re - 1)) :=
    Finset.sum_le_sum fun S hS => cutEntropyBits_le ψ hψ S (Finset.mem_powersetCard.1 hS).2 hk
  have e : ∑ S ∈ T, ((k : ℝ) - c * ((2 : ℝ) ^ k * (Matrix.trace (rdm ψ S * rdm ψ S)).re - 1)) =
      (Nat.choose n k : ℝ) * (k - c * ((2 : ℝ) ^ k * meanRdmPurity ψ k - 1)) := by
    unfold meanRdmPurity
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul, hT]
    field_simp
    ring
  unfold meanEntropy
  rw [div_le_iff₀ hC]
  linarith

/-- info: 'FormalResearch.NQubit.Reduced.meanEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meanEntropy_le

end FormalResearch.NQubit.Reduced

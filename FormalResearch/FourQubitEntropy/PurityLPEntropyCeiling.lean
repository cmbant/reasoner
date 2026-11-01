import FormalResearch.FourQubitEntropy.PurityLPMain
import FormalResearch.FourQubitEntropy.EntropyPuritySlope
import FormalResearch.FourQubitEntropy.SevenQubitLinearPurity

/-!
# Entropy ceilings from the purity minima (Paper E, `tab:fqe-other-n`)

Source: `ResearchNotes/QI/four_qubit_entropy/four_qubit_entropy.tex`, table `tab:fqe-other-n` and the
paragraph "Purity and entropy at other sizes" (verifier `code/verify_entropy_purity_upper_table.py`,
EU-1/EU-2); the slope is `lem:seven-entropy-linear-purity` (`eq:entropy-purity-general-slope`).

For a pure `n`-qubit state `ψ` and `k ≥ 2`, the balanced-cut mean entropy is
`E_k(ψ) = C(n,k)⁻¹ Σ_{|S|=k} S(ρ_S)` (`meanEntropy`), with `S(ρ_S)` the von Neumann entropy in bits
of the explicit partial trace `ρ_S = rdm ψ S`, computed from its Hermitian eigenvalues (`cutEntropyBits`).
Since `ρ_S` is a `2^k`-dimensional density matrix with `tr ρ_S² = Σ λ²`, the sharp slope
(`EntropyPurity.entropy_purity_slope_bits`, `d = 2^k`) and averaging give

  `E_k(ψ) ≤ k - c_{2^k} (2^k π_k(ψ) - 1)`   (`meanEntropy_le`),

with `π_k = piMean ψ k`.  Combined with the exact minima `minPurity<n>` (`PurityLPMain.lean`) this proves
every ceiling of the table, both in the exact form `E_k ≤ k - c_{2^k}(2^k min π_k - 1)` and as the displayed
four-decimal rational upper bound (`entropyCeiling<n>`), for `n = 8–12, 14–18`, `k = ⌊n/2⌋`.  The decimal
step uses `log₂(2^k - 1) = k - log(2^k/(2^k-1))/ln 2` with the `arctanh` upper bound `SevenQubitConseq.LinPur.log_le_arctanhHi`
and `ln 2 > 0.6931471803`.

Everything is proved (no hypotheses).
-/

open Real Finset
open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.FrameFree.NQubit
open FormalResearch.FourQubitEntropy.SpinFlip

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

theorem slopeBits_nonneg {d : ℝ} (hd : 3 ≤ d) : 0 ≤ EntropyPurity.slopeBits d := by
  unfold EntropyPurity.slopeBits
  have : 0 ≤ Real.logb 2 (d - 1) := Real.logb_nonneg (by norm_num) (by linarith)
  apply div_nonneg (mul_nonneg (by linarith) this) (mul_nonneg (by linarith) (by linarith))

/-- **Per-cut slope** (`eq:entropy-purity-general-slope` for `d = 2^k`): for a unit vector and `|S| = k ≥ 2`,
`S(ρ_S) ≤ k - c_{2^k} (2^k tr ρ_S² - 1)`. -/
theorem cutEntropyBits_le (ψ : Ψ n) (hψ : nsq ψ = 1) (S : Finset (Fin n)) {k : ℕ}
    (hS : S.card = k) (hk : 2 ≤ k) :
    cutEntropyBits ψ S ≤ k - EntropyPurity.slopeBits ((2 : ℝ) ^ k) *
      ((2 : ℝ) ^ k * (Matrix.trace (rdm ψ S * rdm ψ S)).re - 1) := by
  have hcard : Fintype.card (CfgOn S) = 2 ^ k := by rw [card_cfgOn', hS]
  have hd : 3 ≤ 2 ^ k := by
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h := EntropyPurity.entropy_purity_slope_bits hd hcard _ (rdm_eig_nonneg ψ S)
    (rdm_eig_sum ψ hψ S)
  rw [rdm_eig_sq] at h
  push_cast at h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
  unfold cutEntropyBits
  linarith

/-- **`E_k ≤ k - c_{2^k}(2^k π_k - 1)`** for every unit vector `ψ` of `n` qubits and `2 ≤ k ≤ n`
(`tab:fqe-other-n`, from `lem:seven-entropy-linear-purity`). -/
theorem meanEntropy_le (ψ : Ψ n) (hψ : nsq ψ = 1) {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    meanEntropy ψ k ≤ k - EntropyPurity.slopeBits ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k * piMean ψ k - 1) := by
  set T := (Finset.univ : Finset (Fin n)).powersetCard k
  have hC : (0 : ℝ) < Nat.choose n k := by exact_mod_cast Nat.choose_pos hkn
  have hT : (T.card : ℝ) = Nat.choose n k := by
    simp [T, Finset.card_powersetCard]
  set c := EntropyPurity.slopeBits ((2 : ℝ) ^ k)
  have hsum : ∑ S ∈ T, cutEntropyBits ψ S ≤
      ∑ S ∈ T, ((k : ℝ) - c * ((2 : ℝ) ^ k * (Matrix.trace (rdm ψ S * rdm ψ S)).re - 1)) :=
    Finset.sum_le_sum fun S hS => cutEntropyBits_le ψ hψ S (Finset.mem_powersetCard.1 hS).2 hk
  have e : ∑ S ∈ T, ((k : ℝ) - c * ((2 : ℝ) ^ k * (Matrix.trace (rdm ψ S * rdm ψ S)).re - 1)) =
      (Nat.choose n k : ℝ) * (k - c * ((2 : ℝ) ^ k * piMean ψ k - 1)) := by
    unfold piMean
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul, hT]
    field_simp
    ring
  unfold meanEntropy
  rw [div_le_iff₀ hC]
  linarith

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.meanEntropy_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms meanEntropy_le

/-! ### From the purity minimum to a rational ceiling -/

/-- `log₂(d - 1) ≥ k - u/ln 2` with `d = 2^k` and `u ≥ log(d/(d-1))`. -/
theorem logb_pred_ge (k : ℕ) (hk : 1 ≤ k) :
    (k : ℝ) - SevenQubitConseq.LinPur.arctanhHi ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) / (6931471803 / 10000000000) ≤
      Real.logb 2 ((2 : ℝ) ^ k - 1) := by
  have hd : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hd1 : (0 : ℝ) < 2 ^ k - 1 := by linarith
  have hx : 1 ≤ (2 : ℝ) ^ k / (2 ^ k - 1) := by rw [le_div_iff₀ hd1]; linarith
  have hu := SevenQubitConseq.LinPur.log_le_arctanhHi hx
  have hu0 : 0 ≤ log ((2 : ℝ) ^ k / (2 ^ k - 1)) := Real.log_nonneg hx
  have l2 := SevenQubitConseq.LinPur.log2_lo
  have l20 : 0 < log 2 := by linarith
  have e : log ((2 : ℝ) ^ k - 1) = k * log 2 - log ((2 : ℝ) ^ k / (2 ^ k - 1)) := by
    rw [Real.log_div (by positivity) hd1.ne', Real.log_pow]; ring
  unfold Real.logb
  rw [e, sub_div, mul_div_assoc, div_self l20.ne', mul_one]
  have : log ((2 : ℝ) ^ k / (2 ^ k - 1)) / log 2 ≤
      SevenQubitConseq.LinPur.arctanhHi ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) / (6931471803 / 10000000000) := by
    calc log ((2 : ℝ) ^ k / (2 ^ k - 1)) / log 2
        ≤ SevenQubitConseq.LinPur.arctanhHi ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) / log 2 :=
          div_le_div_of_nonneg_right hu l20.le
      _ ≤ SevenQubitConseq.LinPur.arctanhHi ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) / (6931471803 / 10000000000) :=
          div_le_div_of_nonneg_left (hu0.trans hu) (by norm_num) l2.le
  linarith

/-- **Ceiling from a purity lower bound.**  If `L ≤ π_k(ψ)` with `2^k L ≥ 1`, then
`E_k(ψ) ≤ k - c_{2^k}(2^k L - 1)`, and this is below `D` whenever the rational test `hD` holds
(it replaces `log₂(2^k-1)` by the lower bound of `logb_pred_ge`). -/
theorem meanEntropy_lt_of (ψ : Ψ n) (hψ : nsq ψ = 1) {k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) {L D : ℝ}
    (hL : L ≤ piMean ψ k) (hL1 : 1 ≤ (2 : ℝ) ^ k * L)
    (hD : (k : ℝ) - ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k * L - 1) / ((2 : ℝ) ^ k * ((2 : ℝ) ^ k - 2)) *
      ((k : ℝ) - SevenQubitConseq.LinPur.arctanhHi ((2 : ℝ) ^ k / ((2 : ℝ) ^ k - 1)) / (6931471803 / 10000000000)) < D) :
    meanEntropy ψ k ≤ k - EntropyPurity.slopeBits ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k * L - 1) ∧
      meanEntropy ψ k < D := by
  have hd4 : (4 : ℝ) ≤ 2 ^ k := by
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  have hc := slopeBits_nonneg (d := (2 : ℝ) ^ k) (by linarith)
  have h := meanEntropy_le ψ hψ hk hkn
  have hmono : EntropyPurity.slopeBits ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k * L - 1) ≤
      EntropyPurity.slopeBits ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k * piMean ψ k - 1) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hc
  refine ⟨by linarith, ?_⟩
  have hlog := logb_pred_ge k (by omega)
  have hA : 0 ≤ ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k * L - 1) / ((2 : ℝ) ^ k * ((2 : ℝ) ^ k - 2)) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  have e : EntropyPurity.slopeBits ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k * L - 1) =
      ((2 : ℝ) ^ k - 1) * ((2 : ℝ) ^ k * L - 1) / ((2 : ℝ) ^ k * ((2 : ℝ) ^ k - 2)) *
        Real.logb 2 ((2 : ℝ) ^ k - 1) := by
    unfold EntropyPurity.slopeBits; ring
  have := mul_le_mul_of_nonneg_left hlog hA
  linarith

/-! ### The rows of `tab:fqe-other-n` -/

/-- **`tab:fqe-other-n`, `n = 8`**: every pure 8-qubit state has
`E_4 ≤ 4 - c_16(16 · (3/35) - 1) < 3.9029` (`min π_4 = 3/35`, `minPurity8`). -/
theorem entropyCeiling8 (ψ : Ψ 8) (hψ : nsq ψ = 1) :
    meanEntropy ψ 4 ≤ 4 - EntropyPurity.slopeBits 16 * (16 * (3 / 35) - 1) ∧
      meanEntropy ψ 4 < 39029 / 10000 := by
  have h := meanEntropy_lt_of (k := 4) (L := 3 / 35) (D := 39029 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity8.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling8

/-- **`tab:fqe-other-n`, `n = 9`**: every pure 9-qubit state has
`E_4 ≤ 4 - c_16(16 · (1/14) - 1) < 3.9627` (`min π_4 = 1/14`, `minPurity9`). -/
theorem entropyCeiling9 (ψ : Ψ 9) (hψ : nsq ψ = 1) :
    meanEntropy ψ 4 ≤ 4 - EntropyPurity.slopeBits 16 * (16 * (1 / 14) - 1) ∧
      meanEntropy ψ 4 < 39627 / 10000 := by
  have h := meanEntropy_lt_of (k := 4) (L := 1 / 14) (D := 39627 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity9.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling9

/-- **`tab:fqe-other-n`, `n = 10`**: every pure 10-qubit state has
`E_5 ≤ 5 - c_32(32 · (1/21) - 1) < 4.9163` (`min π_5 = 1/21`, `minPurity10`). -/
theorem entropyCeiling10 (ψ : Ψ 10) (hψ : nsq ψ = 1) :
    meanEntropy ψ 5 ≤ 5 - EntropyPurity.slopeBits 32 * (32 * (1 / 21) - 1) ∧
      meanEntropy ψ 5 < 49163 / 10000 := by
  have h := meanEntropy_lt_of (k := 5) (L := 1 / 21) (D := 49163 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity10.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling10

/-- **`tab:fqe-other-n`, `n = 11`**: every pure 11-qubit state has
`E_5 ≤ 5 - c_32(32 · (1/28) - 1) < 4.9772` (`min π_5 = 1/28`, `minPurity11`). -/
theorem entropyCeiling11 (ψ : Ψ 11) (hψ : nsq ψ = 1) :
    meanEntropy ψ 5 ≤ 5 - EntropyPurity.slopeBits 32 * (32 * (1 / 28) - 1) ∧
      meanEntropy ψ 5 < 49772 / 10000 := by
  have h := meanEntropy_lt_of (k := 5) (L := 1 / 28) (D := 49772 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity11.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling11' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling11

/-- **`tab:fqe-other-n`, `n = 12`**: every pure 12-qubit state has
`E_6 ≤ 6 - c_64(64 · (5/224) - 1) < 5.9594` (`min π_6 = 5/224`, `minPurity12`). -/
theorem entropyCeiling12 (ψ : Ψ 12) (hψ : nsq ψ = 1) :
    meanEntropy ψ 6 ≤ 6 - EntropyPurity.slopeBits 64 * (64 * (5 / 224) - 1) ∧
      meanEntropy ψ 6 < 59594 / 10000 := by
  have h := meanEntropy_lt_of (k := 6) (L := 5 / 224) (D := 59594 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity12.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling12' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling12

/-- **`tab:fqe-other-n`, `n = 14`**: every pure 14-qubit state has
`E_7 ≤ 7 - c_128(128 · (331/27456) - 1) < 6.9702` (`min π_7 = 331/27456`, `minPurity14`). -/
theorem entropyCeiling14 (ψ : Ψ 14) (hψ : nsq ψ = 1) :
    meanEntropy ψ 7 ≤ 7 - EntropyPurity.slopeBits 128 * (128 * (331 / 27456) - 1) ∧
      meanEntropy ψ 7 < 69702 / 10000 := by
  have h := meanEntropy_lt_of (k := 7) (L := 331 / 27456) (D := 69702 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity14.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling14

/-- **`tab:fqe-other-n`, `n = 15`**: every pure 15-qubit state has
`E_7 ≤ 7 - c_128(128 · (1/104) - 1) < 6.9874` (`min π_7 = 1/104`, `minPurity15`). -/
theorem entropyCeiling15 (ψ : Ψ 15) (hψ : nsq ψ = 1) :
    meanEntropy ψ 7 ≤ 7 - EntropyPurity.slopeBits 128 * (128 * (1 / 104) - 1) ∧
      meanEntropy ψ 7 < 69874 / 10000 := by
  have h := meanEntropy_lt_of (k := 7) (L := 1 / 104) (D := 69874 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity15.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling15' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling15

/-- **`tab:fqe-other-n`, `n = 16`**: every pure 16-qubit state has
`E_8 ≤ 8 - c_256(256 · (1/156) - 1) < 7.9800` (`min π_8 = 1/156`, `minPurity16`). -/
theorem entropyCeiling16 (ψ : Ψ 16) (hψ : nsq ψ = 1) :
    meanEntropy ψ 8 ≤ 8 - EntropyPurity.slopeBits 256 * (256 * (1 / 156) - 1) ∧
      meanEntropy ψ 8 < 79800 / 10000 := by
  have h := meanEntropy_lt_of (k := 8) (L := 1 / 156) (D := 79800 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity16.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling16

/-- **`tab:fqe-other-n`, `n = 17`**: every pure 17-qubit state has
`E_8 ≤ 8 - c_256(256 · (1/208) - 1) < 7.9928` (`min π_8 = 1/208`, `minPurity17`). -/
theorem entropyCeiling17 (ψ : Ψ 17) (hψ : nsq ψ = 1) :
    meanEntropy ψ 8 ≤ 8 - EntropyPurity.slopeBits 256 * (256 * (1 / 208) - 1) ∧
      meanEntropy ψ 8 < 79928 / 10000 := by
  have h := meanEntropy_lt_of (k := 8) (L := 1 / 208) (D := 79928 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity17.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling17

/-- **`tab:fqe-other-n`, `n = 18`**: every pure 18-qubit state has
`E_9 ≤ 9 - c_512(512 · (7/2288) - 1) < 8.9901` (`min π_9 = 7/2288`, `minPurity18`). -/
theorem entropyCeiling18 (ψ : Ψ 18) (hψ : nsq ψ = 1) :
    meanEntropy ψ 9 ≤ 9 - EntropyPurity.slopeBits 512 * (512 * (7 / 2288) - 1) ∧
      meanEntropy ψ 9 < 89901 / 10000 := by
  have h := meanEntropy_lt_of (k := 9) (L := 7 / 2288) (D := 89901 / 10000) ψ hψ (by norm_num) (by norm_num)
    (minPurity18.2 ⟨ψ, hψ, rfl⟩) (by norm_num)
    (by unfold SevenQubitConseq.LinPur.arctanhHi; norm_num)
  norm_num at h ⊢
  exact h

/-- info: 'FormalResearch.FourQubitEntropy.PurityLP.entropyCeiling18' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropyCeiling18

end FormalResearch.FourQubitEntropy.PurityLP

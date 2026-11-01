import FormalResearch.FourQubitEntropy.QVCert.Data

/-!
# The positivity layer of the (QV) certificate

Paper E, `sup_renyi.tex`, `sec:sup-qk` (`thm:fqe-sharp-quadratic-variance`, `eq:fqe-qv-allstate-sos`): the
certificate is `2 D 𝔇(z) = Σ_{k,i} q_ki ‖Φ_ki(z)‖²_{w_{p_k}}` with positive integer weights `q_ki` (verifier map
QVA-2), so every summand is a positive multiple of a weighted squared norm.

* `wnormSq`, `wnormSq_nonneg`: a weighted squared norm `Σ_x w_x |s_x|²` with nonnegative weights is `≥ 0`.
* `Block.q`, `weights_pos`: the 96 concrete weights `q_ki` are positive (kernel-checked, `decide +kernel`;
  integers of up to 24 digits). `weights_length`, `vecs_shape`, `total_count`: shape checks of the data.
-/

open Finset

namespace FormalResearch.FourQubitEntropy.QVCert

/-- The weighted squared norm `‖s‖²_w = Σ_{x ∈ S} w_x |s_x|²` of a complex vector `s : ι → ℂ`. -/
noncomputable def wnormSq {ι : Type*} (S : Finset ι) (w : ι → ℝ) (s : ι → ℂ) : ℝ :=
  ∑ x ∈ S, w x * Complex.normSq (s x)

theorem wnormSq_nonneg {ι : Type*} {S : Finset ι} {w : ι → ℝ} (hw : ∀ x ∈ S, 0 ≤ w x) (s : ι → ℂ) :
    0 ≤ wnormSq S w s :=
  Finset.sum_nonneg fun x hx => mul_nonneg (hw x hx) (Complex.normSq_nonneg _)

/-- The `k`-th block, `k = 0, …, 13`. -/
def blk (k : Fin 14) : Block := blocks.getD k block0

namespace Block

/-- The integer weight `q_ki` of the `i`-th covariant of the block. -/
def q (b : Block) (i : ℕ) : ℤ := b.weights.getD i 0

end Block

/-- The certificate has 14 blocks. -/
theorem blocks_length : blocks.length = 14 := by decide +kernel

/-- There are 96 covariants `Φ_ki` in all. -/
theorem total_count : (blocks.map fun b => b.weights.length).sum = 96 := by decide +kernel

/-- Each block has one multiplicity vector per weight. -/
theorem weights_length : ∀ k : Fin 14, (blk k).vecs.length = (blk k).weights.length := by decide +kernel

/-- The multiplicity vectors have 1112 nonzero entries in all, each of absolute value at most 42. -/
theorem vecs_shape : (blocks.map fun b => (b.vecs.map List.length).sum).sum = 1112 ∧
    ∀ k : Fin 14, ∀ v ∈ (blk k).vecs, ∀ t ∈ v, t.2 ≠ 0 ∧ |t.2| ≤ 42 := by
  decide +kernel

/-- **QVA-2.** All 96 weights `q_ki` are positive integers. -/
theorem weights_pos : ∀ k : Fin 14, ∀ i < (blk k).weights.length, 0 < (blk k).q i := by
  decide +kernel

end FormalResearch.FourQubitEntropy.QVCert

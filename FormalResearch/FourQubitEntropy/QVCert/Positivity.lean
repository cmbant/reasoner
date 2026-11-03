module

public import FormalResearch.FourQubitEntropy.QVCert.Data

/-!
# The positivity layer of the (QV) certificate

Paper E, `sup_renyi.tex`, `sec:sup-qk` (`thm:fqe-sharp-quadratic-variance`, `eq:fqe-qv-allstate-sos`): the
certificate is `2 D 𝔇(z) = Σ_{k,i} q_ki ‖Φ_ki(z)‖²_{w_{p_k}}` with positive integer weights `q_ki` (verifier map
QVA-2), so every summand is a positive multiple of a weighted squared norm.

* `wnormSq`, `wnormSq_nonneg`: a weighted squared norm `Σ_x w_x |s_x|²` with nonnegative weights is `≥ 0`.
* `blk`, `Block.q`, `weights_pos`: the 95 concrete weights `q_ki` are positive (kernel-checked, `decide +kernel`;
  integers of up to 24 digits).
-/

@[expose] public section


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

/-- **QVA-2.** All 95 weights `q_ki` are positive integers. -/
theorem weights_pos : ∀ k : Fin 14, ∀ i < (blk k).weights.length, 0 < (blk k).q i := by
  decide +kernel

end FormalResearch.FourQubitEntropy.QVCert

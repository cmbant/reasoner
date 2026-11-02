import FormalResearch.FourQubitEntropy.Statement
import FormalResearch.FourQubitEntropy.QVCert.Positivity

/-!
# The covariants and weighted norms of the (QV) certificate

Paper E, `sup_renyi.tex`, `sec:sup-qk`, proof of `thm:fqe-sharp-quadratic-variance`; the conventions are those of
`verify_qv_all_state_certificate.py` (QVA), which this file transcribes without materialising any
`2^24`-dimensional vector (all objects are `noncomputable` definitions over `ℂ`).

* **Six-copy intertwiner** `C6`: for each spin `j/2 ∈ {0, 1, 2, 3}` the highest-weight rows `H_μ` of
  `hwSupport j` (vectors in `(ℂ²)^{⊗6}`, bit `k` of the basis index = the spin of the `k`-th tensor position)
  and their lowerings `H_μ F^m / m!` (`rowC j m μ`).
* **`z̃ = J^{⊗4} z̄`** with `J = ((0,1),(-1,0))`: `z̃_{abcd} = (-1)^{a+b+c+d} conj z_{1-a,1-b,1-c,1-d}`.
* **`sixCopy a z`**: the vector `z^{⊗a} ⊗ z̃^{⊗(6-a)}` of `((ℂ²)^{⊗4})^{⊗6}`, written as a function of the four
  six-copy indices `b_q ∈ [0, 64)` (one per qubit slot `q`). Copy `k = 0,…,5` sits at bit `5 - k` of `b_q`, and
  the first `a` copies are `z` (the convention of the Python reference: its first three-copy block occupies
  the high bits).
* **Sector component** `sectorW a p σ m μ z`: apply `C6` in every slot, with spin `p_k`, lowering index `m_k`
  and multiplicity index `μ_k` placed in slot `σ k`. Stacking all `σ ∈ S₄` gives `W_{a,p}` of the paper.
* **Weights** `wp p m = ∏_k (lcm_r C(p_k, r) / C(p_k, m_k))` (`weight` is a positive integer; only `wp ≥ 0` is used).
* **Covariants** `Block.Phi b z i`, `Φ_ki = W_{a_k,p_k} v_ki` for the integer multiplicity vector `v_ki`, and their
  weighted squared norms `Block.normSqPhi b z i = ‖Φ_ki(z)‖²_{w_{p_k}}`.
-/

open scoped ComplexConjugate
open Finset

namespace FormalResearch.FourQubitEntropy.QVCert

/-! ### The six-copy intertwiner -/

/-- The lowering operator `F` on six-copy vectors (bit `k` of the basis index is copy `k`):
`(F v)(b) = Σ_{k : bit k of b = 1} v(b with bit k cleared)`. -/
def lowerOp (v : ℕ → ℤ) (b : ℕ) : ℤ :=
  ∑ k ∈ range 6, if b.testBit k then v (b ^^^ 2 ^ k) else 0

/-- The highest-weight vector `H_μ` of spin `j/2`: `-1` on its negative support, `+1` on its positive one. -/
def hwVec (j μ : ℕ) (b : ℕ) : ℤ :=
  match (hwSupport j)[μ]? with
  | some (neg, pos) => if b ∈ pos then 1 else if b ∈ neg then -1 else 0
  | none => 0

/-- Entry `b` of the row `H_μ F^m / m!` of the six-copy intertwiner `C6` (spin `j/2`, magnetic index `m`,
multiplicity `μ`); the division is exact. -/
def rowC (j m μ : ℕ) (b : ℕ) : ℤ := (lowerOp^[m] (hwVec j μ) b) / (m.factorial : ℤ)

/-- Multiplicity of the spin-`j/2` sector in `(ℂ²)^{⊗6}`. -/
def mult (j : ℕ) : ℕ := (hwSupport j).length

/-- The invariant-inner-product weight of the magnetic row `m` of spin `j/2`:
`lcm_r C(j, r) / C(j, m)`. -/
def weight (j m : ℕ) : ℕ := (range (j + 1)).lcm (Nat.choose j) / Nat.choose j m

/-! ### The vectors `z^{⊗a} ⊗ z̃^{⊗(6-a)}` -/

/-- Bit `k` of `n` as an element of `Fin 2`. -/
def bitF (n k : ℕ) : Fin 2 := if n.testBit k then 1 else 0

/-- `z̃ = J^{⊗4} z̄`, `J = ((0,1),(-1,0))`. -/
noncomputable def ztilde (z : Psi) : Psi := fun a b c d =>
  (-1 : ℂ) ^ (a.val + b.val + c.val + d.val) * conj (z a.rev b.rev c.rev d.rev)

/-- The `k`-th of the six copies: `z` for `k < a`, `z̃` for `k ≥ a`. -/
noncomputable def copyVec (a : ℕ) (z : Psi) (k : Fin 6) : Psi := if k.val < a then z else ztilde z

/-- The component `(z^{⊗a} ⊗ z̃^{⊗(6-a)})(b_0, b_1, b_2, b_3)` for six-copy indices `b_q ∈ [0, 64)` of the
four qubit slots: a product over the six copies, copy `k` reading bit `5 - k` of each `b_q`. -/
noncomputable def sixCopy (a : ℕ) (z : Psi) (b : Fin 4 → Fin 64) : ℂ :=
  ∏ k : Fin 6, copyVec a z k (bitF (b 0).val (5 - k.val)) (bitF (b 1).val (5 - k.val))
    (bitF (b 2).val (5 - k.val)) (bitF (b 3).val (5 - k.val))

/-! ### Sector components and covariants -/

/-- The sector component `W_{a,p}(σ, m, μ)(z)`: the six-copy vector `z^{⊗a} ⊗ z̃^{⊗(6-a)}` contracted
in qubit slot `σ k` with the row `(p_k, m_k, μ_k)` of `C6`. Over all `σ ∈ S₄` and all `m` with
`m_k ≤ p_k` these are the rows of `W_{a,p}`. -/
noncomputable def sectorW (a : ℕ) (p : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4)) (m μ : Fin 4 → ℕ)
    (z : Psi) : ℂ :=
  ∑ b : Fin 4 → Fin 64, (∏ k : Fin 4, (rowC (p k) (m k) (μ k) (b (σ k)).val : ℂ)) * sixCopy a z b

/-- Digit `k` of the flat multiplicity index `c` for the spin tuple `p` (digit `0` most significant): the
multiplicity-column index `c` of `W_{a,p}` is `(μ_0, …, μ_3)`. -/
def muDigit (p : Fin 4 → ℕ) (c : ℕ) (k : Fin 4) : ℕ :=
  (c / ∏ l ∈ univ.filter (fun l : Fin 4 => k < l), mult (p l)) % mult (p k)

/-- The positive weight `w_p(m) = ∏_k weight(p_k, m_k)` of the magnetic row `m`. -/
noncomputable def wp (p : Fin 4 → ℕ) (m : Fin 4 → ℕ) : ℝ := ∏ k, (weight (p k) (m k) : ℝ)

theorem wp_nonneg (p m : Fin 4 → ℕ) : 0 ≤ wp p m := Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _

/-- The index set of the rows of `W_{a,p}`: a qubit permutation `σ` and magnetic indices `m_k ≤ p_k`. -/
def rowIdx (p : Fin 4 → ℕ) : Finset (Equiv.Perm (Fin 4) × (Fin 4 → ℕ)) :=
  univ ×ˢ Fintype.piFinset (fun k => range (p k + 1))

namespace Block

/-- The covariant `Φ_ki = W_{a_k,p_k} v_ki` as a function of the row index `(σ, m)`:
`Φ_i(σ, m) = Σ_{(c, v) ∈ v_i} v · W_{a,p}(σ, m, μ(c))`, where `v_i` is the `i`-th sparse multiplicity vector
of the block. -/
noncomputable def Phi (b : Block) (z : Psi) (i : ℕ) (x : Equiv.Perm (Fin 4) × (Fin 4 → ℕ)) : ℂ :=
  ((b.vecs.getD i []).map fun t =>
    (t.2 : ℂ) * sectorW b.a b.spins x.1 x.2 (muDigit b.spins t.1) z).sum

/-- The squared norm `‖Φ_ki(z)‖²_{w_{p_k}} = Σ_{σ, m} w_{p_k}(m) |Φ_ki(σ, m)|²`, weighted by `w_{p_k}` over
the rows of `W_{a_k,p_k}` (stacked over the 24 qubit permutations). -/
noncomputable def normSqPhi (b : Block) (z : Psi) (i : ℕ) : ℝ :=
  wnormSq (rowIdx b.spins) (fun x => wp b.spins x.2) (b.Phi z i)

/-- Every `‖Φ_ki(z)‖²_w` is nonnegative (the weights `w_p` are positive). -/
theorem normSqPhi_nonneg (b : Block) (z : Psi) (i : ℕ) : 0 ≤ b.normSqPhi z i :=
  wnormSq_nonneg (fun x _ => wp_nonneg b.spins x.2) _

end Block

end FormalResearch.FourQubitEntropy.QVCert

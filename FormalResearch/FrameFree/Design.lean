import Mathlib

/-!
# The degree-4 design identity over the twelve long-root lines of `D₄`

Paper P (`critical_chirality_design.tex`, Lemma `lem:design`): for the twelve unit lines
`(e_a ± e_b)/√2`, `a < b`, and all `q, x ∈ ℂ⁴`,
`∑_u |u·q|² |u·x|² = ½(‖q‖²‖x‖² + |x†q|² + |x·q|²)`.
Here `u·q = (q_a ± q_b)/√2` (no complex conjugation).
-/

open Finset

namespace FormalResearch.FrameFree

/-- `‖q‖²`. -/
def nrm2 (q : Fin 4 → ℂ) : ℝ := ∑ k, Complex.normSq (q k)

/-- `x†q`. -/
def hdot (x q : Fin 4 → ℂ) : ℂ := ∑ k, (starRingEnd ℂ) (x k) * q k

/-- `x·q` (no conjugation). -/
def bdot (x q : Fin 4 → ℂ) : ℂ := ∑ k, x k * q k

/-- `|u·q|²|u·x|²` summed over the six pairs `a<b` and both signs, with `u = (e_a ± e_b)/√2`;
the factor `1/4` is `(1/√2)⁴`. -/
noncomputable def longSum (q x : Fin 4 → ℂ) : ℝ :=
  ∑ p ∈ (univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 < p.2),
    ((1 / 4 : ℝ) * (Complex.normSq (q p.1 + q p.2) * Complex.normSq (x p.1 + x p.2)) +
     (1 / 4 : ℝ) * (Complex.normSq (q p.1 - q p.2) * Complex.normSq (x p.1 - x p.2)))

/-- **Design identity** (`lem:design`). -/
theorem design_identity (q x : Fin 4 → ℂ) :
    longSum q x = (1 / 2) * (nrm2 q * nrm2 x + Complex.normSq (hdot x q) + Complex.normSq (bdot x q)) := by
  have hf : ((univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 < p.2)) =
      {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)} := by decide
  unfold longSum nrm2 hdot bdot
  rw [hf]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Fin.sum_univ_four,
    Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Finset.sum_singleton]
  simp
  ring

end FormalResearch.FrameFree

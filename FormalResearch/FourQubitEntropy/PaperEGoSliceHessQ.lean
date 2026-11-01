import FormalResearch.FourQubitEntropy.PaperEGoSliceHess
import FormalResearch.FourQubitEntropy.PaperEGoSliceNormal

/-!
# `thm:fqe-global-overlap`: `FrameHess` is a theorem

`frameHess : FrameHess`: for every `w ∈ ℝ¹⁰`, `wᵀ H(v) w` equals minus the second derivative at `0` of the
real height along the group curve of `w` (`quad_identity`, a polynomial identity), which is `≤ 0` at a
closest point (`hess_gen`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000

open scoped ComplexConjugate Matrix Kronecker
open scoped Matrix.Norms.Operator

namespace FormalResearch.FourQubitEntropy.GO
open CO OD PaperECritical

noncomputable section

/-- The skew matrix of the left generators of `w` (`w₀ G₀₁ + w₂ G₀₂ + w₄ G₀₃ + w₆ G₁₂ + w₇ G₁₃ + w₈ G₂₃`). -/
def Lw (w : Fin 10 → ℝ) : M4R :=
  !![0, w 0, w 2, w 4; -w 0, 0, w 6, w 7; -w 2, -w 6, 0, w 8; -w 4, -w 7, -w 8, 0]

/-- The skew matrix of the right generators of `w` (`w₁ G₀₁ + w₃ G₀₂ + w₅ G₀₃`). -/
def Rw (w : Fin 10 → ℝ) : M4R :=
  !![0, w 1, w 3, w 5; -w 1, 0, 0, 0; -w 3, 0, 0, 0; -w 5, 0, 0, 0]

theorem Lw_skew (w : Fin 10 → ℝ) : (Lw w)ᵀ = -(Lw w) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Lw]

theorem Rw_skew (w : Fin 10 → ℝ) : (Rw w)ᵀ = -(Rw w) := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Rw]

theorem coordIs_sState (v : SV) : CoordIs (sState v) (sX v) (sY v) := by
  intro p q
  rw [magicCoord_sState]
  rfl

theorem sum_fin10 (f : Fin 10 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 := by
  simp [Fin.sum_univ_succ]
  ring

/-- **`FrameHess` is a theorem**: the height Hessian `H(v) ⪰ 0` at a closest-point frame. -/
theorem frameHess : FrameHess := by
  intro v h hf w
  have key := hess_gen hf (coordIs_sState v) (Lw w) (Rw w) (Lw_skew w) (Rw_skew w) (w 9)
  have eq : ∑ i, ∑ j, w i * sHessExp v i j * w j =
      -(-3 * (w 9) ^ 2 * hgt (sX v) (sY v) +
        (3 * (Tm (Lw w) (Rw w) (Tm (Lw w) (Rw w) (sX v))) 0 0 +
          ∑ k : Fin 3, (Tm (Lw w) (Rw w) (Tm (Lw w) (Rw w) (sY v))) k.succ k.succ) +
        6 * (w 9) * ((Tm (Lw w) (Rw w) (sY v)) 0 0 -
          ∑ k : Fin 3, (Tm (Lw w) (Rw w) (sX v)) k.succ k.succ)) := by
    simp only [sum_fin10, Tm_apply, hgt, Matrix.mul_apply, Matrix.add_apply, Matrix.neg_mul,
      Matrix.neg_apply, Fin.sum_univ_four, Fin.sum_univ_three]
    simp [Lw, Rw, sX, sY, sHessExp]
    ring
  rw [sHess_eq_exp]
  linarith


/-- **`thm:fqe-global-overlap` from the slice certificate.** The normal-slice coverage (`sliceNormalForm`),
all positive constraints at a closest point (`frame_constraints`, with `frameHess`), the existence of a
closest point and the fidelity floor are proved; what remains is the polynomial certificate
(`GOSliceCertificate`) and the polynomial identity `SliceQIdentity`. -/
theorem globalOverlap_of_slice_cert (cert : GOSliceCertificate) (hQ : SliceQIdentity) :
    ∀ ψ : Psi, normSqPsi ψ = 1 → GlobalOverlap ψ :=
  globalOverlap_of_slice' cert hQ frameHess

/-! ### Consequences of the constraints used by the certificate -/

/-- The principal `(0,0)` entry of `K₀` gives `t ≥ 0`. -/
theorem SliceConstraints.t_nonneg {v : SV} (hc : SliceConstraints v) : 0 ≤ v 0 := by
  have := hc.K0 (fun i => if i = 0 then 1 else 0)
  simp [Fin.sum_univ_four, sK0, sX] at this
  linarith

/-- The lower principal block of `K₀` gives `Y₃ ⪰ 0`. -/
theorem SliceConstraints.Y3 {v : SV} (hc : SliceConstraints v) : QF (sY3 v) := by
  intro w
  have := hc.K0 (fun i => if h : i = 0 then 0 else w (i.pred h))
  simpa [Fin.sum_univ_four, Fin.sum_univ_three, sK0, sY3, sY] using this

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.GO.frameHess' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms frameHess

/-- info: 'FormalResearch.FourQubitEntropy.GO.globalOverlap_of_slice_cert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms globalOverlap_of_slice_cert

end

end FormalResearch.FourQubitEntropy.GO

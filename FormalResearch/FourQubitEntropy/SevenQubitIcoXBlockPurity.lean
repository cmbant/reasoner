import Mathlib

/-!
# Block Cauchy-Schwarz purity bound (core of `eq:hamming-ball-robust-purity`)

`ResearchNotes/QI/seven_qubit_entanglement/hamming_ball_schmidt.tex`, proof of `thm:hamming-ball-schmidt`:
"Hilbert-Schmidt Cauchy-Schwarz, applied to the two diagonal blocks, gives
`tr ρ² ≥ q²/R + (1-q)²/(d-R)`", where `Q` is a rank-`R` projector and `q = tr(Qρ)`.

Here `ρ` is a *real symmetric* `d × d` matrix (the paper's `ρ` is complex Hermitian; the complex case is
not formalized) and `Q` a real orthogonal projector (`Qᵀ = Q`, `Q² = Q`) with `tr Q = R`.

* `block_purity`: `tr(ρ²) ≥ (tr Qρ)²/R + (tr (1-Q)ρ)²/(d-R)` for `0 < R < d`.
* `robust_purity_bound`: with `tr ρ = 1`, `tr(Qρ) ≥ 1 - η` and `1 - η ≥ R/d`, this gives
  `tr ρ² ≥ (1-η)²/R + η²/(d-R)` (`eq:hamming-ball-robust-purity`, given the projector).
  The existence of a rank-`R` projector `Q` whose range contains the Schmidt support of the ball
  component (from `hamming_rank_le`) is not formalized here.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitIco

open Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option linter.unusedSectionVars false

theorem trace_mul_self_symm (A : Matrix ι ι ℝ) (hA : Aᵀ = A) :
    trace (A * A) = ∑ i, ∑ j, A i j ^ 2 := by
  simp only [trace, diag_apply, mul_apply]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  have : A j i = A i j := by
    have := congrFun (congrFun hA i) j
    simpa using this
  rw [this]; ring

theorem trace_transpose_mul_self (X : Matrix ι ι ℝ) :
    trace (Xᵀ * X) = ∑ i, ∑ j, X i j ^ 2 := by
  simp only [trace, diag_apply, mul_apply, transpose_apply]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  ring

theorem trace_transpose_mul_self_nonneg (X : Matrix ι ι ℝ) : 0 ≤ trace (Xᵀ * X) := by
  rw [trace_transpose_mul_self]
  exact sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _

/-- Monotonicity step of `eq:hamming-ball-robust-purity`: for `0 < R < d`, the function
`q ↦ q²/R + (1-q)²/(d-R)` is nondecreasing on `q ≥ R/d`. -/
theorem robust_purity_mono (R d q q' : ℝ) (hR : 0 < R) (hRd : R < d) (hq : R / d ≤ q)
    (hqq : q ≤ q') :
    q ^ 2 / R + (1 - q) ^ 2 / (d - R) ≤ q' ^ 2 / R + (1 - q') ^ 2 / (d - R) := by
  have hd : 0 < d := hR.trans hRd
  have hdR : 0 < d - R := sub_pos.2 hRd
  have h1 : R ≤ q * d := by
    have := (div_le_iff₀ hd).1 hq; linarith
  have key : q' ^ 2 / R + (1 - q') ^ 2 / (d - R) - (q ^ 2 / R + (1 - q) ^ 2 / (d - R)) =
      (q' - q) * (((q' + q) * (d - R) - (2 - q' - q) * R) / (R * (d - R))) := by
    field_simp
    ring
  have hnum : 0 ≤ (q' + q) * (d - R) - (2 - q' - q) * R := by
    have : (q' + q) * (d - R) - (2 - q' - q) * R = (q' + q) * d - 2 * R := by ring
    rw [this]
    nlinarith
  have : 0 ≤ (q' - q) * (((q' + q) * (d - R) - (2 - q' - q) * R) / (R * (d - R))) :=
    mul_nonneg (by linarith) (div_nonneg hnum (by positivity))
  linarith

/-- Cauchy-Schwarz for the Frobenius pairing of two symmetric matrices. -/
theorem trace_mul_sq_le (A Q : Matrix ι ι ℝ) (hA : Aᵀ = A) (hQ : Qᵀ = Q) :
    trace (A * Q) ^ 2 ≤ trace (A * A) * trace (Q * Q) := by
  rw [trace_mul_self_symm A hA, trace_mul_self_symm Q hQ]
  have h1 : trace (A * Q) = ∑ p : ι × ι, A p.1 p.2 * Q p.1 p.2 := by
    rw [Fintype.sum_prod_type]
    simp only [trace, diag_apply, mul_apply]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have : Q j i = Q i j := by
      have := congrFun (congrFun hQ i) j
      simpa using this
    rw [this]
  rw [h1]
  have := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset (ι × ι)) (fun p => A p.1 p.2)
    (fun p => Q p.1 p.2)
  simpa [Fintype.sum_prod_type] using this

variable (ρ Q : Matrix ι ι ℝ)

theorem compress_bound (hρ : ρᵀ = ρ) (hQ : Qᵀ = Q) (hQ2 : Q * Q = Q) :
    trace (Q * ρ) ^ 2 ≤ trace Q * trace (Q * ρ * Q * (Q * ρ * Q)) := by
  have hQ' : ∀ X : Matrix ι ι ℝ, Q * (Q * X) = Q * X := fun X => by rw [← mul_assoc, hQ2]
  have hA : (Q * ρ * Q)ᵀ = Q * ρ * Q := by
    simp [transpose_mul, hρ, hQ, mul_assoc]
  have h := trace_mul_sq_le (Q * ρ * Q) Q hA hQ
  have e1 : trace (Q * ρ * Q * Q) = trace (Q * ρ) := by
    rw [mul_assoc (Q * ρ), hQ2, trace_mul_comm (Q * ρ) Q]
    simp only [hQ']
  have e2 : trace (Q * Q) = trace Q := by rw [hQ2]
  rw [e1, e2] at h
  calc _ ≤ _ := h
    _ = _ := mul_comm _ _

variable {ρ Q}

/-- `tr(ρEρF) = tr((FρE)(EρF))` for idempotents `E`, `F`. -/
theorem trace_cross (E F : Matrix ι ι ℝ) (hE2 : E * E = E) (hF2 : F * F = F) :
    trace (ρ * E * ρ * F) = trace (F * ρ * E * (E * ρ * F)) := by
  have hE' : ∀ X : Matrix ι ι ℝ, E * (E * X) = E * X := fun X => by rw [← mul_assoc, hE2]
  have : F * ρ * E * (E * ρ * F) = F * (ρ * (E * (ρ * F))) := by
    simp only [mul_assoc, hE']
  rw [this, trace_mul_comm F]
  congr 1
  simp only [mul_assoc, hF2]

/-- Splitting `tr ρ²` along `Q` and `1 - Q`. -/
theorem trace_sq_split (hρ : ρᵀ = ρ) (hQ : Qᵀ = Q) (hQ2 : Q * Q = Q) :
    trace (ρ * ρ) = trace (Q * ρ * Q * (Q * ρ * Q)) +
      trace ((1 - Q) * ρ * (1 - Q) * ((1 - Q) * ρ * (1 - Q))) +
      (trace ((Q * ρ * (1 - Q))ᵀ * (Q * ρ * (1 - Q))) +
        trace ((Q * ρ * (1 - Q)) * (Q * ρ * (1 - Q))ᵀ)) := by
  set P : Matrix ι ι ℝ := 1 - Q with hP
  have hP2 : P * P = P := by
    simp only [hP, sub_mul, mul_sub, one_mul, mul_one, hQ2]; abel
  have hPt : Pᵀ = P := by rw [hP]; simp [hQ]
  have h1 : (1 : Matrix ι ι ℝ) = Q + P := by rw [hP]; abel
  have hsplit : trace (ρ * ρ) = trace (ρ * Q * ρ * Q) + trace (ρ * Q * ρ * P) +
      trace (ρ * P * ρ * Q) + trace (ρ * P * ρ * P) := by
    have h2 : ρ * (Q + P) * ρ * (Q + P) = ρ * ρ := by rw [← h1]; simp
    rw [← h2]
    simp only [mul_add, add_mul, trace_add]
    ring
  have hC : (Q * ρ * P)ᵀ = P * ρ * Q := by
    simp [transpose_mul, hPt, hρ, hQ, mul_assoc]
  rw [hsplit, hC, trace_cross Q Q hQ2 hQ2, trace_cross P P hP2 hP2,
    trace_cross Q P hQ2 hP2, trace_cross P Q hP2 hQ2]
  simp only [mul_assoc]
  ring

/-- **Block Cauchy-Schwarz purity bound.** For a real symmetric `ρ` and an orthogonal projector `Q`
of trace `R`, `0 < R < d`: `tr ρ² ≥ (tr Qρ)²/R + (tr (1-Q)ρ)²/(d - R)`. -/
theorem block_purity (hρ : ρᵀ = ρ) (hQ : Qᵀ = Q) (hQ2 : Q * Q = Q) (R : ℝ) (hR : trace Q = R)
    (hR0 : 0 < R) (hRd : R < Fintype.card ι) :
    trace (Q * ρ) ^ 2 / R + trace ((1 - Q) * ρ) ^ 2 / (Fintype.card ι - R) ≤ trace (ρ * ρ) := by
  set P : Matrix ι ι ℝ := 1 - Q with hP
  have hP2 : P * P = P := by
    simp only [hP, sub_mul, mul_sub, one_mul, mul_one, hQ2]; abel
  have hPt : Pᵀ = P := by rw [hP]; simp [hQ]
  have htP : trace P = Fintype.card ι - R := by
    rw [hP, trace_sub, trace_one, hR]
  have hdR : 0 < (Fintype.card ι : ℝ) - R := sub_pos.2 hRd
  have hA := compress_bound ρ Q hρ hQ hQ2
  have hB := compress_bound ρ P hρ hPt hP2
  rw [hR] at hA
  rw [htP] at hB
  have hsplit := trace_sq_split (ρ := ρ) hρ hQ hQ2
  have c1 := trace_transpose_mul_self_nonneg (Q * ρ * (1 - Q))
  have c2 : 0 ≤ trace ((Q * ρ * (1 - Q)) * (Q * ρ * (1 - Q))ᵀ) := by
    have := trace_transpose_mul_self_nonneg (Q * ρ * (1 - Q))ᵀ
    simpa using this
  rw [hsplit]
  have e1 : trace (Q * ρ) ^ 2 / R ≤ trace (Q * ρ * Q * (Q * ρ * Q)) := by
    rw [div_le_iff₀ hR0]; linarith
  have e2 : trace (P * ρ) ^ 2 / (Fintype.card ι - R) ≤
      trace ((1 - Q) * ρ * (1 - Q) * ((1 - Q) * ρ * (1 - Q))) := by
    rw [div_le_iff₀ hdR]; linarith
  linarith

/-- **`eq:hamming-ball-robust-purity`, given the projector.** If `tr ρ = 1`, `tr(Qρ) ≥ 1 - η` and
`R/d ≤ 1 - η`, then `tr ρ² ≥ (1-η)²/R + η²/(d-R)`. -/
theorem robust_purity_bound (hρ : ρᵀ = ρ) (hQ : Qᵀ = Q) (hQ2 : Q * Q = Q) (R : ℝ)
    (hR : trace Q = R) (hR0 : 0 < R) (hRd : R < Fintype.card ι) (htr : trace ρ = 1) (η : ℝ)
    (hq : 1 - η ≤ trace (Q * ρ)) (hη : R / Fintype.card ι ≤ 1 - η) :
    (1 - η) ^ 2 / R + η ^ 2 / (Fintype.card ι - R) ≤ trace (ρ * ρ) := by
  have hb := block_purity hρ hQ hQ2 R hR hR0 hRd
  have h1 : trace ((1 - Q) * ρ) = 1 - trace (Q * ρ) := by
    rw [sub_mul, one_mul, trace_sub, htr]
  rw [h1] at hb
  have hmono := robust_purity_mono R (Fintype.card ι) (1 - η) (trace (Q * ρ)) hR0 hRd hη hq
  have e : (1 - (1 - η)) = η := by ring
  rw [e] at hmono
  exact hmono.trans hb

end FormalResearch.FourQubitEntropy.SevenQubitIco

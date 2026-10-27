import Mathlib
import FormalResearch.QIB.BlockRealPe

/-!
# `prop:antiunitary` / `prop:blind` for `Helstrom.Pe` under real isotypic coordinates

Namespace `FormalResearch.QIB`.  Claim class: **proved under the explicit hypothesis**
`RealIsotypicCoords n k` (a *real* unitary `W` putting the frame group in isotypic form).  The
unconditional multiplicity-one statement is `Pe_blockdecomp_blind` (`BlockRealPe.lean`); this file only
derives the multiplicity-block conjugation `τ(Θψ) = conj τ(ψ)` needed for `antiunitary_block` and
`sector_blind_iff` for *all* multiplicities.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Matrix ComplexConjugate
open scoped MatrixOrder ComplexOrder

namespace FormalResearch.QIB

open FormalResearch.FrameFree.Helstrom (qf Pe rotK copies Copies)
open FormalResearch.FrameFree.NQubit (Ψ Θ eps cj)

/-- **Hypothesis.** The frame group has isotypic coordinates by a unitary `W` with real entries. -/
def RealIsotypicCoords (n k : ℕ) : Prop :=
  ∃ (r : ℕ) (a b : Fin r → ℕ)
    (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
    (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ W.map conj = W ∧
    IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
      (transportSet W (frameGroup n k))

section

variable {n k r : ℕ} {a b : Fin r → ℕ}
  {W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ}

theorem mulVec_star_of_real (hW : W.map conj = W) (c : Copies n k → ℂ) :
    Wᴴ *ᵥ star c = star (Wᴴ *ᵥ c) := by
  funext i
  have h : ∀ j, star (W j i) = W j i := fun j => by
    have := congrArg (fun M => M j i) hW
    simpa using this
  simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, h, Pi.star_apply, star_sum,
    star_mul']

/-- Under real isotypic coordinates the multiplicity blocks of `(Θψ)^{⊗k}` and `ψ^{⊗k}` are
complex conjugates (`hconj` of `antiunitary_block`). -/
theorem tau_theta_conj (ha : ∀ l, 0 < a l) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hreal : W.map conj = W)
    (hG : IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
      (transportSet W (frameGroup n k))) (ψ : Ψ n) (l : Fin r) :
    tau (Wᴴ *ᵥ copies k (Θ ψ)) l = (tau (Wᴴ *ᵥ copies k ψ) l).map conj := by
  haveI : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  set R := rotK k (fun _ : Fin n => eps) with hR
  have h1 : Wᴴ *ᵥ copies k (Θ ψ) = (Wᴴ * R * W) *ᵥ (star (Wᴴ *ᵥ copies k ψ)) := by
    rw [copies_theta, ← hR, ← mulVec_star_of_real hreal, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_assoc, Matrix.mul_assoc, hW2, Matrix.mul_one]
  have hmem : Wᴴ * R * W ∈ transportSet W (frameGroup n k) := ⟨R, rotEps_mem n k, rfl⟩
  have hun : (Wᴴ * R * W)ᴴ * (Wᴴ * R * W) = 1 := by
    have hR1 := rotEps_unitary n k
    rw [← hR] at hR1
    calc (Wᴴ * R * W)ᴴ * (Wᴴ * R * W) = Wᴴ * (Rᴴ * (W * Wᴴ) * R) * W := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = 1 := by rw [hW2, Matrix.mul_one, hR1, Matrix.mul_one, hW1]
  rw [h1, tau_mulVec_of_mem hG hmem hun, tau_star]

theorem norm_mulVec_of_unitary {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (U : Matrix ι κ ℂ) (hU : Uᴴ * U = 1) (v : κ → ℂ) : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]

/-- **`prop:antiunitary` for `Helstrom.Pe`** (real isotypic coordinates): for a unit vector `ψ^{⊗k}`,
`1 - 2 P_e = Σ_λ ‖Im τ_λ‖₁`. -/
theorem Pe_antiunitary (ha : ∀ l, 0 < a l) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hreal : W.map conj = W)
    (hG : IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
      (transportSet W (frameGroup n k))) (ψ : Ψ n)
    (hψ : star (copies k ψ) ⬝ᵥ copies k ψ = 1) :
    1 - 2 * Pe k ψ = ∑ l, imNorm (tau (Wᴴ *ᵥ copies k ψ) l) := by
  haveI : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  have hWn : (Wᴴ)ᴴ * Wᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hW2
  have h1 : star (Wᴴ *ᵥ copies k ψ) ⬝ᵥ (Wᴴ *ᵥ copies k ψ) = 1 := by
    rw [norm_mulVec_of_unitary _ hWn]; exact hψ
  have h2 : star (Wᴴ *ᵥ copies k (Θ ψ)) ⬝ᵥ (Wᴴ *ᵥ copies k (Θ ψ)) = 1 := by
    rw [norm_mulVec_of_unitary _ hWn, copies_theta, norm_mulVec_of_unitary _ (rotEps_unitary n k),
      star_star, dotProduct_comm]
    exact hψ
  rw [Pe_eq_invErr_coords hW1 hW2]
  exact antiunitary_block hG h1 h2 (tau_theta_conj ha hW1 hW2 hreal hG ψ)

/-- Under `RealIsotypicCoords`, a sector is blind exactly when `τ_λ` is real. -/
theorem Pe_sector_blind_iff (ha : ∀ l, 0 < a l) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hreal : W.map conj = W)
    (hG : IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
      (transportSet W (frameGroup n k))) (ψ : Ψ n) (l : Fin r) :
    tau (Wᴴ *ᵥ copies k ψ) l = tau (Wᴴ *ᵥ copies k (Θ ψ)) l ↔
      imNorm (tau (Wᴴ *ᵥ copies k ψ) l) = 0 := by
  have := sector_blind_iff (a := Wᴴ *ᵥ copies k ψ) (b := Wᴴ *ᵥ copies k (Θ ψ))
    (fun l => tau_theta_conj ha hW1 hW2 hreal hG ψ l) l
  exact this

/-- **`prop:blind`** for `Helstrom.Pe` (real isotypic coordinates, any multiplicities `T` of real
sectors). -/
theorem Pe_ge_blind (ha : ∀ l, 0 < a l) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hreal : W.map conj = W)
    (hG : IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
      (transportSet W (frameGroup n k))) (ψ : Ψ n) (T : Finset (Fin r))
    (hT : ∀ l ∈ T, (tau (Wᴴ *ᵥ copies k ψ) l).map conj = tau (Wᴴ *ᵥ copies k ψ) l) :
    (1 / 2) * ∑ l ∈ T, (tau (Wᴴ *ᵥ copies k ψ) l).trace.re ≤ Pe k ψ := by
  haveI : ∀ l, Nonempty (Fin (a l)) := fun l => ⟨⟨0, ha l⟩⟩
  rw [Pe_eq_invErr_coords hW1 hW2]
  exact invErr_ge_blind hG (fun l => tau_theta_conj ha hW1 hW2 hreal hG ψ l) T hT

/-- The hypothesis `RealIsotypicCoords` yields all of the above at once. -/
theorem RealIsotypicCoords.antiunitary {n k : ℕ} (h : RealIsotypicCoords n k) :
    ∃ (r : ℕ) (a b : Fin r → ℕ)
      (W : Matrix (Copies n k) (Idx (fun l : Fin r => Fin (a l)) (fun l : Fin r => Fin (b l))) ℂ),
      (∀ l, 0 < a l) ∧ Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      IsotypicInvariants (fun l : Fin r => Fin (a l)) (B := fun l : Fin r => Fin (b l))
        (transportSet W (frameGroup n k)) ∧
      ∀ ψ : Ψ n, star (copies k ψ) ⬝ᵥ copies k ψ = 1 →
        (1 - 2 * Pe k ψ = ∑ l, imNorm (tau (Wᴴ *ᵥ copies k ψ) l)) ∧
        ∀ l, (tau (Wᴴ *ᵥ copies k ψ) l = tau (Wᴴ *ᵥ copies k (Θ ψ)) l ↔
          imNorm (tau (Wᴴ *ᵥ copies k ψ) l) = 0) := by
  obtain ⟨r, a, b, W, ha, hW1, hW2, hreal, hG⟩ := h
  exact ⟨r, a, b, W, ha, hW1, hW2, hG, fun ψ hψ =>
    ⟨Pe_antiunitary ha hW1 hW2 hreal hG ψ hψ, fun l => Pe_sector_blind_iff ha hW1 hW2 hreal hG ψ l⟩⟩

end

end FormalResearch.QIB

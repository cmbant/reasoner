import FormalResearch.FourQubitEntropy.QVCheck.Modes
import FormalResearch.FourQubitEntropy.QVBlock.Kron

/-!
# From the array checks to the invariance hypotheses `hV`, `hW` of `QVBlock.quad_eq_zero_of_int_certificate`

Spins are `Fin 4` (twice the spin over two), `multF j = mult j`; `rho0 i j` is the generator matrix; `Vmat p`, `Wmat p` are the
invariant bases of the checker as matrices on `∀ q, Fin (multF (p q))`.
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy.QVBlock

namespace QVCheck

/-- spin labels -/
abbrev Spin := Fin 4

def multF (j : Spin) : ℕ := mult j.val

theorem multF_pos (j : Spin) : 0 < multF j := by
  unfold multF mult; fin_cases j <;> simp

/-- `ρ_j(s_i)` -/
def rho0 (i : Fin 5) (j : Spin) : Matrix (Fin (multF j)) (Fin (multF j)) ℤ :=
  Matrix.of fun a b => rhoAt j.val i.val a.val b.val

/-- code of a spin tuple -/
def pcode (p : Fin 4 → Spin) : ℕ := (((p 0).val * 4 + (p 1).val) * 4 + (p 2).val) * 4 + (p 3).val

theorem spinDigit_pcode (p : Fin 4 → Spin) (q : Fin 4) : spinDigit (pcode p) q.val = (p q).val := by
  have h0 := (p 0).2; have h1 := (p 1).2; have h2 := (p 2).2; have h3 := (p 3).2
  unfold spinDigit pcode
  fin_cases q <;> simp <;> omega

def nnF (p : Fin 4 → Spin) : ℕ := nn (pcode p)

/-- the radices of the multiplicity space of the sector `p` -/
abbrev radix (p : Fin 4 → Spin) : Fin 4 → ℕ := fun q => multF (p q)

theorem sdim_pcode (p : Fin 4 → Spin) : sdim (pcode p) = radix p 0 * radix p 1 * radix p 2 * radix p 3 := by
  have h0 : spinDigit (pcode p) 0 = (p 0).val := spinDigit_pcode p 0
  have h1 : spinDigit (pcode p) 1 = (p 1).val := spinDigit_pcode p 1
  have h2 : spinDigit (pcode p) 2 = (p 2).val := spinDigit_pcode p 2
  have h3 : spinDigit (pcode p) 3 = (p 3).val := spinDigit_pcode p 3
  unfold sdim radix multF
  rw [h0, h1, h2, h3]

/-- right invariants of the checker as a matrix -/
def Vmat (p : Fin 4 → Spin) : Matrix (∀ q, Fin (multF (p q))) (Fin (nnF p)) ℤ :=
  Matrix.of fun x b => vAt (pcode p) b.val (flatIx (radix p) x)

def Wmat (p : Fin 4 → Spin) : Matrix (∀ q, Fin (multF (p q))) (Fin (nnF p)) ℤ :=
  Matrix.of fun x b => wAt (pcode p) b.val (flatIx (radix p) x)

theorem stride_eq (code : ℕ) :
    stride code 0 = mult (spinDigit code 1) * mult (spinDigit code 2) * mult (spinDigit code 3) ∧
    stride code 1 = mult (spinDigit code 2) * mult (spinDigit code 3) ∧
    stride code 2 = mult (spinDigit code 3) ∧ stride code 3 = 1 := by
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [stride, hr, List.foldl_cons, List.foldl_nil]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp

theorem kronGen_eq_kron4 (code i : ℕ) (tr : Bool) (X : Array Int) :
    kronGen code i tr X =
      kron4 (genMat (spinDigit code 0) i) (genMat (spinDigit code 1) i) (genMat (spinDigit code 2) i)
        (genMat (spinDigit code 3) i) (mult (spinDigit code 0)) (mult (spinDigit code 1)) (mult (spinDigit code 2))
        (mult (spinDigit code 3)) tr X := by
  obtain ⟨h0, h1, h2, h3⟩ := stride_eq code
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  unfold kronGen kron4
  rw [hr]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [h0, h1, h2, h3]

theorem genMat_apply (j i a b : ℕ) (ha : a < mult j) (hb : b < mult j) :
    gt (genMat j i) (a * mult j + b) = rhoAt j i a b := by
  have hlt : a * mult j + b < mult j * mult j := by nlinarith [ha, hb]
  unfold genMat rhoAt
  rw [gt_tab, if_pos hlt, Nat.add_assoc]

theorem mEnt_genMat (tr : Bool) (j i a b : ℕ) (ha : a < mult j) (hb : b < mult j) :
    mEnt tr (genMat j i) (mult j) a b = if tr then rhoAt j i b a else rhoAt j i a b := by
  unfold mEnt
  cases tr
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, genMat_apply j i a b ha hb]
  · rw [if_pos rfl, if_pos rfl, genMat_apply j i b a hb ha]

end QVCheck

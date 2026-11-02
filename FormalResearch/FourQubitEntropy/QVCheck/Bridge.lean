import FormalResearch.FourQubitEntropy.QVCheck.Place3
import FormalResearch.FourQubitEntropy.QVFrame.Final

/-!
# Bridge between the checker's block data and the `QVCert` blocks
-/

open Finset
open scoped Matrix
open FormalResearch.FourQubitEntropy

namespace QVCheck

/-- the spin index `n / 2` as an element of `Spin = Fin 4` -/
def spOfNat (n : ℕ) : Spin := ⟨(n / 2) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- the spins of a checker block -/
def spf (b : BlockD) : Fin 4 → Spin := fun r => spOfNat (b.2.1.getD r.val 0)

/-- a `QVCert` block as checker data -/
def toBlockD (b : QVCert.Block) : BlockD := (b.a, (List.finRange 4).map b.spins, b.weights, b.vecs)

/-- the blocks handed to the checker -/
def blocksQ : List BlockD := (List.finRange 14).map fun k => toBlockD (QVCert.blk k)

theorem blk_spins_le : ∀ k : Fin 14, ∀ r : Fin 4, (QVCert.blk k).spins r ≤ 6 ∧ (QVCert.blk k).spins r % 2 = 0 := by
  decide +kernel

theorem blk_vecs_length : ∀ k : Fin 14, (QVCert.blk k).vecs.length = (QVCert.blk k).weights.length := by
  decide +kernel

theorem mult_bridge (j : Spin) : QVCert.mult (2 * j.val) = multF j := by
  obtain ⟨j, hj⟩ := j
  interval_cases j <;> rfl

theorem blkSp_toBlockD (b : QVCert.Block) (r : Fin 4) :
    (blkSp (toBlockD b)).getD r.val 0 = b.spins r / 2 := by
  unfold blkSp toBlockD
  simp [Array.getD, List.getElem_map, List.getElem_finRange]

theorem spf_toBlockD (b : QVCert.Block) (hb : ∀ r : Fin 4, b.spins r ≤ 6) (r : Fin 4) :
    (spf (toBlockD b) r).val = b.spins r / 2 := by
  unfold spf spOfNat toBlockD
  simp only
  have : ((List.finRange 4).map b.spins).getD r.val 0 = b.spins r := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [this]
  have := hb r
  omega

theorem two_mul_spf (b : QVCert.Block) (hb : ∀ r : Fin 4, b.spins r ≤ 6 ∧ b.spins r % 2 = 0) (r : Fin 4) :
    2 * (spf (toBlockD b) r).val = b.spins r := by
  rw [spf_toBlockD b (fun r => (hb r).1) r]
  have := hb r
  omega

/-- the digit function of the checker is that of `QVCert` -/
theorem muDig_eq (spA : Array ℕ) (p' : Fin 4 → ℕ) (hs : ∀ r : Fin 4, mult (spA.getD r.val 0) = QVCert.mult (p' r))
    (c : ℕ) (r : Fin 4) : muDig spA c r.val = QVCert.muDigit p' c r := by
  have h0 : mult (spA[0]?.getD 0) = QVCert.mult (p' 0) := by simpa [Array.getD_eq_getD_getElem?] using hs 0
  have h1 : mult (spA[1]?.getD 0) = QVCert.mult (p' 1) := by simpa [Array.getD_eq_getD_getElem?] using hs 1
  have h2 : mult (spA[2]?.getD 0) = QVCert.mult (p' 2) := by simpa [Array.getD_eq_getD_getElem?] using hs 2
  have h3 : mult (spA[3]?.getD 0) = QVCert.mult (p' 3) := by simpa [Array.getD_eq_getD_getElem?] using hs 3
  have e0 : (Finset.univ.filter (fun l : Fin 4 => (0 : Fin 4) < l)) = {1, 2, 3} := by decide
  have e1 : (Finset.univ.filter (fun l : Fin 4 => (1 : Fin 4) < l)) = {2, 3} := by decide
  have e2 : (Finset.univ.filter (fun l : Fin 4 => (2 : Fin 4) < l)) = {3} := by decide
  have e3 : (Finset.univ.filter (fun l : Fin 4 => (3 : Fin 4) < l)) = ∅ := by decide
  unfold QVCert.muDigit muDig
  fin_cases r
  · simp only [Fin.zero_eta, e0]
    simp [List.range, List.range.loop, h0, h1, h2, h3, Nat.mul_assoc]
  · simp only [Fin.mk_one, e1]
    simp [List.range, List.range.loop, h0, h1, h2, h3]
  · simp only [Fin.reduceFinMk, e2]
    simp [List.range, List.range.loop, h0, h1, h2, h3]
  · simp only [Fin.reduceFinMk, e3]
    simp [List.range, List.range.loop, h0, h1, h2, h3]

end QVCheck

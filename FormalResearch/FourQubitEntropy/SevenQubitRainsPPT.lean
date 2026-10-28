import Mathlib

/-!
# Two-copy PPT formulation of the Rains LP: the local-flip identity and the generating identity
(`prop:rainsppt`, `replica_hierarchy.tex`)

`ResearchNotes/QI/seven_qubit_entanglement/replica_hierarchy.tex`, `prop:rainsppt`. The proposition
says that after local-unitary and site twirling the Rains LP is the two-copy PPT relaxation on the
globally symmetric subspace. Its proof is representation-theoretic (twirling is without loss of
generality, the commutative algebra spanned by the projectors `R_r`, shadow moments reconstruct a
twirled `X`). **None of that is formalized here.** What is formalized are the two exact algebraic
facts the proof computes with:

* `T_swap`: for one qubit, the map `T = (conjugation by 1 ⊗ ε) ∘ (partial transpose on the second
  copy)` sends the swap `F` of two copies of `ℂ²` to `1 - F` (and `1` to `1`); a concrete `4 × 4`
  integer-matrix check (`decide`). This is the relation `T(F_i) = I - F_i` used in the proof.
* `T2_swap0`, `T2_swap1`, `T2_swap01`, `T2_one`, `swap2_comm`, `swap2_sq`: the same check for two
  qubits (`16 × 16` integer matrices, `decide +kernel`): `T(F_S) = ∏_{i∈S}(1 - F_i)` for all four
  subsets `S ⊆ {0, 1}`, `F_i² = 1` and `F_0 F_1 = F_1 F_0`. For general `n` this tensor-factor
  property is the hypothesis `hT` of the next item and is not proved.
* `generating_identity`: abstractly, in a commutative `ℚ`-algebra `A` with involutive elements `F i`
  (`F i * F i = 1`) and a `ℚ`-linear map `T` with `T(∏_{i∈S} F i) = ∏_{i∈S} (1 - F i)` for every `S`,
  for every scalar `t`
  `(∏ F i) * T(∏ ((1 + F i)/2 + t (1 - F i)/2)) = 2^{-n} ∏ (t + (2 F i - 1))`.
  With `P_sym,i = (1+F_i)/2`, `P_asym,i = (1-F_i)/2` the left factor `∏ (P_sym,i + t P_asym,i)` is the
  generating polynomial `∑_r R_r t^r` of the projectors onto exactly `r` locally antisymmetric
  sites, and the right side is `2^{-n} ∏ (t I + Q_i)` with `Q_i = 2F_i - I`: this is the displayed
  identity `F_all ∑_r T(R_r) t^r = 2^{-n} ∏ (t I + Q_i)` of the proof.

Not proved here: the identification of `T` with an actual operator on the `(ℂ²)^{⊗2n}` copy space and
of `T(F_S)` with `∏_{i∈S}(1 - F_i)` for `n > 2` (the tensor-factor property of partial transpose and
conjugation; `hT` is a hypothesis of `generating_identity`), the shadow-coefficient identity `S_{n-r} = 2^n tr(X R_r)`,
twirling, and the bijection between twirled operators and LP points.
-/

namespace FormalResearch.FourQubitEntropy.SevenQubitRainsPPT

open Finset Matrix

/-! ### One qubit, two copies: `T(F) = 1 - F` -/

/-- Operators on `ℂ² ⊗ ℂ²` (copy 1 index, copy 2 index), integer entries. -/
abbrev Op := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℤ

/-- The swap `F` of the two copies. -/
def swapF : Op := Matrix.of fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- Partial transpose on the second copy. -/
def ptr2 (X : Op) : Op := Matrix.of fun x y => X (x.1, y.2) (y.1, x.2)

/-- `E = 1 ⊗ ε` with `ε = ((0, 1), (-1, 0))`, acting on the second copy. -/
def Emat : Op := Matrix.of fun x y =>
  if x.1 = y.1 then (if x.2 = 0 ∧ y.2 = 1 then 1 else if x.2 = 1 ∧ y.2 = 0 then -1 else 0) else 0

/-- `T(X) = E X^{T_2} E^†` (`E` is real, so `E^† = E^T`). -/
def Tmap (X : Op) : Op := Emat * ptr2 X * Emat.transpose

theorem T_swap : Tmap swapF = 1 - swapF := by decide +kernel

theorem T_one : Tmap 1 = 1 := by decide +kernel


/-! ### Two qubits, two copies: the tensor-factor relations `T(F_S) = ∏_{i∈S} (1 - F_i)` -/

/-- Operators on `(ℂ² ⊗ ℂ²)^{⊗2}` (two sites; each site carries a pair of copy bits). -/
abbrev Op2 := Matrix (Fin 2 → Fin 2 × Fin 2) (Fin 2 → Fin 2 × Fin 2) ℤ

/-- The swap `F_i` of the two copies at site `i` (identity on the other site). -/
def swap2 (i : Fin 2) : Op2 := Matrix.of fun x y =>
  if (∀ j, j ≠ i → x j = y j) ∧ x i = ((y i).2, (y i).1) then 1 else 0

/-- Partial transpose on the second copy at both sites. -/
def ptr2' (X : Op2) : Op2 := Matrix.of fun x y =>
  X (fun i => ((x i).1, (y i).2)) (fun i => ((y i).1, (x i).2))

/-- `E = 1 ⊗ ε ⊗ ε` on the second copies. -/
def Emat2 : Op2 := Matrix.of fun x y =>
  if ∀ i, (x i).1 = (y i).1 then ∏ i, (if (x i).2 = 0 ∧ (y i).2 = 1 then (1 : ℤ)
    else if (x i).2 = 1 ∧ (y i).2 = 0 then -1 else 0) else 0

/-- `T(X) = E X^{T_2} E^†` on two sites. -/
def Tmap2 (X : Op2) : Op2 := Emat2 * ptr2' X * Emat2.transpose

theorem T2_one : Tmap2 1 = 1 := by decide +kernel

theorem T2_swap0 : Tmap2 (swap2 0) = 1 - swap2 0 := by decide +kernel

theorem T2_swap1 : Tmap2 (swap2 1) = 1 - swap2 1 := by decide +kernel

theorem T2_swap01 : Tmap2 (swap2 0 * swap2 1) = (1 - swap2 0) * (1 - swap2 1) := by decide +kernel

theorem swap2_comm : swap2 0 * swap2 1 = swap2 1 * swap2 0 := by decide +kernel

theorem swap2_sq (i : Fin 2) : swap2 i * swap2 i = 1 := by
  fin_cases i <;> decide +kernel

/-! ### The generating identity -/

section Generating

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [CommRing A] [Algebra ℚ A]

local notation "C" => algebraMap ℚ A

/-- Multilinear expansion of `∏ (a + b u_i)`. -/
theorem prod_affine_expand (u : ι → A) (a b : ℚ) :
    ∏ i, (C a + C b * u i) =
      ∑ t ∈ (univ : Finset ι).powerset,
        C (b ^ t.card * a ^ (Fintype.card ι - t.card)) * ∏ i ∈ t, u i := by
  have hc : ∀ i, C a + C b * u i = C b * u i + C a := fun i => add_comm _ _
  simp_rw [hc]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htc : t ⊆ univ := Finset.mem_powerset.1 ht
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const, Finset.card_sdiff_of_subset htc,
    Finset.card_univ]
  simp only [map_mul, map_pow]
  ring

variable (F : ι → A) (hF : ∀ i, F i * F i = 1) (T : A →ₗ[ℚ] A)
  (hT : ∀ S : Finset ι, T (∏ i ∈ S, F i) = ∏ i ∈ S, (1 - F i))

include hT in
/-- `T` acts on `∏ (a + b F_i)` by replacing each `F_i` with `1 - F_i`. -/
theorem T_affine (a b : ℚ) :
    T (∏ i, (C a + C b * F i)) = ∏ i, (C a + C b * (1 - F i)) := by
  rw [prod_affine_expand F a b, prod_affine_expand (fun i => 1 - F i) a b, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Algebra.smul_def, map_smul, hT t, Algebra.smul_def]

include hF hT in
/-- `prop:rainsppt` proof identity: `F_all ∑_r T(R_r) t^r = 2^{-n} ∏ (t I + Q_i)`, where
`∑_r R_r t^r = ∏ ((1+F_i)/2 + t (1-F_i)/2)` and `Q_i = 2 F_i - 1`. -/
theorem generating_identity (t : ℚ) :
    (∏ i, F i) * T (∏ i, (C (1 / 2) * (1 + F i) + C t * (C (1 / 2) * (1 - F i)))) =
      C ((1 / 2) ^ Fintype.card ι) * ∏ i, (C t + (C 2 * F i - 1)) := by
  have e1 : ((1 + t) / 2 : ℚ) = 1 / 2 + t * (1 / 2) := by ring
  have e2 : ((1 - t) / 2 : ℚ) = 1 / 2 - t * (1 / 2) := by ring
  have h1 : ∀ i, C (1 / 2) * (1 + F i) + C t * (C (1 / 2) * (1 - F i)) =
      C ((1 + t) / 2) + C ((1 - t) / 2) * F i := by
    intro i
    rw [e1, e2]
    simp only [map_add, map_sub, map_mul]
    ring
  simp_rw [h1]
  rw [T_affine F T hT, ← Finset.prod_mul_distrib]
  have hc : C ((1 / 2 : ℚ) ^ Fintype.card ι) * ∏ i, (C t + (C 2 * F i - 1)) =
      ∏ i, (C (1 / 2) * (C t + (C 2 * F i - 1))) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, map_pow]
  rw [hc]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [e1, e2]
  simp only [map_add, map_sub, map_mul, map_ofNat]
  linear_combination (-(C (1 / 2 : ℚ) - C t * C (1 / 2 : ℚ))) * hF i

end Generating

end FormalResearch.FourQubitEntropy.SevenQubitRainsPPT

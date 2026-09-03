import Mathlib
import FormalResearch.Blaschke.WalshWronskianExactRank
import FormalResearch.Blaschke.WronskianAtomUnitDisk

namespace FormalResearch.Blaschke

open Polynomial

/-- Synthesis from the `n` singleton Walsh coefficient directions into the
full Boolean function space. -/
def singletonWalshSynthesis (n : Nat) :
    (Fin n → ℚ) →ₗ[ℚ] (Finset (Fin n) → ℚ) :=
  Fintype.linearCombination ℚ
    (fun j : Fin n => walshVector ({j} : Finset (Fin n)))

/-- Synthesis from coefficients into the fixed Wronskian atom family. -/
def wronskianAtomSynthesis {n : Nat} (c : Fin n → ℂ) :
    (Fin n → ℚ) →ₗ[ℚ] ℂ[X] :=
  Fintype.linearCombination ℚ (blaschkeWronskianAtom c)

/-- The singleton Walsh vectors are linearly independent because they are a
subfamily of the full Walsh basis. -/
theorem singletonWalsh_linearIndependent {n : Nat} :
    LinearIndependent ℚ
      (fun j : Fin n => walshVector ({j} : Finset (Fin n))) := by
  apply walshVector_linearIndependent.comp
    (fun j : Fin n => ({j} : Finset (Fin n)))
  intro i j hij
  simpa using hij

/-- Hence singleton Walsh coefficient synthesis loses no information. -/
theorem singletonWalshSynthesis_injective (n : Nat) :
    Function.Injective (singletonWalshSynthesis n) :=
  singletonWalsh_linearIndependent.fintypeLinearCombination_injective

/-- For distinct zeros in the open unit disk, atom synthesis is injective. -/
theorem wronskianAtomSynthesis_injective_of_unitDisk {n : Nat}
    (c : Fin n → ℂ) (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Function.Injective (wronskianAtomSynthesis c) :=
  (blaschkeWronskianAtom_linearIndependent_of_unitDisk c hdisk hinj)
    .fintypeLinearCombination_injective

/-- Exact commuting diagram: applying the zero-flip Wronskian map after
singleton Walsh synthesis is `2^n` times atom synthesis. -/
theorem zeroFlipWronskianLin_singletonSynthesis {n : Nat}
    (c : Fin n → ℂ) (a : Fin n → ℚ) :
    zeroFlipWronskianLin c (singletonWalshSynthesis n a) =
      (((2^n : Nat) : ℚ)) • wronskianAtomSynthesis c a := by
  simp [singletonWalshSynthesis, wronskianAtomSynthesis,
    Fintype.linearCombination_apply, zeroFlipWronskianLin_walsh_singleton,
    smul_smul, mul_comm]

/-- Under the ordinary finite-Blaschke hypotheses, the Wronskian transform is
injective on the synthesized singleton Walsh sector.  Thus all surviving
Wronskian information is carried without loss by these `n` Boolean modes. -/
theorem zeroFlipWronskianLin_singletonSynthesis_injective_of_unitDisk
    {n : Nat} (c : Fin n → ℂ)
    (hdisk : ∀ j, ‖c j‖ < 1)
    (hinj : Function.Injective c) :
    Function.Injective
      (fun a : Fin n → ℚ =>
        zeroFlipWronskianLin c (singletonWalshSynthesis n a)) := by
  intro a b hab
  rw [zeroFlipWronskianLin_singletonSynthesis,
    zeroFlipWronskianLin_singletonSynthesis] at hab
  have hpow : (((2^n : Nat) : ℚ)) ≠ 0 := by positivity
  have hatom : wronskianAtomSynthesis c a = wronskianAtomSynthesis c b :=
    smul_right_injective ℂ[X] hpow hab
  exact wronskianAtomSynthesis_injective_of_unitDisk c hdisk hinj hatom

end FormalResearch.Blaschke

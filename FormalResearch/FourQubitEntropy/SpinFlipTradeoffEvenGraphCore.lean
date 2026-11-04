module

public import FormalResearch.NQubit.Graph.MeanPurity
public import FormalResearch.FourQubitEntropy.PurityLPMaskSum

/-!
# Graph states with all vertices of odd degree have `τ_n = 1` (sharpness of `thm:purity-spinflip-tradeoff`)

Source: `spinflip_tradeoff.tex`, `thm:purity-spinflip-tradeoff` (sharpness clause, which uses that a graph state
with every degree odd is an eigenvector of `σ_y^{⊗n}`).  `tau_gsn_eq_one` combines `tau_graphState` (`τ(graphState Γ) = ‖graphState Γ‖⁴` when every degree is odd) with the
normalisation `graphStateNorm Γ = 2^{-n/2} graphState Γ`.  `gK k r = 2^{k - r}` is the summand of the rank sum of `meanRdmPurity_graphStateNorm`.
Claim class: proved.
-/

@[expose] public section


open scoped ComplexConjugate BigOperators
open FormalResearch.NQubit

namespace FormalResearch.FourQubitEntropy.PurityLP

open FormalResearch.NQubit.Pauli FormalResearch.NQubit.Reduced FormalResearch.NQubit.TimeReversal FormalResearch.NQubit.Graph

/-- The summand `2^{k - r}` of the rank sum `Σ_{|S|=k} 2^{k - rk_2 Γ[S,S^c]}`. -/
def gK (k r : ℕ) : ℕ := 2 ^ (k - r)

theorem tau_smul_real {n : ℕ} (c : ℝ) (ψ : Ψ n) :
    tau (fun x => (c : ℂ) * ψ x) = c ^ 4 * tau ψ := by
  have hΘ : Θ (fun x => (c : ℂ) * ψ x) = fun x => (c : ℂ) * Θ ψ x := by
    funext x
    unfold Θ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have hip : ip (fun x => (c : ℂ) * ψ x) (fun x => (c : ℂ) * Θ ψ x) = ((c ^ 2 : ℝ) : ℂ) * ip ψ (Θ ψ) := by
    unfold ip
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [map_mul, Complex.conj_ofReal]
    push_cast
    ring
  unfold tau
  rw [hΘ, hip, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- **Sharpness of `thm:purity-spinflip-tradeoff`**: the normalised graph state of a simple graph all of whose
vertices have odd degree has `τ_n = 1`. -/
theorem tau_gsn_eq_one {n : ℕ} (Γ : Fin n → Fin n → Bool) (hsym : ∀ i j, Γ i j = Γ j i)
    (hirr : ∀ i, Γ i i = false)
    (hodd : ∀ i, Odd (Finset.univ.filter fun j => Γ i j = true).card) : tau (graphStateNorm Γ) = 1 := by
  have h1 : graphStateNorm Γ = fun x => (((Real.sqrt ((2 : ℝ) ^ n))⁻¹ : ℝ) : ℂ) * graphState Γ x := rfl
  rw [h1, tau_smul_real, tau_graphState Γ hsym hirr]
  simp only [hodd, implies_true, ↓reduceIte, nsq_graphState]
  have hpos : (0 : ℝ) < 2 ^ n := by positivity
  have h4 : ((Real.sqrt ((2 : ℝ) ^ n))⁻¹) ^ 4 = (((2 : ℝ) ^ n)⁻¹) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, inv_pow, Real.sq_sqrt hpos.le]
  rw [h4]
  field_simp

end FormalResearch.FourQubitEntropy.PurityLP

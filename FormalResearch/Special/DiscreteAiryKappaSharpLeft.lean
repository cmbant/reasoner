module

public import FormalResearch.Special.DiscreteAiryKappaMain

/-!
# Sharp `κ`: the left mass (plan K1, sharp constant, step 9)

`ksl_left` is the instance of `kl_hahn_left` (`DiscreteAiryKappaEdge`) for the actual `3j` chain at an arbitrary cut `k₁` with
`((k₁+1)h)² ≤ 1 - e²` (`kf_left` of `DiscreteAiryKappaMain` is the case `k₁ = J + 1`): `Ŷ_k² ≤ C_l (Ŷ_{k₁}² + Ŷ_{k₁-1}²)` for all `k ≤ k₁`.
`ksl_sum`: hence `Σ_{0 ≤ k < k₁} Ŷ_k² ≤ k₁ C_l (Ŷ_{k₁}² + Ŷ_{k₁-1}²)`.  The constant `C_l = ke_C(M,σ,x,e,K₀)` depends on `e` only, so a fixed `e` serves
every cut `k₁` with `q_{k₁+1} ≤ √(1 - e²)`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner

namespace FormalResearch.Special

/-- **The left bound at an arbitrary cut.** -/
lemma ksl_left {M σ N k1 : ℤ} {x : ℚ} {e : ℝ} {K0 : ℕ} (hN0 : 0 < N) (hx0 : 0 < (x : ℝ)) (hxe : (x : ℝ) < e) (he1 : e ≤ 1)
    (hK0 : kl_K0real (M : ℝ) (σ : ℝ) (x : ℝ) e ≤ (K0 : ℝ)) (hk1 : (K0 : ℤ) ≤ k1)
    (hband : (((k1 : ℝ) + 1) * (1 / (N : ℝ))) ^ 2 ≤ 1 - e ^ 2) :
    ∀ k : ℤ, k ≤ k1 → hahn3jY M σ N x k ^ 2 ≤
      ke_C (M : ℝ) (σ : ℝ) (x : ℝ) e K0 * (hahn3jY M σ N x k1 ^ 2 + hahn3jY M σ N x (k1 - 1) ^ 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have hh0 : 0 < 1 / (N : ℝ) := by positivity
  refine kl_hahn_left (M := M) (σ := σ) (x := (x : ℝ)) (e := e) (h := 1 / (N : ℝ)) hx0 hxe he1 hh0 (Y := hahn3jY M σ N x)
    (K0 := K0) hK0 (k1 := k1) hk1 hband ?_ ?_
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hk1' : 1 ≤ k := by have := le_max_left |M| |σ|; have := abs_nonneg M; omega
    have := hahn_class_chain M σ N x hN0 k hk1'
    rw [kl_hrAk_eq, kl_hrCk_eq] at this
    exact this
  · intro k hk
    apply hahn_chain_support
    intro ⟨h1, h2, _⟩
    exact absurd (max_le h1 h2) (not_le.2 hk)

/-- **The left mass**: `Σ_{0 ≤ k < k₁} Ŷ_k² ≤ k₁ C_l (Ŷ_{k₁}² + Ŷ_{k₁-1}²)`. -/
lemma ksl_sum {Y : ℤ → ℝ} {Cl : ℝ} {k1 : ℤ} (hk1 : 0 ≤ k1) (hY : ∀ k : ℤ, k ≤ k1 → Y k ^ 2 ≤ Cl * (Y k1 ^ 2 + Y (k1 - 1) ^ 2)) :
    ∑ k ∈ Finset.Ico (0 : ℤ) k1, Y k ^ 2 ≤ (k1 : ℝ) * (Cl * (Y k1 ^ 2 + Y (k1 - 1) ^ 2)) := by
  have h1 : ∑ k ∈ Finset.Ico (0 : ℤ) k1, Y k ^ 2 ≤ ∑ _k ∈ Finset.Ico (0 : ℤ) k1, Cl * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) :=
    Finset.sum_le_sum fun k hk => hY k (by have := (Finset.mem_Ico.1 hk).2; omega)
  refine h1.trans (le_of_eq ?_)
  rw [Finset.sum_const, Int.card_Ico, nsmul_eq_mul]
  have : ((k1 - 0).toNat : ℝ) = (k1 : ℝ) := by
    have : ((k1 - 0).toNat : ℤ) = k1 := by omega
    exact_mod_cast this
  rw [this]

/-- info: 'FormalResearch.Special.ksl_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksl_left

/-- info: 'FormalResearch.Special.ksl_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksl_sum

end FormalResearch.Special

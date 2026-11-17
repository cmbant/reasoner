module

public import FormalResearch.Special.DiscreteAiryOscVoC

/-!
# Discrete Liouville-Green, M3a: the constant-weight Grönwall march (Airy-free)

For an approximate fundamental pair `(φ, ψ)` of a Jacobi row operator with **uniformly bounded** entries (`|φ|, |ψ| ≤ W`), row defects `≤ ε`
and Casoratian `|cas(φ, ψ)| ≥ γ > 0`, the Cramer coefficients `(α_k, β_k) = (vocA, vocB)` of any exact solution move, over a window of `n` rows, by at most
`(|α_m| + |β_m|)(e^Λ - 1)` in `ℓ¹`, `Λ = n · 2Wε/γ`.  This is `voc_march_up`/`voc_march_down` (`DiscreteAiryOscVoC`) with the weight `ω ≡ 1`; in the
oscillatory bulk, `n = O(1/h)` rows with `ε = O(h²)` give `Λ = O(h)`.  **Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma dlg_exp_small {Λ : ℝ} (h0 : 0 ≤ Λ) (h1 : Λ ≤ 1 / 4) : Real.exp Λ - 1 ≤ 2 * Λ := by
  have h := Real.exp_bound_div_one_sub_of_interval h0 (by linarith)
  have h2 : 1 / (1 - Λ) - 1 ≤ 2 * Λ := by
    have : 0 < 1 - Λ := by linarith
    rw [div_sub_one this.ne', div_le_iff₀ this]
    nlinarith
  linarith

/-- **Constant-weight march**: see the module docstring.  `n = N - J` bounds the number of rows between any two bonds of `[J, N]`. -/
theorem dlg_march_const {a c Y φ ψ : ℤ → ℝ} {J N m : ℤ} (hJm : J ≤ m) (hmN : m ≤ N) {γ ε W Λ : ℝ} (hγ : 0 < γ)
    (hε : 0 ≤ ε) (hW : 0 ≤ W) (hY : ∀ k ∈ Icc (J + 1) N, jac a c Y k = 0)
    (hD : ∀ k ∈ Icc J N, γ ≤ |cas a φ ψ k|) (hφ : ∀ k ∈ Icc J (N + 1), |φ k| ≤ W)
    (hψ : ∀ k ∈ Icc J (N + 1), |ψ k| ≤ W) (hdφ : ∀ k ∈ Icc (J + 1) N, |jac a c φ k| ≤ ε)
    (hdψ : ∀ k ∈ Icc (J + 1) N, |jac a c ψ k| ≤ ε) (hΛ : ((N - J : ℤ) : ℝ) * (2 * W * ε / γ) ≤ Λ) :
    ∀ k ∈ Icc J N, |vocA a Y φ ψ k - vocA a Y φ ψ m| + |vocB a Y φ ψ k - vocB a Y φ ψ m| ≤
      (|vocA a Y φ ψ m| + |vocB a Y φ ψ m|) * (Real.exp Λ - 1) := by
  have hlam0 : 0 ≤ 2 * W * ε / γ := by positivity
  have hlamγ : (2 * W * ε / γ) * γ = 2 * W * ε := by field_simp
  have hsum_up : ∀ k ∈ Icc m N, ∑ i ∈ Ioc m k, (fun _ : ℤ => 2 * W * ε / γ) i ≤ Λ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.sum_const, Int.card_Ioc, nsmul_eq_mul]
    refine le_trans ?_ hΛ
    refine mul_le_mul_of_nonneg_right ?_ hlam0
    have : ((k - m).toNat : ℤ) ≤ N - J := by omega
    exact_mod_cast this
  have hsum_dn : ∀ k ∈ Icc J m, ∑ i ∈ Icc (k + 1) m, (fun _ : ℤ => 2 * W * ε / γ) i ≤ Λ := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
    refine le_trans ?_ hΛ
    refine mul_le_mul_of_nonneg_right ?_ hlam0
    have : ((m + 1 - (k + 1)).toNat : ℤ) ≤ N - J := by omega
    exact_mod_cast this
  have hb : ∀ k ∈ Icc J (N + 1), |ψ k| + |φ k| ≤ 2 * W := fun k hk => by linarith [hφ k hk, hψ k hk]
  have hb' : ∀ k ∈ Icc J (N + 1), |ψ k| + |φ k| ≥ 0 := fun k _ => by positivity
  intro k hk
  rw [Finset.mem_Icc] at hk
  rcases le_total m k with hmk | hkm
  · have := (voc_march_up (a := a) (c := c) (Y := Y) (φ := φ) (ψ := ψ) (ω := fun _ => 1)
      (lam := fun _ => 2 * W * ε / γ) (m := m) (K := N) (γ := γ) (Λ := Λ) hγ
      (fun k hk => hY k (by rw [Finset.mem_Icc] at hk ⊢; omega))
      (fun k hk => hD k (by rw [Finset.mem_Icc] at hk ⊢; omega))
      one_pos (fun k _ => ⟨one_pos, le_refl _⟩) (fun k _ => hlam0)
      (fun k hk => by
        rw [Finset.mem_Icc] at hk
        have h1 := hb k (by rw [Finset.mem_Icc]; omega)
        have h2 := hdφ k (by rw [Finset.mem_Icc]; omega)
        simp only [one_mul]
        rw [hlamγ]
        have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        linarith)
      (fun k hk => by
        rw [Finset.mem_Icc] at hk
        have h1 := hb k (by rw [Finset.mem_Icc]; omega)
        have h2 := hdψ k (by rw [Finset.mem_Icc]; omega)
        simp only [one_mul]
        rw [hlamγ]
        have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        linarith)
      hsum_up k (by rw [Finset.mem_Icc]; omega)).2
    simpa using this
  · have := (voc_march_down (a := a) (c := c) (Y := Y) (φ := φ) (ψ := ψ) (ω := fun _ => 1)
      (lam := fun _ => 2 * W * ε / γ) (J := J) (m := m) (γ := γ) (Λ := Λ) hγ
      (fun k hk => hY k (by rw [Finset.mem_Icc] at hk ⊢; omega))
      (fun k hk => hD k (by rw [Finset.mem_Icc] at hk ⊢; omega))
      one_pos (fun k _ => ⟨one_pos, le_refl _⟩) (fun k _ => hlam0)
      (fun k hk => by
        rw [Finset.mem_Icc] at hk
        have h1 := hb k (by rw [Finset.mem_Icc]; omega)
        have h2 := hdφ k (by rw [Finset.mem_Icc]; omega)
        simp only [one_mul]
        rw [hlamγ]
        have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        linarith)
      (fun k hk => by
        rw [Finset.mem_Icc] at hk
        have h1 := hb k (by rw [Finset.mem_Icc]; omega)
        have h2 := hdψ k (by rw [Finset.mem_Icc]; omega)
        simp only [one_mul]
        rw [hlamγ]
        have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        linarith)
      hsum_dn k (by rw [Finset.mem_Icc]; omega)).2
    simpa using this

/-- info: 'FormalResearch.Special.dlg_march_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dlg_march_const

end FormalResearch.Special

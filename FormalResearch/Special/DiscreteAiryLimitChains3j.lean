module

public import FormalResearch.Special.DiscreteAiryLimitChainsCore
public import FormalResearch.Racah.P2ThreeJRec
public import FormalResearch.Racah.P3FluxGauss

/-!
# The actual Wigner `3j` chain is the closed-form Hahn Jacobi chain (Weyl P3, `prop:hahn-class`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:hahn-class` (`eq:adiabaticJacobi`), with the
rank recurrence `eq:3jrank` (DLMF 34.3.15, formalised as `Racah.Phi3j_rank_recurrence`).

**Setting.**  Integers `M, σ, N` (the integer case of the paper; the half-integer case is `DiscreteAiryLimitChains2Half3j`),
`h = 1/N`, `x = 2μ/N` any rational (`PhiX`), the natural-gauge kernel
`Ŷ_k = √(2k+1) Φ_k^{M,σ}(x; 1/N)` (`hahn3jY`; `Φ_L = (-1)^{2L+j₊+m₊} √N (L j₋ j₊; M m₋ m₊)`, `Racah.Phi3j`), extended by the
library's zero extension.  The closed forms are those of `DiscreteAiryLimitHahn`:
`A_k = ½ r_k ẽ((kh)²)` (`hrAk 1 0 M σ h`: `P = 1`, `Q = 0`, `ẽ(s) = √(1-s)`) and `c_k = τ(x - B_k)`
(`hrCk 1 0 1 x M σ h`, `τ = +1`, `β₀ = 0`, `B_k = Mσ/(k(k+1))`).

## Results (proved)

* `hahn_class_chain` (the identification, `prop:hahn-class` in the integer case): for every integer `k ≥ 1`
  `jac (hrAk 1 0 M σ h) (hrCk 1 0 1 x M σ h) Ŷ k = 0`, i.e. `x Ŷ_k = A_{k+1} Ŷ_{k+1} + A_k Ŷ_{k-1} + B_k Ŷ_k` with exactly the
  closed forms used by `discrete_airy_hahn_racah`.  No hypothesis other than `N > 0`.  The rows `k ≥ 1` are all the
  rows (the paper's row `k = 0` of the exceptional sector `M = σ = 0` is `0 = 0`, `eq:3jexceptionalstart`).
* `hahn_chain_support`: `Ŷ_k = 0` outside `max(|M|,|σ|) ≤ k ≤ N-1` (the physical rank range, `kmin = max(|M|,|σ|)`,
  `kmax = N-1`).
* **End conditions** (`hahn_end_upper`, `hahn_end_lower`): `A_{kmax+1} = A_N = 0` (`ẽ((N·N⁻¹)²) = 0`, the hard edge of
  the Airy instance) and `A_{kmin} = 0` for `kmin = max(|M|,|σ|) ≥ 1`.  Together with the support they say that the
  actual chain is the hard-edge solution of the closed-form recurrence on `[kmin, N-1]`, and that
  `Ŷ` on `[kmin, N-1]` solves the truncated recurrence with `A_{N} = 0`.
* `hahn_chain_sq_le` (condition `(R)` of `thm:general-rank-airy`(ii), `3j` case): at every lattice node
  `x_n = xLat M σ N n` and every `k`, `Ŷ_k² ≤ N`, from the Gauss-weight identity `gaussWeight_3j` (`λ² = N`).

## Not formalised

* The half-integer case (`L, M, σ` half-integers, `N ∈ ℤ + ½`) lives on the shifted lattice `k ∈ ℤ + ½`; it is done
  in `DiscreteAiryLimitChains2Half3j` (identification, support, end rows, `(R)`, nodes, Airy limit) on top of
  `DiscreteAiryLimitChains2HalfAiry`.  Lattice nodes `x_n = x` and the `τ = -1` twist are in
  `DiscreteAiryLimitChains2Nodes`, `DiscreteAiryLimitChains2Twist`.
* The identification is for a single `(M, σ, N, x)`; the Airy theorem is for the closed-form chain with fixed real `x`
  (uniformity over `x`, the compact family of shapes, is not provided: an irrational `x` has no exact node).
* The Darboux normalisation (the value of `|κ|`, its phase and sign); `κ ≠ 0` for the `τ = +1` chain is `hahn_chain_kappa`
  (`DiscreteAiryKappaMain`); the other items listed in `DiscreteAiryLimitHahn`.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The natural-gauge `3j` chain `Ŷ_k = √(2k+1) Φ_k^{M,σ}(x; 1/N)`, `k ∈ ℤ`. -/
noncomputable def hahn3jY (M σ N : ℤ) (x : ℚ) (k : ℤ) : ℝ :=
  Real.sqrt (2 * (k : ℝ) + 1) * PhiX (k : ℚ) (M : ℚ) (σ : ℚ) (N : ℚ) x

lemma hahn_tri_iff (k M σ N : ℤ) :
    (IsTri (k : ℚ) (jMinus (N : ℚ) (σ : ℚ)) (jPlus (N : ℚ) (σ : ℚ)) ∧ IsNat ((k : ℚ) + M) ∧
      IsNat ((k : ℚ) - M)) ↔ (|M| ≤ k ∧ |σ| ≤ k ∧ k ≤ N - 1) := by
  have e1 : (k : ℚ) + jMinus (N : ℚ) (σ : ℚ) - jPlus (N : ℚ) (σ : ℚ) = ((k - σ : ℤ) : ℚ) := by
    unfold jMinus jPlus; push_cast; ring
  have e2 : (k : ℚ) - jMinus (N : ℚ) (σ : ℚ) + jPlus (N : ℚ) (σ : ℚ) = ((k + σ : ℤ) : ℚ) := by
    unfold jMinus jPlus; push_cast; ring
  have e3 : -(k : ℚ) + jMinus (N : ℚ) (σ : ℚ) + jPlus (N : ℚ) (σ : ℚ) = ((N - 1 - k : ℤ) : ℚ) := by
    unfold jMinus jPlus; push_cast; ring
  have e4 : (k : ℚ) + M = ((k + M : ℤ) : ℚ) := by push_cast; ring
  have e5 : (k : ℚ) - M = ((k - M : ℤ) : ℚ) := by push_cast; ring
  unfold IsTri
  rw [e1, e2, e3, e4, e5, isNat_intCast_iff, isNat_intCast_iff, isNat_intCast_iff, isNat_intCast_iff,
    isNat_intCast_iff]
  rw [abs_le, abs_le]
  omega

lemma threeJ_eq_zero_of_not_tri {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : ¬ IsTri j₁ j₂ j₃) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  unfold threeJ
  split_ifs
  · rw [triSq_eq_zero_of_not_isTri h]; simp
  · rfl

lemma threeJ_eq_zero_of_not_isNat_add {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : ¬ IsNat (j₁ + m₁)) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  unfold threeJ
  split_ifs
  · rw [fq_of_not_isNat h]; simp
  · rfl

lemma threeJ_eq_zero_of_not_isNat_sub {j₁ j₂ j₃ m₁ m₂ m₃ : ℚ} (h : ¬ IsNat (j₁ - m₁)) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  unfold threeJ
  split_ifs
  · rw [fq_of_not_isNat h]; simp
  · rfl

/-- **Support of the `3j` chain**: `Ŷ_k = 0` unless `max(|M|,|σ|) ≤ k ≤ N-1`. -/
theorem hahn_chain_support (M σ N : ℤ) (x : ℚ) (k : ℤ)
    (hk : ¬ (|M| ≤ k ∧ |σ| ≤ k ∧ k ≤ N - 1)) : hahn3jY M σ N x k = 0 := by
  unfold hahn3jY PhiX Phi3j
  rw [← hahn_tri_iff] at hk
  by_cases h1 : IsTri (k : ℚ) (jMinus (N : ℚ) (σ : ℚ)) (jPlus (N : ℚ) (σ : ℚ))
  · by_cases h2 : IsNat ((k : ℚ) + M)
    · have h3 : ¬ IsNat ((k : ℚ) - M) := fun h3 => hk ⟨h1, h2, h3⟩
      rw [threeJ_eq_zero_of_not_isNat_sub h3]; simp
    · rw [threeJ_eq_zero_of_not_isNat_add h2]; simp
  · rw [threeJ_eq_zero_of_not_tri h1]; simp

lemma etilde_hahn (s : ℝ) : etilde 1 0 s = Real.sqrt (1 - s) := by
  unfold etilde; congr 1; ring

lemma hrCk_hahn (x : ℚ) (M σ : ℝ) (h : ℝ) (k : ℤ) :
    hrCk 1 0 1 (x : ℝ) M σ h k = (x : ℝ) - M * σ / ((k : ℝ) * ((k : ℝ) + 1)) := by
  unfold hrCk
  simp [hrB_hahn]

/-- **`A_{kmax+1} = 0`**: the hard edge of the `3j` chain, `kmax = N - 1`. -/
theorem hahn_end_upper (M σ : ℝ) {N : ℤ} (hN : 0 < N) : hrAk 1 0 M σ (1 / (N : ℝ)) N = 0 := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold hrAk
  rw [etilde_hahn]
  have : ((N : ℝ) * (1 / (N : ℝ))) ^ 2 = 1 := by field_simp
  rw [this]; simp

/-- **`A_{kmin} = 0`** at the lower end `kmin = max(|M|,|σ|) ≥ 1` (`hrAk_lower_zero` for `P = 1`, `Q = 0`). -/
theorem hahn_end_lower (M σ : ℤ) (h : ℝ) (hlo : 1 ≤ max |M| |σ|) :
    hrAk 1 0 (M : ℝ) (σ : ℝ) h (max |M| |σ|) = 0 := hrAk_lower_zero 1 0 h M σ hlo

/-- **`prop:hahn-class` (integer case): the actual `3j` chain is the closed-form Hahn Jacobi chain.**
For integers `M, σ`, `N > 0` and every rational `x` (`x = 2μ/N`), the natural-gauge kernel
`Ŷ_k = √(2k+1) Φ_k^{M,σ}(x; 1/N)` of the Wigner `3j` symbol satisfies
`A_{k+1} Ŷ_{k+1} + A_k Ŷ_{k-1} = c_k Ŷ_k` for every `k ≥ 1`, with the closed forms `A_k = ½ r_k ẽ((kh)²)`
(`ẽ(s) = √(1-s)`, `P = 1`, `Q = 0`), `c_k = x - Mσ/(k(k+1))`, `h = 1/N` of `discrete_airy_hahn_racah`
(`τ = 1`).  The end rows are included: `Ŷ` is the zero extension of the physical chain, and
`A_{kmin} = 0`, `A_{N} = 0` (`hahn_end_lower`, `hahn_end_upper`). -/
theorem hahn_class_chain (M σ N : ℤ) (x : ℚ) (hN : 0 < N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) (1 / (N : ℝ)))
      (hahn3jY M σ N x) k = 0 := by
  refine chain_extend_rows _ _ _ (max |M| |σ|) (N - 1) ?_ ?_ ?_ ?_ k hk
  · intro j hj
    apply hahn_chain_support
    intro ⟨h1, h2, h3⟩
    have : |M| ≤ j ∧ |σ| ≤ j := ⟨h1, h2⟩
    rcases hj with hj | hj
    · exact absurd (max_le h1 h2) (not_le.2 hj)
    · omega
  · exact fun hlo => hahn_end_lower M σ _ hlo
  · intro _
    have := hahn_end_upper (M : ℝ) (σ : ℝ) hN
    simpa using this
  · intro j hj hlo hhi
    have hlo' : |M| ≤ j ∧ |σ| ≤ j := ⟨(le_max_left _ _).trans hlo, (le_max_right _ _).trans hlo⟩
    have hadm := (hahn_tri_iff j M σ N).2 ⟨hlo'.1, hlo'.2, by omega⟩
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    have hrec := Phi3j_rank_recurrence (j : ℚ) (M : ℚ) (σ : ℚ) (N : ℚ) x hNq hadm.1 hadm.2.1 hadm.2.2
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have hrow := natgauge_row (j : ℝ) (Rk (M : ℚ) (σ : ℚ) (j : ℚ) * Real.sqrt (1 - (j : ℝ) ^ 2 / (N : ℝ) ^ 2))
      (Rk (M : ℚ) (σ : ℚ) ((j : ℚ) + 1) * Real.sqrt (1 - ((j : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2))
      (PhiX ((j : ℚ) - 1) (M : ℚ) (σ : ℚ) (N : ℚ) x) (PhiX (j : ℚ) (M : ℚ) (σ : ℚ) (N : ℚ) x)
      (PhiX ((j : ℚ) + 1) (M : ℚ) (σ : ℚ) (N : ℚ) x) (x : ℝ) 0 ((M : ℝ) * σ) hj1 (by
        push_cast at hrec ⊢
        linear_combination hrec)
    have hA1 : hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) ((j + 1 : ℤ)) =
        Rk (M : ℚ) (σ : ℚ) ((j : ℚ) + 1) * Real.sqrt (1 - ((j : ℝ) + 1) ^ 2 / (N : ℝ) ^ 2) /
          (((j : ℝ) + 1) * Real.sqrt (4 * ((j : ℝ) + 1) ^ 2 - 1)) := by
      rw [hrAk_eq _ _ _ _ _ _ (by omega), etilde_hahn]
      unfold Rk
      push_cast
      congr 3
      ring
    have hA0 : hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ)) j =
        Rk (M : ℚ) (σ : ℚ) (j : ℚ) * Real.sqrt (1 - (j : ℝ) ^ 2 / (N : ℝ) ^ 2) /
          ((j : ℝ) * Real.sqrt (4 * (j : ℝ) ^ 2 - 1)) := by
      rw [hrAk_eq _ _ _ _ _ _ hj, etilde_hahn]
      unfold Rk
      push_cast
      congr 3
      ring
    unfold jac hahn3jY
    rw [hA1, hA0, hrCk_hahn]
    push_cast at hrow ⊢
    linear_combination hrow

/-- **Condition `(R)` for the `3j` chain** (`thm:general-rank-airy`(ii), the paper's bound from orthogonality): at every
node `x_n = xLat M σ N n` of an admissible system, every natural-gauge value satisfies `Ŷ_k² ≤ N`, from
`gaussWeight_3j` (`∑_L (2L+1) Φ_L(x_n)² = N`). -/
theorem hahn_chain_sq_le {M σ N : ℚ} (hA : SpecAdm M σ N) (hN : 0 < N) {K : ℕ}
    (hK : (K : ℚ) = N - max |M| |σ|) {n : ℕ} (hn : n < K) {i : ℕ} (hi : i < K) :
    (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) * PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) ^ 2 ≤ N := by
  have h := (gaussWeight_3j hA hN hK hn).1
  unfold lambdaSq3j at h
  rw [← h]
  exact Finset.single_le_sum (f := fun i : ℕ => (2 * ((max |M| |σ| + i : ℚ) : ℝ) + 1) *
    PhiX (max |M| |σ| + i) M σ N (xLat M σ N n) ^ 2)
    (fun j _ => by positivity) (Finset.mem_range.2 hi)

/-- info: 'FormalResearch.Special.hahn_class_chain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_class_chain

/-- info: 'FormalResearch.Special.hahn_chain_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_support

/-- info: 'FormalResearch.Special.hahn_end_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_end_lower

/-- info: 'FormalResearch.Special.hahn_end_upper' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_end_upper

/-- info: 'FormalResearch.Special.hahn_chain_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_sq_le

end FormalResearch.Special

module

public import FormalResearch.Special.DiscreteAiryKappaProfile

/-!
# Transport of the second-order invariant along a band of the Hahn chain (plan K1, step K-1)

`kp_transport`: let `Y` solve the Jacobi rows with the closed-form Hahn coefficients `a_j² = (1+η_j)(1 - (jh)²)/4`, `c_j = x - κ_j` on the sites
`k₀, …, k₀+n`, on a band where `q_*² - q_j² ≥ A² > 0` (`q_j = (j+½)h`, `q_*² = 1-x²`).  Then the Ermakov amplitude form
`I_k(Y) = a_k² P_{k-1} Y_k² + a_k² P_k Y_{k-1}² - 2 a_k s_k Y_k Y_{k-1}` with the profile `P = 2/√(q_*² - q²)` satisfies
`I_{k₀+n} ≤ e^{Σε} I_{k₀}` and `I_{k₀} ≤ e^{2Σε} I_{k₀+n}`, `ε_j = (40/A)(2(h²/A² + η̄_j)/(xA) + 3x h²/A⁶ + 2κ̄_j/A)`,
provided every `ε_j ≤ ½`.  For a band of `n ≤ 1/h` sites `Σ ε = O(h A⁻⁷ + Σ(η̄ + κ̄)/A²)`: **`1 + O(h A⁻⁷)` invariance of the amplitude**
(`DiscreteAiryKappaErmakov` for the abstract mechanism, `DiscreteAiryKappaProfile` for the defect bound).

**Claim class: proved.**  Numerics (not a Lean claim; `r29_num/erm2.py`, 40 digits): on the actual chain `I_k ∈ 2/π (1 ± 2.6·10⁻⁴)` on
`0.15 q_*N ≤ k ≤ 0.9 q_*N` for `N = 1366..1600`.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The per-site relative error `ε(η̄, κ̄) = (40/A)(2(h²/A² + η̄)/(xA) + 3x h²/A⁶ + 2κ̄/A)` of the amplitude form. -/
noncomputable def kpEps (x h A ηb κb : ℝ) : ℝ :=
  40 / A * (2 * (h ^ 2 / A ^ 2 + ηb) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb / A)

/-- **Transport theorem** (see the module docstring). -/
theorem kp_transport {x qs h A : ℝ} {a c η κ ηb κb Y : ℤ → ℝ} {k0 : ℤ} (n : ℕ) (hx : 0 < x)
    (hqs : qs ^ 2 = 1 - x ^ 2) (hh : 0 < h) (hk0 : 1 ≤ k0) (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hband : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + n → A ^ 2 ≤ qs ^ 2 - kpU h j ^ 2)
    (hrow : ∀ i : ℕ, i < n → jac a c Y (k0 + (i : ℤ)) = 0)
    (hapos : ∀ i : ℕ, i ≤ n → 0 < a (k0 + (i : ℤ)))
    (ha : ∀ i : ℕ, i ≤ n → a (k0 + (i : ℤ)) ^ 2 = (1 + η (k0 + (i : ℤ))) * ((1 - (((k0 + (i : ℤ) : ℤ) : ℝ) * h) ^ 2) / 4))
    (hη : ∀ i : ℕ, i ≤ n → |η (k0 + (i : ℤ))| ≤ x ^ 2)
    (hηb : ∀ i : ℕ, i < n → |η (k0 + (i : ℤ))| ≤ ηb (k0 + (i : ℤ)) ∧ |η (k0 + (i : ℤ) + 1)| ≤ ηb (k0 + (i : ℤ)) ∧
      ηb (k0 + (i : ℤ)) ≤ x ^ 2)
    (hc : ∀ i : ℕ, i < n → c (k0 + (i : ℤ)) = x - κ (k0 + (i : ℤ)))
    (hκ : ∀ i : ℕ, i < n → |κ (k0 + (i : ℤ))| ≤ κb (k0 + (i : ℤ)) ∧ κb (k0 + (i : ℤ)) ≤ 1)
    (hε : ∀ i : ℕ, i < n → kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ))) ≤ 1 / 2) :
    kermI a (kpP qs h) Y (k0 + (n : ℤ)) ≤
        Real.exp (∑ i ∈ range n, kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ)))) * kermI a (kpP qs h) Y k0 ∧
      kermI a (kpP qs h) Y k0 ≤
        Real.exp (2 * ∑ i ∈ range n, kpEps x h A (ηb (k0 + (i : ℤ))) (κb (k0 + (i : ℤ)))) *
          kermI a (kpP qs h) Y (k0 + (n : ℤ)) := by
  have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hP : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + n → 0 < kpP qs h j ∧ kpP qs h j ≤ 2 / A := fun j h1 h2 =>
    ⟨kpP_pos hA0 (hband j h1 h2), kpP_le hA0 (hband j h1 h2)⟩
  have hale : ∀ i : ℕ, i ≤ n → a (k0 + (i : ℤ)) ≤ 1 := by
    intro i hi
    have h1 := ha i hi
    have h2 := hη i hi
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg qs]
    have hh1 : 0 ≤ 1 - (((k0 + (i : ℤ) : ℤ) : ℝ) * h) ^ 2 := by
      have hj := hband (k0 + (i : ℤ)) (by omega) (by omega)
      have hU : 0 < kpU h (k0 + (i : ℤ)) := by
        unfold kpU; push_cast
        have : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        exact mul_pos (by linarith) hh
      have hm : 0 ≤ ((k0 + (i : ℤ) : ℤ) : ℝ) * h := by
        have : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
        have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
        push_cast; positivity
      have hlt : ((k0 + (i : ℤ) : ℤ) : ℝ) * h ≤ kpU h (k0 + (i : ℤ)) := by
        unfold kpU; push_cast; nlinarith
      have := kpU_lt_one hqs1 hA0 hj hU
      nlinarith
    have : a (k0 + (i : ℤ)) ^ 2 ≤ 1 := by
      rw [h1]
      have h3 := (abs_le.1 h2).2
      have h4 : (1 - (((k0 + (i : ℤ) : ℤ) : ℝ) * h) ^ 2) / 4 ≤ 1 / 4 := by nlinarith [sq_nonneg (((k0 + (i : ℤ) : ℤ) : ℝ) * h)]
      have h5 : 0 ≤ (1 - (((k0 + (i : ℤ) : ℤ) : ℝ) * h) ^ 2) / 4 := by linarith
      nlinarith
    nlinarith [hapos i hi]
  have hsucc : ∀ i : ℕ, k0 + ((i + 1 : ℕ) : ℤ) = k0 + (i : ℤ) + 1 := fun i => by push_cast; ring
  refine kerm_invariant (a := a) (c := c) (P := kpP qs h) (Y := Y) (ε := fun j => kpEps x h A (ηb j) (κb j)) n hrow
    (fun i hi => hapos i hi.le) (fun i hi => (hP _ (by omega) (by omega)).1) (hP (k0 - 1) le_rfl (by omega)).1
    (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) (fun i hi => hε i hi)
  · -- radicands
    exact kp_rad_ge (a := a) (η := η (k0 + (i : ℤ))) hqs (by omega) hh hA0 (hband _ (by omega) (by omega))
      (hband _ (by omega) (by omega)) (ha i hi) (hη i hi)
  · -- the defect times B
    have hk1 : 1 ≤ k0 + (i : ℤ) := by omega
    have hdef := kp_defect (x := x) (qs := qs) (h := h) (A := A) (ηb := ηb (k0 + (i : ℤ))) (κb := κb (k0 + (i : ℤ)))
      (k := k0 + (i : ℤ)) (a := a) (c := c) (η := η) (κ := κ) hx hqs hh hk1 hA0 hA1 (hband _ (by omega) (by omega))
      (hband _ (by omega) (by omega)) (hband _ (by omega) (by omega)) (ha i hi.le)
      (by have := ha (i + 1) (by omega); rw [hsucc] at this; push_cast at this ⊢; exact this)
      (hηb i hi).1 (hηb i hi).2.1 (hηb i hi).2.2 (hc i hi) (hκ i hi).1
    have hx1 : x ≤ 1 := by nlinarith [sq_nonneg qs]
    have hcb : |c (k0 + (i : ℤ))| ≤ 2 := by
      rw [hc i hi]
      have := abs_le.1 (hκ i hi).1
      have := (hκ i hi).2
      rw [abs_le]; constructor <;> linarith
    have hB := kp_B (a := a) (c := c) (P := kpP qs h) (k := k0 + (i : ℤ)) hA0 (hapos i hi.le) (hale i hi.le)
      (by have := hapos (i + 1) (by omega); rwa [hsucc] at this)
      (by have := hale (i + 1) (by omega); rwa [hsucc] at this) hcb
      (hP _ (by omega) (by omega)).1 (hP _ (by omega) (by omega)).1 (hP _ (by omega) (by omega)).1
      (hP _ (by omega) (by omega)).2 (hP _ (by omega) (by omega)).2 (hP _ (by omega) (by omega)).2
    have hBnn : 0 ≤ 2 * |c (k0 + (i : ℤ)) * kpP qs h (k0 + (i : ℤ)) + kermS a (kpP qs h) (k0 + (i : ℤ) + 1) -
        kermS a (kpP qs h) (k0 + (i : ℤ))| + 4 * kpP qs h (k0 + (i : ℤ)) * |c (k0 + (i : ℤ))| +
        2 * a (k0 + (i : ℤ)) * (kpP qs h (k0 + (i : ℤ)) + kpP qs h (k0 + (i : ℤ) - 1)) := by
      have h1 := (hP (k0 + (i : ℤ)) (by omega) (by omega)).1
      have h2 := (hP (k0 + (i : ℤ) - 1) (by omega) (by omega)).1
      have h3 := hapos i hi.le
      positivity
    unfold kpEps
    calc _ ≤ (2 * (h ^ 2 / A ^ 2 + ηb (k0 + (i : ℤ))) / (x * A) + 3 * x * (h ^ 2 / A ^ 6) + 2 * κb (k0 + (i : ℤ)) / A) *
          (40 / A) := mul_le_mul hdef hB hBnn (by
            have : 0 ≤ ηb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hηb i hi).1
            have : 0 ≤ κb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hκ i hi).1
            positivity)
      _ = _ := by ring
  · -- nonnegativity
    have h1 : 0 ≤ ηb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hηb i hi).1
    have h2 : 0 ≤ κb (k0 + (i : ℤ)) := (abs_nonneg _).trans (hκ i hi).1
    unfold kpEps
    positivity

/-- info: 'FormalResearch.Special.kp_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_transport

end FormalResearch.Special

module

public import FormalResearch.Special.DiscreteAiryLimitHahn
public import FormalResearch.Wigner.Defs

/-!
# From the paper's rank recurrences to the symmetrised Jacobi form (Weyl P3, `prop:hahn-class`, `prop:racah-class`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:hahn-class` (`eq:adiabaticJacobi`) and
`prop:racah-class` (`eq:racahnaturalJacobi`, `eq:racahAkexact`, `eq:racahBkexact`): in the natural gauge
`Ŷ_k = √(2k+1) Φ_k` the exact rank recurrences `eq:3jrank` / `eq:6jrec` are the symmetric three-term recurrences
`x Ŷ_k = A_{k+1} Ŷ_{k+1} + A_k Ŷ_{k-1} + B_k Ŷ_k` with `A_k = E_k / (k √(4k²-1))`, where
`E_k = R_k √(1-k²h²)` (Hahn) resp. `R_k η_k` (Racah).

This module is pure real algebra, shared by the Hahn (`DiscreteAiryLimitChains3j`) and Racah
(`DiscreteAiryLimitChains6j`) identifications:

* `chain_extend_rows`: a sequence supported on `[lo, hi]` that solves the Jacobi rows on `[lo, hi]` and whose
  coefficient vanishes at the two ends (`a lo = 0` if `lo ≥ 1`, `a (hi+1) = 0`) solves every row `k ≥ 1`
  (this is the paper's zero extension at the end rows, `A_{kmin} = 0`, `A_{kmax+1} = 0`).
* `natgauge_row`: the square-root gauge change `E_k, (2k+1)(k(k+1)(x-δ)-mn)` ↦ `A_k, x-δ-mn/(k(k+1))` for one row.
* `hrAk_eq`: for `k ≥ 1`, the closed form `hrAk` of `P3JacobiComparison` (`A_k = ½ r_k ẽ((kh)²)`) equals
  `R_k ẽ((kh)²) / (k √(4k²-1))`.
* `hrB_hahn`, `hrB_racah`: the diagonal closed form `hrB` is `mn/(k(k+1))` (`β₀ = 0`) resp.
  `q_f + mn/(k(k+1))` with `q_f = (2f(f+1)+1-m²-n²)/(8AB)` when `β₀ h² = 1/(4AB)`.

Proved (no hypothesis beyond those displayed); numerical sanity checks of the final identifications for small spins
(sympy `wigner_3j`, `wigner_6j`) were run before formalising.
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry FormalResearch.Wigner

namespace FormalResearch.Special

lemma isNat_intCast_iff (z : ℤ) : IsNat (z : ℚ) ↔ 0 ≤ z := by
  constructor
  · rintro ⟨n, hn⟩
    have : z = (n : ℤ) := by exact_mod_cast hn
    omega
  · intro h
    refine ⟨z.toNat, ?_⟩
    have : (z.toNat : ℤ) = z := Int.toNat_of_nonneg h
    exact_mod_cast this.symm

/-- `IsTri` of three integers is the three integer inequalities. -/
lemma isTri_int_iff (p q r : ℤ) :
    IsTri (p : ℚ) (q : ℚ) (r : ℚ) ↔ 0 ≤ p + q - r ∧ 0 ≤ p - q + r ∧ 0 ≤ -p + q + r := by
  unfold IsTri
  have e1 : (p : ℚ) + q - r = ((p + q - r : ℤ) : ℚ) := by push_cast; ring
  have e2 : (p : ℚ) - q + r = ((p - q + r : ℤ) : ℚ) := by push_cast; ring
  have e3 : -(p : ℚ) + q + r = ((-p + q + r : ℤ) : ℚ) := by push_cast; ring
  rw [e1, e2, e3, isNat_intCast_iff, isNat_intCast_iff, isNat_intCast_iff]

/-- **Zero extension at the end rows.**  `y` vanishes outside `[lo, hi]`, solves the Jacobi rows on `[lo, hi]` (`k ≥ 1`)
and the coefficient vanishes at the lower end (`a lo = 0`, needed only for `lo ≥ 1`) and at `hi + 1`
(`a (hi+1) = 0`, needed only for `hi ≥ 0`); then every row `k ≥ 1` is solved. -/
theorem chain_extend_rows (a c y : ℤ → ℝ) (lo hi : ℤ) (hy : ∀ k, k < lo ∨ hi < k → y k = 0)
    (hlo : 1 ≤ lo → a lo = 0) (hhi : 0 ≤ hi → a (hi + 1) = 0)
    (hrow : ∀ k, 1 ≤ k → lo ≤ k → k ≤ hi → jac a c y k = 0) :
    ∀ k, 1 ≤ k → jac a c y k = 0 := by
  intro k hk
  by_cases h1 : lo ≤ k
  · by_cases h2 : k ≤ hi
    · exact hrow k hk h1 h2
    · have hk0 : y k = 0 := hy k (Or.inr (by omega))
      have hk2 : y (k + 1) = 0 := hy (k + 1) (Or.inr (by omega))
      by_cases h3 : k = hi + 1
      · subst h3
        have : a (hi + 1) = 0 := hhi (by omega)
        unfold jac
        rw [hk0, hk2, this]; ring
      · have hk1 : y (k - 1) = 0 := hy (k - 1) (Or.inr (by omega))
        unfold jac
        rw [hk0, hk1, hk2]; ring
  · have hk0 : y k = 0 := hy k (Or.inl (by omega))
    have hk1 : y (k - 1) = 0 := hy (k - 1) (Or.inl (by omega))
    by_cases h3 : k + 1 = lo
    · have : a lo = 0 := hlo (by omega)
      unfold jac
      rw [hk0, hk1, h3, this]; ring
    · have hk2 : y (k + 1) = 0 := hy (k + 1) (Or.inl (by omega))
      unfold jac
      rw [hk0, hk1, hk2]; ring

/-- **One row of the square-root gauge change.**  For real `k ≥ 1` and the paper's rank row
`(2k+1)(k(k+1)(x-δ) - mn) Φ_k = k E_{k+1} Φ_{k+1} + (k+1) E_k Φ_{k-1}`, the natural-gauge values
`Ŷ_j = √(2j+1) Φ_j` satisfy `A_{k+1} Ŷ_{k+1} + A_k Ŷ_{k-1} = (x - δ - mn/(k(k+1))) Ŷ_k` with
`A_j = E_j / (j √(4j²-1))`. -/
theorem natgauge_row (k E0 E1 p0 p1 p2 x δ mn : ℝ) (hk : 1 ≤ k)
    (hrec : (2 * k + 1) * (k * (k + 1) * (x - δ) - mn) * p1 = k * E1 * p2 + (k + 1) * E0 * p0) :
    E1 / ((k + 1) * Real.sqrt (4 * (k + 1) ^ 2 - 1)) * (Real.sqrt (2 * (k + 1) + 1) * p2) +
        E0 / (k * Real.sqrt (4 * k ^ 2 - 1)) * (Real.sqrt (2 * (k - 1) + 1) * p0) =
      (x - δ - mn / (k * (k + 1))) * (Real.sqrt (2 * k + 1) * p1) := by
  have hk0 : 0 < k := by linarith
  have hs : 0 < Real.sqrt (2 * k + 1) := Real.sqrt_pos.2 (by linarith)
  have ht : 0 < Real.sqrt (2 * k + 3) := Real.sqrt_pos.2 (by linarith)
  have hu : 0 < Real.sqrt (2 * k - 1) := Real.sqrt_pos.2 (by linarith)
  have hs2 : Real.sqrt (2 * k + 1) ^ 2 = 2 * k + 1 := Real.sq_sqrt (by linarith)
  have e1 : Real.sqrt (4 * (k + 1) ^ 2 - 1) = Real.sqrt (2 * k + 1) * Real.sqrt (2 * k + 3) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  have e0 : Real.sqrt (4 * k ^ 2 - 1) = Real.sqrt (2 * k - 1) * Real.sqrt (2 * k + 1) := by
    rw [← Real.sqrt_mul (by linarith)]; congr 1; ring
  have e2 : Real.sqrt (2 * (k + 1) + 1) = Real.sqrt (2 * k + 3) := by congr 1; ring
  have e3 : Real.sqrt (2 * (k - 1) + 1) = Real.sqrt (2 * k - 1) := by congr 1; ring
  rw [e1, e0, e2, e3]
  have hk1 : 0 < k + 1 := by linarith
  generalize Real.sqrt (2 * k + 1) = s at *
  generalize Real.sqrt (2 * k + 3) = t at *
  generalize Real.sqrt (2 * k - 1) = u at *
  have L : E1 / ((k + 1) * (s * t)) * (t * p2) + E0 / (k * (u * s)) * (u * p0) =
      (k * E1 * p2 + (k + 1) * E0 * p0) / (k * (k + 1) * s) := by
    field_simp
  rw [L, ← hrec, ← hs2]
  field_simp

/-- `hrAk` in the form `R_k ẽ / (k √(4k²-1))` (`A:1319`, `eq:racahAkexact`, `eq:adiabaticJacobi`), `k ≥ 1`. -/
theorem hrAk_eq (P Q a b h : ℝ) (k : ℤ) (hk : 1 ≤ k) :
    hrAk P Q a b h k = Real.sqrt (((k : ℝ) ^ 2 - a ^ 2) * ((k : ℝ) ^ 2 - b ^ 2)) *
      etilde P Q (((k : ℝ) * h) ^ 2) / ((k : ℝ) * Real.sqrt (4 * (k : ℝ) ^ 2 - 1)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : 0 < (k : ℝ) := by linarith
  have h4 : 0 < 4 * (k : ℝ) ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt (4 * (k : ℝ) ^ 2 - 1) := Real.sqrt_pos.2 h4
  unfold hrAk rr
  have e : (1 - a ^ 2 / (k : ℝ) ^ 2) * (1 - b ^ 2 / (k : ℝ) ^ 2) / (1 - 1 / (4 * (k : ℝ) ^ 2)) =
      (((k : ℝ) ^ 2 - a ^ 2) * ((k : ℝ) ^ 2 - b ^ 2)) * (2 / ((k : ℝ) * Real.sqrt (4 * (k : ℝ) ^ 2 - 1))) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt h4.le]
    field_simp
    ring
  rw [e, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

/-- **`A_{kmin} = 0`**: at the lower end `kmin = max(|M|,|σ|) ≥ 1` the factor `R_k` of `hrAk` vanishes (any `P, Q, h`). -/
theorem hrAk_lower_zero (P Q h : ℝ) (M σ : ℤ) (hlo : 1 ≤ max |M| |σ|) :
    hrAk P Q (M : ℝ) (σ : ℝ) h (max |M| |σ|) = 0 := by
  rw [hrAk_eq _ _ _ _ _ _ hlo]
  have : ((max |M| |σ| : ℤ) : ℝ) ^ 2 = (M : ℝ) ^ 2 ∨ ((max |M| |σ| : ℤ) : ℝ) ^ 2 = (σ : ℝ) ^ 2 := by
    rcases max_choice |M| |σ| with hc | hc
    · left; rw [hc]; push_cast; exact sq_abs _
    · right; rw [hc]; push_cast; exact sq_abs _
  have hz : (((max |M| |σ| : ℤ) : ℝ) ^ 2 - (M : ℝ) ^ 2) * (((max |M| |σ| : ℤ) : ℝ) ^ 2 - (σ : ℝ) ^ 2) = 0 := by
    rcases this with h1 | h1 <;> rw [h1] <;> ring
  rw [hz]; simp

/-- `B_k` of the Hahn chain (`β₀ = 0`): `mn/(k(k+1))`. -/
theorem hrB_hahn (a b h k : ℝ) : hrB 0 a b h k = a * b / (k * (k + 1)) := by
  unfold hrB; ring

/-- `B_k` of the centred Racah chain: with `β₀ h² = 1/(4AB)` the closed form is
`q_k + mn/(k(k+1))`, `q_k = (2k(k+1)+1-m²-n²)/(8AB)`. -/
theorem hrB_racah (β₀ a b h k A B : ℝ) (hAB : 0 < A * B) (hβ : β₀ * h ^ 2 = 1 / (4 * (A * B))) :
    hrB β₀ a b h k = (2 * k * (k + 1) + 1 - a ^ 2 - b ^ 2) / (8 * A * B) + a * b / (k * (k + 1)) := by
  unfold hrB
  have e : β₀ * (((k + 1 / 2) * h) ^ 2 + h ^ 2 / 4) - β₀ * h ^ 2 * (a ^ 2 + b ^ 2) / 2 =
      β₀ * h ^ 2 * (2 * k * (k + 1) + 1 - a ^ 2 - b ^ 2) / 2 := by ring
  rw [e, hβ]
  have hA : A ≠ 0 := by rintro rfl; simp at hAB
  have hB : B ≠ 0 := by rintro rfl; simp at hAB
  congr 1
  field_simp
  ring

end FormalResearch.Special

module

public import FormalResearch.Special.DiscreteAiryLimitChains2Half3j
public import FormalResearch.Special.DiscreteAiryLimitChains6j
public import FormalResearch.Special.DiscreteAiryLimitChains2Racah

/-!
# The half-integer Wigner `6j` chain is the shifted closed-form centred Racah Jacobi chain (Weyl P3, `prop:racah-class`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:racah-class`, `thm:racahAiryConnection` (the "half-integer `6j`
family", `N ∈ ¼ + ½ℤ`).

**Setting.**  Integers `a, b, c, m, n`; the rank offsets are half-integers `m_ = m + ½`, `n_ = n + ½` (so `f ∈ ℤ + ½`,
`A = a + (n_+1)/2`, `B = b + (m_+1)/2 ∈ ¼ + ½ℤ`, `C = c + ½`; the chain `Ŷ_k = √(2f+1) Φ_f`, `f = k + ½`,
`racah6jYH`, is supported on `halfLo m n ≤ k ≤ min(2b+m, 2a+n)`).  Half-integer `a, b, c` with integer `m, n` or other mixed
parities are *not* covered.

## Results (proved)

* `racah_class_chain_half`, `racah_class_chain_half_neg`: for every `k ≥ 1` the chain (resp. the twist `(-1)^k Ŷ_k`) solves
  `jac (hrAkH P Q m_ n_ h) (hrCkH P Q (±1) x m_ n_ h) Ŷ k = 0`, `P = 1/(4(Ah)²)`, `Q = 1/(4(Bh)²)`, `x = cosA A B C`;
  end rows `racah_end_upper_half`, support `racah_chain_support_half`.
* `racah_chain_abs_le_half`: `(R)`, `|Ŷ_k| ≤ √(4AB/(2C))`, from `gaussWeight_6j`.
* `racah_chain_airy_geom_half_pos/_neg`: the Airy limit (`AiryOutHalf`) for the actual half-integer `6j` chain from the geometric
  data `(α, β, x)` only (the turn derived as in `DiscreteAiryLimitChains2Racah`).

Claim class: **proved**.  Numerics before formalising (sympy `wigner_6j`, exact rational arithmetic): for
`(a,b,c,m,n) = (2,1,1,0,0), (1,1,1,1,0), (3,2,2,0,0), (3,3,2,-1,0)` (so `A, B ∈ ¼ + ½ℤ`, `f ∈ ℤ+½`) the shifted rows
`A_{f+1}Ŷ_{f+1} + A_fŶ_{f-1} = (x - q_f - m_n_/(f(f+1)))Ŷ_f` hold with residual `0` at every row `f ≥ 3/2` of the physical range.

## Not formalised

`κ`, `κ ≠ 0`; mixed parity labels; uniformity; (realisations: `DiscreteAiryLimitChains2Half6jFam`).
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner
  FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The half-integer natural-gauge `6j` chain `Ŷ_k = √(2f+1) Φ_f(a,b,c; m+½, n+½)`, `f = k + ½`. -/
noncomputable def racah6jYH (a b c m n : ℤ) (k : ℤ) : ℝ :=
  Real.sqrt (2 * ((k : ℝ) + 1 / 2) + 1) *
    Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((k : ℚ) + 1 / 2) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2)

lemma racah_tri_f_half (a b m n k : ℤ) :
    (IsTri ((k : ℚ) + 1 / 2) ((b : ℚ) + ((m : ℚ) + 1 / 2)) (b : ℚ) ∧
        IsTri ((k : ℚ) + 1 / 2) (a : ℚ) ((a : ℚ) + ((n : ℚ) + 1 / 2))) ↔
      (halfLo m n ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n) := by
  have e1 : ((k : ℚ) + 1 / 2) + ((b : ℚ) + ((m : ℚ) + 1 / 2)) - b = ((k + m + 1 : ℤ) : ℚ) := by push_cast; ring
  have e2 : ((k : ℚ) + 1 / 2) - ((b : ℚ) + ((m : ℚ) + 1 / 2)) + b = ((k - m : ℤ) : ℚ) := by push_cast; ring
  have e3 : -((k : ℚ) + 1 / 2) + ((b : ℚ) + ((m : ℚ) + 1 / 2)) + b = ((2 * b + m - k : ℤ) : ℚ) := by push_cast; ring
  have e4 : ((k : ℚ) + 1 / 2) + (a : ℚ) - ((a : ℚ) + ((n : ℚ) + 1 / 2)) = ((k - n : ℤ) : ℚ) := by push_cast; ring
  have e5 : ((k : ℚ) + 1 / 2) - (a : ℚ) + ((a : ℚ) + ((n : ℚ) + 1 / 2)) = ((k + n + 1 : ℤ) : ℚ) := by push_cast; ring
  have e6 : -((k : ℚ) + 1 / 2) + (a : ℚ) + ((a : ℚ) + ((n : ℚ) + 1 / 2)) = ((2 * a + n - k : ℤ) : ℚ) := by push_cast; ring
  unfold IsTri
  rw [e1, e2, e3, e4, e5, e6]
  simp only [isNat_intCast_iff]
  unfold halfLo
  omega

lemma racah_tri_l_half (a b m n k : ℤ) :
    (IsTri ((b : ℚ) + ((m : ℚ) + 1 / 2)) (b : ℚ) ((k : ℚ) + 1 / 2) ∧
        IsTri (a : ℚ) ((a : ℚ) + ((n : ℚ) + 1 / 2)) ((k : ℚ) + 1 / 2)) ↔
      (halfLo m n ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n) := by
  have e1 : ((b : ℚ) + ((m : ℚ) + 1 / 2)) + b - ((k : ℚ) + 1 / 2) = ((2 * b + m - k : ℤ) : ℚ) := by push_cast; ring
  have e2 : ((b : ℚ) + ((m : ℚ) + 1 / 2)) - b + ((k : ℚ) + 1 / 2) = ((k + m + 1 : ℤ) : ℚ) := by push_cast; ring
  have e3 : -((b : ℚ) + ((m : ℚ) + 1 / 2)) + b + ((k : ℚ) + 1 / 2) = ((k - m : ℤ) : ℚ) := by push_cast; ring
  have e4 : (a : ℚ) + ((a : ℚ) + ((n : ℚ) + 1 / 2)) - ((k : ℚ) + 1 / 2) = ((2 * a + n - k : ℤ) : ℚ) := by push_cast; ring
  have e5 : (a : ℚ) - ((a : ℚ) + ((n : ℚ) + 1 / 2)) + ((k : ℚ) + 1 / 2) = ((k - n : ℤ) : ℚ) := by push_cast; ring
  have e6 : -(a : ℚ) + ((a : ℚ) + ((n : ℚ) + 1 / 2)) + ((k : ℚ) + 1 / 2) = ((k + n + 1 : ℤ) : ℚ) := by push_cast; ring
  unfold IsTri
  rw [e1, e2, e3, e4, e5, e6]
  simp only [isNat_intCast_iff]
  unfold halfLo
  omega

/-- **Support of the half-integer `6j` chain**: `Ŷ_k = 0` unless `halfLo m n ≤ k ≤ min(2b+m, 2a+n)`. -/
theorem racah_chain_support_half (a b c m n k : ℤ)
    (hk : ¬ (halfLo m n ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n)) : racah6jYH a b c m n k = 0 := by
  unfold racah6jYH Phi6 W6 sixJ
  rw [← racah_tri_l_half] at hk
  have h0 : triSq ((b : ℚ) + ((m : ℚ) + 1 / 2)) (b : ℚ) ((k : ℚ) + 1 / 2) *
      triSq (a : ℚ) ((a : ℚ) + ((n : ℚ) + 1 / 2)) ((k : ℚ) + 1 / 2) = 0 := by
    by_cases h1 : IsTri ((b : ℚ) + ((m : ℚ) + 1 / 2)) (b : ℚ) ((k : ℚ) + 1 / 2)
    · have h2 : ¬ IsTri (a : ℚ) ((a : ℚ) + ((n : ℚ) + 1 / 2)) ((k : ℚ) + 1 / 2) := fun h2 => hk ⟨h1, h2⟩
      rw [triSq_eq_zero_of_not_isTri h2]; ring
    · rw [triSq_eq_zero_of_not_isTri h1]; ring
  have h1 : Real.sqrt (triSq ((b : ℚ) + ((m : ℚ) + 1 / 2)) (b : ℚ) ((k : ℚ) + 1 / 2)) *
      Real.sqrt (triSq (a : ℚ) ((a : ℚ) + ((n : ℚ) + 1 / 2)) ((k : ℚ) + 1 / 2)) = 0 := by
    rw [← Real.sqrt_mul (triSq_nonneg _ _ _), h0]; simp
  have e : ∀ T : ℝ, Real.sqrt (triSq (a : ℚ) (b : ℚ) (c : ℚ)) *
      Real.sqrt (triSq (a : ℚ) ((a : ℚ) + ((n : ℚ) + 1 / 2)) ((k : ℚ) + 1 / 2)) *
      Real.sqrt (triSq ((b : ℚ) + ((m : ℚ) + 1 / 2)) (b : ℚ) ((k : ℚ) + 1 / 2)) *
      Real.sqrt (triSq ((b : ℚ) + ((m : ℚ) + 1 / 2)) ((a : ℚ) + ((n : ℚ) + 1 / 2)) (c : ℚ)) * T = 0 := by
    intro T
    linear_combination (Real.sqrt (triSq (a : ℚ) (b : ℚ) (c : ℚ)) *
      Real.sqrt (triSq ((b : ℚ) + ((m : ℚ) + 1 / 2)) ((a : ℚ) + ((n : ℚ) + 1 / 2)) (c : ℚ)) * T) * h1
  rw [e]; simp

/-- **`A_{hi+1} = 0`**: `hi = min(2b+m, 2a+n)`, so that `hi + 1 + ½ = min(2A, 2B)` and `η = 0`. -/
theorem racah_end_upper_half (a b m n : ℤ) (h : ℝ) (hh : 0 < h) (hA : 0 < wA (a : ℚ) ((n : ℚ) + 1 / 2))
    (hB : 0 < wB (b : ℚ) ((m : ℚ) + 1 / 2)) :
    hrAkH (1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2))
      ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h (min (2 * b + m) (2 * a + n) + 1) = 0 := by
  have hA' : wA (a : ℚ) ((n : ℚ) + 1 / 2) ≠ 0 := hA.ne'
  have hB' : wB (b : ℚ) ((m : ℚ) + 1 / 2) ≠ 0 := hB.ne'
  have hhi : 1 ≤ min (2 * b + m) (2 * a + n) + 1 ∨ min (2 * b + m) (2 * a + n) + 1 ≤ 0 := by omega
  have he : etilde (1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2))
      (1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2))
      (((((min (2 * b + m) (2 * a + n) + 1 : ℤ) : ℝ) + 1 / 2) * h) ^ 2) = 0 := by
    unfold etilde
    have hc : (((min (2 * b + m) (2 * a + n) + 1 : ℤ) : ℝ) + 1 / 2) = 2 * wA (a : ℚ) ((n : ℚ) + 1 / 2) ∨
        (((min (2 * b + m) (2 * a + n) + 1 : ℤ) : ℝ) + 1 / 2) = 2 * wB (b : ℚ) ((m : ℚ) + 1 / 2) := by
      rcases min_choice (2 * b + m) (2 * a + n) with hc | hc
      · right; rw [hc]; unfold wB; push_cast; ring
      · left; rw [hc]; unfold wA; push_cast; ring
    rw [Real.sqrt_eq_zero_of_nonpos]
    rcases hc with hc | hc
    · rw [hc]
      have : 1 - 1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2) *
          ((2 * wA (a : ℚ) ((n : ℚ) + 1 / 2)) * h) ^ 2 = 0 := by
        generalize wA (a : ℚ) ((n : ℚ) + 1 / 2) = A at hA' ⊢
        field_simp; ring
      rw [this]; simp
    · rw [hc]
      have : 1 - 1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2) *
          ((2 * wB (b : ℚ) ((m : ℚ) + 1 / 2)) * h) ^ 2 = 0 := by
        generalize wB (b : ℚ) ((m : ℚ) + 1 / 2) = B at hB' ⊢
        field_simp; ring
      rw [this]; simp
  unfold hrAkH
  rw [he]; simp

/-- **The half-integer `6j` chain is the shifted closed-form centred Racah Jacobi chain** (`prop:racah-class`). -/
theorem racah_class_chain_half (a b c m n : ℤ) (h : ℝ) (hh : 0 < h) (hA : 0 < wA (a : ℚ) ((n : ℚ) + 1 / 2))
    (hB : 0 < wB (b : ℚ) ((m : ℚ) + 1 / 2)) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAkH (1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2))
        ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
      (hrCkH (1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2)) 1
        (cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)))
        ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
      (racah6jYH a b c m n) k = 0 := by
  set A := wA (a : ℚ) ((n : ℚ) + 1 / 2) with hAdef
  set B := wB (b : ℚ) ((m : ℚ) + 1 / 2) with hBdef
  have hA' : A ≠ 0 := hA.ne'
  have hB' : B ≠ 0 := hB.ne'
  have hh' : h ≠ 0 := hh.ne'
  have hAB : 0 < A * B := mul_pos hA hB
  have hη : ∀ j : ℝ, etilde (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) ((j * h) ^ 2) = etaK A B j := by
    intro j
    unfold etilde etaK
    congr 1
    field_simp
  have hβ : Real.sqrt (1 / (4 * (A * h) ^ 2) * (1 / (4 * (B * h) ^ 2))) = 1 / (4 * (A * B * h ^ 2)) := by
    have e : 1 / (4 * (A * h) ^ 2) * (1 / (4 * (B * h) ^ 2)) = (1 / (4 * (A * B * h ^ 2))) ^ 2 := by
      field_simp
    rw [e, Real.sqrt_sq (by positivity)]
  refine chain_extend_rows _ _ _ (halfLo m n) (min (2 * b + m) (2 * a + n)) ?_ ?_ ?_ ?_ k hk
  · intro j hj
    apply racah_chain_support_half
    intro ⟨h1, h2, h3⟩
    rcases hj with hj | hj
    · omega
    · have := min_le_left (2 * b + m) (2 * a + n)
      have := min_le_right (2 * b + m) (2 * a + n)
      omega
  · exact fun hlo => hahn_end_lower_half m n _ _ h hlo
  · intro _
    exact racah_end_upper_half a b m n h hh hA hB
  · intro j hj hlo hhi
    have hhi' : j ≤ 2 * b + m ∧ j ≤ 2 * a + n := ⟨(min_le_left _ _).trans' hhi, (min_le_right _ _).trans' hhi⟩
    have hadm := (racah_tri_f_half a b m n j).2 ⟨hlo, hhi'.1, hhi'.2⟩
    have hrec := Phi6_midpoint_recurrence (a : ℚ) (b : ℚ) (c : ℚ) ((j : ℚ) + 1 / 2) ((m : ℚ) + 1 / 2)
      ((n : ℚ) + 1 / 2) hadm.1 hadm.2
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 / 2 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hrow := natgauge_row ((j : ℝ) + 1 / 2)
      (rootR ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) ((j : ℝ) + 1 / 2) * etaK A B ((j : ℝ) + 1 / 2))
      (rootR ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) ((j : ℝ) + 1 / 2 + 1) * etaK A B ((j : ℝ) + 1 / 2 + 1))
      (Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((j : ℚ) + 1 / 2 - 1) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2))
      (Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((j : ℚ) + 1 / 2) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2))
      (Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((j : ℚ) + 1 / 2 + 1) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2))
      (cosA A B (wC (c : ℚ))) (qf ((j : ℝ) + 1 / 2) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) A B)
      (((m : ℝ) + 1 / 2) * ((n : ℝ) + 1 / 2)) hj1 (by
        push_cast at hrec ⊢
        linear_combination hrec)
    have hA1 : hrAkH (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h ((j + 1 : ℤ)) =
        rootR ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) ((j : ℝ) + 1 / 2 + 1) * etaK A B ((j : ℝ) + 1 / 2 + 1) /
          (((j : ℝ) + 1 / 2 + 1) * Real.sqrt (4 * ((j : ℝ) + 1 / 2 + 1) ^ 2 - 1)) := by
      rw [hrAkH_eq _ _ _ _ _ _ (by omega)]
      have e : (((j + 1 : ℤ) : ℝ) + 1 / 2) = (j : ℝ) + 1 / 2 + 1 := by push_cast; ring
      rw [e, hη]
      unfold rootR
      ring
    have hA0 : hrAkH (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h j =
        rootR ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) ((j : ℝ) + 1 / 2) * etaK A B ((j : ℝ) + 1 / 2) /
          (((j : ℝ) + 1 / 2) * Real.sqrt (4 * ((j : ℝ) + 1 / 2) ^ 2 - 1)) := by
      rw [hrAkH_eq _ _ _ _ _ _ hj, hη]
      unfold rootR
      ring
    have hC : hrCkH (1 / (4 * (A * h) ^ 2)) (1 / (4 * (B * h) ^ 2)) 1 (cosA A B (wC (c : ℚ))) ((m : ℝ) + 1 / 2)
        ((n : ℝ) + 1 / 2) h j =
        cosA A B (wC (c : ℚ)) - qf ((j : ℝ) + 1 / 2) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) A B -
          ((m : ℝ) + 1 / 2) * ((n : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) * (((j : ℝ) + 1 / 2) + 1)) := by
      unfold hrCkH
      rw [hrB_racah _ _ _ _ _ A B hAB (by rw [hβ]; field_simp)]
      unfold qf
      ring
    have ee1 : (((j + 1 : ℤ) : ℚ) + 1 / 2) = (j : ℚ) + 1 / 2 + 1 := by push_cast; ring
    have ee0 : (((j - 1 : ℤ) : ℚ) + 1 / 2) = (j : ℚ) + 1 / 2 - 1 := by push_cast; ring
    have e3 : ((j : ℝ) + 1 + 1 / 2) = (j : ℝ) + 1 / 2 + 1 := by ring
    have e4 : ((j : ℝ) - 1 + 1 / 2) = (j : ℝ) + 1 / 2 - 1 := by ring
    unfold jac racah6jYH
    rw [hA1, hA0, hC, ee1, ee0]
    push_cast at hrow ⊢
    rw [e3, e4]
    linear_combination hrow

/-- **`(R)` for the half-integer `6j` chain**: `|Ŷ_k| ≤ √(4AB/(2C))` for a finite Racah system and physical `c`. -/
theorem racah_chain_abs_le_half (a b c m n : ℤ) {D : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D)
    (i : Fin (D + 1)) (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i) (k : ℤ) :
    |racah6jYH a b c m n k| ≤
      Real.sqrt (4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ))) := by
  by_cases hk : halfLo m n ≤ k ∧ k ≤ 2 * b + m ∧ k ≤ 2 * a + n
  · set lo : ℤ := halfLo m n with hlo
    set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
    have hklo : lo ≤ k := hk.1
    have hkhi : k ≤ hi := le_min hk.2.1 hk.2.2
    have hmax := max_abs_half m n
    have hD : (D : ℤ) = hi - lo := by
      have h1 := hsys.dim
      have h2 := cMax_sub_cMin (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2)
      have e1 : fMin ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) = (lo : ℚ) + 1 / 2 := by
        unfold fMin; rw [hmax]
      have e2 : fMax (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) = (hi : ℚ) + 1 / 2 := by
        rw [hhi]; unfold fMax; push_cast [Int.cast_min]
        simp only [min_def]
        split_ifs <;> linarith
      rw [e1, e2] at h2
      rw [h2] at h1
      have : ((D : ℤ) : ℚ) = ((hi - lo : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast this
    have hjD : (k - lo).toNat < D + 1 := by omega
    set j : Fin (D + 1) := ⟨(k - lo).toNat, hjD⟩ with hj
    have hfj : fPt ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) j = (k : ℚ) + 1 / 2 := by
      unfold fPt
      have e1 : fMin ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) = (lo : ℚ) + 1 / 2 := by
        unfold fMin; rw [hmax]
      have h3 : (((k - lo).toNat : ℕ) : ℤ) = k - lo := Int.toNat_of_nonneg (by omega)
      have h4 : ((((k - lo).toNat : ℕ) : ℤ) : ℚ) = ((k - lo : ℤ) : ℚ) := by rw [h3]
      push_cast at h4
      show fMin ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) + (((k - lo).toNat : ℕ) : ℚ) = (k : ℚ) + 1 / 2
      rw [e1, h4]; ring
    have hsq := racah_chain_sq_le hsys i j
    rw [← hc, hfj] at hsq
    have hk0 : (0 : ℝ) ≤ k := by
      have : (0 : ℤ) ≤ k := by have := halfLo_nonneg m n; omega
      exact_mod_cast this
    have hY : (racah6jYH a b c m n k) ^ 2 =
        (2 * (((k : ℚ) + 1 / 2 : ℚ) : ℝ) + 1) *
          Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((k : ℚ) + 1 / 2) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) ^ 2 := by
      unfold racah6jYH
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      push_cast; ring
    exact Real.abs_le_sqrt (by rw [hY]; exact hsq)
  · rw [racah_chain_support_half a b c m n k hk]
    simp

/-- info: 'FormalResearch.Special.racah_class_chain_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_class_chain_half

/-- info: 'FormalResearch.Special.racah_chain_abs_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_abs_le_half

lemma hrCkH_neg (P Q x a b h : ℝ) (k : ℤ) : hrCkH P Q (-1) x a b h k = -hrCkH P Q 1 x a b h k := by
  unfold hrCkH; ring

/-- **`τ = -1` branch of the half-integer `6j` chain**: the twist `(-1)^k Ŷ_k`. -/
theorem racah_class_chain_half_neg (a b c m n : ℤ) (h : ℝ) (hh : 0 < h) (hA : 0 < wA (a : ℚ) ((n : ℚ) + 1 / 2))
    (hB : 0 < wB (b : ℚ) ((m : ℚ) + 1 / 2)) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAkH (1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2))
        ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
      (hrCkH (1 / (4 * (wA (a : ℚ) ((n : ℚ) + 1 / 2) * h) ^ 2)) (1 / (4 * (wB (b : ℚ) ((m : ℚ) + 1 / 2) * h) ^ 2)) (-1)
        (cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)))
        ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
      (fun j => (-1 : ℝ) ^ j * racah6jYH a b c m n j) k = 0 := by
  have hh' := jac_twist_zero (racah_class_chain_half a b c m n h hh hA hB k hk)
  convert hh' using 2
  ext j
  exact hrCkH_neg _ _ _ _ _ _ _

/-- **Airy limit of the actual half-integer `6j` chain from the geometric data, `τ = +1`** (`thm:racahAiryConnection`,
half-integer family; no turn hypotheses). -/
theorem racah_chain_airy_geom_half_pos (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' →
        ∀ (i : Fin (D' + 1)) (h : ℝ),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        AiryOutHalf (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (racahQs α β x) (racah6jYH a b c m n)
          (Real.sqrt (4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ))))
          A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    airy_chain_compose_half (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (by positivity) (by positivity)
      ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) 1 x (racahQs α β x) hqs (by norm_num) hκ hαq hβq hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  have hA : 0 < wA (a : ℚ) ((n : ℚ) + 1 / 2) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) ((m : ℚ) + 1 / 2) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine H h (racah6jYH a b c m n) _ hh hhδ (fun k hk => ?_) (fun k => racah_chain_abs_le_half a b c m n hsys i hc k)
  have := racah_class_chain_half a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  exact this

/-- **Airy limit of the actual half-integer `6j` chain from the geometric data, `τ = -1`** (twisted chain). -/
theorem racah_chain_airy_geom_half_neg (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : 0 < (α - β * x) * (β - α * x)) (m n : ℤ) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D' →
        ∀ (i : Fin (D' + 1)) (h : ℝ),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i → 0 < h → h ≤ δ0 ^ 3 →
        wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α → wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β →
        cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x →
        AiryOutHalf (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (-1) x (racahQs α β x)
          (fun j => (-1 : ℝ) ^ j * racah6jYH a b c m n j)
          (Real.sqrt (4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ))))
          A0 r δ0 C Cosc Ctop W Cmu ξ0 D h := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_neg hα hβ hx1 hx2 hprod
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    airy_chain_compose_half (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) (by positivity) (by positivity)
      ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) (-1) x (racahQs α β x) hqs (by norm_num) hκ hαq hβq hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro a b c D' hsys i h hc hh hhδ hAh hBh hx
  have hA : 0 < wA (a : ℚ) ((n : ℚ) + 1 / 2) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hB : 0 < wB (b : ℚ) ((m : ℚ) + 1 / 2) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  refine H h _ _ hh hhδ (fun k hk => ?_) (fun k => ?_)
  · have := racah_class_chain_half_neg a b c m n h hh hA hB k hk
    rw [hAh, hBh, hx] at this
    exact this
  · have h1 : |(-1 : ℝ) ^ k| = 1 := by simp [abs_zpow]
    rw [abs_mul, h1, one_mul]
    exact racah_chain_abs_le_half a b c m n hsys i hc k

/-- info: 'FormalResearch.Special.racah_chain_airy_geom_half_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_geom_half_pos

/-- info: 'FormalResearch.Special.racah_chain_airy_geom_half_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_chain_airy_geom_half_neg

end FormalResearch.Special

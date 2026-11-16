module

public import FormalResearch.Special.DiscreteAiryLimitChains2HalfAiry
public import FormalResearch.Special.DiscreteAiryLimitChains3j

/-!
# The half-integer Wigner `3j` chain is the shifted closed-form Hahn Jacobi chain (Weyl P3, `prop:hahn-class`)

Source: `Weyl/P3/paper/weyl_midpoint_semiclassics.tex`, `prop:hahn-class`, `thm:hahnAiryConnection` for half-integer `N, M, σ`.

**Setting.**  Half-integer data `M_ = M + ½`, `σ_ = σ + ½`, `N_ = N + ½` (`M, σ, N ∈ ℤ`; all of `L, M_, σ_, N_` are congruent mod
1, so the half-integer chain has `L ∈ ℤ + ½`).  Writing `L = k + ½` (`k ∈ ℤ`) the chain is
`Ŷ_k = √(2L+1) Φ_L^{M_,σ_}(x; 1/N_)` (`hahn3jYH`), supported on `halfLo M σ ≤ k ≤ N - 1`,
`halfLo M σ = max(M, -M-1, σ, -σ-1)` (`L_0 = max(|M_|,|σ_|) = halfLo + ½`).

## Results (proved)

* `hahn_class_chain_half`: for every `k ≥ 1`, `jac (hrAkH 1 0 M_ σ_ h) (hrCkH 1 0 1 x M_ σ_ h) Ŷ k = 0`, `h = 1/N_`
  (the shifted closed forms of `DiscreteAiryLimitChains2HalfAiry`), with end rows `A_{lo} = 0`
  (`hahn_end_lower_half`), `A_{N} = 0` (`hahn_end_upper_half`) and the support lemma `hahn_chain_support_half`.
* `hahn_chain_abs_le_half`: `(R)`, `|Ŷ_k| ≤ √N_` for all `k`, from `gaussWeight_3j`.
* `hahn_node_exists_half`, `hahn_node_obstruction_half`: nodes `x_n = p/q` (`gcd(p,q) = 1` for the necessity) of the
  half-integer lattice exist for infinitely many `N` iff `p, q` are odd and `w = (p+q)/2 ≡ 1 + |M+σ+1| (mod 2)` (`N_ = (2N+1)/2`, `N = q(2u+1)/2 - 1/2`).
* `hahn_chain_airy_half`, `hahn_chain_airy_half_infinite`: the Airy limit for the actual half-integer `3j` chain at the nodes
  `x_n = x ∈ (0,1)` (`AiryOutHalf`) and along an infinite sequence of `N`.

Claim class: **proved**.  Numerics before formalising (sympy `wigner_3j`, exact): the shifted rows hold with residual exactly `0`
for `(M_, σ_, N_, n) = (½, ½, 7/2, 1), (3/2, ½, 9/2, 0), (-½, ½, 9/2, 2)`; the node criterion (`q` odd, `p + q = 2w`,
`w ≡ 1 + |M+σ+1| mod 2`) agrees with a brute-force search over `N < 120` in all 18 tested cases
(`(M,σ) = (0,0), (1,0)`, `x ∈ {±1/3, 1/2, ±3/5, 1/5, 1/7, 3/7, 5/7}`; e.g. `(0,0)`, `x = 1/3`: `(N,n) = (1,0), (4,2), (7,4)`).

## Not formalised

`κ`, `κ ≠ 0`; the `Ai/Bi` pair; uniformity over `x`; half-integer `6j` data other than `(a,b,c) ∈ ℤ³`, `m, n ∈ ℤ+½`
(`DiscreteAiryLimitChains2Half6j`); `x < 0`.
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `max(|M_|, |σ_|) = halfLo M σ + ½`, `halfLo M σ = max(M, -M-1, σ, -σ-1)`. -/
def halfLo (M σ : ℤ) : ℤ := max (max M (-M - 1)) (max σ (-σ - 1))

/-- The half-integer natural-gauge `3j` chain `Ŷ_k = √(2L+1) Φ_L^{M+½,σ+½}(x; 1/(N+½))`, `L = k + ½`. -/
noncomputable def hahn3jYH (M σ N : ℤ) (x : ℚ) (k : ℤ) : ℝ :=
  Real.sqrt (2 * ((k : ℝ) + 1 / 2) + 1) *
    PhiX ((k : ℚ) + 1 / 2) ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) x

lemma halfLo_nonneg (M σ : ℤ) : 0 ≤ halfLo M σ := by unfold halfLo; omega

lemma max_abs_half (M σ : ℤ) :
    max |(M : ℚ) + 1 / 2| |(σ : ℚ) + 1 / 2| = (halfLo M σ : ℚ) + 1 / 2 := by
  unfold halfLo
  push_cast [Int.cast_max]
  rcases abs_cases ((M : ℚ) + 1 / 2) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases ((σ : ℚ) + 1 / 2) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
  rw [h1, h2] <;> simp only [max_def] <;> split_ifs <;> linarith

lemma hahn_tri_half (k M σ N : ℤ) :
    (IsTri ((k : ℚ) + 1 / 2) (jMinus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2))
        (jPlus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2)) ∧ IsNat (((k : ℚ) + 1 / 2) + ((M : ℚ) + 1 / 2)) ∧
      IsNat (((k : ℚ) + 1 / 2) - ((M : ℚ) + 1 / 2))) ↔ (halfLo M σ ≤ k ∧ k ≤ N - 1) := by
  have e1 : ((k : ℚ) + 1 / 2) + jMinus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) - jPlus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) =
      ((k - σ : ℤ) : ℚ) := by unfold jMinus jPlus; push_cast; ring
  have e2 : ((k : ℚ) + 1 / 2) - jMinus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) + jPlus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) =
      ((k + σ + 1 : ℤ) : ℚ) := by unfold jMinus jPlus; push_cast; ring
  have e3 : -((k : ℚ) + 1 / 2) + jMinus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) + jPlus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) =
      ((N - 1 - k : ℤ) : ℚ) := by unfold jMinus jPlus; push_cast; ring
  have e4 : ((k : ℚ) + 1 / 2) + ((M : ℚ) + 1 / 2) = ((k + M + 1 : ℤ) : ℚ) := by push_cast; ring
  have e5 : ((k : ℚ) + 1 / 2) - ((M : ℚ) + 1 / 2) = ((k - M : ℤ) : ℚ) := by push_cast; ring
  unfold IsTri
  rw [e1, e2, e3, e4, e5, isNat_intCast_iff, isNat_intCast_iff, isNat_intCast_iff, isNat_intCast_iff,
    isNat_intCast_iff]
  unfold halfLo
  omega

/-- **Support of the half-integer `3j` chain**: `Ŷ_k = 0` unless `halfLo M σ ≤ k ≤ N - 1`. -/
theorem hahn_chain_support_half (M σ N : ℤ) (x : ℚ) (k : ℤ) (hk : ¬ (halfLo M σ ≤ k ∧ k ≤ N - 1)) :
    hahn3jYH M σ N x k = 0 := by
  unfold hahn3jYH PhiX Phi3j
  rw [← hahn_tri_half] at hk
  by_cases h1 : IsTri ((k : ℚ) + 1 / 2) (jMinus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2))
      (jPlus ((N : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2))
  · by_cases h2 : IsNat (((k : ℚ) + 1 / 2) + ((M : ℚ) + 1 / 2))
    · have h3 : ¬ IsNat (((k : ℚ) + 1 / 2) - ((M : ℚ) + 1 / 2)) := fun h3 => hk ⟨h1, h2, h3⟩
      rw [threeJ_eq_zero_of_not_isNat_sub h3]; simp
    · rw [threeJ_eq_zero_of_not_isNat_add h2]; simp
  · rw [threeJ_eq_zero_of_not_tri h1]; simp

/-- `hrAkH` in the form `R_L ẽ / (L √(4L²-1))`, `L = k + ½`, `k ≥ 1`. -/
theorem hrAkH_eq (P Q a b h : ℝ) (k : ℤ) (hk : 1 ≤ k) :
    hrAkH P Q a b h k = Real.sqrt ((((k : ℝ) + 1 / 2) ^ 2 - a ^ 2) * (((k : ℝ) + 1 / 2) ^ 2 - b ^ 2)) *
      etilde P Q ((((k : ℝ) + 1 / 2) * h) ^ 2) / (((k : ℝ) + 1 / 2) * Real.sqrt (4 * ((k : ℝ) + 1 / 2) ^ 2 - 1)) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set κ : ℝ := (k : ℝ) + 1 / 2 with hκdef
  have hk1 : (3 / 2 : ℝ) ≤ κ := by rw [hκdef]; linarith
  have hk0 : 0 < κ := by linarith
  have h4 : 0 < 4 * κ ^ 2 - 1 := by nlinarith
  have hs : 0 < Real.sqrt (4 * κ ^ 2 - 1) := Real.sqrt_pos.2 h4
  unfold hrAkH rr
  rw [← hκdef]
  have e : (1 - a ^ 2 / κ ^ 2) * (1 - b ^ 2 / κ ^ 2) / (1 - 1 / (4 * κ ^ 2)) =
      ((κ ^ 2 - a ^ 2) * (κ ^ 2 - b ^ 2)) * (2 / (κ * Real.sqrt (4 * κ ^ 2 - 1))) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt h4.le]
    field_simp
    ring
  rw [e, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (by positivity)]
  field_simp

/-- **`A_{lo} = 0`** at the lower end `lo = halfLo M σ ≥ 1`. -/
theorem hahn_end_lower_half (M σ : ℤ) (P Q h : ℝ) (hlo : 1 ≤ halfLo M σ) :
    hrAkH P Q ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) h (halfLo M σ) = 0 := by
  rw [hrAkH_eq _ _ _ _ _ _ hlo]
  have hz : ((((halfLo M σ : ℤ) : ℝ) + 1 / 2) ^ 2 - ((M : ℝ) + 1 / 2) ^ 2) *
      ((((halfLo M σ : ℤ) : ℝ) + 1 / 2) ^ 2 - ((σ : ℝ) + 1 / 2) ^ 2) = 0 := by
    have hc : halfLo M σ = M ∨ halfLo M σ = -M - 1 ∨ halfLo M σ = σ ∨ halfLo M σ = -σ - 1 := by
      unfold halfLo; omega
    rcases hc with hc | hc | hc | hc
    · rw [hc]; ring
    · rw [hc]; push_cast; ring
    · rw [hc]; ring
    · rw [hc]; push_cast; ring
  rw [hz]; simp

/-- **`A_{N} = 0`** (hard edge `L = N_ = N + ½`, `h = 1/N_`). -/
theorem hahn_end_upper_half (M σ : ℝ) {N : ℤ} (hN : 0 ≤ N) :
    hrAkH 1 0 M σ (1 / ((N : ℝ) + 1 / 2)) N = 0 := by
  have hN' : (N : ℝ) + 1 / 2 ≠ 0 := by have : (0 : ℝ) ≤ N := by exact_mod_cast hN
                                       linarith
  unfold hrAkH
  rw [etilde_hahn]
  have : (((N : ℝ) + 1 / 2) * (1 / ((N : ℝ) + 1 / 2))) ^ 2 = 1 := by field_simp
  rw [this]; simp

/-- **The half-integer `3j` chain is the shifted closed-form Hahn Jacobi chain** (`prop:hahn-class`, `N_ = N + ½`). -/
theorem hahn_class_chain_half (M σ N : ℤ) (x : ℚ) (hN : 0 ≤ N) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
      (hrCkH 1 0 1 (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)))
      (hahn3jYH M σ N x) k = 0 := by
  have hNq : (0 : ℚ) < (N : ℚ) + 1 / 2 := by
    have : (0 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  have hNr : (0 : ℝ) < (N : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  refine chain_extend_rows _ _ _ (halfLo M σ) (N - 1) ?_ ?_ ?_ ?_ k hk
  · intro j hj
    apply hahn_chain_support_half
    intro ⟨h1, h2⟩
    omega
  · exact fun hlo => hahn_end_lower_half M σ _ _ _ hlo
  · intro _
    have := hahn_end_upper_half ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) hN
    simpa using this
  · intro j hj hlo hhi
    have hadm := (hahn_tri_half j M σ N).2 ⟨hlo, hhi⟩
    have hrec := Phi3j_rank_recurrence ((j : ℚ) + 1 / 2) ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) x hNq
      hadm.1 hadm.2.1 hadm.2.2
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 / 2 := by
      have : (1 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have hrow := natgauge_row ((j : ℝ) + 1 / 2)
      (Rk ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((j : ℚ) + 1 / 2) *
        Real.sqrt (1 - ((j : ℝ) + 1 / 2) ^ 2 / ((N : ℝ) + 1 / 2) ^ 2))
      (Rk ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((j : ℚ) + 1 / 2 + 1) *
        Real.sqrt (1 - ((j : ℝ) + 1 / 2 + 1) ^ 2 / ((N : ℝ) + 1 / 2) ^ 2))
      (PhiX ((j : ℚ) + 1 / 2 - 1) ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) x)
      (PhiX ((j : ℚ) + 1 / 2) ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) x)
      (PhiX ((j : ℚ) + 1 / 2 + 1) ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) x) (x : ℝ) 0
      (((M : ℝ) + 1 / 2) * ((σ : ℝ) + 1 / 2)) hj1 (by
        push_cast at hrec ⊢
        linear_combination hrec)
    have hA1 : hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)) ((j + 1 : ℤ)) =
        Rk ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((j : ℚ) + 1 / 2 + 1) *
          Real.sqrt (1 - ((j : ℝ) + 1 / 2 + 1) ^ 2 / ((N : ℝ) + 1 / 2) ^ 2) /
          (((j : ℝ) + 1 / 2 + 1) * Real.sqrt (4 * ((j : ℝ) + 1 / 2 + 1) ^ 2 - 1)) := by
      rw [hrAkH_eq _ _ _ _ _ _ (by omega), etilde_hahn]
      unfold Rk
      push_cast
      have e : ((j : ℝ) + 1 + 1 / 2) = (j : ℝ) + 1 / 2 + 1 := by ring
      rw [e]
      congr 3
      rw [mul_one_div, div_pow]
    have hA0 : hrAkH 1 0 ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)) j =
        Rk ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((j : ℚ) + 1 / 2) *
          Real.sqrt (1 - ((j : ℝ) + 1 / 2) ^ 2 / ((N : ℝ) + 1 / 2) ^ 2) /
          (((j : ℝ) + 1 / 2) * Real.sqrt (4 * ((j : ℝ) + 1 / 2) ^ 2 - 1)) := by
      rw [hrAkH_eq _ _ _ _ _ _ hj, etilde_hahn]
      unfold Rk
      push_cast
      congr 3
      rw [mul_one_div, div_pow]
    have hC : hrCkH 1 0 1 (x : ℝ) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) (1 / ((N : ℝ) + 1 / 2)) j =
        (x : ℝ) - 0 - ((M : ℝ) + 1 / 2) * ((σ : ℝ) + 1 / 2) / (((j : ℝ) + 1 / 2) * ((j : ℝ) + 1 / 2 + 1)) := by
      unfold hrCkH
      simp only [mul_zero, Real.sqrt_zero]
      rw [hrB_hahn]
      ring
    have ee1 : (((j + 1 : ℤ) : ℚ) + 1 / 2) = (j : ℚ) + 1 / 2 + 1 := by push_cast; ring
    have ee0 : (((j - 1 : ℤ) : ℚ) + 1 / 2) = (j : ℚ) + 1 / 2 - 1 := by push_cast; ring
    have e3 : ((j : ℝ) + 1 + 1 / 2) = (j : ℝ) + 1 / 2 + 1 := by ring
    have e4 : ((j : ℝ) - 1 + 1 / 2) = (j : ℝ) + 1 / 2 - 1 := by ring
    unfold jac hahn3jYH
    rw [hA1, hA0, hC, ee1, ee0]
    push_cast at hrow ⊢
    rw [e3, e4]
    linear_combination hrow

/-- **`(R)` for the half-integer `3j` chain**: `|Ŷ_k| ≤ √N_` at every node of an admissible system. -/
theorem hahn_chain_abs_le_half (M σ N : ℤ) (hN : halfLo M σ < N) (n : ℕ) (hn : (n : ℤ) < N - halfLo M σ) (k : ℤ) :
    |hahn3jYH M σ N (xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n) k| ≤
      Real.sqrt ((N : ℝ) + 1 / 2) := by
  have hlo0 := halfLo_nonneg M σ
  by_cases hk : halfLo M σ ≤ k ∧ k ≤ N - 1
  · set lo : ℤ := halfLo M σ with hlodef
    have hmax := max_abs_half M σ
    have hadm : SpecAdm ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) := by
      unfold SpecAdm
      rw [hmax]
      have := (hahn_tri_half lo M σ N).2 ⟨le_rfl, by omega⟩
      exact this
    set K : ℕ := (N - lo).toNat with hKdef
    have hK : (K : ℚ) = ((N : ℚ) + 1 / 2) - max |(M : ℚ) + 1 / 2| |(σ : ℚ) + 1 / 2| := by
      rw [hmax]
      have : (K : ℤ) = N - lo := Int.toNat_of_nonneg (by omega)
      have h2 : ((K : ℤ) : ℚ) = ((N - lo : ℤ) : ℚ) := by rw [this]
      push_cast at h2
      linarith
    have hnK : n < K := by omega
    set i : ℕ := (k - lo).toNat with hi
    have hiK : i < K := by omega
    have hcast : (max |(M : ℚ) + 1 / 2| |(σ : ℚ) + 1 / 2| + (i : ℚ)) = (k : ℚ) + 1 / 2 := by
      rw [hmax]
      have h3 : (i : ℤ) = k - lo := Int.toNat_of_nonneg (by omega)
      have h4 : ((i : ℤ) : ℚ) = ((k - lo : ℤ) : ℚ) := by rw [h3]
      push_cast at h4
      rw [h4]; ring
    have hNq : (0 : ℚ) < (N : ℚ) + 1 / 2 := by
      have : (0 : ℚ) ≤ N := by exact_mod_cast (show (0 : ℤ) ≤ N by omega)
      linarith
    have hsq := hahn_chain_sq_le hadm hNq hK hnK hiK
    rw [hcast] at hsq
    have hY : (hahn3jYH M σ N (xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n) k) ^ 2 =
        (2 * (((k : ℚ) + 1 / 2 : ℚ) : ℝ) + 1) *
          PhiX ((k : ℚ) + 1 / 2) ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2)
            (xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n) ^ 2 := by
      unfold hahn3jYH
      rw [mul_pow, Real.sq_sqrt (by
        have : (0 : ℝ) ≤ k := by exact_mod_cast (show (0 : ℤ) ≤ k by omega)
        linarith)]
      push_cast; ring
    refine Real.abs_le_sqrt (by rw [hY]; push_cast at hsq ⊢; exact hsq)
  · rw [hahn_chain_support_half M σ N _ k hk]
    simp

/-- info: 'FormalResearch.Special.hahn_class_chain_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_class_chain_half

/-- info: 'FormalResearch.Special.hahn_chain_abs_le_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_abs_le_half

/-! ### Nodes of the half-integer lattice -/

lemma xLat_half (M σ N : ℤ) (hN : 0 ≤ N) (n : ℕ) :
    xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n =
      ((4 * (n : ℤ) + 2 * (1 + |M + σ + 1|) - (2 * N + 1) : ℤ) : ℚ) / ((2 * N + 1 : ℤ) : ℚ) := by
  have hN' : (N : ℚ) + 1 / 2 ≠ 0 := by
    have : (0 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  have hT : ((2 * N + 1 : ℤ) : ℚ) ≠ 0 := by push_cast; intro h; apply hN'; linarith
  unfold xLat
  have e : |((M : ℚ) + 1 / 2) + ((σ : ℚ) + 1 / 2)| = ((|M + σ + 1| : ℤ) : ℚ) := by
    push_cast; congr 1; ring
  rw [e]
  push_cast
  push_cast at hT
  field_simp
  ring

/-- **Sufficient family of half-integer `3j` nodes**: `x = p/q ∈ (-1,1)`, `q` odd, `p + q = 2w`,
`w ≡ 1 + |M+σ+1| (mod 2)`.  Explicitly `N = qu + (q-1)/2`, `n = uw + (w-s)/2`. -/
theorem hahn_node_exists_half (M σ p q w : ℤ) (hp : -q < p) (hpq : p < q) (hq : Odd q) (hw : p + q = 2 * w)
    (hsw : Even (w - (1 + |M + σ + 1|))) (N0 : ℕ) :
    ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ halfLo M σ < N ∧ (n : ℤ) < N - halfLo M σ ∧
      xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = (p : ℚ) / (q : ℚ) := by
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = 1 + |M + σ + 1| := ⟨_, rfl⟩
  rw [← hs] at hsw
  obtain ⟨K, hK⟩ := hsw
  obtain ⟨c, hc⟩ := hq
  have hs1 : 1 ≤ s := by have := abs_nonneg (M + σ + 1); omega
  have hw1 : 1 ≤ w := by omega
  have hqw : 1 ≤ q - w := by omega
  have hlo := halfLo_nonneg M σ
  set u : ℤ := N0 + |K| + halfLo M σ + 1 with hu
  have hK1 := abs_nonneg K
  have hu1 : 0 < u := by omega
  have hc0 : 0 ≤ c := by omega
  have hnn : 0 ≤ u * w + K := by
    have : u ≤ u * w := by nlinarith
    have := neg_abs_le K
    omega
  have hq1 : 0 < q := by omega
  refine ⟨q * u + c, (u * w + K).toNat, ?_, ?_, ?_, ?_⟩
  · have : u ≤ q * u := by nlinarith
    omega
  · have : u ≤ q * u := by nlinarith
    omega
  · have hn : (((u * w + K).toNat : ℕ) : ℤ) = u * w + K := Int.toNat_of_nonneg hnn
    rw [hn]
    have h2 : u ≤ u * (q - w) := by nlinarith
    have := le_abs_self K
    nlinarith
  · have hN0 : 0 ≤ q * u + c := by nlinarith
    rw [xLat_half M σ _ hN0, ← hs]
    have hn : (((u * w + K).toNat : ℕ) : ℤ) = u * w + K := Int.toNat_of_nonneg hnn
    rw [hn]
    have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have hT : ((2 * (q * u + c) + 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (by nlinarith : 2 * (q * u + c) + 1 ≠ 0)
    rw [div_eq_div_iff hT hq0]
    have e1 : (4 * (u * w + K) + 2 * s - (2 * (q * u + c) + 1)) * q = p * (2 * (q * u + c) + 1) := by
      have h1 : 2 * (q * u + c) + 1 = q * (2 * u + 1) := by rw [hc]; ring
      rw [h1]
      have h2 : 4 * (u * w + K) + 2 * s - q * (2 * u + 1) = p * (2 * u + 1) := by
        have : 2 * K = w - s := by omega
        nlinarith
      rw [h2]; ring
    exact_mod_cast e1

/-- **Exact obstruction (half-integer nodes)**: if `xLat = p/q` with `gcd(p,q) = 1` for some admissible `N ≥ 0`, then
`q` is odd, `p + q = 2w` is even and `w ≡ 1 + |M+σ+1| (mod 2)`. -/
theorem hahn_node_obstruction_half (M σ p q : ℤ) (hq : 0 < q) (hcop : IsCoprime p q) (N : ℤ) (hN : 0 ≤ N) (n : ℕ)
    (h : xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = (p : ℚ) / (q : ℚ)) :
    Odd q ∧ Even (p + q) ∧ ∀ w : ℤ, p + q = 2 * w → Even (w - (1 + |M + σ + 1|)) := by
  rw [xLat_half M σ N hN] at h
  have hT : ((2 * N + 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 2 * N + 1 ≠ 0)
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [div_eq_div_iff hT hq'] at h
  have hz : (4 * (n : ℤ) + 2 * (1 + |M + σ + 1|) - (2 * N + 1)) * q = p * (2 * N + 1) := by exact_mod_cast h
  generalize hsdef : 1 + |M + σ + 1| = s at hz ⊢
  have hdvd : q ∣ p * (2 * N + 1) := ⟨4 * (n : ℤ) + 2 * s - (2 * N + 1), by linarith⟩
  obtain ⟨t, ht⟩ := (hcop.symm).dvd_of_dvd_mul_left hdvd
  have hodd : Odd (q * t) := ⟨N, by omega⟩
  obtain ⟨hqo, hto⟩ := Int.odd_mul.1 hodd
  have h2 : 4 * (n : ℤ) + 2 * s - q * t = p * t := by
    apply mul_left_cancel₀ hq.ne'
    rw [ht] at hz
    linarith
  obtain ⟨v, hv⟩ := hto
  have h3 : 4 * (n : ℤ) + 2 * s = (p + q) * t := by linear_combination h2
  have hpe : Even (p + q) := by
    have : Even ((p + q) * t) := ⟨2 * n + s, by omega⟩
    rcases Int.even_mul.1 this with h | h
    · exact h
    · exact absurd h (by rw [hv]; exact Int.not_even_iff_odd.2 ⟨v, rfl⟩)
  refine ⟨hqo, hpe, fun w hw => ?_⟩
  have h4 : 2 * (n : ℤ) + s = w * t := by
    rw [hw] at h3; linarith
  refine ⟨n - v * w, ?_⟩
  rw [hv] at h4
  nlinarith

/-- **Airy limit for the actual half-integer `3j` chain at lattice nodes `x_n = x ∈ (0,1)`**
(`thm:hahnAiryConnection`, half-integer `M_, σ_, N_`; sites `q_k = (k+1)δ³`, `AiryOutHalf`). -/
theorem hahn_chain_airy_half (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ (N : ℤ) (n : ℕ), halfLo M σ < N → (n : ℤ) < N - halfLo M σ →
        xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x → 1 / ((N : ℝ) + 1 / 2) ≤ δ0 ^ 3 →
        AiryOutHalf 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) (hahn3jYH M σ N x)
          (Real.sqrt ((N : ℝ) + 1 / 2)) A0 r δ0 C Cosc Ctop W Cmu ξ0 D (1 / ((N : ℝ) + 1 / 2)) := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx1' : (x : ℝ) < 1 := by exact_mod_cast hx1
  have hq2 : Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hqs : 0 < Real.sqrt (1 - (x : ℝ) ^ 2) := Real.sqrt_pos.2 (by nlinarith)
  have hturn : Phi 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2) ^ 2) = 0 := by
    unfold Phi etilde
    rw [hq2]
    have : (1 - 1 * (1 - (x : ℝ) ^ 2)) * (1 - 0 * (1 - (x : ℝ) ^ 2)) = (x : ℝ) ^ 2 := by ring
    rw [this, Real.sqrt_sq hx0'.le]
    simp
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    airy_chain_compose_half (P := 1) (Q := 0) (by norm_num) (by norm_num) ((M : ℝ) + 1 / 2) ((σ : ℝ) + 1 / 2) 1
      (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) hqs (by norm_num) (by linarith) (by rw [hq2]; nlinarith)
      (by simp) hturn A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro N n hN hn hxn hNδ
  have hlo0 := halfLo_nonneg M σ
  have hN0 : 0 ≤ N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ N := by exact_mod_cast hN0
    linarith
  refine H (1 / ((N : ℝ) + 1 / 2)) _ _ (by positivity) hNδ (fun k hk => hahn_class_chain_half M σ N x hN0 k hk) ?_
  intro k
  rw [← hxn]
  exact hahn_chain_abs_le_half M σ N hN n hn k

/-- info: 'FormalResearch.Special.hahn_node_exists_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_node_exists_half

/-- info: 'FormalResearch.Special.hahn_node_obstruction_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_node_obstruction_half

/-- info: 'FormalResearch.Special.hahn_chain_airy_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_airy_half

/-- **Half-integer Airy asymptotics along an infinite sequence `N → ∞`** (`hahn_chain_airy_half` + `hahn_node_exists_half`). -/
theorem hahn_chain_airy_half_infinite (M σ : ℤ) (x : ℚ) (hx0 : 0 < x) (hx1 : x < 1) (w : ℤ)
    (hq : Odd (x.den : ℤ)) (hw : x.num + (x.den : ℤ) = 2 * w) (hsw : Even (w - (1 + |M + σ + 1|)))
    (A0 : ℝ) (hA0 : 0 < A0) :
    ∃ (r δ0 C Cosc Ctop W Cmu ξ0 D : ℝ), 0 < r ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cosc ∧ 0 < Ctop ∧ 0 < W ∧ 0 < Cmu ∧
      0 < ξ0 ∧ 0 < D ∧ ∀ N0 : ℕ, ∃ (N : ℤ) (n : ℕ), (N0 : ℤ) < N ∧ halfLo M σ < N ∧
        (n : ℤ) < N - halfLo M σ ∧ xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x ∧
        1 / ((N : ℝ) + 1 / 2) ≤ δ0 ^ 3 ∧
        AiryOutHalf 1 0 1 (x : ℝ) (Real.sqrt (1 - (x : ℝ) ^ 2)) (hahn3jYH M σ N x)
          (Real.sqrt ((N : ℝ) + 1 / 2)) A0 r δ0 C Cosc Ctop W Cmu ξ0 D (1 / ((N : ℝ) + 1 / 2)) := by
  obtain ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, H⟩ :=
    hahn_chain_airy_half M σ x hx0 hx1 A0 hA0
  refine ⟨r, δ0, C, Cosc, Ctop, W, Cmu, ξ0, D, hr, hδ0, hC, hCosc, hCtop, hW, hCmu, hξ0, hD, ?_⟩
  intro N0
  have hnum : 0 < x.num := Rat.num_pos.2 hx0
  have hlt : x.num < (x.den : ℤ) := by
    have h1 : (x.num : ℚ) / (x.den : ℚ) < 1 := by rwa [Rat.num_div_den]
    have h2 : (x.num : ℚ) < (x.den : ℚ) := by
      rwa [div_lt_one (by exact_mod_cast x.den_pos)] at h1
    exact_mod_cast h2
  obtain ⟨T, hT⟩ := exists_nat_gt (1 / δ0 ^ 3)
  obtain ⟨N, n, hN0, hN1, hN2, hxn⟩ :=
    hahn_node_exists_half M σ x.num x.den w (by omega) hlt hq hw hsw (max N0 T)
  have hxn' : xLat ((M : ℚ) + 1 / 2) ((σ : ℚ) + 1 / 2) ((N : ℚ) + 1 / 2) n = x := by
    rw [hxn]; exact_mod_cast Rat.num_div_den x
  have hlo0 := halfLo_nonneg M σ
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 / 2 := by
    have : (0 : ℝ) ≤ N := by exact_mod_cast (show (0 : ℤ) ≤ N by omega)
    linarith
  have hNT : (T : ℝ) < (N : ℝ) + 1 / 2 := by
    have : (T : ℤ) < N := by have := le_max_right N0 T; omega
    have : (T : ℝ) < N := by exact_mod_cast this
    linarith
  have hδ : 1 / ((N : ℝ) + 1 / 2) ≤ δ0 ^ 3 := by
    have h3 : 0 < δ0 ^ 3 := by positivity
    rw [div_le_iff₀ hNpos]
    have := (div_lt_iff₀ h3).1 hT
    nlinarith
  exact ⟨N, n, by have := le_max_left N0 T; omega, hN1, hN2, hxn', hδ, H N n hN1 hN2 hxn' hδ⟩

/-- info: 'FormalResearch.Special.hahn_chain_airy_half_infinite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hahn_chain_airy_half_infinite

end FormalResearch.Special

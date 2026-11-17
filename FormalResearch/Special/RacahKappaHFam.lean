module

public import FormalResearch.Special.RacahKappaFam
public import FormalResearch.Special.RacahKappaHLeft
public import FormalResearch.Special.RacahKappaHSharp
public import FormalResearch.Special.RacahKappaHHardEdge
public import FormalResearch.Special.DiscreteAiryLimitChains2Half6j

/-!
# The actual half-integer `6j` chain as a family for the abstract sharp amplitude theorem

Twin of `RacahKappaFam` for `Ŷ_k = racah6jYH a b c m n k` (rank `L = k + ½`, labels `m + ½`, `n + ½`, support `halfLo m n ≤ k ≤ min(2b+m, 2a+n)`, hard edge at `(k_max + 3/2) h`): the Gauss mass
`M h √s = 1`, `Ŷ_k² ≤ M`, the support, the total-mass identity over `ℤ`, and the monotone tail from `hr_hardedge_decayH`.

**Claim class: proved.**
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `Y_k² = (2(k+½)+1) Φ²` for `k ≥ 0`. -/
lemma rdH_y_sq (a b c m n k : ℤ) (hk : 0 ≤ k) :
    racah6jYH a b c m n k ^ 2 =
      (2 * ((k : ℝ) + 1 / 2) + 1) *
        Phi6 (a : ℚ) (b : ℚ) (c : ℚ) ((k : ℚ) + 1 / 2) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) ^ 2 := by
  unfold racah6jYH
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  rw [mul_pow, Real.sq_sqrt (by linarith)]

/-- **Total mass of the half-integer `6j` chain over `ℤ`**: `Σ_{k ∈ [lo, hi+1)} Ŷ_k² = 4AB/(2C)`. -/
lemma rdH_sum (a b c m n : ℤ) {D : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D)
    (i : Fin (D + 1)) (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i) :
    ∑ k ∈ Finset.Ico (halfLo m n) (min (2 * b + m) (2 * a + n) + 1), racah6jYH a b c m n k ^ 2 =
      4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ)) := by
  set lo : ℤ := halfLo m n with hlo
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  have hlo0 : 0 ≤ lo := halfLo_nonneg m n
  have hmax := max_abs_half m n
  have e1 : fMin ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) = (lo : ℚ) + 1 / 2 := by
    unfold fMin; rw [hmax]
  have hD : (D : ℤ) = hi - lo := by
    have h1 := hsys.dim
    have h2 := cMax_sub_cMin (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2)
    have e2 : fMax (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) = (hi : ℚ) + 1 / 2 := by
      rw [hhi]; unfold fMax; push_cast [Int.cast_min]
      simp only [min_def]
      split_ifs <;> linarith
    rw [e1, e2] at h2
    rw [h2] at h1
    have : ((D : ℤ) : ℚ) = ((hi - lo : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hg := (gaussWeight_6j hsys i).1
  rw [hc, ← hg]
  unfold lambdaSq6j
  have hfj : ∀ j : Fin (D + 1), fPt ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) j = ((lo + (j : ℕ) : ℤ) : ℚ) + 1 / 2 := by
    intro j
    unfold fPt
    rw [e1]; push_cast; ring
  rw [kk_ico_range _ (by omega : lo ≤ hi + 1)]
  have hlen : (hi + 1 - lo).toNat = D + 1 := by omega
  rw [hlen, ← Fin.sum_univ_eq_sum_range (fun t : ℕ => racah6jYH a b c m n (lo + (t : ℤ)) ^ 2) (D + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rdH_y_sq a b c m n _ (by have := j.2; omega), hfj j, hc]
  push_cast
  ring

/-- Zero outside `[lo, hi]`. -/
lemma rdH_supp0 (a b c m n k : ℤ) (hk : k < halfLo m n ∨ min (2 * b + m) (2 * a + n) < k) :
    racah6jYH a b c m n k = 0 := by
  apply racah_chain_support_half
  rintro ⟨h1, h2, h3⟩
  rcases hk with hk | hk
  · omega
  · rw [min_def] at hk; split_ifs at hk <;> omega

/-- The total mass over any window containing the support. -/
lemma rdH_meq (a b c m n : ℤ) {D : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D) (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i) (END : ℤ) (hEND : ∀ k : ℤ, END ≤ k → racah6jYH a b c m n k = 0) :
    ∑ k ∈ Finset.Ico 0 END, racah6jYH a b c m n k ^ 2 = 4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ)) := by
  rw [← rdH_sum a b c m n hsys i hc]
  set lo : ℤ := halfLo m n with hlo
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  have hlo0 : 0 ≤ lo := halfLo_nonneg m n
  have e1 : ∑ k ∈ Finset.Ico lo (min END (hi + 1)), racah6jYH a b c m n k ^ 2 =
      ∑ k ∈ Finset.Ico 0 END, racah6jYH a b c m n k ^ 2 := by
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; have := min_le_left END (hi + 1); omega
    · intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      rw [rdH_supp0 a b c m n k (by
        by_cases h1 : k < lo
        · exact Or.inl h1
        · right; have : ¬ (lo ≤ k ∧ k < min END (hi + 1)) := fun h => hk' ⟨h.1, h.2⟩
          have h2 : min END (hi + 1) ≤ k := by by_contra hh; exact this ⟨by omega, by omega⟩
          rcases min_le_iff.1 h2 with h3 | h3 <;> omega)]
      simp
  have e2 : ∑ k ∈ Finset.Ico lo (min END (hi + 1)), racah6jYH a b c m n k ^ 2 =
      ∑ k ∈ Finset.Ico lo (hi + 1), racah6jYH a b c m n k ^ 2 := by
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; have := min_le_right END (hi + 1); omega
    · intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      have : END ≤ k := by
        by_contra hh
        exact hk' ⟨hk.1, lt_min (by omega) hk.2⟩
      rw [hEND k this]; simp
  rw [← e1, e2]

/-- Positivity of `A, B, C` for a physical chain with `A h = α`, `B h = β`. -/
lemma rdH_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D : ℕ} (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α) (hBh : wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β) :
    0 < wA (a : ℚ) ((n : ℚ) + 1 / 2) ∧ 0 < wB (b : ℚ) ((m : ℚ) + 1 / 2) ∧ 0 < wC (c : ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon; push Not at hcon; nlinarith
  · by_contra hcon; push Not at hcon; nlinarith
  · have := cPt_nonneg (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i
    rw [← hc] at this
    unfold wC; push_cast at this ⊢; linarith

/-- **The Gauss mass** `M h √s = 1` for `M = 4AB/(2C)`. -/
lemma rdH_mass {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D : ℕ} (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α) (hBh : wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β)
    (hx : cosA (wA (a : ℚ) ((n : ℚ) + 1 / 2)) (wB (b : ℚ) ((m : ℚ) + 1 / 2)) (wC (c : ℚ)) = x) :
    4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ)) * h *
      Real.sqrt (rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x) = 1 := by
  obtain ⟨hA, hB, hC⟩ := rdH_pos hα hβ a b c m n i hc hh hAh hBh
  set A := wA (a : ℚ) ((n : ℚ) + 1 / 2) with hAd
  set B := wB (b : ℚ) ((m : ℚ) + 1 / 2) with hBd
  set C := wC (c : ℚ) with hCd
  have hC2 : C ^ 2 = A ^ 2 + B ^ 2 - 2 * A * B * x := by
    unfold cosA at hx
    rw [div_eq_iff (by positivity)] at hx
    nlinarith only [hx]
  have hγ : (C * h) ^ 2 = α ^ 2 + β ^ 2 - 2 * α * β * x := by
    rw [← hAh, ← hBh]; linear_combination h ^ 2 * hC2
  obtain ⟨-, hinv⟩ := rk_racah_s hα hβ (by positivity : 0 < C * h) hγ
  have hsq : Real.sqrt (rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x) = C * h / (2 * α * β) := by
    rw [← one_div_one_div (Real.sqrt _), hinv]
    field_simp
  rw [hsq, ← hAh, ← hBh]
  field_simp
  norm_num

/-- `Ŷ_k² ≤ M`. -/
lemma rdH_sq_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) D) (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) ((m : ℚ) + 1 / 2) ((n : ℚ) + 1 / 2) i) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α) (hBh : wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β) (k : ℤ) :
    racah6jYH a b c m n k ^ 2 ≤ 4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ)) := by
  obtain ⟨hA, hB, hC⟩ := rdH_pos hα hβ a b c m n i hc hh hAh hBh
  have h1 := racah_chain_abs_le_half a b c m n hsys i hc k
  have h2 : (0 : ℝ) ≤ 4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ)) := by positivity
  calc racah6jYH a b c m n k ^ 2 = |racah6jYH a b c m n k| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt (4 * wA (a : ℚ) ((n : ℚ) + 1 / 2) * wB (b : ℚ) ((m : ℚ) + 1 / 2) / (2 * wC (c : ℚ))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = _ := Real.sq_sqrt h2

/-- Upper support: `Ŷ_k = 0` as soon as `2α < (k+1)h`. -/
lemma rdH_supp_up {α : ℝ} (a b c m n : ℤ) {h : ℝ} (hh : 0 < h) (hAh : wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α) (k : ℤ)
    (hk : 2 * α < ((k : ℝ) + 1) * h) : racah6jYH a b c m n k = 0 := by
  apply rdH_supp0
  right
  by_contra hcon
  push Not at hcon
  have h1 : k ≤ 2 * a + n := le_trans hcon (min_le_right _ _)
  have h2 : (k : ℝ) ≤ 2 * (a : ℝ) + n := by exact_mod_cast h1
  have e : wA (a : ℚ) ((n : ℚ) + 1 / 2) = (a : ℝ) + (((n : ℝ) + 1 / 2) + 1) / 2 := by unfold wA; push_cast; ring
  rw [e] at hAh
  nlinarith only [hk, h2, hAh, hh]

/-- The hard edge of the half-integer `6j` chain: `ẽ` vanishes at `(hi+3/2)h`. -/
lemma rdH_edge {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b m n : ℤ) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α) (hBh : wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β) (kmax : ℕ)
    (hk : (kmax : ℤ) = min (2 * b + m) (2 * a + n)) :
    (((((kmax : ℝ) + 1) + 1 / 2) * h) ^ 2 ∈ Dom (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2))) ∧
      etilde (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (((((kmax : ℝ) + 1) + 1 / 2) * h) ^ 2) = 0 := by
  have eA : wA (a : ℚ) ((n : ℚ) + 1 / 2) = (a : ℝ) + (((n : ℝ) + 1 / 2) + 1) / 2 := by unfold wA; push_cast; ring
  have eB : wB (b : ℚ) ((m : ℚ) + 1 / 2) = (b : ℝ) + (((m : ℝ) + 1 / 2) + 1) / 2 := by unfold wB; push_cast; ring
  have hk' : (((kmax : ℝ) + 1) + 1 / 2) = min (2 * ((a : ℝ) + (((n : ℝ) + 1 / 2) + 1) / 2)) (2 * ((b : ℝ) + (((m : ℝ) + 1 / 2) + 1) / 2)) := by
    have h0 : ((kmax : ℤ) : ℝ) = ((min (2 * b + m) (2 * a + n) : ℤ) : ℝ) := by rw [hk]
    have h1 : (kmax : ℝ) = min (2 * (b : ℝ) + m) (2 * a + n) := by
      have := h0; push_cast at this; exact this
    rw [h1]
    rcases le_total ((2 : ℝ) * b + m) (2 * a + n) with hc | hc
    · have e1 : min (2 * (b : ℝ) + m) (2 * a + n) = 2 * b + m := min_eq_left hc
      have e2 : min (2 * ((a : ℝ) + (((n : ℝ) + 1 / 2) + 1) / 2)) (2 * ((b : ℝ) + (((m : ℝ) + 1 / 2) + 1) / 2)) =
          2 * ((b : ℝ) + (((m : ℝ) + 1 / 2) + 1) / 2) := min_eq_right (by linarith)
      rw [e1, e2]; ring
    · have e1 : min (2 * (b : ℝ) + m) (2 * a + n) = 2 * a + n := min_eq_right hc
      have e2 : min (2 * ((a : ℝ) + (((n : ℝ) + 1 / 2) + 1) / 2)) (2 * ((b : ℝ) + (((m : ℝ) + 1 / 2) + 1) / 2)) =
          2 * ((a : ℝ) + (((n : ℝ) + 1 / 2) + 1) / 2) := min_eq_left (by linarith)
      rw [e1, e2]; ring
  have hmin : (((kmax : ℝ) + 1) + 1 / 2) * h = min (2 * α) (2 * β) := by
    rw [hk', eA.symm, eB.symm, min_mul_of_nonneg _ _ hh.le]
    congr 1 <;> linarith
  rw [hmin]
  have h1 : min (2 * α) (2 * β) ≤ 2 * α := min_le_left _ _
  have h2 : min (2 * α) (2 * β) ≤ 2 * β := min_le_right _ _
  have h0 : 0 < min (2 * α) (2 * β) := lt_min (by linarith) (by linarith)
  have hPσ : 1 / (4 * α ^ 2) * (min (2 * α) (2 * β)) ^ 2 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith only [h1, h0]
  have hQσ : 1 / (4 * β ^ 2) * (min (2 * α) (2 * β)) ^ 2 ≤ 1 := by
    rw [div_mul_eq_mul_div, div_le_one (by positivity)]; nlinarith only [h2, h0]
  refine ⟨⟨by positivity, hPσ, hQσ⟩, ?_⟩
  unfold etilde
  rw [Real.sqrt_eq_zero (by nlinarith only [hPσ, hQσ, mul_nonneg (sub_nonneg.2 hPσ) (sub_nonneg.2 hQσ)])]
  rcases min_choice (2 * α) (2 * β) with hm | hm
  · rw [hm]
    have : 1 / (4 * α ^ 2) * (2 * α) ^ 2 = 1 := by field_simp; norm_num
    rw [this]; ring
  · rw [hm]
    have : 1 / (4 * β ^ 2) * (2 * β) ^ 2 = 1 := by field_simp; norm_num
    rw [this]; ring

/-- **Monotone tail** of the (twisted) half-integer `6j` chain beyond `q_* + h`. -/
lemma rdH_mono {α β x τ qs : ℝ} (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (a b c m n : ℤ) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) ((n : ℚ) + 1 / 2) * h = α) (hBh : wB (b : ℚ) ((m : ℚ) + 1 / 2) * h = β) (u : ℤ → ℝ)
    (hu : ∀ k, u k ^ 2 = 1)
    (hhM : h * (2 * hrM ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2)) ≤ qs)
    (hhC : h * hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) qs ≤
      2 * ((1 - τ * x) / qs ^ 2) * qs)
    (hrows : ∀ k : ℤ, 1 ≤ k → jac (hrAkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
      (hrCkH (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) h)
      (fun j => u j * racah6jYH a b c m n j) k = 0) :
    ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1) * h → k' ≤ k →
      (u k * racah6jYH a b c m n k) ^ 2 ≤ (u k' * racah6jYH a b c m n k') ^ 2 := by
  intro k' k hk' hkk
  have hk'0 : 0 ≤ k' := by
    have : (0 : ℝ) < ((k' : ℝ) + 1) * h := by nlinarith only [hk', hqs, hh]
    have : (-1 : ℝ) < k' := by
      by_contra hc; push Not at hc; nlinarith only [this, hc, hh]
    have : (-1 : ℤ) < k' := by exact_mod_cast this
    omega
  have hsq : ∀ j : ℤ, (u j * racah6jYH a b c m n j) ^ 2 = racah6jYH a b c m n j ^ 2 := by
    intro j; rw [mul_pow, hu j, one_mul]
  rw [hsq, hsq]
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  by_cases hbig : hi < k'
  · rw [rdH_supp0 a b c m n k (Or.inr (by omega))]
    simpa using sq_nonneg (racah6jYH a b c m n k')
  push Not at hbig
  have hhi0 : 0 ≤ hi := le_trans hk'0 hbig
  by_cases hbig2 : hi < k
  · rw [rdH_supp0 a b c m n k (Or.inr hbig2)]
    simpa using sq_nonneg (racah6jYH a b c m n k')
  push Not at hbig2
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = hi := ⟨hi.toNat, Int.toNat_of_nonneg hhi0⟩
  obtain ⟨hedge, hedge0⟩ := rdH_edge hα hβ a b m n hh hAh hBh kmax hkmax
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  have key := hr_hardedge_decayH hP hQ ((m : ℝ) + 1 / 2) ((n : ℝ) + 1 / 2) τ x qs h hqs hh hτ hκ hturn hhM hhC kmax
    k'.toNat hedge hedge0
    (by
      have : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
        have : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
        exact_mod_cast this
      rw [this]; nlinarith only [hk', hh])
    (by omega)
    (fun j => u j * racah6jYH a b c m n j)
    (fun k hk => hrows k (by rw [Finset.mem_Icc] at hk; omega))
  have := key k (by omega) (by omega)
  have h2 : (|u k * racah6jYH a b c m n k|) ^ 2 ≤ (|u (k'.toNat : ℤ) * racah6jYH a b c m n (k'.toNat : ℤ)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) this 2
  have e : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
  rw [e, sq_abs, sq_abs, hsq, hsq] at h2
  exact h2

/-- A partial sum of squares is at most the total mass, from the support and total-mass hypotheses. -/
lemma rk_mleH {Fam : ℝ → (ℤ → ℝ) → ℝ → Prop} {Rmax : ℝ}
    (hsupp : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Rmax < ((k : ℝ) + 1) * h → Y k = 0)
    (hMeq : ∀ h Y M, Fam h Y M → ∀ END : ℤ, (∀ k : ℤ, END ≤ k → Y k = 0) → ∑ k ∈ Finset.Ico 0 END, Y k ^ 2 = M) :
    ∀ h Y M, Fam h Y M → 0 < h → ∀ k0 k1 : ℤ, 0 ≤ k0 → ∑ k ∈ Finset.Ico k0 k1, Y k ^ 2 ≤ M := by
  intro h Y M hF hh k0 k1 hk0
  set END : ℤ := max k1 (⌈Rmax / h⌉ + 1) with hEND
  have hY : ∀ k : ℤ, END ≤ k → Y k = 0 := by
    intro k hk
    apply hsupp h Y M hF k
    have h1 : ⌈Rmax / h⌉ + 1 ≤ k := le_trans (le_max_right _ _) hk
    have h2 : Rmax / h ≤ (⌈Rmax / h⌉ : ℝ) := Int.le_ceil _
    have h3 : ((⌈Rmax / h⌉ : ℤ) : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h1
    rw [div_le_iff₀ hh] at h2
    nlinarith only [h2, h3, hh]
  rw [← hMeq h Y M hF END hY]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    rw [Finset.mem_Ico] at hk ⊢
    have := le_max_left k1 (⌈Rmax / h⌉ + 1)
    omega
  · intro k _ _; positivity

/-- info: 'FormalResearch.Special.rdH_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rdH_mono

end FormalResearch.Special

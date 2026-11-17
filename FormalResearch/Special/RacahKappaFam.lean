module

public import FormalResearch.Special.RacahKappaLeft
public import FormalResearch.Special.RacahKappaSharp
public import FormalResearch.Special.DiscreteAiryPhysRacah
public import FormalResearch.Special.DiscreteAiryLimitHyperDecay

/-!
# The actual `6j` chain as a family for the abstract sharp amplitude theorem

Facts on a physical `6j` chain `Ŷ_k = racah6jY a b c m n k` (integer data): the Gauss mass `M h √s = 1`, `Ŷ_k² ≤ M`, the support, the total-mass identity over `ℤ`, and the finite-`k` bookkeeping.
Nothing here depends on the sign `τ`: a twist `u_k = ±1` leaves `Y²` unchanged.

**Claim class: proved.**
-/

@[expose] public section

open FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `Y_k² = (2k+1) Φ²` for `k ≥ 0`. -/
lemma rd_y_sq (a b c m n k : ℤ) (hk : 0 ≤ k) :
    racah6jY a b c m n k ^ 2 =
      (2 * (k : ℝ) + 1) * Phi6 (a : ℚ) (b : ℚ) (c : ℚ) (k : ℚ) (m : ℚ) (n : ℚ) ^ 2 := by
  unfold racah6jY
  have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
  rw [mul_pow, Real.sq_sqrt (by linarith)]

/-- **Total mass of the `6j` chain over `ℤ`**: `Σ_{k ∈ [lo, hi+1)} Ŷ_k² = 4AB/(2C)`. -/
lemma rd_sum (a b c m n : ℤ) {D : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D) (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) :
    ∑ k ∈ Finset.Ico (max |m| |n|) (min (2 * b + m) (2 * a + n) + 1), racah6jY a b c m n k ^ 2 =
      4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) := by
  set lo : ℤ := max |m| |n| with hlo
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  have hlo0 : 0 ≤ lo := le_trans (abs_nonneg m) (le_max_left _ _)
  have hD : (D : ℤ) = hi - lo := by
    have h1 := hsys.dim
    have h2 := cMax_sub_cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ)
    have e1 : fMin (m : ℚ) (n : ℚ) = (lo : ℚ) := by rw [hlo]; unfold fMin; push_cast; rfl
    have e2 : fMax (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) = (hi : ℚ) := by rw [hhi]; unfold fMax; push_cast; exact min_comm _ _
    rw [e1, e2] at h2
    rw [h2] at h1
    have : ((D : ℤ) : ℚ) = ((hi - lo : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have hg := (gaussWeight_6j hsys i).1
  rw [hc, ← hg]
  unfold lambdaSq6j
  have e1 : fMin (m : ℚ) (n : ℚ) = (lo : ℚ) := by rw [hlo]; unfold fMin; push_cast; rfl
  have hfj : ∀ j : Fin (D + 1), fPt (m : ℚ) (n : ℚ) j = ((lo + (j : ℕ) : ℤ) : ℚ) := by
    intro j
    unfold fPt
    rw [e1]; push_cast; ring
  rw [kk_ico_range _ (by omega : lo ≤ hi + 1)]
  have hlen : (hi + 1 - lo).toNat = D + 1 := by omega
  rw [hlen, ← Fin.sum_univ_eq_sum_range (fun t : ℕ => racah6jY a b c m n (lo + (t : ℤ)) ^ 2) (D + 1)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rd_y_sq a b c m n _ (by have := j.2; omega), hfj j, hc]
  push_cast
  ring

/-- Zero outside `[lo, hi]`. -/
lemma rd_supp0 (a b c m n k : ℤ) (hk : k < max |m| |n| ∨ min (2 * b + m) (2 * a + n) < k) :
    racah6jY a b c m n k = 0 := by
  apply racah_chain_support
  rintro ⟨h1, h2, h3, h4⟩
  rcases hk with hk | hk
  · rw [max_def] at hk; split_ifs at hk <;> omega
  · rw [min_def] at hk; split_ifs at hk <;> omega

/-- The total mass over any window containing the support. -/
lemma rd_meq (a b c m n : ℤ) {D : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D) (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) (END : ℤ) (hEND : ∀ k : ℤ, END ≤ k → racah6jY a b c m n k = 0) :
    ∑ k ∈ Finset.Ico 0 END, racah6jY a b c m n k ^ 2 = 4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) := by
  rw [← rd_sum a b c m n hsys i hc]
  set lo : ℤ := max |m| |n| with hlo
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  have hlo0 : 0 ≤ lo := le_trans (abs_nonneg m) (le_max_left _ _)
  have e1 : ∑ k ∈ Finset.Ico lo (min END (hi + 1)), racah6jY a b c m n k ^ 2 =
      ∑ k ∈ Finset.Ico 0 END, racah6jY a b c m n k ^ 2 := by
    apply Finset.sum_subset
    · intro k hk; rw [Finset.mem_Ico] at hk ⊢; have := min_le_left END (hi + 1); omega
    · intro k hk hk'
      rw [Finset.mem_Ico] at hk hk'
      rw [rd_supp0 a b c m n k (by
        by_cases h1 : k < lo
        · exact Or.inl h1
        · right; have : ¬ (lo ≤ k ∧ k < min END (hi + 1)) := fun h => hk' ⟨h.1, h.2⟩
          have h2 : min END (hi + 1) ≤ k := by by_contra hh; exact this ⟨by omega, by omega⟩
          rcases min_le_iff.1 h2 with h3 | h3 <;> omega)]
      simp
  have e2 : ∑ k ∈ Finset.Ico lo (min END (hi + 1)), racah6jY a b c m n k ^ 2 =
      ∑ k ∈ Finset.Ico lo (hi + 1), racah6jY a b c m n k ^ 2 := by
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
lemma rd_pos {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D : ℕ} (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) :
    0 < wA (a : ℚ) (n : ℚ) ∧ 0 < wB (b : ℚ) (m : ℚ) ∧ 0 < wC (c : ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hcon; push Not at hcon; nlinarith
  · by_contra hcon; push Not at hcon; nlinarith
  · have := cPt_nonneg (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i
    rw [← hc] at this
    unfold wC; push_cast at this ⊢; linarith

/-- **The Gauss mass** `M h √s = 1` for `M = 4AB/(2C)`. -/
lemma rd_mass {α β x : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D : ℕ} (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β)
    (hx : cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x) :
    4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) * h *
      Real.sqrt (rkS (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) x) = 1 := by
  obtain ⟨hA, hB, hC⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  set A := wA (a : ℚ) (n : ℚ) with hAd
  set B := wB (b : ℚ) (m : ℚ) with hBd
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
lemma rd_sq_le {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D) (i : Fin (D + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) (k : ℤ) :
    racah6jY a b c m n k ^ 2 ≤ 4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) := by
  obtain ⟨hA, hB, hC⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  have h1 := racah_chain_abs_le a b c m n hsys i hc k
  have h2 : (0 : ℝ) ≤ 4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) := by positivity
  calc racah6jY a b c m n k ^ 2 = |racah6jY a b c m n k| ^ 2 := (sq_abs _).symm
    _ ≤ Real.sqrt (4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = _ := Real.sq_sqrt h2

/-- Upper support: `Ŷ_k = 0` as soon as `2α < (k+½)h`. -/
lemma rd_supp_up {α : ℝ} (a b c m n : ℤ) {h : ℝ} (hh : 0 < h) (hAh : wA (a : ℚ) (n : ℚ) * h = α) (k : ℤ)
    (hk : 2 * α < ((k : ℝ) + 1 / 2) * h) : racah6jY a b c m n k = 0 := by
  apply rd_supp0
  right
  by_contra hcon
  push Not at hcon
  have h1 : k ≤ 2 * a + n := le_trans hcon (min_le_right _ _)
  have h2 : (k : ℝ) ≤ 2 * (a : ℝ) + n := by exact_mod_cast h1
  have e : wA (a : ℚ) (n : ℚ) = (a : ℝ) + ((n : ℝ) + 1) / 2 := by unfold wA; push_cast; ring
  rw [e] at hAh
  nlinarith only [hk, h2, hAh, hh]

/-- The hard edge of the `6j` chain: `ẽ` vanishes at `(hi+1)h`. -/
lemma rd_edge {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b m n : ℤ) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) (kmax : ℕ)
    (hk : (kmax : ℤ) = min (2 * b + m) (2 * a + n)) :
    ((((kmax : ℝ) + 1) * h) ^ 2 ∈ Dom (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2))) ∧
      etilde (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((((kmax : ℝ) + 1) * h) ^ 2) = 0 := by
  have eA : wA (a : ℚ) (n : ℚ) = (a : ℝ) + ((n : ℝ) + 1) / 2 := by unfold wA; push_cast; ring
  have eB : wB (b : ℚ) (m : ℚ) = (b : ℝ) + ((m : ℝ) + 1) / 2 := by unfold wB; push_cast; ring
  have hk' : ((kmax : ℝ) + 1) = min (2 * ((a : ℝ) + ((n : ℝ) + 1) / 2)) (2 * ((b : ℝ) + ((m : ℝ) + 1) / 2)) := by
    have h0 : ((kmax : ℤ) : ℝ) = ((min (2 * b + m) (2 * a + n) : ℤ) : ℝ) := by rw [hk]
    have h1 : (kmax : ℝ) = min (2 * (b : ℝ) + m) (2 * a + n) := by
      have := h0; push_cast at this; exact this
    rw [h1]
    rcases le_total ((2 : ℝ) * b + m) (2 * a + n) with hc | hc
    · have e1 : min (2 * (b : ℝ) + m) (2 * a + n) = 2 * b + m := min_eq_left hc
      have e2 : min (2 * ((a : ℝ) + ((n : ℝ) + 1) / 2)) (2 * ((b : ℝ) + ((m : ℝ) + 1) / 2)) =
          2 * ((b : ℝ) + ((m : ℝ) + 1) / 2) := min_eq_right (by linarith)
      rw [e1, e2]; ring
    · have e1 : min (2 * (b : ℝ) + m) (2 * a + n) = 2 * a + n := min_eq_right hc
      have e2 : min (2 * ((a : ℝ) + ((n : ℝ) + 1) / 2)) (2 * ((b : ℝ) + ((m : ℝ) + 1) / 2)) =
          2 * ((a : ℝ) + ((n : ℝ) + 1) / 2) := min_eq_left (by linarith)
      rw [e1, e2]; ring
  have hmin : ((kmax : ℝ) + 1) * h = min (2 * α) (2 * β) := by
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

/-- **Monotone tail** of the (twisted) `6j` chain beyond `q_* + h`. -/
lemma rd_mono {α β x τ qs : ℝ} (hα : 0 < α) (hβ : 0 < β) (hqs : 0 < qs) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x)
    (hturn : Phi (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (qs ^ 2) = 0) (a b c m n : ℤ) {h : ℝ} (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β) (u : ℤ → ℝ) (hu : ∀ k, u k ^ 2 = 1)
    (hhM : h * (2 * hrM (m : ℝ) (n : ℝ)) ≤ qs)
    (hhC : h * hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs)
    (hrows : ∀ k : ℤ, 1 ≤ k → jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
      (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) τ x (m : ℝ) (n : ℝ) h) (fun j => u j * racah6jY a b c m n j) k = 0) :
    ∀ k' k : ℤ, qs + h ≤ ((k' : ℝ) + 1 / 2) * h → k' ≤ k →
      (u k * racah6jY a b c m n k) ^ 2 ≤ (u k' * racah6jY a b c m n k') ^ 2 := by
  intro k' k hk' hkk
  have hk'0 : 0 ≤ k' := by
    have : (0 : ℝ) < ((k' : ℝ) + 1 / 2) * h := by nlinarith only [hk', hqs, hh]
    have : (-1 : ℝ) < k' := by
      by_contra hc; push Not at hc; nlinarith only [this, hc, hh]
    have : (-1 : ℤ) < k' := by exact_mod_cast this
    omega
  have hsq : ∀ j : ℤ, (u j * racah6jY a b c m n j) ^ 2 = racah6jY a b c m n j ^ 2 := by
    intro j; rw [mul_pow, hu j, one_mul]
  rw [hsq, hsq]
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  by_cases hbig : hi < k'
  · rw [rd_supp0 a b c m n k (Or.inr (by omega))]
    simpa using sq_nonneg (racah6jY a b c m n k')
  push Not at hbig
  have hhi0 : 0 ≤ hi := le_trans hk'0 hbig
  by_cases hbig2 : hi < k
  · rw [rd_supp0 a b c m n k (Or.inr hbig2)]
    simpa using sq_nonneg (racah6jY a b c m n k')
  push Not at hbig2
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = hi := ⟨hi.toNat, Int.toNat_of_nonneg hhi0⟩
  obtain ⟨hedge, hedge0⟩ := rd_edge hα hβ a b m n hh hAh hBh kmax hkmax
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  have key := hr_hardedge_decay hP hQ (m : ℝ) (n : ℝ) τ x qs h hqs hh hτ hκ hturn hhM hhC kmax k'.toNat hedge hedge0
    (by
      have : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
        have : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
        exact_mod_cast this
      rw [this]; nlinarith only [hk', hh])
    (by omega)
    (fun j => u j * racah6jY a b c m n j)
    (fun k hk => hrows k (by rw [Finset.mem_Icc] at hk; omega))
  have := key k (by omega) (by omega)
  have h2 : (|u k * racah6jY a b c m n k|) ^ 2 ≤ (|u (k'.toNat : ℤ) * racah6jY a b c m n (k'.toNat : ℤ)|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) this 2
  have e : ((k'.toNat : ℕ) : ℤ) = k' := Int.toNat_of_nonneg hk'0
  rw [e, sq_abs, sq_abs, hsq, hsq] at h2
  exact h2

/-- The oscillatory hypothesis `|u| < 1` on `(0, q_*)` follows from the simple turn. -/
lemma rk_hosc0 {P Q τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hqs : 0 < qs) (hκ : 0 < 1 - τ * x)
    (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hturn : Phi P Q τ x (qs ^ 2) = 0) :
    ∀ q : ℝ, 0 < q → q < qs → |hrU P Q τ x q| < 1 := by
  intro q hq hqq
  have hs := rk_turn_id hP hQ hτ hα hβ hturn
  have hx2 := rk_abs_x_lt hP hQ hτ hqs hα hβ hκ hturn
  have hspos : 0 < rkS P Q x := by
    have : 0 < rkS P Q x * qs ^ 2 := by rw [← hs]; linarith
    by_contra hc; push Not at hc
    nlinarith only [this, mul_nonneg (neg_nonneg.2 hc) (sq_nonneg qs)]
  have hq2 : q ^ 2 < qs ^ 2 := by nlinarith only [hq, hqq]
  have hP1 : 0 < 1 - P * q ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hq2.le hP, hα]
  have hQ1 : 0 < 1 - Q * q ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hq2.le hQ, hβ]
  have hkey := rl_key (P := P) (Q := Q) (x := x) (qs := qs) (σ := q ^ 2) hP hQ hs
  have hpos : 0 < (1 - P * q ^ 2) * (1 - Q * q ^ 2) := mul_pos hP1 hQ1
  have he : etilde P Q (q ^ 2) ^ 2 = (1 - P * q ^ 2) * (1 - Q * q ^ 2) := by
    unfold etilde; exact Real.sq_sqrt hpos.le
  have hep : 0 < etilde P Q (q ^ 2) := by unfold etilde; exact Real.sqrt_pos.2 hpos
  unfold hrU
  rw [abs_div, abs_of_pos hep, div_lt_one hep, abs_mul]
  have hτ1 : |τ| = 1 := by
    have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
    nlinarith only [this, abs_nonneg τ]
  rw [hτ1, one_mul]
  have h1 : |x - Real.sqrt (P * Q) * q ^ 2| ^ 2 < etilde P Q (q ^ 2) ^ 2 := by
    rw [sq_abs, he]
    have : 0 < rkS P Q x * (qs ^ 2 - q ^ 2) := mul_pos hspos (by linarith)
    nlinarith only [hkey, this]
  exact lt_of_pow_lt_pow_left₀ 2 hep.le h1

/-- A partial sum of squares is at most the total mass, from the support and total-mass hypotheses. -/
lemma rk_mle {Fam : ℝ → (ℤ → ℝ) → ℝ → Prop} {Rmax : ℝ}
    (hsupp : ∀ h Y M, Fam h Y M → ∀ k : ℤ, Rmax < ((k : ℝ) + 1 / 2) * h → Y k = 0)
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

end FormalResearch.Special

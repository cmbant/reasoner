module

public import FormalResearch.Racah.P2ThreeJSym

/-!
# The exact Regge exchange of the midpoint `3j` symbol (Weyl P2, `eq:3jRegge`)

`threeJ L (ℓ-σ/2) (ℓ+σ/2) M (μ-M/2) (-μ-M/2) = threeJ L (ℓ+M/2) (ℓ-M/2) (-σ) (μ+σ/2) (-μ+σ/2)`,
i.e. with `N = 2ℓ+1`: the symbol is invariant under `(M,σ) ↦ (-σ,-M)` (`threeJ_regge_mid`), and
in the paper's normalisation `Φ_L^{M,σ} = Φ_L^{-σ,-M}` exactly (`Phi3j_regge`, the first
coefficientwise Regge relation `eq:coeffRegge`).

Proof (all rational labels, no hypotheses): both sides vanish unless the same nine quantities
are natural numbers (`Adm9`); both satisfy the *same* rank recurrence (DLMF 34.3.15, all rows:
`threeJ_recurrence_all`: the coefficients are invariant under `(M,σ) ↦ (-σ,-M)`); and at the
top rank `L = N-1 = j_-+j_+` both are stretched symbols (`threeJ_stretched`) with the same
magnitude and sign.  Descending the rank chain from `L = N`, `N-1` therefore identifies them; the
descent stops at `L_0 = max(|M|,|σ|)` where both are zero below.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner

set_option linter.unusedSimpArgs false

/-- The `3j` symbol `(L j_- j_+; M m_- m_+)` of the midpoint variables, without phase or `√N`. -/
noncomputable def F3 (L M σ N μ : ℚ) : ℝ :=
  threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ)

/-- The nine natural-number conditions for `F3 L M σ N μ` to be possibly nonzero. -/
structure Adm9 (L M σ N μ : ℚ) : Prop where
  q1 : IsNat (L + jMinus N σ - jPlus N σ)
  q2 : IsNat (L - jMinus N σ + jPlus N σ)
  q3 : IsNat (-L + jMinus N σ + jPlus N σ)
  p1 : IsNat (L + M)
  p2 : IsNat (L - M)
  a1 : IsNat (jMinus N σ + mMinus M μ)
  a2 : IsNat (jMinus N σ - mMinus M μ)
  b1 : IsNat (jPlus N σ + mPlus M μ)
  b2 : IsNat (jPlus N σ - mPlus M μ)

lemma threeJ_eq_zero_of_not_isNat (j₁ j₂ j₃ m₁ m₂ m₃ : ℚ)
    (h : ¬ IsNat (j₁ + j₂ - j₃) ∨ ¬ IsNat (j₁ - j₂ + j₃) ∨ ¬ IsNat (-j₁ + j₂ + j₃) ∨
      ¬ IsNat (j₁ + m₁) ∨ ¬ IsNat (j₁ - m₁) ∨ ¬ IsNat (j₂ + m₂) ∨ ¬ IsNat (j₂ - m₂) ∨
      ¬ IsNat (j₃ + m₃) ∨ ¬ IsNat (j₃ - m₃)) :
    threeJ j₁ j₂ j₃ m₁ m₂ m₃ = 0 := by
  unfold threeJ
  split_ifs with hm
  · have key : triSq j₁ j₂ j₃ = 0 ∨
        fq (j₁ + m₁) * fq (j₁ - m₁) * fq (j₂ + m₂) * fq (j₂ - m₂) * fq (j₃ + m₃) *
          fq (j₃ - m₃) = 0 := by
      rcases h with h | h | h | h | h | h | h | h | h
      · left; unfold triSq; rw [fq_of_not_isNat h]; ring
      · left; unfold triSq; rw [fq_of_not_isNat h]; ring
      · left; unfold triSq; rw [fq_of_not_isNat h]; ring
      · right; rw [fq_of_not_isNat h]; ring
      · right; rw [fq_of_not_isNat h]; ring
      · right; rw [fq_of_not_isNat h]; ring
      · right; rw [fq_of_not_isNat h]; ring
      · right; rw [fq_of_not_isNat h]; ring
      · right; rw [fq_of_not_isNat h]; ring
    rcases key with k | k
    · rw [k]; simp
    · rw [k]; simp
  · rfl

lemma F3_eq_zero {L M σ N μ : ℚ} (h : ¬ Adm9 L M σ N μ) : F3 L M σ N μ = 0 := by
  unfold F3
  apply threeJ_eq_zero_of_not_isNat
  by_contra hcon
  push Not at hcon
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ := hcon
  exact h ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩

lemma isNat_congr {x y : ℚ} (h : x = y) (hx : IsNat x) : IsNat y := by rw [← h]; exact hx

lemma Adm9_swap {L M σ N μ : ℚ} (h : Adm9 L M σ N μ) : Adm9 L (-σ) (-M) N μ := by
  obtain ⟨q1, q2, q3, p1, p2, a1, a2, b1, b2⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine isNat_congr ?_ p1; simp only [jMinus, jPlus]; ring
  · refine isNat_congr ?_ p2; simp only [jMinus, jPlus]; ring
  · refine isNat_congr ?_ q3; simp only [jMinus, jPlus]; ring
  · refine isNat_congr ?_ q1; simp only [jMinus, jPlus]; ring
  · refine isNat_congr ?_ q2; simp only [jMinus, jPlus]; ring
  · refine isNat_congr ?_ b2; simp only [jMinus, jPlus, mMinus, mPlus]; ring
  · refine isNat_congr ?_ a2; simp only [jMinus, jPlus, mMinus, mPlus]; ring
  · refine isNat_congr ?_ b1; simp only [jMinus, jPlus, mMinus, mPlus]; ring
  · refine isNat_congr ?_ a1; simp only [jMinus, jPlus, mMinus, mPlus]; ring

lemma Adm9_swap_iff (L M σ N μ : ℚ) : Adm9 L M σ N μ ↔ Adm9 L (-σ) (-M) N μ := by
  refine ⟨Adm9_swap, fun h => ?_⟩
  have := Adm9_swap h
  simpa using this

/-- At the top rank `L = N-1 = j_-+j_+` the symbol is stretched (DLMF 34.3.6). -/
lemma F3_top_formula (M σ N μ : ℚ) (A B C D : ℕ)
    (hA : jMinus N σ + mMinus M μ = A) (hB : jMinus N σ - mMinus M μ = B)
    (hC : jPlus N σ + mPlus M μ = C) (hD : jPlus N σ - mPlus M μ = D) :
    F3 (N - 1) M σ N μ =
      sgn (jMinus N σ - jPlus N σ - M) *
        Real.sqrt (((A + B).factorial : ℝ) * ((C + D).factorial : ℝ) * ((B + D).factorial : ℝ) *
          ((A + C).factorial : ℝ) /
            (((A + B + C + D + 1).factorial : ℝ) * (A.factorial : ℝ) * B.factorial *
              C.factorial * D.factorial)) := by
  have e : N - 1 = jMinus N σ + jPlus N σ := by simp only [jMinus, jPlus]; ring
  unfold F3
  rw [e, ← threeJ_cyc (jMinus N σ + jPlus N σ) (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ)]
  exact threeJ_stretched (by unfold mMinus mPlus; ring) hA hB hC hD

lemma F3_top (M σ N μ : ℚ) : F3 (N - 1) M σ N μ = F3 (N - 1) (-σ) (-M) N μ := by
  by_cases h : Adm9 (N - 1) M σ N μ
  · obtain ⟨⟨A, hA⟩, ⟨B, hB⟩, ⟨C, hC⟩, ⟨D, hD⟩⟩ := (⟨h.a1, h.a2, h.b1, h.b2⟩ :
      IsNat _ ∧ IsNat _ ∧ IsNat _ ∧ IsNat _)
    rw [F3_top_formula M σ N μ A B C D hA hB hC hD,
      F3_top_formula (-σ) (-M) N μ D B C A (by simp only [jMinus, jPlus, mMinus, mPlus] at hD ⊢; linarith)
        (by simp only [jMinus, jPlus, mMinus, mPlus] at hB ⊢; linarith)
        (by simp only [jMinus, jPlus, mMinus, mPlus] at hC ⊢; linarith)
        (by simp only [jMinus, jPlus, mMinus, mPlus] at hA ⊢; linarith)]
    have hs : jMinus N σ - jPlus N σ - M = -(jMinus N (-M) - jPlus N (-M) - -σ) := by
      simp only [jMinus, jPlus]; ring
    rw [hs, sgn_neg']
    congr 1
    rw [show D + B = B + D from add_comm _ _, show C + A = A + C from add_comm _ _,
      show B + A = A + B from add_comm _ _, show D + C = C + D from add_comm _ _,
      show B + D + C + A + 1 = A + B + C + D + 1 by ring]
    congr 1
    ring
  · rw [F3_eq_zero h, F3_eq_zero (fun h' => h ((Adm9_swap_iff _ _ _ _ _).mpr h'))]

/-- The coefficient of `F3 L` in the rank recurrence (DLMF 34.3.15). -/
noncomputable def cD (L M σ N μ : ℚ) : ℝ :=
  (2 * (L : ℝ) + 1) * ((((jMinus N σ : ℚ) : ℝ) * (((jMinus N σ : ℚ) : ℝ) + 1) -
    ((jPlus N σ : ℚ) : ℝ) * (((jPlus N σ : ℚ) : ℝ) + 1)) * (M : ℝ) -
    (L : ℝ) * ((L : ℝ) + 1) * (((mPlus M μ : ℚ) : ℝ) - ((mMinus M μ : ℚ) : ℝ)))

/-- The square root `E₃` of the rank recurrence. -/
noncomputable def eD (M σ N : ℚ) (x : ℝ) : ℝ :=
  E3 ((jMinus N σ : ℚ) : ℝ) ((jPlus N σ : ℚ) : ℝ) (M : ℝ) x

lemma cD_swap (L M σ N μ : ℚ) : cD L (-σ) (-M) N μ = cD L M σ N μ := by
  simp only [cD, jMinus, jPlus, mMinus, mPlus]; push_cast; ring

lemma eD_swap (M σ N : ℚ) (x : ℝ) : eD (-σ) (-M) N x = eD M σ N x := by
  unfold eD E3
  congr 1
  simp only [jMinus, jPlus]; push_cast; ring

lemma F3_rec (L M σ N μ : ℚ) (hT : IsTri L (jMinus N σ) (jPlus N σ)) (h1 : IsNat (L + M))
    (h2 : IsNat (L - M)) :
    cD L M σ N μ * F3 L M σ N μ =
      ((L : ℝ) + 1) * eD M σ N (L : ℝ) * F3 (L - 1) M σ N μ
        + (L : ℝ) * eD M σ N ((L : ℝ) + 1) * F3 (L + 1) M σ N μ := by
  have hm : M + mMinus M μ + mPlus M μ = 0 := by simp only [mMinus, mPlus]; ring
  have := threeJ_recurrence_all L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ) hm hT
    (by simpa using h1) (by simpa using h2)
  exact this

lemma isNat_add_one {x : ℚ} (h : IsNat x) : IsNat (x + 1) := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n + 1, by rw [hn]; push_cast; ring⟩

lemma eD_zero (L M σ N : ℚ) (a b c d e : ℕ) (ha : L - σ = a) (hb : L + σ = b) (hc : L - M = c)
    (hd : L + M = d) (he : N - 1 - L = e) (h0 : eD M σ N (L : ℝ) = 0) :
    a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
  have ha' : (L : ℝ) - σ = a := by exact_mod_cast ha
  have hb' : (L : ℝ) + σ = b := by exact_mod_cast hb
  have hc' : (L : ℝ) - M = c := by exact_mod_cast hc
  have hd' : (L : ℝ) + M = d := by exact_mod_cast hd
  have he' : (N : ℝ) - 1 - L = e := by exact_mod_cast he
  have hjd : ((jMinus N σ : ℚ) : ℝ) - ((jPlus N σ : ℚ) : ℝ) = -(σ : ℝ) := by
    simp only [jMinus, jPlus]; push_cast; ring
  have hjs : ((jMinus N σ : ℚ) : ℝ) + ((jPlus N σ : ℚ) : ℝ) + 1 = N := by
    simp only [jMinus, jPlus]; push_cast; ring
  unfold eD E3 at h0
  rw [hjd, hjs] at h0
  have hP : (a : ℝ) * b * (((e : ℝ) + 1) * ((e : ℝ) + 1 + c + d)) * (c * d) ≤ 0 := by
    have hLN : (N : ℝ) = e + 1 + L := by linarith
    have hL2 : (2 : ℝ) * L = c + d := by linarith
    have : ((L : ℝ) ^ 2 - (-(σ : ℝ)) ^ 2) * ((N : ℝ) ^ 2 - (L : ℝ) ^ 2) *
        ((L : ℝ) ^ 2 - (M : ℝ) ^ 2) =
        (a : ℝ) * b * (((e : ℝ) + 1) * ((e : ℝ) + 1 + c + d)) * (c * d) := by
      have h1 : (L : ℝ) ^ 2 - (-(σ : ℝ)) ^ 2 = a * b := by rw [← ha', ← hb']; ring
      have h2 : (L : ℝ) ^ 2 - (M : ℝ) ^ 2 = c * d := by rw [← hc', ← hd']; ring
      have h3 : (N : ℝ) ^ 2 - (L : ℝ) ^ 2 = ((e : ℝ) + 1) * ((e : ℝ) + 1 + c + d) := by
        rw [hLN]; nlinarith [hL2]
      rw [h1, h2, h3]
    rw [← this]
    exact Real.sqrt_eq_zero'.mp h0
  have hnn : (0 : ℝ) ≤ (a : ℝ) * b * (((e : ℝ) + 1) * ((e : ℝ) + 1 + c + d)) * (c * d) := by
    positivity
  have hz : (a : ℝ) * b * (((e : ℝ) + 1) * ((e : ℝ) + 1 + c + d)) * (c * d) = 0 :=
    le_antisymm hP hnn
  have hmid : ((e : ℝ) + 1) * ((e : ℝ) + 1 + c + d) ≠ 0 := by positivity
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · left; exact_mod_cast h
      · right; left; exact_mod_cast h
    · exact absurd h hmid
  · rcases mul_eq_zero.mp h with h | h
    · right; right; left; exact_mod_cast h
    · right; right; right; exact_mod_cast h

/-- One step of the descent in the rank: if the two symbols agree at `L` and `L+1` (and
`L ≤ N-1`) they agree at `L-1`. -/
lemma regge_step (L M σ N μ : ℚ) (hq3 : IsNat (N - 1 - L))
    (hF0 : F3 L M σ N μ = F3 L (-σ) (-M) N μ)
    (hF1 : F3 (L + 1) M σ N μ = F3 (L + 1) (-σ) (-M) N μ) :
    F3 (L - 1) M σ N μ = F3 (L - 1) (-σ) (-M) N μ := by
  have hnon : ¬ Adm9 (L - 1) M σ N μ →
      F3 (L - 1) M σ N μ = F3 (L - 1) (-σ) (-M) N μ := by
    intro h
    rw [F3_eq_zero h, F3_eq_zero (fun h'' => h ((Adm9_swap_iff _ _ _ _ _).mpr h''))]
  by_cases h : Adm9 L M σ N μ
  · have hF := F3_rec L M σ N μ ⟨h.q1, h.q2, h.q3⟩ h.p1 h.p2
    have h' := Adm9_swap h
    have hG := F3_rec L (-σ) (-M) N μ ⟨h'.q1, h'.q2, h'.q3⟩ h'.p1 h'.p2
    rw [cD_swap, eD_swap, eD_swap] at hG
    rw [← hF0, ← hF1] at hG
    have key : ((L : ℝ) + 1) * eD M σ N (L : ℝ) *
        (F3 (L - 1) M σ N μ - F3 (L - 1) (-σ) (-M) N μ) = 0 := by
      linear_combination hG - hF
    obtain ⟨a, ha⟩ := h.q1
    obtain ⟨b, hb⟩ := h.q2
    obtain ⟨c, hc⟩ := h.p2
    obtain ⟨d, hd⟩ := h.p1
    obtain ⟨e, he⟩ := h.q3
    have hL0 : (0 : ℝ) ≤ L := by
      have : (0 : ℚ) ≤ L := by
        have : (0 : ℚ) ≤ c := Nat.cast_nonneg c
        have : (0 : ℚ) ≤ d := Nat.cast_nonneg d
        linarith
      exact_mod_cast this
    have hLpos : ((L : ℝ) + 1) ≠ 0 := by positivity
    rcases mul_eq_zero.mp key with h0 | h0
    · -- the coefficient vanishes: `L` is the lowest rank of one of the four chains
      have he0 : eD M σ N (L : ℝ) = 0 := by
        rcases mul_eq_zero.mp h0 with h1 | h1
        · exact absurd h1 hLpos
        · exact h1
      have ha' : L - σ = a := by simp only [jMinus, jPlus] at ha; linarith
      have hb' : L + σ = b := by simp only [jMinus, jPlus] at hb; linarith
      have he' : N - 1 - L = e := by simp only [jMinus, jPlus] at he; linarith
      apply hnon
      intro hadm
      rcases eD_zero L M σ N a b c d e ha' hb' hc hd he' he0 with h1 | h1 | h1 | h1
      · obtain ⟨n, hn⟩ := hadm.q1
        have : (L - 1) + jMinus N σ - jPlus N σ = -1 := by
          simp only [jMinus, jPlus]; rw [h1] at ha'; push_cast at ha'; linarith
        rw [this] at hn
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      · obtain ⟨n, hn⟩ := hadm.q2
        have : (L - 1) - jMinus N σ + jPlus N σ = -1 := by
          simp only [jMinus, jPlus]; rw [h1] at hb'; push_cast at hb'; linarith
        rw [this] at hn
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      · obtain ⟨n, hn⟩ := hadm.p2
        have : (L - 1) - M = -1 := by rw [h1] at hc; push_cast at hc; linarith
        rw [this] at hn
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      · obtain ⟨n, hn⟩ := hadm.p1
        have : (L - 1) + M = -1 := by rw [h1] at hd; push_cast at hd; linarith
        rw [this] at hn
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
    · linarith
  · apply hnon
    intro hadm
    apply h
    refine ⟨?_, ?_, ?_, ?_, ?_, hadm.a1, hadm.a2, hadm.b1, hadm.b2⟩
    · exact isNat_congr (by ring) (isNat_add_one hadm.q1)
    · exact isNat_congr (by ring) (isNat_add_one hadm.q2)
    · exact isNat_congr (by simp only [jMinus, jPlus]; ring) hq3
    · exact isNat_congr (by ring) (isNat_add_one hadm.p1)
    · exact isNat_congr (by ring) (isNat_add_one hadm.p2)

lemma regge_descent (M σ N μ : ℚ) (k : ℕ) :
    F3 (N - k) M σ N μ = F3 (N - k) (-σ) (-M) N μ ∧
      F3 (N - k - 1) M σ N μ = F3 (N - k - 1) (-σ) (-M) N μ := by
  induction k with
  | zero =>
    constructor
    · have h : ¬ Adm9 (N - ((0 : ℕ) : ℚ)) M σ N μ := by
        intro h
        obtain ⟨n, hn⟩ := h.q3
        have : -(N - ((0 : ℕ) : ℚ)) + jMinus N σ + jPlus N σ = -1 := by
          simp only [jMinus, jPlus]; push_cast; ring
        rw [this] at hn
        have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
        linarith
      rw [F3_eq_zero h, F3_eq_zero (fun h' => h ((Adm9_swap_iff _ _ _ _ _).mpr h'))]
    · have := F3_top M σ N μ
      simpa using this
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    have e1 : N - ((k + 1 : ℕ) : ℚ) = N - k - 1 := by push_cast; ring
    refine ⟨by rw [e1]; exact ih1, ?_⟩
    have := regge_step (N - k - 1) M σ N μ ⟨k, by ring⟩ ih1
      (by rw [show N - k - 1 + 1 = N - k by ring]; exact ih0)
    rw [e1]; exact this

/-- **`eq:3jRegge`, exact Regge exchange of the midpoint `3j` symbol** (all rational labels, no
hypotheses; `N = 2ℓ+1`):
`(L j_- j_+; M m_- m_+) = (L j_-' j_+'; -σ m_-' m_+')` with `j_∓' = (N-1±M)/2 = ℓ ± M/2`,
`m_-' = μ+σ/2`, `m_+' = -μ+σ/2`.  Written as the invariance of the symbol under
`(M,σ) ↦ (-σ,-M)`. -/
theorem threeJ_regge_mid (L M σ N μ : ℚ) :
    threeJ L (jMinus N σ) (jPlus N σ) M (mMinus M μ) (mPlus M μ) =
      threeJ L (jMinus N (-M)) (jPlus N (-M)) (-σ) (mMinus (-σ) μ) (mPlus (-σ) μ) := by
  show F3 L M σ N μ = F3 L (-σ) (-M) N μ
  by_cases hq : IsNat (N - 1 - L)
  · obtain ⟨j, hj⟩ := hq
    have : L = N - ((j + 1 : ℕ) : ℚ) := by push_cast at *; linarith
    rw [this]
    exact (regge_descent M σ N μ (j + 1)).1
  · have h : ¬ Adm9 L M σ N μ := fun h => hq (isNat_congr (by simp only [jMinus, jPlus]; ring) h.q3)
    rw [F3_eq_zero h, F3_eq_zero (fun h' => h ((Adm9_swap_iff _ _ _ _ _).mpr h'))]

/-- **`eq:coeffRegge` at finite `N`**: `Φ_L^{M,σ} = Φ_L^{-σ,-M}` exactly (same phase and
normalisation: `2L + j_++m_+` is the same number on both sides). -/
theorem Phi3j_regge (L M σ N μ : ℚ) : Phi3j L M σ N μ = Phi3j L (-σ) (-M) N μ := by
  unfold Phi3j
  have hs : 2 * L + jPlus N σ + mPlus M μ = 2 * L + jPlus N (-M) + mPlus (-σ) μ := by
    simp only [jPlus, mPlus]; ring
  rw [hs, threeJ_regge_mid]

/-- info: 'FormalResearch.Racah.threeJ_regge_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms threeJ_regge_mid

/-- info: 'FormalResearch.Racah.Phi3j_regge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_regge

/-! ### Reduction of the minimal-rank seeds to `eq:3jseed`

The seed formula `Phi3j_seed` is the chamber `M = L`.  The other three edge chambers
`M = -L`, `σ = ±L` (where `L = L_0 = max(|M|,|σ|)`) reduce to it by the sign symmetry
(`Phi3j_neg_M`) and the Regge exchange (`Phi3j_regge`), up to the `N`-independent signs below. -/

/-- Chamber `σ = -L`: `Φ_L^{M,-L} = Φ_L^{L,-M}` (Regge). -/
theorem Phi3j_edge_sigma_neg (L M N μ : ℚ) : Phi3j L M (-L) N μ = Phi3j L L (-M) N μ := by
  rw [Phi3j_regge L M (-L) N μ, neg_neg]

/-- Chamber `M = -L`: `Φ_L^{-L,σ}(x) = (-1)^{L-σ} Φ_L^{L,σ}(-x)`. -/
theorem Phi3j_edge_M_neg (L σ N μ : ℚ) (hL : ∃ n : ℤ, 2 * L = n)
    (ht : ∃ n : ℤ, N - 1 + σ = n) (hk : ∃ n : ℤ, L - σ = n)
    (hc : ∃ n : ℤ, jPlus N σ + mPlus L (-μ) = n) :
    Phi3j L (-L) σ N μ = sgn (L - σ) * Phi3j L L σ N (-μ) := by
  have := Phi3j_neg_M L L σ N (-μ) hL ht hk hc
  rwa [neg_neg] at this

/-- Chamber `σ = L`: `Φ_L^{M,L} = Φ_L^{-L,-M}` (Regge), hence by the sign symmetry
`= (-1)^{L+M} Φ_L^{L,-M}(-x)`. -/
theorem Phi3j_edge_sigma_pos (L M N μ : ℚ) (hL : ∃ n : ℤ, 2 * L = n)
    (ht : ∃ n : ℤ, N - 1 + -M = n) (hk : ∃ n : ℤ, L - -M = n)
    (hc : ∃ n : ℤ, jPlus N (-M) + mPlus L (-μ) = n) :
    Phi3j L M L N μ = sgn (L + M) * Phi3j L L (-M) N (-μ) := by
  rw [Phi3j_regge L M L N μ, Phi3j_edge_M_neg L (-M) N μ hL ht hk hc, sub_neg_eq_add]

end FormalResearch.Racah

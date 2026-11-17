module

public import FormalResearch.Special.RacahWindowChain
public import FormalResearch.Special.BulkIndexRight
public import FormalResearch.Special.BulkKappaRacahInst

/-!
# Racah window, part 5: no nodes beyond the turning point of the `6j` chain (integer data, `τ = +1`)

The Racah counterpart of `bix_last_ne_zero`, `bix_hahn_tail` (`BulkIndexRight`).  For the integer `6j` chain `Ŷ_k = racah6jY a b c m n k` of shape `(α, β, x)`, `τ = +1`, on the support
`kmin = max |m| |n| ≤ k ≤ kmax = min(2b + m, 2a + n) = kmin + D'` (`D'` the dimension of the Racah system, `rw_D_eq`):

* `rw_edge`: at `K h = 2α` or `2β` (`K = kmax + 1`) the point `(K h)²` lies in `Dom P Q` and `ẽ((K h)²) = 0` (the hard edge);
* `rw_last_ne_zero`: `Ŷ_{kmax} ≠ 0` (zero propagation `hd_zero_backward` from the hard edge row `A_{kmax+1} = 0`, then the total mass `rd_sum` is positive);
* **`rwn_racah_tail`**: there is `ε > 0` (depending on `(α, β, x, m, n)`) such that for `h ≤ ε` and every site `K + i₁` with `q ≥ q_*` the bonds `i₁, …, D' - 1` carry no node (`bix_tail_sign`:
  all `Ŷ_j`, `j ≥ K + i₁`, are nonzero of one sign).  Hypothesis `1 ≤ kmin` is not needed here (rows `k ≥ 1` only).

**Claim class: proved** (axiom guards pinned).  **Not formalised:** `τ = -1`, half-integer lattice.
-/

@[expose] public section

open Finset FormalResearch.Racah FormalResearch.Racah.SixJ FormalResearch.Racah.P3 FormalResearch.Wigner FormalResearch.DiscreteAiry
open scoped Real

namespace FormalResearch.Special

/-- `D' = kmax - kmin` for a Racah system with integer data. -/
lemma rw_D_eq (a b m n : ℤ) {D : ℕ} (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D) :
    (D : ℤ) = min (2 * b + m) (2 * a + n) - max |m| |n| := by
  set lo : ℤ := max |m| |n| with hlo
  set hi : ℤ := min (2 * b + m) (2 * a + n) with hhi
  have h1 := hsys.dim
  have h2 := cMax_sub_cMin (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ)
  have e1 : fMin (m : ℚ) (n : ℚ) = (lo : ℚ) := by rw [hlo]; unfold fMin; push_cast; rfl
  have e2 : fMax (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) = (hi : ℚ) := by rw [hhi]; unfold fMax; push_cast; exact min_comm _ _
  rw [e1, e2] at h2
  rw [h2] at h1
  have : ((D : ℤ) : ℚ) = ((hi - lo : ℤ) : ℚ) := by push_cast; linarith
  exact_mod_cast this

/-- The hard edge: `(K h)² ∈ Dom` and `ẽ((K h)²) = 0` when `K h = 2α` or `2β` is the smaller of the two. -/
lemma rw_edge {α β h K : ℝ} (hα : 0 < α) (hβ : 0 < β) (hK : K * h = 2 * α ∨ K * h = 2 * β)
    (h2 : K * h ≤ 2 * α) (h3 : K * h ≤ 2 * β) (hK0 : 0 ≤ K * h) :
    (K * h) ^ 2 ∈ Dom (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ∧
      etilde (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((K * h) ^ 2) = 0 := by
  have a1 : (K * h) ^ 2 ≤ 4 * α ^ 2 := by nlinarith
  have a2 : (K * h) ^ 2 ≤ 4 * β ^ 2 := by nlinarith
  have hα2 : 0 < 4 * α ^ 2 := by positivity
  have hβ2 : 0 < 4 * β ^ 2 := by positivity
  have b1 : 1 / (4 * α ^ 2) * (K * h) ^ 2 ≤ 1 := by
    rw [one_div_mul_eq_div, div_le_one hα2]; exact a1
  have b2 : 1 / (4 * β ^ 2) * (K * h) ^ 2 ≤ 1 := by
    rw [one_div_mul_eq_div, div_le_one hβ2]; exact a2
  refine ⟨⟨sq_nonneg _, b1, b2⟩, ?_⟩
  unfold etilde
  apply Real.sqrt_eq_zero_of_nonpos
  have c1 : 0 ≤ 1 - 1 / (4 * α ^ 2) * (K * h) ^ 2 := by linarith
  have c2 : 0 ≤ 1 - 1 / (4 * β ^ 2) * (K * h) ^ 2 := by linarith
  rcases hK with hK | hK
  · have : 1 - 1 / (4 * α ^ 2) * (K * h) ^ 2 = 0 := by
      rw [hK, one_div_mul_eq_div]; field_simp; ring
    rw [this]; simp
  · have : 1 - 1 / (4 * β ^ 2) * (K * h) ^ 2 = 0 := by
      rw [hK, one_div_mul_eq_div]; field_simp; ring
    rw [this]; simp


/-- The rows of the `6j` chain at `(α, β, x)`. -/
lemma rw_rows {α β x h : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D' : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') (i : Fin (D' + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β)
    (hx : cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x) (k : ℤ) (hk : 1 ≤ k) :
    jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
      (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (m : ℝ) (n : ℝ) h) (racah6jY a b c m n) k = 0 := by
  obtain ⟨hA, hB, -⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  have := racah_class_chain a b c m n h hh hA hB k hk
  rw [hAh, hBh, hx] at this
  exact this

/-- The hard edge in the form needed by the tail: `kmax = min(2b+m, 2a+n)`. -/
lemma rw_hedge {α β h : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b m n : ℤ) {kmax : ℕ}
    (hkmax : (kmax : ℤ) = min (2 * b + m) (2 * a + n)) (hAh : wA (a : ℚ) (n : ℚ) * h = α)
    (hBh : wB (b : ℚ) (m : ℚ) * h = β) (hh : 0 < h) :
    (((kmax : ℝ) + 1) * h) ^ 2 ∈ Dom (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ∧
      etilde (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) ((((kmax : ℝ) + 1) * h) ^ 2) = 0 := by
  have e : ((kmax : ℝ) + 1) = (((min (2 * b + m) (2 * a + n)) + 1 : ℤ) : ℝ) := by rw [← hkmax]; push_cast; ring
  have hA2 : (((min (2 * b + m) (2 * a + n)) + 1 : ℤ) : ℝ) ≤ 2 * wA (a : ℚ) (n : ℚ) := by
    have h1 : min (2 * b + m) (2 * a + n) ≤ 2 * a + n := min_le_right _ _
    have : (((min (2 * b + m) (2 * a + n)) : ℤ) : ℝ) ≤ ((2 * a + n : ℤ) : ℝ) := by exact_mod_cast h1
    unfold wA; push_cast at this ⊢; linarith
  have hB2 : (((min (2 * b + m) (2 * a + n)) + 1 : ℤ) : ℝ) ≤ 2 * wB (b : ℚ) (m : ℚ) := by
    have h1 : min (2 * b + m) (2 * a + n) ≤ 2 * b + m := min_le_left _ _
    have : (((min (2 * b + m) (2 * a + n)) : ℤ) : ℝ) ≤ ((2 * b + m : ℤ) : ℝ) := by exact_mod_cast h1
    unfold wB; push_cast at this ⊢; linarith
  have hnn : (0 : ℝ) ≤ ((kmax : ℝ) + 1) * h := by positivity
  refine rw_edge (α := α) (β := β) (h := h) (K := (kmax : ℝ) + 1) hα hβ ?_ ?_ ?_ hnn
  · rw [e]
    rcases min_choice (2 * b + m) (2 * a + n) with hc' | hc'
    · right
      have : (((min (2 * b + m) (2 * a + n)) + 1 : ℤ) : ℝ) = 2 * wB (b : ℚ) (m : ℚ) := by
        rw [hc']; unfold wB; push_cast; ring
      rw [this, ← hBh]; ring
    · left
      have : (((min (2 * b + m) (2 * a + n)) + 1 : ℤ) : ℝ) = 2 * wA (a : ℚ) (n : ℚ) := by
        rw [hc']; unfold wA; push_cast; ring
      rw [this, ← hAh]; ring
  · rw [e, ← hAh]; nlinarith
  · rw [e, ← hBh]; nlinarith

/-- **The last site of the `6j` chain is nonzero.** -/
theorem rw_last_ne_zero {α β x h : ℝ} (hα : 0 < α) (hβ : 0 < β) (a b c m n : ℤ) {D' : ℕ}
    (hsys : RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D') (i : Fin (D' + 1))
    (hc : (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i) (hh : 0 < h)
    (hAh : wA (a : ℚ) (n : ℚ) * h = α) (hBh : wB (b : ℚ) (m : ℚ) * h = β)
    (hx : cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x) (hlo : 1 ≤ max |m| |n|) :
    racah6jY a b c m n (min (2 * b + m) (2 * a + n)) ≠ 0 := by
  obtain ⟨hA, hB, hC⟩ := rd_pos hα hβ a b c m n i hc hh hAh hBh
  set K : ℤ := max |m| |n| with hKdef
  set kZ : ℤ := min (2 * b + m) (2 * a + n) with hkZ
  have hD := rw_D_eq a b m n hsys
  have hkK : K ≤ kZ := by omega
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℕ, (Kn : ℤ) = K := ⟨K.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = kZ := ⟨kZ.toNat, Int.toNat_of_nonneg (by omega)⟩
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  have hedge := rw_hedge hα hβ a b m n (kmax := kmax) (by rw [hkmax]) hAh hBh hh
  intro h0
  have hY0 : racah6jY a b c m n (kmax : ℤ) = 0 := by rw [hkmax]; exact h0
  have key := hd_zero_backward (fun i : ℕ => hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h (i : ℤ))
    (fun i : ℕ => hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (m : ℝ) (n : ℝ) h (i : ℤ))
    (fun i : ℕ => racah6jY a b c m n (i : ℤ)) (Kn + 1) kmax (by omega)
    (by
      intro j h1 h2
      have hjK : ((K : ℤ) : ℝ) < (j : ℝ) := by
        have : K < (j : ℤ) := by omega
        exact_mod_cast this
      have hm : |(m : ℝ)| ≤ (K : ℝ) := by
        have : |m| ≤ K := le_max_left _ _
        have h' : ((|m| : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
        simpa using h'
      have hn : |(n : ℝ)| ≤ (K : ℝ) := by
        have : |n| ≤ K := le_max_right _ _
        have h' : ((|n| : ℤ) : ℝ) ≤ (K : ℝ) := by exact_mod_cast this
        simpa using h'
      have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hlo
      refine hr_Ak_pos hP hQ hh h2 (by linarith) ?_ ?_ hedge.1
      · have : |(m : ℝ)| < j := lt_of_le_of_lt hm hjK
        have := pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
        rwa [sq_abs] at this
      · have : |(n : ℝ)| < j := lt_of_le_of_lt hn hjK
        have := pow_lt_pow_left₀ this (abs_nonneg _) two_ne_zero
        rwa [sq_abs] at this)
    (by
      show hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h (((kmax + 1 : ℕ) : ℤ)) = 0
      have := racah_end_upper a b m n h hh hA hB (by omega)
      rw [hAh, hBh] at this
      rw [← hkZ] at this
      have e : (((kmax + 1 : ℕ) : ℤ)) = kZ + 1 := by push_cast; omega
      rw [e]; exact this)
    (by
      intro j h1 h2
      have hk := rw_rows (x := x) hα hβ a b c m n hsys i hc hh hAh hBh hx (j : ℤ) (by omega)
      unfold jac at hk
      show hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h ((j + 1 : ℕ) : ℤ) * racah6jY a b c m n ((j + 1 : ℕ) : ℤ) +
        hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h (j : ℤ) * racah6jY a b c m n ((j - 1 : ℕ) : ℤ) =
        hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (m : ℝ) (n : ℝ) h (j : ℤ) * racah6jY a b c m n (j : ℤ)
      have e1 : (((j + 1 : ℕ) : ℤ)) = (j : ℤ) + 1 := by push_cast; ring
      have e2 : (((j - 1 : ℕ) : ℤ)) = (j : ℤ) - 1 := by omega
      rw [e1, e2]; linarith)
    hY0
  have hmass := rd_sum a b c m n hsys i hc
  have hpos : 0 < 4 * wA (a : ℚ) (n : ℚ) * wB (b : ℚ) (m : ℚ) / (2 * wC (c : ℚ)) := by positivity
  rw [← hmass] at hpos
  have hz : ∑ k ∈ Finset.Ico K (kZ + 1), racah6jY a b c m n k ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Ico] at hk
    obtain ⟨kn, hkn⟩ : ∃ kn : ℕ, (kn : ℤ) = k := ⟨k.toNat, Int.toNat_of_nonneg (by omega)⟩
    have := key kn (by omega) (by omega)
    simp only [hkn] at this
    rw [this]; ring
  rw [hz] at hpos
  exact lt_irrefl _ hpos

/-- info: 'FormalResearch.Special.rw_last_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rw_last_ne_zero


/-- **No nodes beyond the turning point of the integer `6j` chain** (`τ = +1`).  There is `ε > 0` such that for every finite Racah system with `A h = α`, `B h = β`,
`cos = x`, `h ≤ ε` and every site `K + i₁` with `q ≥ q_*` (`K = max |m| |n|`), the bonds `i₁, …, D' - 1` carry no node (all `Ŷ_j`, `j ≥ K + i₁`, are nonzero of one sign). -/
theorem rwn_racah_tail (α β x : ℝ) (hα : 0 < α) (hβ : 0 < β) (hx1 : -1 < x) (hx2 : x < 1)
    (hprod : (α - β * x) * (β - α * x) < 0) (m n : ℤ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (a b c : ℤ) (D' : ℕ), RacahSystem (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) D' → ∀ i : Fin (D' + 1),
        (c : ℚ) = cPt (a : ℚ) (b : ℚ) (m : ℚ) (n : ℚ) i → ∀ h : ℝ, 0 < h → h ≤ ε →
        wA (a : ℚ) (n : ℚ) * h = α → wB (b : ℚ) (m : ℚ) * h = β →
        cosA (wA (a : ℚ) (n : ℚ)) (wB (b : ℚ) (m : ℚ)) (wC (c : ℚ)) = x → 1 ≤ max |m| |n| →
        ∀ i₁ : ℕ, racahQs α β x ≤ rwQ (1 / 2) h (max |m| |n| + (i₁ : ℤ)) →
          ∑ j ∈ Ico i₁ D', bix_c (fun s : ℕ => racah6jY a b c m n (max |m| |n| + (s : ℤ))) j = 0 := by
  obtain ⟨hqs, hκ, hαq, hβq, hturn⟩ := racah_turn_geom_pos hα hβ hx1 hx2 hprod
  set qs : ℝ := racahQs α β x with hqsdef
  have hP : (0 : ℝ) ≤ 1 / (4 * α ^ 2) := by positivity
  have hQ : (0 : ℝ) ≤ 1 / (4 * β ^ 2) := by positivity
  have hM0 : 0 < hrM (m : ℝ) (n : ℝ) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hρ0 : 0 ≤ hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) qs := by unfold hrRho; positivity
  have hK : 0 < 2 * ((1 - 1 * x) / qs ^ 2) * qs := by positivity
  refine ⟨min (qs / (2 * hrM (m : ℝ) (n : ℝ)))
    ((2 * ((1 - 1 * x) / qs ^ 2) * qs) / (hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) qs + 1)),
    lt_min (by positivity) (by positivity), ?_⟩
  intro a b c D' hsys i hc h hh hhε hAh hBh hx hlo i₁ hi₁
  by_cases hmi : D' ≤ i₁
  · simp [Finset.Ico_eq_empty_of_le hmi]
  push Not at hmi
  set K : ℤ := max |m| |n| with hKdef
  have hKnn : 0 ≤ K := by omega
  have hD := rw_D_eq a b m n hsys
  obtain ⟨Kn, hKn⟩ : ∃ Kn : ℕ, (Kn : ℤ) = K := ⟨K.toNat, Int.toNat_of_nonneg hKnn⟩
  obtain ⟨kmax, hkmax⟩ : ∃ kmax : ℕ, (kmax : ℤ) = min (2 * b + m) (2 * a + n) :=
    ⟨(min (2 * b + m) (2 * a + n)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hkmaxD : kmax = Kn + D' := by omega
  have hedge := rw_hedge hα hβ a b m n hkmax hAh hBh hh
  have hεM : h ≤ qs / (2 * hrM (m : ℝ) (n : ℝ)) := hhε.trans (min_le_left _ _)
  have hεC : h ≤ (2 * ((1 - 1 * x) / qs ^ 2) * qs) / (hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) qs + 1) :=
    hhε.trans (min_le_right _ _)
  have hhM : h * (2 * hrM (m : ℝ) (n : ℝ)) ≤ qs := by
    rwa [le_div_iff₀ (by positivity)] at hεM
  have hhC : h * hrRho (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) qs ≤ 2 * ((1 - 1 * x) / qs ^ 2) * qs := by
    rw [le_div_iff₀ (by positivity)] at hεC
    nlinarith
  have hk1 : qs ≤ (((Kn + i₁ : ℕ) : ℝ) + 1 / 2) * h := by
    have : (((Kn + i₁ : ℕ) : ℝ)) = ((K + (i₁ : ℤ) : ℤ) : ℝ) := by rw [← hKn]; push_cast; ring
    rw [this]; exact hi₁
  have hrows : ∀ k ∈ Finset.Icc (((Kn + i₁ : ℕ) : ℤ) + 1) (kmax : ℤ),
      jac (hrAk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) (m : ℝ) (n : ℝ) h)
        (hrCk (1 / (4 * α ^ 2)) (1 / (4 * β ^ 2)) 1 x (m : ℝ) (n : ℝ) h) (racah6jY a b c m n) k = 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact rw_rows (x := x) hα hβ a b c m n hsys i hc hh hAh hBh hx k (by omega)
  have hYN : racah6jY a b c m n (kmax : ℤ) ≠ 0 := by
    rw [hkmax]; exact rw_last_ne_zero hα hβ a b c m n hsys i hc hh hAh hBh hx hlo
  have H := bix_tail_sign (P := 1 / (4 * α ^ 2)) (Q := 1 / (4 * β ^ 2)) hP hQ (m : ℝ) (n : ℝ) 1 x qs h hqs hh (by norm_num) hκ hturn
    hhM hhC kmax (Kn + i₁) hedge.1 hedge.2 hk1 (by omega) (racah6jY a b c m n) hrows hYN
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Ico] at hj
  have p1 := H (Kn + j) (by omega) (by omega)
  have p2 := H (Kn + (j + 1)) (by omega) (by omega)
  have e1 : ((Kn + j : ℕ) : ℤ) = K + (j : ℤ) := by push_cast; omega
  have e2 : ((Kn + (j + 1) : ℕ) : ℤ) = K + ((j + 1 : ℕ) : ℤ) := by push_cast; omega
  rw [e1] at p1
  rw [e2] at p2
  have hne : racah6jY a b c m n (K + (j : ℤ)) ≠ 0 := by
    intro h0; rw [h0] at p1; simp at p1
  have hpos : 0 < racah6jY a b c m n (K + (j : ℤ)) * racah6jY a b c m n (K + ((j + 1 : ℕ) : ℤ)) := by
    have := mul_pos p1 p2
    have h2 : 0 < racah6jY a b c m n (kmax : ℤ) ^ 2 := by positivity
    have e : (racah6jY a b c m n (K + (j : ℤ)) * racah6jY a b c m n (kmax : ℤ)) *
        (racah6jY a b c m n (K + ((j + 1 : ℕ) : ℤ)) * racah6jY a b c m n (kmax : ℤ)) =
        (racah6jY a b c m n (K + (j : ℤ)) * racah6jY a b c m n (K + ((j + 1 : ℕ) : ℤ))) *
          racah6jY a b c m n (kmax : ℤ) ^ 2 := by ring
    rw [e] at this
    exact (mul_pos_iff_of_pos_right h2).1 this
  unfold bix_c
  have h0 : ¬ (racah6jY a b c m n (K + (j : ℤ)) * racah6jY a b c m n (K + ((j + 1 : ℕ) : ℤ)) < 0) :=
    not_lt.2 hpos.le
  have h1 : ¬ (0 < j ∧ racah6jY a b c m n (K + (j : ℤ)) = 0) := fun h => hne h.2
  simp only [h0, h1, ↓reduceIte]
  rfl

/-- info: 'FormalResearch.Special.rwn_racah_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.rwn_racah_tail

end FormalResearch.Special

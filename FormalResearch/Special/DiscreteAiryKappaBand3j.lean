module

public import FormalResearch.Special.DiscreteAiryKappaBandHahn
public import FormalResearch.Special.DiscreteAiryKappaRiemann
public import FormalResearch.Special.DiscreteAiryKappaLeft
public import FormalResearch.Special.DiscreteAiryLimitChains3j

/-!
# The mass of the actual `3j` Hahn chain on a band (plan K1, step K-2)

Instance of `kp_hahn_band_mass` for `Ŷ = hahn3jY M σ N x` (`DiscreteAiryLimitChains3j`) with `h = 1/N`, `a_k = hrAk 1 0 M σ h k`,
`c_k = hrCk 1 0 1 x M σ h k = x - Mσ/(k(k+1))` (`hahn_class_chain`): `a_k² = (1+η_k)(1-(kh)²)/4` with `η_k = r_k² - 1`,
`|η_k| ≤ 3β/k²` (`β = M² + σ² + 1/3`, `kl_beta`) and `|κ_k| = |Mσ|/(k(k+1)) ≤ |Mσ|/k²` for `k² > β` (`kb_eta_bound`, `kb_coef`).

**Claim class: proved.**  See `hahn3j_band_mass`.
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `|r_k² - 1| ≤ 3β/k²` and `r_k > 0` for `1 ≤ k`, `β < k²` (`β = M² + σ² + 1/3`). -/
lemma kb_eta_bound {M σ k : ℝ} (hk : 1 ≤ k) (hβ : kl_beta M σ < k ^ 2) :
    |rr M σ k ^ 2 - 1| ≤ 3 * kl_beta M σ / k ^ 2 ∧ 0 < rr M σ k := by
  have hM : M ^ 2 ≤ k ^ 2 := by unfold kl_beta at hβ; nlinarith [sq_nonneg σ]
  have hσ : σ ^ 2 ≤ k ^ 2 := by unfold kl_beta at hβ; nlinarith [sq_nonneg M]
  have h1 := kl_rr_close hk hM hσ
  have hk2 : 0 < k ^ 2 := by positivity
  have hb : kl_beta M σ / k ^ 2 < 1 := by rw [div_lt_one hk2]; exact hβ
  have hb0 : 0 ≤ kl_beta M σ / k ^ 2 := by unfold kl_beta; positivity
  have h2 := abs_le.1 h1
  refine ⟨?_, by linarith [h2.1]⟩
  have e : rr M σ k ^ 2 - 1 = (rr M σ k - 1) * (rr M σ k + 1) := by ring
  rw [e, abs_mul]
  have h3 : |rr M σ k + 1| ≤ 3 := by
    rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
  calc |rr M σ k - 1| * |rr M σ k + 1| ≤ (kl_beta M σ / k ^ 2) * 3 := mul_le_mul h1 h3 (abs_nonneg _) hb0
    _ = 3 * kl_beta M σ / k ^ 2 := by ring

/-- **Coefficients of the actual chain on the band**: `a_k > 0`, `a_k² = (1 + (r_k² - 1))(1 - (kh)²)/4`, `|Mσ/(k(k+1))| ≤ |Mσ|/k²`. -/
lemma kb_coef (M σ x h : ℝ) {k : ℤ} (hk : 1 ≤ k) (hβ : kl_beta M σ < (k : ℝ) ^ 2) (hkh : ((k : ℝ) * h) ^ 2 < 1) :
    0 < hrAk 1 0 M σ h k ∧ hrAk 1 0 M σ h k ^ 2 = (1 + (rr M σ (k : ℝ) ^ 2 - 1)) * ((1 - ((k : ℝ) * h) ^ 2) / 4) ∧
      hrCk 1 0 1 x M σ h k = x - M * σ / ((k : ℝ) * ((k : ℝ) + 1)) ∧
      |M * σ / ((k : ℝ) * ((k : ℝ) + 1))| ≤ |M * σ| / (k : ℝ) ^ 2 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨-, hrr⟩ := kb_eta_bound hk' hβ
  have hs : 0 < Real.sqrt (1 - ((k : ℝ) * h) ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hsq : Real.sqrt (1 - ((k : ℝ) * h) ^ 2) ^ 2 = 1 - ((k : ℝ) * h) ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨?_, ?_, kl_hrC x M σ h k, ?_⟩
  · rw [kl_hrA]; positivity
  · rw [kl_hrA]
    have : (1 / 2 * rr M σ (k : ℝ) * Real.sqrt (1 - ((k : ℝ) * h) ^ 2)) ^ 2 =
        rr M σ (k : ℝ) ^ 2 * (1 / 4) * Real.sqrt (1 - ((k : ℝ) * h) ^ 2) ^ 2 := by ring
    rw [this, hsq]; ring
  · rw [abs_div, abs_of_pos (by positivity : 0 < (k : ℝ) * ((k : ℝ) + 1))]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    nlinarith

/-- The total relative variation `S = Σ_{i≤m} ε_{k₀+i}` of the amplitude form along the band, with the `3j` bounds
`η̄_k = 3β/k²`, `κ̄_k = |Mσ|/k²`. -/
noncomputable def kb3S (M σ : ℤ) (x h A : ℝ) (k0 : ℤ) (m : ℕ) : ℝ :=
  ∑ i ∈ range (m + 1), kpEps x h A (3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)
    (|(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)

/-- **The mass of the actual `3j` chain on a band** (`kp_hahn_band_mass` for `Ŷ = hahn3jY M σ N x`, `h = 1/N`).  Band
`k₀, …, k₀+m` with `β < k₀²` (`β = M² + σ² + 1/3`), `A² ≤ q_*² - q_j²` for `j = k₀-1, …, k₀+m+1` (`q_*² = 1 - x²`),
`3β/k₀² ≤ x²`, `|Mσ|/k₀² ≤ 1` and every `ε_{k₀+i} ≤ ½`.  With `I = I_{k₀}(Ŷ)` the amplitude form of the profile `P = 2/α`:
`|Σ_{i≤m} Ŷ_{k₀+i}² - I Σ_{i≤m} P_{k₀+i}/2| ≤ I [((e^{2S} - 1)e^S + 4(|r| + τ)e^S) Σ P/2 + (2τ/A + 32/A³)e^S]`,
`S = kb3S`, `r = kpRb(η_B, κ_B)`, `τ = kpDub(η_B)`, `η_B = 3β/k₀²`, `κ_B = |Mσ|/k₀²`. -/
theorem hahn3j_band_mass (M σ N : ℤ) (x : ℚ) (hN : 0 < N) (hx0 : (0 : ℝ) < x) (hx1 : (x : ℝ) < 1) {k0 : ℤ} (m : ℕ)
    {A : ℝ} (hk0 : 1 ≤ k0) (hβk : kl_beta (M : ℝ) (σ : ℝ) < (k0 : ℝ) ^ 2) (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hband : ∀ j : ℤ, k0 - 1 ≤ j → j ≤ k0 + ((m + 1 : ℕ) : ℤ) →
      A ^ 2 ≤ (Real.sqrt (1 - (x : ℝ) ^ 2)) ^ 2 - kpU (1 / (N : ℝ)) j ^ 2)
    (hηB : 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 ≤ (x : ℝ) ^ 2)
    (hκB : |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 ≤ 1)
    (hε : ∀ i : ℕ, i < m + 1 → kpEps (x : ℝ) (1 / (N : ℝ)) A
      (3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2)
      (|(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2) ≤ 1 / 2) :
    0 ≤ kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 ∧
    (∀ i : ℕ, i ≤ m + 1 →
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x)
          (k0 + (i : ℤ)) ≤
        Real.exp (kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) *
          kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 ∧
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 ≤
        Real.exp (2 * kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) *
          kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x)
            (k0 + (i : ℤ))) ∧
    |∑ i ∈ range (m + 1), hahn3jY M σ N x (k0 + (i : ℤ)) ^ 2 -
        kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 *
          ∑ i ∈ range (m + 1), kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ)) (k0 + (i : ℤ)) / 2| ≤
      kermI (hrAk 1 0 (M : ℝ) (σ : ℝ) (1 / (N : ℝ))) (kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ))) (hahn3jY M σ N x) k0 *
        (((Real.exp (2 * kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) - 1) * Real.exp (kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m) +
          4 * (|kpRb (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2)
                (|(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2)| +
              kpDub (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2)) *
            Real.exp (kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m)) *
          ∑ i ∈ range (m + 1), kpP (Real.sqrt (1 - (x : ℝ) ^ 2)) (1 / (N : ℝ)) (k0 + (i : ℤ)) / 2 +
        (2 * kpDub (x : ℝ) (1 / (N : ℝ)) A (3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) / A + 32 / A ^ 3) *
          Real.exp (kb3S M σ (x : ℝ) (1 / (N : ℝ)) A k0 m)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 1 / (N : ℝ) := by positivity
  set h : ℝ := 1 / (N : ℝ) with hhdef
  set qs : ℝ := Real.sqrt (1 - (x : ℝ) ^ 2) with hqsdef
  have hqs : qs ^ 2 = 1 - (x : ℝ) ^ 2 := Real.sq_sqrt (by nlinarith)
  have hk0' : (1 : ℝ) ≤ k0 := by exact_mod_cast hk0
  have hkc : ∀ i : ℕ, (k0 : ℝ) ≤ ((k0 + (i : ℤ) : ℤ) : ℝ) := fun i => by
    push_cast; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith
  have hβ : ∀ i : ℕ, kl_beta (M : ℝ) (σ : ℝ) < (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 := fun i => by
    have := hkc i
    have h2 : (k0 : ℝ) ^ 2 ≤ (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 := by nlinarith
    linarith
  have hkh : ∀ i : ℕ, i ≤ m + 1 → ((((k0 + (i : ℤ) : ℤ) : ℝ)) * h) ^ 2 < 1 := by
    intro i hi
    have hj := hband (k0 + (i : ℤ)) (by omega) (by omega)
    have hU : 0 < kpU h (k0 + (i : ℤ)) := by
      unfold kpU; push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      exact mul_pos (by linarith) hh
    have hqs1 : qs ^ 2 ≤ 1 := by nlinarith [sq_nonneg (x : ℝ)]
    have hU1 := kpU_lt_one hqs1 hA0 hj hU
    have hm0 : 0 ≤ (((k0 + (i : ℤ) : ℤ) : ℝ)) * h := by
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      push_cast; positivity
    have hlt : (((k0 + (i : ℤ) : ℤ) : ℝ)) * h ≤ kpU h (k0 + (i : ℤ)) := by
      unfold kpU; push_cast; nlinarith
    nlinarith
  have hcoef : ∀ i : ℕ, i ≤ m + 1 → 0 < hrAk 1 0 (M : ℝ) (σ : ℝ) h (k0 + (i : ℤ)) ∧
      hrAk 1 0 (M : ℝ) (σ : ℝ) h (k0 + (i : ℤ)) ^ 2 = (1 + (rr (M : ℝ) (σ : ℝ) (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 - 1)) *
        ((1 - ((((k0 + (i : ℤ) : ℤ) : ℝ)) * h) ^ 2) / 4) ∧
      hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) h (k0 + (i : ℤ)) = (x : ℝ) - (M : ℝ) * (σ : ℝ) /
        ((((k0 + (i : ℤ) : ℤ) : ℝ)) * ((((k0 + (i : ℤ) : ℤ) : ℝ)) + 1)) ∧
      |(M : ℝ) * (σ : ℝ) / ((((k0 + (i : ℤ) : ℤ) : ℝ)) * ((((k0 + (i : ℤ) : ℤ) : ℝ)) + 1))| ≤
        |(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 := fun i hi =>
    kb_coef (M : ℝ) (σ : ℝ) (x : ℝ) h (k := k0 + (i : ℤ)) (by omega) (hβ i) (hkh i hi)
  have hetab : ∀ i : ℕ, |rr (M : ℝ) (σ : ℝ) (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 - 1| ≤
      3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 := fun i =>
    (kb_eta_bound (by have := hkc i; linarith) (hβ i)).1
  have hβ0 : 0 ≤ kl_beta (M : ℝ) (σ : ℝ) := by unfold kl_beta; positivity
  have hmono : ∀ i : ℕ, 3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 ≤
      3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2 := fun i => by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := hkc i; nlinarith
  have hmono' : ∀ i : ℕ, |(M : ℝ) * (σ : ℝ)| / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 ≤ |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2 := fun i => by
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    have := hkc i; nlinarith
  have hsucc : ∀ i : ℕ, k0 + ((i + 1 : ℕ) : ℤ) = k0 + (i : ℤ) + 1 := fun i => by push_cast; ring
  have hstep : ∀ i : ℕ, 3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) + 1 : ℤ) : ℝ)) ^ 2 ≤
      3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) : ℤ) : ℝ)) ^ 2 := fun i => by
    apply div_le_div_of_nonneg_left (by positivity) (by have := hkc i; positivity)
    have h0i : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    push_cast; nlinarith
  refine kp_hahn_band_mass (x := (x : ℝ)) (qs := qs) (h := h) (A := A)
    (ηB := 3 * kl_beta (M : ℝ) (σ : ℝ) / (k0 : ℝ) ^ 2) (κB := |(M : ℝ) * (σ : ℝ)| / (k0 : ℝ) ^ 2)
    (a := hrAk 1 0 (M : ℝ) (σ : ℝ) h) (c := hrCk 1 0 1 (x : ℝ) (M : ℝ) (σ : ℝ) h)
    (η := fun k => rr (M : ℝ) (σ : ℝ) (k : ℝ) ^ 2 - 1) (κ := fun k => (M : ℝ) * (σ : ℝ) / ((k : ℝ) * ((k : ℝ) + 1)))
    (ηb := fun k => 3 * kl_beta (M : ℝ) (σ : ℝ) / (k : ℝ) ^ 2) (κb := fun k => |(M : ℝ) * (σ : ℝ)| / (k : ℝ) ^ 2)
    (Y := hahn3jY M σ N x) (k0 := k0) m hx0 hqs hh hk0 hA0 hA1 hband
    (fun i hi => hahn_class_chain M σ N x hN _ (by omega))
    (fun i hi => (hcoef i hi).1) (fun i hi => (hcoef i hi).2.1) ?_ ?_ (fun i hi => (hcoef i (by omega)).2.2.1) ?_ hε
  · intro i hi
    exact (hetab i).trans ((hmono i).trans hηB)
  · intro i hi
    have h1 := hetab i
    have h2 : |rr (M : ℝ) (σ : ℝ) (((k0 + (i : ℤ) + 1 : ℤ) : ℝ)) ^ 2 - 1| ≤
        3 * kl_beta (M : ℝ) (σ : ℝ) / (((k0 + (i : ℤ) + 1 : ℤ) : ℝ)) ^ 2 := by
      have := hetab (i + 1); rw [hsucc] at this; exact this
    exact ⟨h1, h2.trans (hstep i), hmono i, hηB⟩
  · intro i hi
    exact ⟨(hcoef i (by omega)).2.2.2, hmono' i, hκB⟩

/-- info: 'FormalResearch.Special.hahn3j_band_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hahn3j_band_mass

end FormalResearch.Special

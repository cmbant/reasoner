module

public import FormalResearch.Special.DiscreteAiryKappaEdge
public import FormalResearch.Special.DiscreteAiryKappaOrderLow

/-!
# The left mass from the invariant comparison (abstract coefficients)

`rl_comp`: from `ki_invariant`, the pair mass `S_k = Y_k² + Y_{k-1}²` is comparable along a band `k₀ ≤ k ≤ k₁` of rows with margin, with the constant `C_b = 3e^{2E₀}/m₀`.
`rl_left_mass`: for a vanishing-below chain with a backward-recursion edge `[kmin+1, K₀]` and a comparable band `[K₀, k_mid]`, the left mass `Σ_{k < k_c} Y_k²` is `≤ k_c C_g · 2C_b M/(k_mid - k_c)` where `M ≥ Σ_{k_c ≤ k ≤ k_mid} Y_k²`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **Pair comparison along a band.** -/
lemma rl_comp {a c Y ε : ℤ → ℝ} {k0 k1 : ℤ} {m0 B E0 : ℝ} (hm0 : 0 < m0) (hk : k0 ≤ k1)
    (hrow : ∀ k ∈ Finset.Ico k0 k1, jac a c Y k = 0)
    (ha : ∀ k ∈ Finset.Icc k0 k1, 0 < a k ∧ a k ≤ 3 / 4)
    (hmarg : ∀ k ∈ Finset.Icc k0 k1, m0 ≤ 2 * a k - |c k|)
    (hB : ∀ k ∈ Finset.Ico k0 k1, c k ^ 2 + a k ^ 2 ≤ B * a (k + 1) ^ 2)
    (hε : ∀ k ∈ Finset.Ico k0 k1, 2 * (1 + B) * (|a (k + 1) - a k| + |c (k + 1) - c k|) ≤ m0 * ε k)
    (hε0 : ∀ k ∈ Finset.Ico k0 k1, 0 ≤ ε k) (hε1 : ∀ k ∈ Finset.Ico k0 k1, ε k ≤ 1 / 2)
    (hE : ∑ k ∈ Finset.Ico k0 k1, ε k ≤ E0) :
    Y k1 ^ 2 + Y (k1 - 1) ^ 2 ≤ 3 * Real.exp (2 * E0) / m0 * (Y k0 ^ 2 + Y (k0 - 1) ^ 2) ∧
    Y k0 ^ 2 + Y (k0 - 1) ^ 2 ≤ 3 * Real.exp (2 * E0) / m0 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = k1 - k0 := ⟨(k1 - k0).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hidx : ∀ i : ℕ, i ≤ n → k0 + (i : ℤ) ∈ Finset.Icc k0 k1 := fun i hi => by
    rw [Finset.mem_Icc]; omega
  have hidx' : ∀ i : ℕ, i < n → k0 + (i : ℤ) ∈ Finset.Ico k0 k1 := fun i hi => by
    rw [Finset.mem_Ico]; omega
  have hsum : ∑ i ∈ range n, ε (k0 + (i : ℤ)) = ∑ k ∈ Finset.Ico k0 k1, ε k := by
    rw [kk_ico_range ε hk]
    have : (k1 - k0).toNat = n := by omega
    rw [this]
  have inv := ki_invariant (a := a) (c := c) (Y := Y) (ε := ε) (k0 := k0) (m0 := m0) (B := B) hm0 n
    (fun i hi => hrow _ (hidx' i hi)) (fun i hi => (ha _ (hidx i hi)).1) (fun i hi => hmarg _ (hidx i hi.le))
    (fun i hi => by
      have := hB _ (hidx' i hi)
      rwa [show k0 + (i : ℤ) + 1 = k0 + (i : ℤ) + 1 from rfl] at this)
    (fun i hi => hε _ (hidx' i hi)) (fun i hi => hε0 _ (hidx' i hi)) (fun i hi => hε1 _ (hidx' i hi))
  rw [hsum] at inv
  have hk1 : k0 + (n : ℤ) = k1 := by omega
  rw [hk1] at inv
  obtain ⟨i1, i2⟩ := inv
  have hE0 : 0 ≤ ∑ k ∈ Finset.Ico k0 k1, ε k := Finset.sum_nonneg (fun k hk => hε0 k hk)
  have e1 : Real.exp (∑ k ∈ Finset.Ico k0 k1, ε k) ≤ Real.exp (2 * E0) := Real.exp_le_exp.2 (by linarith)
  have e2 : Real.exp (2 * ∑ k ∈ Finset.Ico k0 k1, ε k) ≤ Real.exp (2 * E0) := Real.exp_le_exp.2 (by linarith)
  have e0 : 1 ≤ Real.exp (2 * E0) := Real.one_le_exp (by linarith)
  have f0l := kiF_lower (a := a) (c := c) (Y := Y) (hmarg k0 (Finset.mem_Icc.2 ⟨le_rfl, hk⟩))
  have f1l := kiF_lower (a := a) (c := c) (Y := Y) (hmarg k1 (Finset.mem_Icc.2 ⟨hk, le_rfl⟩))
  have f0u : kiF a c Y k0 ≤ 3 / 2 * (Y k0 ^ 2 + Y (k0 - 1) ^ 2) := by
    have h1 := kiF_upper (a := a) (c := c) (Y := Y) (k := k0) (by
      have := hmarg k0 (Finset.mem_Icc.2 ⟨le_rfl, hk⟩); have := abs_nonneg (c k0); linarith)
    have h2 := (ha k0 (Finset.mem_Icc.2 ⟨le_rfl, hk⟩)).2
    nlinarith [sq_nonneg (Y k0), sq_nonneg (Y (k0 - 1)), mul_le_mul_of_nonneg_right h2 (add_nonneg (sq_nonneg (Y k0)) (sq_nonneg (Y (k0 - 1))))]
  have f1u : kiF a c Y k1 ≤ 3 / 2 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
    have h1 := kiF_upper (a := a) (c := c) (Y := Y) (k := k1) (by
      have := hmarg k1 (Finset.mem_Icc.2 ⟨hk, le_rfl⟩); have := abs_nonneg (c k1); linarith)
    have h2 := (ha k1 (Finset.mem_Icc.2 ⟨hk, le_rfl⟩)).2
    nlinarith [sq_nonneg (Y k1), sq_nonneg (Y (k1 - 1)), mul_le_mul_of_nonneg_right h2 (add_nonneg (sq_nonneg (Y k1)) (sq_nonneg (Y (k1 - 1))))]
  have S0 : 0 ≤ Y k0 ^ 2 + Y (k0 - 1) ^ 2 := by positivity
  have S1 : 0 ≤ Y k1 ^ 2 + Y (k1 - 1) ^ 2 := by positivity
  have F0 : 0 ≤ kiF a c Y k0 := by nlinarith
  have F1 : 0 ≤ kiF a c Y k1 := by nlinarith
  constructor
  · -- S₁ ≤ (2/m₀) F₁ ≤ (2/m₀) e^E F₀ ≤ (3 e^E/m₀) S₀
    have h1 : m0 / 2 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) ≤ Real.exp (2 * E0) * (3 / 2 * (Y k0 ^ 2 + Y (k0 - 1) ^ 2)) := by
      calc _ ≤ kiF a c Y k1 := f1l
        _ ≤ Real.exp (∑ k ∈ Finset.Ico k0 k1, ε k) * kiF a c Y k0 := i1
        _ ≤ Real.exp (2 * E0) * kiF a c Y k0 := mul_le_mul_of_nonneg_right e1 F0
        _ ≤ _ := mul_le_mul_of_nonneg_left f0u (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    nlinarith [h1]
  · have h1 : m0 / 2 * (Y k0 ^ 2 + Y (k0 - 1) ^ 2) ≤ Real.exp (2 * E0) * (3 / 2 * (Y k1 ^ 2 + Y (k1 - 1) ^ 2)) := by
      calc _ ≤ kiF a c Y k0 := f0l
        _ ≤ Real.exp (2 * ∑ k ∈ Finset.Ico k0 k1, ε k) * kiF a c Y k1 := i2
        _ ≤ Real.exp (2 * E0) * kiF a c Y k1 := mul_le_mul_of_nonneg_right e2 F1
        _ ≤ _ := mul_le_mul_of_nonneg_left f1u (by positivity)
    rw [div_mul_eq_mul_div, le_div_iff₀ hm0]
    nlinarith [h1]

/-- **The left mass.** -/
lemma rl_left_mass {a c Y : ℤ → ℝ} {kmin K0 kc kmid : ℤ} {D Cb M : ℝ} (hD : 0 ≤ D) (hCb : 1 ≤ Cb) (hK00 : 0 ≤ K0)
    (hkmin0 : 0 ≤ kmin) (hkmin : kmin + 1 ≤ K0) (hK0kc : K0 ≤ kc) (hkc : kc < kmid)
    (hsupp : ∀ k : ℤ, k < kmin → Y k = 0)
    (hback : ∀ j ∈ Finset.Icc (kmin + 1) (K0 - 1), jac a c Y j = 0 ∧ 0 < a j ∧ c j ^ 2 + a (j + 1) ^ 2 ≤ D * a j ^ 2)
    (hcomp : ∀ i j : ℤ, K0 ≤ i → i ≤ j → j ≤ kmid → Y j ^ 2 + Y (j - 1) ^ 2 ≤ Cb * (Y i ^ 2 + Y (i - 1) ^ 2) ∧
      Y i ^ 2 + Y (i - 1) ^ 2 ≤ Cb * (Y j ^ 2 + Y (j - 1) ^ 2))
    (hM : ∑ k ∈ Finset.Ico kc (kmid + 1), Y k ^ 2 ≤ M) :
    ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤
      (kc : ℝ) * ((1 + D) ^ K0.toNat * Cb) * (2 * Cb * M / ((kmid - kc : ℤ) : ℝ)) := by
  set S : ℤ → ℝ := fun j => Y j ^ 2 + Y (j - 1) ^ 2 with hS
  have hS0 : ∀ j, 0 ≤ S j := fun j => by simp only [hS]; positivity
  have hkc0 : 0 ≤ kc := le_trans hK00 hK0kc
  have hcnt : (0 : ℝ) < ((kmid - kc : ℤ) : ℝ) := by
    have : (0 : ℤ) < kmid - kc := by omega
    exact_mod_cast this
  -- step 1
  have hS1 : S kc * ((kmid - kc : ℤ) : ℝ) ≤ 2 * Cb * M := by
    have h1 : ∀ j ∈ Finset.Ico (kc + 1) (kmid + 1), S kc / Cb ≤ S j := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      have := (hcomp kc j hK0kc (by omega) (by omega)).2
      rw [div_le_iff₀ (by linarith)]
      simp only [hS]
      linarith
    have h2 := Finset.card_nsmul_le_sum (Finset.Ico (kc + 1) (kmid + 1)) S (S kc / Cb) h1
    rw [Int.card_Ico, nsmul_eq_mul] at h2
    have hcast : (((kmid + 1 - (kc + 1)).toNat : ℕ) : ℝ) = ((kmid - kc : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      push_cast; ring
    rw [hcast] at h2
    -- the sum of pairs is at most `2M`
    have h3 : ∑ j ∈ Finset.Ico (kc + 1) (kmid + 1), S j ≤ 2 * M := by
      simp only [hS]
      rw [Finset.sum_add_distrib]
      have a1 : ∑ j ∈ Finset.Ico (kc + 1) (kmid + 1), Y j ^ 2 ≤ M := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => sq_nonneg _)) hM
        intro j hj; rw [Finset.mem_Ico] at hj ⊢; omega
      have a2 : ∑ j ∈ Finset.Ico (kc + 1) (kmid + 1), Y (j - 1) ^ 2 ≤ M := by
        have : ∑ j ∈ Finset.Ico (kc + 1) (kmid + 1), Y (j - 1) ^ 2 = ∑ j ∈ Finset.Ico kc kmid, Y j ^ 2 := by
          refine Finset.sum_bij (fun j _ => j - 1) ?_ ?_ ?_ ?_
          · intro j hj; rw [Finset.mem_Ico] at hj ⊢; omega
          · intro j1 _ j2 _ h; omega
          · intro j hj; exact ⟨j + 1, by rw [Finset.mem_Ico] at hj ⊢; omega, by omega⟩
          · intro j _; rfl
        rw [this]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => sq_nonneg _)) hM
        intro j hj; rw [Finset.mem_Ico] at hj ⊢; omega
      linarith
    have h4 : ((kmid - kc : ℤ) : ℝ) * (S kc / Cb) ≤ 2 * M := by linarith
    have h5 : S kc * ((kmid - kc : ℤ) : ℝ) ≤ Cb * (2 * M) := by
      have := mul_le_mul_of_nonneg_left h4 (by linarith : 0 ≤ Cb)
      have e : Cb * (((kmid - kc : ℤ) : ℝ) * (S kc / Cb)) = S kc * ((kmid - kc : ℤ) : ℝ) := by field_simp
      linarith
    linarith
  -- step 2
  have hpair : ∀ k' : ℤ, kmin + 1 ≤ k' → k' ≤ kc → S k' ≤ (1 + D) ^ K0.toNat * Cb * S kc := by
    intro k' h1 h2
    have hpow : 1 ≤ (1 + D) ^ K0.toNat := one_le_pow₀ (by linarith)
    by_cases hc : K0 ≤ k'
    · have := (hcomp k' kc hc h2 (by omega)).2
      have h3 : Cb * S kc ≤ (1 + D) ^ K0.toNat * Cb * S kc := by
        have := hS0 kc
        nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (by linarith : (0 : ℝ) ≤ Cb) this)]
      have h4 : S k' ≤ Cb * S kc := this
      linarith
    · push Not at hc
      obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = K0 - k' := ⟨(K0 - k').toNat, Int.toNat_of_nonneg (by omega)⟩
      have hdown := ke_down (a := a) (c := c) (Y := Y) hD hback n (by omega)
      have hk' : K0 - (n : ℤ) = k' := by omega
      rw [hk'] at hdown
      have hnK : n ≤ K0.toNat := by omega
      have h5 : (1 + D) ^ n ≤ (1 + D) ^ K0.toNat := pow_le_pow_right₀ (by linarith) hnK
      have hK0c := (hcomp K0 kc le_rfl hK0kc (by omega)).2
      have : S k' ≤ (1 + D) ^ n * S K0 := by simpa [hS] using hdown
      calc S k' ≤ (1 + D) ^ n * S K0 := this
        _ ≤ (1 + D) ^ K0.toNat * S K0 := mul_le_mul_of_nonneg_right h5 (hS0 _)
        _ ≤ (1 + D) ^ K0.toNat * (Cb * S kc) := mul_le_mul_of_nonneg_left (by simpa [hS] using hK0c) (by linarith)
        _ = _ := by ring
  have hY : ∀ k : ℤ, k ≤ kc → Y k ^ 2 ≤ (1 + D) ^ K0.toNat * Cb * S kc := by
    intro k hk
    have hpow : 1 ≤ (1 + D) ^ K0.toNat := one_le_pow₀ (by linarith)
    have hq : 1 ≤ (1 + D) ^ K0.toNat * Cb := by nlinarith
    by_cases hlt : k < kmin
    · rw [hsupp k hlt]
      have := mul_nonneg (by linarith : (0 : ℝ) ≤ (1 + D) ^ K0.toNat * Cb) (hS0 kc)
      simpa using this
    · push Not at hlt
      by_cases hkk : k = kc
      · subst hkk
        have : Y k ^ 2 ≤ S k := by simp only [hS]; nlinarith [sq_nonneg (Y (k - 1))]
        have h2 := mul_le_mul_of_nonneg_right hq (hS0 k)
        linarith
      · have := hpair (k + 1) (by omega) (by omega)
        have e : S (k + 1) = Y (k + 1) ^ 2 + Y k ^ 2 := by simp [hS]
        rw [e] at this
        nlinarith [sq_nonneg (Y (k + 1))]
  -- step 3
  have h3 : ∑ k ∈ Finset.Ico 0 kc, Y k ^ 2 ≤ (kc : ℝ) * ((1 + D) ^ K0.toNat * Cb * S kc) := by
    have := Finset.card_nsmul_le_sum (Finset.Ico 0 kc) (fun k => Y k ^ 2) (0 : ℝ) (fun _ _ => sq_nonneg _)
    have h4 := Finset.sum_le_card_nsmul (Finset.Ico 0 kc) (fun k => Y k ^ 2) ((1 + D) ^ K0.toNat * Cb * S kc)
      (fun k hk => hY k (by rw [Finset.mem_Ico] at hk; omega))
    rw [Int.card_Ico, nsmul_eq_mul] at h4
    have hcast : (((kc - 0).toNat : ℕ) : ℝ) = (kc : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]; simp
    rw [hcast] at h4
    exact h4
  refine h3.trans ?_
  have hq0 : 0 ≤ (1 + D) ^ K0.toNat * Cb := by
    have h0 : 0 ≤ (1 + D) ^ K0.toNat := by positivity
    nlinarith
  have hkcR : 0 ≤ (kc : ℝ) := by exact_mod_cast hkc0
  have h6 : S kc ≤ 2 * Cb * M / ((kmid - kc : ℤ) : ℝ) := by
    rw [le_div_iff₀ hcnt]; exact hS1
  calc (kc : ℝ) * ((1 + D) ^ K0.toNat * Cb * S kc) = (kc : ℝ) * ((1 + D) ^ K0.toNat * Cb) * S kc := by ring
    _ ≤ (kc : ℝ) * ((1 + D) ^ K0.toNat * Cb) * (2 * Cb * M / ((kmid - kc : ℤ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h6 (mul_nonneg hkcR hq0)

end FormalResearch.Special

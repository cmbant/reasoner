module

public import FormalResearch.Special.RacahKappaLeftBand
public import FormalResearch.Special.RacahKappaLeftMass
public import FormalResearch.Special.DiscreteAiryKappaLeftBand
public import FormalResearch.Special.DiscreteAiryLimitChains2HalfAiry

/-!
# The band comparison for the half-integer Racah chain

`rl_bandH`: twin of `rl_band` (`RacahKappaLeftBand`) for the shifted closed forms `hrAkH`, `hrCkH` (rank `t = k + ½`, `hrAkH P Q a b h k = hrAt P Q a b h (k + ½)`), from the real-rank constants `rl_coef_allT`.  The band is `(k₁ + 4) h ≤ q_*/2`.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma rkAkH_eq (P Q a b h : ℝ) (k : ℤ) : hrAkH P Q a b h k = hrAt P Q a b h ((k : ℝ) + 1 / 2) := rfl

lemma rkCkH_eq (P Q τ x a b h : ℝ) (k : ℤ) : hrCkH P Q τ x a b h k = hrCt P Q τ x a b h ((k : ℝ) + 1 / 2) := rfl

lemma rkAkH_succ (P Q a b h : ℝ) (k : ℤ) : hrAkH P Q a b h (k + 1) = hrAt P Q a b h (((k : ℝ) + 1 / 2) + 1) := by
  unfold hrAkH hrAt; push_cast; ring_nf

lemma rkCkH_succ (P Q τ x a b h : ℝ) (k : ℤ) : hrCkH P Q τ x a b h (k + 1) = hrCt P Q τ x a b h (((k : ℝ) + 1 / 2) + 1) := by
  unfold hrCkH hrCt; push_cast; ring_nf

/-- **The band comparison** for the half-integer Racah coefficients. -/
theorem rl_bandH {P Q a b τ x qs : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hs : 1 - x ^ 2 = rkS P Q x * qs ^ 2)
    (hspos : 0 < rkS P Q x) (hqs : 0 < qs) (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) :
    ∃ (K0 : ℕ) (h0 Cb : ℝ), 2 ≤ K0 ∧ 0 < h0 ∧ h0 ≤ 1 ∧ 1 ≤ Cb ∧ |a| ≤ K0 ∧ |b| ≤ K0 ∧
      ∀ (h : ℝ) (Y : ℤ → ℝ), 0 < h → h ≤ h0 → ∀ k0 k1 : ℤ, (K0 : ℤ) ≤ k0 → k0 ≤ k1 → ((k1 : ℝ) + 4) * h ≤ qs / 2 →
        (∀ k ∈ Finset.Ico k0 k1, jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0) →
        Y k1 ^ 2 + Y (k1 - 1) ^ 2 ≤ Cb * (Y k0 ^ 2 + Y (k0 - 1) ^ 2) ∧
        Y k0 ^ 2 + Y (k0 - 1) ^ 2 ≤ Cb * (Y k1 ^ 2 + Y (k1 - 1) ^ 2) := by
  obtain ⟨K0, h0, m0, B, Λ0, hK02, hh0, hh01, hm0, hB, hΛ0, hKa, hKb, key⟩ :=
    rl_coef_allT (a := a) (b := b) (τ := τ) hP hQ hτ hs hspos hqs hα hβ
  set Ê : ℝ := 2 * (1 + B) * Λ0 / m0 with hÊ
  have hÊ0 : 0 ≤ Ê := by positivity
  set E0 : ℝ := Ê * (1 + qs / 2) with hE0
  refine ⟨K0, h0, max 1 (3 * Real.exp (2 * E0) / m0), by exact_mod_cast hK02, hh0, hh01, le_max_left _ _, hKa, hKb, ?_⟩
  intro h Y hh hhh0 k0 k1 hk0 hk01 hq hrow
  have hk0R : (2 : ℝ) ≤ (k0 : ℝ) + 1 / 2 := by
    have h2 : (2 : ℝ) ≤ (K0 : ℝ) := by exact_mod_cast hK02
    have : (K0 : ℝ) ≤ (k0 : ℝ) := by exact_mod_cast hk0
    linarith
  have hk1R : (k0 : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk01
  have hat : ∀ k ∈ Finset.Icc k0 k1, (K0 : ℝ) ≤ (k : ℝ) + 1 / 2 ∧ (((k : ℝ) + 1 / 2) + 3) * h ≤ qs / 2 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have h1 : (K0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (K0 : ℤ) ≤ k)
    have h2 : (k : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast hk.2
    exact ⟨by linarith, by nlinarith only [h2, hq, hh]⟩
  have hatI : ∀ k ∈ Finset.Ico k0 k1, (K0 : ℝ) ≤ (k : ℝ) + 1 / 2 ∧ (((k : ℝ) + 1 / 2) + 3) * h ≤ qs / 2 := fun k hk =>
    hat k (Finset.Ico_subset_Icc_self hk)
  have hcomp := rl_comp (a := hrAkH P Q a b h) (c := hrCkH P Q τ x a b h) (Y := Y)
    (ε := fun k => Ê * (1 / ((k : ℝ) + 1 / 2) ^ 2 + h)) (k0 := k0) (k1 := k1) (m0 := m0) (B := B) (E0 := E0) hm0 hk01 hrow
    (fun k hk => by
      obtain ⟨a1, a2, a3⟩ := (key h hh hhh0 _ (hat k hk).1 (hat k hk).2).1
      rw [rkAkH_eq]; exact ⟨a1, a2⟩)
    (fun k hk => by
      have := (key h hh hhh0 _ (hat k hk).1 (hat k hk).2).1.2.2
      rw [rkAkH_eq, rkCkH_eq]; exact this)
    (fun k hk => by
      have := (key h hh hhh0 _ (hatI k hk).1 (hatI k hk).2).2.2.1
      have e : (((k + 1 : ℤ) : ℝ) + 1 / 2) = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
      simp only [rkAkH_eq, rkCkH_eq, e]; exact this)
    (fun k hk => by
      have := (key h hh hhh0 _ (hatI k hk).1 (hatI k hk).2).2.2.2.1
      have e : (((k + 1 : ℤ) : ℝ) + 1 / 2) = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
      simp only [rkAkH_eq, rkCkH_eq, e]; exact this)
    (fun k hk => by
      have : 0 ≤ 1 / ((k : ℝ) + 1 / 2) ^ 2 + h := by positivity
      positivity)
    (fun k hk => (key h hh hhh0 _ (hatI k hk).1 (hatI k hk).2).2.2.2.2)
    (by
      rw [kk_ico_range _ hk01]
      have e1 : ∀ i ∈ range (k1 - k0).toNat, Ê * (1 / ((((k0 + (i : ℤ) : ℤ) : ℝ) + 1 / 2)) ^ 2 + h) =
          Ê * (1 / ((k0 : ℝ) + 1 / 2 + (i : ℝ)) ^ 2) + Ê * h := by
        intro i _; push_cast; ring
      rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, ← Finset.mul_sum]
      have h1 := kl_sum_inv_sq_le_one hk0R (k1 - k0).toNat
      have h2 : ∑ i ∈ range (k1 - k0).toNat, Ê * h = ((k1 - k0).toNat : ℝ) * (Ê * h) := by simp
      rw [h2]
      have hn : ((k1 - k0).toNat : ℝ) ≤ (k1 : ℝ) := by
        have : ((k1 - k0).toNat : ℤ) ≤ k1 := by omega
        have h' : (((k1 - k0).toNat : ℤ) : ℝ) ≤ (k1 : ℝ) := by exact_mod_cast this
        exact_mod_cast h'
      have hnh : ((k1 - k0).toNat : ℝ) * h ≤ qs / 2 := by nlinarith only [hn, hq, hh]
      have h3 : ((k1 - k0).toNat : ℝ) * (Ê * h) ≤ Ê * (qs / 2) := by
        have : ((k1 - k0).toNat : ℝ) * (Ê * h) = Ê * (((k1 - k0).toNat : ℝ) * h) := by ring
        rw [this]; exact mul_le_mul_of_nonneg_left hnh hÊ0
      have h4 := mul_le_mul_of_nonneg_left h1 hÊ0
      rw [hE0]
      nlinarith only [h3, h4])
  refine ⟨hcomp.1.trans ?_, hcomp.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end FormalResearch.Special

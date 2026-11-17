module

public import FormalResearch.Special.RacahKappaLeftBand
public import FormalResearch.Special.DiscreteAiryKappaEdge

/-!
# Edge facts of the closed-form Racah chain below the oscillatory band

For `kmin < j < K₀` (`|a|, |b| ≤ kmin`, `K₀ h ≤ q_*/2`): `a_j > 0` and `c_j² + a_{j+1}² ≤ D a_j²`, with `D` depending on the data and `K₀` only.
This feeds the backward recursion `ke_down` below the band.

**Claim class: proved.**
-/

@[expose] public section

open Finset FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The edge constant. -/
lemma rl_edge {P Q a b τ x qs : ℝ} {kmin K0 : ℤ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hτ : τ ^ 2 = 1) (hqs : 0 < qs)
    (hα : 0 < 1 - P * qs ^ 2) (hβ : 0 < 1 - Q * qs ^ 2) (hka : |a| ≤ kmin) (hkb : |b| ≤ kmin) (hkmin0 : 0 ≤ kmin)
    (hK : kmin + 1 ≤ K0) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → (K0 : ℝ) * h ≤ qs / 2 → ∀ j : ℤ, kmin + 1 ≤ j → j ≤ K0 - 1 →
      0 < hrAk P Q a b h j ∧
        hrCk P Q τ x a b h j ^ 2 + hrAk P Q a b h (j + 1) ^ 2 ≤ D * hrAk P Q a b h j ^ 2 := by
  set β0 : ℝ := Real.sqrt (P * Q) with hβ0
  have hβ00 : 0 ≤ β0 := Real.sqrt_nonneg _
  set e0 : ℝ := Real.sqrt ((1 - P * qs ^ 2) * (1 - Q * qs ^ 2)) with he0
  have he0p : 0 < e0 := Real.sqrt_pos.2 (mul_pos hα hβ)
  set G : ℝ := |x| + β0 * (qs ^ 2 + 1 + a ^ 2 + b ^ 2) + |a * b| with hG
  have hG0 : 0 ≤ G := by positivity
  have hK0R : (1 : ℝ) ≤ (K0 : ℝ) := by
    have : (1 : ℤ) ≤ K0 := by omega
    exact_mod_cast this
  refine ⟨(G ^ 2 + 1) / (e0 / (2 * K0)) ^ 2, by positivity, ?_⟩
  intro h hh hh1 hK0h j hj1 hj2
  have hjR : (kmin : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hj1
  have hj1R : (1 : ℝ) ≤ (j : ℝ) := by
    have : (0 : ℝ) ≤ kmin := by exact_mod_cast hkmin0
    linarith
  have hjK : (j : ℝ) + 1 ≤ (K0 : ℝ) := by
    have : j + 1 ≤ K0 := by omega
    exact_mod_cast this
  have hkaR : |a| + 1 ≤ (j : ℝ) := by
    have : |a| ≤ (kmin : ℝ) := by exact_mod_cast hka
    linarith
  have hkbR : |b| + 1 ≤ (j : ℝ) := by
    have : |b| ≤ (kmin : ℝ) := by exact_mod_cast hkb
    linarith
  have hjh : ((j : ℝ) + 1) * h ≤ qs / 2 := by nlinarith only [hjK, hK0h, hh]
  have hjpos : 0 < (j : ℝ) := by linarith
  -- the factor ẽ at j
  have hσ : ((j : ℝ) * h) ^ 2 ≤ qs ^ 2 := by
    have h1 : (j : ℝ) * h ≤ qs := by nlinarith only [hjh, hh, hqs]
    have h2 : 0 ≤ (j : ℝ) * h := by positivity
    nlinarith only [h1, h2]
  have hσ0 : 0 ≤ ((j : ℝ) * h) ^ 2 := by positivity
  have hP1 : 0 ≤ 1 - P * ((j : ℝ) * h) ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hσ hP, hα]
  have hQ1 : 0 ≤ 1 - Q * ((j : ℝ) * h) ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_left hσ hQ, hβ]
  have hee : e0 ≤ etilde P Q (((j : ℝ) * h) ^ 2) := by
    unfold etilde
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (by nlinarith only [mul_le_mul_of_nonneg_left hσ hP]) (by nlinarith only [mul_le_mul_of_nonneg_left hσ hQ])
      hβ.le hP1
  have hrr : 1 / (j : ℝ) ≤ rr a b (j : ℝ) := ke_rr_lower hj1R hkaR hkbR
  have hAj : e0 / (2 * K0) ≤ hrAk P Q a b h j := by
    unfold hrAk
    have h1 : 1 / (j : ℝ) * e0 ≤ rr a b (j : ℝ) * etilde P Q (((j : ℝ) * h) ^ 2) :=
      mul_le_mul hrr hee he0p.le (Real.sqrt_nonneg _)
    have h2 : e0 / (2 * K0) ≤ 1 / 2 * (1 / (j : ℝ) * e0) := by
      rw [show 1 / 2 * (1 / (j : ℝ) * e0) = e0 / (2 * j) by field_simp]
      apply div_le_div_of_nonneg_left he0p.le (by positivity) (by linarith)
    nlinarith only [h1, h2]
  have hApos : 0 < e0 / (2 * K0) := by positivity
  refine ⟨hApos.trans_le hAj, ?_⟩
  -- upper bound of A_{j+1}
  have hA1 : hrAk P Q a b h (j + 1) ≤ 1 := by
    have hj1' : (1 : ℝ) ≤ ((j + 1 : ℤ) : ℝ) := by push_cast; linarith
    have hr2 := ke_rr_sq_le (M := a) (σ := b) hj1' (by push_cast; linarith) (by push_cast; linarith)
    have hr0 : 0 ≤ rr a b ((j + 1 : ℤ) : ℝ) := Real.sqrt_nonneg _
    have hr : rr a b ((j + 1 : ℤ) : ℝ) ≤ 2 := by nlinarith only [hr2, hr0]
    have hσ1 : ((((j + 1 : ℤ) : ℝ)) * h) ^ 2 ≤ qs ^ 2 := by
      push_cast
      have h1 : ((j : ℝ) + 1) * h ≤ qs := by nlinarith only [hjh, hqs]
      have h2 : 0 ≤ ((j : ℝ) + 1) * h := by positivity
      nlinarith only [h1, h2]
    have hσ10 : 0 ≤ ((((j + 1 : ℤ) : ℝ)) * h) ^ 2 := by positivity
    have he1 := rl_e_le_one (P := P) (Q := Q) hP hQ hσ10
      (by nlinarith only [mul_le_mul_of_nonneg_left hσ1 hP, hα]) (by nlinarith only [mul_le_mul_of_nonneg_left hσ1 hQ, hβ])
    have he0' : 0 ≤ etilde P Q ((((j + 1 : ℤ) : ℝ) * h) ^ 2) := Real.sqrt_nonneg _
    unfold hrAk
    nlinarith only [hr, he1, he0', hr0]
  -- bound of c_j
  have hC : |hrCk P Q τ x a b h j| ≤ G := by
    unfold hrCk hrB
    have hτ1 : |τ| = 1 := by
      have : |τ| ^ 2 = 1 := by rw [sq_abs]; exact hτ
      nlinarith only [this, abs_nonneg τ]
    rw [abs_mul, hτ1, one_mul]
    refine (abs_sub _ _).trans ?_
    rw [← hβ0]
    have e1 : (((j : ℝ) + 1 / 2) * h) ^ 2 + h ^ 2 / 4 ≤ qs ^ 2 + 1 := by
      have : ((j : ℝ) + 1 / 2) * h ≤ qs := by nlinarith only [hjh, hh, hqs]
      have h0 : 0 ≤ ((j : ℝ) + 1 / 2) * h := by positivity
      nlinarith only [this, h0, hh, hh1]
    have e2 : 0 ≤ (((j : ℝ) + 1 / 2) * h) ^ 2 + h ^ 2 / 4 := by positivity
    have e3 : |β0 * ((((j : ℝ) + 1 / 2) * h) ^ 2 + h ^ 2 / 4) - β0 * h ^ 2 * (a ^ 2 + b ^ 2) / 2 +
        a * b / ((j : ℝ) * ((j : ℝ) + 1))| ≤ β0 * (qs ^ 2 + 1 + a ^ 2 + b ^ 2) + |a * b| := by
      have t1 : 0 ≤ β0 * ((((j : ℝ) + 1 / 2) * h) ^ 2 + h ^ 2 / 4) := by positivity
      have t1' : β0 * ((((j : ℝ) + 1 / 2) * h) ^ 2 + h ^ 2 / 4) ≤ β0 * (qs ^ 2 + 1) :=
        mul_le_mul_of_nonneg_left e1 hβ00
      have t2 : 0 ≤ β0 * h ^ 2 * (a ^ 2 + b ^ 2) / 2 := by positivity
      have t2' : β0 * h ^ 2 * (a ^ 2 + b ^ 2) / 2 ≤ β0 * (a ^ 2 + b ^ 2) := by
        have : h ^ 2 ≤ 1 := by nlinarith only [hh, hh1]
        have h3 : 0 ≤ β0 * (a ^ 2 + b ^ 2) := by positivity
        have h4 := mul_le_mul_of_nonneg_left this h3
        have h5 : β0 * h ^ 2 * (a ^ 2 + b ^ 2) / 2 = β0 * (a ^ 2 + b ^ 2) * h ^ 2 / 2 := by ring
        rw [h5]; linarith only [h4, h3]
      have t3 : |a * b / ((j : ℝ) * ((j : ℝ) + 1))| ≤ |a * b| := by
        rw [abs_div, abs_of_pos (by positivity : 0 < (j : ℝ) * ((j : ℝ) + 1))]
        apply div_le_self (abs_nonneg _)
        nlinarith only [hj1R]
      have t3' := abs_le.1 t3
      rw [abs_le]
      constructor <;> nlinarith only [t1, t1', t2, t2', t3'.1, t3'.2]
    linarith only [e3]
  have hAj2 : (e0 / (2 * K0)) ^ 2 ≤ hrAk P Q a b h j ^ 2 := by
    nlinarith only [hAj, hApos]
  have hc2 : hrCk P Q τ x a b h j ^ 2 ≤ G ^ 2 := by
    have := sq_abs (hrCk P Q τ x a b h j)
    nlinarith only [this, hC, abs_nonneg (hrCk P Q τ x a b h j)]
  have ha2 : hrAk P Q a b h (j + 1) ^ 2 ≤ 1 := by
    have : 0 ≤ hrAk P Q a b h (j + 1) := by
      unfold hrAk
      have := Real.sqrt_nonneg ((1 - a ^ 2 / ((j + 1 : ℤ) : ℝ) ^ 2) * (1 - b ^ 2 / ((j + 1 : ℤ) : ℝ) ^ 2) / (1 - 1 / (4 * ((j + 1 : ℤ) : ℝ) ^ 2)))
      have h2 : 0 ≤ etilde P Q ((((j + 1 : ℤ) : ℝ) * h) ^ 2) := Real.sqrt_nonneg _
      unfold rr
      positivity
    nlinarith only [hA1, this]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  have hT : hrCk P Q τ x a b h j ^ 2 + hrAk P Q a b h (j + 1) ^ 2 ≤ G ^ 2 + 1 := by linarith only [hc2, ha2]
  calc (hrCk P Q τ x a b h j ^ 2 + hrAk P Q a b h (j + 1) ^ 2) * (e0 / (2 * K0)) ^ 2
      ≤ (G ^ 2 + 1) * (e0 / (2 * K0)) ^ 2 := mul_le_mul_of_nonneg_right hT (by positivity)
    _ ≤ (G ^ 2 + 1) * hrAk P Q a b h j ^ 2 := mul_le_mul_of_nonneg_left hAj2 (by positivity)

end FormalResearch.Special

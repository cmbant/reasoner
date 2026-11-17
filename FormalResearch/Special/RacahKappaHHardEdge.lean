module

public import FormalResearch.Special.DiscreteAiryLimitHyperDecay
public import FormalResearch.Special.DiscreteAiryLimitChains2HalfAiry

/-!
# Hard-edge monotone decay beyond the turn for the half-integer Racah chain

Twin of `hr_Ak_pos`, `hr_hardedge_decay` (`DiscreteAiryLimitHyperDecay`) for the shifted closed forms `hrAkH`, `hrCkH` (rank `t = k + ½`, lattice `q_k = (k+1)h`, hard edge `ẽ(((k_max + 3/2) h)²) = 0`).  It applies
`exact_hyperbolicity_hahn_racah` at the real rank `t = i + ½`.

**Claim class: proved.**
-/

@[expose] public section

open FormalResearch.Racah.P3 FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- Positivity of the off-diagonal coefficients of the half-integer chain below the hard edge. -/
lemma hr_AkH_pos {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) {a b h : ℝ} (hh : 0 < h) {i kmax : ℕ} (hik : i ≤ kmax)
    (hi : 1 ≤ (i : ℝ) + 1 / 2) (ha : a ^ 2 < ((i : ℝ) + 1 / 2) ^ 2) (hb : b ^ 2 < ((i : ℝ) + 1 / 2) ^ 2)
    (hedge : ((((kmax : ℝ) + 1) + 1 / 2) * h) ^ 2 ∈ Dom P Q) : 0 < hrAkH P Q a b h (i : ℤ) := by
  unfold hrAkH
  simp only [Int.cast_natCast]
  have hi2 : 0 < ((i : ℝ) + 1 / 2) ^ 2 := by positivity
  have hrr : 0 < rr a b ((i : ℝ) + 1 / 2) := by
    unfold rr
    refine Real.sqrt_pos.2 (div_pos (mul_pos ?_ ?_) ?_)
    · exact sub_pos.2 ((div_lt_one hi2).2 ha)
    · exact sub_pos.2 ((div_lt_one hi2).2 hb)
    · exact sub_pos.2 ((div_lt_one (by positivity)).2 (by nlinarith))
  have hik' : (i : ℝ) ≤ kmax := Nat.cast_le.2 hik
  have hlt : (((i : ℝ) + 1 / 2) * h) ^ 2 < ((((kmax : ℝ) + 1) + 1 / 2) * h) ^ 2 :=
    pow_lt_pow_left₀ (mul_lt_mul_of_pos_right (by linarith) hh) (by positivity) two_ne_zero
  have hP1 : 0 < 1 - P * (((i : ℝ) + 1 / 2) * h) ^ 2 := by
    rcases hP.eq_or_lt with h0 | h0
    · simp [← h0]
    · have := mul_lt_mul_of_pos_left hlt h0
      nlinarith [hedge.2.1]
  have hQ1 : 0 < 1 - Q * (((i : ℝ) + 1 / 2) * h) ^ 2 := by
    rcases hQ.eq_or_lt with h0 | h0
    · simp [← h0]
    · have := mul_lt_mul_of_pos_left hlt h0
      nlinarith [hedge.2.2]
  have het : 0 < etilde P Q ((((i : ℝ) + 1 / 2) * h) ^ 2) := by
    unfold etilde
    exact Real.sqrt_pos.2 (mul_pos hP1 hQ1)
  exact mul_pos (mul_pos (by norm_num) hrr) het

/-- **Hard-edge monotone decay beyond the turn for the half-integer chain** (see the module docstring). -/
theorem hr_hardedge_decayH {P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q) (a b τ x qs h : ℝ) (hqs : 0 < qs)
    (hh : 0 < h) (hτ : τ ^ 2 = 1) (hκ : 0 < 1 - τ * x) (hturn : Phi P Q τ x (qs ^ 2) = 0)
    (hhM : h * (2 * hrM a b) ≤ qs)
    (hhC : h * hrRho P Q a b qs ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs)
    (kmax k1 : ℕ) (hedge : ((((kmax : ℝ) + 1) + 1 / 2) * h) ^ 2 ∈ Dom P Q)
    (hedge0 : etilde P Q (((((kmax : ℝ) + 1) + 1 / 2) * h) ^ 2) = 0)
    (hk1 : qs ≤ ((k1 : ℝ) + 1) * h) (hk1k : k1 ≤ kmax) (Y : ℤ → ℝ)
    (hY : ∀ k ∈ Finset.Icc ((k1 : ℤ) + 1) (kmax : ℤ),
      jac (hrAkH P Q a b h) (hrCkH P Q τ x a b h) Y k = 0) :
    ∀ k : ℤ, (k1 : ℤ) ≤ k → k ≤ kmax → |Y k| ≤ |Y k1| := by
  rcases hk1k.eq_or_lt with hEq | hlt
  · intro k hk1' hk2
    have : k = k1 := by omega
    rw [this]
  have hM1 : 1 ≤ hrM a b := le_max_left _ _
  have hMa : |a| ≤ hrM a b := (le_max_left _ _).trans (le_max_right _ _)
  have hMb : |b| ≤ hrM a b := (le_max_right _ _).trans (le_max_right _ _)
  have hfacts : ∀ i : ℕ, k1 + 1 ≤ i → 1 ≤ (i : ℝ) + 1 / 2 ∧ a ^ 2 < ((i : ℝ) + 1 / 2) ^ 2 ∧ b ^ 2 < ((i : ℝ) + 1 / 2) ^ 2 ∧
      qs + h ≤ ((i : ℝ) + 1) * h := by
    intro i hi
    have hik : ((k1 : ℝ) + 1) ≤ (i : ℝ) := by exact_mod_cast hi
    have hqh : qs + h ≤ ((i : ℝ) + 1) * h := by
      nlinarith [mul_le_mul_of_nonneg_right hik hh.le]
    have h2M : 2 * hrM a b ≤ (i : ℝ) + 1 / 2 := by
      have : 2 * hrM a b * h ≤ ((i : ℝ) + 1 / 2) * h := by nlinarith
      exact le_of_mul_le_mul_right this hh
    have hiM : hrM a b < (i : ℝ) + 1 / 2 := by linarith
    refine ⟨by linarith, ?_, ?_, hqh⟩
    · have : |a| < (i : ℝ) + 1 / 2 := lt_of_le_of_lt hMa hiM
      have := pow_lt_pow_left₀ this (abs_nonneg a) two_ne_zero
      rwa [sq_abs] at this
    · have : |b| < (i : ℝ) + 1 / 2 := lt_of_le_of_lt hMb hiM
      have := pow_lt_pow_left₀ this (abs_nonneg b) two_ne_zero
      rwa [sq_abs] at this
  have hA : ∀ i, k1 + 1 ≤ i → i ≤ kmax → 0 < (fun n : ℕ => hrAkH P Q a b h (n : ℤ)) i := by
    intro i hi1 hi2
    obtain ⟨f1, f2, f3, -⟩ := hfacts i hi1
    exact hr_AkH_pos hP hQ hh hi2 f1 f2 f3 hedge
  have hend : (fun n : ℕ => hrAkH P Q a b h (n : ℤ)) (kmax + 1) = 0 := by
    show hrAkH P Q a b h (((kmax + 1 : ℕ) : ℤ)) = 0
    unfold hrAkH
    push_cast
    rw [hedge0]; simp
  have hsup : ∀ i, k1 + 1 ≤ i → i ≤ kmax →
      (fun n : ℕ => hrAkH P Q a b h (n : ℤ)) (i + 1) + (fun n : ℕ => hrAkH P Q a b h (n : ℤ)) i ≤
        (fun n : ℕ => hrCkH P Q τ x a b h (n : ℤ)) i := by
    intro i hi1 hi2
    obtain ⟨f1, f2, f3, f4⟩ := hfacts i hi1
    have hik' : (i : ℝ) ≤ kmax := Nat.cast_le.2 hi2
    have hD : ((((i : ℝ) + 1 / 2) + 1) * h) ^ 2 ∈ Dom P Q :=
      Dom_mono hP hQ (by positivity)
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (by linarith) hh.le) 2) hedge
    have hkq : qs ≤ 2 * ((i : ℝ) + 1 / 2) * h := by nlinarith
    have hK : 0 ≤ 2 * ((1 - τ * x) / qs ^ 2) * qs :=
      mul_nonneg (mul_nonneg (by norm_num) (div_nonneg hκ.le (sq_nonneg _))) hqs.le
    have hgap : hrRho P Q a b qs * h ^ 2 ≤
        2 * ((1 - τ * x) / qs ^ 2) * qs * ((((i : ℝ) + 1 / 2) + 1 / 2) * h - qs) := by
      calc hrRho P Q a b qs * h ^ 2 = (h * hrRho P Q a b qs) * h := by ring
        _ ≤ (2 * ((1 - τ * x) / qs ^ 2) * qs) * h := mul_le_mul_of_nonneg_right hhC hh.le
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) hK
    have := exact_hyperbolicity_hahn_racah hP hQ a b τ x qs h ((i : ℝ) + 1 / 2) hh hqs hτ hκ hturn f1
      f2.le f3.le hkq hD hgap
    simp only [hrAkH, hrCkH]
    push_cast
    have e : ((i : ℝ) + 1 + 1 / 2) = ((i : ℝ) + 1 / 2) + 1 := by ring
    rw [e]
    linarith
  have hrow : ∀ i, k1 + 1 ≤ i → i ≤ kmax →
      (fun n : ℕ => hrAkH P Q a b h (n : ℤ)) (i + 1) * (fun n : ℕ => Y (n : ℤ)) (i + 1) +
        (fun n : ℕ => hrAkH P Q a b h (n : ℤ)) i * (fun n : ℕ => Y (n : ℤ)) (i - 1) =
      (fun n : ℕ => hrCkH P Q τ x a b h (n : ℤ)) i * (fun n : ℕ => Y (n : ℤ)) i := by
    intro i hi1 hi2
    have h0 := hY (i : ℤ) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
    unfold jac at h0
    show hrAkH P Q a b h ((i + 1 : ℕ) : ℤ) * Y ((i + 1 : ℕ) : ℤ) +
      hrAkH P Q a b h (i : ℤ) * Y ((i - 1 : ℕ) : ℤ) = hrCkH P Q τ x a b h (i : ℤ) * Y (i : ℤ)
    rw [show ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 by push_cast; ring,
      show ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 by omega]
    linarith
  have H := hd_backward_decay (fun n : ℕ => hrAkH P Q a b h (n : ℤ))
    (fun n : ℕ => hrCkH P Q τ x a b h (n : ℤ)) (fun n : ℕ => Y (n : ℤ)) (k1 + 1) kmax (by omega)
    (by omega) hA hend hsup hrow
  intro k hk1' hk2
  lift k to ℕ using (by omega)
  have := H k (by omega) (by omega)
  simpa using this

/-- info: 'FormalResearch.Special.hr_hardedge_decayH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hr_hardedge_decayH

end FormalResearch.Special

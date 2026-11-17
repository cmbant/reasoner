module

public import FormalResearch.Special.DiscreteAiryKappaTransport

/-!
# The mass of an oscillating solution on a band, from its amplitude form (Airy-free assembly; plan K1, step K-2)

Combine the exact mass identity (`kerm_mass_bound`, weights `v_j = P_j/2`, which is `1/α_j` for the Hahn profile `P = 2/α`) with the
invariance `I_j ≤ e^S I_p`, `I_p ≤ e^{2S} I_j` of the amplitude form on the band (`kerm_invariant`/`kp_transport`):

`|Σ_{i≤m} Y_{p+i}² - I_p Σ_{i≤m} P_{p+i}/2| ≤ I_p [ (e^{2S} - 1)e^{S} Σ v + 4(r + τ) e^{S} Σ v + (2τ/A + 32/A³) e^{S} ]`

(`kp_band_mass`), where `|Ω_j - 1| ≤ r`, `|u_{j+1} - u_j| a_{j+1} ≤ τ` (`u = v s`), `S = Σ ε`, `0 < P ≤ 2/A`, `0 < a ≤ 1` on the band.
`Ω_j = 1 + (P_{j+1} - P_j)/(2P_j) + (1/P_j)(s_{j+1}(u_{j+1} - u_j) + u_j E_j)` exactly for `v = P/2` (`kp_omega_eq`).

**Claim class: proved** (real algebra).  The explicit values of `r, τ, S` for the Hahn band are in `DiscreteAiryKappaBandHahn`.
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- **`Ω` for the weights `v = P/2`, exactly**: `Ω_k = (P_k + P_{k+1})/(2P_k) + (s_{k+1}(u_{k+1} - u_k) + u_k E_k)/P_k`,
`u_j = (P_j/2) s_j`; uses only the radicand identities at `k, k+1`. -/
lemma kp_omega_eq {a c P : ℤ → ℝ} {k : ℤ} (hP : 0 < P k)
    (h0 : a k ^ 2 * P k * P (k - 1) = kermS a P k ^ 2 + 1)
    (h1 : a (k + 1) ^ 2 * P (k + 1) * P k = kermS a P (k + 1) ^ 2 + 1) :
    kmOmega a c P (fun j => P j / 2) k =
      (P k + P (k + 1)) / (2 * P k) +
        (kermS a P (k + 1) * (P (k + 1) / 2 * kermS a P (k + 1) - P k / 2 * kermS a P k) +
          P k / 2 * kermS a P k * kermE a c P k) / P k := by
  unfold kmOmega kermE
  simp only []
  field_simp
  linear_combination 1 * (P k) * h0 + 1 * (P (k + 1)) * h1

/-- **Boundary term**: `|Bd(k-1)| ≤ 16 J/A³` when `I_k ≤ J`, `0 < a_k ≤ 1`, `0 < P ≤ 2/A` (`v = P/2`). -/
lemma kp_bd_bound {a P Y : ℤ → ℝ} {k : ℤ} {A J : ℝ} (hA : 0 < A) (hrad : 1 ≤ a k ^ 2 * P k * P (k - 1))
    (ha0 : 0 < a k) (ha1 : a k ≤ 1) (hp : 0 < P k) (hp' : 0 < P (k - 1)) (hpa : P k ≤ 2 / A)
    (hpb : P (k - 1) ≤ 2 / A) (hJ : kermI a P Y k ≤ J) :
    |kmBd a P Y (fun j => P j / 2) (k - 1)| ≤ 16 * J / A ^ 3 := by
  obtain ⟨l1, l2⟩ := kermI_lower (a := a) (Y := Y) hp hp' hrad
  have hJ0 : 0 ≤ J := by
    have := kermI_nonneg (a := a) (Y := Y) hp hp' hrad
    linarith
  have y1 : Y k ^ 2 ≤ 4 / A * J := by
    calc Y k ^ 2 ≤ 2 * P k * kermI a P Y k := l1
      _ ≤ 2 * (2 / A) * J := by
          apply mul_le_mul (by linarith) hJ (kermI_nonneg (a := a) (Y := Y) hp hp' hrad) (by positivity)
      _ = 4 / A * J := by ring
  have y2 : Y (k - 1) ^ 2 ≤ 4 / A * J := by
    calc Y (k - 1) ^ 2 ≤ 2 * P (k - 1) * kermI a P Y k := l2
      _ ≤ 2 * (2 / A) * J := by
          apply mul_le_mul (by linarith) hJ (kermI_nonneg (a := a) (Y := Y) hp hp' hrad) (by positivity)
      _ = 4 / A * J := by ring
  have hs : kermS a P k ≤ 2 / A := kermS_le hA ha0.le ha1 hp.le hp'.le hpa hpb
  have hs0 := kermS_nonneg a P k
  unfold kmBd
  simp only [sub_add_cancel]
  have hv : P k / 2 ≤ 1 / A := by
    have : P k / 2 ≤ (2 / A) / 2 := by linarith
    linarith [show (2 / A) / 2 = 1 / A by ring]
  have hv0 : 0 ≤ P k / 2 := by linarith
  have t1 : |-(P k / 2 * a k ^ 2 * P k * Y (k - 1) ^ 2)| ≤ 8 * J / A ^ 3 := by
    rw [abs_neg, abs_of_nonneg (by positivity)]
    have h1 : a k ^ 2 ≤ 1 := by nlinarith
    calc P k / 2 * a k ^ 2 * P k * Y (k - 1) ^ 2 ≤ (1 / A) * 1 * (2 / A) * (4 / A * J) := by
          apply mul_le_mul (mul_le_mul (mul_le_mul hv h1 (sq_nonneg _) (by positivity)) hpa hp.le (by positivity)) y2
            (sq_nonneg _) (by positivity)
      _ = 8 * J / A ^ 3 := by field_simp; ring
  have t2 : |P k / 2 * kermS a P k * (a k * Y k * Y (k - 1))| ≤ 8 * J / A ^ 3 := by
    have hyy : |Y k * Y (k - 1)| ≤ (Y k ^ 2 + Y (k - 1) ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (Y k + Y (k - 1)), sq_nonneg (Y k - Y (k - 1))]
    rw [show a k * Y k * Y (k - 1) = a k * (Y k * Y (k - 1)) by ring, abs_mul, abs_mul,
      abs_of_nonneg hv0, abs_of_nonneg hs0, abs_mul, abs_of_pos ha0]
    calc P k / 2 * kermS a P k * (a k * |Y k * Y (k - 1)|) ≤ (1 / A) * (2 / A) * (1 * (4 / A * J)) := by
          apply mul_le_mul (mul_le_mul hv hs hs0 (by positivity)) _ (by positivity) (by positivity)
          apply mul_le_mul ha1 _ (abs_nonneg _) (by norm_num)
          linarith
      _ = 8 * J / A ^ 3 := by field_simp; ring
  calc _ ≤ |-(P k / 2 * a k ^ 2 * P k * Y (k - 1) ^ 2)| + |P k / 2 * kermS a P k * (a k * Y k * Y (k - 1))| :=
        abs_add_le _ _
    _ ≤ 8 * J / A ^ 3 + 8 * J / A ^ 3 := add_le_add t1 t2
    _ = 16 * J / A ^ 3 := by ring

/-- Pointwise deviation of the amplitude form: `|I - I_p| ≤ (e^{2S} - 1)e^S I_p` from `I ≤ e^S I_p`, `I_p ≤ e^{2S} I`. -/
lemma kp_I_dev {I Ip S : ℝ} (hS : 0 ≤ S) (hIp : 0 ≤ Ip) (u1 : I ≤ Real.exp S * Ip)
    (u2 : Ip ≤ Real.exp (2 * S) * I) : |I - Ip| ≤ (Real.exp (2 * S) - 1) * Real.exp S * Ip := by
  have hE1 : 1 ≤ Real.exp S := Real.one_le_exp hS
  have hE2 : 1 ≤ Real.exp (2 * S) := Real.one_le_exp (by linarith)
  have hES : Real.exp S ≤ Real.exp (2 * S) := Real.exp_le_exp.2 (by linarith)
  rw [abs_le]
  constructor
  · have h1 : Ip - I ≤ (Real.exp (2 * S) - 1) * I := by linarith
    have h2 : (Real.exp (2 * S) - 1) * I ≤ (Real.exp (2 * S) - 1) * (Real.exp S * Ip) :=
      mul_le_mul_of_nonneg_left u1 (sub_nonneg.2 hE2)
    nlinarith
  · have h1 : I - Ip ≤ (Real.exp S - 1) * Ip := by nlinarith
    have h2 : (Real.exp S - 1) * Ip ≤ (Real.exp (2 * S) - 1) * Real.exp S * Ip := by
      have : Real.exp S - 1 ≤ (Real.exp (2 * S) - 1) * Real.exp S := by nlinarith
      exact mul_le_mul_of_nonneg_right this hIp
    linarith

theorem kp_band_mass {a c P Y : ℤ → ℝ} {p : ℤ} (m : ℕ) {r τ S A Ip : ℝ} (hA : 0 < A) (hS : 0 ≤ S)
    (hτ : 0 ≤ τ) (hrow : ∀ i : ℕ, i ≤ m → jac a c Y (p + (i : ℤ)) = 0)
    (hP : ∀ i : ℕ, i ≤ m + 1 → 0 < P (p + (i : ℤ)) ∧ P (p + (i : ℤ)) ≤ 2 / A)
    (hPm : 0 < P (p - 1) ∧ P (p - 1) ≤ 2 / A)
    (hrad : ∀ i : ℕ, i ≤ m + 1 → 1 ≤ a (p + (i : ℤ)) ^ 2 * P (p + (i : ℤ)) * P (p + (i : ℤ) - 1))
    (hapos : ∀ i : ℕ, i ≤ m + 1 → 0 < a (p + (i : ℤ))) (hale : ∀ i : ℕ, i ≤ m + 1 → a (p + (i : ℤ)) ≤ 1)
    (hI : ∀ i : ℕ, i ≤ m + 1 → kermI a P Y (p + (i : ℤ)) ≤ Real.exp S * Ip ∧
      Ip ≤ Real.exp (2 * S) * kermI a P Y (p + (i : ℤ)))
    (hΩ : ∀ i : ℕ, i ≤ m → |kmOmega a c P (fun j => P j / 2) (p + (i : ℤ)) - 1| ≤ r)
    (hD : ∀ i : ℕ, i ≤ m → |P (p + (i : ℤ) + 1) / 2 * kermS a P (p + (i : ℤ) + 1) -
        P (p + (i : ℤ)) / 2 * kermS a P (p + (i : ℤ))| * a (p + (i : ℤ) + 1) ≤ τ) :
    |∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 - Ip * ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2| ≤
      Ip * (((Real.exp (2 * S) - 1) * Real.exp S + 4 * (|r| + τ) * Real.exp S) * ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 +
        (2 * τ / A + 32 / A ^ 3) * Real.exp S) := by
  have hPm' : ∀ i : ℕ, i ≤ m + 1 → 0 < P (p + (i : ℤ) - 1) ∧ P (p + (i : ℤ) - 1) ≤ 2 / A := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simpa using hPm
    · have := hP (i - 1) (by omega)
      rwa [show p + ((i - 1 : ℕ) : ℤ) = p + (i : ℤ) - 1 by push_cast [Nat.cast_sub hi0]; ring] at this
  have hIp0 : 0 ≤ Ip := by
    have h1 := (hI 0 (by omega)).1
    have h2 := kermI_nonneg (a := a) (Y := Y) (hP 0 (by omega)).1 (by simpa using (hPm' 0 (by omega)).1)
      (by simpa using hrad 0 (by omega))
    simp only [Nat.cast_zero, add_zero] at h1 h2
    have h3 : 0 ≤ Real.exp S * Ip := h2.trans h1
    exact (mul_nonneg_iff_of_pos_left (Real.exp_pos S)).1 h3
  have hE1 : 1 ≤ Real.exp S := Real.one_le_exp hS
  have hvpos : ∀ i : ℕ, i ≤ m + 1 → 0 < P (p + (i : ℤ)) / 2 := fun i hi => by have := (hP i hi).1; positivity
  have hsucc : ∀ i : ℕ, p + ((i + 1 : ℕ) : ℤ) = p + (i : ℤ) + 1 := fun i => by push_cast; ring
  -- the mass bound
  have mb := kerm_mass_bound (a := a) (c := c) (P := P) (Y := Y) (v := fun j => P j / 2) p m (r := r) (τ := τ) hτ hrow
    hΩ hD (fun i hi => by
      have h := hapos (i + 1) (by omega)
      rwa [hsucc] at h)
  have hY2 : ∀ i : ℕ, i ≤ m + 1 → Y (p + (i : ℤ)) ^ 2 ≤ 2 * P (p + (i : ℤ)) * (Real.exp S * Ip) := fun i hi =>
    (kermI_lower (a := a) (Y := Y) (hP i hi).1 (hPm' i hi).1 (hrad i hi)).1.trans
      (mul_le_mul_of_nonneg_left (hI i hi).1 (by have := (hP i hi).1; positivity))
  set Sv := ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 with hSv
  have hSv0 : 0 ≤ Sv := Finset.sum_nonneg fun i hi => (hvpos i (by have := Finset.mem_range.1 hi; omega)).le
  have hsumY : ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 ≤ 4 * Real.exp S * Ip * Sv := by
    calc ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 ≤ ∑ i ∈ range (m + 1), 2 * P (p + (i : ℤ)) * (Real.exp S * Ip) :=
          Finset.sum_le_sum fun i hi => hY2 i (by have := Finset.mem_range.1 hi; omega)
      _ = 4 * Real.exp S * Ip * Sv := by
          rw [hSv, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have hsumY0 : 0 ≤ ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hdiff : |∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ)) - Ip * Sv| ≤
      (Real.exp (2 * S) - 1) * Real.exp S * Ip * Sv := by
    have : ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ)) - Ip * Sv =
        ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * (kermI a P Y (p + (i : ℤ)) - Ip) := by
      rw [hSv, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i ∈ range (m + 1), |P (p + (i : ℤ)) / 2 * (kermI a P Y (p + (i : ℤ)) - Ip)| ≤
        ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * ((Real.exp (2 * S) - 1) * Real.exp S * Ip) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' := Finset.mem_range.1 hi
          have hv := hvpos i (by omega)
          rw [abs_mul, abs_of_pos hv]
          apply mul_le_mul_of_nonneg_left _ hv.le
          exact kp_I_dev hS hIp0 (hI i (by omega)).1 (hI i (by omega)).2
      _ = (Real.exp (2 * S) - 1) * Real.exp S * Ip * Sv := by
          rw [hSv, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  -- the boundary terms
  have hradm := hrad (m + 1) le_rfl
  rw [hsucc] at hradm
  have hPe := hP (m + 1) le_rfl
  rw [hsucc] at hPe
  have hPe' := hP m (by omega)
  have hae := hapos (m + 1) le_rfl
  rw [hsucc] at hae
  have hale' := hale (m + 1) le_rfl
  rw [hsucc] at hale'
  have hIe := (hI (m + 1) le_rfl).1
  rw [hsucc] at hIe
  have bdE := kp_bd_bound (a := a) (P := P) (Y := Y) (k := p + (m : ℤ) + 1) (A := A) (J := Real.exp S * Ip) hA hradm hae
    hale' hPe.1 (by simpa using hPe'.1) hPe.2 (by simpa using hPe'.2) hIe
  simp only [add_sub_cancel_right] at bdE
  have h0r := hrad 0 (by omega)
  simp only [Nat.cast_zero, add_zero] at h0r
  have hS0 := hI 0 (by omega)
  simp only [Nat.cast_zero, add_zero] at hS0
  have bd0 := kp_bd_bound (a := a) (P := P) (Y := Y) (k := p) (A := A) (J := Real.exp S * Ip) hA h0r
    (by simpa using hapos 0 (by omega)) (by simpa using hale 0 (by omega)) (by simpa using (hP 0 (by omega)).1)
    (by simpa using (hPm' 0 (by omega)).1) (by simpa using (hP 0 (by omega)).2) (by simpa using (hPm' 0 (by omega)).2) hS0.1
  have hYend : Y (p + (m : ℤ) + 1) ^ 2 ≤ 4 / A * (Real.exp S * Ip) := by
    have := hY2 (m + 1) le_rfl
    rw [hsucc] at this
    refine this.trans ?_
    calc 2 * P (p + (m : ℤ) + 1) * (Real.exp S * Ip) ≤ 2 * (2 / A) * (Real.exp S * Ip) :=
          mul_le_mul_of_nonneg_right (by linarith [hPe.2]) (mul_nonneg (Real.exp_pos S).le hIp0)
      _ = 4 / A * (Real.exp S * Ip) := by ring
  have hrt : r + τ ≤ |r| + τ := by linarith [le_abs_self r]
  have h1 : (r + τ) * ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 ≤ (|r| + τ) * (4 * Real.exp S * Ip * Sv) :=
    (mul_le_mul_of_nonneg_right hrt hsumY0).trans (mul_le_mul_of_nonneg_left hsumY (by positivity))
  have h2 : τ / 2 * Y (p + (m : ℤ) + 1) ^ 2 ≤ τ / 2 * (4 / A * (Real.exp S * Ip)) :=
    mul_le_mul_of_nonneg_left hYend (by positivity)
  have e1 : 16 * (Real.exp S * Ip) / A ^ 3 + 16 * (Real.exp S * Ip) / A ^ 3 = 32 / A ^ 3 * (Real.exp S * Ip) := by ring
  have e2 : τ / 2 * (4 / A * (Real.exp S * Ip)) = 2 * τ / A * (Real.exp S * Ip) := by ring
  have e3 : |∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 - Ip * Sv| ≤
      |∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ)) - ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2| +
      |∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ)) - Ip * Sv| := by
    rw [abs_sub_comm (∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ)))]
    calc _ = |(∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 - ∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ))) +
          (∑ i ∈ range (m + 1), P (p + (i : ℤ)) / 2 * kermI a P Y (p + (i : ℤ)) - Ip * Sv)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  have hIe2 : 0 ≤ Real.exp S * Ip := mul_nonneg (Real.exp_pos S).le hIp0
  calc _ ≤ _ := e3
    _ ≤ ((r + τ) * ∑ i ∈ range (m + 1), Y (p + (i : ℤ)) ^ 2 + τ / 2 * Y (p + (m : ℤ) + 1) ^ 2 +
          |kmBd a P Y (fun j => P j / 2) (p + (m : ℤ))| + |kmBd a P Y (fun j => P j / 2) (p - 1)|) +
        (Real.exp (2 * S) - 1) * Real.exp S * Ip * Sv := add_le_add mb hdiff
    _ ≤ ((|r| + τ) * (4 * Real.exp S * Ip * Sv) + 2 * τ / A * (Real.exp S * Ip) + 16 * (Real.exp S * Ip) / A ^ 3 +
          16 * (Real.exp S * Ip) / A ^ 3) + (Real.exp (2 * S) - 1) * Real.exp S * Ip * Sv := by
        have := h1; have := h2; have := bdE; have := bd0
        linarith
    _ = _ := by ring

/-- info: 'FormalResearch.Special.kp_band_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.kp_band_mass

end FormalResearch.Special

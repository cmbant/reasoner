module

public import FormalResearch.Special.DiscreteAiryKappaSharpAlg
public import FormalResearch.Special.DiscreteAiryKappaProfile
public import FormalResearch.Special.DiscreteAiryKappaTransport

/-!
# Sharp `κ`: the phase defect `1 - u² - 1/W` of the Hahn profile (plan K1, sharp constant, step 2)

For the Hahn profile `P = 2/α` at the lattice pair `(k, k-1)` (`q_k = U`, `q_{k-1} = U - h`, `α_a² = q_*² - U²`, `α_b² = q_*² - (U-h)²`) and
`a² = (1 + η_r)(1 - (U - h/2)²)/4`, one has `1/W = α_aα_b/((1 + η_r)(1 - (U-h/2)²))` (`W = a² P_k P_{k-1}`), while the eikonal value at a point
`η ∈ [U-h, U]` is `1 - u(η)² = (q_*² - η²)/(1 - η²)`.  `ksh_rho_core`:

`|1 - u² - 1/W| ≤ 3h/(A x²) + 2(h + |η_r|)/x⁴`        (`α_a, α_b ≥ A`, `|η_r| ≤ ½`).

**Claim class: proved** (real algebra).
-/

@[expose] public section

open Finset

namespace FormalResearch.Special

/-- Numerator part: `|(q_*² - η²) - α_aα_b| ≤ 3h/A`. -/
lemma ksh_rho_N {qs h U η αa αb A : ℝ} (hqs1 : qs ≤ 1) (hh : 0 < h) (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hαa : αa ^ 2 = qs ^ 2 - U ^ 2) (hαb : αb ^ 2 = qs ^ 2 - (U - h) ^ 2) (hAa : A ≤ αa) (hAb : A ≤ αb)
    (hη1 : U - h ≤ η) (hη2 : η ≤ U) (hUh : h ≤ U) (hU1 : U ≤ 1) (hqs0 : 0 ≤ qs) :
    |(qs ^ 2 - η ^ 2) - αa * αb| ≤ 3 * h / A := by
  have hU0 : 0 ≤ U := by linarith
  have hη0 : 0 ≤ η := by linarith
  have hαa0 : 0 < αa := by linarith
  have hαb0 : 0 < αb := by linarith
  have hαa1 : αa ≤ 1 := by nlinarith [hαa, sq_nonneg U, sq_nonneg (αa - 1)]
  have hdiff : |αa - αb| ≤ h / A := by
    have h1 : αa ^ 2 - αb ^ 2 = -(h * (2 * U - h)) := by rw [hαa, hαb]; ring
    have h2 : |αa - αb| * (αa + αb) = h * (2 * U - h) := by
      have e : (αa - αb) * (αa + αb) = αa ^ 2 - αb ^ 2 := by ring
      rw [← abs_of_pos (by linarith : 0 < αa + αb), ← abs_mul, e, h1, abs_neg,
        abs_of_nonneg (by nlinarith [mul_nonneg hh.le (by linarith : 0 ≤ 2 * U - h)])]
    rw [le_div_iff₀ hA0]
    have h3 := mul_le_mul_of_nonneg_left (by linarith : 2 * A ≤ αa + αb) (abs_nonneg (αa - αb))
    have h4 : h * (2 * U - h) ≤ 2 * h := by nlinarith
    nlinarith [abs_nonneg (αa - αb)]
  have e : (qs ^ 2 - η ^ 2) - αa * αb = αa * (αa - αb) + (U ^ 2 - η ^ 2) := by nlinarith [hαa]
  rw [e]
  have a1 : |αa * (αa - αb)| ≤ h / A := by
    rw [abs_mul, abs_of_pos hαa0]
    calc αa * |αa - αb| ≤ 1 * |αa - αb| := mul_le_mul_of_nonneg_right hαa1 (abs_nonneg _)
      _ ≤ h / A := by rw [one_mul]; exact hdiff
  have a2 : |U ^ 2 - η ^ 2| ≤ 2 * h := by
    rw [abs_of_nonneg (by nlinarith)]
    nlinarith [mul_nonneg hh.le hU0]
  have a3 : 3 * h / A = h / A + 2 * h / A := by ring
  have a4 : 2 * h ≤ 2 * h / A := by
    rw [le_div_iff₀ hA0]; nlinarith
  calc |αa * (αa - αb) + (U ^ 2 - η ^ 2)| ≤ |αa * (αa - αb)| + |U ^ 2 - η ^ 2| := abs_add_le _ _
    _ ≤ 3 * h / A := by rw [a3]; linarith

/-- Denominator part: `|(1 + η_r)(1 - (U - h/2)²) - (1 - η²)| ≤ h + |η_r|`. -/
lemma ksh_rho_D {h U η ηr : ℝ} (hh : 0 < h) (hη1 : U - h ≤ η) (hη2 : η ≤ U) (hUh : h ≤ U) (hU1 : U ≤ 1) :
    |(1 + ηr) * (1 - (U - h / 2) ^ 2) - (1 - η ^ 2)| ≤ h + |ηr| := by
  have e : (1 + ηr) * (1 - (U - h / 2) ^ 2) - (1 - η ^ 2) = (η ^ 2 - (U - h / 2) ^ 2) + ηr * (1 - (U - h / 2) ^ 2) := by ring
  rw [e]
  have hm1 : (U - h / 2) ^ 2 ≤ 1 := by nlinarith
  have hm0 : 0 ≤ U - h / 2 := by linarith
  have b1 : |η ^ 2 - (U - h / 2) ^ 2| ≤ h := by
    have : η ^ 2 - (U - h / 2) ^ 2 = (η - (U - h / 2)) * (η + (U - h / 2)) := by ring
    rw [this, abs_mul]
    have c1 : |η - (U - h / 2)| ≤ h / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    have c2 : |η + (U - h / 2)| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
    nlinarith [abs_nonneg (η - (U - h / 2)), abs_nonneg (η + (U - h / 2))]
  have b2 : |ηr * (1 - (U - h / 2) ^ 2)| ≤ |ηr| := by
    have h0 : 0 ≤ 1 - (U - h / 2) ^ 2 := by linarith
    rw [abs_mul, abs_of_nonneg h0]
    have : 1 - (U - h / 2) ^ 2 ≤ 1 := by nlinarith
    nlinarith [abs_nonneg ηr]
  calc |(η ^ 2 - (U - h / 2) ^ 2) + ηr * (1 - (U - h / 2) ^ 2)| ≤ _ := abs_add_le _ _
    _ ≤ h + |ηr| := by linarith

/-- Quotient assembly: `|N₁/D₁ - N₂/D₂| ≤ |N₁ - N₂|/x² + 2|D₂ - D₁|/x⁴` for `D₁ ≥ x²`, `D₂ ≥ x²/2`, `0 ≤ N₂ ≤ 1`. -/
lemma ksh_rho_quot {N1 N2 D1 D2 x2 B C : ℝ} (hx2 : 0 < x2) (hD1 : x2 ≤ D1) (hD2 : x2 / 2 ≤ D2) (hN2 : 0 ≤ N2) (hN2' : N2 ≤ 1)
    (hN : |N1 - N2| ≤ B) (hD : |D2 - D1| ≤ C) :
    |N1 / D1 - N2 / D2| ≤ B / x2 + 2 * C / x2 ^ 2 := by
  have hD1p : 0 < D1 := by linarith
  have hD2p : 0 < D2 := by linarith
  have key : N1 / D1 - N2 / D2 = (N1 - N2) / D1 + N2 * (D2 - D1) / (D1 * D2) := by
    field_simp; ring
  rw [key]
  have t1 : |(N1 - N2) / D1| ≤ B / x2 := by
    rw [abs_div, abs_of_pos hD1p]
    exact div_le_div₀ ((abs_nonneg _).trans hN) hN hx2 hD1
  have t2 : |N2 * (D2 - D1) / (D1 * D2)| ≤ 2 * C / x2 ^ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg hN2, abs_of_pos (mul_pos hD1p hD2p)]
    have hden : x2 * (x2 / 2) ≤ D1 * D2 := mul_le_mul hD1 hD2 (by positivity) hD1p.le
    have hnum : N2 * |D2 - D1| ≤ C := by
      calc N2 * |D2 - D1| ≤ 1 * |D2 - D1| := mul_le_mul_of_nonneg_right hN2' (abs_nonneg _)
        _ ≤ C := by rw [one_mul]; exact hD
    calc N2 * |D2 - D1| / (D1 * D2) ≤ C / (x2 * (x2 / 2)) :=
          div_le_div₀ ((abs_nonneg _).trans hD |>.trans' (by positivity) |> fun h => by
            exact le_trans (by positivity) hnum |> fun h2 => h2) hnum (by positivity) hden
      _ = 2 * C / x2 ^ 2 := by field_simp
  calc _ ≤ |(N1 - N2) / D1| + |N2 * (D2 - D1) / (D1 * D2)| := abs_add_le _ _
    _ ≤ _ := by linarith

lemma ksh_rho_core {x qs h U η ηr αa αb A : ℝ} (hx : 0 < x) (hqs : qs ^ 2 = 1 - x ^ 2) (hqs0 : 0 < qs) (hh : 0 < h)
    (hA0 : 0 < A) (hA1 : A ≤ 1)
    (hαa : αa ^ 2 = qs ^ 2 - U ^ 2) (hαb : αb ^ 2 = qs ^ 2 - (U - h) ^ 2) (hAa : A ≤ αa) (hAb : A ≤ αb)
    (hη1 : U - h ≤ η) (hη2 : η ≤ U) (hUh : h ≤ U) (hηr : |ηr| ≤ 1 / 2) :
    |(qs ^ 2 - η ^ 2) / (1 - η ^ 2) - αa * αb / ((1 + ηr) * (1 - (U - h / 2) ^ 2))| ≤
      3 * h / (A * x ^ 2) + 2 * (h + |ηr|) / x ^ 4 := by
  have hαa0 : 0 < αa := by linarith
  have hαb0 : 0 < αb := by linarith
  have hUq : U < qs := by
    have : U ^ 2 < qs ^ 2 := by nlinarith [hαa, sq_pos_of_pos hαa0]
    exact lt_of_pow_lt_pow_left₀ 2 hqs0.le this
  have hqs1 : qs ≤ 1 := by nlinarith [sq_nonneg x]
  have hU1 : U ≤ 1 := by linarith
  have hU0 : 0 ≤ U := by linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have hD1 : x ^ 2 ≤ 1 - η ^ 2 := by
    have : η ^ 2 ≤ qs ^ 2 := by nlinarith
    linarith
  have hr12 := abs_le.1 hηr
  have hD2a : x ^ 2 ≤ 1 - (U - h / 2) ^ 2 := by
    have : (U - h / 2) ^ 2 ≤ qs ^ 2 := by nlinarith
    linarith
  have hD2 : x ^ 2 / 2 ≤ (1 + ηr) * (1 - (U - h / 2) ^ 2) := by
    nlinarith [mul_le_mul (by linarith : (1 : ℝ) / 2 ≤ 1 + ηr) hD2a hx2.le (by linarith)]
  have hN2le : αa * αb ≤ 1 := by
    have h1 : αa ≤ 1 := by nlinarith [hαa, sq_nonneg U]
    have h2 : αb ≤ 1 := by nlinarith [hαb, sq_nonneg (U - h)]
    nlinarith [mul_le_mul h1 h2 hαb0.le (by norm_num)]
  have hN := ksh_rho_N hqs1 hh hA0 hA1 hαa hαb hAa hAb hη1 hη2 hUh hU1 hqs0.le
  have hD := ksh_rho_D (ηr := ηr) hh hη1 hη2 hUh hU1
  have := ksh_rho_quot (N1 := qs ^ 2 - η ^ 2) (N2 := αa * αb) (D1 := 1 - η ^ 2)
    (D2 := (1 + ηr) * (1 - (U - h / 2) ^ 2)) (x2 := x ^ 2) hx2 hD1 hD2 (by positivity) hN2le hN hD
  refine this.trans (le_of_eq ?_)
  field_simp

/-- **The cosine of the Ermakov phase vs the eikonal value** at the bond `(k, k-1)` of the Hahn profile: with `W = a_k² P_k P_{k-1}`,
`s_k = kermS`, `u = x/√(1-η²)` (`η ∈ [q_{k-1}, q_k]`; `u = Ch(ζζ'²)` of the Langer chart) and `a_k² = (1 + η_r)(1 - (kh)²)/4`:
`|s_k/√W - u| ≤ (3h/(A x²) + 2(h + |η_r|)/x⁴)/x`. -/
theorem ksh_site_rho {x qs h A η ηr : ℝ} {k : ℤ} {a : ℤ → ℝ} (hx : 0 < x) (hqs : qs ^ 2 = 1 - x ^ 2) (hqs0 : 0 < qs)
    (hh : 0 < h) (hk : 1 ≤ k) (hA0 : 0 < A) (hA1 : A ≤ 1) (hAm : A ^ 2 ≤ qs ^ 2 - kpU h (k - 1) ^ 2)
    (hA0' : A ^ 2 ≤ qs ^ 2 - kpU h k ^ 2) (ha : a k ^ 2 = (1 + ηr) * ((1 - ((k : ℝ) * h) ^ 2) / 4))
    (hηr : |ηr| ≤ x ^ 2) (hηr2 : |ηr| ≤ 1 / 2) (hη1 : kpU h (k - 1) ≤ η) (hη2 : η ≤ kpU h k) :
    |kermS a (kpP qs h) k / √(a k ^ 2 * kpP qs h k * kpP qs h (k - 1)) - x / √(1 - η ^ 2)| ≤
      (3 * h / (A * x ^ 2) + 2 * (h + |ηr|) / x ^ 4) / x := by
  have hW := kp_rad_ge (a := a) (η := ηr) hqs hk hh hA0 hAm hA0' ha hηr
  obtain ⟨sa, bA⟩ := kpα_sq hA0'
  obtain ⟨sb, bB⟩ := kpα_sq hAm
  have hkk : kpU h k - h = kpU h (k - 1) := kpU_pred h k
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hUh : h ≤ kpU h k := by
    have : 0 ≤ ((k : ℝ) - 1 / 2) * h := mul_nonneg (by linarith) hh.le
    unfold kpU; nlinarith [this]
  have hηl : kpU h k - h ≤ η := by rw [hkk]; exact hη1
  set W := a k ^ 2 * kpP qs h k * kpP qs h (k - 1) with hWdef
  have hW0 : 0 < W := by linarith
  have hs2 := kermS_sq (a := a) (P := kpP qs h) (k := k) hW
  have hs0 := kermS_nonneg a (kpP qs h) k
  -- the eikonal value
  have hηq : η < qs := by
    have h1 : kpU h k < qs := by
      have hpos : 0 < kpα qs h k := by linarith
      have h2 : 0 < qs ^ 2 - kpU h k ^ 2 := by rw [← sa]; positivity
      have h0 : 0 < kpU h k := by
        have : 0 < ((k : ℝ) + 1 / 2) * h := mul_pos (by linarith) hh
        exact this
      exact lt_of_pow_lt_pow_left₀ 2 hqs0.le (by linarith)
    linarith
  have hη0 : 0 ≤ η := by linarith
  have hqs1 : qs ≤ 1 := by nlinarith [sq_nonneg x]
  have hD1 : x ^ 2 ≤ 1 - η ^ 2 := by
    have : η ^ 2 ≤ qs ^ 2 := pow_le_pow_left₀ hη0 hηq.le 2
    linarith
  have hD1p : 0 < 1 - η ^ 2 := lt_of_lt_of_le (by positivity) hD1
  have hsq := Real.sq_sqrt hD1p.le
  have hsq0 : 0 < √(1 - η ^ 2) := Real.sqrt_pos.2 hD1p
  have hsq1 : √(1 - η ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith [sq_nonneg η]
  have hu0 : 0 < x / √(1 - η ^ 2) := by positivity
  have hux : x ≤ x / √(1 - η ^ 2) := by
    rw [le_div_iff₀ hsq0]; exact mul_le_of_le_one_right hx.le hsq1
  have hv := ksh_v_close hW hs0 hs2 hu0
  have h1u : 1 - (x / √(1 - η ^ 2)) ^ 2 = (qs ^ 2 - η ^ 2) / (1 - η ^ 2) := by
    have e0 : 1 - η ^ 2 - x ^ 2 = qs ^ 2 - η ^ 2 := by linarith [hqs]
    rw [div_pow, hsq, one_sub_div hD1p.ne', e0]
  have h1W : 1 / W = kpα qs h k * kpα qs h (k - 1) / ((1 + ηr) * (1 - (kpU h k - h / 2) ^ 2)) := by
    have hk2 : (k : ℝ) * h = kpU h k - h / 2 := by unfold kpU; ring
    have hαa0 : 0 < kpα qs h k := by linarith
    have hαb0 : 0 < kpα qs h (k - 1) := by linarith
    rw [hWdef, ha, hk2]
    unfold kpP
    field_simp
    ring
  have hcore := ksh_rho_core (x := x) (qs := qs) (h := h) (U := kpU h k) (η := η) (ηr := ηr) (αa := kpα qs h k)
    (αb := kpα qs h (k - 1)) (A := A) hx hqs hqs0 hh hA0 hA1 sa (by rw [hkk]; exact sb) bA bB hηl hη2 hUh hηr2
  have e : 1 - (x / √(1 - η ^ 2)) ^ 2 - 1 / W =
      (qs ^ 2 - η ^ 2) / (1 - η ^ 2) - kpα qs h k * kpα qs h (k - 1) / ((1 + ηr) * (1 - (kpU h k - h / 2) ^ 2)) := by
    rw [h1u, h1W]
  rw [e] at hv
  refine hv.trans ?_
  calc _ ≤ |(qs ^ 2 - η ^ 2) / (1 - η ^ 2) - kpα qs h k * kpα qs h (k - 1) / ((1 + ηr) * (1 - (kpU h k - h / 2) ^ 2))| / x :=
        div_le_div_of_nonneg_left (abs_nonneg _) hx hux
    _ ≤ _ := div_le_div_of_nonneg_right hcore hx.le

/-- info: 'FormalResearch.Special.ksh_site_rho' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksh_site_rho

end FormalResearch.Special

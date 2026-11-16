module

public import FormalResearch.Special.AiryParametrixSkeleton

/-!
# Parametrix defect, part 4: the polynomial truncations and the skeleton constants

In the rescaled variables `ζ = h^{2/3} X`, `s = Δ/h^{1/3}`, the fifth-order Taylor polynomials of the shift
functions are (with `h = t³`, `X = ζ/t²`, `Δ = t s`)
`P₅(X,Δ) = Pe(ζ,s) + h Po(ζ,s)`, `Pe = 1 + ζs²/2 + ζ²s⁴/24`, `Po = s³/6 + ζ s⁵/30`
(`C`) and `P₅ˢ(X,Δ) = t (Sa(ζ,s) + h Sb(s))`, `Sa = s + ζs³/6 + ζ²s⁵/120`, `Sb = s⁴/12` (`S`).  `Pe` is even and `Po`
odd in `s`; `Sa` is odd and `Sb` even, and `Sa' = Pe`.  This file defines them, proves their derivatives and
bounds on `[-S, S]`, and instantiates the parity skeleton (`sk_even_odd`, `sk_odd_even`) for them:
`apx_skel_A`, `apx_skel_B` give the constants depending only on bounds `Z₀ ≥ |ζ|`, `S ≥ |s|`, `B`, `Ee`, `Γ`.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- `Pe(ζ, s) = 1 + ζ s²/2 + ζ² s⁴/24` (even in `s`; truncation of `cosh(√ζ s)`). -/
noncomputable def apxPe (z x : ℝ) : ℝ := 1 + z * x ^ 2 / 2 + z ^ 2 * x ^ 4 / 24
/-- `∂_s Pe`. -/
noncomputable def apxPe1 (z x : ℝ) : ℝ := z * x + z ^ 2 * x ^ 3 / 6
/-- `∂_s² Pe`. -/
noncomputable def apxPe2 (z x : ℝ) : ℝ := z + z ^ 2 * x ^ 2 / 2
/-- `Po(ζ, s) = s³/6 + ζ s⁵/30` (odd in `s`). -/
noncomputable def apxPo (z x : ℝ) : ℝ := x ^ 3 / 6 + z * x ^ 5 / 30
/-- `∂_s Po`. -/
noncomputable def apxPo1 (z x : ℝ) : ℝ := x ^ 2 / 2 + z * x ^ 4 / 6
/-- `Sa(ζ, s) = s + ζ s³/6 + ζ² s⁵/120` (odd; truncation of `sinh(√ζ s)/√ζ`); `∂_s Sa = Pe`. -/
noncomputable def apxSa (z x : ℝ) : ℝ := x + z * x ^ 3 / 6 + z ^ 2 * x ^ 5 / 120
/-- `Sb(s) = s⁴/12` (even). -/
noncomputable def apxSb (x : ℝ) : ℝ := x ^ 4 / 12
/-- `∂_s Sb`. -/
noncomputable def apxSb1 (x : ℝ) : ℝ := x ^ 3 / 3

lemma hasDerivAt_apxPe (z x : ℝ) : HasDerivAt (apxPe z) (apxPe1 z x) x := by
  have h2 := (hasDerivAt_pow 2 x).const_mul (z / 2)
  have h4 := (hasDerivAt_pow 4 x).const_mul (z ^ 2 / 24)
  have := (h2.add h4).const_add 1
  unfold apxPe apxPe1
  convert this using 1
  · funext y; simp only [Pi.add_apply]; ring
  · simp; ring

lemma hasDerivAt_apxPe1 (z x : ℝ) : HasDerivAt (apxPe1 z) (apxPe2 z x) x := by
  have h1 := (hasDerivAt_id x).const_mul z
  have h3 := (hasDerivAt_pow 3 x).const_mul (z ^ 2 / 6)
  have := h1.add h3
  unfold apxPe1 apxPe2
  convert this using 1
  · funext y; simp; ring
  · simp; ring

lemma hasDerivAt_apxPo (z x : ℝ) : HasDerivAt (apxPo z) (apxPo1 z x) x := by
  have h3 := (hasDerivAt_pow 3 x).const_mul (1 / 6 : ℝ)
  have h5 := (hasDerivAt_pow 5 x).const_mul (z / 30)
  have := h3.add h5
  unfold apxPo apxPo1
  convert this using 1
  · funext y; simp only [Pi.add_apply]; ring
  · simp; ring

lemma hasDerivAt_apxSa (z x : ℝ) : HasDerivAt (apxSa z) (apxPe z x) x := by
  have h1 := hasDerivAt_id x
  have h3 := (hasDerivAt_pow 3 x).const_mul (z / 6)
  have h5 := (hasDerivAt_pow 5 x).const_mul (z ^ 2 / 120)
  have := (h1.add h3).add h5
  unfold apxSa apxPe
  convert this using 1
  · funext y; simp; ring
  · simp; ring

lemma hasDerivAt_apxSb (x : ℝ) : HasDerivAt apxSb (apxSb1 x) x := by
  have h4 := (hasDerivAt_pow 4 x).const_mul (1 / 12 : ℝ)
  unfold apxSb apxSb1
  convert h4 using 1
  · funext y; ring
  · simp; ring

lemma hasDerivAt_apxSb1 (x : ℝ) : HasDerivAt apxSb1 (x ^ 2) x := by
  have h3 := (hasDerivAt_pow 3 x).const_mul (1 / 3 : ℝ)
  unfold apxSb1
  convert h3 using 1
  · funext y; ring
  · simp

lemma apxPe_neg (z x : ℝ) : apxPe z (-x) = apxPe z x := by unfold apxPe; ring
lemma apxPo_neg (z x : ℝ) : apxPo z (-x) = -apxPo z x := by unfold apxPo; ring
lemma apxSa_neg (z x : ℝ) : apxSa z (-x) = -apxSa z x := by unfold apxSa; ring
lemma apxSb_neg (x : ℝ) : apxSb (-x) = apxSb x := by unfold apxSb; ring

/-! ### Bounds on `|x| ≤ S` -/

section bounds
variable {z Z S x : ℝ}

/-- `|c z^i x^j| ≤ c Z^i S^j` for `c ≥ 0`, `|z| ≤ Z`, `|x| ≤ S`. -/
lemma apx_mono (c : ℝ) (hc : 0 ≤ c) (i j : ℕ) (hz : |z| ≤ Z) (hx : |x| ≤ S) :
    |c * z ^ i * x ^ j| ≤ c * Z ^ i * S ^ j := by
  rw [abs_mul, abs_mul, abs_of_nonneg hc, abs_pow, abs_pow]
  have hZ : 0 ≤ Z := (abs_nonneg _).trans hz
  have hS : 0 ≤ S := (abs_nonneg _).trans hx
  gcongr

lemma apxPe_le (hz : |z| ≤ Z) (hx : |x| ≤ S) :
    |apxPe z x| ≤ 1 + Z * S ^ 2 / 2 + Z ^ 2 * S ^ 4 / 24 := by
  have e : apxPe z x = 1 + (1 / 2) * z ^ 1 * x ^ 2 + (1 / 24) * z ^ 2 * x ^ 4 := by
    unfold apxPe; ring
  rw [e]
  have h1 := apx_mono (1 / 2) (by norm_num) 1 2 hz hx
  have h2 := apx_mono (1 / 24) (by norm_num) 2 4 hz hx
  calc _ ≤ |(1:ℝ) + (1 / 2) * z ^ 1 * x ^ 2| + |(1 / 24) * z ^ 2 * x ^ 4| := abs_add_le _ _
    _ ≤ |(1:ℝ)| + |(1 / 2) * z ^ 1 * x ^ 2| + |(1 / 24) * z ^ 2 * x ^ 4| := by
        have := abs_add_le (1:ℝ) ((1 / 2) * z ^ 1 * x ^ 2); linarith
    _ ≤ _ := by simp only [abs_one]; nlinarith [h1, h2]

lemma apxPe1_le (hz : |z| ≤ Z) (hx : |x| ≤ S) : |apxPe1 z x| ≤ Z * S + Z ^ 2 * S ^ 3 / 6 := by
  have e : apxPe1 z x = 1 * z ^ 1 * x ^ 1 + (1 / 6) * z ^ 2 * x ^ 3 := by
    unfold apxPe1; ring
  rw [e]
  have h1 := apx_mono 1 (by norm_num) 1 1 hz hx
  have h2 := apx_mono (1 / 6) (by norm_num) 2 3 hz hx
  exact (abs_add_le _ _).trans (by nlinarith [h1, h2])

lemma apxPe2_le (hz : |z| ≤ Z) (hx : |x| ≤ S) : |apxPe2 z x| ≤ Z + Z ^ 2 * S ^ 2 / 2 := by
  have e : apxPe2 z x = 1 * z ^ 1 * x ^ 0 + (1 / 2) * z ^ 2 * x ^ 2 := by
    unfold apxPe2; ring
  rw [e]
  have h1 := apx_mono 1 (by norm_num) 1 0 hz hx
  have h2 := apx_mono (1 / 2) (by norm_num) 2 2 hz hx
  exact (abs_add_le _ _).trans (by nlinarith [h1, h2])

lemma apxPo_le (hz : |z| ≤ Z) (hx : |x| ≤ S) : |apxPo z x| ≤ S ^ 3 / 6 + Z * S ^ 5 / 30 := by
  have e : apxPo z x = (1 / 6) * z ^ 0 * x ^ 3 + (1 / 30) * z ^ 1 * x ^ 5 := by
    unfold apxPo; ring
  rw [e]
  have h1 := apx_mono (1 / 6) (by norm_num) 0 3 hz hx
  have h2 := apx_mono (1 / 30) (by norm_num) 1 5 hz hx
  exact (abs_add_le _ _).trans (by nlinarith [h1, h2])

lemma apxPo1_le (hz : |z| ≤ Z) (hx : |x| ≤ S) : |apxPo1 z x| ≤ S ^ 2 / 2 + Z * S ^ 4 / 6 := by
  have e : apxPo1 z x = (1 / 2) * z ^ 0 * x ^ 2 + (1 / 6) * z ^ 1 * x ^ 4 := by
    unfold apxPo1; ring
  rw [e]
  have h1 := apx_mono (1 / 2) (by norm_num) 0 2 hz hx
  have h2 := apx_mono (1 / 6) (by norm_num) 1 4 hz hx
  exact (abs_add_le _ _).trans (by nlinarith [h1, h2])

lemma apxSa_le (hz : |z| ≤ Z) (hx : |x| ≤ S) :
    |apxSa z x| ≤ S + Z * S ^ 3 / 6 + Z ^ 2 * S ^ 5 / 120 := by
  have e : apxSa z x = 1 * z ^ 0 * x ^ 1 + (1 / 6) * z ^ 1 * x ^ 3 + (1 / 120) * z ^ 2 * x ^ 5 := by
    unfold apxSa; ring
  rw [e]
  have h1 := apx_mono 1 (by norm_num) 0 1 hz hx
  have h2 := apx_mono (1 / 6) (by norm_num) 1 3 hz hx
  have h3 := apx_mono (1 / 120) (by norm_num) 2 5 hz hx
  calc _ ≤ |1 * z ^ 0 * x ^ 1 + (1 / 6) * z ^ 1 * x ^ 3| + |(1 / 120) * z ^ 2 * x ^ 5| := abs_add_le _ _
    _ ≤ |1 * z ^ 0 * x ^ 1| + |(1 / 6) * z ^ 1 * x ^ 3| + |(1 / 120) * z ^ 2 * x ^ 5| := by
        have := abs_add_le (1 * z ^ 0 * x ^ 1) ((1 / 6) * z ^ 1 * x ^ 3); linarith
    _ ≤ _ := by nlinarith [h1, h2, h3]

lemma apxSb_le (hx : |x| ≤ S) : |apxSb x| ≤ S ^ 4 / 12 := by
  have e : apxSb x = (1 / 12) * (1:ℝ) ^ 0 * x ^ 4 := by unfold apxSb; ring
  rw [e]
  have := apx_mono (z := (1:ℝ)) (Z := 1) (1 / 12) (by norm_num) 0 4 (by simp) hx
  nlinarith [this]

lemma apxSb1_le (hx : |x| ≤ S) : |apxSb1 x| ≤ S ^ 3 / 3 := by
  have e : apxSb1 x = (1 / 3) * (1:ℝ) ^ 0 * x ^ 3 := by unfold apxSb1; ring
  rw [e]
  have := apx_mono (z := (1:ℝ)) (Z := 1) (1 / 3) (by norm_num) 0 3 (by simp) hx
  nlinarith [this]

end bounds

/-! ### The skeleton for the polynomials -/

/-- **`𝔄` skeleton for the polynomial truncation.**  For all data with `|ζ| ≤ Z₀`, `|ζ'|,|s±| ≤ S` and the
Taylor remainders `|e±| ≤ Ee h²`, `|γ±| ≤ Γ h²`: `|G₊(Pe + h Po)(s₊) + G₋(Pe + h Po)(s₋) - 2 G₀ Pe(ζ')| ≤ K h²`
with `K` depending only on the bounds. -/
theorem apx_skel_A (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < h → h ≤ 1 → |z0| ≤ Z0 →
      |z2| ≤ B → |G0| ≤ B → |G1| ≤ B → |ep| ≤ Ee * h ^ 2 → |em| ≤ Ee * h ^ 2 →
      |gp| ≤ Γ * h ^ 2 → |gm| ≤ Γ * h ^ 2 → |z1 + h * z2 / 2 + ep| ≤ S →
      |-z1 + h * z2 / 2 + em| ≤ S → |z1| ≤ S →
      |(G0 + h * G1 + gp) * (apxPe z0 (z1 + h * z2 / 2 + ep) + h * apxPo z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apxPe z0 (-z1 + h * z2 / 2 + em) +
          h * apxPo z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apxPe z0 z1| ≤ K * h ^ 2 := by
  refine ⟨B * (2 * (Z0 * S + Z0 ^ 2 * S ^ 3 / 6) * Ee +
      2 * (Z0 + Z0 ^ 2 * S ^ 2 / 2) * (B / 2 + Ee) ^ 2) +
    B * (Z0 * S + Z0 ^ 2 * S ^ 3 / 6) * (B + 2 * Ee) + 2 * Γ * (1 + Z0 * S ^ 2 / 2 + Z0 ^ 2 * S ^ 4 / 24) +
    B * (S ^ 2 / 2 + Z0 * S ^ 4 / 6) * (B + 2 * Ee) + 2 * B * (S ^ 3 / 6 + Z0 * S ^ 5 / 30) +
    2 * Γ * (S ^ 3 / 6 + Z0 * S ^ 5 / 30), ?_, ?_⟩
  · positivity
  · intro h z0 z1 z2 G0 G1 ep em gp gm hh0 hh1 hz0 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1
    exact sk_even_odd (hasDerivAt_apxPe z0) (hasDerivAt_apxPe1 z0) (hasDerivAt_apxPo z0)
      (apxPe_neg z0) (apxPo_neg z0) (fun x hx => apxPe_le hz0 hx) (fun x hx => apxPe1_le hz0 hx)
      (fun x hx => apxPe2_le hz0 hx) (fun x hx => apxPo_le hz0 hx) (fun x hx => apxPo1_le hz0 hx)
      hh0 hh1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1

/-- **`𝔅` skeleton for the polynomial truncation**: `|G₊(Sa + h Sb)(s₊) + G₋(Sa + h Sb)(s₋) - h T| ≤ K h²`
with `T = G₀ ζ'' Pe(ζ') + 2 G₁ Sa(ζ') + 2 G₀ Sb(ζ')`. -/
theorem apx_skel_B (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < h → h ≤ 1 → |z0| ≤ Z0 →
      |z2| ≤ B → |G0| ≤ B → |G1| ≤ B → |ep| ≤ Ee * h ^ 2 → |em| ≤ Ee * h ^ 2 →
      |gp| ≤ Γ * h ^ 2 → |gm| ≤ Γ * h ^ 2 → |z1 + h * z2 / 2 + ep| ≤ S →
      |-z1 + h * z2 / 2 + em| ≤ S → |z1| ≤ S →
      |(G0 + h * G1 + gp) * (apxSa z0 (z1 + h * z2 / 2 + ep) + h * apxSb (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apxSa z0 (-z1 + h * z2 / 2 + em) +
          h * apxSb (-z1 + h * z2 / 2 + em)) -
        h * (G0 * z2 * apxPe z0 z1 + 2 * G1 * apxSa z0 z1 + 2 * G0 * apxSb z1)| ≤ K * h ^ 2 := by
  refine ⟨2 * B * (2 * (1 + Z0 * S ^ 2 / 2 + Z0 ^ 2 * S ^ 4 / 24) * Ee +
      2 * (Z0 * S + Z0 ^ 2 * S ^ 3 / 6) * (B / 2 + Ee) ^ 2) +
    2 * Γ * (S + Z0 * S ^ 3 / 6 + Z0 ^ 2 * S ^ 5 / 120) + 2 * B * (S ^ 3 / 3) * (B / 2 + Ee) +
    2 * B * (S ^ 4 / 12) + 2 * Γ * (S ^ 4 / 12), ?_, ?_⟩
  · positivity
  · intro h z0 z1 z2 G0 G1 ep em gp gm hh0 hh1 hz0 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1
    exact sk_odd_even (hasDerivAt_apxSa z0) (hasDerivAt_apxPe z0) (hasDerivAt_apxSb)
      (apxSa_neg z0) apxSb_neg (fun x hx => apxSa_le hz0 hx) (fun x hx => apxPe_le hz0 hx)
      (fun x hx => apxPe1_le hz0 hx) (fun x hx => apxSb_le hx) (fun x hx => apxSb1_le hx)
      hh0 hh1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1

end FormalResearch.Special

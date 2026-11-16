module

public import FormalResearch.Special.AiryParametrixPoly
public import FormalResearch.Special.AiryParametrixShift
public import FormalResearch.Special.AiryOlverBounds
public import FormalResearch.Special.AiryWt

/-!
# Parametrix defect, part 5: the pointwise estimate

`h = t³`, `X = ζ/t²`.  This file combines the exact shift identity (`AiryShift`), the a priori bounds and Taylor
remainders of `C`, `S` (`AiryParametrixShift`), the parity skeleton for the polynomial truncations
(`AiryParametrixPoly`) and the entire functions `Ch`, `Sh` (`AiryParametrixTaylor`) into the estimate, for
*real data at one lattice point* (no functions of `q` yet):

* `apx_airy_global`: `|Ai x| ≤ 25 airyWt x`, `|Ai' x| ≤ 132500 √(2+|x|) airyWt x` for **all** real `x`
  (Olver's `M/E`, `N/E` bounds of `AiryOlver*` on `x < -1`, `AiryWt` on `x ≥ -1`);
* `apx_PA`: `|G₊C(X,Δ₊) + G₋C(X,Δ₋) - 2G₀ Ch(F)| ≤ K h² (1+|X|)³` (`F = ζζ'²`);
* `apx_PB`: `|G₊S(X,Δ₊) + G₋S(X,Δ₋)| ≤ K h² (1+|X|)²√(1+|X|)`, using the transport identity
  `2G₁ζ'Sh(F) + G₀ζ''(Sh(F) + 2F Sh'(F)) + G₀ζ'⁴ Sh'(F) = 0` (the `q`-derivative of `g²Aζ'Sh(F) = 1`);
* `apx_pointwise`: `|G₊ Ai(X+Δ₊) + G₋ Ai(X+Δ₋) - 2G₀ Ch(F) Ai(X)| ≤ K h² (1+|X|)³ airyWt X`.

`Sh = 2 Ch'` is `langerSinhc`.  All proved; the constants are existential and depend only on the bounds.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-! ### A global bound for `Ai`, `Ai'` against `airyWt` -/

/-- **`Ai` and `Ai'` against `airyWt` on the whole real line**: `|Ai x| ≤ 25 airyWt x`,
`|Ai' x| ≤ 132500 √(2+|x|) airyWt x`. -/
theorem apx_airy_global (x : ℝ) :
    |airyAi x| ≤ 25 * airyWt x ∧ |airyAi' x| ≤ 132500 * √(2 + |x|) * airyWt x := by
  have hw := airyWt_pos x
  have hs : 0 < √(2 + |x|) := Real.sqrt_pos.mpr (by positivity)
  rcases le_or_gt (-1) x with hx | hx
  · have h1 := airyAi_pos_of_neg_one_le hx
    have h2 := airyAi_le_six_airyWt hx
    have h3 := abs_airyAi'_le_airyWt hx
    refine ⟨by rw [abs_of_pos h1]; linarith, ?_⟩
    nlinarith [mul_pos hs hw]
  · -- oscillatory side: Olver's `M/E`, `N/E`
    have hE := one_le_airyOlverE x
    have hM0 := airyOlverM_nonneg x
    have hMsq := (airyOlverM_sq_two_sided x).2
    have hxi : airyXi x = 0 := airyXi_of_nonpos (by linarith)
    have hwt : airyWt x ^ 2 = (√(2 + |x|))⁻¹ := by
      unfold airyWt; rw [hxi]; simp only [neg_zero, Real.exp_zero, mul_one]
      exact rpow_neg_quarter_sq (by positivity)
    have hMw : airyOlverM x ≤ 25 * airyWt x := by
      apply abs_le_of_sq_le_sq' (b := 25 * airyWt x) _ (by positivity) |>.2
      rw [mul_pow, hwt]
      have : 1 / √(2 + |x|) = (√(2 + |x|))⁻¹ := one_div _
      rw [this] at hMsq
      nlinarith [inv_pos.2 hs]
    have hA := abs_airyAi_le_airyOlverM_div_E x
    have hAp := abs_airyAi'_le_airyDerivWeightN_div_E x
    have hN := airyDerivWeightN_le x
    have hE0 : 0 < airyOlverE x := airyOlverE_pos x
    have hDiv : airyOlverM x / airyOlverE x ≤ airyOlverM x :=
      div_le_self hM0 hE
    refine ⟨hA.trans (hDiv.trans hMw), ?_⟩
    have hN0 : 0 ≤ airyDerivWeightN x := by
      have := (abs_nonneg _).trans hAp
      have := (div_nonneg_iff.1 this)
      rcases this with ⟨h, _⟩ | ⟨_, h⟩
      · exact h
      · linarith
    have hDiv2 : airyDerivWeightN x / airyOlverE x ≤ airyDerivWeightN x := div_le_self hN0 hE
    calc |airyAi' x| ≤ airyDerivWeightN x := hAp.trans hDiv2
      _ ≤ 5300 * √(2 + |x|) * airyOlverM x := hN
      _ ≤ 5300 * √(2 + |x|) * (25 * airyWt x) :=
          mul_le_mul_of_nonneg_left hMw (by positivity)
      _ = 132500 * √(2 + |x|) * airyWt x := by ring

/-! ### Rescaling identities and the size of `Λ` -/

lemma apx_P5_rescale {t z0 s : ℝ} (ht : t ≠ 0) :
    1 + (z0 / t ^ 2) * (t * s) ^ 2 / 2 + (t * s) ^ 3 / 6 + (z0 / t ^ 2) ^ 2 * (t * s) ^ 4 / 24 +
      (z0 / t ^ 2) * (t * s) ^ 5 / 30 = apxPe z0 s + t ^ 3 * apxPo z0 s := by
  unfold apxPe apxPo; field_simp; ring

lemma apx_P5S_rescale {t z0 s : ℝ} (ht : t ≠ 0) :
    t * s + (z0 / t ^ 2) * (t * s) ^ 3 / 6 + (t * s) ^ 4 / 12 + (z0 / t ^ 2) ^ 2 * (t * s) ^ 5 / 120 =
      t * (apxSa z0 s + t ^ 3 * apxSb s) := by
  unfold apxSa apxSb; field_simp; ring

/-- `|t s| √(1 + |z0/t²|) ≤ S √(1 + Z₀)` for `0 < t ≤ 1`, `|z0| ≤ Z₀`, `|s| ≤ S`. -/
lemma apx_lambda {t z0 s Z0 S : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hz0 : |z0| ≤ Z0) (hs : |s| ≤ S) :
    |t * s| * √(1 + |z0 / t ^ 2|) ≤ S * √(1 + Z0) := by
  have hZ0 : 0 ≤ Z0 := (abs_nonneg _).trans hz0
  have hS : 0 ≤ S := (abs_nonneg _).trans hs
  have hu : 0 ≤ 1 + |z0 / t ^ 2| := by positivity
  have hsq : (t * √(1 + |z0 / t ^ 2|)) ^ 2 ≤ (√(1 + Z0)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hu, Real.sq_sqrt (by linarith)]
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
    have : t ^ 2 * (1 + |z0| / t ^ 2) = t ^ 2 + |z0| := by field_simp
    rw [this]
    have : t ^ 2 ≤ 1 := by nlinarith
    linarith
  have h1 : t * √(1 + |z0 / t ^ 2|) ≤ √(1 + Z0) :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq hsq (Real.sqrt_nonneg _))
  calc |t * s| * √(1 + |z0 / t ^ 2|) = |s| * (t * √(1 + |z0 / t ^ 2|)) := by
        rw [abs_mul, abs_of_pos ht0]; ring
    _ ≤ S * √(1 + Z0) := mul_le_mul hs h1 (by positivity) hS

lemma apx_sq_small {h Γ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hΓ : 0 ≤ Γ) : Γ * h ^ 2 ≤ Γ := by
  have : h ^ 2 ≤ 1 := pow_le_one₀ hh0.le hh1
  nlinarith

lemma apx_G_bound {h G0 G1 g B Γ σ : ℝ} (hh0 : 0 < h) (hh1 : h ≤ 1) (hG0 : |G0| ≤ B)
    (hG1 : |G1| ≤ B) (hg : |g| ≤ Γ) (hσ : σ = 1 ∨ σ = -1) : |G0 + σ * (h * G1) + g| ≤ 2 * B + Γ := by
  have h1 : |h * G1| ≤ B := by
    rw [abs_mul, abs_of_pos hh0]
    have hB : 0 ≤ B := (abs_nonneg _).trans hG1
    nlinarith [abs_nonneg G1]
  have h2 : |σ * (h * G1)| ≤ B := by
    rcases hσ with rfl | rfl <;> simpa using h1
  calc |G0 + σ * (h * G1) + g| ≤ |G0| + |σ * (h * G1)| + |g| := by
        calc _ ≤ |G0 + σ * (h * G1)| + |g| := abs_add_le _ _
          _ ≤ _ := by linarith [abs_add_le G0 (σ * (h * G1))]
    _ ≤ 2 * B + Γ := by linarith

/-- **`𝔄` bound.**  `|G₊ C(X,Δ₊) + G₋ C(X,Δ₋) - 2 G₀ Ch(F)| ≤ K h² (1+|X|)³` where `X = z0/t²`,
`Δ± = t s±`, `h = t³`, `F = z0 z1²`. -/
theorem apx_PA (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 → t * S ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      |(G0 + t ^ 3 * G1 + gp) * airyShiftC (z0 / t ^ 2) (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftC (z0 / t ^ 2) (t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2)| ≤ K * (t ^ 3) ^ 2 * (1 + |z0 / t ^ 2|) ^ 3 := by
  obtain ⟨K1, hK1, hsk⟩ := apx_skel_A Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  obtain ⟨KC, hKC0, hKC⟩ := langerCosh_taylor (Z0 * S ^ 2)
  set Λ : ℝ := S * √(1 + Z0) with hΛ
  set KR : ℝ := 11 * Real.exp Λ * S ^ 6 with hKR
  have hKR0 : 0 ≤ KR := by positivity
  refine ⟨K1 + 2 * B * KC * S ^ 6 + 2 * (2 * B + Γ) * KR, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 htS hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm
  set h : ℝ := t ^ 3 with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ ht0.le ht1
  have ht0' : t ≠ 0 := ht0.ne'
  set X : ℝ := z0 / t ^ 2 with hX
  set u : ℝ := 1 + |X| with hu
  have hu1 : 1 ≤ u := by have := abs_nonneg X; linarith
  have hsp' : z1 + h * z2 / 2 + ep = z1 + t ^ 3 * z2 / 2 + ep := rfl
  -- the two exact C values
  have hCp := apx_C_taylor (X := X) (s := t * (z1 + h * z2 / 2 + ep)) (Λ := Λ)
    (by rw [abs_mul, abs_of_pos ht0]; nlinarith [abs_nonneg (z1 + h * z2 / 2 + ep)])
    (apx_lambda ht0 ht1 hz0 hsp)
  have hCm := apx_C_taylor (X := X) (s := t * (-z1 + h * z2 / 2 + em)) (Λ := Λ)
    (by rw [abs_mul, abs_of_pos ht0]; nlinarith [abs_nonneg (-z1 + h * z2 / 2 + em)])
    (apx_lambda ht0 ht1 hz0 hsm)
  rw [hX, apx_P5_rescale ht0'] at hCp hCm
  -- remainders
  set ρp : ℝ := airyShiftC X (t * (z1 + h * z2 / 2 + ep)) -
    (apxPe z0 (z1 + h * z2 / 2 + ep) + h * apxPo z0 (z1 + h * z2 / 2 + ep)) with hρp
  set ρm : ℝ := airyShiftC X (t * (-z1 + h * z2 / 2 + em)) -
    (apxPe z0 (-z1 + h * z2 / 2 + em) + h * apxPo z0 (-z1 + h * z2 / 2 + em)) with hρm
  have hρp' : |ρp| ≤ KR * h ^ 2 * u ^ 3 := by
    calc |ρp| ≤ 11 * Real.exp Λ * (1 + |X|) ^ 3 * |t * (z1 + h * z2 / 2 + ep)| ^ 6 := hCp
      _ ≤ 11 * Real.exp Λ * u ^ 3 * (t ^ 6 * S ^ 6) := by
          rw [abs_mul, abs_of_pos ht0, mul_pow]
          gcongr
      _ = KR * h ^ 2 * u ^ 3 := by rw [hKR, hh]; ring
  have hρm' : |ρm| ≤ KR * h ^ 2 * u ^ 3 := by
    calc |ρm| ≤ 11 * Real.exp Λ * (1 + |X|) ^ 3 * |t * (-z1 + h * z2 / 2 + em)| ^ 6 := hCm
      _ ≤ 11 * Real.exp Λ * u ^ 3 * (t ^ 6 * S ^ 6) := by
          rw [abs_mul, abs_of_pos ht0, mul_pow]
          gcongr
      _ = KR * h ^ 2 * u ^ 3 := by rw [hKR, hh]; ring
  -- the Ch remainder
  set F : ℝ := z0 * z1 ^ 2 with hF
  have hFb : |F| ≤ Z0 * S ^ 2 := by
    rw [hF, abs_mul, abs_pow]
    exact mul_le_mul hz0 (pow_le_pow_left₀ (abs_nonneg _) hz1 2) (by positivity) hZ0
  have hChT := (hKC F hFb).1
  have hPeF : apxPe z0 z1 = 1 + F / 2 + F ^ 2 / 24 := by
    unfold apxPe; rw [hF]; ring
  have hF3 : |F| ^ 3 ≤ S ^ 6 * h ^ 2 * u ^ 3 := by
    have hzX : |z0| = t ^ 2 * |X| := by
      rw [hX, abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]; field_simp
    have h1 : |F| = |z0| * z1 ^ 2 := by rw [hF, abs_mul, abs_pow, sq_abs]
    have h2 : |F| ≤ t ^ 2 * |X| * S ^ 2 := by
      rw [h1, hzX]
      have : z1 ^ 2 ≤ S ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg z1) hz1 2; rwa [sq_abs] at this
      exact mul_le_mul_of_nonneg_left this (by positivity)
    calc |F| ^ 3 ≤ (t ^ 2 * |X| * S ^ 2) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) h2 3
      _ = S ^ 6 * h ^ 2 * |X| ^ 3 := by rw [hh]; ring
      _ ≤ S ^ 6 * h ^ 2 * u ^ 3 := by
          gcongr; rw [hu]; linarith
  -- skeleton
  have hskA := hsk h z0 z1 z2 G0 G1 ep em gp gm hh0 hh1 hz0 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1
  -- bounds on `G±`
  have hGp : |G0 + h * G1 + gp| ≤ 2 * B + Γ :=
    apx_G_bound hh0 hh1 hG0 hG1 (hgp.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inl rfl) |> fun h' => by simpa using h'
  have hGm : |G0 - h * G1 + gm| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgm.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inr rfl)
    simpa [sub_eq_add_neg] using this
  -- algebra
  have key : (G0 + h * G1 + gp) * airyShiftC X (t * (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * airyShiftC X (t * (-z1 + h * z2 / 2 + em)) -
        2 * G0 * langerCosh F =
      ((G0 + h * G1 + gp) * (apxPe z0 (z1 + h * z2 / 2 + ep) + h * apxPo z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apxPe z0 (-z1 + h * z2 / 2 + em) +
          h * apxPo z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apxPe z0 z1) +
      2 * G0 * (apxPe z0 z1 - langerCosh F) + (G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm := by
    simp only [hρp, hρm]; ring
  show |_ - 2 * G0 * langerCosh F| ≤ _
  rw [key]
  have e1 : |2 * G0 * (apxPe z0 z1 - langerCosh F)| ≤ 2 * B * KC * S ^ 6 * h ^ 2 * u ^ 3 := by
    rw [abs_mul, abs_mul, abs_two, abs_sub_comm, hPeF]
    have h3 : |langerCosh F - (1 + F / 2 + F ^ 2 / 24)| ≤ KC * (S ^ 6 * h ^ 2 * u ^ 3) :=
      hChT.trans (mul_le_mul_of_nonneg_left hF3 hKC0)
    calc 2 * |G0| * |langerCosh F - (1 + F / 2 + F ^ 2 / 24)|
        ≤ 2 * B * (KC * (S ^ 6 * h ^ 2 * u ^ 3)) :=
          mul_le_mul (by linarith) h3 (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |(G0 + h * G1 + gp) * ρp| ≤ (2 * B + Γ) * KR * h ^ 2 * u ^ 3 := by
    rw [abs_mul]
    calc |G0 + h * G1 + gp| * |ρp| ≤ (2 * B + Γ) * (KR * h ^ 2 * u ^ 3) :=
          mul_le_mul hGp hρp' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e3 : |(G0 - h * G1 + gm) * ρm| ≤ (2 * B + Γ) * KR * h ^ 2 * u ^ 3 := by
    rw [abs_mul]
    calc |G0 - h * G1 + gm| * |ρm| ≤ (2 * B + Γ) * (KR * h ^ 2 * u ^ 3) :=
          mul_le_mul hGm hρm' (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
  have e0 : |(G0 + h * G1 + gp) * (apxPe z0 (z1 + h * z2 / 2 + ep) + h * apxPo z0 (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * (apxPe z0 (-z1 + h * z2 / 2 + em) +
          h * apxPo z0 (-z1 + h * z2 / 2 + em)) - 2 * G0 * apxPe z0 z1| ≤ K1 * h ^ 2 * u ^ 3 := by
    calc _ ≤ K1 * h ^ 2 := hskA
      _ ≤ K1 * h ^ 2 * u ^ 3 := by
          exact le_mul_of_one_le_right (by positivity) hu3
  clear hsk hKC hCp hCm key hskA hρp hρm
  rw [abs_le] at e0 e1 e2 e3 ⊢
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

lemma apx_Fabs {t z0 z1 S : ℝ} (ht0 : 0 < t) (hz1 : |z1| ≤ S) :
    |z0 * z1 ^ 2| ≤ t ^ 2 * |z0 / t ^ 2| * S ^ 2 := by
  have hzX : |z0| = t ^ 2 * |z0 / t ^ 2| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]; field_simp
  rw [abs_mul, abs_pow, hzX]
  have : |z1| ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hz1 2
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **Transport estimate**: from the `q`-derivative of `g² A ζ' Sh(F) = 1`, the `h¹` coefficient
`T = G₀ ζ'' Pe + 2 G₁ Sa + 2 G₀ Sb` of `𝔅` is `O(F)`, `F = ζ ζ'²`. -/
theorem apx_T_bound (Z0 S B : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) :
    ∃ KT : ℝ, 0 ≤ KT ∧ ∀ (z0 z1 z2 G0 G1 : ℝ), |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B →
      |G1| ≤ B →
      2 * G1 * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        G0 * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        G0 * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |G0 * z2 * apxPe z0 z1 + 2 * G1 * apxSa z0 z1 + 2 * G0 * apxSb z1| ≤ KT * |z0 * z1 ^ 2| := by
  obtain ⟨KC, hKC0, hKC⟩ := langerCosh_taylor (Z0 * S ^ 2)
  set W : ℝ := Z0 * S ^ 2 with hW
  set KT : ℝ := KC * (B ^ 2 * W ^ 2 + 2 * B * S * W ^ 2 + B * S ^ 4) with hKT
  have hKT0 : 0 ≤ KT := by positivity
  refine ⟨KT, hKT0, ?_⟩
  intro z0 z1 z2 G0 G1 hz0 hz1 hz2 hG0 hG1 hTR
  set F : ℝ := z0 * z1 ^ 2 with hF
  have hFb : |F| ≤ W := by
    rw [hF, hW, abs_mul, abs_pow]
    exact mul_le_mul hz0 (pow_le_pow_left₀ (abs_nonneg _) hz1 2) (by positivity) hZ0
  obtain ⟨hT2, hT3, hT4⟩ := (fun h' => (⟨h'.2.1, h'.2.2.1, h'.2.2.2⟩ :
    _ ∧ _ ∧ _)) (hKC F hFb)
  set T : ℝ := G0 * z2 * apxPe z0 z1 + 2 * G1 * apxSa z0 z1 + 2 * G0 * apxSb z1 with hT
  have hTexp : T = G0 * z2 * (apxPe z0 z1 - (2 * deriv langerCosh F +
        2 * F * (2 * deriv (deriv langerCosh) F))) +
      2 * G1 * z1 * ((1 + F / 6 + F ^ 2 / 120) - 2 * deriv langerCosh F) +
      G0 * z1 ^ 4 * (1 / 6 - 2 * deriv (deriv langerCosh) F) := by
    have := hTR
    simp only [hT, apxPe, apxSa, apxSb, hF] at this ⊢
    linear_combination this
  have hPeF : apxPe z0 z1 = 1 + F / 2 + F ^ 2 / 24 := by
    unfold apxPe; rw [hF]; ring
  have hF3 : |F| ^ 3 ≤ W ^ 2 * |F| := by
    have : |F| ^ 2 ≤ W ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hFb 2
    calc |F| ^ 3 = |F| ^ 2 * |F| := by ring
      _ ≤ W ^ 2 * |F| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
  have hTb : |T| ≤ KT * |F| := by
    have d1 : |apxPe z0 z1 - (2 * deriv langerCosh F + 2 * F * (2 * deriv (deriv langerCosh) F))| ≤
        KC * |F| ^ 3 := by
      rw [hPeF, abs_sub_comm]
      have := hT4
      convert this using 2; ring
    have d2 : |(1 + F / 6 + F ^ 2 / 120) - 2 * deriv langerCosh F| ≤ KC * |F| ^ 3 := by
      rw [abs_sub_comm]; exact hT2
    have d3 : |1 / 6 - 2 * deriv (deriv langerCosh) F| ≤ KC * |F| := by
      rw [abs_sub_comm]; exact hT3
    rw [hTexp]
    have hz1' : |z1 ^ 4| ≤ S ^ 4 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hz1 4
    have t1 : |G0 * z2 * (apxPe z0 z1 - (2 * deriv langerCosh F +
        2 * F * (2 * deriv (deriv langerCosh) F)))| ≤ B * B * (KC * |F| ^ 3) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hG0 hz2 (abs_nonneg _) hB) d1 (abs_nonneg _) (by positivity)
    have t2 : |2 * G1 * z1 * ((1 + F / 6 + F ^ 2 / 120) - 2 * deriv langerCosh F)| ≤
        2 * B * S * (KC * |F| ^ 3) := by
      rw [abs_mul, abs_mul, abs_mul, abs_two]
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hG1 (by norm_num)) hz1
        (abs_nonneg _) (by positivity)) d2 (abs_nonneg _) (by positivity)
    have t3 : |G0 * z1 ^ 4 * (1 / 6 - 2 * deriv (deriv langerCosh) F)| ≤ B * S ^ 4 * (KC * |F|) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hG0 hz1' (abs_nonneg _) hB) d3 (abs_nonneg _) (by positivity)
    have hKF : KC * |F| ^ 3 ≤ KC * (W ^ 2 * |F|) := mul_le_mul_of_nonneg_left hF3 hKC0
    have a1 := mul_le_mul_of_nonneg_left hKF (mul_nonneg hB hB)
    have a2 := mul_le_mul_of_nonneg_left hKF (by positivity : (0:ℝ) ≤ 2 * B * S)
    calc _ ≤ _ := abs_add_three _ _ _
      _ ≤ B * B * (KC * (W ^ 2 * |F|)) + 2 * B * S * (KC * (W ^ 2 * |F|)) +
          B * S ^ 4 * (KC * |F|) := by linarith
      _ = KT * |F| := by rw [hKT]; ring
  exact hTb

/-- **`𝔅` bound**, using the transport identity `hTR`. -/
theorem apx_PB (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 → t * S ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      2 * G1 * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        G0 * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        G0 * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |(G0 + t ^ 3 * G1 + gp) * airyShiftS (z0 / t ^ 2) (t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyShiftS (z0 / t ^ 2) (t * (-z1 + t ^ 3 * z2 / 2 + em))| ≤
        K * (t ^ 3) ^ 2 * ((1 + |z0 / t ^ 2|) ^ 2 * √(1 + |z0 / t ^ 2|)) := by
  obtain ⟨KB, hKB, hsk⟩ := apx_skel_B Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  obtain ⟨KT, hKT0, hTbound⟩ := apx_T_bound Z0 S B hZ0 hS hB
  set Λ : ℝ := S * √(1 + Z0) with hΛ
  set KR : ℝ := 11 * Real.exp Λ * S ^ 6 with hKR
  have hKR0 : 0 ≤ KR := by positivity
  refine ⟨KT * S ^ 2 + KB + 2 * (2 * B + Γ) * KR, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 htS hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  set h : ℝ := t ^ 3 with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := pow_le_one₀ ht0.le ht1
  have ht0' : t ≠ 0 := ht0.ne'
  set X : ℝ := z0 / t ^ 2 with hX
  set u : ℝ := 1 + |X| with hu
  have hu1 : 1 ≤ u := by have := abs_nonneg X; linarith
  have hr1 : 1 ≤ √u := by rw [Real.one_le_sqrt]; exact hu1
  have hSp := apx_S_taylor (X := X) (s := t * (z1 + h * z2 / 2 + ep)) (Λ := Λ)
    (by rw [abs_mul, abs_of_pos ht0]; nlinarith [abs_nonneg (z1 + h * z2 / 2 + ep)])
    (apx_lambda ht0 ht1 hz0 hsp)
  have hSm := apx_S_taylor (X := X) (s := t * (-z1 + h * z2 / 2 + em)) (Λ := Λ)
    (by rw [abs_mul, abs_of_pos ht0]; nlinarith [abs_nonneg (-z1 + h * z2 / 2 + em)])
    (apx_lambda ht0 ht1 hz0 hsm)
  rw [hX, apx_P5S_rescale ht0'] at hSp hSm
  set ρp : ℝ := airyShiftS X (t * (z1 + h * z2 / 2 + ep)) -
    t * (apxSa z0 (z1 + h * z2 / 2 + ep) + h * apxSb (z1 + h * z2 / 2 + ep)) with hρp
  set ρm : ℝ := airyShiftS X (t * (-z1 + h * z2 / 2 + em)) -
    t * (apxSa z0 (-z1 + h * z2 / 2 + em) + h * apxSb (-z1 + h * z2 / 2 + em)) with hρm
  have hρp' : |ρp| ≤ KR * h ^ 2 * (u ^ 2 * √u) := by
    calc |ρp| ≤ 11 * Real.exp Λ * ((1 + |X|) ^ 2 * √(1 + |X|)) *
          |t * (z1 + h * z2 / 2 + ep)| ^ 6 := hSp
      _ ≤ 11 * Real.exp Λ * (u ^ 2 * √u) * (t ^ 6 * S ^ 6) := by
          rw [abs_mul, abs_of_pos ht0, mul_pow]
          gcongr
      _ = KR * h ^ 2 * (u ^ 2 * √u) := by rw [hKR, hh]; ring
  have hρm' : |ρm| ≤ KR * h ^ 2 * (u ^ 2 * √u) := by
    calc |ρm| ≤ 11 * Real.exp Λ * ((1 + |X|) ^ 2 * √(1 + |X|)) *
          |t * (-z1 + h * z2 / 2 + em)| ^ 6 := hSm
      _ ≤ 11 * Real.exp Λ * (u ^ 2 * √u) * (t ^ 6 * S ^ 6) := by
          rw [abs_mul, abs_of_pos ht0, mul_pow]
          gcongr
      _ = KR * h ^ 2 * (u ^ 2 * √u) := by rw [hKR, hh]; ring
  -- the transport estimate
  set F : ℝ := z0 * z1 ^ 2 with hF
  set T : ℝ := G0 * z2 * apxPe z0 z1 + 2 * G1 * apxSa z0 z1 + 2 * G0 * apxSb z1 with hT
  have hTb : |T| ≤ KT * |F| := hTbound z0 z1 z2 G0 G1 hz0 hz1 hz2 hG0 hG1 hTR
  have hFab : |F| ≤ t ^ 2 * |X| * S ^ 2 := apx_Fabs ht0 hz1
  have hskB := hsk h z0 z1 z2 G0 G1 ep em gp gm hh0 hh1 hz0 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hz1
  rw [← hT] at hskB
  have hGp : |G0 + h * G1 + gp| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgp.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inl rfl)
    simpa using this
  have hGm : |G0 - h * G1 + gm| ≤ 2 * B + Γ := by
    have := apx_G_bound hh0 hh1 hG0 hG1 (hgm.trans (apx_sq_small hh0 hh1 hΓ)) (Or.inr rfl)
    simpa [sub_eq_add_neg] using this
  set Sg : ℝ := (G0 + h * G1 + gp) * (apxSa z0 (z1 + h * z2 / 2 + ep) +
      h * apxSb (z1 + h * z2 / 2 + ep)) +
    (G0 - h * G1 + gm) * (apxSa z0 (-z1 + h * z2 / 2 + em) +
      h * apxSb (-z1 + h * z2 / 2 + em)) with hSg
  have key : (G0 + h * G1 + gp) * airyShiftS X (t * (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * airyShiftS X (t * (-z1 + h * z2 / 2 + em)) =
      t * (h * T) + t * (Sg - h * T) + ((G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm) := by
    simp only [hρp, hρm, hSg]; ring
  show |(G0 + h * G1 + gp) * airyShiftS X (t * (z1 + h * z2 / 2 + ep)) +
        (G0 - h * G1 + gm) * airyShiftS X (t * (-z1 + h * z2 / 2 + em))| ≤ _
  rw [key]
  have hu2 : 1 ≤ u ^ 2 * √u := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hu1) hr1
  have hXu : |X| ≤ u ^ 2 * √u := by
    have h1 : |X| ≤ u := by rw [hu]; linarith
    have h2 : u ≤ u ^ 2 * √u :=
      (le_self_pow₀ hu1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) hr1)
    exact h1.trans h2
  have p1 : |t * (h * T)| ≤ KT * S ^ 2 * h ^ 2 * (u ^ 2 * √u) := by
    rw [abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos hh0]
    have h1 : |T| ≤ KT * (t ^ 2 * |X| * S ^ 2) := hTb.trans (mul_le_mul_of_nonneg_left hFab hKT0)
    calc t * (h * |T|) ≤ t * (h * (KT * (t ^ 2 * |X| * S ^ 2))) := by gcongr
      _ = KT * S ^ 2 * h ^ 2 * |X| := by rw [hh]; ring
      _ ≤ KT * S ^ 2 * h ^ 2 * (u ^ 2 * √u) := by gcongr
  have p2 : |t * (Sg - h * T)| ≤ KB * h ^ 2 * (u ^ 2 * √u) := by
    rw [abs_mul, abs_of_pos ht0]
    calc t * |Sg - h * T| ≤ 1 * (KB * h ^ 2) := mul_le_mul ht1 hskB (abs_nonneg _) (by norm_num)
      _ = KB * h ^ 2 := by ring
      _ ≤ KB * h ^ 2 * (u ^ 2 * √u) := le_mul_of_one_le_right (by positivity) hu2
  have p3 : |(G0 + h * G1 + gp) * ρp + (G0 - h * G1 + gm) * ρm| ≤
      2 * (2 * B + Γ) * KR * h ^ 2 * (u ^ 2 * √u) := by
    calc _ ≤ |(G0 + h * G1 + gp) * ρp| + |(G0 - h * G1 + gm) * ρm| := abs_add_le _ _
      _ ≤ (2 * B + Γ) * (KR * h ^ 2 * (u ^ 2 * √u)) + (2 * B + Γ) * (KR * h ^ 2 * (u ^ 2 * √u)) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul hGp hρp' (abs_nonneg _) (by positivity))
            (mul_le_mul hGm hρm' (abs_nonneg _) (by positivity))
      _ = _ := by ring
  clear hsk hSp hSm key hskB hTbound
  rw [abs_le] at p1 p2 p3 ⊢
  constructor <;> linarith [p1.1, p1.2, p2.1, p2.2, p3.1, p3.2]

/-- The exact shift decomposition `Σ G±Ai(X+Δ±) - c Ai = Ai·𝔄 + Ai'·𝔅`. -/
lemma apx_split (X Dp Dm Gp Gm c : ℝ) :
    Gp * airyAi (X + Dp) + Gm * airyAi (X + Dm) - c * airyAi X =
      airyAi X * (Gp * airyShiftC X Dp + Gm * airyShiftC X Dm - c) +
        airyAi' X * (Gp * airyShiftS X Dp + Gm * airyShiftS X Dm) := by
  rw [airyAi_shift X Dp, airyAi_shift X Dm]; ring

/-- Combination of the `Ai`, `Ai'` bounds with the bounds on `𝔄`, `𝔅`. -/
lemma apx_combine {X Ap Bp KA KB h : ℝ} (_hKA : 0 ≤ KA) (_hKB : 0 ≤ KB)
    (hA : |Ap| ≤ KA * h ^ 2 * (1 + |X|) ^ 3)
    (hB : |Bp| ≤ KB * h ^ 2 * ((1 + |X|) ^ 2 * √(1 + |X|))) :
    |airyAi X * Ap + airyAi' X * Bp| ≤
      (25 * KA + 265000 * KB) * h ^ 2 * (1 + |X|) ^ 3 * airyWt X := by
  set u : ℝ := 1 + |X| with hu
  have hu1 : 1 ≤ u := by have := abs_nonneg X; linarith
  have hr0 : 0 < √u := Real.sqrt_pos.mpr (by linarith)
  have hrr : √u * √u = u := Real.mul_self_sqrt (by linarith)
  obtain ⟨hAi, hAi'⟩ := apx_airy_global X
  have hw := airyWt_pos X
  have hsq : √(2 + |X|) ≤ 2 * √u := by
    have : 2 + |X| ≤ (2 * √u) ^ 2 := by nlinarith [hrr]
    exact Real.sqrt_le_iff.2 ⟨by positivity, this⟩
  have e1 : |airyAi X * Ap| ≤ 25 * KA * h ^ 2 * u ^ 3 * airyWt X := by
    rw [abs_mul]
    calc |airyAi X| * |Ap| ≤ (25 * airyWt X) * (KA * h ^ 2 * u ^ 3) :=
          mul_le_mul hAi hA (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have e2 : |airyAi' X * Bp| ≤ 265000 * KB * h ^ 2 * u ^ 3 * airyWt X := by
    rw [abs_mul]
    have h1 : |airyAi' X| ≤ 265000 * √u * airyWt X := by
      calc |airyAi' X| ≤ 132500 * √(2 + |X|) * airyWt X := hAi'
        _ ≤ 132500 * (2 * √u) * airyWt X := by gcongr
        _ = _ := by ring
    calc |airyAi' X| * |Bp| ≤ (265000 * √u * airyWt X) * (KB * h ^ 2 * (u ^ 2 * √u)) :=
          mul_le_mul h1 hB (abs_nonneg _) (by positivity)
      _ = 265000 * KB * h ^ 2 * (u ^ 2 * (√u * √u)) * airyWt X := by ring
      _ = _ := by rw [hrr]; ring
  calc |airyAi X * Ap + airyAi' X * Bp| ≤ |airyAi X * Ap| + |airyAi' X * Bp| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- **Pointwise defect estimate** (the Airy-level statement for real data at one lattice point):
`|G₊ Ai(X+Δ₊) + G₋ Ai(X+Δ₋) - 2 G₀ Ch(F) Ai(X)| ≤ K h² (1+|X|)³ airyWt(X)`, `h = t³`, `X = z0/t²`,
`Δ± = t s±`, `s± = ±z1 + h z2/2 + e±`, `G± = G₀ ± h G₁ + γ±`, `F = z0 z1²`, given the transport identity
`hTR`. -/
theorem apx_pointwise (Z0 S B Ee Γ : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) (hB : 0 ≤ B) (hEe : 0 ≤ Ee)
    (hΓ : 0 ≤ Γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t z0 z1 z2 G0 G1 ep em gp gm : ℝ), 0 < t → t ≤ 1 → t * S ≤ 1 →
      |z0| ≤ Z0 → |z1| ≤ S → |z2| ≤ B → |G0| ≤ B → |G1| ≤ B →
      |ep| ≤ Ee * (t ^ 3) ^ 2 → |em| ≤ Ee * (t ^ 3) ^ 2 →
      |gp| ≤ Γ * (t ^ 3) ^ 2 → |gm| ≤ Γ * (t ^ 3) ^ 2 →
      |z1 + t ^ 3 * z2 / 2 + ep| ≤ S → |-z1 + t ^ 3 * z2 / 2 + em| ≤ S →
      2 * G1 * z1 * (2 * deriv langerCosh (z0 * z1 ^ 2)) +
        G0 * z2 * (2 * deriv langerCosh (z0 * z1 ^ 2) +
          2 * (z0 * z1 ^ 2) * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2))) +
        G0 * z1 ^ 4 * (2 * deriv (deriv langerCosh) (z0 * z1 ^ 2)) = 0 →
      |(G0 + t ^ 3 * G1 + gp) * airyAi (z0 / t ^ 2 + t * (z1 + t ^ 3 * z2 / 2 + ep)) +
        (G0 - t ^ 3 * G1 + gm) * airyAi (z0 / t ^ 2 + t * (-z1 + t ^ 3 * z2 / 2 + em)) -
        2 * G0 * langerCosh (z0 * z1 ^ 2) * airyAi (z0 / t ^ 2)| ≤
        K * (t ^ 3) ^ 2 * (1 + |z0 / t ^ 2|) ^ 3 * airyWt (z0 / t ^ 2) := by
  obtain ⟨KA, hKA0, hA⟩ := apx_PA Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  obtain ⟨KB, hKB0, hB'⟩ := apx_PB Z0 S B Ee Γ hZ0 hS hB hEe hΓ
  refine ⟨25 * KA + 265000 * KB, by positivity, ?_⟩
  intro t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 htS hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  have hAA := hA t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 htS hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm
  have hBB := hB' t z0 z1 z2 G0 G1 ep em gp gm ht0 ht1 htS hz0 hz1 hz2 hG0 hG1 hep hem hgp hgm hsp hsm hTR
  have hsplit := apx_split (z0 / t ^ 2) (t * (z1 + t ^ 3 * z2 / 2 + ep))
    (t * (-z1 + t ^ 3 * z2 / 2 + em)) (G0 + t ^ 3 * G1 + gp) (G0 - t ^ 3 * G1 + gm)
    (2 * G0 * langerCosh (z0 * z1 ^ 2))
  rw [hsplit]
  exact apx_combine hKA0 hKB0 (by simpa [mul_assoc] using hAA) hBB

end FormalResearch.Special

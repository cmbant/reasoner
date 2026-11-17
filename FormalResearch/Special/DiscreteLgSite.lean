module

public import FormalResearch.Special.DiscreteLgTaylor

/-!
# Discrete Liouville-Green, M2a: the one-site estimates (real algebra)

For the bulk pair `φ_k = w_k cos P_k`, `ψ_k = w_k sin P_k` of a Jacobi row, the row defects reduce to the two combinations
(`Bp = a_{k+1} w_{k+1}/w_k`, `Bm = a_k w_{k-1}/w_k`, `mp, mm` the two phase increments)

* `X₁ = Bp cos mp + Bm cos mm - c_k` (even part: a second difference),
* `X₂ = Bp sin mp - Bm sin mm` (odd part: cancels to second order by the transport equation `2 B₁ sin θ + A θ' cos θ = 0`).

`dlg_X` proves `|X₁|, |X₂| ≤ 35 R⁴ h²` from first-order jets of `Bp, Bm, mp, mm` with `O(h²)` remainders; `dlg_cas_real` is the Casoratian
`a_{k+1} w_k w_{k+1} sin(mp) = 1 + O(h)`.  **Claim class: proved** (real algebra, explicit constants).
-/

@[expose] public section

namespace FormalResearch.Special

lemma dlg_trig (δ : ℝ) : 0 ≤ 1 - Real.cos δ ∧ 1 - Real.cos δ ≤ δ ^ 2 / 2 ∧ |δ - Real.sin δ| ≤ |δ| ^ 3 / 6 :=
  ⟨by linarith [Real.cos_le_one δ], by linarith [Real.one_sub_sq_div_two_le_cos (x := δ)], Real.abs_sub_sin_le δ⟩

lemma dlg_sq_aux {R h d : ℝ} (hd : |d| ≤ 2 * R * h) : d ^ 2 / 2 ≤ 2 * R ^ 2 * h ^ 2 := by
  have : d ^ 2 ≤ (2 * R * h) ^ 2 := by
    rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg _) hd 2
  have e : (2 * R * h) ^ 2 = 4 * R ^ 2 * h ^ 2 := by ring
  linarith

lemma dlg_cu_aux {R h d : ℝ} (hR : 0 < R) (hh : 0 < h) (h1 : h ≤ 1) (hd : |d| ≤ 2 * R * h) :
    |d| ^ 3 / 6 ≤ 2 * R ^ 3 * h ^ 2 := by
  have h3 : |d| ^ 3 ≤ (2 * R * h) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hd 3
  have e : (2 * R * h) ^ 3 = 8 * R ^ 3 * h ^ 3 := by ring
  have h32 : h ^ 3 ≤ h ^ 2 := by
    have : h ^ 3 = h * h ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_left (sq_nonneg h) h1
  have : R ^ 3 * h ^ 3 ≤ R ^ 3 * h ^ 2 := mul_le_mul_of_nonneg_left h32 (pow_pos hR 3).le
  have : 0 ≤ R ^ 3 * h ^ 2 := by positivity
  linarith

/-- Expansion of `cos`, `sin` at the phase increment `h t₁/2 + f` (`|f| ≤ R h²`). -/
lemma dlg_pre {R h t1 fp : ℝ} (hR : 1 ≤ R) (hh : 0 < h) (h1 : h ≤ 1) (ht1 : |t1| ≤ R) (hfp : |fp| ≤ R * h ^ 2) :
    ∃ κ σ : ℝ, Real.cos (h * t1 / 2 + fp) = 1 - κ ∧ Real.sin (h * t1 / 2 + fp) = (h * t1 / 2 + fp) - σ ∧
      |κ| ≤ 2 * R ^ 2 * h ^ 2 ∧ |σ| ≤ 2 * R ^ 3 * h ^ 2 ∧ |h * t1 / 2 + fp| ≤ 2 * R * h := by
  have hR0 : 0 < R := by linarith
  have hh2 : h ^ 2 ≤ h := by
    have : h ^ 2 = h * h := by ring
    rw [this]; exact mul_le_of_le_one_right hh.le h1
  have hht1 : |h * t1 / 2| ≤ R * h / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hh, abs_two]
    have : h * |t1| ≤ h * R := mul_le_mul_of_nonneg_left ht1 hh.le
    linarith
  have hdp : |h * t1 / 2 + fp| ≤ 2 * R * h := by
    refine (abs_add_le _ _).trans ?_
    have : R * h ^ 2 ≤ R * h := mul_le_mul_of_nonneg_left hh2 hR0.le
    have : 0 ≤ R * h := by positivity
    linarith
  obtain ⟨k0, k1, s1⟩ := dlg_trig (h * t1 / 2 + fp)
  refine ⟨1 - Real.cos (h * t1 / 2 + fp), (h * t1 / 2 + fp) - Real.sin (h * t1 / 2 + fp), by ring, by ring, ?_, ?_, hdp⟩
  · rw [abs_of_nonneg k0]; exact k1.trans (dlg_sq_aux hdp)
  · exact s1.trans (dlg_cu_aux hR0 hh h1 hdp)

lemma dlg_Bb {R h A0 B1 ep : ℝ} (hh : 0 < h) (h1 : h ≤ 1) (hR0 : 0 < R) (hA0 : |A0| ≤ R) (hB1 : |B1| ≤ R)
    (hep : |ep| ≤ R * h ^ 2) : |A0 + h * B1 + ep| ≤ 3 * R := by
  have hhB1 : |h * B1| ≤ R := by
    rw [abs_mul, abs_of_pos hh]
    calc h * |B1| ≤ 1 * |B1| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ R := by rw [one_mul]; exact hB1
  have hRh2 : R * h ^ 2 ≤ R := mul_le_of_le_one_right hR0.le (pow_le_one₀ hh.le h1)
  refine (abs_add_le _ _).trans ?_
  have := (abs_add_le A0 (h * B1))
  linarith

lemma dlg_R_pows {R : ℝ} (hR : 1 ≤ R) : R ≤ R ^ 4 ∧ R ^ 2 ≤ R ^ 4 ∧ R ^ 3 ≤ R ^ 4 := by
  have h2 : R ≤ R ^ 2 := by nlinarith
  have h3 : R ^ 2 ≤ R ^ 3 := by nlinarith
  have h4 : R ^ 3 ≤ R ^ 4 := by nlinarith
  exact ⟨h2.trans (h3.trans h4), h3.trans h4, h4⟩

/-- The even combination `X₁ = Bp cos mp + Bm cos mm - c_k` is `O(h²)`. -/
lemma dlg_X1 {R h A0 B1 t0 t1 Bp Bm mp mm ck : ℝ} (hR : 1 ≤ R) (hh : 0 < h) (h1 : h ≤ 1)
    (hA0 : |A0| ≤ R) (hB1 : |B1| ≤ R) (ht1 : |t1| ≤ R)
    (hBp : |Bp - A0 - h * B1| ≤ R * h ^ 2) (hBm : |Bm - A0 + h * B1| ≤ R * h ^ 2)
    (hmp : |mp - t0 - h * t1 / 2| ≤ R * h ^ 2) (hmm : |mm - t0 + h * t1 / 2| ≤ R * h ^ 2)
    (hck : |ck - 2 * A0 * Real.cos t0| ≤ R * h ^ 2) :
    |Bp * Real.cos mp + Bm * Real.cos mm - ck| ≤ 35 * R ^ 4 * h ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hh2' : 0 ≤ h ^ 2 := sq_nonneg h
  have hh3 : h ^ 3 ≤ h ^ 2 := by
    have : h ^ 3 = h * h ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_left hh2' h1
  obtain ⟨R1, R2, R3⟩ := dlg_R_pows hR
  obtain ⟨ep, rfl, hep⟩ : ∃ ep, Bp = A0 + h * B1 + ep ∧ |ep| ≤ R * h ^ 2 := ⟨Bp - A0 - h * B1, by ring, hBp⟩
  obtain ⟨em, rfl, hem⟩ : ∃ em, Bm = A0 - h * B1 + em ∧ |em| ≤ R * h ^ 2 := ⟨Bm - A0 + h * B1, by ring, hBm⟩
  obtain ⟨fp, rfl, hfp⟩ : ∃ fp, mp = t0 + (h * t1 / 2 + fp) ∧ |fp| ≤ R * h ^ 2 := ⟨mp - t0 - h * t1 / 2, by ring, hmp⟩
  obtain ⟨fm, rfl, hfm⟩ : ∃ fm, mm = t0 + (h * (-t1) / 2 + fm) ∧ |fm| ≤ R * h ^ 2 :=
    ⟨mm - t0 + h * t1 / 2, by ring, hmm⟩
  obtain ⟨ee, rfl, hee⟩ : ∃ ee, ck = 2 * A0 * Real.cos t0 + ee ∧ |ee| ≤ R * h ^ 2 := ⟨ck - 2 * A0 * Real.cos t0, by ring, hck⟩
  obtain ⟨κp, σp, hκp, hσp, hκpb, hσpb, hdp⟩ := dlg_pre hR hh h1 ht1 hfp
  obtain ⟨κm, σm, hκm, hσm, hκmb, hσmb, hdm⟩ := dlg_pre hR hh h1 (by rwa [abs_neg]) hfm
  have hBpb := dlg_Bb hh h1 hR0 hA0 hB1 hep
  have hBmb : |A0 - h * B1 + em| ≤ 3 * R := by
    have := dlg_Bb hh h1 hR0 hA0 (by rwa [abs_neg] : |-B1| ≤ R) hem
    simpa [sub_eq_add_neg, mul_neg] using this
  have hht1 : |h * t1 / 2| ≤ R * h / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hh, abs_two]
    have : h * |t1| ≤ h * R := mul_le_mul_of_nonneg_left ht1 hh.le
    linarith
  have hc0 := Real.abs_cos_le_one t0
  have hs0 := Real.abs_sin_le_one t0
  rw [Real.cos_add t0 (h * t1 / 2 + fp), Real.cos_add t0 (h * (-t1) / 2 + fm), hκp, hκm, hσp, hσm]
  have e : (A0 + h * B1 + ep) * (Real.cos t0 * (1 - κp) - Real.sin t0 * ((h * t1 / 2 + fp) - σp)) +
      (A0 - h * B1 + em) * (Real.cos t0 * (1 - κm) - Real.sin t0 * ((h * (-t1) / 2 + fm) - σm)) -
      (2 * A0 * Real.cos t0 + ee) =
        Real.cos t0 * (ep + em) - ee - Real.cos t0 * ((A0 + h * B1 + ep) * κp + (A0 - h * B1 + em) * κm)
        - Real.sin t0 * (h ^ 2 * (t1 * B1)) - Real.sin t0 * ((h * t1 / 2) * (ep - em))
        - Real.sin t0 * ((A0 + h * B1 + ep) * fp + (A0 - h * B1 + em) * fm)
        + Real.sin t0 * ((A0 + h * B1 + ep) * σp + (A0 - h * B1 + em) * σm) := by ring
  rw [e]
  have b1 : |Real.cos t0 * (ep + em)| ≤ 1 * (R * h ^ 2 + R * h ^ 2) :=
    dlg_mul_le hc0 ((abs_add_le _ _).trans (add_le_add hep hem))
  have b2 : |Real.cos t0 * ((A0 + h * B1 + ep) * κp + (A0 - h * B1 + em) * κm)| ≤
      1 * (3 * R * (2 * R ^ 2 * h ^ 2) + 3 * R * (2 * R ^ 2 * h ^ 2)) :=
    dlg_mul_le hc0 ((abs_add_le _ _).trans (add_le_add (dlg_mul_le hBpb hκpb) (dlg_mul_le hBmb hκmb)))
  have b3 : |Real.sin t0 * (h ^ 2 * (t1 * B1))| ≤ 1 * (R ^ 2 * h ^ 2) := by
    refine dlg_mul_le hs0 ?_
    rw [abs_mul, abs_of_nonneg hh2', abs_mul]
    have := mul_le_mul ht1 hB1 (abs_nonneg _) hR0.le
    calc h ^ 2 * (|t1| * |B1|) ≤ h ^ 2 * (R * R) := mul_le_mul_of_nonneg_left this hh2'
      _ = R ^ 2 * h ^ 2 := by ring
  have b4 : |Real.sin t0 * ((h * t1 / 2) * (ep - em))| ≤ 1 * ((R * h / 2) * (R * h ^ 2 + R * h ^ 2)) :=
    dlg_mul_le hs0 (dlg_mul_le hht1 ((abs_sub _ _).trans (add_le_add hep hem)))
  have b5 : |Real.sin t0 * ((A0 + h * B1 + ep) * fp + (A0 - h * B1 + em) * fm)| ≤
      1 * (3 * R * (R * h ^ 2) + 3 * R * (R * h ^ 2)) :=
    dlg_mul_le hs0 ((abs_add_le _ _).trans (add_le_add (dlg_mul_le hBpb hfp) (dlg_mul_le hBmb hfm)))
  have b6 : |Real.sin t0 * ((A0 + h * B1 + ep) * σp + (A0 - h * B1 + em) * σm)| ≤
      1 * (3 * R * (2 * R ^ 3 * h ^ 2) + 3 * R * (2 * R ^ 3 * h ^ 2)) :=
    dlg_mul_le hs0 ((abs_add_le _ _).trans (add_le_add (dlg_mul_le hBpb hσpb) (dlg_mul_le hBmb hσmb)))
  have q1 : R * h ^ 2 ≤ R ^ 4 * h ^ 2 := mul_le_mul_of_nonneg_right R1 hh2'
  have q2 : R ^ 2 * h ^ 2 ≤ R ^ 4 * h ^ 2 := mul_le_mul_of_nonneg_right R2 hh2'
  have q3 : R ^ 3 * h ^ 2 ≤ R ^ 4 * h ^ 2 := mul_le_mul_of_nonneg_right R3 hh2'
  have q4 : R ^ 2 * h ^ 3 ≤ R ^ 2 * h ^ 2 := mul_le_mul_of_nonneg_left hh3 (sq_nonneg R)
  have q5 : R ^ 4 * h ^ 2 ≥ 0 := by positivity
  rw [abs_le] at b1 b2 b3 b4 b5 b6 hee ⊢
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1, b6.2, hee.1, hee.2]

/-- The odd combination `X₂ = Bp sin mp - Bm sin mm` is `O(h²)` by the transport equation `htr`. -/
lemma dlg_X2 {R h A0 B1 t0 t1 Bp Bm mp mm : ℝ} (hR : 1 ≤ R) (hh : 0 < h) (h1 : h ≤ 1)
    (hA0 : |A0| ≤ R) (hB1 : |B1| ≤ R) (ht1 : |t1| ≤ R)
    (hBp : |Bp - A0 - h * B1| ≤ R * h ^ 2) (hBm : |Bm - A0 + h * B1| ≤ R * h ^ 2)
    (hmp : |mp - t0 - h * t1 / 2| ≤ R * h ^ 2) (hmm : |mm - t0 + h * t1 / 2| ≤ R * h ^ 2)
    (htr : 2 * B1 * Real.sin t0 + A0 * t1 * Real.cos t0 = 0) :
    |Bp * Real.sin mp - Bm * Real.sin mm| ≤ 35 * R ^ 4 * h ^ 2 := by
  have hR0 : 0 < R := by linarith
  have hh2' : 0 ≤ h ^ 2 := sq_nonneg h
  have hh3 : h ^ 3 ≤ h ^ 2 := by
    have : h ^ 3 = h * h ^ 2 := by ring
    rw [this]; exact mul_le_of_le_one_left hh2' h1
  obtain ⟨R1, R2, R3⟩ := dlg_R_pows hR
  obtain ⟨ep, rfl, hep⟩ : ∃ ep, Bp = A0 + h * B1 + ep ∧ |ep| ≤ R * h ^ 2 := ⟨Bp - A0 - h * B1, by ring, hBp⟩
  obtain ⟨em, rfl, hem⟩ : ∃ em, Bm = A0 - h * B1 + em ∧ |em| ≤ R * h ^ 2 := ⟨Bm - A0 + h * B1, by ring, hBm⟩
  obtain ⟨fp, rfl, hfp⟩ : ∃ fp, mp = t0 + (h * t1 / 2 + fp) ∧ |fp| ≤ R * h ^ 2 := ⟨mp - t0 - h * t1 / 2, by ring, hmp⟩
  obtain ⟨fm, rfl, hfm⟩ : ∃ fm, mm = t0 + (h * (-t1) / 2 + fm) ∧ |fm| ≤ R * h ^ 2 :=
    ⟨mm - t0 + h * t1 / 2, by ring, hmm⟩
  obtain ⟨κp, σp, hκp, hσp, hκpb, hσpb, hdp⟩ := dlg_pre hR hh h1 ht1 hfp
  obtain ⟨κm, σm, hκm, hσm, hκmb, hσmb, hdm⟩ := dlg_pre hR hh h1 (by rwa [abs_neg]) hfm
  have hBpb := dlg_Bb hh h1 hR0 hA0 hB1 hep
  have hBmb : |A0 - h * B1 + em| ≤ 3 * R := by
    have := dlg_Bb hh h1 hR0 hA0 (by rwa [abs_neg] : |-B1| ≤ R) hem
    simpa [sub_eq_add_neg, mul_neg] using this
  have hht1 : |h * t1 / 2| ≤ R * h / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hh, abs_two]
    have : h * |t1| ≤ h * R := mul_le_mul_of_nonneg_left ht1 hh.le
    linarith
  have hc0 := Real.abs_cos_le_one t0
  have hs0 := Real.abs_sin_le_one t0
  rw [Real.sin_add t0 (h * t1 / 2 + fp), Real.sin_add t0 (h * (-t1) / 2 + fm), hκp, hκm, hσp, hσm]
  have e : (A0 + h * B1 + ep) * (Real.sin t0 * (1 - κp) + Real.cos t0 * ((h * t1 / 2 + fp) - σp)) -
      (A0 - h * B1 + em) * (Real.sin t0 * (1 - κm) + Real.cos t0 * ((h * (-t1) / 2 + fm) - σm)) =
        h * (2 * B1 * Real.sin t0 + A0 * t1 * Real.cos t0) + Real.sin t0 * (ep - em)
        + Real.cos t0 * ((h * t1 / 2) * (ep + em)) + Real.cos t0 * ((A0 + h * B1 + ep) * fp - (A0 - h * B1 + em) * fm)
        - Real.sin t0 * ((A0 + h * B1 + ep) * κp - (A0 - h * B1 + em) * κm)
        - Real.cos t0 * ((A0 + h * B1 + ep) * σp - (A0 - h * B1 + em) * σm) := by ring
  rw [e, htr, mul_zero, zero_add]
  have b1 : |Real.sin t0 * (ep - em)| ≤ 1 * (R * h ^ 2 + R * h ^ 2) :=
    dlg_mul_le hs0 ((abs_sub _ _).trans (add_le_add hep hem))
  have b2 : |Real.cos t0 * ((h * t1 / 2) * (ep + em))| ≤ 1 * ((R * h / 2) * (R * h ^ 2 + R * h ^ 2)) :=
    dlg_mul_le hc0 (dlg_mul_le hht1 ((abs_add_le _ _).trans (add_le_add hep hem)))
  have b3 : |Real.cos t0 * ((A0 + h * B1 + ep) * fp - (A0 - h * B1 + em) * fm)| ≤
      1 * (3 * R * (R * h ^ 2) + 3 * R * (R * h ^ 2)) :=
    dlg_mul_le hc0 ((abs_sub _ _).trans (add_le_add (dlg_mul_le hBpb hfp) (dlg_mul_le hBmb hfm)))
  have b4 : |Real.sin t0 * ((A0 + h * B1 + ep) * κp - (A0 - h * B1 + em) * κm)| ≤
      1 * (3 * R * (2 * R ^ 2 * h ^ 2) + 3 * R * (2 * R ^ 2 * h ^ 2)) :=
    dlg_mul_le hs0 ((abs_sub _ _).trans (add_le_add (dlg_mul_le hBpb hκpb) (dlg_mul_le hBmb hκmb)))
  have b5 : |Real.cos t0 * ((A0 + h * B1 + ep) * σp - (A0 - h * B1 + em) * σm)| ≤
      1 * (3 * R * (2 * R ^ 3 * h ^ 2) + 3 * R * (2 * R ^ 3 * h ^ 2)) :=
    dlg_mul_le hc0 ((abs_sub _ _).trans (add_le_add (dlg_mul_le hBpb hσpb) (dlg_mul_le hBmb hσmb)))
  have q1 : R * h ^ 2 ≤ R ^ 4 * h ^ 2 := mul_le_mul_of_nonneg_right R1 hh2'
  have q2 : R ^ 2 * h ^ 2 ≤ R ^ 4 * h ^ 2 := mul_le_mul_of_nonneg_right R2 hh2'
  have q3 : R ^ 3 * h ^ 2 ≤ R ^ 4 * h ^ 2 := mul_le_mul_of_nonneg_right R3 hh2'
  have q4 : R ^ 2 * h ^ 3 ≤ R ^ 2 * h ^ 2 := mul_le_mul_of_nonneg_left hh3 (sq_nonneg R)
  have q5 : R ^ 4 * h ^ 2 ≥ 0 := by positivity
  rw [abs_le] at b1 b2 b3 b4 b5 ⊢
  constructor <;> linarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2]

/-- **The Casoratian of the pair at one bond**: `a_{k+1} w_k w_{k+1} sin(mp) = 1 + O(h)`, where `A₀ w₀² sin t₀ = 1`. -/
lemma dlg_cas_real {R h A0 w0 wp ap t0 mp : ℝ} (hR : 1 ≤ R) (hA0 : |A0| ≤ R) (hw0 : |w0| ≤ R) (hwp : |wp| ≤ R)
    (hap : |ap - A0| ≤ R * h) (hwd : |wp - w0| ≤ R * h) (hm : |mp - t0| ≤ R * h)
    (hrel : A0 * w0 ^ 2 * Real.sin t0 = 1) : |ap * w0 * wp * Real.sin mp - 1| ≤ 3 * R ^ 4 * h := by
  have hR0 : 0 < R := by linarith
  have hh : 0 ≤ h := by
    by_contra hc; push Not at hc
    have := (abs_nonneg (mp - t0)).trans hm
    nlinarith
  obtain ⟨R1, R2, R3⟩ := dlg_R_pows hR
  have e : ap * w0 * wp * Real.sin mp - 1 =
      (w0 * ((ap - A0) * wp + A0 * (wp - w0))) * Real.sin mp + (A0 * w0 ^ 2) * (Real.sin mp - Real.sin t0) := by
    linear_combination hrel
  rw [e]
  have b1 : |(w0 * ((ap - A0) * wp + A0 * (wp - w0))) * Real.sin mp| ≤ (R * (R * h * R + R * (R * h))) * 1 :=
    dlg_mul_le (dlg_mul_le hw0 ((abs_add_le _ _).trans (add_le_add (dlg_mul_le hap hwp) (dlg_mul_le hA0 hwd))))
      (Real.abs_sin_le_one _)
  have b2 : |(A0 * w0 ^ 2) * (Real.sin mp - Real.sin t0)| ≤ (R * R ^ 2) * (R * h) := by
    refine dlg_mul_le (by rw [abs_mul, abs_pow]; exact mul_le_mul hA0 (pow_le_pow_left₀ (abs_nonneg _) hw0 2) (by positivity) hR0.le)
      ((Real.abs_sin_sub_sin_le _ _).trans hm)
  have q1 : R ^ 3 * h ≤ R ^ 4 * h := mul_le_mul_of_nonneg_right R3 hh
  have q2 : R ^ 4 * h ≥ 0 := by positivity
  refine (abs_add_le _ _).trans ?_
  have : R * (R * h * R + R * (R * h)) * 1 = 2 * (R ^ 3 * h) := by ring
  have : R * R ^ 2 * (R * h) = R ^ 4 * h := by ring
  linarith

end FormalResearch.Special

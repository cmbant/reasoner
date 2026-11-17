module

public import FormalResearch.Special.HermiteKappaInvariant
public import FormalResearch.Special.HermiteKappaWeber

/-!
# Bulk amplitude bound for Weber-type solutions

For a solution `f` of `f'' = (x² - q⁶) f` with `∫_0^x f² ≤ 1` (`WeberData (q^6)`), `q ≥ 4`, the WKB amplitude
`T = w f² + f'²/w`, `w = √(q⁶ - x²)`, satisfies `T ≤ 5` on the bulk `0 ≤ x ≤ x_b`, `x_b² = q⁶ - 100 q²`
(`weber_bulk_T`).  Hence `f² ≤ T/w ≤ 5/√(q⁶ - x²)` there.  Numerically `T ≈ 2/π` (mpmath/numpy scratch check).

Proof (elementary, no Airy function and no WKB error theory): with `M_T = max_{[0,x_b]} T` the second-order invariant `U` of
`HermiteKappaInvariant` shows `T ≥ 0.99 M_T` on the whole bulk; the exact mass identity then gives
`1 ≥ ∫_0^{x_b} f² ≥ 0.24 M_T`.

**Claim class: proved.**  Constants are explicit but not optimised.
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- `w(y) = √(q⁶ - y²)`. -/
noncomputable def bw (q y : ℝ) : ℝ := √(q ^ 6 - y ^ 2)

/-- The end `x_b = √(q⁶ - 100 q²)` of the bulk. -/
noncomputable def bxb (q : ℝ) : ℝ := √(q ^ 6 - 100 * q ^ 2)

lemma mono_of_hd {F F' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hd : ∀ x ∈ Set.Icc a b, HasDerivAt F (F' x) x)
    (h0 : ∀ x ∈ Set.Icc a b, 0 ≤ F' x) : F a ≤ F b := by
  have hm : MonotoneOn F (Set.Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · exact fun x hx => (hd x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [(hd x (interior_subset hx)).deriv]
      exact h0 x (interior_subset hx)
  exact hm (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab) hab

section estimates

lemma T_two_fg_le {w f g : ℝ} (hw : 0 < w) :
    2 * |f * g| ≤ w * f ^ 2 + g ^ 2 / w := by
  have h1 : w * f ^ 2 + g ^ 2 / w - 2 * (f * g) = (w * f - g) ^ 2 / w := by field_simp; ring
  have h2 : w * f ^ 2 + g ^ 2 / w + 2 * (f * g) = (w * f + g) ^ 2 / w := by field_simp; ring
  have h3 : 0 ≤ (w * f - g) ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  have h4 : 0 ≤ (w * f + g) ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  have : |f * g| ≤ (w * f ^ 2 + g ^ 2 / w) / 2 := abs_le.2 ⟨by linarith, by linarith⟩
  linarith

lemma f_sq_le_T {w f g : ℝ} (hw : 0 < w) : f ^ 2 ≤ (w * f ^ 2 + g ^ 2 / w) / w := by
  rw [le_div_iff₀ hw]
  have : 0 ≤ g ^ 2 / w := div_nonneg (sq_nonneg _) hw.le
  nlinarith

end estimates

section numeric

variable {y w q : ℝ}

lemma q4_ge (hq : 4 ≤ q) : 256 ≤ q ^ 4 := by
  have h2 : 16 ≤ q ^ 2 := by nlinarith
  nlinarith


lemma pow_w_ge (hq : 4 ≤ q) (hw : 10 * q ≤ w) (k : ℕ) : (10 * q) ^ k ≤ w ^ k :=
  pow_le_pow_left₀ (by linarith) hw k

lemma n_gam (hq : 4 ≤ q) (hyq : y ≤ q ^ 3) (hw : 10 * q ≤ w) : y / w ^ 3 ≤ 1 / 1000 := by
  have hw0 : 0 < w := by linarith
  rw [div_le_iff₀ (pow_pos hw0 3)]
  have := pow_w_ge hq hw 3
  nlinarith [mul_pow (10 : ℝ) q 3]

lemma n_gam1 (hq : 4 ≤ q) (hy0 : 0 ≤ y) (hyq : y ≤ q ^ 3) (hw : 10 * q ≤ w) :
    invGam1 (fun _ => w) y / w ≤ 1 / 100000 := by
  have hw0 : 0 < w := by linarith
  have h4 := pow_w_ge hq hw 4
  have h6 := pow_w_ge hq hw 6
  have hq0 : 0 < q := by linarith
  have q4 := q4_ge hq
  have e : invGam1 (fun _ => w) y / w = 1 / w ^ 4 + 3 * y ^ 2 / w ^ 6 := by
    simp only [invGam1]; field_simp
  rw [e]
  have a1 : 1 / w ^ 4 ≤ 1 / 1000000 := by
    rw [div_le_div_iff₀ (pow_pos hw0 4) (by norm_num)]
    nlinarith [mul_pow (10 : ℝ) q 4]
  have a2 : 3 * y ^ 2 / w ^ 6 ≤ 3 / 1000000 := by
    rw [div_le_div_iff₀ (pow_pos hw0 6) (by norm_num)]
    have : y ^ 2 ≤ q ^ 6 := by nlinarith [pow_pos hq0 3]
    nlinarith [mul_pow (10 : ℝ) q 6]
  linarith

lemma n_eps (hq : 4 ≤ q) (hy0 : 0 ≤ y) (hyq : y ≤ q ^ 3) (hw : 10 * q ≤ w) :
    invGam (fun _ => w) y / 2 + invGam1 (fun _ => w) y / (2 * w) ≤ 1 / 1000 := by
  have hw0 : 0 < w := by linarith
  have a := n_gam hq hyq hw
  have b := n_gam1 hq hy0 hyq hw
  have e : invGam1 (fun _ => w) y / (2 * w) = invGam1 (fun _ => w) y / w / 2 := by
    field_simp
  rw [e]
  have : invGam (fun _ => w) y = y / w ^ 3 := rfl
  rw [this]
  linarith

lemma n_big (hq : 4 ≤ q) (hw : 10 * q ≤ w) : invBig (q ^ 6) (fun _ => w) y ≤ 1 / 100000 := by
  have hw0 : 0 < w := by linarith
  have h4 := pow_w_ge hq hw 4
  have h6 := pow_w_ge hq hw 6
  have hq0 : 0 < q := by linarith
  have q4 := q4_ge hq
  simp only [invBig]
  have a1 : 9 / 8 / w ^ 4 ≤ 1 / 200000 := by
    rw [div_le_div_iff₀ (pow_pos hw0 4) (by norm_num)]
    nlinarith [mul_pow (10 : ℝ) q 4]
  have a2 : 5 / 4 * q ^ 6 / w ^ 6 ≤ 2 / 1000000 := by
    rw [div_le_div_iff₀ (pow_pos hw0 6) (by norm_num)]
    nlinarith [mul_pow (10 : ℝ) q 6, pow_pos hq0 6]
  linarith

/-- `γ''/(2w) ≤ Γ'`. -/
lemma n_gam2 (hy0 : 0 ≤ y) (hyL : y ^ 2 ≤ L) (hw0 : 0 < w) :
    invGam2 (fun _ => w) y / (2 * w) ≤ 3 * y * (5 * L + 3 * w ^ 2) / (2 * w ^ 8) := by
  have e : invGam2 (fun _ => w) y / (2 * w) = (9 * y * w ^ 2 + 15 * y ^ 3) / (2 * w ^ 8) := by
    simp only [invGam2]; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [mul_nonneg hy0 (sub_nonneg.2 hyL)]

lemma n_gam2_nonneg (hy0 : 0 ≤ y) (hw0 : 0 < w) : 0 ≤ invGam2 (fun _ => w) y := by
  simp only [invGam2]; positivity

lemma n_R {p A f2 : ℝ} (hq : 4 ≤ q) (hy0 : 0 ≤ y) (hyq : y ≤ q ^ 3) (hw : 10 * q ≤ w)
    (hA : 0 ≤ A) (hp : |p| ≤ A / 2) (hf0 : 0 ≤ f2) (hf : f2 ≤ A / w) :
    |-p / (2 * w ^ 2) + y * f2 / (2 * w ^ 4)| ≤ A / 1000 := by
  have hw0 : 0 < w := by linarith
  have hq0 : 0 < q := by linarith
  have q4 := q4_ge hq
  have h2 := pow_w_ge hq hw 2
  have h5 := pow_w_ge hq hw 5
  have h1600 : 1600 ≤ w ^ 2 := by nlinarith [mul_pow (10 : ℝ) q 2]
  have a1 : |-p / (2 * w ^ 2)| ≤ A / 6400 := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * w ^ 2)]
    have := div_le_div₀ (by positivity : 0 ≤ A / 2) hp (by norm_num : (0 : ℝ) < 3200) (by linarith : 3200 ≤ 2 * w ^ 2)
    linarith [show A / 2 / 3200 = A / 6400 by ring]
  have a2 : y * f2 / (2 * w ^ 4) ≤ A / 3000000 := by
    have k : q ^ 3 / (2 * w ^ 5) ≤ 1 / 3000000 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 16 ≤ q ^ 2 := by nlinarith
      have h5' : 100000 * q ^ 5 ≤ w ^ 5 := by nlinarith [mul_pow (10 : ℝ) q 5]
      have : q ^ 5 = q ^ 3 * q ^ 2 := by ring
      nlinarith [pow_pos hq0 3]
    have h1 : y * f2 ≤ q ^ 3 * (A / w) := mul_le_mul hyq hf hf0 (by positivity)
    have h2' : y * f2 / (2 * w ^ 4) ≤ q ^ 3 * (A / w) / (2 * w ^ 4) :=
      div_le_div_of_nonneg_right h1 (by positivity)
    have e : q ^ 3 * (A / w) / (2 * w ^ 4) = A * (q ^ 3 / (2 * w ^ 5)) := by field_simp
    rw [e] at h2'
    have := mul_le_mul_of_nonneg_left k hA
    linarith [show A * (1 / 3000000) = A / 3000000 by ring]
  have a3 : 0 ≤ y * f2 / (2 * w ^ 4) := by positivity
  rw [abs_le]
  have := abs_le.1 a1
  constructor <;> linarith [this.1, this.2]

lemma n_big2 (hq : 4 ≤ q) (hy0 : 0 ≤ y) (hyq : y ≤ q ^ 3) (hw : 10 * q ≤ w) :
    0 ≤ invBig2 (q ^ 3) (1 / (2 * (10 * q) ^ 5)) (fun _ => w) y ∧
    invBig2 (q ^ 3) (1 / (2 * (10 * q) ^ 5)) (fun _ => w) y ≤ 1 / 100000 := by
  have hw0 : 0 < w := by linarith
  have hq0 : 0 < q := by linarith
  have h16 : 16 ≤ q ^ 2 := by nlinarith
  have h5' : 100000 * q ^ 5 ≤ w ^ 5 := by nlinarith [mul_pow (10 : ℝ) q 5, pow_w_ge hq hw 5]
  have e5 : q ^ 5 = q ^ 3 * q ^ 2 := by ring
  simp only [invBig2]
  refine ⟨by positivity, ?_⟩
  have a1 : 2 * q ^ 3 / 5 / w ^ 5 ≤ 1 / 200000 := by
    rw [div_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_pos hq0 3]
  have a2 : 1 / (2 * (10 * q) ^ 5) * y ≤ 1 / 200000 := by
    have : (10 * q) ^ 5 = 100000 * q ^ 5 := by ring
    rw [this, one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [pow_pos hq0 3]
  linarith

end numeric


section bulk

variable {q : ℝ} {f g V : ℝ → ℝ}

lemma bxb_sq (hq : 4 ≤ q) : bxb q ^ 2 = q ^ 6 - 100 * q ^ 2 := by
  unfold bxb
  refine Real.sq_sqrt ?_
  have h4 := q4_ge hq
  have : 0 < q := by linarith
  have : q ^ 6 - 100 * q ^ 2 = q ^ 2 * (q ^ 4 - 100) := by ring
  rw [this]
  exact mul_nonneg (by positivity) (by linarith)

lemma bxb_nonneg (q : ℝ) : 0 ≤ bxb q := Real.sqrt_nonneg _

lemma bxb_ge (hq : 4 ≤ q) : q ^ 3 / 2 ≤ bxb q := by
  have h4 := q4_ge hq
  have hq0 : 0 < q := by linarith
  have : (q ^ 3 / 2) ^ 2 ≤ q ^ 6 - 100 * q ^ 2 := by
    have : q ^ 6 - 100 * q ^ 2 - (q ^ 3 / 2) ^ 2 = q ^ 2 * (3 / 4 * q ^ 4 - 100) := by ring
    have h5 : 0 ≤ q ^ 2 * (3 / 4 * q ^ 4 - 100) := mul_nonneg (by positivity) (by linarith)
    linarith
  unfold bxb
  exact (Real.le_sqrt' (by positivity)).2 this

/-- Facts on a bulk point. -/
lemma bulk_point (hq : 4 ≤ q) {y : ℝ} (hy : y ∈ Set.Icc 0 (bxb q)) :
    0 ≤ y ∧ y ≤ q ^ 3 ∧ 10 * q ≤ bw q y ∧ bw q y ≤ q ^ 3 ∧ bw q y ^ 2 = q ^ 6 - y ^ 2 := by
  have hq0 : 0 < q := by linarith
  obtain ⟨h0, h1⟩ := hy
  have hxb := bxb_sq hq
  have hy2 : y ^ 2 ≤ q ^ 6 - 100 * q ^ 2 := by nlinarith
  have hq2 : 0 < q ^ 2 := by positivity
  have hyq : y ≤ q ^ 3 := by nlinarith [pow_pos hq0 3, pow_pos hq0 2]
  have hw2 : bw q y ^ 2 = q ^ 6 - y ^ 2 := Real.sq_sqrt (by nlinarith)
  refine ⟨h0, hyq, ?_, ?_, hw2⟩
  · have : (10 * q) ^ 2 ≤ q ^ 6 - y ^ 2 := by nlinarith
    exact (Real.le_sqrt' (by positivity)).2 this
  · refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg y]

lemma bw_pos (hq : 4 ≤ q) {y : ℝ} (hy : y ∈ Set.Icc 0 (bxb q)) : 0 < bw q y := by
  have := (bulk_point hq hy).2.2.1
  linarith

lemma invAt_bulk (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) {y : ℝ} (hy : y ∈ Set.Icc 0 (bxb q)) :
    InvAt f g (bw q) y := by
  obtain ⟨-, -, h10, -, hw2⟩ := bulk_point hq hy
  have hwp : 0 < bw q y := by linarith
  refine ⟨h.hf y, ?_, ?_, hwp.ne'⟩
  · refine (h.hg y).congr_deriv ?_
    rw [hw2]; ring
  · have h1 : HasDerivAt (fun y : ℝ => q ^ 6 - y ^ 2) (-(2 * y)) y := by
      have := (hasDerivAt_pow 2 y).const_sub (q ^ 6)
      simpa using this
    have hne : q ^ 6 - y ^ 2 ≠ 0 := by rw [← hw2]; exact pow_ne_zero 2 hwp.ne'
    have := h1.sqrt hne
    refine this.congr_deriv ?_
    have : √(q ^ 6 - y ^ 2) = bw q y := rfl
    rw [this]
    field_simp

/-- **Bulk amplitude bound.**  `T = w f² + f'²/w ≤ 5` on `[0, x_b]` (numerically `T ≈ 2/π`). -/
theorem weber_bulk_T (hq : 4 ≤ q) (h : WeberData (q ^ 6) f g V) :
    ∀ y ∈ Set.Icc 0 (bxb q), invT (bw q) f g y ≤ 5 := by
  have hq0 : 0 < q := by linarith
  have hI : (Set.Icc (0 : ℝ) (bxb q)).Nonempty := ⟨0, le_refl _, bxb_nonneg q⟩
  have hAt : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), InvAt f g (bw q) y := fun y hy => invAt_bulk hq h hy
  have hcont : ContinuousOn (invT (bw q) f g) (Set.Icc 0 (bxb q)) :=
    fun y hy => (hAt y hy).hasDerivAt_T.continuousAt.continuousWithinAt
  obtain ⟨xs, hxs, hmax⟩ := isCompact_Icc.exists_isMaxOn hI hcont
  set A := invT (bw q) f g xs with hA
  have hle : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), invT (bw q) f g y ≤ A := fun y hy => hmax hy
  -- pointwise facts on the bulk
  have hpt := fun y (hy : y ∈ Set.Icc (0 : ℝ) (bxb q)) => bulk_point hq hy
  have hTnn : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), 0 ≤ invT (bw q) f g y := by
    intro y hy
    have := bw_pos hq hy
    simp only [invT]; positivity
  have hAnn : 0 ≤ A := hTnn xs hxs
  have hfg : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), 2 * |f y * g y| ≤ invT (bw q) f g y :=
    fun y hy => T_two_fg_le (bw_pos hq hy)
  have hf2 : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), f y ^ 2 ≤ invT (bw q) f g y / bw q y :=
    fun y hy => f_sq_le_T (bw_pos hq hy)
  -- the corrected invariant is within 1/1000 relative of T
  have hU1 : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q),
      |invU (bw q) f g y - invT (bw q) f g y| ≤ invT (bw q) f g y / 1000 := by
    intro y hy
    obtain ⟨hy0, hyq, h10, hwq, hw2⟩ := hpt y hy
    have hwp := bw_pos hq hy
    have hg0 : 0 ≤ invGam (bw q) y := by simp only [invGam]; positivity
    have hg1 : 0 ≤ invGam1 (bw q) y := by simp only [invGam1]; positivity
    have heps : invGam (bw q) y / 2 + invGam1 (bw q) y / (2 * bw q y) ≤ 1 / 1000 :=
      n_eps hq hy0 hyq h10
    have e1 : invU (bw q) f g y - invT (bw q) f g y =
        -(invGam (bw q) y * (f y * g y)) + invGam1 (bw q) y * f y ^ 2 / 2 := by
      simp only [invU]; ring
    rw [e1]
    have hT := hTnn y hy
    have h2 := hfg y hy
    have h3 := hf2 y hy
    have h4 : invGam (bw q) y * |f y * g y| ≤ invGam (bw q) y * (invT (bw q) f g y / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hg0
    have h5 : invGam1 (bw q) y * f y ^ 2 ≤ invGam1 (bw q) y * (invT (bw q) f g y / bw q y) :=
      mul_le_mul_of_nonneg_left h3 hg1
    have h6 : invGam1 (bw q) y * (invT (bw q) f g y / bw q y) =
        invT (bw q) f g y * (invGam1 (bw q) y / bw q y) := by ring
    have h7 : invT (bw q) f g y * (invGam (bw q) y / 2 + invGam1 (bw q) y / (2 * bw q y)) ≤
        invT (bw q) f g y / 1000 := by
      have := mul_le_mul_of_nonneg_left heps hT
      linarith
    have h8 : invGam1 (bw q) y / (2 * bw q y) = invGam1 (bw q) y / bw q y / 2 := by field_simp
    have h9 := abs_nonneg (f y * g y)
    have hneg : |-(invGam (bw q) y * (f y * g y))| ≤ invGam (bw q) y * |f y * g y| := by
      rw [abs_neg, abs_mul, abs_of_nonneg hg0]
    have hpos : 0 ≤ invGam1 (bw q) y * f y ^ 2 / 2 := by positivity
    rw [abs_le]
    have hl := abs_le.1 hneg
    constructor <;> nlinarith [hl.1, hl.2]
  -- second-order invariance
  have hIcc : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (bxb q) → b ∈ Set.Icc (0 : ℝ) (bxb q) → a ≤ b →
      ∀ x ∈ Set.Icc a b, x ∈ Set.Icc (0 : ℝ) (bxb q) :=
    fun a b ha hb _ x hx => ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  have hU' : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), 0 ≤ invGam2 (bw q) y * f y ^ 2 / 2 ∧
      invGam2 (bw q) y * f y ^ 2 / 2 ≤
        A * (3 * y * (5 * q ^ 6 + 3 * bw q y ^ 2) / (2 * bw q y ^ 8)) := by
    intro y hy
    obtain ⟨hy0, hyq, h10, hwq, hw2⟩ := hpt y hy
    have hwp := bw_pos hq hy
    have hg2 : 0 ≤ invGam2 (bw q) y := n_gam2_nonneg hy0 hwp
    refine ⟨by positivity, ?_⟩
    have hyL : y ^ 2 ≤ q ^ 6 := by nlinarith [pow_pos hq0 3]
    have h1 := n_gam2 (L := q ^ 6) (w := bw q y) hy0 hyL hwp
    have h2 : f y ^ 2 ≤ A / bw q y :=
      (hf2 y hy).trans (div_le_div_of_nonneg_right (hle y hy) hwp.le)
    have h3 : invGam2 (bw q) y * f y ^ 2 / 2 ≤ invGam2 (bw q) y * (A / bw q y) / 2 := by
      have := mul_le_mul_of_nonneg_left h2 hg2
      linarith
    have h4 : invGam2 (bw q) y * (A / bw q y) / 2 = A * (invGam2 (bw q) y / (2 * bw q y)) := by
      field_simp
    have h5 := mul_le_mul_of_nonneg_left h1 hAnn
    have h1' : invGam2 (bw q) y / (2 * bw q y) ≤ 3 * y * (5 * q ^ 6 + 3 * bw q y ^ 2) / (2 * bw q y ^ 8) := h1
    have h5' := mul_le_mul_of_nonneg_left h1' hAnn
    linarith
  have hUm : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (bxb q) → b ∈ Set.Icc (0 : ℝ) (bxb q) → a ≤ b →
      invU (bw q) f g a ≤ invU (bw q) f g b := by
    intro a b ha hb hab
    refine mono_of_hd (F' := fun y => invGam2 (bw q) y * f y ^ 2 / 2) hab (fun x hx => ?_) (fun x hx => ?_)
    · exact (hAt x (hIcc a b ha hb hab x hx)).hasDerivAt_U
    · exact (hU' x (hIcc a b ha hb hab x hx)).1
  have hUG : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (bxb q) → b ∈ Set.Icc (0 : ℝ) (bxb q) → a ≤ b →
      invU (bw q) f g b - invU (bw q) f g a ≤
        A * (invBig (q ^ 6) (bw q) b - invBig (q ^ 6) (bw q) a) := by
    intro a b ha hb hab
    have := mono_of_hd (F := fun y => A * invBig (q ^ 6) (bw q) y - invU (bw q) f g y)
      (F' := fun y => A * (3 * y * (5 * q ^ 6 + 3 * bw q y ^ 2) / (2 * bw q y ^ 8)) -
        invGam2 (bw q) y * f y ^ 2 / 2) hab (fun x hx => ?_) (fun x hx => ?_)
    · beta_reduce at this; linarith
    · exact (((hAt x (hIcc a b ha hb hab x hx)).hasDerivAt_Big (q ^ 6)).const_mul A).sub
        (hAt x (hIcc a b ha hb hab x hx)).hasDerivAt_U
    · have := (hU' x (hIcc a b ha hb hab x hx)).2
      linarith
  have hBig : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), 0 ≤ invBig (q ^ 6) (bw q) y ∧
      invBig (q ^ 6) (bw q) y ≤ 1 / 100000 := by
    intro y hy
    obtain ⟨hy0, hyq, h10, hwq, hw2⟩ := hpt y hy
    have hwp := bw_pos hq hy
    refine ⟨by simp only [invBig]; positivity, ?_⟩
    exact n_big (y := y) hq h10
  -- T is within 1 % of its maximum on the whole bulk
  have hT99 : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), 99 / 100 * A ≤ invT (bw q) f g y := by
    intro y hy
    have u1 := hU1 y hy
    have u2 := hU1 xs hxs
    have u1' := abs_le.1 u1
    have u2' := abs_le.1 u2
    have hTy := hTnn y hy
    have hyA := hle y hy
    rcases le_total y xs with hyx | hxy
    · have := hUG y xs hy hxs hyx
      have b1 := hBig xs hxs
      have b2 := hBig y hy
      have : A * (invBig (q ^ 6) (bw q) xs - invBig (q ^ 6) (bw q) y) ≤ A * (1 / 100000) :=
        mul_le_mul_of_nonneg_left (by linarith [b1.2, b2.1]) hAnn
      nlinarith [hUm y xs hy hxs hyx]
    · have := hUm xs y hxs hy hxy
      nlinarith
  -- the exact mass identity
  set c : ℝ := 99 / 100 * A / (2 * q ^ 3) with hc
  set c2 : ℝ := 1 / (2 * (10 * q) ^ 5) with hc2
  have hF : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), HasDerivAt
      (fun y => V y - invR (bw q) f g y - c * y + A * invBig2 (q ^ 3) c2 (bw q) y)
      (f y ^ 2 - (f y ^ 2 - invT (bw q) f g y / (2 * bw q y) + invRho (bw q) y * f y ^ 2 / 2) - c +
        A * (2 * q ^ 3 * y / bw q y ^ 7 + c2)) y := by
    intro y hy
    have h1 := ((h.hV y).sub (hAt y hy).hasDerivAt_R).sub (((hasDerivAt_id y).const_mul c))
    have h2 := h1.add (((hAt y hy).hasDerivAt_Big2 (q ^ 3) c2).const_mul A)
    refine h2.congr_deriv ?_
    ring
  have hFd : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q),
      0 ≤ f y ^ 2 - (f y ^ 2 - invT (bw q) f g y / (2 * bw q y) + invRho (bw q) y * f y ^ 2 / 2) - c +
        A * (2 * q ^ 3 * y / bw q y ^ 7 + c2) := by
    intro y hy
    obtain ⟨hy0, hyq, h10, hwq, hw2⟩ := hpt y hy
    have hwp := bw_pos hq hy
    have hTy := hT99 y hy
    have ha : c ≤ invT (bw q) f g y / (2 * bw q y) := by
      have h1 : c ≤ 99 / 100 * A / (2 * bw q y) := by
        rw [hc]
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      have h2 : 99 / 100 * A / (2 * bw q y) ≤ invT (bw q) f g y / (2 * bw q y) :=
        div_le_div_of_nonneg_right hTy (by positivity)
      linarith
    have hb1 : 1 / (2 * bw q y ^ 5) ≤ c2 := by
      rw [hc2]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith [pow_w_ge hq h10 5])
    have hb2 : 2 * y ^ 2 / bw q y ^ 7 ≤ 2 * q ^ 3 * y / bw q y ^ 7 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith
    have hf2' : f y ^ 2 ≤ A / bw q y := (hf2 y hy).trans (div_le_div_of_nonneg_right (hle y hy) hwp.le)
    have hrho : 0 ≤ invRho (bw q) y := by simp only [invRho]; positivity
    have hb3 : invRho (bw q) y * f y ^ 2 / 2 ≤ A * (1 / (2 * bw q y ^ 5) + 2 * y ^ 2 / bw q y ^ 7) := by
      have := mul_le_mul_of_nonneg_left hf2' hrho
      have e : invRho (bw q) y * (A / bw q y) / 2 = A * (1 / (2 * bw q y ^ 5) + 2 * y ^ 2 / bw q y ^ 7) := by
        simp only [invRho]; field_simp; ring
      linarith
    have hb4 := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2) hAnn
    have : A * (2 * q ^ 3 * y / bw q y ^ 7 + c2) = A * (c2 + 2 * q ^ 3 * y / bw q y ^ 7) := by ring
    nlinarith
  have hFmono := mono_of_hd (F := fun y => V y - invR (bw q) f g y - c * y + A * invBig2 (q ^ 3) c2 (bw q) y)
    (F' := fun y => f y ^ 2 - (f y ^ 2 - invT (bw q) f g y / (2 * bw q y) + invRho (bw q) y * f y ^ 2 / 2) - c +
        A * (2 * q ^ 3 * y / bw q y ^ 7 + c2)) (bxb_nonneg q) hF hFd
  beta_reduce at hFmono
  -- boundary terms
  have hxb0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (bxb q) := ⟨le_refl _, bxb_nonneg q⟩
  have hxbI : bxb q ∈ Set.Icc (0 : ℝ) (bxb q) := ⟨bxb_nonneg q, le_refl _⟩
  have hRb : ∀ y ∈ Set.Icc (0 : ℝ) (bxb q), |invR (bw q) f g y| ≤ A / 1000 := by
    intro y hy
    obtain ⟨hy0, hyq, h10, hwq, hw2⟩ := hpt y hy
    have hwp := bw_pos hq hy
    have h1 : |f y * g y| ≤ A / 2 := by have := hfg y hy; have := hle y hy; linarith
    exact n_R (p := f y * g y) hq hy0 hyq h10 hAnn h1 (sq_nonneg _)
      ((hf2 y hy).trans (div_le_div_of_nonneg_right (hle y hy) hwp.le))
  have hR0 := abs_le.1 (hRb 0 hxb0)
  have hR1 := abs_le.1 (hRb (bxb q) hxbI)
  have hG0 := n_big2 (y := 0) hq (le_refl _) (by positivity) (hpt 0 hxb0).2.2.1
  have hG1 := n_big2 (y := bxb q) hq (bxb_nonneg q) (by
    have := (hpt _ hxbI).2.1; exact this) (hpt _ hxbI).2.2.1
  have hV1 := h.Vle (bxb q) (bxb_nonneg q)
  have hxbge := bxb_ge hq
  have hcx : 99 / 100 * A / 4 ≤ c * bxb q := by
    have : c * bxb q ≥ c * (q ^ 3 / 2) := mul_le_mul_of_nonneg_left hxbge (by rw [hc]; positivity)
    have e : c * (q ^ 3 / 2) = 99 / 100 * A / 4 := by
      rw [hc]; field_simp; ring
    linarith
  have e0 : invBig2 (q ^ 3) c2 (bw q) 0 = invBig2 (q ^ 3) (1 / (2 * (10 * q) ^ 5)) (fun _ => bw q 0) 0 := rfl
  have e1 : invBig2 (q ^ 3) c2 (bw q) (bxb q) =
      invBig2 (q ^ 3) (1 / (2 * (10 * q) ^ 5)) (fun _ => bw q (bxb q)) (bxb q) := rfl
  rw [h.V0] at hFmono
  have m1 := mul_le_mul_of_nonneg_left hG1.2 hAnn
  have m0 := mul_le_mul_of_nonneg_left hG0.1 hAnn
  rw [e0, e1] at hFmono
  have hAle : A ≤ 5 := by nlinarith [hR0.1, hR0.2, hR1.1, hR1.2]
  intro y hy
  exact (hle y hy).trans hAle


end bulk

end FormalResearch.Special

module

public import FormalResearch.ModularBootstrap.Upper.Window.Product
public import FormalResearch.Special.AiryAsymReal
public import FormalResearch.Special.AiryClarkLabel
public import FormalResearch.Special.AiryZeroSpacing

/-!
# Elementary lower bounds for the Airy function between its zeros (`rem:thmU`, Step (2))

Source: `CFT/notes/n2_ramped_comb.tex`, Lemma U* (`rem:thmU`), Step (2): near `a_n`,
`Ai(u)²/(u - a_n)² ≍ Ai'(a_n)² ≍ n^{1/3}`.  The paper reads this off the Airy asymptotics; here it is derived
from three elementary facts, uniformly in `n ≥ 1`:

* `airyAi'_airyZero_abs_lower`: `|Ai'(a_n)| ≥ c_0 (1 + |a_n|)^{1/4}` (from `airyAi_neg_asymptotic` and
  `airyAi'_neg_asymptotic`);
* `airyZero_abs_two_sided`: `2.3 n^{2/3} ≤ |a_n| ≤ 3 n^{2/3}` for `n ≥ 1`;
* `airy_cell_lower`: on the cell `[a_{n+1}, a_n]` the function `±Ai` is concave (`Ai'' = u Ai`, `u < 0`), so with
  its maximum `m` one gets `|Ai'(a_{n+1})| ≤ |a_{n+1}| · max|Ai| · gap_n` and the chord bound
  `|Ai(u)| ≥ c n^{1/6} min(u - a_{n+1}, a_n - u)`.

All results are proved unconditionally.
-/

@[expose] public section

open Set Filter Topology
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.Special FormalResearch.ModularBootstrap.Upper.Window

lemma neg_airyZero_gt {n : ℕ} (hn : 1 ≤ n) : (233 / 100 : ℝ) < -airyZero n := by
  rcases hn.eq_or_lt with rfl | h1n
  · linarith [airyZero_one.2]
  · linarith [airyZero_lt_of_lt le_rfl h1n, airyZero_one.2]

/-- `|Ai'(a_n)| ≥ c_0 (1 + |a_n|)^{1/4}` for every `n ≥ 1`. -/
theorem airyAi'_airyZero_abs_lower :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ n : ℕ, 1 ≤ n → c₀ * (1 + |airyZero n|) ^ (1 / 4 : ℝ) ≤ |airyAi' (airyZero n)| := by
  refine ⟨7 / 120, by norm_num, fun n hn => ?_⟩
  set y : ℝ := -airyZero n
  have hy_ge : (2.33 : ℝ) < y := by
    have := neg_airyZero_gt hn
    dsimp [y]; linarith
  have hy_pos : 0 < y := by linarith
  have hy3_gt : (9 : ℝ) < y ^ 3 := by
    have := pow_lt_pow_left₀ hy_ge (by norm_num) (by norm_num : 3 ≠ 0)
    linarith [show (9 : ℝ) < 2.33 ^ 3 by norm_num]
  have hy32_gt : (3 : ℝ) < y ^ (3 / 2 : ℝ) := by
    have hsq : (y ^ (3 / 2 : ℝ)) ^ 2 = y ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy_pos.le]; norm_num
    nlinarith [Real.rpow_nonneg hy_pos.le (3 / 2 : ℝ)]
  have hy_neg32 : y ^ (-(3 / 2 : ℝ)) < 1 / 3 := by
    rw [Real.rpow_neg hy_pos.le, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) hy32_gt
  have hpi4 : √π < 2 := by
    rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt Real.pi_pos.le (by norm_num; exact Real.pi_lt_four)
  have hpi_pos : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hy14_pos : 0 < y ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy_pos _
  set θ : ℝ := 2 / 3 * y ^ (3 / 2 : ℝ) - π / 4
  have hAi := airyAi_neg_asymptotic hy_pos
  rw [show airyAi (-y) = 0 by dsimp [y]; rw [neg_neg]; exact airyAi_airyZero n,
    zero_sub, abs_neg, abs_mul, abs_mul, abs_of_pos (div_pos one_pos hpi_pos),
    abs_of_pos (Real.rpow_pos_of_pos hy_pos _)] at hAi
  have hcos_le : |Real.cos θ| ≤ 1 / 2 := by
    have hdiv := div_le_div_of_nonneg_right hAi (Real.rpow_pos_of_pos hy_pos (-(1 / 4 : ℝ))).le
    have hsimp : (1 / √π * y ^ (-(1 / 4 : ℝ)) * |Real.cos θ|) / y ^ (-(1 / 4 : ℝ)) =
        |Real.cos θ| / √π := by
      field_simp [(Real.rpow_pos_of_pos hy_pos (-(1 / 4 : ℝ))).ne']
    rw [hsimp, show (1 / 8 * y ^ (-(7 / 4 : ℝ))) / y ^ (-(1 / 4 : ℝ)) = 1 / 8 * y ^ (-(3 / 2 : ℝ)) by
      rw [mul_div_assoc, ← Real.rpow_sub hy_pos]; norm_num] at hdiv
    nlinarith [(div_le_iff₀ hpi_pos).mp hdiv, hy_neg32, hpi4]
  have hsin_ge : 1 / 2 ≤ |Real.sin θ| := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hcsq : Real.cos θ ^ 2 ≤ 1 / 4 := by
      rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos θ)]
    exact le_of_sq_le_sq (by rw [sq_abs]; linarith) (abs_nonneg _)
  have hAi' := airyAi'_neg_asymptotic hy_pos
  have htri := abs_sub_abs_le_abs_sub (1 / √π * y ^ (1 / 4 : ℝ) * Real.sin θ) (airyAi' (-y))
  rw [abs_sub_comm (1 / √π * y ^ (1 / 4 : ℝ) * Real.sin θ)] at htri
  have hmain_ge : 1 / 4 * y ^ (1 / 4 : ℝ) ≤ |1 / √π * y ^ (1 / 4 : ℝ) * Real.sin θ| := by
    rw [abs_mul, abs_mul, abs_of_pos (div_pos one_pos hpi_pos), abs_of_pos hy14_pos]
    have h1 : 1 / 2 < 1 / √π := by rw [lt_div_iff₀ hpi_pos]; linarith
    calc 1 / 4 * y ^ (1 / 4 : ℝ) = (1 / 2 * y ^ (1 / 4 : ℝ)) * (1 / 2) := by ring
      _ ≤ (1 / √π * y ^ (1 / 4 : ℝ)) * |Real.sin θ| := by gcongr
      _ = 1 / √π * y ^ (1 / 4 : ℝ) * |Real.sin θ| := by ring
  have hrem_le : 2 / 5 * y ^ (-(5 / 4 : ℝ)) ≤ 2 / 15 * y ^ (1 / 4 : ℝ) := by
    rw [show 2 / 5 * y ^ (-(5 / 4 : ℝ)) = (2 / 5 * y ^ (-(3 / 2 : ℝ))) * y ^ (1 / 4 : ℝ) by
      rw [mul_assoc, ← Real.rpow_add hy_pos]; norm_num]
    nlinarith [hy_neg32, hy14_pos]
  have h_y : 7 / 60 * y ^ (1 / 4 : ℝ) ≤ |airyAi' (-y)| := by linarith
  have h_one_add : (1 + |airyZero n|) ^ (1 / 4 : ℝ) ≤ 2 * y ^ (1 / 4 : ℝ) := by
    rw [abs_of_neg (airyZero_neg n)]
    exact (Real.rpow_le_rpow (by positivity) (by linarith : 1 + -airyZero n ≤ 16 * y)
      (by norm_num)).trans_eq
      (by rw [Real.mul_rpow (by norm_num) hy_pos.le, show (16 : ℝ) ^ (1 / 4 : ℝ) = 2 by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul zero_le_two]; norm_num])
  rw [show -y = airyZero n by dsimp [y]; ring] at h_y
  linarith

/-- `2.3 n^{2/3} ≤ |a_n| ≤ 3 n^{2/3}` for every `n ≥ 1`. -/
theorem airyZero_abs_two_sided {n : ℕ} (hn : 1 ≤ n) :
    (23 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ -airyZero n ∧ -airyZero n ≤ 3 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  rcases hn.eq_or_lt with rfl | h1n
  · simp only [Nat.cast_one, Real.one_rpow, mul_one]
    constructor <;> linarith [airyZero_one.1, airyZero_one.2]
  · obtain ⟨h1, h2⟩ := airyZero_abs_bounds (n := n) (by omega)
    have hp : 0 ≤ (n : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    constructor <;> nlinarith

lemma airyZero_abs_ge_pow {n : ℕ} (hn : 1 ≤ n) :
    (23 / 10 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) ≤ |airyZero n| := by
  rw [abs_of_neg (airyZero_neg n)]; exact (airyZero_abs_two_sided hn).1

lemma airyZero_abs_le_pow {n : ℕ} (hn : 1 ≤ n) : |airyZero n| ≤ 3 * (n : ℝ) ^ (2 / 3 : ℝ) := by
  rw [abs_of_neg (airyZero_neg n)]; exact (airyZero_abs_two_sided hn).2

/-! ### The cell lemma -/

section Cell

variable {a b : ℝ}

/-- `Ai` has a fixed sign on the cell `(a_{n+1}, a_n)`: there is `ε = ±1` with `ε Ai > 0` there. -/
lemma exists_sign_cell {n : ℕ} (hn : 1 ≤ n) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ x ∈ Ioo (airyZero (n + 1)) (airyZero n), 0 < ε * airyAi x := by
  set a := airyZero (n + 1)
  set b := airyZero n
  have hab : a < b := airyZero_strictAnti hn
  have hnz : ∀ x ∈ Ioo a b, airyAi x ≠ 0 := by
    intro x hx
    refine airyAi_ne_zero_of_mem_gap (n := n + 1) (by omega) ?_
    rw [mem_airyClarkGap]
    exact ⟨hx.1, Or.inr (by simpa using hx.2)⟩
  have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hcont : Continuous airyAi := continuous_airyAi
  by_cases hpos : 0 < airyAi ((a + b) / 2)
  · refine ⟨1, Or.inl rfl, fun x hx => ?_⟩
    rw [one_mul]
    by_contra hle
    push Not at hle
    have hxne := hnz x hx
    have hneg : airyAi x < 0 := lt_of_le_of_ne hle hxne
    have hivt := intermediate_value_uIcc (a := x) (b := (a + b) / 2) hcont.continuousOn
    have h0 : (0 : ℝ) ∈ uIcc (airyAi x) (airyAi ((a + b) / 2)) := by
      rw [Set.mem_uIcc]; left; exact ⟨hneg.le, hpos.le⟩
    obtain ⟨z, hz, hz0⟩ := hivt h0
    have hz' : z ∈ Ioo a b := by
      rw [Set.mem_uIcc] at hz
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 hm.2⟩
      · exact ⟨lt_of_lt_of_le hm.1 h1, lt_of_le_of_lt h2 hx.2⟩
    exact hnz z hz' hz0
  · have hne := hnz _ hm
    have hneg : airyAi ((a + b) / 2) < 0 := lt_of_le_of_ne (not_lt.mp hpos) hne
    refine ⟨-1, Or.inr rfl, fun x hx => ?_⟩
    by_contra hle
    push Not at hle
    have hxne := hnz x hx
    have hpos' : 0 < airyAi x := by
      have : airyAi x ≥ 0 := by linarith
      exact lt_of_le_of_ne this (Ne.symm hxne)
    have hivt := intermediate_value_uIcc (a := x) (b := (a + b) / 2) hcont.continuousOn
    have h0 : (0 : ℝ) ∈ uIcc (airyAi x) (airyAi ((a + b) / 2)) := by
      rw [Set.mem_uIcc]; right; exact ⟨hneg.le, hpos'.le⟩
    obtain ⟨z, hz, hz0⟩ := hivt h0
    have hz' : z ∈ Ioo a b := by
      rw [Set.mem_uIcc] at hz
      rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 hm.2⟩
      · exact ⟨lt_of_lt_of_le hm.1 h1, lt_of_le_of_lt h2 hx.2⟩
    exact hnz z hz' hz0

/-- **Chord bound on a cell** (concavity of `±Ai`): for `u ∈ [a_{n+1}, a_n]`,
`|Ai'(a_{n+1})| · min(u - a_{n+1}, a_n - u) ≤ |a_{n+1}| · gap_n² · |Ai(u)|`. -/
theorem airy_cell_chord {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu1 : airyZero (n + 1) ≤ u) (hu2 : u ≤ airyZero n) :
    |airyAi' (airyZero (n + 1))| * min (u - airyZero (n + 1)) (airyZero n - u) ≤
      |airyZero (n + 1)| * (airyZero n - airyZero (n + 1)) ^ 2 * |airyAi u| := by
  obtain ⟨ε, hε, hpos⟩ := exists_sign_cell hn
  set a := airyZero (n + 1) with ha
  set b := airyZero n with hb
  have hab : a < b := airyZero_strictAnti hn
  have hb0 : b < 0 := airyZero_neg n
  have habs : |ε| = 1 := by rcases hε with h | h <;> simp [h]
  set f : ℝ → ℝ := fun x => ε * airyAi x with hf
  have hd1 : ∀ x, HasDerivAt f (ε * airyAi' x) x := fun x => (hasDerivAt_airyAi x).const_mul ε
  have hd2 : ∀ x, HasDerivAt (fun x => ε * airyAi' x) (ε * (x * airyAi x)) x := fun x =>
    (hasDerivAt_airyAi' x).const_mul ε
  have hderiv : deriv f = fun x => ε * airyAi' x := funext fun x => (hd1 x).deriv
  have hderiv2 : ∀ x, deriv (deriv f) x = ε * (x * airyAi x) := fun x => by
    rw [hderiv]; exact (hd2 x).deriv
  have hfa : f a = 0 := by simp [hf, ha, airyAi_airyZero]
  have hfb : f b = 0 := by simp [hf, hb, airyAi_airyZero]
  have hfpos : ∀ x ∈ Ioo a b, 0 < f x := fun x hx => hpos x hx
  have hcont : ContinuousOn f (Icc a b) := (continuous_airyAi.const_smul ε).continuousOn
  have hconc : ConcaveOn ℝ (Icc a b) f := by
    refine concaveOn_of_deriv2_nonpos (convex_Icc a b) hcont ?_ ?_ ?_
    · exact fun x _ => (hd1 x).differentiableAt.differentiableWithinAt
    · rw [hderiv]; exact fun x _ => (hd2 x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have : deriv^[2] f x = deriv (deriv f) x := rfl
      rw [this, hderiv2]
      have hx0 : x < 0 := hx.2.trans hb0
      have := hfpos x hx
      simp only [hf] at this
      nlinarith
  obtain ⟨m, hmI, hmax⟩ := isCompact_Icc.exists_isMaxOn (⟨a, left_mem_Icc.2 hab.le⟩ : (Icc a b).Nonempty) hcont
  have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hfm_pos : 0 < f m := lt_of_lt_of_le (hfpos _ hmid) (hmax (Ioo_subset_Icc_self hmid))
  have hm_ab : m ∈ Ioo a b := by
    refine ⟨lt_of_le_of_ne hmI.1 ?_, lt_of_le_of_ne hmI.2 ?_⟩
    · intro h; rw [← h] at hfm_pos; linarith
    · intro h; rw [h] at hfm_pos; linarith
  have hloc : IsLocalMax f m := hmax.isLocalMax (Icc_mem_nhds hm_ab.1 hm_ab.2)
  have hder0 : ε * airyAi' m = 0 := hloc.hasDerivAt_eq_zero (hd1 m)
  -- mean value theorem for `ε Ai'` on `[a, m]`
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope (fun x => ε * airyAi' x)
    (fun x => ε * (x * airyAi x)) hm_ab.1 (fun x _ => (hd2 x).continuousAt.continuousWithinAt)
    (fun x _ => hd2 x)
  have hξab : ξ ∈ Ioo a b := ⟨hξ.1, hξ.2.trans hm_ab.2⟩
  have hξ0 : ξ < 0 := hξab.2.trans hb0
  have hfξ := hfpos ξ hξab
  have hma : 0 < m - a := sub_pos.2 hm_ab.1
  have hkey : ε * airyAi' a = -(ξ * f ξ) * (m - a) := by
    rw [hder0] at hξe
    have : ε * (ξ * airyAi ξ) = ξ * f ξ := by simp only [hf]; ring
    rw [this] at hξe
    field_simp at hξe
    linarith
  have hAip : |airyAi' a| = |ξ| * f ξ * (m - a) := by
    have h1 : |ε * airyAi' a| = |airyAi' a| := by rw [abs_mul, habs, one_mul]
    rw [← h1, hkey, abs_mul, abs_neg, abs_mul, abs_of_pos hfξ, abs_of_pos hma]
  have hfξm : f ξ ≤ f m := hmax (Ioo_subset_Icc_self hξab)
  have hξa : |ξ| ≤ |a| := by
    rw [abs_of_neg hξ0, abs_of_neg (hab.trans hb0)]; linarith [hξab.1]
  have hbound1 : |airyAi' a| ≤ |a| * f m * (b - a) := by
    rw [hAip]
    have h1 : |ξ| * f ξ ≤ |a| * f m := mul_le_mul hξa hfξm hfξ.le (abs_nonneg _)
    have h2 : m - a ≤ b - a := by linarith [hm_ab.2]
    calc |ξ| * f ξ * (m - a) ≤ |a| * f m * (m - a) :=
          mul_le_mul_of_nonneg_right h1 hma.le
      _ ≤ |a| * f m * (b - a) := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- the chord bound
  have hfu : min (u - a) (b - u) * f m ≤ (b - a) * f u := by
    have hu : u ∈ Icc a b := ⟨hu1, hu2⟩
    rcases le_total u m with hum | hmu
    · have h := hconc.2 (left_mem_Icc.2 hab.le) hmI
        (show 0 ≤ 1 - (u - a) / (m - a) by rw [sub_nonneg, div_le_one hma]; linarith)
        (show 0 ≤ (u - a) / (m - a) by exact div_nonneg (by linarith) hma.le) (by ring)
      have hpt : (1 - (u - a) / (m - a)) • a + ((u - a) / (m - a)) • m = u := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [hpt] at h
      simp only [smul_eq_mul, hfa, mul_zero, zero_add] at h
      have h2 : (u - a) / (m - a) * f m ≥ (u - a) / (b - a) * f m := by
        apply mul_le_mul_of_nonneg_right _ hfm_pos.le
        exact div_le_div_of_nonneg_left (by linarith) hma (by linarith [hm_ab.2])
      have h3 : min (u - a) (b - u) * f m ≤ (u - a) * f m :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hfm_pos.le
      have h4 : (u - a) / (b - a) * f m * (b - a) = (u - a) * f m := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right (h2.trans h) (sub_pos.2 hab).le]
    · have hbm : 0 < b - m := sub_pos.2 hm_ab.2
      have h := hconc.2 hmI (right_mem_Icc.2 hab.le)
        (show 0 ≤ 1 - (u - m) / (b - m) by rw [sub_nonneg, div_le_one hbm]; linarith)
        (show 0 ≤ (u - m) / (b - m) by exact div_nonneg (by linarith) hbm.le) (by ring)
      have hpt : (1 - (u - m) / (b - m)) • m + ((u - m) / (b - m)) • b = u := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [hpt] at h
      simp only [smul_eq_mul, hfb, mul_zero, add_zero] at h
      have hc : 1 - (u - m) / (b - m) = (b - u) / (b - m) := by field_simp; ring
      rw [hc] at h
      have h2 : (b - u) / (b - m) * f m ≥ (b - u) / (b - a) * f m := by
        apply mul_le_mul_of_nonneg_right _ hfm_pos.le
        exact div_le_div_of_nonneg_left (by linarith) hbm (by linarith [hm_ab.1])
      have h3 : min (u - a) (b - u) * f m ≤ (b - u) * f m :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hfm_pos.le
      have h4 : (b - u) / (b - a) * f m * (b - a) = (b - u) * f m := by field_simp
      nlinarith [mul_le_mul_of_nonneg_right (h2.trans h) (sub_pos.2 hab).le]
  have hfu_abs : f u ≤ |airyAi u| := by
    have : |f u| = |airyAi u| := by simp only [hf]; rw [abs_mul, habs, one_mul]
    rw [← this]; exact le_abs_self _
  have hgap : 0 < b - a := sub_pos.2 hab
  have hmin : 0 ≤ min (u - a) (b - u) := le_min (by linarith) (by linarith)
  calc |airyAi' a| * min (u - a) (b - u) ≤ |a| * f m * (b - a) * min (u - a) (b - u) :=
        mul_le_mul_of_nonneg_right hbound1 hmin
    _ = |a| * (b - a) * (min (u - a) (b - u) * f m) := by ring
    _ ≤ |a| * (b - a) * ((b - a) * f u) := mul_le_mul_of_nonneg_left hfu (by positivity)
    _ = |a| * (b - a) ^ 2 * f u := by ring
    _ ≤ |a| * (b - a) ^ 2 * |airyAi u| := mul_le_mul_of_nonneg_left hfu_abs (by positivity)

/-- **Cell lemma** (`Ai(u)²/(u - a_n)² ≍ n^{1/3}` near `a_n`, in the form used in `rem:thmU` Step (2)): there is
`c > 0` with `|Ai(u)| ≥ c n^{1/6} min(u - a_{n+1}, a_n - u)` on every cell `[a_{n+1}, a_n]`, `n ≥ 1`. -/
theorem airy_cell_lower : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, airyZero (n + 1) ≤ u → u ≤ airyZero n →
    c * (n : ℝ) ^ (1 / 6 : ℝ) * min (u - airyZero (n + 1)) (airyZero n - u) ≤ |airyAi u| := by
  obtain ⟨c₀, hc₀, hA⟩ := airyAi'_airyZero_abs_lower
  obtain ⟨c₁, c₂, hc₁, hc₂, hgap⟩ := airyGap_bounds_exists
  set C : ℝ := 3 * 2 ^ (2 / 3 : ℝ) * c₂ ^ 2 with hC
  have hCpos : 0 < C := by positivity
  refine ⟨c₀ / C, by positivity, fun n hn u hu1 hu2 => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hchord := airy_cell_chord hn hu1 hu2
  set a := airyZero (n + 1)
  set b := airyZero n
  have hmin : 0 ≤ min (u - a) (b - u) := le_min (by linarith) (by linarith)
  -- `|Ai'(a)| ≥ c₀ n^{1/6}`
  have h1 : (n : ℝ) ^ (1 / 6 : ℝ) ≤ (1 + |a|) ^ (1 / 4 : ℝ) := by
    have h2 : (n : ℝ) ^ (2 / 3 : ℝ) ≤ 1 + |a| := by
      have := airyZero_abs_ge_pow (n := n + 1) (by omega)
      have hmono : (n : ℝ) ^ (2 / 3 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) :=
        Real.rpow_le_rpow hn0.le (by push_cast; linarith) (by norm_num)
      have hp : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      linarith
    calc (n : ℝ) ^ (1 / 6 : ℝ) = ((n : ℝ) ^ (2 / 3 : ℝ)) ^ (1 / 4 : ℝ) := by
          rw [← Real.rpow_mul hn0.le]; norm_num
      _ ≤ (1 + |a|) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity) h2 (by norm_num)
  have hAi' : c₀ * (n : ℝ) ^ (1 / 6 : ℝ) ≤ |airyAi' a| :=
    (mul_le_mul_of_nonneg_left h1 hc₀.le).trans (hA (n + 1) (by omega))
  -- `|a| gap² ≤ C`
  have hgapn : b - a ≤ c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := (hgap n hn).2
  have hgap0 : 0 ≤ b - a := by linarith [airyZero_strictAnti hn]
  have ha3 : |a| ≤ 3 * 2 ^ (2 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ) := by
    have := airyZero_abs_le_pow (n := n + 1) (by omega)
    have hmono : ((n + 1 : ℕ) : ℝ) ^ (2 / 3 : ℝ) ≤ (2 * (n : ℝ)) ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by push_cast; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                            linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) hn0.le] at hmono
    nlinarith
  have hprod : |a| * (b - a) ^ 2 ≤ C := by
    have hg2 : (b - a) ^ 2 ≤ (c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 := pow_le_pow_left₀ hgap0 hgapn 2
    have e : (c₂ * (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 = c₂ ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast ((n : ℝ) ^ (-(1 / 3 : ℝ))) 2, ← Real.rpow_mul hn0.le]
      norm_num
    rw [e] at hg2
    have e2 : (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ)) = 1 := by
      rw [← Real.rpow_add hn0]; norm_num
    calc |a| * (b - a) ^ 2 ≤ (3 * 2 ^ (2 / 3 : ℝ) * (n : ℝ) ^ (2 / 3 : ℝ)) * (c₂ ^ 2 * (n : ℝ) ^ (-(2 / 3 : ℝ))) :=
          mul_le_mul ha3 hg2 (sq_nonneg _) (by positivity)
      _ = C := by rw [hC]; calc _ = 3 * 2 ^ (2 / 3 : ℝ) * c₂ ^ 2 * ((n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ (-(2 / 3 : ℝ))) := by ring
                                _ = _ := by rw [e2, mul_one]
  have key : c₀ * (n : ℝ) ^ (1 / 6 : ℝ) * min (u - a) (b - u) ≤ C * |airyAi u| := by
    calc c₀ * (n : ℝ) ^ (1 / 6 : ℝ) * min (u - a) (b - u) ≤ |airyAi' a| * min (u - a) (b - u) :=
          mul_le_mul_of_nonneg_right hAi' hmin
      _ ≤ |a| * (b - a) ^ 2 * |airyAi u| := hchord
      _ ≤ C * |airyAi u| := mul_le_mul_of_nonneg_right hprod (abs_nonneg _)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hCpos]
  linarith

/-- **Nearest zero**: for `u ∈ [a_{n+1}, a_n]` there is `k ∈ {n, n+1}` with
`|Ai(u)| ≥ c k^{1/6} |u - a_k|`. -/
theorem airy_nearest_zero : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ u : ℝ, airyZero (n + 1) ≤ u → u ≤ airyZero n →
    ∃ k : ℕ, (k = n ∨ k = n + 1) ∧ c * (k : ℝ) ^ (1 / 6 : ℝ) * |u - airyZero k| ≤ |airyAi u| := by
  obtain ⟨c, hc, h⟩ := airy_cell_lower
  refine ⟨c / 2, by positivity, fun n hn u hu1 hu2 => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcell := h n hn u hu1 hu2
  have hpow : (n : ℝ) ^ (1 / 6 : ℝ) ≥ ((n + 1 : ℕ) : ℝ) ^ (1 / 6 : ℝ) / 2 := by
    have h2 : ((n + 1 : ℕ) : ℝ) ^ (1 / 6 : ℝ) ≤ (2 * (n : ℝ)) ^ (1 / 6 : ℝ) :=
      Real.rpow_le_rpow (by positivity) (by push_cast; have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                            linarith) (by norm_num)
    rw [Real.mul_rpow (by norm_num) hn0.le] at h2
    have h3 : (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 6 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hp : 0 ≤ (n : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hn0.le _
    nlinarith
  rcases le_total (u - airyZero (n + 1)) (airyZero n - u) with hle | hle
  · refine ⟨n + 1, Or.inr rfl, ?_⟩
    rw [min_eq_left hle] at hcell
    have e : |u - airyZero (n + 1)| = u - airyZero (n + 1) := abs_of_nonneg (by linarith)
    rw [e]
    have hd : 0 ≤ u - airyZero (n + 1) := by linarith
    calc c / 2 * ((n + 1 : ℕ) : ℝ) ^ (1 / 6 : ℝ) * (u - airyZero (n + 1))
        ≤ c * (n : ℝ) ^ (1 / 6 : ℝ) * (u - airyZero (n + 1)) := by
          apply mul_le_mul_of_nonneg_right _ hd; nlinarith
      _ ≤ _ := hcell
  · refine ⟨n, Or.inl rfl, ?_⟩
    rw [min_eq_right hle] at hcell
    have e : |u - airyZero n| = airyZero n - u := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    rw [e]
    have hd : 0 ≤ airyZero n - u := by linarith
    calc c / 2 * (n : ℝ) ^ (1 / 6 : ℝ) * (airyZero n - u)
        ≤ c * (n : ℝ) ^ (1 / 6 : ℝ) * (airyZero n - u) := by
          apply mul_le_mul_of_nonneg_right _ hd
          have : 0 ≤ (n : ℝ) ^ (1 / 6 : ℝ) := Real.rpow_nonneg hn0.le _
          nlinarith
      _ ≤ _ := hcell

end Cell

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.airyAi'_airyZero_abs_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyAi'_airyZero_abs_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.airy_cell_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_cell_lower

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.airy_nearest_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airy_nearest_zero

end FormalResearch.ModularBootstrap.Upper.Ramped

module

public import FormalResearch.Special.HermiteKappaSites
public import FormalResearch.Special.HermiteKappaLowerX
public import FormalResearch.Special.HermiteKappaUpper

/-!
# Lower bound on the Airy amplitude `κ` of the Hermite chain

The Weber (`x`-variable) side gives `T = w φ_n² + φ_n'²/w ≥ 9/50` at `x ≤ x_b(q)` (`weber_T_lower`).  At the site `k₀ = m - L`
(`HermiteKappaSites`) the index `n = -k₀` is such that `x` lies in the bulk with `w = √(2n+1-x²) ∈ [9 s, 15 s]`, `s = x^{1/3}`;
the chain (`n`-variable) side expresses `φ_n(x), φ_n'(x)` through `Y_{k₀}, Y_{k₀±1}` (ladder) and these through the Airy
decomposition of `HkEdge` with `X ∈ [-102 c₂, 0]`, bounded by `s · R (|κ| + |μ|)²`.  With `μ² s → 0` this gives
`κ² x^{1/3} ≥ c_κ`, so `κ² ≍ x^{-1/3} ≍ √δ` (`hermite_kappa_order`).

**Claim class: proved.**
-/

@[expose] public section

open Real Filter Topology FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `s = x^{1/3}`, `δ³ = 2/x²`: `s³ = x`, `1 ≤ δ s² ≤ 2`, and `1 ≤ s` when `x ≥ 1`. -/
lemma hk_delta_s {x δ : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδx : δ ^ 3 = 2 / x ^ 2) :
    (x ^ (1 / 3 : ℝ)) ^ 3 = x ∧ 1 ≤ δ * (x ^ (1 / 3 : ℝ)) ^ 2 ∧ δ * (x ^ (1 / 3 : ℝ)) ^ 2 ≤ 2 := by
  set s : ℝ := x ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx _
  have hs3 : s ^ 3 = x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  refine ⟨hs3, ?_⟩
  have ht0 : 0 < δ * s ^ 2 := by positivity
  have ht3 : (δ * s ^ 2) ^ 3 = 2 := by
    have : x ^ 2 ≠ 0 := by positivity
    have e : (δ * s ^ 2) ^ 3 = δ ^ 3 * x ^ 2 := by rw [← hs3]; ring
    rw [e, hδx]; field_simp
  constructor
  · by_contra h
    push Not at h
    have := pow_lt_one₀ ht0.le h (by norm_num : (3 : ℕ) ≠ 0)
    linarith
  · by_contra h
    push Not at h
    have := one_lt_pow₀ (by linarith : (1 : ℝ) < δ * s ^ 2) (by norm_num : (3 : ℕ) ≠ 0)
    nlinarith [pow_lt_pow_left₀ h (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (3 : ℕ) ≠ 0)]

lemma hk_cube_aux {u : ℝ} (hu : 400 ≤ u) : 200 * u + 2 ≤ 2 * u ^ 3 := by
  have h1 : 400 * u ≤ u ^ 2 := by nlinarith
  have h2 : 400 * u ^ 2 ≤ u ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ u)]
  nlinarith

/-- **Weber side**: at the lattice index `n` with `x² + 2L - 2 < 2n+1 ≤ x² + 2L`, `L ≈ 100/δ`, the point `x` lies in the bulk, so
`T = w φ_n² + φ_n'²/w ≥ 9/50` with `w = √(2n+1-x²) ∈ [9 s, 15 s]`, `s = x^{1/3}`. -/
lemma hk_weber_side {n : ℕ} {x δ : ℝ} {L : ℕ} (hx : 0 < x) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 400)
    (hδx : δ ^ 3 = 2 / x ^ 2) (hL1 : 100 / δ ≤ (L : ℝ)) (hL2 : (L : ℝ) ≤ 100 / δ + 1)
    (hn1 : x ^ 2 + 2 * (L : ℝ) - 2 < 2 * (n : ℝ) + 1) (hn2 : 2 * (n : ℝ) + 1 ≤ x ^ 2 + 2 * (L : ℝ)) :
    9 / 50 ≤ √(2 * (n : ℝ) + 1 - x ^ 2) * hermitePhi n x ^ 2 + hkDer n x ^ 2 / √(2 * (n : ℝ) + 1 - x ^ 2) ∧
      9 * x ^ (1 / 3 : ℝ) ≤ √(2 * (n : ℝ) + 1 - x ^ 2) ∧ √(2 * (n : ℝ) + 1 - x ^ 2) ≤ 15 * x ^ (1 / 3 : ℝ) := by
  obtain ⟨hs3, hs1, hs2⟩ := hk_delta_s hx hδ hδx
  set s : ℝ := x ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx _
  set lam : ℝ := 2 * (n : ℝ) + 1 with hlam
  set d : ℝ := lam - x ^ 2 with hd
  have hx2 : x ^ 2 = 2 / δ ^ 3 := by rw [hδx]; field_simp
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hxδ : δ ^ 3 * x ^ 2 = 2 := by rw [hx2]; field_simp
  -- `s² ≥ 400`
  have hs400 : 400 ≤ s ^ 2 := by
    have h1 : 1 / δ ≤ s ^ 2 := by
      rw [div_le_iff₀ hδ]; linarith
    have h2 : (400 : ℝ) ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]; linarith
    linarith
  -- `100/δ`-bounds on `d`
  have hinv1 : s ^ 2 / 2 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ]; linarith
  have hinv2 : 1 / δ ≤ s ^ 2 := by
    rw [div_le_iff₀ hδ]; linarith
  have hd1 : 200 / δ - 2 < d := by
    have : 200 / δ = 2 * (100 / δ) := by ring
    rw [hd, hlam]; linarith
  have hd2 : d ≤ 200 / δ + 2 := by
    have : 200 / δ = 2 * (100 / δ) := by ring
    rw [hd, hlam]; linarith
  have e200 : 200 / δ = 200 * (1 / δ) := by ring
  have hdlo : 81 * s ^ 2 ≤ d := by nlinarith
  have hdhi : d ≤ 225 * s ^ 2 := by nlinarith
  have hw1 : 9 * s ≤ √d := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith
  have hw2 : √d ≤ 15 * s := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    nlinarith
  refine ⟨?_, hw1, hw2⟩
  -- the bulk condition
  have hd0 : 0 < d := by nlinarith
  set q : ℝ := lam ^ (1 / 6 : ℝ) with hq
  have hlam0 : 0 < lam := by
    have : 0 ≤ x ^ 2 := by positivity
    linarith
  have hq0 : 0 < q := Real.rpow_pos_of_pos hlam0 _
  have hq6 : q ^ 6 = lam := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hlam0.le]; norm_num
  have hlam_ge : 20 ^ 6 ≤ lam := by
    have : x ^ 2 = 2 / δ ^ 3 := hx2
    have h1 : (400 : ℝ) ^ 3 ≤ 1 / δ ^ 3 := by
      rw [le_div_iff₀ hδ3]
      have : δ ^ 3 ≤ (1 / 400) ^ 3 := pow_le_pow_left₀ hδ.le hδ4 3
      have h2 : (400 : ℝ) ^ 3 * (1 / 400) ^ 3 = 1 := by norm_num
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 400) 3]
    have h3 : 2 * 400 ^ 3 ≤ x ^ 2 := by
      rw [hx2]
      have : 2 / δ ^ 3 = 2 * (1 / δ ^ 3) := by ring
      rw [this]; linarith
    have : 20 ^ 6 ≤ x ^ 2 := by norm_num at h3 ⊢; linarith
    linarith
  have hq20 : 20 ≤ q := by
    by_contra h
    push Not at h
    have := pow_lt_pow_left₀ h hq0.le (by norm_num : (6 : ℕ) ≠ 0)
    linarith
  -- `100 q² ≤ d` via cubes
  have hlam_le : lam ≤ 4 / δ ^ 3 := by
    have h2L : 2 * (L : ℝ) ≤ x ^ 2 := by
      have : 2 * (L : ℝ) ≤ 200 / δ + 2 := by
        have : 200 / δ = 2 * (100 / δ) := by ring
        linarith
      have h3 : 200 / δ + 2 ≤ 2 / δ ^ 3 := by
        have e : 2 / δ ^ 3 = 2 * (1 / δ) ^ 3 := by field_simp
        have h400 : (400 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
        rw [e, e200]
        exact hk_cube_aux h400
      rw [hx2]; linarith
    have : 4 / δ ^ 3 = 2 * (2 / δ ^ 3) := by ring
    rw [this, ← hx2]; linarith
  have hd190 : 190 / δ ≤ d := by
    have : 200 / δ = 200 * (1 / δ) := by ring
    have : 190 / δ = 190 * (1 / δ) := by ring
    have h400 : (400 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have hcube : (100 * q ^ 2) ^ 3 ≤ d ^ 3 := by
    have e1 : (100 * q ^ 2) ^ 3 = 10 ^ 6 * lam := by rw [mul_pow, ← hq6]; ring
    have e2 : (190 / δ) ^ 3 = 190 ^ 3 / δ ^ 3 := by rw [div_pow]
    have h1 : (190 / δ) ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ (by positivity) hd190 3
    rw [e1]
    refine le_trans ?_ h1
    rw [e2]
    have : 10 ^ 6 * lam ≤ 10 ^ 6 * (4 / δ ^ 3) := by gcongr
    refine this.trans ?_
    rw [← mul_div_assoc, div_le_div_iff_of_pos_right hδ3]
    norm_num
  have hqd : 100 * q ^ 2 ≤ d := le_of_pow_le_pow_left₀ (by norm_num) hd0.le hcube
  have hxb : x ∈ Set.Icc 0 (bxb q) := by
    refine ⟨hx.le, Real.le_sqrt_of_sq_le ?_⟩
    rw [hq6]
    have : x ^ 2 = lam - d := by rw [hd]; ring
    nlinarith
  have hW := weber_T_lower hq20 (by rw [hq6]; exact hermite_weberData n) (hermite_V_tendsto n) x hxb
  unfold invT bw at hW
  rw [hq6] at hW
  exact hW

/-- Compactness constants on `[-c, 0]` for a `C¹` function: a sup bound and a Lipschitz constant. -/
lemma hk_compact {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : Continuous F') (c : ℝ) :
    ∃ B0 B1 : ℝ, 0 ≤ B0 ∧ 0 ≤ B1 ∧ (∀ x ∈ Set.Icc (-c) 0, |F x| ≤ B0) ∧
      ∀ x ∈ Set.Icc (-c) 0, ∀ y ∈ Set.Icc (-c) 0, |F x - F y| ≤ B1 * |x - y| := by
  have hcF : Continuous F := continuous_iff_continuousAt.2 fun y => (hF y).continuousAt
  obtain ⟨B0, hB0⟩ := (isCompact_Icc (a := -c) (b := 0)).exists_bound_of_continuousOn hcF.continuousOn
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := -c) (b := 0)).exists_bound_of_continuousOn hF'.continuousOn
  refine ⟨max B0 0, max B1 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
  · intro x hx
    have := hB0 x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · intro x hx y hy
    have hK : ∀ t ∈ Set.Icc (-c) 0, ‖F' t‖ ≤ max B1 0 := fun t ht => (hB1 t ht).trans (le_max_left _ _)
    have := (convex_Icc (-c) (0 : ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t _ => (hF t).hasDerivWithinAt) hK hy hx
    simpa [Real.norm_eq_abs] using this

/-- Airy constants on `[-c, 0]`: sup bounds `A0, B0` of `Ai, Bi` and Lipschitz constants `A1, B1`. -/
lemma hk_airy_compact (c : ℝ) : ∃ A0 A1 B0 B1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧ 0 ≤ B0 ∧ 0 ≤ B1 ∧
    (∀ x ∈ Set.Icc (-c) 0, |airyAi x| ≤ A0) ∧
    (∀ x ∈ Set.Icc (-c) 0, ∀ y ∈ Set.Icc (-c) 0, |airyAi x - airyAi y| ≤ A1 * |x - y|) ∧
    (∀ x ∈ Set.Icc (-c) 0, |airyBi x| ≤ B0) ∧
    (∀ x ∈ Set.Icc (-c) 0, ∀ y ∈ Set.Icc (-c) 0, |airyBi x - airyBi y| ≤ B1 * |x - y|) := by
  obtain ⟨A0, A1, hA0, hA1, hAs, hAl⟩ := hk_compact hasDerivAt_airyAi
    (continuous_iff_continuousAt.2 fun y => (hasDerivAt_airyAi' y).continuousAt) c
  obtain ⟨B0, B1, hB0, hB1, hBs, hBl⟩ := hk_compact hasDerivAt_airyBi
    (continuous_iff_continuousAt.2 fun y => (hasDerivAt_airyBiDeriv y).continuousAt) c
  exact ⟨A0, A1, B0, B1, hA0, hA1, hB0, hB1, hAs, hAl, hBs, hBl⟩

/-- Size of `Y` at a site from the Airy decomposition. -/
lemma hk_site_up {κ μ Y g Ai Bi C δ3 gmax A0 B0 W Wb : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ gmax) (hA : |Ai| ≤ A0)
    (hB : |Bi| ≤ B0) (hW : W ≤ 1) (hWb : Wb ≤ 1) (hC : 0 ≤ C) (hδ0 : 0 ≤ δ3) (hδ1 : δ3 ≤ 1)
    (hY : |Y - (κ * (g * Ai) + μ * (g * Bi))| ≤ C * δ3 * (|κ| * W + |μ| * Wb)) :
    |Y| ≤ (gmax * (A0 + B0) + C) * (|κ| + |μ|) := by
  have hA0 : 0 ≤ A0 := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B0 := (abs_nonneg _).trans hB
  have hgm : 0 ≤ gmax := hg0.trans hg
  have h1 : |κ * (g * Ai) + μ * (g * Bi)| ≤ |κ| * (gmax * A0) + |μ| * (gmax * B0) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_of_nonneg hg0]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hg hA (abs_nonneg _) hgm) (abs_nonneg _)
    · rw [abs_mul, abs_mul, abs_of_nonneg hg0]
      exact mul_le_mul_of_nonneg_left (mul_le_mul hg hB (abs_nonneg _) hgm) (abs_nonneg _)
  have h2 : C * δ3 * (|κ| * W + |μ| * Wb) ≤ C * (|κ| + |μ|) := by
    have e1 : |κ| * W ≤ |κ| := mul_le_of_le_one_right (abs_nonneg κ) hW
    have e2 : |μ| * Wb ≤ |μ| := mul_le_of_le_one_right (abs_nonneg μ) hWb
    have e3 : C * δ3 ≤ C := mul_le_of_le_one_right hC hδ1
    calc C * δ3 * (|κ| * W + |μ| * Wb) ≤ C * δ3 * (|κ| + |μ|) :=
          mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by positivity)
      _ ≤ C * (|κ| + |μ|) := mul_le_mul_of_nonneg_right e3 (by positivity)
  have h3 : |Y| ≤ |Y - (κ * (g * Ai) + μ * (g * Bi))| + |κ * (g * Ai) + μ * (g * Bi)| := by
    have := abs_add_le (Y - (κ * (g * Ai) + μ * (g * Bi))) (κ * (g * Ai) + μ * (g * Bi))
    simpa using this
  have hκ := abs_nonneg κ
  have hμ := abs_nonneg μ
  nlinarith [mul_nonneg hκ (mul_nonneg hgm hB0), mul_nonneg hμ (mul_nonneg hgm hA0)]

/-- Size of `Y_{k+1} - Y_{k-1}` from the Airy decomposition and the Lipschitz bounds. -/
lemma hk_pair {κ μ Yp Ym gp gm ap am bp bm C δ gmax Lg A0 B0 A1 B1 c2 : ℝ} (hC : 0 ≤ C) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hgm0 : 0 ≤ gm) (hgm : gm ≤ gmax) (hLg : 0 ≤ Lg) (hc2 : 0 ≤ c2) (hA0 : 0 ≤ A0) (hB0 : 0 ≤ B0) (hA1 : 0 ≤ A1) (hB1 : 0 ≤ B1)
    (hYp : |Yp - (κ * (gp * ap) + μ * (gp * bp))| ≤ C * δ ^ 3 * (|κ| + |μ|))
    (hYm : |Ym - (κ * (gm * am) + μ * (gm * bm))| ≤ C * δ ^ 3 * (|κ| + |μ|))
    (hgd : |gp - gm| ≤ Lg * δ ^ 3) (hap : |ap| ≤ A0) (hbp : |bp| ≤ B0)
    (had : |ap - am| ≤ A1 * (2 * c2 * δ)) (hbd : |bp - bm| ≤ B1 * (2 * c2 * δ)) :
    |Yp - Ym| ≤ δ * (Lg * (A0 + B0) + 2 * gmax * c2 * (A1 + B1) + 2 * C) * (|κ| + |μ|) := by
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_nonneg hδ0 2, mul_nonneg hδ0 hδ0]
  have hδ3' : 0 ≤ δ ^ 3 := by positivity
  have hgmax : 0 ≤ gmax := hgm0.trans hgm
  have key : ∀ (ap am A A1' : ℝ), |ap| ≤ A → |ap - am| ≤ A1' * (2 * c2 * δ) → 0 ≤ A1' →
      |gp * ap - gm * am| ≤ Lg * δ ^ 3 * A + gmax * (A1' * (2 * c2 * δ)) := by
    intro ap am A A1' h1 h2 h3
    have e : gp * ap - gm * am = (gp - gm) * ap + gm * (ap - am) := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul hgd h1 (abs_nonneg _) (by positivity)
    · rw [abs_mul, abs_of_nonneg hgm0]
      exact mul_le_mul hgm h2 (abs_nonneg _) hgmax
  have ka := key ap am A0 A1 hap had hA1
  have kb := key bp bm B0 B1 hbp hbd hB1
  have e : Yp - Ym = κ * (gp * ap - gm * am) + μ * (gp * bp - gm * bm) +
      ((Yp - (κ * (gp * ap) + μ * (gp * bp))) - (Ym - (κ * (gm * am) + μ * (gm * bm)))) := by ring
  rw [e]
  have h1 : |κ * (gp * ap - gm * am) + μ * (gp * bp - gm * bm) +
      ((Yp - (κ * (gp * ap) + μ * (gp * bp))) - (Ym - (κ * (gm * am) + μ * (gm * bm))))| ≤
      |κ| * |gp * ap - gm * am| + |μ| * |gp * bp - gm * bm| + 2 * (C * δ ^ 3 * (|κ| + |μ|)) := by
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (by rw [abs_mul]) (by rw [abs_mul]))) ?_)
    refine (abs_sub _ _).trans ?_
    linarith
  refine h1.trans ?_
  have hκ := abs_nonneg κ
  have hμ := abs_nonneg μ
  have hLδ : Lg * δ ^ 3 * A0 ≤ δ * (Lg * A0) := by nlinarith [mul_nonneg hLg hA0]
  have hLδ' : Lg * δ ^ 3 * B0 ≤ δ * (Lg * B0) := by nlinarith [mul_nonneg hLg hB0]
  have hCδ : C * δ ^ 3 ≤ C * δ := mul_le_mul_of_nonneg_left hδ3 hC
  have s1 : |κ| * |gp * ap - gm * am| ≤ |κ| * (δ * (Lg * A0) + gmax * (A1 * (2 * c2 * δ))) :=
    mul_le_mul_of_nonneg_left (ka.trans (by linarith)) hκ
  have s2 : |μ| * |gp * bp - gm * bm| ≤ |μ| * (δ * (Lg * B0) + gmax * (B1 * (2 * c2 * δ))) :=
    mul_le_mul_of_nonneg_left (kb.trans (by linarith)) hμ
  have s3 : 2 * (C * δ ^ 3 * (|κ| + |μ|)) ≤ 2 * (C * δ * (|κ| + |μ|)) := by
    have := mul_le_mul_of_nonneg_right hCδ (by positivity : 0 ≤ |κ| + |μ|)
    linarith
  have t1 : 0 ≤ |κ| * (δ * (Lg * B0)) := by positivity
  have t2 : 0 ≤ |κ| * (δ * (2 * gmax * c2 * B1)) := by positivity
  have t3 : 0 ≤ |μ| * (δ * (Lg * A0)) := by positivity
  have t4 : 0 ≤ |μ| * (δ * (2 * gmax * c2 * A1)) := by positivity
  nlinarith [s1, s2, s3, t1, t2, t3, t4]

/-- **Amplitude upper bound from the chain side**: `T = w f² + g²/w ≤ s R S²`. -/
lemma hk_T_alg {w s S P Q a b x δ f g Yp Ym : ℝ} (hs1 : 1 ≤ s) (hw1 : 9 * s ≤ w) (hw2 : w ≤ 15 * s)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hδ : 0 ≤ δ) (hf : |f| ≤ P * S) (hg : g = a * Yp - b * Ym)
    (ha0 : 0 ≤ a) (hax : a ≤ x) (hba0 : 0 ≤ b - a) (hba1 : b - a ≤ 1) (hYm : |Ym| ≤ P * S)
    (hpair : |Yp - Ym| ≤ δ * Q * S) (hxδ : x * δ ≤ 2 * s) :
    w * f ^ 2 + g ^ 2 / w ≤ s * (15 * P ^ 2 + (2 * Q + P) ^ 2 / 9) * S ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hw0 : 0 < w := by linarith
  have hg' : g = a * (Yp - Ym) - (b - a) * Ym := by rw [hg]; ring
  have h1 : |g| ≤ a * (δ * Q * S) + 1 * (P * S) := by
    rw [hg']
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg ha0]
      exact mul_le_mul_of_nonneg_left hpair ha0
    · rw [abs_mul, abs_of_nonneg hba0]
      exact mul_le_mul hba1 hYm (abs_nonneg _) zero_le_one
  have h2 : a * (δ * Q * S) ≤ 2 * s * Q * S := by
    have : a * δ ≤ 2 * s := (mul_le_mul_of_nonneg_right hax hδ).trans hxδ
    have h3 := mul_le_mul_of_nonneg_right this (mul_nonneg hQ hS)
    nlinarith [h3]
  have h4 : 1 * (P * S) ≤ s * P * S := by nlinarith [mul_nonneg hP hS]
  have hgb : |g| ≤ s * (2 * Q + P) * S := by nlinarith
  have hg2 : g ^ 2 ≤ (s * (2 * Q + P) * S) ^ 2 := by
    rw [← sq_abs g]
    exact pow_le_pow_left₀ (abs_nonneg _) hgb 2
  have hf2 : f ^ 2 ≤ (P * S) ^ 2 := by
    rw [← sq_abs f]
    exact pow_le_pow_left₀ (abs_nonneg _) hf 2
  have t1 : w * f ^ 2 ≤ 15 * s * (P * S) ^ 2 :=
    mul_le_mul hw2 hf2 (sq_nonneg _) (by linarith)
  have t2 : g ^ 2 / w ≤ (s * (2 * Q + P) * S) ^ 2 / (9 * s) := by
    calc g ^ 2 / w ≤ g ^ 2 / (9 * s) := div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hw1
      _ ≤ _ := div_le_div_of_nonneg_right hg2 (by positivity)
  have e2 : (s * (2 * Q + P) * S) ^ 2 / (9 * s) = s * ((2 * Q + P) ^ 2 / 9) * S ^ 2 := by
    field_simp
  rw [e2] at t2
  have e1 : 15 * s * (P * S) ^ 2 = s * (15 * P ^ 2) * S ^ 2 := by ring
  rw [e1] at t1
  have e3 : s * (15 * P ^ 2 + (2 * Q + P) ^ 2 / 9) * S ^ 2 =
      s * (15 * P ^ 2) * S ^ 2 + s * ((2 * Q + P) ^ 2 / 9) * S ^ 2 := by ring
  rw [e3]
  linarith

lemma hk_biwt_nonpos {X : ℝ} (hX : X ≤ 0) : airyBiWt X ≤ 1 := by
  rw [airyBiWt_eq_mul]
  have h0 : airyXi X = 0 := by
    unfold airyXi
    rw [max_eq_right hX]
    simp
  rw [h0]
  simpa using airyWt_le_one X

lemma hk_wt_relax {C δ3 κ μ W Wb : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ3) (hW : W ≤ 1) (hWb : Wb ≤ 1) :
    C * δ3 * (|κ| * W + |μ| * Wb) ≤ C * δ3 * (|κ| + |μ|) := by
  have e1 : |κ| * W ≤ |κ| := mul_le_of_le_one_right (abs_nonneg κ) hW
  have e2 : |μ| * Wb ≤ |μ| := mul_le_of_le_one_right (abs_nonneg μ) hWb
  exact mul_le_mul_of_nonneg_left (add_le_add e1 e2) (by positivity)

/-- `2L ≤ x²` for `L ≤ 100/δ + 1`, `δ ≤ 1/400`, `δ³ = 2/x²`. -/
lemma hk_two_L {x δ : ℝ} {L : ℕ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 400) (hδx : δ ^ 3 = 2 / x ^ 2) (hx : 0 < x)
    (hL2 : (L : ℝ) ≤ 100 / δ + 1) : 2 * (L : ℝ) ≤ x ^ 2 := by
  have hδ3 : 0 < δ ^ 3 := by positivity
  have hx2 : x ^ 2 = 2 / δ ^ 3 := by rw [hδx]; field_simp
  have h400 : (400 : ℝ) ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have h1 : 2 * (L : ℝ) ≤ 200 * (1 / δ) + 2 := by
    have : 200 / δ = 200 * (1 / δ) := by ring
    have : 100 / δ = 100 * (1 / δ) := by ring
    linarith
  have h2 : 200 * (1 / δ) + 2 ≤ 2 * (1 / δ) ^ 3 := hk_cube_aux h400
  have e : 2 / δ ^ 3 = 2 * (1 / δ) ^ 3 := by field_simp
  rw [hx2, e]; linarith

/-- **Choice of the site**: from the lattice data of `HkEdge` (as abstract reals `X`, `dalQ`), the index `n = L - m` with the
Weber-side conclusions `T ≥ 9/50`, `w ∈ [9 s, 15 s]` and the lattice position of the three sites. -/
lemma hk_pick {r c1 c2 x δ : ℝ} {J m N : ℤ} {X : ℤ → ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδa : δ ≤ 1 / 400)
    (hsm : 103 * δ ^ 2 < r) (hc1 : 0 < c1) (hcδ : c2 * δ ≤ c1) (hδx : δ ^ 3 = 2 / x ^ 2) (hmN : m ≤ N)
    (hqJ : dalQ (-δ ^ 3 / 2) δ J < -1 - r + δ ^ 3) (hqm1 : -1 ≤ dalQ (-δ ^ 3 / 2) δ m)
    (hqm2 : dalQ (-δ ^ 3 / 2) δ m < -1 + δ ^ 3)
    (hgap : ∀ k ∈ Finset.Icc J N, c1 * δ ≤ X (k + 1) - X k ∧ X (k + 1) - X k ≤ c2 * δ)
    (hX0 : 0 ≤ X m) (hX1 : X m ≤ c2 * δ) :
    ∃ (L n : ℕ), (n : ℤ) = L - m ∧ J + 1 ≤ m - L - 1 ∧ (1 : ℤ) ≤ L ∧ (n : ℝ) ≤ x ^ 2 ∧
      9 / 50 ≤ √(2 * (n : ℝ) + 1 - x ^ 2) * hermitePhi n x ^ 2 + hkDer n x ^ 2 / √(2 * (n : ℝ) + 1 - x ^ 2) ∧
      9 * x ^ (1 / 3 : ℝ) ≤ √(2 * (n : ℝ) + 1 - x ^ 2) ∧ √(2 * (n : ℝ) + 1 - x ^ 2) ≤ 15 * x ^ (1 / 3 : ℝ) ∧
      X (m - L + 1) ≤ 0 ∧ -(102 * c2) ≤ X (m - L - 1) ∧ X (m - L + 1) - X (m - L - 1) ≤ 2 * c2 * δ ∧
      X (m - L - 1) ≤ X (m - L) ∧ X (m - L) ≤ X (m - L + 1) := by
  have hδ1' : δ ≤ 1 := by linarith
  obtain ⟨L, hL1, hL2, hJL, hlam1, hlam2, hXp, hXm, hXd, hXmo, hXom⟩ :=
    hk_sites hx hδ hδ1' hsm hc1 hcδ hδx hmN hqJ hqm1 hqm2 hgap hX0 hX1
  have hL100 : (100 : ℝ) ≤ L := by
    have : (100 : ℝ) ≤ 100 / δ := by rw [le_div_iff₀ hδ]; linarith
    linarith
  have hLpos : (1 : ℤ) ≤ L := by
    have : (1 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  have hm1 : m ≤ -1 := by
    have : (m : ℝ) ≤ -1 ∨ True := Or.inr trivial
    -- from `q_m < -1 + δ³` and `q_m = -δ³/2 + m δ³`
    by_contra hcon
    have h0 : (0 : ℝ) ≤ m := by exact_mod_cast (by omega : (0 : ℤ) ≤ m)
    simp only [dalQ] at hqm2
    have hδ3 : 0 < δ ^ 3 := by positivity
    nlinarith [mul_nonneg h0 hδ3.le]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = L - m := ⟨(L - m).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hnR : (n : ℝ) = L - m := by exact_mod_cast hn
  have hk0R : ((m - L : ℤ) : ℝ) = (m : ℝ) - L := by push_cast; ring
  rw [hk0R] at hlam1 hlam2
  have hn1 : x ^ 2 + 2 * (L : ℝ) - 2 < 2 * (n : ℝ) + 1 := by rw [hnR]; linarith
  have hn2 : 2 * (n : ℝ) + 1 ≤ x ^ 2 + 2 * (L : ℝ) := by rw [hnR]; linarith
  obtain ⟨hT, hw1, hw2⟩ := hk_weber_side hx hδ hδa hδx hL1 hL2 hn1 hn2
  have h2L := hk_two_L hδ hδa hδx hx hL2
  refine ⟨L, n, hn, hJL, hLpos, by linarith, hT, hw1, hw2, hXp, hXm, hXd, hXmo, hXom⟩

/-- **Chain side**: the Airy decomposition at the three sites `k₀ - 1, k₀, k₀ + 1` (`k₀ = m - L = -n`) bounds the Weber
amplitude `T = w φ_n(x)² + φ_n'(x)²/w` by `s R (|κ| + |μ|)²`. -/
lemma hk_chain {C gmax Lg c2 δ x κ μ A0 A1 B0 B1 P Q R w s : ℝ} {G XX : ℤ → ℝ} {J N m : ℤ} {n L : ℕ}
    (hx : 0 < x) (hC : 0 < C) (hLg : 0 ≤ Lg) (hc2 : 0 ≤ c2) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hP : P = gmax * (A0 + B0) + C)
    (hQ : Q = 2 * Lg * (A0 + B0) + 2 * gmax * c2 * (A1 + B1) + 2 * C) (hR : R = 15 * P ^ 2 + (2 * Q + P) ^ 2 / 9)
    (hAs : ∀ y ∈ Set.Icc (-(102 * c2)) 0, |airyAi y| ≤ A0)
    (hAl : ∀ y ∈ Set.Icc (-(102 * c2)) 0, ∀ z ∈ Set.Icc (-(102 * c2)) 0, |airyAi y - airyAi z| ≤ A1 * |y - z|)
    (hBs : ∀ y ∈ Set.Icc (-(102 * c2)) 0, |airyBi y| ≤ B0)
    (hBl : ∀ y ∈ Set.Icc (-(102 * c2)) 0, ∀ z ∈ Set.Icc (-(102 * c2)) 0, |airyBi y - airyBi z| ≤ B1 * |y - z|)
    (hYs : ∀ k ∈ Finset.Icc J (N + 1), |hermitePsi (-k) x - (κ * (G k * airyAi (XX k)) + μ * (G k * airyBi (XX k)))| ≤
      C * δ ^ 3 * (|κ| * airyWt (XX k) + |μ| * airyBiWt (XX k)))
    (hGb : ∀ k ∈ Finset.Icc J (N + 1), 0 ≤ G k ∧ G k ≤ gmax)
    (hLgb : ∀ k ∈ Finset.Icc J N, |G (k + 1) - G k| ≤ Lg * δ ^ 3)
    (hJL : J + 1 ≤ m - L - 1) (hLpos : (1 : ℤ) ≤ L) (hmN : m ≤ N) (hn : (n : ℤ) = L - m) (hnx : (n : ℝ) ≤ x ^ 2)
    (hXp : XX (m - L + 1) ≤ 0) (hXm : -(102 * c2) ≤ XX (m - L - 1)) (hXd : XX (m - L + 1) - XX (m - L - 1) ≤ 2 * c2 * δ)
    (hXmo : XX (m - L - 1) ≤ XX (m - L)) (hXom : XX (m - L) ≤ XX (m - L + 1))
    (hs1 : 1 ≤ s) (hxδ : x * δ ≤ 2 * s) (hw1 : 9 * s ≤ w) (hw2 : w ≤ 15 * s) :
    w * hermitePhi n x ^ 2 + hkDer n x ^ 2 / w ≤ s * R * (|κ| + |μ|) ^ 2 := by
  have hδ3 : δ ^ 3 ≤ 1 := pow_le_one₀ hδ.le hδ1
  have hδ3' : 0 < δ ^ 3 := by positivity
  have hk0 : m - L ∈ Finset.Icc J (N + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hkm : m - L - 1 ∈ Finset.Icc J (N + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hkp : m - L + 1 ∈ Finset.Icc J (N + 1) := Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hgmax : 0 ≤ gmax := (hGb _ hk0).1.trans (hGb _ hk0).2
  have hIc : ∀ y, -(102 * c2) ≤ y → y ≤ 0 → y ∈ Set.Icc (-(102 * c2)) 0 := fun y h1 h2 => ⟨h1, h2⟩
  have hI0 := hIc (XX (m - L)) (by linarith) (by linarith)
  have hIm := hIc (XX (m - L - 1)) hXm (by linarith)
  have hIp := hIc (XX (m - L + 1)) (by linarith) hXp
  have hS0 : 0 ≤ |κ| + |μ| := by positivity
  have hsite : ∀ k ∈ Finset.Icc J (N + 1), XX k ∈ Set.Icc (-(102 * c2)) 0 →
      |hermitePsi (-k) x| ≤ P * (|κ| + |μ|) := by
    intro k hk hI
    rw [hP]
    exact hk_site_up (hGb k hk).1 (hGb k hk).2 (hAs _ hI) (hBs _ hI) (airyWt_le_one _)
      (hk_biwt_nonpos hI.2) hC.le hδ3'.le hδ3 (hYs k hk)
  have hY0 := hsite _ hk0 hI0
  have hYm := hsite _ hkm hIm
  have hgd : |G (m - L + 1) - G (m - L - 1)| ≤ 2 * Lg * δ ^ 3 := by
    have a1 := hLgb (m - L - 1) (by rw [Finset.mem_Icc]; omega)
    have a2 := hLgb (m - L) (by rw [Finset.mem_Icc]; omega)
    have e1 : m - (L : ℤ) - 1 + 1 = m - L := by ring
    rw [e1] at a1
    have h3 := abs_sub (G (m - L + 1) - G (m - L)) (G (m - L - 1) - G (m - L))
    have e2 : G (m - L + 1) - G (m - L) - (G (m - L - 1) - G (m - L)) = G (m - L + 1) - G (m - L - 1) := by ring
    rw [e2, abs_sub_comm (G (m - L - 1)) (G (m - L))] at h3
    linarith
  have hrelax : ∀ k ∈ Finset.Icc J (N + 1), XX k ∈ Set.Icc (-(102 * c2)) 0 →
      |hermitePsi (-k) x - (κ * (G k * airyAi (XX k)) + μ * (G k * airyBi (XX k)))| ≤
        C * δ ^ 3 * (|κ| + |μ|) := fun k hk hI =>
    (hYs k hk).trans (hk_wt_relax hC.le hδ3'.le (airyWt_le_one _) (hk_biwt_nonpos hI.2))
  have hXdd : 0 ≤ XX (m - L + 1) - XX (m - L - 1) := by linarith
  have hpair := hk_pair (κ := κ) (μ := μ) (Yp := hermitePsi (-(m - L + 1)) x) (Ym := hermitePsi (-(m - L - 1)) x)
    (gp := G (m - L + 1)) (gm := G (m - L - 1)) (ap := airyAi (XX (m - L + 1))) (am := airyAi (XX (m - L - 1)))
    (bp := airyBi (XX (m - L + 1))) (bm := airyBi (XX (m - L - 1))) (C := C) (δ := δ) (gmax := gmax) (Lg := 2 * Lg)
    (A0 := A0) (B0 := B0) (A1 := A1) (B1 := B1) (c2 := c2) hC.le hδ.le hδ1 (hGb _ hkm).1 (hGb _ hkm).2
    (by positivity) hc2 hA0 hB0 hA1 hB1 (hrelax _ hkp hIp) (hrelax _ hkm hIm) hgd
    (hAs _ hIp) (hBs _ hIp)
    ((hAl _ hIp _ hIm).trans (by rw [abs_of_nonneg hXdd]; exact mul_le_mul_of_nonneg_left hXd hA1))
    ((hBl _ hIp _ hIm).trans (by rw [abs_of_nonneg hXdd]; exact mul_le_mul_of_nonneg_left hXd hB1))
  have e0 : -(m - (L : ℤ)) = (n : ℤ) := by omega
  have ep : -(m - (L : ℤ) + 1) = (n : ℤ) - 1 := by omega
  have em : -(m - (L : ℤ) - 1) = (n : ℤ) + 1 := by omega
  rw [e0, hermitePsi_natCast] at hY0
  rw [ep, em] at hpair
  rw [em] at hYm
  have hQ' : 2 * Lg * (A0 + B0) + 2 * gmax * c2 * (A1 + B1) + 2 * C = Q := hQ.symm
  rw [hQ'] at hpair
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha : √((n : ℝ) / 2) ≤ x := by
    refine Real.sqrt_le_iff.2 ⟨hx.le, ?_⟩
    nlinarith [sq_nonneg x]
  have hba : √(((n : ℝ) + 1) / 2) - √((n : ℝ) / 2) ≤ 1 := by
    have h1 : √((n : ℝ) / 2) ^ 2 = (n : ℝ) / 2 := Real.sq_sqrt (by positivity)
    have h0 := Real.sqrt_nonneg ((n : ℝ) / 2)
    have : √(((n : ℝ) + 1) / 2) ≤ √((n : ℝ) / 2) + 1 := by
      refine Real.sqrt_le_iff.2 ⟨by linarith, ?_⟩
      nlinarith
    linarith
  have hba0 : 0 ≤ √(((n : ℝ) + 1) / 2) - √((n : ℝ) / 2) :=
    sub_nonneg.2 (Real.sqrt_le_sqrt (by linarith))
  have hw0 : 0 ≤ w := by linarith
  have hT := hk_T_alg (w := w) (s := s) (S := |κ| + |μ|) (P := P) (Q := Q) (a := √((n : ℝ) / 2))
    (b := √(((n : ℝ) + 1) / 2)) (x := x) (δ := δ) (f := hermitePhi n x) (g := hkDer n x)
    (Yp := hermitePsi ((n : ℤ) - 1) x) (Ym := hermitePsi ((n : ℤ) + 1) x) hs1 hw1 hw2 (by rw [hP]; positivity)
    (by rw [hQ]; positivity) hS0 hδ.le hY0 rfl (Real.sqrt_nonneg _) ha hba0 hba hYm hpair hxδ
  rw [hR]
  exact hT

/-- Final algebra: `9/50 ≤ s R (|κ|+|μ|)²` and `μ² s ≤ M/s ≤ 9/(200 R)` give `κ² s ≥ 9/(200 R)`. -/
lemma hk_lower_alg {R M D s κ μ : ℝ} (hR : 0 < R) (hM : 0 < M) (hD : D = 1 + 200 * R * M / 9) (hs : D ≤ s)
    (hT : 9 / 50 ≤ s * R * (|κ| + |μ|) ^ 2) (hmu : μ ^ 2 * s ≤ M / s) : 9 / (200 * R) ≤ κ ^ 2 * s := by
  have hD1 : 1 ≤ D := by
    have : 0 ≤ 200 * R * M / 9 := by positivity
    linarith
  have hs0 : 0 < s := by linarith
  have hsq : (|κ| + |μ|) ^ 2 ≤ 2 * κ ^ 2 + 2 * μ ^ 2 := by
    nlinarith [sq_nonneg (|κ| - |μ|), sq_abs κ, sq_abs μ]
  have h1 : 9 / 50 ≤ 2 * R * (κ ^ 2 * s + μ ^ 2 * s) := by
    have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ s * R)
    nlinarith
  have h2 : M / s ≤ 9 / (200 * R) := by
    rw [div_le_div_iff₀ hs0 (by positivity)]
    have : 200 * R * M / 9 ≤ s := by linarith
    have h3 : 200 * R * M ≤ 9 * s := by linarith
    nlinarith
  have h3 : 9 / (100 * R) ≤ κ ^ 2 * s + μ ^ 2 * s := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e : 9 / (100 * R) = 2 * (9 / (200 * R)) := by field_simp; ring
  linarith

/-- Scales: `δ ≤ 1/D²`, `δ ≤ 1/400`, `δ³ = 2/x²` give `D ≤ x^{1/3}`, `x δ ≤ 2 x^{1/3}`, `4 ≤ x`. -/
lemma hk_scale {x δ D : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδx : δ ^ 3 = 2 / x ^ 2) (hD : 0 < D) (hδb : δ ≤ 1 / D ^ 2)
    (hδa : δ ≤ 1 / 400) : D ≤ x ^ (1 / 3 : ℝ) ∧ x * δ ≤ 2 * x ^ (1 / 3 : ℝ) ∧ 4 ≤ x := by
  obtain ⟨hs3, hs1, hs2⟩ := hk_delta_s hx hδ hδx
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = x ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hs] at hs3 hs1 hs2 ⊢
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hx _
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 1 / δ ≤ s ^ 2 := by rw [div_le_iff₀ hδ]; linarith
    have h2 : D ^ 2 ≤ 1 / δ := by
      rw [le_div_iff₀ hδ]
      have := mul_le_mul_of_nonneg_left hδb (by positivity : 0 ≤ D ^ 2)
      have e : D ^ 2 * (1 / D ^ 2) = 1 := by field_simp
      linarith
    exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hs0.le (h2.trans h1)
  · have : x * δ = s * (δ * s ^ 2) := by
      calc x * δ = s ^ 3 * δ := by rw [hs3]
        _ = _ := by ring
    rw [this]; nlinarith
  · have hδ3' : 0 < δ ^ 3 := by positivity
    have hx2 : 2 / δ ^ 3 = x ^ 2 := by rw [hδx]; field_simp
    have h8 : δ ^ 3 ≤ 1 / 8 := by nlinarith [pow_pos hδ 2]
    have : 16 ≤ x ^ 2 := by
      rw [← hx2, le_div_iff₀ hδ3']
      nlinarith
    nlinarith

/-- **Amplitude bound at the data of `HkEdge`**: `9/50 ≤ x^{1/3} R (|κ| + |μ|)²`. -/
lemma hk_edge_amp {r C Cmu ξ0 gmax gmin c1 c2 Lg A0 A1 B0 B1 P Q R x δ κ μ : ℝ} {J m N : ℤ}
    (hC : 0 < C) (hgmin : 0 < gmin) (hLg : 0 ≤ Lg) (hc1 : 0 < c1) (hc2 : 0 ≤ c2) (hA0 : 0 ≤ A0) (hA1 : 0 ≤ A1)
    (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hP : P = gmax * (A0 + B0) + C)
    (hQ : Q = 2 * Lg * (A0 + B0) + 2 * gmax * c2 * (A1 + B1) + 2 * C) (hR : R = 15 * P ^ 2 + (2 * Q + P) ^ 2 / 9)
    (hAs : ∀ y ∈ Set.Icc (-(102 * c2)) 0, |airyAi y| ≤ A0)
    (hAl : ∀ y ∈ Set.Icc (-(102 * c2)) 0, ∀ z ∈ Set.Icc (-(102 * c2)) 0, |airyAi y - airyAi z| ≤ A1 * |y - z|)
    (hBs : ∀ y ∈ Set.Icc (-(102 * c2)) 0, |airyBi y| ≤ B0)
    (hBl : ∀ y ∈ Set.Icc (-(102 * c2)) 0, ∀ z ∈ Set.Icc (-(102 * c2)) 0, |airyBi y - airyBi z| ≤ B1 * |y - z|)
    (hx : 0 < x) (hδ : 0 < δ) (hδa : δ ≤ 1 / 400) (hcδ : c2 * δ ≤ c1) (hsm : 103 * δ ^ 2 < r)
    (hδx : δ ^ 3 = 2 / x ^ 2) (hs1 : 1 ≤ x ^ (1 / 3 : ℝ)) (hxδ : x * δ ≤ 2 * x ^ (1 / 3 : ℝ))
    (h : HkEdge r C Cmu ξ0 gmax gmin c1 c2 Lg x δ J m N κ μ) :
    9 / 50 ≤ x ^ (1 / 3 : ℝ) * R * (|κ| + |μ|) ^ 2 := by
  obtain ⟨hJN, hJm, hmN, hNneg, hwin, hqJ2, hqm1, hqm2, hqN, hqN1, hg, hgap, hLgb, ⟨hX0, hX1⟩, hc2δ, hμ, hY⟩ := h
  obtain ⟨L, n, hn, hJL, hLpos, hnx, hT, hw1, hw2, hXp, hXm, hXd, hXmo, hXom⟩ :=
    hk_pick hx hδ hδa hsm hc1 hcδ hδx hmN hqJ2 hqm1 hqm2 hgap hX0 hX1
  have hch := hk_chain (G := fun k => langerAmp hmU hmA (-1) (dalQ (-δ ^ 3 / 2) δ k))
    (XX := turnX hmU (-1) (-δ ^ 3 / 2) δ) (J := J) (N := N) (m := m) (n := n) (L := L) hx hC hLg hc2 hδ
    (by linarith) hA0 hA1 hB0 hB1 hP hQ hR hAs hAl hBs hBl hY
    (fun k hk => ⟨hgmin.le.trans (hg k hk).1, (hg k hk).2⟩) hLgb hJL hLpos hmN hn hnx hXp hXm hXd hXmo hXom
    hs1 hxδ hw1 hw2
  exact hT.trans hch

/-- **Order bound, lower half**: for the data of `HkEdge` there are `δ₁, c_κ > 0` with `κ² x^{1/3} ≥ c_κ` whenever
`δ ≤ δ₁`, `δ³ = 2/x²`, i.e. `|κ| ≥ c S^{-1/12}`. -/
theorem hermite_kappa_ge {r C Cmu ξ0 gmax gmin c1 c2 Lg : ℝ} (hr : 0 < r) (hC : 0 < C) (hCmu : 0 < Cmu)
    (hξ0 : 0 < ξ0) (hgmin : 0 < gmin) (hgg : gmin ≤ gmax) (hc1 : 0 < c1) (hc12 : c1 ≤ c2) (hLg : 0 ≤ Lg) :
    ∃ δ1 ck : ℝ, 0 < δ1 ∧ 0 < ck ∧ ∀ (x δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < x → 0 < δ → δ ≤ δ1 →
      δ ^ 3 = 2 / x ^ 2 → HkEdge r C Cmu ξ0 gmax gmin c1 c2 Lg x δ J m N κ μ →
      ck ≤ κ ^ 2 * x ^ (1 / 3 : ℝ) := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin hgg
  obtain ⟨A0, A1, B0, B1, hA0, hA1, hB0, hB1, hAs, hAl, hBs, hBl⟩ := hk_airy_compact (102 * c2)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = gmax * (A0 + B0) + C := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * Lg * (A0 + B0) + 2 * gmax * c2 * (A1 + B1) + 2 * C := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 15 * P ^ 2 + (2 * Q + P) ^ 2 / 9 := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 8 * Cmu ^ 2 / ξ0 ^ 2 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 1 + 200 * R * M / 9 := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have hR0 : 0 < R := by rw [hR]; positivity
  have hM0 : 0 < M := by rw [hM]; positivity
  have hD1 : 1 ≤ D := by
    have : 0 ≤ 200 * R * M / 9 := by positivity
    linarith
  have hD0 : 0 < D := by linarith
  refine ⟨min (1 / 400) (min (1 / D ^ 2) (min (c1 / c2) (r / 104))), 9 / (200 * R), by positivity, by positivity, ?_⟩
  intro x δ J m N κ μ hx hδ hδ1 hδx h
  have hδa : δ ≤ 1 / 400 := hδ1.trans (min_le_left _ _)
  have hδb : δ ≤ 1 / D ^ 2 := hδ1.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc : δ ≤ c1 / c2 := hδ1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd : δ ≤ r / 104 :=
    hδ1.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hcδ : c2 * δ ≤ c1 := by rwa [le_div_iff₀ hc2, mul_comm] at hδc
  have hsm : 103 * δ ^ 2 < r := by
    have h1 : δ ^ 2 ≤ δ := by nlinarith
    have h2 : 103 * δ ≤ 103 / 104 * r := by linarith
    nlinarith
  obtain ⟨hsD, hxδ, hx4⟩ := hk_scale hx hδ hδx hD0 hδb hδa
  have hs1 : 1 ≤ x ^ (1 / 3 : ℝ) := hD1.trans hsD
  have hT := hk_edge_amp hC hgmin hLg hc1 hc2.le hA0 hA1 hB0 hB1 hP hQ hR hAs hAl hBs hBl hx hδ hδa hcδ hsm hδx hs1
    hxδ h
  have hmu := hk_mu_bound hCmu hξ0 hx4 hδ hδx h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [← hM] at hmu
  exact hk_lower_alg hR0 hM0 hD hsD hT hmu

/-- **The Airy amplitude of the Hermite chain has the order `κ² ≍ x^{-1/3}`** (`|κ| ≍ S^{-1/12}`, `S = x²/2`, `κ² ≍ √δ`):
there are absolute constants (the chart constants `r, C, C_μ, ξ₀, g_max, g_min, c₁, c₂, L_g` of `HkEdge`, `δ₀`, `c_κ`, `C_κ`, all positive,
fixed before `x` is chosen) such that for every `x > 0`, `δ ≤ δ₀`, `δ³ = 2/x²` the Airy-edge data `HkEdge` exist with
`c_κ ≤ κ² x^{1/3} ≤ C_κ`.  Combined with the content of `HkEdge` (`hermite_airy_edge`), `φ_{-k}(x) = κ g_k Ai(X_k) + μ g_k Bi(X_k) + O(δ³)`
with `|κ| ≍ x^{-1/6}` and `|μ|` exponentially small.  `κ` is only constrained through `HkEdge`; its uniqueness is not shown. -/
theorem hermite_kappa_order :
    ∃ r δ0 C Cmu ξ0 gmax gmin c1 c2 Lg ck Ck : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ 0 < δ0 ∧ 0 < C ∧ 0 < Cmu ∧ 0 < ξ0 ∧ 0 < gmin ∧
      gmin ≤ gmax ∧ 0 < c1 ∧ c1 ≤ c2 ∧ 0 ≤ Lg ∧ 0 < ck ∧ 0 < Ck ∧
      ∀ x δ : ℝ, 0 < x → 0 < δ → δ ≤ δ0 → δ ^ 3 = 2 / x ^ 2 →
        ∃ (J m N : ℤ) (κ μ : ℝ), HkEdge r C Cmu ξ0 gmax gmin c1 c2 Lg x δ J m N κ μ ∧
          ck ≤ κ ^ 2 * x ^ (1 / 3 : ℝ) ∧ κ ^ 2 * x ^ (1 / 3 : ℝ) ≤ Ck := by
  obtain ⟨r, δ0, C, Cmu, ξ0, gmax, gmin, c1, c2, Lg, hr, hrr0, hδ0, hC, hCmu, hξ0, hgmin, hgg, hc1, hc12, hLg, H⟩ :=
    hermite_kappa_edge
  obtain ⟨δ1, Ck, hδ1, hCk, Hle⟩ := hermite_kappa_le (r := r) (c1 := c1) (c2 := c2) (Lg := Lg) hC hCmu hξ0 hgmin hgg
  obtain ⟨δ2, ck, hδ2, hck, Hge⟩ := hermite_kappa_ge hr hC hCmu hξ0 hgmin hgg hc1 hc12 hLg
  refine ⟨r, min δ0 (min δ1 δ2), C, Cmu, ξ0, gmax, gmin, c1, c2, Lg, ck, Ck, hr, hrr0, by positivity, hC, hCmu, hξ0, hgmin,
    hgg, hc1, hc12, hLg, hck, hCk, ?_⟩
  intro x δ hx hδ hδm hδx
  have h0 : δ ≤ δ0 := hδm.trans (min_le_left _ _)
  have h1 : δ ≤ δ1 := hδm.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h2 : δ ≤ δ2 := hδm.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨J, m, N, κ, μ, hE⟩ := H x δ hx hδ h0 hδx
  exact ⟨J, m, N, κ, μ, hE, Hge x δ J m N κ μ hx hδ h2 hδx hE, Hle x δ J m N κ μ hx hδ h1 hδx hE⟩

/-- info: 'FormalResearch.Special.hermite_kappa_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_kappa_ge

/-- info: 'FormalResearch.Special.hermite_kappa_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_kappa_order

end FormalResearch.Special

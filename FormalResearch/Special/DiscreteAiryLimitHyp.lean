module

public import FormalResearch.Special.DiscreteAiryLimitDefect

/-!
# Discrete-to-Airy limit, step 4: the interface `AiryWindowHyp` and its Airy-free pieces

Part of the wiring module `DiscreteAiryLimit*`.

`AiryWindowHyp X ψ a c J m N δ W …` bundles *exactly* the hypotheses of the window theorems
`discrete_airy_window` / `discrete_airy_window_physical` (M6) on the lattice data `(X, ψ, a, c)`:
top window `Icc m (N+1)` with `X ≥ -1` (`AiryLattice`, `AiryComparison`, relative defect `|jac ψ| ≤ C₀ δ⁶ ψ`),
oscillatory window `Icc J m` (spacings, `X_m - X_J ≤ S`, near-hyperbolic coefficients `Sg, Qq`, absolute defect
`≤ C₀ δ⁶ W`), and the junction (`ψ_m ≤ W`, `|ψ_m - ψ_{m+1}| ≤ Λ δ W`, `w₀ ≤ ψ_m`).  It is the single place where the
data of a concrete chain is checked against M5/M6.

Airy-free pieces proved here: `dal_defT_abs` (the relative defect for perturbed coefficients from the exact one),
`dal_defW_abs` (the absolute defect), `dal_airyWt_ge`, `dal_Ai_lip`, `dal_junction`.
-/

@[expose] public section

open FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- All hypotheses of M6's window theorems on given lattice data, in one place. -/
structure AiryWindowHyp (X ψ a c : ℤ → ℝ) (J m N : ℤ) (δ W c1 B ca κ1 κ2 C0 Λ S Sg Qq w0 : ℝ) : Prop where
  lat : AiryLattice X m N c1 B δ
  cmp : AiryComparison ψ X m N κ1 κ2
  gap : ∀ k ∈ Finset.Ico J m, c1 * δ ≤ X (k + 1) - X k
  span : X m - X J ≤ S
  alow : ∀ k ∈ Finset.Icc (J + 1) (N + 1), ca ≤ a k
  hyp : ∀ k ∈ Finset.Ioc J m, |c k - a k - a (k + 1)| ≤ Sg * δ ^ 2
  lipa : ∀ k ∈ Finset.Ioc J m, |a (k + 1) - a k| ≤ Qq * δ ^ 2
  defT : ∀ i ∈ Finset.Icc (m + 1) N, |jac a c ψ i| ≤ C0 * δ ^ 6 * ψ i
  defW : ∀ i ∈ Finset.Ioc J m, |jac a c ψ i| ≤ C0 * δ ^ 6 * W
  psim : ψ m ≤ W
  junction : |ψ m - ψ (m + 1)| ≤ Λ * δ * W
  psilow : w0 ≤ ψ m
  psiabs : ∀ k ∈ Finset.Icc J (N + 1), |ψ k| ≤ W
  Xnn : ∀ k ∈ Finset.Icc m (N + 1), 0 ≤ X k

/-- Relative defect for perturbed coefficients on the top window. -/
lemma dal_defT_abs {a c a' c' ψ X : ℤ → ℝ} {m N : ℤ} {E K' κ1 κ2 Cn δ : ℝ} (hE : 0 ≤ E)
    (hex : ∀ i ∈ Finset.Icc (m + 1) N, |jac a' c' ψ i| ≤ K' * δ ^ 6 * ψ i)
    (hpa : ∀ i ∈ Finset.Icc (m + 1) N, |a (i + 1) - a' (i + 1)| ≤ E * δ ^ 6 ∧ |a i - a' i| ≤ E * δ ^ 6 ∧
      |c i - c' i| ≤ E * δ ^ 6)
    (hcmp : AiryComparison ψ X m N κ1 κ2)
    (hnbr : ∀ i ∈ Finset.Icc (m + 1) N,
      airyWt (X (i + 1)) ≤ Cn * airyWt (X i) ∧ airyWt (X (i - 1)) ≤ Cn * airyWt (X i))
    (hCn : 0 ≤ Cn) :
    ∀ i ∈ Finset.Icc (m + 1) N,
      |jac a c ψ i| ≤ (K' + E * (1 + 2 * κ2 * Cn / κ1)) * δ ^ 6 * ψ i := by
  intro i hi
  have hκ1 := hcmp.κ1_pos
  have hmem : ∀ j, m ≤ j → j ≤ N + 1 → j ∈ Finset.Icc m (N + 1) := fun j h1 h2 => by
    rw [Finset.mem_Icc]; exact ⟨h1, h2⟩
  have hi' := Finset.mem_Icc.1 hi
  have hψi := hcmp.pos (hmem i (by omega) (by omega))
  have hψ1 := hcmp.pos (hmem (i + 1) (by omega) (by omega))
  have hψ2 := hcmp.pos (hmem (i - 1) (by omega) (by omega))
  have hu1 := hcmp.upper (i + 1) (hmem (i + 1) (by omega) (by omega))
  have hu2 := hcmp.upper (i - 1) (hmem (i - 1) (by omega) (by omega))
  have hl0 := hcmp.lower i (hmem i (by omega) (by omega))
  obtain ⟨hn1, hn2⟩ := hnbr i hi
  have hw0 := airyWt_pos (X i)
  obtain ⟨hp1, hp2, hp3⟩ := hpa i hi
  have hper := dal_jac_perturb a a' c c' ψ i
  rw [abs_of_pos hψ1, abs_of_pos hψ2, abs_of_pos hψi] at hper
  have hd6 : 0 ≤ δ ^ 6 := by positivity
  have t1 : |a (i + 1) - a' (i + 1)| * ψ (i + 1) ≤ E * δ ^ 6 * (κ2 * Cn * airyWt (X i)) := by
    apply mul_le_mul hp1 _ hψ1.le (by positivity)
    exact hu1.trans (by
      calc κ2 * airyWt (X (i + 1)) ≤ κ2 * (Cn * airyWt (X i)) :=
            mul_le_mul_of_nonneg_left hn1 (hκ1.le.trans hcmp.κ1_le)
        _ = κ2 * Cn * airyWt (X i) := by ring)
  have t2 : |a i - a' i| * ψ (i - 1) ≤ E * δ ^ 6 * (κ2 * Cn * airyWt (X i)) := by
    apply mul_le_mul hp2 _ hψ2.le (by positivity)
    exact hu2.trans (by
      calc κ2 * airyWt (X (i - 1)) ≤ κ2 * (Cn * airyWt (X i)) :=
            mul_le_mul_of_nonneg_left hn2 (hκ1.le.trans hcmp.κ1_le)
        _ = κ2 * Cn * airyWt (X i) := by ring)
  have t3 : |c i - c' i| * ψ i ≤ E * δ ^ 6 * ψ i := mul_le_mul_of_nonneg_right hp3 hψi.le
  have hwψ : airyWt (X i) ≤ ψ i / κ1 := by rw [le_div_iff₀ hκ1]; linarith
  have t4 : E * δ ^ 6 * (κ2 * Cn * airyWt (X i)) ≤ E * δ ^ 6 * (κ2 * Cn * (ψ i / κ1)) := by
    have hnn : 0 ≤ κ2 * Cn := mul_nonneg (hκ1.le.trans hcmp.κ1_le) hCn
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hwψ hnn) (by positivity)
  have hex' := hex i hi
  have hfin : |jac a c ψ i| ≤ K' * δ ^ 6 * ψ i + (E * δ ^ 6 * (κ2 * Cn * (ψ i / κ1)) * 2 + E * δ ^ 6 * ψ i) := by
    have h1 : |jac a c ψ i| ≤ |jac a' c' ψ i| + |jac a c ψ i - jac a' c' ψ i| := by
      have := abs_sub_abs_le_abs_sub (jac a c ψ i) (jac a' c' ψ i)
      linarith
    nlinarith
  have e : (K' + E * (1 + 2 * κ2 * Cn / κ1)) * δ ^ 6 * ψ i =
      K' * δ ^ 6 * ψ i + (E * δ ^ 6 * (κ2 * Cn * (ψ i / κ1)) * 2 + E * δ ^ 6 * ψ i) := by
    field_simp; ring
  rw [e]; exact hfin

/-- Absolute defect for perturbed coefficients on the oscillatory window. -/
lemma dal_defW_abs {a c a' c' ψ : ℤ → ℝ} {J m : ℤ} {E K W δ : ℝ} (hE : 0 ≤ E) (hW : 0 < W)
    (hex : ∀ i ∈ Finset.Ioc J m, |jac a' c' ψ i| ≤ K * δ ^ 6)
    (hpa : ∀ i ∈ Finset.Ioc J m, |a (i + 1) - a' (i + 1)| ≤ E * δ ^ 6 ∧ |a i - a' i| ≤ E * δ ^ 6 ∧
      |c i - c' i| ≤ E * δ ^ 6)
    (hψ : ∀ i ∈ Finset.Ioc J m, |ψ (i + 1)| ≤ W ∧ |ψ (i - 1)| ≤ W ∧ |ψ i| ≤ W) :
    ∀ i ∈ Finset.Ioc J m, |jac a c ψ i| ≤ (K / W + 3 * E) * δ ^ 6 * W := by
  intro i hi
  obtain ⟨hp1, hp2, hp3⟩ := hpa i hi
  obtain ⟨hb1, hb2, hb3⟩ := hψ i hi
  have hper := dal_jac_perturb a a' c c' ψ i
  have t1 : |a (i + 1) - a' (i + 1)| * |ψ (i + 1)| ≤ E * δ ^ 6 * W :=
    mul_le_mul hp1 hb1 (abs_nonneg _) (by positivity)
  have t2 : |a i - a' i| * |ψ (i - 1)| ≤ E * δ ^ 6 * W :=
    mul_le_mul hp2 hb2 (abs_nonneg _) (by positivity)
  have t3 : |c i - c' i| * |ψ i| ≤ E * δ ^ 6 * W :=
    mul_le_mul hp3 hb3 (abs_nonneg _) (by positivity)
  have h1 : |jac a c ψ i| ≤ |jac a' c' ψ i| + |jac a c ψ i - jac a' c' ψ i| := by
    have := abs_sub_abs_le_abs_sub (jac a c ψ i) (jac a' c' ψ i)
    linarith
  have hex' := hex i hi
  have e : (K / W + 3 * E) * δ ^ 6 * W = K * δ ^ 6 + 3 * (E * δ ^ 6 * W) := by
    field_simp
  rw [e]; linarith

/-- `airyWt ≥ 2/9` on `[0, 1]`. -/
lemma dal_airyWt_ge {X : ℝ} (h0 : 0 ≤ X) (h1 : X ≤ 1) : 2 / 9 ≤ airyWt X := by
  unfold airyWt
  have hX : |X| = X := abs_of_nonneg h0
  have hξ : airyXi X ≤ 2 / 3 := by
    unfold airyXi
    rw [max_eq_left h0]
    have : X ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one h0 h1 (by norm_num)
    linarith
  have h2 : (1 : ℝ) / 3 ≤ Real.exp (-airyXi X) := by
    have := Real.add_one_le_exp (-airyXi X)
    linarith
  have h3 : (2 : ℝ) / 3 ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) := by
    have h4 : (2 + |X|) ^ (-(1 / 4) : ℝ) = ((2 + |X|) ^ (1 / 4 : ℝ))⁻¹ := by
      rw [Real.rpow_neg (by positivity)]
    rw [h4]
    have h5 : (2 + |X|) ^ (1 / 4 : ℝ) ≤ 3 / 2 := by
      calc (2 + |X|) ^ (1 / 4 : ℝ) ≤ (3 : ℝ) ^ (1 / 4 : ℝ) :=
            Real.rpow_le_rpow (by positivity) (by rw [hX]; linarith) (by norm_num)
        _ ≤ 3 / 2 := three_rpow_quarter_le
    have h6 : 0 < (2 + |X|) ^ (1 / 4 : ℝ) := by positivity
    rw [le_inv_comm₀ (by norm_num) h6]
    simpa using h5
  nlinarith

/-- `|Ai x - Ai y| ≤ 265000 |x - y|` on `[0,1]`. -/
lemma dal_Ai_lip {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    |airyAi x - airyAi y| ≤ 265000 * |x - y| := by
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖deriv airyAi t‖ ≤ 265000 := by
    intro t ht
    rw [(hasDerivAt_airyAi t).deriv, Real.norm_eq_abs]
    have h := (apx_airy_global t).2
    have hw := airyWt_le_one t
    have hs : √(2 + |t|) ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      rw [abs_of_nonneg ht.1]; linarith [ht.2]
    have hs0 := Real.sqrt_nonneg (2 + |t|)
    have hw0 := airyWt_pos t
    calc |airyAi' t| ≤ 132500 * √(2 + |t|) * airyWt t := h
      _ ≤ 132500 * 2 * 1 := by gcongr
      _ = 265000 := by norm_num
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := airyAi) (s := Set.Icc (0 : ℝ) 1) (C := 265000)
    (fun t _ => (hasDerivAt_airyAi t).differentiableAt) hb (convex_Icc 0 1) hy hx
  simpa [Real.norm_eq_abs] using this

/-- The junction estimate: for `ψ = g Ai`, sites with `X, X' ∈ [0,1]`, `|X' - X| ≤ c₂ δ`,
`|g - g'| ≤ L_g δ³`, `0 ≤ g' ≤ g_max`, `0 ≤ g ≤ g_max`, `δ ≤ 1`:
`|g Ai X - g' Ai X'| ≤ (25 L_g + 265000 g_max c₂) δ`. -/
lemma dal_junction {g g' X X' gmax Lg c2 δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hg0 : 0 ≤ g')
    (hg2 : g' ≤ gmax) (hLg : 0 ≤ Lg) (hX : X ∈ Set.Icc (0 : ℝ) 1) (hX' : X' ∈ Set.Icc (0 : ℝ) 1)
    (hd : |X' - X| ≤ c2 * δ) (hgd : |g - g'| ≤ Lg * δ ^ 3) :
    |g * airyAi X - g' * airyAi X'| ≤ (25 * Lg + 265000 * gmax * c2) * δ := by
  have e : g * airyAi X - g' * airyAi X' = (g - g') * airyAi X + g' * (airyAi X - airyAi X') := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have hA : |airyAi X| ≤ 25 := (apx_airy_global X).1.trans (by linarith [airyWt_le_one X])
  have b1 : |g - g'| * |airyAi X| ≤ Lg * δ ^ 3 * 25 := mul_le_mul hgd hA (abs_nonneg _) (by positivity)
  have hl := dal_Ai_lip hX hX'
  have hd' : |X - X'| ≤ c2 * δ := by rw [abs_sub_comm]; exact hd
  have b2 : |g'| * |airyAi X - airyAi X'| ≤ gmax * (265000 * (c2 * δ)) := by
    rw [abs_of_nonneg hg0]
    exact mul_le_mul hg2 (hl.trans (mul_le_mul_of_nonneg_left hd' (by norm_num))) (abs_nonneg _)
      (hg0.trans hg2)
  have h3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  nlinarith [mul_le_mul_of_nonneg_left h3 hLg]

end FormalResearch.Special

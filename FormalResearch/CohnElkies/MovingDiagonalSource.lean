module

public import FormalResearch.CohnElkies.CardinalSignRegions
public import FormalResearch.CohnElkies.AirySeedFloors
public import FormalResearch.Special.AiryKernelOpSharp
public import FormalResearch.Special.AiryTransformKernel

/-!
# Moving Diagonal Complement (`O.11w`), Dirichlet Vector (`O.11x`), and Two-Scale Joint Source (`O.11y`)

Formalizes `CFT/sign_uncertainty/paper/ce_o1_route.tex` (lines 413–589 on `origin/main`):

* **Part 1 — Lemma `O.11x` (`ceo:O11x`, `(ceo:O11x.4)`–`(ceo:O11x.5)`):**
  `dirichletVecS`, square-summability, global `ℓ²` bound `∑' n, v_{S,h}(t)_n² ≤ C θ` (`t ≥ 0`),
  linear-at-zero `ℓ²` bound `≤ C θ t²` (`t ∈ [0, 1]`), and combined `min t 1` form.
* **Part 2 — Theorem `O.11w` unconditional (`ceo:O11w`, `(ceo:O11w.3)`, `(ceo:O11w.4)`, `(ceo:O11w.7)`,
  `(ceo:O11w.9)`):**
  `movingDiagS`, `movingDiagQ`, nonnegativity, domination by `cohnT`, exact integral `∫ S_h = D_h`
  and `J_{2,p} √h + o(√h)` asymptotic, exact node matching at `a_n` (`n ≥ 2`), and uniform
  compact `O_U(h^p)` bound.
* **Part 3 — Theorem `O.11w` far-tail and uniform `B`-bounds (`(ceo:O11w.12)` → `(ceo:O11w.5)`,
  `(ceo:O11w.6)`, `(ceo:O11w.10)`, `(ceo:O11w.11)`):**
  clean packaging `MovingDiagFarTail p` of `CR.4`, far-tail asymptotic (`x ≥ 1, h x ≥ 1`),
  moving far-tail floor (`x ≥ T_p(ε₀)/h`), and uniform `O(B)` / `O(t^p B)` bounds on `v ≥ v₀`.
* **Part 4 — Theorem `O.11y` (`ceo:O11y`, `(ceo:O11y.1)`–`(ceo:O11y.10)`):**
  two-scale joint source `twoScaleS`, `twoScaleF0`, `twoScaleQc`, `twoScaleFc`, exact origin
  moments and mass `(ceo:O11y.4)`, full real-space CE seed inequality `(ceo:O11y.5)`,
  unconditional twisted-Laplace `g₁` decay and B-spline `M_{ψ,c}` witness, exact finite-`c`
  odd-Mellin origin tuning `(ceo:O11y.6)`–`(ceo:O11y.7)` with persistence of `F_c > 0`, and
  complementary compact/moving-far scale bounds `(ceo:O11y.8)`–`(ceo:O11y.9)`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Shared elementary and Airy-zero helpers -/

private lemma cohnC_sq_hasSum : HasSum (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2) (-airyDerivFirstZero) := by
  have h := hasSum_inv_sq airyDerivFirstZero (airyAi_ne_zero_of_deriv_zero airyDerivFirstZero_spec.2.2)
  rw [show cohnM airyDerivFirstZero = 0 by simp [cohnM, airyDerivFirstZero_spec.2.2], zero_pow two_ne_zero, zero_sub] at h
  exact h.congr_fun fun n => by rw [cohnC, inv_pow]; ring_nf

private lemma cohnC_tail_sq_hasSum :
    HasSum (fun n : ℕ => cohnC airyDerivFirstZero (n + 1) ^ 2) (-airyDerivFirstZero - cohnC airyDerivFirstZero 0 ^ 2) := by
  simpa [Finset.sum_range_one] using (hasSum_nat_add_iff' 1).mpr cohnC_sq_hasSum

private lemma ceVarphiP_pos {p x : ℝ} (hx : 0 ≤ x) : 0 < ceVarphiP p x := by
  unfold ceVarphiP; exact inv_pos.mpr (by linarith [Real.rpow_nonneg hx p])

private lemma ceVarphiP_le_one {p x : ℝ} (hx : 0 ≤ x) : ceVarphiP p x ≤ 1 := by
  unfold ceVarphiP; exact inv_le_one_of_one_le₀ (by linarith [Real.rpow_nonneg hx p])

private lemma one_sub_ceVarphiP_sq_nonneg {p x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - ceVarphiP p x ^ 2 := by
  have h0 := (ceVarphiP_pos (p := p) hx).le; have h1 := ceVarphiP_le_one (p := p) hx; nlinarith

private lemma one_sub_ceVarphiP_sq_le_one (p x : ℝ) : 1 - ceVarphiP p x ^ 2 ≤ 1 := by
  linarith [sq_nonneg (ceVarphiP p x)]

private lemma one_sub_ceVarphiP_sq_le_two_rpow {p x : ℝ} (hx : 0 ≤ x) : 1 - ceVarphiP p x ^ 2 ≤ 2 * x ^ p := by
  have h0 := (ceVarphiP_pos (p := p) hx).le; have h1 := ceVarphiP_le_one (p := p) hx
  have hxp : 0 ≤ x ^ p := Real.rpow_nonneg hx p
  have hle : 1 - ceVarphiP p x ≤ x ^ p := by
    unfold ceVarphiP; have hden : 0 < 1 + x ^ p := by linarith
    rw [show 1 - (1 + x ^ p)⁻¹ = x ^ p / (1 + x ^ p) by field_simp [hden.ne']; ring]; exact div_le_self hxp (by linarith)
  calc 1 - ceVarphiP p x ^ 2 = (1 + ceVarphiP p x) * (1 - ceVarphiP p x) := by ring
    _ ≤ 2 * x ^ p := mul_le_mul (by linarith) hle (by linarith) zero_le_two

private lemma airyZero_succ_ne {n m : ℕ} (h : n ≠ m) : airyZero (n + 1) ≠ airyZero (m + 1) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact (airyZero_lt_of_lt (n := n + 1) (m := m + 1) (by omega) (by omega)).ne'
  · exact (airyZero_lt_of_lt (n := m + 1) (m := n + 1) (by omega) (by omega)).ne

private lemma cohnE_succ_pos (m : ℕ) : 0 < cohnE (m + 1) := by
  unfold cohnE; linarith [airyZero_lt_of_lt (n := 1) (m := m + 2) le_rfl (by omega)]

private lemma compact_abs_bound {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) :
    ∃ M > 0, ∀ u ∈ Icc a b, |f u| ≤ M := by
  obtain ⟨u, _, hu⟩ := isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr hab⟩ hf.abs
  exact ⟨|f u| + 1, by positivity, fun _ hx => (hu hx).trans (by linarith)⟩

private lemma compact_pos_min {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ u ∈ Icc a b, 0 < f u) (hab : a ≤ b) : ∃ m > 0, ∀ u ∈ Icc a b, m ≤ f u := by
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨a, left_mem_Icc.mpr hab⟩ hf
  exact ⟨f u, hpos u hu, fun _ hx => hmin hx⟩

private lemma rpow_le_of_inv_rpow {x q A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) (hq : 0 < q) (h : x ≤ A ^ (1 / q)) :
    x ^ q ≤ A :=
  (Real.rpow_le_rpow hx h hq.le).trans_eq (by rw [← Real.rpow_mul hA, one_div_mul_cancel hq.ne', Real.rpow_one])

private lemma airyAi'_airyZero_abs_lower :
    ∃ c₀ > 0, ∀ n : ℕ, c₀ * (1 + |airyZero (n + 1)|) ^ (1 / 4 : ℝ) ≤ |airyAi' (airyZero (n + 1))| := by
  refine ⟨7 / 120, by norm_num, fun n => ?_⟩
  set y : ℝ := -airyZero (n + 1)
  have hy_ge : (2.33 : ℝ) < y := by dsimp [y]; linarith [airyZero_anti (by omega) (by omega : 1 ≤ n + 1), airyZero_one.2]
  have hy_pos : 0 < y := by linarith
  have hy3_gt : (9 : ℝ) < y ^ 3 := by have := pow_lt_pow_left₀ hy_ge (by norm_num) (by norm_num : 3 ≠ 0); linarith [show (9 : ℝ) < 2.33 ^ 3 by norm_num]
  have hy32_gt : (3 : ℝ) < y ^ (3 / 2 : ℝ) := by
    have hsq : (y ^ (3 / 2 : ℝ)) ^ 2 = y ^ 3 := by rw [← Real.rpow_natCast, ← Real.rpow_mul hy_pos.le]; norm_num
    nlinarith [Real.rpow_nonneg hy_pos.le (3 / 2 : ℝ)]
  have hy_neg32 : y ^ (-(3 / 2 : ℝ)) < 1 / 3 := by rw [Real.rpow_neg hy_pos.le, ← one_div]; exact one_div_lt_one_div_of_lt (by norm_num) hy32_gt
  have hpi4 : √π < 2 := by rw [show (2 : ℝ) = √(2 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]; exact Real.sqrt_lt_sqrt Real.pi_pos.le (by norm_num; exact Real.pi_lt_four)
  have hpi_pos : 0 < √π := Real.sqrt_pos.mpr Real.pi_pos; have hy14_pos : 0 < y ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hy_pos _
  set θ : ℝ := 2 / 3 * y ^ (3 / 2 : ℝ) - π / 4
  have hAi := airyAi_neg_asymptotic hy_pos
  rw [show airyAi (-y) = 0 by dsimp [y]; rw [neg_neg]; exact airyAi_airyZero (n + 1),
    zero_sub, abs_neg, abs_mul, abs_mul, abs_of_pos (div_pos one_pos hpi_pos), abs_of_pos (Real.rpow_pos_of_pos hy_pos _)] at hAi
  have hcos_le : |Real.cos θ| ≤ 1 / 2 := by
    have hdiv := div_le_div_of_nonneg_right hAi (Real.rpow_pos_of_pos hy_pos (-(1 / 4 : ℝ))).le
    have hsimp : (1 / √π * y ^ (-(1 / 4 : ℝ)) * |Real.cos θ|) / y ^ (-(1 / 4 : ℝ)) = |Real.cos θ| / √π := by
      field_simp [(Real.rpow_pos_of_pos hy_pos (-(1 / 4 : ℝ))).ne']
    rw [hsimp, show (1 / 8 * y ^ (-(7 / 4 : ℝ))) / y ^ (-(1 / 4 : ℝ)) = 1 / 8 * y ^ (-(3 / 2 : ℝ)) by
      rw [mul_div_assoc, ← Real.rpow_sub hy_pos]; norm_num] at hdiv
    nlinarith [(div_le_iff₀ hpi_pos).mp hdiv, hy_neg32, hpi4]
  have hsin_ge : 1 / 2 ≤ |Real.sin θ| := by
    have hsq := Real.sin_sq_add_cos_sq θ
    have hcsq : Real.cos θ ^ 2 ≤ 1 / 4 := by rw [← sq_abs]; nlinarith [abs_nonneg (Real.cos θ)]
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
    rw [show 2 / 5 * y ^ (-(5 / 4 : ℝ)) = (2 / 5 * y ^ (-(3 / 2 : ℝ))) * y ^ (1 / 4 : ℝ) by rw [mul_assoc, ← Real.rpow_add hy_pos]; norm_num]
    nlinarith [hy_neg32, hy14_pos]
  have h_y : 7 / 60 * y ^ (1 / 4 : ℝ) ≤ |airyAi' (-y)| := by linarith
  have h_one_add : (1 + |airyZero (n + 1)|) ^ (1 / 4 : ℝ) ≤ 2 * y ^ (1 / 4 : ℝ) := by
    rw [abs_of_neg (airyZero_neg (n + 1))]
    exact (Real.rpow_le_rpow (by positivity) (by linarith : 1 + -airyZero (n + 1) ≤ 16 * y) (by norm_num)).trans_eq
      (by rw [Real.mul_rpow (by norm_num) hy_pos.le, show (16 : ℝ) ^ (1 / 4 : ℝ) = 2 by
        rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num, ← Real.rpow_mul zero_le_two]; norm_num])
  rw [show -y = airyZero (n + 1) by dsimp [y]; ring] at h_y; linarith

/-! ### Part 1: Lemma `O.11x` (`ceo:O11x`) — Dirichlet vector of the moving diagonal complement -/

/-- Weighted Dirichlet vector `v_{S,h}(t)_n = √θ · c_n · √(1 - φ_p(h E_n)²) · φ_n(t)`
(`ce_o1_route.tex` `(ceo:O11x.4)`). With 0-indexed `n : ℕ`, `cohnE 0 = 0` so the `n = 0` entry vanishes. -/
noncomputable def dirichletVecS (p h θ t : ℝ) (n : ℕ) : ℝ :=
  √θ * cohnC airyDerivFirstZero n * √(1 - ceVarphiP p (h * cohnE n) ^ 2) * dirichletPhi n t

private lemma dirichletPhi_abs_le : ∃ C > 0, ∀ (n : ℕ) (t : ℝ), |dirichletPhi n t| ≤ C := by
  obtain ⟨c₀, hc₀, hderiv⟩ := airyAi'_airyZero_abs_lower
  refine ⟨3 / c₀, by positivity, fun n _ => ?_⟩
  have hden : c₀ ≤ |airyAi' (airyZero (n + 1))| :=
    (le_mul_of_one_le_right hc₀.le (Real.one_le_rpow (by linarith [abs_nonneg (airyZero (n + 1))]) (by norm_num))).trans (hderiv n)
  unfold dirichletPhi; rw [abs_div]; exact div_le_div₀ (by norm_num) (abs_airyAi_le_three _) hc₀ hden

private lemma dirichletPhi_linear_le :
    ∃ C > 0, ∀ (n : ℕ) {t : ℝ}, t ∈ Icc 0 1 → |dirichletPhi n t| ≤ C * t := by
  obtain ⟨c₀, hc₀, hderiv⟩ := airyAi'_airyZero_abs_lower
  refine ⟨5 / c₀, by positivity, fun n {t} ht => ?_⟩
  set w : ℝ := (1 + |airyZero (n + 1)|) ^ (1 / 4 : ℝ)
  have hw_pos : 0 < w := Real.rpow_pos_of_pos (by linarith [abs_nonneg (airyZero (n + 1))]) _
  have ha_le : airyZero (n + 1) ≤ airyZero 1 := airyZero_anti (by omega) (by omega)
  have hc : ∀ s : ℝ, HasDerivAt (fun x => airyAi (x + airyZero (n + 1))) (airyAi' (s + airyZero (n + 1))) s := fun s => by
    simpa [Function.comp_def] using (hasDerivAt_airyAi (s + airyZero (n + 1))).comp s ((hasDerivAt_id s).add_const (airyZero (n + 1)))
  have hbd : ∀ s ∈ Icc 0 t, ‖deriv (fun x => airyAi (x + airyZero (n + 1))) s‖ ≤ 5 * w := fun s hs => by
    have hle0 : s + airyZero (n + 1) ≤ 0 := by linarith [hs.2.trans ht.2, ha_le, airyZero_one.2]
    have habs_le : |s + airyZero (n + 1)| ≤ |airyZero (n + 1)| := by
      rw [abs_of_nonpos hle0, abs_of_neg (airyZero_neg (n + 1))]; linarith [hs.1]
    rw [(hc s).deriv, Real.norm_eq_abs]
    exact (abs_airyAi'_le_of_nonpos hle0).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)) (by norm_num))
  have hmvt : |airyAi (t + airyZero (n + 1))| ≤ 5 * w * t := by
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (fun s _ => (hc s).differentiableAt)
      hbd (convex_Icc 0 t) (left_mem_Icc.mpr ht.1) (right_mem_Icc.mpr ht.1)
    simpa [zero_add, airyAi_airyZero, Real.norm_eq_abs, abs_of_nonneg ht.1] using h
  unfold dirichletPhi; rw [abs_div]
  exact (div_le_div₀ (mul_nonneg (by positivity) ht.1) hmvt (mul_pos hc₀ hw_pos) (hderiv n)).trans_eq
    (by rw [show 5 * w * t / (c₀ * w) = (w / w) * (5 / c₀ * t) by ring, div_self hw_pos.ne', one_mul])

private lemma dirichletVecS_sq_eq {p h θ t : ℝ} (hh : 0 ≤ h) (hθ : 0 ≤ θ) (n : ℕ) :
    dirichletVecS p h θ t n ^ 2 =
      θ * cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) * dirichletPhi n t ^ 2 := by
  unfold dirichletVecS; rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hθ,
    Real.sq_sqrt (one_sub_ceVarphiP_sq_nonneg (mul_nonneg hh (cohnE_nonneg n)))]

/-- Square-summability of `dirichletVecS p h θ t` (`(ceo:O11x)`). -/
theorem dirichletVecS_sq_summable {p h θ : ℝ} (_hp : 0 < p) (hh : 0 ≤ h) (hθ : 0 ≤ θ) (t : ℝ) :
    Summable (fun n : ℕ => dirichletVecS p h θ t n ^ 2) := by
  obtain ⟨C, _, hC⟩ := dirichletPhi_abs_le
  refine (cohnC_sq_hasSum.summable.mul_left (θ * C ^ 2)).of_nonneg_of_le (fun _ => sq_nonneg _) fun n => ?_
  rw [dirichletVecS_sq_eq hh hθ n]
  have h1 := one_sub_ceVarphiP_sq_le_one p (h * cohnE n)
  have h2 : dirichletPhi n t ^ 2 ≤ C ^ 2 := by rw [← sq_abs (dirichletPhi n t)]; exact pow_le_pow_left₀ (abs_nonneg _) (hC n t) 2
  calc θ * cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) * dirichletPhi n t ^ 2
      ≤ θ * cohnC airyDerivFirstZero n ^ 2 * 1 * C ^ 2 := by gcongr
    _ = θ * C ^ 2 * cohnC airyDerivFirstZero n ^ 2 := by ring

private lemma dirichletVecS_tsum_le_of_phi {p h θ t B : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hθ : 0 ≤ θ)
    (_hB : 0 ≤ B) (hPhi : ∀ n : ℕ, |dirichletPhi n t| ≤ B) :
    ∑' n : ℕ, dirichletVecS p h θ t n ^ 2 ≤ B ^ 2 * (-airyDerivFirstZero) * θ := by
  have hle : ∀ n : ℕ, dirichletVecS p h θ t n ^ 2 ≤ θ * B ^ 2 * cohnC airyDerivFirstZero n ^ 2 := fun n => by
    rw [dirichletVecS_sq_eq hh hθ n]
    have h1 := one_sub_ceVarphiP_sq_le_one p (h * cohnE n)
    have h2 : dirichletPhi n t ^ 2 ≤ B ^ 2 := by rw [← sq_abs (dirichletPhi n t)]; exact pow_le_pow_left₀ (abs_nonneg _) (hPhi n) 2
    calc θ * cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) * dirichletPhi n t ^ 2
        ≤ θ * cohnC airyDerivFirstZero n ^ 2 * 1 * B ^ 2 := by gcongr
      _ = θ * B ^ 2 * cohnC airyDerivFirstZero n ^ 2 := by ring
  exact ((dirichletVecS_sq_summable hp hh hθ t).tsum_le_tsum hle (cohnC_sq_hasSum.summable.mul_left _)).trans_eq
    (by rw [tsum_mul_left, cohnC_sq_hasSum.tsum_eq]; ring)

/-- **Lemma `O.11x` (`(ceo:O11x.5)`), global `ℓ²` bound:** `∑_{n ≥ 2} v_{S,h}(t)_n² ≤ C θ` (`h, t ≥ 0`). -/
theorem dirichletVecS_l2_sq_bound :
    ∃ C > 0, ∀ {p h θ t : ℝ}, 0 < p → 0 ≤ h → 0 ≤ θ → 0 ≤ t → ∑' n : ℕ, dirichletVecS p h θ t n ^ 2 ≤ C * θ := by
  obtain ⟨C₀, hC₀, hPhi⟩ := dirichletPhi_abs_le
  have hM : 0 < -airyDerivFirstZero := neg_pos.mpr airyDerivFirstZero_spec.2.1
  exact ⟨C₀ ^ 2 * (-airyDerivFirstZero), by positivity, fun hp hh hθ _ => dirichletVecS_tsum_le_of_phi hp hh hθ hC₀.le (fun n => hPhi n _)⟩

/-- **Lemma `O.11x` (`(ceo:O11x.5)`), linear-at-zero `ℓ²` bound:** `∑_{n ≥ 2} v_{S,h}(t)_n² ≤ C θ t²` (`t ∈ [0, 1]`). -/
theorem dirichletVecS_l2_sq_linear_bound :
    ∃ C > 0, ∀ {p h θ t : ℝ}, 0 < p → 0 ≤ h → 0 ≤ θ → t ∈ Icc 0 1 → ∑' n : ℕ, dirichletVecS p h θ t n ^ 2 ≤ C * θ * t ^ 2 := by
  obtain ⟨C₁, hC₁, hPhi⟩ := dirichletPhi_linear_le
  have hM : 0 < -airyDerivFirstZero := neg_pos.mpr airyDerivFirstZero_spec.2.1
  refine ⟨C₁ ^ 2 * (-airyDerivFirstZero), by positivity, fun hp hh hθ ht =>
    (dirichletVecS_tsum_le_of_phi hp hh hθ (mul_nonneg hC₁.le ht.1) fun n => hPhi n ht).trans_eq (by ring)⟩

/-- **Lemma `O.11x` (`(ceo:O11x.5)`), combined `min t 1` `ℓ²` bound for all `t ≥ 0`.** -/
theorem dirichletVecS_l2_sq_min_bound :
    ∃ C > 0, ∀ {p h θ t : ℝ}, 0 < p → 0 ≤ h → 0 ≤ θ → 0 ≤ t →
      ∑' n : ℕ, dirichletVecS p h θ t n ^ 2 ≤ C * θ * (min t 1) ^ 2 := by
  obtain ⟨C_g, hC_g, hglob⟩ := dirichletVecS_l2_sq_bound; obtain ⟨C_l, hC_l, hlin⟩ := dirichletVecS_l2_sq_linear_bound
  refine ⟨max C_g C_l, lt_max_iff.mpr (Or.inl hC_g), fun {p h θ t} hp hh hθ ht => ?_⟩
  rcases le_or_gt t 1 with h1 | h1
  · rw [min_eq_left h1]; exact (hlin hp hh hθ ⟨ht, h1⟩).trans (by gcongr; exact le_max_right _ _)
  · rw [min_eq_right h1.le, one_pow, mul_one]; exact (hglob hp hh hθ ht).trans (by gcongr; exact le_max_left _ _)

/-! ### Part 2: Theorem `O.11w` unconditional — `movingDiagS`, mass, nodes, and compact bound -/

/-- Positive diagonal complement `S_h(u) = ∑_{n ≥ 2} c_n² (1 - φ_p(h E_n)²) L_n(u)²`
(`ce_o1_route.tex` `(ceo:O11w.3)`). Since `cohnE 0 = 0`, the `n = 0` term vanishes for `p > 0`. -/
noncomputable def movingDiagS (p h u : ℝ) : ℝ :=
  ∑' n : ℕ, cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) * cohnL n u ^ 2

/-- Far-tail cutoff profile `q_p(t) = 1 - φ_p(t)²` (`ce_o1_route.tex` `(ceo:O11w)`). -/
noncomputable def movingDiagQ (p t : ℝ) : ℝ := 1 - ceVarphiP p t ^ 2

lemma movingDiagS_eq_cohnS (p h u : ℝ) :
    movingDiagS p h u = cohnS airyDerivFirstZero (ceVarphiP p) h u := rfl

private lemma continuous_cohnL (n : ℕ) : Continuous (cohnL n) := by
  have h_eq : cohnL n = dslope airyAi (airyZero (n + 1)) := funext fun u => by
    by_cases hu : u = airyZero (n + 1)
    · subst hu; rw [cohnL_self, dslope_same, (hasDerivAt_airyAi _).deriv]
    · rw [cohnL_of_ne hu, dslope_of_ne _ hu, slope_def_field, airyAi_airyZero, sub_zero]
  rw [h_eq, ← continuousOn_univ, continuousOn_dslope univ_mem]
  exact ⟨differentiable_airyAi.continuous.continuousOn, differentiable_airyAi _⟩

private lemma cohn_tail_weighted_uniform_bound {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) {R : ℝ} (hR : 0 ≤ R) :
    ∃ C > 0, ∀ u ∈ Icc (-R) R,
      Summable (fun m : ℕ => cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * cohnL (m + 1) u ^ 2) ∧
      ∑' m : ℕ, cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * cohnL (m + 1) u ^ 2 ≤ C := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp (airyCft_eventually_ge (2 * (R + |airyDerivFirstZero| + 1)))
  let headBd : ℕ → ℝ := fun m => Classical.choose (compact_abs_bound ((continuous_cohnL (m + 1)).pow 2).continuousOn (by linarith : -R ≤ R))
  have hheadBd : ∀ m : ℕ, 0 < headBd m ∧ ∀ u ∈ Icc (-R) R, |cohnL (m + 1) u ^ 2| ≤ headBd m := fun m =>
    Classical.choose_spec (compact_abs_bound ((continuous_cohnL (m + 1)).pow 2).continuousOn (by linarith : -R ≤ R))
  let C_head : ℝ := ∑ m ∈ Finset.range M, cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * headBd m
  let e : ℝ := 2 * (4 - q) / 3
  have he : 1 < e := by dsimp [e]; linarith
  have htail_sum : Summable (fun m : ℕ => ((m + 2 : ℕ) : ℝ) ^ (-e)) :=
    ((summable_nat_add_iff 2).mpr (Real.summable_nat_rpow_inv.mpr he)).congr fun m => by
      rw [Real.rpow_neg (Nat.cast_nonneg _), inv_eq_one_div, one_div]
  let C_fac : ℝ := 144 * (2.5 : ℝ) ^ (q - 4)
  let C_tail : ℝ := C_fac * ∑' m : ℕ, ((m + 2 : ℕ) : ℝ) ^ (-e)
  have hC_head_nn : 0 ≤ C_head := Finset.sum_nonneg fun m _ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (cohnE_nonneg (m + 1)) _)) (hheadBd m).1.le
  have hC_tail_nn : 0 ≤ C_tail := mul_nonneg (by positivity) (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨C_head + C_tail + 1, by positivity, fun u huR => ?_⟩
  have hmaj : ∀ m : ℕ, M ≤ m →
      cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * cohnL (m + 1) u ^ 2 ≤ C_fac * ((m + 2 : ℕ) : ℝ) ^ (-e) := fun m hm => by
    have hge : 2 * (R + |airyDerivFirstZero| + 1) ≤ -airyZero (m + 2) := by simpa only [Nat.add_assoc] using hM (m + 1) (by omega)
    have hy_pos : 0 < -airyZero (m + 2) := neg_pos.mpr (airyZero_neg (m + 2))
    have hsep_u : (-airyZero (m + 2)) / 2 ≤ |u - airyZero (m + 2)| := by
      have h1 := abs_sub_abs_le_abs_sub (airyZero (m + 2)) u
      rw [abs_sub_comm, abs_of_neg (airyZero_neg (m + 2))] at h1; linarith [abs_le.mpr huR, abs_nonneg airyDerivFirstZero]
    have hsep_a : (-airyZero (m + 2)) / 2 ≤ |airyZero (m + 2) - airyDerivFirstZero| := by
      have h1 := abs_sub_abs_le_abs_sub (airyZero (m + 2)) airyDerivFirstZero
      rw [abs_of_neg (airyZero_neg (m + 2))] at h1; linarith [hR]
    have hne : u ≠ airyZero (m + 2) := fun h => by rw [h, sub_self, abs_zero] at hsep_u; linarith
    have hsq : (-airyZero (m + 2) / 2) ^ 2 = (-airyZero (m + 2)) ^ 2 / 4 := by ring
    have hinv2 : ((-airyZero (m + 2)) ^ 2)⁻¹ = (-airyZero (m + 2)) ^ (-2 : ℝ) := by
      rw [← Real.rpow_natCast (-airyZero (m + 2)) 2, show ((2 : ℕ) : ℝ) = (2 : ℝ) by norm_num, Real.rpow_neg hy_pos.le]
    have hL2 : cohnL (m + 1) u ^ 2 ≤ 36 * (-airyZero (m + 2)) ^ (-2 : ℝ) := by
      rw [show (m + 1) + 1 = m + 2 by ring] at hne; rw [cohnL_of_ne hne, div_pow, ← sq_abs (airyAi u), ← sq_abs (u - airyZero (m + 2))]
      exact (div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) (abs_airyAi_le_three u) 2) (by positivity)
        (pow_le_pow_left₀ (by positivity) hsep_u 2)).trans_eq (by rw [hsq, div_div_eq_mul_div, div_eq_mul_inv, hinv2]; ring)
    have hC2 : cohnC airyDerivFirstZero (m + 1) ^ 2 ≤ 4 * (-airyZero (m + 2)) ^ (-2 : ℝ) := by
      rw [cohnC, inv_pow, ← sq_abs (airyZero (m + 2) - airyDerivFirstZero)]
      exact (inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hsep_a 2)).trans_eq (by rw [hsq, inv_div, div_eq_mul_inv, hinv2])
    have hE_le : cohnE (m + 1) ^ q ≤ (-airyZero (m + 2)) ^ q :=
      Real.rpow_le_rpow (cohnE_nonneg (m + 1)) (by unfold cohnE; linarith [airyZero_neg 1]) hq0
    have hpow : (-airyZero (m + 2)) ^ (-2 : ℝ) * (-airyZero (m + 2)) ^ q * (-airyZero (m + 2)) ^ (-2 : ℝ) = (-airyZero (m + 2)) ^ (q - 4) := by
      rw [← Real.rpow_add hy_pos, ← Real.rpow_add hy_pos]; congr 1; ring
    have hcmp : (-airyZero (m + 2)) ^ (q - 4) ≤ (2.5 : ℝ) ^ (q - 4) * ((m + 2 : ℕ) : ℝ) ^ (-e) :=
      (Real.rpow_le_rpow_of_nonpos (by positivity) (airyZero_abs_bounds (n := m + 2) (by omega)).1 (by linarith)).trans_eq
        (by rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (Nat.cast_nonneg _)]; congr 2; dsimp [e]; ring)
    calc cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * cohnL (m + 1) u ^ 2
        ≤ (4 * (-airyZero (m + 2)) ^ (-2 : ℝ)) * (-airyZero (m + 2)) ^ q * (36 * (-airyZero (m + 2)) ^ (-2 : ℝ)) := by gcongr; exact Real.rpow_nonneg (cohnE_nonneg (m + 1)) q
      _ = 144 * (-airyZero (m + 2)) ^ (q - 4) := by rw [← hpow]; ring
      _ ≤ C_fac * ((m + 2 : ℕ) : ℝ) ^ (-e) := (mul_le_mul_of_nonneg_left hcmp (by norm_num)).trans_eq (by dsimp [C_fac]; ring)
  have hsum : Summable (fun m : ℕ => cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * cohnL (m + 1) u ^ 2) := by
    rw [← summable_nat_add_iff M]
    exact ((summable_nat_add_iff M).mpr htail_sum |>.mul_left C_fac).of_nonneg_of_le
      (fun _ => mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (cohnE_nonneg _) _)) (sq_nonneg _)) fun k => hmaj (k + M) (by omega)
  refine ⟨hsum, ?_⟩
  have hhead : ∑ m ∈ Finset.range M, cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ q * cohnL (m + 1) u ^ 2 ≤ C_head :=
    Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left ((le_abs_self _).trans ((hheadBd m).2 u huR))
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (cohnE_nonneg (m + 1)) _))
  have htail : ∑' k : ℕ, cohnC airyDerivFirstZero (k + M + 1) ^ 2 * cohnE (k + M + 1) ^ q * cohnL (k + M + 1) u ^ 2 ≤ C_tail := by
    have hle_sum := ((summable_nat_add_iff M).mpr hsum).tsum_le_tsum (fun k => hmaj (k + M) (by omega))
      (((summable_nat_add_iff M).mpr htail_sum).mul_left C_fac)
    have hrem : ∑' k : ℕ, ((k + M + 2 : ℕ) : ℝ) ^ (-e) ≤ ∑' m : ℕ, ((m + 2 : ℕ) : ℝ) ^ (-e) := by
      linarith [htail_sum.sum_add_tsum_nat_add M, Finset.sum_nonneg fun m (_ : m ∈ Finset.range M) => Real.rpow_nonneg (Nat.cast_nonneg (m + 2)) (-e)]
    rw [tsum_mul_left] at hle_sum; exact hle_sum.trans (mul_le_mul_of_nonneg_left hrem (by positivity))
  rw [← hsum.sum_add_tsum_nat_add M]; linarith

private lemma cohnL_sq_bounded_at (u : ℝ) : ∃ K > 0, ∀ n : ℕ, cohnL n u ^ 2 ≤ K := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (airyCft_eventually_ge (2 * (|u| + 1)))
  let K_fin := (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ (fun k => cohnL k u ^ 2)
  refine ⟨max K_fin 9 + 1, by positivity, fun n => ?_⟩
  by_cases hn : n < N + 1
  · exact (Finset.le_sup' (fun k => cohnL k u ^ 2) (Finset.mem_range.mpr hn)).trans ((le_max_left _ _).trans (by linarith))
  · have hsep : 1 ≤ |u - airyZero (n + 1)| := by
      have h1 := abs_sub_abs_le_abs_sub (airyZero (n + 1)) u
      rw [abs_sub_comm, abs_of_neg (airyZero_neg (n + 1))] at h1; linarith [hN n (by omega), abs_nonneg u]
    have hne : u ≠ airyZero (n + 1) := fun h => by rw [h, sub_self, abs_zero] at hsep; linarith
    rw [cohnL_of_ne hne, div_pow, ← sq_abs (airyAi u), ← sq_abs (u - airyZero (n + 1))]
    exact (div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) (abs_airyAi_le_three u) 2) (by positivity)
      (pow_le_pow_left₀ (by positivity) hsep 2)).trans (by norm_num; linarith [le_max_right K_fin 9])

private lemma summable_cohnT_all (u : ℝ) : Summable (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2 * cohnL n u ^ 2) := by
  obtain ⟨K, _, hK⟩ := cohnL_sq_bounded_at u
  exact (cohnC_sq_hasSum.summable.mul_right K).of_nonneg_of_le (fun _ => by positivity) fun n => mul_le_mul_of_nonneg_left (hK n) (sq_nonneg _)

private lemma cohnT_compact_bound {R : ℝ} (hR : 0 ≤ R) : ∃ C > 0, ∀ u ∈ Icc (-R) R, cohnT airyDerivFirstZero u ≤ C := by
  obtain ⟨C_tail, _, htail⟩ := cohn_tail_weighted_uniform_bound le_rfl zero_lt_one hR
  obtain ⟨M₀, _, hL0⟩ := compact_abs_bound ((continuous_cohnL 0).pow 2).continuousOn (by linarith : -R ≤ R)
  refine ⟨cohnC airyDerivFirstZero 0 ^ 2 * M₀ + C_tail, by positivity, fun u hu => ?_⟩
  unfold cohnT; rw [(summable_cohnT_all u).tsum_eq_zero_add]
  have h0 := mul_le_mul_of_nonneg_left ((le_abs_self (cohnL 0 u ^ 2)).trans (hL0 u hu)) (sq_nonneg (cohnC airyDerivFirstZero 0))
  have h1 : (∑' m : ℕ, cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnL (m + 1) u ^ 2) ≤ C_tail := by simpa [Real.rpow_zero] using (htail u hu).2
  exact add_le_add h0 h1

lemma movingDiagS_summable {p h : ℝ} (_hp : 0 < p) (hh : 0 ≤ h) (u : ℝ) :
    Summable (fun n : ℕ => cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) * cohnL n u ^ 2) :=
  (summable_cohnT_all u).of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg (sq_nonneg _) (one_sub_ceVarphiP_sq_nonneg (mul_nonneg hh (cohnE_nonneg n)))) (sq_nonneg _))
    fun n => (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg _) (one_sub_ceVarphiP_sq_le_one p (h * cohnE n))) (sq_nonneg _))

lemma movingDiagS_eq_tsum_succ {p h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (u : ℝ) :
    movingDiagS p h u = ∑' m : ℕ, cohnC airyDerivFirstZero (m + 1) ^ 2 *
        (1 - ceVarphiP p (h * cohnE (m + 1)) ^ 2) * cohnL (m + 1) u ^ 2 := by
  unfold movingDiagS; rw [(movingDiagS_summable hp hh u).tsum_eq_zero_add]
  have hφ0 : ceVarphiP p (h * cohnE 0) = 1 := by
    rw [show cohnE 0 = 0 by simp [cohnE], mul_zero]; unfold ceVarphiP; rw [Real.zero_rpow hp.ne']; norm_num
  rw [hφ0, one_pow, sub_self, mul_zero, zero_mul, zero_add]

/-- **Theorem `O.11w` (`(ceo:O11w.3)`):** nonnegativity `0 ≤ S_h(u)`. -/
theorem movingDiagS_nonneg {p h : ℝ} (_hp : 0 < p) (hh : 0 ≤ h) (u : ℝ) : 0 ≤ movingDiagS p h u :=
  tsum_nonneg fun n => mul_nonneg (mul_nonneg (sq_nonneg _) (one_sub_ceVarphiP_sq_nonneg (mul_nonneg hh (cohnE_nonneg n)))) (sq_nonneg _)

/-- Domination by the full cardinal resolvent diagonal `S_h(u) ≤ T(u)` (`(ceo:O11w)`). -/
theorem movingDiagS_le_cohnT {p h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (u : ℝ) : movingDiagS p h u ≤ cohnT airyDerivFirstZero u :=
  (movingDiagS_summable hp hh u).tsum_le_tsum (fun n =>
    mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (sq_nonneg _) (one_sub_ceVarphiP_sq_le_one p (h * cohnE n))) (sq_nonneg _))
    (summable_cohnT_all u)

private lemma ennreal_ofReal_tsum_eq {f : ℕ → ℝ} (hf_nn : ∀ n, 0 ≤ f n) (hf : Summable f) :
    ∑' n : ℕ, ENNReal.ofReal (f n) = ENNReal.ofReal (∑' n : ℕ, f n) := by
  rw [ENNReal.tsum_eq_iSup_nat, show (fun N : ℕ => ∑ n ∈ Finset.range N, ENNReal.ofReal (f n)) =
      fun N => ENNReal.ofReal (∑ n ∈ Finset.range N, f n) from funext fun N => (ENNReal.ofReal_sum_of_nonneg fun n _ => hf_nn n).symm]
  exact tendsto_nhds_unique (tendsto_atTop_iSup fun a b hab => ENNReal.ofReal_le_ofReal
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun n _ _ => hf_nn n))
    (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hf.hasSum.tendsto_sum_nat)

/-- **Theorem `O.11w` (`(ceo:O11w.4)`), exact mass identity:**
`movingDiagS p h` is integrable and `∫ u, movingDiagS p h u = cardinalDh p h` (`p > 0, h ≥ 0`). -/
theorem movingDiagS_integral {p h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) :
    Integrable (movingDiagS p h) ∧ ∫ u : ℝ, movingDiagS p h u = cardinalDh p h := by
  let a : ℕ → ℝ := fun m => cohnC airyDerivFirstZero (m + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (m + 1)) ^ 2)
  have ha_nn : ∀ m : ℕ, 0 ≤ a m := fun m => mul_nonneg (sq_nonneg _) (one_sub_ceVarphiP_sq_nonneg (mul_nonneg hh (cohnE_nonneg (m + 1))))
  have ha_sum : Summable a := cohnC_tail_sq_hasSum.summable.of_nonneg_of_le ha_nn fun m =>
    mul_le_of_le_one_right (sq_nonneg _) (one_sub_ceVarphiP_sq_le_one p (h * cohnE (m + 1)))
  let g : ℕ → ℝ → ℝ := fun m u => a m * cohnL (m + 1) u ^ 2
  have hg_nn : ∀ m u, 0 ≤ g m u := fun m u => mul_nonneg (ha_nn m) (sq_nonneg _)
  have hg_meas : ∀ m : ℕ, Measurable (g m) := fun m => measurable_const.mul ((continuous_cohnL (m + 1)).pow 2).measurable
  have hS_eq : movingDiagS p h = fun u => ∑' m : ℕ, g m u := funext fun u => movingDiagS_eq_tsum_succ hp hh u
  have hS_meas : Measurable (movingDiagS p h) := by
    rw [hS_eq]
    exact measurable_of_tendsto_metrizable (fun N => Finset.measurable_sum _ fun m _ => hg_meas m)
      (tendsto_pi_nhds.mpr fun u => ((movingDiagS_summable hp hh u).comp_injective Nat.succ_injective).hasSum.tendsto_sum_nat)
  have hg_int : ∀ m : ℕ, Integrable (g m) ∧ ∫ u : ℝ, g m u = a m := fun m => by
    have hL := cohnL_integral_mul (m + 1) (m + 1); simp only [ite_true, ← sq] at hL
    exact ⟨hL.1.const_mul (a m), by rw [integral_const_mul, hL.2, mul_one]⟩
  have hlint_S : (∫⁻ u : ℝ, ENNReal.ofReal (movingDiagS p h u)) = ENNReal.ofReal (cardinalDh p h) := by
    have h_ofReal_eq : (fun u => ENNReal.ofReal (movingDiagS p h u)) = fun u => ∑' m : ℕ, ENNReal.ofReal (g m u) :=
      funext fun u => by rw [hS_eq]; exact (ennreal_ofReal_tsum_eq (fun m => hg_nn m u)
        ((movingDiagS_summable hp hh u).comp_injective Nat.succ_injective)).symm
    rw [h_ofReal_eq, lintegral_tsum fun m => (hg_meas m).ennreal_ofReal.aemeasurable]
    simp_rw [fun m => (ofReal_integral_eq_lintegral_ofReal (hg_int m).1 (ae_of_all _ (hg_nn m))).symm, fun m => (hg_int m).2]
    exact ennreal_ofReal_tsum_eq ha_nn ha_sum
  have hint_S : Integrable (movingDiagS p h) := ⟨hS_meas.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_norm, show (fun u => ENNReal.ofReal ‖movingDiagS p h u‖) = fun u => ENNReal.ofReal (movingDiagS p h u)
      from funext fun u => by rw [Real.norm_of_nonneg (movingDiagS_nonneg hp hh u)], hlint_S]
    exact ENNReal.ofReal_lt_top⟩
  refine ⟨hint_S, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint_S (ae_of_all _ (movingDiagS_nonneg hp hh))
  rw [hlint_S] at h1
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (movingDiagS_nonneg hp hh)) (by unfold cardinalDh; exact tsum_nonneg ha_nn)).mp h1

/-- **Theorem `O.11w` (`(ceo:O11w.4)`):** complete mass, positivity, and `J_{2,p} √h + o(√h)` asymptotic. -/
theorem movingDiagS_integral_asymptotic {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) :
    (∀ {h : ℝ}, 0 < h → Integrable (cardinalQ p h 1) ∧ ∫ u : ℝ, cardinalQ p h 1 u = 0 ∧
      (∀ u : ℝ, 0 ≤ movingDiagS p h u) ∧ Integrable (movingDiagS p h) ∧
      ∫ u : ℝ, movingDiagS p h u = cardinalDh p h) ∧
    (∃ C > 0, ∀ {h : ℝ}, 0 < h → |(∫ u : ℝ, movingDiagS p h u) - fracJ2 p * √h| ≤ C * h ^ p) ∧
    Tendsto (fun h : ℝ => ((∫ u : ℝ, movingDiagS p h u) - fracJ2 p * √h) / √h) (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := by linarith [hp.1]
  obtain ⟨C, hC, hD⟩ := cardinalDh_asymptotic_pos hp
  refine ⟨fun {h} hh => ?_, ⟨C, hC, fun {h} hh => ?_⟩, ?_⟩
  · have hpq := cardinalPQ_integrals hp0 hh.le zero_le_one le_rfl; have hms := movingDiagS_integral hp0 hh.le
    exact ⟨hpq.2.2.1, hpq.2.2.2, movingDiagS_nonneg hp0 hh.le, hms.1, hms.2⟩
  · rw [(movingDiagS_integral hp0 hh.le).2]; exact hD hh
  · refine (cardinalDh_littleO hp).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh; rw [(movingDiagS_integral hp0 (mem_Ioi.mp hh).le).2]

/-- **Theorem `O.11w` (`(ceo:O11w.7)`), exact node matching:**
for every `n ≥ 1` (`a_{n+1}`), `Q_h(a_{n+1}) = S_h(a_{n+1}) = Ai'(a_{n+1})² c_n² (1 - φ_n²) > 0`. -/
theorem movingDiagS_node_eq {p h : ℝ} (hp : 0 < p) (hh : 0 < h) {n : ℕ} (hn : 1 ≤ n) :
    cardinalQ p h 1 (airyZero (n + 1)) = movingDiagS p h (airyZero (n + 1)) ∧
    movingDiagS p h (airyZero (n + 1)) =
      airyAi' (airyZero (n + 1)) ^ 2 * cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) ∧
    0 < movingDiagS p h (airyZero (n + 1)) := by
  set u := airyZero (n + 1)
  have hS_eq : movingDiagS p h u =
      airyAi' u ^ 2 * cohnC airyDerivFirstZero n ^ 2 * (1 - ceVarphiP p (h * cohnE n) ^ 2) := by
    unfold movingDiagS; rw [tsum_eq_single n]
    · rw [cohnL_self]; ring
    · intro m hm; rw [cohnL_of_ne (airyZero_succ_ne hm.symm), airyAi_airyZero, zero_div, zero_pow two_ne_zero, mul_zero]
  have hH_eq : cardinalH p h 1 u = cardinalB p h 1 n * airyAi' u := by
    have hs := (cardinalH_hasSum hp hh.le zero_le_one le_rfl).2 u; rw [← hs.tsum_eq, tsum_eq_single n]
    · rw [cohnL_self]
    · intro m hm; rw [cohnL_of_ne (airyZero_succ_ne hm.symm), airyAi_airyZero, zero_div, mul_zero]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hb_eq : cardinalB p h 1 (m + 1) = cohnC airyDerivFirstZero (m + 1) * ceVarphiP p (h * cohnE (m + 1)) := by simp [cardinalB]
  have hF1_zero : ceF1 u = 0 := by unfold ceF1; rw [show airyAi u = 0 from airyAi_airyZero _, zero_mul]
  have hua' : u ≠ airyDerivFirstZero :=
    (lt_trans (airyZero_lt_of_lt (n := 1) (m := m + 2) le_rfl (by omega)) airyDerivFirstZero_spec.1).ne
  have hG1'_eq : ceG1Deriv airyDerivFirstZero u = airyAi' u ^ 2 * cohnC airyDerivFirstZero (m + 1) ^ 2 := by
    unfold ceG1Deriv; rw [dslope_of_ne _ hua', slope_def_field, airyDerivFirstZero_spec.2.2, sub_zero, cohnC, div_pow, inv_pow]; ring
  have hQ_eq : cardinalQ p h 1 u = movingDiagS p h u := by
    unfold cardinalQ cardinalP; rw [hF1_zero, neg_zero, zero_add, hG1'_eq, hH_eq, hb_eq, hS_eq]; ring
  have hpos : 0 < movingDiagS p h u := by
    rw [hS_eq]
    obtain ⟨c₀, hc₀, hderiv⟩ := airyAi'_airyZero_abs_lower
    have hAi'_nz : airyAi' u ≠ 0 :=
      abs_pos.mp (hc₀.trans_le ((le_mul_of_one_le_right hc₀.le (Real.one_le_rpow
        (by linarith [abs_nonneg u]) (by norm_num))).trans (hderiv (m + 1))))
    have hC_nz : cohnC airyDerivFirstZero (m + 1) ≠ 0 := by rw [cohnC]; exact inv_ne_zero (sub_ne_zero.mpr hua')
    have ht_pos : 0 < h * cohnE (m + 1) := mul_pos hh (cohnE_succ_pos m)
    have hφ_lt : ceVarphiP p (h * cohnE (m + 1)) < 1 := by
      unfold ceVarphiP; exact inv_lt_one_of_one_lt₀ (by linarith [Real.rpow_pos_of_pos ht_pos p])
    have hφ_nn := (ceVarphiP_pos (p := p) ht_pos.le).le
    exact mul_pos (mul_pos (sq_pos_of_ne_zero hAi'_nz) (sq_pos_of_ne_zero hC_nz)) (by nlinarith)
  exact ⟨hQ_eq, hS_eq, hpos⟩

/-- **Theorem `O.11w` (`(ceo:O11w.9)`), compact bound:**
for `p ∈ (0, 1)` and every compact `U ⊂ ℝ`, `S_h(u) ≤ C_U h^p` uniformly for `h > 0` and `u ∈ U`. -/
theorem movingDiagS_compact_bound {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {U : Set ℝ} (hU : IsCompact U) :
    ∃ C > 0, ∀ {h u : ℝ}, 0 < h → u ∈ U → movingDiagS p h u ≤ C * h ^ p := by
  rcases U.eq_empty_or_nonempty with rfl | _
  · exact ⟨1, one_pos, fun _ hu => hu.elim⟩
  obtain ⟨R₀, hR₀⟩ := hU.isBounded.subset_closedBall 0
  set R : ℝ := max R₀ 0
  have hU_sub : U ⊆ Icc (-R) R := fun u hu => by
    have hd := hR₀ hu; rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hd
    exact abs_le.mp (hd.trans (le_max_left _ _))
  obtain ⟨C_tail, hC_tail, htail⟩ := cohn_tail_weighted_uniform_bound hp.1.le hp.2 (le_max_right R₀ 0)
  refine ⟨2 * C_tail, by positivity, fun {h u} hh hu => ?_⟩
  obtain ⟨hsum_maj, hle_maj⟩ := htail u (hU_sub hu)
  have hterm : ∀ m : ℕ,
      cohnC airyDerivFirstZero (m + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (m + 1)) ^ 2) * cohnL (m + 1) u ^ 2 ≤
        2 * h ^ p * (cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ p * cohnL (m + 1) u ^ 2) := fun m => by
    have hφ := one_sub_ceVarphiP_sq_le_two_rpow (p := p) (mul_nonneg hh.le (cohnE_nonneg (m + 1)))
    rw [Real.mul_rpow hh.le (cohnE_nonneg (m + 1))] at hφ
    calc cohnC airyDerivFirstZero (m + 1) ^ 2 * (1 - ceVarphiP p (h * cohnE (m + 1)) ^ 2) * cohnL (m + 1) u ^ 2
        ≤ cohnC airyDerivFirstZero (m + 1) ^ 2 * (2 * (h ^ p * cohnE (m + 1) ^ p)) * cohnL (m + 1) u ^ 2 := by gcongr
      _ = 2 * h ^ p * (cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ p * cohnL (m + 1) u ^ 2) := by ring
  rw [movingDiagS_eq_tsum_succ hp.1 hh.le u]
  calc ∑' m : ℕ, cohnC airyDerivFirstZero (m + 1) ^ 2 *
          (1 - ceVarphiP p (h * cohnE (m + 1)) ^ 2) * cohnL (m + 1) u ^ 2
      ≤ ∑' m : ℕ, 2 * h ^ p * (cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ p * cohnL (m + 1) u ^ 2) :=
        ((movingDiagS_summable hp.1 hh.le u).comp_injective Nat.succ_injective).tsum_le_tsum
          hterm (hsum_maj.mul_left _)
    _ = 2 * h ^ p * ∑' m : ℕ, cohnC airyDerivFirstZero (m + 1) ^ 2 * cohnE (m + 1) ^ p * cohnL (m + 1) u ^ 2 :=
        tsum_mul_left
    _ ≤ 2 * h ^ p * C_tail := by gcongr
    _ = (2 * C_tail) * h ^ p := by ring

/-! ### Part 3: Theorem `O.11w` (`(ceo:O11w.12)` → `(ceo:O11w.5)–(6), (10)–(11)`) -/

/-- The `CR.4` far-tail estimate (`ce_o1_route.tex` `(ceo:O11w.12)`) for `movingDiagS`:
`S_h(-x) = q_p(h x) (π x^{3/2})⁻¹ [1 + O(x⁻¹)]` uniformly in `h > 0` and `x ≥ x₀`. -/
def MovingDiagFarTail (p : ℝ) : Prop :=
  ∃ x₀ ≥ 1, ∃ C > 0, ∀ {h x : ℝ}, 0 < h → x₀ ≤ x →
    |movingDiagS p h (-x) - movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ))| ≤
      C * movingDiagQ p (h * x) * x ^ (-(5 / 2 : ℝ))

private lemma movingDiagQ_nonneg {p t : ℝ} (ht : 0 ≤ t) : 0 ≤ movingDiagQ p t :=
  one_sub_ceVarphiP_sq_nonneg ht

private lemma movingDiagQ_le_one (p t : ℝ) : movingDiagQ p t ≤ 1 :=
  one_sub_ceVarphiP_sq_le_one p t

private lemma one_sub_movingDiagQ_le {p t : ℝ} (_hp : 0 < p) (ht : 1 ≤ t) :
    1 - movingDiagQ p t ≤ t ^ (-(2 * p)) := by
  unfold movingDiagQ ceVarphiP
  have ht0 : 0 < t := by linarith
  have htp : 0 < t ^ p := Real.rpow_pos_of_pos ht0 p
  rw [show 1 - (1 - (1 + t ^ p)⁻¹ ^ 2) = (1 + t ^ p)⁻¹ ^ 2 by ring,
    ← Real.rpow_neg_one (1 + t ^ p), ← Real.rpow_natCast ((1 + t ^ p) ^ (-1 : ℝ)) 2,
    ← Real.rpow_mul (by positivity), show (-1 : ℝ) * (2 : ℕ) = -2 by norm_num]
  calc (1 + t ^ p) ^ (-2 : ℝ) ≤ (t ^ p) ^ (-2 : ℝ) := Real.rpow_le_rpow_of_nonpos htp (by linarith) (by norm_num)
    _ = t ^ (-(2 * p)) := by rw [← Real.rpow_mul ht0.le]; congr 1; ring

private lemma rpow_neg_five_halves {x : ℝ} (hx : 0 < x) : x ^ (-(5 / 2 : ℝ)) = x⁻¹ / x ^ (3 / 2 : ℝ) := by
  calc x ^ (-(5 / 2 : ℝ)) = x ^ ((-1 : ℝ) + -(3 / 2 : ℝ)) := by congr 1; norm_num
    _ = x⁻¹ / x ^ (3 / 2 : ℝ) := by rw [Real.rpow_add hx, Real.rpow_neg_one, Real.rpow_neg hx.le, ← div_eq_mul_inv]

/-- **Theorem `O.11w` (`(ceo:O11w.5)`), moving far-tail asymptotic (`x ≥ 1, h x ≥ 1`).** -/
theorem movingDiagS_far_asymptotic {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) :
    ∃ C₁ > 0, ∃ C₂ > 0, ∀ {h x : ℝ}, 0 < h → 1 ≤ x → 1 ≤ h * x →
      |movingDiagS p h (-x) - 1 / (π * x ^ (3 / 2 : ℝ))| ≤ (C₁ * x⁻¹ + C₂ * (h * x) ^ (-(2 * p))) / (π * x ^ (3 / 2 : ℝ)) := by
  have hp0 : 0 < p := by linarith [hp.1]
  obtain ⟨x₀, _, C, hC, hfar⟩ := hft; obtain ⟨M_T, _, hT_bd⟩ := cohnT_compact_bound (by linarith : 0 ≤ x₀)
  let C₁ : ℝ := max (π * C) ((M_T + 1 / π) * π * x₀ ^ (5 / 2 : ℝ))
  refine ⟨C₁, by positivity, 1, one_pos, fun {h x} hh hx1 hhx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hden_pos : 0 < π * x ^ (3 / 2 : ℝ) := by positivity
  by_cases hxx₀ : x₀ ≤ x
  · have hrem1 : |movingDiagS p h (-x) - movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ))| ≤ (C₁ * x⁻¹) / (π * x ^ (3 / 2 : ℝ)) := calc
      _ ≤ C * movingDiagQ p (h * x) * x ^ (-(5 / 2 : ℝ)) := hfar hh hxx₀
      _ ≤ C * 1 * x ^ (-(5 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (movingDiagQ_le_one p _) hC.le) (Real.rpow_nonneg hx0.le _)
      _ = (π * C) * x⁻¹ / (π * x ^ (3 / 2 : ℝ)) := by rw [mul_one, rpow_neg_five_halves hx0, ← mul_div_assoc, ← mul_div_mul_left _ _ Real.pi_ne_zero, mul_assoc]
      _ ≤ (C₁ * x⁻¹) / (π * x ^ (3 / 2 : ℝ)) := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hx0.le)) hden_pos.le
    have hrem2 : |(movingDiagQ p (h * x) - 1) / (π * x ^ (3 / 2 : ℝ))| ≤ (1 * (h * x) ^ (-(2 * p))) / (π * x ^ (3 / 2 : ℝ)) := by
      rw [abs_div, abs_of_pos hden_pos, abs_sub_comm, abs_of_nonneg (by linarith [movingDiagQ_le_one p (h * x)]), one_mul]
      exact div_le_div_of_nonneg_right (one_sub_movingDiagQ_le hp0 hhx) hden_pos.le
    rw [show movingDiagS p h (-x) - 1 / (π * x ^ (3 / 2 : ℝ)) =
      (movingDiagS p h (-x) - movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ))) + (movingDiagQ p (h * x) - 1) / (π * x ^ (3 / 2 : ℝ)) by ring]
    exact ((abs_add_le _ _).trans (add_le_add hrem1 hrem2)).trans_eq (by ring)
  · have hS_le := (movingDiagS_le_cohnT hp0 hh.le (-x)).trans (hT_bd (-x) ⟨by linarith [le_of_not_ge hxx₀], by linarith⟩)
    have hS_nn := movingDiagS_nonneg hp0 hh.le (-x)
    have h1x_le : 1 / (π * x ^ (3 / 2 : ℝ)) ≤ 1 / π :=
      div_le_div_of_nonneg_left zero_le_one Real.pi_pos (by nlinarith [Real.one_le_rpow hx1 (by norm_num : (0 : ℝ) ≤ 3 / 2)])
    have hdiff_le : |movingDiagS p h (-x) - 1 / (π * x ^ (3 / 2 : ℝ))| ≤ M_T + 1 / π :=
      (abs_sub _ _).trans (by rw [abs_of_nonneg hS_nn, abs_of_nonneg (by positivity)]; exact add_le_add hS_le h1x_le)
    have hx_eq : x ^ (5 / 2 : ℝ) = x * x ^ (3 / 2 : ℝ) := by nth_rw 2 [← Real.rpow_one x]; rw [← Real.rpow_add hx0]; norm_num
    have hpow_le : (M_T + 1 / π) * (π * x ^ (3 / 2 : ℝ)) * x ≤ C₁ := calc
      _ = (M_T + 1 / π) * π * x ^ (5 / 2 : ℝ) := by rw [hx_eq]; ring
      _ ≤ (M_T + 1 / π) * π * x₀ ^ (5 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le (le_of_not_ge hxx₀) (by norm_num)) (by positivity)
      _ ≤ C₁ := le_max_right _ _
    have h1 : M_T + 1 / π ≤ (C₁ * x⁻¹) / (π * x ^ (3 / 2 : ℝ)) := by
      rw [le_div_iff₀ hden_pos]
      exact (le_of_eq (by rw [mul_assoc _ x x⁻¹, mul_inv_cancel₀ hx0.ne', mul_one])).trans (mul_le_mul_of_nonneg_right hpow_le (inv_nonneg.mpr hx0.le))
    calc _ ≤ M_T + 1 / π := hdiff_le
      _ ≤ (C₁ * x⁻¹) / (π * x ^ (3 / 2 : ℝ)) := h1
      _ ≤ (C₁ * x⁻¹ + 1 * (h * x) ^ (-(2 * p))) / (π * x ^ (3 / 2 : ℝ)) :=
          div_le_div_of_nonneg_right (le_add_of_nonneg_right (mul_nonneg zero_le_one (Real.rpow_nonneg (mul_pos hh hx0).le _))) hden_pos.le

/-- **Theorem `O.11w` (`(ceo:O11w.6)`), moving far-tail floor:**
for any `ε₀ > 0`, `∃ T > 0` such that for `0 < h ≤ 1` and `x ≥ T / h`, `S_h(-x) ≥ (1 - ε₀) / (π x^{3/2})`. -/
theorem movingDiagS_far_floor {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ T > 0, ∀ {h x : ℝ}, 0 < h → h ≤ 1 → T / h ≤ x → (1 - ε₀) / (π * x ^ (3 / 2 : ℝ)) ≤ movingDiagS p h (-x) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, hasy⟩ := movingDiagS_far_asymptotic hp hft
  set T : ℝ := max 1 (max (2 * C₁ / ε₀) ((2 * C₂ / ε₀) ^ (1 / (2 * p))))
  refine ⟨T, one_pos.trans_le (le_max_left _ _), fun {h x} hh hh1 hx => ?_⟩
  have hT1 : 1 ≤ T := le_max_left _ _; have hhx : T ≤ h * x := (div_le_iff₀' hh).mp hx
  have hx0 : 0 ≤ x := (div_pos (one_pos.trans_le hT1) hh).le.trans hx
  have hTx : T ≤ x := hhx.trans (mul_le_of_le_one_left hx0 hh1)
  have hx1 : 1 ≤ x := hT1.trans hTx
  have hx_ge1 : 2 * C₁ / ε₀ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hTx
  have h1 : C₁ * x⁻¹ ≤ ε₀ / 2 := (mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hx_ge1) hC₁.le).trans_eq
    (by rw [inv_div, ← mul_div_assoc, mul_comm C₁ ε₀, mul_div_mul_right _ _ hC₁.ne'])
  have h2 : C₂ * (h * x) ^ (-(2 * p)) ≤ ε₀ / 2 := by
    have hp2 : 0 < 2 * p := mul_pos two_pos (lt_trans (by norm_num) hp.1)
    have hpow : 2 * C₂ / ε₀ ≤ (h * x) ^ (2 * p) :=
      (by rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hp2.ne', Real.rpow_one] :
        2 * C₂ / ε₀ = ((2 * C₂ / ε₀) ^ (1 / (2 * p))) ^ (2 * p)) ▸
        Real.rpow_le_rpow (by positivity) (((le_max_right _ _).trans (le_max_right _ _)).trans hhx) hp2.le
    calc C₂ * (h * x) ^ (-(2 * p)) ≤ C₂ * (2 * C₂ / ε₀)⁻¹ := by rw [Real.rpow_neg (by positivity)]; exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hpow) hC₂.le
      _ = ε₀ / 2 := by rw [inv_div, ← mul_div_assoc, mul_comm C₂ ε₀, mul_div_mul_right _ _ hC₂.ne']
  have herr := (hasy hh hx1 (hT1.trans hhx)).trans
    (div_le_div_of_nonneg_right ((add_le_add h1 h2).trans_eq (add_halves ε₀)) (by positivity))
  calc (1 - ε₀) / (π * x ^ (3 / 2 : ℝ)) = 1 / (π * x ^ (3 / 2 : ℝ)) + -(ε₀ / (π * x ^ (3 / 2 : ℝ))) := by ring
    _ ≤ 1 / (π * x ^ (3 / 2 : ℝ)) + (movingDiagS p h (-x) - 1 / (π * x ^ (3 / 2 : ℝ))) := add_le_add le_rfl (abs_le.mp herr).1
    _ = movingDiagS p h (-x) := by ring

private lemma uniform_B_far_lower {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) {v₀ : ℝ} (_hv₀ : 0 < v₀) :
    ∃ x₁ ≥ max 10 (|airyZero 1 - v₀| + 1),
      (∀ {x : ℝ}, x₁ ≤ x → (2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ)) ≤ ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) ∧
      (∀ {h x : ℝ}, 0 < h → x₁ ≤ x → movingDiagS p h (-x) ≤ 2 * movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ))) := by
  obtain ⟨x₀, _, C_ft, hC_ft, hfar⟩ := hft; obtain ⟨C_B, hC_B, hB⟩ := cardinalH_far_asymptotic hp
  set x₁ : ℝ := max (max x₀ (max 10 (|airyZero 1 - v₀| + 1))) (max (2 * π * C_B) (π * C_ft))
  refine ⟨x₁, (le_max_right _ _).trans (le_max_left _ _), fun {x} hx => ?_, fun {h x} hh hx => ?_⟩
  · have hBx := (hB (⟨zero_lt_one, le_rfl⟩ : (1 : ℝ) ∈ Ioc 0 1) ((le_max_left 10 _).trans ((le_max_right x₀ _).trans ((le_max_left _ _).trans hx)))).2.2
    have hx_ge : 2 * π * C_B ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx); have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx_ge
    have hCx : C_B * x⁻¹ ≤ (2 * π)⁻¹ := calc C_B * x⁻¹ = C_B / x := (div_eq_mul_inv _ _).symm
      _ ≤ 1 / (2 * π) := (div_le_div_iff₀ hx0 (by positivity)).mpr (by rw [one_mul, mul_comm C_B (2 * π)]; exact hx_ge)
      _ = (2 * π)⁻¹ := one_div _
    have hrem : C_B * x ^ (-(5 / 2 : ℝ)) ≤ (2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ)) := by
      rw [show x ^ (-(5 / 2 : ℝ)) = x⁻¹ * x ^ (-(3 / 2 : ℝ)) by rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]; norm_num, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hCx (Real.rpow_nonneg hx0.le _)
    calc (2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ)) = π⁻¹ * x ^ (-(3 / 2 : ℝ)) + -((2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ))) := by ring
      _ ≤ π⁻¹ * x ^ (-(3 / 2 : ℝ)) + -(C_B * x ^ (-(5 / 2 : ℝ))) := add_le_add le_rfl (neg_le_neg hrem)
      _ ≤ π⁻¹ * x ^ (-(3 / 2 : ℝ)) + ((ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) - π⁻¹ * x ^ (-(3 / 2 : ℝ))) := add_le_add le_rfl (abs_le.mp hBx).1
      _ = ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x) := by ring
  · have hx_ge : π * C_ft ≤ x := (le_max_right _ _).trans ((le_max_right _ _).trans hx); have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx_ge
    have hfx := (abs_le.mp (hfar hh ((le_max_left x₀ _).trans ((le_max_left _ _).trans hx)))).2
    have h1' : C_ft / x ≤ 1 / π := (div_le_div_iff₀ hx0 Real.pi_pos).mpr ((mul_comm C_ft π).trans_le (hx_ge.trans (one_mul x).symm.le))
    have hC_rem : C_ft * movingDiagQ p (h * x) * x ^ (-(5 / 2 : ℝ)) ≤ movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ)) := by
      rw [rpow_neg_five_halves hx0]
      calc C_ft * movingDiagQ p (h * x) * (x⁻¹ / x ^ (3 / 2 : ℝ)) = (C_ft / x) * (movingDiagQ p (h * x) / x ^ (3 / 2 : ℝ)) := by ring
        _ ≤ (1 / π) * (movingDiagQ p (h * x) / x ^ (3 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_right h1' (div_nonneg (movingDiagQ_nonneg (mul_pos hh hx0).le) (by positivity))
        _ = movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ)) := by ring
    exact (sub_le_iff_le_add.mp (hfx.trans hC_rem)).trans_eq (by ring)

private lemma uniform_B_far_and_min {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ x₁ ≥ max 10 (|airyZero 1 - v₀| + 1), ∃ b > 0, -x₁ ≤ airyZero 1 - v₀ ∧
      (∀ u ∈ Icc (-x₁) (airyZero 1 - v₀), b ≤ ceG1Deriv airyDerivFirstZero u - ceF1 u) ∧
      (∀ {x : ℝ}, x₁ ≤ x → (2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ)) ≤ ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) ∧
      (∀ {h x : ℝ}, 0 < h → x₁ ≤ x → movingDiagS p h (-x) ≤ 2 * movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ))) := by
  obtain ⟨x₁, hx₁, hBf, hSf⟩ := uniform_B_far_lower hp hft hv₀
  have hle : -x₁ ≤ airyZero 1 - v₀ := by
    linarith [(abs_le.mp ((by linarith [le_max_right 10 (|airyZero 1 - v₀| + 1)] : |airyZero 1 - v₀| ≤ max 10 (|airyZero 1 - v₀| + 1)).trans hx₁)).1]
  obtain ⟨b, hb, hbmin⟩ := compact_pos_min ((continuous_ceG1Deriv airyDerivFirstZero).sub continuous_ceF1).continuousOn
    (fun u hu => (o11p_B_eq_X_sq_add_Y_sq (by linarith [hu.2, hv₀])).2) hle
  exact ⟨x₁, hx₁, b, hb, hle, hbmin, hBf, hSf⟩

/-- **Theorem `O.11w` (`(ceo:O11w.10)`), uniform `B`-bound (`v ≥ v₀, h > 0`).** -/
theorem movingDiagS_le_B {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) {v₀ : ℝ} (hv₀ : 0 < v₀) :
    ∃ C > 0, ∀ {h u : ℝ}, 0 < h → u ≤ airyZero 1 - v₀ → movingDiagS p h u ≤ C * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := by
  have hp0 : 0 < p := by linarith [hp.1]
  obtain ⟨x₁, hx₁_ge, b, hb_pos, _, hb_min, hB_far, hS_far⟩ := uniform_B_far_and_min hp hft hv₀
  obtain ⟨M_T, _, hT_bd⟩ := cohnT_compact_bound (R := max x₁ |airyZero 1 - v₀|) (by positivity)
  refine ⟨max 4 (M_T / b), by positivity, fun {h u} hh hu => ?_⟩
  by_cases hux : u ≤ -x₁
  · set x := -u; have hx : x₁ ≤ x := by dsimp [x]; linarith
    have hx0 : 0 < x := by linarith [(le_max_left 10 _).trans hx₁_ge]
    have hu_eq : u = -x := by dsimp [x]; ring
    have hB0 := (o11p_B_eq_X_sq_add_Y_sq (by linarith [hv₀, hu] : u < airyZero 1)).2.le
    rw [hu_eq] at hB0 ⊢
    calc movingDiagS p h (-x) ≤ 2 * movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ)) := hS_far hh hx
      _ ≤ 2 * 1 / (π * x ^ (3 / 2 : ℝ)) := by gcongr; exact movingDiagQ_le_one p (h * x)
      _ = 4 * ((2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_neg hx0.le]; field_simp [Real.pi_ne_zero]; ring
      _ ≤ 4 * (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) := by gcongr; exact hB_far hx
      _ ≤ max 4 (M_T / b) * (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hB0
  · have hu_mem : u ∈ Icc (-x₁) (airyZero 1 - v₀) := ⟨le_of_not_ge hux, hu⟩
    have hS_le := (movingDiagS_le_cohnT hp0 hh.le u).trans (hT_bd u
      ⟨by linarith [hu_mem.1, le_max_left x₁ |airyZero 1 - v₀|], hu_mem.2.trans ((le_abs_self _).trans (le_max_right x₁ |airyZero 1 - v₀|))⟩)
    calc movingDiagS p h u ≤ M_T := hS_le
      _ = (M_T / b) * b := by rw [div_mul_cancel₀ _ hb_pos.ne']
      _ ≤ max 4 (M_T / b) * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := mul_le_mul (le_max_right _ _) (hb_min u hu_mem) hb_pos.le (by positivity)

/-- **Theorem `O.11w` (`(ceo:O11w.11)`), intermediate `t^p B`-bound (`v ≥ v₀, t ≤ t₀`).** -/
theorem movingDiagS_le_t_pow_mul_B {p : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p)
    {v₀ t₀ : ℝ} (hv₀ : 0 < v₀) (_ht₀ : t₀ ∈ Ioc (0 : ℝ) 1) :
    ∃ C > 0, ∀ {h u : ℝ}, 0 < h → u ≤ airyZero 1 - v₀ → h * (airyZero 1 - u) ≤ t₀ →
      movingDiagS p h u ≤ C * (h * (airyZero 1 - u)) ^ p * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨x₁, hx₁_ge, b, hb_pos, _, hb_min, hB_far, hS_far⟩ := uniform_B_far_and_min hp hft hv₀
  obtain ⟨C_U, _, hcomp⟩ := movingDiagS_compact_bound hp01 (isCompact_Icc (a := -x₁) (b := airyZero 1 - v₀))
  let fac_far : ℝ := 8 * (1 + (-airyZero 1) / v₀) ^ p; let fac_cmp : ℝ := C_U * v₀ ^ (-p) / b
  refine ⟨max fac_far fac_cmp, by positivity, fun {h u} hh hu _ => ?_⟩
  have hv_ge : v₀ ≤ airyZero 1 - u := by linarith
  have hv_pos : 0 < airyZero 1 - u := lt_of_lt_of_le hv₀ hv_ge
  by_cases hux : u ≤ -x₁
  · set x := -u; have hx : x₁ ≤ x := by dsimp [x]; linarith
    have hx0 : 0 < x := by linarith [(le_max_left 10 _).trans hx₁_ge]
    have hdiv : (-airyZero 1) / (airyZero 1 - u) ≤ (-airyZero 1) / v₀ := div_le_div_of_nonneg_left (by linarith [airyZero_one.2]) hv₀ hv_ge
    have hx_le_v : x ≤ (1 + (-airyZero 1) / v₀) * (airyZero 1 - u) :=
      calc x = (airyZero 1 - u) + (-airyZero 1) := by dsimp [x]; ring
        _ = (1 + (-airyZero 1) / (airyZero 1 - u)) * (airyZero 1 - u) := by rw [add_mul, one_mul, div_mul_cancel₀ _ hv_pos.ne']
        _ ≤ (1 + (-airyZero 1) / v₀) * (airyZero 1 - u) := by gcongr
    have h1v_nn : 0 ≤ 1 + (-airyZero 1) / v₀ := add_nonneg zero_le_one (div_nonneg (by linarith [airyZero_one.2]) hv₀.le)
    have hhx_rpow : (h * x) ^ p ≤ (1 + (-airyZero 1) / v₀) ^ p * (h * (airyZero 1 - u)) ^ p :=
      (Real.rpow_le_rpow (mul_pos hh hx0).le (mul_le_mul_of_nonneg_left hx_le_v hh.le) hp01.1.le).trans_eq
        (by rw [show h * ((1 + (-airyZero 1) / v₀) * (airyZero 1 - u)) = (1 + (-airyZero 1) / v₀) * (h * (airyZero 1 - u)) by ring,
          Real.mul_rpow h1v_nn (mul_nonneg hh.le hv_pos.le)])
    have hu_eq : u = -x := by dsimp [x]; ring
    have hB_pos_u := (o11p_B_eq_X_sq_add_Y_sq (by linarith [hv_pos] : u < airyZero 1)).2
    rw [hu_eq] at hB_pos_u
    calc movingDiagS p h u = movingDiagS p h (-x) := by rw [hu_eq]
      _ ≤ 2 * movingDiagQ p (h * x) / (π * x ^ (3 / 2 : ℝ)) := hS_far hh hx
      _ ≤ 2 * (2 * (h * x) ^ p) / (π * x ^ (3 / 2 : ℝ)) := by gcongr; exact one_sub_ceVarphiP_sq_le_two_rpow (mul_pos hh hx0).le
      _ = 8 * (h * x) ^ p * ((2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ))) := by rw [Real.rpow_neg hx0.le]; field_simp [Real.pi_ne_zero]; ring
      _ ≤ 8 * ((1 + (-airyZero 1) / v₀) ^ p * (h * (airyZero 1 - u)) ^ p) * ((2 * π)⁻¹ * x ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hhx_rpow (by norm_num)) (by positivity)
      _ ≤ (8 * ((1 + (-airyZero 1) / v₀) ^ p * (h * (airyZero 1 - u)) ^ p)) * (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x)) :=
          mul_le_mul_of_nonneg_left (hB_far hx) (mul_nonneg (by norm_num) (mul_nonneg (Real.rpow_nonneg h1v_nn p) (Real.rpow_nonneg (mul_nonneg hh.le hv_pos.le) p)))
      _ = fac_far * ((h * (airyZero 1 - u)) ^ p * (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x))) := by dsimp [fac_far]; rw [← hu_eq]; ring
      _ ≤ max fac_far fac_cmp * ((h * (airyZero 1 - u)) ^ p * (ceG1Deriv airyDerivFirstZero (-x) - ceF1 (-x))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (Real.rpow_nonneg (mul_nonneg hh.le hv_pos.le) p) hB_pos_u.le)
      _ = max fac_far fac_cmp * (h * (airyZero 1 - u)) ^ p * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := by rw [← hu_eq]; ring
  · have hu_mem : u ∈ Icc (-x₁) (airyZero 1 - v₀) := ⟨le_of_not_ge hux, hu⟩
    have h1 : 1 ≤ v₀⁻¹ * (airyZero 1 - u) := by rw [← div_eq_inv_mul, one_le_div hv₀]; exact hv_ge
    have hpow_le : h ^ p ≤ v₀ ^ (-p) * (h * (airyZero 1 - u)) ^ p :=
      calc h ^ p = 1 * h ^ p := (one_mul _).symm
        _ ≤ (v₀⁻¹ * (airyZero 1 - u)) ^ p * h ^ p := mul_le_mul_of_nonneg_right ((Real.one_rpow p).symm ▸ Real.rpow_le_rpow zero_le_one h1 hp01.1.le) (Real.rpow_nonneg hh.le p)
        _ = v₀ ^ (-p) * (h * (airyZero 1 - u)) ^ p := by rw [Real.mul_rpow (inv_nonneg.mpr hv₀.le) hv_pos.le, Real.inv_rpow hv₀.le, ← Real.rpow_neg hv₀.le, Real.mul_rpow hh.le hv_pos.le]; ring
    calc movingDiagS p h u ≤ C_U * h ^ p := hcomp hh hu_mem
      _ ≤ C_U * (v₀ ^ (-p) * (h * (airyZero 1 - u)) ^ p) := by gcongr
      _ = fac_cmp * ((h * (airyZero 1 - u)) ^ p * b) := by
          dsimp [fac_cmp]; rw [show C_U * v₀ ^ (-p) / b * ((h * (airyZero 1 - u)) ^ p * b) = (C_U * v₀ ^ (-p) / b * b) * (h * (airyZero 1 - u)) ^ p by ring, div_mul_cancel₀ _ hb_pos.ne', mul_assoc]
      _ ≤ max fac_far fac_cmp * (h * (airyZero 1 - u)) ^ p * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := by
          rw [mul_assoc (max fac_far fac_cmp)]
          exact mul_le_mul (le_max_right _ _) (mul_le_mul_of_nonneg_left (hb_min u hu_mem) (Real.rpow_nonneg (mul_nonneg hh.le hv_pos.le) p))
            (mul_nonneg (Real.rpow_nonneg (mul_nonneg hh.le hv_pos.le) p) hb_pos.le) (by positivity)

/-! ### Part 4: Theorem `O.11y` (`ceo:O11y`) — Two-scale joint Airy source -/

/-- Two-scale positive source `S_c = θ S_h + γ ε S₀`, with `ε = c^{-1/3}` and `h = λ ε²`
(`ce_o1_route.tex` `(ceo:O11y.3)`). -/
noncomputable def twoScaleS (p lam γ θ c u : ℝ) : ℝ :=
  θ * movingDiagS p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) u +
    γ * c ^ (-(1 / 3 : ℝ)) * ceS0 (airyZero 1) airyDerivFirstZero u

/-- Untuned coherent cardinal complement `Q_c^{(0)} = Q_{h, σ_c}` with `h = λ c^{-2/3}` and
`σ_c = √(1 - R c^{-1/3})` (`ce_o1_route.tex` `(ceo:O11y.2)`). -/
noncomputable def twoScaleQ0 (p lam R c u : ℝ) : ℝ :=
  cardinalQ p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (√(1 - R * c ^ (-(1 / 3 : ℝ)))) u

/-- Untuned two-scale Cohn–Elkies seed `F_c^{(0)} = 2 Q_c^{(0)} - S_c` (`(ceo:O11y.3)`). -/
noncomputable def twoScaleF0 (p lam γ θ R c u : ℝ) : ℝ :=
  2 * twoScaleQ0 p lam R c u - twoScaleS p lam γ θ c u

/-- Odd-Mellin origin-tuning shift `η_c` (`(ceo:O11y.6)`), given scalar filter value `Mpsi = M_{ψ,c}(c^{1/3})`. -/
noncomputable def twoScaleEta (p lam R Mpsi c : ℝ) : ℝ :=
  Mpsi * airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ)) /
    (ceK - Mpsi * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)))

/-- Origin-tuned cardinal source `Q_c = Q_c^{(0)} + η_c g₁` (`(ceo:O11y.6)`). -/
noncomputable def twoScaleQc (p lam R Mpsi c u : ℝ) : ℝ :=
  twoScaleQ0 p lam R c u + twoScaleEta p lam R Mpsi c * ceG1 (airyZero 1) u

/-- Origin-tuned two-scale Cohn–Elkies seed `F_c = 2 Q_c - S_c` (`(ceo:O11y)`(3)). -/
noncomputable def twoScaleFc (p lam γ θ R Mpsi c u : ℝ) : ℝ :=
  2 * twoScaleQc p lam R Mpsi c u - twoScaleS p lam γ θ c u

private lemma c_rpow_neg_third_sq {c : ℝ} (hc : 0 ≤ c) :
    (c ^ (-(1 / 3 : ℝ))) ^ 2 = c ^ (-(2 / 3 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc]; congr 1; norm_num

private lemma c_rpow_neg_third_mul_third {c : ℝ} (hc : 0 < c) :
    c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ) = 1 := by
  rw [← Real.rpow_add hc, neg_add_cancel, Real.rpow_zero]

private lemma ceS0_le_C_B {v₀ : ℝ} (hv₀ : 0 < v₀) {u : ℝ} (hu : u ≤ airyZero 1 - v₀) :
    ceS0 (airyZero 1) airyDerivFirstZero u ≤ max 1 v₀⁻¹ * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ∧
    ceG1 (airyZero 1) u ≤ v₀⁻¹ * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := by
  have hv_ge : v₀ ≤ airyZero 1 - u := by linarith
  have hv_pos : 0 < airyZero 1 - u := lt_of_lt_of_le hv₀ hv_ge
  have hB := (@o11p_B_eq_X_sq_add_Y_sq u (sub_pos.mp hv_pos)).1
  set X : ℝ := cardinalHstar airyDerivFirstZero u; set Y : ℝ := airyAi u / √(airyZero 1 - u)
  have hg1_eq : ceG1 (airyZero 1) u = Y ^ 2 / (airyZero 1 - u) := by
    unfold ceG1; rw [dslope_of_ne _ (by linarith : u ≠ airyZero 1), slope_def_field, airyAi_airyZero, sub_zero, div_pow,
      show u - airyZero 1 = -(airyZero 1 - u) by ring, neg_pow_two]
    dsimp [Y]; rw [div_pow, Real.sq_sqrt hv_pos.le, div_div, ← pow_two]
  have h1v : (airyZero 1 - u)⁻¹ ≤ v₀⁻¹ := inv_anti₀ hv₀ hv_ge
  have hg1_le : ceG1 (airyZero 1) u ≤ v₀⁻¹ * (X ^ 2 + Y ^ 2) := by
    rw [hg1_eq, div_eq_mul_inv]
    exact (mul_le_mul_of_nonneg_left h1v (sq_nonneg Y)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (sq_nonneg X)) (inv_nonneg.mpr hv₀.le)) |>.trans_eq (mul_comm _ _)
  have hS0_le : ceS0 (airyZero 1) airyDerivFirstZero u ≤ max 1 v₀⁻¹ * (X ^ 2 + Y ^ 2) := by
    unfold ceS0; rw [show ceG1Deriv airyDerivFirstZero u = X ^ 2 from rfl, hg1_eq, div_eq_mul_inv]
    calc Y ^ 2 * (airyZero 1 - u)⁻¹ + X ^ 2 ≤ v₀⁻¹ * Y ^ 2 + 1 * X ^ 2 :=
          add_le_add ((mul_le_mul_of_nonneg_left h1v (sq_nonneg Y)).trans_eq (mul_comm _ _)) (one_mul _).ge
      _ ≤ max 1 v₀⁻¹ * Y ^ 2 + max 1 v₀⁻¹ * X ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
      _ = max 1 v₀⁻¹ * (X ^ 2 + Y ^ 2) := by ring
  rw [← hB] at hg1_le hS0_le; exact ⟨hS0_le, hg1_le⟩

/-- **Theorem `O.11y(1)` (`(ceo:O11y.4)`), exact origin Airy moment and source mass:**
`∫ Q_c^{(0)} = 0`, `S_c ≥ 0`, `∫ S_c = θ D_h + γ ε (1 + M) = [θ J_{2,p} √λ + γ(1 + M) + o(1)] ε`. -/
theorem twoScale_origin_mass {p lam γ θ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) :
    (∀ {R c : ℝ}, 0 ≤ R → 0 < c → R * c ^ (-(1 / 3 : ℝ)) ≤ 1 →
      Integrable (twoScaleQ0 p lam R c) ∧ ∫ u : ℝ, twoScaleQ0 p lam R c u = 0) ∧
    (∀ {c : ℝ}, 0 ≤ c → (∀ u : ℝ, 0 ≤ twoScaleS p lam γ θ c u) ∧ Integrable (twoScaleS p lam γ θ c) ∧
      ∫ u : ℝ, twoScaleS p lam γ θ c u =
        θ * cardinalDh p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) + γ * c ^ (-(1 / 3 : ℝ)) * (1 + (-airyDerivFirstZero))) ∧
    (∃ C > 0, ∀ {c : ℝ}, 0 < c →
      |(∫ u : ℝ, twoScaleS p lam γ θ c u) -
          (θ * fracJ2 p * √lam + γ * (1 + (-airyDerivFirstZero))) * c ^ (-(1 / 3 : ℝ))| ≤ C * c ^ (-(2 * p / 3 : ℝ))) ∧
    Tendsto (fun c : ℝ => (∫ u : ℝ, twoScaleS p lam γ θ c u) / c ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 (θ * fracJ2 p * √lam + γ * (1 + (-airyDerivFirstZero)))) := by
  have hp0 : 0 < p := by linarith [hp.1]
  have ha1 := airyAi_airyZero 1; have ha1' := airyDerivFirstZero_spec.2.2; have hS0_int := ceS0_integrable ha1 ha1'
  have hS0_val : ∫ u : ℝ, ceS0 (airyZero 1) airyDerivFirstZero u = 1 + (-airyDerivFirstZero) := by
    unfold ceS0; rw [integral_add airy_seed_integrals.2.1.1 ceG1Deriv_integral_eq_M.1, airy_seed_integrals.2.1.2, ceG1Deriv_integral_eq_M.2]
  have hQ : ∀ {R c : ℝ}, 0 ≤ R → 0 < c → R * c ^ (-(1 / 3 : ℝ)) ≤ 1 →
      Integrable (twoScaleQ0 p lam R c) ∧ ∫ u : ℝ, twoScaleQ0 p lam R c u = 0 := fun {R c} hR hc _ => by
    have hpq := cardinalPQ_integrals hp0 (mul_nonneg hlam.le (sq_nonneg (c ^ (-(1 / 3 : ℝ))))) (Real.sqrt_nonneg _)
      (show √(1 - R * c ^ (-(1 / 3 : ℝ))) ≤ 1 from Real.sqrt_le_one.mpr (sub_le_self _ (mul_nonneg hR (Real.rpow_nonneg hc.le _))))
    exact ⟨hpq.2.2.1, hpq.2.2.2⟩
  have hS_mass : ∀ {c : ℝ}, 0 ≤ c → (∀ u : ℝ, 0 ≤ twoScaleS p lam γ θ c u) ∧ Integrable (twoScaleS p lam γ θ c) ∧
      ∫ u : ℝ, twoScaleS p lam γ θ c u =
        θ * cardinalDh p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) + γ * c ^ (-(1 / 3 : ℝ)) * (1 + (-airyDerivFirstZero)) := fun {c} _ => by
    have hh : 0 ≤ lam * (c ^ (-(1 / 3 : ℝ))) ^ 2 := by positivity
    have hSh := movingDiagS_integral hp0 hh
    refine ⟨fun u => add_nonneg (mul_nonneg hθ (movingDiagS_nonneg hp0 hh u))
        (mul_nonneg (mul_nonneg hγ (Real.rpow_nonneg (by positivity) _)) (ceS0_pos _ _ ha1 ha1' u).le),
      (hSh.1.const_mul θ).add (hS0_int.const_mul _), ?_⟩
    unfold twoScaleS; rw [integral_add (hSh.1.const_mul θ) (hS0_int.const_mul _), integral_const_mul, integral_const_mul, hSh.2, hS0_val]
  obtain ⟨Cd, _, hDbd⟩ := cardinalDh_asymptotic_pos hp
  have h_err : ∃ C > 0, ∀ {c : ℝ}, 0 < c →
      |(∫ u : ℝ, twoScaleS p lam γ θ c u) - (θ * fracJ2 p * √lam + γ * (1 + (-airyDerivFirstZero))) * c ^ (-(1 / 3 : ℝ))| ≤ C * c ^ (-(2 * p / 3 : ℝ)) := by
    refine ⟨θ * Cd * lam ^ p + 1, by positivity, fun {c} hc => ?_⟩
    set ε := c ^ (-(1 / 3 : ℝ)); set h := lam * ε ^ 2
    have hsqh : √h = √lam * ε := by dsimp [h]; rw [Real.sqrt_mul hlam.le, Real.sqrt_sq (Real.rpow_pos_of_pos hc _).le]
    have hhp : h ^ p = lam ^ p * c ^ (-(2 * p / 3 : ℝ)) := by
      dsimp [h]; rw [Real.mul_rpow hlam.le (sq_nonneg ε), c_rpow_neg_third_sq hc.le, ← Real.rpow_mul hc.le]; congr 2; ring
    rw [(hS_mass hc.le).2.2, show θ * cardinalDh p h + γ * ε * (1 + (-airyDerivFirstZero)) -
        (θ * fracJ2 p * √lam + γ * (1 + (-airyDerivFirstZero))) * ε = θ * (cardinalDh p h - fracJ2 p * √h) by rw [hsqh]; ring,
      abs_mul, abs_of_nonneg hθ]
    calc θ * |cardinalDh p h - fracJ2 p * √h| ≤ θ * (Cd * h ^ p) := by gcongr; exact hDbd (by dsimp [h, ε]; positivity)
      _ = (θ * Cd * lam ^ p) * c ^ (-(2 * p / 3 : ℝ)) := by rw [hhp]; ring
      _ ≤ (θ * Cd * lam ^ p + 1) * c ^ (-(2 * p / 3 : ℝ)) := by gcongr; linarith
  obtain ⟨C, hC, hC_bd⟩ := h_err
  have htend : Tendsto (fun c : ℝ => (∫ u : ℝ, twoScaleS p lam γ θ c u) / c ^ (-(1 / 3 : ℝ)))
      atTop (𝓝 (θ * fracJ2 p * √lam + γ * (1 + (-airyDerivFirstZero)))) := by
    set L := θ * fracJ2 p * √lam + γ * (1 + (-airyDerivFirstZero))
    have hdiff_tend : Tendsto (fun c : ℝ => C * c ^ (-((2 * p - 1) / 3))) atTop (𝓝 0) := by
      simpa using (tendsto_rpow_neg_atTop (by linarith [hp.1] : 0 < (2 * p - 1) / 3)).const_mul C
    refine Metric.tendsto_atTop.mpr fun δ hδ => ?_; obtain ⟨C₀, hC₀⟩ := Metric.tendsto_atTop.mp hdiff_tend δ hδ
    refine ⟨max C₀ 1, fun c hc => ?_⟩
    have hc0 : 0 < c := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hc)
    have hCc := hC₀ c ((le_max_left _ _).trans hc)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hc0.le _))] at hCc
    have hc_rpow : c ^ (-(1 / 3 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hc0 _).ne'
    have hdiv_eq : c ^ (-(2 * p / 3 : ℝ)) / c ^ (-(1 / 3 : ℝ)) = c ^ (-((2 * p - 1) / 3)) := by rw [← Real.rpow_sub hc0]; congr 1; ring
    rw [Real.dist_eq, show (∫ u : ℝ, twoScaleS p lam γ θ c u) / c ^ (-(1 / 3 : ℝ)) - L =
        ((∫ u : ℝ, twoScaleS p lam γ θ c u) - L * c ^ (-(1 / 3 : ℝ))) / c ^ (-(1 / 3 : ℝ)) by rw [sub_div, mul_div_cancel_right₀ _ hc_rpow],
      abs_div, abs_of_pos (Real.rpow_pos_of_pos hc0 _)]
    exact ((div_le_div_of_nonneg_right (hC_bd hc0) (Real.rpow_pos_of_pos hc0 _).le).trans_eq (by rw [mul_div_assoc, hdiv_eq])).trans_lt hCc
  exact ⟨hQ, hS_mass, ⟨C, hC, hC_bd⟩, htend⟩

/-- **Theorem `O.11y(2)` (`(ceo:O11y.5)`), full real-space CE seed inequality with margins:**
for any `R > max (2 * γ) (γ * C_{v₀})` (`v₀ = (a₁ - a₂)/2`), there is `θ₀ > 0` such that
for all `θ ∈ (0, min 1 θ₀]`, `F_c^{(0)}(u) > 0` for `u < a₁ - K_* ε` and `c ≥ c_*`,
together with explicit tip/intermediate/far margin lower bounds for tuning `(3)`. -/
theorem twoScaleF0_pos_with_margins {p lam γ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) (hlam : 0 < lam) (hγ : 0 < γ) :
    let v₀ : ℝ := (airyZero 1 - airyZero 2) / 2; let C_v0 : ℝ := max 1 v₀⁻¹
    ∀ {R : ℝ}, max (2 * γ) (γ * C_v0) < R →
    ∃ θ₀ > 0, ∀ {θ : ℝ}, θ ∈ Ioc 0 (min 1 θ₀) →
      ∃ K_star > 0, ∃ c_star > 0, ∃ m_tip > 0, ∃ c_far > 0,
        ∀ {c u : ℝ}, c_star ≤ c → u < airyZero 1 - K_star * c ^ (-(1 / 3 : ℝ)) →
          let ε := c ^ (-(1 / 3 : ℝ)); let B := ceG1Deriv airyDerivFirstZero u - ceF1 u
          0 < twoScaleF0 p lam γ θ R c u ∧ (airyZero 1 - v₀ ≤ u → m_tip * ε ≤ twoScaleF0 p lam γ θ R c u) ∧
          (u ≤ airyZero 1 - v₀ → lam * ε ^ 2 * (airyZero 1 - u) ≤ 1 → (R - γ * C_v0) * ε * B ≤ twoScaleF0 p lam γ θ R c u) ∧
          (u ≤ airyZero 1 - v₀ → 1 ≤ lam * ε ^ 2 * (airyZero 1 - u) → (1 / 2) * c_far * B ≤ twoScaleF0 p lam γ θ R c u) := by
  intro v₀ C_v0 R hR
  have hv₀ : v₀ ∈ Ioo (0 : ℝ) (airyZero 1 - airyZero 2) := by
    have hd := sub_pos.mpr (airyZero_lt_of_lt (n := 1) (m := 2) le_rfl (by omega)); dsimp [v₀]; exact ⟨half_pos hd, half_lt_self hd⟩
  have ht₀ : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨zero_lt_one, le_rfl⟩
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) ((le_max_left (2 * γ) (γ * C_v0)).trans hR.le)
  set R₀ : ℝ := R / √lam; set m : ℝ := sInf ((fun u => dslope airyAi (airyZero 1) u ^ 2) '' Icc (airyZero 1 - v₀) (airyZero 1))
  have hO := lemma_O11p hp (by positivity : 0 ≤ R₀) hv₀ ht₀; dsimp only at hO
  obtain ⟨hm, h₀, hh₀, K₀, hK₀, c₀, hc₀, hO11p⟩ := hO
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩
  obtain ⟨C_U, hC_U, hS_comp⟩ := movingDiagS_compact_bound hp01 (isCompact_Icc (a := airyZero 1 - v₀) (b := airyZero 1))
  obtain ⟨C_w, hC_w, hS_intm⟩ := movingDiagS_le_t_pow_mul_B hp hft hv₀.1 ht₀
  obtain ⟨C_far, hC_far, hS_far⟩ := movingDiagS_le_B hp hft hv₀.1
  obtain ⟨M_S0, hM_S0, hS0_bd⟩ := compact_abs_bound (continuous_ceS0 (airyZero 1) airyDerivFirstZero).continuousOn (sub_le_self _ hv₀.1.le)
  set θ₀ : ℝ := min (1 / (4 * C_w)) (c₀ / (2 * C_far))
  refine ⟨θ₀, lt_min (by positivity) (by positivity), fun {θ} hθ => ?_⟩
  have hθ_nn : 0 ≤ θ := hθ.1.le; have hθ_le1 : θ ≤ 1 := hθ.2.trans (min_le_left _ _)
  have hθ_Cw : θ * C_w ≤ 1 / 4 := (mul_le_mul_of_nonneg_right (hθ.2.trans ((min_le_right _ _).trans (min_le_left _ _))) hC_w.le).trans_eq (by field_simp [hC_w.ne'])
  have hθ_Cfar : θ * C_far ≤ c₀ / 2 := (mul_le_mul_of_nonneg_right (hθ.2.trans ((min_le_right _ _).trans (min_le_right _ _))) hC_far.le).trans_eq (by field_simp [hC_far.ne'])
  set C_near : ℝ := 2 * K₀ * √lam + C_U * lam ^ p + γ * M_S0; set K_star : ℝ := C_near / (2 * m) + 1
  set ε_max : ℝ := min 1 (min (1 / (2 * R)) (min (√(h₀ / (2 * lam))) (c₀ / (γ * C_v0))))
  have hε_max : 0 < ε_max := lt_min one_pos (lt_min (by positivity) (lt_min (Real.sqrt_pos.mpr (by positivity)) (by positivity)))
  set c_star : ℝ := ε_max ^ (-3 : ℝ); have hc_star : 0 < c_star := Real.rpow_pos_of_pos hε_max _
  refine ⟨K_star, by positivity, c_star, hc_star, m, hm, c₀, hc₀, fun {c u} hc hu => ?_⟩
  have hc_pos : 0 < c := lt_of_lt_of_le hc_star hc; set ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc_pos _
  have hε_le : ε ≤ ε_max := (Real.rpow_le_rpow_of_nonpos hc_star hc (by norm_num)).trans_eq (by dsimp [c_star]; rw [← Real.rpow_mul hε_max.le]; norm_num)
  have hε_1 : ε ≤ 1 := hε_le.trans (min_le_left _ _); set h : ℝ := lam * ε ^ 2; have hh_pos : 0 < h := by positivity
  have hh_lt : h < h₀ := by
    have hsq2 : ε ^ 2 ≤ h₀ / (2 * lam) := (pow_le_pow_left₀ hε_pos.le (hε_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))) 2).trans_eq (Real.sq_sqrt (by positivity))
    calc h ≤ lam * (h₀ / (2 * lam)) := mul_le_mul_of_nonneg_left hsq2 hlam.le
      _ = h₀ / 2 := by rw [show lam * (h₀ / (2 * lam)) = (lam / lam) * (h₀ / 2) by ring, div_self hlam.ne', one_mul]
      _ < h₀ := half_lt_self hh₀
  have hRε_le : R * ε ≤ 1 / 2 := (mul_le_mul_of_nonneg_left (hε_le.trans ((min_le_right _ _).trans (min_le_left _ _))) hR_pos.le).trans_eq (by field_simp [hR_pos.ne'])
  set σ : ℝ := √(1 - R * ε)
  have hσ_sq : 1 - σ ^ 2 = R * ε := by have := Real.sq_sqrt (by linarith : 0 ≤ 1 - R * ε); linarith
  have hsqh : √h = √lam * ε := by dsimp [h]; rw [Real.sqrt_mul hlam.le, Real.sqrt_sq hε_pos.le]
  have hsig : 1 - σ ^ 2 ≤ R₀ * √h := by rw [hσ_sq, hsqh]; dsimp [R₀]; rw [← mul_assoc, div_mul_cancel₀ _ (Real.sqrt_pos.mpr hlam).ne']
  have hp_spec := hO11p ⟨hh_pos, hh_lt⟩ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (by linarith [mul_pos hR_pos hε_pos])) hsig
  have hγCε : γ * C_v0 * ε ≤ c₀ := (mul_le_mul_of_nonneg_left (hε_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))) (by positivity)).trans_eq
    (by field_simp [hγ.ne', (show 0 < C_v0 by positivity).ne'])
  have h_tip : airyZero 1 - v₀ ≤ u → m * ε ≤ twoScaleF0 p lam γ θ R c u := fun huv₀ => by
    have hu_le : u ≤ airyZero 1 := by linarith [show 0 < K_star * ε by positivity]
    have hQ_near := (hp_spec.1 u ⟨huv₀, hu_le⟩).2; have hS0_le : ceS0 (airyZero 1) airyDerivFirstZero u ≤ M_S0 := (le_abs_self _).trans (hS0_bd u ⟨huv₀, hu_le⟩)
    have hhp_le : h ^ p ≤ lam ^ p * ε := by
      have hε_2p : ε ^ (2 * p) ≤ ε := by simpa using Real.rpow_le_rpow_of_exponent_ge hε_pos hε_1 (by linarith [hp.1] : 1 ≤ 2 * p)
      calc h ^ p = lam ^ p * (ε ^ 2) ^ p := by dsimp [h]; rw [Real.mul_rpow hlam.le (sq_nonneg ε)]
        _ = lam ^ p * ε ^ (2 * p) := by rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε_pos.le]; norm_num
        _ ≤ lam ^ p * ε := by gcongr
    have hS_bd : θ * movingDiagS p h u ≤ C_U * lam ^ p * ε :=
      (mul_le_mul hθ_le1 (hS_comp hh_pos ⟨huv₀, hu_le⟩) (movingDiagS_nonneg hp01.1 hh_pos.le u) zero_le_one).trans
        (by rw [one_mul]; exact (mul_le_mul_of_nonneg_left hhp_le hC_U.le).trans_eq (by ring))
    have h2mK : 2 * m * K_star = C_near + 2 * m := by dsimp [K_star]; rw [mul_add, mul_one, mul_div_cancel₀ _ (by positivity : (2 * m) ≠ 0)]
    have hm_v : (C_near + 2 * m) * ε < 2 * m * (airyZero 1 - u) :=
      calc (C_near + 2 * m) * ε = 2 * m * (K_star * ε) := by rw [← mul_assoc, h2mK]
        _ < 2 * m * (airyZero 1 - u) := mul_lt_mul_of_pos_left (by linarith [hu]) (by positivity)
    dsimp [C_near] at hm_v; unfold twoScaleF0 twoScaleQ0 twoScaleS
    have hle_S := add_le_add hS_bd (mul_le_mul_of_nonneg_left hS0_le (mul_nonneg hγ.le hε_pos.le))
    calc m * ε ≤ 2 * m * ε := by linarith [mul_pos hm hε_pos]
      _ = (2 * K₀ * √lam + C_U * lam ^ p + γ * M_S0 + 2 * m) * ε - (2 * K₀ * √lam + C_U * lam ^ p + γ * M_S0) * ε := by ring
      _ ≤ 2 * m * (airyZero 1 - u) - (2 * K₀ * √lam + C_U * lam ^ p + γ * M_S0) * ε := sub_le_sub_right hm_v.le _
      _ = 2 * (m * (airyZero 1 - u) - K₀ * √h) - (C_U * lam ^ p * ε + γ * ε * M_S0) := by rw [hsqh]; ring
      _ ≤ 2 * cardinalQ p h σ u - (θ * movingDiagS p h u + γ * ε * ceS0 (airyZero 1) airyDerivFirstZero u) := by linarith
  have h_intm : u ≤ airyZero 1 - v₀ → h * (airyZero 1 - u) ≤ 1 →
      (R - γ * C_v0) * ε * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ twoScaleF0 p lam γ θ R c u := fun hu_le ht1 => by
    have hB_pos := (@o11p_B_eq_X_sq_add_Y_sq u (by linarith [hv₀.1, hu_le])).2
    have hQ_intm := hp_spec.2.2.1 hu_le ht1; have hS_intm' := hS_intm hh_pos hu_le ht1; have hS0_le := (ceS0_le_C_B hv₀.1 hu_le).1
    have ht_nn : 0 ≤ (h * (airyZero 1 - u)) ^ p := Real.rpow_nonneg (mul_nonneg hh_pos.le (by linarith [hv₀.1])) p
    have hcoeff : (R - γ * C_v0) * ε ≤ 2 * ((1 / 2 : ℝ) * (1 - σ ^ 2) + (1 / 4 : ℝ) * (h * (airyZero 1 - u)) ^ p) -
        θ * C_w * (h * (airyZero 1 - u)) ^ p - γ * ε * C_v0 := by rw [hσ_sq]; nlinarith [mul_le_mul_of_nonneg_right hθ_Cw ht_nn]
    have hmul := mul_le_mul_of_nonneg_right hcoeff hB_pos.le; unfold twoScaleF0 twoScaleQ0 twoScaleS
    have hle_S := add_le_add (mul_le_mul_of_nonneg_left hS_intm' hθ_nn) (mul_le_mul_of_nonneg_left hS0_le (mul_nonneg hγ.le hε_pos.le))
    linarith
  have h_far : u ≤ airyZero 1 - v₀ → 1 ≤ h * (airyZero 1 - u) →
      (1 / 2) * c₀ * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ twoScaleF0 p lam γ θ R c u := fun hu_le ht_ge => by
    have hB_pos := (@o11p_B_eq_X_sq_add_Y_sq u (by linarith [hv₀.1, hu_le])).2
    have hQ_far := hp_spec.2.2.2 hu_le ht_ge; have hS_far' := hS_far hh_pos hu_le; have hS0_le := (ceS0_le_C_B hv₀.1 hu_le).1
    have hmul := mul_le_mul_of_nonneg_right (by linarith : (1 / 2) * c₀ ≤ 2 * c₀ - θ * C_far - γ * ε * C_v0) hB_pos.le
    unfold twoScaleF0 twoScaleQ0 twoScaleS
    have hle_S := add_le_add (mul_le_mul_of_nonneg_left hS_far' hθ_nn) (mul_le_mul_of_nonneg_left hS0_le (mul_nonneg hγ.le hε_pos.le))
    linarith
  have hpos : 0 < twoScaleF0 p lam γ θ R c u := by
    rcases le_or_gt (airyZero 1 - v₀) u with huv₀ | huv₀
    · exact lt_of_lt_of_le (by positivity) (h_tip huv₀)
    · have hB_pos := (@o11p_B_eq_X_sq_add_Y_sq u (by linarith [hv₀.1, huv₀])).2
      rcases le_or_gt (h * (airyZero 1 - u)) 1 with ht1 | ht1
      · exact lt_of_lt_of_le (mul_pos (mul_pos (by linarith [le_max_right (2 * γ) (γ * C_v0)]) hε_pos) hB_pos) (h_intm huv₀.le ht1)
      · exact lt_of_lt_of_le (mul_pos (mul_pos (by norm_num) hc₀) hB_pos) (h_far huv₀.le ht1.le)
  exact ⟨hpos, h_tip, h_intm, h_far⟩

/-- **Theorem `O.11y(2)` (`(ceo:O11y.5)`), clean real-space CE seed inequality.** -/
theorem twoScaleF0_pos {p lam γ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p) (hlam : 0 < lam) (hγ : 0 < γ) :
    ∃ R > 2 * γ, ∃ θ₀ > 0, ∀ {θ : ℝ}, θ ∈ Ioc 0 (min 1 θ₀) →
      ∃ K_star > 0, ∃ c_star > 0, ∀ {c u : ℝ}, c_star ≤ c → u < airyZero 1 - K_star * c ^ (-(1 / 3 : ℝ)) →
        0 < twoScaleF0 p lam γ θ R c u := by
  let R : ℝ := max (2 * γ) (γ * max 1 (((airyZero 1 - airyZero 2) / 2)⁻¹)) + 1
  have hR_lt : max (2 * γ) (γ * max 1 (((airyZero 1 - airyZero 2) / 2)⁻¹)) < R := by dsimp [R]; exact lt_add_one _
  obtain ⟨θ₀, hθ₀, hres⟩ := twoScaleF0_pos_with_margins hp hft hlam hγ hR_lt
  refine ⟨R, lt_of_le_of_lt (le_max_left _ _) hR_lt, θ₀, hθ₀, fun {θ} hθ => ?_⟩
  obtain ⟨K_star, hK_star, c_star, hc_star, _, _, _, _, hpos⟩ := hres hθ
  exact ⟨K_star, hK_star, c_star, hc_star, fun hc hu => (hpos hc hu).1⟩

/-! #### Part 4B: Unconditional twisted-Laplace controls, B-spline weight witness, and `(ceo:O11y.6)–(7)` -/

private lemma integrable_mul_exp_of_le_ceS0 {f : ℝ → ℝ} {xtilde : ℝ} (hx : 0 ≤ xtilde)
    (hf_cont : Continuous f) (hf_nn : ∀ u, 0 ≤ f u) (hf_le : ∀ u, f u ≤ ceS0 (airyZero 1) airyDerivFirstZero u) :
    Integrable (fun u : ℝ => f u * Real.exp (xtilde * u)) := by
  have ha1 := airyAi_airyZero 1; have ha1' := airyDerivFirstZero_spec.2.2
  obtain ⟨_, C_tl, hC_tl, htail, hR_bd⟩ := ceS0_pos_tail ha1 ha1'
  refine (tail_integrable (ceS0_integrable ha1 ha1') htail hC_tl hR_bd hx).mono'
    ((hf_cont.mul (by fun_prop)).aestronglyMeasurable) ?_
  filter_upwards with u
  rw [Real.norm_of_nonneg (mul_nonneg (hf_nn u) (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_right (hf_le u) (Real.exp_pos _).le

private lemma integrable_ceG1_mul_exp {xtilde : ℝ} (hx : 0 ≤ xtilde) :
    Integrable (fun u : ℝ => ceG1 (airyZero 1) u * Real.exp (xtilde * u)) :=
  integrable_mul_exp_of_le_ceS0 hx (continuous_ceG1 _) (fun _ => by unfold ceG1; positivity) fun u => by
    unfold ceS0 ceG1Deriv; linarith [sq_nonneg (dslope airyAi' airyDerivFirstZero u)]

private lemma integrable_ceG1Deriv_mul_exp {xtilde : ℝ} (hx : 0 ≤ xtilde) :
    Integrable (fun u : ℝ => ceG1Deriv airyDerivFirstZero u * Real.exp (xtilde * u)) :=
  integrable_mul_exp_of_le_ceS0 hx (continuous_ceG1Deriv _) (fun _ => by unfold ceG1Deriv; positivity) fun u => by
    unfold ceS0 ceG1; linarith [sq_nonneg (dslope airyAi (airyZero 1) u)]

private lemma integrable_ceF1_mul_exp {xtilde : ℝ} (hx : 0 ≤ xtilde) :
    Integrable (fun u : ℝ => ceF1 u * Real.exp (xtilde * u)) := by
  have hneg : IntegrableOn (fun u : ℝ => ceF1 u * Real.exp (xtilde * u)) (Iic 0) := by
    refine ceF1_integral_eq_zero.1.abs.integrableOn.mono' (((continuous_ceF1.mul (by fun_prop)).aestronglyMeasurable).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hx hu))
  have hpos : IntegrableOn (fun u : ℝ => ceF1 u * Real.exp (xtilde * u)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    have ha1_neg : 0 < -airyZero 1 := by linarith [airyZero_one.2]
    refine ((integrableOn_exp_mul_Ioi (by norm_num : -(2 / 3 : ℝ) < 0) 0).const_mul
      (9 / (-airyZero 1) * Real.exp (xtilde ^ 3 / 3 + 2 / 3))).mono' (((continuous_ceF1.mul (by fun_prop)).aestronglyMeasurable).restrict) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    have hF1 : |ceF1 u| ≤ airyAi u ^ 2 / (-airyZero 1) := by
      unfold ceF1
      rw [dslope_of_ne _ (by linarith [airyZero_one.2, hu0] : u ≠ airyZero 1), slope_def_field, airyAi_airyZero, sub_zero,
        show airyAi u * (airyAi u / (u - airyZero 1)) = airyAi u ^ 2 / (u - airyZero 1) by ring,
        abs_div, abs_of_nonneg (sq_nonneg _), abs_of_pos (by linarith [airyZero_one.2, hu0] : 0 < u - airyZero 1)]
      exact div_le_div_of_nonneg_left (sq_nonneg _) ha1_neg (by linarith [hu0])
    have hAi2 : airyAi u ^ 2 ≤ 9 * airyEnv (u : ℂ) := by
      have h := airyAiC_norm_sq_le (u : ℂ); rw [airyAiC_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
      exact h.trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (by norm_num)
        (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg (u : ℂ)]) (by norm_num))) (airyEnv_pos _).le)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc |ceF1 u| * Real.exp (xtilde * u) ≤ (9 / (-airyZero 1)) * (Real.exp (xtilde * u) * airyEnv (u : ℂ)) :=
          (mul_le_mul_of_nonneg_right (hF1.trans (div_le_div_of_nonneg_right hAi2 ha1_neg.le)) (Real.exp_pos _).le).trans_eq (by ring)
      _ ≤ (9 / (-airyZero 1)) * (Real.exp (xtilde ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul_of_nonneg_left (exp_mul_airyEnv_le hx hu.le) (by positivity)
      _ = _ := by ring
  rw [← integrableOn_univ, ← Iic_union_Ici (a := (0 : ℝ)), integrableOn_union]; exact ⟨hneg, hpos⟩

private lemma integrable_cardinalP_mul_exp {p h σ xtilde : ℝ} (hp : 0 < p) (hh : 0 ≤ h) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hx : 0 ≤ xtilde) :
    Integrable (fun u : ℝ => cardinalP p h σ u * Real.exp (xtilde * u)) := by
  have hP_int := (cardinalPQ_integrals hp hh hσ0 hσ1).1
  have hP_meas : AEStronglyMeasurable (fun u : ℝ => cardinalP p h σ u * Real.exp (xtilde * u)) volume := hP_int.aestronglyMeasurable.mul (by fun_prop)
  have hP_nn : ∀ u, 0 ≤ cardinalP p h σ u := fun _ => by unfold cardinalP; exact sq_nonneg _
  have hneg : IntegrableOn (fun u : ℝ => cardinalP p h σ u * Real.exp (xtilde * u)) (Iic 0) := by
    refine hP_int.integrableOn.mono' hP_meas.restrict ?_; filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hP_nn u)]
    exact mul_le_of_le_one_right (hP_nn u) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hx hu))
  have hpos : IntegrableOn (fun u : ℝ => cardinalP p h σ u * Real.exp (xtilde * u)) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine ((airyPws_integrableOn_pow_mul_exp 1 (by norm_num : (0 : ℝ) < 2 / 3)).const_mul
      (23 * (-airyDerivFirstZero) * Real.exp (xtilde ^ 3 / 3 + 2 / 3))).mono' hP_meas.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hH_le := cardinalHC_norm_sq_le hp hh hσ0 hσ1 (u : ℂ)
    have hP_eq : cardinalP p h σ u = ‖cardinalHC p h σ (u : ℂ)‖ ^ 2 := by
      unfold cardinalP; have hs := cardinalH_hasSum hp hh hσ0 hσ1
      rw [show cardinalHC p h σ (u : ℂ) = (cardinalH p h σ u : ℂ) by
        rw [← (hs.1 (u : ℂ)).tsum_eq, ← (hs.2 u).tsum_eq]; push_cast; exact tsum_congr fun n => by rw [cohnLC_ofReal],
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hM_nn : 0 ≤ 23 * (-airyDerivFirstZero) * (1 + u) := by
      have : 0 ≤ -airyDerivFirstZero := neg_nonneg.mpr airyDerivFirstZero_spec.2.1.le; have hu0 : (0 : ℝ) ≤ u := hu.le; positivity
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu.le, ← hP_eq] at hH_le
    rw [Real.norm_of_nonneg (mul_nonneg (hP_nn u) (Real.exp_pos _).le)]
    calc cardinalP p h σ u * Real.exp (xtilde * u) ≤ (23 * (-airyDerivFirstZero) * (1 + u) * airyEnv (u : ℂ)) * Real.exp (xtilde * u) :=
          mul_le_mul_of_nonneg_right hH_le (Real.exp_pos _).le
      _ = 23 * (-airyDerivFirstZero) * (1 + u) * (Real.exp (xtilde * u) * airyEnv (u : ℂ)) := by ring
      _ ≤ 23 * (-airyDerivFirstZero) * (1 + u) * (Real.exp (xtilde ^ 3 / 3 + 2 / 3) * Real.exp (-(2 / 3) * u)) :=
          mul_le_mul_of_nonneg_left (exp_mul_airyEnv_le hx hu.le) hM_nn
      _ = _ := by rw [pow_one]; ring
  rw [← integrableOn_univ, ← Iic_union_Ici (a := (0 : ℝ)), integrableOn_union]; exact ⟨hneg, hpos⟩

private lemma airyTwistedLaplace_twoScaleQc_linear {p lam R Mpsi c : ℝ} (hp : 0 < p) (hlam : 0 ≤ lam) (hR : 0 ≤ R) (hc : 0 < c) :
    airyTwistedLaplace (twoScaleQc p lam R Mpsi c) (ceCs * c ^ (1 / 3 : ℝ)) =
      airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ)) +
        twoScaleEta p lam R Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) := by
  set xtilde : ℝ := ceCs * c ^ (1 / 3 : ℝ); have hx : 0 ≤ xtilde := mul_nonneg ceCs_pos.le (Real.rpow_nonneg hc.le _)
  have hσ1 : √(1 - R * c ^ (-(1 / 3 : ℝ))) ≤ 1 :=
    Real.sqrt_le_one.mpr (sub_le_self _ (mul_nonneg hR (Real.rpow_nonneg hc.le _)))
  have hQ0_int : Integrable (fun u : ℝ => twoScaleQ0 p lam R c u * Real.exp (xtilde * u)) := by
    rw [show (fun u : ℝ => twoScaleQ0 p lam R c u * Real.exp (xtilde * u)) = fun u => -(ceF1 u * Real.exp (xtilde * u)) +
        ceG1Deriv airyDerivFirstZero u * Real.exp (xtilde * u) -
        cardinalP p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (√(1 - R * c ^ (-(1 / 3 : ℝ)))) u * Real.exp (xtilde * u) from funext fun u => by unfold twoScaleQ0 cardinalQ; ring]
    exact ((integrable_ceF1_mul_exp hx).neg.add (integrable_ceG1Deriv_mul_exp hx)).sub
      (integrable_cardinalP_mul_exp hp (by positivity) (Real.sqrt_nonneg _) hσ1 hx)
  unfold airyTwistedLaplace twoScaleQc
  rw [show (fun u : ℝ => (twoScaleQ0 p lam R c u + twoScaleEta p lam R Mpsi c * ceG1 (airyZero 1) u) * Real.exp (xtilde * u)) =
      fun u => twoScaleQ0 p lam R c u * Real.exp (xtilde * u) + twoScaleEta p lam R Mpsi c * (ceG1 (airyZero 1) u * Real.exp (xtilde * u))
    from funext fun _ => by ring, integral_add hQ0_int ((integrable_ceG1_mul_exp hx).const_mul _), integral_const_mul]
  ring

/-- **Unconditional `g₁` twisted-Laplace bound:** `0 ≤ g̃₁(i c_s x) ≤ C_g (1 + x)^{-5/2}` (`x ≥ 0`). -/
theorem airyTwistedLaplace_ceG1_bound :
    ∃ C_g > 0, ∀ {x : ℝ}, 0 ≤ x →
      0 ≤ airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) ∧
      airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) ≤ C_g * (1 + x) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨_, _, _, C_hi, _, _, hS0_bd⟩ := positive_source_S0_floor
  refine ⟨C_hi, by linarith, fun {x} hx => ?_⟩
  have ha1 := airyAi_airyZero 1; have ha1' := airyDerivFirstZero_spec.2.2
  obtain ⟨_, C_tl, hC_tl, htail, hR_bd⟩ := ceS0_pos_tail ha1 ha1'; have hx0 : 0 ≤ ceCs * x := mul_nonneg ceCs_pos.le hx
  have hS0_int := tail_integrable (ceS0_integrable ha1 ha1') htail hC_tl hR_bd hx0
  have h_nn : 0 ≤ airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) := by
    unfold airyTwistedLaplace; exact mul_nonneg (mul_pos ceK_pos (Real.exp_pos _)).le (integral_nonneg fun u => mul_nonneg (by unfold ceG1; positivity) (Real.exp_pos _).le)
  have h_le_S0 : airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * x) ≤ airyTwistedLaplace (ceS0 (airyZero 1) airyDerivFirstZero) (ceCs * x) := by
    unfold airyTwistedLaplace
    refine mul_le_mul_of_nonneg_left (integral_mono (integrable_ceG1_mul_exp hx0) hS0_int fun u =>
      mul_le_mul_of_nonneg_right (by unfold ceS0 ceG1Deriv; linarith [sq_nonneg (dslope airyAi' airyDerivFirstZero u)]) (Real.exp_pos _).le)
      (mul_pos ceK_pos (Real.exp_pos _)).le
  exact ⟨h_nn, h_le_S0.trans (hS0_bd x hx).2⟩

/-- **Unconditional `P_b` reduction (`(ceo:O11n.11)`, `j = 0`):**
a uniform bound `|v_b(t)| ≤ M` on `t ≥ 0` implies `|P̃_b(i c_s x)| ≤ C M² x^{-5/2}`. -/
theorem airyTwistedLaplace_cardinalP_le_of_dirichletV_bound {b : ℕ → ℝ}
    (hb : Summable (fun n : ℕ => b n ^ 2)) {M : ℝ} (hM : ∀ t : ℝ, 0 ≤ t → |dirichletV b t| ≤ M) {x : ℝ} (hx : 0 < x) :
    |airyTwistedLaplace (cardinalPb b) (ceCs * x)| ≤ (2 * ceK * ceCs ^ (-(5 / 2 : ℝ)) / √π) * M ^ 2 * x ^ (-(5 / 2 : ℝ)) := by
  have h := airySquare_uniform_line_bound_of_forall hb hM hx 0
  simp only [Complex.ofReal_zero, mul_zero, sub_zero, mul_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, add_zero, Real.one_rpow, airyTwistedLaplaceC_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- B-spline origin Mellin weight `M_{ψ,c}(c^{1/3}) = ∫ ψ_m(t; κ c^{-1/3}) e^{-c_s c^{1/3} t} dt`
(`ce_o1_route.tex` `(ceo:O11y.6)`, `u1c_o1_upper.tex` `(e28)`). -/
noncomputable def bsplineMellinWeight (m : ℕ) (κ c : ℝ) : ℝ :=
  ∫ t : ℝ, bspline m (κ * c ^ (-(1 / 3 : ℝ))) t * Real.exp (-(ceCs * c ^ (1 / 3 : ℝ)) * t)

/-- Concrete non-vacuity of `0 < M_{ψ,c}(ε⁻¹) ≤ 1` using the uniform B-spline density `bspline m (κ ε)`. -/
theorem bsplineMellinWeight_bounds {m : ℕ} (hm : 1 ≤ m) {κ : ℝ} (hκ : 0 < κ) {c : ℝ} (hc : 0 < c) :
    Real.exp (-(ceCs * κ)) ≤ bsplineMellinWeight m κ c ∧ 0 < bsplineMellinWeight m κ c ∧ bsplineMellinWeight m κ c ≤ 1 := by
  set δ : ℝ := κ * c ^ (-(1 / 3 : ℝ)); have hδ : 0 < δ := mul_pos hκ (Real.rpow_pos_of_pos hc _)
  set y : ℝ := ceCs * c ^ (1 / 3 : ℝ); have hy : 0 < y := mul_pos ceCs_pos (Real.rpow_pos_of_pos hc _)
  have hsupp : ∀ t ∉ Icc (0 : ℝ) δ, bspline m δ t = 0 := fun t ht => by
    unfold bspline; rw [bsplineUnit_support hm fun hmem => ht ⟨(div_nonneg_iff.mp hmem.1).elim (·.1) (by linarith [·.2, hδ]), (div_le_one hδ).mp hmem.2⟩, mul_zero]
  have h_eq_set : bsplineMellinWeight m κ c = ∫ t in Icc (0 : ℝ) δ, bspline m δ t * Real.exp (-y * t) := by
    unfold bsplineMellinWeight; exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by rw [hsupp t ht, zero_mul]).symm
  have hb_int : IntegrableOn (bspline m δ) (Icc 0 δ) := (((bsplineUnit_integrable m).comp_div hδ.ne').const_mul δ⁻¹).integrableOn
  have hbe_int : IntegrableOn (fun t => bspline m δ t * Real.exp (-y * t)) (Icc 0 δ) := by
    refine hb_int.mono' ((bspline_aestronglyMeasurable m hδ).mul (by fun_prop)).restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_of_nonneg (mul_nonneg (bspline_nonneg m hδ t) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (bspline_nonneg m hδ t) (Real.exp_le_one_iff.mpr (by nlinarith [ht.1, hy]))
  have hyδ : y * δ = ceCs * κ := by
    dsimp [y, δ]; rw [show ceCs * c ^ (1 / 3 : ℝ) * (κ * c ^ (-(1 / 3 : ℝ))) = ceCs * κ * (c ^ (-(1 / 3 : ℝ)) * c ^ (1 / 3 : ℝ)) by ring, c_rpow_neg_third_mul_third hc, mul_one]
  have h_lo : Real.exp (-(ceCs * κ)) ≤ bsplineMellinWeight m κ c := by
    rw [h_eq_set]
    calc Real.exp (-(ceCs * κ)) = ∫ t in Icc (0 : ℝ) δ, Real.exp (-(ceCs * κ)) * bspline m δ t := by rw [integral_const_mul, bspline_setIntegral_one hm hδ, mul_one]
      _ ≤ ∫ t in Icc (0 : ℝ) δ, bspline m δ t * Real.exp (-y * t) :=
          setIntegral_mono_on (hb_int.const_mul _) hbe_int measurableSet_Icc fun t ht => by
            rw [mul_comm (Real.exp (-(ceCs * κ)))]; exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by rw [← hyδ]; nlinarith [ht.2, hy])) (bspline_nonneg m hδ t)
  have h_hi : bsplineMellinWeight m κ c ≤ 1 := by
    rw [h_eq_set]
    exact (setIntegral_mono_on hbe_int hb_int measurableSet_Icc fun t ht =>
      mul_le_of_le_one_right (bspline_nonneg m hδ t) (Real.exp_le_one_iff.mpr (by nlinarith [ht.1, hy]))).trans_eq (bspline_setIntegral_one hm hδ)
  exact ⟨h_lo, lt_of_lt_of_le (Real.exp_pos _) h_lo, h_hi⟩

private lemma twoScale_eta_bound {p lam R : ℝ} {Mpsi : ℝ → ℝ} {c C_g C_Q : ℝ}
    (hc_pos : 0 < c) (hC_g : 0 < C_g) (hC_Q : 0 < C_Q) (hM_pos : 0 < Mpsi c) (hM_le1 : Mpsi c ≤ 1)
    (hg_lap : 0 ≤ airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) ∧
      airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) ≤ C_g * (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)))
    (hQ0_lap : |airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ))| ≤ C_Q * c ^ (-(5 / 6 : ℝ)))
    (hε_cg : c ^ (-(1 / 3 : ℝ)) ≤ (ceK / (2 * C_g)) ^ (2 / 5 : ℝ)) :
    ceK / 2 ≤ ceK - Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) ∧
    |twoScaleEta p lam R (Mpsi c) c| ≤ (2 * C_Q / ceK) * c ^ (-(5 / 6 : ℝ)) := by
  have hc56 : c ^ (-(5 / 6 : ℝ)) ≤ ceK / (2 * C_g) := by
    rw [show c ^ (-(5 / 6 : ℝ)) = (c ^ (-(1 / 3 : ℝ))) ^ (5 / 2 : ℝ) by rw [← Real.rpow_mul hc_pos.le]; norm_num]
    exact rpow_le_of_inv_rpow (Real.rpow_nonneg hc_pos.le _) (div_pos ceK_pos (mul_pos two_pos hC_g)).le
      (by norm_num) (hε_cg.trans_eq (by congr 1; norm_num))
  have hx_le : (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) ≤ c ^ (-(5 / 6 : ℝ)) :=
    (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hc_pos _) (le_add_of_nonneg_left zero_le_one) (by norm_num)).trans_eq
      (by rw [← Real.rpow_mul hc_pos.le]; norm_num)
  have hg_le_cg : airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) ≤ ceK / 2 :=
    calc _ ≤ C_g * (1 + c ^ (1 / 3 : ℝ)) ^ (-(5 / 2 : ℝ)) := hg_lap.2
      _ ≤ C_g * c ^ (-(5 / 6 : ℝ)) := by gcongr
      _ ≤ C_g * (ceK / (2 * C_g)) := by gcongr
      _ = ceK / 2 := by field_simp [hC_g.ne']
  have hden_ge : ceK / 2 ≤ ceK - Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) :=
    (sub_le_sub_left ((mul_le_mul hM_le1 hg_le_cg hg_lap.1 zero_le_one).trans_eq (one_mul _)) ceK).trans_eq' (by ring)
  have hden_pos : 0 < ceK - Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) :=
    lt_of_lt_of_le (div_pos ceK_pos two_pos) hden_ge
  refine ⟨hden_ge, ?_⟩
  unfold twoScaleEta; rw [abs_div, abs_mul, abs_of_pos hM_pos, abs_of_pos hden_pos]
  calc _ ≤ (1 * (C_Q * c ^ (-(5 / 6 : ℝ)))) / (ceK / 2) :=
        div_le_div₀ (by positivity) (mul_le_mul hM_le1 hQ0_lap (abs_nonneg _) zero_le_one) (div_pos ceK_pos two_pos) hden_ge
    _ = (2 * C_Q / ceK) * c ^ (-(5 / 6 : ℝ)) := by ring

/-- **Theorem `O.11y(3)` (`(ceo:O11y.6)`–`(ceo:O11y.7)`):**
exact finite-`c` odd-Mellin origin equation `M_{ψ,c}(x) Q̃_c(i y) = k ∫ Q_c = k η_c`,
`η_c = O(ε^{5/2})`, and persistence of `F_c = 2 Q_c - S_c > 0` on `u < a₁ - K_*' ε` (`c ≥ c_*'`). -/
theorem twoScale_mellin_origin {p lam γ R θ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hγ : 0 < γ)
    (hR : max (2 * γ) (γ * max 1 (((airyZero 1 - airyZero 2) / 2)⁻¹)) < R)
    (hθ_spec : ∃ K_star > 0, ∃ c_star > 0, ∃ m_tip > 0, ∃ c_far > 0,
      ∀ {c u : ℝ}, c_star ≤ c → u < airyZero 1 - K_star * c ^ (-(1 / 3 : ℝ)) →
        let ε := c ^ (-(1 / 3 : ℝ)); let v₀ := (airyZero 1 - airyZero 2) / 2
        let C_v0 := max 1 v₀⁻¹; let B := ceG1Deriv airyDerivFirstZero u - ceF1 u
        0 < twoScaleF0 p lam γ θ R c u ∧
        (airyZero 1 - v₀ ≤ u → m_tip * ε ≤ twoScaleF0 p lam γ θ R c u) ∧
        (u ≤ airyZero 1 - v₀ → lam * ε ^ 2 * (airyZero 1 - u) ≤ 1 → (R - γ * C_v0) * ε * B ≤ twoScaleF0 p lam γ θ R c u) ∧
        (u ≤ airyZero 1 - v₀ → 1 ≤ lam * ε ^ 2 * (airyZero 1 - u) → (1 / 2) * c_far * B ≤ twoScaleF0 p lam γ θ R c u))
    {Mpsi : ℝ → ℝ} {c₁ : ℝ} (hMpsi : ∀ {c : ℝ}, c₁ ≤ c → 0 < Mpsi c ∧ Mpsi c ≤ 1)
    {C_Q : ℝ} (hC_Q : 0 < C_Q)
    (hQ0_lap : ∀ {c : ℝ}, c₁ ≤ c → |airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ))| ≤ C_Q * c ^ (-(5 / 6 : ℝ))) :
    ∃ C_eta > 0, ∃ K_star' > 0, ∃ c_star' > 0,
      (∀ {c : ℝ}, c_star' ≤ c →
        |twoScaleEta p lam R (Mpsi c) c| ≤ C_eta * c ^ (-(5 / 6 : ℝ)) ∧
        Integrable (twoScaleQc p lam R (Mpsi c) c) ∧
        Mpsi c * airyTwistedLaplace (twoScaleQc p lam R (Mpsi c) c) (ceCs * c ^ (1 / 3 : ℝ)) =
          ceK * ∫ u : ℝ, twoScaleQc p lam R (Mpsi c) c u ∧
        ceK * ∫ u : ℝ, twoScaleQc p lam R (Mpsi c) c u = ceK * twoScaleEta p lam R (Mpsi c) c) ∧
      (∀ {c u : ℝ}, c_star' ≤ c → u < airyZero 1 - K_star' * c ^ (-(1 / 3 : ℝ)) →
        0 < twoScaleFc p lam γ θ R (Mpsi c) c u) := by
  set v₀ : ℝ := (airyZero 1 - airyZero 2) / 2
  have hv₀ : 0 < v₀ := half_pos (sub_pos.mpr (airyZero_lt_of_lt (n := 1) (m := 2) le_rfl (by omega)))
  set C_v0 : ℝ := max 1 v₀⁻¹
  have hR_Cv0 : 0 < R - γ * C_v0 := sub_pos.mpr ((le_max_right (2 * γ) (γ * C_v0)).trans_lt hR)
  have hR_pos : 0 < R := lt_of_lt_of_le (by positivity) ((le_max_left (2 * γ) (γ * C_v0)).trans hR.le)
  obtain ⟨K_star, hK_star, c_star, hc_star, m_tip, hm_tip, c_far, hc_far, hF0⟩ := hθ_spec
  obtain ⟨C_g, hC_g, hg_lap⟩ := airyTwistedLaplace_ceG1_bound
  obtain ⟨M_g1, hM_g1, hg1_tip⟩ := compact_abs_bound (continuous_ceG1 (airyZero 1)).continuousOn (sub_le_self _ hv₀.le)
  let C_eta : ℝ := 2 * C_Q / ceK; have hC_eta : 0 < C_eta := div_pos (mul_pos two_pos hC_Q) ceK_pos
  let ε_cut : ℝ := min 1 (min (1 / R) (min ((ceK / (2 * C_g)) ^ (2 / 5 : ℝ))
    (min ((m_tip / (4 * C_eta * M_g1)) ^ (2 / 3 : ℝ)) (min ((v₀ * (R - γ * C_v0) / (4 * C_eta)) ^ (2 / 3 : ℝ)) ((v₀ * c_far / (8 * C_eta)) ^ (2 / 5 : ℝ))))))
  have hε_cut : 0 < ε_cut := lt_min one_pos (lt_min (div_pos one_pos hR_pos)
    (lt_min (Real.rpow_pos_of_pos (div_pos ceK_pos (by positivity)) _) (lt_min (Real.rpow_pos_of_pos (div_pos hm_tip (by positivity)) _)
      (lt_min (Real.rpow_pos_of_pos (div_pos (mul_pos hv₀ hR_Cv0) (by positivity)) _) (Real.rpow_pos_of_pos (div_pos (mul_pos hv₀ hc_far) (by positivity)) _)))))
  let c_star' : ℝ := max (max c₁ c_star) (ε_cut ^ (-3 : ℝ)); have hc_star' : 0 < c_star' := lt_of_lt_of_le (Real.rpow_pos_of_pos hε_cut _) (le_max_right _ _)
  let K_star' : ℝ := K_star + 1
  have h_setup : ∀ {c : ℝ}, c_star' ≤ c → 0 < c ∧ c ^ (-(1 / 3 : ℝ)) ≤ ε_cut ∧ R * c ^ (-(1 / 3 : ℝ)) ≤ 1 ∧
      0 < ceK - Mpsi c * airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ)) ∧
      |twoScaleEta p lam R (Mpsi c) c| ≤ C_eta * c ^ (-(5 / 6 : ℝ)) := fun {c} hc => by
    have hc_c1 : c₁ ≤ c := (le_max_left _ _).trans ((le_max_left _ _).trans hc); have hc_pos : 0 < c := lt_of_lt_of_le hc_star' hc
    have hε_le : c ^ (-(1 / 3 : ℝ)) ≤ ε_cut := (Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hε_cut _) ((le_max_right _ _).trans hc) (by norm_num)).trans_eq
      (by rw [← Real.rpow_mul hε_cut.le]; norm_num)
    have hRc : R * c ^ (-(1 / 3 : ℝ)) ≤ 1 := (mul_le_mul_of_nonneg_left (hε_le.trans ((min_le_right _ _).trans (min_le_left _ _))) hR_pos.le).trans_eq (by field_simp [hR_pos.ne'])
    obtain ⟨hM_pos, hM_le1⟩ := hMpsi hc_c1
    obtain ⟨hden_ge, heta⟩ := twoScale_eta_bound hc_pos hC_g hC_Q hM_pos hM_le1 (hg_lap (Real.rpow_nonneg hc_pos.le _))
      (hQ0_lap hc_c1) (hε_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    exact ⟨hc_pos, hε_le, hRc, lt_of_lt_of_le (div_pos ceK_pos two_pos) hden_ge, heta⟩
  refine ⟨C_eta, hC_eta, K_star', by positivity, c_star', hc_star', fun {c} hc => ?_, fun {c u} hc hu => ?_⟩
  · obtain ⟨hc_pos, _, hRc, hden_pos, heta_bd⟩ := h_setup hc
    have hQ0_int_pair := (twoScale_origin_mass hp hlam hγ.le hγ.le).1 hR_pos.le hc_pos hRc
    have hQc_int : Integrable (twoScaleQc p lam R (Mpsi c) c) := hQ0_int_pair.1.add (airy_seed_integrals.2.1.1.const_mul _)
    have hQc_mass : ∫ u : ℝ, twoScaleQc p lam R (Mpsi c) c u = twoScaleEta p lam R (Mpsi c) c := by
      unfold twoScaleQc; rw [integral_add hQ0_int_pair.1 (airy_seed_integrals.2.1.1.const_mul _), hQ0_int_pair.2, zero_add, integral_const_mul, ceG1_integral_eq_one, mul_one]
    have hM_tune : Mpsi c * airyTwistedLaplace (twoScaleQc p lam R (Mpsi c) c) (ceCs * c ^ (1 / 3 : ℝ)) = ceK * twoScaleEta p lam R (Mpsi c) c := by
      rw [airyTwistedLaplace_twoScaleQc_linear (lt_trans (by norm_num) hp.1) hlam.le hR_pos.le hc_pos]
      set Q := airyTwistedLaplace (twoScaleQ0 p lam R c) (ceCs * c ^ (1 / 3 : ℝ)); set g := airyTwistedLaplace (ceG1 (airyZero 1)) (ceCs * c ^ (1 / 3 : ℝ))
      unfold twoScaleEta
      rw [show ceK * (Mpsi c * Q / (ceK - Mpsi c * g)) = (ceK * Mpsi c * Q) / (ceK - Mpsi c * g) by ring, eq_div_iff hden_pos.ne']
      calc Mpsi c * (Q + Mpsi c * Q / (ceK - Mpsi c * g) * g) * (ceK - Mpsi c * g)
          = Mpsi c * Q * (ceK - Mpsi c * g) + Mpsi c * g * ((Mpsi c * Q / (ceK - Mpsi c * g)) * (ceK - Mpsi c * g)) := by ring
        _ = Mpsi c * Q * (ceK - Mpsi c * g) + Mpsi c * g * (Mpsi c * Q) := by rw [div_mul_cancel₀ _ hden_pos.ne']
        _ = ceK * Mpsi c * Q := by ring
    exact ⟨heta_bd, hQc_int, hM_tune.trans (by rw [hQc_mass]), by rw [hQc_mass]⟩
  · obtain ⟨hc_pos, hε_le, _, _, heta_bd⟩ := h_setup hc
    have hc_cs : c_star ≤ c := (le_max_right _ _).trans ((le_max_left _ _).trans hc)
    set ε : ℝ := c ^ (-(1 / 3 : ℝ)); have hε_pos : 0 < ε := Real.rpow_pos_of_pos hc_pos _
    rw [show c ^ (-(5 / 6 : ℝ)) = ε ^ (5 / 2 : ℝ) by dsimp [ε]; rw [← Real.rpow_mul hc_pos.le]; norm_num] at heta_bd
    have hu_K : u < airyZero 1 - K_star * c ^ (-(1 / 3 : ℝ)) :=
      lt_of_lt_of_le (by dsimp [K_star'] at hu; exact hu) (sub_le_sub_left (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hε_pos.le) _)
    obtain ⟨_, hF0_tip, hF0_intm, hF0_far⟩ := @hF0 c u hc_cs hu_K
    rw [show twoScaleFc p lam γ θ R (Mpsi c) c u = twoScaleF0 p lam γ θ R c u + 2 * twoScaleEta p lam R (Mpsi c) c * ceG1 (airyZero 1) u by
      unfold twoScaleFc twoScaleQc twoScaleF0; ring]
    have hε_pow : ε ^ (5 / 2 : ℝ) = ε * ε ^ (3 / 2 : ℝ) := by nth_rw 2 [← Real.rpow_one ε]; rw [← Real.rpow_add hε_pos]; norm_num
    have hg1_nn : 0 ≤ ceG1 (airyZero 1) u := by unfold ceG1; positivity
    by_cases huv₀ : airyZero 1 - v₀ ≤ u
    · have hpert : |2 * twoScaleEta p lam R (Mpsi c) c * ceG1 (airyZero 1) u| ≤ 2 * C_eta * M_g1 * ε ^ (5 / 2 : ℝ) := by
        rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hg1_nn]
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left heta_bd two_pos.le) hg1_nn).trans
          ((mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hg1_tip u ⟨huv₀, hu_K.le.trans (sub_le_self _ (mul_pos hK_star hε_pos).le)⟩)) (by positivity)).trans_eq (by ring))
      have hε32 : ε ^ (3 / 2 : ℝ) ≤ m_tip / (4 * C_eta * M_g1) := rpow_le_of_inv_rpow hε_pos.le (div_pos hm_tip (by positivity)).le (by norm_num)
        ((hε_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))).trans_eq (by congr 1; norm_num))
      have hloss : 2 * C_eta * M_g1 * ε ^ (5 / 2 : ℝ) ≤ (m_tip / 2) * ε := by
        rw [hε_pow]; calc 2 * C_eta * M_g1 * (ε * ε ^ (3 / 2 : ℝ)) ≤ 2 * C_eta * M_g1 * (ε * (m_tip / (4 * C_eta * M_g1))) := by gcongr
          _ = (m_tip / 2) * ε := by rw [show 2 * C_eta * M_g1 * (ε * (m_tip / (4 * C_eta * M_g1))) = ((C_eta * M_g1) / (C_eta * M_g1)) * ((2 / 4) * m_tip * ε) by ring, div_self (mul_ne_zero hC_eta.ne' hM_g1.ne')]; ring
      exact lt_of_lt_of_le (by positivity : 0 < (m_tip / 2) * ε) ((add_le_add (hF0_tip huv₀ : m_tip * ε ≤ twoScaleF0 p lam γ θ R c u) (neg_le_of_abs_le (hpert.trans hloss))).trans' (le_of_eq (by ring)))
    · have hu_le : u ≤ airyZero 1 - v₀ := le_of_not_ge huv₀
      have hB_pos := (@o11p_B_eq_X_sq_add_Y_sq u (lt_of_le_of_lt hu_le (sub_lt_self _ hv₀))).2
      have hpert : |2 * twoScaleEta p lam R (Mpsi c) c * ceG1 (airyZero 1) u| ≤ (2 * C_eta / v₀) * ε ^ (5 / 2 : ℝ) * (ceG1Deriv airyDerivFirstZero u - ceF1 u) := by
        rw [abs_mul, abs_mul, abs_two, abs_of_nonneg hg1_nn]
        calc 2 * |twoScaleEta p lam R (Mpsi c) c| * ceG1 (airyZero 1) u ≤ 2 * (C_eta * ε ^ (5 / 2 : ℝ)) * (v₀⁻¹ * (ceG1Deriv airyDerivFirstZero u - ceF1 u)) := by gcongr; exact (ceS0_le_C_B hv₀ hu_le).2
          _ = _ := by ring
      by_cases ht1 : lam * ε ^ 2 * (airyZero 1 - u) ≤ 1
      · have hε32 : ε ^ (3 / 2 : ℝ) ≤ v₀ * (R - γ * C_v0) / (4 * C_eta) := rpow_le_of_inv_rpow hε_pos.le (div_pos (mul_pos hv₀ hR_Cv0) (by positivity)).le (by norm_num)
          ((hε_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))).trans_eq (by congr 1; norm_num))
        have hloss : (2 * C_eta / v₀) * ε ^ (5 / 2 : ℝ) ≤ (1 / 2) * (R - γ * C_v0) * ε := by
          rw [hε_pow]; calc (2 * C_eta / v₀) * (ε * ε ^ (3 / 2 : ℝ)) ≤ (2 * C_eta / v₀) * (ε * (v₀ * (R - γ * C_v0) / (4 * C_eta))) := by gcongr
            _ = (1 / 2) * (R - γ * C_v0) * ε := by rw [show (2 * C_eta / v₀) * (ε * (v₀ * (R - γ * C_v0) / (4 * C_eta))) = (C_eta / C_eta) * (v₀ / v₀) * ((2 / 4) * (R - γ * C_v0) * ε) by ring, div_self hC_eta.ne', div_self hv₀.ne']; ring
        exact lt_of_lt_of_le (by positivity : 0 < (1 / 2) * (R - γ * C_v0) * ε * (ceG1Deriv airyDerivFirstZero u - ceF1 u))
          ((add_le_add (hF0_intm hu_le ht1 : (R - γ * C_v0) * ε * _ ≤ _) (neg_le_of_abs_le (hpert.trans (mul_le_mul_of_nonneg_right hloss hB_pos.le)))).trans' (le_of_eq (by ring)))
      · have hε52 : ε ^ (5 / 2 : ℝ) ≤ v₀ * c_far / (8 * C_eta) := rpow_le_of_inv_rpow hε_pos.le (div_pos (mul_pos hv₀ hc_far) (by positivity)).le (by norm_num)
          ((hε_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))).trans_eq (by congr 1; norm_num))
        have hloss : (2 * C_eta / v₀) * ε ^ (5 / 2 : ℝ) ≤ (1 / 4) * c_far := by
          calc (2 * C_eta / v₀) * ε ^ (5 / 2 : ℝ) ≤ (2 * C_eta / v₀) * (v₀ * c_far / (8 * C_eta)) := by gcongr
            _ = (1 / 4) * c_far := by rw [show (2 * C_eta / v₀) * (v₀ * c_far / (8 * C_eta)) = (C_eta / C_eta) * (v₀ / v₀) * ((2 / 8) * c_far) by ring, div_self hC_eta.ne', div_self hv₀.ne']; ring
        have hF0' : (1 / 2) * c_far * (ceG1Deriv airyDerivFirstZero u - ceF1 u) ≤ twoScaleF0 p lam γ θ R c u := hF0_far hu_le (le_of_not_ge ht1)
        exact lt_of_lt_of_le (by positivity : 0 < (1 / 4) * c_far * (ceG1Deriv airyDerivFirstZero u - ceF1 u))
          ((add_le_add hF0' (neg_le_of_abs_le (hpert.trans (mul_le_mul_of_nonneg_right hloss hB_pos.le)))).trans' (le_of_eq (by ring)))

/-- **Theorem `O.11y(4)` (`(ceo:O11y.8)`), fixed compact Airy-window scale:**
for every compact `U ⊂ ℝ`, `S_c(u) = γ ε S₀(u) + O_{p,θ,λ,U}(ε^{2p})`. -/
theorem twoScaleS_compact_scale {p lam γ θ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hlam : 0 < lam) (hθ : 0 ≤ θ) (_hγ : 0 ≤ γ)
    {U : Set ℝ} (hU : IsCompact U) :
    ∃ C > 0, ∀ {c u : ℝ}, 0 < c → u ∈ U →
      |twoScaleS p lam γ θ c u - γ * c ^ (-(1 / 3 : ℝ)) * ceS0 (airyZero 1) airyDerivFirstZero u| ≤ C * c ^ (-(2 * p / 3 : ℝ)) := by
  have hp01 : p ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hp.1], hp.2⟩; obtain ⟨C_U, _, hcomp⟩ := movingDiagS_compact_bound hp01 hU
  refine ⟨θ * C_U * lam ^ p + 1, by positivity, fun {c u} hc hu => ?_⟩
  set ε : ℝ := c ^ (-(1 / 3 : ℝ)); set h : ℝ := lam * ε ^ 2; have hh_pos : 0 < h := by dsimp [h, ε]; positivity
  have hhp : h ^ p = lam ^ p * c ^ (-(2 * p / 3 : ℝ)) := by
    dsimp [h, ε]; rw [Real.mul_rpow hlam.le (sq_nonneg _), c_rpow_neg_third_sq hc.le, ← Real.rpow_mul hc.le]; congr 2; ring
  rw [show twoScaleS p lam γ θ c u - γ * ε * ceS0 (airyZero 1) airyDerivFirstZero u = θ * movingDiagS p h u by unfold twoScaleS; ring,
    abs_mul, abs_of_nonneg hθ, abs_of_nonneg (movingDiagS_nonneg hp01.1 hh_pos.le u)]
  calc θ * movingDiagS p h u ≤ θ * (C_U * h ^ p) := mul_le_mul_of_nonneg_left (hcomp hh_pos hu) hθ
    _ = (θ * C_U * lam ^ p) * c ^ (-(2 * p / 3 : ℝ)) := by rw [hhp]; ring
    _ ≤ (θ * C_U * lam ^ p + 1) * c ^ (-(2 * p / 3 : ℝ)) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hc.le _)

/-- **Theorem `O.11y(4)` (`(ceo:O11y.9)`), moving negative high-band scale:**
for `x ≥ 1` and `h x ≥ 1` (`h = λ c^{-2/3}`),
`S_c(-x) - γ ε S₀(-x) = (θ / (π x^{3/2})) [1 + O(x⁻¹) + O((h x)^{-2p})]`,
with uniform moving far-tail floor `S_c(-x) ≥ θ (1 - ε₀) / (π x^{3/2})`. -/
theorem twoScaleS_far_scale {p lam γ θ : ℝ} (hp : p ∈ Ioo (1 / 2 : ℝ) 1) (hft : MovingDiagFarTail p)
    (hlam : 0 < lam) (hθ : 0 ≤ θ) (hγ : 0 ≤ γ) :
    (∃ C₁ > 0, ∃ C₂ > 0, ∀ {c x : ℝ}, 0 < c → 1 ≤ x → 1 ≤ lam * (c ^ (-(1 / 3 : ℝ))) ^ 2 * x →
        |(twoScaleS p lam γ θ c (-x) - γ * c ^ (-(1 / 3 : ℝ)) * ceS0 (airyZero 1) airyDerivFirstZero (-x)) -
            θ / (π * x ^ (3 / 2 : ℝ))| ≤ θ * (C₁ * x⁻¹ + C₂ * (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2 * x) ^ (-(2 * p))) / (π * x ^ (3 / 2 : ℝ))) ∧
    (∀ {ε₀ : ℝ}, 0 < ε₀ → ∃ T > 0, ∀ {c x : ℝ}, 0 < c → lam * (c ^ (-(1 / 3 : ℝ))) ^ 2 ≤ 1 →
        T / (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) ≤ x → θ * (1 - ε₀) / (π * x ^ (3 / 2 : ℝ)) ≤ twoScaleS p lam γ θ c (-x)) := by
  obtain ⟨C₁, hC₁, C₂, hC₂, hasy⟩ := movingDiagS_far_asymptotic hp hft
  refine ⟨⟨C₁, hC₁, C₂, hC₂, fun {c x} hc hx1 hhx => ?_⟩, fun {ε₀} hε₀ => ?_⟩
  · rw [show twoScaleS p lam γ θ c (-x) - γ * c ^ (-(1 / 3 : ℝ)) * ceS0 (airyZero 1) airyDerivFirstZero (-x) - θ / (π * x ^ (3 / 2 : ℝ)) =
        θ * (movingDiagS p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (-x) - 1 / (π * x ^ (3 / 2 : ℝ))) by unfold twoScaleS; ring, abs_mul, abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left (hasy (by positivity) hx1 hhx) hθ).trans_eq (by ring)
  · obtain ⟨T, hT, hfloor⟩ := movingDiagS_far_floor hp hft hε₀
    refine ⟨T, hT, fun {c x} hc hh1 hx => ?_⟩
    have hS0_nn : 0 ≤ γ * c ^ (-(1 / 3 : ℝ)) * ceS0 (airyZero 1) airyDerivFirstZero (-x) :=
      mul_nonneg (mul_nonneg hγ (Real.rpow_nonneg hc.le _)) (ceS0_pos _ _ (airyAi_airyZero 1) airyDerivFirstZero_spec.2.2 _).le
    calc θ * (1 - ε₀) / (π * x ^ (3 / 2 : ℝ)) = θ * ((1 - ε₀) / (π * x ^ (3 / 2 : ℝ))) := by ring
      _ ≤ θ * movingDiagS p (lam * (c ^ (-(1 / 3 : ℝ))) ^ 2) (-x) := mul_le_mul_of_nonneg_left (hfloor (by positivity) hh1 hx) hθ
      _ ≤ twoScaleS p lam γ θ c (-x) := by unfold twoScaleS; exact le_add_of_nonneg_right hS0_nn

/-! ### Part 5: Axiom audit -/

/-- info: 'FormalResearch.CohnElkies.dirichletVecS_sq_summable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.dirichletVecS_sq_summable
/-- info: 'FormalResearch.CohnElkies.dirichletVecS_l2_sq_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.dirichletVecS_l2_sq_bound
/-- info: 'FormalResearch.CohnElkies.dirichletVecS_l2_sq_linear_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.dirichletVecS_l2_sq_linear_bound
/-- info: 'FormalResearch.CohnElkies.dirichletVecS_l2_sq_min_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.dirichletVecS_l2_sq_min_bound
/-- info: 'FormalResearch.CohnElkies.movingDiagS_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_nonneg
/-- info: 'FormalResearch.CohnElkies.movingDiagS_le_cohnT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_le_cohnT
/-- info: 'FormalResearch.CohnElkies.movingDiagS_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_integral
/-- info: 'FormalResearch.CohnElkies.movingDiagS_integral_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_integral_asymptotic
/-- info: 'FormalResearch.CohnElkies.movingDiagS_node_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_node_eq
/-- info: 'FormalResearch.CohnElkies.movingDiagS_compact_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_compact_bound
/-- info: 'FormalResearch.CohnElkies.movingDiagS_far_asymptotic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_far_asymptotic
/-- info: 'FormalResearch.CohnElkies.movingDiagS_far_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_far_floor
/-- info: 'FormalResearch.CohnElkies.movingDiagS_le_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_le_B
/-- info: 'FormalResearch.CohnElkies.movingDiagS_le_t_pow_mul_B' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.movingDiagS_le_t_pow_mul_B
/-- info: 'FormalResearch.CohnElkies.twoScale_origin_mass' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.twoScale_origin_mass
/-- info: 'FormalResearch.CohnElkies.twoScaleF0_pos_with_margins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.twoScaleF0_pos_with_margins
/-- info: 'FormalResearch.CohnElkies.twoScaleF0_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.twoScaleF0_pos
/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplace_ceG1_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyTwistedLaplace_ceG1_bound
/-- info: 'FormalResearch.CohnElkies.airyTwistedLaplace_cardinalP_le_of_dirichletV_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.airyTwistedLaplace_cardinalP_le_of_dirichletV_bound
/-- info: 'FormalResearch.CohnElkies.bsplineMellinWeight_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.bsplineMellinWeight_bounds
/-- info: 'FormalResearch.CohnElkies.twoScale_mellin_origin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.twoScale_mellin_origin
/-- info: 'FormalResearch.CohnElkies.twoScaleS_compact_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.twoScaleS_compact_scale
/-- info: 'FormalResearch.CohnElkies.twoScaleS_far_scale' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.CohnElkies.twoScaleS_far_scale

end FormalResearch.CohnElkies

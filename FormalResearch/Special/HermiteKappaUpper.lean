module

public import FormalResearch.Special.HermiteKappaEdge
public import FormalResearch.Special.HermiteKappaSup

/-!
# Upper bound for the Airy amplitude `κ` of the Hermite chain

`κ² x^{1/3} ≤ C_κ` (`hermite_kappa_le`), i.e. `|κ| ≤ C S^{-1/12}`, `S = x²/2` (the numerically sharp value is `κ = S^{-1/12}(1+o(1))`).

Proof.  At the turn site `m` (`q_m ∈ [-1, -1+δ³)`, `X_m ∈ [0, c₂δ] ⊂ [0, 1/8]`, `g ≥ g_min`, `Ai ≥ Ai_min > 0` on `[0, 1/8]`) the Airy-edge
decomposition of `hermite_kappa_edge` gives `|κ| g_min Ai_min / 2 ≤ |φ_n(x)| + K |μ|` (`n = -m`, `2n+1 ∈ (x²-2, x²]`), with `μ` exponentially
small, and `φ_n(x)² ≤ 24·10⁶ x^{-1/3}` by `hermite_envelope` (the uniform sup bound of `HermiteKappaEnvelope`, proved in the `x` variable).
So `κ` is bounded by the envelope; no mass argument in `n` is needed.

**Claim class: proved** (constants existential).  Not formalised here: the lower bound `|κ| ≥ c S^{-1/12}` (`HermiteKappaLower`).
-/

@[expose] public section

open Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

lemma hk_phi_bound (n : ℕ) {x : ℝ} (hx : 0 < x) (hn : x ^ 2 / 2 ≤ 2 * (n : ℝ) + 1) :
    hermitePhi n x ^ 2 * x ^ (1 / 3 : ℝ) ≤ 24000000 := by
  have H := hermite_envelope n x
  set s : ℝ := x ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx _
  have hs3 : s ^ 3 = x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
  set l : ℝ := 2 * (n : ℝ) + 1 with hl
  have hl0 : 0 ≤ l := by positivity
  set t : ℝ := l ^ (1 / 3 : ℝ) with ht
  have ht0 : 0 ≤ t := Real.rpow_nonneg hl0 _
  have ht3 : t ^ 3 = l := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hl0]; norm_num
  have hst : s ^ 2 / 2 ≤ t := by
    have h1 : (s ^ 2 / 2) ^ 3 ≤ t ^ 3 := by
      rw [ht3]
      have : x ^ 2 = s ^ 6 := by rw [← hs3]; ring
      have h2 : (s ^ 2 / 2) ^ 3 = s ^ 6 / 8 := by ring
      rw [h2]
      have : 0 ≤ s ^ 6 := by positivity
      linarith
    exact le_of_pow_le_pow_left₀ (by norm_num) ht0 h1
  have hsq : s / 2 ≤ √t := by
    refine Real.le_sqrt_of_sq_le ?_
    nlinarith [sq_nonneg s]
  have hmono : √t ≤ √(|l - x ^ 2| + t) := Real.sqrt_le_sqrt (by have := abs_nonneg (l - x ^ 2); linarith)
  have hphi : 0 ≤ hermitePhi n x ^ 2 := sq_nonneg _
  have h1 : hermitePhi n x ^ 2 * (s / 2) ≤ 12000000 :=
    le_trans (mul_le_mul_of_nonneg_left (hsq.trans hmono) hphi) H
  linarith

lemma hk_mu_bound {Cmu ξ0 x δ μ : ℝ} (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) (hx : 4 ≤ x) (hδ : 0 < δ)
    (hδx : δ ^ 3 = 2 / x ^ 2) (hμ : |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-ξ0 / δ ^ 3) / δ) :
    μ ^ 2 * x ^ (1 / 3 : ℝ) ≤ 8 * Cmu ^ 2 / ξ0 ^ 2 / x ^ (1 / 3 : ℝ) := by
  have hx0 : 0 < x := by linarith
  set s : ℝ := x ^ (1 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos hx0 _
  have hs3 : s ^ 3 = x := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hs1 : 1 ≤ s := by
    by_contra h
    have : s ^ 3 < 1 := by nlinarith [pow_pos hs0 2]
    linarith
  have hx2 : x ^ 2 = s ^ 6 := by rw [← hs3]; ring
  -- `1/δ ≤ s²`
  have hδs : 1 / s ^ 2 ≤ δ := by
    have h1 : (1 / s ^ 2) ^ 3 ≤ δ ^ 3 := by
      rw [hδx, hx2, div_pow]
      rw [show (s ^ 2) ^ 3 = s ^ 6 by ring]
      have : 0 < s ^ 6 := by positivity
      rw [one_pow]
      exact div_le_div_of_nonneg_right (by norm_num) this.le
    exact le_of_pow_le_pow_left₀ (by norm_num) hδ.le h1
  have hinv : 1 / δ ≤ s ^ 2 := by
    rw [div_le_iff₀ hδ]
    have := mul_le_mul_of_nonneg_left hδs (by positivity : 0 ≤ s ^ 2)
    have e : s ^ 2 * (1 / s ^ 2) = 1 := by field_simp
    linarith
  have hexp : -ξ0 / δ ^ 3 = -(ξ0 * s ^ 6 / 2) := by
    rw [hδx, hx2]; field_simp
  rw [hexp] at hμ
  have hsq : √(x ^ 2 + 2) ≤ 2 * s ^ 3 := by
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc x ^ 2 + 2 ≤ 4 * x ^ 2 := by nlinarith
      _ = (2 * s ^ 3) ^ 2 := by rw [mul_pow, hs3]; ring
  have h1 : |μ| ≤ Cmu * (2 * s ^ 3) * Real.exp (-(ξ0 * s ^ 6 / 2)) * s ^ 2 := by
    have e : Cmu * √(x ^ 2 + 2) * Real.exp (-(ξ0 * s ^ 6 / 2)) / δ =
        Cmu * √(x ^ 2 + 2) * Real.exp (-(ξ0 * s ^ 6 / 2)) * (1 / δ) := by ring
    rw [e] at hμ
    refine hμ.trans ?_
    have hE := (Real.exp_pos (-(ξ0 * s ^ 6 / 2))).le
    refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hsq hCmu.le) le_rfl hE (by positivity)) hinv (by positivity) (by positivity)
  have h2 : μ ^ 2 ≤ (Cmu * (2 * s ^ 3) * Real.exp (-(ξ0 * s ^ 6 / 2)) * s ^ 2) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e3 : (Cmu * (2 * s ^ 3) * Real.exp (-(ξ0 * s ^ 6 / 2)) * s ^ 2) ^ 2 =
      4 * Cmu ^ 2 * s ^ 10 * Real.exp (-(ξ0 * s ^ 6)) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(ξ0 * s ^ 6 / 2)) = -(ξ0 * s ^ 6) := by push_cast; ring
    rw [this]; ring
  rw [e3] at h2
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ ξ0 * s ^ 6 by positivity)
  have h4 : Real.exp (-(ξ0 * s ^ 6)) ≤ 2 / (ξ0 ^ 2 * s ^ 12) := by
    rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
    nlinarith [mul_pos hξ0 (pow_pos hs0 6)]
  have h5 : μ ^ 2 * s ≤ 4 * Cmu ^ 2 * s ^ 10 * (2 / (ξ0 ^ 2 * s ^ 12)) * s := by
    have := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 4 * Cmu ^ 2 * s ^ 10)
    have := mul_le_mul_of_nonneg_right (h2.trans this) hs0.le
    exact this
  have e6 : 4 * Cmu ^ 2 * s ^ 10 * (2 / (ξ0 ^ 2 * s ^ 12)) * s = 8 * Cmu ^ 2 / ξ0 ^ 2 / s := by
    field_simp
    norm_num
  rw [e6] at h5
  exact h5

lemma hk_mu_bound_weak {Cmu ξ0 x δ μ : ℝ} (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) (hx : 4 ≤ x) (hδ : 0 < δ)
    (hδx : δ ^ 3 = 2 / x ^ 2) (hμ : |μ| ≤ Cmu * √(x ^ 2 + 2) * Real.exp (-ξ0 / δ ^ 3) / δ) :
    μ ^ 2 * x ^ (1 / 3 : ℝ) ≤ 8 * Cmu ^ 2 / ξ0 ^ 2 := by
  have h := hk_mu_bound hCmu hξ0 hx hδ hδx hμ
  have hx0 : 0 < x := by linarith
  have hs1 : 1 ≤ x ^ (1 / 3 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  exact h.trans (div_le_self (by positivity) hs1)

lemma hk_airy_consts : ∃ aiMin biMax : ℝ, 0 < aiMin ∧ 0 ≤ biMax ∧
    ∀ X ∈ Set.Icc (0 : ℝ) (1 / 8), aiMin ≤ airyAi X ∧ |airyBi X| ≤ biMax := by
  have hne : (Set.Icc (0 : ℝ) (1 / 8)).Nonempty := ⟨0, le_refl _, by norm_num⟩
  have hcA : ContinuousOn airyAi (Set.Icc (0 : ℝ) (1 / 8)) :=
    differentiable_airyAi.continuous.continuousOn
  have hcB : ContinuousOn airyBi (Set.Icc (0 : ℝ) (1 / 8)) :=
    (continuous_iff_continuousAt.2 fun y => (hasDerivAt_airyBi y).continuousAt).continuousOn
  obtain ⟨x1, hx1, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcA
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcB
  refine ⟨airyAi x1, max B 0, airyAi_pos hx1.1, le_max_right _ _, fun X hX => ⟨hmin hX, ?_⟩⟩
  have := hB X hX
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

lemma hk_biwt_le {X : ℝ} (hX : X ∈ Set.Icc (0 : ℝ) (1 / 8)) : airyBiWt X ≤ 8 := by
  rw [airyBiWt_eq_mul]
  have h1 : airyXi X ≤ 2 / 3 := by
    unfold airyXi
    have : max X 0 ≤ 1 := max_le (by linarith [hX.2]) zero_le_one
    have h2 : (max X 0) ^ (3 / 2 : ℝ) ≤ 1 := Real.rpow_le_one (le_max_right _ _) this (by norm_num)
    linarith
  have h2 : Real.exp (2 * airyXi X) ≤ Real.exp (4 / 3) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (4 / 3) ≤ 8 := by
    have := Real.exp_one_lt_d9
    have h4 : Real.exp (4 / 3) ≤ Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by norm_num)
    nlinarith [Real.exp_one_gt_d9]
  have := mul_le_mul (airyWt_le_one X) (h2.trans h3) (Real.exp_pos _).le zero_le_one
  linarith

/-- Pure algebra at the turn site: the Airy-edge decomposition bounds `|κ|` by `|Y| + K|μ|`. -/
lemma hk_site_alg {κ μ Y gm Ai Bi gmin gmax aiMin biMax C δ3 W Wb : ℝ} (hC : 0 < C) (hgmin : 0 < gmin)
    (hgl : gmin ≤ gm) (hgu : gm ≤ gmax) (hai : 0 < aiMin) (hAi : aiMin ≤ Ai) (hBi : |Bi| ≤ biMax)
    (hW : W ≤ 1) (hWb : Wb ≤ 8) (hδ0 : 0 ≤ δ3) (hδ1 : δ3 ≤ 1) (hCδ : C * δ3 ≤ gmin * aiMin / 2)
    (hY : |Y - (κ * (gm * Ai) + μ * (gm * Bi))| ≤ C * δ3 * (|κ| * W + |μ| * Wb)) :
    gmin * aiMin / 2 * |κ| ≤ |Y| + (gmax * biMax + 8 * C) * |μ| := by
  set a : ℝ := gmin * aiMin / 2 with ha
  have hgm0 : 0 < gm := lt_of_lt_of_le hgmin hgl
  have hAi0 : 0 ≤ Ai := hai.le.trans hAi
  have hAiX : gmin * aiMin ≤ gm * Ai := mul_le_mul hgl hAi hai.le hgm0.le
  have hkap : |κ * (gm * Ai)| = |κ| * (gm * Ai) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg hgm0.le hAi0)]
  have hbiX : |μ * (gm * Bi)| ≤ |μ| * (gmax * biMax) := by
    rw [abs_mul, abs_mul, abs_of_pos hgm0]
    have : gm * |Bi| ≤ gmax * biMax := mul_le_mul hgu hBi (abs_nonneg _) (by linarith)
    exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have hwt : C * δ3 * (|κ| * W + |μ| * Wb) ≤ a * |κ| + C * 8 * |μ| := by
    have h1 : |κ| * W ≤ |κ| := mul_le_of_le_one_right (abs_nonneg κ) hW
    have h2 : |μ| * Wb ≤ |μ| * 8 := mul_le_mul_of_nonneg_left hWb (abs_nonneg μ)
    have h4 : 0 ≤ C * δ3 := by positivity
    have h6 : C * δ3 * |κ| ≤ a * |κ| := mul_le_mul_of_nonneg_right hCδ (abs_nonneg _)
    have h7 : C * δ3 ≤ C := mul_le_of_le_one_right hC.le hδ1
    calc C * δ3 * (|κ| * W + |μ| * Wb) ≤ C * δ3 * (|κ| + |μ| * 8) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) h4
      _ = C * δ3 * |κ| + (C * δ3) * (|μ| * 8) := by ring
      _ ≤ a * |κ| + C * (|μ| * 8) := add_le_add h6 (mul_le_mul_of_nonneg_right h7 (by positivity))
      _ = a * |κ| + C * 8 * |μ| := by ring
  have h1 : |κ * (gm * Ai)| ≤ |Y| + |μ * (gm * Bi)| + |Y - (κ * (gm * Ai) + μ * (gm * Bi))| := by
    generalize κ * (gm * Ai) = P at *
    generalize μ * (gm * Bi) = Q at *
    have e : P = Y - (Y - (P + Q)) - Q := by ring
    calc |P| = |Y - (Y - (P + Q)) - Q| := by rw [← e]
      _ ≤ |Y - (Y - (P + Q))| + |Q| := abs_sub _ _
      _ ≤ |Y| + |Y - (P + Q)| + |Q| := by
        have := abs_sub Y (Y - (P + Q)); linarith
      _ = |Y| + |Q| + |Y - (P + Q)| := by ring
  rw [hkap] at h1
  have h2 : |κ| * (gmin * aiMin) ≤ |κ| * (gm * Ai) := mul_le_mul_of_nonneg_left hAiX (abs_nonneg _)
  have h3 : |κ| * (gmin * aiMin) = 2 * (a * |κ|) := by rw [ha]; ring
  have h4 : (gmax * biMax + 8 * C) * |μ| = |μ| * (gmax * biMax) + C * 8 * |μ| := by ring
  linarith

/-- Index arithmetic at the turn: `q_m ∈ [-1, -1+δ³)`, `δ³ = 2/x²`, `n = -m` give `x²/2 ≤ 2n+1`. -/
lemma hk_index {x δ : ℝ} {m : ℤ} {n : ℕ} (hx : 4 ≤ x) (hδx : δ ^ 3 = 2 / x ^ 2)
    (hqm2 : -δ ^ 3 / 2 + (m : ℝ) * δ ^ 3 < -1 + δ ^ 3) (hn : (n : ℝ) = -(m : ℝ)) :
    x ^ 2 / 2 ≤ 2 * (n : ℝ) + 1 := by
  have hx2' : δ ^ 3 * x ^ 2 = 2 := by
    have : x ^ 2 ≠ 0 := by positivity
    rw [hδx]; field_simp
  have hx2pos : 0 < x ^ 2 := by positivity
  have hkey : 2 * (m : ℝ) - 1 < -x ^ 2 + 2 := by
    have h := mul_lt_mul_of_pos_right hqm2 hx2pos
    have hm2 : (m : ℝ) * (δ ^ 3 * x ^ 2) = (m : ℝ) * 2 := by rw [hx2']
    linarith [h, hx2', hm2]
  have : 16 ≤ x ^ 2 := by nlinarith
  rw [hn]; linarith

/-- Final algebra: `a|κ| ≤ |φ| + K|μ|`, `φ² w ≤ 24·10⁶`, `μ² w ≤ 8 C_μ²/ξ₀²` give `κ² w ≤ C_κ`. -/
lemma hk_final {Cmu ξ0 a K κ μ φ x : ℝ} (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0) (ha0 : 0 < a) (hK0 : 0 ≤ K)
    (hκ1 : a * |κ| ≤ |φ| + K * |μ|) (hphi : φ ^ 2 * x ^ (1 / 3 : ℝ) ≤ 24000000)
    (hmu : μ ^ 2 * x ^ (1 / 3 : ℝ) ≤ 8 * Cmu ^ 2 / ξ0 ^ 2) (hx : 0 < x) :
    κ ^ 2 * x ^ (1 / 3 : ℝ) ≤ (48000000 + 16 * K ^ 2 * Cmu ^ 2 / ξ0 ^ 2) / a ^ 2 := by
  set w : ℝ := x ^ (1 / 3 : ℝ) with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hx _
  have hsq : (a * |κ|) ^ 2 ≤ 2 * φ ^ 2 + 2 * K ^ 2 * μ ^ 2 := by
    have h0 : 0 ≤ a * |κ| := by positivity
    have h1 : (a * |κ|) ^ 2 ≤ (|φ| + K * |μ|) ^ 2 := pow_le_pow_left₀ h0 hκ1 2
    have h2 : (|φ| + K * |μ|) ^ 2 ≤ 2 * |φ| ^ 2 + 2 * (K * |μ|) ^ 2 := by
      nlinarith [sq_nonneg (|φ| - K * |μ|)]
    have e1 : |φ| ^ 2 = φ ^ 2 := sq_abs _
    have e2 : (K * |μ|) ^ 2 = K ^ 2 * μ ^ 2 := by rw [mul_pow, sq_abs]
    linarith
  have hfin : a ^ 2 * (κ ^ 2 * w) ≤ 48000000 + 16 * K ^ 2 * Cmu ^ 2 / ξ0 ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_right hsq hw0.le
    have e : (a * |κ|) ^ 2 * w = a ^ 2 * (κ ^ 2 * w) := by rw [mul_pow, sq_abs]; ring
    have h3 : (2 * φ ^ 2 + 2 * K ^ 2 * μ ^ 2) * w = 2 * (φ ^ 2 * w) + 2 * K ^ 2 * (μ ^ 2 * w) := by ring
    have h4 : 2 * K ^ 2 * (μ ^ 2 * w) ≤ 2 * K ^ 2 * (8 * Cmu ^ 2 / ξ0 ^ 2) :=
      mul_le_mul_of_nonneg_left hmu (by positivity)
    have h5 : 2 * K ^ 2 * (8 * Cmu ^ 2 / ξ0 ^ 2) = 16 * K ^ 2 * Cmu ^ 2 / ξ0 ^ 2 := by ring
    linarith
  rw [le_div_iff₀ (by positivity)]
  linarith

/-- **Order bound, upper half**: for the data of `HkEdge` (with positive constants) there are `δ₁, C_κ > 0` such that
`κ² x^{1/3} ≤ C_κ`, i.e. `|κ| ≤ C S^{-1/12}`, whenever `δ ≤ δ₁`, `δ³ = 2/x²`. -/
theorem hermite_kappa_le {r C Cmu ξ0 gmax gmin c1 c2 Lg : ℝ} (hC : 0 < C) (hCmu : 0 < Cmu) (hξ0 : 0 < ξ0)
    (hgmin : 0 < gmin) (hgg : gmin ≤ gmax) :
    ∃ δ1 Ck : ℝ, 0 < δ1 ∧ 0 < Ck ∧ ∀ (x δ : ℝ) (J m N : ℤ) (κ μ : ℝ), 0 < x → 0 < δ → δ ≤ δ1 → δ ^ 3 = 2 / x ^ 2 →
      HkEdge r C Cmu ξ0 gmax gmin c1 c2 Lg x δ J m N κ μ → κ ^ 2 * x ^ (1 / 3 : ℝ) ≤ Ck := by
  obtain ⟨aiMin, biMax, hai, hbi, hAB⟩ := hk_airy_consts
  have hgmax : 0 < gmax := lt_of_lt_of_le hgmin hgg
  set a : ℝ := gmin * aiMin / 2 with ha
  have ha0 : 0 < a := by positivity
  set K : ℝ := gmax * biMax + 8 * C with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨min (1 / 2) (a / C), (48000000 + 16 * K ^ 2 * Cmu ^ 2 / ξ0 ^ 2) / a ^ 2, by positivity, by positivity, ?_⟩
  intro x δ J m N κ μ hx hδ hδ1 hδx h
  obtain ⟨hJN, hJm, hmN, hNneg, hwin, hqJ2, hqm1, hqm2, hqN, hqN1, hg, hgap, hLg, ⟨hX0, hX1⟩, hc2δ, hμ, hY⟩ := h
  have hδ12 : δ ≤ 1 / 2 := hδ1.trans (min_le_left _ _)
  have hδa : δ ≤ a / C := hδ1.trans (min_le_right _ _)
  have hδ3 : δ ^ 3 ≤ δ := by nlinarith [pow_pos hδ 2]
  have hCδ : C * δ ^ 3 ≤ a := by
    have h1 : C * δ ≤ a := by rwa [le_div_iff₀ hC, mul_comm] at hδa
    nlinarith [mul_le_mul_of_nonneg_left hδ3 hC.le]
  have hx4 : 4 ≤ x := by
    have hx2 : 2 / δ ^ 3 = x ^ 2 := by rw [hδx]; field_simp
    have h8 : δ ^ 3 ≤ 1 / 8 := by nlinarith [pow_pos hδ 2]
    have : 16 ≤ x ^ 2 := by
      rw [← hx2, le_div_iff₀ (by positivity)]
      nlinarith
    nlinarith
  have hm : m ∈ Finset.Icc J (N + 1) := by rw [Finset.mem_Icc]; omega
  have hYm := hY m hm
  have hXI : turnX hmU (-1) (-δ ^ 3 / 2) δ m ∈ Set.Icc (0 : ℝ) (1 / 8) := ⟨hX0, hX1.trans hc2δ⟩
  obtain ⟨hAi, hBi⟩ := hAB _ hXI
  have hW' : airyBiWt (turnX hmU (-1) (-δ ^ 3 / 2) δ m) ≤ 8 := hk_biwt_le hXI
  have hkap := hk_site_alg (κ := κ) (μ := μ) (Y := hermitePsi (-m) x) hC hgmin (hg m hm).1 (hg m hm).2 hai hAi hBi
    (airyWt_le_one _) hW' (by positivity) (by linarith [hδ3, hδ12]) hCδ hYm
  have hmneg : m ≤ -1 := hmN.trans hNneg
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = -m := ⟨(-m).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hYn : hermitePsi (-m) x = hermitePhi n x := by rw [← hn, hermitePsi_natCast]
  have hnR : (n : ℝ) = -(m : ℝ) := by exact_mod_cast hn
  have hqm2' : -δ ^ 3 / 2 + (m : ℝ) * δ ^ 3 < -1 + δ ^ 3 := by
    have := hqm2; simp only [dalQ] at this; exact this
  have hlam := hk_index hx4 hδx hqm2' hnR
  have hphi := hk_phi_bound n hx hlam
  rw [hYn] at hkap
  have hmu := hk_mu_bound_weak hCmu hξ0 hx4 hδ hδx hμ
  exact hk_final hCmu hξ0 ha0 hK0 hkap hphi hmu hx

/-- info: 'FormalResearch.Special.hermite_kappa_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_kappa_le

end FormalResearch.Special

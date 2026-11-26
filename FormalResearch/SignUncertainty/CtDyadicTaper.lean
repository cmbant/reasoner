module

public import Mathlib
public import FormalResearch.SignUncertainty.CtBoasTent

/-!
# `ct:dyadic` (4), `ct:taper-harnack`: the taper weight `w̃_R` and its block regularity (phase-free)

`constant_terms_lower.tex`, `ct:dyadic` (4) (the weight `w_R(v) = 1 - W₆(-v) = 2(v/R)^{12} - (v/R)^{24}` and the taper
`w̃_R(ξ) = w_R(-û(ũ(ξ)))`) and the proof of `ct:boas` Step 5 (c), (d) (`ct:taper-harnack`, `ct:Bj-pointwise`).

* `taperW R v = w_R(clamp(v))`, `clamp(v) = max 0 (min v R)` (`C¹` in `v`, `= 1` for `v ≥ R`): `taperW_le`
  (`w_R ≤ min(1, 2(v/R)^{12})`), `taperW_ge` (`w_R ≥ min(1, (v/R)^{12})`), `taperW_sub_le`
  (`0 ≤ w_R(v') - w_R(v) ≤ 24 w_R(v')(v'-v)/v'` for `0 < v ≤ v'`: the integrated form of `w_R'(v) ≤ 24 w_R(v)/v`),
  `taperW_harnack` (`v' ≤ ρv ⇒ w_R(v') ≤ 2ρ^{12} w_R(v)`).
* `TaperProfile R A v`: the chart facts of `ct:taper-harnack` (c) about `v(L) = -û(-v'(L))` in integral form
  (`v > 0`, `v` nondecreasing, `v(L')/v(L) ≤ (L'/L)^{A_v}`, i.e. `L ∂_L log v ≤ A_v`); `TaperProfile.reg` gives
  `TaperReg wt A Kw` for `wt = w_R ∘ v` with `K_w = 2·3^{12A}` (`taperKw`): `wt` monotone, `wt(L') - wt(L) ≤ 24A wt(L')(L'-L)/L'`
  (`|w̃'| ≤ 24A_v w̃/L'`) and `wt(L') ≤ K_w wt(L)` for `L ≤ L' ≤ 3L` (`(ct:taper-harnack)`).
* Block form for the tent grid (`tentQ a j = I_j^{**}`): the Lipschitz bound `taper_hlip` and supremum `taper_hSup` of
  `w̃(1 - 𝔰_far)χ_j` on `Q_j` (the hypotheses `hlip`, `hSup` of `boas_freeze_field`) and the bounds `taper_hMp_bd`, `taper_hS_bd`
  (`M_j' ≤ M_j^σ + K_mp w̃(L)/min(L,1)`, `S_j ≤ K_w w̃(L)`, the hypotheses of `boas_pointwise_field`), with the explicit
  `Mp = tapMp`, `S = tapS`.  Differences from the TeX: the Lipschitz bounds are derivative-free (log-Lipschitz of `w̃` through
  `taperW_sub_le`), the constants are `K_mp = (13/12)K₀`, `K₀ = (288/11)A K_w + 108K_w` instead of `72A_v + 9C_χ`, which is only a
  change of absolute constants (`δ_j = min(L_j,1)/36` in the Lean tent grid).

**Proved**, unconditional (`TaperProfile` is a hypothesis structure for the chart, see `CtDyadicTaperChart`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

/-! ### The weight `w_R` as a function of `v` -/

/-- `x = (clamp(v)/R)^{12}`, `clamp(v) = max 0 (min v R)`. -/
noncomputable def taperX (R v : ℝ) : ℝ := (max 0 (min v R) / R) ^ 12

/-- **`w_R(v) = 2(v/R)^{12} - (v/R)^{24}`** (`ct:dyadic` (4)) on `[0, R]`, extended by `0` for `v ≤ 0` and by `1` for `v ≥ R`. -/
noncomputable def taperW (R v : ℝ) : ℝ := taperX R v * (2 - taperX R v)

lemma taperX_nonneg {R : ℝ} (hR : 0 < R) (v : ℝ) : 0 ≤ taperX R v :=
  pow_nonneg (div_nonneg (le_max_left _ _) hR.le) _

lemma taperX_le_one {R : ℝ} (hR : 0 < R) (v : ℝ) : taperX R v ≤ 1 :=
  pow_le_one₀ (div_nonneg (le_max_left _ _) hR.le)
    ((div_le_one hR).2 (max_le hR.le (min_le_right _ _)))

lemma taperX_mono {R : ℝ} (hR : 0 < R) {v v' : ℝ} (h : v ≤ v') : taperX R v ≤ taperX R v' :=
  pow_le_pow_left₀ (div_nonneg (le_max_left _ _) hR.le)
    (div_le_div_of_nonneg_right (max_le_max le_rfl (min_le_min h le_rfl)) hR.le) _

lemma taperW_nonneg {R : ℝ} (hR : 0 < R) (v : ℝ) : 0 ≤ taperW R v := by
  have h0 := taperX_nonneg hR v; have h1 := taperX_le_one hR v
  unfold taperW; nlinarith

lemma taperW_le_one {R : ℝ} (_hR : 0 < R) (v : ℝ) : taperW R v ≤ 1 := by
  unfold taperW; nlinarith [sq_nonneg (taperX R v - 1)]

lemma taperX_le_taperW {R : ℝ} (hR : 0 < R) (v : ℝ) : taperX R v ≤ taperW R v := by
  have h0 := taperX_nonneg hR v; have h1 := taperX_le_one hR v
  unfold taperW; nlinarith

lemma taperW_le_two_mul {R : ℝ} (hR : 0 < R) (v : ℝ) : taperW R v ≤ 2 * taperX R v := by
  have h0 := taperX_nonneg hR v
  unfold taperW; nlinarith

lemma taperX_of_ge {R v : ℝ} (hR : 0 < R) (hv : R ≤ v) : taperX R v = 1 := by
  unfold taperX
  rw [min_eq_right hv, max_eq_right hR.le, div_self hR.ne']; simp

/-- `w_R(v) = 1` for `v ≥ R`. -/
lemma taperW_of_ge {R v : ℝ} (hR : 0 < R) (hv : R ≤ v) : taperW R v = 1 := by
  unfold taperW; rw [taperX_of_ge hR hv]; norm_num

lemma taperW_mono {R : ℝ} (hR : 0 < R) {v v' : ℝ} (h : v ≤ v') : taperW R v ≤ taperW R v' := by
  have h1 := taperX_mono hR h; have h2 := taperX_le_one hR v'; have h3 := taperX_nonneg hR v
  unfold taperW; nlinarith

/-- `w_R(v) ≤ 2 (v/R)^{12}` for `v ≥ 0`. -/
lemma taperW_le_pow {R v : ℝ} (hR : 0 < R) (hv : 0 ≤ v) : taperW R v ≤ 2 * (v / R) ^ 12 := by
  have h : taperX R v ≤ (v / R) ^ 12 := by
    unfold taperX
    exact pow_le_pow_left₀ (div_nonneg (le_max_left _ _) hR.le)
      (div_le_div_of_nonneg_right (max_le hv (min_le_left _ _)) hR.le) _
  linarith [taperW_le_two_mul hR v]

/-- `w_R(v) ≥ min(1, (v/R)^{12})` for `v ≥ 0`. -/
lemma taperW_ge {R v : ℝ} (hR : 0 < R) (hv : 0 ≤ v) : min 1 ((v / R) ^ 12) ≤ taperW R v := by
  rcases le_or_gt R v with h | h
  · rw [taperW_of_ge hR h]; exact min_le_left _ _
  · have hx : taperX R v = (v / R) ^ 12 := by
      unfold taperX; rw [min_eq_left h.le, max_eq_right hv]
    have := taperX_le_taperW hR v
    rw [hx] at this
    exact (min_le_right _ _).trans this

/-- **`w_R'(v) ≤ 24 w_R(v)/v`, integrated**: `0 ≤ w_R(v') - w_R(v) ≤ 24 w_R(v')(v' - v)/v'` for `0 < v ≤ v'`. -/
lemma taperW_sub_le {R v v' : ℝ} (hR : 0 < R) (hv : 0 < v) (hvv : v ≤ v') :
    taperW R v' - taperW R v ≤ 24 * taperW R v' * ((v' - v) / v') := by
  have hv' : 0 < v' := lt_of_lt_of_le hv hvv
  have hc0 : 0 < min v R := lt_min hv hR
  have hc'0 : 0 < min v' R := lt_min hv' hR
  have hcc' : min v R ≤ min v' R := min_le_min hvv le_rfl
  have hx : taperX R v = (min v R / R) ^ 12 := by unfold taperX; rw [max_eq_right hc0.le]
  have hx' : taperX R v' = (min v' R / R) ^ 12 := by unfold taperX; rw [max_eq_right hc'0.le]
  have hratio : v / v' ≤ min v R / min v' R := by
    rcases le_or_gt v' R with h1 | h1
    · rw [min_eq_left (hvv.trans h1), min_eq_left h1]
    · rw [min_eq_right h1.le]
      rcases le_or_gt v R with h2 | h2
      · rw [min_eq_left h2]
        exact div_le_div_of_nonneg_left hv.le hR h1.le
      · rw [min_eq_right h2.le, div_self hR.ne']
        exact (div_le_one hv').2 hvv
  set r := min v R / min v' R with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r ≤ 1 := (div_le_one hc'0).2 hcc'
  have hxr : taperX R v = r ^ 12 * taperX R v' := by
    rw [hx, hx', ← mul_pow, hr]; congr 1; field_simp
  have hbern : 1 - 12 * (1 - r) ≤ r ^ 12 := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ r - 1 by linarith) 12
    norm_num at this; linarith
  have hx0 := taperX_nonneg hR v
  have hx1 := taperX_le_one hR v
  have hx0' := taperX_nonneg hR v'
  have hx1' := taperX_le_one hR v'
  have hdiff : taperX R v' - taperX R v ≤ taperX R v' * (12 * ((v' - v) / v')) := by
    have e : 1 - v / v' = (v' - v) / v' := by field_simp
    have h12 : 1 - r ≤ (v' - v) / v' := by linarith
    have : taperX R v' - taperX R v = taperX R v' * (1 - r ^ 12) := by rw [hxr]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hx0'
  have hmon : taperX R v ≤ taperX R v' := taperX_mono hR hvv
  have hdd : 0 ≤ (v' - v) / v' := div_nonneg (by linarith) hv'.le
  have hW : taperW R v' - taperW R v = (taperX R v' - taperX R v) * (2 - taperX R v - taperX R v') := by
    unfold taperW; ring
  rw [hW]
  have hle : taperX R v' ≤ taperW R v' := taperX_le_taperW hR v'
  calc (taperX R v' - taperX R v) * (2 - taperX R v - taperX R v')
      ≤ (taperX R v' - taperX R v) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ (taperX R v' * (12 * ((v' - v) / v'))) * 2 := by linarith
    _ = 24 * taperX R v' * ((v' - v) / v') := by ring
    _ ≤ 24 * taperW R v' * ((v' - v) / v') := by
        have := mul_le_mul_of_nonneg_right hle hdd
        nlinarith

/-- **Harnack inequality for `w_R`**: `0 < v ≤ v' ≤ ρ v`, `ρ ≥ 1` give `w_R(v') ≤ 2ρ^{12} w_R(v)`. -/
lemma taperW_harnack {R v v' ρ : ℝ} (hR : 0 < R) (hv : 0 < v) (hvv : v ≤ v') (hρ : 1 ≤ ρ)
    (hr : v' ≤ ρ * v) : taperW R v' ≤ 2 * ρ ^ 12 * taperW R v := by
  have hρ0 : 0 < ρ := by linarith
  have hρ12 : 1 ≤ ρ ^ 12 := one_le_pow₀ hρ
  have hW0 := taperW_nonneg hR v
  have hge := taperW_ge hR hv.le
  rcases le_or_gt R v' with h | h
  · rw [taperW_of_ge hR h]
    have h1 : R ≤ ρ * v := h.trans hr
    have h2 : (1 / ρ) ^ 12 ≤ (v / R) ^ 12 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_div_iff₀ hρ0 hR]; linarith
    have hz : (1 / ρ) ^ 12 ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hρ0).2 hρ)
    have h3 : (1 / ρ) ^ 12 ≤ taperW R v := (le_min hz h2).trans hge
    have h4 : (1 / ρ) ^ 12 * ρ ^ 12 = 1 := by rw [← mul_pow]; field_simp
    nlinarith [mul_le_mul_of_nonneg_right h3 (by positivity : (0 : ℝ) ≤ ρ ^ 12)]
  · have hv'0 : 0 < v' := lt_of_lt_of_le hv hvv
    have h1 : taperW R v' ≤ 2 * (v' / R) ^ 12 := taperW_le_pow hR hv'0.le
    have h2 : (v' / R) ^ 12 ≤ ρ ^ 12 * (v / R) ^ 12 := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      rw [div_le_iff₀ hR]; rw [mul_div_assoc']; rw [div_mul_cancel₀ _ hR.ne']; exact hr
    have h3 : (v / R) ^ 12 ≤ taperW R v := by
      have hvR : v / R ≤ 1 := (div_le_one hR).2 (hvv.trans h.le)
      have := pow_le_one₀ (div_nonneg hv.le hR.le) hvR (n := 12)
      have h5 := min_eq_right this
      rw [← h5]; exact hge
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * ρ ^ 12)]

/-! ### The taper as a function of `L`: regularity from the chart facts -/

/-- `K_w = 2·3^{12A}` (`ct:taper-harnack`). -/
noncomputable def taperKw (A : ℝ) : ℝ := 2 * ((3 : ℝ) ^ A) ^ 12

lemma taperKw_nonneg (A : ℝ) : 0 ≤ taperKw A := by unfold taperKw; positivity

/-- **The chart facts of `ct:taper-harnack` (c)** about `v(L) = -û(-v'(L))` (`L = log(π²ξ)`), in integral form:
`v > 0` and nondecreasing on `L > 0`, and `L ∂_L log v ≤ A_v`, i.e. `v(L')/v(L) ≤ (L'/L)^{A}` for `0 < L ≤ L'`
(`A ≥ 1`, which is no loss).  These are statements about the Langer chart (the envelope identity `Φ' = τ₀`,
`(4/3)v'^{3/2} = cΦ`, `v/v' = 1 + O(c^{-1/3})`), proved elsewhere or assumed; see `CtDyadicTaperChart`. -/
structure TaperProfile (R A : ℝ) (v : ℝ → ℝ) : Prop where
  R_pos : 0 < R
  one_le_A : 1 ≤ A
  v_pos : ∀ L, 0 < L → 0 < v L
  v_mono : ∀ L L', 0 < L → L ≤ L' → v L ≤ v L'
  v_ratio : ∀ L L', 0 < L → L ≤ L' → v L' ≤ (L' / L) ^ A * v L

/-- The regularity of the taper `wt = w̃(L)` used by the block lemmas (`ct:taper-harnack`):
`0 ≤ wt ≤ 1`, `wt` nondecreasing on `L > 0`, `wt(L') - wt(L) ≤ 24A wt(L')(L'-L)/L'` (the integrated `|w̃'| ≤ 24A_v w̃/L'`)
and `wt(L') ≤ K_w wt(L)` for `L ≤ L' ≤ 3L`. -/
structure TaperReg (wt : ℝ → ℝ) (A Kw : ℝ) : Prop where
  A_nonneg : 0 ≤ A
  Kw_nonneg : 0 ≤ Kw
  mem : ∀ L, 0 ≤ wt L ∧ wt L ≤ 1
  mono : ∀ L L', 0 < L → L ≤ L' → wt L ≤ wt L'
  loglip : ∀ L L', 0 < L → L ≤ L' → wt L' - wt L ≤ 24 * A * wt L' * ((L' - L) / L')
  harnack : ∀ L L', 0 < L → L ≤ L' → L' ≤ 3 * L → wt L' ≤ Kw * wt L

lemma TaperProfile.reg {R A : ℝ} {v : ℝ → ℝ} (h : TaperProfile R A v) :
    TaperReg (fun L => taperW R (v L)) A (taperKw A) where
  A_nonneg := by linarith [h.one_le_A]
  Kw_nonneg := taperKw_nonneg A
  mem := fun L => ⟨taperW_nonneg h.R_pos _, taperW_le_one h.R_pos _⟩
  mono := fun L L' hL hLL => taperW_mono h.R_pos (h.v_mono L L' hL hLL)
  loglip := by
    intro L L' hL hLL
    have hL' : 0 < L' := lt_of_lt_of_le hL hLL
    have hv := h.v_pos L hL
    have hv' := h.v_pos L' hL'
    have h1 := taperW_sub_le h.R_pos hv (h.v_mono L L' hL hLL)
    have ht0 : 0 < L / L' := div_pos hL hL'
    have ht1 : L / L' ≤ 1 := (div_le_one hL').2 hLL
    -- `v/v' ≥ (L/L')^A`
    have h2 : (L / L') ^ A ≤ v L / v L' := by
      have := h.v_ratio L L' hL hLL
      rw [le_div_iff₀ hv']
      have e : (L / L') ^ A * (L' / L) ^ A = 1 := by
        rw [← Real.mul_rpow ht0.le (div_pos hL' hL).le]
        rw [show L / L' * (L' / L) = 1 by field_simp]; simp
      calc (L / L') ^ A * v L' ≤ (L / L') ^ A * ((L' / L) ^ A * v L) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = v L := by rw [← mul_assoc, e, one_mul]
    -- Bernoulli: `1 - t^A ≤ A (1 - t)`
    have h3 : 1 + A * (L / L' - 1) ≤ (L / L') ^ A := by
      have := one_add_mul_self_le_rpow_one_add (show (-1 : ℝ) ≤ L / L' - 1 by linarith) h.one_le_A
      simpa using this
    have h4 : (v L' - v L) / v L' ≤ A * ((L' - L) / L') := by
      have e : (v L' - v L) / v L' = 1 - v L / v L' := by field_simp
      have e2 : A * ((L' - L) / L') = A * (1 - L / L') := by field_simp
      rw [e, e2]; linarith
    have hw0 := taperW_nonneg h.R_pos (v L')
    calc taperW R (v L') - taperW R (v L) ≤ 24 * taperW R (v L') * ((v L' - v L) / v L') := h1
      _ ≤ 24 * taperW R (v L') * (A * ((L' - L) / L')) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 24 * A * taperW R (v L') * ((L' - L) / L') := by ring
  harnack := by
    intro L L' hL hLL h3
    have hv := h.v_pos L hL
    have hρ : 1 ≤ (3 : ℝ) ^ A := Real.one_le_rpow (by norm_num) (by linarith [h.one_le_A])
    have hr : v L' ≤ (3 : ℝ) ^ A * v L := by
      refine (h.v_ratio L L' hL hLL).trans ?_
      apply mul_le_mul_of_nonneg_right _ hv.le
      apply Real.rpow_le_rpow (div_pos (lt_of_lt_of_le hL hLL) hL).le _ (by linarith [h.one_le_A])
      rw [div_le_iff₀ hL]; linarith
    exact taperW_harnack h.R_pos hv (h.v_mono L L' hL hLL) hρ hr

/-! ### Block form on the tent grid -/

section blocks

variable {a : ℝ}

/-- Left end `L_j - 3δ_j` of `Q_j = I_j^{**}` (`tentQ`). -/
noncomputable def tapLeft (a : ℝ) (j : ℕ) : ℝ := tentNode a (j + 1) - 3 * tentDelta a j

/-- `ℓ_j = min(L_j, 1)`. -/
noncomputable def tapEll (a : ℝ) (j : ℕ) : ℝ := min (tentNode a (j + 1)) 1

lemma tapEll_pos (ha : 0 < a) (j : ℕ) : 0 < tapEll a j := lt_min (tentNode_pos ha _) one_pos

lemma tentDelta_eq (a : ℝ) (j : ℕ) : tentDelta a j = tapEll a j / 36 := rfl

lemma tapEll_le (a : ℝ) (j : ℕ) : tapEll a j ≤ tentNode a (j + 1) := min_le_left _ _

lemma tapLeft_ge (a : ℝ) (j : ℕ) : 11 / 12 * tapEll a j ≤ tapLeft a j := by
  unfold tapLeft; rw [tentDelta_eq]; linarith [tapEll_le a j]

lemma mem_tentQ_iff {a : ℝ} {j : ℕ} {L : ℝ} : L ∈ tentQ a j ↔ tapLeft a j ≤ L ∧
    L ≤ tentNode a (j + 1) + 3 * tentDelta a j := Iff.rfl

lemma tentQ_le_three_left (ha : 0 < a) (j : ℕ) {L : ℝ} (hL : L ∈ tentQ a j) : L ≤ 3 * tapLeft a j := by
  have := tapEll_pos ha j
  have h1 := tapEll_le a j
  have h2 := hL.2
  unfold tapLeft; rw [tentDelta_eq] at h2 ⊢; linarith

lemma tentQ_ge (_ha : 0 < a) (j : ℕ) {L : ℝ} (hL : L ∈ tentQ a j) : 11 / 12 * tapEll a j ≤ L :=
  (tapLeft_ge a j).trans hL.1

lemma tentQ_min_le (ha : 0 < a) (j : ℕ) {L : ℝ} (hL : L ∈ tentQ a j) : min L 1 ≤ 13 / 12 * tapEll a j := by
  have h1 := tapEll_le a j
  have h2 := hL.2
  rw [tentDelta_eq] at h2
  have h3 : min L 1 ≤ min (tentNode a (j + 1)) 1 + tapEll a j / 12 := by
    rcases le_total (tentNode a (j + 1)) 1 with h | h
    · rw [min_eq_left h] at *; calc min L 1 ≤ L := min_le_left _ _
        _ ≤ _ := by unfold tapEll at *; rw [min_eq_left h] at *; linarith
    · have := tapEll_pos ha j
      calc min L 1 ≤ 1 := min_le_right _ _
        _ ≤ _ := by unfold tapEll; rw [min_eq_right h]; linarith
  unfold tapEll at *; linarith

lemma mul_le_one_aux {q r : ℝ} (hq : q ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : q * r ≤ 1 :=
  (mul_le_of_le_one_left hr0 hq).trans hr1

/-- On `Q_j` the taper is Lipschitz with constant `(288/11)A K_w wt(L_j - 3δ_j)/ℓ_j`. -/
lemma taperReg_block_lip {wt : ℝ → ℝ} {A Kw : ℝ} (hreg : TaperReg wt A Kw) (ha : 0 < a) (j : ℕ) {L L0 : ℝ}
    (hL : L ∈ tentQ a j) (hL0 : L0 ∈ tentQ a j) :
    |wt L - wt L0| ≤ 288 / 11 * A * Kw * wt (tapLeft a j) / tapEll a j * |L - L0| := by
  have hℓ := tapEll_pos ha j
  have hl0 : 0 < tapLeft a j := lt_of_lt_of_le (by positivity) (tapLeft_ge a j)
  have key : ∀ {L L0 : ℝ}, L ∈ tentQ a j → L0 ∈ tentQ a j → L0 ≤ L →
      wt L - wt L0 ≤ 288 / 11 * A * Kw * wt (tapLeft a j) / tapEll a j * |L - L0| := by
    intro L L0 hL hL0 hle
    have hL0pos : 0 < L0 := lt_of_lt_of_le hl0 hL0.1
    have hLpos : 0 < L := lt_of_lt_of_le hl0 hL.1
    have h1 := hreg.loglip L0 L hL0pos hle
    have h2 : wt L ≤ Kw * wt (tapLeft a j) := hreg.harnack _ L hl0 hL.1 (tentQ_le_three_left ha j hL)
    have h3 : 1 / L ≤ 12 / 11 / tapEll a j := by
      rw [div_le_div_iff₀ hLpos hℓ]; have := tentQ_ge ha j hL; linarith
    have hw0 := (hreg.mem (tapLeft a j)).1
    have hA := hreg.A_nonneg
    have hK := hreg.Kw_nonneg
    have habs : |L - L0| = L - L0 := abs_of_nonneg (by linarith)
    rw [habs]
    have e : (L - L0) / L = (L - L0) * (1 / L) := by ring
    have hd : 0 ≤ L - L0 := by linarith
    calc wt L - wt L0 ≤ 24 * A * wt L * ((L - L0) / L) := h1
      _ ≤ 24 * A * (Kw * wt (tapLeft a j)) * ((L - L0) * (12 / 11 / tapEll a j)) := by
          rw [e]
          apply mul_le_mul (mul_le_mul_of_nonneg_left h2 (by positivity)) _ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 hd
      _ = 288 / 11 * A * Kw * wt (tapLeft a j) / tapEll a j * (L - L0) := by field_simp; ring
  rcases le_total L0 L with h | h
  · have := key hL hL0 h
    have h0 := hreg.mono L0 L (lt_of_lt_of_le hl0 hL0.1) h
    rw [abs_of_nonneg (by linarith)]; exact this
  · have := key hL0 hL h
    have h0 := hreg.mono L L0 (lt_of_lt_of_le hl0 hL.1) h
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm]; exact this

/-- `K₀ = (288/11)A K_w + 108K_w`, the constant of `tapMp`. -/
noncomputable def taperK0 (A : ℝ) : ℝ := 288 / 11 * A * taperKw A + 108 * taperKw A

/-- The Lipschitz constant `M_j'` of `Ω_near χ_j` on `Q_j`: `M_j^σ + K₀ wt(L_j - 3δ_j)/ℓ_j`. -/
noncomputable def tapMp (wt : ℝ → ℝ) (Msig : ℕ → ℝ) (K0 a : ℝ) (j : ℕ) : ℝ :=
  Msig j + K0 * wt (tapLeft a j) / tapEll a j

/-- The supremum bound `S_j = K_w wt(L_j - 3δ_j)` of `Ω_near χ_j` on `Q_j`. -/
noncomputable def tapS (wt : ℝ → ℝ) (Kw a : ℝ) (j : ℕ) : ℝ := Kw * wt (tapLeft a j)

/-- **`hlip` of `boas_freeze_field`** (`ct:Bj-pointwise` (d), `ct:taper-harnack`): the Lipschitz bound of
`ω_j = w̃(1 - 𝔰_far)χ_j` on `Q_j` with constant `M_j' = tapMp`, from the log-Lipschitz bound and Harnack inequality of `w̃`, the
Lipschitz bound `|𝔰_far(L) - 𝔰_far(L')| ≤ M_j^σ|L - L'|` on `Q_j` and `|χ_j'| ≤ 3/δ_j`. -/
theorem taper_hlip {wt sf : ℝ → ℝ} {A : ℝ} {Msig : ℕ → ℝ} (hreg : TaperReg wt A (taperKw A)) (ha : 0 < a)
    (hsf : ∀ L, 0 ≤ sf L ∧ sf L ≤ 1)
    (hσ : ∀ j, ∀ L ∈ tentQ a j, ∀ L0 ∈ tentQ a j, |sf L - sf L0| ≤ Msig j * |L - L0|) :
    ∀ j, ∀ L ∈ tentQ a j, ∀ L0 ∈ tentQ a j,
      |wt L * (1 - sf L) * tent (tentNode a) j L - wt L0 * (1 - sf L0) * tent (tentNode a) j L0| ≤
        tapMp wt Msig (taperK0 A) a j * |L - L0| := by
  intro j L hL L0 hL0
  have hx := tentNode_strictMono ha
  have hℓ := tapEll_pos ha j
  have hl0 : 0 < tapLeft a j := lt_of_lt_of_le (by positivity) (tapLeft_ge a j)
  set Kw := taperKw A with hKw
  have hK := hreg.Kw_nonneg
  have hA := hreg.A_nonneg
  set p := wt L; set p0 := wt L0
  set q := 1 - sf L; set q0 := 1 - sf L0
  set r := tent (tentNode a) j L; set r0 := tent (tentNode a) j L0
  have hp0 : 0 ≤ p0 := (hreg.mem L0).1
  have hp1 : p0 ≤ 1 := (hreg.mem L0).2
  have hq0 : 0 ≤ q ∧ q ≤ 1 := ⟨by linarith [(hsf L).2], by linarith [(hsf L).1]⟩
  have hq00 : 0 ≤ q0 ∧ q0 ≤ 1 := ⟨by linarith [(hsf L0).2], by linarith [(hsf L0).1]⟩
  have hr0 : 0 ≤ r ∧ r ≤ 1 := ⟨tent_nonneg hx j L, tent_le_one _ j L⟩
  have hr00 : 0 ≤ r0 ∧ r0 ≤ 1 := ⟨tent_nonneg hx j L0, tent_le_one _ j L0⟩
  have e : p * q * r - p0 * q0 * r0 = (p - p0) * q * r + p0 * (q - q0) * r + p0 * q0 * (r - r0) := by ring
  have t1 : |(p - p0) * q * r| ≤ 288 / 11 * A * Kw * wt (tapLeft a j) / tapEll a j * |L - L0| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hq0.1, abs_of_nonneg hr0.1]
    refine le_trans ?_ (taperReg_block_lip hreg ha j hL hL0)
    have := mul_le_mul_of_nonneg_left (mul_le_one_aux hq0.2 hr0.1 hr0.2) (abs_nonneg (p - p0))
    nlinarith [this, abs_nonneg (p - p0)]
  have t2 : |p0 * (q - q0) * r| ≤ Msig j * |L - L0| := by
    have hs : |q - q0| = |sf L - sf L0| := by
      rw [show q - q0 = -(sf L - sf L0) by ring, abs_neg]
    rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hr0.1, hs]
    have h := hσ j L hL L0 hL0
    have hM : 0 ≤ Msig j * |L - L0| := (abs_nonneg _).trans h
    have := mul_le_one_aux hp1 hr0.1 hr0.2
    nlinarith [mul_nonneg (abs_nonneg (sf L - sf L0)) hr0.1, mul_nonneg (abs_nonneg (sf L - sf L0)) hp0,
      mul_le_mul_of_nonneg_left (mul_le_one_aux hp1 hr0.1 hr0.2) (abs_nonneg (sf L - sf L0))]
  have t3 : |p0 * q0 * (r - r0)| ≤ 108 * Kw * wt (tapLeft a j) / tapEll a j * |L - L0| := by
    have h1 : p0 ≤ Kw * wt (tapLeft a j) := hreg.harnack _ L0 hl0 hL0.1 (tentQ_le_three_left ha j hL0)
    have h2 := tent_lipschitz_tentNode ha j L L0
    have hδ : 3 / tentDelta a j = 108 / tapEll a j := by rw [tentDelta_eq]; field_simp; norm_num
    rw [hδ] at h2
    rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hq00.1]
    have hpq : p0 * q0 ≤ Kw * wt (tapLeft a j) := by nlinarith [hq00.1, hq00.2]
    have h3 : 0 ≤ p0 * q0 := mul_nonneg hp0 hq00.1
    calc p0 * q0 * |r - r0| ≤ (Kw * wt (tapLeft a j)) * (108 / tapEll a j * |L - L0|) :=
          mul_le_mul hpq h2 (abs_nonneg _) (by have := (hreg.mem (tapLeft a j)).1; positivity)
      _ = 108 * Kw * wt (tapLeft a j) / tapEll a j * |L - L0| := by ring
  rw [e]
  calc _ ≤ |(p - p0) * q * r + p0 * (q - q0) * r| + |p0 * q0 * (r - r0)| := abs_add_le _ _
    _ ≤ |(p - p0) * q * r| + |p0 * (q - q0) * r| + |p0 * q0 * (r - r0)| := by
        gcongr; exact abs_add_le _ _
    _ ≤ _ := by
        unfold tapMp taperK0
        rw [← hKw]
        have : (288 / 11 * A * Kw + 108 * Kw) * wt (tapLeft a j) / tapEll a j =
            288 / 11 * A * Kw * wt (tapLeft a j) / tapEll a j + 108 * Kw * wt (tapLeft a j) / tapEll a j := by ring
        rw [add_mul, this, add_mul]
        linarith [t1, t2, t3]

/-- **`hSup` of `boas_freeze_field`**: `w̃(1 - 𝔰_far)χ_j ≤ S_j = K_w wt(L_j - 3δ_j)` on `Q_j`. -/
theorem taper_hSup {wt sf : ℝ → ℝ} {A : ℝ} (hreg : TaperReg wt A (taperKw A)) (ha : 0 < a)
    (hsf : ∀ L, 0 ≤ sf L ∧ sf L ≤ 1) :
    ∀ j, ∀ L ∈ tentQ a j, wt L * (1 - sf L) * tent (tentNode a) j L ≤ tapS wt (taperKw A) a j := by
  intro j L hL
  have hx := tentNode_strictMono ha
  have hl0 : 0 < tapLeft a j := lt_of_lt_of_le (by have := tapEll_pos ha j; positivity) (tapLeft_ge a j)
  have h1 : wt L ≤ taperKw A * wt (tapLeft a j) := hreg.harnack _ L hl0 hL.1 (tentQ_le_three_left ha j hL)
  have hw0 := (hreg.mem L).1
  have hq : 0 ≤ 1 - sf L ∧ 1 - sf L ≤ 1 := ⟨by linarith [(hsf L).2], by linarith [(hsf L).1]⟩
  have hr : 0 ≤ tent (tentNode a) j L ∧ tent (tentNode a) j L ≤ 1 := ⟨tent_nonneg hx j L, tent_le_one _ j L⟩
  have := mul_le_one_aux hq.2 hr.1 hr.2
  unfold tapS
  calc wt L * (1 - sf L) * tent (tentNode a) j L = wt L * ((1 - sf L) * tent (tentNode a) j L) := by ring
    _ ≤ wt L * 1 := mul_le_mul_of_nonneg_left this hw0
    _ ≤ _ := by linarith

/-- **`hMp_bd` of `boas_pointwise_field`** (`ct:Bj-pointwise` (d)): `M_j' ≤ M_j^σ + K_mp w̃(L)/min(L,1)` for every `L ∈ Q_j`,
`K_mp = (13/12)K₀`. -/
theorem taper_hMp_bd {wt : ℝ → ℝ} {A : ℝ} (hreg : TaperReg wt A (taperKw A)) (ha : 0 < a) (Msig : ℕ → ℝ) :
    ∀ j, ∀ L ∈ tentQ a j,
      tapMp wt Msig (taperK0 A) a j ≤ Msig j + 13 / 12 * taperK0 A * wt L / min L 1 := by
  intro j L hL
  have hℓ := tapEll_pos ha j
  have hl0 : 0 < tapLeft a j := lt_of_lt_of_le (by positivity) (tapLeft_ge a j)
  have hLpos : 0 < L := lt_of_lt_of_le hl0 hL.1
  have hm : 0 < min L 1 := lt_min hLpos one_pos
  have hK0 : 0 ≤ taperK0 A := by
    have := hreg.A_nonneg; have := taperKw_nonneg A; unfold taperK0; positivity
  have h1 : wt (tapLeft a j) ≤ wt L := hreg.mono _ L hl0 hL.1
  have h2 := tentQ_min_le ha j hL
  unfold tapMp
  have : taperK0 A * wt (tapLeft a j) / tapEll a j ≤ 13 / 12 * taperK0 A * wt L / min L 1 := by
    rw [div_le_div_iff₀ hℓ hm]
    have hw0 := (hreg.mem (tapLeft a j)).1
    have := mul_le_mul h1 h2 hm.le (hreg.mem L).1
    nlinarith [mul_nonneg hK0 hw0, mul_le_mul_of_nonneg_left this hK0]
  linarith

/-- **`hS_bd` of `boas_pointwise_field`**: `S_j ≤ K_w w̃(L)` for every `L ∈ Q_j`. -/
theorem taper_hS_bd {wt : ℝ → ℝ} {A : ℝ} (hreg : TaperReg wt A (taperKw A)) (ha : 0 < a) :
    ∀ j, ∀ L ∈ tentQ a j, tapS wt (taperKw A) a j ≤ taperKw A * wt L := by
  intro j L hL
  have hl0 : 0 < tapLeft a j := lt_of_lt_of_le (by have := tapEll_pos ha j; positivity) (tapLeft_ge a j)
  exact mul_le_mul_of_nonneg_left (hreg.mono _ L hl0 hL.1) (taperKw_nonneg A)

lemma tapS_nonneg {wt : ℝ → ℝ} {A : ℝ} (hreg : TaperReg wt A (taperKw A)) (j : ℕ) :
    0 ≤ tapS wt (taperKw A) a j := mul_nonneg (taperKw_nonneg A) (hreg.mem _).1

lemma tapMp_nonneg {wt : ℝ → ℝ} {A : ℝ} (hreg : TaperReg wt A (taperKw A)) (ha : 0 < a) {Msig : ℕ → ℝ}
    (hM : ∀ j, 0 ≤ Msig j) (j : ℕ) : 0 ≤ tapMp wt Msig (taperK0 A) a j := by
  have := hreg.A_nonneg; have := taperKw_nonneg A
  have := tapEll_pos ha j; have := (hreg.mem (tapLeft a j)).1; have := hM j
  unfold tapMp taperK0; positivity

/-- info: 'FormalResearch.SignUncertainty.TaperProfile.reg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms TaperProfile.reg

/-- info: 'FormalResearch.SignUncertainty.taper_hlip' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taper_hlip

/-- info: 'FormalResearch.SignUncertainty.taper_hSup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taper_hSup

/-- info: 'FormalResearch.SignUncertainty.taper_hMp_bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taper_hMp_bd

/-- info: 'FormalResearch.SignUncertainty.taper_hS_bd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms taper_hS_bd

end blocks

end FormalResearch.SignUncertainty

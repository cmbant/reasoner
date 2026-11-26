module

public import Mathlib
public import FormalResearch.SignUncertainty.CtDyadicTaperBuild
public import FormalResearch.SignUncertainty.CtDyadicMoments
public import FormalResearch.SignUncertainty.CtBoasPointwise
public import FormalResearch.SignUncertainty.FctCuspEdgeIbp

/-!
# `ct:Bj-pointwise` (f): the pointwise bounds on `e(L)`, from the `τ₀`-asymptotics

`constant_terms_lower.tex`, proof of `ct:boas` Step 5 (f): `e(L) = w̃(L)[c(1+τ²)W²/τ + W/τ + W/ℓ]` (`boasE c wt`), `τ = τ₀(L)`
(`tau0`, `m(τ₀) = L`), `W = N/(cτ)`, `N² = 10⁶(1+L) log c`, `ℓ = min(L, 1)`.  The two hypotheses of `boas_e_moment_split` (field
`e_moment`):

* **`ctE_small`** (`L ≤ Λ`; `τ₀ ≍ L^{1/2}` via `tau0_small_bounds`, `L ≍ v'/K`, `w̃ ≤ 2(v/R)^{12}`): for `0 < L ≤ Λ` with `v'(L) ≥ 1`,
  `e(L) ≤ α_e · v'(L)`, `α_e = C_e log c/(R² √R)` (`≍ c^{-5/3} log c`), `v'(L) = -ũ(ξ(L))` (`ctVprime`); also with `ctTaperV`
  in place of `v'` (`ctE_small_v`, as `v' ≤ v`);
* **`ctE_large`** (`L > Λ`; `τ₀ ≳ L^{1/2}` for `L ≤ 1`, `τ₀ ≍ e^L` for `L ≥ 1`): for `L ≥ Λ₀`, `0 < Λ₀ ≤ 1`, `w̃(L) ≤ 1`,
  `e(L) ≤ β_e = 2·10⁷ log c/(c Λ₀^{3/2})`, and `Λ₀ ≍ 1` follows from `R ≥ r₁c^{2/3}` (`ctTaperLam_ge`).

**Proved**, unconditional given `TaperBand ε c R` (`taperBand`).
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctCuspEdge

/-- The bracket of `e(L)`: `c(1+τ²)W²/τ + W/τ + W/ℓ`. -/
noncomputable def boasBracket (c L : ℝ) : ℝ :=
  c * (1 + tau0 L ^ 2) / tau0 L * boasWf c L ^ 2 + boasWf c L / tau0 L + boasWf c L / min L 1

lemma boasE_eq (c : ℝ) (wt : ℝ → ℝ) (L : ℝ) : boasE c wt L = wt L * boasBracket c L := rfl

lemma boasBracket_nonneg {c L : ℝ} (hc : 0 < c) (hL : 0 < L) : 0 ≤ boasBracket c L := by
  have hτ := tau0_pos hL
  have hW := boasWf_nonneg hc hL
  unfold boasBracket
  have : 0 < min L 1 := lt_min hL one_pos
  positivity

lemma N_sq {c L : ℝ} (hc : 1 ≤ c) (hL : 0 ≤ L) :
    √(1000000 * (1 + L) * Real.log c) ^ 2 = 1000000 * (1 + L) * Real.log c :=
  Real.sq_sqrt (by have := Real.log_nonneg hc; positivity)

/-- `Y = c L √L`: the small-`L` bracket is `≤ 1.4·10⁷ log c / Y` (`τ₀ ≥ √L`). -/
lemma boasBracket_small {c L : ℝ} (hc : 3 ≤ c) (hL : 0 < L) (hL1 : L ≤ 1) :
    boasBracket c L ≤ 14000000 * Real.log c / (c * (L * √L)) := by
  have hc0 : 0 < c := by linarith
  have hlog1 := one_le_log_of_three_le hc
  obtain ⟨hs, -, hτ2⟩ := tau0_small_bounds hL hL1
  have hτ := tau0_pos hL
  have hsq := tau0_sq_ge hL
  set τ := tau0 L with hτdef
  set s := √L with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.2 hL
  have hs2 : s ^ 2 = L := Real.sq_sqrt hL.le
  have hs1 : s ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hL1
  set N := √(1000000 * (1 + L) * Real.log c) with hNdef
  have hN2 : N ^ 2 = 1000000 * (1 + L) * Real.log c := N_sq (by linarith) hL.le
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN1 : N ≤ N ^ 2 := by
    have h1 : 1 ≤ N ^ 2 := by
      rw [hN2]
      have := mul_le_mul (show (1 : ℝ) ≤ 1 + L by linarith) hlog1 (by norm_num) (by linarith)
      linarith only [this]
    have h2 : 1 ≤ N := by nlinarith only [h1, hN0]
    nlinarith only [h2]
  have hY : 0 < c * (L * s) := by positivity
  set Y := c * (L * s) with hYdef
  have hW : boasWf c L = N / (c * τ) := rfl
  have hLs : L * s ≤ τ * τ := by
    have : L * s ≤ L := by nlinarith only [mul_le_mul_of_nonneg_left hs1 hL.le]
    nlinarith only [this, hsq]
  have hs3 : s * s * s ≤ τ * τ * τ := by
    have h1 : s * s ≤ τ * τ := mul_le_mul hs hs hs0.le hτ.le
    exact mul_le_mul h1 hs hs0.le (by positivity)
  have hLs3 : L * s = s * s * s := by rw [← hs2]; ring
  have hmin : min L 1 = L := min_eq_left hL1
  have T1 : c * (1 + τ ^ 2) / τ * boasWf c L ^ 2 ≤ 5 * N ^ 2 / Y := by
    rw [hW]
    have e1 : c * (1 + τ ^ 2) / τ * (N / (c * τ)) ^ 2 = (1 + τ ^ 2) * N ^ 2 / (c * (τ * τ * τ)) := by
      field_simp
    rw [e1]
    have hτ4 : τ ^ 2 ≤ 4 := by nlinarith only [hτ2, hτ]
    have h1 : (1 + τ ^ 2) * N ^ 2 ≤ 5 * N ^ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hτ4 (sq_nonneg N)]
    calc (1 + τ ^ 2) * N ^ 2 / (c * (τ * τ * τ)) ≤ 5 * N ^ 2 / (c * (τ * τ * τ)) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ 5 * N ^ 2 / Y := by
          apply div_le_div_of_nonneg_left (by positivity) hY
          rw [hYdef, hLs3]
          exact mul_le_mul_of_nonneg_left hs3 hc0.le
  have T2 : boasWf c L / τ ≤ N / Y := by
    rw [hW, div_div]
    apply div_le_div_of_nonneg_left hN0 hY
    calc Y = c * (L * s) := rfl
      _ ≤ c * (τ * τ) := mul_le_mul_of_nonneg_left hLs hc0.le
      _ = c * τ * τ := by ring
  have T3 : boasWf c L / min L 1 ≤ N / Y := by
    rw [hW, hmin, div_div]
    apply div_le_div_of_nonneg_left hN0 hY
    calc Y = c * (L * s) := rfl
      _ ≤ c * τ * L := by nlinarith only [mul_le_mul_of_nonneg_left hs (mul_pos hc0 hL).le]
  have hsum : boasBracket c L ≤ 5 * N ^ 2 / Y + N / Y + N / Y := by
    unfold boasBracket; linarith
  have hNb : N ^ 2 ≤ 2000000 * Real.log c := by
    rw [hN2]
    nlinarith only [mul_le_mul_of_nonneg_right (show 1 + L ≤ 2 by linarith) (show 0 ≤ Real.log c by linarith)]
  calc boasBracket c L ≤ 5 * N ^ 2 / Y + N / Y + N / Y := hsum
    _ = (5 * N ^ 2 + 2 * N) / Y := by ring
    _ ≤ (7 * (2000000 * Real.log c)) / Y := by
        apply div_le_div_of_nonneg_right _ hY.le
        nlinarith only [hN1, hNb]
    _ = 14000000 * Real.log c / (c * (L * √L)) := by ring

/-- `1/Y`-type comparison: `X √X ≤ P · c L √L` when `X ≤ 1.0025 K L` (`K = c^{2/3}κ`, `P² = (1.0025κ)³`). -/
lemma langerScale_cube {c : ℝ} (hc : 0 < c) : langerScale c ^ 3 = langerKappa ^ 3 * c ^ 2 := by
  unfold langerScale
  rw [mul_pow]
  have : (c ^ (2 / 3 : ℝ)) ^ 3 = c ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
  rw [this]; ring

lemma sqrt_mul_le {c L X : ℝ} (hc : 0 < c) (hL : 0 < L) (hX0 : 0 ≤ X) (hX : X ≤ 1.0025 * langerScale c * L) :
    X * √X ≤ √((1.0025 * langerKappa) ^ 3) * (c * (L * √L)) := by
  have hκ := langerKappa_pos
  have hP0 := Real.sqrt_nonneg ((1.0025 * langerKappa) ^ 3)
  have hPsq : √((1.0025 * langerKappa) ^ 3) ^ 2 = (1.0025 * langerKappa) ^ 3 := Real.sq_sqrt (by positivity)
  have hL0 : 0 ≤ L := hL.le
  have hlhs : (X * √X) ^ 2 = X ^ 3 := by rw [mul_pow, Real.sq_sqrt hX0]; ring
  have hrhs : (√((1.0025 * langerKappa) ^ 3) * (c * (L * √L))) ^ 2 =
      (1.0025 * langerKappa) ^ 3 * (c ^ 2 * L ^ 3) := by
    have hsL : √L ^ 2 = L := Real.sq_sqrt hL0
    calc (√((1.0025 * langerKappa) ^ 3) * (c * (L * √L))) ^ 2
        = √((1.0025 * langerKappa) ^ 3) ^ 2 * (c ^ 2 * (L ^ 2 * √L ^ 2)) := by ring
      _ = _ := by rw [hPsq, hsL]; ring
  have hX3 : X ^ 3 ≤ (1.0025 * langerScale c * L) ^ 3 := pow_le_pow_left₀ hX0 hX 3
  have hK3 := langerScale_cube hc
  have h3 : (1.0025 * langerScale c * L) ^ 3 = (1.0025 * langerKappa) ^ 3 * (c ^ 2 * L ^ 3) := by
    have : (1.0025 * langerScale c * L) ^ 3 = 1.0025 ^ 3 * langerScale c ^ 3 * L ^ 3 := by ring
    rw [this, hK3]; ring
  have hsq : (X * √X) ^ 2 ≤ (√((1.0025 * langerKappa) ^ 3) * (c * (L * √L))) ^ 2 := by
    rw [hlhs, hrhs, ← h3]; exact hX3
  exact le_of_sq_le_sq hsq (by positivity)

/-- `(2X/R)^{12}/(X√X) ≤ 4096 X/(R²√R)` for `1 ≤ X ≤ R`. -/
lemma pow_aux {X R : ℝ} (hX : 1 ≤ X) (hXR : X ≤ R) :
    (2 * X / R) ^ 12 / (X * √X) ≤ 4096 * X / (R ^ 2 * √R) := by
  have hX0 : 0 < X := by linarith
  have hR0 : 0 < R := by linarith
  set a := √X with ha
  set t := √R with ht
  have ha0 : 0 < a := Real.sqrt_pos.2 hX0
  have ht0 : 0 < t := Real.sqrt_pos.2 hR0
  have hXa : X = a ^ 2 := (Real.sq_sqrt hX0.le).symm
  have hRt : R = t ^ 2 := (Real.sq_sqrt hR0.le).symm
  have hat : a ≤ t := Real.sqrt_le_sqrt hXR
  have h19 : a ^ 19 ≤ t ^ 19 := pow_le_pow_left₀ ha0.le hat 19
  have hL : (2 * X / R) ^ 12 / (X * a) = 4096 * a ^ 21 / t ^ 24 := by
    rw [hXa, hRt]; field_simp; ring
  have hR : 4096 * X / (R ^ 2 * t) = 4096 * a ^ 2 / t ^ 5 := by
    rw [hXa, hRt]; field_simp
  rw [hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
  have := mul_le_mul_of_nonneg_left h19 (by positivity : 0 ≤ 4096 * a ^ 2 * t ^ 5)
  calc 4096 * a ^ 21 * t ^ 5 = 4096 * a ^ 2 * t ^ 5 * a ^ 19 := by ring
    _ ≤ 4096 * a ^ 2 * t ^ 5 * t ^ 19 := this
    _ = 4096 * a ^ 2 * t ^ 24 := by ring

/-- **`ct:Bj-pointwise` (f), `L ≤ Λ`**: for `0 < L ≤ Λ` with `v'(L) = -ũ(ξ(L)) ≥ 1`,
`e(L) ≤ α_e v'(L)`, `α_e = C_e log c/(R²√R)`, `C_e = 2·10¹¹ P`, `P = ((1.0025κ)³)^{1/2}` (`κ = langerKappa`).  With `R ≍ c^{2/3}`,
`α_e ≍ c^{-5/3} log c`.  (The condition `v' ≥ 1` is the paper's `L ≥ ½L_min`, where `v' ≥ c^{1/2}`.) -/
theorem ctE_small {ε c R : ℝ} (hB : TaperBand ε c R) (hc3 : 3 ≤ c) {L : ℝ} (hL : 0 < L)
    (hLΛ : L ≤ ctTaperLam ε c R) (hX : 1 ≤ ctVprime c L) :
    boasE c (ctTaper ε c R) L ≤
      (200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R)) * ctVprime c L := by
  have hc0 : 0 < c := by linarith
  have hK := langerScale_pos hc0
  have hκ := langerKappa_pos
  have hI := hB.inputs
  have hR := hI.R_pos
  have hlog1 := one_le_log_of_three_le hc3
  have hexpL : Real.exp L - 1 ≤ 5e-4 := by
    have := Real.exp_le_exp.2 hLΛ
    linarith [hB.Lam_le_small]
  have hL1 : L ≤ 1 := by linarith [Real.add_one_le_exp L]
  set X := ctVprime c L with hXdef
  have hXg : X ≤ 1.0025 * langerScale c * L := by
    have hg := (ctChartG_bounds hL.le hexpL).2.1
    have := mul_le_mul_of_nonneg_left hg hK.le
    rw [hXdef]; unfold ctVprime; linarith
  have hXR : X ≤ R := (hB.vp_le_R L hL hLΛ).trans hB.Rprime_le
  have hv : ctTaperV ε c L ≤ 2 * X := by linarith [hB.v_le L hL hLΛ]
  have hvbar_pos := hI.profile.v_pos L hL
  have hvbar : ctTaperVbar ε c R L ≤ 2 * X := by
    unfold ctTaperVbar
    rw [if_pos hLΛ]
    exact (min_le_right _ _).trans hv
  have hwt : ctTaper ε c R L ≤ 2 * (2 * X / R) ^ 12 := by
    refine (ctTaper_le_pow hI hL).trans ?_
    have : (ctTaperVbar ε c R L / R) ^ 12 ≤ (2 * X / R) ^ 12 :=
      pow_le_pow_left₀ (div_nonneg hvbar_pos.le hR.le) (div_le_div_of_nonneg_right hvbar hR.le) 12
    linarith
  have hP := Real.sqrt_pos.2 (show 0 < (1.0025 * langerKappa) ^ 3 by positivity)
  set P := √((1.0025 * langerKappa) ^ 3) with hPdef
  have hXs : 0 < X * √X := by
    have : 0 < X := by linarith
    positivity
  have hY : 0 < c * (L * √L) := by have := Real.sqrt_pos.2 hL; positivity
  have hXY := sqrt_mul_le hc0 hL (by linarith : 0 ≤ X) hXg
  rw [← hPdef] at hXY
  have hbr := boasBracket_small hc3 hL hL1
  have hbr' : boasBracket c L ≤ 14000000 * Real.log c * P / (X * √X) := by
    refine hbr.trans ?_
    rw [div_le_div_iff₀ hY hXs]
    have := mul_le_mul_of_nonneg_left hXY (by positivity : 0 ≤ 14000000 * Real.log c)
    linarith
  have hb0 := boasBracket_nonneg hc0 hL
  have hpa := pow_aux hX hXR
  rw [boasE_eq]
  calc ctTaper ε c R L * boasBracket c L
      ≤ 2 * (2 * X / R) ^ 12 * (14000000 * Real.log c * P / (X * √X)) :=
        mul_le_mul hwt hbr' hb0 (by positivity)
    _ = 28000000 * Real.log c * P * ((2 * X / R) ^ 12 / (X * √X)) := by ring
    _ ≤ 28000000 * Real.log c * P * (4096 * X / (R ^ 2 * √R)) :=
        mul_le_mul_of_nonneg_left hpa (by positivity)
    _ = (114688000000 * P * Real.log c / (R ^ 2 * √R)) * X := by ring
    _ ≤ (200000000000 * P * Real.log c / (R ^ 2 * √R)) * X := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        apply div_le_div_of_nonneg_right _ (by positivity)
        have := mul_pos hP (by linarith : (0 : ℝ) < Real.log c)
        linarith only [this]

/-- `ctE_small` with `v = ctTaperV` in place of `v'` (`v' ≤ v` on `(0, Λ]`). -/
theorem ctE_small_v {ε c R : ℝ} (hB : TaperBand ε c R) (hc3 : 3 ≤ c) {L : ℝ} (hL : 0 < L)
    (hLΛ : L ≤ ctTaperLam ε c R) (hX : 1 ≤ ctVprime c L) :
    boasE c (ctTaper ε c R) L ≤
      (200000000000 * √((1.0025 * langerKappa) ^ 3) * Real.log c / (R ^ 2 * √R)) * ctTaperV ε c L := by
  refine (ctE_small hB hc3 hL hLΛ hX).trans ?_
  have hR := hB.inputs.R_pos
  have hlog1 := one_le_log_of_three_le hc3
  have hP := Real.sqrt_pos.2 (show 0 < (1.0025 * langerKappa) ^ 3 by have := langerKappa_pos; positivity)
  exact mul_le_mul_of_nonneg_left (hB.vp_le_v L hL hLΛ) (by positivity)

/-- **The bracket for `L ≥ Λ₀`** (`τ₀ ≳ L^{1/2}` for `L ≤ 1`, `τ₀ ≳ e^L` for `L ≥ 1`): for `0 < Λ₀ ≤ 1` and `L ≥ Λ₀`,
`c(1+τ²)W²/τ + W/τ + W/ℓ ≤ 7·10⁷ log c/(c Λ₀^{3/2})`. -/
lemma boasBracket_large {c L Λ₀ : ℝ} (hc : 3 ≤ c) (hΛ0 : 0 < Λ₀) (hΛ1 : Λ₀ ≤ 1) (hL : Λ₀ ≤ L) :
    boasBracket c L ≤ 70000000 * Real.log c / (c * (Λ₀ * √Λ₀)) := by
  have hc0 : 0 < c := by linarith
  have hlog1 := one_le_log_of_three_le hc
  have hL0 : 0 < L := lt_of_lt_of_le hΛ0 hL
  set q := √Λ₀ with hqdef
  have hq0 : 0 < q := Real.sqrt_pos.2 hΛ0
  have hq2 : q ^ 2 = Λ₀ := Real.sq_sqrt hΛ0.le
  have hq1 : q ≤ 1 := by rw [hqdef, Real.sqrt_le_one]; exact hΛ1
  have hτ := tau0_pos hL0
  set τ := tau0 L with hτdef
  have hA : (1 + L) * q ≤ 4 * τ := by
    rcases le_total L 1 with h1 | h1
    · obtain ⟨hs, -, -⟩ := tau0_small_bounds hL0 h1
      have hqL : q ≤ √L := Real.sqrt_le_sqrt hL
      nlinarith
    · obtain ⟨hlo, -⟩ := tau0_large_bounds h1
      have h2 : 1 + L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
      have h3 : Real.exp L ≤ π * τ := by rwa [div_le_iff₀ Real.pi_pos, mul_comm] at hlo
      nlinarith [Real.pi_lt_d2]
  have hq4 : q ≤ 4 * τ := by nlinarith
  have hq2' : q ^ 2 ≤ 4 * τ := by nlinarith
  have hq16 : q ^ 2 ≤ 16 * τ ^ 2 := by nlinarith
  have hmin : Λ₀ ≤ min L 1 := le_min hL hΛ1
  have hℓ : 0 < min L 1 := lt_min hL0 one_pos
  set N := √(1000000 * (1 + L) * Real.log c) with hNdef
  have hN2 : N ^ 2 = 1000000 * (1 + L) * Real.log c := N_sq (by linarith) hL0.le
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hN3 : N ≤ 1000 * (1 + L) * Real.log c := by
    have h1 : N ^ 2 ≤ (1000 * (1 + L) * Real.log c) ^ 2 := by
      rw [hN2]
      have hp : 1 ≤ (1 + L) * Real.log c := by nlinarith
      have hq : 0 ≤ (1 + L) * Real.log c * ((1 + L) * Real.log c - 1) :=
        mul_nonneg (by positivity) (by linarith)
      nlinarith [hq]
    exact le_of_sq_le_sq h1 (by positivity)
  have hW : boasWf c L = N / (c * τ) := rfl
  have hY : 0 < c * (Λ₀ * q) := by positivity
  have hY' : c * (Λ₀ * q) = c * q ^ 3 := by rw [← hq2]; ring
  have T1 : c * (1 + τ ^ 2) / τ * boasWf c L ^ 2 ≤ 68000000 * Real.log c / (c * q ^ 3) := by
    rw [hW]
    have e1 : c * (1 + τ ^ 2) / τ * (N / (c * τ)) ^ 2 = (1 + τ ^ 2) * N ^ 2 / (c * τ ^ 3) := by
      field_simp
    rw [e1, div_le_div_iff₀ (by positivity) (by positivity), hN2]
    have hq21 : q ^ 2 ≤ 1 := by nlinarith only [hq0, hq1]
    have h17 : (1 + τ ^ 2) * q ^ 2 ≤ 17 * τ ^ 2 := by
      linarith only [hq16, mul_le_mul_of_nonneg_left hq21 (sq_nonneg τ)]
    have h68 : (1 + τ ^ 2) * q ^ 2 * ((1 + L) * q) ≤ 17 * τ ^ 2 * (4 * τ) :=
      mul_le_mul h17 hA (by positivity) (by positivity)
    have hl0 : 0 ≤ 1000000 * Real.log c * c := by positivity
    linarith only [mul_le_mul_of_nonneg_left h68 hl0]
  have T2 : boasWf c L / τ ≤ 16000 * Real.log c / (c * q ^ 3) := by
    rw [hW, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : N * q ^ 3 ≤ 16000 * Real.log c * (τ * τ) := by
      have : N * q ^ 3 ≤ 1000 * (1 + L) * Real.log c * q ^ 3 := mul_le_mul_of_nonneg_right hN3 (by positivity)
      have h2 : (1 + L) * q * q ^ 2 ≤ 4 * τ * (4 * τ) :=
        mul_le_mul hA hq2' (by positivity) (by positivity)
      linarith only [this, mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1000 * Real.log c)]
    linarith only [mul_le_mul_of_nonneg_left h1 hc0.le]
  have T3 : boasWf c L / min L 1 ≤ 4000 * Real.log c / (c * q ^ 3) := by
    rw [hW, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : N * q ^ 3 ≤ 4000 * Real.log c * (τ * min L 1) := by
      have : N * q ^ 3 ≤ 1000 * (1 + L) * Real.log c * q ^ 3 := mul_le_mul_of_nonneg_right hN3 (by positivity)
      have h2 : (1 + L) * q * q ^ 2 ≤ 4 * τ * min L 1 :=
        mul_le_mul hA (by rw [hq2]; exact hmin) (by positivity) (by positivity)
      linarith only [this, mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 1000 * Real.log c)]
    linarith only [mul_le_mul_of_nonneg_left h1 hc0.le]
  have hsum : boasBracket c L ≤ (68000000 + 16000 + 4000) * Real.log c / (c * q ^ 3) := by
    unfold boasBracket
    have : (68000000 + 16000 + 4000) * Real.log c / (c * q ^ 3) =
        68000000 * Real.log c / (c * q ^ 3) + 16000 * Real.log c / (c * q ^ 3) +
          4000 * Real.log c / (c * q ^ 3) := by ring
    rw [this]; linarith
  refine hsum.trans ?_
  rw [← hY']
  rw [show c * (Λ₀ * √Λ₀) = c * (Λ₀ * q) from rfl, hY']
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith

/-- `w̃ = 1` for `L > Λ`. -/
lemma ctTaper_eq_one_of_gt {ε c R A : ℝ} (I : TaperChartInputs ε c R A) {L : ℝ} (hL : ctTaperLam ε c R < L) :
    ctTaper ε c R L = 1 := by
  unfold ctTaper
  rw [if_neg (not_le.2 (I.Lam_pos.trans hL)), if_neg (not_le.2 hL)]
  exact taperW_of_ge I.R_pos le_rfl

/-- **`ct:Bj-pointwise` (f), `L > Λ`**: for `0 < Λ₀ ≤ Λ` (`Λ₀ ≤ 1` automatic as `Λ ≤ 5·10⁻⁴`) and `L > Λ`,
`e(L) ≤ β_e = 7·10⁷ log c/(c Λ₀^{3/2})` (`w̃ = 1`; `e = O(log c/c)` with `Λ₀ ≍ 1`, `ctTaperLam_ge`). -/
theorem ctE_large {ε c R : ℝ} (hB : TaperBand ε c R) (hc3 : 3 ≤ c) {Λ₀ : ℝ} (hΛ0 : 0 < Λ₀)
    (hΛ : Λ₀ ≤ ctTaperLam ε c R) {L : ℝ} (hL : ctTaperLam ε c R < L) :
    boasE c (ctTaper ε c R) L ≤ 70000000 * Real.log c / (c * (Λ₀ * √Λ₀)) := by
  have hΛ1 : Λ₀ ≤ 1 := by
    have := hB.Lam_le_small
    linarith [Real.add_one_le_exp (ctTaperLam ε c R)]
  rw [boasE_eq, ctTaper_eq_one_of_gt hB.inputs hL, one_mul]
  exact boasBracket_large hc3 hΛ0 hΛ1 (hΛ.trans hL.le)

/-- **`Λ ≍ 1`** (`ct:Bj-pointwise` notation): `r₁ c^{2/3} ≤ R` and `1 ≤ R` give `Λ ≥ r₁/(2.01 κ)`
(`R' ≥ R - 1/2 ≥ R/2`, `R' ≤ 1.0025 K Λ`, `K = c^{2/3}κ`). -/
theorem ctTaperLam_ge {ε c R : ℝ} (hB : TaperBand ε c R) (hc : 0 < c) (hR1 : 1 ≤ R) {r₁ : ℝ}
    (hR : r₁ * c ^ (2 / 3 : ℝ) ≤ R) : r₁ / (2.01 * langerKappa) ≤ ctTaperLam ε c R := by
  have hκ := langerKappa_pos
  have hc23 : 0 < c ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have h1 := hB.Rprime_le_Lam
  have h2 := hB.Rprime_ge
  have hK : langerScale c = c ^ (2 / 3 : ℝ) * langerKappa := rfl
  rw [div_le_iff₀ (by positivity)]
  have h3 : r₁ * c ^ (2 / 3 : ℝ) ≤ ctTaperLam ε c R * (2.01 * langerKappa) * c ^ (2 / 3 : ℝ) := by
    have hΛ0 : 0 ≤ ctTaperLam ε c R := hB.inputs.Lam_pos.le
    have : 2.005 * langerKappa * c ^ (2 / 3 : ℝ) * ctTaperLam ε c R ≥ R := by
      rw [hK] at h1
      nlinarith only [h1, h2, hR1]
    nlinarith only [this, hR, mul_nonneg (mul_nonneg hκ.le hc23.le) hΛ0]
  exact le_of_mul_le_mul_right h3 hc23

/-- info: 'FormalResearch.SignUncertainty.ctE_small' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctE_small

/-- info: 'FormalResearch.SignUncertainty.ctE_small_v' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctE_small_v

/-- info: 'FormalResearch.SignUncertainty.ctE_large' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctE_large

/-- info: 'FormalResearch.SignUncertainty.ctTaperLam_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ctTaperLam_ge

end FormalResearch.SignUncertainty

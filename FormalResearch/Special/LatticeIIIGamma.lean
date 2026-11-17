module

public import FormalResearch.Special.LatticeIII

/-!
# `lem:latticesum` (iii) for the Gamma phase

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `lem:latticesum` (iii).  Same setting as
`latticesum_gamma` (`LatticeMain`): `ϰ = nc ≥ 1`, `b > 0`, `c_* < ½`, `L^{c_*/2} ≤ X ≤ L^{c_*}`,
`F_- ≤ F_i ≤ F_+`, `G = θ₀ + sℓ_Σ - ϰ arg Γ(½+is)` (`gammaG`), `Θ` continuous strictly increasing on `[-X,X]`
with `|Θ - G| ≤ L^{-b}`, `S = {x ∈ [-X,X] : Θ(x) ∈ πℤ}`, `t₀ = Θ(0)/π`.  With `b₁ < b`, `b₁ < ϰ/4`:

* if `{t₀} ≠ 0`: `|∑_{x∈S}[ν(2πx) - 1_{x<0}] - ({t₀} - ½)| ≤ C L^{-b₁}`;
* in all cases `∃ m ∈ ℤ, |∑_{x∈S}[ν(2πx) - 1_{x<0}] - t₀ + ½ - m| ≤ C L^{-b₁}`,

`C, L₀` depending only on `nc, b, c_*, F_±, b₁`.  (The paper's hypothesis `b₁ < ϰ min(δ, ¼)` has `δ` playing no
role in (iii); only `b₁ < ϰ/4` is used.)  The case `t₀ ∈ ℤ` is proved directly (by `LatticeIII`'s exact
identity), not by the paper's limit `ε ↓ 0`.

Not formalised: the identification of `argGammaHalf` with the polar argument of `Γ(½+is)`.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

/-- Collecting the error of `latticeI_bound` for `φ = w` with `M = 4m`, `m ≥ 1`, `ε ≤ 1`. -/
theorem explicit_I_le (κ r y1 K : ℝ) (hκ : 0 < κ) (hr : 0 < r) (hy1 : 0 < y1) (hK : 0 ≤ K) :
    ∃ A1 A2 A3 : ℝ, 0 ≤ A1 ∧ 0 ≤ A2 ∧ 0 ≤ A3 ∧ ∀ (Cφ ε X m : ℝ), 0 ≤ Cφ → 0 ≤ ε → ε ≤ 1 → 1 ≤ m →
      Cφ * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) +
        (Cφ * Real.exp (-κ * X) / m +
          1 / 12 * (2 * smoothCw Cφ κ r m K * y1 * Real.exp (-κ * X) +
            2 * smoothCw Cφ κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1)))) ≤
      Cφ * (A1 * Real.exp (-κ * X) + A2 * ε + A3 * Real.exp (-(2 * Real.pi * m * y1))) := by
  set c1 : ℝ := Real.exp (κ * r) / r + K with hc1
  have hc1p : 0 ≤ c1 := by positivity
  have hwc : 0 ≤ wconst κ := by
    unfold wconst
    have : Real.exp (-κ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have : 0 < 1 - Real.exp (-κ) := by linarith
    positivity
  refine ⟨1 + c1 * y1 / 6, 29 * wconst κ, c1 / (6 * κ), by positivity, by positivity, by positivity, ?_⟩
  intro Cφ ε X m hCφ hε hε1 hm
  have hm0 : 0 < m := by linarith
  have eX := (Real.exp_pos (-κ * X)).le
  have eY := (Real.exp_pos (-(2 * Real.pi * m * y1))).le
  have hCw : smoothCw Cφ κ r m K ≤ Cφ * c1 := by
    unfold smoothCw
    have h2 : Real.exp (κ * r) / (r * m) ≤ Real.exp (κ * r) / r := by
      rw [div_le_div_iff₀ (by positivity) hr]
      nlinarith [mul_nonneg (Real.exp_pos (κ * r)).le (mul_nonneg hr.le (sub_nonneg.mpr hm))]
    have h3 : K / m ^ 2 ≤ K := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hK (sq_nonneg (m - 1)), mul_nonneg hK (sub_nonneg.mpr hm)]
    have : Cφ * (Real.exp (κ * r) / (r * m) + K / m ^ 2) ≤ Cφ * (Real.exp (κ * r) / r + K) :=
      mul_le_mul_of_nonneg_left (by linarith) hCφ
    exact this
  have hfac : 1 + 4 * (4 * m + 2 * ε + 1) / m ≤ 29 := by
    rw [show 1 + 4 * (4 * m + 2 * ε + 1) / m = 17 + (8 * ε + 4) / m by field_simp; ring]
    have : (8 * ε + 4) / m ≤ 12 := by
      rw [div_le_iff₀ hm0]; nlinarith
    linarith
  have t3 : Cφ * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) ≤ Cφ * (29 * wconst κ * ε) := by
    have : 0 ≤ Cφ * wconst κ * ε := by positivity
    nlinarith
  have t4 : Cφ * Real.exp (-κ * X) / m ≤ Cφ * Real.exp (-κ * X) := by
    rw [div_le_iff₀ hm0]
    have : 0 ≤ Cφ * Real.exp (-κ * X) := by positivity
    nlinarith
  have a1 : smoothCw Cφ κ r m K * y1 * Real.exp (-κ * X) ≤ Cφ * c1 * y1 * Real.exp (-κ * X) := by
    have := mul_le_mul_of_nonneg_right hCw (mul_nonneg hy1.le eX)
    nlinarith
  have a2 : smoothCw Cφ κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1)) ≤
      Cφ * c1 / κ * Real.exp (-(2 * Real.pi * m * y1)) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hCw hκ.le) eY
  have e1 : 2 * smoothCw Cφ κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1)) =
      2 * (smoothCw Cφ κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1))) := by ring
  have e2 : Cφ * (c1 * y1 / 6 * Real.exp (-κ * X) + c1 / (6 * κ) * Real.exp (-(2 * Real.pi * m * y1))) =
      1 / 12 * (2 * (Cφ * c1 * y1 * Real.exp (-κ * X)) +
        2 * (Cφ * c1 / κ * Real.exp (-(2 * Real.pi * m * y1)))) := by
    field_simp; ring
  have t5 : 1 / 12 * (2 * smoothCw Cφ κ r m K * y1 * Real.exp (-κ * X) +
      2 * smoothCw Cφ κ r m K / κ * Real.exp (-(2 * Real.pi * m * y1))) ≤
      Cφ * (c1 * y1 / 6 * Real.exp (-κ * X) + c1 / (6 * κ) * Real.exp (-(2 * Real.pi * m * y1))) := by
    rw [e1, e2]
    linarith [a1, a2]
  calc _ ≤ Cφ * (29 * wconst κ * ε) + (Cφ * Real.exp (-κ * X) +
        Cφ * (c1 * y1 / 6 * Real.exp (-κ * X) + c1 / (6 * κ) * Real.exp (-(2 * Real.pi * m * y1)))) := by
        linarith
    _ = _ := by ring

lemma gamma_odd (nc : ℕ) (ℓ θ0 : ℝ) (s : ℝ) :
    realPhase (gammaPhase nc ℓ θ0) (-s) - realPhase (gammaPhase nc ℓ θ0) 0 =
      -(realPhase (gammaPhase nc ℓ θ0) s - realPhase (gammaPhase nc ℓ θ0) 0) := by
  have h0 : argGammaHalf ((0 : ℝ) : ℂ) = 0 := by
    have := argGammaHalf_neg (0 : ℂ)
    simp only [neg_zero] at this
    have h2 : argGammaHalf 0 = 0 := by linear_combination (1 / 2 : ℂ) * this
    simpa using h2
  have hn : (argGammaHalf (((-s : ℝ)) : ℂ)).re = -(argGammaHalf (s : ℂ)).re := by
    have := argGammaHalf_neg (s : ℂ)
    rw [show (((-s : ℝ)) : ℂ) = -(s : ℂ) by push_cast; ring, this]
    simp
  simp only [realPhase_gamma, gammaG, h0, hn, Complex.zero_re]
  ring

/-- `explicit` collection of the error of `latticeIII_bound` in the Gamma setting. -/
theorem error_asymp_III (nc : ℕ) {cs b b1 y1 A1 A2 A3 : ℝ} (hcs0 : 0 < cs) (hb : 0 < b)
    (hb1b : b1 ≤ b) (hy : b1 ≤ nc * y1) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 < L → ∀ X : ℝ, L ^ (cs / 2) ≤ X →
      2 * (L ^ (-b) / Real.pi) +
        (4 * Real.pi) * (A1 * Real.exp (-(2 * Real.pi) * X) + A2 * (L ^ (-b) / Real.pi) +
          A3 * Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1))) +
        nuR (2 * Real.pi * X) * (4 * (nc * Real.log L / (2 * Real.pi)) * (2 * X) +
          2 * (L ^ (-b) / Real.pi) + 2) ≤ C * L ^ (-b1) := by
  obtain ⟨C1, hC1, hE⟩ := exp_neg_rpow_le (a := Real.pi) (c := cs / 2) (p := b1 + 1) Real.pi_pos
    (by positivity)
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  refine ⟨2 + 4 * Real.pi * (A1 * C1 + A2 + A3) + 8 * nc * C1 + 3 * C1 + 1, by positivity, ?_⟩
  intro L hL X hX
  have hL0 : 0 < L := by linarith
  have hlogL0 : 0 < Real.log L := Real.log_pos hL
  have hncr : (0 : ℝ) ≤ nc := Nat.cast_nonneg _
  set P : ℝ := L ^ (-b1) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 _
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hX
  have hEX : Real.exp (-(Real.pi * X)) ≤ C1 * (P / L) := by
    have h1 : Real.exp (-(Real.pi * X)) ≤ Real.exp (-(Real.pi * L ^ (cs / 2))) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left hX hpi.le
      linarith
    have h2 := hE L hL.le
    have h3 : L ^ (-(b1 + 1)) = P / L := by
      rw [show -(b1 + 1) = -b1 - 1 by ring, Real.rpow_sub_one hL0.ne']
    rw [h3] at h2
    exact h1.trans h2
  have hPL : P / L ≤ P := div_le_self hP0.le hL.le
  have hEX' : Real.exp (-(Real.pi * X)) ≤ C1 * P := hEX.trans (mul_le_mul_of_nonneg_left hPL hC1.le)
  have e1 : Real.exp (-(2 * Real.pi) * X) ≤ Real.exp (-(Real.pi * X)) :=
    Real.exp_le_exp.2 (by have := mul_pos hpi hXpos; linarith)
  have hexp0 := (Real.exp_pos (-(2 * Real.pi) * X)).le
  have e2 : X * Real.exp (-(2 * Real.pi) * X) ≤ Real.exp (-(Real.pi * X)) := by
    have h1 : X ≤ Real.exp (Real.pi * X) := by
      have := Real.add_one_le_exp (Real.pi * X)
      have := mul_pos (by linarith : 0 < Real.pi - 1) hXpos
      nlinarith
    have h2 : Real.exp (Real.pi * X) * Real.exp (-(2 * Real.pi) * X) = Real.exp (-(Real.pi * X)) := by
      rw [← Real.exp_add]; congr 1; ring
    calc X * Real.exp (-(2 * Real.pi) * X) ≤ Real.exp (Real.pi * X) * Real.exp (-(2 * Real.pi) * X) :=
          mul_le_mul_of_nonneg_right h1 hexp0
      _ = _ := h2
  have hε0 : 0 ≤ L ^ (-b) / Real.pi := by positivity
  have hLb1 : L ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL.le (by linarith)
  have hε1 : L ^ (-b) / Real.pi ≤ 1 / 3 := by
    rw [div_le_iff₀ hpi]; linarith
  have hεP : L ^ (-b) / Real.pi ≤ P := by
    calc L ^ (-b) / Real.pi ≤ L ^ (-b) := div_le_self (Real.rpow_pos_of_pos hL0 _).le (by linarith)
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have hexpP : Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1)) ≤ P := by
    have e : Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1)) = L ^ (-(nc * y1)) := by
      rw [Real.rpow_def_of_pos hL0]; congr 1; field_simp
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hν : nuR (2 * Real.pi * X) ≤ Real.exp (-(2 * Real.pi) * X) := by
    refine (nuR_le_exp _).trans (le_of_eq ?_); congr 1; ring
  have hν0 : 0 ≤ nuR (2 * Real.pi * X) := (nuR_mem _).1
  set ε : ℝ := L ^ (-b) / Real.pi with hε
  set m : ℝ := nc * Real.log L / (2 * Real.pi) with hm
  have hm0 : 0 ≤ m := by positivity
  have hmL : m ≤ nc * L := by
    rw [hm, div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hlogL hncr
    have := mul_nonneg (mul_nonneg hncr hL0.le) (by linarith : 0 ≤ 2 * Real.pi - 1)
    linarith
  -- the tail term
  have hT : nuR (2 * Real.pi * X) * (4 * m * (2 * X) + 2 * ε + 2) ≤ (8 * nc * C1 + 3 * C1) * P := by
    have h1 : nuR (2 * Real.pi * X) * (4 * m * (2 * X)) ≤ 8 * m * Real.exp (-(Real.pi * X)) := by
      have : nuR (2 * Real.pi * X) * (4 * m * (2 * X)) ≤ Real.exp (-(2 * Real.pi) * X) * (8 * m * X) := by
        have := mul_le_mul_of_nonneg_right hν (by positivity : 0 ≤ 4 * m * (2 * X))
        calc _ ≤ _ := this
          _ = _ := by ring
      have h2 : Real.exp (-(2 * Real.pi) * X) * (8 * m * X) = 8 * m * (X * Real.exp (-(2 * Real.pi) * X)) := by
        ring
      rw [h2] at this
      exact this.trans (mul_le_mul_of_nonneg_left e2 (by positivity))
    have h3 : 8 * m * Real.exp (-(Real.pi * X)) ≤ 8 * nc * (C1 * P) := by
      have : 8 * m * Real.exp (-(Real.pi * X)) ≤ 8 * m * (C1 * (P / L)) :=
        mul_le_mul_of_nonneg_left hEX (by positivity)
      have h4 : 8 * m * (C1 * (P / L)) ≤ 8 * (nc * L) * (C1 * (P / L)) :=
        mul_le_mul_of_nonneg_right (by linarith [hmL]) (by positivity)
      have h5 : 8 * (nc * L) * (C1 * (P / L)) = 8 * nc * (C1 * P) := by field_simp
      linarith
    have h6 : nuR (2 * Real.pi * X) * (2 * ε + 2) ≤ 3 * (C1 * P) := by
      have : nuR (2 * Real.pi * X) * (2 * ε + 2) ≤ Real.exp (-(Real.pi * X)) * 3 :=
        mul_le_mul (hν.trans e1) (by linarith) (by positivity) (by positivity)
      calc _ ≤ _ := this
        _ ≤ C1 * P * 3 := by linarith [hEX']
        _ = _ := by ring
    have hsplit : nuR (2 * Real.pi * X) * (4 * m * (2 * X) + 2 * ε + 2) =
        nuR (2 * Real.pi * X) * (4 * m * (2 * X)) + nuR (2 * Real.pi * X) * (2 * ε + 2) := by ring
    rw [hsplit]
    linarith
  have hA : 4 * Real.pi * (A1 * Real.exp (-(2 * Real.pi) * X) + A2 * ε +
      A3 * Real.exp (-(2 * Real.pi * m * y1))) ≤ 4 * Real.pi * (A1 * (C1 * P) + A2 * P + A3 * P) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have a1 : A1 * Real.exp (-(2 * Real.pi) * X) ≤ A1 * (C1 * P) :=
      mul_le_mul_of_nonneg_left (e1.trans hEX') hA1
    have a2 : A2 * ε ≤ A2 * P := mul_le_mul_of_nonneg_left hεP hA2
    have a3 : A3 * Real.exp (-(2 * Real.pi * m * y1)) ≤ A3 * P :=
      mul_le_mul_of_nonneg_left hexpP hA3
    linarith
  have hC : (2 + 4 * Real.pi * (A1 * C1 + A2 + A3) + 8 * nc * C1 + 3 * C1 + 1) * P =
      2 * P + 4 * Real.pi * (A1 * (C1 * P) + A2 * P + A3 * P) + (8 * nc * C1 + 3 * C1) * P + P := by ring
  linarith [hT, hA, hεP]

end FormalResearch.Special.Lattice

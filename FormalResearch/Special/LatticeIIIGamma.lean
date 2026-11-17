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

/-- **`lem:latticesum` (iii) for the Gamma phase** (paper form), `t₀ = Θ(0)/π`.  Constants `C, L₀` depend only on
`nc, b, c_*, b₁, F_±`.  `Sν = ∑_{x∈S} [ν(2πx) - 1_{x<0}]` with `ν(e) = (1+e^e)⁻¹` (`nuR`). -/
theorem latticesum_gamma_iii (nc : ℕ) (hnc : 1 ≤ nc) {b cs b1 Fm Fp : ℝ}
    (hb : 0 < b) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hb1 : 0 < b1)
    (hb1b : b1 < b) (hb1δ : b1 < nc * (1 / 4)) (hFm : 0 < Fm) :
    ∃ C L0 : ℝ, 0 < C ∧ 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ F : Fin nc → ℝ, (∀ i, Fm ≤ F i ∧ F i ≤ Fp) →
      ∀ (X θ0 : ℝ), L ^ (cs / 2) ≤ X → X ≤ L ^ cs →
      ∀ Θ : ℝ → ℝ, ContinuousOn Θ (Icc (-X) X) → StrictMonoOn Θ (Icc (-X) X) →
      (∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) →
      ∀ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) →
      (Int.fract (Θ 0 / Real.pi) ≠ 0 →
        |(∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0)) -
          (Int.fract (Θ 0 / Real.pi) - 1 / 2)| ≤ C * L ^ (-b1)) ∧
      ∃ m : ℤ, |(∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0)) -
          Θ 0 / Real.pi + 1 / 2 - m| ≤ C * L ^ (-b1) := by
  have hncpos : (0 : ℝ) < nc := by exact_mod_cast hnc
  have hpi := Real.pi_pos
  set y1 : ℝ := (b1 / nc + 1 / 4) / 2 with hy1d
  have hbY : b1 / nc < 1 / 4 := by rw [div_lt_iff₀ hncpos]; linarith
  have hy1 : 0 < y1 := by positivity
  have hy1Y : y1 < 1 / 4 := by rw [hy1d]; linarith
  set r : ℝ := 1 / 4 - y1 with hrd
  have hr : 0 < r := by rw [hrd]; linarith
  have hyr : y1 + r ≤ 1 / 4 := by rw [hrd]; linarith
  have hnc_y : b1 ≤ nc * y1 := by
    have : (nc : ℝ) * (b1 / nc) = b1 := by field_simp
    have h2 : (nc : ℝ) * y1 = (b1 + nc * (1 / 4)) / 2 := by rw [hy1d]; field_simp
    rw [h2]; linarith
  have hK : 0 ≤ (nc : ℝ) * (16 * invSqSum) / Real.pi := by
    have := invSqSum_nonneg; positivity
  obtain ⟨A1, A2, A3, hA1, hA2, hA3, hA⟩ :=
    explicit_I_le (2 * Real.pi) r y1 ((nc : ℝ) * (16 * invSqSum) / Real.pi) (by positivity) hr hy1 hK
  obtain ⟨C, hC, hCb⟩ := error_asymp_III nc (cs := cs) (b := b) (b1 := b1) (y1 := y1) (A1 := A1)
    (A2 := A2) (A3 := A3) hcs0 hb hb1b.le hnc_y hA1 hA2 hA3
  set Λ : ℝ := max (max (2 * Real.pi) ((Real.log 3 + 5 - Real.log Fm) / (1 / 2 - cs)))
    (max (Real.log Fp + 3) (-Real.log Fm)) with hΛ
  refine ⟨C, Real.exp Λ + 1, hC, by linarith [Real.exp_pos Λ], ?_⟩
  intro L hLL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS
  have hL1 : 1 < L := by linarith [Real.exp_pos Λ]
  have hL0 : 0 < L := by linarith
  have hlogL : Λ ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 (by linarith)
  have hΛ1 : 2 * Real.pi ≤ Real.log L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlogL
  have hΛ2 : (Real.log 3 + 5 - Real.log Fm) / (1 / 2 - cs) ≤ Real.log L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlogL
  have hΛ3 : Real.log Fp + 3 ≤ Real.log L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogL
  have hm1 : 2 * Real.pi ≤ nc * Real.log L := by
    have hlp : 0 ≤ Real.log L := by linarith [Real.pi_pos]
    have : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
    nlinarith
  have h1 : Real.log 3 + 5 - Real.log Fm ≤ (1 / 2 - cs) * Real.log L := by
    have := (div_le_iff₀ (by linarith : 0 < 1 / 2 - cs)).1 hΛ2
    linarith
  set ℓ := lsum nc L F with hℓ
  set m : ℝ := nc * Real.log L / (2 * Real.pi) with hm
  have hm1' : 1 ≤ m := by rw [hm, le_div_iff₀ (by positivity)]; linarith
  set ε : ℝ := L ^ (-b) / Real.pi with hε
  have hε0 : 0 ≤ ε := by positivity
  have hLb1 : L ^ (-b) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1.le (by linarith)
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_iff₀ hpi]; nlinarith [Real.pi_gt_three]
  have hCal := gamma_calPhase nc hnc hL1 hFm F hF hcs0 hcs hX hXu h1 hΛ3 (θ0 := θ0)
  obtain ⟨t', hd, ht'⟩ := exists_levelData hCal (continuous_realPhase_gamma nc ℓ θ0)
    (t := fun s => Θ s / Real.pi) (ε := ε)
    (hΘc.div_const _) (fun x hx y hy hxy => div_lt_div_of_pos_right (hΘm hx hy hxy) hpi) hε0
    (fun s hs => by
      rw [realPhase_gamma, ← sub_div, abs_div, abs_of_pos hpi]
      exact div_le_div_of_nonneg_right (hΘG s hs) hpi.le) (S := S)
    (fun x => by
      rw [hS x]
      refine and_congr_right (fun _ => exists_congr (fun n => ?_))
      rw [div_eq_iff hpi.ne'])
  have hb0 := latticeIII_bound hd (y1 := y1) (r := r) hy1 hr hyr le_rfl (gamma_odd nc ℓ θ0)
  have h0 : t' 0 = Θ 0 / Real.pi := ht' 0 ⟨by linarith [hd.cal.hX], hd.cal.hX.le⟩
  rw [h0, ← hm] at hb0
  have hI := hA (4 * Real.pi) ε X m (by positivity) hε0 hε1 hm1'
  have hE := hCb L hL1 X hX
  rw [← hε, ← hm] at hE
  set Sν := ∑ x ∈ S, (nuR (2 * Real.pi * x) - if x < 0 then (1 : ℝ) else 0) with hSν
  have hfin : |Sν - ((Int.fract (Θ 0 / Real.pi) - 1 / 2) +
      if Int.fract (Θ 0 / Real.pi) = 0 then 1 else 0)| ≤ C * L ^ (-b1) := by
    refine hb0.trans ?_
    refine le_trans ?_ hE
    linarith
  exact offset_of_bound hfin

/-- info: 'FormalResearch.Special.Lattice.latticesum_gamma_iii' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms latticesum_gamma_iii

end FormalResearch.Special.Lattice

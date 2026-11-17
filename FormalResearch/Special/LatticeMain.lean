module

public import FormalResearch.Special.LatticeSumGamma

/-!
# `lem:latticesum` (o) and (ii) for the Gamma phase

Source: `Weyl/free_fermion/paper/parts/constants.tex`, `lem:latticesum`.  Setting: `ϰ = nc ≥ 1`,
`b > 0`, `c_* < ½`, `L^{c_*/2} ≤ X ≤ L^{c_*}`, `F_- ≤ F_i ≤ F_+`, `ℓ_Σ = ∑ log(L F_i)`,
`G(s) = θ₀ + sℓ_Σ - ϰ arg Γ(½+is)` (`gammaG`), `Θ` continuous strictly increasing on `[-X, X]` with
`|Θ - G| ≤ L^{-b}`, `S = {x ∈ [-X,X] : Θ(x) ∈ πℤ}`, `φ` analytic in `|Im s| ≤ δ` with
`|φ| ≤ C_φ e^{-κ|Re s|}`, `0 < b₁ < min(b, ϰ min(δ, ¼))`.

* (o): each `[a,a']` contains `≤ 2ϰ log L/π (a'-a) + 2` levels; consecutive levels are at distance in
  `[π/(4ϰ log L), 4π/(ϰ log L)]`;
* (ii): `‖∑_{x∈S} φ(x) - (1/π)∫_ℝ φ(s)(ℓ_Σ - ϰ Re ψ(½+is)) ds‖ ≤ C C_φ L^{-b₁}`, `C, L₀` depending only on
  `nc, b, c_*, F_±, δ, κ, b₁` (not on `φ`'s constant, `θ₀`, `X`, `Θ`, `F`).

Not formalised: the Gamma-function identification of the phase (the continuous branch
`argGammaHalf` is used; its relation to the polar argument of `Γ(½+is)` is not proved); (i) for the Gamma phase
as a standalone statement (the abstract (i) is `latticeI_bound`).  (iii) for the Gamma phase is `latticesum_gamma_iii`
(`LatticeIIIGamma`).
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex Barnes MeasureTheory intervalIntegral

/-- Elementary bound `‖φ‖ |g| ≤ C (A + B|s|) e^{-κ|s|} ≤ C (A + 2B/κ) e^{-κ|s|/2}`. -/
lemma phi_gdens_le {κ Cφ A B u g s : ℝ} (hκ : 0 < κ) (hCφ : 0 ≤ Cφ)
    (hφs : u ≤ Cφ * Real.exp (-κ * |s|)) (hg : g ≤ A + B * |s|) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hg0 : 0 ≤ g) :
    u * g ≤ Cφ * (A + 2 * B / κ) * Real.exp (-(κ / 2) * |s|) := by
  have hs0 := abs_nonneg s
  have e1 : Real.exp (-κ * |s|) = Real.exp (-(κ / 2) * |s|) * Real.exp (-(κ / 2) * |s|) := by
    rw [← Real.exp_add]; ring_nf
  have hE0 := (Real.exp_pos (-(κ / 2) * |s|)).le
  have e3 : |s| * Real.exp (-(κ / 2) * |s|) ≤ 2 / κ := by
    have h5 : κ / 2 * |s| ≤ Real.exp (κ / 2 * |s|) := by
      have := Real.add_one_le_exp (κ / 2 * |s|); linarith
    have h6 : Real.exp (-(κ / 2) * |s|) * Real.exp (κ / 2 * |s|) = 1 := by
      rw [← Real.exp_add]; simp
    rw [le_div_iff₀ hκ]
    have := mul_le_mul_of_nonneg_left h5 hE0
    nlinarith
  have step : (A + B * |s|) * Real.exp (-(κ / 2) * |s|) ≤ A + 2 * B / κ := by
    have h1 : B * (|s| * Real.exp (-(κ / 2) * |s|)) ≤ B * (2 / κ) :=
      mul_le_mul_of_nonneg_left e3 hB0
    have e2 : Real.exp (-(κ / 2) * |s|) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have h2 : A * Real.exp (-(κ / 2) * |s|) ≤ A := by nlinarith
    calc (A + B * |s|) * Real.exp (-(κ / 2) * |s|)
        = A * Real.exp (-(κ / 2) * |s|) + B * (|s| * Real.exp (-(κ / 2) * |s|)) := by ring
      _ ≤ A + B * (2 / κ) := add_le_add h2 h1
      _ = A + 2 * B / κ := by ring
  have h8 : Cφ * ((A + B * |s|) * Real.exp (-(κ / 2) * |s|)) ≤ Cφ * (A + 2 * B / κ) :=
    mul_le_mul_of_nonneg_left step hCφ
  calc u * g ≤ (Cφ * Real.exp (-κ * |s|)) * (A + B * |s|) :=
        mul_le_mul hφs hg hg0 (by positivity)
    _ = Cφ * ((A + B * |s|) * Real.exp (-(κ / 2) * |s|)) * Real.exp (-(κ / 2) * |s|) := by
        rw [e1]; ring
    _ ≤ Cφ * (A + 2 * B / κ) * Real.exp (-(κ / 2) * |s|) :=
        mul_le_mul_of_nonneg_right h8 hE0

/-- Linear bound for the density constant. -/
theorem lin_bound (nc : ℕ) {κ T ℓ L : ℝ} (hκ : 0 < κ) (hT : 0 ≤ T) (hℓ0 : 0 ≤ ℓ)
    (hℓ : ℓ ≤ nc * (Real.log L + T)) (hL : 1 < L) (hlogL : Real.log L ≤ L) :
    (ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ ≤
      (nc * (T + 6) / Real.pi + 2 * nc / (Real.pi * κ)) * L := by
  have hpi := Real.pi_pos
  have hL0 : 0 < L := by linarith
  have hnc0 : (0 : ℝ) ≤ nc := Nat.cast_nonneg _
  have h5 : ℓ + 5 * nc ≤ nc * (T + 6) * L := by
    have h : Real.log L + T + 5 ≤ (T + 6) * L := by nlinarith
    have := mul_le_mul_of_nonneg_left h hnc0
    nlinarith
  have h6 : (ℓ + 5 * nc) / Real.pi ≤ nc * (T + 6) / Real.pi * L := by
    rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right h5 hpi.le
  have h7 : 2 * (nc / Real.pi) / κ ≤ 2 * nc / (Real.pi * κ) * L := by
    have e : 2 * (nc / Real.pi) / κ = 2 * nc / (Real.pi * κ) := by field_simp
    rw [e]
    have : 0 ≤ 2 * (nc : ℝ) / (Real.pi * κ) := by positivity
    nlinarith
  calc _ ≤ _ := add_le_add h6 h7
    _ = _ := by ring

/-- The explicit error of `latticesum_gamma_fixed` is `O(C_φ L^{-b₁})` uniformly in `X ≥ L^{c_*/2}` and
`0 ≤ ℓ ≤ nc (log L + T)`. -/
theorem error_asymp (nc : ℕ) {κ cs b b1 y1 A1 A2 A3 T : ℝ} (hκ : 0 < κ) (hcs0 : 0 < cs)
    (hb1b : b1 ≤ b) (hy : b1 ≤ nc * y1) (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hA3 : 0 ≤ A3) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 < L → ∀ X Cφ ℓ : ℝ, L ^ (cs / 2) ≤ X → 0 ≤ Cφ → 0 ≤ ℓ →
      ℓ ≤ nc * (Real.log L + T) →
      Cφ * (A1 * Real.exp (-κ * X) + A2 * (L ^ (-b) / Real.pi) +
          A3 * Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1))) +
        2 * (Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ)) * Real.exp (-(κ / 2) * X) /
          (κ / 2) ≤ C * Cφ * L ^ (-b1) := by
  obtain ⟨C1, hC1, hE⟩ := exp_neg_rpow_le (a := κ / 2) (c := cs / 2) (p := b1 + 1) (by positivity)
    (by positivity)
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  set Q : ℝ := nc * (T + 6) / Real.pi + 2 * nc / (Real.pi * κ) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  refine ⟨A1 * C1 + A2 + A3 + 4 * Q * C1 / κ + 1, by positivity, ?_⟩
  intro L hL X Cφ ℓ hX hCφ hℓ0 hℓ
  have hL0 : 0 < L := by linarith
  set P : ℝ := L ^ (-b1) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hL0 _
  have hXpos : 0 < X := lt_of_lt_of_le (Real.rpow_pos_of_pos hL0 _) hX
  -- exponential tail
  have hEX : Real.exp (-(κ / 2) * X) ≤ C1 * (P / L) := by
    have h1 : Real.exp (-(κ / 2) * X) ≤ Real.exp (-((κ / 2) * L ^ (cs / 2))) := by
      apply Real.exp_le_exp.2
      nlinarith
    have h2 := hE L hL.le
    have h3 : L ^ (-(b1 + 1)) = P / L := by
      rw [show -(b1 + 1) = -b1 - 1 by ring, Real.rpow_sub_one hL0.ne']
    rw [h3] at h2
    exact h1.trans h2
  have hEX0 : 0 ≤ Real.exp (-(κ / 2) * X) := (Real.exp_pos _).le
  have hEX1 : Real.exp (-κ * X) ≤ C1 * P := by
    have : Real.exp (-κ * X) ≤ Real.exp (-(κ / 2) * X) := Real.exp_le_exp.2 (by nlinarith)
    have h4 : P / L ≤ P := div_le_self hP0.le hL.le
    nlinarith
  have hexpP : Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1)) ≤ P := by
    have e : Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1)) =
        L ^ (-(nc * y1)) := by
      rw [Real.rpow_def_of_pos hL0]; congr 1; field_simp
    rw [e]
    exact Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have hPb : L ^ (-b) ≤ P := Real.rpow_le_rpow_of_exponent_le hL.le (by linarith)
  have hlogL : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hlin := lin_bound nc hκ hT hℓ0 hℓ hL hlogL
  have hT2 : 2 * (Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ)) *
        Real.exp (-(κ / 2) * X) / (κ / 2) ≤ 4 * Q * C1 / κ * Cφ * P := by
    have h8 : Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ) ≤ Cφ * (Q * L) :=
      mul_le_mul_of_nonneg_left hlin hCφ
    have h9 : Cφ * (Q * L) * Real.exp (-(κ / 2) * X) ≤ Cφ * (Q * L) * (C1 * (P / L)) :=
      mul_le_mul_of_nonneg_left hEX (by positivity)
    have h10 : Cφ * (Q * L) * (C1 * (P / L)) = Q * C1 * Cφ * P := by field_simp
    have h11 : Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ) * Real.exp (-(κ / 2) * X) ≤
        Cφ * (Q * L) * Real.exp (-(κ / 2) * X) := mul_le_mul_of_nonneg_right h8 hEX0
    rw [div_le_iff₀ (by positivity)]
    have : 2 * (Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ)) * Real.exp (-(κ / 2) * X) ≤
        2 * (Q * C1 * Cφ * P) := by nlinarith
    calc _ ≤ 2 * (Q * C1 * Cφ * P) := this
      _ = 4 * Q * C1 / κ * Cφ * P * (κ / 2) := by field_simp; ring
  have hT1 : Cφ * (A1 * Real.exp (-κ * X) + A2 * (L ^ (-b) / Real.pi) +
          A3 * Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1))) ≤
      Cφ * (A1 * (C1 * P) + A2 * P + A3 * P) := by
    apply mul_le_mul_of_nonneg_left _ hCφ
    have a1 : A1 * Real.exp (-κ * X) ≤ A1 * (C1 * P) := mul_le_mul_of_nonneg_left hEX1 hA1
    have a2 : A2 * (L ^ (-b) / Real.pi) ≤ A2 * P := by
      apply mul_le_mul_of_nonneg_left _ hA2
      calc L ^ (-b) / Real.pi ≤ L ^ (-b) := div_le_self (Real.rpow_pos_of_pos hL0 _).le (by linarith)
        _ ≤ P := hPb
    have a3 := mul_le_mul_of_nonneg_left hexpP hA3
    linarith
  have hfinal : Cφ * (A1 * (C1 * P) + A2 * P + A3 * P) + 4 * Q * C1 / κ * Cφ * P ≤
      (A1 * C1 + A2 + A3 + 4 * Q * C1 / κ + 1) * Cφ * P := by
    have : 0 ≤ Cφ * P := by positivity
    nlinarith
  linarith

/-- The fixed-`L` form of `latticesum_gamma`: all error terms explicit. -/
theorem latticesum_gamma_fixed (nc : ℕ) (hnc : 1 ≤ nc) {L Fm Fp cs δ κ b X θ0 y1 r r0 A1 A2 A3 : ℝ}
    (hL : 1 < L) (hFm : 0 < Fm) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hδ : 0 < δ)
    (hκ : 0 < κ) (hy1 : 0 < y1) (hr : 0 < r) (hr0 : 0 < r0) (hyr : y1 + r + r0 ≤ min δ (1 / 4))
    (hA : ∀ (Cφ ε X m : ℝ), 0 ≤ Cφ → 0 ≤ ε → ε ≤ 1 → 1 ≤ m →
      (1 / 2 + ε) * (2 * (Cφ * Real.exp (-κ * X))) +
      ε * (Cφ * Real.exp (κ * r0) / r0 * (2 / κ)) +
      (Cφ * Real.exp (κ * r0) / r0 * wconst κ * ε * (1 + 4 * (4 * m + 2 * ε + 1) / m) +
        (Cφ * Real.exp (κ * r0) / r0 * Real.exp (-κ * X) / m +
          1 / 12 * (2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m (nc * (16 * invSqSum) / Real.pi) * y1 *
              Real.exp (-κ * X) +
            2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m (nc * (16 * invSqSum) / Real.pi) / κ *
              Real.exp (-(2 * Real.pi * m * y1))))) ≤
      Cφ * (A1 * Real.exp (-κ * X) + A2 * ε + A3 * Real.exp (-(2 * Real.pi * m * y1))))
    (F : Fin nc → ℝ) (hF : ∀ i, Fm ≤ F i ∧ F i ≤ Fp)
    (hX : L ^ (cs / 2) ≤ X) (hXu : X ≤ L ^ cs)
    (h1 : Real.log 3 + 5 - Real.log Fm ≤ (1 / 2 - cs) * Real.log L)
    (h2 : Real.log Fp + 3 ≤ Real.log L) (hm1 : 2 * Real.pi ≤ nc * Real.log L)
    (hℓ0 : 0 ≤ lsum nc L F) (hε4 : L ^ (-b) ≤ 1 / 4)
    (Θ : ℝ → ℝ) (hΘc : ContinuousOn Θ (Icc (-X) X)) (hΘm : StrictMonoOn Θ (Icc (-X) X))
    (hΘG : ∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) (S : Finset ℝ)
    (hS : ∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) :
    ((∀ a a' : ℝ, -X ≤ a → a ≤ a' → a' ≤ X →
        ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ 2 * nc * Real.log L / Real.pi * (a' - a) + 2) ∧
     (∀ x ∈ S, ∀ y ∈ S, x < y → (∀ z ∈ S, ¬(x < z ∧ z < y)) →
        Real.pi / (4 * nc * Real.log L) ≤ y - x ∧ y - x ≤ 4 * Real.pi / (nc * Real.log L))) ∧
    ∀ (φ : ℂ → ℂ) (Cφ : ℝ), 0 ≤ Cφ → DifferentiableOn ℂ φ {s | |s.im| ≤ δ} →
      (∀ s : ℂ, |s.im| ≤ δ → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|)) →
      ‖∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, φ (s : ℂ) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ ≤
        Cφ * (A1 * Real.exp (-κ * X) + A2 * (L ^ (-b) / Real.pi) +
          A3 * Real.exp (-(2 * Real.pi * (nc * Real.log L / (2 * Real.pi)) * y1))) +
        2 * (Cφ * ((lsum nc L F + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ)) *
          Real.exp (-(κ / 2) * X) / (κ / 2) := by
  have hL0 : 0 < L := by linarith
  have hlogL : 0 < Real.log L := Real.log_pos hL
  have hpi := Real.pi_pos
  have hncr : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
  set ℓ := lsum nc L F with hℓ
  set m : ℝ := nc * Real.log L / (2 * Real.pi) with hm
  have hm1' : 1 ≤ m := by rw [hm, le_div_iff₀ (by positivity)]; linarith
  set ε : ℝ := L ^ (-b) / Real.pi with hε
  have hε0 : 0 ≤ ε := by positivity
  have hε1 : ε ≤ 1 / 4 := by
    rw [hε, div_le_iff₀ hpi]
    nlinarith [Real.pi_gt_three]
  have hCal := gamma_calPhase nc hnc hL hFm F hF hcs0 hcs hX hXu h1 h2 (θ0 := θ0)
  have hy0c : 0 < min δ (1 / 4) := lt_min hδ (by norm_num)
  have hCal' := hCal.mono hy0c (min_le_right _ _)
  have hX0 : 0 < X := hCal.hX
  -- level data
  obtain ⟨t', hd, ht'⟩ := exists_levelData hCal' (continuous_realPhase_gamma nc ℓ θ0)
    (t := fun s => Θ s / Real.pi) (ε := ε)
    (hΘc.div_const _) (fun x hx y hy hxy => div_lt_div_of_pos_right (hΘm hx hy hxy) hpi) hε0
    (fun s hs => by
      rw [realPhase_gamma, ← sub_div, abs_div, abs_of_pos hpi]
      exact div_le_div_of_nonneg_right (hΘG s hs) hpi.le) (S := S)
    (fun x => by
      rw [hS x]
      refine and_congr_right (fun _ => exists_congr (fun n => ?_))
      rw [div_eq_iff hpi.ne'])
  have hmMeq : 4 * m = 2 * nc * Real.log L / Real.pi := by rw [hm]; field_simp; ring
  refine ⟨⟨fun a a' ha haa' ha' => ?_, fun x hx y hy hxy hcons => ?_⟩, fun φ Cφ hCφ hφd hφb => ?_⟩
  · have := hd.card_levels_le haa' ha ha'
    rw [hmMeq] at this
    linarith
  · have h3 := hd.spacing_ge hx hy hxy hcons
    have h4 := hd.spacing_le hx hy hxy hcons
    have hM : 4 * m = 2 * nc * Real.log L / Real.pi := hmMeq
    have hnl : 0 < (nc : ℝ) * Real.log L := mul_pos (by positivity) hlogL
    constructor
    · refine le_trans ?_ h3
      have e : (1 - 2 * ε) / (4 * m) = (1 - 2 * ε) * Real.pi / (2 * (nc * Real.log L)) := by
        rw [hm]; field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hpi hnl]
    · refine h4.trans ?_
      have e : (1 + 2 * ε) / m = (1 + 2 * ε) * (2 * Real.pi) / (nc * Real.log L) := by
        rw [hm]; field_simp
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_pos hpi hnl]
  · have hφd' : DifferentiableOn ℂ φ {s | |s.im| ≤ min δ (1 / 4)} :=
      hφd.mono (fun s (hs : |s.im| ≤ min δ (1 / 4)) => show |s.im| ≤ δ from le_trans hs (min_le_left _ _))
    have hφb' : ∀ s : ℂ, |s.im| ≤ min δ (1 / 4) → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|) :=
      fun s hs => hφb s (hs.trans (min_le_left _ _))
    have hII := latticeII_bound hd (φ := φ) (Cφ := Cφ) (κ := κ) (y1 := y1) (r := r) (r0 := r0)
      hκ hCφ hy1 hr hr0 hyr hφd' hφb'
    have hE := hA Cφ ε X m hCφ hε0 (by linarith) hm1'
    have hφc : Continuous (fun s : ℝ => φ (s : ℂ)) := continuous_real_of_strip hy0c hφd'
    set f : ℝ → ℂ := fun s => φ (s : ℂ) * ((gdens nc ℓ s : ℝ) : ℂ) with hf
    have hfc : Continuous f := by
      have := continuous_gdens nc ℓ
      exact hφc.mul (Complex.continuous_ofReal.comp this)
    have hint_eq : ∫ s in (-X)..X, φ (s : ℂ) * ((CalPhase.realDeriv (gammaPhase nc ℓ θ0) s : ℝ) : ℂ) =
        ∫ s in (-X)..X, f s := by
      refine intervalIntegral.integral_congr (fun s _ => ?_)
      simp only [hf, realDeriv_gamma]
    rw [hint_eq] at hII
    -- the tail
    have hfb : ∀ s, ‖f s‖ ≤ Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ) *
        Real.exp (-(κ / 2) * |s|) := by
      intro s
      have hφs : ‖φ (s : ℂ)‖ ≤ Cφ * Real.exp (-κ * |s|) := by
        have := hφb (s : ℂ) (by simpa using hδ.le)
        simpa using this
      simp only [hf]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact phi_gdens_le hκ hCφ hφs (abs_gdens_le nc hℓ0 s) (by positivity) (by positivity)
        (abs_nonneg _)
    have hD : 0 ≤ Cφ * ((ℓ + 5 * nc) / Real.pi + 2 * (nc / Real.pi) / κ) := by positivity
    obtain ⟨_, htail⟩ := tail_integral_le hfc (a := κ / 2) (X := X) (by positivity) hD hX0.le hfb
    have hfin : ‖∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, f s‖ ≤
        ‖∑ x ∈ S, φ (x : ℂ) - ∫ s in (-X)..X, f s‖ + ‖(∫ s : ℝ, f s) - ∫ s in (-X)..X, f s‖ := by
      have : ∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, f s =
          (∑ x ∈ S, φ (x : ℂ) - ∫ s in (-X)..X, f s) - ((∫ s : ℝ, f s) - ∫ s in (-X)..X, f s) := by ring
      rw [this]; exact norm_sub_le _ _
    simp only [hf] at hfin hII htail ⊢
    refine hfin.trans (add_le_add (hII.trans ?_) htail)
    convert hE using 3

/-- **`lem:latticesum` (o) and (ii) for the Gamma phase** (paper form).  Constants `C, L₀` depend only on
`nc, b, c_*, δ, κ, b₁, F_±`. -/
theorem latticesum_gamma (nc : ℕ) (hnc : 1 ≤ nc) {b cs δ κ b1 Fm Fp : ℝ}
    (hb : 0 < b) (hcs0 : 0 < cs) (hcs : cs < 1 / 2) (hδ : 0 < δ) (hκ : 0 < κ) (hb1 : 0 < b1)
    (hb1b : b1 < b) (hb1δ : b1 < nc * min δ (1 / 4)) (hFm : 0 < Fm) (hFmp : Fm ≤ Fp) :
    ∃ C L0 : ℝ, 0 < C ∧ 1 < L0 ∧ ∀ L : ℝ, L0 ≤ L → ∀ F : Fin nc → ℝ, (∀ i, Fm ≤ F i ∧ F i ≤ Fp) →
      ∀ (X θ0 : ℝ), L ^ (cs / 2) ≤ X → X ≤ L ^ cs →
      ∀ Θ : ℝ → ℝ, ContinuousOn Θ (Icc (-X) X) → StrictMonoOn Θ (Icc (-X) X) →
      (∀ s ∈ Icc (-X) X, |Θ s - gammaG nc (lsum nc L F) θ0 s| ≤ L ^ (-b)) →
      ∀ S : Finset ℝ, (∀ x, x ∈ S ↔ x ∈ Icc (-X) X ∧ ∃ n : ℤ, Θ x = n * Real.pi) →
      ((∀ a a' : ℝ, -X ≤ a → a ≤ a' → a' ≤ X →
          ((S.filter fun x => x ∈ Icc a a').card : ℝ) ≤ 2 * nc * Real.log L / Real.pi * (a' - a) + 2) ∧
       (∀ x ∈ S, ∀ y ∈ S, x < y → (∀ z ∈ S, ¬(x < z ∧ z < y)) →
          Real.pi / (4 * nc * Real.log L) ≤ y - x ∧ y - x ≤ 4 * Real.pi / (nc * Real.log L))) ∧
      ∀ (φ : ℂ → ℂ) (Cφ : ℝ), 0 ≤ Cφ → DifferentiableOn ℂ φ {s | |s.im| ≤ δ} →
        (∀ s : ℂ, |s.im| ≤ δ → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|)) →
        ‖∑ x ∈ S, φ (x : ℂ) - ∫ s : ℝ, φ (s : ℂ) * ((gdens nc (lsum nc L F) s : ℝ) : ℂ)‖ ≤
          C * Cφ * L ^ (-b1) := by
  have hncpos : (0 : ℝ) < nc := by exact_mod_cast hnc
  set Y : ℝ := min δ (1 / 4) with hY
  have hY0 : 0 < Y := lt_min hδ (by norm_num)
  have hbY : b1 / nc < Y := by rw [div_lt_iff₀ hncpos]; linarith
  set y1 : ℝ := (b1 / nc + Y) / 2 with hy1d
  have hy1 : 0 < y1 := by positivity
  have hy1Y : y1 < Y := by rw [hy1d]; linarith
  set r : ℝ := (Y - y1) / 2 with hrd
  have hr : 0 < r := by rw [hrd]; linarith
  have hyr : y1 + r + r ≤ Y := by rw [hrd]; linarith
  have hnc_y : b1 ≤ nc * y1 := by
    have : (nc : ℝ) * (b1 / nc) = b1 := by field_simp
    have h2 : (nc : ℝ) * y1 = (b1 + nc * Y) / 2 := by rw [hy1d]; field_simp
    rw [h2]; linarith
  have hK : 0 ≤ (nc : ℝ) * (16 * invSqSum) / Real.pi := by
    have := invSqSum_nonneg; positivity
  obtain ⟨A1, A2, A3, hA1, hA2, hA3, hA⟩ :=
    explicit_total_le κ r r y1 ((nc : ℝ) * (16 * invSqSum) / Real.pi) hκ hr hr hy1 hK
  obtain ⟨C, hC, hCb⟩ := error_asymp nc (cs := cs) (b := b) (b1 := b1) (y1 := y1) (A1 := A1)
    (A2 := A2) (A3 := A3) (T := |Real.log Fp|) hκ hcs0 hb1b.le hnc_y hA1 hA2 hA3 (abs_nonneg _)
  set Λ : ℝ := max (max (2 * Real.pi) ((Real.log 3 + 5 - Real.log Fm) / (1 / 2 - cs)))
    (max (max (Real.log Fp + 3) (-Real.log Fm)) (Real.log 4 / b)) with hΛ
  refine ⟨C, Real.exp Λ + 1, hC, by linarith [Real.exp_pos Λ], ?_⟩
  intro L hLL F hF X θ0 hX hXu Θ hΘc hΘm hΘG S hS
  have hL1 : 1 < L := by linarith [Real.exp_pos Λ]
  have hL0 : 0 < L := by linarith
  have hlogL : Λ ≤ Real.log L := (Real.le_log_iff_exp_le hL0).2 (by linarith)
  have hΛ1 : 2 * Real.pi ≤ Real.log L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlogL
  have hΛ2 : (Real.log 3 + 5 - Real.log Fm) / (1 / 2 - cs) ≤ Real.log L :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlogL
  have hΛ3 : Real.log Fp + 3 ≤ Real.log L :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hlogL
  have hΛ4 : -Real.log Fm ≤ Real.log L :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hlogL
  have hΛ5 : Real.log 4 / b ≤ Real.log L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlogL
  have hm1 : 2 * Real.pi ≤ nc * Real.log L := by
    have hlp : 0 ≤ Real.log L := by linarith [Real.pi_pos]
    have : (1 : ℝ) ≤ nc := by exact_mod_cast hnc
    nlinarith
  have h1 : Real.log 3 + 5 - Real.log Fm ≤ (1 / 2 - cs) * Real.log L := by
    have := (div_le_iff₀ (by linarith : 0 < 1 / 2 - cs)).1 hΛ2
    linarith
  have hε4 : L ^ (-b) ≤ 1 / 4 := by
    rw [Real.rpow_def_of_pos hL0]
    have h : Real.log 4 ≤ b * Real.log L := by
      have := (div_le_iff₀ hb).1 hΛ5
      linarith
    have e : Real.log L * -b = -(b * Real.log L) := by ring
    rw [e, show (1 / 4 : ℝ) = Real.exp (-Real.log 4) by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num]
    exact Real.exp_le_exp.2 (by linarith)
  obtain ⟨hlo, hup⟩ := lsum_bounds nc hL0 hFm F hF
  have hℓ0 : 0 ≤ lsum nc L F := le_trans (mul_nonneg hncpos.le (by linarith)) hlo
  have hℓup : lsum nc L F ≤ nc * (Real.log L + |Real.log Fp|) :=
    hup.trans (mul_le_mul_of_nonneg_left (by linarith [le_abs_self (Real.log Fp)]) hncpos.le)
  have hfix := latticesum_gamma_fixed nc hnc (L := L) (Fm := Fm) (Fp := Fp) (cs := cs) (δ := δ)
    (κ := κ) (b := b) (X := X) (θ0 := θ0) (y1 := y1) (r := r) (r0 := r) (A1 := A1) (A2 := A2)
    (A3 := A3) hL1 hFm hcs0 hcs hδ hκ hy1 hr hr hyr hA F hF hX hXu h1 hΛ3 hm1 hℓ0 hε4 Θ hΘc hΘm hΘG
    S hS
  refine ⟨hfix.1, fun φ Cφ hCφ hφd hφb => ?_⟩
  refine (hfix.2 φ Cφ hCφ hφd hφb).trans ?_
  exact hCb L hL1 X Cφ (lsum nc L F) hX hCφ hℓ0 hℓup

/-- info: 'FormalResearch.Special.Lattice.latticesum_gamma' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms latticesum_gamma

/-- info: 'FormalResearch.Special.Lattice.latticesum_gamma_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms latticesum_gamma_fixed

end FormalResearch.Special.Lattice

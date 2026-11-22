module

public import FormalResearch.ModularBootstrap.Crossing.LemmaInputs
public import FormalResearch.ModularBootstrap.Crossing.BesselBridge
public import FormalResearch.ModularBootstrap.SlitStrip.EntropyAndDeficit

/-!
# Lemma G from Lemma PJ (fixed gap `x₀ = 0.05`)

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma G (`vlo:Gap`), last paragraph
"Poisson--Jensen and integration" of its proof.

`Crossing.LemmaGapInput fg` (`Crossing.LemmaInputs`) is the uniform deep-lobe estimate
`∫₀^{c'·0.05²/3} |g| V dt ≤ C_deep e^{-κ_deep c'} M[g]` over all concrete Virasoro tests.  The paper
derives it from the strip Poisson--Jensen bound, the deficit `(G-deficit)` and the Bessel bound
`V ≤ 2 e^{c' L(x)}`; this file carries that derivation out:

* `lemmaGapInput_of_lemmaPJInput`: for any real-slice data `rs` and majorant `U` obeying `(G-deficit)`
  (`g_deficit`), `LemmaPJInput rs c_PJ C_PJ U` implies `LemmaGapInput fg` for an explicit
  `fg : FixedGapInput` (`c_deep = max c_PJ 24`, `κ_deep = κ₀/2` with `κ₀ = 2.228 (ξ_* - 0.05)^{3/2}`,
  `C_deep` from `Proposition M` and `exists_rpow_le_mul_exp`).

The proof uses `proposition_M` (Lemma E + Lemma S for the mass and entropy terms), the proved deficit
bound `slitDeficit_ge`, and `cardyV_le_two_exp` from `Crossing.BesselBridge`.  Consequently
`Crossing.VirasoroStripInput` carries no deep-lobe field: `Crossing.Bridge` derives it from `hPJ`.
(`WeaklyFeasibleTest.hDeepLobe` itself stays a field there, because that structure is abstract in
`V` and `K_a`.)

Covered: the whole derivation for the fixed gap `x₀ = 0.05`.  The paper's Lemma G for every
`δ ∈ (0, ξ_*)` is the same computation with `0.05` replaced by `ξ_* - δ`; only `0.05` is formalised,
because that is the form `LemmaGapInput` and `theorem_A` use.
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology

namespace FormalResearch.ModularBootstrap.Integration

open Crossing

/-- Polynomial growth is dominated by any exponential: for any real `p` and `κ > 0` there is `C ≥ 0` with
`c ^ p ≤ C e^{κ c}` for all `c ≥ 1`. -/
theorem exists_rpow_le_mul_exp {p κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 1 ≤ c → c ^ p ≤ C * exp (κ * c) := by
  set n : ℕ := ⌈p⌉₊ with hn
  refine ⟨(n.factorial : ℝ) / κ ^ n, by positivity, fun c hc => ?_⟩
  have h1 : c ^ p ≤ c ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hc (Nat.le_ceil p)
  rw [Real.rpow_natCast] at h1
  have h2 := Real.pow_div_factorial_le_exp (x := κ * c) (by positivity) n
  have hfac : (0 : ℝ) < n.factorial := by positivity
  have hκn : 0 < κ ^ n := by positivity
  rw [div_le_iff₀ hfac, mul_pow] at h2
  calc c ^ p ≤ c ^ n := h1
    _ = (n.factorial : ℝ) / κ ^ n * (κ ^ n * c ^ n / n.factorial) := by field_simp
    _ ≤ (n.factorial : ℝ) / κ ^ n * exp (κ * c) := by gcongr; rw [div_le_iff₀ hfac]; linarith

/-- **Lemma G from Lemma PJ (`vlo:Gap`, fixed gap `x₀ = 0.05`).**  Let `rs` be real-slice data and `U`
a majorant satisfying `(G-deficit)` (`U x + (2π/3) x ≤ -κ(ξ_* - x)` on `[0, ξ_*)`).  If
`LemmaPJInput rs c_PJ C_PJ U` holds, then `LemmaGapInput fg` holds for some `fg : FixedGapInput`.
Not covered: the proof of `LemmaPJInput` itself (the strip Poisson--Jensen inequality). -/
theorem lemmaGapInput_of_lemmaPJInput (rs : RealSliceData) (U : ℝ → ℝ) {c_PJ C_PJ : ℝ}
    (hc_PJ : 1 ≤ c_PJ)
    (hdef : ∀ x ∈ Ico 0 xiStar, U x + (2 * π / 3) * x ≤ -slitDeficit (xiStar - x))
    (hPJ : LemmaPJInput rs c_PJ C_PJ U) :
    ∃ fg : FixedGapInput, LemmaGapInput fg := by
  obtain ⟨C_M1, C_M2, hCM1, hprop⟩ := proposition_M rs (C_PJ := C_PJ) hc_PJ
  set δ₀ : ℝ := xiStar - 0.05 with hδ₀def
  have hδ₀ : 0 < δ₀ := sub_pos.mpr xiStar_gt_005
  set κ₀ : ℝ := 2.228 * δ₀ ^ ((3 : ℝ) / 2) with hκ₀def
  have hκ₀ : 0 < κ₀ := by positivity
  obtain ⟨C₄, hC₄, hC₄le⟩ := exists_rpow_le_mul_exp (p := C_M1 + 1) (κ := κ₀ / 2)
    (by positivity)
  refine ⟨{ c_deep := max c_PJ 24
            C_deep := (2 / δ₀) * exp C_M2 * C₄
            κ_deep := κ₀ / 2
            hc_deep := le_max_of_le_left hc_PJ
            hC_deep := by positivity
            hκ_deep := by positivity }, ?_⟩
  intro c' hc' g hg
  change max c_PJ 24 ≤ c' at hc'
  dsimp only
  have hc24 : (24 : ℝ) ≤ c' := le_trans (le_max_right _ _) hc'
  have hcPJ : c_PJ ≤ c' := le_trans (le_max_left _ _) hc'
  have hc1 : 1 ≤ c' := by linarith
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  have hMnn : 0 ≤ virasoroProblem.cardyNorm (c' / 12) g := virasoroProblem.cardyNorm_nonneg hshift g
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g with hM
  set t₀ : ℝ := c' * (0.05 : ℝ) ^ 2 / 3 with ht₀
  have ht₀nn : 0 ≤ t₀ := by positivity
  have hrhs_nn : 0 ≤ (2 / δ₀) * exp C_M2 * C₄ * exp (-(κ₀ / 2) * c') * M := by positivity
  by_cases hz : ∃ t ≥ 0, g t ≠ 0
  swap
  · push Not at hz
    have : ∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t = 0 := by
      rw [intervalIntegral.integral_of_le ht₀nn]
      refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
      rw [hz t ht.1.le]; simp
    rw [this]; exact hrhs_nn
  have hMpos : 0 < M := cardyNorm_pos_of_nonzero hshift hg hz
  have hbound := hprop hcPJ hMpos (fun x hx hne => hPJ hcPJ hg hMpos x hx hne)
  -- the pointwise bound on `x ∈ [0, 0.05]`
  set B : ℝ := (2 / δ₀) * exp C_M2 * c' ^ C_M1 * exp (-κ₀ * c') * M with hB
  have hBnn : 0 ≤ B := by positivity
  have key : ∀ x ∈ Icc (0 : ℝ) 0.05,
      |g (c' * x ^ 2 / 3)| * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤ B := by
    intro x hx
    have hxξ : x ∈ Ico 0 xiStar := ⟨hx.1, by linarith [hx.2, xiStar_gt_005]⟩
    have hV0 : 0 ≤ virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) :=
      virasoroProblem.cardyV_nonneg hshift (by positivity)
    by_cases h0 : g (c' * x ^ 2 / 3) = 0
    · rw [h0, abs_zero, zero_mul]; exact hBnn
    have hlog := hbound x hxξ h0
    -- the weak form of the log bound
    have hδx : δ₀ ≤ xiStar - x := by rw [hδ₀def]; linarith [hx.2]
    have hδxpos : 0 < xiStar - x := lt_of_lt_of_le hδ₀ hδx
    have hlogc : 0 ≤ Real.log c' := Real.log_nonneg hc1
    have hsqrt1 : Real.sqrt (xiStar - x) ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith [xiStar_lt_one, hx.1]
    have hterm1 : C_M1 * Real.sqrt (xiStar - x) * Real.log c' ≤ C_M1 * Real.log c' := by
      have := mul_le_mul_of_nonneg_left hsqrt1 hCM1
      nlinarith [mul_le_mul_of_nonneg_right this hlogc]
    have hterm2 : Real.log (1 / (xiStar - x)) ≤ Real.log (1 / δ₀) :=
      Real.log_le_log (by positivity) (one_div_le_one_div_of_le hδ₀ hδx)
    have hlog' : Real.log |g (c' * x ^ 2 / 3)| ≤
        c' * U x + Real.log M + C_M1 * Real.log c' + Real.log (1 / δ₀) + C_M2 := by
      linarith
    have hg_le : |g (c' * x ^ 2 / 3)| ≤
        M * c' ^ C_M1 * (1 / δ₀) * exp C_M2 * exp (c' * U x) := by
      have := Real.exp_le_exp.mpr hlog'
      rw [Real.exp_log (abs_pos.mpr h0)] at this
      refine this.trans_eq ?_
      rw [show c' * U x + Real.log M + C_M1 * Real.log c' + Real.log (1 / δ₀) + C_M2 =
          (c' * U x) + Real.log M + (C_M1 * Real.log c') + Real.log (1 / δ₀) + C_M2 by ring,
        Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hMpos,
        Real.exp_log (by positivity),
        show exp (C_M1 * Real.log c') = c' ^ C_M1 by rw [Real.rpow_def_of_pos hc0, mul_comm]]
      ring
    have hV_le : virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3) ≤
        2 * exp (c' * ((2 * π / 3) * x)) := by
      have h := cardyV_le_two_exp ha (t := c' * x ^ 2 / 3) (by positivity)
      have hsq : c' / 12 * (c' * x ^ 2 / 3) = (c' * x / 6) ^ 2 := by ring
      rw [hsq, Real.sqrt_sq (by have := hx.1; positivity)] at h
      have e : 4 * π * (c' * x / 6) = c' * ((2 * π / 3) * x) := by ring
      rwa [e] at h
    have hdef' : c' * U x + c' * ((2 * π / 3) * x) ≤ -(κ₀ * c') := by
      have h1 := hdef x hxξ
      have h2 := slitDeficit_ge (δ := xiStar - x) hδxpos.le (by linarith [hx.1])
      have h3 : δ₀ ^ ((3 : ℝ) / 2) ≤ (xiStar - x) ^ ((3 : ℝ) / 2) :=
        Real.rpow_le_rpow hδ₀.le hδx (by norm_num)
      have h4 : κ₀ ≤ slitDeficit (xiStar - x) := by
        refine le_trans ?_ h2
        rw [hκ₀def]; gcongr
      have h5 : U x + (2 * π / 3) * x ≤ -κ₀ := by linarith
      have := mul_le_mul_of_nonneg_left h5 hc0.le
      linarith
    calc |g (c' * x ^ 2 / 3)| * virasoroProblem.cardyV (c' / 12) (c' * x ^ 2 / 3)
        ≤ (M * c' ^ C_M1 * (1 / δ₀) * exp C_M2 * exp (c' * U x)) *
            (2 * exp (c' * ((2 * π / 3) * x))) := by gcongr
      _ = (2 / δ₀) * exp C_M2 * c' ^ C_M1 * M *
            exp (c' * U x + c' * ((2 * π / 3) * x)) := by rw [Real.exp_add]; ring
      _ ≤ (2 / δ₀) * exp C_M2 * c' ^ C_M1 * M * exp (-(κ₀ * c')) := by
          gcongr
      _ = B := by rw [hB, show -κ₀ * c' = -(κ₀ * c') by ring]; ring
  -- integrate
  have hint : ‖∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t‖ ≤ B * |t₀ - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [uIoc_of_le ht₀nn] at ht
    have hV0 : 0 ≤ virasoroProblem.cardyV (c' / 12) t :=
      virasoroProblem.cardyV_nonneg hshift ht.1.le
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hV0)]
    set x : ℝ := Real.sqrt (3 * t / c') with hx
    have hx2 : x ^ 2 = 3 * t / c' := Real.sq_sqrt (by have := ht.1; positivity)
    have htx : c' * x ^ 2 / 3 = t := by rw [hx2]; field_simp
    have hxle : x ≤ 0.05 := by
      rw [hx, Real.sqrt_le_left (by norm_num)]
      rw [div_le_iff₀ hc0]
      have := ht.2; rw [ht₀] at this; nlinarith
    have := key x ⟨Real.sqrt_nonneg _, hxle⟩
    rwa [htx] at this
  have hle1 : |t₀ - 0| ≤ c' := by
    rw [sub_zero, abs_of_nonneg ht₀nn, ht₀]; nlinarith
  have hfin : B * c' ≤ (2 / δ₀) * exp C_M2 * C₄ * exp (-(κ₀ / 2) * c') * M := by
    have hc'pow : c' ^ C_M1 * c' ≤ C₄ * exp (κ₀ / 2 * c') := by
      rw [← Real.rpow_add_one hc0.ne']; exact hC₄le c' hc1
    have e : B * c' = (2 / δ₀) * exp C_M2 * (c' ^ C_M1 * c') * exp (-κ₀ * c') * M := by
      rw [hB]; ring
    have e2 : (2 / δ₀) * exp C_M2 * (c' ^ C_M1 * c') * exp (-κ₀ * c') * M ≤
        (2 / δ₀) * exp C_M2 * (C₄ * exp (κ₀ / 2 * c')) * exp (-κ₀ * c') * M := by gcongr
    have e3 : exp (κ₀ / 2 * c') * exp (-κ₀ * c') = exp (-(κ₀ / 2) * c') := by
      rw [← Real.exp_add]; congr 1; ring
    calc B * c' = _ := e
      _ ≤ _ := e2
      _ = (2 / δ₀) * exp C_M2 * C₄ * (exp (κ₀ / 2 * c') * exp (-κ₀ * c')) * M := by ring
      _ = _ := by rw [e3]
  calc ∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t
      ≤ ‖∫ t in (0 : ℝ)..t₀, |g t| * virasoroProblem.cardyV (c' / 12) t‖ := le_abs_self _
    _ ≤ B * |t₀ - 0| := hint
    _ ≤ B * c' := by gcongr
    _ ≤ _ := hfin

/-- info: 'FormalResearch.ModularBootstrap.Integration.lemmaGapInput_of_lemmaPJInput' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaGapInput_of_lemmaPJInput

end FormalResearch.ModularBootstrap.Integration

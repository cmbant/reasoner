/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import FormalResearch.SignUncertainty.FctInnerSymbols
public import FormalResearch.SignUncertainty.FctEdgeIbp
public import FormalResearch.SignUncertainty.FctSymCal

/-!
# Lemma `fct:inner-symbols` (FCT.5b) (a): existence and bounds of the Abel limit `𝒮[κ]` (proved)

Paper I (`constant_terms_five.tex`), Lemma `fct:inner-symbols` (a).  For `M > 0`, `n ≥ 1`, `p < 3n - 1/2`, `|û| ≤ M`, `κ ∈ C^n([0,∞))` with `|κ^{(r)}| ≤ B (1+u)^{p-r}`:
the limit `lim_{ε ↓ 0} e^{-iπ/4} ∫₀^∞ u^{-1/2} e^{-i(ûu + u³/12) - εu²} κ(u) du` exists, `|𝒮[κ]| ≤ C_{M,n,p} B`, and `|𝒮[κ]| ≤ C B u_*^{p+1/2-3n}` if `κ = 0` on `[0, u_*]`,
`u_* ≥ U₀ = max(6, √(8M))`.

**Proof (Lean).**  The Gaussian is put into the phase: `w_ε(u) = -i(ûu + u³/12) - εu²`, `w_ε' = D_ε = -i(û + u²/4) - 2εu`, `|D_ε(u)| ≥ u²/8` for `u ≥ U₀`, `|e^{w_ε}| ≤ 1`.
The operator `𝒟_ε g = -(g/D_ε)'` satisfies `∫_U^∞ g e^{w_ε} = ∫_U^∞ (𝒟_ε g) e^{w_ε}` (`ibp_cexp`: complex-phase integration by parts, boundary terms vanish).
`Q_ε = 1/D_ε` is a symbol of order `-2` uniformly in `ε ∈ [0, 1]` (`fctQ_bound`, from `D Q = 1` and Leibniz) and its derivatives are continuous in `ε`
(`fctQ_cont`).  A `C^n` amplitude family of order `q < 3n - 1`, vanishing on `(V, U)`, therefore has an Abel limit of `∫ h_ε e^{w_ε}`, bounded by `C A U^{q+1-3n}`
(`fam_main`, induction on `n`: `𝒟_ε` lowers `C^{n+1}`, order `q` to `C^n`, order `q - 3`; the base case `q < -1` is dominated convergence).
`κ` is cut at `U₀` by a smooth step (`Real.smoothTransition`); the part near `0` is absolutely integrable (`near_part`), the part beyond `U₀` is `fam_main` with
`h = s · u^{-1/2} κ` (`amp_far`, symbol calculus `SBd.mul`); the tail clause is `fam_main` with `h = u^{-1/2} κ` and `U = u_*` (`amp_tail`).

Headline: `fctInnerSymbolsA : FctInnerSymbolsA`.  Corollaries (the "in particular" clauses): `fctInnerSymbolsA_box`, `fctInnerSymbolsA_tail_c`.

Class: proved.
-/
@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Real ContDiff

namespace FormalResearch.SignUncertainty

namespace FctSymA

/-- `w_ε(u) = -i(ûu + u³/12) - εu²`, the exponent of the regularised integrand of `𝒮`. -/
noncomputable def fctW (û ε u : ℝ) : ℂ :=
  -(Complex.I * ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) - ((ε * u ^ 2 : ℝ) : ℂ)

/-- `D_ε = w_ε'`, a quadratic polynomial in `u`. -/
noncomputable def fctD (û ε u : ℝ) : ℂ :=
  (-(Complex.I * (û : ℂ))) + (((-(2 * ε) : ℝ) : ℂ)) * (u : ℂ) + (-(Complex.I / 4)) * (u : ℂ) ^ 2

lemma hasDerivAt_ofReal_id (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 u := by
  simpa using (hasDerivAt_id u).ofReal_comp

lemma hasDerivAt_ofReal_sq (u : ℝ) : HasDerivAt (fun x : ℝ => (x : ℂ) ^ 2) (2 * (u : ℂ)) u := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2) (2 * u) u := by simpa using hasDerivAt_pow 2 u
  simpa using h.ofReal_comp

/-- `D_ε' = -2ε - (i/2) u`. -/
noncomputable def fctD1 (ε u : ℝ) : ℂ := (((-(2 * ε) : ℝ) : ℂ)) + (-(Complex.I / 4)) * (2 * (u : ℂ))

lemma hasDerivAt_fctD (û ε u : ℝ) : HasDerivAt (fctD û ε) (fctD1 ε u) u := by
  have h1 := hasDerivAt_ofReal_id u
  have h2 := hasDerivAt_ofReal_sq u
  have := ((h1.const_mul (((-(2 * ε) : ℝ) : ℂ))).const_add (-(Complex.I * (û : ℂ)))).add (h2.const_mul (-(Complex.I / 4)))
  exact this.congr_deriv (by simp [fctD1])

lemma hasDerivAt_fctD1 (ε u : ℝ) : HasDerivAt (fctD1 ε) (-(Complex.I / 2)) u := by
  have h1 := hasDerivAt_ofReal_id u
  have := (h1.const_mul (2 : ℂ)).const_mul (-(Complex.I / 4)) |>.const_add (((-(2 * ε) : ℝ) : ℂ))
  exact this.congr_deriv (by ring)

lemma hasDerivAt_fctW (û ε u : ℝ) : HasDerivAt (fctW û ε) (fctD û ε u) u := by
  have h1 : HasDerivAt (fun x : ℝ => ((û * x + x ^ 3 / 12 : ℝ) : ℂ)) (((û + u ^ 2 / 4 : ℝ) : ℂ)) u := by
    have h : HasDerivAt (fun x : ℝ => û * x + x ^ 3 / 12) (û + u ^ 2 / 4) u := by
      have := ((hasDerivAt_id u).const_mul û).add ((hasDerivAt_pow 3 u).div_const 12)
      exact this.congr_deriv (by simp; ring)
    exact h.ofReal_comp
  have h2 : HasDerivAt (fun x : ℝ => ((ε * x ^ 2 : ℝ) : ℂ)) (((2 * ε * u : ℝ) : ℂ)) u := by
    have h : HasDerivAt (fun x : ℝ => ε * x ^ 2) (2 * ε * u) u := by
      have := (hasDerivAt_pow 2 u).const_mul ε
      exact this.congr_deriv (by simp; ring)
    exact h.ofReal_comp
  have := (h1.const_mul (-Complex.I)).sub h2
  have e : fctW û ε = (fun y : ℝ => -Complex.I * ((û * y + y ^ 3 / 12 : ℝ) : ℂ)) - fun x : ℝ => ((ε * x ^ 2 : ℝ) : ℂ) := by
    funext x; simp [fctW]
  rw [e]
  refine this.congr_deriv ?_
  simp only [fctD]; push_cast; ring

lemma deriv_fctD (û ε : ℝ) : deriv (fctD û ε) = fctD1 ε := by
  funext u; exact (hasDerivAt_fctD û ε u).deriv

lemma deriv_fctD1 (ε : ℝ) : deriv (fctD1 ε) = fun _ => -(Complex.I / 2) := by
  funext u; exact (hasDerivAt_fctD1 ε u).deriv

lemma iteratedDeriv_fctD_two (û ε u : ℝ) : iteratedDeriv 2 (fctD û ε) u = -(Complex.I / 2) := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', deriv_fctD, deriv_fctD1]; simp

lemma iteratedDeriv_fctD_ge (û ε u : ℝ) (i : ℕ) : iteratedDeriv (i + 3) (fctD û ε) u = 0 := by
  rw [iteratedDeriv_succ', iteratedDeriv_succ', iteratedDeriv_succ', deriv_fctD, deriv_fctD1]
  simp

lemma iteratedDeriv_fctD_one (û ε u : ℝ) : iteratedDeriv 1 (fctD û ε) u = fctD1 ε u := by
  rw [iteratedDeriv_one, deriv_fctD]


/-- `Q_ε = 1/D_ε`. -/
noncomputable def fctQ (û ε : ℝ) : ℝ → ℂ := fun u => (fctD û ε u)⁻¹

/-- The threshold `U₀(M) = max(6, √(8M))`. -/
noncomputable def fctU0 (M : ℝ) : ℝ := max 6 (√(8 * M))

lemma fctD_eq (û ε u : ℝ) : fctD û ε u = ⟨-(2 * ε * u), -(û + u ^ 2 / 4)⟩ := by
  have hre : ((u : ℂ) ^ 2).re = u ^ 2 := by rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have him : ((u : ℂ) ^ 2).im = 0 := by rw [← Complex.ofReal_pow, Complex.ofReal_im]
  apply Complex.ext
  · simp [fctD, hre, him]
  · simp [fctD, hre, him]; ring

lemma fctD_im_le (û ε u : ℝ) : |û + u ^ 2 / 4| ≤ ‖fctD û ε u‖ := by
  have := Complex.abs_im_le_norm (fctD û ε u)
  rw [fctD_eq] at this ⊢
  have e : |û + u ^ 2 / 4| = |-(u ^ 2 / 4) + -û| := by rw [← abs_neg]; ring_nf
  simpa [e] using this

lemma fctU0_sq {M : ℝ} (hM : 0 ≤ M) : 8 * M ≤ fctU0 M ^ 2 := by
  have h : √(8 * M) ≤ fctU0 M := le_max_right _ _
  have := Real.sq_sqrt (by linarith : 0 ≤ 8 * M)
  nlinarith [Real.sqrt_nonneg (8 * M)]

lemma fctU0_ge_six (M : ℝ) : 6 ≤ fctU0 M := le_max_left _ _

lemma fctD_ne {M û ε u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M - 1 < u) : fctD û ε u ≠ 0 := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have h6 := fctU0_ge_six M
  have hsq := fctU0_sq hM0
  have hu1 : 5 / 6 * fctU0 M < u := by linarith
  have hu2 : (5 / 6 * fctU0 M) ^ 2 < u ^ 2 := pow_lt_pow_left₀ hu1 (by linarith) (by norm_num)
  have h3 : 0 < û + u ^ 2 / 4 := by
    have := neg_le_of_abs_le hM
    nlinarith
  intro h0
  have := fctD_im_le û ε u
  rw [h0, norm_zero, abs_of_pos h3] at this
  linarith

lemma fctD_lower {M û ε u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M ≤ u) : u ^ 2 / 8 ≤ ‖fctD û ε u‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hsq := fctU0_sq hM0
  have h6 := fctU0_ge_six M
  have hu2 : fctU0 M ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by linarith) hu 2
  refine le_trans ?_ (fctD_im_le û ε u)
  have h1 := neg_abs_le û
  have h2 : u ^ 2 / 4 - M ≤ û + u ^ 2 / 4 := by linarith [neg_le_of_abs_le hM]
  rw [le_abs]; left; nlinarith


lemma contDiff_fctD (û ε : ℝ) : ContDiff ℝ ⊤ (fctD û ε) := by
  unfold fctD
  have h : ContDiff ℝ ⊤ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  fun_prop

lemma iteratedDeriv_fctD_norm_le (û ε u : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hu : 4 ≤ u) (j : ℕ) (hj : 1 ≤ j) :
    ‖iteratedDeriv j (fctD û ε) u‖ ≤ u ^ ((2 : ℝ) - j) := by
  have hu0 : 0 < u := by linarith
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  rcases i with _ | _ | i
  · rw [iteratedDeriv_fctD_one]
    simp only [fctD1, Nat.cast_one, Nat.zero_add]
    have e : ((-(2 * ε) : ℝ) : ℂ) + -(Complex.I / 4) * (2 * (u : ℂ)) = ⟨-(2 * ε), -(u / 2)⟩ := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [e]
    have : ‖(⟨-(2 * ε), -(u / 2)⟩ : ℂ)‖ ≤ |-(2 * ε)| + |-(u / 2)| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp
    refine this.trans ?_
    rw [Real.rpow_sub hu0, Real.rpow_two, Real.rpow_one]
    rw [abs_neg, abs_neg, abs_of_nonneg (by linarith : 0 ≤ 2 * ε), abs_of_nonneg (by linarith : 0 ≤ u / 2)]
    rw [show u ^ 2 / u = u by field_simp]
    linarith
  · rw [iteratedDeriv_fctD_two]
    simp only [Nat.cast_ofNat, Nat.reduceAdd, Nat.cast_ofNat]
    norm_num
  · rw [iteratedDeriv_fctD_ge]
    simp only [norm_zero]
    positivity


lemma contDiffAt_fctQ {M û ε u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M - 1 < u) : ContDiffAt ℝ ⊤ (fctQ û ε) u :=
  (contDiff_fctD û ε).contDiffAt.inv (fctD_ne hM hu)

lemma iteratedDeriv_fctQ_rec {M û ε u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M - 1 < u) (m : ℕ) (hm : 1 ≤ m) :
    iteratedDeriv m (fctQ û ε) u = -(fctD û ε u)⁻¹ * ∑ i ∈ Finset.range m,
      (m.choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD û ε) u * iteratedDeriv (m - (i + 1)) (fctQ û ε) u := by
  have hev : (fun x => fctD û ε x * fctQ û ε x) =ᶠ[𝓝 u] fun _ => (1 : ℂ) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    exact mul_inv_cancel₀ (fctD_ne hM hx)
  have h1 : iteratedDeriv m (fun x => fctD û ε x * fctQ û ε x) u = 0 := by
    rw [hev.iteratedDeriv_eq, iteratedDeriv_const]; simp; omega
  rw [iteratedDeriv_fun_mul ((contDiff_fctD û ε).contDiffAt.of_le (by exact_mod_cast le_top))
    ((contDiffAt_fctQ hM hu).of_le (by exact_mod_cast le_top)), Finset.sum_range_succ'] at h1
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, iteratedDeriv_zero, Nat.sub_zero] at h1
  have hD0 : fctD û ε u ≠ 0 := fctD_ne hM hu
  have e : (fctD û ε u)⁻¹ * fctD û ε u = 1 := inv_mul_cancel₀ hD0
  rw [neg_mul, eq_neg_iff_add_eq_zero]
  linear_combination (fctD û ε u)⁻¹ * h1 - (iteratedDeriv m (fctQ û ε) u) * e


lemma fctQ_norm_zero {M û ε u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M ≤ u) :
    ‖fctQ û ε u‖ ≤ 8 * u ^ ((-2 : ℝ) - ((0 : ℕ) : ℝ)) := by
  have h6 := fctU0_ge_six M
  have hu0 : 0 < u := by linarith
  have hl := fctD_lower (ε := ε) hM hu
  have hpos : 0 < u ^ 2 / 8 := by positivity
  simp only [fctQ, norm_inv, Nat.cast_zero, sub_zero]
  rw [Real.rpow_neg hu0.le, Real.rpow_two]
  calc (‖fctD û ε u‖)⁻¹ ≤ (u ^ 2 / 8)⁻¹ := inv_anti₀ hpos hl
    _ = 8 * (u ^ 2)⁻¹ := by field_simp

lemma fctQ_bound (m : ℕ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ (M û ε u : ℝ), |û| ≤ M → 0 ≤ ε → ε ≤ 1 → fctU0 M ≤ u →
    ∀ j ≤ m, ‖iteratedDeriv j (fctQ û ε) u‖ ≤ c * u ^ ((-2 : ℝ) - j) := by
  induction m with
  | zero =>
    refine ⟨8, by norm_num, fun M û ε u hM hε0 hε1 hu j hj => ?_⟩
    obtain rfl : j = 0 := by omega
    simpa using fctQ_norm_zero (ε := ε) hM hu
  | succ m ih =>
    obtain ⟨c, hc0, hc⟩ := ih
    refine ⟨c + 8 * ((m + 1) * 2 ^ (m + 1)) * c, by positivity, fun M û ε u hM hε0 hε1 hu j hj => ?_⟩
    have h6 := fctU0_ge_six M
    have hu0 : 0 < u := by linarith
    have hu4 : 4 ≤ u := by linarith
    rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · refine (hc M û ε u hM hε0 hε1 hu j (by omega)).trans ?_
      have : 0 ≤ 8 * ((m + 1 : ℝ) * 2 ^ (m + 1)) * c := by positivity
      have hp : 0 < u ^ ((-2 : ℝ) - j) := Real.rpow_pos_of_pos hu0 _
      nlinarith
    · obtain rfl : j = m + 1 := by omega
      have hv : fctU0 M - 1 < u := by linarith
      rw [iteratedDeriv_fctQ_rec hM hv (m + 1) (by omega)]
      have hl := fctD_lower (ε := ε) hM hu
      have hDinv : ‖(fctD û ε u)⁻¹‖ ≤ 8 * u ^ ((-2 : ℝ)) := by
        have := fctQ_norm_zero (ε := ε) hM hu
        simpa [fctQ] using this
      rw [norm_mul, norm_neg]
      have hterm : ∀ i ∈ Finset.range (m + 1),
          ‖((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD û ε) u * iteratedDeriv (m + 1 - (i + 1)) (fctQ û ε) u‖
            ≤ (2 ^ (m + 1) : ℝ) * c * u ^ ((-1 : ℝ) - m) := by
        intro i hi
        have him : i ≤ m := by have := Finset.mem_range.1 hi; omega
        have hD1 := iteratedDeriv_fctD_norm_le û ε u hε0 hε1 hu4 (i + 1) (by omega)
        have hQ1 := hc M û ε u hM hε0 hε1 hu (m + 1 - (i + 1)) (by omega)
        have hch : ((m + 1).choose (i + 1) : ℝ) ≤ 2 ^ (m + 1) := by exact_mod_cast Nat.choose_le_two_pow _ _
        rw [norm_mul, norm_mul, Complex.norm_natCast]
        have e : u ^ ((2 : ℝ) - ((i + 1 : ℕ) : ℝ)) * u ^ ((-2 : ℝ) - ((m + 1 - (i + 1) : ℕ) : ℝ)) = u ^ ((-1 : ℝ) - m) := by
          rw [← Real.rpow_add hu0]; congr 1
          rw [show m + 1 - (i + 1) = m - i by omega, Nat.cast_sub him]; push_cast; ring
        calc ((m + 1).choose (i + 1) : ℝ) * ‖iteratedDeriv (i + 1) (fctD û ε) u‖ * ‖iteratedDeriv (m + 1 - (i + 1)) (fctQ û ε) u‖
            ≤ (2 ^ (m + 1) : ℝ) * u ^ ((2 : ℝ) - ((i + 1 : ℕ) : ℝ)) * (c * u ^ ((-2 : ℝ) - ((m + 1 - (i + 1) : ℕ) : ℝ))) := by
              gcongr
          _ = (2 ^ (m + 1) : ℝ) * c * (u ^ ((2 : ℝ) - ((i + 1 : ℕ) : ℝ)) * u ^ ((-2 : ℝ) - ((m + 1 - (i + 1) : ℕ) : ℝ))) := by ring
          _ = _ := by rw [e]
      have hsum := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
      have hp1 : 0 ≤ (2 ^ (m + 1) : ℝ) * c * u ^ ((-1 : ℝ) - m) := by positivity
      calc ‖(fctD û ε u)⁻¹‖ * ‖∑ i ∈ Finset.range (m + 1), ((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD û ε) u * iteratedDeriv (m + 1 - (i + 1)) (fctQ û ε) u‖
          ≤ (8 * u ^ ((-2 : ℝ))) * (((m + 1 : ℕ) : ℝ) * ((2 ^ (m + 1) : ℝ) * c * u ^ ((-1 : ℝ) - m))) :=
            mul_le_mul hDinv hsum (norm_nonneg _) (by positivity)
        _ = 8 * ((m + 1) * 2 ^ (m + 1)) * c * (u ^ ((-2 : ℝ)) * u ^ ((-1 : ℝ) - m)) := by push_cast; ring
        _ = 8 * ((m + 1) * 2 ^ (m + 1)) * c * u ^ ((-2 : ℝ) - ((m + 1 : ℕ) : ℝ)) := by
            rw [← Real.rpow_add hu0]; congr 2; push_cast; ring
        _ ≤ (c + 8 * ((m + 1) * 2 ^ (m + 1)) * c) * u ^ ((-2 : ℝ) - ((m + 1 : ℕ) : ℝ)) := by
            have hp : 0 ≤ u ^ ((-2 : ℝ) - ((m + 1 : ℕ) : ℝ)) := by positivity
            nlinarith


lemma continuous_fctD_eps (û u : ℝ) : Continuous (fun ε : ℝ => fctD û ε u) := by
  unfold fctD
  have h : Continuous (fun ε : ℝ => ((-(2 * ε) : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (by fun_prop)
  fun_prop

lemma continuous_iteratedDeriv_fctD_eps (û u : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Continuous (fun ε : ℝ => iteratedDeriv k (fctD û ε) u) := by
  by_cases h1 : k = 1
  · subst h1
    simp_rw [iteratedDeriv_fctD_one]
    unfold fctD1
    have h : Continuous (fun ε : ℝ => ((-(2 * ε) : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (by fun_prop)
    fun_prop
  by_cases h2 : k = 2
  · subst h2; simp_rw [iteratedDeriv_fctD_two]; exact continuous_const
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 3 := ⟨k - 3, by omega⟩
  simp_rw [iteratedDeriv_fctD_ge]; exact continuous_const

lemma fctQ_cont {M û u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M - 1 < u) (m : ℕ) :
    ∀ j ≤ m, Continuous (fun ε : ℝ => iteratedDeriv j (fctQ û ε) u) := by
  induction m with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by omega
    simp only [iteratedDeriv_zero, fctQ]
    exact (continuous_fctD_eps û u).inv₀ (fun ε => fctD_ne hM hu)
  | succ m ih =>
    intro j hj
    rcases Nat.lt_or_ge j (m + 1) with hjm | hjm
    · exact ih j (by omega)
    · obtain rfl : j = m + 1 := by omega
      have e : (fun ε : ℝ => iteratedDeriv (m + 1) (fctQ û ε) u) = fun ε => -(fctD û ε u)⁻¹ *
          ∑ i ∈ Finset.range (m + 1), ((m + 1).choose (i + 1) : ℂ) * iteratedDeriv (i + 1) (fctD û ε) u *
            iteratedDeriv (m + 1 - (i + 1)) (fctQ û ε) u := by
        funext ε; exact iteratedDeriv_fctQ_rec hM hu (m + 1) (by omega)
      rw [e]
      refine ((continuous_fctD_eps û u).inv₀ (fun ε => fctD_ne hM hu)).neg.mul (continuous_finsetSum _ fun i hi => ?_)
      have him : i ≤ m := by have := Finset.mem_range.1 hi; omega
      exact (continuous_const.mul (continuous_iteratedDeriv_fctD_eps û u (i + 1) (by omega))).mul
        (ih (m + 1 - (i + 1)) (by omega))


/-- One integration by parts for `∫_U^∞ g e^{w}` with a complex phase `w`, `w' = D ≠ 0`, `|e^w| ≤ 1`:
`∫ g e^w = ∫ (-(g/D)') e^w` (boundary terms vanish). -/
lemma ibp_cexp {U : ℝ} {g D w : ℝ → ℂ}
    (hg : ∀ u ∈ Ioi U, DifferentiableAt ℝ g u)
    (hw : ∀ u ∈ Ioi U, HasDerivAt w (D u) u)
    (hD0 : ∀ u ∈ Ioi U, D u ≠ 0) (hDd : ∀ u ∈ Ioi U, DifferentiableAt ℝ D u)
    (hE : ∀ u, ‖Complex.exp (w u)‖ ≤ 1)
    (hg_int : IntegrableOn (fun u => g u * Complex.exp (w u)) (Ioi U))
    (hDg_int : IntegrableOn (fun u => (-deriv (fun s => g s * (D s)⁻¹) u) * Complex.exp (w u)) (Ioi U))
    (hlim_U : Tendsto (fun u => g u * (D u)⁻¹) (𝓝[>] U) (𝓝 0))
    (hlim_top : Tendsto (fun u => g u * (D u)⁻¹ * Complex.exp (w u)) atTop (𝓝 0)) :
    ∫ u in Ioi U, g u * Complex.exp (w u) =
      ∫ u in Ioi U, (-deriv (fun s => g s * (D s)⁻¹) u) * Complex.exp (w u) := by
  set q : ℝ → ℂ := fun u => g u * (D u)⁻¹ with hq
  set E : ℝ → ℂ := fun u => Complex.exp (w u) with hEdef
  have hq_diff : ∀ u ∈ Ioi U, DifferentiableAt ℝ q u := fun u hu =>
    (hg u hu).mul ((hDd u hu).inv (hD0 u hu))
  have hE_deriv : ∀ u ∈ Ioi U, HasDerivAt E (E u * D u) u := fun u hu => (hw u hu).cexp
  have hF_deriv : ∀ u ∈ Ioi U, HasDerivAt (fun s => q s * E s) (deriv q u * E u + g u * E u) u := by
    intro u hu
    have h1 := (hq_diff u hu).hasDerivAt.mul (hE_deriv u hu)
    refine h1.congr_deriv ?_
    have : q u * (E u * D u) = g u * E u := by
      simp only [hq]
      field_simp [hD0 u hu]
    rw [this]
  have hIoi_a : ∀ a ∈ Ioi U,
      (∫ u in Ioi a, deriv q u * E u) + (∫ u in Ioi a, g u * E u) = -(q a * E a) := by
    intro a ha
    have hsub : Ioi a ⊆ Ioi U := fun u hu => (lt_trans ha hu : U < u)
    have hg_a : IntegrableOn (fun u => g u * E u) (Ioi a) := hg_int.mono_set hsub
    have hq'_a : IntegrableOn (fun u => deriv q u * E u) (Ioi a) := by
      have := (hDg_int.mono_set hsub).neg
      refine this.congr_fun (fun u _ => by simp only [Pi.neg_apply, q, E, neg_mul, neg_neg]) measurableSet_Ioi
    have hsum_a : IntegrableOn (fun u => deriv q u * E u + g u * E u) (Ioi a) := hq'_a.add hg_a
    have hFTC : ∀ b : ℝ, a ≤ b →
        ∫ u in a..b, (deriv q u * E u + g u * E u) = q b * E b - q a * E a := by
      intro b hab
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun s => q s * E s) (f' := fun u => deriv q u * E u + g u * E u)
        (fun u hu => ?_) ?_
      · rw [uIcc_of_le hab] at hu
        exact hF_deriv u (lt_of_lt_of_le ha hu.1)
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
          (hsum_a.mono_set Ioc_subset_Ioi_self)
    have hlim_int : Tendsto (fun b : ℝ => ∫ u in a..b, (deriv q u * E u + g u * E u)) atTop
        (𝓝 (∫ u in Ioi a, (deriv q u * E u + g u * E u))) :=
      intervalIntegral_tendsto_integral_Ioi a hsum_a tendsto_id
    have hlim_rhs : Tendsto (fun b : ℝ => q b * E b - q a * E a) atTop (𝓝 (-(q a * E a))) := by
      simpa using hlim_top.sub_const (q a * E a)
    have heq_sum : ∫ u in Ioi a, (deriv q u * E u + g u * E u) = -(q a * E a) := by
      refine tendsto_nhds_unique hlim_int (hlim_rhs.congr' ?_)
      filter_upwards [eventually_ge_atTop a] with b hab
      exact (hFTC b hab).symm
    rw [← heq_sum, integral_add hq'_a hg_a]
  have hlim_lhs : Tendsto (fun a : ℝ => (∫ u in Ioi a, deriv q u * E u) + (∫ u in Ioi a, g u * E u))
      (𝓝[>] U) (𝓝 ((∫ u in Ioi U, deriv q u * E u) + (∫ u in Ioi U, g u * E u))) := by
    have hq'_r : IntegrableOn (fun u => deriv q u * E u) (Ioi U) := by
      have := hDg_int.neg
      refine this.congr_fun (fun u _ => by simp only [Pi.neg_apply, q, E, neg_mul, neg_neg]) measurableSet_Ioi
    exact (FctEdgeIbp.tendsto_setIntegral_Ioi_right hq'_r).add (FctEdgeIbp.tendsto_setIntegral_Ioi_right hg_int)
  have hlim_rhs : Tendsto (fun a : ℝ => -(q a * E a)) (𝓝[>] U) (𝓝 0) := by
    have h0 : Tendsto (fun a : ℝ => q a * E a) (𝓝[>] U) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun a => norm_nonneg _) (fun a => ?_) (tendsto_zero_iff_norm_tendsto_zero.mp hlim_U)
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hE a)
    simpa using h0.neg
  have hsum_zero : (∫ u in Ioi U, deriv q u * E u) + (∫ u in Ioi U, g u * E u) = 0 := by
    refine tendsto_nhds_unique hlim_lhs (hlim_rhs.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact (hIoi_a a ha).symm
  have hneg : ∫ u in Ioi U, (-deriv q u) * E u = -(∫ u in Ioi U, deriv q u * E u) := by
    simp_rw [neg_mul]
    exact integral_neg _
  rw [show (fun u => (-deriv (fun s => g s * (D s)⁻¹) u) * Complex.exp (w u)) = fun u => (-deriv q u) * E u from rfl, hneg]
  exact eq_neg_of_add_eq_zero_right hsum_zero


lemma continuous_fctW_eps (û u : ℝ) : Continuous (fun ε : ℝ => fctW û ε u) := by
  unfold fctW
  have h : Continuous (fun ε : ℝ => ((ε * u ^ 2 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (by fun_prop)
  fun_prop

lemma continuous_fctW (û ε : ℝ) : Continuous (fctW û ε) := by
  unfold fctW
  have h1 : Continuous (fun u : ℝ => ((û * u + u ^ 3 / 12 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (by fun_prop)
  have h2 : Continuous (fun u : ℝ => ((ε * u ^ 2 : ℝ) : ℂ)) := Complex.continuous_ofReal.comp (by fun_prop)
  fun_prop

lemma norm_exp_fctW (û ε u : ℝ) : ‖Complex.exp (fctW û ε u)‖ = Real.exp (-(ε * u ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [fctW, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma norm_exp_fctW_le {û ε : ℝ} (hε : 0 ≤ ε) (u : ℝ) : ‖Complex.exp (fctW û ε u)‖ ≤ 1 := by
  rw [norm_exp_fctW]
  exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg u])

/-- Integrability of `g e^{w_ε}` on `(U, ∞)` for polynomially bounded continuous `g` and `ε > 0`. -/
lemma integrableOn_amp {û ε U σ A : ℝ} {g : ℝ → ℂ} (hU : 1 ≤ U) (hε : 0 < ε) (hg : ContinuousOn g (Ioi U))
    (hb : ∀ u, U ≤ u → ‖g u‖ ≤ A * u ^ σ) :
    IntegrableOn (fun u => g u * Complex.exp (fctW û ε u)) (Ioi U) := by
  have hint : IntegrableOn (fun x : ℝ => x ^ (max σ 0) * Real.exp (-ε * x ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hε (by have := le_max_right σ 0; linarith)
  have hint' := (hint.mono_set (Ioi_subset_Ioi (by linarith : (0 : ℝ) ≤ U))).const_mul A
  refine Integrable.mono' hint' ?_ ?_
  · exact (hg.mul (continuous_fctW û ε).cexp.continuousOn).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
    have hu1 : 1 ≤ u := by have : U < u := hu; linarith
    rw [norm_mul, norm_exp_fctW]
    have h1 : ‖g u‖ ≤ A * u ^ (max σ 0) := by
      refine (hb u hu.le).trans ?_
      have hA : 0 ≤ A := by
        have := (norm_nonneg (g u)).trans (hb u hu.le)
        have hp : 0 < u ^ σ := Real.rpow_pos_of_pos (by linarith) _
        by_contra hneg; push Not at hneg; nlinarith
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hu1 (le_max_left _ _)) hA
    have e : Real.exp (-(ε * u ^ 2)) = Real.exp (-ε * u ^ 2) := by ring_nf
    rw [e]
    calc ‖g u‖ * Real.exp (-ε * u ^ 2) ≤ (A * u ^ (max σ 0)) * Real.exp (-ε * u ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = A * (u ^ (max σ 0) * Real.exp (-ε * u ^ 2)) := by ring

lemma tendsto_amp_top {û ε U σ A : ℝ} {g : ℝ → ℂ} (hε : 0 < ε) (hb : ∀ u, U ≤ u → ‖g u‖ ≤ A * u ^ σ) :
    Tendsto (fun u => g u * Complex.exp (fctW û ε u)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun x : ℝ => A * (x ^ σ * Real.exp (-ε * x))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero σ ε hε).const_mul A
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun u => norm_nonneg _) ?_ h0
  filter_upwards [eventually_ge_atTop (max U 1)] with u hu
  have hu1 : 1 ≤ u := (le_max_right _ _).trans hu
  have hUu : U ≤ u := (le_max_left _ _).trans hu
  rw [norm_mul, norm_exp_fctW]
  have hA : 0 ≤ A := by
    have := (norm_nonneg (g u)).trans (hb u hUu)
    have hp : 0 < u ^ σ := Real.rpow_pos_of_pos (by linarith) _
    by_contra hneg; push Not at hneg; nlinarith
  have e : Real.exp (-(ε * u ^ 2)) ≤ Real.exp (-ε * u) := by
    apply Real.exp_le_exp.2
    nlinarith [mul_nonneg (mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ u)) (by linarith : (0 : ℝ) ≤ u - 1)]
  calc ‖g u‖ * Real.exp (-(ε * u ^ 2)) ≤ (A * u ^ σ) * Real.exp (-ε * u) :=
        mul_le_mul (hb u hUu) e (Real.exp_pos _).le (by positivity)
    _ = A * (u ^ σ * Real.exp (-ε * u)) := by ring


/-! ### The operator `𝒟_ε g = -(g Q_ε)'` and symbol families -/

/-- `𝒟_ε g = -(g/D_ε)'`. -/
noncomputable def fctDop (û ε : ℝ) (g : ℝ → ℂ) : ℝ → ℂ := fun u => -deriv (fun s => g s * fctQ û ε s) u

/-- Symbol bound on `[U, ∞)`: `‖g^{(r)}(u)‖ ≤ A u^{q - r}` for `r ≤ n`. -/
def SBd (n : ℕ) (U q A : ℝ) (f : ℝ → ℂ) : Prop :=
  ∀ r : ℕ, r ≤ n → ∀ u : ℝ, U ≤ u → ‖iteratedDeriv r f u‖ ≤ A * u ^ (q - r)

/-- A family `h_ε` (`ε ∈ [0, 1]`) of `C^n` amplitudes on `(V, ∞)` vanishing on `(V, U)`, with uniform symbol bounds on `[U, ∞)` of order `q` and constant `A`,
whose derivatives of order `≤ n` converge as `ε ↓ 0`. -/
structure Fam (V U : ℝ) (n : ℕ) (q A : ℝ) (h : ℝ → ℝ → ℂ) : Prop where
  smooth : ∀ ε ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ n (h ε) (Ioi V)
  zero : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ u, V < u → u < U → h ε u = 0
  bound : ∀ ε ∈ Icc (0 : ℝ) 1, SBd n U q A (h ε)
  cont : ∀ r : ℕ, r ≤ n → ∀ u, V < u →
    Tendsto (fun ε => iteratedDeriv r (h ε) u) (𝓝[>] 0) (𝓝 (iteratedDeriv r (h 0) u))

lemma iteratedDeriv_fctDop {M û ε u : ℝ} (hM : |û| ≤ M) (hu : fctU0 M - 1 < u) {g : ℝ → ℂ} (r : ℕ)
    (hg : ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) g u) :
    iteratedDeriv r (fctDop û ε g) u = -∑ k ∈ Finset.range (r + 2),
      ((r + 1).choose k : ℂ) * iteratedDeriv k g u * iteratedDeriv (r + 1 - k) (fctQ û ε) u := by
  have h1 : fctDop û ε g = fun u => -(deriv (fun s => g s * fctQ û ε s) u) := rfl
  rw [h1, iteratedDeriv_fun_neg, ← iteratedDeriv_succ', iteratedDeriv_fun_mul hg
    ((contDiffAt_fctQ hM hu).of_le (by exact_mod_cast le_top))]


lemma contDiffOn_fctQ {M û ε V : ℝ} (hM : |û| ≤ M) (hV : V = fctU0 M - 1) :
    ContDiffOn ℝ ⊤ (fctQ û ε) (Ioi V) := fun u hu =>
  (contDiffAt_fctQ hM (by rw [← hV]; exact hu)).contDiffWithinAt

/-- One integration by parts at the level of families: `𝒟_ε` maps a `C^{n+1}` symbol family of order `q` to a `C^n` family of order `q - 3`. -/
lemma fam_step (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (M û V U q A : ℝ) (h : ℝ → ℝ → ℂ), |û| ≤ M → V = fctU0 M - 1 →
    fctU0 M ≤ U → Fam V U (n + 1) q A h → Fam V U n (q - 3) (K * A) (fun ε => fctDop û ε (h ε)) := by
  obtain ⟨c, hc0, hc⟩ := fctQ_bound (n + 1)
  refine ⟨2 ^ (n + 1) * c, by positivity, fun M û V U q A h hM hV hU hF => ?_⟩
  have h6 := fctU0_ge_six M
  have hU0 : 0 < U := by linarith
  have hA0 : 0 ≤ A := by
    have h1 := hF.bound 0 (by simp) 0 (by norm_num) U (by linarith)
    simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1
    have hp : 0 < U ^ q := Real.rpow_pos_of_pos hU0 _
    by_contra hneg; push Not at hneg
    nlinarith [norm_nonneg (h 0 U)]
  have hVu : ∀ u, U ≤ u → fctU0 M - 1 < u := fun u hu => by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ε hε
    have hF1 : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun s => h ε s * fctQ û ε s) (Ioi V) :=
      (hF.smooth ε hε).mul ((contDiffOn_fctQ hM hV (ε := ε)).of_le (by exact_mod_cast le_top))
    have := (hF1.deriv_of_isOpen isOpen_Ioi (m := (n : WithTop ℕ∞)) (by norm_cast)).neg
    exact this
  · intro ε hε u hVu' huU
    have hev : (fun s => h ε s * fctQ û ε s) =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [Ioo_mem_nhds hVu' huU] with s hs
      rw [hF.zero ε hε s hs.1 hs.2]; simp
    show -deriv (fun s => h ε s * fctQ û ε s) u = 0
    rw [hev.deriv_eq]; simp
  · intro ε hε r hr u hu
    have hu' : fctU0 M - 1 < u := hVu u hu
    have hcd : ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (h ε) u :=
      ((hF.smooth ε hε).contDiffAt (Ioi_mem_nhds (by rw [hV]; exact hu'))).of_le (by exact_mod_cast Nat.succ_le_succ hr)
    rw [iteratedDeriv_fctDop hM hu' r hcd, norm_neg]
    have hu0 : 0 < u := by linarith
    have hterm : ∀ k ∈ Finset.range (r + 2), ‖((r + 1).choose k : ℂ) * iteratedDeriv k (h ε) u *
        iteratedDeriv (r + 1 - k) (fctQ û ε) u‖ ≤ ((r + 1).choose k : ℝ) * (A * c) * u ^ ((q - 3) - (r : ℝ)) := by
      intro k hk
      have hkr : k ≤ r + 1 := by have := Finset.mem_range.1 hk; omega
      have h1 := hF.bound ε hε k (by omega) u hu
      have h2 := hc M û ε u hM hε.1 hε.2 (by linarith) (r + 1 - k) (by omega)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have e : u ^ (q - (k : ℝ)) * u ^ ((-2 : ℝ) - ((r + 1 - k : ℕ) : ℝ)) = u ^ ((q - 3) - (r : ℝ)) := by
        rw [← Real.rpow_add hu0]; congr 1
        rw [Nat.cast_sub hkr]; push_cast; ring
      calc ((r + 1).choose k : ℝ) * ‖iteratedDeriv k (h ε) u‖ * ‖iteratedDeriv (r + 1 - k) (fctQ û ε) u‖
          ≤ ((r + 1).choose k : ℝ) * (A * u ^ (q - (k : ℝ))) * (c * u ^ ((-2 : ℝ) - ((r + 1 - k : ℕ) : ℝ))) := by
            gcongr
        _ = ((r + 1).choose k : ℝ) * (A * c) * (u ^ (q - (k : ℝ)) * u ^ ((-2 : ℝ) - ((r + 1 - k : ℕ) : ℝ))) := by ring
        _ = _ := by rw [e]
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hsum : ∑ k ∈ Finset.range (r + 2), ((r + 1).choose k : ℝ) = 2 ^ (r + 1) := by
      exact_mod_cast Nat.sum_range_choose (r + 1)
    rw [hsum]
    have hp : 0 ≤ u ^ ((q - 3) - (r : ℝ)) := by positivity
    have h2 : (2 : ℝ) ^ (r + 1) ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have hAc : 0 ≤ A * c := mul_nonneg hA0 hc0
    calc (2 : ℝ) ^ (r + 1) * (A * c) * u ^ ((q - 3) - (r : ℝ)) ≤ 2 ^ (n + 1) * (A * c) * u ^ ((q - 3) - (r : ℝ)) := by gcongr
      _ = _ := by ring
  · intro r hr u hu
    have hu' : fctU0 M - 1 < u := by rw [hV] at hu; exact hu
    have hcdε : ∀ ε ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (h ε) u := fun ε hε =>
      ((hF.smooth ε hε).contDiffAt (Ioi_mem_nhds hu)).of_le (by exact_mod_cast Nat.succ_le_succ hr)
    have hlim : Tendsto (fun ε => -∑ k ∈ Finset.range (r + 2),
        ((r + 1).choose k : ℂ) * iteratedDeriv k (h ε) u * iteratedDeriv (r + 1 - k) (fctQ û ε) u) (𝓝[>] 0)
        (𝓝 (-∑ k ∈ Finset.range (r + 2),
        ((r + 1).choose k : ℂ) * iteratedDeriv k (h 0) u * iteratedDeriv (r + 1 - k) (fctQ û 0) u)) := by
      refine (tendsto_finsetSum _ fun k hk => ?_).neg
      have hkr : k ≤ r + 1 := by have := Finset.mem_range.1 hk; omega
      refine (tendsto_const_nhds.mul (hF.cont k (by omega) u hu)).mul ?_
      exact ((fctQ_cont hM hu' (n + 1) (r + 1 - k) (by omega)).tendsto 0).mono_left nhdsWithin_le_nhds
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    have hlim' := hlim.congr' (by
      filter_upwards [hmem] with ε hε
      exact (iteratedDeriv_fctDop hM hu' r (hcdε ε ⟨hε.1.le, hε.2.le⟩)).symm)
    rw [iteratedDeriv_fctDop hM hu' r (hcdε 0 ⟨le_rfl, zero_le_one⟩)]
    exact hlim'


lemma Fam.zero_at {V U : ℝ} {n : ℕ} {q A : ℝ} {h : ℝ → ℝ → ℂ} (hF : Fam V U n q A h) (hVU : V < U) {ε : ℝ}
    (hε : ε ∈ Icc (0 : ℝ) 1) : h ε U = 0 := by
  have hc : ContinuousAt (h ε) U :=
    ((hF.smooth ε hε).continuousOn).continuousAt (Ioi_mem_nhds hVU)
  have h1 : Tendsto (h ε) (𝓝[<] U) (𝓝 (h ε U)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (h ε) (𝓝[<] U) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hVU] with u hu
    exact (hF.zero ε hε u hu.1 hu.2).symm
  exact tendsto_nhds_unique h1 h2

lemma Fam.A_nonneg {V U : ℝ} {n : ℕ} {q A : ℝ} {h : ℝ → ℝ → ℂ} (hF : Fam V U n q A h) (hU : 0 < U) : 0 ≤ A := by
  have h1 := hF.bound 0 ⟨le_rfl, zero_le_one⟩ 0 (Nat.zero_le _) U le_rfl
  simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1
  have hp : 0 < U ^ q := Real.rpow_pos_of_pos hU _
  by_contra hneg; push Not at hneg
  nlinarith [norm_nonneg (h 0 U)]

/-- The main induction: a `C^n` symbol family of order `q < 3n - 1` has an Abel limit of `∫ h_ε e^{w_ε}`, bounded by `C A U^{q+1-3n}`. -/
theorem fam_main (M : ℝ) : ∀ n : ℕ, ∀ q : ℝ, q < 3 * n - 1 → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (û V U A : ℝ) (h : ℝ → ℝ → ℂ), |û| ≤ M → V = fctU0 M - 1 → fctU0 M ≤ U → Fam V U n q A h →
      ∃ R : ℂ, Tendsto (fun ε => ∫ u in Ioi U, h ε u * Complex.exp (fctW û ε u)) (𝓝[>] 0) (𝓝 R) ∧
        ‖R‖ ≤ C * A * U ^ (q + 1 - 3 * (n : ℝ)) := by
  intro n
  induction n with
  | zero =>
    intro q hq
    have hq' : q < -1 := by simpa using hq
    refine ⟨1 / (-q - 1), by apply div_nonneg zero_le_one; linarith, fun û V U A h hM hV hU hF => ?_⟩
    have h6 := fctU0_ge_six M
    have hU0 : 0 < U := by linarith
    have hA0 := hF.A_nonneg hU0
    have hbd : ∀ ε ∈ Icc (0 : ℝ) 1, ∀ u, U ≤ u → ‖h ε u‖ ≤ A * u ^ q := fun ε hε u hu => by
      simpa using hF.bound ε hε 0 le_rfl u hu
    have hint : IntegrableOn (fun u : ℝ => A * u ^ q) (Ioi U) := (integrableOn_Ioi_rpow_of_lt hq' hU0).const_mul A
    have hmeas : ∀ ε ∈ Icc (0 : ℝ) 1, ContinuousOn (h ε) (Ioi U) := fun ε hε =>
      ((hF.smooth ε hε).continuousOn).mono (Ioi_subset_Ioi (by linarith))
    have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    refine ⟨∫ u in Ioi U, h 0 u * Complex.exp (fctW û 0 u), ?_, ?_⟩
    · refine tendsto_integral_filter_of_dominated_convergence (fun u => A * u ^ q) ?_ ?_ hint ?_
      · filter_upwards [hmem] with ε hε
        exact ((hmeas ε ⟨hε.1.le, hε.2.le⟩).mul (continuous_fctW û ε).cexp.continuousOn).aestronglyMeasurable
          measurableSet_Ioi
      · filter_upwards [hmem] with ε hε
        refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le hε.1.le u)).trans (hbd ε ⟨hε.1.le, hε.2.le⟩ u (le_of_lt hu))
      · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun u hu => ?_)
        have hu' : V < u := by rw [hV]; have : U < u := hu; linarith
        have h1 : Tendsto (fun ε => h ε u) (𝓝[>] 0) (𝓝 (h 0 u)) := by
          simpa using hF.cont 0 le_rfl u hu'
        have h2 : Tendsto (fun ε : ℝ => Complex.exp (fctW û ε u)) (𝓝[>] 0) (𝓝 (Complex.exp (fctW û 0 u))) :=
          (((continuous_fctW_eps û u).cexp).tendsto 0).mono_left nhdsWithin_le_nhds
        exact h1.mul h2
    · have hg : ∀ u ∈ Ioi U, ‖h 0 u * Complex.exp (fctW û 0 u)‖ ≤ A * u ^ q := fun u hu => by
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le le_rfl u)).trans
          (hbd 0 ⟨le_rfl, zero_le_one⟩ u (le_of_lt hu))
      refine (norm_integral_le_of_norm_le hint ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hg))).trans ?_
      rw [integral_const_mul, integral_Ioi_rpow_of_lt hq' hU0]
      have : -U ^ (q + 1) / (q + 1) = (1 / (-q - 1)) * U ^ (q + 1) := by
        have h1 : q + 1 ≠ 0 := by linarith
        have h2 : -q - 1 = -(q + 1) := by ring
        rw [h2, one_div, inv_neg, neg_mul, inv_mul_eq_div, neg_div]
      rw [this]
      simp only [Nat.cast_zero, mul_zero, sub_zero]
      apply le_of_eq; ring
  | succ n ih =>
    intro q hq
    obtain ⟨C', hC'0, hC'⟩ := ih (q - 3) (by push_cast at hq; linarith)
    obtain ⟨K, hK0, hK⟩ := fam_step n
    refine ⟨C' * K, mul_nonneg hC'0 hK0, fun û V U A h hM hV hU hF => ?_⟩
    have h6 := fctU0_ge_six M
    have hU0 : 0 < U := by linarith
    have hVU : V < U := by rw [hV]; linarith
    have hF' := hK M û V U q A h hM hV hU hF
    obtain ⟨R, hR, hRb⟩ := hC' û V U (K * A) _ hM hV hU hF'
    refine ⟨R, ?_, ?_⟩
    · refine hR.congr' ?_
      have hmem : Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [hmem] with ε hε
      have hε' : ε ∈ Icc (0 : ℝ) 1 := ⟨hε.1.le, hε.2.le⟩
      have hA0 := hF.A_nonneg hU0
      symm
      refine ibp_cexp (U := U) (g := h ε) (D := fctD û ε) (w := fctW û ε) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · intro u hu
        have : V < u := lt_trans hVU hu
        exact (((hF.smooth ε hε').contDiffAt (Ioi_mem_nhds this)).differentiableAt (by exact_mod_cast Nat.succ_ne_zero n))
      · intro u hu; exact hasDerivAt_fctW û ε u
      · intro u hu; exact fctD_ne hM (by have : U < u := hu; linarith)
      · intro u hu; exact (hasDerivAt_fctD û ε u).differentiableAt
      · exact norm_exp_fctW_le hε.1.le
      · refine integrableOn_amp (σ := q) (A := A) (by linarith) hε.1 ((hF.smooth ε hε').continuousOn.mono (Ioi_subset_Ioi hVU.le)) ?_
        intro u hu; simpa using hF.bound ε hε' 0 (Nat.zero_le _) u hu
      · refine integrableOn_amp (σ := q - 3) (A := K * A) (by linarith) hε.1
          ((hF'.smooth ε hε').continuousOn.mono (Ioi_subset_Ioi hVU.le)) ?_
        intro u hu; simpa [fctDop, fctQ] using hF'.bound ε hε' 0 (Nat.zero_le _) u hu
      · have hc1 : ContinuousAt (fun u => h ε u * fctQ û ε u) U := by
          refine ContinuousAt.mul ((hF.smooth ε hε').continuousOn.continuousAt (Ioi_mem_nhds hVU)) ?_
          exact (contDiffAt_fctQ hM (by linarith)).continuousAt
        have := hc1.tendsto
        rw [hF.zero_at hVU hε', zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · refine tendsto_amp_top (σ := q - 2) (A := 8 * A) (U := U) (g := fun u => h ε u * (fctD û ε u)⁻¹) hε.1 ?_
        intro u hu
        have hu0 : 0 < u := by linarith
        have h1 := hF.bound ε hε' 0 (Nat.zero_le _) u hu
        have h2 := fctQ_norm_zero (ε := ε) hM (by linarith : fctU0 M ≤ u)
        simp only [iteratedDeriv_zero, Nat.cast_zero, sub_zero] at h1 h2
        rw [norm_mul]
        calc ‖h ε u‖ * ‖(fctD û ε u)⁻¹‖ ≤ (A * u ^ q) * (8 * u ^ (-2 : ℝ)) :=
              mul_le_mul h1 (by simpa [fctQ] using h2) (norm_nonneg _) (by positivity)
          _ = 8 * A * u ^ (q - 2) := by
              rw [show q - 2 = q + (-2) by ring, Real.rpow_add hu0]; ring
    · refine hRb.trans ?_
      have e : (q - 3) + 1 - 3 * (n : ℝ) = q + 1 - 3 * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      apply le_of_eq; ring


/-! ### Symbol calculus on `[U, ∞)` -/

lemma SBd.A_nonneg {n : ℕ} {U q A : ℝ} {f : ℝ → ℂ} (hU : 0 < U) (h : SBd n U q A f) : 0 ≤ A := by
  have h1 := h 0 (Nat.zero_le _) U le_rfl
  have hp : 0 < U ^ (q - ((0 : ℕ) : ℝ)) := Real.rpow_pos_of_pos hU _
  by_contra hneg; push Not at hneg
  nlinarith [norm_nonneg (iteratedDeriv 0 f U)]

lemma SBd.mul {V U : ℝ} (hVU : V < U) (hU : 0 < U) {n : ℕ} {q1 q2 A1 A2 : ℝ} {f g : ℝ → ℂ}
    (hf : ContDiffOn ℝ n f (Ioi V)) (hg : ContDiffOn ℝ n g (Ioi V))
    (h1 : SBd n U q1 A1 f) (h2 : SBd n U q2 A2 g) :
    SBd n U (q1 + q2) (2 ^ n * A1 * A2) (fun u => f u * g u) := by
  have hA1 := h1.A_nonneg hU
  have hA2 := h2.A_nonneg hU
  intro r hr u hu
  have hu0 : 0 < u := by linarith
  have hVu : V < u := by linarith
  rw [iteratedDeriv_fun_mul (((hf.contDiffAt (Ioi_mem_nhds hVu))).of_le (by exact_mod_cast hr))
    (((hg.contDiffAt (Ioi_mem_nhds hVu))).of_le (by exact_mod_cast hr))]
  have hterm : ∀ i ∈ Finset.range (r + 1), ‖(r.choose i : ℂ) * iteratedDeriv i f u * iteratedDeriv (r - i) g u‖ ≤
      (r.choose i : ℝ) * (A1 * A2) * u ^ (q1 + q2 - (r : ℝ)) := by
    intro i hi
    have hir : i ≤ r := by have := Finset.mem_range.1 hi; omega
    have e1 := h1 i (by omega) u hu
    have e2 := h2 (r - i) (by omega) u hu
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    have e : u ^ (q1 - (i : ℝ)) * u ^ (q2 - ((r - i : ℕ) : ℝ)) = u ^ (q1 + q2 - (r : ℝ)) := by
      rw [← Real.rpow_add hu0]; congr 1; rw [Nat.cast_sub hir]; ring
    calc (r.choose i : ℝ) * ‖iteratedDeriv i f u‖ * ‖iteratedDeriv (r - i) g u‖
        ≤ (r.choose i : ℝ) * (A1 * u ^ (q1 - (i : ℝ))) * (A2 * u ^ (q2 - ((r - i : ℕ) : ℝ))) := by gcongr
      _ = (r.choose i : ℝ) * (A1 * A2) * (u ^ (q1 - (i : ℝ)) * u ^ (q2 - ((r - i : ℕ) : ℝ))) := by ring
      _ = _ := by rw [e]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) = 2 ^ r := by exact_mod_cast Nat.sum_range_choose r
  rw [hsum]
  have hp : 0 ≤ u ^ (q1 + q2 - (r : ℝ)) := by positivity
  have h2' : (2 : ℝ) ^ r ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hr
  have hAA : 0 ≤ A1 * A2 := mul_nonneg hA1 hA2
  calc (2 : ℝ) ^ r * (A1 * A2) * u ^ (q1 + q2 - (r : ℝ)) ≤ 2 ^ n * (A1 * A2) * u ^ (q1 + q2 - (r : ℝ)) := by gcongr
    _ = _ := by ring

lemma SBd.mono_q_A {n : ℕ} {U q A A' : ℝ} {f : ℝ → ℂ} (h : SBd n U q A f) (hA : A ≤ A') (hU : 1 ≤ U) :
    SBd n U q A' f := fun r hr u hu =>
  (h r hr u hu).trans (mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg (by linarith) _))


lemma norm_iteratedDeriv_ofReal (f : ℝ → ℝ) (r : ℕ) (x : ℝ) (hf : ContDiffAt ℝ r f x) :
    ‖iteratedDeriv r (fun u => ((f u : ℝ) : ℂ)) x‖ = ‖iteratedDeriv r f x‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left hf le_rfl

lemma SBd.mono_U {n : ℕ} {U U' q A : ℝ} {f : ℝ → ℂ} (h : SBd n U q A f) (hU : U ≤ U') : SBd n U' q A f :=
  fun r hr u hu => h r hr u (hU.trans hu)

/-- Bounds on the derivatives of the smooth step. -/
lemma smoothTransition_bound (n : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ r : ℕ, r ≤ n → ∀ x : ℝ, ‖iteratedDeriv r Real.smoothTransition x‖ ≤ K := by
  have hcont : ∀ r : ℕ, Continuous (iteratedDeriv r Real.smoothTransition) := fun r => by
    rw [iteratedDeriv_eq_iterate]; exact (Real.smoothTransition.contDiff.iterate_deriv r).continuous
  have hb : ∀ r : ℕ, ∃ K : ℝ, ∀ x : ℝ, ‖iteratedDeriv r Real.smoothTransition x‖ ≤ K := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · refine ⟨1, fun x => ?_⟩
      simp only [iteratedDeriv_zero, Real.norm_eq_abs]
      rw [abs_of_nonneg (Real.smoothTransition.nonneg x)]; exact Real.smoothTransition.le_one x
    · obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn (hcont r).continuousOn
      refine ⟨max K 0, fun x => ?_⟩
      by_cases hx : x ∈ Icc (0 : ℝ) 1
      · exact (hK x hx).trans (le_max_left _ _)
      · rw [Set.mem_Icc, not_and_or] at hx
        obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
        rcases hx with hx | hx
        · have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
            filter_upwards [Iio_mem_nhds (not_le.mp hx)] with y hy using Real.smoothTransition.zero_of_nonpos hy.le
          rw [hev.iteratedDeriv_eq, iteratedDeriv_succ']; simp
        · have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
            filter_upwards [Ioi_mem_nhds (not_le.mp hx)] with y hy using Real.smoothTransition.one_of_one_le hy.le
          rw [hev.iteratedDeriv_eq, iteratedDeriv_succ']; simp
  choose K hK using hb
  refine ⟨1 + ∑ i ∈ Finset.range (n + 1), |K i|, ?_, fun r hr x => ?_⟩
  · have : 0 ≤ ∑ i ∈ Finset.range (n + 1), |K i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  · have h1 : |K r| ≤ ∑ j ∈ Finset.range (n + 1), |K j| :=
      Finset.single_le_sum (f := fun j => |K j|) (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))
    linarith [hK r x, le_abs_self (K r)]

lemma smoothTransition_zero_deriv {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx : 1 < x) :
    iteratedDeriv r Real.smoothTransition x = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 := ⟨r - 1, by omega⟩
  have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using Real.smoothTransition.one_of_one_le hy.le
  rw [hev.iteratedDeriv_eq, iteratedDeriv_succ']; simp

/-- The cutoff `s(u) = smoothTransition(u - U₀)`, `0` for `u ≤ U₀`, `1` for `u ≥ U₀ + 1`. -/
noncomputable def fctStep (U₀ u : ℝ) : ℂ := ((Real.smoothTransition (u - U₀) : ℝ) : ℂ)

lemma contDiff_fctStep (U₀ : ℝ) : ContDiff ℝ ∞ (fctStep U₀) := by
  unfold fctStep
  exact Complex.ofRealCLM.contDiff.comp ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const))

lemma fctStep_sbd (n : ℕ) {U₀ : ℝ} (hU₀ : 1 ≤ U₀) : ∃ A : ℝ, 1 ≤ A ∧ SBd n U₀ 0 A (fctStep U₀) := by
  obtain ⟨K, hK1, hK⟩ := smoothTransition_bound n
  have hP : (1 : ℝ) ≤ (U₀ + 2) ^ n := one_le_pow₀ (by linarith)
  refine ⟨K * (U₀ + 2) ^ n, by nlinarith, fun r hr u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hcd : ContDiffAt ℝ r (fun x => Real.smoothTransition (x - U₀)) u :=
    ((Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)).contDiffAt.of_le (by exact_mod_cast le_top)
  have e : ‖iteratedDeriv r (fctStep U₀) u‖ = ‖iteratedDeriv r Real.smoothTransition (u - U₀)‖ := by
    unfold fctStep
    rw [norm_iteratedDeriv_ofReal _ r u hcd, iteratedDeriv_comp_sub_const]
  rw [e]
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · simp only [Nat.cast_zero, sub_zero, Real.rpow_zero, mul_one]
    exact (hK 0 (Nat.zero_le _) _).trans (by nlinarith)
  · rcases le_or_gt u (U₀ + 2) with hle | hgt
    · have h1 : u ^ r ≤ (U₀ + 2) ^ r := pow_le_pow_left₀ hu0.le hle r
      have h2 : (U₀ + 2) ^ r ≤ (U₀ + 2) ^ n := pow_le_pow_right₀ (by linarith) hr
      have hp : 0 < u ^ (0 - (r : ℝ)) := Real.rpow_pos_of_pos hu0 _
      have e2 : u ^ (0 - (r : ℝ)) = (u ^ r)⁻¹ := by rw [zero_sub, Real.rpow_neg hu0.le, Real.rpow_natCast]
      rw [e2]
      refine (hK r hr _).trans ?_
      have hur : 0 < u ^ r := pow_pos hu0 r
      have key : 1 ≤ (U₀ + 2) ^ n / u ^ r := by rw [le_div_iff₀ hur]; linarith
      calc K = K * 1 := by ring
        _ ≤ K * ((U₀ + 2) ^ n / u ^ r) := by gcongr
        _ = K * (U₀ + 2) ^ n * (u ^ r)⁻¹ := by rw [div_eq_mul_inv]; ring
    · rw [smoothTransition_zero_deriv hr0 (by linarith)]
      simp only [norm_zero]; positivity


/-- `ρ(u) = u^{-1/2}` as a complex-valued function. -/
noncomputable def fctRho (u : ℝ) : ℂ := ((u ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)

lemma contDiffOn_fctRho (n : ℕ) : ContDiffOn ℝ n fctRho (Ioi 0) := by
  intro u hu
  have h : ContDiffAt ℝ n (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) u :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hu)
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp u h).contDiffWithinAt

lemma fctRho_sbd (n : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ SBd n 1 (-(1 / 2)) A fctRho := by
  refine ⟨∑ r ∈ Finset.range (n + 1), |∏ i ∈ Finset.range r, (-(1 / 2 : ℝ) - (i : ℝ))|,
    Finset.sum_nonneg fun _ _ => abs_nonneg _, fun r hr u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have h : ContDiffAt ℝ r (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) u :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hu0)
  have e : ‖iteratedDeriv r fctRho u‖ = ‖iteratedDeriv r (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) u‖ :=
    norm_iteratedDeriv_ofReal _ r u h
  rw [e]
  have h2 := FctSym.SymW.iteratedDeriv_rpow_sub (-(1 / 2 : ℝ)) 0 r hu0
  simp only [sub_zero] at h2
  rw [h2, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg hu0.le _)]
  have h1 : |∏ i ∈ Finset.range r, (-(1 / 2 : ℝ) - (i : ℝ))| ≤ ∑ j ∈ Finset.range (n + 1), |∏ i ∈ Finset.range j, (-(1 / 2 : ℝ) - (i : ℝ))| :=
    Finset.single_le_sum (f := fun j => |∏ i ∈ Finset.range j, (-(1 / 2 : ℝ) - (i : ℝ))|) (fun j _ => abs_nonneg _)
      (Finset.mem_range.2 (by omega))
  exact mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu0.le _)

lemma kappa_sbd {n : ℕ} {p B : ℝ} {κ : ℝ → ℂ} (hκ : FctSymCls n p B κ) (hB : 0 ≤ B) :
    ContDiffOn ℝ n κ (Ioi 0) ∧ SBd n 2 p ((2 : ℝ) ^ (|p| + n) * B) κ := by
  refine ⟨hκ.1.mono Ioi_subset_Ici_self, fun r hr u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hcd : ContDiffAt ℝ r κ u := (hκ.1.contDiffAt (Ici_mem_nhds hu0)).of_le (by exact_mod_cast hr)
  rw [← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hcd (mem_Ici.2 hu0.le)]
  refine (hκ.2 r hr u (mem_Ici.2 hu0.le)).trans ?_
  have hs : |(-1 : ℝ)| ≤ u / 2 := by rw [abs_neg, abs_one]; linarith
  have h1 := FctSym.SymW.rpow_shift_le (p := p - r) hs hu0
  have e : u - (-1 : ℝ) = 1 + u := by ring
  rw [e] at h1
  have h2 : (2 : ℝ) ^ |p - r| ≤ (2 : ℝ) ^ (|p| + n) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : |p - r| ≤ |p| + |(r : ℝ)| := abs_sub _ _
    have h3 : |(r : ℝ)| = r := abs_of_nonneg (Nat.cast_nonneg r)
    have h4 : (r : ℝ) ≤ n := by exact_mod_cast hr
    linarith
  have hp : 0 ≤ u ^ (p - r) := Real.rpow_nonneg hu0.le _
  calc B * (1 + u) ^ (p - r) ≤ B * ((2 : ℝ) ^ |p - r| * u ^ (p - r)) := mul_le_mul_of_nonneg_left h1 hB
    _ ≤ B * ((2 : ℝ) ^ (|p| + n) * u ^ (p - r)) := by gcongr
    _ = _ := by ring


lemma fam_const {V U : ℝ} {n : ℕ} {q A : ℝ} {h₀ : ℝ → ℂ} (hs : ContDiffOn ℝ n h₀ (Ioi V))
    (hz : ∀ u, V < u → u < U → h₀ u = 0) (hb : SBd n U q A h₀) : Fam V U n q A (fun _ => h₀) where
  smooth := fun _ _ => hs
  zero := fun _ _ u h1 h2 => hz u h1 h2
  bound := fun _ _ => hb
  cont := fun _ _ _ _ => tendsto_const_nhds

lemma amp_far (M : ℝ) (n : ℕ) (p : ℝ) : ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ (B : ℝ) (κ : ℝ → ℂ), 0 ≤ B → FctSymCls n p B κ →
    ContDiffOn ℝ n (fun u => fctStep (fctU0 M) u * fctRho u * κ u) (Ioi (fctU0 M - 1)) ∧
    SBd n (fctU0 M) (p - 1 / 2) (Ch * B) (fun u => fctStep (fctU0 M) u * fctRho u * κ u) := by
  have h6 := fctU0_ge_six M
  obtain ⟨As, hAs1, hAs⟩ := fctStep_sbd n (by linarith : 1 ≤ fctU0 M)
  obtain ⟨Ar, hAr0, hAr⟩ := fctRho_sbd n
  refine ⟨2 ^ n * (2 ^ n * As * Ar) * (2 : ℝ) ^ (|p| + n), by positivity, fun B κ hB hκ => ?_⟩
  obtain ⟨hκc, hκb⟩ := kappa_sbd hκ hB
  have hV0 : (0 : ℝ) ≤ fctU0 M - 1 := by linarith
  have hsub : Ioi (fctU0 M - 1) ⊆ Ioi 0 := Ioi_subset_Ioi hV0
  have hs : ContDiffOn ℝ n (fctStep (fctU0 M)) (Ioi (fctU0 M - 1)) :=
    (contDiff_fctStep _).contDiffOn.of_le (by exact_mod_cast le_top)
  have hr : ContDiffOn ℝ n fctRho (Ioi (fctU0 M - 1)) := (contDiffOn_fctRho n).mono hsub
  have hk : ContDiffOn ℝ n κ (Ioi (fctU0 M - 1)) := hκc.mono hsub
  have h1 := SBd.mul (V := fctU0 M - 1) (by linarith) (by linarith) hs hr hAs (hAr.mono_U (by linarith : (1 : ℝ) ≤ fctU0 M))
  have h2 := SBd.mul (V := fctU0 M - 1) (by linarith) (by linarith) (hs.mul hr) hk h1 (hκb.mono_U (by linarith : (2 : ℝ) ≤ fctU0 M))
  refine ⟨(hs.mul hr).mul hk, ?_⟩
  have e : (0 + -(1 / 2 : ℝ)) + p = p - 1 / 2 := by ring
  rw [e] at h2
  exact h2.mono_q_A (le_of_eq (by ring)) (by linarith)

lemma amp_tail (M : ℝ) (n : ℕ) (p : ℝ) : ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ (B : ℝ) (κ : ℝ → ℂ), 0 ≤ B → FctSymCls n p B κ →
    ContDiffOn ℝ n (fun u => fctRho u * κ u) (Ioi (fctU0 M - 1)) ∧
    SBd n (fctU0 M) (p - 1 / 2) (Ct * B) (fun u => fctRho u * κ u) := by
  have h6 := fctU0_ge_six M
  obtain ⟨Ar, hAr0, hAr⟩ := fctRho_sbd n
  refine ⟨2 ^ n * Ar * (2 : ℝ) ^ (|p| + n), by positivity, fun B κ hB hκ => ?_⟩
  obtain ⟨hκc, hκb⟩ := kappa_sbd hκ hB
  have hV0 : (0 : ℝ) ≤ fctU0 M - 1 := by linarith
  have hsub : Ioi (fctU0 M - 1) ⊆ Ioi 0 := Ioi_subset_Ioi hV0
  have hr : ContDiffOn ℝ n fctRho (Ioi (fctU0 M - 1)) := (contDiffOn_fctRho n).mono hsub
  have hk : ContDiffOn ℝ n κ (Ioi (fctU0 M - 1)) := hκc.mono hsub
  have h2 := SBd.mul (V := fctU0 M - 1) (by linarith) (by linarith) hr hk (hAr.mono_U (by linarith : (1 : ℝ) ≤ fctU0 M))
    (hκb.mono_U (by linarith : (2 : ℝ) ≤ fctU0 M))
  refine ⟨hr.mul hk, ?_⟩
  have e : (-(1 / 2 : ℝ)) + p = p - 1 / 2 := by ring
  rw [e] at h2
  exact h2.mono_q_A (le_of_eq (by ring)) (by linarith)


lemma fctStep_eq_one {U₀ u : ℝ} (h : U₀ + 1 ≤ u) : fctStep U₀ u = 1 := by
  unfold fctStep
  rw [Real.smoothTransition.one_of_one_le (by linarith)]; simp

lemma norm_one_sub_fctStep_le (U₀ u : ℝ) : ‖1 - fctStep U₀ u‖ ≤ 1 := by
  unfold fctStep
  have h1 := Real.smoothTransition.nonneg (u - U₀)
  have h2 := Real.smoothTransition.le_one (u - U₀)
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

lemma norm_fctRho {u : ℝ} (hu : 0 < u) : ‖fctRho u‖ = u ^ (-(1 / 2 : ℝ)) := by
  unfold fctRho
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _)]

/-- The part of the regularised integral near `0` (where the cutoff `1 - s` is supported): integrable for every `ε ≥ 0`, and the Abel limit exists with a bound `C_N B`. -/
lemma near_part (M : ℝ) (n : ℕ) (p : ℝ) : ∃ CN : ℝ, 0 ≤ CN ∧ ∀ (û B : ℝ) (κ : ℝ → ℂ), 0 ≤ B → FctSymCls n p B κ →
    (∀ ε : ℝ, 0 ≤ ε → IntegrableOn (fun u => (1 - fctStep (fctU0 M) u) * fctRho u * κ u * Complex.exp (fctW û ε u)) (Ioi 0)) ∧
    ∃ N₀ : ℂ, Tendsto (fun ε => ∫ u in Ioi 0, (1 - fctStep (fctU0 M) u) * fctRho u * κ u * Complex.exp (fctW û ε u))
      (𝓝[>] 0) (𝓝 N₀) ∧ ‖N₀‖ ≤ CN * B := by
  have h6 := fctU0_ge_six M
  set U₀ := fctU0 M with hU₀
  set Kp : ℝ := (U₀ + 2) ^ |p| with hKp
  have hKp0 : 0 ≤ Kp := Real.rpow_nonneg (by linarith) _
  refine ⟨Kp * (2 * (U₀ + 1) ^ (1 / 2 : ℝ)), by positivity, fun û B κ hB hκ => ?_⟩
  obtain ⟨hκc, -⟩ := kappa_sbd hκ hB
  set g₀ : ℝ → ℂ := fun u => (1 - fctStep U₀ u) * fctRho u * κ u with hg₀
  have hg0 : ∀ u, U₀ + 1 ≤ u → g₀ u = 0 := fun u hu => by
    simp only [hg₀, fctStep_eq_one hu]; simp
  have hκb : ∀ u, 0 < u → ‖κ u‖ ≤ B * (1 + u) ^ p := fun u hu => by
    have := hκ.2 0 (Nat.zero_le _) u (mem_Ici.2 hu.le)
    simpa using this
  have hKb : ∀ u, 0 < u → u ≤ U₀ + 1 → (1 + u) ^ p ≤ Kp := fun u hu hu1 => by
    rcases le_total 0 p with hp | hp
    · calc (1 + u) ^ p ≤ (U₀ + 2) ^ p := Real.rpow_le_rpow (by linarith) (by linarith) hp
        _ = Kp := by rw [hKp, abs_of_nonneg hp]
    · calc (1 + u) ^ p ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hp
        _ ≤ Kp := Real.one_le_rpow (by linarith) (abs_nonneg _)
  have hbd : ∀ u, 0 < u → u ≤ U₀ + 1 → ‖g₀ u‖ ≤ B * Kp * u ^ (-(1 / 2 : ℝ)) := fun u hu hu1 => by
    simp only [hg₀, norm_mul]
    rw [norm_fctRho hu]
    have h1 := norm_one_sub_fctStep_le U₀ u
    have h2 := hκb u hu
    have h3 := hKb u hu hu1
    have hp : 0 ≤ u ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu.le _
    calc ‖1 - fctStep U₀ u‖ * u ^ (-(1 / 2 : ℝ)) * ‖κ u‖ ≤ 1 * u ^ (-(1 / 2 : ℝ)) * (B * Kp) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_left h3 hB)
      _ = _ := by ring
  have hcont : ContinuousOn g₀ (Ioi 0) := by
    have hs : ContinuousOn (fun u => 1 - fctStep U₀ u) (Ioi 0) :=
      (continuous_const.sub (contDiff_fctStep U₀).continuous).continuousOn
    have hr : ContinuousOn fctRho (Ioi 0) := (contDiffOn_fctRho 0).continuousOn
    have hk : ContinuousOn κ (Ioi 0) := hκc.continuousOn
    exact (hs.mul hr).mul hk
  have hbint : IntegrableOn (fun u : ℝ => B * Kp * u ^ (-(1 / 2 : ℝ))) (Ioc 0 (U₀ + 1)) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := U₀ + 1) (r := -(1 / 2 : ℝ)) (by norm_num)).const_mul (B * Kp)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1 this
  have hmeasF : ∀ ε : ℝ, ContinuousOn (fun u => g₀ u * Complex.exp (fctW û ε u)) (Ioi 0) := fun ε =>
    hcont.mul (continuous_fctW û ε).cexp.continuousOn
  have hFint : ∀ ε : ℝ, 0 ≤ ε → IntegrableOn (fun u => g₀ u * Complex.exp (fctW û ε u)) (Ioc 0 (U₀ + 1)) := by
    intro ε hε
    refine Integrable.mono' hbint ((hmeasF ε).mono Ioc_subset_Ioi_self |>.aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le hε u)).trans (hbd u hu.1 hu.2)
  have hzero : ∀ ε : ℝ, ∀ u ∈ Ioi (0 : ℝ) \ Ioc 0 (U₀ + 1), g₀ u * Complex.exp (fctW û ε u) = 0 := by
    intro ε u hu
    have : U₀ + 1 < u := by
      by_contra hle; push Not at hle
      exact hu.2 ⟨hu.1, hle⟩
    rw [hg0 u this.le, zero_mul]
  refine ⟨fun ε hε => ?_, ?_⟩
  · exact (hFint ε hε).of_forall_sdiff_eq_zero measurableSet_Ioi (hzero ε)
  · have hI : ∀ ε : ℝ, ∫ u in Ioi 0, g₀ u * Complex.exp (fctW û ε u) = ∫ u in Ioc 0 (U₀ + 1), g₀ u * Complex.exp (fctW û ε u) :=
      fun ε => setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self (hzero ε)
    have hfun : (fun ε : ℝ => ∫ u in Ioi 0, g₀ u * Complex.exp (fctW û ε u)) =
        fun ε => ∫ u in Ioc 0 (U₀ + 1), g₀ u * Complex.exp (fctW û ε u) := funext hI
    have hmem : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
    refine ⟨∫ u in Ioc 0 (U₀ + 1), g₀ u * Complex.exp (fctW û 0 u), ?_, ?_⟩
    · show Tendsto (fun ε : ℝ => ∫ u in Ioi 0, g₀ u * Complex.exp (fctW û ε u)) _ _
      rw [hfun]
      refine tendsto_integral_filter_of_dominated_convergence (fun u => B * Kp * u ^ (-(1 / 2 : ℝ))) ?_ ?_ hbint ?_
      · exact Filter.Eventually.of_forall fun ε =>
          ((hmeasF ε).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
      · filter_upwards [hmem] with ε hε
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le (le_of_lt hε) u)).trans (hbd u hu.1 hu.2)
      · refine Filter.Eventually.of_forall fun u => ?_
        exact tendsto_const_nhds.mul ((((continuous_fctW_eps û u).cexp).tendsto 0).mono_left nhdsWithin_le_nhds)
    · refine (norm_integral_le_of_norm_le hbint ?_).trans ?_
      · refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
        rw [norm_mul]
        exact (mul_le_of_le_one_right (norm_nonneg _) (norm_exp_fctW_le le_rfl u)).trans (hbd u hu.1 hu.2)
      · rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ U₀ + 1),
          integral_rpow (Or.inl (by norm_num))]
        have : (-(1 / 2 : ℝ)) + 1 = 1 / 2 := by norm_num
        rw [this, Real.zero_rpow (by norm_num), sub_zero]
        apply le_of_eq; field_simp


lemma fctSEps_eq (û ε : ℝ) (κ : ℝ → ℂ) :
    fctSEps û ε κ = Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
      ∫ u in Ioi (0 : ℝ), fctRho u * Complex.exp (fctW û ε u) * κ u := rfl

lemma norm_phase : ‖Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma fctStep_eq_zero {U₀ u : ℝ} (h : u ≤ U₀) : fctStep U₀ u = 0 := by
  unfold fctStep
  rw [Real.smoothTransition.zero_of_nonpos (by linarith)]; simp


lemma main_ident {û ε U₀ : ℝ} {κ : ℝ → ℂ} (hU₀ : 0 < U₀)
    (hN : IntegrableOn (fun u => (1 - fctStep U₀ u) * fctRho u * κ u * Complex.exp (fctW û ε u)) (Ioi 0))
    (hF : IntegrableOn (fun u => fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u)) (Ioi U₀)) :
    fctSEps û ε κ = Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) *
      ((∫ u in Ioi 0, (1 - fctStep U₀ u) * fctRho u * κ u * Complex.exp (fctW û ε u)) +
        ∫ u in Ioi U₀, fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u)) := by
  rw [fctSEps_eq]
  congr 1
  have hzero : ∀ u ∈ Ioi (0 : ℝ) \ Ioi U₀, fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u) = 0 := by
    intro u hu
    have : u ≤ U₀ := by by_contra h; push Not at h; exact hu.2 h
    rw [fctStep_eq_zero this]; simp
  have hF' : IntegrableOn (fun u => fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u)) (Ioi 0) :=
    hF.of_forall_sdiff_eq_zero measurableSet_Ioi hzero
  have e1 : ∫ u in Ioi (0 : ℝ), fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u) =
      ∫ u in Ioi U₀, fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hU₀.le) hzero
  rw [← e1, ← integral_add hN hF']
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  ring


/-- **`fct:inner-symbols` (a), existence and bounds** (Lemma FCT.5b (a)): proved.  Integration by parts `n` times with the complex phase `e^{w_ε}`,
`w_ε' = D_ε`, `𝒟_ε g = -(g/D_ε)'`, uniformly in `ε ∈ (0, 1]`, after cutting `κ` at `U₀ = max(6, √(8M))` with a smooth step. -/
theorem fctInnerSymbolsA : FctInnerSymbolsA := by
  intro M n p hM hn hp
  have hq : p - 1 / 2 < 3 * (n : ℝ) - 1 := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := fam_main M n (p - 1 / 2) hq
  obtain ⟨Ch, hCh0, hCh⟩ := amp_far M n p
  obtain ⟨Ct, hCt0, hCt⟩ := amp_tail M n p
  obtain ⟨CN, hCN0, hCN⟩ := near_part M n p
  have h6 := fctU0_ge_six M
  set U₀ := fctU0 M with hU₀def
  have hU0pos : 0 < U₀ := by linarith
  set e : ℝ := (p - 1 / 2) + 1 - 3 * (n : ℝ) with he
  have hUe : 0 ≤ U₀ ^ e := Real.rpow_nonneg hU0pos.le _
  refine ⟨max (CN + C₁ * Ch * U₀ ^ e) (C₁ * Ct), le_max_of_le_left (by positivity), fun û B κ hû hB hκ => ?_⟩
  obtain ⟨hfc, hfb⟩ := hCh B κ hB hκ
  have hFam : Fam (U₀ - 1) U₀ n (p - 1 / 2) (Ch * B) (fun _ => fun u => fctStep U₀ u * fctRho u * κ u) :=
    fam_const hfc (fun u _ hu => by simp [fctStep_eq_zero hu.le]) hfb
  obtain ⟨R₁, hR₁, hR₁b⟩ := hC₁ û (U₀ - 1) U₀ (Ch * B) _ hû rfl le_rfl hFam
  obtain ⟨hNint, N₀, hN₀, hN₀b⟩ := hCN û B κ hB hκ
  have hFint : ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun u => fctStep U₀ u * fctRho u * κ u * Complex.exp (fctW û ε u)) (Ioi U₀) := by
    intro ε hε
    refine integrableOn_amp (σ := p - 1 / 2) (A := Ch * B) (by linarith) hε
      (hfc.continuousOn.mono (Ioi_subset_Ioi (by linarith))) ?_
    intro u hu; simpa using hfb 0 (Nat.zero_le _) u hu
  have hL : FctSLimit û κ (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * (N₀ + R₁)) := by
    unfold FctSLimit
    refine (tendsto_const_nhds.mul (hN₀.add hR₁)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (main_ident hU0pos (hNint ε (le_of_lt hε)) (hFint ε hε)).symm
  have hBmain : ‖fctS û κ‖ ≤ (CN + C₁ * Ch * U₀ ^ e) * B := by
    rw [hL.fctS_eq, norm_mul, norm_phase, one_mul]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖R₁‖ ≤ C₁ * (Ch * B) * U₀ ^ e := hR₁b
    nlinarith [hN₀b]
  refine ⟨⟨_, hL⟩, hBmain.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hB), fun ustar hust hz => ?_⟩
  have hust' : U₀ ≤ ustar := hust
  have hus0 : 0 < ustar := by linarith
  obtain ⟨htc, htb⟩ := hCt B κ hB hκ
  have hFam2 : Fam (U₀ - 1) ustar n (p - 1 / 2) (Ct * B) (fun _ => fun u => fctRho u * κ u) :=
    fam_const htc (fun u hu1 hu2 => by
      have : κ u = 0 := hz u ⟨by linarith, hu2.le⟩
      simp [this]) (htb.mono_U hust')
  obtain ⟨R₂, hR₂, hR₂b⟩ := hC₁ û (U₀ - 1) ustar (Ct * B) _ hû rfl hust' hFam2
  have hL2 : FctSLimit û κ (Complex.exp (((-(π / 4) : ℝ) : ℂ) * Complex.I) * R₂) := by
    unfold FctSLimit
    refine (tendsto_const_nhds.mul hR₂).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [fctSEps_eq]
    congr 1
    have hz' : ∀ u ∈ Ioi (0 : ℝ) \ Ioi ustar, fctRho u * Complex.exp (fctW û ε u) * κ u = 0 := by
      intro u hu
      have : u ≤ ustar := by by_contra h; push Not at h; exact hu.2 h
      rw [hz u ⟨hu.1.le, this⟩]; simp
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (Ioi_subset_Ioi hus0.le) hz']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    ring
  rw [hL2.fctS_eq, norm_mul, norm_phase, one_mul]
  refine hR₂b.trans ?_
  have hp0 : 0 ≤ ustar ^ (p + 1 / 2 - 3 * (n : ℝ)) := Real.rpow_nonneg hus0.le _
  have e2 : e = p + 1 / 2 - 3 * (n : ℝ) := by rw [he]; ring
  rw [e2]
  have hmax : C₁ * Ct ≤ max (CN + C₁ * Ch * U₀ ^ (p + 1 / 2 - 3 * (n : ℝ))) (C₁ * Ct) := le_max_right _ _
  have h3 : C₁ * (Ct * B) * ustar ^ (p + 1 / 2 - 3 * (n : ℝ)) = (C₁ * Ct) * B * ustar ^ (p + 1 / 2 - 3 * (n : ℝ)) := by ring
  rw [h3]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax hB) hp0

end FctSymA

/-- **The "in particular" clause of `fct:inner-symbols` (a)** (`|û - a₁| ≤ 1`, `n = 8`, `U₀ = 6`, tail exponent `p - 47/2`), from `fctInnerSymbolsA`:
for `p ≤ 21` there is `C` with `|𝒮[κ]| ≤ C B` and, if `κ = 0` on `[0, u_*]`, `u_* ≥ 6`, `|𝒮[κ]| ≤ C B u_*^{p - 47/2}`, for every `κ ∈ 𝒮^p(B)` (`n = 8`) and
`|û - a₁| ≤ 1`, `a₁ = airyZero 1`. -/
theorem fctInnerSymbolsA_box {p : ℝ} (hp : p ≤ 21) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (û B : ℝ) (κ : ℝ → ℂ), |û - FormalResearch.Special.airyZero 1| ≤ 1 → 0 ≤ B → FctSymCls 8 p B κ →
      (∃ L, FctSLimit û κ L) ∧ ‖fctS û κ‖ ≤ C * B ∧
      ∀ ustar : ℝ, 6 ≤ ustar → (∀ u ∈ Icc (0 : ℝ) ustar, κ u = 0) → ‖fctS û κ‖ ≤ C * B * ustar ^ (p - 47 / 2) := by
  obtain ⟨C, hC0, hC⟩ := FctSymA.fctInnerSymbolsA 3.35 8 p (by norm_num) (by norm_num) (by push_cast; linarith)
  refine ⟨C, hC0, fun û B κ hû hB hκ => ?_⟩
  have ha := FormalResearch.Special.airyZero_one
  have hûM : |û| ≤ 3.35 := by
    have h1 : |û| ≤ |û - FormalResearch.Special.airyZero 1| + |FormalResearch.Special.airyZero 1| := by
      calc |û| = |(û - FormalResearch.Special.airyZero 1) + FormalResearch.Special.airyZero 1| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h2 : |FormalResearch.Special.airyZero 1| ≤ 2.35 := by
      rw [abs_of_neg (by linarith [ha.2])]; linarith [ha.1]
    linarith
  obtain ⟨hex, hb1, hb2⟩ := hC û B κ hûM hB hκ
  refine ⟨hex, hb1, fun ustar hu hz => ?_⟩
  have h8 : √(8 * (3.35 : ℝ)) ≤ 6 := by
    apply Real.sqrt_le_iff.2; constructor <;> norm_num
  have := hb2 ustar (max_le hu (h8.trans hu)) hz
  have e : p + 1 / 2 - 3 * ((8 : ℕ) : ℝ) = p - 47 / 2 := by push_cast; ring
  rwa [e] at this

/-- Step 3 consumption of (a) (`fct:warp-asymp` (1), `(fct:RI-bounds)`): with `u_* = 2.7 c^{1/12}` (`c ≥ 15000` so that `u_* ≥ 6`) a symbol `κ ∈ 𝒮^p(B)` vanishing on
`[0, u_*]`, `p ≤ 21`, has `|𝒮[κ]| ≤ C B c^{(p - 47/2)/12}` (`p = 2, 3, 4`: `c^{-43/24}`, `c^{-41/24}`, `c^{-39/24}`, as in Step 3). -/
theorem fctInnerSymbolsA_tail_c {p : ℝ} (hp : p ≤ 21) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c : ℝ, 15000 ≤ c → ∀ (û B : ℝ) (κ : ℝ → ℂ), |û - FormalResearch.Special.airyZero 1| ≤ 1 → 0 ≤ B →
      FctSymCls 8 p B κ → (∀ u ∈ Icc (0 : ℝ) (fctUstar c), κ u = 0) → ‖fctS û κ‖ ≤ C * B * c ^ ((p - 47 / 2) / 12) := by
  obtain ⟨C, hC0, hC⟩ := fctInnerSymbolsA_box hp
  refine ⟨C * 2.7 ^ (p - 47 / 2), mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _), fun c hc û B κ hû hB hκ hz => ?_⟩
  have hc0 : 0 < c := by linarith
  set x : ℝ := c ^ ((1 : ℝ) / 12) with hx
  have hxpos : 0 < x := Real.rpow_pos_of_pos hc0 _
  have hcx : c = x ^ 12 := by
    rw [hx, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
  have hx6 : (2.223 : ℝ) ≤ x := by
    by_contra hlt
    push Not at hlt
    have : x ^ 12 < 2.223 ^ 12 := pow_lt_pow_left₀ hlt hxpos.le (by norm_num)
    have h2 : (2.223 : ℝ) ^ 12 < 15000 := by norm_num
    linarith
  have hu6 : 6 ≤ fctUstar c := by unfold fctUstar; rw [← hx]; linarith
  obtain ⟨-, -, hb2⟩ := hC û B κ hû hB hκ
  have := hb2 (fctUstar c) hu6 hz
  refine this.trans ?_
  have e : fctUstar c ^ (p - 47 / 2) = 2.7 ^ (p - 47 / 2) * c ^ ((p - 47 / 2) / 12) := by
    unfold fctUstar
    rw [← hx, Real.mul_rpow (by norm_num) hxpos.le]
    congr 1
    rw [hx, ← Real.rpow_mul hc0.le]; congr 1; ring
  rw [e]
  apply le_of_eq
  ring

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsA_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsA_box

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsA_tail_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsA_tail_c


/-- info: 'FormalResearch.SignUncertainty.FctSymA.fctInnerSymbolsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FctSymA.fctInnerSymbolsA

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsA_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsA_box

/-- info: 'FormalResearch.SignUncertainty.fctInnerSymbolsA_tail_c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fctInnerSymbolsA_tail_c

end FormalResearch.SignUncertainty

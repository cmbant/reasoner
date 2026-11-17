module

public import FormalResearch.Special.AiryPwsGrowth
public import FormalResearch.Special.AiryRatioBounds

/-!
# The Airy Paley–Wiener–Schwartz theorem, direction `(a) ⇒ (b)`: `F̃ ∈ H^∞` with `‖F̃‖_∞ ≤ k ‖f‖₁`

Theorem 3.1 of `CFT/notes/general_theorems.tex` (`GENERAL_THEOREMS`), `(a)⇒(b)`: for `f ∈ G` (`AiryClassG`: entire,
`L¹(ℝ)`, `|f(z)| ≤ C(1+|z|)^N e(z)`), the twisted transform `F̃(ζ) = k e^{-iζ³/12} ∫ f(u) e^{-iζu} du`, `k = 2^{2/3}`,
is holomorphic on `Im ζ > 0`, continuous on `Im ζ ≥ 0` and bounded there by `k ‖f‖_{L¹}`:

* `airyFtilde_diffContOnCl`: `DiffContOnCl ℂ F̃ {Im ζ > 0}`;
* `airyFtilde_norm_le`: `‖F̃(ζ)‖ ≤ k ∫_ℝ |f|` for all `Im ζ ≥ 0`   (the **uniform `H^∞` bound**, CE_O1_ROUTE O.11n);
* `airyFtilde_boundary`: on `ℝ`, `F̃(ξ) = k e^{-iξ³/12} f̂(ξ)`.

Proof (the paper's): polynomial growth of `F̃` on `Im ζ ≥ 0` from the contour deformation in `s = √u`
(`AiryPwsContour`, `AiryPwsGrowth`; the half plane `Re ζ ≤ 0` directly and `Re ζ ≥ 0` by applying it to
`f^*(z) = conj f(conj z)`, `F̃_{f^*}(-conj ζ) = conj F̃_f(ζ)`), and then the half-plane Phragmén–Lindelöf principle for
polynomially bounded functions that are bounded on the boundary (`pl_halfPlane`, regularised by `(1+εw)^{-M}` and Mathlib's
`PhragmenLindelof.right_half_plane_of_bounded_on_real`).

Also here: `pl_halfPlane_decay`, the transfer of a boundary decay `|F(ξ)| ≤ B (1+|ξ|)^{-m}` of a bounded holomorphic
function to the closed half plane (the step "Phragmén–Lindelöf as in Lemma U.2" of O.11n).

The converse `(b) ⇒ (a)` is `AiryPwsConverseMain`, the plane-wave identity and the Laplace form of `(c)` are
`AiryPwsPlaneWave`, `AiryPwsLaplace`.

**Not formalised:** the distributional form `(c)` (`f = ∫ Φ_τ dμ(τ)`, `supp μ ⊂ [0,∞)`, `μ` tempered).
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set Bornology Asymptotics
open scoped Real

namespace FormalResearch.Special

/-! ### Phragmén–Lindelöf in the upper half plane for polynomially bounded functions -/

/-- **Phragmén–Lindelöf**: `g` holomorphic on `Im ζ > 0`, continuous on `Im ζ ≥ 0`, polynomially bounded there and
`‖g‖ ≤ B` on `ℝ` implies `‖g‖ ≤ B` on `Im ζ ≥ 0`. -/
theorem pl_halfPlane {g : ℂ → ℂ} {A B : ℝ} {M : ℕ} (hA : 0 ≤ A)
    (hd : DiffContOnCl ℂ g {ζ : ℂ | 0 < ζ.im})
    (hpoly : ∀ ζ : ℂ, 0 ≤ ζ.im → ‖g ζ‖ ≤ A * (1 + ‖ζ‖) ^ M)
    (hbd : ∀ ξ : ℝ, ‖g (ξ : ℂ)‖ ≤ B) {ζ : ℂ} (hζ : 0 ≤ ζ.im) : ‖g ζ‖ ≤ B := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hbd 0)
  -- the regularised functions on the right half plane
  have key : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ w : ℂ, 0 ≤ w.re →
      ‖g (I * w)‖ ≤ B * ‖1 + (ε : ℂ) * w‖ ^ M := by
    intro ε hε hε1 w hw
    set h : ℂ → ℂ := fun w => g (I * w) / (1 + (ε : ℂ) * w) ^ M with hh
    have hden : ∀ w : ℂ, 0 ≤ w.re → 1 ≤ ‖1 + (ε : ℂ) * w‖ := by
      intro w hw
      have : 1 ≤ (1 + (ε : ℂ) * w).re := by simp; nlinarith
      exact this.trans (Complex.re_le_norm _)
    have hden0 : ∀ w : ℂ, 0 ≤ w.re → (1 + (ε : ℂ) * w) ≠ 0 := fun w hw =>
      norm_pos_iff.mp (lt_of_lt_of_le one_pos (hden w hw))
    have hIw : ∀ w : ℂ, (I * w).im = w.re := by intro w; simp
    -- differentiability and continuity
    have hmaps : MapsTo (fun w : ℂ => I * w) {w : ℂ | 0 < w.re} {ζ : ℂ | 0 < ζ.im} := fun w hw => by
      show 0 < (I * w).im
      rw [hIw]; exact hw
    have hdiff : DifferentiableOn ℂ h {w : ℂ | 0 < w.re} := by
      refine DifferentiableOn.div ?_ ?_ ?_
      · exact hd.differentiableOn.comp (differentiableOn_id.const_mul I) hmaps
      · exact DifferentiableOn.pow (by fun_prop) _
      · intro w hw; exact pow_ne_zero _ (hden0 w (le_of_lt hw))
    have hcont : ContinuousOn h (closure {w : ℂ | 0 < w.re}) := by
      rw [closure_setOfPred_lt_re]
      refine ContinuousOn.div ?_ ?_ ?_
      · refine hd.continuousOn.comp (continuous_const.mul continuous_id).continuousOn ?_
        intro w hw
        rw [closure_setOfPred_lt_im]
        simpa [hIw] using hw
      · exact (by fun_prop : Continuous fun w : ℂ => (1 + (ε : ℂ) * w) ^ M).continuousOn
      · intro w hw; exact pow_ne_zero _ (hden0 w hw)
    have hdc : DiffContOnCl ℂ h {w : ℂ | 0 < w.re} := ⟨hdiff, hcont⟩
    -- growth
    have hexp : ∃ c < (2 : ℝ), ∃ B' : ℝ, h =O[cobounded ℂ ⊓ 𝓟 {w : ℂ | 0 < w.re}]
        fun z => Real.exp (B' * ‖z‖ ^ c) := by
      refine ⟨1, by norm_num, M, ?_⟩
      refine Asymptotics.IsBigO.of_bound A ?_
      refine eventually_inf_principal.mpr (Eventually.of_forall fun w hw => ?_)
      have hw' : 0 ≤ w.re := le_of_lt hw
      have h1 : ‖h w‖ ≤ ‖g (I * w)‖ := by
        rw [hh]; simp only [norm_div, norm_pow]
        have := hden w hw'
        have hp : 1 ≤ ‖1 + (ε : ℂ) * w‖ ^ M := one_le_pow₀ this
        exact div_le_self (norm_nonneg _) hp
      have h2 : ‖g (I * w)‖ ≤ A * (1 + ‖w‖) ^ M := by
        have := hpoly (I * w) (by rw [hIw]; exact hw')
        simpa using this
      have h3 : (1 + ‖w‖) ^ M ≤ Real.exp (M * ‖w‖ ^ (1 : ℝ)) := by
        rw [Real.rpow_one]
        calc (1 + ‖w‖) ^ M ≤ (Real.exp ‖w‖) ^ M :=
              pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp ‖w‖]) M
          _ = _ := by rw [← Real.exp_nat_mul]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc ‖h w‖ ≤ A * (1 + ‖w‖) ^ M := h1.trans h2
        _ ≤ A * Real.exp (M * ‖w‖ ^ (1 : ℝ)) := mul_le_mul_of_nonneg_left h3 hA
    have hre : IsBoundedUnder (· ≤ ·) atTop fun x : ℝ => ‖h (x : ℂ)‖ := by
      refine isBoundedUnder_of_eventually_le (a := A * (ε⁻¹) ^ M) ?_
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
      show ‖h (x : ℂ)‖ ≤ A * (ε⁻¹) ^ M
      rw [hh]; simp only [norm_div, norm_pow]
      have h1 : ‖g (I * (x : ℂ))‖ ≤ A * (1 + x) ^ M := by
        have := hpoly (I * (x : ℂ)) (by simpa using hx)
        simpa [abs_of_nonneg hx] using this
      have hden' : ‖1 + (ε : ℂ) * (x : ℂ)‖ = 1 + ε * x := by
        rw [show (1 : ℂ) + (ε : ℂ) * (x : ℂ) = ((1 + ε * x : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [hden']
      have hpos : 0 < (1 + ε * x) ^ M := by positivity
      rw [div_le_iff₀ hpos]
      calc ‖g (I * (x : ℂ))‖ ≤ A * (1 + x) ^ M := h1
        _ ≤ A * ((ε⁻¹) ^ M * (1 + ε * x) ^ M) := by
            refine mul_le_mul_of_nonneg_left ?_ hA
            rw [← mul_pow]
            refine pow_le_pow_left₀ (by positivity) ?_ M
            have : ε⁻¹ * (1 + ε * x) = ε⁻¹ + x := by field_simp
            rw [this]
            have : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).mpr hε1
            linarith
        _ = _ := by ring
    have him : ∀ x : ℝ, ‖h ((x : ℂ) * I)‖ ≤ B := by
      intro x
      rw [hh]; simp only [norm_div, norm_pow]
      have e : I * ((x : ℂ) * I) = ((-x : ℝ) : ℂ) := by
        push_cast; rw [← mul_assoc, mul_comm I, mul_assoc, Complex.I_mul_I]; ring
      rw [e]
      have hd1 : 1 ≤ ‖1 + (ε : ℂ) * ((x : ℂ) * I)‖ := hden _ (by simp)
      have hp : 1 ≤ ‖1 + (ε : ℂ) * ((x : ℂ) * I)‖ ^ M := one_le_pow₀ hd1
      exact (div_le_self (norm_nonneg _) hp).trans (hbd (-x))
    have := PhragmenLindelof.right_half_plane_of_bounded_on_real hdc hexp hre him hw
    rw [hh] at this
    simp only [norm_div, norm_pow] at this
    have hpos : 0 < ‖1 + (ε : ℂ) * w‖ ^ M := by
      have := hden w hw
      positivity
    rwa [div_le_iff₀ hpos] at this
  -- let `ε → 0`
  set w : ℂ := -I * ζ with hw
  have hwre : 0 ≤ w.re := by simp [hw, hζ]
  have hIw : I * w = ζ := by rw [hw]; ring_nf; simp
  have hlim : Tendsto (fun ε : ℝ => B * ‖1 + (ε : ℂ) * w‖ ^ M) (𝓝[>] 0) (𝓝 B) := by
    have hc : Continuous fun ε : ℝ => B * ‖1 + (ε : ℂ) * w‖ ^ M := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  refine ge_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
  have := key ε hε.1 hε.2.le w hwre
  rwa [hIw] at this

/-! ### The reflected function `f^*` and the boundary bound -/

/-- `f^*(z) = conj f(conj z)`. -/
noncomputable def airyClassStar (f : ℂ → ℂ) : ℂ → ℂ := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))

lemma AiryClassG.star {f : ℂ → ℂ} (hf : AiryClassG f) : AiryClassG (airyClassStar f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have := (hf.differentiable ((starRingEnd ℂ) z)).conj_conj
    rw [Complex.conj_conj] at this
    exact this
  · have h := Integrable.mono' hf.integrable.norm
      (Complex.continuous_conj.comp_aestronglyMeasurable hf.integrable.1)
      (Eventually.of_forall fun x => by simp)
    simpa [airyClassStar, Complex.conj_ofReal] using h
  · obtain ⟨C, N, hC, hb⟩ := hf.bound
    refine ⟨C, N, hC, fun z => ?_⟩
    have := hb ((starRingEnd ℂ) z)
    rw [Complex.norm_conj, airyEnv_conj] at this
    simpa [airyClassStar, Complex.norm_conj] using this

lemma airyFhat_star (f : ℂ → ℂ) (ζ : ℂ) :
    airyFhat (airyClassStar f) (-(starRingEnd ℂ) ζ) = (starRingEnd ℂ) (airyFhat f ζ) := by
  unfold airyFhat
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [airyClassStar, Complex.conj_ofReal, map_mul]
  congr 1
  rw [← Complex.exp_conj]
  congr 1
  simp [map_neg, map_mul]

lemma airyFtilde_star (f : ℂ → ℂ) (ζ : ℂ) :
    airyFtilde (airyClassStar f) (-(starRingEnd ℂ) ζ) = (starRingEnd ℂ) (airyFtilde f ζ) := by
  unfold airyFtilde
  rw [airyFhat_star, map_mul, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp [map_neg, map_div₀, map_mul, map_pow, map_ofNat]
  ring_nf

lemma airyFtilde_boundary (f : ℂ → ℂ) (ξ : ℝ) :
    airyFtilde f (ξ : ℂ) = (airyPhiK : ℂ) * cexp (-(I * (ξ : ℂ) ^ 3 / 12)) * ∫ u : ℝ, f (u : ℂ) *
      cexp (-(I * (ξ : ℂ) * (u : ℂ))) := rfl

/-- On `ℝ`: `‖F̃(ξ)‖ ≤ k ‖f‖₁`. -/
lemma norm_airyFtilde_real_le (f : ℂ → ℂ) (ξ : ℝ) :
    ‖airyFtilde f (ξ : ℂ)‖ ≤ airyPhiK * ∫ u : ℝ, ‖f (u : ℂ)‖ := by
  unfold airyFtilde
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos airyPhiK_pos]
  have h1 : ‖cexp (-(I * (ξ : ℂ) ^ 3 / 12))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (-(I * (ξ : ℂ) ^ 3 / 12)).re = 0 := by
      simp [pow_succ, Complex.mul_re, Complex.mul_im]
    rw [this, Real.exp_zero]
  rw [h1, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ airyPhiK_pos.le
  unfold airyFhat
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [norm_mul, norm_cexp_airyFhat, Complex.ofReal_im, zero_mul, Real.exp_zero, mul_one]

/-! ### Polynomial growth of `F̃`, then the `H^∞` bound -/

lemma airyFtilde_poly_left {g : ℂ → ℂ} (hg : AiryClassG g) :
    ∃ (A : ℝ) (M : ℕ), 0 ≤ A ∧ ∀ ζ : ℂ, 0 ≤ ζ.im → ζ.re ≤ 0 → ‖airyFtilde g ζ‖ ≤ A * (1 + ‖ζ‖) ^ M := by
  obtain ⟨C, N, hC, hb⟩ := hg.bound
  set m := 2 * N + 1 with hm
  set K := airyK3 m with hK
  set L1 := ∫ u : ℝ, ‖g (u : ℂ)‖ with hL1
  have hK0 : 0 ≤ K := airyK3_nonneg m
  have hL0 : 0 ≤ L1 := integral_nonneg fun u => norm_nonneg _
  refine ⟨airyPhiK * (2 * C * (1 + K) + L1), 2 * m + 1, by have := airyPhiK_pos; positivity, ?_⟩
  intro ζ him hre
  set b : ℝ := -ζ.re / 2 with hbdef
  set η : ℝ := ζ.im with hηdef
  have hb0 : 0 ≤ b := by rw [hbdef]; linarith
  have hζ : ζ = (((-2 * b : ℝ) : ℂ)) + η * I := by
    apply Complex.ext
    · simp [hbdef]; ring
    · simp [hηdef]
  have h1 := norm_airyFtilde_le hg hC hb hb0 him
  rw [← hζ] at h1
  set r := ‖ζ‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  have hbr : b ≤ r := by
    have := Complex.abs_re_le_norm ζ
    rw [hbdef]; rw [abs_of_nonpos hre] at this; linarith
  have hηr : η ≤ r := by
    have := Complex.abs_im_le_norm ζ
    rw [hηdef]; exact (le_abs_self _).trans this
  have hr1 : 1 ≤ 1 + r := by linarith
  have e1 : (1 + b) ^ m ≤ (1 + r) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
  have e2 : (1 + η) ^ m * η ≤ (1 + r) ^ m * (1 + r) :=
    mul_le_mul (pow_le_pow_left₀ (by linarith [ζ.im]) (by linarith) m) (by linarith) (by linarith) (by positivity)
  have e3 : (1 + r) ^ m ≤ (1 + r) ^ (2 * m + 1) := pow_le_pow_right₀ hr1 (by omega)
  have e4 : (1 + r) ^ m * (1 + r) = (1 + r) ^ (m + 1) := by ring
  have e5 : (1 + r) ^ (m + 1) ≤ (1 + r) ^ (2 * m + 1) := pow_le_pow_right₀ hr1 (by omega)
  have e6 : (1 : ℝ) ≤ (1 + r) ^ (2 * m + 1) := one_le_pow₀ hr1
  have hP : 0 ≤ (1 + r) ^ (2 * m + 1) := by positivity
  have hmid : 2 * C * (1 + b) ^ m * ((1 + η) ^ m * η + K) + L1 ≤
      (2 * C * (1 + K) + L1) * (1 + r) ^ (2 * m + 1) := by
    have a1 : 2 * C * (1 + b) ^ m * ((1 + η) ^ m * η + K) ≤
        2 * C * (1 + r) ^ m * ((1 + r) ^ (m + 1) + K) := by
      have e7 : (1 + η) ^ m * η + K ≤ (1 + r) ^ (m + 1) + K := by
        have := e2.trans (le_of_eq e4)
        linarith
      exact mul_le_mul (mul_le_mul_of_nonneg_left e1 (by positivity)) e7 (by positivity) (by positivity)
    have a2 : 2 * C * (1 + r) ^ m * ((1 + r) ^ (m + 1) + K) ≤ 2 * C * (1 + K) * (1 + r) ^ (2 * m + 1) := by
      have h3 : (1 + r) ^ m * (1 + r) ^ (m + 1) = (1 + r) ^ (2 * m + 1) := by ring
      have h4 : (1 + r) ^ m * K ≤ (1 + r) ^ (2 * m + 1) * K := mul_le_mul_of_nonneg_right e3 hK0
      have : (1 + r) ^ m * ((1 + r) ^ (m + 1) + K) ≤ (1 + K) * (1 + r) ^ (2 * m + 1) := by
        rw [mul_add, h3]; nlinarith
      calc 2 * C * (1 + r) ^ m * ((1 + r) ^ (m + 1) + K) = 2 * C * ((1 + r) ^ m * ((1 + r) ^ (m + 1) + K)) := by ring
        _ ≤ 2 * C * ((1 + K) * (1 + r) ^ (2 * m + 1)) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have a3 : L1 ≤ L1 * (1 + r) ^ (2 * m + 1) :=
      calc L1 = L1 * 1 := by ring
        _ ≤ L1 * (1 + r) ^ (2 * m + 1) := mul_le_mul_of_nonneg_left e6 hL0
    have a4 : (2 * C * (1 + K) + L1) * (1 + r) ^ (2 * m + 1) =
        2 * C * (1 + K) * (1 + r) ^ (2 * m + 1) + L1 * (1 + r) ^ (2 * m + 1) := by ring
    linarith
  calc ‖airyFtilde g ζ‖
      ≤ airyPhiK * (2 * C * (1 + b) ^ (2 * N + 1) * ((1 + η) ^ (2 * N + 1) * η + airyK3 (2 * N + 1)) + L1) := h1
    _ ≤ airyPhiK * ((2 * C * (1 + K) + L1) * (1 + r) ^ (2 * m + 1)) :=
        mul_le_mul_of_nonneg_left hmid airyPhiK_pos.le
    _ = _ := by ring

theorem airyFtilde_poly {f : ℂ → ℂ} (hf : AiryClassG f) :
    ∃ (A : ℝ) (M : ℕ), 0 ≤ A ∧ ∀ ζ : ℂ, 0 ≤ ζ.im → ‖airyFtilde f ζ‖ ≤ A * (1 + ‖ζ‖) ^ M := by
  obtain ⟨A1, M1, hA1, h1⟩ := airyFtilde_poly_left hf
  obtain ⟨A2, M2, hA2, h2⟩ := airyFtilde_poly_left hf.star
  refine ⟨max A1 A2, max M1 M2, le_max_of_le_left hA1, fun ζ him => ?_⟩
  have hr1 : (1 : ℝ) ≤ 1 + ‖ζ‖ := by linarith [norm_nonneg ζ]
  rcases le_total ζ.re 0 with hre | hre
  · refine (h1 ζ him hre).trans ?_
    refine mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ hr1 (le_max_left _ _)) (by positivity)
      (le_trans hA1 (le_max_left _ _))
  · have hs := airyFtilde_star f ζ
    have hb2 := h2 (-(starRingEnd ℂ) ζ) (by simpa using him) (by simp; linarith)
    rw [hs, Complex.norm_conj, norm_neg, Complex.norm_conj] at hb2
    exact hb2.trans (mul_le_mul (le_max_right _ _) (pow_le_pow_right₀ hr1 (le_max_right M1 M2))
      (by positivity) (le_trans hA1 (le_max_left _ _)))

theorem airyFtilde_diffContOnCl {f : ℂ → ℂ} (hf : AiryClassG f) :
    DiffContOnCl ℂ (airyFtilde f) {ζ : ℂ | 0 < ζ.im} := by
  have hent : Differentiable ℂ (fun ζ : ℂ => (airyPhiK : ℂ) * cexp (-(I * ζ ^ 3 / 12))) := by fun_prop
  refine ⟨?_, ?_⟩
  · exact (hent.differentiableOn).mul (differentiableOn_airyFhat hf)
  · rw [closure_setOfPred_lt_im]
    exact (hent.continuous.continuousOn).mul (continuousOn_airyFhat hf)

/-- **The uniform `H^∞` bound** (Theorem 3.1 `(a)⇒(b)` of `GENERAL_THEOREMS`, with the norm bound): for `f ∈ G`
and `Im ζ ≥ 0`, `|F̃(ζ)| = |k e^{-iζ³/12} ∫ f(u) e^{-iζu} du| ≤ k ‖f‖_{L¹(ℝ)}`, `k = 2^{2/3}`. -/
theorem airyFtilde_norm_le {f : ℂ → ℂ} (hf : AiryClassG f) {ζ : ℂ} (hζ : 0 ≤ ζ.im) :
    ‖airyFtilde f ζ‖ ≤ airyPhiK * ∫ u : ℝ, ‖f (u : ℂ)‖ := by
  obtain ⟨A, M, hA, hpoly⟩ := airyFtilde_poly hf
  exact pl_halfPlane hA (airyFtilde_diffContOnCl hf) hpoly (norm_airyFtilde_real_le f) hζ

/-- info: 'FormalResearch.Special.pl_halfPlane' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.pl_halfPlane

/-- info: 'FormalResearch.Special.airyFtilde_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyFtilde_norm_le

end FormalResearch.Special

module

public import FormalResearch.Special.AiryCftQUnc
public import FormalResearch.Special.AiryEnvCalculus
public import FormalResearch.Special.AiryClarkLabel

/-!
# Sign uncertainty on the Airy class: `u₁ ≤ a₁` (Theorem B of the Airy–Poisson note), and the extremal

CFT `AIRY_POISSON.md` §4 (Theorem B, Proof 2 = translation proof), survey item T2.  Let `𝒢` be the class of entire `f` with
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`) and `f ∈ L¹(ℝ)`.

* `airy_sign_uncertainty` (**Theorem B, inequality**, proved): if `f ∈ 𝒢` is real on `ℝ`, `f ≢ 0`, `f ≥ 0` on `(-∞, u₁]` and `∫ f ≤ 0`, then
  `u₁ ≤ a₁` (`a₁ = airyZero 1 ≈ -2.338`, the first zero of `Ai`).  Proof (the note's translation argument with the unconditional Theorem Q (4),
  `airyQ_hasSum_unc`, in place of Theorem D): if `u₁ > a₁`, then for `0 < ε < u₁ - a₁` the translate `f(·+ε) ∈ 𝒢`
  (`e(u+ε) ≤ e(u) e^{-2ε Re √u} ≤ e(u)`, the shift inequality (E3) `airyEnv_add_real_le`; `(1+|u+ε|) ≤ (1+ε)(1+|u|)`), `∫ f(·+ε) = ∫ f ≤ 0`
  and every sample `f(a_n + ε) ≥ 0` (as `a_n + ε ≤ a₁ + ε < u₁`), so the nonnegative series `Σ f(a_n+ε)/Ai'(a_n)²` with sum `≤ 0` vanishes termwise;
  the `n = 1` term gives `f ≡ 0` on `(a₁, u₁)`, hence `f ≡ 0` (identity theorem).  The note proves this for `ν < -1/2`; Theorem Q (3)–(4)
  removes that restriction (`ν` arbitrary).
* `airyExtremal` (**the extremal `f_* = -Ai²/(u - a₁)`**, proved): `f_*(u) = -Ai(u) · dslope Ai a₁ (u)` is entire, real on `ℝ`, `f_* ≥ 0` on `(-∞, a₁]`,
  `f_* ≢ 0`, in `𝒢` (`‖f_*(u)‖ ≤ C (1+|u|)^{-1/2}·… e(u)`), and `∫ f_* = 0` (`airyExtremal_integral`: all samples `f_*(a_n)` vanish, Theorem Q (4)).
  Hence **`u₁ = a₁` is attained and the bound of `airy_sign_uncertainty` is sharp.**

The equality case (`u₁ = a₁ ⇒ f = c Ai²/(u - a₁)`, `c < 0`, and the converse) is proved in `AiryCftSignEquality` (samples) and
`AiryCftSignEqualityMain` (`airy_sign_equality`, `airy_sign_equality_iff`).  Not formalised: the Airy–Poisson identity
`Σ_n Φ_τ(a_n)/Ai'(a_n)² = 2^{-2/3}` (Theorem 1) with Lemma 3 (`u f_m = f_{Lm}`), and the note's Remark B.1 (tangent rigidity).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- **Shifted envelope bound.**  `f(u + ε)` satisfies the class bound with exponent `|ν|` and constant `C (1+ε)^{|ν|}`. -/
lemma airy_shift_bound {f : ℂ → ℂ} {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) {ε : ℝ} (hε : 0 ≤ ε) (u : ℂ) :
    ‖f (u + (ε : ℂ))‖ ≤ (C * (1 + ε) ^ |ν|) * (1 + ‖u‖) ^ |ν| * airyEnv u := by
  have h1 := hb (u + (ε : ℂ))
  have he : airyEnv (u + (ε : ℂ)) ≤ airyEnv u := by
    have h := airyEnv_add_real_le u ε
    have h2 : Real.exp (-2 * ε * airySqrtRe u) ≤ 1 := by
      apply Real.exp_le_one_iff.2
      have := airySqrtRe_nonneg u
      nlinarith
    calc airyEnv (u + (ε : ℂ)) ≤ airyEnv u * Real.exp (-2 * ε * airySqrtRe u) := h
      _ ≤ airyEnv u * 1 := by gcongr; exact (airyEnv_pos u).le
      _ = airyEnv u := mul_one _
  have hn : 1 + ‖u + (ε : ℂ)‖ ≤ (1 + ε) * (1 + ‖u‖) := by
    have : ‖u + (ε : ℂ)‖ ≤ ‖u‖ + ε := by
      calc ‖u + (ε : ℂ)‖ ≤ ‖u‖ + ‖(ε : ℂ)‖ := norm_add_le _ _
        _ = ‖u‖ + ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε]
    nlinarith [norm_nonneg u]
  have hp : (1 + ‖u + (ε : ℂ)‖) ^ ν ≤ (1 + ε) ^ |ν| * (1 + ‖u‖) ^ |ν| := by
    have hb1 : 1 ≤ 1 + ‖u + (ε : ℂ)‖ := by linarith [norm_nonneg (u + (ε : ℂ))]
    calc (1 + ‖u + (ε : ℂ)‖) ^ ν ≤ (1 + ‖u + (ε : ℂ)‖) ^ |ν| :=
          Real.rpow_le_rpow_of_exponent_le hb1 (le_abs_self ν)
      _ ≤ ((1 + ε) * (1 + ‖u‖)) ^ |ν| := Real.rpow_le_rpow (by linarith) hn (abs_nonneg ν)
      _ = _ := Real.mul_rpow (by linarith) (by linarith [norm_nonneg u])
  have hE := airyEnv_pos (u + (ε : ℂ))
  calc ‖f (u + (ε : ℂ))‖ ≤ C * (1 + ‖u + (ε : ℂ)‖) ^ ν * airyEnv (u + (ε : ℂ)) := h1
    _ ≤ C * ((1 + ε) ^ |ν| * (1 + ‖u‖) ^ |ν|) * airyEnv u := by
        gcongr
    _ = _ := by ring

/-- A real-valued entire function vanishing on a real interval vanishes identically. -/
lemma airy_entire_eq_zero_of_real_interval {f : ℂ → ℂ} (hf : Differentiable ℂ f) {a b : ℝ} (hab : a < b)
    (h0 : ∀ x : ℝ, a < x → x < b → f (x : ℂ) = 0) : ∀ z : ℂ, f z = 0 := by
  set x₀ : ℝ := (a + b) / 2 with hx₀
  have hmem : x₀ ∈ Ioo a b := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
  have hreal : ∃ᶠ x : ℝ in 𝓝[≠] x₀, f (x : ℂ) = 0 := by
    refine Filter.Eventually.frequently ?_
    have : ∀ᶠ x in 𝓝 x₀, x ∈ Ioo a b := Ioo_mem_nhds hmem.1 hmem.2
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds this] with x hx
    exact h0 x hx.1 hx.2
  have hmap : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (Complex.continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using hx
  have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), f z = 0 := hmap.frequently hreal
  have := AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (f := f) (U := univ)
    (fun z _ => hf.analyticAt z) isPreconnected_univ (mem_univ _) hfreq
  exact fun z => this (mem_univ z)

/-- `f(x) = Re f(x)` for `f` real on `ℝ`. -/
lemma airy_real_cast {f : ℂ → ℂ} (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (x : ℝ) :
    f (x : ℂ) = (((f (x : ℂ)).re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simpa using hreal x)

/-- **Translated quadrature** (Theorem Q (4) for `f(· + ε)`, `ε ≥ 0`, in real form): for `f` in the class and real on `ℝ`,
`Σ_{n ≥ 1} Re f(a_n + ε)/Ai'(a_n)² = ∫_ℝ Re f`, a series of the real numbers `f(a_n + ε)/Ai'(a_n)²`. -/
theorem airy_shift_hasSum {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {ε : ℝ} (hε : 0 ≤ ε) :
    HasSum (fun n : ℕ => (f (((airyZero (n + 1) + ε : ℝ)) : ℂ)).re / (airyAi' (airyZero (n + 1))) ^ 2)
      (∫ x : ℝ, (f (x : ℂ)).re) := by
  set g : ℂ → ℂ := fun u => f (u + (ε : ℂ)) with hg
  have hgd : Differentiable ℂ g := hf.comp (differentiable_id.add_const _)
  have hgc : ∀ x : ℝ, g (x : ℂ) = f (((x + ε : ℝ)) : ℂ) := fun x => by simp only [hg]; push_cast; rfl
  have hgi : Integrable (fun x : ℝ => g (x : ℂ)) := by
    simp_rw [hgc]
    exact hfi.comp_add_right ε
  have hgint : ∫ x : ℝ, g (x : ℂ) = ∫ x : ℝ, f (x : ℂ) := by
    simp_rw [hgc]
    exact integral_add_right_eq_self (fun x : ℝ => f (x : ℂ)) ε
  have hsum := airyQ_hasSum_unc hgd hgi (by positivity) (airy_shift_bound hC hb hε)
  rw [hgint] at hsum
  set t : ℕ → ℝ := fun n => (f (((airyZero (n + 1) + ε : ℝ)) : ℂ)).re / (airyAi' (airyZero (n + 1))) ^ 2 with ht
  have hterm : ∀ n : ℕ, (g (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).re = t n := by
    intro n
    rw [hgc, deriv_airyAiC_ofReal, airy_real_cast hreal (airyZero (n + 1) + ε)]
    simp only [ht]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
  have hre' : HasSum t ((∫ x : ℝ, f (x : ℂ)).re) := by
    have h := hsum.mapL Complex.reCLM
    have e : (fun n : ℕ => Complex.reCLM (g (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)) = t := by
      funext n; exact hterm n
    rw [e] at h
    exact h
  have hS : (∫ x : ℝ, f (x : ℂ)).re = ∫ x : ℝ, (f (x : ℂ)).re := by
    have := integral_re hfi
    simpa using this.symm
  rw [hS] at hre'
  exact hre'

lemma airyAi'_sq_first_ne : (airyAi' (airyZero 1)) ^ 2 ≠ 0 := by
  have := airyKer_pos' (airyZero 1)
  rw [airyAi_airyZero] at this
  have h2 : airyAi' (airyZero 1) ^ 2 - airyZero 1 * (0 : ℝ) ^ 2 = airyAi' (airyZero 1) ^ 2 := by ring
  rw [h2] at this
  exact this.ne'

/-- **Theorem B (sign uncertainty on the Airy class), inequality.**  `f` entire, `f ∈ L¹(ℝ)`, `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`),
real on `ℝ`, `f ≢ 0`, `f ≥ 0` on `(-∞, u₁]`, `∫ f ≤ 0`: then `u₁ ≤ a₁`. -/
theorem airy_sign_uncertainty {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {u₁ : ℝ} (hpos : ∀ x : ℝ, x ≤ u₁ → 0 ≤ (f (x : ℂ)).re)
    (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0) (hne : ∃ z : ℂ, f z ≠ 0) : u₁ ≤ airyZero 1 := by
  by_contra hlt
  push Not at hlt
  have hzero : ∀ ε : ℝ, 0 < ε → ε < u₁ - airyZero 1 → f (((airyZero 1 + ε : ℝ)) : ℂ) = 0 := by
    intro ε hε0 hεδ
    have hre' := airy_shift_hasSum hf hfi hC hb hreal hε0.le
    set t : ℕ → ℝ := fun n => (f (((airyZero (n + 1) + ε : ℝ)) : ℂ)).re / (airyAi' (airyZero (n + 1))) ^ 2 with ht
    have ht0 : ∀ n : ℕ, 0 ≤ t n := by
      intro n
      refine div_nonneg (hpos _ ?_) (sq_nonneg _)
      have h1 : airyZero (n + 1) ≤ airyZero 1 := airyZero_le_of_le le_rfl (by omega)
      linarith
    have hS0 : 0 ≤ ∫ x : ℝ, (f (x : ℂ)).re := hre'.nonneg ht0
    have hS1 : (∫ x : ℝ, (f (x : ℂ)).re) = 0 := le_antisymm hint hS0
    rw [hS1] at hre'
    have htz := (hasSum_zero_iff_of_nonneg ht0).1 hre'
    have h0 := congrFun htz 0
    simp only [ht, Pi.zero_apply, zero_add] at h0
    have hre0 : (f (((airyZero 1 + ε : ℝ)) : ℂ)).re = 0 := by
      rcases div_eq_zero_iff.1 h0 with h | h
      · exact h
      · exact absurd h airyAi'_sq_first_ne
    rw [airy_real_cast hreal, hre0]; simp
  obtain ⟨z, hz⟩ := hne
  refine hz (airy_entire_eq_zero_of_real_interval hf hlt (fun x hx1 hx2 => ?_) z)
  have := hzero (x - airyZero 1) (by linarith) (by linarith)
  rwa [show airyZero 1 + (x - airyZero 1) = x by ring] at this

/-- info: 'FormalResearch.Special.airy_sign_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sign_uncertainty

/-! ### The extremal `f_* = -Ai²/(u - a₁)` -/

/-- `e(u) ≥ exp(-(4/3)(1+R)³)` for `‖u‖ ≤ R`. -/
lemma airyEnv_ge_of_norm_le {u : ℂ} {R : ℝ} (hR : ‖u‖ ≤ R) :
    Real.exp (-(4 / 3) * (1 + R) ^ 3) ≤ airyEnv u := by
  unfold airyEnv
  apply Real.exp_le_exp.2
  have h1 : ‖u ^ (1 / 2 : ℂ)‖ ^ 2 = ‖u‖ := norm_cpow_half_sq u
  have h2 : ‖u ^ (1 / 2 : ℂ)‖ ≤ 1 + R := by
    set s := ‖u ^ (1 / 2 : ℂ)‖
    have hs0 : 0 ≤ s := norm_nonneg _
    nlinarith [norm_nonneg u]
  have h3 : (u ^ (3 / 2 : ℂ)).re ≤ (1 + R) ^ 3 := by
    rw [← cpow_half_cube]
    calc (((u ^ (1 / 2 : ℂ)) ^ 3)).re ≤ ‖(u ^ (1 / 2 : ℂ)) ^ 3‖ := Complex.re_le_norm _
      _ = ‖u ^ (1 / 2 : ℂ)‖ ^ 3 := norm_pow _ _
      _ ≤ (1 + R) ^ 3 := by gcongr
  linarith

/-- The extremal `f_*(u) = -Ai(u) · (Ai(u) - Ai(a₁))/(u - a₁)` (`= -Ai(u)²/(u - a₁)`, entire since `Ai(a₁) = 0`). -/
noncomputable def airyExtremal (u : ℂ) : ℂ :=
  -(airyAiC u * dslope airyAiC (airyZero 1 : ℂ) u)

lemma airyAiC_airyZero (n : ℕ) : airyAiC (airyZero n : ℂ) = 0 := by
  rw [airyAiC_ofReal, airyAi_airyZero]; simp

lemma differentiable_airyExtremal : Differentiable ℂ airyExtremal := by
  have h : Differentiable ℂ (dslope airyAiC (airyZero 1 : ℂ)) := by
    intro z
    have := (Complex.differentiableOn_dslope (s := univ) (f := airyAiC) (c := (airyZero 1 : ℂ))
      Filter.univ_mem).2 differentiable_airyAiC.differentiableOn
    exact (this z (mem_univ z)).differentiableAt Filter.univ_mem
  unfold airyExtremal
  exact (differentiable_airyAiC.mul h).neg

/-- `f_*(u) = -Ai(u)²/(u - a₁)` for `u ≠ a₁`. -/
lemma airyExtremal_eq {u : ℂ} (hu : u ≠ (airyZero 1 : ℂ)) :
    airyExtremal u = -(airyAiC u ^ 2 / (u - (airyZero 1 : ℂ))) := by
  unfold airyExtremal
  rw [dslope_of_ne _ hu, slope_def_field, airyAiC_airyZero]
  ring

lemma airyExtremal_ofReal (x : ℝ) :
    airyExtremal (x : ℂ) = ((-(airyAi x ^ 2 / (x - airyZero 1)) : ℝ) : ℂ) := by
  by_cases hx : (x : ℂ) = (airyZero 1 : ℂ)
  · have hx' : x = airyZero 1 := by exact_mod_cast hx
    unfold airyExtremal
    rw [hx, airyAiC_airyZero]
    simp [hx']
  · have hx' : x ≠ airyZero 1 := fun h => hx (by rw [h])
    rw [airyExtremal_eq hx, airyAiC_ofReal]
    push_cast
    ring

lemma airyExtremal_re (x : ℝ) : (airyExtremal (x : ℂ)).re = -(airyAi x ^ 2 / (x - airyZero 1)) := by
  rw [airyExtremal_ofReal, Complex.ofReal_re]

lemma airyExtremal_nonneg {x : ℝ} (hx : x ≤ airyZero 1) : 0 ≤ (airyExtremal (x : ℂ)).re := by
  rw [airyExtremal_re]
  have : airyAi x ^ 2 / (x - airyZero 1) ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith)
  linarith

lemma airyExtremal_ne_zero : ∃ z : ℂ, airyExtremal z ≠ 0 := by
  refine ⟨((0 : ℝ) : ℂ), fun h => ?_⟩
  have h1 := airyExtremal_re 0
  rw [h] at h1
  have ha := airyAi_pos (le_refl (0 : ℝ))
  have hz := airyZero_neg 1
  have : 0 < airyAi 0 ^ 2 / (0 - airyZero 1) := div_pos (by positivity) (by linarith)
  simp only [Complex.zero_re] at h1
  linarith

lemma airyExtremal_bdd_near : ∃ M : ℝ, 0 ≤ M ∧ ∀ u : ℂ, ‖u - (airyZero 1 : ℂ)‖ ≤ 1 → ‖airyExtremal u‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (airyZero 1 : ℂ) 1).exists_bound_of_continuousOn
    differentiable_airyExtremal.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun u hu => (hM u ?_).trans (le_max_left _ _)⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hu

/-- **The extremal is in the class** (`‖f_*(u)‖ ≤ C e(u)`, i.e. `ν = 0`; the note's `f_* ∈ 𝒢_{-3/2}` is stronger). -/
theorem airyExtremal_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖airyExtremal u‖ ≤ C * (1 + ‖u‖) ^ (0 : ℝ) * airyEnv u := by
  obtain ⟨M, hM0, hM⟩ := airyExtremal_bdd_near
  set R : ℝ := |airyZero 1| + 1 with hR
  set e₀ : ℝ := Real.exp (-(4 / 3) * (1 + R) ^ 3) with he₀
  have he₀pos : 0 < e₀ := Real.exp_pos _
  refine ⟨max 9 (M / e₀), by positivity, fun u => ?_⟩
  rw [Real.rpow_zero, mul_one]
  by_cases hu : ‖u - (airyZero 1 : ℂ)‖ ≤ 1
  · have hnu : ‖u‖ ≤ R := by
      calc ‖u‖ = ‖(u - (airyZero 1 : ℂ)) + (airyZero 1 : ℂ)‖ := by ring_nf
        _ ≤ ‖u - (airyZero 1 : ℂ)‖ + ‖(airyZero 1 : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 + |airyZero 1| := by
            gcongr
            rw [Complex.norm_real, Real.norm_eq_abs]
        _ = R := by rw [hR]; ring
    have h1 := airyEnv_ge_of_norm_le hnu
    calc ‖airyExtremal u‖ ≤ M := hM u hu
      _ = (M / e₀) * e₀ := by field_simp
      _ ≤ (M / e₀) * airyEnv u := by gcongr
      _ ≤ max (9 : ℝ) (M / e₀) * airyEnv u := mul_le_mul_of_nonneg_right (le_max_right (9 : ℝ) (M / e₀)) (airyEnv_pos u).le
  · push Not at hu
    have hne : u ≠ (airyZero 1 : ℂ) := fun h => by rw [h, sub_self, norm_zero] at hu; linarith
    rw [airyExtremal_eq hne, norm_neg, norm_div, norm_pow]
    have h1 := airyAiC_norm_sq_le u
    have h2 : (1 + ‖u‖) ^ (-(1 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg u]) (by norm_num)
    have he := airyEnv_pos u
    calc ‖airyAiC u‖ ^ 2 / ‖u - (airyZero 1 : ℂ)‖ ≤ ‖airyAiC u‖ ^ 2 := by
          apply div_le_self (sq_nonneg _) hu.le
      _ ≤ 9 * (1 + ‖u‖) ^ (-(1 / 2) : ℝ) * airyEnv u := h1
      _ ≤ 9 * 1 * airyEnv u := by gcongr
      _ ≤ max 9 (M / e₀) * airyEnv u := by
          have := le_max_left 9 (M / e₀)
          nlinarith

/-- **The extremal is in `L¹(ℝ)`.** -/
theorem airyExtremal_integrable : Integrable (fun x : ℝ => airyExtremal (x : ℂ)) := by
  obtain ⟨M, hM0, hM⟩ := airyExtremal_bdd_near
  set A : ℝ := 2 + |airyZero 1| with hA
  have hApos : 0 < A := by positivity
  set K : ℝ := max (9 * A) (M * A ^ (3 / 2 : ℝ)) with hK
  have hint : Integrable (fun x : ℝ => (1 + ‖x‖) ^ (-(3 / 2) : ℝ)) :=
    integrable_one_add_norm (E := ℝ) (by simp; norm_num)
  have hcont : Continuous (fun x : ℝ => airyExtremal (x : ℂ)) :=
    differentiable_airyExtremal.continuous.comp Complex.continuous_ofReal
  refine Integrable.mono' (hint.const_mul K) hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hx1 : 0 < 1 + ‖x‖ := by positivity
  by_cases hx : |x - airyZero 1| ≤ 1
  · have hxn : ‖(x : ℂ) - (airyZero 1 : ℂ)‖ ≤ 1 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hx
    have h1 := hM _ hxn
    have h2 : 1 + ‖x‖ ≤ A := by
      have : |x| ≤ |x - airyZero 1| + |airyZero 1| := by
        calc |x| = |(x - airyZero 1) + airyZero 1| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [Real.norm_eq_abs, hA]; linarith
    have h3 : A ^ (-(3 / 2) : ℝ) ≤ (1 + ‖x‖) ^ (-(3 / 2) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hx1 h2 (by norm_num)
    have h4 : M ≤ K * A ^ (-(3 / 2) : ℝ) := by
      have : M = (M * A ^ (3 / 2 : ℝ)) * A ^ (-(3 / 2) : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hApos]; norm_num
      rw [this]
      gcongr
      exact le_max_right _ _
    calc ‖airyExtremal (x : ℂ)‖ ≤ M := h1
      _ ≤ K * A ^ (-(3 / 2) : ℝ) := h4
      _ ≤ K * (1 + ‖x‖) ^ (-(3 / 2) : ℝ) := by gcongr
  · push Not at hx
    have hne : (x : ℂ) ≠ (airyZero 1 : ℂ) := fun h => by
      have : x = airyZero 1 := by exact_mod_cast h
      rw [this, sub_self, abs_zero] at hx; linarith
    have hnorm : ‖airyExtremal (x : ℂ)‖ = ‖airyAiC (x : ℂ)‖ ^ 2 / |x - airyZero 1| := by
      rw [airyExtremal_eq hne, norm_neg, norm_div, norm_pow, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hAi : ‖airyAiC (x : ℂ)‖ ^ 2 ≤ 9 * (1 + ‖x‖) ^ (-(1 / 2) : ℝ) := by
      have h := airyAiC_norm_sq_le (x : ℂ)
      rw [Complex.norm_real] at h
      refine h.trans ?_
      have := airyEnv_ofReal_le_one x
      have hp : 0 ≤ 9 * (1 + ‖x‖) ^ (-(1 / 2) : ℝ) := by positivity
      nlinarith
    have hden : 1 + ‖x‖ ≤ A * |x - airyZero 1| := by
      have : |x| ≤ |x - airyZero 1| + |airyZero 1| := by
        calc |x| = |(x - airyZero 1) + airyZero 1| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      rw [Real.norm_eq_abs, hA]; nlinarith [abs_nonneg (airyZero 1)]
    have hpos : 0 < |x - airyZero 1| := by linarith
    have hsplit : (1 + ‖x‖) ^ (-(3 / 2) : ℝ) = (1 + ‖x‖) ^ (-(1 / 2) : ℝ) * (1 + ‖x‖)⁻¹ := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hx1]; norm_num
    rw [hnorm, div_le_iff₀ hpos]
    calc ‖airyAiC (x : ℂ)‖ ^ 2 ≤ 9 * (1 + ‖x‖) ^ (-(1 / 2) : ℝ) := hAi
      _ = 9 * (1 + ‖x‖) ^ (-(1 / 2) : ℝ) * (1 + ‖x‖)⁻¹ * (1 + ‖x‖) := by field_simp
      _ ≤ 9 * (1 + ‖x‖) ^ (-(1 / 2) : ℝ) * (1 + ‖x‖)⁻¹ * (A * |x - airyZero 1|) := by gcongr
      _ = (9 * A) * ((1 + ‖x‖) ^ (-(3 / 2) : ℝ)) * |x - airyZero 1| := by rw [hsplit]; ring
      _ ≤ K * ((1 + ‖x‖) ^ (-(3 / 2) : ℝ)) * |x - airyZero 1| := by
          gcongr; exact le_max_left _ _

/-- **`∫ f_* = 0`** (all samples `f_*(a_n)` vanish, Theorem Q (4)). -/
theorem airyExtremal_integral : ∫ x : ℝ, airyExtremal (x : ℂ) = 0 := by
  obtain ⟨C, hC, hb⟩ := airyExtremal_bound
  have h := airyQ_hasSum_unc differentiable_airyExtremal airyExtremal_integrable hC hb
  have h0 : ∀ n : ℕ, airyExtremal (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2 = 0 := by
    intro n
    unfold airyExtremal
    rw [airyAiC_airyZero]; simp
  simp_rw [h0] at h
  exact h.unique hasSum_zero

/-- **Sharpness of Theorem B**: the extremal `f_* = -Ai²/(u - a₁)` is real, entire, in the class, `f_* ≥ 0` on `(-∞, a₁]`, `f_* ≢ 0` and
`∫ f_* = 0`; so `u₁ = a₁` is attained in `airy_sign_uncertainty`. -/
theorem airyExtremal_attains :
    Differentiable ℂ airyExtremal ∧ Integrable (fun x : ℝ => airyExtremal (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖airyExtremal u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (airyExtremal (x : ℂ)).im = 0) ∧ (∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (airyExtremal (x : ℂ)).re) ∧
      (∫ x : ℝ, (airyExtremal (x : ℂ)).re) = 0 ∧ (∃ z : ℂ, airyExtremal z ≠ 0) := by
  obtain ⟨C, hC, hb⟩ := airyExtremal_bound
  refine ⟨differentiable_airyExtremal, airyExtremal_integrable, ⟨C, 0, hC, hb⟩,
    fun x => by rw [airyExtremal_ofReal, Complex.ofReal_im], fun x hx => airyExtremal_nonneg hx, ?_,
    airyExtremal_ne_zero⟩
  have h2 : ∫ x : ℝ, (airyExtremal (x : ℂ)).re = (∫ x : ℝ, airyExtremal (x : ℂ)).re :=
    integral_re airyExtremal_integrable
  rw [h2, airyExtremal_integral]; simp

/-- info: 'FormalResearch.Special.airyExtremal_attains' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyExtremal_attains

end FormalResearch.Special

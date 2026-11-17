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

Not formalised: the equality case of Theorem B (`u₁ = a₁ ⇒ f = c Ai²/(u - a₁)`, `c < 0`), which needs the double-zero/Liouville argument on good
circles (lower bound `|Ai| ≥ c (1+|u|)^{-1/4} e^{1/2}`, `f/Ai²` polynomial plus a simple pole, `Ai² P ∈ L¹ ⇒ P = 0`), and the Airy–Poisson identity
`Σ_n Φ_τ(a_n)/Ai'(a_n)² = 2^{-2/3}` (Theorem 1) with Lemma 3 (`u f_m = f_{Lm}`).
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

/-- **Theorem B (sign uncertainty on the Airy class), inequality.**  `f` entire, `f ∈ L¹(ℝ)`, `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`),
real on `ℝ`, `f ≢ 0`, `f ≥ 0` on `(-∞, u₁]`, `∫ f ≤ 0`: then `u₁ ≤ a₁`. -/
theorem airy_sign_uncertainty {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) {u₁ : ℝ} (hpos : ∀ x : ℝ, x ≤ u₁ → 0 ≤ (f (x : ℂ)).re)
    (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0) (hne : ∃ z : ℂ, f z ≠ 0) : u₁ ≤ airyZero 1 := by
  by_contra hlt
  push Not at hlt
  have hcast : ∀ x : ℝ, f (x : ℂ) = (((f (x : ℂ)).re : ℝ) : ℂ) := fun x =>
    Complex.ext (by simp) (by simpa using hreal x)
  have hzero : ∀ ε : ℝ, 0 < ε → ε < u₁ - airyZero 1 → f (((airyZero 1 + ε : ℝ)) : ℂ) = 0 := by
    intro ε hε0 hεδ
    set g : ℂ → ℂ := fun u => f (u + (ε : ℂ)) with hg
    have hgd : Differentiable ℂ g := hf.comp (differentiable_id.add_const _)
    have hgc : ∀ x : ℝ, g (x : ℂ) = f (((x + ε : ℝ)) : ℂ) := fun x => by simp only [hg]; push_cast; rfl
    have hgi : Integrable (fun x : ℝ => g (x : ℂ)) := by
      simp_rw [hgc]
      exact hfi.comp_add_right ε
    have hgint : ∫ x : ℝ, g (x : ℂ) = ∫ x : ℝ, f (x : ℂ) := by
      simp_rw [hgc]
      exact integral_add_right_eq_self (fun x : ℝ => f (x : ℂ)) ε
    have hsum := airyQ_hasSum_unc hgd hgi (by positivity) (airy_shift_bound hC hb hε0.le)
    rw [hgint] at hsum
    have hre := hsum.mapL Complex.reCLM
    set t : ℕ → ℝ := fun n => (f (((airyZero (n + 1) + ε : ℝ)) : ℂ)).re / (airyAi' (airyZero (n + 1))) ^ 2 with ht
    have hterm : ∀ n : ℕ, (g (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2).re = t n := by
      intro n
      rw [hgc, deriv_airyAiC_ofReal, hcast (airyZero (n + 1) + ε)]
      simp only [ht]
      rw [← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
    have hre' : HasSum t ((∫ x : ℝ, f (x : ℂ)).re) := by
      have h := hsum.mapL Complex.reCLM
      have e : (fun n : ℕ => Complex.reCLM (g (airyZero (n + 1) : ℂ) / (deriv airyAiC (airyZero (n + 1) : ℂ)) ^ 2)) = t := by
        funext n; exact hterm n
      rw [e] at h
      exact h
    have ht0 : ∀ n : ℕ, 0 ≤ t n := by
      intro n
      refine div_nonneg (hpos _ ?_) (sq_nonneg _)
      have h1 : airyZero (n + 1) ≤ airyZero 1 := airyZero_le_of_le le_rfl (by omega)
      linarith
    have hS : (∫ x : ℝ, f (x : ℂ)).re = ∫ x : ℝ, (f (x : ℂ)).re := by
      have := integral_re hfi
      simpa using this.symm
    have hS0 : 0 ≤ (∫ x : ℝ, f (x : ℂ)).re := hre'.nonneg ht0
    have hS1 : (∫ x : ℝ, f (x : ℂ)).re = 0 := by rw [hS] at hS0 ⊢; linarith
    rw [hS1] at hre'
    have htz := (hasSum_zero_iff_of_nonneg ht0).1 hre'
    have h0 := congrFun htz 0
    simp only [ht, Pi.zero_apply, zero_add] at h0
    have hd : (airyAi' (airyZero 1)) ^ 2 ≠ 0 := by
      have := airyKer_pos' (airyZero 1)
      rw [airyAi_airyZero] at this
      have h2 : airyAi' (airyZero 1) ^ 2 - airyZero 1 * (0 : ℝ) ^ 2 = airyAi' (airyZero 1) ^ 2 := by ring
      rw [h2] at this
      exact this.ne'
    have hre0 : (f (((airyZero 1 + ε : ℝ)) : ℂ)).re = 0 := by
      rcases div_eq_zero_iff.1 h0 with h | h
      · exact h
      · exact absurd h hd
    rw [hcast, hre0]; simp
  obtain ⟨z, hz⟩ := hne
  refine hz (airy_entire_eq_zero_of_real_interval hf hlt (fun x hx1 hx2 => ?_) z)
  have := hzero (x - airyZero 1) (by linarith) (by linarith)
  rwa [show airyZero 1 + (x - airyZero 1) = x by ring] at this

/-- info: 'FormalResearch.Special.airy_sign_uncertainty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sign_uncertainty

end FormalResearch.Special

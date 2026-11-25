module

public import FormalResearch.SignUncertainty.MiddleBandRegions

/-!
# GT.2a: two integrations by parts for a general phase on a half-line

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Outer pieces" (main outer piece on the `τ`-line, where
the phase is `c Φ(τ; L)`, not cubic).

For a phase `ψ ∈ C³` with `p ≤ |ψ'|`, `|ψ''| ≤ M₂`, `|ψ'''| ≤ M₃` on the support of an amplitude `a ∈ C²` with `‖a^{(r)}(x)‖ ≤ B x^{-s}`
(`r ≤ 2`, `x ≥ α > 0`, `s > 1`):

* `two_ibp_phase_compact`: `a` supported in `[α, β]`: `‖∫ a e^{iψ}‖ ≤ B α^{1-s}/(s-1) · Λ`, `Λ = p⁻² + 3M₂p⁻³ + M₃p⁻³ + 3M₂²p⁻⁴`;
* `two_ibp_phase_tail`: `a` supported in `[α, ∞)`, with the factor `1 + 4K₁/α + 4K₂/α²` from the truncation `ϑ(x/R)` (`Prof ϑ K₁ K₂`);
* `two_ibp_phase_tail_neg`: the mirror half-line `(-∞, -α]` (reflection `x ↦ -x`, `ψ ↦ -ψ(-·)`).

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- The phase factor `Λ(p, M₂, M₃) = p⁻² + 3M₂p⁻³ + M₃p⁻³ + 3M₂²p⁻⁴` of two integrations by parts. -/
noncomputable def ibpLam (p M2 M3 : ℝ) : ℝ := 1 / p ^ 2 + 3 * M2 / p ^ 3 + M3 / p ^ 3 + 3 * M2 ^ 2 / p ^ 4

lemma ibpLam_nonneg {p M2 M3 : ℝ} (hp : 0 < p) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) : 0 ≤ ibpLam p M2 M3 := by
  unfold ibpLam; positivity

/-- Two integrations by parts on `[α, β]`, general phase. -/
theorem two_ibp_phase_compact {a : ℝ → ℂ} {ψ : ℝ → ℝ} {α β B p M2 M3 s : ℝ} (hαβ : α ≤ β) (hα : 0 < α) (hs : 1 < s)
    (hB : 0 ≤ B) (hp : 0 < p) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (ha : ContDiff ℝ 2 a)
    (hsupp : ∀ x, x ∉ Set.Icc α β → a x = 0)
    (hb0 : ∀ x ∈ Set.Icc α β, ‖a x‖ ≤ B * x ^ (-s)) (hb1 : ∀ x ∈ Set.Icc α β, ‖deriv a x‖ ≤ B * x ^ (-s))
    (hb2 : ∀ x ∈ Set.Icc α β, ‖deriv (deriv a) x‖ ≤ B * x ^ (-s))
    (hψ : ContDiff ℝ 3 ψ) (hψ1 : ∀ x ∈ Set.Icc α β, p ≤ |deriv ψ x|)
    (hψ2 : ∀ x ∈ Set.Icc α β, |deriv (deriv ψ) x| ≤ M2)
    (hψ3 : ∀ x ∈ Set.Icc α β, |deriv (deriv (deriv ψ)) x| ≤ M3) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤ B * (α ^ (1 - s) / (s - 1)) * ibpLam p M2 M3 := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hda : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdda : Continuous (deriv (deriv a)) := hda.continuous_deriv le_rfl
  have hint2 : IntegrableOn (deriv (deriv a)) (Set.Icc α β) := hdda.integrableOn_Icc
  have ha2 : ∀ x ∉ (∅ : Set ℝ), DifferentiableAt ℝ (deriv a) x := fun x _ => hda.differentiable (by norm_num) x
  have hne : ∀ x ∈ Set.Icc α β, deriv ψ x ≠ 0 := by
    intro x hx h
    have := hψ1 x hx
    rw [h, abs_zero] at this
    linarith
  have hmain := two_ibp_phase_abs hαβ ha1 ∅ Set.countable_empty ha2 hint2 hsupp hψ hne
  refine hmain.trans ?_
  set g : ℝ → ℝ := fun x => B * ibpLam p M2 M3 * x ^ (-s) with hg
  have hΛ := ibpLam_nonneg hp hM2 hM3
  have hpt : ∀ x ∈ Set.Icc α β, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) ≤ g x := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have hxs : 0 ≤ x ^ (-s) := Real.rpow_nonneg hx0.le _
    have hD : 0 ≤ B * x ^ (-s) := mul_nonneg hB hxs
    have hpd := hψ1 x hx
    have hd2 : p ^ 2 ≤ deriv ψ x ^ 2 := by
      have := pow_le_pow_left₀ hp.le hpd 2
      rwa [sq_abs] at this
    have hd3 : p ^ 3 ≤ |deriv ψ x| ^ 3 := pow_le_pow_left₀ hp.le hpd 3
    have hd4 : p ^ 4 ≤ deriv ψ x ^ 4 := by
      have h4 := pow_le_pow_left₀ hp.le hpd 4
      have : |deriv ψ x| ^ 4 = deriv ψ x ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      rwa [this] at h4
    have t1 : ‖deriv (deriv a) x‖ / deriv ψ x ^ 2 ≤ (B * x ^ (-s)) / p ^ 2 :=
      div_le_div₀ hD (hb2 x hx) (by positivity) hd2
    have t2 : 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3 ≤ 3 * (B * x ^ (-s)) * M2 / p ^ 3 :=
      div_le_div₀ (by positivity)
        (mul_le_mul (mul_le_mul_of_nonneg_left (hb1 x hx) (by norm_num)) (hψ2 x hx) (abs_nonneg _) (by positivity))
        (by positivity) hd3
    have t3 : ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3 ≤ (B * x ^ (-s)) * M3 / p ^ 3 :=
      div_le_div₀ (by positivity) (mul_le_mul (hb0 x hx) (hψ3 x hx) (abs_nonneg _) hD) (by positivity) hd3
    have t4 : 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4 ≤ 3 * (B * x ^ (-s)) * M2 ^ 2 / p ^ 4 := by
      refine div_le_div₀ (by positivity) ?_ (by positivity) hd4
      have h2 : deriv (deriv ψ) x ^ 2 ≤ M2 ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) (hψ2 x hx) 2
        rwa [sq_abs] at this
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hb0 x hx) (by norm_num)) h2 (sq_nonneg _) (by positivity)
    have : g x = (B * x ^ (-s)) / p ^ 2 + 3 * (B * x ^ (-s)) * M2 / p ^ 3 + (B * x ^ (-s)) * M3 / p ^ 3 +
        3 * (B * x ^ (-s)) * M2 ^ 2 / p ^ 4 := by
      simp only [hg, ibpLam]; ring
    rw [this]; linarith
  have hgint : IntegrableOn g (Set.Icc α β) := by
    have : ContinuousOn g (Set.Icc α β) := by
      refine ContinuousOn.mul continuousOn_const ?_
      exact ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (lt_of_lt_of_le hα hx.1).ne')
    exact this.integrableOn_Icc
  have hgIoi : IntegrableOn g (Set.Ioi α) := by
    refine Integrable.const_mul ?_ _
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hα
  calc ∫ x in Set.Icc α β, (‖deriv (deriv a) x‖ / deriv ψ x ^ 2
        + 3 * ‖deriv a x‖ * |deriv (deriv ψ) x| / |deriv ψ x| ^ 3
        + ‖a x‖ * |deriv (deriv (deriv ψ)) x| / |deriv ψ x| ^ 3
        + 3 * ‖a x‖ * deriv (deriv ψ) x ^ 2 / deriv ψ x ^ 4) ≤ ∫ x in Set.Icc α β, g x := by
        refine integral_mono_of_nonneg (ae_of_all _ fun x => by positivity) hgint ?_
        exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hpt)
    _ ≤ ∫ x in Set.Ioi α, g x := by
        refine setIntegral_mono_set hgIoi ?_ ?_
        · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx => ?_)
          have : 0 < x := lt_trans hα hx
          simp only [hg]; positivity
        · exact (Filter.eventuallySubset_antisymm_iff.1 (Ioc_ae_eq_Icc (μ := volume)).symm).1.trans (Ioc_subset_Ioi_self.eventuallySubset)
    _ = B * (α ^ (1 - s) / (s - 1)) * ibpLam p M2 M3 := by
        simp only [hg]
        rw [integral_const_mul, mb_tail_pow hα hs]; ring

/-- Bounds for the truncated amplitude `ϑ(·/R) a` on `[α, ∞)`: all three orders by `(1 + 4K₁/α + 4K₂/α²) B x^{-s}`. -/
lemma tail_trunc_bounds {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {a : ℝ → ℂ} {α B s R : ℝ} (hα : 0 < α) (hB : 0 ≤ B)
    (hR : 0 < R) (ha : ContDiff ℝ 2 a)
    (hb0 : ∀ x, α ≤ x → ‖a x‖ ≤ B * x ^ (-s)) (hb1 : ∀ x, α ≤ x → ‖deriv a x‖ ≤ B * x ^ (-s))
    (hb2 : ∀ x, α ≤ x → ‖deriv (deriv a) x‖ ≤ B * x ^ (-s)) {x : ℝ} (hx : α ≤ x) :
    ‖(ϑ (x / R) : ℂ) * a x‖ ≤ (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * x ^ (-s) ∧
    ‖deriv (fun y => (ϑ (y / R) : ℂ) * a y) x‖ ≤ (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * x ^ (-s) ∧
    ‖deriv (deriv (fun y => (ϑ (y / R) : ℂ) * a y)) x‖ ≤ (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * x ^ (-s) := by
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  have hx0 : 0 < x := lt_of_lt_of_le hα hx
  have hcut := hϑ.cut hR
  have hxs : 0 ≤ x ^ (-s) := Real.rpow_nonneg hx0.le _
  have hBx : 0 ≤ B * x ^ (-s) := mul_nonneg hB hxs
  have hζ : |ϑ (x / R)| ≤ 1 := hcut.bound0 x
  have hζ1 : |deriv (fun u => ϑ (u / R)) x| ≤ 2 * K1 / α := by
    have := hcut.bound1 x hx0.ne'
    rw [abs_of_pos hx0] at this
    rw [le_div_iff₀ hα]
    nlinarith [abs_nonneg (deriv (fun u => ϑ (u / R)) x)]
  have hζ2 : |deriv (deriv (fun u => ϑ (u / R))) x| ≤ 4 * K2 / α ^ 2 := by
    have := hcut.bound2 x hx0.ne'
    rw [le_div_iff₀ (by positivity)]
    have hxx : α ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hα.le hx 2
    nlinarith [abs_nonneg (deriv (deriv (fun u => ϑ (u / R))) x)]
  set ζ : ℝ → ℝ := fun u => ϑ (u / R) with hζdef
  have hζd : ContDiff ℝ 2 ζ := hcut.contDiff
  have haD : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hζD : Differentiable ℝ ζ := hζd.differentiable (by norm_num)
  have hc1 : 0 ≤ 2 * K1 / α := by positivity
  have hc2 : 0 ≤ 4 * K2 / α ^ 2 := by positivity
  have e1 : deriv (fun y => (ζ y : ℂ) * a y) x = ((deriv ζ x : ℝ) : ℂ) * a x + (ζ x : ℂ) * deriv a x :=
    (mbt_hasDerivAt_mul hζD haD x).deriv
  have a0 := hb0 x hx
  have a1 := hb1 x hx
  have a2 := hb2 x hx
  have hKt : (1 : ℝ) ≤ 1 + 4 * K1 / α + 4 * K2 / α ^ 2 := by
    have : 0 ≤ 4 * K1 / α := by positivity
    have : 0 ≤ 4 * K2 / α ^ 2 := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |ζ x| * ‖a x‖ ≤ 1 * (B * x ^ (-s)) := mul_le_mul hζ a0 (norm_nonneg _) zero_le_one
      _ ≤ (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * (B * x ^ (-s)) := by
        exact mul_le_mul_of_nonneg_right hKt hBx
      _ = _ := by ring
  · rw [e1]
    refine mbt_norm_two.trans ?_
    calc |deriv ζ x| * ‖a x‖ + |ζ x| * ‖deriv a x‖ ≤ (2 * K1 / α) * (B * x ^ (-s)) + 1 * (B * x ^ (-s)) :=
          add_le_add (mul_le_mul hζ1 a0 (norm_nonneg _) hc1) (mul_le_mul hζ a1 (norm_nonneg _) zero_le_one)
      _ ≤ (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * (B * x ^ (-s)) := by
        have e : (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * (B * x ^ (-s)) = (2 * K1 / α) * (B * x ^ (-s)) + 1 * (B * x ^ (-s)) +
            (2 * K1 / α + 4 * K2 / α ^ 2) * (B * x ^ (-s)) := by ring
        rw [e]
        have : 0 ≤ (2 * K1 / α + 4 * K2 / α ^ 2) * (B * x ^ (-s)) := mul_nonneg (add_nonneg hc1 hc2) hBx
        linarith
      _ = _ := by ring
  · rw [mbt_deriv2_mul hζd ha x]
    refine mbt_norm_three.trans ?_
    calc |deriv (deriv ζ) x| * ‖a x‖ + 2 * |deriv ζ x| * ‖deriv a x‖ + |ζ x| * ‖deriv (deriv a) x‖
        ≤ (4 * K2 / α ^ 2) * (B * x ^ (-s)) + 2 * (2 * K1 / α) * (B * x ^ (-s)) + 1 * (B * x ^ (-s)) :=
          add_le_add (add_le_add (mul_le_mul hζ2 a0 (norm_nonneg _) hc2)
            (mul_le_mul (mul_le_mul_of_nonneg_left hζ1 (by norm_num)) a1 (norm_nonneg _) (by positivity)))
            (mul_le_mul hζ a2 (norm_nonneg _) zero_le_one)
      _ = (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * x ^ (-s) := by ring

/-- **Two integrations by parts on `[α, ∞)`, general phase.** -/
theorem two_ibp_phase_tail {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {a : ℝ → ℂ} {ψ : ℝ → ℝ} {α B p M2 M3 s : ℝ}
    (hα : 0 < α) (hs : 1 < s) (hB : 0 ≤ B) (hp : 0 < p) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3) (ha : ContDiff ℝ 2 a)
    (hψ : ContDiff ℝ 3 ψ) (hsupp : ∀ x, x < α → a x = 0)
    (hb0 : ∀ x, α ≤ x → ‖a x‖ ≤ B * x ^ (-s)) (hb1 : ∀ x, α ≤ x → ‖deriv a x‖ ≤ B * x ^ (-s))
    (hb2 : ∀ x, α ≤ x → ‖deriv (deriv a) x‖ ≤ B * x ^ (-s))
    (hψ1 : ∀ x, α ≤ x → p ≤ |deriv ψ x|) (hψ2 : ∀ x, α ≤ x → |deriv (deriv ψ) x| ≤ M2)
    (hψ3 : ∀ x, α ≤ x → |deriv (deriv (deriv ψ)) x| ≤ M3) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * (α ^ (1 - s) / (s - 1)) * ibpLam p M2 M3 := by
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  set Kt : ℝ := 1 + 4 * K1 / α + 4 * K2 / α ^ 2 with hKt
  have hKt0 : 0 ≤ Kt := by rw [hKt]; positivity
  have hbound : ∀ R : ℝ, α ≤ R →
      ‖∫ x, (ϑ (x / R) : ℂ) * a x * Complex.exp (Complex.I * ψ x)‖ ≤ Kt * B * (α ^ (1 - s) / (s - 1)) * ibpLam p M2 M3 := by
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le hα hR
    have hcut := hϑ.cut hRpos
    have hAR : ContDiff ℝ 2 (fun x => (ϑ (x / R) : ℂ) * a x) :=
      (Complex.ofRealCLM.contDiff.comp hcut.contDiff).mul ha
    have hsuppR : ∀ x, x ∉ Set.Icc α (2 * R) → (ϑ (x / R) : ℂ) * a x = 0 := by
      intro x hx
      by_cases h1 : x < α
      · simp [hsupp x h1]
      · have h2 : 2 * R < x := lt_of_not_ge fun hc => hx ⟨not_lt.1 h1, hc⟩
        have h3 : 2 ≤ |x / R| := by
          rw [abs_of_pos (div_pos (by linarith) hRpos), le_div_iff₀ hRpos]; linarith
        simp [hϑ.zero _ h3]
    have hB' : 0 ≤ Kt * B := mul_nonneg hKt0 hB
    have := two_ibp_phase_compact (a := fun x => (ϑ (x / R) : ℂ) * a x) (ψ := ψ) (α := α) (β := 2 * R) (B := Kt * B)
      (p := p) (M2 := M2) (M3 := M3) (s := s) (by linarith) hα hs hB' hp hM2 hM3 hAR hsuppR
      (fun x hx => (tail_trunc_bounds hϑ hα hB hRpos ha hb0 hb1 hb2 hx.1).1)
      (fun x hx => (tail_trunc_bounds hϑ hα hB hRpos ha hb0 hb1 hb2 hx.1).2.1)
      (fun x hx => (tail_trunc_bounds hϑ hα hB hRpos ha hb0 hb1 hb2 hx.1).2.2) hψ
      (fun x hx => hψ1 x hx.1) (fun x hx => hψ2 x hx.1) (fun x hx => hψ3 x hx.1)
    simpa [mul_assoc] using this
  -- dominated convergence
  have hlim : Filter.Tendsto (fun R : ℝ => ∫ x, (ϑ (x / R) : ℂ) * a x * Complex.exp (Complex.I * ψ x)) Filter.atTop
      (𝓝 (∫ x, a x * Complex.exp (Complex.I * ψ x))) := by
    have hbI : IntegrableOn (fun y : ℝ => B * y ^ (-s)) (Set.Ici α) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hα) B
    have hψc : Continuous ψ := hψ.continuous
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => Set.indicator (Set.Ici α) (fun y => B * y ^ (-s)) x) ?_ ?_
      (hbI.integrable_indicator measurableSet_Ici) ?_
    · refine Filter.Eventually.of_forall (fun R => ?_)
      have hθc : Continuous (fun x : ℝ => (ϑ (x / R) : ℂ)) :=
        Complex.continuous_ofReal.comp (hϑ.contDiff.continuous.comp (continuous_id.div_const R))
      exact Continuous.aestronglyMeasurable ((hθc.mul ha.continuous).mul
        (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hψc))))
    · refine Filter.Eventually.of_forall (fun R => ae_of_all _ (fun x => ?_))
      by_cases hx : x < α
      · have h0 : a x = 0 := hsupp x hx
        have hxn : x ∉ Set.Ici α := fun h => absurd (Set.mem_Ici.1 h) (not_le.2 hx)
        simp [h0, hxn]
      · have hx' : α ≤ x := not_lt.1 hx
        have hthn : ‖(ϑ (x / R) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hϑ.range _).1]
          exact (hϑ.range _).2
        rw [Set.indicator_of_mem (Set.mem_Ici.2 hx'), norm_mul, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
        exact (mul_le_of_le_one_left (norm_nonneg _) hthn).trans (hb0 x hx')
    · refine Filter.Eventually.of_forall (fun x => ?_)
      by_cases hx : x < α
      · have h0 : a x = 0 := hsupp x hx
        simp only [h0, zero_mul, mul_zero]
        exact tendsto_const_nhds
      · have hx' : α ≤ x := not_lt.1 hx
        have hpos : 0 < x := lt_of_lt_of_le hα hx'
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.eventually_ge_atTop x] with R hR
        have hRpos : 0 < R := lt_of_lt_of_le hpos hR
        have h1 : ϑ (x / R) = 1 := by
          apply hϑ.one
          rw [abs_of_pos (div_pos hpos hRpos), div_le_one hRpos]; exact hR
        rw [h1]
        simp
  have hnorm := hlim.norm
  refine le_of_tendsto hnorm (Filter.eventually_atTop.2 ⟨α, fun R hR => ?_⟩)
  exact hbound R hR

/-- Mirror of `two_ibp_phase_tail` on `(-∞, -α]`, by the reflection `a ↦ conj a(-·)`, `ψ ↦ -ψ(-·)`. -/
theorem two_ibp_phase_tail_neg {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {a : ℝ → ℂ} {ψ : ℝ → ℝ}
    {α B p M2 M3 s : ℝ} (hα : 0 < α) (hs : 1 < s) (hB : 0 ≤ B) (hp : 0 < p) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (ha : ContDiff ℝ 2 a) (hψ : ContDiff ℝ 3 ψ) (hsupp : ∀ x, -α < x → a x = 0)
    (hb0 : ∀ x, x ≤ -α → ‖a x‖ ≤ B * (-x) ^ (-s)) (hb1 : ∀ x, x ≤ -α → ‖deriv a x‖ ≤ B * (-x) ^ (-s))
    (hb2 : ∀ x, x ≤ -α → ‖deriv (deriv a) x‖ ≤ B * (-x) ^ (-s))
    (hψ1 : ∀ x, x ≤ -α → p ≤ |deriv ψ x|) (hψ2 : ∀ x, x ≤ -α → |deriv (deriv ψ) x| ≤ M2)
    (hψ3 : ∀ x, x ≤ -α → |deriv (deriv (deriv ψ)) x| ≤ M3) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      (1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * (α ^ (1 - s) / (s - 1)) * ibpLam p M2 M3 := by
  set b : ℝ → ℂ := fun y => star (a (-y)) with hb
  set ψt : ℝ → ℝ := fun y => -ψ (-y) with hψt
  have haD : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hda : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdaD : Differentiable ℝ (deriv a) := hda.differentiable (by norm_num)
  have hbC : ContDiff ℝ 2 b :=
    (Complex.conjCLE.contDiff.comp (ha.comp contDiff_neg) : ContDiff ℝ 2 (fun y => Complex.conjCLE (a (-y))))
  have hd1 : ∀ y, deriv b y = -star (deriv a (-y)) := fun y => mbt_deriv_reflect haD y
  have hd1' : deriv b = fun y => -star (deriv a (-y)) := funext hd1
  have hd2 : ∀ y, deriv (deriv b) y = star (deriv (deriv a) (-y)) := by
    intro y
    rw [hd1']
    have := mbt_deriv_reflect hdaD y
    have h3 : deriv (fun y => -star (deriv a (-y))) y = -deriv (fun y => star (deriv a (-y))) y := by
      rw [deriv.fun_neg]
    rw [h3, this, neg_neg]
  -- derivatives of the reflected phase
  have ψC : ContDiff ℝ 3 ψt := (hψ.comp contDiff_neg).neg
  have p1 : ∀ y, deriv ψt y = deriv ψ (-y) := by
    intro y
    simp only [hψt]
    rw [deriv.fun_neg, deriv_comp_neg]; ring
  have p1' : deriv ψt = fun y => deriv ψ (-y) := funext p1
  have p2 : ∀ y, deriv (deriv ψt) y = -deriv (deriv ψ) (-y) := by
    intro y; rw [p1']; exact deriv_comp_neg _ _
  have p2' : deriv (deriv ψt) = fun y => -deriv (deriv ψ) (-y) := funext p2
  have p3 : ∀ y, deriv (deriv (deriv ψt)) y = deriv (deriv (deriv ψ)) (-y) := by
    intro y; rw [p2', deriv.fun_neg, deriv_comp_neg]; ring
  have hmain := two_ibp_phase_tail hϑ (a := b) (ψ := ψt) (α := α) (B := B) (p := p) (M2 := M2) (M3 := M3) (s := s)
    hα hs hB hp hM2 hM3 hbC ψC
    (fun x hx => by simp [hb, hsupp (-x) (by linarith)])
    (fun x hx => by
      have := hb0 (-x) (by linarith)
      simpa [hb, neg_neg] using this)
    (fun x hx => by
      have := hb1 (-x) (by linarith)
      rw [hd1]; simpa [norm_neg, neg_neg] using this)
    (fun x hx => by
      have := hb2 (-x) (by linarith)
      rw [hd2]; simpa [neg_neg] using this)
    (fun x hx => by rw [p1]; exact hψ1 (-x) (by linarith))
    (fun x hx => by rw [p2, abs_neg]; exact hψ2 (-x) (by linarith))
    (fun x hx => by rw [p3]; exact hψ3 (-x) (by linarith))
  have hrefl : ∫ x, a x * Complex.exp (Complex.I * ψ x) =
      star (∫ y, b y * Complex.exp (Complex.I * ψt y)) := by
    rw [← integral_neg_eq_self, RCLike.star_def, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hexp : Complex.exp (Complex.I * ((ψ (-y) : ℝ) : ℂ)) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * ((ψt y : ℝ) : ℂ))) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1
      simp only [hψt]; push_cast; ring
    simp only [hb, RCLike.star_def, map_mul, Complex.conj_conj, hexp]
  rw [hrefl, norm_star]
  exact hmain

/-- info: 'FormalResearch.SignUncertainty.two_ibp_phase_tail_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_ibp_phase_tail_neg

/-- Integrability of a continuous amplitude supported in `[α, ∞)` with `‖a‖ ≤ B x^{-s}` against `e^{iψ}`. -/
lemma tail_integrable {a : ℝ → ℂ} {ψ : ℝ → ℝ} {α B s : ℝ} (hα : 0 < α) (hs : 1 < s) (ha : Continuous a) (hψ : Continuous ψ)
    (hsupp : ∀ x, x < α → a x = 0) (hb0 : ∀ x, α ≤ x → ‖a x‖ ≤ B * x ^ (-s)) :
    Integrable (fun x => a x * Complex.exp (Complex.I * ψ x)) := by
  have hbI : IntegrableOn (fun y : ℝ => B * y ^ (-s)) (Set.Ici α) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact Integrable.const_mul (integrableOn_Ioi_rpow_of_lt (by linarith) hα) B
  refine Integrable.mono' (hbI.integrable_indicator measurableSet_Ici)
    (Continuous.aestronglyMeasurable (ha.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp hψ))))) (ae_of_all _ fun x => ?_)
  by_cases hx : x < α
  · have h0 : a x = 0 := hsupp x hx
    have hxn : x ∉ Set.Ici α := fun h => absurd (Set.mem_Ici.1 h) (not_le.2 hx)
    simp [h0, hxn]
  · have hx' : α ≤ x := not_lt.1 hx
    rw [Set.indicator_of_mem (Set.mem_Ici.2 hx'), norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    exact hb0 x hx'

/-- Integrability for the mirror half-line `(-∞, -α]`. -/
lemma tail_integrable_neg {a : ℝ → ℂ} {ψ : ℝ → ℝ} {α B s : ℝ} (hα : 0 < α) (hs : 1 < s) (ha : Continuous a)
    (hψ : Continuous ψ) (hsupp : ∀ x, -α < x → a x = 0) (hb0 : ∀ x, x ≤ -α → ‖a x‖ ≤ B * (-x) ^ (-s)) :
    Integrable (fun x => a x * Complex.exp (Complex.I * ψ x)) := by
  have := tail_integrable (a := fun y => a (-y)) (ψ := fun y => ψ (-y)) hα hs (ha.comp continuous_neg)
    (hψ.comp continuous_neg) (fun x hx => hsupp (-x) (by linarith)) (fun x hx => by have := hb0 (-x) (by linarith); rwa [neg_neg] at this)
  simpa using this.comp_neg

/-- **Two integrations by parts on the whole line, amplitude supported in `|x| ≥ α`.** -/
theorem two_ibp_phase_line {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) {a : ℝ → ℂ} {ψ : ℝ → ℝ}
    {α B p M2 M3 s : ℝ} (hα : 0 < α) (hs : 1 < s) (hB : 0 ≤ B) (hp : 0 < p) (hM2 : 0 ≤ M2) (hM3 : 0 ≤ M3)
    (ha : ContDiff ℝ 2 a) (hψ : ContDiff ℝ 3 ψ) (hsupp : ∀ x, |x| < α → a x = 0)
    (hb0 : ∀ x, α ≤ |x| → ‖a x‖ ≤ B * |x| ^ (-s)) (hb1 : ∀ x, α ≤ |x| → ‖deriv a x‖ ≤ B * |x| ^ (-s))
    (hb2 : ∀ x, α ≤ |x| → ‖deriv (deriv a) x‖ ≤ B * |x| ^ (-s))
    (hψ1 : ∀ x, α ≤ |x| → p ≤ |deriv ψ x|) (hψ2 : ∀ x, α ≤ |x| → |deriv (deriv ψ) x| ≤ M2)
    (hψ3 : ∀ x, α ≤ |x| → |deriv (deriv (deriv ψ)) x| ≤ M3) :
    ‖∫ x, a x * Complex.exp (Complex.I * ψ x)‖ ≤
      2 * ((1 + 4 * K1 / α + 4 * K2 / α ^ 2) * B * (α ^ (1 - s) / (s - 1)) * ibpLam p M2 M3) := by
  set ap : ℝ → ℂ := fun x => if 0 < x then a x else 0 with hap
  set an : ℝ → ℂ := fun x => a x - ap x with han
  have hapC : ContDiff ℝ 2 ap := posPart_contDiff hα hsupp ha
  have hanC : ContDiff ℝ 2 an := ha.sub hapC
  -- local identifications
  have hap_pos : ∀ x, 0 < x → ap =ᶠ[nhds x] a := fun x hx => by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using by simp only [hap]; rw [if_pos (show 0 < y from hy)]
  have han_neg : ∀ x, x < 0 → an =ᶠ[nhds x] a := fun x hx => by
    filter_upwards [isOpen_Iio.mem_nhds hx] with y hy using by simp only [han, hap]; rw [if_neg (not_lt.2 (le_of_lt (show y < 0 from hy)))]; simp
  have hdap : ∀ x, 0 < x → deriv ap x = deriv a x ∧ deriv (deriv ap) x = deriv (deriv a) x := by
    intro x hx
    have h1 : deriv ap =ᶠ[nhds x] deriv a := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using (hap_pos y hy).deriv_eq
    exact ⟨(hap_pos x hx).deriv_eq, h1.deriv_eq⟩
  have hdan : ∀ x, x < 0 → deriv an x = deriv a x ∧ deriv (deriv an) x = deriv (deriv a) x := by
    intro x hx
    have h1 : deriv an =ᶠ[nhds x] deriv a := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy using (han_neg y hy).deriv_eq
    exact ⟨(han_neg x hx).deriv_eq, h1.deriv_eq⟩
  have hsp : ∀ x, x < α → ap x = 0 := by
    intro x hx
    by_cases h : 0 < x
    · simp [hap, h, hsupp x (by rw [abs_of_pos h]; exact hx)]
    · simp [hap, h]
  have hsn : ∀ x, -α < x → an x = 0 := by
    intro x hx
    by_cases h : 0 < x
    · simp [han, hap, h]
    · simp [han, hap, h, hsupp x (by rw [abs_of_nonpos (not_lt.1 h)]; linarith)]
  have hpos : ∀ x, α ≤ x → 0 < x := fun x hx => lt_of_lt_of_le hα hx
  have hint1 := tail_integrable (a := ap) (ψ := ψ) (α := α) (B := B) (s := s) hα hs hapC.continuous hψ.continuous hsp
    (fun x hx => by
      have := hb0 x (by rw [abs_of_pos (hpos x hx)]; exact hx)
      rw [abs_of_pos (hpos x hx)] at this
      rwa [(hap_pos x (hpos x hx)).eq_of_nhds])
  have hint2 := tail_integrable_neg (a := an) (ψ := ψ) (α := α) (B := B) (s := s) hα hs hanC.continuous hψ.continuous hsn
    (fun x hx => by
      have hxn : x < 0 := by linarith
      have := hb0 x (by rw [abs_of_neg hxn]; linarith)
      rw [abs_of_neg hxn] at this
      rwa [(han_neg x hxn).eq_of_nhds])
  have hsplit : ∫ x, a x * Complex.exp (Complex.I * ψ x) =
      (∫ x, ap x * Complex.exp (Complex.I * ψ x)) + ∫ x, an x * Complex.exp (Complex.I * ψ x) := by
    rw [← integral_add hint1 hint2]
    congr 1; funext x; simp only [han]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hpl := two_ibp_phase_tail hϑ (a := ap) (ψ := ψ) (α := α) (B := B) (p := p) (M2 := M2) (M3 := M3) (s := s)
    hα hs hB hp hM2 hM3 hapC hψ hsp
    (fun x hx => by
      have := hb0 x (by rw [abs_of_pos (hpos x hx)]; exact hx)
      rw [abs_of_pos (hpos x hx)] at this
      rwa [(hap_pos x (hpos x hx)).eq_of_nhds])
    (fun x hx => by
      have := hb1 x (by rw [abs_of_pos (hpos x hx)]; exact hx)
      rw [abs_of_pos (hpos x hx)] at this
      rwa [(hdap x (hpos x hx)).1])
    (fun x hx => by
      have := hb2 x (by rw [abs_of_pos (hpos x hx)]; exact hx)
      rw [abs_of_pos (hpos x hx)] at this
      rwa [(hdap x (hpos x hx)).2])
    (fun x hx => hψ1 x (by rw [abs_of_pos (hpos x hx)]; exact hx))
    (fun x hx => hψ2 x (by rw [abs_of_pos (hpos x hx)]; exact hx))
    (fun x hx => hψ3 x (by rw [abs_of_pos (hpos x hx)]; exact hx))
  have hng := two_ibp_phase_tail_neg hϑ (a := an) (ψ := ψ) (α := α) (B := B) (p := p) (M2 := M2) (M3 := M3) (s := s)
    hα hs hB hp hM2 hM3 hanC hψ hsn
    (fun x hx => by
      have hxn : x < 0 := by linarith
      have := hb0 x (by rw [abs_of_neg hxn]; linarith)
      rw [abs_of_neg hxn] at this
      rwa [(han_neg x hxn).eq_of_nhds])
    (fun x hx => by
      have hxn : x < 0 := by linarith
      have := hb1 x (by rw [abs_of_neg hxn]; linarith)
      rw [abs_of_neg hxn] at this
      rwa [(hdan x hxn).1])
    (fun x hx => by
      have hxn : x < 0 := by linarith
      have := hb2 x (by rw [abs_of_neg hxn]; linarith)
      rw [abs_of_neg hxn] at this
      rwa [(hdan x hxn).2])
    (fun x hx => hψ1 x (by rw [abs_of_neg (by linarith : x < 0)]; linarith))
    (fun x hx => hψ2 x (by rw [abs_of_neg (by linarith : x < 0)]; linarith))
    (fun x hx => hψ3 x (by rw [abs_of_neg (by linarith : x < 0)]; linarith))
  linarith

/-- info: 'FormalResearch.SignUncertainty.two_ibp_phase_compact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_ibp_phase_compact

/-- info: 'FormalResearch.SignUncertainty.two_ibp_phase_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_ibp_phase_line

/-- info: 'FormalResearch.SignUncertainty.two_ibp_phase_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms two_ibp_phase_tail

end FormalResearch.SignUncertainty

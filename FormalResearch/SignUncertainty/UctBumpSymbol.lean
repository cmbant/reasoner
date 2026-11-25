module

public import FormalResearch.SignUncertainty.UctAiryTransPhi

/-!
# `uct:bump-symbol` (Laplace-symbol estimate): decay of the Laplace transform of a floor-trimming bump (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_upper.tex`, Lemma `uct:bump-symbol` (Section "Mellin-strip Laplace floor-bump operator"), the display
`|B̂(c(σ+iτ))| ≤ C_r M Λ_α(δ) e^{-bcσδ} (1 + cδ|τ|)^{-r}`.
Notation: `bumpLaplace B s = B̂(s) = ∫ e^{-sx} B(x) dx`, `bumpLambda α δ = Λ_α(δ)`, `BumpProfile b δ M α β K B` the hypotheses of the lemma on `B`
(smooth, supported in `[bδ, ∞)`, `|B^{(k)}| ≤ K_k M x^{-α-k}` on `[bδ, 1]`, `≤ K_k M x^{-β-k}` on `[1, ∞)`; stated verbatim, no unproved hypotheses).

Formalised here: `bump_laplace_decay` (the estimate, with `C_r` depending only on `b, α, β, r, K`; the restriction `σ ≤ 1` is not needed), proved as in the TeX
(`r₁`-fold integration by parts retaining `e^{-bcσδ}`, `laplace_ibp`, `laplace_pow`; `L¹` bounds of `B` and `B^{(r₁)}`, `l1_le`, `J0_le`, `l1_big`; minimum of the two bounds).

Not formalised (rest of `uct:bump-symbol`): (i) admissibility of `ΔW_c(ζ) = c^{-1/3} B̂(cζ)` in the sense of `uct:admiss` with Hölder exponent `1/2`
(hypotheses `StripAdmissData` of `StripAdmiss.lean`: (M1) follows from the present estimate with `r = 2` (holomorphy on the open strip and continuity on the closed strip of a
Laplace transform of an integrable profile are not yet recorded for this `B̂`), (M2) at `ζ = 1`, (M3) at `ζ = 0`: the split of `x^j B` at `x = 1/|s|` and the
`j+1` integrations by parts for `j = 1, 2`); (ii) the bound `C M (cδ)^{-1} Λ_α(δ) e^{-κ c δ^{3/2}}` of the main density for `L ≤ bδ/2` (vertical representation
`admiss_vert_rep` on `σ = k√δ` plus the phase bound `im_stripG_ge_gaussian` of `mat:T3`(3) in the form needed for this `σ`); (iii) the reflected-density bound `C M (cδ)^{-1} Λ_α(δ) e^{-bcδ/2} min(1, L_+^{-2})`
(boundary derivatives of `B̂(c(1 - iτ))`, two integrations by parts against `e^{icLτ}` with the Binet and `m`-bounds `ct:binet-decay`); (iv) the exact Fourier inversion
identity `(uct:E0-def)`.  Items (ii)-(iv) rest on the strip-kernel machinery of `StripAdmiss*`, `MellinLift*` for a general (non-seed) symbol and on `ct:binet-decay`.

Class: proved, no hypotheses.  Axiom guards are at the end.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

/-- `Λ_α(δ) = 1 + δ^{1-α}` for `α ≠ 1`, `Λ_1(δ) = 1 + log(1/δ)`. -/
noncomputable def bumpLambda (α δ : ℝ) : ℝ := if α = 1 then 1 + Real.log (1 / δ) else 1 + δ ^ (1 - α)

/-- The Laplace transform `B̂(s) = ∫ e^{-sx} B(x) dx`. -/
noncomputable def bumpLaplace (B : ℝ → ℝ) (s : ℂ) : ℂ := ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * (B x : ℂ)

/-- The hypotheses on the bump profile of `uct:bump-symbol`: smooth, supported in `[bδ, ∞)`, `|B^{(k)}(x)| ≤ K_k M x^{-α-k}` on `[bδ, 1]` and
`|B^{(k)}(x)| ≤ K_k M x^{-β-k}` on `[1, ∞)`. -/
structure BumpProfile (b δ M α β : ℝ) (K : ℕ → ℝ) (B : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) B
  support : ∀ x : ℝ, x < b * δ → B x = 0
  near : ∀ (k : ℕ) (x : ℝ), b * δ ≤ x → x ≤ 1 → |iteratedDeriv k B x| ≤ K k * M * x ^ (-α - (k : ℝ))
  far : ∀ (k : ℕ) (x : ℝ), 1 ≤ x → |iteratedDeriv k B x| ≤ K k * M * x ^ (-β - (k : ℝ))

namespace BumpProfile

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma zero_of_lt (h : BumpProfile b δ M α β K B) (j : ℕ) {x : ℝ} (hx : x < b * δ) : iteratedDeriv j B x = 0 := by
  have hev : B =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds hx] with y hy using h.support y hy
  rw [hev.iteratedDeriv_eq]
  cases j with
  | zero => simp
  | succ n => simp

lemma contDiff_iteratedDeriv (h : BumpProfile b δ M α β K B) (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv j B) :=
  by rw [iteratedDeriv_eq_iterate]; exact h.smooth.iterate_deriv j

lemma hasDerivAt_iteratedDeriv (h : BumpProfile b δ M α β K B) (j : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv j B) (iteratedDeriv (j + 1) B x) x := by
  have := ((h.contDiff_iteratedDeriv j).differentiable (by simp)) x
  rw [iteratedDeriv_succ]
  exact this.hasDerivAt



lemma integrable_iteratedDeriv (h : BumpProfile b δ M α β K B) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (j : ℕ) :
    Integrable (iteratedDeriv j B) := by
  set f := iteratedDeriv j B with hf
  have hcont : Continuous f := (h.contDiff_iteratedDeriv j).continuous
  have hind : f = (Ici (b * δ)).indicator f := by
    funext x
    by_cases hx : b * δ ≤ x
    · rw [indicator_of_mem (mem_Ici.mpr hx)]
    · rw [indicator_of_notMem (by simpa using hx)]; exact h.zero_of_lt j (not_le.mp hx)
  rw [hind, integrable_indicator_iff measurableSet_Ici, ← Icc_union_Ioi_eq_Ici hbδ]
  refine IntegrableOn.union (hcont.integrableOn_Icc) ?_
  have hint : IntegrableOn (fun x : ℝ => x ^ (-β - (j : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) one_pos
  refine (hint.const_mul (K j * M)).mono' hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [Real.norm_eq_abs]
  exact h.far j x (le_of_lt hx)

lemma integrable_laplace_mul (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (j : ℕ) {s : ℂ}
    (hs : 0 ≤ s.re) :
    Integrable (fun x : ℝ => Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv j B x : ℝ) : ℂ)) := by
  have hi := (integrable_iteratedDeriv h hbδ hβ j).norm
  refine hi.mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (h.contDiff_iteratedDeriv j).continuous).aestronglyMeasurable
  · rcases lt_or_ge x (b * δ) with hx | hx
    · rw [h.zero_of_lt j hx]; simp
    · rw [norm_mul, Complex.norm_exp, Complex.norm_real]
      have : (-s * (x : ℂ)).re ≤ 0 := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
        nlinarith [mul_nonneg hs (hb0.trans hx)]
      have := Real.exp_le_one_iff.mpr this
      calc Real.exp (-s * (x : ℂ)).re * ‖iteratedDeriv j B x‖ ≤ 1 * ‖iteratedDeriv j B x‖ := by gcongr
        _ = _ := one_mul _

/-- Integration by parts: `∫ e^{-sx} B^{(j+1)} = s ∫ e^{-sx} B^{(j)}` (no boundary terms). -/
lemma laplace_ibp (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (j : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv (j + 1) B x : ℝ) : ℂ) =
      s * ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv j B x : ℝ) : ℂ) := by
  have hu : ∀ x : ℝ, HasDerivAt (fun x : ℝ => ((iteratedDeriv j B x : ℝ) : ℂ)) ((iteratedDeriv (j + 1) B x : ℝ) : ℂ) x :=
    fun x => (h.hasDerivAt_iteratedDeriv j x).ofReal_comp
  have hv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.exp (-s * (x : ℂ))) (-s * Complex.exp (-s * (x : ℂ))) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => -s * (x : ℂ)) (-s) x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_mul (-s)
    exact (h1.cexp).congr_deriv (by ring)
  have i1 := integrable_laplace_mul h hb0 hbδ hβ j hs
  have i2 := integrable_laplace_mul h hb0 hbδ hβ (j + 1) hs
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun x : ℝ => ((iteratedDeriv j B x : ℝ) : ℂ))
    (v := fun x : ℝ => Complex.exp (-s * (x : ℂ))) (u' := fun x : ℝ => ((iteratedDeriv (j + 1) B x : ℝ) : ℂ))
    (v' := fun x : ℝ => -s * Complex.exp (-s * (x : ℂ))) (fun x _ => hu x) (fun x _ => hv x)
    (by
      refine (i1.const_mul (-s)).congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      refine i2.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      refine i1.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
  have e1 : ∫ x : ℝ, ((iteratedDeriv j B x : ℝ) : ℂ) * (-s * Complex.exp (-s * (x : ℂ))) =
      -s * ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv j B x : ℝ) : ℂ) := by
    rw [← integral_const_mul]; congr 1; funext x; ring
  have e2 : ∫ x : ℝ, ((iteratedDeriv (j + 1) B x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ)) =
      ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv (j + 1) B x : ℝ) : ℂ) := by
    congr 1; funext x; ring
  rw [e1, e2] at key
  linear_combination key


lemma laplace_pow (h : BumpProfile b δ M α β K B) (hb0 : 0 ≤ b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) :
    ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv j B x : ℝ) : ℂ) = s ^ j * bumpLaplace B s := by
  induction j with
  | zero => simp [bumpLaplace]
  | succ n ih => rw [laplace_ibp h hb0 hbδ hβ n hs, ih]; ring

lemma norm_laplace_le (h : BumpProfile b δ M α β K B) (hbδ : b * δ ≤ 1) (hβ : 1 < β) {s : ℂ} (hs : 0 ≤ s.re) (j : ℕ) :
    ‖∫ x : ℝ, Complex.exp (-s * (x : ℂ)) * ((iteratedDeriv j B x : ℝ) : ℂ)‖ ≤
      Real.exp (-(s.re * (b * δ))) * ∫ x : ℝ, ‖iteratedDeriv j B x‖ := by
  have hi := (integrable_iteratedDeriv h hbδ hβ j).norm.const_mul (Real.exp (-(s.re * (b * δ))))
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le hi (ae_of_all _ fun x => ?_)
  rcases lt_or_ge x (b * δ) with hx | hx
  · rw [h.zero_of_lt j hx]; simp
  · rw [norm_mul, Complex.norm_exp, Complex.norm_real]
    have : (-s * (x : ℂ)).re = -(s.re * x) := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, neg_mul]
    rw [this]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hx hs]


lemma l1_le (h : BumpProfile b δ M α β K B) (hbδ0 : 0 < b * δ) (hbδ : b * δ ≤ 1) (hβ : 1 < β) (j : ℕ) :
    ∫ x : ℝ, ‖iteratedDeriv j B x‖ ≤ K j * M * ((∫ x in (b * δ)..1, x ^ (-(α + j))) + 1 / (β + j - 1)) := by
  have hint := (integrable_iteratedDeriv h hbδ hβ j).norm
  have hKM : 0 ≤ K j * M := by
    have h1 := h.far j 1 le_rfl
    have : 0 ≤ |iteratedDeriv j B 1| := abs_nonneg _
    have h2 : (1 : ℝ) ^ (-β - (j : ℝ)) = 1 := Real.one_rpow _
    rw [h2, mul_one] at h1
    by_contra hneg
    linarith [not_le.mp hneg]
  have hzero : ∀ x ∉ Ici (b * δ), ‖iteratedDeriv j B x‖ = 0 := fun x hx => by
    rw [h.zero_of_lt j (not_le.mp hx)]; simp
  have hdisj : Disjoint (Icc (b * δ) 1) (Ioi (1 : ℝ)) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr (mem_Ioi.mp hx'))
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← Icc_union_Ioi_eq_Ici hbδ,
    setIntegral_union hdisj measurableSet_Ioi (hint.integrableOn) (hint.integrableOn)]
  have hI1 : IntegrableOn (fun x : ℝ => x ^ (-(α + j))) (Icc (b * δ) 1) := by
    refine ContinuousOn.integrableOn_Icc ?_
    exact fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (by linarith [hx.1]))).continuousWithinAt
  have hI2 : IntegrableOn (fun x : ℝ => x ^ (-β - (j : ℝ))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) one_pos
  have h1 : ∫ x in Icc (b * δ) 1, ‖iteratedDeriv j B x‖ ≤ ∫ x in Icc (b * δ) 1, K j * M * x ^ (-(α + j)) := by
    refine setIntegral_mono_on hint.integrableOn (hI1.const_mul _) measurableSet_Icc fun x hx => ?_
    rw [Real.norm_eq_abs]
    have := h.near j x hx.1 hx.2
    rwa [show -α - (j : ℝ) = -(α + j) by ring] at this
  have h2 : ∫ x in Ioi 1, ‖iteratedDeriv j B x‖ ≤ ∫ x in Ioi 1, K j * M * x ^ (-β - (j : ℝ)) := by
    refine setIntegral_mono_on hint.integrableOn (hI2.const_mul _) measurableSet_Ioi fun x hx => ?_
    rw [Real.norm_eq_abs]
    exact h.far j x (le_of_lt hx)
  have e1 : ∫ x in Icc (b * δ) 1, K j * M * x ^ (-(α + j)) = K j * M * ∫ x in (b * δ)..1, x ^ (-(α + j)) := by
    rw [integral_const_mul, intervalIntegral.integral_of_le hbδ, integral_Icc_eq_integral_Ioc]
  have e2 : ∫ x in Ioi 1, K j * M * x ^ (-β - (j : ℝ)) = K j * M * (1 / (β + j - 1)) := by
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by have : (0 : ℝ) ≤ j := j.cast_nonneg; linarith) one_pos]
    congr 1
    rw [Real.one_rpow, show -β - (j : ℝ) + 1 = -(β + j - 1) by ring, neg_div_neg_eq]
  rw [mul_add]
  linarith [e1, e2]

end BumpProfile

lemma one_le_bumpLambda {α δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : 1 ≤ bumpLambda α δ := by
  unfold bumpLambda
  split_ifs
  · have : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    linarith
  · have : 0 ≤ δ ^ (1 - α) := Real.rpow_nonneg hδ0.le _
    linarith

lemma rpow_le_bumpLambda {α δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) : δ ^ (1 - α) ≤ bumpLambda α δ := by
  unfold bumpLambda
  split_ifs with h
  · rw [h]; simp only [sub_self, Real.rpow_zero]
    have : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    linarith
  · linarith

/-- Bounds for `∫_{c₀}^1 x^{-a} dx`. -/
lemma integral_rpow_neg_bounds {a c₀ : ℝ} (hc : 0 < c₀) (hc1 : c₀ ≤ 1) :
    (1 < a → ∫ x in c₀..1, x ^ (-a) ≤ c₀ ^ (1 - a) / (a - 1)) ∧ (a < 1 → ∫ x in c₀..1, x ^ (-a) ≤ 1 / (1 - a)) ∧
      (a = 1 → ∫ x in c₀..1, x ^ (-a) = Real.log (1 / c₀)) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc c₀ 1 := by
    rw [Set.uIcc_of_le hc1]; intro h; linarith [h.1]
  refine ⟨fun ha => ?_, fun ha => ?_, fun ha => ?_⟩
  · rw [integral_rpow (Or.inr ⟨by linarith, h0⟩), Real.one_rpow, show -a + 1 = 1 - a by ring]
    rw [show (1 - c₀ ^ (1 - a)) / (1 - a) = (c₀ ^ (1 - a) - 1) / (a - 1) by
      rw [← neg_div_neg_eq]; congr 1 <;> ring]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · rw [integral_rpow (Or.inl (by linarith)), Real.one_rpow, show -a + 1 = 1 - a by ring]
    have : 0 ≤ c₀ ^ (1 - a) := Real.rpow_nonneg hc.le _
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  · subst ha
    rw [show (-(1 : ℝ)) = -1 from rfl]
    simp only [Real.rpow_neg_one]
    exact integral_inv_of_pos hc one_pos

/-- The constant `C₀ = b^{1-α}/|α-1| + 1/|1-α| + |log b| + 1`. -/
noncomputable def bumpC0 (b α : ℝ) : ℝ := b ^ (1 - α) / |α - 1| + 1 / |1 - α| + |Real.log b| + 1

lemma bumpC0_nonneg {b : ℝ} (hb : 0 < b) (α : ℝ) : 0 ≤ bumpC0 b α := by
  unfold bumpC0; have := Real.rpow_nonneg hb.le (1 - α); positivity

lemma J0_le {b α δ : ℝ} (hb : 0 < b) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hbδ : b * δ ≤ 1) :
    ∫ x in (b * δ)..1, x ^ (-α) ≤ bumpC0 b α * bumpLambda α δ := by
  have hbδ0 : 0 < b * δ := by positivity
  have hΛ1 := one_le_bumpLambda (α := α) hδ0 hδ1
  have hΛ2 := rpow_le_bumpLambda (α := α) hδ0 hδ1
  obtain ⟨h1, h2, h3⟩ := integral_rpow_neg_bounds (a := α) hbδ0 hbδ
  have hb1 : 0 ≤ b ^ (1 - α) := Real.rpow_nonneg hb.le _
  have hlog : 0 ≤ |Real.log b| := abs_nonneg _
  have hΛ0 : 0 ≤ bumpLambda α δ := by linarith
  rcases lt_trichotomy α 1 with ha | ha | ha
  · refine (h2 ha).trans ?_
    have : 1 / (1 - α) = 1 / |1 - α| := by rw [abs_of_pos (by linarith)]
    rw [this]
    unfold bumpC0
    have e1 : 0 ≤ b ^ (1 - α) / |α - 1| := by positivity
    have e2 : 0 ≤ 1 / |1 - α| := by positivity
    nlinarith [mul_nonneg e1 hΛ0, mul_nonneg hlog hΛ0, mul_le_mul_of_nonneg_left hΛ1 e2]
  · have hΛ : bumpLambda α δ = 1 + Real.log (1 / δ) := by unfold bumpLambda; simp [ha]
    rw [h3 ha, hΛ]
    have ht : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ0]; linarith)
    have e : Real.log (1 / (b * δ)) = -Real.log b + Real.log (1 / δ) := by
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hb.ne' hδ0.ne']; ring
    rw [e]
    unfold bumpC0
    have e2 : 0 ≤ b ^ (1 - α) / |α - 1| := by positivity
    have e3 : 0 ≤ 1 / |1 - α| := by positivity
    have := neg_abs_le (Real.log b)
    nlinarith [mul_nonneg hlog ht, mul_nonneg e2 (by linarith : 0 ≤ 1 + Real.log (1 / δ)), mul_nonneg e3 (by linarith : 0 ≤ 1 + Real.log (1 / δ))]
  · refine (h1 ha).trans ?_
    rw [Real.mul_rpow hb.le hδ0.le]
    have h4 : b ^ (1 - α) * δ ^ (1 - α) / (α - 1) ≤ b ^ (1 - α) / (α - 1) * bumpLambda α δ := by
      have : b ^ (1 - α) / (α - 1) * bumpLambda α δ = b ^ (1 - α) * bumpLambda α δ / (α - 1) := by ring
      rw [this]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hΛ2 hb1) (by linarith)
    refine h4.trans ?_
    unfold bumpC0
    rw [abs_of_pos (by linarith : 0 < α - 1)]
    have e2 : 0 ≤ b ^ (1 - α) / (α - 1) := by have : 0 < α - 1 := by linarith
                                              positivity
    have e3 : 0 ≤ 1 / |1 - α| := by positivity
    nlinarith [mul_nonneg hlog hΛ0, mul_nonneg e3 hΛ0, mul_nonneg e2 hΛ0]

namespace BumpProfile

variable {b δ M α β : ℝ} {K : ℕ → ℝ} {B : ℝ → ℝ}

lemma norm_laplace_le_one (h : BumpProfile b δ M α β K B) (hb : 0 < b) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hbδ : b * δ ≤ 1) (hβ : 3 / 2 ≤ β)
    (hM : 0 ≤ M) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖bumpLaplace B s‖ ≤ Real.exp (-(s.re * (b * δ))) * (|K 0| * (bumpC0 b α + 2) * M * bumpLambda α δ) := by
  have hbδ0 : 0 < b * δ := by positivity
  have hβ1 : 1 < β := by linarith
  have h0 := norm_laplace_le h hbδ hβ1 hs 0
  rw [laplace_pow h hbδ0.le hbδ hβ1 hs 0] at h0
  simp only [pow_zero, one_mul, iteratedDeriv_zero] at h0
  have hl := l1_le h hbδ0 hbδ hβ1 0
  simp only [iteratedDeriv_zero, Nat.cast_zero, add_zero] at hl
  have hJ := J0_le (α := α) hb hδ0 hδ1 hbδ
  have hΛ1 := one_le_bumpLambda (α := α) hδ0 hδ1
  have hC0 := bumpC0_nonneg hb α
  have h2 : 1 / (β - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hK : K 0 * M ≤ |K 0| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
  have hint : ∫ x : ℝ, ‖B x‖ ≤ |K 0| * (bumpC0 b α + 2) * M * bumpLambda α δ := by
    refine hl.trans ?_
    have e1 : K 0 * M * ((∫ x in (b * δ)..1, x ^ (-α)) + 1 / (β - 1)) ≤ |K 0| * M * (bumpC0 b α * bumpLambda α δ + 2) := by
      have hq : (∫ x in (b * δ)..1, x ^ (-α)) + 1 / (β - 1) ≤ bumpC0 b α * bumpLambda α δ + 2 := by linarith
      have hq0 : 0 ≤ (∫ x in (b * δ)..1, x ^ (-α)) + 1 / (β - 1) := by
        have : 0 ≤ ∫ x in (b * δ)..1, x ^ (-α) :=
          intervalIntegral.integral_nonneg hbδ (fun x hx => Real.rpow_nonneg (by linarith [hx.1]) _)
        have : 0 < 1 / (β - 1) := by apply div_pos one_pos; linarith
        linarith
      calc K 0 * M * ((∫ x in (b * δ)..1, x ^ (-α)) + 1 / (β - 1)) ≤ |K 0| * M * ((∫ x in (b * δ)..1, x ^ (-α)) + 1 / (β - 1)) :=
            mul_le_mul_of_nonneg_right hK hq0
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (mul_nonneg (abs_nonneg _) hM)
    refine e1.trans ?_
    have : |K 0| * M * (bumpC0 b α * bumpLambda α δ + 2) ≤ |K 0| * M * ((bumpC0 b α + 2) * bumpLambda α δ) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (mul_nonneg (abs_nonneg _) hM)
    linarith
  calc ‖bumpLaplace B s‖ ≤ Real.exp (-(s.re * (b * δ))) * ∫ x : ℝ, ‖B x‖ := h0
    _ ≤ _ := mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le

lemma l1_big (h : BumpProfile b δ M α β K B) (hb : 0 < b) (hδ0 : 0 < δ) (hbδ : b * δ ≤ 1) (hβ : 3 / 2 ≤ β) (hM : 0 ≤ M) (r₁ : ℕ)
    (ha : 2 ≤ α + r₁) :
    ∫ x : ℝ, ‖iteratedDeriv r₁ B x‖ ≤ 3 * |K r₁| * M * (b * δ) ^ (1 - (α + r₁)) := by
  have hbδ0 : 0 < b * δ := by positivity
  have hl := l1_le h hbδ0 hbδ (by linarith) r₁
  have hJ := (integral_rpow_neg_bounds (a := α + r₁) hbδ0 hbδ).1 (by linarith)
  have hX : 1 ≤ (b * δ) ^ (1 - (α + r₁)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hbδ0 hbδ (by linarith)
  have h1 : 1 / (α + r₁ - 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have h2 : 1 / (β + r₁ - 1) ≤ 2 := by
    rw [div_le_iff₀ (by have : (0 : ℝ) ≤ r₁ := r₁.cast_nonneg; linarith)]
    have : (0 : ℝ) ≤ r₁ := r₁.cast_nonneg
    linarith
  have h3 : (b * δ) ^ (1 - (α + r₁)) / (α + r₁ - 1) ≤ (b * δ) ^ (1 - (α + r₁)) := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hq : (∫ x in (b * δ)..1, x ^ (-(α + r₁))) + 1 / (β + r₁ - 1) ≤ 3 * (b * δ) ^ (1 - (α + r₁)) := by linarith
  have hq0 : 0 ≤ (∫ x in (b * δ)..1, x ^ (-(α + r₁))) + 1 / (β + r₁ - 1) := by
    have : 0 ≤ ∫ x in (b * δ)..1, x ^ (-(α + r₁)) :=
      intervalIntegral.integral_nonneg hbδ (fun x hx => Real.rpow_nonneg (by linarith [hx.1]) _)
    have : 0 < 1 / (β + r₁ - 1) := by
      apply div_pos one_pos
      have : (0 : ℝ) ≤ r₁ := r₁.cast_nonneg
      linarith
    linarith
  have hK : K r₁ * M ≤ |K r₁| * M := mul_le_mul_of_nonneg_right (le_abs_self _) hM
  calc ∫ x : ℝ, ‖iteratedDeriv r₁ B x‖ ≤ K r₁ * M * ((∫ x in (b * δ)..1, x ^ (-(α + r₁))) + 1 / (β + r₁ - 1)) := hl
    _ ≤ |K r₁| * M * ((∫ x in (b * δ)..1, x ^ (-(α + r₁))) + 1 / (β + r₁ - 1)) := mul_le_mul_of_nonneg_right hK hq0
    _ ≤ |K r₁| * M * (3 * (b * δ) ^ (1 - (α + r₁))) := mul_le_mul_of_nonneg_left hq (mul_nonneg (abs_nonneg _) hM)
    _ = _ := by ring

end BumpProfile

/-- **`uct:bump-symbol`, first display** (the Laplace-symbol estimate): for a bump profile `B` (smooth, supported in `[bδ, ∞)`, with
`|B^{(k)}(x)| ≤ K_k M x^{-α-k}` on `[bδ,1]` and `|B^{(k)}(x)| ≤ K_k M x^{-β-k}` on `[1,∞)`, `β ≥ 3/2`), and `0 < δ ≤ 1`, `bδ ≤ 1`, `c > 0`, `σ ≥ 0`,
`|B̂(c(σ+iτ))| ≤ C_r M Λ_α(δ) e^{-bcσδ} (1 + cδ|τ|)^{-r}`, with `C_r` depending only on `b, α, β, r` and the constants `K_k`, not on `c, δ, M, σ, τ, B`.
The restriction `σ ≤ 1` of the paper is not needed. -/
theorem bump_laplace_decay {b α β : ℝ} (hb : 0 < b) (hβ : 3 / 2 ≤ β) (K : ℕ → ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ → ℝ) (δ M c σ τ : ℝ), 0 < δ → δ ≤ 1 → b * δ ≤ 1 → 0 ≤ M → 0 < c → 0 ≤ σ →
      BumpProfile b δ M α β K B →
        ‖bumpLaplace B ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I))‖ ≤
          C * M * bumpLambda α δ * Real.exp (-(b * c * σ * δ)) / (1 + c * δ * |τ|) ^ r := by
  set r₁ : ℕ := r + ⌈|α|⌉₊ + 2 with hr₁
  have hr₁r : r ≤ r₁ := by omega
  have hα2 : 2 ≤ α + r₁ := by
    have h1 : |α| ≤ (⌈|α|⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : -|α| ≤ α := neg_abs_le α
    have : (r₁ : ℝ) = r + ⌈|α|⌉₊ + 2 := by rw [hr₁]; push_cast; ring
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    linarith
  set A₀ : ℝ := |K 0| * (bumpC0 b α + 2) with hA₀
  set A₁ : ℝ := 3 * |K r₁| * b ^ (1 - (α + r₁)) with hA₁
  have hA₀0 : 0 ≤ A₀ := by rw [hA₀]; have := bumpC0_nonneg hb α; positivity
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; have := Real.rpow_nonneg hb.le (1 - (α + r₁)); positivity
  refine ⟨2 ^ r * max A₀ A₁, by positivity, fun B δ M c σ τ hδ0 hδ1 hbδ hM hc hσ hB => ?_⟩
  have hbδ0 : 0 < b * δ := by positivity
  have hΛ1 := one_le_bumpLambda (α := α) hδ0 hδ1
  have hΛ2 := rpow_le_bumpLambda (α := α) hδ0 hδ1
  set s : ℂ := (c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) with hs
  have hsre : s.re = c * σ := by simp [hs]
  have hsim : s.im = c * τ := by simp [hs]
  have hs0 : 0 ≤ s.re := by rw [hsre]; positivity
  set E : ℝ := Real.exp (-(b * c * σ * δ)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEe : Real.exp (-(s.re * (b * δ))) = E := by rw [hE, hsre]; congr 1; ring
  set X : ℝ := c * δ * |τ| with hX
  have hX0 : 0 ≤ X := by positivity
  have hmax0 := le_max_left A₀ A₁
  have hmax1 := le_max_right A₀ A₁
  have hMΛ : 0 ≤ M * bumpLambda α δ := mul_nonneg hM (by linarith)
  have hb1 := hB.norm_laplace_le_one hb hδ0 hδ1 hbδ hβ hM hs0
  rw [hEe] at hb1
  have hpos : 0 < (1 + X) ^ r := by positivity
  rw [le_div_iff₀ hpos]
  by_cases hX1 : X ≤ 1
  · have h1 : (1 + X) ^ r ≤ 2 ^ r := pow_le_pow_left₀ (by linarith) (by linarith) r
    have h2 : ‖bumpLaplace B s‖ ≤ E * (max A₀ A₁ * M * bumpLambda α δ) := by
      refine hb1.trans (mul_le_mul_of_nonneg_left ?_ hE0.le)
      have : |K 0| * (bumpC0 b α + 2) = A₀ := rfl
      rw [this]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax0 hM) (by linarith)
    have hn0 : 0 ≤ ‖bumpLaplace B s‖ := norm_nonneg _
    calc ‖bumpLaplace B s‖ * (1 + X) ^ r ≤ (E * (max A₀ A₁ * M * bumpLambda α δ)) * 2 ^ r :=
          mul_le_mul h2 h1 hpos.le (by positivity)
      _ = _ := by ring
  · have hX1' : 1 < X := not_le.mp hX1
    have hτ0 : τ ≠ 0 := by
      intro h0; rw [hX, h0] at hX1'; simp at hX1'; linarith
    have hs1 : (1 : ℝ) < (X) := hX1'
    -- the integrated-by-parts bound
    have hb2 := hB.norm_laplace_le hbδ (by linarith) hs0 r₁
    rw [hB.laplace_pow hbδ0.le hbδ (by linarith) hs0 r₁, hEe] at hb2
    rw [norm_mul, norm_pow] at hb2
    have hbig := hB.l1_big hb hδ0 hbδ hβ hM r₁ hα2
    have hnorm_s : c * |τ| ≤ ‖s‖ := by
      have := Complex.abs_im_le_norm s
      rw [hsim, abs_mul, abs_of_pos hc] at this
      exact this
    have hdp : 0 < δ ^ r₁ := by positivity
    have hsp : (c * |τ| * δ) ^ r₁ ≤ ‖s‖ ^ r₁ * δ ^ r₁ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hnorm_s r₁) hdp.le
    have hXe : X ^ r₁ = (c * |τ| * δ) ^ r₁ := by rw [hX]; congr 1; ring
    have hbd : (b * δ) ^ (1 - (α + r₁)) * δ ^ r₁ = b ^ (1 - (α + r₁)) * δ ^ (1 - α) := by
      rw [Real.mul_rpow hb.le hδ0.le, mul_assoc]
      congr 1
      rw [← Real.rpow_natCast δ r₁, ← Real.rpow_add hδ0]
      congr 1; ring
    have hE1 : 0 ≤ E * (3 * |K r₁| * M) := by positivity
    have h3 : ‖s‖ ^ r₁ * ‖bumpLaplace B s‖ ≤ E * (3 * |K r₁| * M * (b * δ) ^ (1 - (α + r₁))) :=
      hb2.trans (mul_le_mul_of_nonneg_left hbig hE0.le)
    have h4 : ‖s‖ ^ r₁ * ‖bumpLaplace B s‖ * δ ^ r₁ ≤ E * (3 * |K r₁| * M * (b * δ) ^ (1 - (α + r₁))) * δ ^ r₁ :=
      mul_le_mul_of_nonneg_right h3 hdp.le
    have h5 : E * (3 * |K r₁| * M * (b * δ) ^ (1 - (α + r₁))) * δ ^ r₁ = E * (A₁ * M * δ ^ (1 - α)) := by
      have : E * (3 * |K r₁| * M * (b * δ) ^ (1 - (α + r₁))) * δ ^ r₁ =
          E * (3 * |K r₁| * M) * ((b * δ) ^ (1 - (α + r₁)) * δ ^ r₁) := by ring
      rw [this, hbd, hA₁]; ring
    have hn0 : 0 ≤ ‖bumpLaplace B s‖ := norm_nonneg _
    have key : ‖bumpLaplace B s‖ * X ^ r₁ ≤ E * (A₁ * M * bumpLambda α δ) := by
      calc ‖bumpLaplace B s‖ * X ^ r₁ ≤ ‖bumpLaplace B s‖ * (‖s‖ ^ r₁ * δ ^ r₁) := by
            rw [hXe]; exact mul_le_mul_of_nonneg_left hsp hn0
        _ = ‖s‖ ^ r₁ * ‖bumpLaplace B s‖ * δ ^ r₁ := by ring
        _ ≤ E * (A₁ * M * δ ^ (1 - α)) := h4.trans_eq h5
        _ ≤ E * (A₁ * M * bumpLambda α δ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΛ2 (mul_nonneg hA₁0 hM)) hE0.le
    have hXr : X ^ r ≤ X ^ r₁ := pow_le_pow_right₀ hX1'.le hr₁r
    have h6 : (1 + X) ^ r ≤ 2 ^ r * X ^ r := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) r
    calc ‖bumpLaplace B s‖ * (1 + X) ^ r ≤ ‖bumpLaplace B s‖ * (2 ^ r * X ^ r) := mul_le_mul_of_nonneg_left h6 hn0
      _ ≤ ‖bumpLaplace B s‖ * (2 ^ r * X ^ r₁) := by
          refine mul_le_mul_of_nonneg_left ?_ hn0
          exact mul_le_mul_of_nonneg_left hXr (by positivity)
      _ = 2 ^ r * (‖bumpLaplace B s‖ * X ^ r₁) := by ring
      _ ≤ 2 ^ r * (E * (A₁ * M * bumpLambda α δ)) := mul_le_mul_of_nonneg_left key (by positivity)
      _ ≤ 2 ^ r * (E * (max A₀ A₁ * M * bumpLambda α δ)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hE0.le) (by positivity)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hmax1 hM) (by linarith)
      _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.bump_laplace_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bump_laplace_decay

end FormalResearch.SignUncertainty

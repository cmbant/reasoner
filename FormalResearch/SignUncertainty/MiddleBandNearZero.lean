module

public import FormalResearch.SignUncertainty.MiddleBandRegions

/-!
# GT.2a: the near-zero region

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Near zero".

* `near_zero_bound`: for `g` continuous at `0` with `|g(u) - g(0)| ≤ G|u|^{1/2}`, `|g'| ≤ G|u|^{-1/2}`, `|g''| ≤ G|u|^{-3/2}`
  on `0 < |u| < 3` and the phase gradient `ψ' ≥ p₀ ≥ 2` on `|u| ≤ 2`, the cutoff integral `∫ ϑ(u) g(u) e^{iψ(u)} du` is `≤ C G p₀^{-3/2}`:
  the constant `g(0)` by two integrations by parts, the remainder by the absolute bound on `|u| ≤ 2/p₀` and two integrations by
  parts beyond.

Status: proved, unconditional (hypotheses are pointwise bounds on `g`).
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.SignUncertainty


lemma cut_mul_continuous {η : ℝ → ℝ} (hη : Continuous η) (hη0 : ∀ u, 2 ≤ |u| → η u = 0) {g : ℝ → ℂ} {g0 : ℂ} {G : ℝ}
    (hg0 : g 0 = g0) (hc : ∀ u, 0 < |u| → |u| < 3 → ContDiffAt ℝ 2 g u)
    (hH : ∀ u, 0 < |u| → |u| < 3 → ‖g u - g0‖ ≤ G * |u| ^ (1 / 2 : ℝ)) :
    Continuous (fun u => (η u : ℂ) * (g u - g0)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have hηc : ContinuousAt (fun u => (η u : ℂ)) u := (Complex.continuous_ofReal.comp hη).continuousAt
  by_cases hu0 : u = 0
  · subst hu0
    have h1 : Filter.Tendsto (fun u : ℝ => G * |u| ^ (1 / 2 : ℝ)) (nhds 0) (nhds 0) := by
      have : ContinuousAt (fun u : ℝ => G * |u| ^ (1 / 2 : ℝ)) 0 := by
        refine continuousAt_const.mul ?_
        exact (Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp (continuous_abs.continuousAt)
      simpa using this.tendsto
    have h2 : Filter.Tendsto (fun u : ℝ => g u - g0) (nhds 0) (nhds 0) := by
      refine squeeze_zero_norm' ?_ h1
      have hm : Metric.ball (0 : ℝ) 3 ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [hm] with v hv
      have hv' : |v| < 3 := by simpa [Real.dist_eq] using hv
      by_cases hv0 : v = 0
      · subst hv0; simp [hg0]
      · exact hH v (abs_pos.mpr hv0) hv'
    have h3 : ContinuousAt (fun u => g u - g0) 0 := by
      rw [ContinuousAt]; simpa [hg0] using h2
    exact hηc.mul h3
  · by_cases hu3 : |u| < 3
    · have := (hc u (abs_pos.mpr hu0) hu3).continuousAt
      exact hηc.mul (this.sub continuousAt_const)
    · have hz : (fun u => (η u : ℂ) * (g u - g0)) =ᶠ[nhds u] fun _ => (0 : ℂ) := by
        have : ∀ᶠ v in nhds u, 2 ≤ |v| := by
          have : (2 : ℝ) < |u| := by linarith [not_lt.1 hu3]
          exact (continuous_abs.continuousAt.eventually (lt_mem_nhds this)).mono fun v hv => hv.le
        filter_upwards [this] with v hv
        simp [hη0 v hv]
      exact (continuousAt_const).congr hz.symm


lemma integrable_osc_of_cont {f : ℝ → ℂ} (hf : Continuous f) (hz : ∀ u, 2 ≤ |u| → f u = 0) (a0 : ℝ) :
    Integrable (fun u => f u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) := by
  refine Continuous.integrable_of_hasCompactSupport (hf.mul (by fun_prop)) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -2) (b := 2)) (fun x hx => ?_)
  have : 2 ≤ |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [hz x this]

lemma oscInt_add3 {f1 f2 f3 : ℝ → ℂ} (a0 : ℝ) (h1 : Integrable (fun u => f1 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))))
    (h2 : Integrable (fun u => f2 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))))
    (h3 : Integrable (fun u => f3 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)))) :
    oscInt a0 (fun u => f1 u + f2 u + f3 u) = oscInt a0 f1 + oscInt a0 f2 + oscInt a0 f3 := by
  unfold oscInt
  rw [← integral_add h1 h2, ← integral_add (by exact h1.add h2) h3]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show (f1 u + f2 u + f3 u) * _ = f1 u * _ + f2 u * _ + f3 u * _
  ring

lemma int_rpow_m32 {α β : ℝ} (hα : 0 < α) : ∫ x in Set.Icc α β, x ^ (-(3 / 2 : ℝ)) ≤ 2 * α ^ (-(1 / 2 : ℝ)) := by
  have hfi : IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Set.Ici α) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) hα
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici α)] (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) :=
    (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x hx =>
      Real.rpow_nonneg (by have := Set.mem_Ici.1 hx; linarith) _)
  calc ∫ x in Set.Icc α β, x ^ (-(3 / 2 : ℝ)) ≤ ∫ x in Set.Ici α, x ^ (-(3 / 2 : ℝ)) :=
        setIntegral_mono_set hfi hnn (ae_of_all _ fun x (hx : x ∈ Set.Icc α β) => Set.Icc_subset_Ici_self hx)
    _ = ∫ x in Set.Ioi α, x ^ (-(3 / 2 : ℝ)) := by rw [integral_Ici_eq_integral_Ioi]
    _ = α ^ (1 - 3 / 2 : ℝ) / (3 / 2 - 1) := mb_tail_pow hα (by norm_num)
    _ = 2 * α ^ (-(1 / 2 : ℝ)) := by
        rw [show (1 - 3 / 2 : ℝ) = -(1 / 2) by norm_num]; ring


lemma p0_pow_le {p0 : ℝ} (hp : 1 ≤ p0) (k : ℕ) (hk : 2 ≤ k) : 1 / p0 ^ k ≤ p0 ^ (-(3 / 2 : ℝ)) := by
  have hp0 : 0 < p0 := by linarith
  have h1 : p0 ^ (3 / 2 : ℝ) ≤ p0 ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hp (by have : (2 : ℝ) ≤ k := by exact_mod_cast hk
                                                  linarith)
  rw [Real.rpow_neg hp0.le, one_div]
  exact inv_anti₀ (Real.rpow_pos_of_pos hp0 _) h1

lemma nz_const_part {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a0 p0 : ℝ} {g0 : ℂ}, 2 ≤ p0 → (∀ x, |x| ≤ 2 → p0 ≤ a0 - Real.pi ^ 2 * x ^ 2 / 12) →
      ‖oscInt a0 (fun u => (ϑ u : ℂ) * g0)‖ ≤ C * ‖g0‖ * p0 ^ (-(3 / 2 : ℝ)) := by
  refine ⟨4 * (1 + K1 + K2) * (1 + Real.pi ^ 2 + Real.pi ^ 2 / 6 + Real.pi ^ 4 / 3), by
    have := hϑ.hK1; have := hϑ.hK2; positivity, ?_⟩
  intro a0 p0 g0 hp2 hgrad
  have hp1 : 1 ≤ p0 := by linarith
  have hp0 : 0 < p0 := by linarith
  have hϑ2 : ContDiff ℝ 2 ϑ := hϑ.contDiff.of_le (by norm_num)
  have hϑd : Differentiable ℝ ϑ := hϑ.contDiff.differentiable (by norm_num)
  have hϑ1 : ContDiff ℝ 2 (deriv ϑ) := hϑ.contDiff.deriv'
  have hϑ1d : Differentiable ℝ (deriv ϑ) := hϑ1.differentiable (by norm_num)
  have hb : ContDiff ℝ 2 (fun u => (ϑ u : ℂ) * g0) :=
    (Complex.ofRealCLM.contDiff.comp hϑ2).mul contDiff_const
  have hd1 : deriv (fun u => (ϑ u : ℂ) * g0) = fun u => ((deriv ϑ u : ℝ) : ℂ) * g0 := by
    funext u
    exact ((hϑd u).hasDerivAt.ofReal_comp.mul_const g0).deriv
  have hd2 : deriv (deriv (fun u => (ϑ u : ℂ) * g0)) = fun u => ((deriv (deriv ϑ) u : ℝ) : ℂ) * g0 := by
    rw [hd1]
    funext u
    exact ((hϑ1d u).hasDerivAt.ofReal_comp.mul_const g0).deriv
  have hg0 := norm_nonneg g0
  set B : ℝ := (1 + K1 + K2) * ‖g0‖ with hB
  have hB0 : 0 ≤ B := by have := hϑ.hK1; have := hϑ.hK2; positivity
  have hmain := cubic_two_ibp_const (b := fun u => (ϑ u : ℂ) * g0) (a0 := a0) (α := -2) (β := 2) (B := B)
    (p0 := p0) (R := 2) (by norm_num) hB0 hp0 (fun x hx => by rw [abs_le]; exact ⟨hx.1, hx.2⟩) hb
    (fun x hx => by
      have : 2 ≤ |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp [hϑ.zero x this])
    (fun x hx => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hB]
      have h1 : |ϑ x| ≤ 1 + K1 + K2 := by
        rw [abs_of_nonneg (hϑ.range x).1]; linarith [(hϑ.range x).2, hϑ.hK1, hϑ.hK2]
      exact mul_le_mul_of_nonneg_right h1 hg0)
    (fun x hx => by
      rw [hd1]; dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hB]
      have h1 : |deriv ϑ x| ≤ 1 + K1 + K2 := by linarith [hϑ.d1 x, hϑ.hK2]
      exact mul_le_mul_of_nonneg_right h1 hg0)
    (fun x hx => by
      rw [hd2]; dsimp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hB]
      have h1 : |deriv (deriv ϑ) x| ≤ 1 + K1 + K2 := by linarith [hϑ.d2 x, hϑ.hK1]
      exact mul_le_mul_of_nonneg_right h1 hg0)
    (fun x hx => by
      have h := hgrad x (by rw [abs_le]; exact ⟨hx.1, hx.2⟩)
      have hpos : 0 < a0 - Real.pi ^ 2 * x ^ 2 / 12 := by linarith
      rw [abs_of_pos hpos]; exact h)
  -- numeric simplification
  have e2 := p0_pow_le hp1 2 le_rfl
  have e3 := p0_pow_le hp1 3 (by norm_num)
  have e4 := p0_pow_le hp1 4 (by norm_num)
  have hq : 0 ≤ p0 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hpi2 : 0 ≤ Real.pi ^ 2 := by positivity
  have hsum : 1 / p0 ^ 2 + Real.pi ^ 2 * 2 / (2 * p0 ^ 3) + Real.pi ^ 2 / (6 * p0 ^ 3)
      + Real.pi ^ 4 * 2 ^ 2 / (12 * p0 ^ 4) ≤ (1 + Real.pi ^ 2 + Real.pi ^ 2 / 6 + Real.pi ^ 4 / 3) * p0 ^ (-(3 / 2 : ℝ)) := by
    have a1 : Real.pi ^ 2 * 2 / (2 * p0 ^ 3) = Real.pi ^ 2 * (1 / p0 ^ 3) := by field_simp
    have a2 : Real.pi ^ 2 / (6 * p0 ^ 3) = Real.pi ^ 2 / 6 * (1 / p0 ^ 3) := by field_simp
    have a3 : Real.pi ^ 4 * 2 ^ 2 / (12 * p0 ^ 4) = Real.pi ^ 4 / 3 * (1 / p0 ^ 4) := by field_simp; ring
    rw [a1, a2, a3]
    have := mul_le_mul_of_nonneg_left e3 hpi2
    have := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ Real.pi ^ 2 / 6)
    have := mul_le_mul_of_nonneg_left e4 (by positivity : (0 : ℝ) ≤ Real.pi ^ 4 / 3)
    nlinarith
  calc ‖oscInt a0 (fun u => (ϑ u : ℂ) * g0)‖
      ≤ (2 - (-2)) * B * (1 / p0 ^ 2 + Real.pi ^ 2 * 2 / (2 * p0 ^ 3) + Real.pi ^ 2 / (6 * p0 ^ 3)
        + Real.pi ^ 4 * 2 ^ 2 / (12 * p0 ^ 4)) := hmain
    _ ≤ (2 - (-2)) * B * ((1 + Real.pi ^ 2 + Real.pi ^ 2 / 6 + Real.pi ^ 4 / 3) * p0 ^ (-(3 / 2 : ℝ))) := by
        gcongr
    _ = _ := by rw [hB]; ring


lemma nz_small_part {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a0 p0 G : ℝ} {g : ℝ → ℂ} {g0 : ℂ}, 2 ≤ p0 → 0 ≤ G → g 0 = g0 →
      (∀ u, 0 < |u| → |u| < 3 → ‖g u - g0‖ ≤ G * |u| ^ (1 / 2 : ℝ)) →
      ‖oscInt a0 (fun u => (ϑ (u / (1 / p0)) : ℂ) * (g u - g0))‖ ≤ C * G * p0 ^ (-(3 / 2 : ℝ)) := by
  refine ⟨8, by norm_num, ?_⟩
  intro a0 p0 G g g0 hp2 hG hg0 hH
  have hp0 : 0 < p0 := by linarith
  set r : ℝ := 2 / p0 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hp0]; exact hp2
  have hzero : ∀ x, x ∉ Set.Icc (-r) r → (ϑ (x / (1 / p0)) : ℂ) * (g x - g0) = 0 := by
    intro x hx
    have : 2 ≤ |x / (1 / p0)| := by
      have hx' : r < |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      rw [one_div, div_inv_eq_mul, abs_mul, abs_of_pos hp0]
      have : 2 / p0 * p0 = 2 := by field_simp
      nlinarith
    rw [hϑ.zero _ this]; simp
  unfold oscInt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-r) r) (fun x hx => by beta_reduce; rw [hzero x hx]; simp)]
  have hbd : ∀ x ∈ Set.Icc (-r) r, ‖(ϑ (x / (1 / p0)) : ℂ) * (g x - g0) *
      Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤ G * r ^ (1 / 2 : ℝ) := by
    intro x hx
    have hxr : |x| ≤ r := abs_le.mpr ⟨hx.1, hx.2⟩
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hϑ.range _).1]
    have hle : ‖g x - g0‖ ≤ G * r ^ (1 / 2 : ℝ) := by
      by_cases hx0 : x = 0
      · subst hx0; simp [hg0]; positivity
      · refine (hH x (abs_pos.mpr hx0) (by linarith)).trans ?_
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hxr (by norm_num)) hG
    calc ϑ (x / (1 / p0)) * ‖g x - g0‖ ≤ 1 * (G * r ^ (1 / 2 : ℝ)) :=
          mul_le_mul (hϑ.range _).2 hle (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (-r) r) (by simp) hbd
  refine this.trans ?_
  rw [Real.volume_real_Icc_of_le (by linarith)]
  have hrp : r ^ (1 / 2 : ℝ) ≤ 2 * p0 ^ (-(1 / 2 : ℝ)) := by
    rw [hr, Real.div_rpow (by norm_num) hp0.le, Real.rpow_neg hp0.le, div_eq_mul_inv]
    have : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by simp
    gcongr
  have hp32 : p0 ^ (-(1 / 2 : ℝ)) * p0⁻¹ = p0 ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hp0]; norm_num
  have hrr : (r - -r) = 4 * p0⁻¹ := by rw [hr]; field_simp; ring
  rw [hrr]
  calc G * r ^ (1 / 2 : ℝ) * (4 * p0⁻¹) ≤ G * (2 * p0 ^ (-(1 / 2 : ℝ))) * (4 * p0⁻¹) := by gcongr
    _ = 8 * G * (p0 ^ (-(1 / 2 : ℝ)) * p0⁻¹) := by ring
    _ = _ := by rw [hp32]


lemma contOn_rpow_Icc {α β : ℝ} (hα : 0 < α) (t : ℝ) : ContinuousOn (fun x : ℝ => x ^ t) (Set.Icc α β) :=
  continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hα hx.1)))

lemma setIntegral_le_aux {α β c d : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hc : 0 ≤ c) {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Icc α β)) (hle : ∀ x ∈ Set.Icc α β, f x ≤ c * x ^ (-(3 / 2 : ℝ)) + d) :
    ∫ x in Set.Icc α β, f x ≤ c * (2 * α ^ (-(1 / 2 : ℝ))) + d * (β - α) := by
  have hi1 : IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Set.Icc α β) :=
    (contOn_rpow_Icc hα _).integrableOn_Icc
  have hi : IntegrableOn (fun x : ℝ => c * x ^ (-(3 / 2 : ℝ)) + d) (Set.Icc α β) :=
    (hi1.const_mul c).add (integrableOn_const (by simp))
  calc ∫ x in Set.Icc α β, f x ≤ ∫ x in Set.Icc α β, (c * x ^ (-(3 / 2 : ℝ)) + d) :=
        setIntegral_mono_on hf hi measurableSet_Icc hle
    _ = c * (∫ x in Set.Icc α β, x ^ (-(3 / 2 : ℝ))) + d * (β - α) := by
        rw [integral_add (hi1.const_mul c) (integrableOn_const (by simp)), integral_const_mul, setIntegral_const,
          Real.volume_real_Icc_of_le hαβ, smul_eq_mul]
        ring
    _ ≤ c * (2 * α ^ (-(1 / 2 : ℝ))) + d * (β - α) := by
        have := int_rpow_m32 (β := β) hα
        gcongr


lemma nz_ibp_part {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a0 p0 G : ℝ} {g : ℝ → ℂ} {g0 : ℂ}, 2 ≤ p0 → 0 ≤ G →
      (∀ x, |x| ≤ 2 → p0 ≤ a0 - Real.pi ^ 2 * x ^ 2 / 12) →
      (∀ u, 0 < |u| → |u| < 3 → ContDiffAt ℝ 2 g u) →
      (∀ u, 0 < |u| → |u| < 3 → ‖g u - g0‖ ≤ G * |u| ^ (1 / 2 : ℝ)) →
      (∀ u, 0 < |u| → |u| < 3 → ‖deriv g u‖ ≤ G * |u| ^ (-(1 / 2 : ℝ))) →
      (∀ u, 0 < |u| → |u| < 3 → ‖deriv (deriv g) u‖ ≤ G * |u| ^ (-(3 / 2 : ℝ))) →
      ‖oscInt a0 (fun u => ((ϑ u - ϑ (u / (1 / p0)) : ℝ) : ℂ) * (g u - g0))‖ ≤ C * G * p0 ^ (-(3 / 2 : ℝ)) := by
  set Kc : ℝ := 8 * K2 + 8 * K1 + 2 with hKc
  have hKc0 : 0 ≤ Kc := by have := hϑ.hK1; have := hϑ.hK2; positivity
  refine ⟨2 * Kc * (2 + 4 * Real.pi ^ 2 / 3 * 2 + 2 * Real.pi ^ 4 / 3 * 2) , by positivity, ?_⟩
  intro a0 p0 G g g0 hp2 hG hgrad hc hH hd1 hd2
  have hp1 : 1 ≤ p0 := by linarith
  have hp0 : 0 < p0 := by linarith
  have hα : 0 < 1 / p0 := by positivity
  have hα2 : 1 / p0 ≤ 2 := by rw [div_le_iff₀ hp0]; linarith
  have hν : IsCut ϑ 1 (2 * K1) (4 * K2) := by simpa using hϑ.cut one_pos
  have hm := hϑ.cut hα
  have hη := hν.sub hm
  set η : ℝ → ℝ := fun u => ϑ u - ϑ (u / (1 / p0)) with hηdef
  have hη_small : ∀ u, |u| ≤ 1 / p0 → η u = 0 := by
    intro u hu
    have h1 : ϑ u = 1 := hϑ.one u (hu.trans (by rw [div_le_one hp0]; exact hp1))
    have h2 : ϑ (u / (1 / p0)) = 1 := by
      apply hϑ.one
      rw [one_div, div_inv_eq_mul, abs_mul, abs_of_pos hp0]
      calc |u| * p0 ≤ 1 / p0 * p0 := by gcongr
        _ = 1 := by field_simp
    have e : η u = ϑ u - ϑ (u / (1 / p0)) := rfl
    rw [e, h1, h2]; ring
  have hη_big : ∀ u, 2 ≤ |u| → η u = 0 := by
    intro u hu
    have h1 : ϑ u = 0 := hϑ.zero u hu
    have h2 : ϑ (u / (1 / p0)) = 0 := by
      apply hϑ.zero
      rw [one_div, div_inv_eq_mul, abs_mul, abs_of_pos hp0]
      nlinarith
    have e : η u = ϑ u - ϑ (u / (1 / p0)) := rfl
    rw [e, h1, h2]; ring
  -- global smoothness of the amplitude
  set gt : ℝ → ℂ := fun u => g u - g0 with hgt
  have hAC : ContDiff ℝ 2 (fun u => (η u : ℂ) * gt u) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    by_cases hu0 : u = 0
    · subst hu0
      have : (fun u => (η u : ℂ) * gt u) =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
        have h00 : |(0 : ℝ)| < 1 / p0 := by simpa using hα
        have : ∀ᶠ v in nhds (0 : ℝ), |v| < 1 / p0 := continuous_abs.continuousAt.eventually (gt_mem_nhds h00)
        filter_upwards [this] with v hv
        simp [hη_small v hv.le]
      exact (contDiffAt_const).congr_of_eventuallyEq this
    · by_cases hu3 : |u| < 3
      · have h1 : ContDiffAt ℝ 2 (fun u => (η u : ℂ)) u :=
          (Complex.ofRealCLM.contDiff.comp hη.contDiff).contDiffAt
        exact h1.mul ((hc u (abs_pos.mpr hu0) hu3).sub contDiffAt_const)
      · have : (fun u => (η u : ℂ) * gt u) =ᶠ[nhds u] fun _ => (0 : ℂ) := by
          have h3 : (2 : ℝ) < |u| := by linarith [not_lt.1 hu3]
          have : ∀ᶠ v in nhds u, 2 < |v| := continuous_abs.continuousAt.eventually (lt_mem_nhds h3)
          filter_upwards [this] with v hv
          simp [hη_big v hv.le]
        exact (contDiffAt_const).congr_of_eventuallyEq this
  -- Leibniz bounds
  have hdg : deriv gt = deriv g := funext fun x => deriv_sub_const g0
  have hleib : ∀ x, 1 / p0 ≤ |x| → |x| ≤ 2 →
      ‖(η x : ℂ) * gt x‖ ≤ Kc * G * |x| ^ (1 / 2 : ℝ) ∧
      ‖deriv (fun y => (η y : ℂ) * gt y) x‖ ≤ Kc * G * |x| ^ (-(1 / 2 : ℝ)) ∧
      ‖deriv (deriv (fun y => (η y : ℂ) * gt y)) x‖ ≤ Kc * G * |x| ^ (-(3 / 2 : ℝ)) := by
    intro x h1 h2
    have hxpos : 0 < |x| := lt_of_lt_of_le hα h1
    have hx0 : x ≠ 0 := abs_pos.mp hxpos
    have hx3 : |x| < 3 := by linarith
    have hcx : ContDiffAt ℝ 2 gt x := (hc x hxpos hx3).sub contDiffAt_const
    have hL := leibniz_cut hη hcx (G := G) (s := -(1 / 2 : ℝ)) hG hx0
      (by simpa [hgt, neg_neg] using hH x hxpos hx3)
      (by rw [hdg]; have := hd1 x hxpos hx3; norm_num at this ⊢; linarith [this])
      (by rw [hdg]; have := hd2 x hxpos hx3; norm_num at this ⊢; linarith [this])
    obtain ⟨h0', h1', h2'⟩ := hL
    have e0 : -(-(1 / 2 : ℝ)) = 1 / 2 := by norm_num
    have e1 : -(-(1 / 2 : ℝ)) - 1 = -(1 / 2) := by norm_num
    have e2 : -(-(1 / 2 : ℝ)) - 2 = -(3 / 2) := by norm_num
    rw [e0] at h0'; rw [e1] at h1'; rw [e2] at h2'
    have q0 : 0 ≤ |x| ^ (1 / 2 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have q1 : 0 ≤ |x| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    have q2 : 0 ≤ |x| ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    have k1 := hϑ.hK1
    have k2 := hϑ.hK2
    refine ⟨?_, ?_, ?_⟩
    · refine h0'.trans ?_
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Kc - (1 + 1)) (mul_nonneg hG q0)]
    · refine h1'.trans ?_
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Kc - (2 * K1 + 2 * K1 + (1 + 1))) (mul_nonneg hG q1)]
    · refine h2'.trans ?_
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ Kc - (4 * K2 + 4 * K2 + 2 * (2 * K1 + 2 * K1) + (1 + 1))) (mul_nonneg hG q2)]
  have hz : ∀ x, |x| < 1 / p0 → (η x : ℂ) * gt x = 0 := fun x hx => by simp [hη_small x hx.le]
  have hβ : ∀ x, 2 < |x| → (η x : ℂ) * gt x = 0 := fun x hx => by simp [hη_big x hx.le]
  set F : ℝ → ℝ := fun x => Kc * G * x ^ (-(3 / 2 : ℝ)) / p0 ^ 2
      + 3 * (Kc * G * x ^ (-(1 / 2 : ℝ))) * (Real.pi ^ 2 * |x| / 6) / p0 ^ 3
      + Kc * G * x ^ (1 / 2 : ℝ) * (Real.pi ^ 2 / 6) / p0 ^ 3
      + 3 * (Kc * G * x ^ (1 / 2 : ℝ)) * (Real.pi ^ 2 * x / 6) ^ 2 / p0 ^ 4 with hF
  have hFc : ContinuousOn F (Set.Icc (1 / p0) 2) := by
    have h1 := contOn_rpow_Icc (β := 2) hα (1 / 2 : ℝ)
    have h2 := contOn_rpow_Icc (β := 2) hα (-(1 / 2 : ℝ))
    have h3 := contOn_rpow_Icc (β := 2) hα (-(3 / 2 : ℝ))
    have h4 : ContinuousOn (fun x : ℝ => |x|) (Set.Icc (1 / p0) 2) := continuous_abs.continuousOn
    simp only [hF]
    fun_prop
  have hmain := ibp_pw_sym (a := fun u => (η u : ℂ) * gt u) (a0 := a0) (α := 1 / p0) (β := 2) (p0 := p0)
    (b0 := fun x => Kc * G * x ^ (1 / 2 : ℝ)) (b1 := fun x => Kc * G * x ^ (-(1 / 2 : ℝ)))
    (b2 := fun x => Kc * G * x ^ (-(3 / 2 : ℝ))) hα hα2 hp0 hAC hz hβ
    (fun x h1 h2 => (hleib x h1 h2).1) (fun x h1 h2 => (hleib x h1 h2).2.1) (fun x h1 h2 => (hleib x h1 h2).2.2)
    (fun x h1 h2 => by
      have h := hgrad x h2
      have hpos : 0 < a0 - Real.pi ^ 2 * x ^ 2 / 12 := by linarith
      rw [abs_of_pos hpos]; exact h)
    hFc.integrableOn_Icc
  -- pointwise bound for the integrand
  have hpt : ∀ x ∈ Set.Icc (1 / p0) 2, F x ≤ (Kc * G / p0 ^ 2) * x ^ (-(3 / 2 : ℝ)) +
      Kc * G * ((Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 + Real.pi ^ 4 / 12 * 8 / p0 ^ 4) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hα hx.1
    have hx2 : x ≤ 2 := hx.2
    have hxr1 : x ^ (-(1 / 2 : ℝ)) * x = x ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add_one hx0.ne']; norm_num
    have hX2 : x ^ (1 / 2 : ℝ) ≤ 2 := by
      calc x ^ (1 / 2 : ℝ) ≤ 2 ^ (1 / 2 : ℝ) := Real.rpow_le_rpow hx0.le hx2 (by norm_num)
        _ ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := by simp
    have hX0 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
    have hXx : x ^ (1 / 2 : ℝ) * x ^ 2 ≤ 8 := by
      have : x ^ 2 ≤ 4 := by nlinarith
      nlinarith
    have hKG : 0 ≤ Kc * G := mul_nonneg hKc0 hG
    have hp3 : 0 < p0 ^ 3 := pow_pos hp0 3
    have hp4 : 0 < p0 ^ 4 := pow_pos hp0 4
    have t1 : 3 * (Kc * G * x ^ (-(1 / 2 : ℝ))) * (Real.pi ^ 2 * |x| / 6) / p0 ^ 3
        = Kc * G * (Real.pi ^ 2 / 2) * x ^ (1 / 2 : ℝ) / p0 ^ 3 := by
      rw [abs_of_pos hx0, ← hxr1]; field_simp; ring
    have t3 : 3 * (Kc * G * x ^ (1 / 2 : ℝ)) * (Real.pi ^ 2 * x / 6) ^ 2 / p0 ^ 4
        = Kc * G * (Real.pi ^ 4 / 12) * (x ^ (1 / 2 : ℝ) * x ^ 2) / p0 ^ 4 := by
      field_simp; ring
    have hb1 : Kc * G * (Real.pi ^ 2 / 2) * x ^ (1 / 2 : ℝ) / p0 ^ 3 ≤ Kc * G * (Real.pi ^ 2 / 2) * 2 / p0 ^ 3 := by
      gcongr
    have hb2 : Kc * G * x ^ (1 / 2 : ℝ) * (Real.pi ^ 2 / 6) / p0 ^ 3 ≤ Kc * G * (Real.pi ^ 2 / 6) * 2 / p0 ^ 3 := by
      have : Kc * G * x ^ (1 / 2 : ℝ) * (Real.pi ^ 2 / 6) = Kc * G * (Real.pi ^ 2 / 6) * x ^ (1 / 2 : ℝ) := by ring
      rw [this]; gcongr
    have hb3 : Kc * G * (Real.pi ^ 4 / 12) * (x ^ (1 / 2 : ℝ) * x ^ 2) / p0 ^ 4 ≤ Kc * G * (Real.pi ^ 4 / 12) * 8 / p0 ^ 4 := by
      gcongr
    have e : (Kc * G / p0 ^ 2) * x ^ (-(3 / 2 : ℝ)) = Kc * G * x ^ (-(3 / 2 : ℝ)) / p0 ^ 2 := by ring
    have e2 : Kc * G * ((Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 + Real.pi ^ 4 / 12 * 8 / p0 ^ 4)
        = Kc * G * (Real.pi ^ 2 / 2) * 2 / p0 ^ 3 + Kc * G * (Real.pi ^ 2 / 6) * 2 / p0 ^ 3
          + Kc * G * (Real.pi ^ 4 / 12) * 8 / p0 ^ 4 := by ring
    simp only [hF]
    rw [t1, t3, e, e2]
    linarith
  have hI := setIntegral_le_aux (c := Kc * G / p0 ^ 2)
    (d := Kc * G * ((Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 + Real.pi ^ 4 / 12 * 8 / p0 ^ 4)) hα hα2
    (by positivity) hFc.integrableOn_Icc hpt
  -- final arithmetic
  have hpow : (1 / p0) ^ (-(1 / 2 : ℝ)) = p0 ^ (1 / 2 : ℝ) := by
    rw [one_div, Real.inv_rpow hp0.le, Real.rpow_neg hp0.le, inv_inv]
  have hq : p0 ^ (1 / 2 : ℝ) / p0 ^ 2 = p0 ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hp0]
    norm_num
  have e3 := p0_pow_le hp1 3 (by norm_num)
  have e4 := p0_pow_le hp1 4 (by norm_num)
  have hqq : 0 ≤ p0 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  have hKG : 0 ≤ Kc * G := mul_nonneg hKc0 hG
  have hlen : (2 : ℝ) - 1 / p0 ≤ 2 := by linarith
  have hd0 : 0 ≤ Kc * G * ((Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 + Real.pi ^ 4 / 12 * 8 / p0 ^ 4) := by positivity
  have hdle : Kc * G * ((Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 + Real.pi ^ 4 / 12 * 8 / p0 ^ 4)
      ≤ Kc * G * ((4 * Real.pi ^ 2 / 3 + 2 * Real.pi ^ 4 / 3) * p0 ^ (-(3 / 2 : ℝ))) := by
    have a1 : (Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 = 4 * Real.pi ^ 2 / 3 * (1 / p0 ^ 3) := by field_simp; ring
    have a2 : Real.pi ^ 4 / 12 * 8 / p0 ^ 4 = 2 * Real.pi ^ 4 / 3 * (1 / p0 ^ 4) := by field_simp; ring
    rw [a1, a2]
    have := mul_le_mul_of_nonneg_left e3 (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 / 3)
    have := mul_le_mul_of_nonneg_left e4 (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 4 / 3)
    refine mul_le_mul_of_nonneg_left ?_ hKG
    nlinarith
  have hc1 : Kc * G / p0 ^ 2 * (2 * (1 / p0) ^ (-(1 / 2 : ℝ))) = 2 * Kc * G * p0 ^ (-(3 / 2 : ℝ)) := by
    rw [hpow, ← hq]; ring
  calc _ ≤ 2 * ∫ x in Set.Icc (1 / p0) 2, F x := hmain
    _ ≤ 2 * (Kc * G / p0 ^ 2 * (2 * (1 / p0) ^ (-(1 / 2 : ℝ))) +
        Kc * G * ((Real.pi ^ 2 / 2 + Real.pi ^ 2 / 6) * 2 / p0 ^ 3 + Real.pi ^ 4 / 12 * 8 / p0 ^ 4) * (2 - 1 / p0)) := by
        gcongr
    _ ≤ 2 * (2 * Kc * G * p0 ^ (-(3 / 2 : ℝ)) +
        Kc * G * ((4 * Real.pi ^ 2 / 3 + 2 * Real.pi ^ 4 / 3) * p0 ^ (-(3 / 2 : ℝ))) * 2) := by
        rw [hc1]
        gcongr
    _ = _ := by ring


/-- **Near zero.** For `g` continuous at `0` with `g(0) = g₀`, `‖g₀‖ ≤ G`, and on `0 < |u| < 3` of class `C²` with
`‖g(u) - g₀‖ ≤ G|u|^{1/2}`, `‖g'(u)‖ ≤ G|u|^{-1/2}`, `‖g''(u)‖ ≤ G|u|^{-3/2}`, and phase gradient `ψ' ≥ p₀ ≥ 2` on `|u| ≤ 2`:
`‖∫ ϑ(u) g(u) e^{iψ(u)} du‖ ≤ C G p₀^{-3/2}`. -/
theorem near_zero_bound {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {a0 p0 G : ℝ} {g : ℝ → ℂ} {g0 : ℂ}, 2 ≤ p0 → 0 ≤ G → g 0 = g0 → ‖g0‖ ≤ G →
      (∀ x, |x| ≤ 2 → p0 ≤ a0 - Real.pi ^ 2 * x ^ 2 / 12) →
      (∀ u, 0 < |u| → |u| < 3 → ContDiffAt ℝ 2 g u) →
      (∀ u, 0 < |u| → |u| < 3 → ‖g u - g0‖ ≤ G * |u| ^ (1 / 2 : ℝ)) →
      (∀ u, 0 < |u| → |u| < 3 → ‖deriv g u‖ ≤ G * |u| ^ (-(1 / 2 : ℝ))) →
      (∀ u, 0 < |u| → |u| < 3 → ‖deriv (deriv g) u‖ ≤ G * |u| ^ (-(3 / 2 : ℝ))) →
      ‖oscInt a0 (fun u => (ϑ u : ℂ) * g u)‖ ≤ C * G * p0 ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨CA, hCA0, hA⟩ := nz_const_part hϑ
  obtain ⟨CB, hCB0, hB⟩ := nz_small_part hϑ
  obtain ⟨CC, hCC0, hC⟩ := nz_ibp_part hϑ
  refine ⟨CA + CB + CC, by positivity, ?_⟩
  intro a0 p0 G g g0 hp2 hG hg0 hgG hgrad hc hH hd1 hd2
  have hp0 : 0 < p0 := by linarith
  have hq : 0 ≤ p0 ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  set m : ℝ → ℝ := fun u => ϑ (u / (1 / p0)) with hm
  have hmc : Continuous m := hϑ.contDiff.continuous.comp (by fun_prop)
  have hm0 : ∀ u, 2 ≤ |u| → m u = 0 := by
    intro u hu
    apply hϑ.zero
    rw [one_div, div_inv_eq_mul, abs_mul, abs_of_pos hp0]
    nlinarith
  have hϑc : Continuous ϑ := hϑ.contDiff.continuous
  have hdecomp : ∀ u, (ϑ u : ℂ) * g u = (ϑ u : ℂ) * g0 + (m u : ℂ) * (g u - g0) + ((ϑ u - m u : ℝ) : ℂ) * (g u - g0) := by
    intro u; push_cast; ring
  have hI1 := integrable_osc_of_cont (f := fun u => (ϑ u : ℂ) * g0) ((Complex.continuous_ofReal.comp hϑc).mul continuous_const)
    (fun u hu => by simp [hϑ.zero u hu]) a0
  have hI2 := integrable_osc_of_cont (f := fun u => (m u : ℂ) * (g u - g0))
    (cut_mul_continuous hmc hm0 hg0 hc hH) (fun u hu => by simp [hm0 u hu]) a0
  have hI3 := integrable_osc_of_cont (f := fun u => ((ϑ u - m u : ℝ) : ℂ) * (g u - g0))
    (cut_mul_continuous (G := G) (hϑc.sub hmc) (fun u hu => by simp [hϑ.zero u hu, hm0 u hu]) hg0 hc hH)
    (fun u hu => by simp [hϑ.zero u hu, hm0 u hu]) a0
  have hsum : oscInt a0 (fun u => (ϑ u : ℂ) * g u) =
      oscInt a0 (fun u => (ϑ u : ℂ) * g0) + oscInt a0 (fun u => (m u : ℂ) * (g u - g0)) +
        oscInt a0 (fun u => ((ϑ u - m u : ℝ) : ℂ) * (g u - g0)) := by
    rw [← oscInt_add3 a0 hI1 hI2 hI3]
    congr 1
    funext u
    exact hdecomp u
  have bA := hA (a0 := a0) (g0 := g0) hp2 hgrad
  have bB := hB (a0 := a0) (g := g) (g0 := g0) hp2 hG hg0 hH
  have bC := hC (a0 := a0) (g := g) (g0 := g0) hp2 hG hgrad hc hH hd1 hd2
  rw [hsum]
  calc _ ≤ ‖oscInt a0 (fun u => (ϑ u : ℂ) * g0)‖ + ‖oscInt a0 (fun u => (m u : ℂ) * (g u - g0))‖ +
        ‖oscInt a0 (fun u => ((ϑ u - m u : ℝ) : ℂ) * (g u - g0))‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ CA * ‖g0‖ * p0 ^ (-(3 / 2 : ℝ)) + CB * G * p0 ^ (-(3 / 2 : ℝ)) + CC * G * p0 ^ (-(3 / 2 : ℝ)) := by
        gcongr
    _ ≤ CA * G * p0 ^ (-(3 / 2 : ℝ)) + CB * G * p0 ^ (-(3 / 2 : ℝ)) + CC * G * p0 ^ (-(3 / 2 : ℝ)) := by
        gcongr
    _ = _ := by ring

/-- info: 'FormalResearch.SignUncertainty.near_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms near_zero_bound

end FormalResearch.SignUncertainty

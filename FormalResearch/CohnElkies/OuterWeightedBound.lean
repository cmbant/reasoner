module

public import FormalResearch.CohnElkies.OuterAmplitude

/-!
# The outer integral of `I_main` with a weighted amplitude (`O.3(2)`, the `(1 - χ_ξ)`-part)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `u1co:O3`(2), item *Pieces*.  `main_outer_phase_bound` bounds the outer integral by a
sup-norm bound `A_h (1+τ²)^{-5/4}` on `h^{(r)}`, `r ≤ 2`, which loses powers of `τ₁^{-1}` when the amplitude lives on `|τ| ≥ τ₁` with `τ₁ ≪ 1`
(`L ≤ 1`).  Here the amplitude is given by the weighted bounds `‖h^{(r)}‖ ≤ Q |τ|^{-(m+5/2+r)}` on `|τ| ≥ τ₁` of `outer_amplitude`:

* `outer_bound_large_tau` (`τ₁ ≥ 1`): the sup form applies without loss, `A_h = 2^{5/4} Q τ₁^{-m}`;
* `outer_bound_small_L` (`L ≤ 8`, any `τ₁ > 0`): each term of the binomial expansion is bounded by `dual_phase_mv_bound` from the sup norm and the total
  variation of `k h`, which are `≲ Q τ₁^{-(m+5/2)} (1 + τ₁)`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Asymptotics

/-! ### Elementary weights -/

lemma rpow_abs_le_two_pow_mul {t τ₁ : ℝ} {s : ℝ} (hs : 0 ≤ s) (hτ₁ : 0 < τ₁) (ht : τ₁ ≤ t) :
    t ^ (-s) ≤ 2 ^ s * τ₁ ^ (-s) * (1 + t / τ₁) ^ (-s) := by
  have ht0 : 0 < t := hτ₁.trans_le ht
  set u : ℝ := t / τ₁ with hu
  have hu1 : 1 ≤ u := by rw [hu, le_div_iff₀ hτ₁]; linarith
  have hu0 : 0 < u := by linarith
  have htu : t = τ₁ * u := by rw [hu]; field_simp
  have h1 : 1 + u ≤ 2 * u := by linarith
  have h2 : (2 * u) ^ (-s) ≤ (1 + u) ^ (-s) := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  rw [Real.mul_rpow (by norm_num) hu0.le] at h2
  have e1 : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
  have h3 : u ^ (-s) ≤ 2 ^ s * (1 + u) ^ (-s) := by
    calc u ^ (-s) = 2 ^ s * (2 ^ (-s) * u ^ (-s)) := by rw [← mul_assoc, e1, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  rw [htu, Real.mul_rpow hτ₁.le hu0.le]
  calc τ₁ ^ (-s) * u ^ (-s) ≤ τ₁ ^ (-s) * (2 ^ s * (1 + u) ^ (-s)) := mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = _ := by ring

lemma integrable_scaled_weight {s : ℝ} (hs : 1 < s) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    Integrable (fun τ : ℝ => (1 + |τ| / τ₁) ^ (-s)) := by
  have h := (integrable_w0 hs).comp_div hτ₁.ne'
  refine h.congr (ae_of_all _ fun τ => ?_)
  simp only [abs_div, abs_of_pos hτ₁]

lemma integral_scaled_weight_le {s : ℝ} (hs : 2 ≤ s) {τ₁ : ℝ} (hτ₁ : 0 < τ₁) :
    ∫ τ : ℝ, (1 + |τ| / τ₁) ^ (-s) ≤ τ₁ * ∫ x : ℝ, (1 + |x|) ^ (-(2 : ℝ)) := by
  have h1 : ∫ τ : ℝ, (1 + |τ| / τ₁) ^ (-s) = τ₁ * ∫ x : ℝ, (1 + |x|) ^ (-s) := by
    have := Measure.integral_comp_div (fun x : ℝ => (1 + |x|) ^ (-s)) τ₁
    simp only [abs_div, abs_of_pos hτ₁, smul_eq_mul] at this ⊢
    exact this
  rw [h1]
  refine mul_le_mul_of_nonneg_left (integral_mono (integrable_w0 (by linarith)) (integrable_w0 (by norm_num)) fun x => ?_) hτ₁.le
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg x]) (by linarith)

/-! ### The smooth factor `k_c` -/

/-- `k_c(τ) = (1 - iτ)^{-1/2} e^{B_c(iτ)}`. -/
noncomputable def outerK (c : ℝ) (τ : ℝ) : ℂ :=
  (1 - Complex.I * (τ : ℂ)) ^ (-((1 / 2 : ℝ) : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ)))

lemma outerK_eq (c τ : ℝ) : (1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) = outerK c τ := by
  unfold outerK; push_cast; rfl

lemma outerK_bounds : ∃ C_K > 0, ∀ {c : ℝ}, 2 ≤ c → ContDiff ℝ 2 (outerK c) ∧
    ∀ r ≤ 2, ∀ τ : ℝ, ‖iteratedDeriv r (outerK c) τ‖ ≤ C_K * (1 + τ ^ 2) ^ (-(1 / 4 : ℝ)) := by
  refine ⟨8 * (2 ^ (1 / 2 : ℝ) * Real.exp 1), by positivity, fun {c} hc => ?_⟩
  obtain ⟨hk_cd, hk_bd⟩ := cpow_mul_binet_deriv_bound (by norm_num : (0 : ℝ) < 1 / 2) hc
  refine ⟨hk_cd.of_le (by simp), fun r hr τ => ?_⟩
  refine (hk_bd r hr τ).trans (le_of_eq ?_)
  norm_num

/-! ### Case `τ₁ ≥ 1` -/

theorem outer_bound_large_tau :
    ∃ C > 0, ∀ {m : ℕ}, 1 ≤ m → ∀ {κ c L Q τ₁ : ℝ} {h : ℝ → ℂ}, 0 < κ → 2 ≤ c → 0 < L → (m : ℝ) * κ ≤ c * L / 2 →
      1 ≤ c * (L / 2) ^ (3 / 2 : ℝ) → 0 ≤ Q → 1 ≤ τ₁ → ContDiff ℝ 2 h → (∀ τ : ℝ, |τ| < τ₁ → h τ = 0) →
      (∀ r ≤ 2, ∀ τ : ℝ, τ₁ ≤ |τ| → ‖iteratedDeriv r h τ‖ ≤ Q * |τ| ^ (-((m : ℝ) + 5 / 2 + r))) →
      ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
          (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        C * 2 ^ m * (2 ^ (5 / 4 : ℝ) * Q * τ₁ ^ (-(m : ℝ))) * c ^ (-(1 / 2 : ℝ)) * min (L ^ (-(1 / 4 : ℝ))) (L ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hmain⟩ := main_outer_phase_bound
  refine ⟨C, hC, fun {m} hm {κ c L Q τ₁} {h} hκ hc hL hmκ hcL hQ hτ₁ hh_cd hvan hbd => ?_⟩
  have hτ₁0 : 0 < τ₁ := by linarith
  refine hmain hm hκ hc hL hmκ hcL (by positivity) hh_cd (fun r hr τ => ?_)
  by_cases hτ : |τ| < τ₁
  · have h0 : h =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hτ] with x hx using hvan x hx
    rw [h0.iteratedDeriv_eq]
    rw [iteratedDeriv_fun_const_zero, norm_zero]; positivity
  · have hτ' : τ₁ ≤ |τ| := not_lt.mp hτ
    have ht : 1 ≤ |τ| := hτ₁.trans hτ'
    have ht0 : 0 < |τ| := by linarith
    refine (hbd r hr τ hτ').trans ?_
    have e1 : |τ| ^ (-((m : ℝ) + 5 / 2 + r)) ≤ τ₁ ^ (-(m : ℝ)) * |τ| ^ (-(5 / 2 : ℝ)) := by
      have : |τ| ^ (-((m : ℝ) + 5 / 2 + r)) = |τ| ^ (-((m : ℝ) + r)) * |τ| ^ (-(5 / 2 : ℝ)) := by
        rw [← Real.rpow_add ht0]; ring_nf
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      calc |τ| ^ (-((m : ℝ) + r)) ≤ |τ| ^ (-(m : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le ht (by linarith [Nat.cast_nonneg (α := ℝ) r])
        _ ≤ τ₁ ^ (-(m : ℝ)) := Real.rpow_le_rpow_of_nonpos hτ₁0 hτ' (by simp)
    have e2 : |τ| ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 4 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) := by
      have h1 : 1 + τ ^ 2 ≤ 2 * (|τ| ^ (2 : ℝ)) := by
        rw [Real.rpow_two, sq_abs]; nlinarith [(one_le_sq_iff_one_le_abs τ).mpr ht]
      have h2 : (2 * (|τ| ^ (2 : ℝ))) ^ (-(5 / 4 : ℝ)) ≤ (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      have h3 : (2 * (|τ| ^ (2 : ℝ))) ^ (-(5 / 4 : ℝ)) = 2 ^ (-(5 / 4 : ℝ)) * |τ| ^ (-(5 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul ht0.le]; norm_num
      have h4 : (2 : ℝ) ^ (5 / 4 : ℝ) * 2 ^ (-(5 / 4 : ℝ)) = 1 := by rw [← Real.rpow_add (by norm_num)]; simp
      rw [h3] at h2
      calc |τ| ^ (-(5 / 2 : ℝ)) = (2 ^ (5 / 4 : ℝ) * 2 ^ (-(5 / 4 : ℝ))) * |τ| ^ (-(5 / 2 : ℝ)) := by rw [h4, one_mul]
        _ = 2 ^ (5 / 4 : ℝ) * (2 ^ (-(5 / 4 : ℝ)) * |τ| ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
    calc Q * |τ| ^ (-((m : ℝ) + 5 / 2 + r)) ≤ Q * (τ₁ ^ (-(m : ℝ)) * |τ| ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left e1 hQ
      _ ≤ Q * (τ₁ ^ (-(m : ℝ)) * (2 ^ (5 / 4 : ℝ) * (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)))) := by gcongr
      _ = _ := by ring

/-! ### Case `L ≤ 8` -/

lemma tv_le_integral {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) {W : ℝ → ℝ} (hW : Integrable W)
    (hbd : ∀ x : ℝ, ‖deriv g x‖ ≤ W x) {u v : ℝ} (huv : u ≤ v) :
    (eVariationOn g (Icc u v)).toReal ≤ ∫ x : ℝ, W x := by
  have hint : IntervalIntegrable (deriv g) volume u v := (hg.continuous_deriv (by decide)).intervalIntegrable u v
  have hev := eVariationOn_le_integral_norm_deriv huv (fun x _ => ((hg.differentiable (by decide)) x).hasDerivAt) hint
  have hW0 : ∀ x : ℝ, 0 ≤ W x := fun x => (norm_nonneg _).trans (hbd x)
  have h1 : ∫ t in u..v, ‖deriv g t‖ ≤ ∫ x : ℝ, W x := by
    calc ∫ t in u..v, ‖deriv g t‖ ≤ ∫ t in u..v, W t :=
          intervalIntegral.integral_mono_on huv hint.norm (hW.intervalIntegrable) fun t _ => hbd t
      _ = ∫ t in Ioc u v, W t := intervalIntegral.integral_of_le huv
      _ ≤ ∫ x : ℝ, W x := setIntegral_le_integral hW (Filter.Eventually.of_forall hW0)
  exact ENNReal.toReal_le_of_le_ofReal (integral_nonneg hW0) (hev.trans (ENNReal.ofReal_le_ofReal h1))

theorem outer_bound_small_L :
    ∃ C > 0, ∀ {m : ℕ}, 1 ≤ m → ∀ {κ c L Q τ₁ : ℝ} {h : ℝ → ℂ}, 0 < κ → 2 ≤ c → 0 < L → L ≤ 8 → (m : ℝ) * κ ≤ c * L / 2 →
      1 ≤ c * (L / 2) ^ (3 / 2 : ℝ) → 0 ≤ Q → 0 < τ₁ → ContDiff ℝ 2 h → (∀ τ : ℝ, |τ| < τ₁ → h τ = 0) →
      (∀ r ≤ 2, ∀ τ : ℝ, τ₁ ≤ |τ| → ‖iteratedDeriv r h τ‖ ≤ Q * |τ| ^ (-((m : ℝ) + 5 / 2 + r))) →
      ‖∫ τ : ℝ, ((1 - Complex.I * (τ : ℂ)) ^ (-(1 / 2 : ℂ)) * Complex.exp (binetDiff c (Complex.I * (τ : ℂ))) *
          (bsplineImag κ m τ * ((Complex.I * (κ : ℂ) * (τ : ℂ)) ^ m * h τ))) *
            Complex.exp (Complex.I * (c : ℂ) * (edgePhi L τ : ℂ))‖ ≤
        C * 4 ^ m * Q * τ₁ ^ (-((m : ℝ) + 5 / 2)) * (1 + τ₁) * c ^ (-(1 / 2 : ℝ)) * L ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C_mv, hCmv, hmv⟩ := dual_phase_mv_bound
  obtain ⟨C_K, hCK, hK⟩ := outerK_bounds
  let J : ℝ := ∫ x : ℝ, (1 + |x|) ^ (-(2 : ℝ))
  have hJ0 : 0 ≤ J := integral_nonneg fun x => by positivity
  refine ⟨C_mv * C_K * 2 ^ (5 / 2 : ℝ) * (1 + J) * 2 ^ (1 / 4 : ℝ), by positivity,
    fun {m} hm {κ c L Q τ₁} {h} hκ hc hL hL8 hmκ hcL hQ hτ₁ hh_cd hvan hbd => ?_⟩
  have hc_pos : 0 < c := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set s : ℝ := (m : ℝ) + 5 / 2 with hs
  have hs2 : 2 ≤ s := by rw [hs]; linarith
  obtain ⟨hk_cd, hk_bd⟩ := hK hc
  let g : ℝ → ℂ := fun τ => outerK c τ * h τ
  let Hb : ℝ → ℝ := fun τ => Q * 2 ^ s * τ₁ ^ (-s) * (1 + |τ| / τ₁) ^ (-s)
  have hHb0 : ∀ τ, 0 ≤ Hb τ := fun τ => by positivity
  have hzero : ∀ τ : ℝ, |τ| < τ₁ → h =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := fun τ hτ => by
    filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds hτ] with x hx using hvan x hx
  have hh0 : ∀ τ, ‖h τ‖ ≤ Hb τ := fun τ => by
    by_cases hτ : |τ| < τ₁
    · rw [hvan τ hτ]; simpa using hHb0 τ
    · have hτ' : τ₁ ≤ |τ| := not_lt.mp hτ
      have := hbd 0 (by norm_num) τ hτ'
      rw [iteratedDeriv_zero] at this
      refine this.trans ?_
      have e : -((m : ℝ) + 5 / 2 + ((0 : ℕ) : ℝ)) = -s := by rw [hs]; simp
      rw [e]
      have := rpow_abs_le_two_pow_mul (s := s) (by linarith) hτ₁ hτ'
      calc Q * |τ| ^ (-s) ≤ Q * (2 ^ s * τ₁ ^ (-s) * (1 + |τ| / τ₁) ^ (-s)) := mul_le_mul_of_nonneg_left this hQ
        _ = Hb τ := by simp only [Hb]; ring
  have hh1 : ∀ τ, ‖deriv h τ‖ ≤ τ₁⁻¹ * Hb τ := fun τ => by
    by_cases hτ : |τ| < τ₁
    · rw [(hzero τ hτ).deriv_eq]; simp only [deriv_const]; simpa using mul_nonneg (inv_nonneg.mpr hτ₁.le) (hHb0 τ)
    · have hτ' : τ₁ ≤ |τ| := not_lt.mp hτ
      have ht0 : 0 < |τ| := hτ₁.trans_le hτ'
      have := hbd 1 (by norm_num) τ hτ'
      rw [iteratedDeriv_one] at this
      refine this.trans ?_
      have e : -((m : ℝ) + 5 / 2 + ((1 : ℕ) : ℝ)) = -s + -1 := by rw [hs]; simp; ring
      rw [e, Real.rpow_add ht0]
      have h1 : |τ| ^ (-(1 : ℝ)) ≤ τ₁⁻¹ := by
        rw [Real.rpow_neg_one]; exact inv_anti₀ hτ₁ hτ'
      have h2 := rpow_abs_le_two_pow_mul (s := s) (by linarith) hτ₁ hτ'
      calc Q * (|τ| ^ (-s) * |τ| ^ (-1 : ℝ)) ≤ Q * ((2 ^ s * τ₁ ^ (-s) * (1 + |τ| / τ₁) ^ (-s)) * τ₁⁻¹) := by gcongr
        _ = τ₁⁻¹ * Hb τ := by simp only [Hb]; ring
  have hk0 : ∀ τ, ‖outerK c τ‖ ≤ C_K := fun τ => by
    have := hk_bd 0 (by norm_num) τ
    rw [iteratedDeriv_zero] at this
    exact this.trans (mul_le_of_le_one_right hCK.le (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg τ]) (by norm_num)))
  have hk1 : ∀ τ, ‖deriv (outerK c) τ‖ ≤ C_K := fun τ => by
    have := hk_bd 1 (by norm_num) τ
    rw [iteratedDeriv_one] at this
    exact this.trans (mul_le_of_le_one_right hCK.le (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [sq_nonneg τ]) (by norm_num)))
  have hg_cd : ContDiff ℝ 2 g := hk_cd.mul hh_cd
  have hgb : ∀ τ, ‖g τ‖ ≤ C_K * Hb τ := fun τ => by
    simp only [g]; rw [norm_mul]
    exact mul_le_mul (hk0 τ) (hh0 τ) (norm_nonneg _) hCK.le
  have hgd : ∀ τ, ‖deriv g τ‖ ≤ C_K * (1 + τ₁⁻¹) * Hb τ := fun τ => by
    have : deriv g τ = deriv (outerK c) τ * h τ + outerK c τ * deriv h τ := deriv_mul_of_contDiff hk_cd hh_cd τ
    rw [this]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    calc ‖deriv (outerK c) τ‖ * ‖h τ‖ + ‖outerK c τ‖ * ‖deriv h τ‖ ≤ C_K * Hb τ + C_K * (τ₁⁻¹ * Hb τ) :=
          add_le_add (mul_le_mul (hk1 τ) (hh0 τ) (norm_nonneg _) hCK.le) (mul_le_mul (hk0 τ) (hh1 τ) (norm_nonneg _) hCK.le)
      _ = _ := by ring
  have hHint : Integrable Hb := by
    have := (integrable_scaled_weight (s := s) (by linarith) hτ₁).const_mul (Q * 2 ^ s * τ₁ ^ (-s))
    exact this
  have hHint_le : ∫ τ : ℝ, Hb τ ≤ Q * 2 ^ s * τ₁ ^ (-s) * (τ₁ * J) := by
    have h1 : ∫ τ : ℝ, Hb τ = Q * 2 ^ s * τ₁ ^ (-s) * ∫ τ : ℝ, (1 + |τ| / τ₁) ^ (-s) := integral_const_mul _ _
    rw [h1]
    exact mul_le_mul_of_nonneg_left (integral_scaled_weight_le hs2 hτ₁) (by positivity)
  let M : ℝ := C_K * (Q * 2 ^ s * τ₁ ^ (-s))
  let V : ℝ := C_K * (1 + τ₁⁻¹) * (Q * 2 ^ s * τ₁ ^ (-s) * (τ₁ * J))
  have hM : ∀ τ, ‖g τ‖ ≤ M := fun τ => by
    refine (hgb τ).trans ?_
    simp only [M, Hb]
    have h0' : 0 ≤ |τ| / τ₁ := by positivity
    have : (1 + |τ| / τ₁) ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc C_K * (Q * 2 ^ s * τ₁ ^ (-s) * (1 + |τ| / τ₁) ^ (-s)) ≤ C_K * (Q * 2 ^ s * τ₁ ^ (-s) * 1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this (by positivity)) hCK.le
      _ = _ := by ring
  have hV : ∀ u v : ℝ, u ≤ v → (eVariationOn g (Icc u v)).toReal ≤ V := fun u v huv => by
    have hW : Integrable (fun τ => C_K * (1 + τ₁⁻¹) * Hb τ) := hHint.const_mul _
    refine (tv_le_integral hg_cd hW hgd huv).trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hHint_le (by positivity)
  have hMV : M + V ≤ C_K * Q * 2 ^ s * τ₁ ^ (-s) * ((1 + J) * (1 + τ₁)) := by
    have e : M + V = C_K * Q * 2 ^ s * τ₁ ^ (-s) * (1 + (1 + τ₁⁻¹) * (τ₁ * J)) := by simp only [M, V]; ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have : (1 + τ₁⁻¹) * (τ₁ * J) = (τ₁ + 1) * J := by field_simp
    rw [this]; nlinarith [mul_nonneg hτ₁.le hJ0]
  have hMV0 : 0 ≤ M + V := by
    have := (norm_nonneg (g 0)).trans (hM 0)
    have h2 := (ENNReal.toReal_nonneg (a := eVariationOn g (Icc 0 0))).trans (hV 0 0 le_rfl)
    linarith
  let Lj : ℕ → ℝ := fun j => L - (j : ℝ) * κ / c
  have hLj : ∀ j ∈ Finset.range (m + 1), L / 2 ≤ Lj j := fun j hj => by
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [Lj]
    have : (j : ℝ) * κ / c ≤ L / 2 := by
      rw [div_le_iff₀ hc_pos]; nlinarith [mul_le_mul_of_nonneg_right hjm hκ.le]
    linarith
  have hLj' : ∀ j ∈ Finset.range (m + 1), Lj j ≤ L := fun j hj => by
    simp only [Lj]
    have : 0 ≤ (j : ℝ) * κ / c := by positivity
    linarith
  have hmain := outer_decomp_bound (m := m) (κ := κ) (L := L) (h := h) (B := C_mv * (M + V) * c ^ (-(1 / 2 : ℝ)) * (2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ)))) hc
    (fun j hj => by
      simp only [outerK_eq]
      exact (hHint.const_mul C_K).mono' (dual_phase_cont hg_cd).aestronglyMeasurable (ae_of_all _ fun τ => by
        rw [norm_mul, show Complex.I * (c : ℂ) * (edgePhi (L - (j : ℝ) * κ / c) τ : ℂ) = ((c * edgePhi (L - (j : ℝ) * κ / c) τ : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact hgb τ))
    (fun j hj => by
      simp only [outerK_eq]
      have hLj2 := hLj j hj
      have hLjpos : 0 < Lj j := by linarith
      have hint : Integrable (fun τ : ℝ => g τ * Complex.exp (Complex.I * (c : ℂ) * (edgePhi (Lj j) τ : ℂ))) :=
        (hHint.const_mul C_K).mono' (dual_phase_cont hg_cd).aestronglyMeasurable (ae_of_all _ fun τ => by
          rw [norm_mul, show Complex.I * (c : ℂ) * (edgePhi (Lj j) τ : ℂ) = ((c * edgePhi (Lj j) τ : ℝ) : ℂ) * Complex.I by
            push_cast; ring, Complex.norm_exp_ofReal_mul_I, mul_one]
          exact hgb τ)
      have hcLj : 1 ≤ c * (Lj j) ^ (3 / 2 : ℝ) :=
        hcL.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hLj2 (by norm_num)) hc_pos.le)
      have h1 := hmv hg_cd hM hV hint hc hLjpos (hLj' j hj |>.trans hL8) hcLj
      have h2 : (Lj j) ^ (-(1 / 4 : ℝ)) ≤ 2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ)) := by
        refine (Real.rpow_le_rpow_of_nonpos (by positivity) hLj2 (by norm_num)).trans_eq ?_
        rw [Real.div_rpow hL.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
      refine h1.trans ?_
      calc C_mv * (M + V) * c ^ (-(1 / 2 : ℝ)) * (Lj j) ^ (-(1 / 4 : ℝ)) ≤
          C_mv * (M + V) * c ^ (-(1 / 2 : ℝ)) * (2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ _ := le_rfl)
  refine hmain.trans ?_
  have h2s : (2 : ℝ) ^ s = 2 ^ m * 2 ^ (5 / 2 : ℝ) := by
    rw [hs, Real.rpow_add (by norm_num), Real.rpow_natCast]
  have hfin : C_mv * (M + V) * c ^ (-(1 / 2 : ℝ)) * (2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ))) ≤
      C_mv * (C_K * Q * 2 ^ s * τ₁ ^ (-s) * ((1 + J) * (1 + τ₁))) * c ^ (-(1 / 2 : ℝ)) * (2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ))) := by
    gcongr
  calc 2 ^ m * (C_mv * (M + V) * c ^ (-(1 / 2 : ℝ)) * (2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ))))
      ≤ 2 ^ m * (C_mv * (C_K * Q * 2 ^ s * τ₁ ^ (-s) * ((1 + J) * (1 + τ₁))) * c ^ (-(1 / 2 : ℝ)) * (2 ^ (1 / 4 : ℝ) * L ^ (-(1 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = _ := by
      rw [h2s]
      have : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
      rw [this]
      ring

/-- info: 'FormalResearch.CohnElkies.outerK_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.outerK_bounds
/-- info: 'FormalResearch.CohnElkies.outer_bound_large_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.outer_bound_large_tau
/-- info: 'FormalResearch.CohnElkies.outer_bound_small_L' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FormalResearch.CohnElkies.outer_bound_small_L

end FormalResearch.CohnElkies

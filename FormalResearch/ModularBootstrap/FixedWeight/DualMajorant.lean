module

public import FormalResearch.ModularBootstrap.Duality.DualMajorant
public import FormalResearch.ModularBootstrap.FixedWeight.CrossingMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Fixed-Weight Dual Majorant `h` (Lemma M of `dual_spectrum.tex`)

Generalises `Duality.DualMajorant` (`CFT/modular_bootstrap/paper/dual_spectrum.tex`, Lemma M,
`ds:M`) to every fixed-weight problem `prob : FixedWeightProblem` (`w ≥ 1`, positive product
`Q(q) = ∏ (1 - q^{μ_l})`, `a = c̃ / 12 > 0`, `a ≥ S = ∑ μ_l`):

* `t0 w β = β log(2 β^{-w}) / (2π(1 - β²))` and `t0Star w β₀ = sup_{0 < β ≤ β₀} t0 w β`,
  with `t0_mono` for all `w` on `(0, 1)` (hence `t0Star w β₀ = t0 w β₀` on `(0, 1/2]`);
* `hMaj w a β₀ t = 2 ∫₀^{β₀} Ξ_β^{(w)}(t) ϑ(dβ)` and `dualC0 prob a β₀`;
* `hMaj_mem_TestClass`, `hMaj_vac`, `dualC0_pos`, `wStar_le_hMaj`, `tendsto_thermalDiff_div_wStar`,
  `tendsto_psiK_div_wStar`;
* `lemma_M`: full Lemma M (`ds:M`) at general `(w, Q)`, including `ψ_k / w_* → 0` for the
  generalized Laguerre functions `ψ_k(t) = L_k^{(w-1)}(4π t) e^{-2π t}`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real FourierTransform

namespace FormalResearch.ModularBootstrap.FixedWeight

open FormalResearch.ModularBootstrap.Crossing
open FormalResearch.ModularBootstrap.Duality

/-! ### Section 1: Cutoff `t₀(w, β)` and monotonicity on `(0, 1)` -/

/-- `t₀(w, β) = β log(2 β^{-w}) / (2π(1 - β²))`: `2 Ξ_β(t) ≥ e^{-2πβt}` iff `t ≥ t₀(w, β)`. -/
noncomputable def t0 (w : ℕ) (β : ℝ) : ℝ :=
  β * Real.log (2 * β ^ (-(w : ℝ))) / (2 * π * (1 - β ^ 2))

/-- `t₀^*(w, β₀) = sup_{0 < β ≤ β₀} t₀(w, β)`. -/
noncomputable def t0Star (w : ℕ) (β₀ : ℝ) : ℝ :=
  sSup (t0 w '' Ioc 0 β₀)

lemma t0_one (β : ℝ) : t0 1 β = Duality.t0 β := by
  unfold t0 Duality.t0
  simp only [Nat.cast_one, Real.rpow_neg_one]
  ring_nf

private lemma sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    (x ^ 2 - 1) / (x ^ 2 + 1) ≤ Real.log x := by
  let f : ℝ → ℝ := fun y => Real.log y - (y ^ 2 - 1) / (y ^ 2 + 1)
  have hf_mono : MonotoneOn f (Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · exact Real.continuousOn_log.mono fun y hy => ne_of_gt (lt_of_lt_of_le zero_lt_one hy)
      · exact Continuous.continuousOn (by fun_prop (disch := intro y; positivity))
    · refine DifferentiableOn.sub ?_ ?_
      · intro y hy
        exact (Real.differentiableAt_log (ne_of_gt (lt_of_lt_of_le zero_lt_one (interior_subset hy)))).differentiableWithinAt
      · intro y _
        exact (DifferentiableAt.div (by fun_prop) (by fun_prop) (by positivity)).differentiableWithinAt
    · intro y hy
      have hy1 : 1 < y := by simpa [interior_Ici] using hy
      have hy0 : 0 < y := by linarith
      have hd1 : HasDerivAt Real.log y⁻¹ y := Real.hasDerivAt_log hy0.ne'
      have hd2 : HasDerivAt (fun z : ℝ => (z ^ 2 - 1) / (z ^ 2 + 1))
          (((2 * y) * (y ^ 2 + 1) - (y ^ 2 - 1) * (2 * y)) / (y ^ 2 + 1) ^ 2) y := by
        exact (((hasDerivAt_pow 2 y).sub_const 1).div ((hasDerivAt_pow 2 y).add_const 1)
          (by positivity)).congr_deriv (by ring)
      have hdiv : deriv f y =
          y⁻¹ - ((2 * y) * (y ^ 2 + 1) - (y ^ 2 - 1) * (2 * y)) / (y ^ 2 + 1) ^ 2 :=
        (hd1.sub hd2).deriv
      change 0 ≤ deriv f y
      rw [hdiv]
      have hid : y⁻¹ - ((2 * y) * (y ^ 2 + 1) - (y ^ 2 - 1) * (2 * y)) / (y ^ 2 + 1) ^ 2 =
          (y ^ 2 - 1) ^ 2 / (y * (y ^ 2 + 1) ^ 2) := by
        field_simp [hy0.ne']; ring
      rw [hid]
      positivity
  have h0 : f 1 ≤ f x := hf_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  have hf1 : f 1 = 0 := by simp [f]
  linarith

private lemma neg_mul_log_div_one_sub_sq_mono {β β' : ℝ} (hβ : 0 < β) (hle : β ≤ β')
    (hβ' : β' < 1) :
    (-β * Real.log β) / (1 - β ^ 2) ≤ (-β' * Real.log β') / (1 - β' ^ 2) := by
  let g : ℝ → ℝ := fun u => (-u * Real.log u) / (1 - u ^ 2)
  have hg_mono : MonotoneOn g (Ioo 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioo 0 1) ?_ ?_ ?_
    · refine ContinuousOn.div ?_ (by fun_prop) ?_
      · exact (continuousOn_id.neg.mul (Real.continuousOn_log.mono fun u hu => hu.1.ne'))
      · intro u hu; exact ne_of_gt (by nlinarith [hu.1, hu.2])
    · refine DifferentiableOn.div ?_ (by fun_prop) ?_
      · intro u hu
        exact ((differentiableAt_id.neg.mul (Real.differentiableAt_log (interior_subset hu).1.ne'))).differentiableWithinAt
      · intro u hu; exact ne_of_gt (by nlinarith [(interior_subset hu).1, (interior_subset hu).2])
    · intro u hu
      rw [interior_Ioo] at hu
      have hu0 : 0 < u := hu.1
      have hu1 : u < 1 := hu.2
      have hden : 1 - u ^ 2 ≠ 0 := by nlinarith
      have hlog_u : HasDerivAt (fun x => -x * Real.log x) (-Real.log u - 1) u := by
        have h := ((hasDerivAt_id u).neg.mul (Real.hasDerivAt_log hu0.ne'))
        refine h.congr_deriv ?_
        change -1 * Real.log u + -u * u⁻¹ = -Real.log u - 1
        field_simp [hu0.ne']; ring
      have hden_d : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * u) u := by
        have h := ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_pow 2 u)).congr_deriv (by ring :
          0 - 2 * u ^ (2 - 1) = -2 * u)
        exact h
      have hdiv : deriv g u =
          ((-Real.log u - 1) * (1 - u ^ 2) - (-u * Real.log u) * (-2 * u)) / (1 - u ^ 2) ^ 2 :=
        (hlog_u.div hden_d hden).deriv
      change 0 ≤ deriv g u
      rw [hdiv]
      have hnum_eq : (-Real.log u - 1) * (1 - u ^ 2) - (-u * Real.log u) * (-2 * u) =
          (1 + u ^ 2) * Real.log (1 / u) - (1 - u ^ 2) := by
        rw [one_div, Real.log_inv]; ring
      rw [hnum_eq]
      have hinv_ge : 1 ≤ 1 / u := (one_le_div hu0).mpr hu1.le
      have hlog_ge := sub_div_add_le_log hinv_ge
      have hsub_eq : ((1 / u) ^ 2 - 1) / ((1 / u) ^ 2 + 1) = (1 - u ^ 2) / (1 + u ^ 2) := by
        field_simp [hu0.ne']
      rw [hsub_eq, div_le_iff₀ (by positivity)] at hlog_ge
      have hnum_nn : 0 ≤ (1 + u ^ 2) * Real.log (1 / u) - (1 - u ^ 2) := by linarith
      exact div_nonneg hnum_nn (sq_nonneg _)
  exact hg_mono ⟨hβ, hle.trans_lt hβ'⟩ ⟨hβ.trans_le hle, hβ'⟩ hle

/-- Monotonicity of `t₀(w, β)` on `(0, 1)` for every `w : ℕ`. -/
lemma t0_mono (w : ℕ) {β β' : ℝ} (hβ : 0 < β) (hle : β ≤ β') (hβ' : β' < 1) :
    t0 w β ≤ t0 w β' := by
  have hβ1 : β < 1 := hle.trans_lt hβ'
  have hβ'pos : 0 < β' := hβ.trans_le hle
  have hexp : ∀ u : ℝ, 0 < u → u * Real.log (2 * u ^ (-(w : ℝ))) =
      u * Real.log 2 + (w : ℝ) * (-u * Real.log u) := fun u hu => by
    rw [Real.log_mul two_ne_zero (Real.rpow_pos_of_pos hu _).ne',
      Real.log_rpow hu]
    ring
  have ht0_eq : ∀ u : ℝ, 0 < u → u < 1 →
      t0 w u = (2 * π)⁻¹ * (Real.log 2 * (u / (1 - u ^ 2)) +
        (w : ℝ) * ((-u * Real.log u) / (1 - u ^ 2))) := fun u hu hu1 => by
    unfold t0
    rw [hexp u hu]
    have hden : 1 - u ^ 2 ≠ 0 := by nlinarith
    field_simp [Real.pi_pos.ne', hden]
  rw [ht0_eq β hβ hβ1, ht0_eq β' hβ'pos hβ']
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) (by positivity)
  · refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by norm_num))
    exact div_le_div₀ hβ'pos.le hle (by nlinarith) (by nlinarith [pow_le_pow_left₀ hβ.le hle 2])
  · exact mul_le_mul_of_nonneg_left (neg_mul_log_div_one_sub_sq_mono hβ hle hβ')
      (Nat.cast_nonneg w)

lemma t0_nonneg {w : ℕ} {β : ℝ} (hβ : 0 < β) (hβ2 : β ≤ 1 / 2) : 0 ≤ t0 w β := by
  unfold t0
  have hpow : β ^ (w : ℝ) ≤ 1 := Real.rpow_le_one hβ.le (by linarith) (Nat.cast_nonneg w)
  have hbw : 1 ≤ 2 * β ^ (-(w : ℝ)) := by
    rw [Real.rpow_neg hβ.le]
    have hpos : 0 < β ^ (w : ℝ) := Real.rpow_pos_of_pos hβ _
    calc (1 : ℝ) ≤ 2 := by norm_num
      _ ≤ 2 * (β ^ (w : ℝ))⁻¹ := le_mul_of_one_le_right (by norm_num) ((one_le_inv₀ hpos).mpr hpow)
  have hlog : 0 ≤ Real.log (2 * β ^ (-(w : ℝ))) := Real.log_nonneg hbw
  have hden : 0 < 1 - β ^ 2 := by nlinarith
  positivity

lemma t0_le_t0Star {w : ℕ} {β β₀ : ℝ} (hβ : 0 < β) (hle : β ≤ β₀) (hβ₀ : β₀ < 1) :
    t0 w β ≤ t0Star w β₀ := by
  unfold t0Star
  refine le_csSup ⟨t0 w β₀, ?_⟩ ⟨β, ⟨hβ, hle⟩, rfl⟩
  rintro y ⟨u, hu, rfl⟩
  exact t0_mono w hu.1 hu.2 hβ₀

lemma t0Star_eq_t0 {w : ℕ} {β₀ : ℝ} (hβ₀ : 0 < β₀) (hβ₀1 : β₀ < 1) :
    t0Star w β₀ = t0 w β₀ :=
  le_antisymm (csSup_le ⟨t0 w β₀, β₀, ⟨hβ₀, le_rfl⟩, rfl⟩ fun _ ⟨_, hu, hy⟩ =>
    hy ▸ t0_mono w hu.1 hu.2 hβ₀1) (t0_le_t0Star hβ₀ le_rfl hβ₀1)

/-- `t₀^*(w, β₀) → 0` as `β₀ ↓ 0`: every `T₀ > 0` admits `β₀ ∈ (0, 1/2]` with `t₀^*(w, β₀) ≤ T₀`. -/
lemma exists_beta0 (w : ℕ) {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ β₀ : ℝ, 0 < β₀ ∧ β₀ ≤ 1 / 2 ∧ t0Star w β₀ ≤ T₀ := by
  let η : ℝ := 3 * π / 2 * T₀
  have hηpos : 0 < η := by positivity
  let φ : ℝ → ℝ := fun β => β * Real.log 2 - (w : ℝ) * (β * Real.log β)
  have hφc : Continuous φ := (continuous_id.mul continuous_const).sub
    (continuous_const.mul Real.continuous_mul_log)
  have hφ0 : φ 0 = 0 := by simp [φ]
  have hlim : Tendsto φ (𝓝[>] 0) (𝓝 0) := by
    have := hφc.continuousAt (x := 0)
    rw [ContinuousAt, hφ0] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ev1 : ∀ᶠ β in 𝓝[>] (0 : ℝ), φ β < η := hlim.eventually (gt_mem_nhds hηpos)
  have ev2 : ∀ᶠ β in 𝓝[>] (0 : ℝ), β ∈ Ioo (0 : ℝ) (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨β, hβ1, hβ2⟩ := (ev1.and ev2).exists
  refine ⟨β, hβ2.1, hβ2.2.le, ?_⟩
  rw [t0Star_eq_t0 hβ2.1 (by linarith [hβ2.2])]
  have hφeq : φ β = β * Real.log (2 * β ^ (-(w : ℝ))) := by
    simp only [φ]
    rw [Real.log_mul two_ne_zero (Real.rpow_pos_of_pos hβ2.1 _).ne', Real.log_rpow hβ2.1]
    ring
  have hden : 3 / 4 ≤ 1 - β ^ 2 := by nlinarith [hβ2.1, hβ2.2]
  unfold t0
  rw [div_le_iff₀ (by have := Real.pi_pos; nlinarith)]
  have h1 : β * Real.log (2 * β ^ (-(w : ℝ))) < η := by rw [← hφeq]; exact hβ1
  have hden_le : η ≤ T₀ * (2 * π * (1 - β ^ 2)) := by
    calc η = T₀ * (2 * π * (3 / 4)) := by dsimp [η]; ring
      _ ≤ T₀ * (2 * π * (1 - β ^ 2)) := by gcongr
  linarith

/-- `2 Ξ_β(t) ≥ e^{-2πβt}` for `t ≥ t₀(w, β)`, `0 < β < 1`, at every weight `w : ℕ`. -/
lemma two_thermalDiff_ge {w : ℕ} {β t : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (ht : t0 w β ≤ t) :
    Real.exp (-2 * π * β * t) ≤ 2 * thermalDiff w β t := by
  unfold thermalDiff
  have hbw_pos : 0 < β ^ (-(w : ℝ)) := Real.rpow_pos_of_pos hβ _
  have hbw_inv : 0 < β ^ (w : ℝ) := Real.rpow_pos_of_pos hβ _
  have hpos : 0 < 1 / β - β := by rw [sub_pos, lt_div_iff₀ hβ]; nlinarith
  have hk : Real.log (2 * β ^ (-(w : ℝ))) ≤ 2 * π * t * (1 / β - β) := by
    have hmul : t0 w β * (2 * π * (1 / β - β)) = Real.log (2 * β ^ (-(w : ℝ))) := by
      unfold t0
      have h1 : 1 / β - β = (1 - β ^ 2) / β := by field_simp
      have hden : 1 - β ^ 2 ≠ 0 := by nlinarith
      rw [h1]
      field_simp [hβ.ne', hden, Real.pi_pos.ne']
    rw [← hmul, show 2 * π * t * (1 / β - β) = t * (2 * π * (1 / β - β)) by ring]
    exact mul_le_mul_of_nonneg_right ht (show 0 ≤ 2 * π * (1 / β - β) by positivity)
  have hle : Real.exp (-(2 * π * t * (1 / β - β))) ≤ (1 / 2) * β ^ (w : ℝ) := by
    calc Real.exp (-(2 * π * t * (1 / β - β)))
        ≤ Real.exp (-Real.log (2 * β ^ (-(w : ℝ)))) := Real.exp_le_exp.mpr (by linarith)
      _ = (2 * β ^ (-(w : ℝ)))⁻¹ := by rw [Real.exp_neg, Real.exp_log (by positivity)]
      _ = (1 / 2) * β ^ (w : ℝ) := by
          rw [Real.rpow_neg hβ.le, mul_inv, inv_inv]; ring
  have hexp : Real.exp (-2 * π * t / β) ≤ (1 / 2) * β ^ (w : ℝ) * Real.exp (-2 * π * β * t) := by
    have h1 : -2 * π * t / β = -2 * π * β * t + -(2 * π * t * (1 / β - β)) := by
      field_simp [hβ.ne']; ring
    rw [h1, Real.exp_add]
    calc Real.exp (-2 * π * β * t) * Real.exp (-(2 * π * t * (1 / β - β)))
        ≤ Real.exp (-2 * π * β * t) * ((1 / 2) * β ^ (w : ℝ)) :=
          mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le
      _ = (1 / 2) * β ^ (w : ℝ) * Real.exp (-2 * π * β * t) := mul_comm _ _
  have hbw_cancel : β ^ (-(w : ℝ)) * β ^ (w : ℝ) = 1 := by
    rw [Real.rpow_neg hβ.le, inv_mul_cancel₀ hbw_inv.ne']
  have hterm : β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) ≤ (1 / 2) * Real.exp (-2 * π * β * t) := by
    calc β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β)
        ≤ β ^ (-(w : ℝ)) * ((1 / 2) * β ^ (w : ℝ) * Real.exp (-2 * π * β * t)) :=
          mul_le_mul_of_nonneg_left hexp hbw_pos.le
      _ = (1 / 2) * (β ^ (-(w : ℝ)) * β ^ (w : ℝ)) * Real.exp (-2 * π * β * t) := by ring
      _ = (1 / 2) * Real.exp (-2 * π * β * t) := by rw [hbw_cancel, mul_one]
  linarith

/-! ### Section 2: General-`w` integrability and Fubini bounds for `h` -/

/-- For `w ≥ 1`, `c > 0`, and `β > 0`: `β^{-w} e^{-c/β} ≤ (w / c)^w`. -/
lemma rpow_neg_mul_exp_neg_div_le {w : ℕ} (hw : 1 ≤ w) {c β : ℝ} (hc : 0 < c) (hβ : 0 < β) :
    β ^ (-(w : ℝ)) * Real.exp (-c / β) ≤ ((w : ℝ) / c) ^ w := by
  have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
  have hy_nn : 0 ≤ c / ((w : ℝ) * β) := by positivity
  have hexp1 : c / ((w : ℝ) * β) ≤ Real.exp (c / ((w : ℝ) * β)) := by
    linarith [Real.add_one_le_exp (c / ((w : ℝ) * β))]
  have hexp_w : (c / ((w : ℝ) * β)) ^ w ≤ Real.exp (c / β) := by
    calc (c / ((w : ℝ) * β)) ^ w ≤ (Real.exp (c / ((w : ℝ) * β))) ^ w :=
          pow_le_pow_left₀ hy_nn hexp1 w
      _ = Real.exp ((w : ℝ) * (c / ((w : ℝ) * β))) := by rw [← Real.exp_nat_mul]
      _ = Real.exp (c / β) := by congr 1; field_simp [hw_pos.ne']
  have h1 : β ^ (-(w : ℝ)) = (β ^ w)⁻¹ := by
    rw [Real.rpow_neg hβ.le, Real.rpow_natCast]
  have h2 : Real.exp (-c / β) = (Real.exp (c / β))⁻¹ := by
    rw [← Real.exp_neg, neg_div]
  rw [h1, h2]
  have he_pos : 0 < Real.exp (c / β) := Real.exp_pos _
  calc (β ^ w)⁻¹ * (Real.exp (c / β))⁻¹
      ≤ (β ^ w)⁻¹ * ((c / ((w : ℝ) * β)) ^ w)⁻¹ := by
        gcongr
    _ = ((w : ℝ) / c) ^ w := by
        rw [div_pow, mul_pow, inv_div, div_pow]
        field_simp [hβ.ne', hc.ne', hw_pos.ne']

lemma rpow_neg_mul_thetaW_le {w : ℕ} (hw : 1 ≤ w) {a : ℝ} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    β ^ (-(w : ℝ)) * thetaW a β ≤ Real.exp (8 * π * a) * ((w : ℝ) / (4 * π * a)) ^ w := by
  rw [thetaW_eq]
  have h1 := rpow_neg_mul_exp_neg_div_le hw (by positivity : 0 < 4 * π * a) hβ
  calc β ^ (-(w : ℝ)) * (Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β))
      = Real.exp (8 * π * a) * (β ^ (-(w : ℝ)) * Real.exp (-(4 * π * a) / β)) := by ring
    _ ≤ Real.exp (8 * π * a) * ((w : ℝ) / (4 * π * a)) ^ w := by
        gcongr

lemma rpow_neg_mul_exp_thetaW_le {w : ℕ} (hw : 1 ≤ w) {a : ℝ} (ha : 0 < a) {β : ℝ} (hβ : 0 < β) :
    β ^ (-(w : ℝ)) * Real.exp (2 * π * a / β) * thetaW a β ≤
      Real.exp (8 * π * a) * ((w : ℝ) / (2 * π * a)) ^ w := by
  rw [thetaW_eq]
  have h1 := rpow_neg_mul_exp_neg_div_le hw (by positivity : 0 < 2 * π * a) hβ
  have h2 : Real.exp (2 * π * a / β) * Real.exp (-(4 * π * a) / β) = Real.exp (-(2 * π * a) / β) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  calc β ^ (-(w : ℝ)) * Real.exp (2 * π * a / β) * (Real.exp (8 * π * a) * Real.exp (-(4 * π * a) / β))
      = Real.exp (8 * π * a) * (β ^ (-(w : ℝ)) * (Real.exp (2 * π * a / β) * Real.exp (-(4 * π * a) / β))) := by
        ring
    _ = Real.exp (8 * π * a) * (β ^ (-(w : ℝ)) * Real.exp (-(2 * π * a) / β)) := by rw [h2]
    _ ≤ Real.exp (8 * π * a) * ((w : ℝ) / (2 * π * a)) ^ w := by
        gcongr

lemma abs_thermalDiff_le {w : ℕ} {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    |thermalDiff w β t| ≤ Real.exp (-2 * π * β * t) + β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) := by
  unfold thermalDiff
  have h1 := (Real.exp_pos (-2 * π * β * t)).le
  have h2 : 0 ≤ β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) :=
    mul_nonneg (Real.rpow_nonneg hβ.le _) (Real.exp_pos _).le
  rw [abs_le]
  constructor <;> linarith

private lemma integrableOn_pow_mul_exp_Ioi (n : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(r * t))) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ =>
      ((n.factorial : ℝ) * (2 / r) ^ n) * Real.exp (-(r / 2) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul _
  refine hdom.mono' (by fun_prop : Continuous fun t : ℝ =>
      t ^ n * Real.exp (-(r * t))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht0 _) (Real.exp_pos _).le)]
  have hpow_le : (r / 2 * t) ^ n / (n.factorial : ℝ) ≤ Real.exp (r / 2 * t) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    exact (Real.summable_pow_div_factorial (r / 2 * t)).le_tsum n
      fun k _ => div_nonneg (pow_nonneg (by positivity) k) (by positivity)
  have h1 : t ^ n ≤ (n.factorial : ℝ) * (2 / r) ^ n * Real.exp (r / 2 * t) := by
    have hmul := mul_le_mul_of_nonneg_left hpow_le
      (show 0 ≤ (n.factorial : ℝ) * (2 / r) ^ n by positivity)
    have hcancel : (2 / r) ^ n * (r / 2) ^ n = 1 := by
      rw [← mul_pow, show (2 / r) * (r / 2) = 1 by field_simp [hr.ne'], one_pow]
    calc t ^ n = t ^ n * 1 := (mul_one _).symm
      _ = t ^ n * ((2 / r) ^ n * (r / 2) ^ n) := by rw [hcancel]
      _ = (n.factorial : ℝ) * (2 / r) ^ n * ((r / 2 * t) ^ n / (n.factorial : ℝ)) := by
          rw [mul_pow]; field_simp
      _ ≤ (n.factorial : ℝ) * (2 / r) ^ n * Real.exp (r / 2 * t) := hmul
  calc t ^ n * Real.exp (-(r * t))
      ≤ ((n.factorial : ℝ) * (2 / r) ^ n * Real.exp (r / 2 * t)) * Real.exp (-(r * t)) := by
        gcongr
    _ = ((n.factorial : ℝ) * (2 / r) ^ n) * Real.exp (-(r / 2) * t) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

private lemma integral_pow_mul_exp_Ioi {w : ℕ} (hw : 1 ≤ w) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ (w - 1) * Real.exp (-(r * t)) =
      ((w - 1).factorial : ℝ) * r ^ (-(w : ℝ)) := by
  have hw_pos : (0 : ℝ) < (w : ℝ) := by exact_mod_cast (by omega : 0 < w)
  have hw_sub : w - 1 + 1 = w := Nat.sub_add_cancel hw
  have hgam : Real.Gamma (w : ℝ) = ((w - 1).factorial : ℝ) := by
    rw [← hw_sub]
    simp only [Nat.cast_add, Nat.cast_one, Real.Gamma_nat_eq_factorial, add_tsub_cancel_right]
  have hpow_eq : ∀ t ∈ Ioi (0 : ℝ),
      t ^ ((w : ℝ) - 1) * Real.exp (-(r * t)) = t ^ (w - 1) * Real.exp (-(r * t)) := by
    intro t _
    rw [← Real.rpow_natCast t (w - 1)]
    congr 2
    rw [← hw_sub]; push_cast; ring
  rw [← setIntegral_congr_fun measurableSet_Ioi hpow_eq,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hw_pos hr, hgam, one_div, Real.inv_rpow hr.le,
    ← Real.rpow_neg hr.le, mul_comm]

/-- Weight-`w` radial `L¹` bound for `Ξ_β`: `∫₀^∞ t^{w-1} |Ξ_β(t)| dt ≤ (w-1)! (2π)^{-w} (β^{-w} + 1)`
(`dual_spectrum.tex`, Lemma M(a) proof). -/
lemma integral_pow_mul_abs_thermalDiff_le {w : ℕ} (hw : 1 ≤ w) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => t ^ (w - 1) * |thermalDiff w β t|) (Ioi 0) ∧
      ((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
          ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t| ≤
        β ^ (-(w : ℝ)) + 1 := by
  have hr1 : 0 < 2 * π * β := by positivity
  have hr2 : 0 < 2 * π / β := by positivity
  have i1 := integrableOn_pow_mul_exp_Ioi (w - 1) hr1
  have i2 := integrableOn_pow_mul_exp_Ioi (w - 1) hr2
  have v1 := integral_pow_mul_exp_Ioi hw hr1
  have v2 := integral_pow_mul_exp_Ioi hw hr2
  have hsum : IntegrableOn (fun t : ℝ => t ^ (w - 1) * Real.exp (-(2 * π * β * t)) +
      β ^ (-(w : ℝ)) * (t ^ (w - 1) * Real.exp (-(2 * π / β * t)))) (Ioi 0) :=
    i1.add (i2.const_mul _)
  have hmeas : Measurable fun t : ℝ => t ^ (w - 1) * |thermalDiff w β t| := by
    unfold thermalDiff; fun_prop
  have hle : ∀ t ∈ Ioi (0 : ℝ), t ^ (w - 1) * |thermalDiff w β t| ≤
      t ^ (w - 1) * Real.exp (-(2 * π * β * t)) +
      β ^ (-(w : ℝ)) * (t ^ (w - 1) * Real.exp (-(2 * π / β * t))) := by
    intro t ht
    have ht0 : 0 ≤ t ^ (w - 1) := pow_nonneg (mem_Ioi.mp ht).le _
    have htri := abs_thermalDiff_le (w := w) hβ t
    have e1 : -2 * π * β * t = -(2 * π * β * t) := by ring
    have e2 : -2 * π * t / β = -(2 * π / β * t) := by ring
    rw [e1, e2] at htri
    nlinarith
  have hint : IntegrableOn (fun t => t ^ (w - 1) * |thermalDiff w β t|) (Ioi 0) := by
    refine hsum.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t ^ (w - 1) := pow_nonneg (mem_Ioi.mp ht).le _
    rw [Real.norm_of_nonneg (mul_nonneg ht0 (abs_nonneg _))]
    exact hle t ht
  refine ⟨hint, ?_⟩
  have hmono : ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t| ≤
      ((w - 1).factorial : ℝ) * (2 * π) ^ (-(w : ℝ)) * (β ^ (-(w : ℝ)) + 1) := by
    calc ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t|
        ≤ ∫ t in Ioi 0, (t ^ (w - 1) * Real.exp (-(2 * π * β * t)) +
            β ^ (-(w : ℝ)) * (t ^ (w - 1) * Real.exp (-(2 * π / β * t)))) :=
          setIntegral_mono_on hint hsum measurableSet_Ioi hle
      _ = ((w - 1).factorial : ℝ) * (2 * π * β) ^ (-(w : ℝ)) +
            β ^ (-(w : ℝ)) * (((w - 1).factorial : ℝ) * (2 * π / β) ^ (-(w : ℝ))) := by
          rw [integral_add i1 (i2.const_mul _), v1, integral_const_mul, v2]
      _ = ((w - 1).factorial : ℝ) * (2 * π) ^ (-(w : ℝ)) * (β ^ (-(w : ℝ)) + 1) := by
          rw [Real.mul_rpow (by positivity) hβ.le,
            Real.div_rpow (by positivity) hβ.le,
            Real.rpow_neg (by positivity), Real.rpow_neg hβ.le]
          have hbw_ne : (β ^ (w : ℝ))⁻¹ ≠ 0 := inv_ne_zero (Real.rpow_pos_of_pos hβ _).ne'
          have hw_cancel : (β ^ (w : ℝ))⁻¹ * (((2 * π) ^ (w : ℝ))⁻¹ / (β ^ (w : ℝ))⁻¹) =
              ((2 * π) ^ (w : ℝ))⁻¹ := by
            field_simp [hbw_ne]
          calc ((w - 1).factorial : ℝ) * (((2 * π) ^ (w : ℝ))⁻¹ * (β ^ (w : ℝ))⁻¹) +
                (β ^ (w : ℝ))⁻¹ * (((w - 1).factorial : ℝ) * (((2 * π) ^ (w : ℝ))⁻¹ / (β ^ (w : ℝ))⁻¹))
              = ((w - 1).factorial : ℝ) * ((2 * π) ^ (w : ℝ))⁻¹ * (β ^ (w : ℝ))⁻¹ +
                  ((w - 1).factorial : ℝ) * ((β ^ (w : ℝ))⁻¹ * (((2 * π) ^ (w : ℝ))⁻¹ / (β ^ (w : ℝ))⁻¹)) := by
                ring
            _ = ((w - 1).factorial : ℝ) * ((2 * π) ^ (w : ℝ))⁻¹ * (β ^ (w : ℝ))⁻¹ +
                  ((w - 1).factorial : ℝ) * ((2 * π) ^ (w : ℝ))⁻¹ := by rw [hw_cancel]
            _ = ((w - 1).factorial : ℝ) * ((2 * π) ^ (w : ℝ))⁻¹ * ((β ^ (w : ℝ))⁻¹ + 1) := by ring
  have hpref : ((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
      (((w - 1).factorial : ℝ) * (2 * π) ^ (-(w : ℝ))) = 1 := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    have h1 : ((w - 1).factorial : ℝ) ≠ 0 := by positivity
    have h2 : (2 * π) ^ w ≠ 0 := by positivity
    field_simp
  calc ((2 * π) ^ w / ((w - 1).factorial : ℝ)) * ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t|
      ≤ ((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
          (((w - 1).factorial : ℝ) * (2 * π) ^ (-(w : ℝ)) * (β ^ (-(w : ℝ)) + 1)) := by
        gcongr
    _ = (((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
          (((w - 1).factorial : ℝ) * (2 * π) ^ (-(w : ℝ)))) * (β ^ (-(w : ℝ)) + 1) := by ring
    _ = β ^ (-(w : ℝ)) + 1 := by rw [hpref, one_mul]

/-- Cardy-weighted `L¹` bound for `Ξ_β` at general `(w, Q)` and `a ≥ S`
(`dual_spectrum.tex`, Lemma M(a) proof). -/
lemma integral_abs_thermalDiff_V_le (prob : FixedWeightProblem) {a : ℝ}
    (ha : prob.totalShift ≤ a) {β : ℝ} (hβ : 0 < β) :
    IntegrableOn (fun t => |thermalDiff prob.w β t| * prob.cardyV a t) (Ioi 0) ∧
      ∫ t in Ioi 0, |thermalDiff prob.w β t| * prob.cardyV a t ≤
        (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β)) / (2 * π) := by
  have hint := (thermalDiff_mem_TestClass prob ha hβ).int_cardy
  refine ⟨by simpa using hint, ?_⟩
  obtain ⟨i1, v1⟩ := prob.cardyV_laplace a hβ
  obtain ⟨i2, v2⟩ := prob.cardyV_laplace a (inv_pos.mpr hβ)
  have hsum : IntegrableOn (fun t => prob.cardyV a t * Real.exp (-2 * π * β * t) +
      β ^ (-(prob.w : ℝ)) * (prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))) (Ioi 0) :=
    i1.add (i2.const_mul _)
  have hle : ∀ t ∈ Ioi (0 : ℝ), |thermalDiff prob.w β t| * prob.cardyV a t ≤
      prob.cardyV a t * Real.exp (-2 * π * β * t) +
      β ^ (-(prob.w : ℝ)) * (prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) := by
    intro t ht
    have hV := prob.cardyV_nonneg ha (le_of_lt ht)
    have htri := abs_thermalDiff_le (w := prob.w) hβ t
    rw [show -2 * π * t / β = -2 * π * β⁻¹ * t by ring] at htri
    nlinarith
  have hint' : IntegrableOn (fun t => |thermalDiff prob.w β t| * prob.cardyV a t) (Ioi 0) := by
    simpa using hint
  calc ∫ t in Ioi 0, |thermalDiff prob.w β t| * prob.cardyV a t
      ≤ ∫ t in Ioi 0, (prob.cardyV a t * Real.exp (-2 * π * β * t) +
          β ^ (-(prob.w : ℝ)) * (prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))) :=
        setIntegral_mono_on hint' hsum measurableSet_Ioi hle
    _ = (∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β * t)) +
          β ^ (-(prob.w : ℝ)) * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t) := by
        rw [integral_add i1 (i2.const_mul _), integral_const_mul]
    _ ≤ (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β)) / (2 * π) := by
        have hq1 : prob.nullPoly (Real.exp (-2 * π / β)) ≤ 1 :=
          prob.nullPoly_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr
            (div_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hβ.le))
        have hq2 : prob.nullPoly (Real.exp (-2 * π / β⁻¹)) ≤ 1 :=
          prob.nullPoly_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr
            (div_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) (inv_pos.mpr hβ).le))
        have p1 : 2 * π * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β * t) ≤
            β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) := by
          rw [v1]
          calc β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) *
                prob.nullPoly (Real.exp (-2 * π / β))
              ≤ β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * 1 :=
                mul_le_mul_of_nonneg_left hq1 (by positivity)
            _ = β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) := mul_one _
        have p2 : 2 * π * ∫ t in Ioi 0, prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t) ≤
            β ^ (prob.w : ℝ) * Real.exp (2 * π * a * β) := by
          rw [v2, Real.inv_rpow hβ.le, Real.rpow_neg hβ.le, inv_inv, div_inv_eq_mul]
          calc β ^ (prob.w : ℝ) * Real.exp (2 * π * a * β) *
                prob.nullPoly (Real.exp (-2 * π / β⁻¹))
              ≤ β ^ (prob.w : ℝ) * Real.exp (2 * π * a * β) * 1 :=
                mul_le_mul_of_nonneg_left hq2 (by positivity)
            _ = β ^ (prob.w : ℝ) * Real.exp (2 * π * a * β) := mul_one _
        have hbw_cancel : β ^ (-(prob.w : ℝ)) * β ^ (prob.w : ℝ) = 1 := by
          rw [Real.rpow_neg hβ.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hβ _).ne']
        have p2' : β ^ (-(prob.w : ℝ)) * (2 * π * ∫ t in Ioi 0,
              prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t)) ≤ Real.exp (2 * π * a * β) := by
          calc β ^ (-(prob.w : ℝ)) * (2 * π * ∫ t in Ioi 0,
                prob.cardyV a t * Real.exp (-2 * π * β⁻¹ * t))
              ≤ β ^ (-(prob.w : ℝ)) * (β ^ (prob.w : ℝ) * Real.exp (2 * π * a * β)) :=
                mul_le_mul_of_nonneg_left p2 (Real.rpow_nonneg hβ.le _)
            _ = (β ^ (-(prob.w : ℝ)) * β ^ (prob.w : ℝ)) * Real.exp (2 * π * a * β) := by ring
            _ = Real.exp (2 * π * a * β) := by rw [hbw_cancel, one_mul]
        have hπ : 0 < 2 * π := by positivity
        rw [le_div_iff₀ hπ]
        nlinarith

lemma integrable_prod_family_w {w : ℕ} {a β₀ B : ℝ} (φ : ℝ → ℝ) (hφm : Measurable φ)
    (hφ0 : ∀ t, 0 < t → 0 ≤ φ t)
    (hB : ∀ β ∈ Ioc 0 β₀, IntegrableOn (fun t => |thermalDiff w β t| * φ t) (Ioi 0) ∧
        (∫ t in Ioi 0, |thermalDiff w β t| * φ t) * thetaW a β ≤ B) :
    Integrable (fun p : ℝ × ℝ => thermalDiff w p.2 p.1 * φ p.1 * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  have hFm : Measurable (fun p : ℝ × ℝ => thermalDiff w p.2 p.1 * φ p.1 * thetaW a p.2) := by
    have := measurable_thetaW a
    unfold thermalDiff
    fun_prop
  rw [integrable_prod_iff' hFm.aestronglyMeasurable]
  have hnorm : ∀ β ∈ Ioc 0 β₀,
      ∫ t, ‖thermalDiff w β t * φ t * thetaW a β‖ ∂(volume.restrict (Ioi 0)) =
      (∫ t in Ioi 0, |thermalDiff w β t| * φ t) * thetaW a β := by
    intro β _
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hφ0 t ht), abs_of_pos (thetaW_pos a β)]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have hm : Measurable fun t => thermalDiff w β t * φ t * thetaW a β := by
      unfold thermalDiff; fun_prop
    refine ((hB β hβ).1.mul_const (thetaW a β)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (hφ0 t ht), abs_of_pos (thetaW_pos a β)]
  · have hmeas : AEStronglyMeasurable
        (fun β => ∫ t, ‖thermalDiff w β t * φ t * thetaW a β‖ ∂(volume.restrict (Ioi 0)))
        (volume.restrict (Ioc 0 β₀)) := by
      have h := (hFm.norm.aestronglyMeasurable
        (μ := (volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀)))).prod_swap
      exact h.integral_prod_right'
    refine Integrable.of_bound (C := B) hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [hnorm β hβ, Real.norm_of_nonneg]
    · exact (hB β hβ).2
    · rw [← hnorm β hβ]; exact integral_nonneg fun _ => norm_nonneg _

lemma integrable_prod_pow {w : ℕ} (hw : 1 ≤ w) {a β₀ : ℝ} (ha : 0 < a) :
    Integrable (fun p : ℝ × ℝ =>
        thermalDiff w p.2 p.1 * (p.1 ^ (w - 1)) * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  let C_bnd : ℝ := ((w - 1).factorial : ℝ) / (2 * π) ^ w *
    (Real.exp (8 * π * a) * ((w : ℝ) / (4 * π * a)) ^ w + Real.exp (8 * π * a))
  refine integrable_prod_family_w (B := C_bnd) (fun t : ℝ => t ^ (w - 1))
    (by fun_prop) (fun t ht => pow_nonneg ht.le _) fun β hβ => ?_
  obtain ⟨hi, hv⟩ := integral_pow_mul_abs_thermalDiff_le hw hβ.1
  have h1 := rpow_neg_mul_thetaW_le hw ha hβ.1
  have h2 := thetaW_le ha.le hβ.1
  have hint' : IntegrableOn (fun t => |thermalDiff w β t| * t ^ (w - 1)) (Ioi 0) :=
    hi.congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  refine ⟨hint', ?_⟩
  have hpref_pos : (0 : ℝ) < (2 * π) ^ w / ((w - 1).factorial : ℝ) := by positivity
  have hiv : ∫ t in Ioi 0, |thermalDiff w β t| * t ^ (w - 1) ≤
      ((w - 1).factorial : ℝ) / (2 * π) ^ w * (β ^ (-(w : ℝ)) + 1) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _]
    have hmul := mul_le_mul_of_nonneg_left hv (by positivity :
      0 ≤ ((w - 1).factorial : ℝ) / (2 * π) ^ w)
    have hcan : (((w - 1).factorial : ℝ) / (2 * π) ^ w) *
        ((2 * π) ^ w / ((w - 1).factorial : ℝ)) = 1 := by
      have hfac : ((w - 1).factorial : ℝ) ≠ 0 := by positivity
      have hpiw : (2 * π) ^ w ≠ 0 := by positivity
      field_simp
    rwa [← mul_assoc, hcan, one_mul] at hmul
  calc (∫ t in Ioi 0, |thermalDiff w β t| * t ^ (w - 1)) * thetaW a β
      ≤ (((w - 1).factorial : ℝ) / (2 * π) ^ w * (β ^ (-(w : ℝ)) + 1)) * thetaW a β :=
        mul_le_mul_of_nonneg_right hiv (thetaW_pos a β).le
    _ = ((w - 1).factorial : ℝ) / (2 * π) ^ w *
          (β ^ (-(w : ℝ)) * thetaW a β + thetaW a β) := by ring
    _ ≤ C_bnd := by dsimp [C_bnd]; gcongr

lemma integrable_prod_V (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) :
    Integrable (fun p : ℝ × ℝ =>
        thermalDiff prob.w p.2 p.1 * prob.cardyV a p.1 * thetaW a p.2)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioc 0 β₀))) := by
  let B : ℝ := (Real.exp (8 * π * a) * ((prob.w : ℝ) / (2 * π * a)) ^ prob.w +
    Real.exp (2 * π * a * max β₀ 0) * Real.exp (8 * π * a)) / (2 * π)
  refine integrable_prod_family_w (B := B) (prob.cardyV a)
    (continuous_cardyV prob a).measurable
    (fun t ht => prob.cardyV_nonneg ha ht.le) fun β hβ => ?_
  obtain ⟨hi, hv⟩ := integral_abs_thermalDiff_V_le prob ha hβ.1
  refine ⟨hi, ?_⟩
  have h1 := rpow_neg_mul_exp_thetaW_le prob.hw ha0 hβ.1
  have h2 := thetaW_le ha0.le hβ.1
  have h3 : Real.exp (2 * π * a * β) ≤ Real.exp (2 * π * a * max β₀ 0) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hβ.2.trans (le_max_left _ _)) (by positivity))
  calc (∫ t in Ioi 0, |thermalDiff prob.w β t| * prob.cardyV a t) * thetaW a β
      ≤ ((β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) +
          Real.exp (2 * π * a * β)) / (2 * π)) * thetaW a β :=
        mul_le_mul_of_nonneg_right hv (thetaW_pos a β).le
    _ = (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * thetaW a β +
          Real.exp (2 * π * a * β) * thetaW a β) / (2 * π) := by ring
    _ ≤ B := by
        dsimp [B]
        exact div_le_div_of_nonneg_right (add_le_add h1
          (mul_le_mul h3 h2 (thetaW_pos a β).le (Real.exp_pos _).le)) (by positivity)

/-! ### Section 3: The dual majorant `h`, `C₀`, and Lemma M (`ds:M`) -/

/-- The dual majorant `h = 2 ∫₀^{β₀} Ξ_β^{(w)} ϑ(dβ)` at weight `w`. -/
noncomputable def hMaj (w : ℕ) (a β₀ t : ℝ) : ℝ :=
  2 * ∫ β in Ioc 0 β₀, thermalDiff w β t * thetaW a β

lemma hMaj_one (a β₀ t : ℝ) : hMaj 1 a β₀ t = Duality.hMaj a β₀ t := rfl

lemma continuousOn_hMaj {w : ℕ} (hw : 1 ≤ w) {a β₀ : ℝ} (ha : 0 < a) :
    ContinuousOn (hMaj w a β₀) (Ici 0) := by
  unfold hMaj
  refine continuousOn_const.mul ?_
  refine continuousOn_of_dominated
    (bound := fun β => (1 + β ^ (-(w : ℝ))) * thetaW a β) ?_ ?_ ?_ ?_
  · intro t _
    exact (by have := measurable_thetaW a; unfold thermalDiff; fun_prop :
      Measurable fun β : ℝ => thermalDiff w β t * thetaW a β).aestronglyMeasurable
  · intro t ht
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β)]
    refine mul_le_mul_of_nonneg_right ?_ (thetaW_pos a β).le
    refine (abs_thermalDiff_le (w := w) hβ.1 t).trans ?_
    have e1 : Real.exp (-2 * π * β * t) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ β * t := mul_nonneg hβ.1.le (mem_Ici.mp ht)
      nlinarith [Real.pi_pos])
    have e2 : Real.exp (-2 * π * t / β) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ t / β := div_nonneg (mem_Ici.mp ht) hβ.1.le
      rw [show -2 * π * t / β = -(2 * π) * (t / β) by ring]
      nlinarith [Real.pi_pos])
    have hbw : β ^ (-(w : ℝ)) * Real.exp (-2 * π * t / β) ≤ β ^ (-(w : ℝ)) :=
      mul_le_of_le_one_right (Real.rpow_nonneg hβ.1.le _) e2
    linarith
  · refine Integrable.of_bound (C := Real.exp (8 * π * a) +
        Real.exp (8 * π * a) * ((w : ℝ) / (4 * π * a)) ^ w) ?_ ?_
    · exact (by have := measurable_thetaW a; fun_prop :
        Measurable fun β : ℝ => (1 + β ^ (-(w : ℝ))) * thetaW a β).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      have h1 := rpow_neg_mul_thetaW_le hw ha hβ.1
      have h2 := thetaW_le ha.le hβ.1
      rw [Real.norm_of_nonneg (mul_nonneg (by have := Real.rpow_pos_of_pos hβ.1 (-(w : ℝ)); linarith)
        (thetaW_pos a β).le)]
      nlinarith
  · refine Eventually.of_forall fun β => ?_
    refine ContinuousOn.mul ?_ continuousOn_const
    unfold thermalDiff; fun_prop

lemma integrableOn_pow_hMaj {w : ℕ} (hw : 1 ≤ w) {a β₀ : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t => t ^ (w - 1) * hMaj w a β₀ t) (Ioi 0) := by
  unfold hMaj
  have hprod := (integrable_prod_pow hw (β₀ := β₀) ha).integral_prod_left.const_mul 2
  have heq : (fun t => t ^ (w - 1) * (2 * ∫ β in Ioc 0 β₀, thermalDiff w β t * thetaW a β)) =
      fun t => 2 * ∫ β in Ioc 0 β₀, thermalDiff w β t * t ^ (w - 1) * thetaW a β := by
    ext t
    rw [mul_left_comm, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    ring
  rw [heq]
  exact hprod

lemma measurable_hMaj (w : ℕ) (a β₀ : ℝ) : Measurable (hMaj w a β₀) := by
  unfold hMaj
  have h1 : Measurable (Function.uncurry fun (t β : ℝ) => thermalDiff w β t * thetaW a β) := by
    have := measurable_thetaW a
    unfold thermalDiff; fun_prop
  exact (h1.stronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Ioc 0 β₀))).measurable.const_mul 2

lemma integrableOn_abs_hMaj_V (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) :
    IntegrableOn (fun t => |hMaj prob.w a β₀ t| * prob.cardyV a t) (Ioi 0) := by
  have hP := integrable_prod_V prob (β₀ := β₀) ha ha0
  have hI := (hP.integral_norm_prod_left).const_mul 2
  refine hI.mono' ?_ ?_
  · exact ((continuous_abs.measurable.comp (measurable_hMaj prob.w a β₀)).mul
      (continuous_cardyV prob a).measurable).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hV := prob.cardyV_nonneg ha (le_of_lt ht)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hV)]
    unfold hMaj
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc |∫ β in Ioc 0 β₀, thermalDiff prob.w β t * thetaW a β| * prob.cardyV a t
        ≤ (∫ β in Ioc 0 β₀, ‖thermalDiff prob.w β t * thetaW a β‖) * prob.cardyV a t := by
          refine mul_le_mul_of_nonneg_right ?_ hV
          have := norm_integral_le_integral_norm (μ := volume.restrict (Ioc 0 β₀))
            (fun β => thermalDiff prob.w β t * thetaW a β)
          rwa [Real.norm_eq_abs] at this
      _ = ∫ β in Ioc 0 β₀, ‖thermalDiff prob.w β t * prob.cardyV a t * thetaW a β‖ := by
          rw [← integral_mul_const]
          refine integral_congr_ae (Eventually.of_forall fun β => ?_)
          simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β), abs_of_nonneg hV]
          ring

open scoped FourierTransform in
lemma fourier_odd_hMaj (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) :
    𝓕 (radialLift prob.w (hMaj prob.w a β₀)) = -(radialLift prob.w (hMaj prob.w a β₀)) := by
  let w := prob.w
  let F : ℝ → EuclideanSpace ℝ (Fin (2 * w)) → ℂ := fun β x =>
    ((2 * thetaW a β : ℝ) : ℂ) • radialLift w (thermalDiff w β) x
  have hrep : ∀ x, radialLift w (hMaj w a β₀) x = ∫ β in Ioc 0 β₀, F β x := by
    intro x
    simp only [F, radialLift, hMaj, smul_eq_mul]
    have hterm : ∀ β : ℝ, ((2 * thetaW a β : ℝ) : ℂ) * ((thermalDiff w β (‖x‖ ^ 2 / 2) : ℝ) : ℂ) =
        ((2 * (thermalDiff w β (‖x‖ ^ 2 / 2) * thetaW a β) : ℝ) : ℂ) := by
      intro β; push_cast; ring
    simp_rw [hterm]
    rw [integral_complex_ofReal, integral_const_mul]
  have hint : Integrable (fun p : EuclideanSpace ℝ (Fin (2 * w)) × ℝ => F p.2 p.1)
      (volume.prod (volume.restrict (Ioc 0 β₀))) := by
    have hFm : Measurable (fun p : EuclideanSpace ℝ (Fin (2 * w)) × ℝ => F p.2 p.1) := by
      have := measurable_thetaW a
      simp only [F, radialLift, thermalDiff]
      fun_prop
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    have hnorm : ∀ β ∈ Ioc 0 β₀, ∫ x, ‖F β x‖ =
        2 * thetaW a β * (((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
          ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t|) := by
      intro β _
      have hx : ∀ x : EuclideanSpace ℝ (Fin (2 * w)), ‖F β x‖ =
          2 * thetaW a β * |thermalDiff w β (‖x‖ ^ 2 / 2)| := fun x => by
        simp only [F, radialLift, norm_smul, Complex.norm_real, Real.norm_eq_abs]
        rw [abs_of_pos (by have := thetaW_pos a β; positivity)]
      simp_rw [hx]
      rw [integral_const_mul]
      congr 1
      exact integral_radialLiftReal prob.hw (fun t => |thermalDiff w β t|)
    refine ⟨?_, ?_⟩
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      show Integrable (fun x => ((2 * thetaW a β : ℝ) : ℂ) • radialLift w (thermalDiff w β) x) volume
      exact ((thermalDiff_mem_TestClass prob ha hβ.1).int_lift).smul ((2 * thetaW a β : ℝ) : ℂ)
    · have hmeas : AEStronglyMeasurable
          (fun β => ∫ x, ‖F β x‖) (volume.restrict (Ioc 0 β₀)) := by
        have h := (hFm.norm.aestronglyMeasurable
          (μ := volume.prod (volume.restrict (Ioc 0 β₀)))).prod_swap
        exact h.integral_prod_right'
      refine Integrable.of_bound
        (C := 2 * (Real.exp (8 * π * a) * ((w : ℝ) / (4 * π * a)) ^ w + Real.exp (8 * π * a)))
        hmeas ?_
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun β hβ => ?_
      rw [hnorm β hβ]
      obtain ⟨_, hv⟩ := integral_pow_mul_abs_thermalDiff_le prob.hw hβ.1
      have h1 := rpow_neg_mul_thetaW_le prob.hw ha0 hβ.1
      have h2 := thetaW_le ha0.le hβ.1
      have hθ := thetaW_pos a β
      have hI : 0 ≤ ((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
          ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t| := by
        refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
        exact mul_nonneg (pow_nonneg (mem_Ioi.mp ht).le _) (abs_nonneg _)
      rw [Real.norm_of_nonneg (by positivity)]
      calc 2 * thetaW a β * (((2 * π) ^ w / ((w - 1).factorial : ℝ)) *
            ∫ t in Ioi 0, t ^ (w - 1) * |thermalDiff w β t|)
          ≤ 2 * thetaW a β * (β ^ (-(w : ℝ)) + 1) := by gcongr
        _ = 2 * (β ^ (-(w : ℝ)) * thetaW a β + thetaW a β) := by ring
        _ ≤ _ := by linarith
  ext ξ
  have h1 := fourier_integral_family hint ξ
  have hrep' : (fun x => ∫ β in Ioc 0 β₀, F β x) = radialLift w (hMaj w a β₀) :=
    (funext hrep).symm
  rw [hrep'] at h1
  rw [h1]
  have h2 : ∀ᵐ β ∂(volume.restrict (Ioc 0 β₀)), 𝓕 (F β) ξ = -(F β ξ) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have hodd := (thermalDiff_mem_TestClass prob ha hβ.1).fourier_odd
    simp only [F]
    rw [fourier_const_smul]
    change (((2 * thetaW a β : ℝ) : ℂ) • 𝓕 (radialLift w (thermalDiff w β))) ξ = _
    rw [hodd]
    simp only [Pi.smul_apply, Pi.neg_apply, smul_neg]
    rfl
  rw [integral_congr_ae h2, integral_neg, ← hrep ξ]
  rfl

theorem hMaj_mem_TestClass (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) :
    TestClass prob a (hMaj prob.w a β₀) where
  cont := continuousOn_hMaj prob.hw ha0
  int_lift := by
    rw [integrable_radialLift_iff prob.hw]
    exact integrableOn_pow_hMaj prob.hw ha0
  fourier_odd := fourier_odd_hMaj prob ha ha0
  int_cardy := integrableOn_abs_hMaj_V prob ha ha0

/-- `g_vac(h) = 2 ∫ g_vac(Ξ_β) ϑ(dβ)` (Fubini) for every `(w, Q)`. -/
lemma gVac_hMaj (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) :
    prob.gVac a (hMaj prob.w a β₀) =
      2 * ∫ β in Ioc 0 β₀, prob.gVac a (thermalDiff prob.w β) * thetaW a β := by
  have hP := integrable_prod_V prob (β₀ := β₀) ha ha0
  have hswap := integral_integral_swap (μ := volume.restrict (Ioi 0))
    (ν := volume.restrict (Ioc 0 β₀))
    (f := fun t β => thermalDiff prob.w β t * prob.cardyV a t * thetaW a β) hP
  unfold FixedWeightProblem.gVac hMaj
  have e1 : ∀ t : ℝ, 2 * (∫ β in Ioc 0 β₀, thermalDiff prob.w β t * thetaW a β) *
      prob.cardyV a t =
      2 * ∫ β in Ioc 0 β₀, thermalDiff prob.w β t * prob.cardyV a t * thetaW a β := by
    intro t
    rw [mul_assoc, ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun β => ?_)
    ring
  have e2 : ∀ β : ℝ, ∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyV a t * thetaW a β =
      (∫ t in Ioi 0, thermalDiff prob.w β t * prob.cardyV a t) * thetaW a β := by
    intro β; rw [integral_mul_const]
  simp_rw [e1]
  rw [integral_const_mul, hswap]
  simp_rw [e2]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun β => ?_)
  ring

/-- `C₀ := -h_vac` (`dual_spectrum.tex`, eq. before Lemma M) for any `prob : FixedWeightProblem`. -/
noncomputable def dualC0 (prob : FixedWeightProblem) (a β₀ : ℝ) : ℝ :=
  2 * ∫ β in Ioc 0 β₀,
    (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) -
      Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))) * thetaW a β

lemma dualC0_virasoro (a β₀ : ℝ) : dualC0 virasoroProblem a β₀ = Duality.dualC0 a β₀ := by
  unfold dualC0 Duality.dualC0
  simp only [virasoroProblem_w, Nat.cast_one, Real.rpow_neg_one, virasoroProblem_nullPoly]

private lemma dterm_pos (prob : FixedWeightProblem) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (hβ1 : β < 1) :
    0 < β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) -
      Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β)) := by
  have hg := gVac_thermalDiff_neg prob ha hβ hβ1
  rw [prob.gVac_thermalDiff a hβ] at hg
  linarith

private lemma integrableOn_dterm (prob : FixedWeightProblem) {a β₀ : ℝ} (ha : 0 < a) :
    IntegrableOn (fun β =>
      (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) -
        Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))) * thetaW a β)
      (Ioc 0 β₀) := by
  refine Integrable.of_bound
    (C := Real.exp (8 * π * a) * ((prob.w : ℝ) / (2 * π * a)) ^ prob.w +
      Real.exp (2 * π * a * max β₀ 0) * Real.exp (8 * π * a)) ?_ ?_
  · have := measurable_thetaW a
    unfold FixedWeightProblem.nullPoly
    refine Measurable.aestronglyMeasurable ?_
    refine (Measurable.sub ?_ ?_).mul this
    · refine (Measurable.mul ?_ ?_).mul ?_
      · exact measurable_id.pow_const _
      · exact (measurable_const.div measurable_id).exp
      · exact Finset.measurable_prod _ fun l _ =>
          measurable_const.sub (((measurable_const.div measurable_id).exp).pow_const _)
    · refine (Measurable.mul ?_ ?_)
      · exact (measurable_const.mul measurable_id).exp
      · exact Finset.measurable_prod _ fun l _ =>
          measurable_const.sub (((measurable_const.mul measurable_id).exp).pow_const _)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    have h1 := rpow_neg_mul_exp_thetaW_le prob.hw ha hβ.1
    have h2 := thetaW_le ha.le hβ.1
    have h3 : Real.exp (2 * π * a * β) ≤ Real.exp (2 * π * a * max β₀ 0) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hβ.2.trans (le_max_left _ _)) (by positivity))
    have hq1 : prob.nullPoly (Real.exp (-2 * π / β)) ≤ 1 :=
      prob.nullPoly_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (by linarith [Real.pi_pos]) hβ.1.le))
    have hq2 : prob.nullPoly (Real.exp (-2 * π * β)) ≤ 1 :=
      prob.nullPoly_le_one (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by
        have : 0 ≤ 2 * π * β := mul_nonneg (by positivity) hβ.1.le; linarith))
    have hq1_nn : 0 ≤ prob.nullPoly (Real.exp (-2 * π / β)) :=
      (prob.nullPoly_pos (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr
        (div_neg_of_neg_of_pos (by linarith [Real.pi_pos]) hβ.1))).le
    have hq2_nn : 0 ≤ prob.nullPoly (Real.exp (-2 * π * β)) :=
      (prob.nullPoly_pos (Real.exp_pos _).le (Real.exp_lt_one_iff.mpr (by
        have : 0 < 2 * π * β := mul_pos (by positivity) hβ.1; linarith))).le
    have hθ := thetaW_pos a β
    have hA_nn : 0 ≤ β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) *
        prob.nullPoly (Real.exp (-2 * π / β)) :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg hβ.1.le _) (Real.exp_pos _).le) hq1_nn
    have hB_nn : 0 ≤ Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β)) :=
      mul_nonneg (Real.exp_pos _).le hq2_nn
    have hA' : β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) *
        prob.nullPoly (Real.exp (-2 * π / β)) ≤
        β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) :=
      mul_le_of_le_one_right (mul_nonneg (Real.rpow_nonneg hβ.1.le _) (Real.exp_pos _).le) hq1
    have hB' : Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β)) ≤
        Real.exp (2 * π * a * β) :=
      mul_le_of_le_one_right (Real.exp_pos _).le hq2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hθ]
    have habs : |β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) *
          prob.nullPoly (Real.exp (-2 * π / β)) -
        Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))| ≤
        β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) + Real.exp (2 * π * a * β) := by
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) +
            Real.exp (2 * π * a * β)) * thetaW a β :=
          mul_le_mul_of_nonneg_right habs hθ.le
      _ = β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * thetaW a β +
            Real.exp (2 * π * a * β) * thetaW a β := by ring
      _ ≤ _ := add_le_add h1 (mul_le_mul h3 h2 hθ.le (Real.exp_pos _).le)

lemma hMaj_vac (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : prob.totalShift ≤ a) (ha0 : 0 < a) :
    prob.gVac a (hMaj prob.w a β₀) = -dualC0 prob a β₀ := by
  rw [gVac_hMaj prob ha ha0, dualC0, ← mul_neg, ← integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun β hβ => ?_
  rw [prob.gVac_thermalDiff a hβ.1]
  ring

lemma dualC0_pos (prob : FixedWeightProblem) {a β₀ : ℝ}
    (ha : 0 < a) (hβ₀ : 0 < β₀) (hβ₀1 : β₀ < 1) :
    0 < dualC0 prob a β₀ := by
  unfold dualC0
  refine mul_pos two_pos ?_
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hsupp : Function.support (fun β =>
        (β ^ (-(prob.w : ℝ)) * Real.exp (2 * π * a / β) * prob.nullPoly (Real.exp (-2 * π / β)) -
          Real.exp (2 * π * a * β) * prob.nullPoly (Real.exp (-2 * π * β))) * thetaW a β) ∩
        Ioc 0 β₀ = Ioc 0 β₀ := by
      ext β
      simp only [mem_inter_iff, Function.mem_support, ne_eq, and_iff_right_iff_imp]
      intro hβ
      exact (mul_pos (dterm_pos prob ha hβ.1 (hβ.2.trans_lt hβ₀1)) (thetaW_pos a β)).ne'
    rw [hsupp]; simp [hβ₀]
  · rw [EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall fun β hβ =>
      (mul_pos (dterm_pos prob ha hβ.1 (hβ.2.trans_lt hβ₀1)) (thetaW_pos a β)).le
  · exact integrableOn_dterm prob ha

lemma integrableOn_Xi_theta {w : ℕ} (hw : 1 ≤ w) {a β₀ : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun β => thermalDiff w β t * thetaW a β) (Ioc 0 β₀) := by
  refine Integrable.of_bound (C := Real.exp (8 * π * a) +
      Real.exp (8 * π * a) * ((w : ℝ) / (4 * π * a)) ^ w) ?_ ?_
  · exact (by have := measurable_thetaW a; unfold thermalDiff; fun_prop :
      Measurable fun β : ℝ => thermalDiff w β t * thetaW a β).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun β hβ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (thetaW_pos a β)]
    have h1 := rpow_neg_mul_thetaW_le hw ha hβ.1
    have h2 := thetaW_le ha.le hβ.1
    have e1 : Real.exp (-2 * π * β * t) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ β * t := mul_nonneg hβ.1.le ht; nlinarith [Real.pi_pos])
    have e2 : Real.exp (-2 * π * t / β) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ t / β := div_nonneg ht hβ.1.le
      rw [show -2 * π * t / β = -(2 * π) * (t / β) by ring]
      nlinarith [Real.pi_pos])
    have h3 : |thermalDiff w β t| ≤ 1 + β ^ (-(w : ℝ)) := by
      refine (abs_thermalDiff_le (w := w) hβ.1 t).trans ?_
      have hbw := mul_le_of_le_one_right (Real.rpow_nonneg hβ.1.le (-(w : ℝ))) e2
      linarith
    calc |thermalDiff w β t| * thetaW a β
        ≤ (1 + β ^ (-(w : ℝ))) * thetaW a β := mul_le_mul_of_nonneg_right h3 (thetaW_pos a β).le
      _ = thetaW a β + β ^ (-(w : ℝ)) * thetaW a β := by ring
      _ ≤ _ := add_le_add h2 h1

/-- Lemma M(b): `h ≥ w_*` on `[T₀, ∞)` when `t₀^*(w, β₀) ≤ T₀`. -/
lemma wStar_le_hMaj {w : ℕ} (hw : 1 ≤ w) {a β₀ T₀ : ℝ} (ha : 0 < a) (hβ₀ : 0 < β₀)
    (hβ₀1 : β₀ < 1) (hT₀ : t0Star w β₀ ≤ T₀) {t : ℝ} (ht : T₀ ≤ t) :
    wStar a β₀ t ≤ hMaj w a β₀ t := by
  have ht0 : 0 ≤ t := by
    have hβ₀_half : 0 ≤ t0 w β₀ := by
      unfold t0
      have hpow : β₀ ^ (w : ℝ) ≤ 1 := Real.rpow_le_one hβ₀.le hβ₀1.le (Nat.cast_nonneg w)
      have hbw : 1 ≤ 2 * β₀ ^ (-(w : ℝ)) := by
        rw [Real.rpow_neg hβ₀.le]
        have hpos : 0 < β₀ ^ (w : ℝ) := Real.rpow_pos_of_pos hβ₀ _
        calc (1 : ℝ) ≤ 2 := by norm_num
          _ ≤ 2 * (β₀ ^ (w : ℝ))⁻¹ :=
              le_mul_of_one_le_right (by norm_num) ((one_le_inv₀ hpos).mpr hpow)
      have hlog : 0 ≤ Real.log (2 * β₀ ^ (-(w : ℝ))) := Real.log_nonneg hbw
      have hden : 0 < 1 - β₀ ^ 2 := by nlinarith
      positivity
    have hle := t0_le_t0Star (w := w) hβ₀ le_rfl hβ₀1
    linarith
  unfold wStar hMaj
  have hint := integrableOn_Xi_theta hw (β₀ := β₀) ha ht0
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_wStar_integrand ha.le β₀ t) (hint.const_mul 2)
    measurableSet_Ioc fun β hβ => ?_
  have h2 := two_thermalDiff_ge hβ.1 (hβ.2.trans_lt hβ₀1)
    ((t0_le_t0Star (w := w) hβ.1 hβ.2 hβ₀1).trans (hT₀.trans ht))
  have hθ := thetaW_pos a β
  nlinarith

lemma tendsto_thermalDiff_div_wStar {w : ℕ} {a β₀ β : ℝ}
    (ha : 0 ≤ a) (hβ₀ : 0 < β₀) (hβ : 0 < β) :
    Tendsto (fun t => thermalDiff w β t / wStar a β₀ t) atTop (𝓝 0) := by
  have h1 := Duality.tendsto_exp_div_wStar (a := a) ha hβ₀ hβ
  have h2 := (Duality.tendsto_exp_div_wStar (a := a) ha hβ₀ (inv_pos.mpr hβ)).const_mul
    (β ^ (-(w : ℝ)))
  have h3 := h1.add h2
  rw [mul_zero, add_zero] at h3
  refine squeeze_zero_norm' ?_ h3
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hwpos := wStar_pos ha hβ₀ ht
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hwpos]
  have htri := abs_thermalDiff_le (w := w) hβ t
  rw [show -2 * π * t / β = -2 * π * β⁻¹ * t by ring] at htri
  calc |thermalDiff w β t| / wStar a β₀ t
      ≤ (Real.exp (-2 * π * β * t) + β ^ (-(w : ℝ)) * Real.exp (-2 * π * β⁻¹ * t)) /
          wStar a β₀ t := div_le_div_of_nonneg_right htri hwpos.le
    _ = _ := by ring

lemma tendsto_pow_exp_div_wStar (k : ℕ) {a β₀ : ℝ} (ha : 0 ≤ a) (hβ₀ : 0 < β₀) :
    Tendsto (fun t => t ^ k * Real.exp (-2 * π * t) / wStar a β₀ t) atTop (𝓝 0) := by
  let β₁ : ℝ := min (1 / 4) (β₀ / 2)
  have hβ₁pos : 0 < β₁ := lt_min (by norm_num) (by positivity)
  have h2 : 2 * β₁ ≤ β₀ := by have := min_le_right (1 / 4) (β₀ / 2); linarith
  have h2' : 4 * β₁ ≤ 1 := by have := min_le_left (1 / 4) (β₀ / 2); linarith
  let K : ℝ := β₁ * thetaW a β₁
  have hKpos : 0 < K := mul_pos hβ₁pos (thetaW_pos a β₁)
  have hpow_exp : Tendsto (fun t : ℝ => t ^ k * Real.exp (-(π * t))) atTop (𝓝 0) := by
    have h0 := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    have hcomp := (h0.comp (tendsto_id.const_mul_atTop Real.pi_pos)).const_mul (π ^ k)⁻¹
    rw [mul_zero] at hcomp
    refine hcomp.congr' (by
      filter_upwards [eventually_ge_atTop 0] with t _
      simp only [Function.comp_apply, id_eq, mul_pow]
      field_simp [Real.pi_pos.ne'])
  have hlim : Tendsto (fun t : ℝ => K⁻¹ * (t ^ k * Real.exp (-(π * t)))) atTop (𝓝 0) := by
    simpa using hpow_exp.const_mul K⁻¹
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact div_nonneg (mul_nonneg (pow_nonneg ht k) (Real.exp_pos _).le)
      (wStar_pos ha hβ₀ ht).le
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hw := wStar_lower (a := a) (β₀ := β₀) (β₁ := β₁) (t := t) ha hβ₁pos h2 ht
    have hwpos := wStar_pos ha hβ₀ ht
    rw [div_le_iff₀ hwpos]
    have he : Real.exp (-2 * π * t) ≤ Real.exp (-(π * t)) * Real.exp (-4 * π * β₁ * t) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.pi_pos, mul_nonneg ht Real.pi_pos.le]
    have hK_le : K * Real.exp (-4 * π * β₁ * t) ≤ wStar a β₀ t := by
      calc K * Real.exp (-4 * π * β₁ * t)
          = β₁ * (Real.exp (-4 * π * β₁ * t) * thetaW a β₁) := by dsimp [K]; ring
        _ ≤ wStar a β₀ t := hw
    calc t ^ k * Real.exp (-2 * π * t)
        ≤ t ^ k * (Real.exp (-(π * t)) * Real.exp (-4 * π * β₁ * t)) :=
          mul_le_mul_of_nonneg_left he (pow_nonneg ht k)
      _ = K⁻¹ * (t ^ k * Real.exp (-(π * t))) * (K * Real.exp (-4 * π * β₁ * t)) := by
          field_simp [hKpos.ne']
      _ ≤ K⁻¹ * (t ^ k * Real.exp (-(π * t))) * wStar a β₀ t :=
          mul_le_mul_of_nonneg_left hK_le (by positivity)

/-- Generalized Laguerre basis function `ψ_k(t) = L_k^{(w-1)}(4π t) e^{-2π t}` (`dual_spectrum.tex`). -/
noncomputable def genLaguerrePsi (w k : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (k + 1),
    (-1 : ℝ) ^ j * ((Nat.choose (k + w - 1) (k - j) : ℝ) * (4 * π * t) ^ j / (j.factorial : ℝ))) *
    Real.exp (-2 * π * t)

lemma tendsto_genLaguerrePsi_div_wStar (w k : ℕ) {a β₀ : ℝ} (ha : 0 ≤ a) (hβ₀ : 0 < β₀) :
    Tendsto (fun t => genLaguerrePsi w k t / wStar a β₀ t) atTop (𝓝 0) := by
  have heq : (fun t => genLaguerrePsi w k t / wStar a β₀ t) =
      fun t => ∑ j ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ j * (Nat.choose (k + w - 1) (k - j) : ℝ) * (4 * π) ^ j / (j.factorial : ℝ)) *
          (t ^ j * Real.exp (-2 * π * t) / wStar a β₀ t) := by
    ext t
    unfold genLaguerrePsi
    rw [Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]; ring
  rw [heq]
  have hsum : Tendsto (fun t => ∑ j ∈ Finset.range (k + 1),
      ((-1 : ℝ) ^ j * (Nat.choose (k + w - 1) (k - j) : ℝ) * (4 * π) ^ j / (j.factorial : ℝ)) *
        (t ^ j * Real.exp (-2 * π * t) / wStar a β₀ t))
      atTop (𝓝 (∑ _j ∈ Finset.range (k + 1), (0 : ℝ))) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    simpa using (tendsto_pow_exp_div_wStar j ha hβ₀).const_mul _
  simpa using hsum

/-- **Lemma M** (`dual_spectrum.tex`, `ds:M`) for every fixed weight `(w, Q)` (`prob : FixedWeightProblem`)
with `c̃ > 0` and `c̃ ≥ 12 S` (`a = c̃ / 12 > 0`, `a ≥ prob.totalShift`).
Let `β₀ ∈ (0, 1/2]`, `T₀ ≥ t₀^*(w, β₀)`, `ϑ(dβ) = e^{-4πa(1/β - 2)} dβ` on `(0, β₀]`,
`w_*(t) = ∫₀^{β₀} e^{-2πβt} ϑ(dβ)`, `h = 2 ∫₀^{β₀} Ξ_β^{(w)} ϑ(dβ)`. Then:
* (a) `h ∈ \overline{\mathcal A}_w` (`TestClass prob a`), `h_vac = -C₀`, and `0 < C₀ < ∞` (`dualC0`);
* (b) `h ≥ w_*` on `[T₀, ∞)`;
* (c) for every `β > 0` there is `C_β > 0` with `e^{-2πβt} ≤ C_β w_*(t)` on `[0, ∞)`,
  and `ψ_k / w_* → 0`, `Ξ_β^{(w)} / w_* → 0` as `t → ∞`. -/
theorem lemma_M (prob : FixedWeightProblem) {cTilde β₀ T₀ : ℝ}
    (hc_pos : 0 < cTilde) (hc : 12 * prob.totalShift ≤ cTilde)
    (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2) (hT₀ : t0Star prob.w β₀ ≤ T₀) :
    TestClass prob (cTilde / 12) (hMaj prob.w (cTilde / 12) β₀) ∧
      prob.gVac (cTilde / 12) (hMaj prob.w (cTilde / 12) β₀) = -dualC0 prob (cTilde / 12) β₀ ∧
      0 < dualC0 prob (cTilde / 12) β₀ ∧
      (∀ t, T₀ ≤ t → wStar (cTilde / 12) β₀ t ≤ hMaj prob.w (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
        ∀ t, 0 ≤ t → Real.exp (-2 * π * β * t) ≤ C * wStar (cTilde / 12) β₀ t) ∧
      (∀ k : ℕ, Tendsto (fun t => genLaguerrePsi prob.w k t / wStar (cTilde / 12) β₀ t)
        atTop (𝓝 0)) ∧
      (∀ β : ℝ, 0 < β →
        Tendsto (fun t => thermalDiff prob.w β t / wStar (cTilde / 12) β₀ t) atTop (𝓝 0)) := by
  have ha : prob.totalShift ≤ cTilde / 12 := by linarith
  have ha0 : 0 < cTilde / 12 := by linarith
  have hβ₀1 : β₀ < 1 := by linarith
  exact ⟨hMaj_mem_TestClass prob ha ha0, hMaj_vac prob ha ha0, dualC0_pos prob ha0 hβ₀ hβ₀1,
    fun t ht => wStar_le_hMaj prob.hw ha0 hβ₀ hβ₀1 hT₀ ht,
    fun β hβ => exp_le_const_wStar ha0.le hβ₀ hβ,
    fun k => tendsto_genLaguerrePsi_div_wStar prob.w k ha0.le hβ₀,
    fun β hβ => tendsto_thermalDiff_div_wStar ha0.le hβ₀ hβ⟩

/-- Spinless Virasoro instance of `lemma_M`, recovering `Duality.lemma_M`. -/
theorem virasoro_lemma_M {cTilde β₀ T₀ : ℝ}
    (hc : 12 * virasoroProblem.totalShift ≤ cTilde)
    (hβ₀ : 0 < β₀) (hβ₀2 : β₀ ≤ 1 / 2) (hT₀ : Duality.t0 β₀ ≤ T₀) :
    TestClass virasoroProblem (cTilde / 12) (Duality.hMaj (cTilde / 12) β₀) ∧
      virasoroProblem.gVac (cTilde / 12) (Duality.hMaj (cTilde / 12) β₀) =
        -Duality.dualC0 (cTilde / 12) β₀ ∧
      0 < Duality.dualC0 (cTilde / 12) β₀ ∧
      (∀ t, T₀ ≤ t → wStar (cTilde / 12) β₀ t ≤ Duality.hMaj (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β → ∃ C : ℝ, 0 < C ∧
        ∀ t, 0 ≤ t → Real.exp (-2 * π * β * t) ≤ C * wStar (cTilde / 12) β₀ t) ∧
      (∀ β : ℝ, 0 < β →
        Tendsto (fun t => thermalDiff 1 β t / wStar (cTilde / 12) β₀ t) atTop (𝓝 0)) := by
  have hc_pos : 0 < cTilde := by
    have := hc; rw [virasoroProblem_totalShift] at this; linarith
  have hT₀' : t0Star virasoroProblem.w β₀ ≤ T₀ := by
    rw [t0Star_eq_t0 hβ₀ (by linarith), virasoroProblem_w, t0_one]
    exact hT₀
  obtain ⟨h1, h2, h3, h4, h5, _, h7⟩ := lemma_M virasoroProblem hc_pos hc hβ₀ hβ₀2 hT₀'
  simp only [virasoroProblem_w, hMaj_one, dualC0_virasoro] at h1 h2 h3 h4 h7
  exact ⟨h1, h2, h3, h4, h5, h7⟩

/-! ### Axiom checks -/

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.lemma_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.lemma_M

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.virasoro_lemma_M' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.virasoro_lemma_M

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.exists_beta0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.exists_beta0

/-- info: 'FormalResearch.ModularBootstrap.FixedWeight.tendsto_genLaguerrePsi_div_wStar' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FixedWeight.tendsto_genLaguerrePsi_div_wStar

end FormalResearch.ModularBootstrap.FixedWeight

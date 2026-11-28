module

public import FormalResearch.SignUncertainty.CtBoasContour
public import FormalResearch.SignUncertainty.CtBoasSmoothBlock
public import FormalResearch.SignUncertainty.CtBoasPhaseReg

/-!
# `ct:boas` Steps 3–5: exact-phase harmonic estimate (`O(c^{-14})`) on every near block

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, `ct:boas` Steps 3–5.
For `c ≥ c₀`, `ε = ±1`, `c₁² c^{2/3} ≤ R ≤ 4 c₁² c^{2/3}`, `j < N`, and `2 ≤ k ≤ ⌈c²⌉`:

`boas_harmonic_bound`:
`|∫ nearWeight ε c R j L * hankelHL c f L * cos (k * (boasX c ε L + π/2)) dL| ≤ C_har * M[f] * c^{-14}`.

Proof combines `hankelHL_compact_fourier` and `hankel_contour_shift_norm_le` (`CtBoasContour`)
with shift `s_j = min (τ_j / 4) (min (1 / 4) (325 log c / (c ℓ_j)))` and cutoff `T_j = 3 τ_j / 2`:
* `|τ| ≤ T_j` (`σ = 0`) and horizontal connectors `τ = ±T_j` (`0 ≤ σ ≤ s_j`): `osc_ibp_r` at `r = 200`
  against `θ = k X + c τ` (`k ≥ 2 ⇒ θ' ≥ 0.015 k c τ_j`);
* `|τ| ≥ T_j` (`σ = s_j`): `S0_ineq` + `hankelEdge_delta32_ge_L` give `exp(-50 log c) = c^{-50}`
  in `ĥ(s_j + i τ) e^{c s_j L_j}`, paired with explicit `c^{12} / τ²` from `osc_ibp_linear_two`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.SignUncertainty.FctSym

private lemma iteratedDeriv_ofReal_c (g : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => ((g y : ℝ) : ℂ)) x = ((iteratedDeriv n g x : ℝ) : ℂ) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hfun : iteratedDeriv n (fun y => ((g y : ℝ) : ℂ)) = fun y => ((iteratedDeriv n g y : ℝ) : ℂ) :=
      funext ih
    rw [iteratedDeriv_succ, hfun]
    calc deriv (fun y => ((iteratedDeriv n g y : ℝ) : ℂ)) x
        = ((deriv (iteratedDeriv n g) x : ℝ) : ℂ) := by
          by_cases hd : DifferentiableAt ℝ (iteratedDeriv n g) x
          · exact ((hd.hasDerivAt).ofReal_comp).deriv
          · have hnd : ¬DifferentiableAt ℝ (fun y : ℝ => ((iteratedDeriv n g y : ℝ) : ℂ)) x := fun hc =>
              hd (Complex.reCLM.differentiableAt.comp x hc)
            rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hnd, Complex.ofReal_zero]
      _ = ((iteratedDeriv (n + 1) g x : ℝ) : ℂ) := by rw [← iteratedDeriv_succ]

private lemma exp_shift_iteratedDeriv (α L₀ : ℝ) (k : ℕ) (L : ℝ) :
    iteratedDeriv k (fun x : ℝ => Complex.exp ((α * (x - L₀) : ℝ) : ℂ)) L =
      ((α : ℝ) : ℂ) ^ k * Complex.exp ((α * (L - L₀) : ℝ) : ℂ) := by
  induction k generalizing L with
  | zero => simp
  | succ k ih =>
    have hfun : iteratedDeriv k (fun x : ℝ => Complex.exp ((α * (x - L₀) : ℝ) : ℂ)) =
        fun x => ((α : ℝ) : ℂ) ^ k * Complex.exp ((α * (x - L₀) : ℝ) : ℂ) := funext ih
    rw [iteratedDeriv_succ, hfun]
    have hd : HasDerivAt (fun x : ℝ => ((α : ℝ) : ℂ) ^ k * Complex.exp ((α * (x - L₀) : ℝ) : ℂ))
        (((α : ℝ) : ℂ) ^ (k + 1) * Complex.exp ((α * (L - L₀) : ℝ) : ℂ)) L := by
      have h1 : HasDerivAt (fun x : ℝ => ((α * (x - L₀) : ℝ) : ℂ)) ((α : ℝ) : ℂ) L := by
        have := (((hasDerivAt_id L).sub_const L₀).const_mul α).ofReal_comp
        exact this.congr_deriv (by simp)
      refine (h1.cexp.const_mul (((α : ℝ) : ℂ) ^ k)).congr_deriv ?_
      rw [pow_succ]; ring
    exact hd.deriv

private lemma iteratedDeriv_linear_zero {m : ℕ} (hm : 1 ≤ m) (α x : ℝ) :
    iteratedDeriv (m + 1) (fun y : ℝ => α * y) x = 0 := by
  have h1 : deriv (fun y : ℝ => α * y) = fun _ => α := funext fun y =>
    (((hasDerivAt_id y).const_mul α).congr_deriv (by simp)).deriv
  rw [iteratedDeriv_succ', h1]
  cases m with
  | zero => omega
  | succ k =>
    rw [iteratedDeriv_succ', deriv_const']
    clear hm
    induction k with
    | zero => simp
    | succ k ih => rw [iteratedDeriv_succ', deriv_const', ih]

private lemma integral_Ioi_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ τ in Ioi T, (τ ^ 2)⁻¹ = T⁻¹ := by
  have hint : IntegrableOn (fun τ : ℝ => (τ ^ 2)⁻¹) (Ioi T) := by
    refine (integrable_inv_one_add_sq.const_mul (1 + T⁻¹ ^ 2)).integrableOn.mono'
      ((measurable_id.pow_const 2).inv.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : T < τ) => ?_)
    have hτ2 : T ^ 2 ≤ τ ^ 2 := by nlinarith only [hT, hτ]
    have h1 : 1 ≤ T⁻¹ ^ 2 * τ ^ 2 := by
      rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]; exact hτ2
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (τ ^ 2)⁻¹ * (1 + τ ^ 2) ≤ (τ ^ 2)⁻¹ * ((1 + T⁻¹ ^ 2) * τ ^ 2) := by gcongr; linarith
      _ = 1 + T⁻¹ ^ 2 := by
        field_simp [pow_ne_zero 2 (lt_trans hT hτ).ne']
        rw [div_self (lt_trans hT hτ).ne']
  have hlimL : Tendsto (fun Y : ℝ => ∫ τ in T..Y, (τ ^ 2)⁻¹) atTop (𝓝 (∫ τ in Ioi T, (τ ^ 2)⁻¹)) :=
    intervalIntegral_tendsto_integral_Ioi T hint tendsto_id
  have hlimR : Tendsto (fun Y : ℝ => T⁻¹ - Y⁻¹) atTop (𝓝 T⁻¹) := by
    simpa using (tendsto_const_nhds (x := T⁻¹)).sub tendsto_inv_atTop_zero
  refine tendsto_nhds_unique hlimL (hlimR.congr' ?_)
  filter_upwards [eventually_ge_atTop T] with Y hY
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := T) (b := Y)
    (f := fun x : ℝ => -x⁻¹) (f' := fun x : ℝ => (x ^ 2)⁻¹)
    (fun x hx => by
      rw [uIcc_of_le hY] at hx
      exact (hasDerivAt_inv (lt_of_lt_of_le hT hx.1).ne').neg.congr_deriv (by ring))
    ((ContinuousOn.inv₀ (by fun_prop) fun x hx => by
      rw [uIcc_of_le hY] at hx
      exact pow_ne_zero 2 (lt_of_lt_of_le hT hx.1).ne').intervalIntegrable_of_Icc hY)
  linarith only [hftc]

private lemma integral_Iio_inv_sq {T : ℝ} (hT : 0 < T) :
    ∫ τ in Iio (-T), (τ ^ 2)⁻¹ = T⁻¹ := by
  rw [← integral_indicator measurableSet_Iio, ← integral_neg_eq_self]
  have : (fun u : ℝ => (Iio (-T)).indicator (fun τ : ℝ => (τ ^ 2)⁻¹) (-u)) =
      (Ioi T).indicator (fun u : ℝ => (u ^ 2)⁻¹) := by
    ext u
    by_cases hu : T < u
    · have hu' : -u ∈ Iio (-T) := by change -u < -T; linarith
      rw [indicator_of_mem hu', indicator_of_mem hu, neg_sq]
    · have hu' : -u ∉ Iio (-T) := by change ¬ (-u < -T); linarith
      rw [indicator_of_notMem hu', indicator_of_notMem hu]
  rw [this, integral_indicator measurableSet_Ioi]
  exact integral_Ioi_inv_sq hT

private lemma osc_amplitude_deriv_bound (r : ℕ) {C_u : ℕ → ℝ} (hCu : ∀ m, 0 ≤ C_u m)
    {u : ℝ → ℝ} (hu_cd : ∀ n : ℕ, ContDiff ℝ n u) {E α L₀ M_e a b : ℝ}
    (hE1 : 1 ≤ E) (hα0 : 0 ≤ α) (hαE : α ≤ E)
    (hu_sym : ∀ m ≤ r, ∀ L : ℝ, |iteratedDeriv m u L| ≤ C_u m * E ^ m)
    (hMe0 : 0 ≤ M_e) (hexp_bd : ∀ L ∈ Icc a b, Real.exp (α * (L - L₀)) ≤ M_e) :
    let w : ℝ → ℂ := fun L => ((u L : ℝ) : ℂ) * Complex.exp ((α * (L - L₀) : ℝ) : ℂ)
    ContDiff ℝ r w ∧
      ∀ m ≤ r, ∀ L ∈ Icc a b,
        ‖iteratedDeriv m w L‖ ≤
          ((∑ m' ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_u i) * M_e) * E ^ m := by
  intro w
  have hE0 : 0 ≤ E := zero_le_one.trans hE1
  have hcd_exp : ContDiff ℝ r (fun L : ℝ => Complex.exp ((α * (L - L₀) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_const (c := α)).mul (contDiff_id.sub contDiff_const))).cexp
  have hcd_uC : ContDiff ℝ r (fun L : ℝ => ((u L : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hu_cd r)
  refine ⟨hcd_uC.mul hcd_exp, fun m hm L hL => ?_⟩
  have h1 : ContDiffAt ℝ m (fun y : ℝ => ((u y : ℝ) : ℂ)) L :=
    (hcd_uC.of_le (by exact_mod_cast hm : (m : WithTop ℕ∞) ≤ r)).contDiffAt
  have h2 : ContDiffAt ℝ m (fun y : ℝ => Complex.exp ((α * (y - L₀) : ℝ) : ℂ)) L :=
    (hcd_exp.of_le (by exact_mod_cast hm : (m : WithTop ℕ∞) ≤ r)).contDiffAt
  rw [show w = fun y => ((u y : ℝ) : ℂ) * Complex.exp ((α * (y - L₀) : ℝ) : ℂ) from rfl,
    iteratedDeriv_fun_mul h1 h2]
  refine (norm_sum_le _ _).trans ?_
  have hexp_n : ∀ (i : ℕ), ‖iteratedDeriv i (fun y : ℝ => Complex.exp ((α * (y - L₀) : ℝ) : ℂ)) L‖ ≤
      E ^ i * M_e := fun i => by
    rw [exp_shift_iteratedDeriv, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα0,
      Complex.norm_exp, show ((α * (L - L₀) : ℝ) : ℂ).re = α * (L - L₀) from rfl]
    exact mul_le_mul (pow_le_pow_left₀ hα0 hαE i) (hexp_bd L hL) (Real.exp_pos _).le (pow_nonneg hE0 i)
  calc ∑ i ∈ Finset.range (m + 1),
          ‖(m.choose i : ℝ) * iteratedDeriv i (fun y => ((u y : ℝ) : ℂ)) L *
            iteratedDeriv (m - i) (fun y => Complex.exp ((α * (y - L₀) : ℝ) : ℂ)) L‖
      ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * (C_u i * E ^ i) * (E ^ (m - i) * M_e) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        rw [show (m.choose i : ℝ) * iteratedDeriv i (fun y => ((u y : ℝ) : ℂ)) L *
            iteratedDeriv (m - i) (fun y => Complex.exp ((α * (y - L₀) : ℝ) : ℂ)) L =
            ((m.choose i : ℂ)) * (iteratedDeriv i (fun y => ((u y : ℝ) : ℂ)) L *
            iteratedDeriv (m - i) (fun y => Complex.exp ((α * (y - L₀) : ℝ) : ℂ)) L) by
          push_cast; ring,
          norm_mul, Complex.norm_natCast, norm_mul,
          iteratedDeriv_ofReal_c, Complex.norm_real, Real.norm_eq_abs]
        have hu1 := hu_sym i (him.trans hm) L
        have he1 := hexp_n (m - i)
        rw [mul_assoc ((m.choose i : ℝ))]
        exact mul_le_mul_of_nonneg_left (mul_le_mul hu1 he1 (norm_nonneg _) (mul_nonneg (hCu i) (pow_nonneg hE0 _)))
          (Nat.cast_nonneg _)
    _ = (∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C_u i) * M_e * E ^ m := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        have him : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hpow : E ^ i * E ^ (m - i) = E ^ m := by rw [← pow_add]; congr 1; omega
        calc (m.choose i : ℝ) * (C_u i * E ^ i) * (E ^ (m - i) * M_e)
            = ((m.choose i : ℝ) * C_u i) * M_e * (E ^ i * E ^ (m - i)) := by ring
          _ = _ := by rw [hpow]
    _ ≤ (∑ m' ∈ Finset.range (r + 1), ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_u i) * M_e * E ^ m := by
        gcongr
        exact Finset.single_le_sum (f := fun m' => ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_u i)
          (fun m' _ => Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCu i))
          (Finset.mem_range.2 (Nat.lt_succ_of_le hm))

private lemma tau0_le_of_le {L B : ℝ} (hL : 0 < L) (hLB : L ≤ B) :
    tau0 L ≤ Real.exp B := by
  set τ := tau0 L
  have hτ : 0 < τ := tau0_pos hL
  have hm0 : hankelEdgeM 0 = 0 := by
    have h1 := hankelEdgeM_le_sq le_rfl
    have h2 := hankelEdgeM_nonneg le_rfl
    linarith only [h1, h2]
  have hsub := hankelEdgeM_sub_log_mono le_rfl hτ.le
  rw [hm0, sub_zero, show (1 + (0 : ℝ) ^ 2 : ℝ) = 1 by norm_num, Real.log_one, zero_div, sub_zero,
    hankelEdgeM_tau0 hL] at hsub
  have hlog : Real.log (1 + τ ^ 2) ≤ 2 * B := by linarith only [hsub, hLB]
  have hexp : 1 + τ ^ 2 ≤ Real.exp (2 * B) := by
    calc 1 + τ ^ 2 = Real.exp (Real.log (1 + τ ^ 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (2 * B) := Real.exp_le_exp.2 hlog
  have hsq : τ ^ 2 ≤ (Real.exp B) ^ 2 := by
    rw [pow_two (Real.exp B), ← Real.exp_add, show B + B = 2 * B by ring]
    linarith only [hexp]
  nlinarith only [hsq, hτ, Real.exp_pos B]

private lemma hankelHhat_norm_le_mass {c ε : ℝ} (hc : 0 < c) {f : ℝ → ℝ} (hf : IsHankelEigenfn c ε f) (τ : ℝ) :
    ‖hankelHhat c f ((τ : ℂ) * Complex.I)‖ ≤ hankelMass c f := by
  unfold hankelHhat
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  have h1 : (∫ L : ℝ, ‖Complex.exp (-((c : ℂ) * ((τ : ℂ) * Complex.I) * (L : ℂ))) * (hankelHL c f L : ℂ)‖) =
      ∫ L : ℝ, |hankelHL c f L| := by
    refine integral_congr_ae (ae_of_all _ fun L => ?_)
    dsimp only
    rw [norm_mul,
      show -((c : ℂ) * ((τ : ℂ) * Complex.I) * (L : ℂ)) = ((-(c * τ * L) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, integral_abs_hankelHL hc hf]

/-- Standalone helper for `|τ| ≤ T_j` (`σ = 0`) and horizontal connectors `τ = ±T_j` (`0 ≤ σ ≤ s_j`)
using `osc_ibp_r` at order `r = 200`. Isolated from `boas_harmonic_bound` to avoid `whnf` bloat. -/
private lemma central_horiz_osc_bound
    {Bθ : ℕ → ℝ} {C_D : ℝ} (hCD0 : 0 ≤ C_D)
    (hibp_r : ∀ {a₀ a a' b' b b₀ μ Λ M_u E : ℝ} {θ : ℝ → ℝ} {u : ℝ → ℂ},
      0 < μ → 1 ≤ Λ → Λ ≤ E → 0 ≤ M_u → a₀ < a → a < a' → a' ≤ b' → b' < b → b < b₀ →
      ContDiffOn ℝ (200 + 1) θ (Ioo a₀ b₀) → (∀ x ∈ Ioo a₀ b₀, μ ≤ |deriv θ x|) →
      (∀ j : ℕ, 1 ≤ j → j ≤ 200 → ∀ x ∈ Ioo a₀ b₀, |iteratedDeriv (j + 1) θ x| ≤ Bθ j * |deriv θ x| * Λ ^ j) →
      ContDiff ℝ 200 u → (∀ x ∉ Icc a' b', u x = 0) →
      (∀ m ≤ 200, ∀ x ∈ Icc a b, ‖iteratedDeriv m u x‖ ≤ M_u * E ^ m) →
      ‖∫ x in a..b, u x * Complex.exp (Complex.I * (θ x : ℂ))‖ ≤ (b - a) * C_D * μ⁻¹ ^ 200 * M_u * E ^ 200)
    {c_x κ_min c ε : ℝ} {C_X : (r : ℕ) → 1 ≤ r → ℝ} {C_m : ℕ → ℝ} {nw : ℝ → ℝ} {f : ℝ → ℝ}
    {Lj ℓj τj a₀ a a' b' b b₀ sj Tj M_tot_w : ℝ} {k : ℕ}
    (hc1 : 1 < c) (hc32 : 3 / 2 < c) (hε : ε = 1 ∨ ε = -1) (hc_x : c_x ≤ c)
    (hf : IsHankelEigenfn c ε f) (hk2 : 2 ≤ k)
    (hκmin_pos : 0 < κ_min) (hLj_pos : 0 < Lj) (hℓ0 : 0 < ℓj) (hτ_pos : 0 < τj)
    (hℓ_lb : κ_min * c ^ (-(2 / 21 : ℝ)) ≤ ℓj) (hτ_lb : κ_min * c ^ (-(1 / 21 : ℝ)) ≤ τj)
    (hL0_pos : 0 < ctLv0 c)
    (haa : a₀ < a) (haa' : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b) (hbb₀ : b < b₀) (hba_le1 : b - a ≤ 1)
    (hsj_pos : 0 < sj) (hsj_τ : sj ≤ τj / 4) (hsj_4 : sj ≤ 1 / 4) (hsj_log : sj ≤ 325 * Real.log c / (c * ℓj))
    (hTj_def : Tj = 3 * τj / 2)
    (hsub_win : ∀ L ∈ Ioo a₀ b₀, ctLv0 c / 4 ≤ L ∧ 0 < L ∧ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100))
    (hwin : ∀ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100), 0.9 * τj ≤ tau0 L ∧ tau0 L ≤ 1.1 * τj)
    (hnw_cd : ∀ n : ℕ, ContDiff ℝ n nw) (hnw_supp : ∀ L ∉ Icc a' b', nw L = 0)
    (hCm0 : ∀ r : ℕ, 0 ≤ C_m r) (hnw_drv : ∀ r : ℕ, ∀ L : ℝ, |iteratedDeriv r nw L| ≤ C_m r * (c ^ (5 / 6 : ℝ)) ^ r)
    (hMtot_eq : M_tot_w = ∑ m' ∈ Finset.range 201, ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_m i)
    (hx_drv : ∀ L, ctLv0 c / 4 ≤ L →
      0 < L ∧ HasDerivAt (boasX c ε) (deriv (boasX c ε) L) L ∧
      0.85 * c * tau0 L ≤ deriv (boasX c ε) L ∧ deriv (boasX c ε) L ≤ 1.15 * c * tau0 L)
    (hCX_nn : ∀ r hr, 0 ≤ C_X r hr)
    (hx_sym : ∀ r hr L, ctLv0 c / 4 ≤ L → |iteratedDeriv r (boasX c ε) L| ≤ C_X r hr * c * tau0 L * lamL L ^ (r - 1))
    (hBθ_eq : ∀ i, Bθ i = (1.1 / 0.015) * C_X (i + 1) (Nat.succ_pos i))
    (hlam_le : max 1 ((ctLv0 c / 4)⁻¹) ≤ c ^ (5 / 6 : ℝ))
    (hcs_le : 325 * Real.log c / (κ_min * c ^ (-(2 / 21 : ℝ))) ≤ c ^ (5 / 6 : ℝ))
    (hdeg : (0.03 * κ_min)⁻¹ ^ 200 ≤ c)
    {σ τ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) sj) (hτ : τ ∈ Icc (-Tj) Tj) (hside : σ = 0 ∨ |τ| = Tj) :
    let u : ℝ → ℂ := fun L => ((nw L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))
    ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I) *
        Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ)) *
        boasB0 Lj u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ) := by
  intro u
  have hc0 : 0 < c := zero_lt_one.trans hc1
  have hlog1 : 1 ≤ Real.log c := by linarith only [hlog2]
  have hM := hankelMass_nonneg hc0 f
  have hMtotw_nn : 0 ≤ M_tot_w := by
    rw [hMtot_eq]
    exact Finset.sum_nonneg fun m' _ => Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCm0 i)
  have hsub_ab : Icc a b ⊆ Ioo a₀ b₀ := fun L hL => ⟨lt_of_lt_of_le haa hL.1, lt_of_le_of_lt hL.2 hbb₀⟩
  have hc56_ge1 : 1 ≤ c ^ (5 / 6 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hk_real2 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hH_le : ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I) *
      Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ))‖ ≤ 3 * hankelMass c f := by
    rcases hside with rfl | hτeq
    · simp only [Complex.ofReal_zero, zero_add, norm_mul]
      rw [show (c : ℂ) * ((τ : ℂ) * Complex.I) * (Lj : ℂ) = ((c * τ * Lj : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
      exact (hankelHhat_norm_le_mass hc0 hf τ).trans (by linarith only [hM])
    · by_cases hσ0 : σ = 0
      · subst hσ0
        simp only [Complex.ofReal_zero, zero_add, norm_mul]
        rw [show (c : ℂ) * ((τ : ℂ) * Complex.I) * (Lj : ℂ) = ((c * τ * Lj : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact (hankelHhat_norm_le_mass hc0 hf τ).trans (by linarith only [hM])
      · have hσ_pos : 0 < σ := lt_of_le_of_ne hσ.1 (Ne.symm hσ0)
        have hτ32 : 3 * τj / 2 ≤ |τ| := by linarith only [hτeq, hTj_def]
        have hS0 := S0_ineq hτ_pos hσ_pos (hσ.2.trans hsj_τ) (hσ.2.trans hsj_4) hτ32
        have hmL : hankelEdgeM τj = Lj := by rw [hτj_def]; exact hankelEdgeM_tau0 hLj_pos
        have hdel := (hankelEdge_delta32_ge_L hτ_pos).2
        have hm_mono : hankelEdgeM (3 * τj / 2) ≤ hankelEdgeM |τ| :=
          hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (by positivity)) (mem_Ici.2 (abs_nonneg _)) hτ32
        have hmin0 : 0 ≤ 5 / 26 * min (hankelEdgeM τj) 1 := by
          rw [hmL]; exact mul_nonneg (by norm_num) (le_min hLj_pos.le zero_le_one)
        have hexp_le1 : Real.exp (c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re + c * σ * Lj) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          have hle0 : (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re + σ * Lj ≤ 0 := by
            rw [hmL] at hS0
            have h1 : 0 ≤ hankelEdgeM |τ| - Lj := by linarith only [hm_mono, hdel, hmin0, hmL]
            nlinarith only [hS0, hσ_pos, h1]
          nlinarith only [hle0, hc0]
        rw [norm_mul, Complex.norm_exp,
          show ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ)).re = c * σ * Lj by
            simp [Complex.mul_re, Complex.mul_im] ]
        have hbnd := hankelHhat_bound hc32 hf hε hσ.1 (hσ.2.trans hsj_4) τ
        calc ‖hankelHhat c f ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ * Real.exp (c * σ * Lj)
            ≤ (3 * hankelMass c f * Real.exp (c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re)) *
                Real.exp (c * σ * Lj) := mul_le_mul_of_nonneg_right hbnd (Real.exp_pos _).le
          _ = 3 * hankelMass c f * Real.exp (c * (stripS0Tilde ((σ : ℂ) + (τ : ℂ) * Complex.I)).re + c * σ * Lj) := by
              rw [mul_assoc (3 * hankelMass c f), ← Real.exp_add]
          _ ≤ 3 * hankelMass c f * 1 := mul_le_mul_of_nonneg_left hexp_le1 (by positivity)
          _ = 3 * hankelMass c f := mul_one _
  have hB0_le : ‖boasB0 Lj u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      C_D * M_tot_w * c ^ (5 - 500 / 21 : ℝ) := by
    set w : ℝ → ℂ := fun L => ((nw L : ℝ) : ℂ) * Complex.exp ((c * σ * (L - Lj) : ℝ) : ℂ)
    set θ : ℝ → ℝ := fun L => (k : ℝ) * boasX c ε L + c * τ * L
    have hsplit : boasB0 Lj u c a b ((σ : ℂ) + (τ : ℂ) * Complex.I) =
        Complex.exp (-(Complex.I * ((c * τ * Lj : ℝ) : ℂ))) *
          ∫ L in a..b, w L * Complex.exp (Complex.I * (θ L : ℂ)) := by
      unfold boasB0
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun L _ => ?_
      simp only [w, θ, u]
      have hexp : Complex.exp ((c : ℂ) * ((σ : ℂ) + (τ : ℂ) * Complex.I) * ((L - Lj : ℝ) : ℂ)) =
          Complex.exp (-(Complex.I * ((c * τ * Lj : ℝ) : ℂ))) *
            (Complex.exp ((c * σ * (L - Lj) : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * τ * L : ℝ) : ℂ))) := by
        rw [← Complex.exp_add, ← Complex.exp_add]
        congr 1; push_cast; ring
      have hexp2 : Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) *
          Complex.exp (Complex.I * ((c * τ * L : ℝ) : ℂ)) =
          Complex.exp (Complex.I * (((k : ℝ) * boasX c ε L + c * τ * L : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [hexp]
      calc ((nw L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) *
            (Complex.exp (-(Complex.I * ((c * τ * Lj : ℝ) : ℂ))) *
              (Complex.exp ((c * σ * (L - Lj) : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * τ * L : ℝ) : ℂ))))
          = Complex.exp (-(Complex.I * ((c * τ * Lj : ℝ) : ℂ))) *
              (((nw L : ℝ) : ℂ) * Complex.exp ((c * σ * (L - Lj) : ℝ) : ℂ) *
                (Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) * Complex.exp (Complex.I * ((c * τ * L : ℝ) : ℂ)))) := by ring
        _ = _ := by rw [hexp2]
    rw [hsplit, norm_mul,
      show -(Complex.I * ((c * τ * Lj : ℝ) : ℂ)) = ((-(c * τ * Lj) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    set μ : ℝ := 0.015 * (k : ℝ) * c * τj
    have hμ_pos : 0 < μ := by positivity
    set E : ℝ := c ^ (5 / 6 : ℝ)
    have hcs_bd : 0 ≤ c * σ ∧ c * σ ≤ E := by
      refine ⟨mul_nonneg hc0.le hσ.1, ?_⟩
      calc c * σ ≤ c * sj := mul_le_mul_of_nonneg_left hσ.2 hc0.le
        _ ≤ c * (325 * Real.log c / (c * ℓj)) := mul_le_mul_of_nonneg_left hsj_log hc0.le
        _ = 325 * Real.log c / ℓj := by field_simp [hc0.ne', hℓ0.ne']
        _ ≤ 325 * Real.log c / (κ_min * c ^ (-(2 / 21 : ℝ))) :=
            div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (Real.log_nonneg hc1.le))
              (mul_pos hκmin_pos (Real.rpow_pos_of_pos hc0 _)) hℓ_lb
        _ ≤ E := hcs_le
    have hMe_bd : ∀ L ∈ Icc a b, Real.exp (c * σ * (L - Lj)) ≤ c ^ (4 : ℝ) := by
      intro L hL
      have hLdiff : L - Lj ≤ ℓj / 100 := by linarith only [(hsub_win L (hsub_ab hL)).2.2.2]
      have hle_log : c * σ * (L - Lj) ≤ 4 * Real.log c := by
        have h1 : c * σ * (L - Lj) ≤ c * σ * (ℓj / 100) := mul_le_mul_of_nonneg_left hLdiff hcs_bd.1
        have h2 : c * σ * (ℓj / 100) ≤ c * sj * (ℓj / 100) := by gcongr; exact hσ.2
        have h3 : c * sj * (ℓj / 100) ≤ c * (325 * Real.log c / (c * ℓj)) * (ℓj / 100) := by gcongr
        have h4 : c * (325 * Real.log c / (c * ℓj)) * (ℓj / 100) = 3.25 * Real.log c := by
          field_simp [hc0.ne', hℓ0.ne']; norm_num
        linarith only [h1, h2, h3, h4, Real.log_nonneg hc1.le]
      calc Real.exp (c * σ * (L - Lj)) ≤ Real.exp (4 * Real.log c) := Real.exp_le_exp.2 hle_log
        _ = Real.exp (Real.log c * 4) := by ring_nf
        _ = c ^ (4 : ℝ) := by rw [← Real.rpow_def_of_pos hc0]
    have hamp := osc_amplitude_deriv_bound 200 hCm0 hnw_cd hc56_ge1 hcs_bd.1 hcs_bd.2
      (fun m _ L => hnw_drv m L) (Real.rpow_nonneg hc0.le _) hMe_bd
    rw [← hMtot_eq] at hamp
    have hw_supp : ∀ L ∉ Icc a' b', w L = 0 := fun L hL => by simp [w, hnw_supp L hL]
    have hθ_cd : ContDiffOn ℝ ((200 : ℕ) + 1) θ (Ioo a₀ b₀) := by
      have hsub0 : Ioo a₀ b₀ ⊆ Ioi (0 : ℝ) := fun L hL => (hsub_win L hL).2.1
      have hXcd := (boasX_contDiffOn hε 201).mono hsub0
      exact ((contDiffOn_const.mul hXcd).add (contDiffOn_const.mul contDiffOn_id)).of_le (by norm_num)
    have hθ_lb : ∀ L ∈ Ioo a₀ b₀, μ ≤ |deriv θ L| := by
      intro L hL
      obtain ⟨hLlv, _, hLIcc⟩ := hsub_win L hL
      have hX_drv := hx_drv L hLlv
      have htau_w := hwin L hLIcc
      have hθ_hd : HasDerivAt θ ((k : ℝ) * deriv (boasX c ε) L + c * τ) L :=
        ((hX_drv.2.1.const_mul (k : ℝ)).add ((hasDerivAt_id L).const_mul (c * τ))).congr_deriv (by simp)
      rw [hθ_hd.deriv]
      have htau_lb : -(3 / 2 * τj) ≤ τ := by linarith only [hτ.1, hTj_def]
      have hlow : μ ≤ (k : ℝ) * deriv (boasX c ε) L + c * τ := by
        have h1 : (0.85 : ℝ) * c * (0.9 * τj) ≤ deriv (boasX c ε) L := by
          nlinarith only [hX_drv.2.2.1, htau_w.1, hc0]
        have h2 : (k : ℝ) * ((0.85 : ℝ) * c * (0.9 * τj)) ≤ (k : ℝ) * deriv (boasX c ε) L :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h3 : (k : ℝ) * (0.765 * c * τj) + c * -(3 / 2 * τj) = ((0.765 * k - 1.5) * c * τj) := by ring
        have h4 : (0.015 : ℝ) * k ≤ 0.765 * k - 1.5 := by linarith only [hk_real2]
        have h5 : (0.015 : ℝ) * k * c * τj ≤ (0.765 * k - 1.5) * c * τj := by
          have := mul_le_mul_of_nonneg_right h4 (mul_nonneg hc0.le hτ_pos.le)
          linarith only [this]
        dsimp only [μ]
        linarith only [h2, htau_lb, h3, h5]
      exact hlow.trans (le_abs_self _)
    have hθ_sym : ∀ j_i : ℕ, 1 ≤ j_i → j_i ≤ 200 → ∀ L ∈ Ioo a₀ b₀,
        |iteratedDeriv (j_i + 1) θ L| ≤ Bθ j_i * |deriv θ L| * E ^ j_i := by
      intro j_i hj1 hj200 L hL
      obtain ⟨hLlv, hLpos, hLIcc⟩ := hsub_win L hL
      have hXcd_at : ContDiffAt ℝ (j_i + 1) (boasX c ε) L :=
        ((boasX_contDiffOn hε (j_i + 1)).contDiffAt (Ioi_mem_nhds hLpos)).of_le le_rfl
      have hlcd_at : ContDiffAt ℝ (j_i + 1) (fun y : ℝ => c * τ * y) L := by fun_prop
      have hfun_eq : θ = fun y => (k : ℝ) * boasX c ε y + c * τ * y := rfl
      have hsplit_d : iteratedDeriv (j_i + 1) θ L = (k : ℝ) * iteratedDeriv (j_i + 1) (boasX c ε) L := by
        rw [hfun_eq, iteratedDeriv_fun_add ((contDiffAt_const (c := (k : ℝ))).mul hXcd_at) hlcd_at,
          iteratedDeriv_linear_zero hj1 (c * τ) L, add_zero, iteratedDeriv_const_mul_field]
      rw [hsplit_d, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      have hs := hx_sym (j_i + 1) (Nat.succ_pos j_i) L hLlv
      rw [Nat.add_sub_cancel] at hs
      have hτ_hi := (hwin L hLIcc).2
      have hlam_bd : lamL L ≤ E := by
        unfold lamL
        exact (max_le_max_left 1 (inv_anti₀ (by linarith only [hL0_pos]) hLlv)).trans hlam_le
      have hlam_pow : lamL L ^ j_i ≤ E ^ j_i := pow_le_pow_left₀ (lamL_nonneg L) hlam_bd j_i
      have hμL := hθ_lb L hL
      have hkc_le : (k : ℝ) * c * tau0 L ≤ (1.1 / 0.015) * |deriv θ L| := by
        have h1 : (k : ℝ) * c * tau0 L ≤ (k : ℝ) * c * (1.1 * τj) :=
          mul_le_mul_of_nonneg_left hτ_hi (by positivity)
        have h2 : (k : ℝ) * c * (1.1 * τj) = (1.1 / 0.015) * μ := by simp only [μ]; ring
        linarith only [h1, h2, hμL]
      calc (k : ℝ) * |iteratedDeriv (j_i + 1) (boasX c ε) L|
          ≤ (k : ℝ) * (C_X (j_i + 1) (Nat.succ_pos j_i) * c * tau0 L * lamL L ^ j_i) :=
              mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)
        _ = C_X (j_i + 1) (Nat.succ_pos j_i) * ((k : ℝ) * c * tau0 L) * lamL L ^ j_i := by ring
        _ ≤ C_X (j_i + 1) (Nat.succ_pos j_i) * ((1.1 / 0.015) * |deriv θ L|) * E ^ j_i :=
              mul_le_mul
                (mul_le_mul_of_nonneg_left hkc_le (hCX_nn _ _))
                hlam_pow (pow_nonneg (lamL_nonneg L) j_i) (mul_nonneg (hCX_nn _ _) (by positivity))
        _ = Bθ j_i * |deriv θ L| * E ^ j_i := by rw [hBθ_eq]; ring
    have hibp := hibp_r (a₀ := a₀) (a := a) (a' := a') (b' := b') (b := b) (b₀ := b₀)
      (μ := μ) (Λ := E) (M_u := M_tot_w * c ^ (4 : ℝ)) (E := E) (θ := θ) (u := w)
      hμ_pos hc56_ge1 le_rfl (by positivity) haa haa' ha'b' hb'b hbb₀ hθ_cd hθ_lb hθ_sym
      hamp.1 hw_supp hamp.2
    have hμ_inv : μ⁻¹ ≤ (0.03 * κ_min)⁻¹ * c ^ (-(20 / 21 : ℝ)) := by
      have hc20 : c ^ (20 / 21 : ℝ) * c ^ (-(20 / 21 : ℝ)) = 1 := by
        rw [← Real.rpow_add hc0]; norm_num
      have hc_tau_eq : c * c ^ (-(1 / 21 : ℝ)) = c ^ (20 / 21 : ℝ) := by
        nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
      have hμ_lb : 0.03 * κ_min * c ^ (20 / 21 : ℝ) ≤ μ := by
        calc 0.03 * κ_min * c ^ (20 / 21 : ℝ) = 0.015 * 2 * c * (κ_min * c ^ (-(1 / 21 : ℝ))) := by
              rw [← hc_tau_eq]; ring
          _ ≤ 0.015 * (k : ℝ) * c * τj := by gcongr
      rw [inv_eq_one_div, div_le_iff₀' hμ_pos]
      calc 1 = (0.03 * κ_min)⁻¹ * (0.03 * κ_min) * (c ^ (-(20 / 21 : ℝ)) * c ^ (20 / 21 : ℝ)) := by
            rw [inv_mul_cancel₀ (by positivity), one_mul, mul_comm (c ^ (-(20 / 21 : ℝ))), hc20]
        _ = (0.03 * κ_min * c ^ (20 / 21 : ℝ)) * ((0.03 * κ_min)⁻¹ * c ^ (-(20 / 21 : ℝ))) := by ring
        _ ≤ μ * ((0.03 * κ_min)⁻¹ * c ^ (-(20 / 21 : ℝ))) := by gcongr
    have hpow_200 : μ⁻¹ ^ 200 * E ^ 200 ≤ c ^ (1 - 500 / 21 : ℝ) := by
      have h1 : μ⁻¹ ^ 200 ≤ ((0.03 * κ_min)⁻¹ ^ 200) * (c ^ (-(20 / 21 : ℝ))) ^ 200 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (inv_nonneg.2 hμ_pos.le) hμ_inv 200
      have h2 : (c ^ (-(20 / 21 : ℝ))) ^ 200 * (c ^ (5 / 6 : ℝ)) ^ 200 = c ^ (-(500 / 21) : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le, ← Real.rpow_mul hc0.le,
          ← Real.rpow_add hc0]
        norm_num
      calc μ⁻¹ ^ 200 * E ^ 200 ≤ ((0.03 * κ_min)⁻¹ ^ 200 * (c ^ (-(20 / 21 : ℝ))) ^ 200) * (c ^ (5 / 6 : ℝ)) ^ 200 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = ((0.03 * κ_min)⁻¹ ^ 200) * c ^ (-(500 / 21) : ℝ) := by rw [mul_assoc, h2]
        _ ≤ c * c ^ (-(500 / 21) : ℝ) := by gcongr
        _ = c ^ (1 - 500 / 21 : ℝ) := by
            nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    refine hibp.trans ?_
    calc (b - a) * C_D * μ⁻¹ ^ 200 * (M_tot_w * c ^ (4 : ℝ)) * E ^ 200
        = (b - a) * (C_D * M_tot_w * c ^ (4 : ℝ) * (μ⁻¹ ^ 200 * E ^ 200)) := by ring
      _ ≤ 1 * (C_D * M_tot_w * c ^ (4 : ℝ) * c ^ (1 - 500 / 21 : ℝ)) := by
          apply mul_le_mul hba_le1 (mul_le_mul_of_nonneg_left hpow_200 (by positivity))
            (by positivity) zero_le_one
      _ = C_D * M_tot_w * c ^ (5 - 500 / 21 : ℝ) := by
          rw [one_mul, mul_assoc (C_D * M_tot_w), ← Real.rpow_add hc0]; congr 2; norm_num
  rw [norm_mul]
  exact mul_le_mul hH_le hB0_le (norm_nonneg _) (by positivity) |>.trans (le_of_eq (by ring))

/-- Standalone helper for `‖boasB0 Lj u c a b (sj + i τ)‖ ≤ C_v2 * c^12 / τ^2` (`|τ| ≥ T_j`),
isolated from `boas_harmonic_bound` so `M_tot_w` (`range 201`) never enters its context. -/
private lemma vertical_tail_ibp_bound
    {c_x κ_min c ε : ℝ} {nw : ℝ → ℝ} {C_m : ℕ → ℝ} {CX2 M_tot_2 C_v2 : ℝ}
    {Lj ℓj τj a₀ a a' b' b b₀ sj τ : ℝ} {k : ℕ}
    (hc1 : 1 < c) (hlog2 : 2 ≤ Real.log c) (hε : ε = 1 ∨ ε = -1) (hc_x : c_x ≤ c)
    (hk_c2 : (k : ℝ) ≤ c ^ 2 + 1) (hκmin_pos : 0 < κ_min) (hℓ0 : 0 < ℓj)
    (hℓ_lb : κ_min * c ^ (-(2 / 21 : ℝ)) ≤ ℓj) (hτj_le_c : τj ≤ c) (hL0_pos : 0 < ctLv0 c)
    (haa : a₀ < a) (haa' : a < a') (ha'b' : a' ≤ b') (hb'b : b' < b) (hbb₀ : b < b₀) (hba_le1 : b - a ≤ 1)
    (hsj_pos : 0 < sj) (hsj_log : sj ≤ 325 * Real.log c / (c * ℓj)) (hτne : τ ≠ 0)
    (hsub_win : ∀ L ∈ Ioo a₀ b₀, ctLv0 c / 4 ≤ L ∧ 0 < L ∧ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100))
    (hwin : ∀ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100), tau0 L ≤ 1.1 * τj)
    (hnw_cd : ∀ n : ℕ, ContDiff ℝ n nw) (hnw_supp : ∀ L ∉ Icc a' b', nw L = 0)
    (hCm0 : ∀ r : ℕ, 0 ≤ C_m r) (hnw_drv : ∀ r : ℕ, ∀ L : ℝ, |iteratedDeriv r nw L| ≤ C_m r * (c ^ (5 / 6 : ℝ)) ^ r)
    (hMtot2_eq : M_tot_2 = ∑ m' ∈ Finset.range 3, ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_m i)
    (hCX2_nn : 0 ≤ CX2) (hCv2_eq : C_v2 = M_tot_2 * (16 + 3 * CX2))
    (hx_drv : ∀ L, ctLv0 c / 4 ≤ L →
      0 < L ∧ HasDerivAt (boasX c ε) (deriv (boasX c ε) L) L ∧
      0.85 * c * tau0 L ≤ deriv (boasX c ε) L ∧ deriv (boasX c ε) L ≤ 1.15 * c * tau0 L)
    (hx_sym2 : ∀ L, ctLv0 c / 4 ≤ L → |iteratedDeriv 2 (boasX c ε) L| ≤ CX2 * c * tau0 L * lamL L ^ (2 - 1))
    (hlam_le : max 1 ((ctLv0 c / 4)⁻¹) ≤ c ^ (5 / 6 : ℝ))
    (hcs_le : 325 * Real.log c / (κ_min * c ^ (-(2 / 21 : ℝ))) ≤ c ^ (5 / 6 : ℝ))
    (hu_cd : ContDiff ℝ 2 fun L => ((nw L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))) :
    let u : ℝ → ℂ := fun L => ((nw L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))
    ‖boasB0 Lj u c a b ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ C_v2 * c ^ (12 : ℝ) * (τ ^ 2)⁻¹ := by
  intro u
  have hc0 : 0 < c := zero_lt_one.trans hc1
  have hsub_ab : Icc a b ⊆ Ioo a₀ b₀ := fun L hL => ⟨lt_of_lt_of_le haa hL.1, lt_of_le_of_lt hL.2 hbb₀⟩
  have hc56_ge1 : 1 ≤ c ^ (5 / 6 : ℝ) := Real.one_le_rpow hc1.le (by norm_num)
  have hMtot2_nn : 0 ≤ M_tot_2 := by
    rw [hMtot2_eq]
    exact Finset.sum_nonneg fun m' _ => Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCm0 i)
  set A : ℝ → ℂ := fun L => ((nw L : ℝ) : ℂ) * Complex.exp ((c * sj * (L - Lj) : ℝ) : ℂ)
  set B : ℝ → ℂ := fun L => Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))
  set w : ℝ → ℂ := fun L => u L * Complex.exp ((c * sj * (L - Lj) : ℝ) : ℂ)
  have hw_split : boasB0 Lj u c a b ((sj : ℂ) + (τ : ℂ) * Complex.I) =
      Complex.exp (-(Complex.I * ((c * τ * Lj : ℝ) : ℂ))) *
        ∫ L in a..b, w L * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (L : ℂ)) := by
    unfold boasB0
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun L _ => ?_
    simp only [w]
    have hexp : Complex.exp ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * ((L - Lj : ℝ) : ℂ)) =
        Complex.exp (-(Complex.I * ((c * τ * Lj : ℝ) : ℂ))) *
          (Complex.exp ((c * sj * (L - Lj) : ℝ) : ℂ) * Complex.exp (Complex.I * ((c * τ : ℝ) : ℂ) * (L : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [hexp]; ring
  rw [hw_split, norm_mul,
    show -(Complex.I * ((c * τ * Lj : ℝ) : ℂ)) = ((-(c * τ * Lj) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  have hcd_exp : ContDiff ℝ 2 (fun L : ℝ => Complex.exp ((c * sj * (L - Lj) : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.contDiff.comp ((contDiff_const (c := c * sj)).mul (contDiff_id.sub contDiff_const))).cexp
  have hcd_w : ContDiff ℝ 2 w := hu_cd.mul hcd_exp
  have hsupp_w : ∀ L ∉ Icc a' b', w L = 0 := fun L hL => by simp [w, u, hnw_supp L hL]
  have hcsj_bd : 0 ≤ c * sj ∧ c * sj ≤ c ^ (5 / 6 : ℝ) := by
    refine ⟨mul_nonneg hc0.le hsj_pos.le, ?_⟩
    calc c * sj ≤ c * (325 * Real.log c / (c * ℓj)) := mul_le_mul_of_nonneg_left hsj_log hc0.le
      _ = 325 * Real.log c / ℓj := by field_simp [hc0.ne', hℓ0.ne']
      _ ≤ 325 * Real.log c / (κ_min * c ^ (-(2 / 21 : ℝ))) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hκmin_pos (Real.rpow_pos_of_pos hc0 _)) hℓ_lb
      _ ≤ c ^ (5 / 6 : ℝ) := hcs_le
  have hMe_bd : ∀ L ∈ Icc a b, Real.exp (c * sj * (L - Lj)) ≤ c ^ (4 : ℝ) := by
    intro L hL
    have hLdiff : L - Lj ≤ ℓj / 100 := by linarith only [(hsub_win L (hsub_ab hL)).2.2.2]
    have hle_log : c * sj * (L - Lj) ≤ 4 * Real.log c := by
      have h1 : c * sj * (L - Lj) ≤ c * sj * (ℓj / 100) := mul_le_mul_of_nonneg_left hLdiff hcsj_bd.1
      have h2 : c * sj * (ℓj / 100) ≤ c * (325 * Real.log c / (c * ℓj)) * (ℓj / 100) := by gcongr
      have h3 : c * (325 * Real.log c / (c * ℓj)) * (ℓj / 100) = 3.25 * Real.log c := by
        field_simp [hc0.ne', hℓ0.ne']; norm_num
      linarith only [h1, h2, h3, hlog2]
    calc Real.exp (c * sj * (L - Lj)) ≤ Real.exp (4 * Real.log c) := Real.exp_le_exp.2 hle_log
      _ = Real.exp (Real.log c * 4) := by ring_nf
      _ = c ^ (4 : ℝ) := by rw [← Real.rpow_def_of_pos hc0]
  have hamp := osc_amplitude_deriv_bound 2 hCm0 hnw_cd hc56_ge1 hcsj_bd.1 hcsj_bd.2
    (fun m _ L => hnw_drv m L) (Real.rpow_nonneg hc0.le _) hMe_bd
  rw [← hMtot2_eq] at hamp
  have h2w_bd : ∀ L ∈ Icc a b, ‖iteratedDeriv 2 w L‖ ≤ C_v2 * c ^ (14 : ℝ) := by
    intro L hLI
    have hLo : L ∈ Ioo a₀ b₀ := hsub_ab hLI
    obtain ⟨hLlv, hLpos, hLIcc⟩ := hsub_win L hLo
    have hX_drv := hx_drv L hLlv
    have hτ_hi := hwin L hLIcc
    have hX_cdOn : ContDiffOn ℝ 2 (boasX c ε) (Ioi 0) := boasX_contDiffOn hε 2
    have hX_cd2 : ContDiffAt ℝ 2 (boasX c ε) L := hX_cdOn.contDiffAt (Ioi_mem_nhds hLpos)
    have hX2 : HasDerivAt (deriv (boasX c ε)) (iteratedDeriv 2 (boasX c ε) L) L := by
      have hs : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) (boasX c ε) (Ioi 0) := hX_cdOn
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi] at hs
      have hd := ((hs.2.2.differentiableOn one_ne_zero L hLpos).differentiableAt
        (isOpen_Ioi.mem_nhds hLpos)).hasDerivAt
      have h2e : deriv (deriv (boasX c ε)) L = iteratedDeriv 2 (boasX c ε) L := by
        rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
      rwa [h2e] at hd
    have hB1 : ∀ y ∈ Ioo a₀ b₀, HasDerivAt B (Complex.I * ((k : ℝ) * deriv (boasX c ε) y : ℝ) * B y) y := by
      intro y hy
      have hXy := (hx_drv y (hsub_win y hy).1).2.1
      have h := ((hXy.const_mul (k : ℝ)).ofReal_comp.const_mul Complex.I).cexp
      exact h.congr_deriv (by simp only [B]; push_cast; ring)
    have hB1_eq : deriv B =ᶠ[𝓝 L] fun y => Complex.I * ((k : ℝ) * deriv (boasX c ε) y : ℝ) * B y := by
      filter_upwards [isOpen_Ioo.mem_nhds hLo] with y hy
      exact (hB1 y hy).deriv
    have hderivB : HasDerivAt (fun y => Complex.I * ((k : ℝ) * deriv (boasX c ε) y : ℝ) * B y)
        ((Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ) -
          (((k : ℝ) * deriv (boasX c ε) L : ℝ) : ℂ) ^ 2) * B L) L := by
      have hA' : HasDerivAt (fun y => Complex.I * ((k : ℝ) * deriv (boasX c ε) y : ℝ))
          (Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ)) L := by
        have h := ((hX2.const_mul (k : ℝ)).ofReal_comp.const_mul Complex.I)
        exact h.congr_deriv (by push_cast; ring)
      have h1 := hA'.mul (hB1 L hLo)
      refine h1.congr_deriv ?_
      calc Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ) * B L +
            Complex.I * ((k : ℝ) * deriv (boasX c ε) L : ℝ) *
              (Complex.I * ((k : ℝ) * deriv (boasX c ε) L : ℝ) * B L)
          = (Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ) +
              Complex.I ^ 2 * (((k : ℝ) * deriv (boasX c ε) L : ℝ) : ℂ) ^ 2) * B L := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    have hB2_val : iteratedDeriv 2 B L =
        (Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ) -
          (((k : ℝ) * deriv (boasX c ε) L : ℝ) : ℂ) ^ 2) * B L := by
      rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, hB1_eq.deriv_eq, hderivB.deriv]
    have hA_at : ContDiffAt ℝ 2 A L := (hamp.1.of_le le_rfl).contDiffAt
    have hB_at : ContDiffAt ℝ 2 B L :=
      ((contDiffAt_const (c := Complex.I)).mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp L ((contDiffAt_const (c := (k : ℝ))).mul hX_cd2))).cexp
    have hw_eq : w = fun y => A y * B y := by ext y; simp only [w, u, A, B]; ring
    rw [hw_eq, iteratedDeriv_fun_mul hA_at hB_at]
    have hc56_le_c : c ^ (5 / 6 : ℝ) ≤ c :=
      (Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num : (5 / 6 : ℝ) ≤ 1)).trans_eq (Real.rpow_one c)
    have hc56_sq : (c ^ (5 / 6 : ℝ)) ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (by positivity) hc56_le_c 2
    have hA0 : ‖A L‖ ≤ M_tot_2 * c ^ (6 : ℝ) := by
      have := hamp.2 0 (by norm_num) L hLI
      simp only [iteratedDeriv_zero, pow_zero, mul_one] at this
      exact this.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)) hMtot2_nn)
    have hA1 : ‖iteratedDeriv 1 A L‖ ≤ M_tot_2 * c ^ (6 : ℝ) := by
      have := hamp.2 1 (by norm_num) L hLI
      simp only [pow_one] at this
      have hc46 : c ^ (4 : ℝ) * c ≤ c ^ (6 : ℝ) := by
        calc c ^ (4 : ℝ) * c = c ^ (5 : ℝ) := by
              nth_rw 2 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
          _ ≤ c ^ (6 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
      calc ‖iteratedDeriv 1 A L‖ ≤ M_tot_2 * c ^ (4 : ℝ) * c ^ (5 / 6 : ℝ) := this
        _ ≤ M_tot_2 * c ^ (4 : ℝ) * c := by gcongr
        _ = M_tot_2 * (c ^ (4 : ℝ) * c) := by ring
        _ ≤ M_tot_2 * c ^ (6 : ℝ) := mul_le_mul_of_nonneg_left hc46 hMtot2_nn
    have hA2 : ‖iteratedDeriv 2 A L‖ ≤ M_tot_2 * c ^ (6 : ℝ) := by
      have := hamp.2 2 le_rfl L hLI
      calc ‖iteratedDeriv 2 A L‖ ≤ M_tot_2 * c ^ (4 : ℝ) * (c ^ (5 / 6 : ℝ)) ^ 2 := this
        _ ≤ M_tot_2 * c ^ (4 : ℝ) * c ^ 2 := by gcongr
        _ = M_tot_2 * c ^ (6 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_natCast c 2, ← Real.rpow_add hc0]; norm_num
    have hB0 : ‖B L‖ = 1 := by
      simp only [B]
      rw [show Complex.I * ((k : ℝ) * boasX c ε L : ℝ) = (((k : ℝ) * boasX c ε L : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    have hτL_pos : 0 < tau0 L := tau0_pos hLpos
    have hkd_bd : |(k : ℝ) * deriv (boasX c ε) L| ≤ 3 * c ^ (4 : ℝ) := by
      have h1 : 0 ≤ deriv (boasX c ε) L := le_trans (mul_nonneg (mul_nonneg (by norm_num) hc0.le) hτL_pos.le) hX_drv.2.2.1
      have h2 : deriv (boasX c ε) L ≤ 1.15 * c * (1.1 * τj) := by nlinarith only [hX_drv.2.2.2, hτ_hi, hc0]
      have h3 : (k : ℝ) ≤ 2 * c ^ 2 := by nlinarith only [hk_c2, hc1]
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) h1)]
      calc (k : ℝ) * deriv (boasX c ε) L ≤ (2 * c ^ 2) * (1.15 * c * (1.1 * c)) := by
            gcongr; exact h2.trans (by gcongr)
        _ = 2.53 * c ^ 4 := by ring
        _ ≤ 3 * c ^ (4 : ℝ) := by rw [Real.rpow_natCast]; nlinarith only [pow_pos hc0 4]
    have hB1n : ‖iteratedDeriv 1 B L‖ ≤ 3 * c ^ (4 : ℝ) := by
      rw [iteratedDeriv_one, hB1_eq.deriv_eq, (hB1 L hLo).deriv, norm_mul, hB0, mul_one,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact hkd_bd
    have hB2n : ‖iteratedDeriv 2 B L‖ ≤ (3 * CX2 + 9) * c ^ (8 : ℝ) := by
      rw [hB2_val, norm_mul, hB0, mul_one]
      have hx2 := hx_sym2 L hLlv
      have hlam_c : lamL L ≤ c := (max_le_max_left 1 (inv_anti₀ (by linarith only [hL0_pos]) hLlv)).trans
        (hlam_le.trans hc56_le_c)
      have hkx2 : |(k : ℝ) * iteratedDeriv 2 (boasX c ε) L| ≤ 3 * CX2 * c ^ (8 : ℝ) := by
        have hk2c : (k : ℝ) ≤ 2 * c ^ 2 := by nlinarith only [hk_c2, hc1]
        have hc58 : c ^ 2 * (c * c * c) = c ^ (5 : ℝ) := by
          rw [← Real.rpow_natCast c 2, ← Real.rpow_one c]
          rw [← Real.rpow_add hc0, ← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
        have hc5_le8 : c ^ (5 : ℝ) ≤ c ^ (8 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
        calc (k : ℝ) * |iteratedDeriv 2 (boasX c ε) L|
            ≤ (2 * c ^ 2) * (CX2 * c * tau0 L * lamL L ^ 1) := by gcongr; exact hx2
          _ ≤ (2 * c ^ 2) * (CX2 * c * (1.1 * c) * c) := by
              rw [pow_one]
              gcongr
              exact (mul_le_mul_of_nonneg_left hτ_hi (by norm_num)).trans (by gcongr)
          _ = 2.2 * CX2 * (c ^ 2 * (c * c * c)) := by ring
          _ ≤ 3 * CX2 * c ^ (8 : ℝ) := by rw [hc58]; gcongr; norm_num
      calc ‖Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ) -
              (((k : ℝ) * deriv (boasX c ε) L : ℝ) : ℂ) ^ 2‖
          ≤ ‖Complex.I * ((k : ℝ) * iteratedDeriv 2 (boasX c ε) L : ℝ)‖ +
              ‖(((k : ℝ) * deriv (boasX c ε) L : ℝ) : ℂ) ^ 2‖ := norm_sub_le _ _
        _ ≤ 3 * CX2 * c ^ (8 : ℝ) + (3 * c ^ (4 : ℝ)) ^ 2 := by
            gcongr
            · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hkx2
            · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) hkd_bd 2
        _ = (3 * CX2 + 9) * c ^ (8 : ℝ) := by
            have : (c ^ (4 : ℝ)) ^ 2 = c ^ (8 : ℝ) := by
              rw [← Real.rpow_natCast (c ^ (4 : ℝ)) 2, ← Real.rpow_mul hc0.le]; norm_num
            rw [mul_pow, this]; ring
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, Nat.choose_zero_right,
      Nat.choose_self, Nat.cast_one, one_smul, Nat.sub_zero, Nat.sub_self, show (2 : ℕ) - 1 = 1 by rfl,
      show Nat.choose 2 1 = 2 by rfl, Nat.cast_ofNat]
    have htr := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    refine htr.trans ?_
    rw [norm_smul, Real.norm_of_nonneg (by norm_num), norm_mul, norm_mul, norm_mul]
    have hc68 : c ^ (6 : ℝ) * c ^ (8 : ℝ) = c ^ (14 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
    have hc64 : c ^ (6 : ℝ) * c ^ (4 : ℝ) ≤ c ^ (14 : ℝ) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
    have hc6_14 : c ^ (6 : ℝ) ≤ c ^ (14 : ℝ) := Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
    calc ‖A L‖ * ‖iteratedDeriv 2 B L‖ + 2 * (‖iteratedDeriv 1 A L‖ * ‖iteratedDeriv 1 B L‖) +
          ‖iteratedDeriv 2 A L‖ * ‖B L‖
        ≤ (M_tot_2 * c ^ (6 : ℝ)) * ((3 * CX2 + 9) * c ^ (8 : ℝ)) +
            2 * ((M_tot_2 * c ^ (6 : ℝ)) * (3 * c ^ (4 : ℝ))) +
            (M_tot_2 * c ^ (6 : ℝ)) * 1 := by rw [hB0]; gcongr
      _ ≤ M_tot_2 * (3 * CX2 + 9) * c ^ (14 : ℝ) + 6 * M_tot_2 * c ^ (14 : ℝ) + M_tot_2 * c ^ (14 : ℝ) := by
          have h1 : M_tot_2 * c ^ (6 : ℝ) * ((3 * CX2 + 9) * c ^ (8 : ℝ)) =
              M_tot_2 * (3 * CX2 + 9) * c ^ (14 : ℝ) := by rw [← hc68]; ring
          have h2 : 2 * (M_tot_2 * c ^ (6 : ℝ) * (3 * c ^ (4 : ℝ))) ≤ 6 * M_tot_2 * c ^ (14 : ℝ) := by
            calc _ = 6 * M_tot_2 * (c ^ (6 : ℝ) * c ^ (4 : ℝ)) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hc64 (by positivity)
          have h3 : M_tot_2 * c ^ (6 : ℝ) * 1 ≤ M_tot_2 * c ^ (14 : ℝ) := by
            rw [mul_one]; exact mul_le_mul_of_nonneg_left hc6_14 hMtot2_nn
          linarith only [h1, h2, h3]
      _ = C_v2 * c ^ (14 : ℝ) := by rw [hCv2_eq]; ring
  have hct_ne : c * τ ≠ 0 := mul_ne_zero hc0.ne' hτne
  have hibp := osc_ibp_linear_two hct_ne haa' ha'b' hb'b hcd_w hsupp_w h2w_bd
  refine hibp.trans ?_
  have hc12 : c ^ (14 : ℝ) / c ^ 2 = c ^ (12 : ℝ) := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_sub hc0]; norm_num
  calc (b - a) * (C_v2 * c ^ (14 : ℝ)) / (c * τ) ^ 2
      = (b - a) * (C_v2 * (c ^ (14 : ℝ) / c ^ 2) * (τ ^ 2)⁻¹) := by ring
    _ ≤ 1 * (C_v2 * c ^ (12 : ℝ) * (τ ^ 2)⁻¹) := by
        rw [hc12]; exact mul_le_mul hba_le1 le_rfl (by positivity) zero_le_one
    _ = C_v2 * c ^ (12 : ℝ) * (τ ^ 2)⁻¹ := one_mul _

/-- **Exact-phase harmonic estimate** (`ct:boas` Steps 3–5): for `c₁ ∈ (0, c₁₀]` and `c ≥ c₀`,
for every near block `j < N` and harmonic `2 ≤ k ≤ ⌈c²⌉`,
`|∫ nearWeight ε c R j L * hankelHL c f L * cos (k * (boasX c ε L + π/2)) dL| ≤ C_har M[f] c^{-14}`. -/
theorem boas_harmonic_bound : ∃ c₁₀ : ℝ, 0 < c₁₀ ∧
    ∀ c₁ : ℝ, 0 < c₁ → c₁ ≤ c₁₀ → ∃ c₀ C_har : ℝ, Real.exp 2 ≤ c₀ ∧ 0 ≤ C_har ∧
      ∀ {ε c R : ℝ} {f : ℝ → ℝ},
        (ε = 1 ∨ ε = -1) → c₀ ≤ c →
        c₁ ^ 2 * c ^ (2 / 3 : ℝ) ≤ R → R ≤ 4 * c₁ ^ 2 * c ^ (2 / 3 : ℝ) →
        IsHankelEigenfn c ε f →
        ∀ j ∈ Finset.range (partCount (ctLv0 c / 4) (nearB c)),
          ∀ k : ℕ, 2 ≤ k → k ≤ Nat.ceil (c ^ 2) →
            |∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| ≤
              C_har * hankelMass c f * c ^ (-(14 : ℝ)) := by
  obtain ⟨c₁₀, hc₁₀, hnw⟩ := exists_near_weights
  obtain ⟨c_x, hcx3, hx_drv, hx_sym⟩ := boasX_deriv_and_symbol
  obtain ⟨κ_L, hκL_pos, cL, hcL1, hLv0⟩ := ctLv0_facts
  choose C_X hCX_nn hx_sym using hx_sym
  let CX2 : ℝ := C_X 2 (by norm_num)
  let Bθ : ℕ → ℝ := fun i => (1.1 / 0.015) * C_X (i + 1) (Nat.succ_pos i)
  have hBθ0 : ∀ i, 0 ≤ Bθ i := fun i => by dsimp only [Bθ]; exact mul_nonneg (by positivity) (hCX_nn _ _)
  obtain ⟨C_D, hCD0, hibp_r⟩ := osc_ibp_r 200 Bθ hBθ0
  refine ⟨c₁₀, hc₁₀, fun c₁ hc₁ hle => ?_⟩
  obtain ⟨c_w, κ_min, hcw_e2, hκmin_pos, C_m, hCm0, hblocks⟩ := hnw c₁ hc₁ hle
  let M_tot_w : ℝ := ∑ m' ∈ Finset.range 201, ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_m i
  let M_tot_2 : ℝ := ∑ m' ∈ Finset.range 3, ∑ i ∈ Finset.range (m' + 1), (m'.choose i : ℝ) * C_m i
  have hMtotw_nn : 0 ≤ M_tot_w := Finset.sum_nonneg fun m' _ =>
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCm0 i)
  have hMtot2_nn : 0 ≤ M_tot_2 := Finset.sum_nonneg fun m' _ =>
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hCm0 i)
  have hev_lam : ∀ᶠ c : ℝ in atTop, max 1 ((ctLv0 c / 4)⁻¹) ≤ c ^ (5 / 6 : ℝ) := by
    have ht := tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 31 / 42)
    have hlim : Tendsto (fun c : ℝ => (5 / κ_L) * c ^ (-(31 / 42 : ℝ))) atTop (𝓝 0) := by
      simpa using ht.const_mul (5 / κ_L)
    filter_upwards [eventually_ge_atTop (max 1 cL), hlim.eventually (Iic_mem_nhds one_pos)] with c hc1 hc_lam
    have hc_pos : 0 < c := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hc1)
    have hc_L : cL ≤ c := le_trans (le_max_right _ _) hc1
    obtain ⟨hL0, _, _, hL_lb⟩ := hLv0 c hc_L
    have hc56 : 1 ≤ c ^ (5 / 6 : ℝ) := Real.one_le_rpow (le_trans (le_max_left _ _) hc1) (by norm_num)
    refine max_le hc56 ?_
    rw [inv_div, div_le_iff₀ hL0]
    have h56 : c ^ (5 / 6 : ℝ) * c ^ (-(2 / 21 : ℝ)) = c ^ (31 / 42 : ℝ) := by
      rw [← Real.rpow_add hc_pos]; norm_num
    have hpow_le : 5 / κ_L ≤ c ^ (31 / 42 : ℝ) := by
      calc 5 / κ_L = (5 / κ_L * c ^ (-(31 / 42 : ℝ))) * c ^ (31 / 42 : ℝ) := by
            rw [mul_assoc, ← Real.rpow_add hc_pos]; norm_num
        _ ≤ 1 * c ^ (31 / 42 : ℝ) := mul_le_mul_of_nonneg_right hc_lam (Real.rpow_nonneg hc_pos.le _)
        _ = c ^ (31 / 42 : ℝ) := one_mul _
    have hL_ge : (6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ)) ≤ ctLv0 c := by linarith only [hL_lb]
    calc 4 ≤ (6 / 5 : ℝ) * 5 := by norm_num
      _ ≤ (6 / 5 : ℝ) * κ_L * c ^ (31 / 42 : ℝ) := by
          rw [div_le_iff₀ hκL_pos] at hpow_le; nlinarith only [hpow_le]
      _ = ((6 / 5 : ℝ) * κ_L * c ^ (-(2 / 21 : ℝ))) * c ^ (5 / 6 : ℝ) := by rw [← h56]; ring
      _ ≤ ctLv0 c * c ^ (5 / 6 : ℝ) := mul_le_mul_of_nonneg_right hL_ge (Real.rpow_nonneg hc_pos.le _)
  have hev_cs : ∀ᶠ c : ℝ in atTop, 325 * Real.log c / (κ_min * c ^ (-(2 / 21 : ℝ))) ≤ c ^ (5 / 6 : ℝ) := by
    have h1 := isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 31 / 42)
    have hlim : Tendsto (fun c : ℝ => (325 / κ_min) * (Real.log c / c ^ (31 / 42 : ℝ))) atTop (𝓝 0) := by
      simpa using h1.tendsto_div_nhds_zero.const_mul (325 / κ_min)
    filter_upwards [eventually_gt_atTop (1 : ℝ), hlim.eventually (Iic_mem_nhds one_pos)] with c hc1 hc_s
    have hc0 : 0 < c := zero_lt_one.trans hc1
    have hdiv : 325 / κ_min * Real.log c ≤ c ^ (31 / 42 : ℝ) := by
      calc 325 / κ_min * Real.log c = 325 / κ_min * (Real.log c / c ^ (31 / 42 : ℝ)) * c ^ (31 / 42 : ℝ) := by
            field_simp [(Real.rpow_pos_of_pos hc0 _).ne']
        _ ≤ 1 * c ^ (31 / 42 : ℝ) := mul_le_mul_of_nonneg_right hc_s (Real.rpow_nonneg hc0.le _)
        _ = _ := one_mul _
    have h56 : c ^ (-(2 / 21 : ℝ)) * c ^ (5 / 6 : ℝ) = c ^ (31 / 42 : ℝ) := by
      rw [← Real.rpow_add hc0]; norm_num
    rw [div_le_iff₀ (mul_pos hκmin_pos (Real.rpow_pos_of_pos hc0 _))]
    calc 325 * Real.log c = κ_min * (325 / κ_min * Real.log c) := by field_simp [hκmin_pos.ne']
      _ ≤ κ_min * c ^ (31 / 42 : ℝ) := mul_le_mul_of_nonneg_left hdiv hκmin_pos.le
      _ = c ^ (5 / 6 : ℝ) * (κ_min * c ^ (-(2 / 21 : ℝ))) := by rw [← h56]; ring
  have hev_vert : ∀ᶠ c : ℝ in atTop,
      50 * Real.log c ≤ (1 / 26 : ℝ) * κ_min ^ 2 * c ^ (6 / 7 : ℝ) ∧
      50 * Real.log c ≤ (1 / 26 : ℝ) * κ_min * c ^ (19 / 21 : ℝ) := by
    have h1 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 6 / 7)).tendsto_div_nhds_zero.const_mul
      (50 * 26 / κ_min ^ 2)
    have h2 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 19 / 21)).tendsto_div_nhds_zero.const_mul
      (50 * 26 / κ_min)
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      h1.eventually (Iic_mem_nhds (by rw [mul_zero]; exact one_pos)),
      h2.eventually (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))] with c hc1 ha hb
    have hc0 : 0 < c := zero_lt_one.trans hc1
    refine ⟨?_, ?_⟩
    · have hha : 50 * 26 / κ_min ^ 2 * Real.log c ≤ c ^ (6 / 7 : ℝ) := by
        calc 50 * 26 / κ_min ^ 2 * Real.log c = 50 * 26 / κ_min ^ 2 * (Real.log c / c ^ (6 / 7 : ℝ)) * c ^ (6 / 7 : ℝ) := by
              field_simp [(Real.rpow_pos_of_pos hc0 _).ne']
          _ ≤ 1 * c ^ (6 / 7 : ℝ) := mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hc0.le _)
          _ = _ := one_mul _
      calc 50 * Real.log c = (1 / 26 : ℝ) * κ_min ^ 2 * (50 * 26 / κ_min ^ 2 * Real.log c) := by
            field_simp [hκmin_pos.ne']
        _ ≤ (1 / 26 : ℝ) * κ_min ^ 2 * c ^ (6 / 7 : ℝ) := mul_le_mul_of_nonneg_left hha (by positivity)
    · have hhb : 50 * 26 / κ_min * Real.log c ≤ c ^ (19 / 21 : ℝ) := by
        calc 50 * 26 / κ_min * Real.log c = 50 * 26 / κ_min * (Real.log c / c ^ (19 / 21 : ℝ)) * c ^ (19 / 21 : ℝ) := by
              field_simp [(Real.rpow_pos_of_pos hc0 _).ne']
          _ ≤ 1 * c ^ (19 / 21 : ℝ) := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hc0.le _)
          _ = _ := one_mul _
      calc 50 * Real.log c = (1 / 26 : ℝ) * κ_min * (50 * 26 / κ_min * Real.log c) := by
            field_simp [hκmin_pos.ne']
        _ ≤ (1 / 26 : ℝ) * κ_min * c ^ (19 / 21 : ℝ) := mul_le_mul_of_nonneg_left hhb (by positivity)
  have hev_tau : ∀ᶠ c : ℝ in atTop, Real.exp (nearB c + 4) ≤ c := by
    have hlog : ∀ᶠ c : ℝ in atTop, π ^ 2 * Real.log c * Real.exp 6 ≤ c := by
      have ht := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.const_mul
        (π ^ 2 * Real.exp 6)
      filter_upwards [eventually_gt_atTop (1 : ℝ),
        ht.eventually (Iic_mem_nhds (by rw [mul_zero]; exact one_pos))] with c hc1 h
      have hc0 : 0 < c := zero_lt_one.trans hc1
      calc π ^ 2 * Real.log c * Real.exp 6
          = π ^ 2 * Real.exp 6 * (Real.log c / c ^ (1 : ℝ)) * c := by
            rw [Real.rpow_one]; field_simp [hc0.ne']
        _ ≤ 1 * c := mul_le_mul_of_nonneg_right h hc0.le
        _ = c := one_mul _
    filter_upwards [eventually_ge_atTop (Real.exp 2), hlog] with c hce2 hl
    have hc0 : 0 < c := lt_of_lt_of_le (Real.exp_pos 2) hce2
    have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce2
    have hne : 0 < π ^ 2 * Real.log c := by positivity
    unfold nearB
    calc Real.exp (Real.log (π ^ 2 * Real.log c) + 2 + 4)
        = Real.exp (Real.log (π ^ 2 * Real.log c)) * Real.exp 6 := by rw [← Real.exp_add]; ring_nf
      _ = π ^ 2 * Real.log c * Real.exp 6 := by rw [Real.exp_log hne]
      _ ≤ c := hl
  have hev_deg : ∀ᶠ c : ℝ in atTop, (0.03 * κ_min)⁻¹ ^ 200 ≤ c := eventually_ge_atTop _
  obtain ⟨c₀, hc₀_prop⟩ := ((eventually_ge_atTop (max c_w (max c_x (max cL (Real.exp 2))))).and
    (hev_lam.and (hev_cs.and (hev_vert.and (hev_tau.and hev_deg))))).exists_forall_of_atTop
  have hc₀_ge_e2 : Real.exp 2 ≤ c₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (hc₀_prop c₀ le_rfl).1))
  let C_v2 : ℝ := M_tot_2 * (16 + 3 * CX2)
  have hCv2_nn : 0 ≤ C_v2 := mul_nonneg hMtot2_nn (by have := hCX_nn 2 (by norm_num); dsimp only [CX2]; positivity)
  let C_har : ℝ := 1 / (2 * π) * (15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) + 1
  refine ⟨c₀, C_har, hc₀_ge_e2, by positivity, ?_⟩
  intro ε c R f hε hc hRlo hRhi hf j hj k hk2 hk_le
  obtain ⟨hcM, hlam_le, hcs_le, hvert, htau_c, hdeg⟩ := hc₀_prop c hc
  have hce2 : Real.exp 2 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcM))
  have hc_w : c_w ≤ c := (le_max_left _ _).trans hcM
  have hc_x : c_x ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hcM)
  have hc_L : cL ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hcM))
  have hc1 : 1 < c := lt_of_lt_of_le (by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]) hce2
  have hc0 : 0 < c := by linarith
  have hc32 : 3 / 2 < c := by linarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 2)]
  have hlog2 : 2 ≤ Real.log c := (Real.le_log_iff_exp_le hc0).2 hce2
  have hM := hankelMass_nonneg hc0 f
  have hc14_nn : 0 ≤ c ^ (-(14 : ℝ)) := Real.rpow_nonneg hc0.le _
  obtain ⟨_, _, _, _, hblock⟩ := hblocks hε hc_w hRlo hRhi
  obtain ⟨hLj_lo, hLj_hi, hℓ0, hℓ_lb, hτ_lb, hτ_pos, hnw_cd, hnw_bd, hnw_supp, hnw_lo, _, hwin, hnw_drv⟩ :=
    hblock j hj
  set Lj := partGrid (ctLv0 c / 4) (j + 1)
  set ℓj := min Lj 1
  set τj := tau0 Lj
  obtain ⟨hL0, _, _, _⟩ := hLv0 c hc_L
  set a₀ : ℝ := max (ctLv0 c / 4) (Lj - ℓj / 100)
  set a' : ℝ := max (ctLv0 c / 3) (Lj - ℓj / 120)
  set b' : ℝ := Lj + ℓj / 120
  set b₀ : ℝ := Lj + ℓj / 100
  by_cases ha'b' : b' < a'
  · have hzero : ∀ L : ℝ, nearWeight ε c R j L = 0 := fun L => by
      by_cases hL1 : L ≤ ctLv0 c / 3
      · exact hnw_lo L hL1
      · by_cases hL2 : L < Lj - ℓj / 120
        · exact hnw_supp L fun h => by linarith only [h.1, hL2]
        · exact hnw_supp L fun h => by
            have : a' ≤ L := max_le (not_le.1 hL1).le (not_lt.1 hL2)
            linarith only [this, ha'b', h.2]
    have hint0 : ∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2)) = 0 := by
      simp [hzero]
    rw [hint0, abs_zero]
    positivity
  rw [not_lt] at ha'b'
  have ha₀a' : a₀ < a' := by dsimp only [a₀, a']; exact max_lt_max (by linarith only [hL0]) (by linarith only [hℓ0])
  have hb'b₀ : b' < b₀ := by dsimp only [b', b₀]; linarith only [hℓ0]
  set a : ℝ := (a₀ + a') / 2
  set b : ℝ := (b' + b₀) / 2
  have haa : a₀ < a := by dsimp only [a]; linarith only [ha₀a']
  have haa' : a < a' := by dsimp only [a]; linarith only [ha₀a']
  have hb'b : b' < b := by dsimp only [b]; linarith only [hb'b₀]
  have hbb₀ : b < b₀ := by dsimp only [b]; linarith only [hb'b₀]
  have hba_le1 : b - a ≤ 1 := by
    have hℓ1 : ℓj ≤ 1 := min_le_right _ _
    dsimp only [a, b, a₀, b₀] at *
    linarith only [hbb₀, haa, ha₀a', hb'b₀, hℓ1, le_max_right (ctLv0 c / 4) (Lj - ℓj / 100)]
  set u : ℝ → ℂ := fun L => ((nearWeight ε c R j L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))
  have hnw_supp' : ∀ L ∉ Icc a' b', nearWeight ε c R j L = 0 := fun L hL => by
    by_cases h1 : L ≤ ctLv0 c / 3
    · exact hnw_lo L h1
    · rw [not_le] at h1
      exact hnw_supp L fun hc_i => hL ⟨max_le h1.le hc_i.1, hc_i.2⟩
  have hsupp_u : ∀ L ∉ Icc a' b', u L = 0 := fun L hL => by simp [u, hnw_supp' L hL]
  have hcd_u : ContDiff ℝ 2 u := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_or_ge x (ctLv0 c / 3) with hlt | hge
    · have hev : u =ᶠ[𝓝 x] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hlt] with L hL
        simp [u, hnw_lo L (Set.mem_Iio.1 hL).le]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hev
    · have hX_at : ContDiffAt ℝ 2 (boasX c ε) x :=
        (boasX_contDiffOn hε 2).contDiffAt (Ioi_mem_nhds (by linarith only [hL0, hge] : 0 < x))
      have hnw_at : ContDiffAt ℝ 2 (fun L => ((nearWeight ε c R j L : ℝ) : ℂ)) x :=
        (Complex.ofRealCLM.contDiff.comp (hnw_cd 2)).contDiffAt
      have hexp_at : ContDiffAt ℝ 2 (fun L => Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))) x :=
        ((contDiffAt_const (c := Complex.I)).mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp x ((contDiffAt_const (c := (k : ℝ))).mul hX_at))).cexp
      exact hnw_at.mul hexp_at
  have hh := integrable_hankelHL hc0 hf
  have hcos_le : |∫ L : ℝ, nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))| ≤
      ‖∫ L : ℝ, u L * (hankelHL c f L : ℂ)‖ := by
    have hrew : (fun L : ℝ => nearWeight ε c R j L * hankelHL c f L * Real.cos ((k : ℝ) * (boasX c ε L + π / 2))) =
        fun L => (Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) * (u L * (hankelHL c f L : ℂ))).re := by
      ext L
      have hre : (Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
          (u L * (hankelHL c f L : ℂ))).re =
          nearWeight ε c R j L * hankelHL c f L *
            (Complex.exp ((((k : ℝ) * (boasX c ε L + π / 2) : ℝ) : ℂ) * Complex.I)).re := by
        simp only [u]
        have hexp : Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) =
            Complex.exp ((((k : ℝ) * (boasX c ε L + π / 2) : ℝ) : ℂ) * Complex.I) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [show Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
              (((nearWeight ε c R j L : ℝ) : ℂ) * Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ)) *
                (hankelHL c f L : ℂ)) =
            (((nearWeight ε c R j L * hankelHL c f L : ℝ) : ℂ)) *
              (Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
                Complex.exp (Complex.I * ((k : ℝ) * boasX c ε L : ℝ))) by push_cast; ring,
          hexp, Complex.re_ofReal_mul]
      rw [hre, Complex.exp_ofReal_mul_I_re]
    have hu_int_c : Integrable (fun L : ℝ => Complex.exp (Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ)) *
        (u L * (hankelHL c f L : ℂ))) := by
      refine hh.norm.mono'
        (((continuous_const.mul hcd_u.continuous).aestronglyMeasurable).mul
          (Complex.continuous_ofReal.comp_aestronglyMeasurable hh.aestronglyMeasurable) |>.congr
            (ae_of_all _ fun L => by dsimp only; ring))
        (ae_of_all _ fun L => ?_)
      rw [norm_mul, norm_mul,
        show Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ) = (((k : ℝ) * (π / 2) : ℝ) : ℂ) * Complex.I by ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]
      have hnu : ‖u L‖ ≤ 1 := by
        simp only [u, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hnw_bd L).1,
          show Complex.I * ((k : ℝ) * boasX c ε L : ℝ) = (((k : ℝ) * boasX c ε L : ℝ) : ℂ) * Complex.I by push_cast; ring,
          Complex.norm_exp_ofReal_mul_I, mul_one]
        exact (hnw_bd L).2
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_left (abs_nonneg _) hnu
    have hre_int := integral_re hu_int_c
    simp only [RCLike.re_to_complex] at hre_int
    rw [hrew, hre_int]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [integral_const_mul, norm_mul,
      show Complex.I * (((k : ℝ) * (π / 2) : ℝ) : ℂ) = (((k : ℝ) * (π / 2) : ℝ) : ℂ) * Complex.I by ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
  set Tj : ℝ := 3 * τj / 2
  set sj : ℝ := min (τj / 4) (min (1 / 4) (325 * Real.log c / (c * ℓj)))
  have hTj_pos : 0 < Tj := by positivity
  have hsj_pos : 0 < sj := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hsj_τ : sj ≤ τj / 4 := min_le_left _ _
  have hsj_4 : sj ≤ 1 / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hsj_log : sj ≤ 325 * Real.log c / (c * ℓj) := (min_le_right _ _).trans (min_le_right _ _)
  have hfour := hankelHL_compact_fourier hc32 hf haa' ha'b' hb'b hcd_u hsupp_u Lj
  have hshift := hankel_contour_shift_norm_le hc32 hf hε haa' ha'b' hb'b hcd_u hsupp_u hTj_pos hsj_pos hsj_4 Lj
  dsimp only at hshift
  set Φ : ℂ → ℂ := fun ζ =>
    hankelHhat c f ζ * Complex.exp ((c : ℂ) * ζ * (Lj : ℂ)) * boasB0 Lj u c a b ζ
  have hsub_win : ∀ L ∈ Ioo a₀ b₀, ctLv0 c / 4 ≤ L ∧ 0 < L ∧ L ∈ Icc (Lj - ℓj / 100) (Lj + ℓj / 100) := by
    intro L hL
    have hLlv : ctLv0 c / 4 ≤ L := le_trans (le_max_left _ _) hL.1.le
    exact ⟨hLlv, lt_of_lt_of_le (by positivity) hLlv, le_trans (le_max_right _ _) hL.1.le, hL.2.le⟩
  have hk_c2 : (k : ℝ) ≤ c ^ 2 + 1 := by
    have h1 : (k : ℝ) ≤ Nat.ceil (c ^ 2) := by exact_mod_cast hk_le
    have h2 : (Nat.ceil (c ^ 2) : ℝ) < c ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith only [h1, h2]
  have hLj_pos : 0 < Lj := by linarith only [hL0, hLj_lo]
  have hτj_le_c : τj ≤ c := (tau0_le_of_le hLj_pos hLj_hi).trans htau_c
  have hosc_box : ∀ σ ∈ Icc (0 : ℝ) sj, ∀ τ ∈ Icc (-Tj) Tj, (σ = 0 ∨ |τ| = Tj) →
      ‖Φ ((σ : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ) :=
    fun σ hσ τ hτ hside => central_horiz_osc_bound hCD0 hibp_r hc1 hc32 hε hc_x hf hk2
      hκmin_pos hLj_pos hℓ0 hτ_pos hℓ_lb hτ_lb hL0 haa haa' ha'b' hb'b hbb₀ hba_le1
      hsj_pos hsj_τ hsj_4 hsj_log rfl hsub_win (fun L hL => ⟨(hwin L hL).1, (hwin L hL).2.1⟩)
      hnw_cd hnw_supp' hCm0 hnw_drv rfl (fun L hL => hx_drv hc_x hε L hL) hCX_nn
      (fun r hr L hL => hx_sym r hr hc_x hε L hL) (fun i => rfl) hlam_le hcs_le hdeg hσ hτ hside
  have htail_bd : ∀ {τ : ℝ}, Tj ≤ |τ| →
      ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤ 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * (τ ^ 2)⁻¹ := by
    intro τ hτ
    have hτne : τ ≠ 0 := fun h => by rw [h, abs_zero] at hτ; linarith only [hτ, hTj_pos]
    have hH_tail : ‖hankelHhat c f ((sj : ℂ) + (τ : ℂ) * Complex.I) *
        Complex.exp ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ))‖ ≤
        3 * hankelMass c f * c ^ (-50 : ℝ) := by
      have hS0 := S0_ineq hτ_pos hsj_pos hsj_τ hsj_4 hτ
      have hmL : hankelEdgeM τj = Lj := hankelEdgeM_tau0 hLj_pos
      have hm_mono : hankelEdgeM (3 * τj / 2) ≤ hankelEdgeM |τ| :=
        hankelEdgeM_strictMonoOn.monotoneOn (mem_Ici.2 (by positivity)) (mem_Ici.2 (abs_nonneg _)) hτ
      have hdel := (hankelEdge_delta32_ge_L hτ_pos).2
      rw [hmL] at hS0 hdel
      have hsj_del : c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj ≤ -50 * Real.log c := by
        have hstep1 : (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + sj * Lj ≤ -(2 / 13) * sj * ℓj := by
          have h1 : 5 / 26 * ℓj ≤ hankelEdgeM |τ| - Lj := le_trans hdel (by linarith only [hm_mono])
          nlinarith only [hS0, hsj_pos, h1]
        have h50 : 50 * Real.log c ≤ 2 / 13 * c * sj * ℓj := by
          rcases le_total (τj / 4) (min (1 / 4) (325 * Real.log c / (c * ℓj))) with hs1 | hs23
          · have hs_eq : sj = τj / 4 := min_eq_left hs1
            have h1 : 50 * Real.log c ≤ 1 / 26 * κ_min ^ 2 * c ^ (6 / 7 : ℝ) := hvert.1
            have hpow : c * c ^ (-(1 / 21 : ℝ)) * c ^ (-(2 / 21 : ℝ)) = c ^ (6 / 7 : ℝ) := by
              nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0, ← Real.rpow_add hc0]; norm_num
            have h2 : 1 / 26 * κ_min ^ 2 * c ^ (6 / 7 : ℝ) ≤ 2 / 13 * c * sj * ℓj := by
              rw [hs_eq]
              calc 1 / 26 * κ_min ^ 2 * c ^ (6 / 7 : ℝ)
                  = 2 / 13 * c * (κ_min * c ^ (-(1 / 21 : ℝ)) / 4) * (κ_min * c ^ (-(2 / 21 : ℝ))) := by
                    rw [← hpow]; ring
                _ ≤ 2 / 13 * c * (τj / 4) * ℓj := by gcongr
            linarith only [h1, h2]
          · have hs_eq : sj = min (1 / 4) (325 * Real.log c / (c * ℓj)) := min_eq_right hs23
            rw [hs_eq]
            rcases le_total (1 / 4) (325 * Real.log c / (c * ℓj)) with h14 | hlog_min
            · rw [min_eq_left h14]
              have h1 : 50 * Real.log c ≤ 1 / 26 * κ_min * c ^ (19 / 21 : ℝ) := hvert.2
              have hpow : c * c ^ (-(2 / 21 : ℝ)) = c ^ (19 / 21 : ℝ) := by
                nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
              have h2 : 1 / 26 * κ_min * c ^ (19 / 21 : ℝ) ≤ 2 / 13 * c * (1 / 4) * ℓj := by
                calc 1 / 26 * κ_min * c ^ (19 / 21 : ℝ) = 2 / 13 * c * (1 / 4) * (κ_min * c ^ (-(2 / 21 : ℝ))) := by
                      rw [← hpow]; ring
                  _ ≤ 2 / 13 * c * (1 / 4) * ℓj := by gcongr
              linarith only [h1, h2]
            · rw [min_eq_right hlog_min]
              field_simp [hc0.ne', hℓ0.ne']; norm_num
        nlinarith only [hstep1, h50, hc0]
      have hexp_50 : Real.exp (c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj) ≤
          c ^ (-50 : ℝ) := by
        calc Real.exp (c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj)
            ≤ Real.exp (-50 * Real.log c) := Real.exp_le_exp.2 hsj_del
          _ = c ^ (-50 : ℝ) := by rw [show -50 * Real.log c = Real.log c * (-50) by ring, ← Real.rpow_def_of_pos hc0]
      rw [norm_mul, Complex.norm_exp,
        show ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ)).re = c * sj * Lj by
          simp [Complex.mul_re, Complex.mul_im] ]
      have hbnd := hankelHhat_bound hc32 hf hε hsj_pos.le hsj_4 τ
      calc ‖hankelHhat c f ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ * Real.exp (c * sj * Lj)
          ≤ 3 * hankelMass c f * Real.exp (c * (stripS0Tilde ((sj : ℂ) + (τ : ℂ) * Complex.I)).re + c * sj * Lj) := by
            have := mul_le_mul_of_nonneg_right hbnd (Real.exp_pos _).le
            refine this.trans_eq ?_
            rw [mul_assoc (3 * hankelMass c f), ← Real.exp_add, mul_add]
        _ ≤ 3 * hankelMass c f * c ^ (-50 : ℝ) := by gcongr
    have hB_tail := vertical_tail_ibp_bound hc1 hlog2 hε hc_x hk_c2 hκmin_pos hℓ0 hℓ_lb hτj_le_c hL0
      haa haa' ha'b' hb'b hbb₀ hba_le1 hsj_pos hsj_log hτne hsub_win (fun L hL => (hwin L hL).2.1)
      hnw_cd hnw_supp' hCm0 hnw_drv rfl (hCX_nn 2 (by norm_num)) rfl
      (fun L hL => hx_drv hc_x hε L hL) (fun L hL => hx_sym 2 (by norm_num) hc_x hε L hL)
      hlam_le hcs_le hcd_u
    rw [norm_mul]
    calc ‖hankelHhat c f ((sj : ℂ) + (τ : ℂ) * Complex.I) *
            Complex.exp ((c : ℂ) * ((sj : ℂ) + (τ : ℂ) * Complex.I) * (Lj : ℂ))‖ *
          ‖boasB0 Lj u c a b ((sj : ℂ) + (τ : ℂ) * Complex.I)‖
        ≤ (3 * hankelMass c f * c ^ (-50 : ℝ)) * (C_v2 * c ^ (12 : ℝ) * (τ ^ 2)⁻¹) := by gcongr
      _ = 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * (τ ^ 2)⁻¹ := by
          have hc5012 : c ^ (-50 : ℝ) * c ^ (12 : ℝ) = c ^ (-38 : ℝ) := by rw [← Real.rpow_add hc0]; norm_num
          calc _ = 3 * hankelMass c f * C_v2 * (c ^ (-50 : ℝ) * c ^ (12 : ℝ)) * (τ ^ 2)⁻¹ := by ring
            _ = _ := by rw [hc5012]
  have hpiece_mid : ∫ τ in Icc (-Tj) Tj, ‖Φ ((τ : ℂ) * Complex.I)‖ ≤
      9 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) := by
    have hconst := setIntegral_mono_on hshift.1 ((integrableOn_const).2 (Or.inr measure_Icc_lt_top))
      measurableSet_Icc fun τ hτ => by simpa using hosc_box 0 ⟨le_rfl, hsj_pos.le⟩ τ hτ (Or.inl rfl)
    refine hconst.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith only [hTj_pos]),
      show Tj - -Tj = 3 * τj by simp only [Tj]; ring]
    have h6 : c * c ^ (5 - 500 / 21 : ℝ) = c ^ (6 - 500 / 21 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    calc (3 * τj) * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))
        ≤ (3 * c) * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) := by gcongr
      _ = 9 * C_D * M_tot_w * hankelMass c f * (c * c ^ (5 - 500 / 21 : ℝ)) := by ring
      _ = _ := by rw [h6]
  have hpiece_topH : ∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (Tj : ℂ) * Complex.I)‖ ≤
      3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) := by
    rw [intervalIntegral.integral_of_le hsj_pos.le]
    have hconst := setIntegral_mono_on (hshift.2.1.mono_set (by rw [uIoc_of_le hsj_pos.le])).integrableOn
      ((integrableOn_const).2 (Or.inr measure_Ioc_lt_top)) measurableSet_Ioc fun σ hσ =>
        hosc_box σ ⟨hσ.1.le, hσ.2⟩ Tj ⟨by linarith only [hTj_pos], le_rfl⟩ (Or.inr (abs_of_pos hTj_pos))
    refine hconst.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hsj_pos.le, sub_zero]
    have h1 : sj ≤ c := by linarith only [hsj_4, hc1]
    have h6 : c * c ^ (5 - 500 / 21 : ℝ) = c ^ (6 - 500 / 21 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    calc sj * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))
        ≤ c * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) := by gcongr
      _ = 3 * C_D * M_tot_w * hankelMass c f * (c * c ^ (5 - 500 / 21 : ℝ)) := by ring
      _ = _ := by rw [h6]
  have hpiece_botH : ∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (-Tj : ℝ) * Complex.I)‖ ≤
      3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) := by
    rw [intervalIntegral.integral_of_le hsj_pos.le]
    have hconst := setIntegral_mono_on (hshift.2.2.1.mono_set (by rw [uIoc_of_le hsj_pos.le])).integrableOn
      ((integrableOn_const).2 (Or.inr measure_Ioc_lt_top)) measurableSet_Ioc fun σ hσ =>
        hosc_box σ ⟨hσ.1.le, hσ.2⟩ (-Tj) ⟨le_rfl, by linarith only [hTj_pos]⟩
          (Or.inr (by rw [abs_neg, abs_of_pos hTj_pos]))
    refine hconst.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hsj_pos.le, sub_zero]
    have h1 : sj ≤ c := by linarith only [hsj_4, hc1]
    have h6 : c * c ^ (5 - 500 / 21 : ℝ) = c ^ (6 - 500 / 21 : ℝ) := by
      nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; ring_nf
    calc sj * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ))
        ≤ c * (3 * C_D * M_tot_w * hankelMass c f * c ^ (5 - 500 / 21 : ℝ)) := by gcongr
      _ = 3 * C_D * M_tot_w * hankelMass c f * (c * c ^ (5 - 500 / 21 : ℝ)) := by ring
      _ = _ := by rw [h6]
  have hinvsq_Ioi : IntegrableOn (fun τ : ℝ => (τ ^ 2)⁻¹) (Ioi Tj) := by
    refine (integrable_inv_one_add_sq.const_mul (1 + Tj⁻¹ ^ 2)).integrableOn.mono'
      ((measurable_id.pow_const 2).inv.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun τ (hτ : Tj < τ) => ?_)
    have hτ2 : Tj ^ 2 ≤ τ ^ 2 := by nlinarith only [hTj_pos, hτ]
    have h1 : 1 ≤ Tj⁻¹ ^ 2 * τ ^ 2 := by rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]; exact hτ2
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (τ ^ 2)⁻¹ * (1 + τ ^ 2) ≤ (τ ^ 2)⁻¹ * ((1 + Tj⁻¹ ^ 2) * τ ^ 2) := by gcongr; linarith
      _ = 1 + Tj⁻¹ ^ 2 := by
        field_simp [pow_ne_zero 2 (lt_trans hTj_pos hτ).ne']
        rw [mul_inv_cancel₀ (lt_trans hTj_pos hτ).ne']
  have hinvsq_Iio : IntegrableOn (fun τ : ℝ => (τ ^ 2)⁻¹) (Iio (-Tj)) := by
    refine (integrable_inv_one_add_sq.const_mul (1 + Tj⁻¹ ^ 2)).integrableOn.mono'
      ((measurable_id.pow_const 2).inv.aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Iio).2 (ae_of_all _ fun τ (hτ : τ < -Tj) => ?_)
    have hτ2 : Tj ^ 2 ≤ τ ^ 2 := by nlinarith only [hTj_pos, hτ]
    have h1 : 1 ≤ Tj⁻¹ ^ 2 * τ ^ 2 := by rw [inv_pow, inv_mul_eq_div, one_le_div (by positivity)]; exact hτ2
    rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc (τ ^ 2)⁻¹ * (1 + τ ^ 2) ≤ (τ ^ 2)⁻¹ * ((1 + Tj⁻¹ ^ 2) * τ ^ 2) := by gcongr; linarith
      _ = 1 + Tj⁻¹ ^ 2 := by
        have hτn : τ ≠ 0 := by linarith only [hτ, hTj_pos]
        field_simp [pow_ne_zero 2 hτn]
        rw [mul_inv_cancel₀ hτn]
  have hTj_inv : Tj⁻¹ ≤ (2 / 3) * κ_min⁻¹ * c ^ (1 / 21 : ℝ) := by
    have hc121 : c ^ (-(1 / 21 : ℝ)) * c ^ (1 / 21 : ℝ) = 1 := by rw [← Real.rpow_add hc0]; norm_num
    rw [show Tj = 3 / 2 * τj by simp only [Tj]; ring, inv_eq_one_div, div_le_iff₀' (by positivity)]
    calc 1 = (3 / 2 * (κ_min * c ^ (-(1 / 21 : ℝ)))) * ((2 / 3 : ℝ) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by
          rw [show (3 / 2 * (κ_min * c ^ (-(1 / 21 : ℝ)))) * ((2 / 3 : ℝ) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) =
              (3 / 2 * (2 / 3)) * (κ_min * κ_min⁻¹) * (c ^ (-(1 / 21 : ℝ)) * c ^ (1 / 21 : ℝ)) by ring,
            mul_inv_cancel₀ hκmin_pos.ne', hc121]; norm_num
      _ ≤ (3 / 2 * τj) * ((2 / 3 : ℝ) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by gcongr
  have hpiece_topV : ∫ τ in Ioi Tj, ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) := by
    have hm := setIntegral_mono_on hshift.2.2.2.1 (hinvsq_Ioi.const_mul _) measurableSet_Ioi fun τ (hτ : Tj < τ) =>
      htail_bd (le_trans hτ.le (le_abs_self τ))
    refine hm.trans ?_
    rw [integral_const_mul, integral_Ioi_inv_sq hTj_pos]
    have hc38 : c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ) ≤ c ^ (-37 : ℝ) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
    calc 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * Tj⁻¹
        ≤ 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * ((2 / 3) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by gcongr
      _ = 2 * κ_min⁻¹ * C_v2 * hankelMass c f * (c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ)) := by ring
      _ ≤ _ := by gcongr
  have hpiece_botV : ∫ τ in Iio (-Tj), ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖ ≤
      2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) := by
    have hm := setIntegral_mono_on hshift.2.2.2.2.1 (hinvsq_Iio.const_mul _) measurableSet_Iio fun τ (hτ : τ < -Tj) =>
      htail_bd (by rw [abs_of_neg (by linarith only [hτ, hTj_pos])]; linarith only [hτ])
    refine hm.trans ?_
    rw [integral_const_mul, integral_Iio_inv_sq hTj_pos]
    have hc38 : c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ) ≤ c ^ (-37 : ℝ) := by
      rw [← Real.rpow_add hc0]; exact Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
    calc 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * Tj⁻¹
        ≤ 3 * hankelMass c f * C_v2 * c ^ (-38 : ℝ) * ((2 / 3) * κ_min⁻¹ * c ^ (1 / 21 : ℝ)) := by gcongr
      _ = 2 * κ_min⁻¹ * C_v2 * hankelMass c f * (c ^ (-38 : ℝ) * c ^ (1 / 21 : ℝ)) := by ring
      _ ≤ _ := by gcongr
  refine hcos_le.trans ?_
  rw [hfour.2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ c / (2 * π))]
  have hc17 : c ^ (6 - 500 / 21 : ℝ) ≤ c ^ (-15 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hc37 : c ^ (-37 : ℝ) ≤ c ^ (-15 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hc1.le (by norm_num)
  have hsum_phi : ‖∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I)‖ ≤
      (15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) * hankelMass c f * c ^ (-15 : ℝ) := by
    refine hshift.2.2.2.2.2.trans ?_
    calc (∫ τ in Icc (-Tj) Tj, ‖Φ ((τ : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (Tj : ℂ) * Complex.I)‖) +
          (∫ σ in (0 : ℝ)..sj, ‖Φ ((σ : ℂ) + (-Tj : ℝ) * Complex.I)‖) +
          (∫ τ in Ioi Tj, ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖) +
          (∫ τ in Iio (-Tj), ‖Φ ((sj : ℂ) + (τ : ℂ) * Complex.I)‖)
        ≤ 9 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) +
          3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) +
          3 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) +
          2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) +
          2 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) := by
            linarith only [hpiece_mid, hpiece_topH, hpiece_botH, hpiece_topV, hpiece_botV]
      _ ≤ 15 * C_D * M_tot_w * hankelMass c f * c ^ (-15 : ℝ) +
          4 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-15 : ℝ) := by
            have h1 : 15 * C_D * M_tot_w * hankelMass c f * c ^ (6 - 500 / 21 : ℝ) ≤
                15 * C_D * M_tot_w * hankelMass c f * c ^ (-15 : ℝ) := by gcongr
            have h2 : 4 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-37 : ℝ) ≤
                4 * κ_min⁻¹ * C_v2 * hankelMass c f * c ^ (-15 : ℝ) := by gcongr
            linarith only [h1, h2]
      _ = _ := by ring
  have hc14 : c * c ^ (-15 : ℝ) = c ^ (-(14 : ℝ)) := by
    nth_rw 1 [← Real.rpow_one c]; rw [← Real.rpow_add hc0]; norm_num
  calc c / (2 * π) * ‖∫ τ : ℝ, Φ ((τ : ℂ) * Complex.I)‖
      ≤ c / (2 * π) * ((15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) * hankelMass c f * c ^ (-15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsum_phi (by positivity)
    _ = 1 / (2 * π) * (15 * C_D * M_tot_w + 4 * κ_min⁻¹ * C_v2) * hankelMass c f * (c * c ^ (-15 : ℝ)) := by ring
    _ ≤ C_har * hankelMass c f * c ^ (-(14 : ℝ)) := by
        rw [hc14]; dsimp only [C_har]; gcongr; linarith

/-- info: 'FormalResearch.SignUncertainty.boas_harmonic_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms boas_harmonic_bound

end FormalResearch.SignUncertainty

module

public import FormalResearch.CohnElkies.SeedSymbolDerivs
public import FormalResearch.CohnElkies.PieceCSmooth
public import FormalResearch.CohnElkies.AiryWindowInversion
public import FormalResearch.Special.AiryKernelOpSharp

/-!
# Square-root structure at the origin of the seed transforms (`u1c:U1`, `u1c:U3` Piece C item 1)

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, Piece C, step 1 (subtraction of the branch point) and
Lemma `U.1` (`u1c:U1`) for the seeds `f₁`, `g₁`, `g₁'` and their combinations.

Method (exact, no tail asymptotics).  With `Λ_X(y) = ∫ X(u) e^{yu} du` and `a` a zero of `Ai` (resp. `Ai'`) one has
`(u - a) f₁ = Ai²`, `(u - a)² g₁ = Ai²` and `(u - a')² g₁' = Ai'²`, so `M_X(y) = e^{-ay} Λ_X(y)` solves
`M_{f₁}' = e^{-ay} Λ_{Ai²}`, `M_{g₁}'' = e^{-ay} Λ_{Ai²}`, `M_{g₁'}'' = e^{-ay} Λ_{Ai'²}`, where
`Λ_{Ai²}(y) = (2 √π)^{-1} y^{-1/2} e^{y³/12}` and `Λ_{Ai'²}(y) = Λ_{Ai²}(y) (y²/4 + 1/(2y))`.  The right-hand sides are
`y^{-1/2}·(entire)` or `y^{-3/2}·(entire)`, and integrating once or twice gives
`airyTwistedLaplaceC X y = A(y) + y^{1/2} B(y)` with `A, B` entire (`SqForm`).  Consequently the subtracted symbol
`G_sm = X̃(i c_s v) + γ₀ (iv)^{1/2} e^{iπ²v³/36} χ₁(v)`, with `γ₀ = -c_s^{1/2} B(0)`, is `C¹`, has
`G_sm'' = O(|v|^{-1/2})` near `v = 0`, and (with the large-`|v|` bounds of `SeedSymbolDerivs`) satisfies `SmoothSymbol`.
Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Complex Filter Topology Set
open scoped Real

namespace FormalResearch.CohnElkies

open FormalResearch.Special

/-! ### Laplace calculus on `Re y > 0` -/

/-- The plain Laplace integral `Λ_X(y) = ∫ X(u) e^{yu} du`. -/
noncomputable def lapC (X : ℝ → ℝ) (y : ℂ) : ℂ := ∫ u : ℝ, (X u : ℂ) * Complex.exp (y * (u : ℂ))

lemma airyTwistedLaplaceC_eq_lapC (X : ℝ → ℝ) (y : ℂ) :
    airyTwistedLaplaceC X y = (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12) * lapC X y := rfl

/-- Weighted integrability class: `X` continuous and `|u|^k |X(u)| e^{cu}` integrable for all `c > 0`, `k`. -/
structure LapOK (X : ℝ → ℝ) : Prop where
  cont : Continuous X
  integ : ∀ c : ℝ, 0 < c → ∀ k : ℕ, Integrable (fun u : ℝ => |u| ^ k * |X u| * Real.exp (c * u))

lemma LapOK.integrable_cplx {X : ℝ → ℝ} (hX : LapOK X) {y : ℂ} (hy : 0 < y.re) (k : ℕ) :
    Integrable (fun u : ℝ => (u : ℂ) ^ k * (X u : ℂ) * Complex.exp (y * (u : ℂ))) := by
  refine (hX.integ y.re hy k).mono' ?_ (ae_of_all _ fun u => ?_)
  · exact (((Complex.continuous_ofReal.pow k).mul (Complex.continuous_ofReal.comp hX.cont)).mul
      (by fun_prop)).aestronglyMeasurable
  · simp [norm_pow, Complex.norm_exp, Complex.mul_re]

lemma LapOK.mulX {X : ℝ → ℝ} (hX : LapOK X) : LapOK (fun u => u * X u) where
  cont := continuous_id.mul hX.cont
  integ c hc k := (hX.integ c hc (k + 1)).congr (ae_of_all _ fun u => by simp only [abs_mul, pow_succ]; ring)

lemma LapOK.shift {X : ℝ → ℝ} (hX : LapOK X) (a : ℝ) : LapOK (fun u => (u - a) * X u) where
  cont := (continuous_id.sub continuous_const).mul hX.cont
  integ c hc k := by
    have hcont : Continuous fun u : ℝ => |u| ^ k * |(u - a) * X u| * Real.exp (c * u) := by
      have := hX.cont; fun_prop
    refine ((hX.integ c hc (k + 1)).add ((hX.integ c hc k).const_mul |a|)).mono' hcont.aestronglyMeasurable
      (ae_of_all _ fun u => ?_)
    have h1 : |(u - a) * X u| ≤ (|u| + |a|) * |X u| := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_right (abs_sub u a) (abs_nonneg _)
    have h2 : 0 ≤ |u| ^ k * Real.exp (c * u) := by positivity
    rw [Real.norm_of_nonneg (by positivity)]
    calc |u| ^ k * |(u - a) * X u| * Real.exp (c * u) ≤ |u| ^ k * ((|u| + |a|) * |X u|) * Real.exp (c * u) := by gcongr
      _ = |u| ^ (k + 1) * |X u| * Real.exp (c * u) + |a| * (|u| ^ k * |X u| * Real.exp (c * u)) := by
        simp only [pow_succ]; ring

lemma hasDerivAt_lapC {X : ℝ → ℝ} (hX : LapOK X) {y₀ : ℂ} (hy₀ : 0 < y₀.re) :
    HasDerivAt (lapC X) (lapC (fun u => u * X u) y₀) y₀ := by
  set ε : ℝ := y₀.re / 2 with hε
  have hε0 : 0 < ε := by positivity
  set R : ℝ := y₀.re + ε with hR
  have hR0 : 0 < R := by positivity
  let F : ℂ → ℝ → ℂ := fun y u => (X u : ℂ) * Complex.exp (y * (u : ℂ))
  let F' : ℂ → ℝ → ℂ := fun y u => ((u * X u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))
  let bound : ℝ → ℝ := fun u => |u| ^ 1 * |X u| * Real.exp (ε * u) + |u| ^ 1 * |X u| * Real.exp (R * u)
  have hmeas : ∀ y : ℂ, AEStronglyMeasurable (F y) volume := fun y =>
    ((Complex.continuous_ofReal.comp hX.cont).mul (by fun_prop)).aestronglyMeasurable
  have hF'meas : AEStronglyMeasurable (F' y₀) volume :=
    ((Complex.continuous_ofReal.comp (continuous_id.mul hX.cont)).mul (by fun_prop)).aestronglyMeasurable
  have hFint : Integrable (F y₀) volume := by
    have := hX.integrable_cplx hy₀ 0
    simpa [F] using this
  have hbound_int : Integrable bound := (hX.integ ε hε0 1).add (hX.integ R hR0 1)
  have hball : ∀ {y : ℂ}, y ∈ Metric.ball y₀ ε → ε ≤ y.re ∧ y.re ≤ R := fun {y} hy => by
    have hdist : ‖y - y₀‖ < ε := by simpa [Complex.dist_eq] using Metric.mem_ball.mp hy
    have h1 : |y.re - y₀.re| ≤ ‖y - y₀‖ := by
      simpa using Complex.abs_re_le_norm (y - y₀)
    have h2 := abs_lt.mp (lt_of_le_of_lt h1 hdist)
    constructor <;> linarith [h2.1, h2.2]
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := F') (Metric.ball_mem_nhds y₀ hε0)
    (Eventually.of_forall hmeas) hFint hF'meas (ae_of_all _ fun u y hy => ?_) hbound_int
    (ae_of_all _ fun u y _ => (((hasDerivAt_id y).mul_const (u : ℂ)).cexp.const_mul (X u : ℂ)).congr_deriv
      (by dsimp [F']; push_cast; ring))
  · exact hd.2
  · obtain ⟨h1, h2⟩ := hball hy
    simp only [F', bound]
    rw [norm_mul, Complex.norm_real, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Real.norm_eq_abs, abs_mul, pow_one]
    rcases le_or_gt u 0 with hu | hu
    · have : Real.exp (y.re * u) ≤ Real.exp (ε * u) := Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right h1 hu)
      have h0 : 0 ≤ |u| * |X u| := by positivity
      calc |u| * |X u| * Real.exp (y.re * u) ≤ |u| * |X u| * Real.exp (ε * u) := by gcongr
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
    · have : Real.exp (y.re * u) ≤ Real.exp (R * u) := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right h2 hu.le)
      have h0 : 0 ≤ |u| * |X u| := by positivity
      calc |u| * |X u| * Real.exp (y.re * u) ≤ |u| * |X u| * Real.exp (R * u) := by gcongr
        _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma lapC_shift {X : ℝ → ℝ} (hX : LapOK X) (a : ℝ) {y : ℂ} (hy : 0 < y.re) :
    lapC (fun u => (u - a) * X u) y = lapC (fun u => u * X u) y - (a : ℂ) * lapC X y := by
  unfold lapC
  have h0 : Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (y * (u : ℂ))) := by
    simpa using hX.integrable_cplx hy 0
  have h1 : Integrable (fun u : ℝ => ((u * X u : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
    (hX.integrable_cplx hy 1).congr (ae_of_all _ fun u => by push_cast; ring)
  rw [← integral_const_mul, ← integral_sub h1 (h0.const_mul (a : ℂ))]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  push_cast; ring

/-- `y ↦ e^{-ay} Λ_X(y)` has derivative `e^{-ay} Λ_{(u-a)X}(y)`. -/
lemma hasDerivAt_modLap {X : ℝ → ℝ} (hX : LapOK X) (a : ℝ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC X z)
      (Complex.exp (-(a : ℂ) * y) * lapC (fun u => (u - a) * X u) y) y := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.exp (-(a : ℂ) * z)) (Complex.exp (-(a : ℂ) * y) * (-(a : ℂ))) y := by
    simpa using ((hasDerivAt_id y).const_mul (-(a : ℂ))).cexp
  have := h1.mul (hasDerivAt_lapC hX hy)
  convert this using 1
  rw [lapC_shift hX a hy]; ring

/-! ### Instances of `LapOK` -/

lemma abs_pow_mul_exp_le {c : ℝ} (hc : 0 < c) (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    |u| ^ k * Real.exp (c * u) ≤ (k.factorial : ℝ) * (2 / c) ^ k * Real.exp (c / 2 * u) := by
  have ht : |u| = -u := abs_of_nonpos hu
  have h1 : (c * |u| / 2) ^ k / k.factorial ≤ Real.exp (c * |u| / 2) := Real.pow_div_factorial_le_exp _ (by positivity) k
  have h2 : |u| ^ k ≤ (k.factorial : ℝ) * (2 / c) ^ k * Real.exp (c * |u| / 2) := by
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp h1
    calc |u| ^ k = (2 / c) ^ k * (c * |u| / 2) ^ k := by rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / c) ^ k * (Real.exp (c * |u| / 2) * k.factorial) := by gcongr
      _ = _ := by ring
  calc |u| ^ k * Real.exp (c * u) ≤ ((k.factorial : ℝ) * (2 / c) ^ k * Real.exp (c * |u| / 2)) * Real.exp (c * u) := by gcongr
    _ = (k.factorial : ℝ) * (2 / c) ^ k * Real.exp (c / 2 * u) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; rw [ht]; ring

lemma integrableOn_abs_pow_exp_Iio {c : ℝ} (hc : 0 < c) (k : ℕ) :
    IntegrableOn (fun u : ℝ => |u| ^ k * Real.exp (c * u)) (Iio 0) := by
  have hint := ((integrableOn_exp_mul_Iic (by positivity : 0 < c / 2) 0).mono_set Iio_subset_Iic_self).const_mul
    ((k.factorial : ℝ) * (2 / c) ^ k)
  refine hint.mono' (by fun_prop : Continuous fun u : ℝ => |u| ^ k * Real.exp (c * u)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  rw [Real.norm_of_nonneg (by positivity)]
  exact abs_pow_mul_exp_le hc k (le_of_lt (mem_Iio.mp hu))

lemma LapOK.mk' {X : ℝ → ℝ} (hcont : Continuous X)
    (hneg : ∀ c : ℝ, 0 < c → ∀ k : ℕ, IntegrableOn (fun u : ℝ => |u| ^ k * |X u| * Real.exp (c * u)) (Iio 0))
    (hpos : ∃ C α : ℝ, 0 < α ∧ ∀ u : ℝ, 0 ≤ u → |X u| ≤ C * Real.exp (-α * u ^ (3 / 2 : ℝ))) : LapOK X where
  cont := hcont
  integ c hc k := by
    obtain ⟨C, α, hα, hb⟩ := hpos
    have hposint : IntegrableOn (fun u : ℝ => |u| ^ k * |X u| * Real.exp (c * u)) (Ici 0) := by
      have h0 := (integrableOn_exp_neg_rpow32_add hα (by positivity : (0 : ℝ) ≤ c + 1)).const_mul
        ((k.factorial : ℝ) * |C|)
      refine h0.mono' (by have := hcont; fun_prop : Continuous fun u : ℝ => |u| ^ k * |X u| * Real.exp (c * u)).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
      have hu0 : 0 ≤ u := hu
      have e1 : |u| ^ k ≤ (k.factorial : ℝ) * Real.exp u := by
        have := Real.pow_div_factorial_le_exp u hu0 k
        rw [abs_of_nonneg hu0]
        exact (div_le_iff₀ (by positivity : (0 : ℝ) < k.factorial)).mp this |>.trans_eq (by ring)
      have e2 : |X u| ≤ |C| * Real.exp (-α * u ^ (3 / 2 : ℝ)) :=
        (hb u hu0).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
      rw [Real.norm_of_nonneg (by positivity)]
      calc |u| ^ k * |X u| * Real.exp (c * u) ≤ ((k.factorial : ℝ) * Real.exp u) * (|C| * Real.exp (-α * u ^ (3 / 2 : ℝ))) * Real.exp (c * u) := by
            gcongr
        _ = (k.factorial : ℝ) * |C| * Real.exp (-α * u ^ (3 / 2 : ℝ) + (c + 1) * u) := by
            rw [Real.exp_add]
            have : Real.exp ((c + 1) * u) = Real.exp u * Real.exp (c * u) := by rw [← Real.exp_add]; congr 1; ring
            rw [this]; ring
    rw [← integrableOn_univ, ← Set.Iio_union_Ici (a := (0 : ℝ))]
    exact (hneg c hc k).union hposint

lemma LapOK.of_integrable {X : ℝ → ℝ} (hcont : Continuous X) (hint : Integrable X)
    (hpos : ∃ C α : ℝ, 0 < α ∧ ∀ u : ℝ, 0 ≤ u → |X u| ≤ C * Real.exp (-α * u ^ (3 / 2 : ℝ))) : LapOK X := by
  refine LapOK.mk' hcont (fun c hc k => ?_) hpos
  refine (hint.abs.integrableOn.const_mul ((k.factorial : ℝ) * (2 / c) ^ k)).mono'
    (by have := hcont; fun_prop : Continuous fun u : ℝ => |u| ^ k * |X u| * Real.exp (c * u)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  have hu0 : u ≤ 0 := le_of_lt (mem_Iio.mp hu)
  rw [Real.norm_of_nonneg (by positivity)]
  have h1 := abs_pow_mul_exp_le hc k hu0
  have h2 : Real.exp (c / 2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu0)
  calc |u| ^ k * |X u| * Real.exp (c * u) = |X u| * (|u| ^ k * Real.exp (c * u)) := by ring
    _ ≤ |X u| * ((k.factorial : ℝ) * (2 / c) ^ k * 1) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) (abs_nonneg _)
        calc (k.factorial : ℝ) * (2 / c) ^ k * Real.exp (c / 2 * u) ≤ (k.factorial : ℝ) * (2 / c) ^ k * 1 :=
              mul_le_mul_of_nonneg_left h2 (by positivity)
          _ = _ := rfl
    _ = _ := by ring

lemma LapOK.of_linear {X : ℝ → ℝ} (hcont : Continuous X) (C₀ : ℝ) (hneg : ∀ u : ℝ, u < 0 → |X u| ≤ C₀ * (1 + |u|))
    (hpos : ∃ C α : ℝ, 0 < α ∧ ∀ u : ℝ, 0 ≤ u → |X u| ≤ C * Real.exp (-α * u ^ (3 / 2 : ℝ))) : LapOK X := by
  refine LapOK.mk' hcont (fun c hc k => ?_) hpos
  have hC0 : 0 ≤ C₀ := by
    have := (abs_nonneg (X (-1))).trans (hneg (-1) (by norm_num))
    simp at this; linarith
  refine (((integrableOn_abs_pow_exp_Iio hc k).add (integrableOn_abs_pow_exp_Iio hc (k + 1))).const_mul C₀).mono'
    (by have := hcont; fun_prop : Continuous fun u : ℝ => |u| ^ k * |X u| * Real.exp (c * u)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
  have hu0 : u < 0 := mem_Iio.mp hu
  rw [Real.norm_of_nonneg (by positivity)]
  calc |u| ^ k * |X u| * Real.exp (c * u) ≤ |u| ^ k * (C₀ * (1 + |u|)) * Real.exp (c * u) := by gcongr; exact hneg u hu0
    _ = C₀ * (|u| ^ k * Real.exp (c * u) + |u| ^ (k + 1) * Real.exp (c * u)) := by simp only [pow_succ]; ring

lemma lapOK_ceF1 : LapOK ceF1 := by
  obtain ⟨C, hC, hb⟩ := ceF1_tail_exp_rpow32
  exact LapOK.of_integrable continuous_ceF1 ceF1_integral_eq_zero.1 ⟨C, 2 / 3, by norm_num, hb⟩

lemma lapOK_ceG1 : LapOK (ceG1 (airyZero 1)) := by
  obtain ⟨C, hC, hb⟩ := ceG1_tail_exp_rpow32
  exact LapOK.of_integrable (continuous_ceG1 _) ceG1_integrable ⟨C, 2 / 3, by norm_num, hb⟩

lemma lapOK_ceG1Deriv : LapOK (ceG1Deriv airyDerivFirstZero) := by
  obtain ⟨C, hC, hb⟩ := ceG1Deriv_tail_exp_rpow32
  exact LapOK.of_integrable (continuous_ceG1Deriv _) ceG1Deriv_integral_eq_M.1 ⟨C, 2 / 3, by norm_num, hb⟩

lemma lapOK_airySq : LapOK (fun u => airyAi u ^ 2) := by
  obtain ⟨C, hC, hb⟩ := airyAi_and_deriv_rpow32_decay
  refine LapOK.of_linear (continuous_airyAi.pow 2) 9 (fun u _ => ?_) ⟨C ^ 2, 1, one_pos, fun u hu => ?_⟩
  · rw [abs_pow]
    have h3 := abs_airyAi_le_three u
    nlinarith [abs_nonneg (airyAi u), abs_nonneg u]
  · rw [abs_pow, show C ^ 2 * Real.exp (-1 * u ^ (3 / 2 : ℝ)) = (C * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ))) ^ 2 by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb u hu).1 2

lemma lapOK_airyDerivSq : LapOK (fun u => airyAi' u ^ 2) := by
  obtain ⟨C, hC, hb⟩ := airyAi_and_deriv_rpow32_decay
  refine LapOK.of_linear (continuous_airyAi'.pow 2) 25 (fun u hu => ?_) ⟨C ^ 2, 1, one_pos, fun u hu => ?_⟩
  · rw [abs_pow]
    have h5 := abs_airyAi'_le_of_nonpos hu.le
    have hb1 : (1 + |u|) ^ (1 / 4 : ℝ) ≤ (1 + |u|) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) (by norm_num)
    have hb2 : (1 + |u|) ^ (1 / 2 : ℝ) ≤ 1 + |u| := by
      calc (1 + |u|) ^ (1 / 2 : ℝ) ≤ (1 + |u|) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg u]) (by norm_num)
        _ = 1 + |u| := Real.rpow_one _
    have hsq : ((1 + |u|) ^ (1 / 4 : ℝ)) ^ 2 = (1 + |u|) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [abs_nonneg u])]; norm_num
    calc |airyAi' u| ^ 2 ≤ (5 * (1 + |u|) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
      _ = 25 * (1 + |u|) ^ (1 / 2 : ℝ) := by rw [mul_pow, hsq]; norm_num
      _ ≤ 25 * (1 + |u|) := by gcongr
  · rw [abs_pow, show C ^ 2 * Real.exp (-1 * u ^ (3 / 2 : ℝ)) = (C * Real.exp (-(1 / 2 : ℝ) * u ^ (3 / 2 : ℝ))) ^ 2 by
      rw [mul_pow, ← Real.exp_nat_mul]; ring_nf]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb u hu).2 2

/-! ### The Laplace transforms of `Ai²` and `Ai'²` -/

/-- The constant `(2 √π)⁻¹`. -/
noncomputable def cA : ℝ := (2 * Real.sqrt π)⁻¹

lemma cA_pos : 0 < cA := by unfold cA; positivity

lemma lapC_airySq {y : ℂ} (hy : 0 < y.re) :
    lapC (fun u => airyAi u ^ 2) y = (cA : ℂ) * y ^ (-(1 / 2 : ℂ)) * Complex.exp (y ^ 3 / 12) := by
  have h := (airy_pair_laplace_eq 0 0 hy).2
  rw [rpow_neg_half_mul_four_pi hy] at h
  have hL : lapC (fun u => airyAi u ^ 2) y =
      ∫ u : ℝ, (airyAi (u + 0) : ℂ) * (airyAi (u + 0) : ℂ) * Complex.exp (y * (u : ℂ)) := by
    unfold lapC; refine integral_congr_ae (ae_of_all _ fun u => ?_); push_cast; ring_nf
  rw [hL, h]
  simp [cA]

/-- `d/dy` of the transform of `Ai²`. -/
lemma hasDerivAt_airySq_closed {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => (cA : ℂ) * z ^ (-(1 / 2 : ℂ)) * Complex.exp (z ^ 3 / 12))
      ((cA : ℂ) * (y ^ (-(1 / 2 : ℂ)) * (-(1 / 2 : ℂ) / y + y ^ 2 / 4)) * Complex.exp (y ^ 3 / 12)) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h1 : HasDerivAt (fun z : ℂ => z ^ (-(1 / 2 : ℂ))) (-(1 / 2 : ℂ) * y ^ (-(1 / 2 : ℂ) - 1)) y :=
    (hasDerivAt_id y).cpow_const (Or.inl (by simpa using hy)) |>.congr_deriv (by simp)
  have h2 : HasDerivAt (fun z : ℂ => Complex.exp (z ^ 3 / 12)) (Complex.exp (y ^ 3 / 12) * (y ^ 2 / 4)) y := by
    refine ((((hasDerivAt_pow 3 y).div_const 12).cexp)).congr_deriv ?_
    norm_num; ring
  have := ((h1.const_mul (cA : ℂ)).mul h2)
  convert this using 1
  rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one]
  field_simp

lemma lapC_airySq_mulX {y : ℂ} (hy : 0 < y.re) :
    lapC (fun u => u * airyAi u ^ 2) y =
      (cA : ℂ) * (y ^ (-(1 / 2 : ℂ)) * (-(1 / 2 : ℂ) / y + y ^ 2 / 4)) * Complex.exp (y ^ 3 / 12) := by
  have hd1 := hasDerivAt_lapC lapOK_airySq hy
  have hd2 := hasDerivAt_airySq_closed hy
  have hev : lapC (fun u => airyAi u ^ 2) =ᶠ[𝓝 y] fun z => (cA : ℂ) * z ^ (-(1 / 2 : ℂ)) * Complex.exp (z ^ 3 / 12) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hy] with z hz using lapC_airySq hz
  exact hd1.unique (hd2.congr_of_eventuallyEq hev)

/-- The first integral `Q = Ai'² - u Ai²` of the Airy product ODE, `Q' = -Ai²`. -/
lemma lapC_Q {y : ℂ} (hy : 0 < y.re) :
    lapC (fun u => airyAi' u ^ 2 - u * airyAi u ^ 2) y * y = lapC (fun u => airyAi u ^ 2) y := by
  have iA : Integrable (fun u : ℝ => ((airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) := by
    simpa using lapOK_airySq.integrable_cplx hy 0
  have iB : Integrable (fun u : ℝ => ((u * airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
    (lapOK_airySq.mulX.integrable_cplx hy 0).congr (ae_of_all _ fun u => by simp)
  have iC : Integrable (fun u : ℝ => ((airyAi' u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) := by
    simpa using lapOK_airyDerivSq.integrable_cplx hy 0
  have hQint : Integrable (fun u : ℝ => ((airyAi' u ^ 2 - u * airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
    (iC.sub iB).congr (ae_of_all _ fun u => by simp only [Pi.sub_apply]; push_cast; ring)
  let f : ℝ → ℂ := fun u => ((airyAi' u ^ 2 - u * airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))
  let f' : ℝ → ℂ := fun u => -(((airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) +
    y * (((airyAi' u ^ 2 - u * airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ)))
  have hderiv : ∀ u : ℝ, HasDerivAt f (f' u) u := fun u => by
    have hq : HasDerivAt (fun t : ℝ => airyAi' t ^ 2 - t * airyAi t ^ 2) (-(airyAi u ^ 2)) u := by
      have := ((hasDerivAt_airyAi' u).pow 2).sub ((hasDerivAt_id u).mul ((hasDerivAt_airyAi u).pow 2))
      refine this.congr_deriv ?_
      simp only [id, Pi.pow_apply]; push_cast; ring
    have he : HasDerivAt (fun t : ℝ => Complex.exp (y * (t : ℂ))) (Complex.exp (y * (u : ℂ)) * y) u := by
      have h0 : HasDerivAt (fun t : ℝ => y * (t : ℂ)) y u := by
        simpa using (((hasDerivAt_id (u : ℂ)).const_mul y).comp_ofReal)
      exact h0.cexp
    refine (hq.ofReal_comp.mul he).congr_deriv ?_
    simp only [f']; push_cast; ring
  have hf'int : Integrable f' := (iA.neg).add (hQint.const_mul y)
  have h1 : Tendsto f atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun x _ => hderiv x) hf'int.integrableOn hQint.integrableOn
  have h2 : Tendsto f atBot (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun x _ => hderiv x) hf'int.integrableOn hQint.integrableOn
  have h3 := integral_of_hasDerivAt_of_tendsto hderiv hf'int h2 h1
  simp only [sub_zero] at h3
  have h4 : ∫ u : ℝ, f' u = -lapC (fun u => airyAi u ^ 2) y + y * lapC (fun u => airyAi' u ^ 2 - u * airyAi u ^ 2) y := by
    simp only [f']
    have hn : Integrable (fun u : ℝ => -(((airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ)))) := iA.neg
    rw [integral_add hn (hQint.const_mul y), integral_neg, integral_const_mul]
    rfl
  rw [h4] at h3
  linear_combination h3

lemma lapC_airyDerivSq {y : ℂ} (hy : 0 < y.re) :
    lapC (fun u => airyAi' u ^ 2) y =
      (cA : ℂ) * y ^ (-(1 / 2 : ℂ)) * Complex.exp (y ^ 3 / 12) * (y ^ 2 / 4 + 1 / (2 * y)) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have iB : Integrable (fun u : ℝ => ((u * airyAi u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) :=
    (lapOK_airySq.mulX.integrable_cplx hy 0).congr (ae_of_all _ fun u => by simp)
  have iC : Integrable (fun u : ℝ => ((airyAi' u ^ 2 : ℝ) : ℂ) * Complex.exp (y * (u : ℂ))) := by
    simpa using lapOK_airyDerivSq.integrable_cplx hy 0
  have hsplit : lapC (fun u => airyAi' u ^ 2) y =
      lapC (fun u => airyAi' u ^ 2 - u * airyAi u ^ 2) y + lapC (fun u => u * airyAi u ^ 2) y := by
    unfold lapC
    rw [← integral_add ((iC.sub iB).congr (ae_of_all _ fun u => by simp only [Pi.sub_apply]; push_cast; ring)) iB]
    refine integral_congr_ae (ae_of_all _ fun u => ?_)
    push_cast; ring
  have hQ : lapC (fun u => airyAi' u ^ 2 - u * airyAi u ^ 2) y = lapC (fun u => airyAi u ^ 2) y / y :=
    eq_div_of_mul_eq hy0 (lapC_Q hy)
  rw [hsplit, hQ, lapC_airySq hy, lapC_airySq_mulX hy]
  field_simp
  ring

/-! ### Antiderivatives of `y^{n-1/2} h(y)` with entire `h` -/

lemma rhp_open : IsOpen {y : ℂ | 0 < y.re} := isOpen_lt continuous_const Complex.continuous_re

lemma rhp_preconnected : IsPreconnected {y : ℂ | 0 < y.re} := (convex_halfSpace_re_gt 0).isPreconnected

lemma ode1_unique {D : ℂ → ℂ} (hD : ∀ y : ℂ, 0 < y.re → HasDerivAt D 0 y) :
    ∃ c : ℂ, ∀ y : ℂ, 0 < y.re → D y = c := by
  obtain ⟨a, ha⟩ := rhp_open.exists_is_const_of_deriv_eq_zero rhp_preconnected
    (fun y hy => (hD y hy).differentiableAt.differentiableWithinAt) (fun y hy => by simpa using (hD y hy).deriv)
  exact ⟨a, ha⟩

lemma ode2_unique {D D1 : ℂ → ℂ} (h1 : ∀ y : ℂ, 0 < y.re → HasDerivAt D (D1 y) y)
    (h2 : ∀ y : ℂ, 0 < y.re → HasDerivAt D1 0 y) :
    ∃ c₀ c₁ : ℂ, ∀ y : ℂ, 0 < y.re → D y = c₀ + c₁ * y := by
  obtain ⟨c₁, hc₁⟩ := ode1_unique h2
  obtain ⟨c₀, hc₀⟩ := ode1_unique (D := fun y => D y - c₁ * y) (fun y hy => by
    have h3 : HasDerivAt (fun y => D y - c₁ * y) (D1 y - c₁ * 1) y := (h1 y hy).sub ((hasDerivAt_id y).const_mul c₁)
    simpa [hc₁ y hy] using h3)
  exact ⟨c₀, c₁, fun y hy => by
    have h : D y - c₁ * y = c₀ := hc₀ y hy
    linear_combination h⟩

/-- `H_n[h](y) = 2 ∫₀¹ r^{2n} h(r² y) dr`, so that `y^{n+1/2} H_n[h](y) = ∫₀^y s^{n-1/2} h(s) ds`. -/
noncomputable def sqH (n : ℕ) (h : ℂ → ℂ) (y : ℂ) : ℂ :=
  2 * ∫ r in (0 : ℝ)..1, (r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)

lemma hasDerivAt_sqH (n : ℕ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) (y₀ : ℂ) :
    HasDerivAt (sqH n h)
      (2 * ∫ r in (0 : ℝ)..1, (r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y₀)) y₀ := by
  have hcd : ContDiff ℂ 1 h := hh.contDiff
  have hdc : Continuous (deriv h) := hcd.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (‖y₀‖ + 1)).exists_bound_of_continuousOn hdc.continuousOn
  let F : ℂ → ℝ → ℂ := fun y r => (r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)
  let F' : ℂ → ℝ → ℂ := fun y r => (r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y)
  have hFc : ∀ y, Continuous (F y) := fun y => by
    have := hh.continuous; simp only [F]; fun_prop
  have hF'c : ∀ y, Continuous (F' y) := fun y => by
    have := hdc; simp only [F']; fun_prop
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
    (F := F) (F' := F') (x₀ := y₀) (bound := fun _ => M) (Metric.ball_mem_nhds y₀ one_pos)
    (Eventually.of_forall fun y => (hFc y).aestronglyMeasurable)
    ((hFc y₀).integrableOn_Ioc) (hF'c y₀).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr y hy
      have hr1 : r ≤ 1 := hr.2
      have hr0 : 0 ≤ r := hr.1.le
      have hyn : ‖y‖ ≤ ‖y₀‖ + 1 := by
        have := Metric.mem_ball.mp hy
        rw [Complex.dist_eq] at this
        calc ‖y‖ = ‖(y - y₀) + y₀‖ := by ring_nf
          _ ≤ ‖y - y₀‖ + ‖y₀‖ := norm_add_le _ _
          _ ≤ _ := by linarith
      have hz : ‖(r : ℂ) ^ 2 * y‖ ≤ ‖y₀‖ + 1 := by
        rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
        calc r ^ 2 * ‖y‖ ≤ 1 * (‖y₀‖ + 1) := by
              apply mul_le_mul (pow_le_one₀ hr0 hr1) hyn (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
      have hMb := hM _ (mem_closedBall_zero_iff.mpr hz)
      have hr' : ‖(r : ℂ) ^ (2 * n + 2)‖ ≤ 1 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact pow_le_one₀ hr0 hr1
      simp only [F']
      rw [norm_mul]
      calc ‖(r : ℂ) ^ (2 * n + 2)‖ * ‖deriv h ((r : ℂ) ^ 2 * y)‖ ≤ 1 * M := mul_le_mul hr' hMb (norm_nonneg _) zero_le_one
        _ = M := one_mul _)
    (integrableOn_const (by simp))
    (by
      filter_upwards with r y _
      simp only [F, F']
      have h1 : HasDerivAt (fun z : ℂ => (r : ℂ) ^ 2 * z) ((r : ℂ) ^ 2) y := by simpa using (hasDerivAt_id y).const_mul ((r : ℂ) ^ 2)
      have h2 := ((hh ((r : ℂ) ^ 2 * y)).hasDerivAt.comp y h1).const_mul ((r : ℂ) ^ (2 * n))
      refine h2.congr_deriv ?_
      ring)
  have e1 : (fun y => ∫ r in Set.Ioc (0 : ℝ) 1, F y r) = fun y => ∫ r in (0 : ℝ)..1, F y r := by
    funext y; rw [intervalIntegral.integral_of_le zero_le_one]
  have e2 : ∫ r in Set.Ioc (0 : ℝ) 1, F' y₀ r = ∫ r in (0 : ℝ)..1, F' y₀ r := by
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [e1, e2] at hd
  exact (hd.2.const_mul 2)

/-- Fundamental theorem of calculus for `r ↦ r^{2n+1} h(r² y)`. -/
lemma sqH_ftc (n : ℕ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) (y : ℂ) :
    ∫ r in (0 : ℝ)..1, (((2 * n + 1 : ℕ) : ℂ) * ((r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)) +
      2 * y * ((r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y))) = h y := by
  have hdc : Continuous (deriv h) := (hh.contDiff (n := 1)).continuous_deriv le_rfl
  let f : ℝ → ℂ := fun r => (r : ℂ) ^ (2 * n + 1) * h ((r : ℂ) ^ 2 * y)
  have hder : ∀ r ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt f
      (((2 * n + 1 : ℕ) : ℂ) * ((r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)) +
        2 * y * ((r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y))) r := fun r _ => by
    have h1 : HasDerivAt (fun z : ℂ => z ^ 2 * y) (2 * (r : ℂ) * y) (r : ℂ) := by
      simpa using ((hasDerivAt_pow 2 (r : ℂ)).mul_const y)
    have h2 := (hasDerivAt_pow (2 * n + 1) (r : ℂ)).mul ((hh ((r : ℂ) ^ 2 * y)).hasDerivAt.comp (r : ℂ) h1)
    have h3 := h2.comp_ofReal
    refine h3.congr_deriv ?_
    simp only [Function.comp_apply, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    ring
  have hint : IntervalIntegrable (fun r : ℝ => ((2 * n + 1 : ℕ) : ℂ) * ((r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)) +
      2 * y * ((r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y))) volume 0 1 := by
    have := hh.continuous; have := hdc
    exact (by fun_prop : Continuous fun r : ℝ => ((2 * n + 1 : ℕ) : ℂ) * ((r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)) +
      2 * y * ((r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  simp [f]

lemma hasDerivAt_sqPhi (n : ℕ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => z ^ ((n : ℂ) + 1 / 2) * sqH n h z) (y ^ ((n : ℂ) - 1 / 2) * h y) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have hp : HasDerivAt (fun z : ℂ => z ^ ((n : ℂ) + 1 / 2)) (((n : ℂ) + 1 / 2) * y ^ ((n : ℂ) + 1 / 2 - 1)) y :=
    (hasDerivAt_id y).cpow_const (Or.inl (by simpa using hy)) |>.congr_deriv (by simp)
  have hprod := hp.mul (hasDerivAt_sqH n hh y)
  refine hprod.congr_deriv ?_
  have e1 : y ^ ((n : ℂ) + 1 / 2 - 1) = y ^ ((n : ℂ) - 1 / 2) := by congr 1; ring
  have e2 : y ^ ((n : ℂ) + 1 / 2) = y ^ ((n : ℂ) - 1 / 2) * y := by
    rw [show (n : ℂ) + 1 / 2 = ((n : ℂ) - 1 / 2) + 1 by ring, Complex.cpow_add _ _ hy0, Complex.cpow_one]
  have hft := sqH_ftc n hh y
  have hint1 : IntervalIntegrable (fun r : ℝ => (r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)) volume 0 1 := by
    have := hh.continuous
    exact (by fun_prop : Continuous fun r : ℝ => (r : ℂ) ^ (2 * n) * h ((r : ℂ) ^ 2 * y)).intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun r : ℝ => (r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y)) volume 0 1 := by
    have := (hh.contDiff (n := 1)).continuous_deriv le_rfl
    exact (by fun_prop : Continuous fun r : ℝ => (r : ℂ) ^ (2 * n + 2) * deriv h ((r : ℂ) ^ 2 * y)).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add (hint1.const_mul _) (hint2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hft
  unfold sqH
  rw [e1, e2]
  have hc : ((2 * n + 1 : ℕ) : ℂ) = 2 * ((n : ℂ) + 1 / 2) := by push_cast; ring
  rw [hc] at hft
  linear_combination (y ^ ((n : ℂ) - 1 / 2)) * hft

/-! ### The square-root form of the seed transforms -/

/-- `T = A + y^{1/2} B` on `Re y > 0` with `A, B` entire and `B(0)` real. -/
def SqForm (T : ℂ → ℂ) : Prop :=
  ∃ A B : ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧ (∃ b : ℝ, B 0 = b) ∧
    ∀ y : ℂ, 0 < y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y

lemma differentiable_sqH (n : ℕ) {h : ℂ → ℂ} (hh : Differentiable ℂ h) : Differentiable ℂ (sqH n h) :=
  fun y => (hasDerivAt_sqH n hh y).differentiableAt

/-- `SqForm` with the value of `B 0` recorded (the real number `b`). -/
def SqFormAt (T : ℂ → ℂ) (b : ℝ) : Prop :=
  ∃ A B : ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧ B 0 = b ∧
    ∀ y : ℂ, 0 < y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y

lemma SqFormAt.sqForm {T : ℂ → ℂ} {b : ℝ} (h : SqFormAt T b) : SqForm T := by
  obtain ⟨A, B, hA, hB, hb, he⟩ := h
  exact ⟨A, B, hA, hB, ⟨b, hb⟩, he⟩

lemma SqFormAt.of_eq {T : ℂ → ℂ} {b b' : ℝ} (h : SqFormAt T b) (e : b = b') : SqFormAt T b' := e ▸ h

lemma sqFormAt_of_mod {X : ℝ → ℝ} (a : ℝ) {Bm : ℂ → ℂ} (hBm : Differentiable ℂ Bm) {c₀ c₁ : ℂ} {b : ℝ}
    (hb : (ceK : ℂ) * Bm 0 = b)
    (hP : ∀ y : ℂ, 0 < y.re →
      Complex.exp (-(a : ℂ) * y) * lapC X y = c₀ + c₁ * y + y ^ (1 / 2 : ℂ) * Bm y) :
    SqFormAt (airyTwistedLaplaceC X) b := by
  refine ⟨fun y => (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12 + a * y) * (c₀ + c₁ * y),
    fun y => (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12 + a * y) * Bm y, ?_, ?_, ?_, ?_⟩
  · fun_prop
  · exact (by fun_prop : Differentiable ℂ fun y : ℂ => (ceK : ℂ) * Complex.exp (-(y ^ 3) / 12 + a * y)).mul hBm
  · simpa using hb
  · intro y hy
    have h := hP y hy
    rw [airyTwistedLaplaceC_eq_lapC]
    have : lapC X y = Complex.exp ((a : ℂ) * y) * (Complex.exp (-(a : ℂ) * y) * lapC X y) := by
      rw [← mul_assoc, ← Complex.exp_add]; simp
    beta_reduce
    rw [this, h, Complex.exp_add]; ring

lemma sqForm_of_mod {X : ℝ → ℝ} (a : ℝ) {Bm : ℂ → ℂ} (hBm : Differentiable ℂ Bm) {c₀ c₁ : ℂ}
    (hb : ∃ b : ℝ, (ceK : ℂ) * Bm 0 = b)
    (hP : ∀ y : ℂ, 0 < y.re →
      Complex.exp (-(a : ℂ) * y) * lapC X y = c₀ + c₁ * y + y ^ (1 / 2 : ℂ) * Bm y) :
    SqForm (airyTwistedLaplaceC X) := by
  obtain ⟨b, hb⟩ := hb
  exact (sqFormAt_of_mod a hBm hb hP).sqForm

/-- The entire factor `h(y) = (2√π)⁻¹ e^{-ay + y³/12}`. -/
noncomputable def hExp (a : ℝ) (y : ℂ) : ℂ := (cA : ℂ) * Complex.exp (-(a : ℂ) * y + y ^ 3 / 12)

lemma differentiable_hExp (a : ℝ) : Differentiable ℂ (hExp a) := by unfold hExp; fun_prop

lemma modLap_airySq (a : ℝ) {y : ℂ} (hy : 0 < y.re) :
    Complex.exp (-(a : ℂ) * y) * lapC (fun u => airyAi u ^ 2) y = y ^ (-(1 / 2 : ℂ)) * hExp a y := by
  rw [lapC_airySq hy]; unfold hExp; rw [Complex.exp_add]; ring

lemma hasDerivAt_sqPhi0 (a : ℝ) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ) * sqH 0 (hExp a) z) (y ^ (-(1 / 2 : ℂ)) * hExp a y) y := by
  have := hasDerivAt_sqPhi 0 (differentiable_hExp a) hy
  simpa using this

lemma sub_dslope_zero {g : ℝ → ℝ} {a : ℝ} (hga : g a = 0) (u : ℝ) : (u - a) * dslope g a u = g u := by
  have := sub_smul_dslope g a u
  simpa [smul_eq_mul, hga] using this

lemma ceF1_mul (u : ℝ) : (u - airyZero 1) * ceF1 u = airyAi u ^ 2 := by
  unfold ceF1
  have := sub_dslope_zero (airyAi_airyZero 1) u
  calc (u - airyZero 1) * (airyAi u * dslope airyAi (airyZero 1) u) = airyAi u * ((u - airyZero 1) * dslope airyAi (airyZero 1) u) := by ring
    _ = _ := by rw [this]; ring

lemma ceG1_mul_eq_ceF1 (u : ℝ) : (u - airyZero 1) * ceG1 (airyZero 1) u = ceF1 u := by
  unfold ceG1 ceF1
  have := sub_dslope_zero (airyAi_airyZero 1) u
  calc (u - airyZero 1) * dslope airyAi (airyZero 1) u ^ 2 = dslope airyAi (airyZero 1) u * ((u - airyZero 1) * dslope airyAi (airyZero 1) u) := by ring
    _ = _ := by rw [this]; ring

lemma ceG1Deriv_mul2 (u : ℝ) :
    (u - airyDerivFirstZero) * ((u - airyDerivFirstZero) * ceG1Deriv airyDerivFirstZero u) = airyAi' u ^ 2 := by
  unfold ceG1Deriv
  have := sub_dslope_zero (g := airyAi') airyDerivFirstZero_spec.2.2 u
  calc (u - airyDerivFirstZero) * ((u - airyDerivFirstZero) * dslope airyAi' airyDerivFirstZero u ^ 2)
      = ((u - airyDerivFirstZero) * dslope airyAi' airyDerivFirstZero u) ^ 2 := by ring
    _ = _ := by rw [this]

lemma lapC_congr {X Y : ℝ → ℝ} (h : ∀ u, X u = Y u) : lapC X = lapC Y := by
  have : X = Y := funext h
  rw [this]

lemma modLap_ceF1_form : ∃ c : ℂ, ∀ y : ℂ, 0 < y.re →
    Complex.exp (-(airyZero 1 : ℂ) * y) * lapC ceF1 y = c + y ^ (1 / 2 : ℂ) * sqH 0 (hExp (airyZero 1)) y := by
  let a := airyZero 1
  have hM : ∀ y : ℂ, 0 < y.re → HasDerivAt (fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC ceF1 z)
      (y ^ (-(1 / 2 : ℂ)) * hExp a y) y := fun y hy => by
    have := hasDerivAt_modLap lapOK_ceF1 a hy
    rw [lapC_congr (Y := fun u => airyAi u ^ 2) ceF1_mul, modLap_airySq a hy] at this
    exact this
  obtain ⟨c, hc⟩ := ode1_unique (D := fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC ceF1 z - z ^ (1 / 2 : ℂ) * sqH 0 (hExp a) z)
    (fun y hy => by
      have h3 : HasDerivAt (fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC ceF1 z - z ^ (1 / 2 : ℂ) * sqH 0 (hExp a) z)
          (y ^ (-(1 / 2 : ℂ)) * hExp a y - y ^ (-(1 / 2 : ℂ)) * hExp a y) y := (hM y hy).sub (hasDerivAt_sqPhi0 a hy)
      rwa [sub_self] at h3)
  refine ⟨c, fun y hy => ?_⟩
  have h : Complex.exp (-(a : ℂ) * y) * lapC ceF1 y - y ^ (1 / 2 : ℂ) * sqH 0 (hExp a) y = c := hc y hy
  linear_combination h

lemma sqFormAt_ceF1 : SqFormAt (airyTwistedLaplaceC ceF1) (2 * ceK * cA) := by
  obtain ⟨c, hc⟩ := modLap_ceF1_form
  refine sqFormAt_of_mod (airyZero 1) (Bm := sqH 0 (hExp (airyZero 1))) (differentiable_sqH 0 (differentiable_hExp _))
    (c₀ := c) (c₁ := 0) ?_ (fun y hy => by rw [hc y hy]; ring)
  simp [sqH, hExp]; ring

lemma sqForm_ceF1 : SqForm (airyTwistedLaplaceC ceF1) := sqFormAt_ceF1.sqForm

lemma hasDerivAt_sqPhi0' {h : ℂ → ℂ} (hh : Differentiable ℂ h) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ) * sqH 0 h z) (y ^ (-(1 / 2 : ℂ)) * h y) y := by
  have := hasDerivAt_sqPhi 0 hh hy
  simpa using this

lemma pow_nat_one_half {y : ℂ} (hy0 : y ≠ 0) : y ^ (((1 : ℕ) : ℂ) + 1 / 2) = y ^ (1 / 2 : ℂ) * y := by
  rw [Nat.cast_one, add_comm, Complex.cpow_add _ _ hy0, Complex.cpow_one]

lemma hasDerivAt_sqPhi1 {h : ℂ → ℂ} (hh : Differentiable ℂ h) {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => z ^ (((1 : ℕ) : ℂ) + 1 / 2) * sqH 1 h z) (y ^ (1 / 2 : ℂ) * h y) y := by
  have := hasDerivAt_sqPhi 1 hh hy
  rwa [show ((1 : ℕ) : ℂ) - 1 / 2 = 1 / 2 by norm_num] at this

lemma sqFormAt_ceG1 : SqFormAt (airyTwistedLaplaceC (ceG1 (airyZero 1))) 0 := by
  let a := airyZero 1
  obtain ⟨c, hc⟩ := modLap_ceF1_form
  have hH0 : Differentiable ℂ (sqH 0 (hExp a)) := differentiable_sqH 0 (differentiable_hExp a)
  have hM : ∀ y : ℂ, 0 < y.re → HasDerivAt (fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC (ceG1 a) z)
      (c + y ^ (1 / 2 : ℂ) * sqH 0 (hExp a) y) y := fun y hy => by
    have := hasDerivAt_modLap lapOK_ceG1 a hy
    rw [lapC_congr (Y := ceF1) ceG1_mul_eq_ceF1, hc y hy] at this
    exact this
  have hΨ : ∀ y : ℂ, 0 < y.re → HasDerivAt (fun z : ℂ => c * z + z ^ (((1 : ℕ) : ℂ) + 1 / 2) * sqH 1 (sqH 0 (hExp a)) z)
      (c + y ^ (1 / 2 : ℂ) * sqH 0 (hExp a) y) y := fun y hy => by
    exact (((hasDerivAt_id y).const_mul c).add (hasDerivAt_sqPhi1 hH0 hy)).congr_deriv (by simp)
  obtain ⟨c₀, hc₀⟩ := ode1_unique
    (D := fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC (ceG1 a) z - (c * z + z ^ (((1 : ℕ) : ℂ) + 1 / 2) * sqH 1 (sqH 0 (hExp a)) z))
    (fun y hy => by
      have h3 : HasDerivAt (fun z : ℂ => Complex.exp (-(a : ℂ) * z) * lapC (ceG1 a) z - (c * z + z ^ (((1 : ℕ) : ℂ) + 1 / 2) * sqH 1 (sqH 0 (hExp a)) z))
          (c + y ^ (1 / 2 : ℂ) * sqH 0 (hExp a) y - (c + y ^ (1 / 2 : ℂ) * sqH 0 (hExp a) y)) y := (hM y hy).sub (hΨ y hy)
      rwa [sub_self] at h3)
  refine sqFormAt_of_mod a (Bm := fun y => y * sqH 1 (sqH 0 (hExp a)) y)
    (differentiable_id.mul (differentiable_sqH 1 hH0)) (c₀ := c₀) (c₁ := c) (b := 0) (by simp) (fun y hy => ?_)
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h : Complex.exp (-(a : ℂ) * y) * lapC (ceG1 a) y - (c * y + y ^ (((1 : ℕ) : ℂ) + 1 / 2) * sqH 1 (sqH 0 (hExp a)) y) = c₀ := hc₀ y hy
  rw [pow_nat_one_half hy0] at h
  linear_combination h

lemma sqForm_ceG1 : SqForm (airyTwistedLaplaceC (ceG1 (airyZero 1))) := sqFormAt_ceG1.sqForm

/-- The entire function `k(y) = (2√π)⁻¹ e^{-ay + y³/12} (1/2 + y³/4)` with `y^{-3/2} k(y) = e^{-ay} Λ_{Ai'²}(y)`. -/
noncomputable def kExp (a : ℝ) (y : ℂ) : ℂ := (cA : ℂ) * Complex.exp (-(a : ℂ) * y + y ^ 3 / 12) * (1 / 2 + y ^ 3 / 4)

lemma differentiable_kExp (a : ℝ) : Differentiable ℂ (kExp a) := by unfold kExp; fun_prop

lemma kExp_zero (a : ℝ) : kExp a 0 = (cA : ℂ) / 2 := by simp [kExp]; ring

lemma differentiable_dslope_zero {k : ℂ → ℂ} (hk : Differentiable ℂ k) : Differentiable ℂ (dslope k 0) := by
  have := (differentiableOn_dslope (c := (0 : ℂ)) (s := Set.univ) Filter.univ_mem).mpr hk.differentiableOn
  exact differentiableOn_univ.mp this

lemma modLap_airyDerivSq (a : ℝ) {y : ℂ} (hy : 0 < y.re) :
    Complex.exp (-(a : ℂ) * y) * lapC (fun u => airyAi' u ^ 2) y = y ^ (-(1 / 2 : ℂ)) * (kExp a y / y) := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  rw [lapC_airyDerivSq hy]; unfold kExp; rw [Complex.exp_add]
  field_simp
  ring

lemma hasDerivAt_sqrt_cpow {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * y ^ (-(1 / 2 : ℂ))) y := by
  refine ((hasDerivAt_id y).cpow_const (Or.inl (by simpa using hy))).congr_deriv ?_
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring]; simp

lemma hasDerivAt_inv_sqrt_cpow {y : ℂ} (hy : 0 < y.re) :
    HasDerivAt (fun z : ℂ => z ^ (-(1 / 2 : ℂ))) (-(1 / 2 : ℂ) * (y ^ (-(1 / 2 : ℂ)) / y)) y := by
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  refine ((hasDerivAt_id y).cpow_const (Or.inl (by simpa using hy))).congr_deriv ?_
  simp only [id_eq]
  rw [Complex.cpow_sub _ _ hy0, Complex.cpow_one]; ring

lemma sqFormAt_ceG1Deriv : SqFormAt (airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero)) (-2 * ceK * cA) := by
  let a := airyDerivFirstZero
  let k := kExp a
  let k₁ := dslope k 0
  have hk₁ : Differentiable ℂ k₁ := differentiable_dslope_zero (differentiable_kExp a)
  have hH0 : Differentiable ℂ (sqH 0 k₁) := differentiable_sqH 0 hk₁
  have hk : ∀ y : ℂ, k y = (cA : ℂ) / 2 + y * k₁ y := fun y => by
    have := sub_smul_dslope k 0 y
    simp only [smul_eq_mul, sub_zero] at this
    have h0 : k 0 = (cA : ℂ) / 2 := kExp_zero a
    rw [h0] at this
    linear_combination -this
  let Ψ : ℂ → ℂ := fun z => -4 * ((cA : ℂ) / 2) * z ^ (1 / 2 : ℂ) + z ^ (((1 : ℕ) : ℂ) + 1 / 2) * sqH 1 (sqH 0 k₁) z
  let Ψ1 : ℂ → ℂ := fun z => -2 * ((cA : ℂ) / 2) * z ^ (-(1 / 2 : ℂ)) + z ^ (1 / 2 : ℂ) * sqH 0 k₁ z
  let Y : ℂ → ℂ := fun z => Complex.exp (-(a : ℂ) * z) * lapC (ceG1Deriv a) z
  let Y1 : ℂ → ℂ := fun z => Complex.exp (-(a : ℂ) * z) * lapC (fun u => (u - a) * ceG1Deriv a u) z
  have hΨ : ∀ y : ℂ, 0 < y.re → HasDerivAt Ψ (Ψ1 y) y := fun y hy => by
    have h1 := ((hasDerivAt_sqrt_cpow hy).const_mul (-4 * ((cA : ℂ) / 2))).add (hasDerivAt_sqPhi1 hH0 hy)
    refine h1.congr_deriv ?_
    simp only [Ψ1]; ring
  have hΨ1 : ∀ y : ℂ, 0 < y.re → HasDerivAt Ψ1 (y ^ (-(1 / 2 : ℂ)) * (kExp a y / y)) y := fun y hy => by
    have hy0 : y ≠ 0 := fun h => by simp [h] at hy
    have h1 := ((hasDerivAt_inv_sqrt_cpow hy).const_mul (-2 * ((cA : ℂ) / 2))).add (hasDerivAt_sqPhi0' hk₁ hy)
    refine h1.congr_deriv ?_
    show _ = y ^ (-(1 / 2 : ℂ)) * (k y / y)
    rw [hk y]
    field_simp
  have hY : ∀ y : ℂ, 0 < y.re → HasDerivAt Y (Y1 y) y := fun y hy => hasDerivAt_modLap lapOK_ceG1Deriv a hy
  have hY1 : ∀ y : ℂ, 0 < y.re → HasDerivAt Y1 (y ^ (-(1 / 2 : ℂ)) * (kExp a y / y)) y := fun y hy => by
    have := hasDerivAt_modLap (lapOK_ceG1Deriv.shift a) a hy
    rw [lapC_congr (Y := fun u => airyAi' u ^ 2) ceG1Deriv_mul2, modLap_airyDerivSq a hy] at this
    exact this
  obtain ⟨c₀, c₁, hc⟩ := ode2_unique (D := fun z => Y z - Ψ z) (D1 := fun z => Y1 z - Ψ1 z)
    (fun y hy => (hY y hy).sub (hΨ y hy))
    (fun y hy => by
      have h3 : HasDerivAt (fun z => Y1 z - Ψ1 z) (y ^ (-(1 / 2 : ℂ)) * (kExp a y / y) - y ^ (-(1 / 2 : ℂ)) * (kExp a y / y)) y :=
        (hY1 y hy).sub (hΨ1 y hy)
      rwa [sub_self] at h3)
  refine sqFormAt_of_mod a (Bm := fun y => -4 * ((cA : ℂ) / 2) + y * sqH 1 (sqH 0 k₁) y)
    (differentiable_const _ |>.add (differentiable_id.mul (differentiable_sqH 1 hH0))) (c₀ := c₀) (c₁ := c₁)
    (b := -2 * ceK * cA) (by simp; ring) (fun y hy => ?_)
  have hy0 : y ≠ 0 := fun h => by simp [h] at hy
  have h : Y y - Ψ y = c₀ + c₁ * y := hc y hy
  simp only [Ψ] at h
  rw [pow_nat_one_half hy0] at h
  show Y y = _
  linear_combination h

lemma sqForm_ceG1Deriv : SqForm (airyTwistedLaplaceC (ceG1Deriv airyDerivFirstZero)) := sqFormAt_ceG1Deriv.sqForm

/-! ### Closure of `SqForm` and the combinations -/

lemma SqForm.smul {T : ℂ → ℂ} (h : SqForm T) (c : ℝ) : SqForm (fun y => (c : ℂ) * T y) := by
  obtain ⟨A, B, hA, hB, ⟨b, hb⟩, he⟩ := h
  refine ⟨fun y => (c : ℂ) * A y, fun y => (c : ℂ) * B y, hA.const_mul _, hB.const_mul _, ⟨c * b, ?_⟩, fun y hy => ?_⟩
  · simp [hb]
  · simp only [he y hy]; ring

lemma SqForm.add {T U : ℂ → ℂ} (h : SqForm T) (h' : SqForm U) : SqForm (fun y => T y + U y) := by
  obtain ⟨A, B, hA, hB, ⟨b, hb⟩, he⟩ := h
  obtain ⟨A', B', hA', hB', ⟨b', hb'⟩, he'⟩ := h'
  refine ⟨fun y => A y + A' y, fun y => B y + B' y, hA.add hA', hB.add hB', ⟨b + b', ?_⟩, fun y hy => ?_⟩
  · simp [hb, hb']
  · simp only [he y hy, he' y hy]; ring

lemma SqForm.congr {T U : ℂ → ℂ} (h : SqForm T) (he : ∀ y : ℂ, 0 < y.re → T y = U y) : SqForm U := by
  obtain ⟨A, B, hA, hB, hb, hT⟩ := h
  exact ⟨A, B, hA, hB, hb, fun y hy => (he y hy).symm.trans (hT y hy)⟩

lemma SqFormAt.smul {T : ℂ → ℂ} {b : ℝ} (h : SqFormAt T b) (c : ℝ) : SqFormAt (fun y => (c : ℂ) * T y) (c * b) := by
  obtain ⟨A, B, hA, hB, hb, he⟩ := h
  refine ⟨fun y => (c : ℂ) * A y, fun y => (c : ℂ) * B y, hA.const_mul _, hB.const_mul _, ?_, fun y hy => ?_⟩
  · simp [hb]
  · simp only [he y hy]; ring

lemma SqFormAt.add {T U : ℂ → ℂ} {b b' : ℝ} (h : SqFormAt T b) (h' : SqFormAt U b') :
    SqFormAt (fun y => T y + U y) (b + b') := by
  obtain ⟨A, B, hA, hB, hb, he⟩ := h
  obtain ⟨A', B', hA', hB', hb', he'⟩ := h'
  refine ⟨fun y => A y + A' y, fun y => B y + B' y, hA.add hA', hB.add hB', ?_, fun y hy => ?_⟩
  · simp [hb, hb']
  · simp only [he y hy, he' y hy]; ring

lemma SqFormAt.congr {T U : ℂ → ℂ} {b : ℝ} (h : SqFormAt T b) (he : ∀ y : ℂ, 0 < y.re → T y = U y) : SqFormAt U b := by
  obtain ⟨A, B, hA, hB, hb, hT⟩ := h
  exact ⟨A, B, hA, hB, hb, fun y hy => (he y hy).symm.trans (hT y hy)⟩

/-- **The value of `B 0` for the one-level seeds**: `a f₁ + b g₁ + c g₁'` has square-root coefficient `B 0 = (a - c) · 2 k c_A`
(`f₁`: `2 k c_A`, `g₁`: `0`, `g₁'`: `-2 k c_A`). -/
theorem airySeedU2_sqFormAt (a b c : ℝ) :
    SqFormAt (airyTwistedLaplaceC (airySeedU2 a b c)) ((a - c) * (2 * ceK * cA)) := by
  have h := ((sqFormAt_ceF1.smul a).add (sqFormAt_ceG1.smul b)).add (sqFormAt_ceG1Deriv.smul c)
  refine (h.congr fun y hy => by rw [airySeedU2_transform a b c hy.le]).of_eq ?_
  ring

theorem airySeedU2_sqForm (a b c : ℝ) : SqForm (airyTwistedLaplaceC (airySeedU2 a b c)) :=
  (airySeedU2_sqFormAt a b c).sqForm

/-- On the closed half-plane the square-root form persists by continuity (value of `B 0` recorded). -/
lemma SqFormAt.closed {T : ℂ → ℂ} {b : ℝ} (h : SqFormAt T b) (hcont : ContinuousOn T {y : ℂ | 0 ≤ y.re}) :
    ∃ A B : ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧ B 0 = b ∧
      ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y := by
  obtain ⟨A, B, hA, hB, hb, he⟩ := h
  refine ⟨A, B, hA, hB, hb, ?_⟩
  have hcont2 : ContinuousOn (fun y : ℂ => A y + y ^ (1 / 2 : ℂ) * B y) {y : ℂ | 0 ≤ y.re} := by
    have hs : ContinuousOn (fun y : ℂ => y ^ (1 / 2 : ℂ)) {y : ℂ | 0 ≤ y.re} := fun y hy =>
      (Complex.continuousAt_cpow_const_of_re_pos (Or.inl hy) (by norm_num)).continuousWithinAt
    exact hA.continuous.continuousOn.add (hs.mul hB.continuous.continuousOn)
  have hEq : Set.EqOn T (fun y : ℂ => A y + y ^ (1 / 2 : ℂ) * B y) {y : ℂ | 0 ≤ y.re} :=
    Set.EqOn.of_subset_closure (s := {y : ℂ | 0 < y.re}) (fun y hy => he y hy) hcont hcont2
      (fun y (hy : y ∈ {y : ℂ | 0 < y.re}) => (le_of_lt (show 0 < y.re from hy) : 0 ≤ y.re)) (by rw [Complex.closure_setOfPred_lt_re])
  exact fun y hy => hEq hy

/-- On the closed half-plane the square-root form persists by continuity. -/
lemma SqForm.closed {T : ℂ → ℂ} (h : SqForm T) (hcont : ContinuousOn T {y : ℂ | 0 ≤ y.re}) :
    ∃ A B : ℂ → ℂ, Differentiable ℂ A ∧ Differentiable ℂ B ∧ (∃ b : ℝ, B 0 = b) ∧
      ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y := by
  obtain ⟨A, B, hA, hB, ⟨b, hb⟩, he⟩ := h
  have h' : SqFormAt T b := ⟨A, B, hA, hB, hb, he⟩
  obtain ⟨A', B', hA', hB', hb', he'⟩ := h'.closed hcont
  exact ⟨A', B', hA', hB', ⟨b, hb'⟩, he'⟩

/-! ### The subtracted symbol: the points `c_s (iv)` -/

/-- The point `c_s · (i v)` on the imaginary axis. -/
noncomputable def yv (v : ℝ) : ℂ := (ceCs : ℂ) * ((v : ℂ) * Complex.I)

lemma yv_re (v : ℝ) : (yv v).re = 0 := by simp [yv, Complex.mul_re]

lemma yv_im (v : ℝ) : (yv v).im = ceCs * v := by simp [yv, Complex.mul_im]

lemma yv_ne {v : ℝ} (hv : v ≠ 0) : yv v ≠ 0 := fun h => by
  have := yv_im v; rw [h] at this; simp at this
  rcases this with h | h
  · exact ceCs_pos.ne' h
  · exact hv h

lemma norm_yv (v : ℝ) : ‖yv v‖ = ceCs * |v| := by
  simp [yv, abs_of_pos ceCs_pos]

lemma yv_mem_slit {v : ℝ} (hv : v ≠ 0) : yv v ∈ Complex.slitPlane := by
  refine Or.inr ?_
  rw [yv_im]; exact mul_ne_zero ceCs_pos.ne' hv

lemma contDiff_yv {n : WithTop ℕ∞} : ContDiff ℝ n yv := by
  unfold yv
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.mul contDiff_const)

lemma continuous_yv : Continuous yv := (contDiff_yv (n := 0)).continuous

lemma hasDerivAt_yv (v : ℝ) : HasDerivAt yv ((ceCs : ℂ) * Complex.I) v := by
  have h0 : HasDerivAt (fun z : ℂ => (ceCs : ℂ) * (z * Complex.I)) ((ceCs : ℂ) * Complex.I) (v : ℂ) := by
    simpa using ((hasDerivAt_id (v : ℂ)).mul_const Complex.I).const_mul (ceCs : ℂ)
  exact h0.comp_ofReal

lemma ceCs_one_lt : 1 < ceCs := by
  have h3 : (1 : ℝ) < Real.pi ^ 2 / 3 := by
    have := Real.pi_gt_three; nlinarith
  unfold ceCs
  exact Real.one_lt_rpow h3 (by norm_num)

/-- `√(c_s i v)` along the imaginary axis (principal branch). -/
noncomputable def sq (v : ℝ) : ℂ := (yv v) ^ (1 / 2 : ℂ)

lemma continuous_sq : Continuous sq := by
  refine continuous_iff_continuousAt.mpr fun v => ?_
  exact (Complex.continuousAt_cpow_const_of_re_pos (Or.inl (by rw [yv_re])) (by norm_num)).comp
    continuous_yv.continuousAt

lemma hasDerivAt_sq_ne {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt sq ((1 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I) * (yv v) ^ (-(1 / 2 : ℂ))) v := by
  have h1 : HasDerivAt (fun z : ℂ => z ^ (1 / 2 : ℂ)) ((1 / 2 : ℂ) * (yv v) ^ ((1 / 2 : ℂ) - 1)) (yv v) :=
    ((hasDerivAt_id (yv v)).cpow_const (yv_mem_slit hv)).congr_deriv (by simp)
  have h2 := h1.scomp v (hasDerivAt_yv v)
  refine h2.congr_deriv ?_
  rw [show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by ring]
  simp only [smul_eq_mul]; ring

/-- `s_A(v) = (c_s iv)^{3/2}`. -/
noncomputable def sA (v : ℝ) : ℂ := sq v * yv v

/-- `s_A'(v) = (3/2) c_s i · √(c_s i v)`, continuous through `v = 0`. -/
noncomputable def sA' (v : ℝ) : ℂ := (3 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I) * sq v

lemma continuous_sA' : Continuous sA' := by unfold sA'; have := continuous_sq; fun_prop

lemma hasDerivAt_sA_ne {v : ℝ} (hv : v ≠ 0) : HasDerivAt sA (sA' v) v := by
  have h := (hasDerivAt_sq_ne hv).mul (hasDerivAt_yv v)
  refine h.congr_deriv ?_
  have hw : yv v ≠ 0 := yv_ne hv
  unfold sA' sq
  have : (yv v) ^ (-(1 / 2 : ℂ)) * yv v = (yv v) ^ (1 / 2 : ℂ) := by
    rw [show (yv v) ^ (1 / 2 : ℂ) = (yv v) ^ (-(1 / 2 : ℂ) + 1) by norm_num, Complex.cpow_add _ _ hw, Complex.cpow_one]
  calc (1 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I) * (yv v) ^ (-(1 / 2 : ℂ)) * yv v + (yv v) ^ (1 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I)
      = (1 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I) * ((yv v) ^ (-(1 / 2 : ℂ)) * yv v) + (yv v) ^ (1 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I) := by ring
    _ = _ := by rw [this]; ring

lemma continuous_sA : Continuous sA := by unfold sA; have := continuous_sq; have := continuous_yv; fun_prop

lemma hasDerivAt_sA (v : ℝ) : HasDerivAt sA (sA' v) v := by
  by_cases hv : v = 0
  · subst hv
    exact hasDerivAt_of_hasDerivAt_of_ne (fun y hy => hasDerivAt_sA_ne hy) continuous_sA.continuousAt
      continuous_sA'.continuousAt
  · exact hasDerivAt_sA_ne hv

lemma contDiff_sA : ContDiff ℝ 1 sA :=
  contDiff_one_iff_deriv.mpr ⟨fun v => (hasDerivAt_sA v).differentiableAt, by
    have : deriv sA = sA' := funext fun v => (hasDerivAt_sA v).deriv
    rw [this]; exact continuous_sA'⟩

lemma hasDerivAt_sA'_ne {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt sA' ((3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ))) v := by
  have h := (hasDerivAt_sq_ne hv).const_mul ((3 / 2 : ℂ) * ((ceCs : ℂ) * Complex.I))
  refine h.congr_deriv ?_
  ring

lemma norm_sA'_deriv_le {v : ℝ} (hv : v ≠ 0) :
    ‖(3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ))‖ ≤ (3 / 4) * ceCs ^ 2 * |v| ^ (-(1 / 2 : ℝ)) := by
  have hw : yv v ≠ 0 := yv_ne hv
  have h1 : ‖(yv v) ^ (-(1 / 2 : ℂ))‖ = (ceCs * |v|) ^ (-(1 / 2 : ℝ)) := by
    have := norm_cpow_ofReal_exponent hw (-(1 / 2 : ℝ))
    rw [norm_yv] at this
    simpa using this
  have hcpos : 0 < ceCs := ceCs_pos
  have h2 : (ceCs * |v|) ^ (-(1 / 2 : ℝ)) ≤ |v| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.mul_rpow hcpos.le (abs_nonneg v)]
    have : ceCs ^ (-(1 / 2 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ceCs_one_lt.le (by norm_num)
    calc ceCs ^ (-(1 / 2 : ℝ)) * |v| ^ (-(1 / 2 : ℝ)) ≤ 1 * |v| ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (abs_nonneg v) _)
      _ = _ := one_mul _
  have h3 : ‖(3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ))‖ =
      (3 / 4) * ceCs ^ 2 * ‖(yv v) ^ (-(1 / 2 : ℂ))‖ := by
    rw [norm_mul, norm_mul, norm_pow, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcpos]
    norm_num
  rw [h3, h1]
  have : 0 ≤ (3 / 4 : ℝ) * ceCs ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left h2 this

lemma cpow_ofReal_mul_half {c : ℝ} (hc : 0 < c) (z : ℂ) :
    ((c : ℂ) * z) ^ (1 / 2 : ℂ) = (((c ^ (1 / 2 : ℝ) : ℝ)) : ℂ) * z ^ (1 / 2 : ℂ) := by
  by_cases hz : z = 0
  · subst hz; simp
  · have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
    rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hc0 hz), Complex.cpow_def_of_ne_zero hz,
      Complex.log_ofReal_mul hc hz]
    have e : (((c ^ (1 / 2 : ℝ) : ℝ)) : ℂ) = Complex.exp (((Real.log c : ℝ) : ℂ) * (1 / 2)) := by
      rw [Real.rpow_def_of_pos hc, Complex.ofReal_exp]; push_cast; ring_nf
    rw [e, add_mul, Complex.exp_add]

lemma sq_eq (v : ℝ) : sq v = ((ceCs ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) := by
  unfold sq yv
  rw [show (ceCs : ℂ) * ((v : ℂ) * Complex.I) = (ceCs : ℂ) * (Complex.I * (v : ℂ)) by ring]
  exact cpow_ofReal_mul_half ceCs_pos _

lemma exp_yv (v : ℝ) : Complex.exp (-(yv v) ^ 3 / 12) = Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) := by
  have hcube : (yv v) ^ 3 = -(Complex.I * ((ceCs ^ 3 * v ^ 3 : ℝ) : ℂ)) := by
    unfold yv
    push_cast
    have : Complex.I ^ 3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
    calc ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) ^ 3 = (ceCs : ℂ) ^ 3 * (v : ℂ) ^ 3 * Complex.I ^ 3 := by ring
      _ = _ := by rw [this]; ring
  rw [hcube, ceCs_cube']; congr 1; push_cast; ring

/-- The subtracted symbol with `γ₀ = -c_s^{1/2} B(0)`, in terms of the entire data `A, B`. -/
lemma G_formula {T A B : ℂ → ℂ} {b0 : ℝ} (hT : ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y)
    (χ₁ : ℝ → ℝ) (v : ℝ) :
    T ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        ((-(b0 * ceCs ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ) =
      A (yv v) + sq v * (B (yv v) - (b0 : ℂ) * Complex.exp (-(yv v) ^ 3 / 12) * (χ₁ v : ℂ)) := by
  have h1 : T (yv v) = A (yv v) + sq v * B (yv v) := hT _ (by rw [yv_re])
  rw [← exp_yv v]
  have h2 : ((-(b0 * ceCs ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) = -((b0 : ℂ) * sq v) := by
    rw [sq_eq v]; push_cast; ring
  show T (yv v) + _ = _
  rw [h1]
  calc A (yv v) + sq v * B (yv v) + ((-(b0 * ceCs ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
        Complex.exp (-(yv v) ^ 3 / 12) * (χ₁ v : ℂ)
      = A (yv v) + sq v * B (yv v) + (((-(b0 * ceCs ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ)) *
        Complex.exp (-(yv v) ^ 3 / 12) * (χ₁ v : ℂ) := by ring
    _ = _ := by rw [h2]; ring

/-! ### The regular part `p + s_A k` near `v = 0` -/

lemma exists_abs_bound {f : ℝ → ℂ} (hf : Continuous f) : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, |v| ≤ 1 / 2 → ‖f v‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-(1 / 2) : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨|C|, abs_nonneg _, fun v hv => (hC v (abs_le.mp hv |> fun h => ⟨h.1, h.2⟩)).trans (le_abs_self C)⟩

lemma one_le_rpow_neg_half {v : ℝ} (hv : v ≠ 0) (hv1 : |v| ≤ 1 / 2) : 1 ≤ |v| ^ (-(1 / 2 : ℝ)) :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr hv) (hv1.trans (by norm_num)) (by norm_num)

lemma G1_regularity {p k : ℝ → ℂ} (hp : ContDiff ℝ 2 p) (hk : ContDiff ℝ 2 k) :
    (∀ v : ℝ, HasDerivAt (fun v => p v + sA v * k v) (deriv p v + sA' v * k v + sA v * deriv k v) v) ∧
    ∃ M : ℝ, ∀ v : ℝ, v ≠ 0 → |v| ≤ 1 / 2 →
      ‖deriv (deriv (fun v => p v + sA v * k v)) v‖ ≤ M * |v| ^ (-(1 / 2 : ℝ)) := by
  have hpd : Differentiable ℝ p := hp.differentiable (by norm_num)
  have hkd : Differentiable ℝ k := hk.differentiable (by norm_num)
  have hp1 : ContDiff ℝ 1 (deriv p) := hp.deriv'
  have hk1 : ContDiff ℝ 1 (deriv k) := hk.deriv'
  have hDg : ∀ v : ℝ, HasDerivAt (fun v => p v + sA v * k v) (deriv p v + sA' v * k v + sA v * deriv k v) v := fun v =>
    ((hpd v).hasDerivAt.add ((hasDerivAt_sA v).mul (hkd v).hasDerivAt)).congr_deriv (by ring)
  refine ⟨hDg, ?_⟩
  have hderiv : deriv (fun v => p v + sA v * k v) = fun v => deriv p v + sA' v * k v + sA v * deriv k v :=
    funext fun v => (hDg v).deriv
  -- bounds on the compact interval
  obtain ⟨Mp2, hMp2, bp2⟩ := exists_abs_bound hp1.continuous_deriv_one
  obtain ⟨Mk, hMk, bk⟩ := exists_abs_bound hkd.continuous
  obtain ⟨Mk1, hMk1, bk1⟩ := exists_abs_bound hk1.continuous
  obtain ⟨Mk2, hMk2, bk2⟩ := exists_abs_bound hk1.continuous_deriv_one
  obtain ⟨MsA, hMsA, bsA⟩ := exists_abs_bound continuous_sA
  obtain ⟨MsA', hMsA', bsA'⟩ := exists_abs_bound continuous_sA'
  refine ⟨Mp2 + (3 / 4) * ceCs ^ 2 * Mk + 2 * (MsA' * Mk1) + MsA * Mk2, fun v hv hv1 => ?_⟩
  have h1 : HasDerivAt (deriv p) (deriv (deriv p) v) v := (hp1.differentiable (by norm_num) v).hasDerivAt
  have h2 : HasDerivAt (deriv k) (deriv (deriv k) v) v := (hk1.differentiable (by norm_num) v).hasDerivAt
  have hb := (hasDerivAt_sA'_ne hv).mul (hkd v).hasDerivAt
  have hc := (hasDerivAt_sA v).mul h2
  have hDd := (h1.add hb).add hc
  have hval : deriv (deriv (fun v => p v + sA v * k v)) v =
      deriv (deriv p) v + ((3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ)) * k v + sA' v * deriv k v) +
        (sA' v * deriv k v + sA v * deriv (deriv k) v) := by
    rw [hderiv]; exact hDd.deriv
  rw [hval]
  have hv2 : |v| ≤ 1 / 2 := hv1
  have e1 : ‖deriv (deriv p) v‖ ≤ Mp2 := bp2 v hv2
  have e2 : ‖(3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ))‖ ≤ (3 / 4) * ceCs ^ 2 * |v| ^ (-(1 / 2 : ℝ)) :=
    norm_sA'_deriv_le hv
  have e3 : ‖k v‖ ≤ Mk := bk v hv2
  have e4 : ‖deriv k v‖ ≤ Mk1 := bk1 v hv2
  have e5 : ‖deriv (deriv k) v‖ ≤ Mk2 := bk2 v hv2
  have e6 : ‖sA v‖ ≤ MsA := bsA v hv2
  have e7 : ‖sA' v‖ ≤ MsA' := bsA' v hv2
  set r : ℝ := |v| ^ (-(1 / 2 : ℝ)) with hr
  have hr1 : 1 ≤ r := one_le_rpow_neg_half hv hv1
  have hc2 : 0 ≤ (3 / 4 : ℝ) * ceCs ^ 2 := by positivity
  have t1 : ‖(3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ)) * k v‖ ≤ (3 / 4) * ceCs ^ 2 * r * Mk := by
    rw [norm_mul]; exact mul_le_mul e2 e3 (norm_nonneg _) (by positivity)
  have t2 : ‖sA' v * deriv k v‖ ≤ MsA' * Mk1 := by
    rw [norm_mul]; exact mul_le_mul e7 e4 (norm_nonneg _) hMsA'
  have t3 : ‖sA v * deriv (deriv k) v‖ ≤ MsA * Mk2 := by
    rw [norm_mul]; exact mul_le_mul e6 e5 (norm_nonneg _) hMsA
  calc ‖deriv (deriv p) v + ((3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ)) * k v + sA' v * deriv k v) +
        (sA' v * deriv k v + sA v * deriv (deriv k) v)‖
      ≤ ‖deriv (deriv p) v‖ + (‖(3 / 4 : ℂ) * ((ceCs : ℂ) * Complex.I) ^ 2 * (yv v) ^ (-(1 / 2 : ℂ)) * k v‖ + ‖sA' v * deriv k v‖) +
        (‖sA' v * deriv k v‖ + ‖sA v * deriv (deriv k) v‖) := by
        exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _)))
          (norm_add_le _ _))
    _ ≤ Mp2 + ((3 / 4) * ceCs ^ 2 * r * Mk + MsA' * Mk1) + (MsA' * Mk1 + MsA * Mk2) := by gcongr
    _ ≤ (Mp2 + (3 / 4) * ceCs ^ 2 * Mk + 2 * (MsA' * Mk1) + MsA * Mk2) * r := by
        have := mul_nonneg hMp2 (sub_nonneg.2 hr1)
        have := mul_nonneg (mul_nonneg hMsA' hMk1) (sub_nonneg.2 hr1)
        have := mul_nonneg (mul_nonneg hMsA hMk2) (sub_nonneg.2 hr1)
        nlinarith

/-- The subtracted symbol `G_sm` in terms of the entire data `A, B`. -/
noncomputable def Gsm (A B : ℂ → ℂ) (b0 : ℝ) (χ₁ : ℝ → ℝ) (v : ℝ) : ℂ :=
  A (yv v) + sq v * (B (yv v) - (b0 : ℂ) * Complex.exp (-(yv v) ^ 3 / 12) * (χ₁ v : ℂ))

/-- The entire function `N(y) = B(y) - b₀ e^{-y³/12}`, vanishing at `0` when `b₀ = B(0)`. -/
noncomputable def Nfun (B : ℂ → ℂ) (b0 : ℝ) (y : ℂ) : ℂ := B y - (b0 : ℂ) * Complex.exp (-(y ^ 3) / 12)

lemma differentiable_Nfun {B : ℂ → ℂ} (hB : Differentiable ℂ B) (b0 : ℝ) : Differentiable ℂ (Nfun B b0) := by
  unfold Nfun; exact hB.sub (by fun_prop)

lemma Nfun_zero {B : ℂ → ℂ} {b0 : ℝ} (hb : B 0 = b0) : Nfun B b0 0 = 0 := by
  simp [Nfun, hb]

lemma Kfun_spec {B : ℂ → ℂ} {b0 : ℝ} (hb : B 0 = b0) (y : ℂ) : y * dslope (Nfun B b0) 0 y = Nfun B b0 y := by
  have := sub_smul_dslope (Nfun B b0) 0 y
  simp only [smul_eq_mul, sub_zero, Nfun_zero hb] at this
  linear_combination this

lemma Gsm_near {A B : ℂ → ℂ} {b0 : ℝ} (hb : B 0 = b0) {χ₁ : ℝ → ℝ} (hχ1 : ∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1)
    {v : ℝ} (hv : |v| ≤ 1 / 2) :
    Gsm A B b0 χ₁ v = A (yv v) + sA v * dslope (Nfun B b0) 0 (yv v) := by
  unfold Gsm sA
  rw [hχ1 v hv, mul_assoc (sq v) (yv v), Kfun_spec hb (yv v)]
  simp only [Nfun, Complex.ofReal_one, mul_one]

lemma contDiff_comp_yv {F : ℂ → ℂ} (hF : Differentiable ℂ F) {n : ℕ} : ContDiff ℝ n (fun v => F (yv v)) :=
  (hF.contDiff.restrict_scalars ℝ).comp contDiff_yv

lemma contDiffAt_sq {v : ℝ} (hv : v ≠ 0) {n : ℕ} : ContDiffAt ℝ n sq v := by
  have h1 : ContDiffAt ℂ n (fun y : ℂ => y ^ (1 / 2 : ℂ)) (yv v) :=
    (AnalyticAt.cpow (f := fun z : ℂ => z) (g := fun _ => (1 / 2 : ℂ)) analyticAt_id analyticAt_const
      (yv_mem_slit hv)).contDiffAt
  exact (h1.restrict_scalars ℝ).comp v contDiff_yv.contDiffAt

lemma Gsm_contDiffAt {A B : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (b0 : ℝ) {χ₁ : ℝ → ℝ}
    (hχ : ContDiff ℝ 2 χ₁) {v : ℝ} (hv : v ≠ 0) : ContDiffAt ℝ 2 (Gsm A B b0 χ₁) v := by
  have hE : ContDiff ℝ 2 (fun v => Complex.exp (-(yv v) ^ 3 / 12)) :=
    (((contDiff_yv (n := 2)).pow 3).neg.div_const (12 : ℂ)).cexp
  have hχc : ContDiff ℝ 2 (fun v => (χ₁ v : ℂ)) := Complex.ofRealCLM.contDiff.comp hχ
  unfold Gsm
  exact (contDiff_comp_yv hA).contDiffAt.add ((contDiffAt_sq hv).mul
    ((contDiff_comp_yv hB).contDiffAt.sub ((contDiff_const.mul hE).mul hχc).contDiffAt))

lemma Gsm_regular {A B : ℂ → ℂ} {b0 : ℝ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B) (hb : B 0 = b0)
    {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁) (hχ1 : ∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1) :
    ContDiff ℝ 1 (Gsm A B b0 χ₁) ∧
    ∃ M : ℝ, ∀ v : ℝ, v ≠ 0 → |v| < 1 / 2 → ‖deriv (deriv (Gsm A B b0 χ₁)) v‖ ≤ M * |v| ^ (-(1 / 2 : ℝ)) := by
  have hK : Differentiable ℂ (dslope (Nfun B b0) 0) := differentiable_dslope_zero (differentiable_Nfun hB b0)
  have hp : ContDiff ℝ 2 (fun v => A (yv v)) := contDiff_comp_yv hA
  have hk : ContDiff ℝ 2 (fun v => dslope (Nfun B b0) 0 (yv v)) := contDiff_comp_yv hK
  obtain ⟨hD, M, hM⟩ := G1_regularity hp hk
  have hnear : ∀ v : ℝ, |v| < 1 / 2 → Gsm A B b0 χ₁ =ᶠ[𝓝 v] fun v => A (yv v) + sA v * dslope (Nfun B b0) 0 (yv v) := by
    intro v hv
    have hopen : IsOpen {w : ℝ | |w| < 1 / 2} := isOpen_lt continuous_abs continuous_const
    filter_upwards [hopen.mem_nhds hv] with w hw using Gsm_near hb hχ1 (le_of_lt hw)
  refine ⟨?_, M, fun v hv hv1 => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun v => ?_
    by_cases hv : |v| < 1 / 2
    · have h1 : ContDiff ℝ 1 (fun v => A (yv v) + sA v * dslope (Nfun B b0) 0 (yv v)) :=
        (hp.of_le (by norm_num)).add (contDiff_sA.mul (hk.of_le (by norm_num)))
      exact h1.contDiffAt.congr_of_eventuallyEq (hnear v hv)
    · have hv0 : v ≠ 0 := fun h => hv (by simp [h])
      exact (Gsm_contDiffAt hA hB b0 hχ hv0).of_le (by norm_num)
  · rw [(hnear v hv1).deriv.deriv_eq]
    exact hM v hv (le_of_lt hv1)

/-! ### The large-`|v|` bounds of `G_sm` from `ImagAxisBounds` -/

lemma rpow_tail {x s : ℝ} (hx : 1 ≤ x) (hs : 0 ≤ s) : x ^ (-s) ≤ 2 ^ s * (1 + x) ^ (-s) := by
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ s := Real.rpow_pos_of_pos hx0 _
  have hq : 0 < (1 + x) ^ s := Real.rpow_pos_of_pos (by linarith) _
  have h1 : (1 + x) ^ s ≤ 2 ^ s * x ^ s := by
    calc (1 + x) ^ s ≤ (2 * x) ^ s := Real.rpow_le_rpow (by linarith) (by linarith) hs
      _ = 2 ^ s * x ^ s := Real.mul_rpow (by norm_num) hx0.le
  rw [Real.rpow_neg hx0.le, Real.rpow_neg (by linarith)]
  have h2 : (x ^ s)⁻¹ * (1 + x) ^ s ≤ 2 ^ s := by
    rw [inv_mul_le_iff₀ hp, mul_comm]; exact h1
  calc (x ^ s)⁻¹ = ((x ^ s)⁻¹ * (1 + x) ^ s) * ((1 + x) ^ s)⁻¹ := by field_simp
    _ ≤ 2 ^ s * ((1 + x) ^ s)⁻¹ := by gcongr

lemma rpow_cmul_le {x s : ℝ} (hx : 0 ≤ x) (hs : 0 ≤ s) : (ceCs * x) ^ (-s) ≤ x ^ (-s) := by
  rw [Real.mul_rpow ceCs_pos.le hx]
  have : ceCs ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ceCs_one_lt.le (by linarith)
  calc ceCs ^ (-s) * x ^ (-s) ≤ 1 * x ^ (-s) := mul_le_mul_of_nonneg_right this (Real.rpow_nonneg hx _)
    _ = _ := one_mul _

lemma Gsm_tail {T A B : ℂ → ℂ} {b0 : ℝ} (hT : ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y)
    (himag : ImagAxisBounds T) {χ₁ : ℝ → ℝ} (hχs : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : ℝ, 1 < |v| →
      ‖Gsm A B b0 χ₁ v‖ ≤ C * (1 + |v|) ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (Gsm A B b0 χ₁) v‖ ≤ C * (1 + |v|) ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (deriv (Gsm A B b0 χ₁)) v‖ ≤ C * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by
  obtain ⟨g1, g2, h1, h2, C, hC, hb⟩ := himag
  let c : ℝ := ceCs
  have hc1 : 1 < c := ceCs_one_lt
  have hc0 : 0 < c := by linarith
  have hω : ∀ v : ℝ, 1 < |v| → 1 < |c * v| := fun v hv => by
    rw [abs_mul, abs_of_pos hc0]; nlinarith [abs_nonneg v]
  -- identification with the transform on the imaginary axis
  have hGT : ∀ w : ℝ, 1 < |w| → Gsm A B b0 χ₁ w = T (((c * w : ℝ) : ℂ) * Complex.I) := fun w hw => by
    have h : T (yv w) = A (yv w) + sq w * B (yv w) := hT _ (by rw [yv_re])
    have hy : yv w = ((c * w : ℝ) : ℂ) * Complex.I := by unfold yv; push_cast; ring
    rw [← hy, h]
    unfold Gsm
    rw [hχs w hw]; simp
  have hopen : IsOpen {w : ℝ | 1 < |w|} := isOpen_lt continuous_const continuous_abs
  have hev : ∀ v : ℝ, 1 < |v| → Gsm A B b0 χ₁ =ᶠ[𝓝 v] fun w => T (((c * w : ℝ) : ℂ) * Complex.I) := fun v hv => by
    filter_upwards [hopen.mem_nhds hv] with w hw using hGT w hw
  have hlin : ∀ v : ℝ, HasDerivAt (fun w : ℝ => c * w) c v := fun v => by simpa using (hasDerivAt_id v).const_mul c
  have hd1 : ∀ v : ℝ, 1 < |v| → HasDerivAt (Gsm A B b0 χ₁) ((c : ℂ) * g1 (c * v)) v := fun v hv => by
    have h := (h1 (c * v) (hω v hv)).scomp v (hlin v)
    have h' : HasDerivAt (fun w : ℝ => T (((c * w : ℝ) : ℂ) * Complex.I)) ((c : ℂ) * g1 (c * v)) v :=
      h.congr_deriv (by simp [Complex.real_smul])
    exact h'.congr_of_eventuallyEq (hev v hv)
  have hderiv1 : ∀ v : ℝ, 1 < |v| → deriv (Gsm A B b0 χ₁) v = (c : ℂ) * g1 (c * v) := fun v hv => (hd1 v hv).deriv
  have hd2 : ∀ v : ℝ, 1 < |v| → deriv (deriv (Gsm A B b0 χ₁)) v = (c : ℂ) * ((c : ℂ) * g2 (c * v)) := fun v hv => by
    have hev2 : deriv (Gsm A B b0 χ₁) =ᶠ[𝓝 v] fun w => (c : ℂ) * g1 (c * w) := by
      filter_upwards [hopen.mem_nhds hv] with w hw using hderiv1 w hw
    rw [hev2.deriv_eq]
    have h := (h2 (c * v) (hω v hv)).scomp v (hlin v)
    have h' : HasDerivAt (fun w : ℝ => g1 (c * w)) ((c : ℂ) * g2 (c * v)) v :=
      h.congr_deriv (by simp [Complex.real_smul])
    exact (h'.const_mul (c : ℂ)).deriv
  refine ⟨C * (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4), by positivity, fun v hv => ?_⟩
  obtain ⟨b0', b1', b2'⟩ := hb (c * v) (hω v hv)
  have habs : |c * v| = c * |v| := by rw [abs_mul, abs_of_pos hc0]
  have hv0 : 0 ≤ |v| := abs_nonneg v
  have hv1 : 1 ≤ |v| := hv.le
  have K1 : (c * |v|) ^ (-(5 / 2 : ℝ)) ≤ |v| ^ (-(5 / 2 : ℝ)) := rpow_cmul_le hv0 (by norm_num)
  have K2 : (c * |v|) ^ (-(7 / 2 : ℝ)) ≤ |v| ^ (-(5 / 2 : ℝ)) :=
    (rpow_cmul_le hv0 (by norm_num)).trans (Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num))
  have K3 : (c * |v|) ^ (-(9 / 2 : ℝ)) ≤ |v| ^ (-(1 / 2 : ℝ)) * |v| ^ (-(2 : ℝ)) := by
    refine (rpow_cmul_le hv0 (by norm_num)).trans ?_
    rw [← Real.rpow_add (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hv1 (by norm_num)
  have T5 : |v| ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := rpow_tail hv1 (by norm_num)
  have T2 : |v| ^ (-(2 : ℝ)) ≤ 2 ^ (2 : ℝ) * (1 + |v|) ^ (-(2 : ℝ)) := rpow_tail hv1 (by norm_num)
  have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num
  rw [h22] at T2
  have P5 : 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have P2 : 0 ≤ (1 + |v|) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have Q : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hv0 _
  have hK : (0 : ℝ) < 2 ^ (5 / 2 : ℝ) := by positivity
  have hcc : 0 ≤ (c + 1) ^ 2 := by positivity
  have e0 : (1 : ℝ) ≤ (c + 1) ^ 2 := by nlinarith
  have F1 : C * 2 ^ (5 / 2 : ℝ) ≤ C * (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4) := by
    have : (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4) := by nlinarith
    calc C * 2 ^ (5 / 2 : ℝ) ≤ C * ((c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4)) := mul_le_mul_of_nonneg_left this hC.le
      _ = _ := by ring
  have F2 : c * C * 2 ^ (5 / 2 : ℝ) ≤ C * (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4) := by
    have hc' : c ≤ (c + 1) ^ 2 := by nlinarith
    have : c * (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4) :=
      calc c * (2 : ℝ) ^ (5 / 2 : ℝ) ≤ (c + 1) ^ 2 * 2 ^ (5 / 2 : ℝ) := mul_le_mul_of_nonneg_right hc' hK.le
        _ ≤ _ := by nlinarith
    calc c * C * 2 ^ (5 / 2 : ℝ) = C * (c * 2 ^ (5 / 2 : ℝ)) := by ring
      _ ≤ C * ((c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4)) := mul_le_mul_of_nonneg_left this hC.le
      _ = _ := by ring
  have F3 : c ^ 2 * C * 4 ≤ C * (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4) := by
    have : c ^ 2 * 4 ≤ (c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4) := by nlinarith
    calc c ^ 2 * C * 4 = C * (c ^ 2 * 4) := by ring
      _ ≤ C * ((c + 1) ^ 2 * (2 ^ (5 / 2 : ℝ) + 4)) := mul_le_mul_of_nonneg_left this hC.le
      _ = _ := by ring
  rw [hGT v hv, hderiv1 v hv, hd2 v hv]
  rw [habs] at b0' b1' b2'
  have nC : ‖(c : ℂ)‖ = c := by simp [abs_of_pos hc0]
  refine ⟨?_, ?_, ?_⟩
  · calc ‖T (((c * v : ℝ) : ℂ) * Complex.I)‖ ≤ C * (c * |v|) ^ (-(5 / 2 : ℝ)) := by simpa using b0'
      _ ≤ C * (2 ^ (5 / 2 : ℝ) * (1 + |v|) ^ (-(5 / 2 : ℝ))) := by gcongr; exact K1.trans T5
      _ = (C * 2 ^ (5 / 2 : ℝ)) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right F1 P5
  · calc ‖(c : ℂ) * g1 (c * v)‖ = c * ‖g1 (c * v)‖ := by rw [norm_mul, nC]
      _ ≤ c * (C * (c * |v|) ^ (-(7 / 2 : ℝ))) := by gcongr
      _ ≤ c * (C * (2 ^ (5 / 2 : ℝ) * (1 + |v|) ^ (-(5 / 2 : ℝ)))) := by gcongr; exact K2.trans T5
      _ = (c * C * 2 ^ (5 / 2 : ℝ)) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right F2 P5
  · calc ‖(c : ℂ) * ((c : ℂ) * g2 (c * v))‖ = c * (c * ‖g2 (c * v)‖) := by rw [norm_mul, norm_mul, nC]
      _ ≤ c * (c * (C * (c * |v|) ^ (-(9 / 2 : ℝ)))) := by gcongr
      _ ≤ c * (c * (C * (|v| ^ (-(1 / 2 : ℝ)) * (4 * (1 + |v|) ^ (-(2 : ℝ)))))) := by
          gcongr
          exact K3.trans (mul_le_mul_of_nonneg_left T2 Q)
      _ = (c ^ 2 * C * 4) * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right F3 (mul_nonneg Q P2)

lemma one_add_rpow_ge {v s : ℝ} (hv : |v| ≤ 1) (hs : 0 ≤ s) (hs3 : s ≤ 3) : 1 / 8 ≤ (1 + |v|) ^ (-s) := by
  have h1 : (2 : ℝ) ^ (-s) ≤ (1 + |v|) ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos (by linarith [abs_nonneg v]) (by linarith) (by linarith)
  have h2 : (1 / 8 : ℝ) ≤ (2 : ℝ) ^ (-s) := by
    have : (2 : ℝ) ^ (-(3 : ℝ)) ≤ (2 : ℝ) ^ (-s) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h8 : (2 : ℝ) ^ (-(3 : ℝ)) = 1 / 8 := by
      rw [Real.rpow_neg (by norm_num), show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    rw [h8] at this; exact this
  linarith

/-- **Square-root structure gives `SmoothSymbol`.**  If `T = A + y^{1/2} B` on the closed right half-plane with `A, B`
entire and `B(0) = b₀ ∈ ℝ`, and `T` has the `(e27)` bounds on the imaginary axis, then with `γ₀ = -c_s^{1/2} b₀` and a
cut-off `χ₁` (`C²`, `= 1` on `[-1/2, 1/2]`, supported in `[-1, 1]`) the subtracted symbol is a `SmoothSymbol`. -/
theorem smoothSymbol_of_sqData {T A B : ℂ → ℂ} {b0 : ℝ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hb : B 0 = b0) (hT : ∀ y : ℂ, 0 ≤ y.re → T y = A y + y ^ (1 / 2 : ℂ) * B y) (himag : ImagAxisBounds T)
    {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁) (hχ1 : ∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1)
    (hχs : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ∃ CG : ℝ, SmoothSymbol (fun v : ℝ => T ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        ((-(b0 * ceCs ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) CG := by
  have hfun : (fun v : ℝ => T ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        ((-(b0 * ceCs ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) = Gsm A B b0 χ₁ :=
    funext fun v => G_formula hT χ₁ v
  rw [hfun]
  obtain ⟨hC1, M, hM⟩ := Gsm_regular hA hB hb hχ hχ1
  obtain ⟨Ct, hCt, htail⟩ := Gsm_tail (b0 := b0) hT himag hχs
  set G := Gsm A B b0 χ₁ with hG
  have hU : IsOpen {v : ℝ | v ≠ 0} := isOpen_ne
  have hCD : ContDiffOn ℝ 2 G {v : ℝ | v ≠ 0} := fun v hv => (Gsm_contDiffAt hA hB b0 hχ hv).contDiffWithinAt
  have hCD1 : ContDiffOn ℝ 1 (deriv G) {v : ℝ | v ≠ 0} := hCD.deriv_of_isOpen hU (by norm_num)
  have hCD0 : ContDiffOn ℝ 0 (deriv (deriv G)) {v : ℝ | v ≠ 0} := hCD1.deriv_of_isOpen hU (by norm_num)
  obtain ⟨M0, hM0⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn hC1.continuous.continuousOn
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hC1.continuous_deriv_one.continuousOn
  have hKc : IsCompact ({v : ℝ | 1 / 2 ≤ |v|} ∩ Set.Icc (-1 : ℝ) 1) :=
    (isCompact_Icc).inter_left (isClosed_le continuous_const continuous_abs)
  have hKU : {v : ℝ | 1 / 2 ≤ |v|} ∩ Set.Icc (-1 : ℝ) 1 ⊆ {v : ℝ | v ≠ 0} := fun v hv h0 => by
    have := hv.1; simp [h0] at this; linarith
  obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn (hCD0.continuousOn.mono hKU)
  refine ⟨8 * (|M0| + |M1| + |M| + |M2|) + Ct, ?_⟩
  have hCG : ∀ X : ℝ, 0 ≤ X → X ≤ 8 * (|M0| + |M1| + |M| + |M2|) + Ct → True := fun _ _ _ => trivial
  have hMn : 0 ≤ 8 * (|M0| + |M1| + |M| + |M2|) + Ct := by positivity
  have hbd : ∀ v : ℝ, |v| ≤ 1 → ∀ {s : ℝ}, 0 ≤ s → s ≤ 3 → ∀ X : ℝ, X ≤ |X| →
      8 * |X| * (1 + |v|) ^ (-s) ≥ |X| := fun v hv s hs hs3 X _ => by
    have := one_add_rpow_ge hv hs hs3
    nlinarith [abs_nonneg X]
  have h5 : ∀ v : ℝ, |v| ≤ 1 → 1 / 8 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := fun v hv => one_add_rpow_ge hv (by norm_num) (by norm_num)
  have h2 : ∀ v : ℝ, |v| ≤ 1 → 1 / 8 ≤ (1 + |v|) ^ (-(2 : ℝ)) := fun v hv => one_add_rpow_ge hv (by norm_num) (by norm_num)
  have P5 : ∀ v : ℝ, 0 ≤ (1 + |v|) ^ (-(5 / 2 : ℝ)) := fun v => Real.rpow_nonneg (by linarith [abs_nonneg v]) _
  have P2 : ∀ v : ℝ, 0 ≤ (1 + |v|) ^ (-(2 : ℝ)) := fun v => Real.rpow_nonneg (by linarith [abs_nonneg v]) _
  refine ⟨hC1, fun x hx => ?_, fun v => ?_, fun v => ?_, fun v hv => ?_⟩
  · exact (hCD1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hx)
  · by_cases hv : 1 < |v|
    · exact (htail v hv).1.trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) (P5 v))
    · have hv1 : |v| ≤ 1 := not_lt.mp hv
      have := hM0 v (abs_le.mp hv1 |> fun h => ⟨h.1, h.2⟩)
      have h8 := h5 v hv1
      calc ‖G v‖ ≤ |M0| := this.trans (le_abs_self _)
        _ ≤ (8 * |M0|) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by nlinarith [abs_nonneg M0]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) (P5 v)
  · by_cases hv : 1 < |v|
    · exact (htail v hv).2.1.trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) (P5 v))
    · have hv1 : |v| ≤ 1 := not_lt.mp hv
      have := hM1 v (abs_le.mp hv1 |> fun h => ⟨h.1, h.2⟩)
      have h8 := h5 v hv1
      calc ‖deriv G v‖ ≤ |M1| := this.trans (le_abs_self _)
        _ ≤ (8 * |M1|) * (1 + |v|) ^ (-(5 / 2 : ℝ)) := by nlinarith [abs_nonneg M1]
        _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) (P5 v)
  · have hv0 : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg v) _
    have hQ : 0 ≤ |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := mul_nonneg hv0 (P2 v)
    by_cases h1 : 1 < |v|
    · exact (htail v h1).2.2.trans (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) hQ)
    · have hv1 : |v| ≤ 1 := not_lt.mp h1
      have hr : 1 ≤ |v| ^ (-(1 / 2 : ℝ)) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr hv) hv1 (by norm_num)
      have hP := h2 v hv1
      by_cases h3 : |v| < 1 / 2
      · have hm := hM v hv h3
        calc ‖deriv (deriv G) v‖ ≤ M * |v| ^ (-(1 / 2 : ℝ)) := hm
          _ ≤ |M| * |v| ^ (-(1 / 2 : ℝ)) := mul_le_mul_of_nonneg_right (le_abs_self _) hv0
          _ ≤ (8 * |M|) * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by
              nlinarith [abs_nonneg M, mul_nonneg (abs_nonneg M) hv0, mul_nonneg (abs_nonneg M) (sub_nonneg.2 hP)]
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) hQ
      · have h3' : 1 / 2 ≤ |v| := not_lt.mp h3
        have hmem : v ∈ {v : ℝ | 1 / 2 ≤ |v|} ∩ Set.Icc (-1 : ℝ) 1 := ⟨h3', (abs_le.mp hv1).1, (abs_le.mp hv1).2⟩
        have hm := hM2 v hmem
        have hrP : 1 / 8 ≤ |v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ)) := by nlinarith
        calc ‖deriv (deriv G) v‖ ≤ |M2| := hm.trans (le_abs_self _)
          _ ≤ (8 * |M2|) * (|v| ^ (-(1 / 2 : ℝ)) * (1 + |v|) ^ (-(2 : ℝ))) := by nlinarith [abs_nonneg M2]
          _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [abs_nonneg M0, abs_nonneg M1, abs_nonneg M, abs_nonneg M2]) hQ

/-- A smooth cut-off `χ₁` with `χ₁ = 1` on `[-1/2, 1/2]` and `χ₁ = 0` off `[-1, 1]`. -/
lemma exists_cutoff_chi1 : ∃ χ₁ : ℝ → ℝ, (∀ n : ℕ, ContDiff ℝ n χ₁) ∧ (∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1) ∧
    (∀ v : ℝ, 1 < |v| → χ₁ v = 0) := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  refine ⟨f, fun n => f.contDiff, fun v hv => f.one_of_mem_closedBall ?_, fun v hv => f.zero_of_le_dist ?_⟩
  · simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]; exact hv
  · simp only [Real.dist_eq, sub_zero]; exact hv.le

/-- **`SmoothSymbol` for every one-level seed `a f₁ + b g₁ + c g₁'`** (Piece C, step 1 of `u1c:U3(3)`). -/
theorem airySeedU2_smoothSymbol (a b c : ℝ) {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁)
    (hχ1 : ∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1) (hχs : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ∃ γ₀ CG : ℝ, SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC (airySeedU2 a b c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) CG := by
  obtain ⟨A, B, hA, hB, ⟨b0, hb⟩, hT⟩ := (airySeedU2_sqForm a b c).closed (hasU2_airySeedU2 a b c).continuousOn
  obtain ⟨CG, hCG⟩ := smoothSymbol_of_sqData hA hB hb hT (airySeedU2_imagAxisBounds a b c) hχ hχ1 hχs
  exact ⟨-(b0 * ceCs ^ (1 / 2 : ℝ)), CG, hCG⟩

/-- **`SmoothSymbol` for the `m₀ = 1` Hermite–Biehler seed.** -/
theorem hbSeed_m1_smoothSymbol (γ₁ γ₂ δ r : ℝ) {χ₁ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ₁)
    (hχ1 : ∀ v : ℝ, |v| ≤ 1 / 2 → χ₁ v = 1) (hχs : ∀ v : ℝ, 1 < |v| → χ₁ v = 0) :
    ∃ γ₀ CG : ℝ, SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC
        (fun u : ℝ => -ceF1 u - γ₁ * δ * ceG1 (airyZero 1) u + γ₂ * δ * ceSb 1 u + r * ceG1 (airyZero 1) u)
        ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) CG := by
  rw [hbSeed_m1_eq_airySeedU2]; exact airySeedU2_smoothSymbol _ _ _ hχ hχ1 hχs

/-- **Non-vacuity**: a cut-off exists and the `SmoothSymbol` instance holds for the seed `-f₁` (`β_∞ = 1`). -/
theorem airySeedU2_smoothSymbol_nonvacuous (a b c : ℝ) :
    ∃ (χ₁ : ℝ → ℝ) (γ₀ CG : ℝ), ContDiff ℝ 2 χ₁ ∧ χ₁ 0 = 1 ∧
      SmoothSymbol (fun v : ℝ => airyTwistedLaplaceC (airySeedU2 a b c) ((ceCs : ℂ) * ((v : ℂ) * Complex.I)) +
        (γ₀ : ℂ) * (Complex.I * (v : ℂ)) ^ (1 / 2 : ℂ) *
          Complex.exp (Complex.I * ((Real.pi ^ 2 / 36 * v ^ 3 : ℝ) : ℂ)) * (χ₁ v : ℂ)) CG := by
  obtain ⟨χ₁, hχ, hχ1, hχs⟩ := exists_cutoff_chi1
  obtain ⟨γ₀, CG, h⟩ := airySeedU2_smoothSymbol a b c (hχ 2) hχ1 hχs
  exact ⟨χ₁, γ₀, CG, hχ 2, hχ1 0 (by simp), h⟩

/-- info: 'FormalResearch.CohnElkies.airySeedU2_smoothSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airySeedU2_smoothSymbol
/-- info: 'FormalResearch.CohnElkies.hbSeed_m1_smoothSymbol' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hbSeed_m1_smoothSymbol
/-- info: 'FormalResearch.CohnElkies.airySeedU2_smoothSymbol_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airySeedU2_smoothSymbol_nonvacuous
/-- info: 'FormalResearch.CohnElkies.airySeedU2_sqForm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airySeedU2_sqForm
/-- info: 'FormalResearch.CohnElkies.airySeedU2_sqFormAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms airySeedU2_sqFormAt
/-- info: 'FormalResearch.CohnElkies.smoothSymbol_of_sqData' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms smoothSymbol_of_sqData

end FormalResearch.CohnElkies

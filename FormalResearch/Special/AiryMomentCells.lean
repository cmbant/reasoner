module

public import Mathlib
public import FormalResearch.Asymptotics.MidpointRule

/-!
# Cell estimates for the Airy linear moment (phase-free)

Real-variable inputs for `cts:airy-sum-zero` (the Airy linear moment of `cts:tip-shared` (a)).  With the sites
`c_n = n + 3/4` (`= k - 1/4`, `k = n + 1`) and the cells `[c_n - 1/2, c_n + 1/2]`:

* `sp_midpoint`: the midpoint defect `d₀(c) = c^{2/3} - ∫_{cell} u^{2/3}` is `O(c^{-4/3})` (`d0c_bound`);
* `cphi`: the kernel `φ_x(u) = (x + κ u^{2/3})^{-2}`; `inv_sq_taylor` is the exact second-order remainder of `y ↦ y^{-2}`
  (`y^{-2} - y₀^{-2} + 2 y₀^{-3}(y - y₀) = (y - y₀)²(2y + y₀)/(y² y₀³)`), and `cphi_cell` the cell defect
  `φ_x(c) - ∫_{cell} φ_x = -2κ y₀^{-3} d₀ + O(κ² (c - 1/2)^{-2/3} / y₀⁴)` (`y₀ = x + κ c^{2/3}`), so that
  `dcell_bound`: `x³ |φ_x(c_n) - ∫_{cell_n} φ_x| ≤ K (n+1)^{-4/3}` uniformly in `x > 0` and `dcell_tendsto`:
  `x³ (φ_x(c_n) - ∫_{cell_n} φ_x) → -2κ d₀(c_n)` as `x → ∞`;
* `cphi_integral`: `∫_0^∞ (x + κ u^{2/3})^{-2} du = 1/(2√x)` when `κ³ = (3π/2)²` (substitution `u = t³` and the
  primitive `qPrim`).

All proved; constants explicit and not optimised.
-/

@[expose] public section

open Set MeasureTheory intervalIntegral Filter Topology
open scoped Real

namespace FormalResearch.Special.AiryMoment

lemma sp_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => u ^ (2 / 3 : ℝ)) (2 / 3 * t ^ (-(1 / 3) : ℝ)) t := by
  have := Real.hasDerivAt_rpow_const (p := (2 / 3 : ℝ)) (Or.inl ht.ne')
  refine this.congr_deriv ?_
  norm_num

lemma sp1_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u : ℝ => 2 / 3 * u ^ (-(1 / 3) : ℝ)) (-(2 / 9) * t ^ (-(4 / 3) : ℝ)) t := by
  have := (Real.hasDerivAt_rpow_const (p := (-(1 / 3) : ℝ)) (Or.inl ht.ne')).const_mul (2 / 3 : ℝ)
  refine this.congr_deriv ?_
  norm_num
  ring

/-- The midpoint defect of `u ↦ u^{2/3}` at `c ≥ 3/4`. -/
lemma sp_midpoint {c : ℝ} (hc : 3 / 4 ≤ c) :
    |c ^ (2 / 3 : ℝ) - ∫ u in (c - 1 / 2)..(c + 1 / 2), u ^ (2 / 3 : ℝ)| ≤
      (2 / 9) * (c - 1 / 2) ^ (-(4 / 3) : ℝ) / 12 := by
  have h := FormalResearch.Asymptotics.midpoint_remainder (f := fun u : ℝ => u ^ (2 / 3 : ℝ))
    (f1 := fun u => 2 / 3 * u ^ (-(1 / 3) : ℝ)) (f2 := fun u => -(2 / 9) * u ^ (-(4 / 3) : ℝ)) (c := c)
    (B := (2 / 9) * (c - 1 / 2) ^ (-(4 / 3) : ℝ))
    (fun t ht => sp_hasDerivAt (by linarith [ht.1]))
    (fun t ht => sp1_hasDerivAt (by linarith [ht.1]))
    (fun t ht => by
      have ht0 : 0 < c - 1 / 2 := by linarith
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 2 / 9), abs_of_pos (Real.rpow_pos_of_pos
        (by linarith [ht.1]) _)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.rpow_le_rpow_of_nonpos ht0 ht.1 (by norm_num))
  exact h

/-- The resolvent-type kernel `φ_x(u) = (x + κ u^{2/3})^{-2}`. -/
noncomputable def cphi (κ x u : ℝ) : ℝ := ((x + κ * u ^ (2 / 3 : ℝ)) ^ 2)⁻¹

/-- Exact second-order remainder of `y ↦ y^{-2}` (positive, with an explicit bound). -/
lemma inv_sq_taylor {y y0 : ℝ} (hy : 0 < y) (hy0 : 0 < y0) (hyy : y0 / 3 ≤ y) :
    0 ≤ (y ^ 2)⁻¹ - (y0 ^ 2)⁻¹ + 2 * (y0 ^ 3)⁻¹ * (y - y0) ∧
    (y ^ 2)⁻¹ - (y0 ^ 2)⁻¹ + 2 * (y0 ^ 3)⁻¹ * (y - y0) ≤ 15 * (y - y0) ^ 2 / y0 ^ 4 := by
  have e : (y ^ 2)⁻¹ - (y0 ^ 2)⁻¹ + 2 * (y0 ^ 3)⁻¹ * (y - y0) =
      (y - y0) ^ 2 * (2 * y + y0) / (y ^ 2 * y0 ^ 3) := by
    field_simp
    ring
  rw [e]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : (2 * y + y0) * y0 ≤ 15 * y ^ 2 := by nlinarith only [hyy, hy, hy0]
    have h2 : 0 ≤ (y - y0) ^ 2 := sq_nonneg _
    calc (y - y0) ^ 2 * (2 * y + y0) * y0 ^ 4 = (y - y0) ^ 2 * y0 ^ 3 * ((2 * y + y0) * y0) := by ring
      _ ≤ (y - y0) ^ 2 * y0 ^ 3 * (15 * y ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 15 * (y - y0) ^ 2 * (y ^ 2 * y0 ^ 3) := by ring

lemma sp_intervalIntegrable {a b : ℝ} (_ha : 0 < a) (_hb : 0 < b) :
    IntervalIntegrable (fun u : ℝ => u ^ (2 / 3 : ℝ)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have : 0 < t := by
    rcases Set.mem_uIcc.mp ht with h | h
    · linarith [h.1]
    · linarith [h.1]
  exact (sp_hasDerivAt this).continuousAt.continuousWithinAt

/-- The cell defect of `φ_x` against the linearised one: for `c ≥ 3/4`, `y₀ = x + κ c^{2/3}`,
`|φ_x(c) - ∫_{c-1/2}^{c+1/2} φ_x + 2κ y₀^{-3} d₀| ≤ (5/3) κ² (c - 1/2)^{-2/3} / y₀⁴` where
`d₀ = c^{2/3} - ∫ u^{2/3}`. -/
lemma cphi_cell {κ x c : ℝ} (hκ : 0 < κ) (hx : 0 < x) (hc : 3 / 4 ≤ c) :
    |cphi κ x c - (∫ u in (c - 1 / 2)..(c + 1 / 2), cphi κ x u) +
        2 * κ * ((x + κ * c ^ (2 / 3 : ℝ)) ^ 3)⁻¹ *
          (c ^ (2 / 3 : ℝ) - ∫ u in (c - 1 / 2)..(c + 1 / 2), u ^ (2 / 3 : ℝ))| ≤
      5 / 3 * κ ^ 2 * (c - 1 / 2) ^ (-(2 / 3) : ℝ) / (x + κ * c ^ (2 / 3 : ℝ)) ^ 4 := by
  have hc0 : 0 < c := by linarith
  have hcm : 0 < c - 1 / 2 := by linarith
  set I : Set ℝ := Icc (c - 1 / 2) (c + 1 / 2) with hI
  have hcI : c ∈ I := ⟨by linarith, by linarith⟩
  set s0 : ℝ := c ^ (2 / 3 : ℝ) with hs0
  have hs00 : 0 < s0 := Real.rpow_pos_of_pos hc0 _
  set y0 : ℝ := x + κ * s0 with hy0def
  have hy0 : 0 < y0 := by positivity
  have hup : ∀ u ∈ I, 0 < u := fun u hu => by linarith [hu.1]
  -- the sandwich of s(u) = u^{2/3} on I
  have hlow : ∀ u ∈ I, s0 / 3 ≤ u ^ (2 / 3 : ℝ) := by
    intro u hu
    have h1 : c / 3 ≤ u := by linarith [hu.1]
    have h2 : (c / 3) ^ (2 / 3 : ℝ) ≤ u ^ (2 / 3 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : (c / 3) ^ (2 / 3 : ℝ) = c ^ (2 / 3 : ℝ) / 3 ^ (2 / 3 : ℝ) := Real.div_rpow hc0.le (by norm_num) _
    have h4 : (3 : ℝ) ^ (2 / 3 : ℝ) ≤ 3 := by
      calc (3 : ℝ) ^ (2 / 3 : ℝ) ≤ 3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 3 := Real.rpow_one 3
    have h5 : 0 < (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
    calc s0 / 3 ≤ s0 / 3 ^ (2 / 3 : ℝ) := by
          apply div_le_div_of_nonneg_left hs00.le h5 h4
      _ = (c / 3) ^ (2 / 3 : ℝ) := by rw [h3]
      _ ≤ _ := h2
  have hlip : ∀ u ∈ I, |u ^ (2 / 3 : ℝ) - s0| ≤ 1 / 3 * (c - 1 / 2) ^ (-(1 / 3) : ℝ) := by
    intro u hu
    have := (convex_Icc (c - 1 / 2) (c + 1 / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun u : ℝ => u ^ (2 / 3 : ℝ)) (f' := fun t => 2 / 3 * t ^ (-(1 / 3) : ℝ))
      (C := 2 / 3 * (c - 1 / 2) ^ (-(1 / 3) : ℝ))
      (fun t ht => (sp_hasDerivAt (hup t ht)).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_pos (by have := Real.rpow_pos_of_pos (hup t ht) (-(1 / 3) : ℝ); positivity)]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos hcm ht.1 (by norm_num))
      hcI hu
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    have hd : |u - c| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have hpos : 0 < (c - 1 / 2) ^ (-(1 / 3) : ℝ) := Real.rpow_pos_of_pos hcm _
    calc |u ^ (2 / 3 : ℝ) - s0| ≤ 2 / 3 * (c - 1 / 2) ^ (-(1 / 3) : ℝ) * |u - c| := this
      _ ≤ 2 / 3 * (c - 1 / 2) ^ (-(1 / 3) : ℝ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by ring
  -- pointwise bound for the remainder R(u)
  set R : ℝ → ℝ := fun u => ((x + κ * u ^ (2 / 3 : ℝ)) ^ 2)⁻¹ - (y0 ^ 2)⁻¹ +
      2 * (y0 ^ 3)⁻¹ * ((x + κ * u ^ (2 / 3 : ℝ)) - y0) with hR
  set Bd : ℝ := 5 / 3 * κ ^ 2 * (c - 1 / 2) ^ (-(2 / 3) : ℝ) / y0 ^ 4 with hBd
  have hRb : ∀ u ∈ I, 0 ≤ R u ∧ R u ≤ Bd := by
    intro u hu
    have hsu : 0 < u ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos (hup u hu) _
    have hyu : 0 < x + κ * u ^ (2 / 3 : ℝ) := by positivity
    have hyy : y0 / 3 ≤ x + κ * u ^ (2 / 3 : ℝ) := by
      have := hlow u hu
      rw [hy0def]
      nlinarith only [this, hκ, hx]
    obtain ⟨h1, h2⟩ := inv_sq_taylor hyu hy0 hyy
    refine ⟨h1, h2.trans ?_⟩
    have hδ : (x + κ * u ^ (2 / 3 : ℝ) - y0) ^ 2 ≤ κ ^ 2 * (1 / 9 * (c - 1 / 2) ^ (-(2 / 3) : ℝ)) := by
      have e1 : x + κ * u ^ (2 / 3 : ℝ) - y0 = κ * (u ^ (2 / 3 : ℝ) - s0) := by rw [hy0def]; ring
      rw [e1, mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have h3 := hlip u hu
      have h4 : (u ^ (2 / 3 : ℝ) - s0) ^ 2 = |u ^ (2 / 3 : ℝ) - s0| ^ 2 := (sq_abs _).symm
      rw [h4]
      have h5 : (1 / 3 * (c - 1 / 2) ^ (-(1 / 3) : ℝ)) ^ 2 = 1 / 9 * (c - 1 / 2) ^ (-(2 / 3) : ℝ) := by
        have h6 : ((c - 1 / 2) ^ (-(1 / 3) : ℝ)) ^ 2 = (c - 1 / 2) ^ (-(2 / 3) : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hcm.le]; norm_num
        rw [mul_pow, h6]; norm_num
      calc |u ^ (2 / 3 : ℝ) - s0| ^ 2 ≤ (1 / 3 * (c - 1 / 2) ^ (-(1 / 3) : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h3 2
        _ = _ := h5
    have h4pos : 0 < y0 ^ 4 := by positivity
    calc 15 * (x + κ * u ^ (2 / 3 : ℝ) - y0) ^ 2 / y0 ^ 4
        ≤ 15 * (κ ^ 2 * (1 / 9 * (c - 1 / 2) ^ (-(2 / 3) : ℝ))) / y0 ^ 4 := by
          gcongr
      _ = Bd := by rw [hBd]; ring
  -- integrals
  have hcont : ContinuousOn (fun u => cphi κ x u) I := by
    intro u hu
    have hsu := (sp_hasDerivAt (hup u hu)).continuousAt
    unfold cphi
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun u : ℝ => x + κ * u ^ (2 / 3 : ℝ)) u := continuousAt_const.add (continuousAt_const.mul hsu)
    have hne : (x + κ * u ^ (2 / 3 : ℝ)) ^ 2 ≠ 0 := by
      have := Real.rpow_pos_of_pos (hup u hu) (2 / 3 : ℝ); positivity
    exact (h1.pow 2).inv₀ hne
  have hphiI : IntervalIntegrable (fun u => cphi κ x u) volume (c - 1 / 2) (c + 1 / 2) := by
    apply ContinuousOn.intervalIntegrable; rwa [uIcc_of_le (by linarith)]
  have hsI := sp_intervalIntegrable hcm (by linarith : 0 < c + 1 / 2)
  have hRint : ∫ u in (c - 1 / 2)..(c + 1 / 2), R u =
      (∫ u in (c - 1 / 2)..(c + 1 / 2), cphi κ x u) - (y0 ^ 2)⁻¹ -
        2 * κ * (y0 ^ 3)⁻¹ * (s0 - ∫ u in (c - 1 / 2)..(c + 1 / 2), u ^ (2 / 3 : ℝ)) := by
    have e : R = fun u => (cphi κ x u - (y0 ^ 2)⁻¹) + (2 * κ * (y0 ^ 3)⁻¹) * (u ^ (2 / 3 : ℝ) - s0) := by
      funext u; simp only [hR, cphi, hy0def]; ring
    rw [e, intervalIntegral.integral_add (hphiI.sub intervalIntegrable_const)
      ((hsI.sub intervalIntegrable_const).const_mul _), integral_sub hphiI intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_sub hsI intervalIntegrable_const]
    simp
    ring
  have hRi : IntervalIntegrable R volume (c - 1 / 2) (c + 1 / 2) := by
    have e : R = fun u => (cphi κ x u - (y0 ^ 2)⁻¹) + (2 * κ * (y0 ^ 3)⁻¹) * (u ^ (2 / 3 : ℝ) - s0) := by
      funext u; simp only [hR, cphi, hy0def]; ring
    rw [e]
    exact (hphiI.sub intervalIntegrable_const).add ((hsI.sub intervalIntegrable_const).const_mul _)
  have hlo : 0 ≤ ∫ u in (c - 1 / 2)..(c + 1 / 2), R u := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro u hu; exact (hRb u ⟨hu.1, hu.2⟩).1
  have hhi : ∫ u in (c - 1 / 2)..(c + 1 / 2), R u ≤ Bd := by
    have := intervalIntegral.integral_mono_on (a := c - 1 / 2) (b := c + 1 / 2) (by linarith) hRi
      (intervalIntegrable_const (c := Bd)) (fun u hu => (hRb u hu).2)
    simp at this
    linarith only [this]
  have hphic : cphi κ x c = (y0 ^ 2)⁻¹ := by simp [cphi, hy0def, hs0]
  rw [abs_le]
  rw [hRint] at hlo hhi
  rw [hphic]
  constructor <;> nlinarith only [hlo, hhi, hBd]

/-- The primitive `F(t) = (3/κ²)(arctan(t/a)/(2a) - t/(2(a²+t²)))`, `a² = x/κ`, of `3 t²/(x + κ t²)²`. -/
noncomputable def qPrim (κ x t : ℝ) : ℝ :=
  3 / κ ^ 2 * (Real.arctan (t / √(x / κ)) / (2 * √(x / κ)) - t / (2 * (x / κ + t ^ 2)))

lemma hasDerivAt_qPrim {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) (t : ℝ) :
    HasDerivAt (qPrim κ x) (3 * t ^ 2 / (x + κ * t ^ 2) ^ 2) t := by
  have hxk : 0 < x / κ := by positivity
  have ha : 0 < √(x / κ) := Real.sqrt_pos.mpr hxk
  have haa : √(x / κ) ^ 2 = x / κ := Real.sq_sqrt hxk.le
  have h1 : HasDerivAt (fun t : ℝ => t / √(x / κ)) (1 / √(x / κ)) t := (hasDerivAt_id t).div_const _
  have h2 := (Real.hasDerivAt_arctan (t / √(x / κ))).comp t h1
  have h3 := h2.div_const (2 * √(x / κ))
  have h4 : HasDerivAt (fun t : ℝ => x / κ + t ^ 2) (2 * t) t := by
    simpa using (hasDerivAt_pow 2 t).const_add (x / κ)
  have h5 := ((hasDerivAt_id t).div (h4.const_mul 2) (by positivity))
  have h6 := (h3.sub h5).const_mul (3 / κ ^ 2)
  unfold qPrim
  refine h6.congr_deriv ?_
  simp only [id]
  generalize √(x / κ) = a at *
  have hxa : x = κ * a ^ 2 := by rw [haa]; field_simp
  subst hxa
  have hne : a ≠ 0 := ha.ne'
  field_simp
  ring

lemma qPrim_zero {κ x : ℝ} : qPrim κ x 0 = 0 := by simp [qPrim]

lemma qPrim_tendsto {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    Tendsto (qPrim κ x) atTop (𝓝 (3 / κ ^ 2 * (π / 2 / (2 * √(x / κ))))) := by
  have hxk : 0 < x / κ := by positivity
  have ha : 0 < √(x / κ) := Real.sqrt_pos.mpr hxk
  have h1 : Tendsto (fun t : ℝ => t / √(x / κ)) atTop atTop :=
    tendsto_id.atTop_div_const ha
  have h2 := ((Real.tendsto_arctan_atTop.comp h1).mono_right nhdsWithin_le_nhds).div_const (2 * √(x / κ))
  have h3 : Tendsto (fun t : ℝ => t / (2 * (x / κ + t ^ 2))) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun t : ℝ => t⁻¹)
    · filter_upwards [eventually_gt_atTop 0] with t ht
      positivity
    · filter_upwards [eventually_gt_atTop 0] with t ht
      rw [div_le_iff₀ (by positivity)]
      have : 0 < t⁻¹ := inv_pos.mpr ht
      calc t = t⁻¹ * (t * t) := by field_simp
        _ ≤ t⁻¹ * (2 * (x / κ + t ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ this.le
          nlinarith only [hxk, sq_nonneg t]
    · exact tendsto_inv_atTop_zero
  have := (h2.sub h3).const_mul (3 / κ ^ 2)
  rw [sub_zero] at this
  exact this

lemma q_integrableOn {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => 3 * t ^ 2 / (x + κ * t ^ 2) ^ 2) (Ioi 0) := by
  refine integrableOn_Ioi_deriv_of_nonneg (g := qPrim κ x) ?_ (fun t _ => hasDerivAt_qPrim hκ hx t)
    (fun t _ => by positivity) (qPrim_tendsto hκ hx)
  exact (hasDerivAt_qPrim hκ hx 0).continuousAt.continuousWithinAt

lemma q_integral {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    ∫ t in Ioi 0, 3 * t ^ 2 / (x + κ * t ^ 2) ^ 2 = 3 / κ ^ 2 * (π / 2 / (2 * √(x / κ))) := by
  have := integral_Ioi_of_hasDerivAt_of_tendsto (f := qPrim κ x)
    (f' := fun t => 3 * t ^ 2 / (x + κ * t ^ 2) ^ 2)
    (hasDerivAt_qPrim hκ hx 0).continuousAt.continuousWithinAt
    (fun t _ => hasDerivAt_qPrim hκ hx t) (q_integrableOn hκ hx) (qPrim_tendsto hκ hx)
  rw [this, qPrim_zero, sub_zero]

lemma cphi_comp_cube {κ x t : ℝ} (ht : 0 < t) :
    (3 * t ^ ((3 : ℝ) - 1)) • cphi κ x (t ^ (3 : ℝ)) = 3 * t ^ 2 / (x + κ * t ^ 2) ^ 2 := by
  have e1 : (t ^ (3 : ℝ)) ^ (2 / 3 : ℝ) = t ^ 2 := by
    rw [← Real.rpow_mul ht.le]
    norm_num
  have e2 : t ^ ((3 : ℝ) - 1) = t ^ 2 := by norm_num
  unfold cphi
  rw [e1, e2, smul_eq_mul]
  field_simp

theorem cphi_integrableOn {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) :
    IntegrableOn (cphi κ x) (Ioi 0) := by
  have := integrableOn_Ioi_comp_rpow_iff (cphi κ x) (p := 3) (by norm_num)
  rw [← this]
  have e : IntegrableOn (fun t : ℝ => 3 * t ^ 2 / (x + κ * t ^ 2) ^ 2) (Ioi 0) := q_integrableOn hκ hx
  refine e.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have := cphi_comp_cube (κ := κ) (x := x) ht
  simp only [abs_of_pos (by norm_num : (0:ℝ) < 3)]
  rw [← this]

/-- `∫_0^∞ (x + κ u^{2/3})^{-2} du = 3π/(4 κ² √(x/κ))`, which is `1/(2√x)` when `κ³ = (3π/2)²`. -/
theorem cphi_integral {κ x : ℝ} (hκ : 0 < κ) (hκ3 : κ ^ 3 = (3 * π / 2) ^ 2) (hx : 0 < x) :
    ∫ u in Ioi 0, cphi κ x u = 1 / (2 * √x) := by
  have h := integral_comp_rpow_Ioi_of_pos (g := cphi κ x) (p := 3) (by norm_num)
  have e : ∫ t in Ioi (0 : ℝ), (3 * t ^ ((3 : ℝ) - 1)) • cphi κ x (t ^ (3 : ℝ)) =
      ∫ t in Ioi (0 : ℝ), 3 * t ^ 2 / (x + κ * t ^ 2) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => cphi_comp_cube ht)
  rw [← h, e, q_integral hκ hx]
  have hk : 0 < √κ := Real.sqrt_pos.mpr hκ
  have hkk : √κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hxs : 0 < √x := Real.sqrt_pos.mpr hx
  have hsq : √(x / κ) = √x / √κ := Real.sqrt_div hx.le _
  have key : 3 * π * √κ = 2 * κ ^ 2 := by
    have h1 : (3 * π * √κ) ^ 2 = (2 * κ ^ 2) ^ 2 := by
      have : (3 * π * √κ) ^ 2 = 9 * π ^ 2 * κ := by rw [mul_pow, mul_pow, hkk]; ring
      rw [this]
      have h2 : (2 * κ ^ 2) ^ 2 = 4 * κ * κ ^ 3 := by ring
      rw [h2, hκ3]; ring
    exact (pow_left_inj₀ (by positivity) (by positivity) (by norm_num)).mp h1
  rw [hsq]
  field_simp
  nlinarith only [key, hk, hxs, hκ]

/-! ### Cell data at the sites `c_n = n + 3/4` -/

/-- The sites `c_n = n + 3/4` (`= k - 1/4` for `k = n + 1`). -/
noncomputable def cc (n : ℕ) : ℝ := (n : ℝ) + 3 / 4

/-- The cell defect of `u^{2/3}`. -/
noncomputable def d0c (n : ℕ) : ℝ := cc n ^ (2 / 3 : ℝ) - ∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), u ^ (2 / 3 : ℝ)

/-- The cell defect of `φ_x`. -/
noncomputable def dcell (κ x : ℝ) (n : ℕ) : ℝ :=
  cphi κ x (cc n) - ∫ u in (cc n - 1 / 2)..(cc n + 1 / 2), cphi κ x u

/-- The constant `4^{4/3}`. -/
noncomputable def c43 : ℝ := (4 : ℝ) ^ (4 / 3 : ℝ)

lemma c43_pos : 0 < c43 := by unfold c43; positivity

lemma rpow_quarter_le (n : ℕ) {e : ℝ} (he : 0 ≤ e) :
    ((n : ℝ) + 1 / 4) ^ (-e) ≤ (4 : ℝ) ^ e * ((n : ℝ) + 1) ^ (-e) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : ((n : ℝ) + 1) / 4 ≤ (n : ℝ) + 1 / 4 := by linarith
  have h2 : ((n : ℝ) + 1 / 4) ^ (-e) ≤ (((n : ℝ) + 1) / 4) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith)
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4)]
  rw [Real.rpow_neg (by positivity)]
  have : (4 : ℝ) ^ e ≠ 0 := by positivity
  field_simp

lemma cc_sub_half (n : ℕ) : cc n - 1 / 2 = (n : ℝ) + 1 / 4 := by unfold cc; ring

lemma cc_ge (n : ℕ) : 3 / 4 ≤ cc n := by unfold cc; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith

lemma d0c_bound (n : ℕ) : |d0c n| ≤ (2 / 9 / 12 * c43) * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) := by
  have h := sp_midpoint (cc_ge n)
  have h2 : (cc n - 1 / 2) ^ (-(4 / 3) : ℝ) ≤ (4 : ℝ) ^ (4 / 3 : ℝ) * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) := by
    rw [cc_sub_half]; exact rpow_quarter_le n (e := 4 / 3) (by norm_num)
  unfold d0c c43
  calc _ ≤ _ := h
    _ ≤ 2 / 9 * ((4 : ℝ) ^ (4 / 3 : ℝ) * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ)) / 12 := by
        gcongr
    _ = _ := by ring

lemma tendsto_ratio_cube {b : ℝ} (hb : 0 ≤ b) : Tendsto (fun x : ℝ => (x / (x + b)) ^ 3) atTop (𝓝 1) := by
  have h1 : Tendsto (fun x : ℝ => (1 + b * x⁻¹)⁻¹) atTop (𝓝 ((1 + b * 0)⁻¹)) := by
    apply Tendsto.inv₀ _ (by norm_num)
    exact tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
  simp only [mul_zero, add_zero, inv_one] at h1
  have h2 := h1.pow 3
  rw [one_pow] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  congr 1
  field_simp

/-- The cell defect of `φ_x` equals the linearised one up to `(5/3) κ² (n + 1/4)^{-2/3}/y₀⁴`. -/
lemma dcell_decomp {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) (n : ℕ) :
    |dcell κ x n + 2 * κ * ((x + κ * cc n ^ (2 / 3 : ℝ)) ^ 3)⁻¹ * d0c n| ≤
      5 / 3 * κ ^ 2 * ((n : ℝ) + 1 / 4) ^ (-(2 / 3) : ℝ) / (x + κ * cc n ^ (2 / 3 : ℝ)) ^ 4 := by
  have h := cphi_cell hκ hx (cc_ge n)
  have e : (cc n - 1 / 2) ^ (-(2 / 3) : ℝ) = ((n : ℝ) + 1 / 4) ^ (-(2 / 3) : ℝ) := by rw [cc_sub_half]
  rw [e] at h
  exact h

/-- Uniform bound on `x³ · (cell defect)` for `x > 0`. -/
lemma dcell_bound {κ x : ℝ} (hκ : 0 < κ) (hx : 0 < x) (n : ℕ) :
    |x ^ 3 * dcell κ x n| ≤ (5 / 3 * κ * c43 + 2 * κ * (2 / 9 / 12 * c43)) * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn4 : 0 < (n : ℝ) + 1 / 4 := by linarith
  have hc : (n : ℝ) + 1 / 4 ≤ cc n := by unfold cc; linarith
  set s : ℝ := cc n ^ (2 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by unfold cc; linarith) _
  set y0 : ℝ := x + κ * s with hy0
  have hy0p : 0 < y0 := by positivity
  have hxy : x ≤ y0 := by rw [hy0]; nlinarith only [hκ, hs0]
  set q : ℝ := ((n : ℝ) + 1 / 4) ^ (-(2 / 3) : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hn4 _
  have hsq : s⁻¹ ≤ q := by
    have h1 : ((n : ℝ) + 1 / 4) ^ (2 / 3 : ℝ) ≤ s := Real.rpow_le_rpow hn4.le hc (by norm_num)
    have h2 : q = (((n : ℝ) + 1 / 4) ^ (2 / 3 : ℝ))⁻¹ := by
      rw [hq, Real.rpow_neg hn4.le]
    rw [h2]
    exact inv_anti₀ (Real.rpow_pos_of_pos hn4 _) h1
  have hqq : q * q = ((n : ℝ) + 1 / 4) ^ (-(4 / 3) : ℝ) := by
    rw [hq, ← Real.rpow_add hn4]; norm_num
  have hqq2 : ((n : ℝ) + 1 / 4) ^ (-(4 / 3) : ℝ) ≤ c43 * ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) :=
    rpow_quarter_le n (e := 4 / 3) (by norm_num)
  have hd := dcell_decomp hκ hx n
  have hd0 := d0c_bound n
  set Bn : ℝ := ((n : ℝ) + 1) ^ (-(4 / 3) : ℝ) with hBn
  have hBn0 : 0 < Bn := Real.rpow_pos_of_pos (by linarith) _
  -- the decomposition
  set A : ℝ := 2 * κ * (y0 ^ 3)⁻¹ * d0c n with hA
  have hx3 : x ^ 3 * (y0 ^ 3)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    exact pow_le_pow_left₀ hx.le hxy 3
  have hAb : |x ^ 3 * A| ≤ 2 * κ * (2 / 9 / 12 * c43 * Bn) := by
    have : x ^ 3 * A = 2 * κ * (x ^ 3 * (y0 ^ 3)⁻¹) * d0c n := by rw [hA]; ring
    rw [this, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * κ),
      abs_of_nonneg (by positivity : 0 ≤ x ^ 3 * (y0 ^ 3)⁻¹)]
    have h3 : 2 * κ * (x ^ 3 * (y0 ^ 3)⁻¹) * |d0c n| ≤ 2 * κ * 1 * |d0c n| := by
      gcongr
    have h4 : 2 * κ * 1 * |d0c n| ≤ 2 * κ * (2 / 9 / 12 * c43 * Bn) := by
      have := mul_le_mul_of_nonneg_left hd0 (by positivity : (0 : ℝ) ≤ 2 * κ * 1)
      linarith only [this]
    exact h3.trans h4
  have hBb : |x ^ 3 * (dcell κ x n + A)| ≤ 5 / 3 * κ * c43 * Bn := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < x ^ 3)]
    calc x ^ 3 * |dcell κ x n + A| ≤ x ^ 3 * (5 / 3 * κ ^ 2 * q / y0 ^ 4) := by
          apply mul_le_mul_of_nonneg_left hd (by positivity)
      _ = 5 / 3 * κ ^ 2 * q * (x ^ 3 / y0 ^ 4) := by ring
      _ ≤ 5 / 3 * κ ^ 2 * q * (1 / (κ * s)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : x ^ 3 / y0 ^ 4 ≤ 1 / y0 := by
            rw [div_le_div_iff₀ (by positivity) hy0p]
            have : x ^ 3 ≤ y0 ^ 3 := pow_le_pow_left₀ hx.le hxy 3
            nlinarith only [this, hy0p]
          refine h1.trans ?_
          apply one_div_le_one_div_of_le (by positivity)
          rw [hy0]; linarith only [hx]
      _ = 5 / 3 * κ * (q * s⁻¹) := by field_simp
      _ ≤ 5 / 3 * κ * (q * q) := by gcongr
      _ ≤ 5 / 3 * κ * (c43 * Bn) := by rw [hqq]; gcongr
      _ = 5 / 3 * κ * c43 * Bn := by ring
  have hsplit : x ^ 3 * dcell κ x n = x ^ 3 * (dcell κ x n + A) - x ^ 3 * A := by ring
  rw [hsplit]
  refine (abs_sub _ _).trans ?_
  nlinarith only [hAb, hBb]

lemma dcell_tendsto {κ : ℝ} (hκ : 0 < κ) (n : ℕ) :
    Tendsto (fun x : ℝ => x ^ 3 * dcell κ x n) atTop (𝓝 (-(2 * κ * d0c n))) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn4 : 0 < (n : ℝ) + 1 / 4 := by linarith
  set s : ℝ := cc n ^ (2 / 3 : ℝ) with hs
  have hs0 : 0 < s := Real.rpow_pos_of_pos (by unfold cc; linarith) _
  set b : ℝ := κ * s with hb
  have hb0 : 0 < b := by positivity
  set q : ℝ := ((n : ℝ) + 1 / 4) ^ (-(2 / 3) : ℝ) with hq
  -- (i) the remainder tends to 0
  have hi : Tendsto (fun x : ℝ => x ^ 3 * (dcell κ x n + 2 * κ * ((x + b) ^ 3)⁻¹ * d0c n)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => 5 / 3 * κ ^ 2 * q * x⁻¹)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : 0 < x ^ 3)]
      have hd := dcell_decomp hκ hx n
      have hy0 : 0 < x + b := by positivity
      calc x ^ 3 * |dcell κ x n + 2 * κ * ((x + b) ^ 3)⁻¹ * d0c n|
          ≤ x ^ 3 * (5 / 3 * κ ^ 2 * q / (x + b) ^ 4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact hd
        _ = 5 / 3 * κ ^ 2 * q * (x ^ 3 / (x + b) ^ 4) := by ring
        _ ≤ 5 / 3 * κ ^ 2 * q * x⁻¹ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← one_div, div_le_div_iff₀ (by positivity) hx]
            have h1 : x ≤ x + b := by linarith
            have h2 : x ^ 4 ≤ (x + b) ^ 4 := pow_le_pow_left₀ hx.le h1 4
            nlinarith only [h2]
    · have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (5 / 3 * κ ^ 2 * q)
      simpa using this
  have hii : Tendsto (fun x : ℝ => x ^ 3 * (2 * κ * ((x + b) ^ 3)⁻¹ * d0c n)) atTop (𝓝 (2 * κ * d0c n)) := by
    have := (tendsto_ratio_cube hb0.le).const_mul (2 * κ * d0c n)
    simp only [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have : 0 < x + b := by positivity
    field_simp
  have := hi.sub hii
  simp only [zero_sub] at this
  refine this.congr' ?_
  filter_upwards with x
  ring

/-- info: 'FormalResearch.Special.AiryMoment.cphi_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cphi_integral

/-- info: 'FormalResearch.Special.AiryMoment.dcell_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dcell_tendsto

/-- info: 'FormalResearch.Special.AiryMoment.dcell_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dcell_bound

end FormalResearch.Special.AiryMoment


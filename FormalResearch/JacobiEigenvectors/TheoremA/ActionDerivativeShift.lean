module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.ActionDerivativeStable

/-!
# Paper J, Layer 2: the derivative of a shifted action (L2.E, Step 1 of cor:eigen, part 2)

Source: Paper J `thmA.tex`, proof of `cor:eigen`, Step 1 (`eq:cp-S0p`: `S_0'(X) = -int_{u_-}^{u_+} du/sqrt(T)`; `eq:cp-dt`: `d_t S_0^{(t)}(X)|_{t=0} = int (B_1 + Q_0 G_1/(2 G_0))/sqrt(T) du`).

## Proved here

* `arccos_sub_eq`: `arccos w_2 - arccos w_1 = - int_{w_1}^{w_2} h`, `h(w) = 1/sqrt(1 - w^2)` (`0` for `|w| >= 1`): the fundamental theorem of calculus for `arccos`, differentiable off `{-1, 1}`.
* `pt_formula` (the pointwise identity): for `E >= 0`,
  `arccos((X + t r - beta)/(2 sqrt E)) - arccos((X - beta)/(2 sqrt E)) = - int_0^t r / sqrt(4 E - (X + s r - beta)^2) ds` (also for `E = 0`, both sides vanish).
* `interval_swap`: Fubini for `int_0^L int_0^t` for either sign of `t`.
* **`hasDerivAt_shiftAction`** (the shift theorem): let `E, B` have `HasDerivWithinAt` derivatives continuous on `[0, L]`, `E(0) = E(L) = 0`, `E > 0` on `(0, L)`, `rho(u, t)` jointly continuous with continuous
  `u`-derivative, and let `T_0(u) = 4 E - (X - B)^2` have, at `X`, the allowed set `[a_0, b_0]` with `T_0 > 0` inside, `T_0 < 0` outside and simple zeros (`T_0'(a_0) > 0 > T_0'(b_0)`).  Then
  `t |-> int_0^L arccos((X + t rho(u, t) - B(u))/(2 sqrt(E(u)))) du` has derivative `- int_0^L rho(u, 0)/sqrt(T_0(u)) du` at `t = 0`.
  Proof: the pointwise identity with `s`-integral, Fubini, and continuity of `(t, s) |-> int_0^L rho(u, t)/sqrt(T(X + s rho(u,t); u)) du` at `(0, 0)` from `ActionDerivativeStable.lean` (`stable_structure`, `integral_inv_sqrt_continuousAt`).

`rho = 1` gives `eq:cp-S0p`, and `rho = -(B_1 + (X - B_0) G_1/(2 G_0))`-type shifts give `eq:cp-dt` (`ActionDerivative.lean`).

## Differences from the paper

The paper differentiates under the integral sign after the substitution `u = u_-(lambda) + (u_+ - u_-) s` (Hadamard division, smooth turning points by the implicit function theorem, `hasDerivAt_integral_of_dominated_loc_of_deriv_le`).  Here the derivative is obtained
without differentiating the turning points: `S(t) - S(0)` is written as `- int_0^t Psi(t, s) ds` (fundamental theorem of calculus in the energy variable for each fixed `u`, then Fubini), and only the continuity of `Psi` at `(0, 0)` is needed;
that continuity is the content of `ActionDerivativeStable.lean`.  No implicit function theorem is used.

## Not formalised

See `ActionDerivative.lean` for the application to `actionS0`.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv

open Set Filter Topology MeasureTheory
open scoped Interval

/-- `h w = 1/sqrt(1 - w^2)` for `|w| < 1` and `0` otherwise (Lean's `sqrt` of a nonpositive number is `0`). -/
def hfun (w : ℝ) : ℝ := (Real.sqrt (1 - w ^ 2))⁻¹

lemma hfun_eq_indicator : hfun = Set.indicator (Icc (-1 : ℝ) 1) (fun w => (Real.sqrt ((w - (-1)) * (1 - w)))⁻¹) := by
  funext w
  unfold hfun
  by_cases hw : w ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hw]
    congr 2
    ring
  · rw [Set.indicator_of_notMem hw]
    have : 1 - w ^ 2 ≤ 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hw
      rcases hw with h | h <;> nlinarith
    rw [Real.sqrt_eq_zero_of_nonpos this, inv_zero]

lemma integrable_hfun : Integrable hfun volume := by
  rw [hfun_eq_indicator, integrable_indicator_iff measurableSet_Icc]
  have := intervalIntegrable_inv_sqrt (a := (-1 : ℝ)) (b := 1) (by norm_num)
  rwa [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at this

lemma intervalIntegrable_hfun (a b : ℝ) : IntervalIntegrable hfun volume a b :=
  integrable_hfun.intervalIntegrable

/-- **FTC for `arccos` with the clamped derivative**: `arccos w2 - arccos w1 = - int_{w1}^{w2} h`. -/
lemma arccos_sub_eq (w1 w2 : ℝ) : Real.arccos w2 - Real.arccos w1 = -∫ w in w1..w2, hfun w := by
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable (fun w => Real.arccos w)
    (fun w => -hfun w) (a := w1) (b := w2) (s := {-1, 1}) (by simp [Set.countable_insert])
    Real.continuous_arccos.continuousOn (fun w hw => ?_) (intervalIntegrable_hfun w1 w2).neg
  · rw [intervalIntegral.integral_neg] at h
    linarith
  · have h1 : w ≠ -1 := fun e => hw.2 (by simp [e])
    have h2 : w ≠ 1 := fun e => hw.2 (by simp [e])
    rcases lt_trichotomy w 1 with hlt | heq | hgt
    · rcases lt_trichotomy w (-1) with hlt' | heq' | hgt'
      · have : HasDerivAt (fun _ : ℝ => Real.pi) 0 w := hasDerivAt_const _ _
        refine (this.congr_of_eventuallyEq ?_).congr_deriv ?_
        · filter_upwards [Iio_mem_nhds hlt'] with z hz
          exact Real.arccos_of_le_neg_one (le_of_lt hz)
        · have : 1 - w ^ 2 ≤ 0 := by nlinarith
          simp [hfun, Real.sqrt_eq_zero_of_nonpos this]
      · exact absurd heq' h1
      · have := Real.hasDerivAt_arccos h1 h2
        refine this.congr_deriv ?_
        simp [hfun]
    · exact absurd heq h2
    · have : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 w := hasDerivAt_const _ _
      refine (this.congr_of_eventuallyEq ?_).congr_deriv ?_
      · filter_upwards [Ioi_mem_nhds hgt] with z hz
        exact Real.arccos_of_one_le (le_of_lt hz)
      · have : 1 - w ^ 2 ≤ 0 := by nlinarith
        simp [hfun, Real.sqrt_eq_zero_of_nonpos this]

lemma pt_formula {E β X r t : ℝ} (hE : 0 ≤ E) :
    Real.arccos ((X + t * r - β) / (2 * Real.sqrt E)) - Real.arccos ((X - β) / (2 * Real.sqrt E)) =
      -∫ s in (0 : ℝ)..t, r * (Real.sqrt (4 * E - (X + s * r - β) ^ 2))⁻¹ := by
  rcases hE.eq_or_lt with h0 | hpos
  · rw [← h0]
    have this : ∀ s : ℝ, r * (Real.sqrt (4 * 0 - (X + s * r - β) ^ 2))⁻¹ = 0 := by
      intro s
      rw [Real.sqrt_eq_zero_of_nonpos (by nlinarith [sq_nonneg (X + s * r - β)]), inv_zero, mul_zero]
    have hz : ∫ s in (0 : ℝ)..t, r * (Real.sqrt (4 * 0 - (X + s * r - β) ^ 2))⁻¹ = 0 := by
      simp only [this, intervalIntegral.integral_zero]
    rw [hz]
    simp
  · set σ := 2 * Real.sqrt E with hσ
    have hσpos : 0 < σ := by rw [hσ]; have := Real.sqrt_pos.2 hpos; positivity
    have hσ2 : σ ^ 2 = 4 * E := by
      rw [hσ, mul_pow, Real.sq_sqrt hE]; ring
    have h1 := arccos_sub_eq ((X - β) / σ) ((X + t * r - β) / σ)
    have h2 : ∫ w in (X - β) / σ..(X + t * r - β) / σ, hfun w =
        ∫ s in (0 : ℝ)..t, r * (Real.sqrt (4 * E - (X + s * r - β) ^ 2))⁻¹ := by
      have e1 : ∀ ξ : ℝ, (Real.sqrt (4 * E - (ξ - β) ^ 2))⁻¹ = σ⁻¹ * hfun ((ξ - β) / σ) := by
        intro ξ
        unfold hfun
        have : 4 * E - (ξ - β) ^ 2 = σ ^ 2 * (1 - ((ξ - β) / σ) ^ 2) := by
          rw [hσ2.symm]; field_simp
        rw [this, Real.sqrt_mul (sq_nonneg σ), Real.sqrt_sq hσpos.le, mul_inv]
      have e2 := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := t)
        (f := fun ξ => (Real.sqrt (4 * E - (ξ - β) ^ 2))⁻¹) r X
      simp only [mul_zero, zero_add, smul_eq_mul] at e2
      have e3 : ∫ ξ in X..r * t + X, (Real.sqrt (4 * E - (ξ - β) ^ 2))⁻¹ =
          σ⁻¹ * ∫ ξ in X..r * t + X, hfun ((ξ - β) / σ) := by
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun ξ _ => e1 ξ)
      have e4 : ∫ ξ in X..r * t + X, hfun ((ξ - β) / σ) =
          σ * ∫ w in (X - β) / σ..(r * t + X - β) / σ, hfun w := by
        have := intervalIntegral.integral_comp_div (a := X - β) (b := r * t + X - β) (fun w => hfun w) hσpos.ne'
        have h5 := intervalIntegral.integral_comp_sub_right (a := X) (b := r * t + X) (fun y => hfun (y / σ)) β
        simp only [smul_eq_mul] at this
        rw [this] at h5
        simpa using h5
      have e5 : ∀ s : ℝ, r * (Real.sqrt (4 * E - (r * s + X - β) ^ 2))⁻¹ =
          r * (Real.sqrt (4 * E - (X + s * r - β) ^ 2))⁻¹ := by
        intro s; congr 3; ring
      have e6 : r * t + X = X + t * r := by ring
      rw [e3, e4, e6] at e2
      have e7 : (X + t * r - β) / σ = (r * t + X - β) / σ := by rw [e6]
      have : σ⁻¹ * (σ * ∫ w in (X - β) / σ..(X + t * r - β) / σ, hfun w) =
          ∫ s in (0 : ℝ)..t, r * (Real.sqrt (4 * E - (X + s * r - β) ^ 2))⁻¹ := by
        rw [← e2, ← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun s _ => e5 s)
      rw [← this]
      field_simp
    rw [← h2]
    linarith

/-- Fubini for `int_0^L int_0^t` (any sign of `t`). -/
lemma interval_swap {L t : ℝ} (hL : 0 ≤ L) {Φ : ℝ → ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2)
      ((volume.restrict (Ι (0 : ℝ) L)).prod (volume.restrict (Ι (0 : ℝ) t))))
    (hint : ∀ s ∈ Ι (0 : ℝ) t, IntervalIntegrable (fun u => Φ u s) volume 0 L)
    (hnorm : IntervalIntegrable (fun s => ∫ u in (0 : ℝ)..L, ‖Φ u s‖) volume 0 t) :
    ∫ u in (0 : ℝ)..L, ∫ s in (0 : ℝ)..t, Φ u s = ∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..L, Φ u s := by
  set μ : Measure ℝ := volume.restrict (Ι (0 : ℝ) L) with hμ
  set ν : Measure ℝ := volume.restrict (Ι (0 : ℝ) t) with hν
  have hI : Integrable (fun p : ℝ × ℝ => Φ p.1 p.2) (μ.prod ν) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨?_, ?_⟩
    · rw [hν, ae_restrict_iff' measurableSet_uIoc]
      refine Eventually.of_forall fun s hs => ?_
      have := hint s hs
      rw [intervalIntegrable_iff] at this
      exact this
    · have := hnorm
      rw [intervalIntegrable_iff] at this
      have e : ∀ s, ∫ u in (0 : ℝ)..L, ‖Φ u s‖ = ∫ u, ‖Φ u s‖ ∂μ := by
        intro s
        rw [intervalIntegral.integral_of_le hL, hμ, Set.uIoc_of_le hL]
      exact Integrable.congr this (Eventually.of_forall fun s => e s)
  have hsw := integral_integral_swap hI
  have key : ∀ g : ℝ → ℝ, ∫ s in (0 : ℝ)..t, g s = (if 0 ≤ t then 1 else -1) * ∫ s, g s ∂ν := by
    intro g
    rcases le_total 0 t with h | h
    · simp only [h, ↓reduceIte, one_mul]
      rw [intervalIntegral.integral_of_le h, hν, Set.uIoc_of_le h]
    · by_cases h0 : 0 ≤ t
      · have : t = 0 := le_antisymm h h0
        subst this
        simp [hν]
      · simp only [h0, ↓reduceIte]
        rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le h, hν, Set.uIoc_of_ge h]
        ring
  have e1 : ∀ g : ℝ → ℝ, ∫ u in (0 : ℝ)..L, g u = ∫ u, g u ∂μ := by
    intro g
    rw [intervalIntegral.integral_of_le hL, hμ, Set.uIoc_of_le hL]
  simp_rw [key, e1]
  rw [integral_const_mul, hsw]

lemma intervalIntegrable_arccos_aux {L : ℝ} (hL : 0 ≤ L) {g : ℝ → ℝ} (hg : ContinuousOn g (Ioo 0 L)) :
    IntervalIntegrable (fun u => Real.arccos (g u)) volume 0 L := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
  have hm : AEStronglyMeasurable (fun u => Real.arccos (g u)) (volume.restrict (Ioc 0 L)) := by
    have h1 := (Real.continuous_arccos.comp_continuousOn hg).aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h1
  have hfin : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) L)) := ⟨by simp⟩
  refine (integrable_const Real.pi).mono' hm (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.arccos_nonneg _)]
  exact Real.arccos_le_pi _

theorem hasDerivAt_shiftAction {L : ℝ} (hL : 0 < L) {E B E1 B1 : ℝ → ℝ}
    (hEd : ∀ u ∈ Icc 0 L, HasDerivWithinAt E (E1 u) (Icc 0 L) u) (hE1c : ContinuousOn E1 (Icc 0 L))
    (hBd : ∀ u ∈ Icc 0 L, HasDerivWithinAt B (B1 u) (Icc 0 L) u) (hB1c : ContinuousOn B1 (Icc 0 L))
    (hE0 : E 0 = 0) (hEL : E L = 0) (hEpos : ∀ u ∈ Ioo 0 L, 0 < E u)
    {ρ ρ1 : ℝ → ℝ → ℝ}
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) (Icc 0 L ×ˢ univ))
    (hρd : ∀ t, ∀ u ∈ Icc 0 L, HasDerivWithinAt (fun v => ρ v t) (ρ1 u t) (Icc 0 L) u)
    (hρ1c : ContinuousOn (fun p : ℝ × ℝ => ρ1 p.1 p.2) (Icc 0 L ×ˢ univ))
    {X a0 b0 : ℝ} (ha0 : 0 ≤ a0) (hab : a0 < b0) (hb0 : b0 ≤ L)
    (hza : 4 * E a0 - (X - B a0) ^ 2 = 0) (hzb : 4 * E b0 - (X - B b0) ^ 2 = 0)
    (hneg : ∀ u ∈ Icc 0 L, u ∉ Icc a0 b0 → 4 * E u - (X - B u) ^ 2 < 0)
    (hpos : ∀ u ∈ Ioo a0 b0, 0 < 4 * E u - (X - B u) ^ 2)
    (hda : 0 < 4 * E1 a0 + 2 * (X - B a0) * B1 a0) (hdb : 4 * E1 b0 + 2 * (X - B b0) * B1 b0 < 0) :
    HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..L, Real.arccos ((X + t * ρ u t - B u) / (2 * Real.sqrt (E u))))
      (-∫ u in (0 : ℝ)..L, ρ u 0 / Real.sqrt (4 * E u - (X - B u) ^ 2)) 0 := by
  -- the family `f u (t, s) = T(X + s ρ(u, t); u)`
  set f : ℝ → ℝ × ℝ → ℝ := fun u l => 4 * E u - (X + l.2 * ρ u l.1 - B u) ^ 2 with hf
  set f1 : ℝ → ℝ × ℝ → ℝ := fun u l =>
    4 * E1 u - 2 * (X + l.2 * ρ u l.1 - B u) * (l.2 * ρ1 u l.1 - B1 u) with hf1
  have hEcont : ContinuousOn E (Icc 0 L) := fun u hu => (hEd u hu).continuousWithinAt
  have hBcont : ContinuousOn B (Icc 0 L) := fun u hu => (hBd u hu).continuousWithinAt
  have hSρ : ∀ (g : ℝ → ℝ → ℝ), ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Icc 0 L ×ˢ univ) →
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => g p.1 p.2.1) (Icc 0 L ×ˢ univ) := by
    intro g hg
    refine hg.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn ?_
    intro p hp
    exact ⟨hp.1, mem_univ _⟩
  have hSE : ∀ (g : ℝ → ℝ), ContinuousOn g (Icc 0 L) →
      ContinuousOn (fun p : ℝ × (ℝ × ℝ) => g p.1) (Icc 0 L ×ˢ univ) := by
    intro g hg
    exact hg.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hs2 : Continuous (fun p : ℝ × (ℝ × ℝ) => p.2.2) := continuous_snd.comp continuous_snd
  have hfc : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2) (Icc 0 L ×ˢ univ) := by
    show ContinuousOn (fun p : ℝ × (ℝ × ℝ) => 4 * E p.1 - (X + p.2.2 * ρ p.1 p.2.1 - B p.1) ^ 2) _
    exact (continuousOn_const.mul (hSE E hEcont)).sub
      (ContinuousOn.pow ((continuousOn_const.add (hs2.continuousOn.mul (hSρ ρ hρc))).sub (hSE B hBcont)) 2)
  have hf1c : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => f1 p.1 p.2) (Icc 0 L ×ˢ univ) := by
    show ContinuousOn (fun p : ℝ × (ℝ × ℝ) => 4 * E1 p.1 - 2 * (X + p.2.2 * ρ p.1 p.2.1 - B p.1) *
      (p.2.2 * ρ1 p.1 p.2.1 - B1 p.1)) _
    exact (continuousOn_const.mul (hSE E1 hE1c)).sub
      ((continuousOn_const.mul ((continuousOn_const.add (hs2.continuousOn.mul (hSρ ρ hρc))).sub (hSE B hBcont))).mul
        ((hs2.continuousOn.mul (hSρ ρ1 hρ1c)).sub (hSE B1 hB1c)))
  have hfd : ∀ l : ℝ × ℝ, ∀ u ∈ Icc 0 L, HasDerivWithinAt (fun v => f v l) (f1 u l) (Icc 0 L) u := by
    intro l u hu
    have h1 := ((hEd u hu).const_mul 4).sub ((((hρd l.1 u hu).const_mul l.2).const_add X).sub (hBd u hu) |>.pow 2)
    refine h1.congr_deriv ?_
    simp only [hf1, Pi.sub_apply]
    ring
  have hf0 : ∀ l : ℝ × ℝ, f 0 l ≤ 0 := fun l => by
    show 4 * E 0 - (X + l.2 * ρ 0 l.1 - B 0) ^ 2 ≤ 0
    rw [hE0]; nlinarith [sq_nonneg (X + l.2 * ρ 0 l.1 - B 0)]
  have hfL : ∀ l : ℝ × ℝ, f L l ≤ 0 := fun l => by
    show 4 * E L - (X + l.2 * ρ L l.1 - B L) ^ 2 ≤ 0
    rw [hEL]; nlinarith [sq_nonneg (X + l.2 * ρ L l.1 - B L)]
  have hf00 : ∀ u, f u (0, 0) = 4 * E u - (X - B u) ^ 2 := fun u => by simp [hf]
  have hf10 : ∀ u, f1 u (0, 0) = 4 * E1 u + 2 * (X - B u) * B1 u := fun u => by simp [hf1]
  obtain ⟨V, hVo, hl0V, a, b, c, hc0, hab', hprop⟩ := stable_structure (l0 := ((0 : ℝ), (0 : ℝ))) hfc hfd hf1c hf0 hfL ha0 hab hb0
    (by rw [hf00]; exact hza) (by rw [hf00]; exact hzb)
    (fun u hu hn => by rw [hf00]; exact hneg u hu hn)
    (fun u hu => by rw [hf00]; exact hpos u hu)
    (by rw [hf10]; exact hda) (by rw [hf10]; exact hdb)
  have hq1 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => ρ p.1 p.2.1) (Icc 0 L ×ˢ univ) := hSρ ρ hρc
  have hq2 : ContinuousOn (fun p : ℝ × (ℝ × ℝ) => |ρ p.1 p.2.1|) (Icc 0 L ×ˢ univ) := hq1.abs
  have hΨ1 := integral_inv_sqrt_continuousAt (q := fun u (l : ℝ × ℝ) => ρ u l.1) hfc hq1 hc0 hVo
    (fun l hl => hab' l hl) (fun l hl => hprop l hl)
  have hΨ2 := integral_inv_sqrt_continuousAt (q := fun u (l : ℝ × ℝ) => |ρ u l.1|) hfc hq2 hc0 hVo
    (fun l hl => hab' l hl) (fun l hl => hprop l hl)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hVo _ hl0V
  have hVmem : ∀ t s : ℝ, |t| < ε → |s| ≤ |t| → (t, s) ∈ V := by
    intro t s ht hs
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq]
    simp only [Real.dist_eq, sub_zero]
    exact max_lt ht (lt_of_le_of_lt hs ht)
  have hEnn : ∀ u ∈ Icc 0 L, 0 ≤ E u := by
    intro u hu
    rcases hu.1.eq_or_lt with h | h
    · rw [← h, hE0]
    rcases hu.2.eq_or_lt with h' | h'
    · rw [h', hEL]
    exact (hEpos u ⟨h, h'⟩).le
  -- continuity of the integrand of `S` in `u`
  have hSint : ∀ t : ℝ, IntervalIntegrable (fun u => Real.arccos ((X + t * ρ u t - B u) / (2 * Real.sqrt (E u))))
      volume 0 L := by
    intro t
    refine intervalIntegrable_arccos_aux hL.le ?_
    have hsub : Ioo 0 L ⊆ Icc 0 L := Ioo_subset_Icc_self
    have hρt : ContinuousOn (fun u => ρ u t) (Icc 0 L) := cont_slice hρc t
    refine ((continuousOn_const.add (continuousOn_const.mul (hρt.mono hsub))).sub (hBcont.mono hsub)).div
      (continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn (hEcont.mono hsub))) (fun u hu => ?_)
    have := Real.sqrt_pos.2 (hEpos u hu)
    positivity
  -- the key identity
  have hkey : ∀ t : ℝ, |t| < ε →
      (∫ u in (0 : ℝ)..L, Real.arccos ((X + t * ρ u t - B u) / (2 * Real.sqrt (E u)))) -
        (∫ u in (0 : ℝ)..L, Real.arccos ((X + 0 * ρ u 0 - B u) / (2 * Real.sqrt (E u)))) =
      -∫ s in (0 : ℝ)..t, ∫ u in (0 : ℝ)..L, ρ u t / Real.sqrt (f u (t, s)) := by
    intro t ht
    have hseg : ∀ s ∈ uIcc (0 : ℝ) t, |s| ≤ |t| := by
      intro s hs
      rcases le_total 0 t with h | h
      · rw [uIcc_of_le h] at hs
        rw [abs_of_nonneg h, abs_of_nonneg hs.1]; exact hs.2
      · rw [uIcc_of_ge h] at hs
        rw [abs_of_nonpos h, abs_of_nonpos hs.2]; linarith [hs.1]
    set Φ : ℝ → ℝ → ℝ := fun u s => ρ u t / Real.sqrt (f u (t, s)) with hΦ
    have hint : ∀ s ∈ Ι (0 : ℝ) t, IntervalIntegrable (fun u => Φ u s) volume 0 L := by
      intro s hs
      exact (hΨ1 (t, s) (hVmem t s ht (hseg s (Set.uIoc_subset_uIcc hs)))).1
    have hnorm : IntervalIntegrable (fun s => ∫ u in (0 : ℝ)..L, ‖Φ u s‖) volume 0 t := by
      have hcon : ContinuousOn (fun s => ∫ u in (0 : ℝ)..L, ‖Φ u s‖) (uIcc 0 t) := by
        intro s hs
        have hc := (hΨ2 (t, s) (hVmem t s ht (hseg s hs))).2
        have hc' : ContinuousAt (fun s' : ℝ => ∫ u in (0 : ℝ)..L, |ρ u t| / Real.sqrt (f u (t, s'))) s :=
          ContinuousAt.comp (f := fun s' : ℝ => (t, s')) (g := fun l : ℝ × ℝ => ∫ u in (0 : ℝ)..L, |ρ u l.1| / Real.sqrt (f u l))
            hc (by fun_prop)
        have e : (fun s' : ℝ => ∫ u in (0 : ℝ)..L, ‖Φ u s'‖) =
            (fun s' : ℝ => ∫ u in (0 : ℝ)..L, |ρ u t| / Real.sqrt (f u (t, s'))) := by
          funext s'
          refine intervalIntegral.integral_congr (fun u _ => ?_)
          simp only [hΦ, norm_div, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        rw [e]
        exact hc'.continuousWithinAt
      exact hcon.intervalIntegrable
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => Φ p.1 p.2)
        ((volume.restrict (Ι (0 : ℝ) L)).prod (volume.restrict (Ι (0 : ℝ) t))) := by
      have hN : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 t) (Icc 0 L ×ˢ univ) :=
        (cont_slice hρc t).comp continuous_fst.continuousOn (fun p hp => hp.1)
      have hD : ContinuousOn (fun p : ℝ × ℝ => f p.1 (t, p.2)) (Icc 0 L ×ˢ univ) :=
        hfc.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
          (fun p hp => ⟨hp.1, mem_univ _⟩)
      have hset : Ι (0 : ℝ) L ×ˢ Ι (0 : ℝ) t ⊆ Icc 0 L ×ˢ (univ : Set ℝ) := by
        intro p hp
        have := hp.1
        rw [Set.uIoc_of_le hL.le] at this
        exact ⟨⟨this.1.le, this.2⟩, mem_univ _⟩
      have hm : MeasurableSet (Ι (0 : ℝ) L ×ˢ Ι (0 : ℝ) t) := measurableSet_uIoc.prod measurableSet_uIoc
      rw [Measure.prod_restrict]
      refine AEMeasurable.aestronglyMeasurable ?_
      exact (((hN.mono hset).aemeasurable (μ := volume.prod volume) hm)).div
        (Real.continuous_sqrt.measurable.comp_aemeasurable ((hD.mono hset).aemeasurable (μ := volume.prod volume) hm))
    have hpt : ∀ u ∈ Icc 0 L,
        Real.arccos ((X + t * ρ u t - B u) / (2 * Real.sqrt (E u))) -
          Real.arccos ((X + 0 * ρ u 0 - B u) / (2 * Real.sqrt (E u))) =
        -∫ s in (0 : ℝ)..t, Φ u s := by
      intro u hu
      have := pt_formula (E := E u) (β := B u) (X := X) (r := ρ u t) (t := t) (hEnn u hu)
      rw [show X + 0 * ρ u 0 - B u = X - B u by ring, this]
      simp only [hΦ, hf, div_eq_mul_inv]
    rw [← intervalIntegral.integral_sub (hSint t) (hSint 0)]
    rw [intervalIntegral.integral_congr (fun u hu => hpt u (by rwa [uIcc_of_le hL.le] at hu)),
      intervalIntegral.integral_neg]
    congr 1
    exact interval_swap hL.le hmeas hint hnorm
  -- the limit
  set Ψ : ℝ × ℝ → ℝ := fun l => ∫ u in (0 : ℝ)..L, ρ u l.1 / Real.sqrt (f u l) with hΨ
  have hΨc : ContinuousAt Ψ (0, 0) := (hΨ1 (0, 0) hl0V).2
  have hΨ00 : Ψ (0, 0) = ∫ u in (0 : ℝ)..L, ρ u 0 / Real.sqrt (4 * E u - (X - B u) ^ 2) := by
    simp [hΨ, hf]
  rw [← hΨ00]
  refine hasDerivAt_iff_tendsto_slope_zero.2 ?_
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε' hε'
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hΨc (ε' / 2) (by linarith)
  refine ⟨min δ ε, lt_min hδ hε, ?_⟩
  intro t ht0 htd
  have ht0' : t ≠ 0 := ht0
  have htd' : |t| < min δ ε := by simpa [Real.dist_eq] using htd
  have htδ : |t| < δ := lt_of_lt_of_le htd' (min_le_left _ _)
  have htε : |t| < ε := lt_of_lt_of_le htd' (min_le_right _ _)
  have hseg : ∀ s ∈ uIcc (0 : ℝ) t, |s| ≤ |t| := by
    intro s hs
    rcases le_total 0 t with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg h, abs_of_nonneg hs.1]; exact hs.2
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos h, abs_of_nonpos hs.2]; linarith [hs.1]
  have hΨint : IntervalIntegrable (fun s => Ψ (t, s)) volume 0 t := by
    have : ContinuousOn (fun s => Ψ (t, s)) (uIcc 0 t) := by
      intro s hs
      have hc := (hΨ1 (t, s) (hVmem t s htε (hseg s hs))).2
      exact (ContinuousAt.comp (f := fun s' : ℝ => (t, s')) (g := Ψ) hc (by fun_prop)).continuousWithinAt
    exact this.intervalIntegrable
  have hk := hkey t htε
  simp only [zero_add]
  have hI : ∫ s in (0 : ℝ)..t, Ψ (t, s) - Ψ (0, 0) = (∫ s in (0 : ℝ)..t, Ψ (t, s)) - t * Ψ (0, 0) := by
    rw [intervalIntegral.integral_sub hΨint intervalIntegrable_const]
    simp
  have hbd : ‖∫ s in (0 : ℝ)..t, (Ψ (t, s) - Ψ (0, 0))‖ ≤ ε' / 2 * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => ?_)
    have hs' : |s| ≤ |t| := hseg s (Set.uIoc_subset_uIcc hs)
    have := hδ' (x := (t, s)) (by
      rw [Prod.dist_eq]
      simp only [Real.dist_eq, sub_zero]
      exact max_lt htδ (lt_of_le_of_lt hs' htδ))
    rw [Real.norm_eq_abs]
    rw [Real.dist_eq] at this
    exact this.le
  have hS : (∫ u in (0 : ℝ)..L, Real.arccos ((X + t * ρ u t - B u) / (2 * Real.sqrt (E u)))) -
      (∫ u in (0 : ℝ)..L, Real.arccos ((X + 0 * ρ u 0 - B u) / (2 * Real.sqrt (E u)))) =
      -∫ s in (0 : ℝ)..t, Ψ (t, s) := hk
  rw [Real.dist_eq]
  show |t⁻¹ * ((∫ u in (0 : ℝ)..L, Real.arccos ((X + t * ρ u t - B u) / (2 * Real.sqrt (E u)))) -
      (∫ u in (0 : ℝ)..L, Real.arccos ((X + 0 * ρ u 0 - B u) / (2 * Real.sqrt (E u))))) - -Ψ (0, 0)| < ε'
  rw [hS]
  have e : t⁻¹ * -(∫ s in (0 : ℝ)..t, Ψ (t, s)) - -Ψ (0, 0) =
      -(t⁻¹ * ∫ s in (0 : ℝ)..t, (Ψ (t, s) - Ψ (0, 0))) := by
    rw [hI]
    field_simp
    ring
  rw [e, abs_neg, abs_mul, abs_inv]
  have hb2 : |∫ s in (0 : ℝ)..t, (Ψ (t, s) - Ψ (0, 0))| ≤ ε' / 2 * |t| := by
    simpa [Real.norm_eq_abs] using hbd
  have htpos : 0 < |t| := abs_pos.2 ht0'
  calc |t|⁻¹ * |∫ s in (0 : ℝ)..t, (Ψ (t, s) - Ψ (0, 0))| ≤ |t|⁻¹ * (ε' / 2 * |t|) :=
        mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = ε' / 2 := by field_simp
    _ < ε' := by linarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.arccos_sub_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.arccos_sub_eq

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.pt_formula' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.pt_formula

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.interval_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.interval_swap

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.hasDerivAt_shiftAction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv.hasDerivAt_shiftAction

end FormalResearch.JacobiEigenvectors.TheoremA.ActionDeriv

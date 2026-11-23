module

public import FormalResearch.ModularBootstrap.Upper.Membership.Vacuum
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Decay `|ψ| ≤ C e^{-c' L(x) - πx}` implies the integrability used for membership and vacuum

With `t = c' x² / 3`, `x = (3t/c')^{1/2}` and `L(x) = 2πx/3` (`comb_estimates.tex`, Setup):

* `radialLift_integrable_of_decay`: a continuous profile with this decay has an integrable radial lift on
  `ℝ^{2w}` (`∫₀^∞ |ψ| t^{w-1} dt < ∞`; `fw:FWM` item 1, `cmb:K7` "Membership");
* `kernelIntegrable_of_decay`: `∫₀^∞ |ψ| K_{c'/12}^{(w)} dt < ∞`, via `K_{c'/12}^{(w)}(t) ≤ (2x)^{w-1} e^{c' L(x)}`
  (`n1:L4`(a), `kernelK_le_pow_mul_exp`), so that `|ψ| K ≤ C (2x)^{w-1} e^{-πx}`
  (`cmb:K7`: "`K_a(t) = I_0(c' L(x)) ≤ e^{c' L(x)}` ... `∫ |g| V dt ≤ C(c) ∫ e^{-πx} dt < ∞`").

All proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Membership

open FormalResearch.ModularBootstrap.Crossing FormalResearch.ModularBootstrap.WeightAxioms

/-- The physical variable `x = (3t/c')^{1/2}` (`t = c' x² / 3`). -/
noncomputable def xOf (c' t : ℝ) : ℝ := Real.sqrt (3 * t / c')

/-- The envelope `C e^{-c' L(x) - πx}`, `L(x) = 2πx/3`, as a function of `t`. -/
noncomputable def decayEnv (c' C t : ℝ) : ℝ :=
  C * Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t)

/-- `|ψ(t)| ≤ C e^{-c' L(x) - πx}` for all `t ≥ 0` (`t = c' x² / 3`). -/
def DecayBound (c' C : ℝ) (ψ : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → |ψ t| ≤ decayEnv c' C t

lemma xOf_comp {c' x : ℝ} (hc' : 0 < c') (hx : 0 ≤ x) : xOf c' (c' * x ^ 2 / 3) = x := by
  unfold xOf
  rw [show 3 * (c' * x ^ 2 / 3) / c' = x ^ 2 by field_simp]
  exact Real.sqrt_sq hx

lemma xOf_nonneg (c' t : ℝ) : 0 ≤ xOf c' t := Real.sqrt_nonneg _

lemma sq_xOf {c' t : ℝ} (hc' : 0 < c') (ht : 0 ≤ t) : xOf c' t ^ 2 = 3 * t / c' := by
  unfold xOf; exact Real.sq_sqrt (by positivity)

lemma continuousOn_xOf (c' : ℝ) : Continuous (xOf c') := by
  unfold xOf; fun_prop

/-- `∫₀^∞ x^k e^{-βx} dt < ∞` in the variable `t = c' x² / 3`. -/
lemma integrableOn_xpow_exp {c' β : ℝ} (hc' : 0 < c') (hβ : 0 < β) (k : ℕ) :
    IntegrableOn (fun t : ℝ => xOf c' t ^ k * Real.exp (-β * xOf c' t)) (Ioi 0) := by
  let φ : ℝ → ℝ := fun x => c' * x ^ 2 / 3
  have himg : φ '' Ioi 0 = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact div_pos (mul_pos hc' (pow_pos hx 2)) (by norm_num)
    · intro hy
      refine ⟨Real.sqrt (3 * y / c'), Real.sqrt_pos.mpr (by have := mem_Ioi.mp hy; positivity), ?_⟩
      show c' * Real.sqrt (3 * y / c') ^ 2 / 3 = y
      rw [Real.sq_sqrt (by have := mem_Ioi.mp hy; positivity)]
      field_simp
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivWithinAt φ (2 * c' * x / 3) (Ioi 0) x := by
    intro x _
    have := ((hasDerivAt_pow 2 x).const_mul c').div_const 3
    exact (this.congr_deriv (by simp only [Nat.cast_ofNat]; ring)).hasDerivWithinAt
  have hinj : InjOn φ (Ioi 0) := by
    intro x hx y hy hxy
    have hx0 : 0 < x := hx
    have hy0 : 0 < y := hy
    have h1 : x ^ 2 = y ^ 2 := by
      have : c' * x ^ 2 = c' * y ^ 2 := by simp only [φ] at hxy; linarith
      exact mul_left_cancel₀ hc'.ne' this
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
  have hcomp := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (g := fun t : ℝ => xOf c' t ^ k * Real.exp (-β * xOf c' t))
  rw [himg] at hcomp
  refine hcomp.mpr ?_
  have hint : IntegrableOn (fun x : ℝ => x ^ ((k : ℝ) + 1) * Real.exp (-β * x ^ (1 : ℝ))) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      one_pos hβ
  refine IntegrableOn.congr_fun (hint.const_mul (2 * c' / 3)) (fun x hx => ?_) measurableSet_Ioi
  have hx0 : 0 < x := hx
  simp only [φ, smul_eq_mul, Real.rpow_one]
  rw [xOf_comp hc' hx0.le, abs_of_pos (by positivity), Real.rpow_add hx0, Real.rpow_natCast,
    Real.rpow_one]
  ring

lemma xpow_exp_le {c' β : ℝ} {k : ℕ} {t : ℝ} :
    0 ≤ xOf c' t ^ k * Real.exp (-β * xOf c' t) := by
  have := xOf_nonneg c' t
  positivity

/-- A continuous profile with decay has an integrable radial lift on `ℝ^{2w}`. -/
theorem radialLift_integrable_of_decay {w : ℕ} (hw : 1 ≤ w) {c' C : ℝ} (hc' : 0 < c')
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Ici 0)) (hd : DecayBound c' C ψ) :
    Integrable (radialLift w ψ) := by
  rw [integrable_radialLift_iff hw]
  set β : ℝ := c' * (2 * π / 3) + π with hβ
  have hβpos : 0 < β := by rw [hβ]; positivity
  have hdom := (integrableOn_xpow_exp hc' hβpos (2 * (w - 1))).const_mul
    (|C| * (c' / 3) ^ (w - 1))
  refine hdom.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact (((continuous_id.pow (w - 1)).continuousOn).mul (hψ.mono Ioi_subset_Ici_self)
      ).aestronglyMeasurable measurableSet_Ioi
  · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hx2 : xOf c' t ^ 2 = 3 * t / c' := sq_xOf hc' ht0
    have htx : t = c' * xOf c' t ^ 2 / 3 := by rw [hx2]; field_simp
    have hexp : Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t) =
        Real.exp (-β * xOf c' t) := by congr 1; rw [hβ]; ring
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ht0 _)]
    have hψb := hd t ht0
    unfold decayEnv at hψb
    rw [hexp] at hψb
    have hpow : t ^ (w - 1) = (c' / 3) ^ (w - 1) * xOf c' t ^ (2 * (w - 1)) := by
      conv_lhs => rw [htx]
      rw [show c' * xOf c' t ^ 2 / 3 = c' / 3 * xOf c' t ^ 2 by ring, mul_pow, ← pow_mul]
    calc t ^ (w - 1) * |ψ t| ≤ t ^ (w - 1) * (C * Real.exp (-β * xOf c' t)) :=
          mul_le_mul_of_nonneg_left hψb (pow_nonneg ht0 _)
      _ ≤ t ^ (w - 1) * (|C| * Real.exp (-β * xOf c' t)) := by
          gcongr; exact le_abs_self C
      _ = |C| * (c' / 3) ^ (w - 1) * (xOf c' t ^ (2 * (w - 1)) * Real.exp (-β * xOf c' t)) := by
          rw [hpow]; ring

/-- Decay implies `∫₀^∞ |ψ| K_{c'/12}^{(w)} dt < ∞`. -/
theorem kernelIntegrable_of_decay {w : ℕ} (hw : 1 ≤ w) {c' C : ℝ} (hc' : 0 < c')
    {ψ : ℝ → ℝ} (hψ : ContinuousOn ψ (Ici 0)) (hd : DecayBound c' C ψ) :
    KernelIntegrable w (c' / 12) ψ := by
  have hdom := (integrableOn_xpow_exp hc' (β := π) Real.pi_pos (w - 1)).const_mul
    (|C| * 2 ^ (w - 1))
  refine hdom.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_))
  · exact ((hψ.abs.mono Ioi_subset_Ici_self).mul (continuous_kernelK w (c' / 12)).continuousOn
      ).aestronglyMeasurable measurableSet_Ioi
  · have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
    have hx2 : xOf c' t ^ 2 = 3 * t / c' := sq_xOf hc' ht0
    have hx0 := xOf_nonneg c' t
    have ha : 0 < c' / 12 := by positivity
    have hK := kernelK_le_pow_mul_exp hw ha ht0
    have h1 : Real.sqrt (t / (c' / 12)) = 2 * xOf c' t := by
      rw [show t / (c' / 12) = (2 * xOf c' t) ^ 2 by rw [mul_pow, hx2]; field_simp; ring]
      exact Real.sqrt_sq (by positivity)
    have h2 : 4 * π * Real.sqrt (c' / 12 * t) = c' * (2 * π * xOf c' t / 3) := by
      rw [show c' / 12 * t = (c' * xOf c' t / 6) ^ 2 by
        rw [show (c' * xOf c' t / 6) ^ 2 = c' ^ 2 * xOf c' t ^ 2 / 36 by ring, hx2]
        field_simp; ring]
      rw [Real.sqrt_sq (by positivity)]; ring
    rw [h1, h2] at hK
    have hψb := hd t ht0
    unfold decayEnv at hψb
    have hKnn := kernelK_nonneg (w := w) ha.le ht0
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hKnn)]
    calc |ψ t| * kernelK w (c' / 12) t
        ≤ (C * Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t)) *
            ((2 * xOf c' t) ^ (w - 1) * Real.exp (c' * (2 * π * xOf c' t / 3))) :=
          mul_le_mul hψb hK hKnn (le_trans (abs_nonneg _) hψb)
      _ ≤ (|C| * Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t)) *
            ((2 * xOf c' t) ^ (w - 1) * Real.exp (c' * (2 * π * xOf c' t / 3))) := by
          gcongr; exact le_abs_self C
      _ = |C| * 2 ^ (w - 1) * (xOf c' t ^ (w - 1) * Real.exp (-π * xOf c' t)) := by
          rw [mul_pow]
          have : Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t) *
              Real.exp (c' * (2 * π * xOf c' t / 3)) = Real.exp (-π * xOf c' t) := by
            rw [← Real.exp_add]; congr 1; ring
          calc |C| * Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t) *
                (2 ^ (w - 1) * xOf c' t ^ (w - 1) * Real.exp (c' * (2 * π * xOf c' t / 3)))
              = |C| * 2 ^ (w - 1) * xOf c' t ^ (w - 1) *
                (Real.exp (-(c' * (2 * π * xOf c' t / 3)) - π * xOf c' t) *
                  Real.exp (c' * (2 * π * xOf c' t / 3))) := by ring
            _ = _ := by rw [this]; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.kernelIntegrable_of_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kernelIntegrable_of_decay

/-- info: 'FormalResearch.ModularBootstrap.Upper.Membership.radialLift_integrable_of_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radialLift_integrable_of_decay

end FormalResearch.ModularBootstrap.Upper.Membership

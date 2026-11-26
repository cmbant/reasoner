module

public import Mathlib
public import FormalResearch.CohnElkies.AirySeedSymbols
public import FormalResearch.CohnElkies.ParametricIterated
public import FormalResearch.SignUncertainty.ConvSourceDefs

/-!
# Laplace transform of a weight and the product formula for convolution sources (M6)

For a weight `w` integrable on `(0, ∞)` and a seed `X` (`HasU2 X`, `X` continuous), the right convolution
`convR w X (u) = ∫₀^∞ w(y) X(u + y) dy` has twisted transform `lapW w z · X̃(z)` (Lemma `O.12(3)`, `ceo:conv`):
`airyTwistedLaplaceC_convR`.  Consequently `HasU2 (convR w X)` (`hasU2_convR`): `convR w X` is again a `U.2` seed
(integrability, holomorphy on `Re y > 0`, the bound `C ‖1 + w‖^{-5/2}` on `Re w ≥ 0`).

* `lapW w z = ∫₀^∞ w(y) e^{-z y} dy`, `lapW_norm_le` (`|lapW w z| ≤ ‖w‖₁`, `Re z ≥ 0`),
  `lapW_differentiableOn` (holomorphic on `Re z > 0`);
* `convR_twisted` (Fubini for `Re z ≥ 0`), `airyTwistedLaplaceC_convR`, `hasU2_convR`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

/-- The Laplace transform `∫₀^∞ w(y) e^{-z y} dy` of a weight on `(0, ∞)`. -/
noncomputable def lapW (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y in Ioi (0 : ℝ), (w y : ℂ) * Complex.exp (-(z * (y : ℂ)))

/-- The right convolution `∫₀^∞ w(y) X(u + y) dy`. -/
noncomputable def convR (w X : ℝ → ℝ) (u : ℝ) : ℝ := ∫ y in Ioi (0 : ℝ), w y * X (u + y)

/-- The convolution source of `ceo:conv` is the right convolution of `g₁` with the weight `w_c`. -/
lemma convSource_eq_convR (p γ θ ε h : ℝ) :
    convSource p γ θ ε h = convR (convWc p γ θ ε h) (ceG1 (airyZero 1)) := rfl

lemma norm_exp_neg_mul_le {z : ℂ} (hz : 0 ≤ z.re) {y : ℝ} (hy : 0 ≤ y) :
    ‖Complex.exp (-(z * (y : ℂ)))‖ ≤ 1 := by
  rw [Complex.norm_exp]
  have : (-(z * (y : ℂ))).re = -(z.re * y) := by simp [Complex.mul_re]
  rw [this]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

lemma integrableOn_ofReal_weight {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) :
    IntegrableOn (fun y : ℝ => (w y : ℂ)) (Ioi 0) := Complex.ofRealCLM.integrable_comp hw

lemma integrableOn_lapW {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) {z : ℂ} (hz : 0 ≤ z.re) :
    IntegrableOn (fun y : ℝ => (w y : ℂ) * Complex.exp (-(z * (y : ℂ)))) (Ioi 0) := by
  refine hw.norm.mono' ((integrableOn_ofReal_weight hw).1.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  rw [norm_mul, Complex.norm_real]
  calc ‖w y‖ * ‖Complex.exp (-(z * (y : ℂ)))‖ ≤ ‖w y‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le hz (le_of_lt hy)) (norm_nonneg _)
    _ = ‖w y‖ := mul_one _

/-- `|lapW w z| ≤ ‖w‖₁` for `Re z ≥ 0`. -/
lemma lapW_norm_le {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖lapW w z‖ ≤ ∫ y in Ioi (0 : ℝ), ‖w y‖ := by
  unfold lapW
  refine norm_integral_le_of_norm_le hw.norm ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun y hy => ?_))
  rw [norm_mul, Complex.norm_real]
  calc ‖w y‖ * ‖Complex.exp (-(z * (y : ℂ)))‖ ≤ ‖w y‖ * 1 :=
        mul_le_mul_of_nonneg_left (norm_exp_neg_mul_le hz (le_of_lt hy)) (norm_nonneg _)
    _ = ‖w y‖ := mul_one _

lemma hasDerivAt_lapW {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasDerivAt (lapW w) (∫ y in Ioi (0 : ℝ), (w y : ℂ) * (-(y : ℂ)) * Complex.exp (-(z₀ * (y : ℂ)))) z₀ := by
  set δ : ℝ := z₀.re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hs : {z : ℂ | δ < z.re} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp only [mem_ofPred_eq, hδ]; linarith)
  have hwc := integrableOn_ofReal_weight hw
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun y : ℝ => (w y : ℂ) * Complex.exp (-(z * (y : ℂ))))
      (volume.restrict (Ioi (0 : ℝ))) := fun z =>
    hwc.1.mul (Continuous.aestronglyMeasurable (by fun_prop))
  refine (hasDerivAt_integral_Ioi (F := fun z y => (w y : ℂ) * Complex.exp (-(z * (y : ℂ))))
    (F' := fun z y => (w y : ℂ) * (-(y : ℂ)) * Complex.exp (-(z * (y : ℂ)))) hs (bound := fun y => ‖w y‖ / δ)
    (Eventually.of_forall hmeasF) (integrableOn_lapW hw hz₀.le) ?_ ?_ (hw.norm.div_const δ) ?_).2
  · have hneg : Continuous (fun y : ℝ => -(y : ℂ)) := by fun_prop
    have hex : Continuous (fun y : ℝ => Complex.exp (-(z₀ * (y : ℂ)))) := by fun_prop
    exact (hwc.1.mul hneg.aestronglyMeasurable).mul hex.aestronglyMeasurable
  · intro t ht z hz
    have hz' : δ < z.re := hz
    have ht0 : 0 < t := ht
    rw [norm_mul, norm_mul, Complex.norm_real, norm_neg, Complex.norm_real, Complex.norm_exp]
    have : (-(z * (t : ℂ))).re = -(z.re * t) := by simp [Complex.mul_re]
    rw [this]
    simp only [Real.norm_eq_abs, abs_of_pos ht0]
    have h1 : Real.exp (-(z.re * t)) ≤ Real.exp (-(δ * t)) := Real.exp_le_exp.mpr (by nlinarith)
    have h2 : t * Real.exp (-(δ * t)) ≤ 1 / δ := by
      have h3 : δ * t ≤ Real.exp (δ * t) := by linarith [Real.add_one_le_exp (δ * t)]
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) hδ0]
      nlinarith
    calc |w t| * t * Real.exp (-(z.re * t)) ≤ |w t| * t * Real.exp (-(δ * t)) := by gcongr
      _ = |w t| * (t * Real.exp (-(δ * t))) := by ring
      _ ≤ |w t| * (1 / δ) := by gcongr
      _ = |w t| / δ := by ring
  · intro t ht z hz
    have h1 : HasDerivAt (fun y : ℂ => -(y * (t : ℂ))) (-(1 * (t : ℂ))) z :=
      ((hasDerivAt_id' z).mul_const (t : ℂ)).neg
    have h2 := (h1.cexp).const_mul (w t : ℂ)
    convert h2 using 1
    ring

lemma lapW_differentiableOn {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) :
    DifferentiableOn ℂ (lapW w) {z : ℂ | 0 < z.re} :=
  fun _ hz => (hasDerivAt_lapW hw hz).differentiableAt.differentiableWithinAt

/-- The integrand of the Fubini identity, `F(u, y) = w(y) e^{-z y} · X(u + y) e^{z (u + y)}`. -/
private noncomputable def convF (w X : ℝ → ℝ) (z : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((w p.2 : ℂ) * Complex.exp (-(z * (p.2 : ℂ)))) * ((X (p.1 + p.2) : ℂ) * Complex.exp (z * ((p.1 + p.2 : ℝ) : ℂ)))

private lemma convF_eq (w X : ℝ → ℝ) (z : ℂ) (u y : ℝ) :
    convF w X z (u, y) = ((w y * X (u + y) : ℝ) : ℂ) * Complex.exp (z * (u : ℂ)) := by
  unfold convF
  have : Complex.exp (-(z * (y : ℂ))) * Complex.exp (z * ((u + y : ℝ) : ℂ)) = Complex.exp (z * (u : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  push_cast
  calc (w y : ℂ) * Complex.exp (-(z * (y : ℂ))) * ((X (u + y) : ℂ) * Complex.exp (z * ((u : ℂ) + (y : ℂ))))
      = (w y : ℂ) * (X (u + y) : ℂ) * (Complex.exp (-(z * (y : ℂ))) * Complex.exp (z * ((u : ℂ) + (y : ℂ)))) := by ring
    _ = _ := by
        have h2 : Complex.exp (-(z * (y : ℂ))) * Complex.exp (z * ((u : ℂ) + (y : ℂ))) = Complex.exp (z * (u : ℂ)) := by
          push_cast at this; exact this
        rw [h2]

/-- Fubini for the convolution (`O.12(3)`, before the entire-extension step): for `Re z ≥ 0`, the twisted transform of
`convR w X` is integrable and equals `lapW w z` times that of `X`. -/
theorem convR_twisted {w X : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) (hX : Continuous X) {z : ℂ} (hz : 0 ≤ z.re)
    (hXi : Integrable (fun u : ℝ => (X u : ℂ) * Complex.exp (z * (u : ℂ)))) :
    Integrable (fun u : ℝ => (convR w X u : ℂ) * Complex.exp (z * (u : ℂ))) ∧
      ∫ u : ℝ, (convR w X u : ℂ) * Complex.exp (z * (u : ℂ)) =
        lapW w z * ∫ v : ℝ, (X v : ℂ) * Complex.exp (z * (v : ℂ)) := by
  set ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hν
  have hwc := integrableOn_ofReal_weight hw
  have hmeas : AEStronglyMeasurable (convF w X z) ((volume : Measure ℝ).prod ν) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => (w p.2 : ℂ)) ((volume : Measure ℝ).prod ν) := hwc.1.comp_snd
    have h2 : Continuous (fun p : ℝ × ℝ => Complex.exp (-(z * (p.2 : ℂ)))) := by fun_prop
    have h3 : Continuous (fun p : ℝ × ℝ => (X (p.1 + p.2) : ℂ) * Complex.exp (z * ((p.1 + p.2 : ℝ) : ℂ))) := by
      have := hX.comp (continuous_fst.add continuous_snd)
      fun_prop
    exact (h1.mul h2.aestronglyMeasurable).mul h3.aestronglyMeasurable
  have hslice : ∀ y : ℝ, Integrable (fun u : ℝ => convF w X z (u, y)) volume := fun y => by
    have := (hXi.comp_add_right y).const_mul ((w y : ℂ) * Complex.exp (-(z * (y : ℂ))))
    exact this
  have hnorm : ∀ y : ℝ, ∫ u : ℝ, ‖convF w X z (u, y)‖ =
      ‖(w y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖ * ∫ v : ℝ, ‖(X v : ℂ) * Complex.exp (z * (v : ℂ))‖ := fun y => by
    have : ∀ u : ℝ, ‖convF w X z (u, y)‖ = ‖(w y : ℂ) * Complex.exp (-(z * (y : ℂ)))‖ *
        ‖(X (u + y) : ℂ) * Complex.exp (z * ((u + y : ℝ) : ℂ))‖ := fun u => by
      unfold convF; simp only [norm_mul]
    simp_rw [this]
    rw [integral_const_mul]
    congr 1
    exact integral_add_right_eq_self (fun v : ℝ => ‖(X v : ℂ) * Complex.exp (z * (v : ℂ))‖) y
  have hF : Integrable (convF w X z) ((volume : Measure ℝ).prod ν) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall hslice, ?_⟩
    simp_rw [hnorm]
    exact (integrableOn_lapW hw hz).norm.mul_const _
  have hinner : ∀ u : ℝ, ∫ y, convF w X z (u, y) ∂ν = (convR w X u : ℂ) * Complex.exp (z * (u : ℂ)) := fun u => by
    simp_rw [convF_eq]
    rw [integral_mul_const]
    congr 1
    unfold convR
    exact integral_complex_ofReal (μ := ν) (f := fun y => w y * X (u + y))
  have hint : Integrable (fun u : ℝ => (convR w X u : ℂ) * Complex.exp (z * (u : ℂ))) := by
    have := hF.integral_prod_left
    exact this.congr (Eventually.of_forall hinner)
  refine ⟨hint, ?_⟩
  have h1 := integral_prod (convF w X z) hF
  have h2 := integral_prod_symm (convF w X z) hF
  rw [h1] at h2
  simp_rw [hinner] at h2
  rw [h2]
  have hy : ∀ y : ℝ, ∫ u : ℝ, convF w X z (u, y) = ((w y : ℂ) * Complex.exp (-(z * (y : ℂ)))) *
      ∫ v : ℝ, (X v : ℂ) * Complex.exp (z * (v : ℂ)) := fun y => by
    unfold convF
    dsimp only
    rw [integral_const_mul]
    congr 1
    exact integral_add_right_eq_self (fun v : ℝ => (X v : ℂ) * Complex.exp (z * (v : ℂ))) y
  simp_rw [hy]
  rw [integral_mul_const]
  rfl

/-- The product formula `S̃(z) = lapW w z · X̃(z)` for the twisted transform (`O.12(3)`), `Re z ≥ 0`. -/
theorem airyTwistedLaplaceC_convR {w X : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) (hX : Continuous X) (hU : HasU2 X)
    {z : ℂ} (hz : 0 ≤ z.re) :
    airyTwistedLaplaceC (convR w X) z = lapW w z * airyTwistedLaplaceC X z := by
  unfold airyTwistedLaplaceC
  rw [(convR_twisted hw hX hz (hU.integrable z hz)).2]
  ring

/-- `HasU2` is preserved by convolution with a weight integrable on `(0, ∞)`. -/
theorem hasU2_convR {w X : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) (hX : Continuous X) (hU : HasU2 X) :
    HasU2 (convR w X) where
  integrable y hy := (convR_twisted hw hX hy (hU.integrable y hy)).1
  differentiable := ((lapW_differentiableOn hw).mul hU.differentiable).congr fun y hy =>
    airyTwistedLaplaceC_convR hw hX hU (le_of_lt hy)
  rhp := by
    obtain ⟨C, hC, hb⟩ := hU.rhp
    refine ⟨(∫ y in Ioi (0 : ℝ), ‖w y‖) * C + 1, by positivity, fun v hv => ?_⟩
    have hre : 0 ≤ ((ceCs : ℂ) * v).re := by simp [Complex.mul_re, mul_nonneg ceCs_pos.le hv]
    rw [airyTwistedLaplaceC_convR hw hX hU hre, norm_mul]
    have hp : 0 ≤ ‖1 + v‖ ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h1 := lapW_norm_le hw hre
    have h2 := hb v hv
    have hI : 0 ≤ ∫ y in Ioi (0 : ℝ), ‖w y‖ := integral_nonneg fun _ => norm_nonneg _
    calc ‖lapW w ((ceCs : ℂ) * v)‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * v)‖
        ≤ (∫ y in Ioi (0 : ℝ), ‖w y‖) * (C * ‖1 + v‖ ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul h1 h2 (norm_nonneg _) hI
      _ ≤ ((∫ y in Ioi (0 : ℝ), ‖w y‖) * C + 1) * ‖1 + v‖ ^ (-(5 / 2 : ℝ)) := by nlinarith


/-- info: 'FormalResearch.SignUncertainty.norm_exp_neg_mul_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms norm_exp_neg_mul_le

/-- info: 'FormalResearch.SignUncertainty.integrableOn_ofReal_weight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_ofReal_weight

/-- info: 'FormalResearch.SignUncertainty.integrableOn_lapW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integrableOn_lapW

/-- info: 'FormalResearch.SignUncertainty.hasDerivAt_lapW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasDerivAt_lapW

/-- info: 'FormalResearch.SignUncertainty.convSource_eq_convR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convSource_eq_convR

/-- info: 'FormalResearch.SignUncertainty.lapW_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lapW_norm_le

/-- info: 'FormalResearch.SignUncertainty.lapW_differentiableOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lapW_differentiableOn

/-- info: 'FormalResearch.SignUncertainty.convR_twisted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convR_twisted

/-- info: 'FormalResearch.SignUncertainty.airyTwistedLaplaceC_convR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms airyTwistedLaplaceC_convR

/-- info: 'FormalResearch.SignUncertainty.hasU2_convR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasU2_convR

end FormalResearch.SignUncertainty

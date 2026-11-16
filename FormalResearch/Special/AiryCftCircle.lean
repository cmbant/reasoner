module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A circle formula for the logarithmic derivative of an entire function with simple zeros

Generic complex analysis (no Airy function here), used by `AiryCftMittagLeffler` for the Mittag-Leffler
expansion of `Ai'/Ai`.  Setting: `f` entire, `R > 0`, `c : ℕ → ℂ` an injective-on-`s` list of the zeros of `f` in the
closed disc `|w| ≤ R` (all in the open disc, all simple); then, with `F = f'/f` (`logDeriv f`),

* `cftCircle_logDeriv`: for `|z| < R`, `f z ≠ 0`:
  `F(z) - Σ_{i ∈ s} 1/(z - c_i) = (2πi)⁻¹ ∮_{|ζ|=R} F(ζ)/(ζ - z) dζ`;
* `cftCircle_deriv_logDeriv`: `F'(z) + Σ_{i ∈ s} (z - c_i)⁻² = (2πi)⁻¹ ∮_{|ζ|=R} F(ζ)/(ζ - z)² dζ`.

Proof: factor `f = Π_{i ∈ s}(w - c_i) · φ` with `φ` entire and zero-free on `|w| ≤ R` (`cftCircle_factor`, by induction
using `dslope`); `φ'/φ` is holomorphic near the closed disc, equals `F - Σ 1/(w - c_i)` off the zeros, and the
rational part has vanishing Cauchy integral against `1/(ζ - w)` (partial fractions); then Cauchy's integral formula
for `φ'/φ`, and `hasDerivAt_circleIntegral_sub_inv_smul` for the second formula.

Everything here is proved (axiom-checked below); this is a standard textbook residue-type argument, formalised without
the residue theorem (which is not in Mathlib).
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- **Division by simple zeros.** If an entire function vanishes at the points `c i`, `i ∈ s` (`c` injective on `s`),
then it is divisible by `Π_{i ∈ s} (w - c i)` in the ring of entire functions. -/
lemma cftCircle_factor (c : ℕ → ℂ) (s : Finset ℕ) (hinj : Set.InjOn c s) :
    ∀ (H : ℂ → ℂ), Differentiable ℂ H → (∀ i ∈ s, H (c i) = 0) →
      ∃ K : ℂ → ℂ, Differentiable ℂ K ∧ ∀ w, H w = (∏ i ∈ s, (w - c i)) * K w := by
  classical
  induction s using Finset.induction_on with
  | empty => intro H hH _; exact ⟨H, hH, fun w => by simp⟩
  | insert j s hj ih =>
    intro H hH hz
    have hinj' : Set.InjOn c s := hinj.mono (by intro x hx; simp [hx])
    obtain ⟨K, hK, hKe⟩ := ih hinj' H hH (fun i hi => hz i (Finset.mem_insert_of_mem hi))
    have hKj : K (c j) = 0 := by
      have h1 := hz j (Finset.mem_insert_self j s)
      rw [hKe] at h1
      have hne : ∏ i ∈ s, (c j - c i) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi h
        have := hinj (by simp) (by simp [hi]) (sub_eq_zero.mp h)
        exact hj (this ▸ hi)
      exact (mul_eq_zero.mp h1).resolve_left hne
    have hd : Differentiable ℂ (dslope K (c j)) := by
      have := (differentiableOn_dslope (f := K) (c := c j) (s := Set.univ) Filter.univ_mem).mpr
        hK.differentiableOn
      exact differentiableOn_univ.mp this
    refine ⟨dslope K (c j), hd, fun w => ?_⟩
    have h2 := sub_smul_dslope K (c j) w
    rw [hKj, sub_zero, smul_eq_mul] at h2
    rw [Finset.prod_insert hj, hKe w, ← h2]
    ring

/-! ### Rational parts have vanishing Cauchy integrals -/

lemma cftCircle_integrable_inv {R : ℝ} (hR : 0 ≤ R) {w : ℂ} (hw : ‖w‖ < R) :
    CircleIntegrable (fun ζ : ℂ => (ζ - w)⁻¹) 0 R := by
  refine ContinuousOn.circleIntegrable hR ?_
  refine (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => ?_
  have : ‖ζ‖ = R := by simpa using hζ
  intro h
  have : ζ = w := sub_eq_zero.mp h
  subst this; linarith

lemma cftCircle_integral_pair {R : ℝ} (hR : 0 ≤ R) {w c : ℂ} (hw : ‖w‖ < R) (hc : ‖c‖ < R) (hne : w ≠ c) :
    ∮ ζ in C(0, R), (ζ - w)⁻¹ * (ζ - c)⁻¹ = 0 := by
  have hwb : w ∈ ball (0 : ℂ) R := by simpa using hw
  have hcb : c ∈ ball (0 : ℂ) R := by simpa using hc
  have hcw : c - w ≠ 0 := sub_ne_zero.mpr hne.symm
  have e : ∀ ζ ∈ sphere (0 : ℂ) R, (ζ - w)⁻¹ * (ζ - c)⁻¹ = (c - w)⁻¹ * ((ζ - c)⁻¹ - (ζ - w)⁻¹) := by
    intro ζ hζ
    have h1 : ζ - w ≠ 0 := by
      intro h; have : ζ = w := sub_eq_zero.mp h
      have hn : ‖ζ‖ = R := by simpa using hζ
      rw [this] at hn; linarith
    have h2 : ζ - c ≠ 0 := by
      intro h; have : ζ = c := sub_eq_zero.mp h
      have hn : ‖ζ‖ = R := by simpa using hζ
      rw [this] at hn; linarith
    field_simp
    ring
  rw [circleIntegral.integral_congr hR e, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub (cftCircle_integrable_inv hR hc) (cftCircle_integrable_inv hR hw),
    circleIntegral.integral_sub_inv_of_mem_ball hcb, circleIntegral.integral_sub_inv_of_mem_ball hwb]
  simp

lemma cftCircle_integral_sum {R : ℝ} (hR : 0 ≤ R) {w : ℂ} (hw : ‖w‖ < R) (c : ℕ → ℂ) (s : Finset ℕ)
    (hc : ∀ i ∈ s, ‖c i‖ < R) (hne : ∀ i ∈ s, w ≠ c i) :
    CircleIntegrable (fun ζ : ℂ => (ζ - w)⁻¹ * ∑ i ∈ s, (ζ - c i)⁻¹) 0 R ∧
      ∮ ζ in C(0, R), (ζ - w)⁻¹ * ∑ i ∈ s, (ζ - c i)⁻¹ = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [CircleIntegrable, circleIntegral]
  | insert j s hj ih =>
    obtain ⟨h1, h2⟩ := ih (fun i hi => hc i (Finset.mem_insert_of_mem hi))
      (fun i hi => hne i (Finset.mem_insert_of_mem hi))
    have hcj := hc j (Finset.mem_insert_self j s)
    have hnj := hne j (Finset.mem_insert_self j s)
    have hI : CircleIntegrable (fun ζ : ℂ => (ζ - w)⁻¹ * (ζ - c j)⁻¹) 0 R := by
      refine ContinuousOn.circleIntegrable hR ?_
      have hc1 : ∀ x ∈ sphere (0 : ℂ) R, x - w ≠ 0 := by
        intro x hx h; have : x = w := sub_eq_zero.mp h
        have hn : ‖x‖ = R := by simpa using hx
        rw [this] at hn; linarith
      have hc2 : ∀ x ∈ sphere (0 : ℂ) R, x - c j ≠ 0 := by
        intro x hx h; have : x = c j := sub_eq_zero.mp h
        have hn : ‖x‖ = R := by simpa using hx
        rw [this] at hn; linarith
      exact ((continuousOn_id.sub continuousOn_const).inv₀ hc1).mul
        ((continuousOn_id.sub continuousOn_const).inv₀ hc2)
    have e : (fun ζ : ℂ => (ζ - w)⁻¹ * ∑ i ∈ insert j s, (ζ - c i)⁻¹) =
        fun ζ => (ζ - w)⁻¹ * (ζ - c j)⁻¹ + (ζ - w)⁻¹ * ∑ i ∈ s, (ζ - c i)⁻¹ := by
      funext ζ; rw [Finset.sum_insert hj]; ring
    rw [e]
    refine ⟨hI.add h1, ?_⟩
    rw [circleIntegral.integral_add hI h1, h2, cftCircle_integral_pair hR hw hcj hnj, add_zero]

/-! ### The circle formulas -/

section main

variable {f : ℂ → ℂ} {c : ℕ → ℂ} {s : Finset ℕ} {R : ℝ}

/-- Hypotheses: `f` entire; `c` lists (injectively on `s`) exactly the zeros of `f` in `|w| ≤ R`, all in `|w| < R`
and simple. -/
structure CftCircleData (f : ℂ → ℂ) (c : ℕ → ℂ) (s : Finset ℕ) (R : ℝ) : Prop where
  entire : Differentiable ℂ f
  radius_pos : 0 < R
  inj : Set.InjOn c s
  inside : ∀ i ∈ s, ‖c i‖ < R
  zero : ∀ i ∈ s, f (c i) = 0
  simple : ∀ i ∈ s, deriv f (c i) ≠ 0
  complete : ∀ w : ℂ, ‖w‖ ≤ R → f w = 0 → ∃ i ∈ s, c i = w

lemma CftCircleData.ne_zero_sphere (h : CftCircleData f c s R) {ζ : ℂ} (hζ : ‖ζ‖ = R) : f ζ ≠ 0 := by
  intro h0
  obtain ⟨i, hi, hci⟩ := h.complete ζ hζ.le h0
  have := h.inside i hi
  rw [hci, hζ] at this
  exact lt_irrefl _ this

lemma CftCircleData.continuousOn_logDeriv (h : CftCircleData f c s R) :
    ContinuousOn (logDeriv f) (sphere (0 : ℂ) R) := by
  have : logDeriv f = fun w => deriv f w / f w := funext (logDeriv_apply f)
  rw [this]
  refine (h.entire.deriv.continuous.continuousOn).div h.entire.continuous.continuousOn fun ζ hζ => ?_
  exact h.ne_zero_sphere (by simpa using hζ)

/-- The factorisation `f = Π(w - c_i) · φ` with `φ` zero-free on the closed disc. -/
lemma CftCircleData.factor (h : CftCircleData f c s R) :
    ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ (∀ w, f w = (∏ i ∈ s, (w - c i)) * φ w) ∧
      ∀ w : ℂ, ‖w‖ ≤ R → φ w ≠ 0 := by
  classical
  obtain ⟨φ, hφ, hfe⟩ := cftCircle_factor c s h.inj f h.entire h.zero
  refine ⟨φ, hφ, hfe, fun w hw h0 => ?_⟩
  have hf0 : f w = 0 := by rw [hfe, h0, mul_zero]
  obtain ⟨i, hi, hci⟩ := h.complete w hw hf0
  have hφc : φ (c i) = 0 := hci ▸ h0
  -- f = (w - c i) ψ with ψ(c i) = 0, so f'(c i) = 0
  set ψ : ℂ → ℂ := fun w => (∏ j ∈ s.erase i, (w - c j)) * φ w with hψ
  have hfe' : f = fun w => (w - c i) * ψ w := by
    funext w
    rw [hfe, ← Finset.mul_prod_erase s (fun j => w - c j) hi, hψ]; ring
  have hψd : Differentiable ℂ ψ := by
    refine Differentiable.mul ?_ hφ
    fun_prop
  have hψ0 : ψ (c i) = 0 := by simp [hψ, hφc]
  have hder : HasDerivAt f (ψ (c i)) (c i) := by
    rw [hfe']
    have := ((hasDerivAt_id (c i)).sub_const (c i)).fun_mul (hψd (c i)).hasDerivAt
    simpa using this
  exact h.simple i hi (by rw [hder.deriv, hψ0])



/-- `φ'/φ = F - Σ 1/(w - c_i)` off the zeros. -/
lemma cftCircle_logDeriv_split {φ : ℂ → ℂ} (hφ : Differentiable ℂ φ)
    (hfe : ∀ w, f w = (∏ i ∈ s, (w - c i)) * φ w) {w : ℂ} (hfw : f w ≠ 0) :
    deriv φ w / φ w = logDeriv f w - ∑ i ∈ s, 1 / (w - c i) := by
  classical
  have hpw : (∏ i ∈ s, (w - c i)) ≠ 0 := by
    intro h0; apply hfw; rw [hfe, h0, zero_mul]
  have hφw : φ w ≠ 0 := by
    intro h0; apply hfw; rw [hfe, h0, mul_zero]
  have hfeq : f = (fun w => ∏ i ∈ s, (w - c i)) * φ := by
    funext x; simp [hfe x]
  have hfac : ∀ i ∈ s, (fun w : ℂ => w - c i) w ≠ 0 := by
    intro i hi h0
    apply hpw
    exact Finset.prod_eq_zero hi h0
  have hprod : logDeriv (fun w => ∏ i ∈ s, (w - c i)) w = ∑ i ∈ s, 1 / (w - c i) := by
    have h1 := logDeriv_prod (s := s) (f := fun i (w : ℂ) => w - c i) (x := w) hfac
      (fun i _ => by fun_prop)
    have e : (∏ i ∈ s, fun w : ℂ => w - c i) = fun w => ∏ i ∈ s, (w - c i) := by
      funext x; simp [Finset.prod_apply]
    rw [e] at h1
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [logDeriv_apply]
    simp
  have hmul := logDeriv_mul (f := fun w => ∏ i ∈ s, (w - c i)) (g := φ) w hpw hφw (by fun_prop)
    (hφ w)
  rw [hfeq, hmul, hprod, logDeriv_apply φ w]
  ring

/-- The Cauchy integral of `F = f'/f` against `1/(ζ - w)`, off the zeros: `F(w) - Σ 1/(w - c_i)`. -/
lemma CftCircleData.cauchy_eq (h : CftCircleData f c s R) {w : ℂ} (hw : ‖w‖ < R)
    (hne : ∀ i ∈ s, w ≠ c i) :
    (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - w)⁻¹ • logDeriv f ζ =
      logDeriv f w - ∑ i ∈ s, 1 / (w - c i) := by
  obtain ⟨φ, hφ, hfe, hφne⟩ := h.factor
  have hR := h.radius_pos
  have hfw : f w ≠ 0 := by
    intro h0
    obtain ⟨i, hi, hci⟩ := h.complete w hw.le h0
    exact hne i hi hci.symm
  set g : ℂ → ℂ := fun w => deriv φ w / φ w with hg
  have hgd : DifferentiableOn ℂ g (closedBall 0 R) := fun x hx =>
    (((hφ.deriv x).div (hφ x) (hφne x (by simpa using hx))).differentiableWithinAt)
  have hwb : w ∈ ball (0 : ℂ) R := by simpa using hw
  have hC := DifferentiableOn.circleIntegral_sub_inv_smul hgd hwb
  -- on the circle `F = g + S`
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) R, logDeriv f ζ = g ζ + ∑ i ∈ s, (ζ - c i)⁻¹ := by
    intro ζ hζ
    have hn : ‖ζ‖ = R := by simpa using hζ
    have := cftCircle_logDeriv_split hφ hfe (h.ne_zero_sphere hn)
    rw [hg]; simp only [one_div] at this ⊢
    rw [this]; ring
  have hint_g : CircleIntegrable (fun ζ : ℂ => (ζ - w)⁻¹ • g ζ) 0 R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    have h1 : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (sphere (0 : ℂ) R) := by
      refine (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => ?_
      have hn : ‖ζ‖ = R := by simpa using hζ
      intro h0; have : ζ = w := sub_eq_zero.mp h0
      rw [this] at hn; linarith
    exact h1.smul (hgd.continuousOn.mono sphere_subset_closedBall)
  obtain ⟨hint_S, hS⟩ := cftCircle_integral_sum hR.le hw c s h.inside hne
  have e : ∀ ζ ∈ sphere (0 : ℂ) R, (ζ - w)⁻¹ • logDeriv f ζ =
      (ζ - w)⁻¹ • g ζ + (ζ - w)⁻¹ * ∑ i ∈ s, (ζ - c i)⁻¹ := by
    intro ζ hζ; rw [hsph ζ hζ, smul_eq_mul, smul_eq_mul, mul_add]
  rw [circleIntegral.integral_congr hR.le e, circleIntegral.integral_add hint_g hint_S, hS, add_zero, hC,
    smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_smul]
  exact cftCircle_logDeriv_split hφ hfe hfw

/-- **Circle formula for `F = f'/f`**: for `|z| < R`, `f(z) ≠ 0`,
`F(z) - Σ_i 1/(z - c_i) = (2πi)⁻¹ ∮_{|ζ|=R} F(ζ)/(ζ - z) dζ`. -/
theorem cftCircle_logDeriv (h : CftCircleData f c s R) {z : ℂ} (hz : ‖z‖ < R) (hfz : f z ≠ 0) :
    logDeriv f z - ∑ i ∈ s, 1 / (z - c i) =
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - z)⁻¹ • logDeriv f ζ := by
  refine (h.cauchy_eq hz fun i hi hzi => hfz ?_).symm
  rw [hzi]; exact h.zero i hi

/-- **Circle formula for `F'`**: for `|z| < R`, `f(z) ≠ 0`,
`F'(z) + Σ_i (z - c_i)⁻² = (2πi)⁻¹ ∮_{|ζ|=R} F(ζ)/(ζ - z)² dζ`. -/
theorem cftCircle_deriv_logDeriv (h : CftCircleData f c s R) {z : ℂ} (hz : ‖z‖ < R) (hfz : f z ≠ 0) :
    deriv (logDeriv f) z + ∑ i ∈ s, ((z - c i) ^ 2)⁻¹ =
      (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - z) ^ (-2 : ℤ) • logDeriv f ζ := by
  have hR := h.radius_pos
  have hint : CircleIntegrable (logDeriv f) 0 R :=
    ContinuousOn.circleIntegrable hR.le h.continuousOn_logDeriv
  have hzs : z ∉ sphere (0 : ℂ) |R| := by
    rw [abs_of_pos hR]; intro hh
    have : ‖z‖ = R := by simpa using hh
    linarith
  have hT := (hasDerivAt_circleIntegral_sub_inv_smul hint hzs).const_smul ((2 * π * I : ℂ)⁻¹)
  -- the right-hand side function near `z`
  have hF : DifferentiableAt ℂ (logDeriv f) z := by
    have : logDeriv f = fun w => deriv f w / f w := funext (logDeriv_apply f)
    rw [this]
    exact (h.entire.deriv z).div (h.entire z) hfz
  have hS : HasDerivAt (fun w => ∑ i ∈ s, 1 / (w - c i)) (∑ i ∈ s, -((z - c i) ^ 2)⁻¹) z := by
    refine HasDerivAt.fun_sum fun i hi => ?_
    have hne : z - c i ≠ 0 := by
      intro h0; apply hfz
      have : z = c i := sub_eq_zero.mp h0
      rw [this]; exact h.zero i hi
    have := ((hasDerivAt_id z).sub_const (c i)).inv hne
    convert this using 1
    · funext w; simp [one_div]
    · rw [neg_div, one_div]; simp
  have hRHS := hF.hasDerivAt.sub hS
  -- equality of the two functions near `z`
  have hopen : IsOpen {w : ℂ | ‖w‖ < R ∧ f w ≠ 0} :=
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_ne_fun h.entire.continuous continuous_const)
  have hev : (fun w => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - w)⁻¹ • logDeriv f ζ) =ᶠ[𝓝 z]
      fun w => logDeriv f w - ∑ i ∈ s, 1 / (w - c i) := by
    filter_upwards [hopen.mem_nhds (show z ∈ {w : ℂ | ‖w‖ < R ∧ f w ≠ 0} from ⟨hz, hfz⟩)] with w hw
    refine h.cauchy_eq hw.1 fun i hi hwi => hw.2 ?_
    rw [hwi]; exact h.zero i hi
  have := (hT.congr_of_eventuallyEq hev.symm).unique hRHS
  rw [this, Finset.sum_neg_distrib, sub_neg_eq_add]

lemma cftCircle_norm_inv_two_pi_I : ‖(2 * π * I : ℂ)⁻¹‖ = (2 * π)⁻¹ := by
  rw [norm_inv]; congr 1
  simp

/-- On the circle, `‖ζ - z‖ ≥ R - ‖z‖`. -/
lemma cftCircle_norm_sub_ge {R : ℝ} {z ζ : ℂ} (hζ : ‖ζ‖ = R) : R - ‖z‖ ≤ ‖ζ - z‖ := by
  have := norm_sub_norm_le ζ z
  linarith

/-- **First error bound.** If `‖F‖ ≤ B` on `|ζ| = R` and `f(0) ≠ 0`, `f(z) ≠ 0`, `|z| < R`, then
`‖(F(z) - F(0)) - Σ_i (1/(z - c_i) + 1/c_i)‖ ≤ B |z| / (R - |z|)`. -/
theorem cftCircle_error_one (h : CftCircleData f c s R) {z : ℂ} (hz : ‖z‖ < R) (hfz : f z ≠ 0)
    (hf0 : f 0 ≠ 0) {B : ℝ} (hB : ∀ ζ : ℂ, ‖ζ‖ = R → ‖logDeriv f ζ‖ ≤ B) :
    ‖(logDeriv f z - logDeriv f 0) - ∑ i ∈ s, (1 / (z - c i) + 1 / c i)‖ ≤ B * ‖z‖ / (R - ‖z‖) := by
  have hR := h.radius_pos
  have hz0 : ‖(0 : ℂ)‖ < R := by simpa using hR
  have hA := cftCircle_logDeriv h hz hfz
  have hA0 := cftCircle_logDeriv h hz0 hf0
  have hint : ∀ w : ℂ, ‖w‖ < R →
      CircleIntegrable (fun ζ : ℂ => (ζ - w)⁻¹ • logDeriv f ζ) 0 R := fun w hw => by
    refine ContinuousOn.circleIntegrable hR.le ?_
    have h1 : ContinuousOn (fun ζ : ℂ => (ζ - w)⁻¹) (sphere (0 : ℂ) R) := by
      refine (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ => ?_
      have hn : ‖ζ‖ = R := by simpa using hζ
      intro h0; have : ζ = w := sub_eq_zero.mp h0
      rw [this] at hn; linarith
    exact h1.smul h.continuousOn_logDeriv
  have hsum : (logDeriv f z - logDeriv f 0) - ∑ i ∈ s, (1 / (z - c i) + 1 / c i) =
      (logDeriv f z - ∑ i ∈ s, 1 / (z - c i)) - (logDeriv f 0 - ∑ i ∈ s, 1 / ((0 : ℂ) - c i)) := by
    rw [Finset.sum_add_distrib]
    have : ∑ i ∈ s, 1 / ((0 : ℂ) - c i) = -∑ i ∈ s, 1 / c i := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [zero_sub, one_div, one_div, inv_neg]
    rw [this]; ring
  rw [hsum, hA, hA0, ← smul_sub, ← circleIntegral.integral_sub (hint z hz) (hint 0 hz0), norm_smul,
    cftCircle_norm_inv_two_pi_I]
  have hbd := circleIntegral.norm_integral_le_of_norm_le_const (c := (0 : ℂ)) (R := R) hR.le
    (C := B * ‖z‖ / ((R - ‖z‖) * R))
    (f := fun ζ : ℂ => (ζ - z)⁻¹ • logDeriv f ζ - (ζ - 0)⁻¹ • logDeriv f ζ) (fun ζ hζ => by
      have hn : ‖ζ‖ = R := by simpa using hζ
      have hRz : 0 < R - ‖z‖ := by linarith
      have hne : ζ - z ≠ 0 := by
        intro h0; have h2 : ζ = z := sub_eq_zero.mp h0
        rw [h2] at hn; linarith
      have hne0 : ζ ≠ 0 := by
        intro h0; rw [h0] at hn; simp at hn; linarith
      have e : (ζ - z)⁻¹ • logDeriv f ζ - (ζ - 0)⁻¹ • logDeriv f ζ =
          (z * ((ζ - z)⁻¹ * ζ⁻¹)) • logDeriv f ζ := by
        rw [sub_zero, ← sub_smul]
        congr 1
        field_simp
        ring
      rw [e, norm_smul, norm_mul, norm_mul, norm_inv, norm_inv]
      have h1 : ‖ζ - z‖⁻¹ ≤ (R - ‖z‖)⁻¹ :=
        inv_anti₀ hRz (cftCircle_norm_sub_ge hn)
      have h2 : ‖ζ‖⁻¹ = R⁻¹ := by rw [hn]
      rw [h2]
      have h3 := hB ζ hn
      have h4 : 0 ≤ ‖logDeriv f ζ‖ := norm_nonneg _
      calc ‖z‖ * (‖ζ - z‖⁻¹ * R⁻¹) * ‖logDeriv f ζ‖
          ≤ ‖z‖ * ((R - ‖z‖)⁻¹ * R⁻¹) * B := by gcongr
        _ = B * ‖z‖ / ((R - ‖z‖) * R) := by field_simp)
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans (le_of_eq ?_)
  have hRz : R - ‖z‖ ≠ 0 := by linarith
  field_simp

/-- **Second error bound.** If `‖F‖ ≤ B` on `|ζ| = R`, `f(z) ≠ 0`, `|z| < R`, then
`‖F'(z) + Σ_i (z - c_i)⁻²‖ ≤ B R / (R - |z|)²`. -/
theorem cftCircle_error_two (h : CftCircleData f c s R) {z : ℂ} (hz : ‖z‖ < R) (hfz : f z ≠ 0)
    {B : ℝ} (hB : ∀ ζ : ℂ, ‖ζ‖ = R → ‖logDeriv f ζ‖ ≤ B) :
    ‖deriv (logDeriv f) z + ∑ i ∈ s, ((z - c i) ^ 2)⁻¹‖ ≤ B * R / (R - ‖z‖) ^ 2 := by
  have hR := h.radius_pos
  have hRz : 0 < R - ‖z‖ := by linarith
  rw [cftCircle_deriv_logDeriv h hz hfz, norm_smul, cftCircle_norm_inv_two_pi_I]
  have hbd := circleIntegral.norm_integral_le_of_norm_le_const (c := (0 : ℂ)) (R := R) hR.le
    (C := B / (R - ‖z‖) ^ 2)
    (f := fun ζ : ℂ => (ζ - z) ^ (-2 : ℤ) • logDeriv f ζ) (fun ζ hζ => by
      have hn : ‖ζ‖ = R := by simpa using hζ
      rw [norm_smul, norm_zpow]
      have h1 : ‖ζ - z‖ ^ (-2 : ℤ) ≤ ((R - ‖z‖) ^ 2)⁻¹ := by
        rw [zpow_neg, zpow_two, ← sq]
        exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hRz.le (cftCircle_norm_sub_ge hn) 2)
      have h3 := hB ζ hn
      calc ‖ζ - z‖ ^ (-2 : ℤ) * ‖logDeriv f ζ‖ ≤ ((R - ‖z‖) ^ 2)⁻¹ * B := by
            gcongr
        _ = B / (R - ‖z‖) ^ 2 := by ring)
  refine (mul_le_mul_of_nonneg_left hbd (by positivity)).trans (le_of_eq ?_)
  field_simp

end main

/-- info: 'FormalResearch.Special.cftCircle_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cftCircle_logDeriv

/-- info: 'FormalResearch.Special.cftCircle_deriv_logDeriv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cftCircle_deriv_logDeriv

/-- info: 'FormalResearch.Special.cftCircle_error_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cftCircle_error_one

/-- info: 'FormalResearch.Special.cftCircle_error_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.cftCircle_error_two

end FormalResearch.Special

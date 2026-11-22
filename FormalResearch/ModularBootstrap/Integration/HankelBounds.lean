module

public import FormalResearch.ModularBootstrap.Crossing.BesselBridge

/-!
# Lemma B (b) and the integral part of (d): the test-class estimates

Source: `CFT/modular_bootstrap/paper/lower_o1_two_edge.tex`, Lemma B (`vlo:Bessel`), parts (b), (d).
Test class `TestClass virasoroProblem a` (`Crossing/Setup.lean`): continuous `g` on `[0, ∞)` whose radial
lift `x ↦ g(‖x‖²/2)` to `ℝ²` is integrable and Fourier-odd for Mathlib's unitary transform.

## Normalisation

The Lean test class uses `t = ‖x‖²/2` and `𝓕 f ξ = ∫ e^{-2πi⟪x,ξ⟫} f(x) dx`, whereas the paper uses
`t = |x|²/(4π)` and `(2π)^{-1} ∫ e^{-i⟪x,ξ⟫} f(x) dx`.  The variable `t` is the same spectral variable
(`V = K_a - 2K_{a-1} + K_{a-2}` and `K_α(t) = I₀(4π√(α t))` are identical in both) and the constants in
(b) are unchanged: in both normalisations `‖g‖_∞ ≤ 2π ‖g‖_{L¹(dt)}`, the Lean proof being
`|g(t)| = |𝓕 f (x)| ≤ ‖f‖_{L¹(ℝ²)} = 2π ∫₀^∞ |g| dt` (`integral_radialLiftReal`, `w = 1`).  No change of
constant is needed.

* `abs_le_two_pi_integral`: `sup_{t ≥ 0} |g(t)| ≤ 2π ∫₀^∞ |g|` (the `|J₀| ≤ 1` step of (b));
* `lemmaB_b_integral`: `∫₀^∞ |g| ≤ (4/π²) M[g]` (Lemma B (b), first bound);
* `lemmaB_b_sup`: `sup_{t ≥ 0} |g(t)| ≤ (8/π) M[g]` (Lemma B (b), second bound);
* `lemmaB_d_integral`: for `c' ≥ 1000`, `∫₀^∞ |g| K_a dt ≤ 2 e^{92} c'² M[g]` with `a = c'/12`
  (Lemma B (d), first bound, with the explicit constant `C = 2 e^{92}`), and integrability of `|g| K_a`.

Not covered here: the second bound of (d), `sup_{|Im b| ≤ 1/2} |G(b)| ≤ C c'² M[g]` for the Hankel
continuation `G` (see `Integration.StripKernel`).
-/

@[expose] public section

open Real MeasureTheory Set Filter Topology
open scoped FourierTransform

namespace FormalResearch.ModularBootstrap.Integration

open Crossing

variable {a : ℝ} {g : ℝ → ℝ}

/-- A test function is integrable on `(0, ∞)` (from integrability of its radial lift on `ℝ²`). -/
theorem testClass_integrableOn_Ioi (hg : TestClass virasoroProblem a g) :
    IntegrableOn g (Ioi 0) := by
  have := (integrable_radialLift_iff (w := 1) le_rfl g).1 hg.int_lift
  simpa using this

theorem testClass_integrableOn_abs (hg : TestClass virasoroProblem a g) :
    IntegrableOn (fun t => |g t|) (Ioi 0) := (testClass_integrableOn_Ioi hg).norm

/-- **`‖g‖_∞ ≤ 2π ‖g‖₁`** for a Fourier-odd test function (the order-zero Hankel relation
`ĝ = -g` and `|J₀| ≤ 1` of Lemma B (b)): `|g t| ≤ 2π ∫₀^∞ |g|` for every `t ≥ 0`. -/
theorem abs_le_two_pi_integral (hg : TestClass virasoroProblem a g) {t : ℝ} (ht : 0 ≤ t) :
    |g t| ≤ 2 * π * ∫ s in Ioi 0, |g s| := by
  let i0 : Fin (2 * 1) := ⟨0, by norm_num⟩
  let x₀ : EuclideanSpace ℝ (Fin (2 * 1)) := EuclideanSpace.single i0 (√(2 * t))
  have hx₀ : ‖x₀‖ = √(2 * t) := by
    simp [x₀, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hfx : radialLift 1 g x₀ = (g t : ℂ) := by
    simp only [radialLift, hx₀, Real.sq_sqrt (by linarith : 0 ≤ 2 * t)]
    congr 2; ring
  have hodd : 𝓕 (radialLift 1 g) x₀ = -(radialLift 1 g x₀) :=
    congrFun (show 𝓕 (radialLift 1 g) = -(radialLift 1 g) from hg.fourier_odd) x₀
  have h1 := Real.norm_fourier_le_integral_norm (radialLift 1 g) x₀
  rw [hodd, norm_neg, hfx, Complex.norm_real, Real.norm_eq_abs] at h1
  refine h1.trans (le_of_eq ?_)
  have h2 : ∫ v : EuclideanSpace ℝ (Fin (2 * 1)), ‖radialLift 1 g v‖ =
      ∫ v : EuclideanSpace ℝ (Fin (2 * 1)), (fun s => |g s|) (‖v‖ ^ 2 / 2) := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [radialLift]
  have h3 := integral_radialLiftReal (w := 1) le_rfl (fun s => |g s|)
  rw [h2, h3]
  simp

/-- **Lemma B (b), first bound (`vlo:Bessel`)**: `∫₀^∞ |g| dt ≤ (4/π²) M[g]` for `a ≥ 2` and
every `g` in the (Virasoro, `w = 1`) test class.  The paper's `a > 2` is not needed. -/
theorem lemmaB_b_integral (ha : 2 ≤ a) (hg : TestClass virasoroProblem a g) :
    ∫ t in Ioi 0, |g t| ≤ 4 / π ^ 2 * virasoroProblem.cardyNorm a g := by
  set A : ℝ := ∫ t in Ioi 0, |g t| with hA
  set t₀ : ℝ := 1 / (4 * π) with ht₀
  have hpi := Real.pi_pos
  have ht₀pos : 0 < t₀ := by positivity
  have hAint : IntegrableOn (fun t => |g t|) (Ioi 0) := testClass_integrableOn_abs hg
  have hMint : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV a t) (Ioi 0) := hg.int_cardy
  have hsplit : A = (∫ t in Ioc 0 t₀, |g t|) + ∫ t in Ioi t₀, |g t| := by
    rw [hA, ← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hAint.mono_set Ioc_subset_Ioi_self) (hAint.mono_set (Ioi_subset_Ioi ht₀pos.le)),
      Ioc_union_Ioi_eq_Ioi ht₀pos.le]
  -- the head
  have hhead : ∫ t in Ioc 0 t₀, |g t| ≤ A / 2 := by
    have hb : ∀ t ∈ Ioc 0 t₀, ‖|g t|‖ ≤ 2 * π * A := fun t ht => by
      rw [Real.norm_eq_abs, abs_abs]; exact abs_le_two_pi_integral hg ht.1.le
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 t₀)
      (by simp) hb
    rw [Real.volume_real_Ioc_of_le ht₀pos.le, sub_zero] at this
    have e : 2 * π * A * t₀ = A / 2 := by
      rw [ht₀]; field_simp; ring
    rw [e] at this
    exact (le_abs_self _).trans (this.trans' (by rw [Real.norm_eq_abs]))
  -- the tail
  have hVge : ∀ t ∈ Ioi t₀, π ^ 2 / 2 ≤ virasoroProblem.cardyV a t := fun t ht => by
    have ht' : t₀ < t := ht
    have h1 := virasoro_cardyV_ge ha (ht₀pos.trans ht').le
    have h2 : 8 * π ^ 4 * t₀ ^ 2 = π ^ 2 / 2 := by rw [ht₀]; field_simp; ring
    have h3 : 8 * π ^ 4 * t₀ ^ 2 ≤ 8 * π ^ 4 * t ^ 2 := by gcongr
    linarith
  have htail : ∫ t in Ioi t₀, |g t| ≤ (2 / π ^ 2) * virasoroProblem.cardyNorm a g := by
    have hmono : ∫ t in Ioi t₀, |g t| ≤
        ∫ t in Ioi t₀, (2 / π ^ 2) * (|g t| * virasoroProblem.cardyV a t) := by
      refine setIntegral_mono_on (hAint.mono_set (Ioi_subset_Ioi ht₀pos.le))
        ((hMint.mono_set (Ioi_subset_Ioi ht₀pos.le)).const_mul _) measurableSet_Ioi fun t ht => ?_
      have h := hVge t ht
      have hg0 : 0 ≤ |g t| := abs_nonneg _
      have : |g t| = (2 / π ^ 2) * (|g t| * (π ^ 2 / 2)) := by field_simp
      calc |g t| = (2 / π ^ 2) * (|g t| * (π ^ 2 / 2)) := this
        _ ≤ (2 / π ^ 2) * (|g t| * virasoroProblem.cardyV a t) := by gcongr
    have hle : ∫ t in Ioi t₀, |g t| * virasoroProblem.cardyV a t ≤ virasoroProblem.cardyNorm a g := by
      unfold FixedWeightProblem.cardyNorm
      refine setIntegral_mono_set hMint ?_ (Ioi_subset_Ioi ht₀pos.le).eventuallyLE
      exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
        mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg
          (by rw [virasoroProblem_totalShift]; exact ha) (mem_Ioi.mp ht).le))
    rw [integral_const_mul] at hmono
    calc _ ≤ _ := hmono
      _ ≤ (2 / π ^ 2) * virasoroProblem.cardyNorm a g := by gcongr
  have : A ≤ A / 2 + (2 / π ^ 2) * virasoroProblem.cardyNorm a g := by
    rw [hsplit] at hhead ⊢; linarith [hhead, htail]
  have e : 4 / π ^ 2 * virasoroProblem.cardyNorm a g =
      2 * ((2 / π ^ 2) * virasoroProblem.cardyNorm a g) := by ring
  rw [e]; linarith

/-- **Lemma B (b), second bound (`vlo:Bessel`)**: `sup_{t ≥ 0} |g(t)| ≤ (8/π) M[g]`. -/
theorem lemmaB_b_sup (ha : 2 ≤ a) (hg : TestClass virasoroProblem a g) {t : ℝ} (ht : 0 ≤ t) :
    |g t| ≤ 8 / π * virasoroProblem.cardyNorm a g := by
  have h1 := abs_le_two_pi_integral hg ht
  have h2 := lemmaB_b_integral ha hg
  have hpi := Real.pi_pos
  calc |g t| ≤ 2 * π * ∫ s in Ioi 0, |g s| := h1
    _ ≤ 2 * π * (4 / π ^ 2 * virasoroProblem.cardyNorm a g) := by gcongr
    _ = 8 / π * virasoroProblem.cardyNorm a g := by field_simp; ring

/-- **Lemma B (d), first bound (`vlo:Bessel`)** with explicit constant: for `c' ≥ 1000` and every
`g ∈ TestClass virasoroProblem (c'/12)`, `|g| K_a` is integrable on `(0, ∞)` and
`∫₀^∞ |g| K_a dt ≤ 2 e^{92} c'² M[g]` where `K_a = kernelK 1 (c'/12)`.  (The paper's `C` is unspecified;
the threshold `1000` and `C = 2e^{92}` come from `kernelK_le_mul_cardyV`.) -/
theorem lemmaB_d_integral {c' : ℝ} (hc : 1000 ≤ c') {g : ℝ → ℝ}
    (hg : TestClass virasoroProblem (c' / 12) g) :
    IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioi 0) ∧
      ∫ t in Ioi 0, |g t| * kernelK 1 (c' / 12) t ≤
        2 * exp 92 * c' ^ 2 * virasoroProblem.cardyNorm (c' / 12) g := by
  have hc0 : 0 < c' := by linarith
  have ha : (2 : ℝ) ≤ c' / 12 := by linarith
  have hshift : virasoroProblem.totalShift ≤ c' / 12 := by
    rw [virasoroProblem_totalShift]; exact ha
  set M : ℝ := virasoroProblem.cardyNorm (c' / 12) g with hM
  set t₁ : ℝ := 1 / c' with ht₁
  have ht₁pos : 0 < t₁ := by positivity
  have hMnn : 0 ≤ M := virasoroProblem.cardyNorm_nonneg hshift g
  have hMint : IntegrableOn (fun t => |g t| * virasoroProblem.cardyV (c' / 12) t) (Ioi 0) :=
    hg.int_cardy
  have hKcont : Continuous (kernelK 1 (c' / 12)) := continuous_kernelK 1 _
  have hcontOn : ContinuousOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ici 0) :=
    hg.cont.abs.mul hKcont.continuousOn
  -- head `(0, t₁]`
  have hheadInt : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioc 0 t₁) :=
    (ContinuousOn.integrableOn_Icc (hcontOn.mono (fun t ht => ht.1))).mono_set Ioc_subset_Icc_self
  have hI0 : Bessel.besselI0 (4 * π / √12) ≤ exp 5 := by
    refine (Bessel.besselI0_le_exp (by positivity)).trans (exp_le_exp.mpr ?_)
    have h12 : (3 : ℝ) ≤ √12 := by
      rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    rw [div_le_iff₀ (by linarith)]
    nlinarith [Real.pi_lt_d2]
  have hheadBound : ∀ t ∈ Ioc 0 t₁, ‖|g t| * kernelK 1 (c' / 12) t‖ ≤
      (8 / π * M) * exp 5 := fun t ht => by
    have hK0 : 0 ≤ kernelK 1 (c' / 12) t := kernelK_nonneg (by positivity) ht.1.le
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hK0)]
    have h1 := lemmaB_b_sup ha hg ht.1.le
    have h2 := kernelK_le_of_le_inv hc0 ht.1.le ht.2
    gcongr
    exact h2.trans hI0
  have hheadle : ∫ t in Ioc 0 t₁, |g t| * kernelK 1 (c' / 12) t ≤ exp 92 * c' ^ 2 * M := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioc 0 t₁) (by simp) hheadBound
    rw [Real.volume_real_Ioc_of_le ht₁pos.le, sub_zero] at this
    refine (le_abs_self _).trans ((this.trans' (by rw [Real.norm_eq_abs])).trans ?_)
    have hpi := Real.pi_pos
    have hpi3 : π < 4 := Real.pi_lt_four
    have h8 : 8 / π ≤ 3 := by rw [div_le_iff₀ hpi]; nlinarith [Real.pi_gt_three]
    have he5 : 3 * exp 5 ≤ exp 92 := by
      have h87 : (88 : ℝ) ≤ exp 87 := by have := Real.add_one_le_exp (87 : ℝ); linarith
      have : exp 92 = exp 87 * exp 5 := by rw [← exp_add]; norm_num
      rw [this]; nlinarith [exp_pos 5]
    have hc2 : (1 : ℝ) ≤ c' ^ 2 := by nlinarith
    have ht1 : t₁ ≤ 1 := by rw [ht₁, div_le_one hc0]; linarith
    have he := exp_pos 5
    have e1 : 8 / π * M * exp 5 * t₁ ≤ 3 * M * exp 5 * 1 := by gcongr
    have e2 : 3 * M * exp 5 * 1 ≤ exp 92 * M := by
      have := mul_le_mul_of_nonneg_right he5 hMnn
      linarith
    have e3 : exp 92 * M ≤ exp 92 * c' ^ 2 * M := by
      have h0 : 0 ≤ exp 92 * M := by positivity
      nlinarith
    linarith
  -- tail `(t₁, ∞)`
  have htailBound : ∀ t ∈ Ioi t₁, |g t| * kernelK 1 (c' / 12) t ≤
      exp 92 * c' ^ 2 * (|g t| * virasoroProblem.cardyV (c' / 12) t) := fun t ht => by
    have h := kernelK_le_mul_cardyV hc (le_of_lt ht)
    have := abs_nonneg (g t)
    calc |g t| * kernelK 1 (c' / 12) t ≤ |g t| * (exp 92 * c' ^ 2 * virasoroProblem.cardyV (c' / 12) t) := by
          gcongr
      _ = _ := by ring
  have hmeas : AEStronglyMeasurable (fun t => |g t| * kernelK 1 (c' / 12) t)
      (volume.restrict (Ioi t₁)) :=
    (hcontOn.mono (fun t ht => (ht₁pos.trans ht).le)).aestronglyMeasurable measurableSet_Ioi
  have htailInt : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioi t₁) := by
    refine Integrable.mono' ((hMint.mono_set (Ioi_subset_Ioi ht₁pos.le)).const_mul
      (exp 92 * c' ^ 2)) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have hK0 : 0 ≤ kernelK 1 (c' / 12) t := kernelK_nonneg (by positivity) (ht₁pos.trans ht).le
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hK0)]
    exact htailBound t ht
  have htaille : ∫ t in Ioi t₁, |g t| * kernelK 1 (c' / 12) t ≤ exp 92 * c' ^ 2 * M := by
    calc ∫ t in Ioi t₁, |g t| * kernelK 1 (c' / 12) t
        ≤ ∫ t in Ioi t₁, exp 92 * c' ^ 2 * (|g t| * virasoroProblem.cardyV (c' / 12) t) :=
          setIntegral_mono_on htailInt ((hMint.mono_set (Ioi_subset_Ioi ht₁pos.le)).const_mul _)
            measurableSet_Ioi htailBound
      _ = exp 92 * c' ^ 2 * ∫ t in Ioi t₁, |g t| * virasoroProblem.cardyV (c' / 12) t :=
          integral_const_mul _ _
      _ ≤ exp 92 * c' ^ 2 * M := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine setIntegral_mono_set hMint ?_ (Ioi_subset_Ioi ht₁pos.le).eventuallyLE
          exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht =>
            mul_nonneg (abs_nonneg _) (virasoroProblem.cardyV_nonneg hshift (mem_Ioi.mp ht).le))
  have hunion : Ioc 0 t₁ ∪ Ioi t₁ = Ioi 0 := Ioc_union_Ioi_eq_Ioi ht₁pos.le
  have hall : IntegrableOn (fun t => |g t| * kernelK 1 (c' / 12) t) (Ioi 0) := by
    rw [← hunion]; exact hheadInt.union htailInt
  refine ⟨hall, ?_⟩
  rw [← hunion, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hheadInt htailInt]
  have : 2 * exp 92 * c' ^ 2 * M = exp 92 * c' ^ 2 * M + exp 92 * c' ^ 2 * M := by ring
  rw [this]; exact add_le_add hheadle htaille

/-- info: 'FormalResearch.ModularBootstrap.Integration.lemmaB_b_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaB_b_integral

/-- info: 'FormalResearch.ModularBootstrap.Integration.lemmaB_b_sup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaB_b_sup

/-- info: 'FormalResearch.ModularBootstrap.Integration.lemmaB_d_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lemmaB_d_integral

end FormalResearch.ModularBootstrap.Integration

module

public import Mathlib
public import FormalResearch.JacobiEigenvectors.TheoremA.GeometrySoftInt

/-!
# Paper J, Layer 2 (L2.G4 (d)): the Morse coordinate of a nondegenerate maximum

Source: Paper J `thmA.tex`, `lem:tha-geom` (d) (the Morse coordinate `t` of `f_+` at the fold `u_c`), `lem:hyp-morse`, `app_smooth`.

Let `f` be `C^{n+2}` on an open set `U` containing `[a - rho, a + rho]`, with `f'(a) = 0` and `m <= -f'' <= M` on
`[a - rho, a + rho]` (`0 < m <= M`).  Put `h(x) = int_0^1 (1 - s)(-f''(a + s x)) ds` and `t(x) = x sqrt(h(x))`.  Then on
`(-rho, rho)`:

* `f(a + x) = f(a) - t(x)^2`   (Taylor with integral remainder, by integration by parts),
* `t(0) = 0`, `t` is differentiable with `t' >= c_t = m / (2 sqrt(M/2))` (`t' = (g'/x)/(2 sqrt h)` for `x != 0`, `t'(0) = sqrt h(0)`),
* `t` is `C^n` (`h` is `C^n` by `SoftInt.contDiffOn_wint`, `h >= m/2 > 0`).

Differences from the paper: the paper takes `t = sign(x) sqrt(f(a) - f(a + x))`; here `t(x) = x sqrt(h(x))` is the same function
(`t^2 = f(a) - f(a+x)`, `t` has the sign of `x`).  The derivative bound is explicit: `c_t = m/(2 sqrt(M/2))`.
Not formalised: nothing; this file is a self-contained lemma about one function.
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA.SoftMorse

open Set Filter Topology MeasureTheory intervalIntegral FormalResearch.JacobiEigenvectors.TheoremA.SoftInt

/-- `h(x) = int_0^1 (1 - s) (-f''(a + s x)) ds`. -/
def hh (f : ℝ → ℝ) (a x : ℝ) : ℝ := wint 0 (fun u => -deriv (deriv f) u) a x

/-- The Morse coordinate `t(x) = x sqrt(h(x))`. -/
def morseT (f : ℝ → ℝ) (a x : ℝ) : ℝ := x * Real.sqrt (hh f a x)

/-- Hypotheses of the Morse lemma. -/
structure MorseData (f : ℝ → ℝ) (a ρ : ℝ) (U : Set ℝ) (n : ℕ) (m M : ℝ) : Prop where
  hρ : 0 < ρ
  hU : IsOpen U
  hUρ : Icc (a - ρ) (a + ρ) ⊆ U
  hf : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f U
  hf0 : deriv f a = 0
  hm : 0 < m
  hmM : m ≤ M
  hb : ∀ u ∈ Icc (a - ρ) (a + ρ), m ≤ -deriv (deriv f) u ∧ -deriv (deriv f) u ≤ M

lemma cd_succ {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {k : ℕ}
    (h : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g U) :
    DifferentiableOn ℝ g U ∧ ContDiffOn ℝ (k : WithTop ℕ∞) (deriv g) U := by
  have hc : ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 := by push_cast; rfl
  rw [hc] at h
  have := (contDiffOn_succ_iff_deriv_of_isOpen hU).1 h
  exact ⟨this.1, this.2.2⟩

lemma int_one_sub : ∫ s in (0 : ℝ)..1, (1 - s) = 1 / 2 := by
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  simp [integral_id]
  norm_num

namespace MorseData

variable {f : ℝ → ℝ} {a ρ : ℝ} {U : Set ℝ} {n : ℕ} {m M : ℝ} (d : MorseData f a ρ U n m M)

include d

lemma cd1 : DifferentiableOn ℝ f U ∧ ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (deriv f) U :=
  cd_succ d.hU (k := n + 1) d.hf

lemma cd2 : DifferentiableOn ℝ (deriv f) U ∧ ContDiffOn ℝ (n : WithTop ℕ∞) (deriv (deriv f)) U :=
  cd_succ d.hU (k := n) d.cd1.2

lemma hasDeriv1 {u : ℝ} (hu : u ∈ U) : HasDerivAt f (deriv f u) u :=
  ((d.cd1.1 u hu).differentiableAt (d.hU.mem_nhds hu)).hasDerivAt

lemma hasDeriv2 {u : ℝ} (hu : u ∈ U) : HasDerivAt (deriv f) (deriv (deriv f) u) u :=
  ((d.cd2.1 u hu).differentiableAt (d.hU.mem_nhds hu)).hasDerivAt

lemma phi_cd : ContDiffOn ℝ (n : WithTop ℕ∞) (fun u => -deriv (deriv f) u) U := d.cd2.2.neg

lemma mem_U {x s : ℝ} (hx : x ∈ Ioo (-ρ) ρ) (hs : s ∈ Icc (0 : ℝ) 1) : a + s * x ∈ U :=
  d.hUρ (affine_mem hx hs)

/-- Bounds on `h`. -/
lemma hh_bounds {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) : m / 2 ≤ hh f a x ∧ hh f a x ≤ M / 2 := by
  have hI : ∀ c : ℝ, ∫ s in (0 : ℝ)..1, (1 - s) * c = c / 2 := by
    intro c
    rw [intervalIntegral.integral_mul_const, int_one_sub]
    ring
  have hcont : ContinuousOn (fun s : ℝ => (1 - s) * (-deriv (deriv f) (a + s * x))) (uIcc 0 1) := by
    have h1 : ContinuousOn (fun s : ℝ => -deriv (deriv f) (a + s * x)) (uIcc 0 1) := by
      refine (d.cd2.2.continuousOn.neg).comp (by fun_prop : Continuous (fun s : ℝ => a + s * x)).continuousOn ?_
      intro s hs
      rw [uIcc_of_le zero_le_one] at hs
      exact d.mem_U hx hs
    exact (by fun_prop : Continuous (fun s : ℝ => 1 - s)).continuousOn.mul h1
  have hEq : hh f a x = ∫ s in (0 : ℝ)..1, (1 - s) * (-deriv (deriv f) (a + s * x)) := by
    unfold hh wint
    apply intervalIntegral.integral_congr
    intro s _
    simp
  have hbd : ∀ s ∈ Icc (0 : ℝ) 1, m ≤ -deriv (deriv f) (a + s * x) ∧ -deriv (deriv f) (a + s * x) ≤ M :=
    fun s hs => d.hb _ (affine_mem hx hs)
  constructor
  · rw [hEq, ← hI m]
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (by fun_prop : Continuous (fun s : ℝ => (1 - s) * m)).intervalIntegrable _ _
    · exact (hcont.intervalIntegrable)
    · intro s hs
      exact mul_le_mul_of_nonneg_left (hbd s hs).1 (by linarith [hs.2])
  · rw [hEq, ← hI M]
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (hcont.intervalIntegrable)
    · exact (by fun_prop : Continuous (fun s : ℝ => (1 - s) * M)).intervalIntegrable _ _
    · intro s hs
      exact mul_le_mul_of_nonneg_left (hbd s hs).2 (by linarith [hs.2])

lemma hh_pos {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) : 0 < hh f a x := by
  have := (d.hh_bounds hx).1
  linarith [d.hm]

lemma hh_cd : ContDiffOn ℝ (n : WithTop ℕ∞) (hh f a) (Ioo (-ρ) ρ) :=
  contDiffOn_wint d.hU d.hUρ n _ d.phi_cd 0

lemma morseT_cd : ContDiffOn ℝ (n : WithTop ℕ∞) (morseT f a) (Ioo (-ρ) ρ) := by
  unfold morseT
  exact contDiffOn_id.mul (d.hh_cd.sqrt (fun x hx => (d.hh_pos hx).ne'))

omit d in
lemma morseT_zero : morseT f a 0 = 0 := by simp [morseT]

/-- Taylor with integral remainder: `f(a) - f(a + x) = x^2 h(x)`. -/
lemma taylor {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) : f a - f (a + x) = x ^ 2 * hh f a x := by
  have hmemU : ∀ s ∈ uIcc (0 : ℝ) 1, a + s * x ∈ U := by
    intro s hs
    rw [uIcc_of_le zero_le_one] at hs
    exact d.mem_U hx hs
  have hin : ∀ s : ℝ, HasDerivAt (fun y : ℝ => a + y * x) x s := by
    intro s
    simpa using ((hasDerivAt_id s).mul_const x).const_add a
  have hψ : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => f (a + s * x)) (deriv f (a + s * x) * x) s := by
    intro s hs
    exact (d.hasDeriv1 (hmemU s hs)).comp s (hin s)
  have hv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => x * deriv f (a + s * x)) (x * (deriv (deriv f) (a + s * x) * x)) s := by
    intro s hs
    exact ((d.hasDeriv2 (hmemU s hs)).comp s (hin s)).const_mul x
  have hu : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => 1 - s) (-1) s := by
    intro s _
    simpa using (hasDerivAt_id s).const_sub 1
  have c2 : ContinuousOn (fun s : ℝ => deriv (deriv f) (a + s * x)) (uIcc 0 1) :=
    d.cd2.2.continuousOn.comp (by fun_prop : Continuous (fun s : ℝ => a + s * x)).continuousOn hmemU
  have c1 : ContinuousOn (fun s : ℝ => deriv f (a + s * x)) (uIcc 0 1) :=
    d.cd1.2.continuousOn.comp (by fun_prop : Continuous (fun s : ℝ => a + s * x)).continuousOn hmemU
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (by simp)
    ((by fun_prop : ContinuousOn (fun s : ℝ => x * (deriv (deriv f) (a + s * x) * x)) (uIcc 0 1)).intervalIntegrable)
  have hψint : ∫ s in (0 : ℝ)..1, deriv f (a + s * x) * x = f (a + 1 * x) - f (a + 0 * x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hψ ((c1.mul continuousOn_const).intervalIntegrable)
  have hh_eq : hh f a x = -∫ s in (0 : ℝ)..1, (1 - s) * deriv (deriv f) (a + s * x) := by
    unfold hh wint
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro s _
    simp
  have left : ∫ s in (0 : ℝ)..1, (1 - s) * (x * (deriv (deriv f) (a + s * x) * x))
      = (x * x) * ∫ s in (0 : ℝ)..1, (1 - s) * deriv (deriv f) (a + s * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    simp only; ring
  have right : ∫ s in (0 : ℝ)..1, (-1 : ℝ) * (x * deriv f (a + s * x)) = -(f (a + 1 * x) - f (a + 0 * x)) := by
    have : ∀ s : ℝ, (-1 : ℝ) * (x * deriv f (a + s * x)) = -(deriv f (a + s * x) * x) := fun s => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_neg, hψint]
  simp only [left, right] at ibp
  simp only [sub_self, mul_zero, zero_mul, one_mul, sub_zero, zero_add, mul_one, sub_neg_eq_add] at ibp
  rw [hh_eq]
  have h0 : x * deriv f a = 0 := by rw [d.hf0]; ring
  simp only [add_zero, zero_mul, mul_zero] at ibp
  rw [h0] at ibp
  nlinarith [ibp]

lemma morseT_sq {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) : f (a + x) = f a - morseT f a x ^ 2 := by
  have := d.taylor hx
  have hp := d.hh_pos hx
  unfold morseT
  rw [mul_pow, Real.sq_sqrt hp.le]
  linarith

/-- `y |-> -f'(a + y)` has derivative `-f''(a + y)` on `(-rho, rho)`. -/
lemma G1_hasDeriv {y : ℝ} (hy : y ∈ Ioo (-ρ) ρ) :
    HasDerivAt (fun y : ℝ => -deriv f (a + y)) (-deriv (deriv f) (a + y)) y := by
  have hmem : a + y ∈ U := d.hUρ ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have h := ((d.hasDeriv2 hmem).comp y ((hasDerivAt_id y).const_add a)).neg
  convert h using 1
  · rfl
  · ring

lemma G1_zero : -deriv f (a + 0) = 0 := by simp [d.hf0]

/-- `m x <= -f'(a + x) <= M x` for `x > 0`. -/
lemma G1_pos {x : ℝ} (hx : x ∈ Ioo 0 ρ) : m * x ≤ -deriv f (a + x) ∧ -deriv f (a + x) ≤ M * x := by
  have hsub : Icc 0 x ⊆ Ioo (-ρ) ρ := fun y hy => ⟨by linarith [hy.1, d.hρ], by linarith [hy.2, hx.2]⟩
  have hdiff : ∀ y ∈ Ioo 0 x, HasDerivAt (fun y : ℝ => -deriv f (a + y)) (-deriv (deriv f) (a + y)) y :=
    fun y hy => d.G1_hasDeriv (hsub ⟨hy.1.le, hy.2.le⟩)
  have hcont : ContinuousOn (fun y : ℝ => -deriv f (a + y)) (Icc 0 x) := fun y hy =>
    (d.G1_hasDeriv (hsub hy)).continuousAt.continuousWithinAt
  have hdo : DifferentiableOn ℝ (fun y : ℝ => -deriv f (a + y)) (interior (Icc 0 x)) := by
    rw [interior_Icc]; exact fun y hy => (hdiff y hy).differentiableAt.differentiableWithinAt
  have hbd : ∀ y ∈ interior (Icc 0 x), m ≤ deriv (fun y : ℝ => -deriv f (a + y)) y ∧
      deriv (fun y : ℝ => -deriv f (a + y)) y ≤ M := by
    intro y hy
    rw [interior_Icc] at hy
    rw [(hdiff y hy).deriv]
    exact d.hb _ ⟨by linarith [hy.1, hy.2, hx.2, d.hρ], by linarith [hy.1, hy.2, hx.2, d.hρ]⟩
  have h0 : (0 : ℝ) ∈ Icc 0 x := ⟨le_rfl, hx.1.le⟩
  have h1 : x ∈ Icc 0 x := ⟨hx.1.le, le_rfl⟩
  have hlo := (convex_Icc 0 x).mul_sub_le_image_sub_of_le_deriv hcont hdo (fun y hy => (hbd y hy).1) 0 h0 x h1 hx.1.le
  have hhi := (convex_Icc 0 x).image_sub_le_mul_sub_of_deriv_le hcont hdo (fun y hy => (hbd y hy).2) 0 h0 x h1 hx.1.le
  have hz := d.G1_zero
  simp only [sub_zero, hz] at hlo hhi
  exact ⟨by linarith, by linarith⟩

/-- `M x <= -f'(a + x) <= m x` for `x < 0`. -/
lemma G1_neg {x : ℝ} (hx : x ∈ Ioo (-ρ) 0) : M * x ≤ -deriv f (a + x) ∧ -deriv f (a + x) ≤ m * x := by
  have hsub : Icc x 0 ⊆ Ioo (-ρ) ρ := fun y hy => ⟨by linarith [hy.1, hx.1], by linarith [hy.2, d.hρ]⟩
  have hdiff : ∀ y ∈ Ioo x 0, HasDerivAt (fun y : ℝ => -deriv f (a + y)) (-deriv (deriv f) (a + y)) y :=
    fun y hy => d.G1_hasDeriv (hsub ⟨hy.1.le, hy.2.le⟩)
  have hcont : ContinuousOn (fun y : ℝ => -deriv f (a + y)) (Icc x 0) := fun y hy =>
    (d.G1_hasDeriv (hsub hy)).continuousAt.continuousWithinAt
  have hdo : DifferentiableOn ℝ (fun y : ℝ => -deriv f (a + y)) (interior (Icc x 0)) := by
    rw [interior_Icc]; exact fun y hy => (hdiff y hy).differentiableAt.differentiableWithinAt
  have hbd : ∀ y ∈ interior (Icc x 0), m ≤ deriv (fun y : ℝ => -deriv f (a + y)) y ∧
      deriv (fun y : ℝ => -deriv f (a + y)) y ≤ M := by
    intro y hy
    rw [interior_Icc] at hy
    rw [(hdiff y hy).deriv]
    exact d.hb _ ⟨by linarith [hy.1, hy.2, hx.1, d.hρ], by linarith [hy.1, hy.2, hx.2, d.hρ]⟩
  have h0 : (0 : ℝ) ∈ Icc x 0 := ⟨hx.2.le, le_rfl⟩
  have h1 : x ∈ Icc x 0 := ⟨le_rfl, hx.2.le⟩
  have hlo := (convex_Icc x 0).mul_sub_le_image_sub_of_le_deriv hcont hdo (fun y hy => (hbd y hy).1) x h1 0 h0 hx.2.le
  have hhi := (convex_Icc x 0).image_sub_le_mul_sub_of_deriv_le hcont hdo (fun y hy => (hbd y hy).2) x h1 0 h0 hx.2.le
  have hz := d.G1_zero
  simp only [zero_sub, hz] at hlo hhi
  exact ⟨by linarith, by linarith⟩

lemma morseT_pos_of_pos {x : ℝ} (hx : x ∈ Ioo 0 ρ) : 0 < morseT f a x := by
  have hx' : x ∈ Ioo (-ρ) ρ := ⟨by linarith [hx.1, d.hρ], hx.2⟩
  exact mul_pos hx.1 (Real.sqrt_pos.2 (d.hh_pos hx'))

lemma morseT_neg_of_neg {x : ℝ} (hx : x ∈ Ioo (-ρ) 0) : morseT f a x < 0 := by
  have hx' : x ∈ Ioo (-ρ) ρ := ⟨hx.1, by linarith [hx.2, d.hρ]⟩
  exact mul_neg_of_neg_of_pos hx.2 (Real.sqrt_pos.2 (d.hh_pos hx'))

/-- Derivative of `t` away from `0`. -/
lemma hasDeriv_ne {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) (hx0 : x ≠ 0) :
    HasDerivAt (morseT f a) (-deriv f (a + x) / (2 * morseT f a x)) x := by
  set g : ℝ → ℝ := fun y => f a - f (a + y) with hg
  have hgd : ∀ y ∈ Ioo (-ρ) ρ, HasDerivAt g (-deriv f (a + y)) y := by
    intro y hy
    have hmem : a + y ∈ U := d.hUρ ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have := (d.hasDeriv1 hmem).comp y ((hasDerivAt_id y).const_add a)
    simpa using this.const_sub (f a)
  have hgt : ∀ y ∈ Ioo (-ρ) ρ, g y = morseT f a y ^ 2 := by
    intro y hy
    have := d.morseT_sq hy
    simp only [hg]; linarith
  have hnhds : Ioo (-ρ) ρ ∈ 𝓝 x := isOpen_Ioo.mem_nhds hx
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · -- x < 0
    have hxn : x ∈ Ioo (-ρ) 0 := ⟨hx.1, hneg⟩
    have hT : morseT f a x < 0 := d.morseT_neg_of_neg hxn
    have hgx : g x ≠ 0 := by rw [hgt x hx]; exact pow_ne_zero 2 hT.ne
    have hev : morseT f a =ᶠ[𝓝 x] fun y => -Real.sqrt (g y) := by
      have hn2 : Ioo (-ρ) 0 ∈ 𝓝 x := isOpen_Ioo.mem_nhds hxn
      filter_upwards [hn2] with y hy
      have hyT : morseT f a y < 0 := d.morseT_neg_of_neg hy
      have hy' : y ∈ Ioo (-ρ) ρ := ⟨hy.1, by linarith [hy.2, d.hρ]⟩
      rw [hgt y hy', Real.sqrt_sq_eq_abs, abs_of_neg hyT]; ring
    have hs := ((hgd x hx).sqrt hgx).neg
    have hsx : Real.sqrt (g x) = -morseT f a x := by
      rw [hgt x hx, Real.sqrt_sq_eq_abs, abs_of_neg hT]
    have := hs.congr_of_eventuallyEq hev
    convert this using 1
    rw [hsx]
    field_simp
  · have hxp : x ∈ Ioo 0 ρ := ⟨hpos, hx.2⟩
    have hT : 0 < morseT f a x := d.morseT_pos_of_pos hxp
    have hgx : g x ≠ 0 := by rw [hgt x hx]; exact pow_ne_zero 2 hT.ne'
    have hev : morseT f a =ᶠ[𝓝 x] fun y => Real.sqrt (g y) := by
      have hn2 : Ioo 0 ρ ∈ 𝓝 x := isOpen_Ioo.mem_nhds hxp
      filter_upwards [hn2] with y hy
      have hyT : 0 < morseT f a y := d.morseT_pos_of_pos hy
      have hy' : y ∈ Ioo (-ρ) ρ := ⟨by linarith [hy.1, d.hρ], hy.2⟩
      rw [hgt y hy', Real.sqrt_sq_eq_abs, abs_of_pos hyT]
    have hs := (hgd x hx).sqrt hgx
    have hsx : Real.sqrt (g x) = morseT f a x := by
      rw [hgt x hx, Real.sqrt_sq_eq_abs, abs_of_pos hT]
    have := hs.congr_of_eventuallyEq hev
    convert this using 1
    rw [hsx]

/-- Derivative of `t` at `0`. -/
lemma hasDeriv_zero : HasDerivAt (morseT f a) (Real.sqrt (hh f a 0)) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-ρ) ρ := ⟨by linarith [d.hρ], d.hρ⟩
  have hc : ContinuousAt (hh f a) 0 := (d.hh_cd.continuousOn.continuousAt (isOpen_Ioo.mem_nhds h0))
  rw [hasDerivAt_iff_tendsto_slope]
  have ht : Tendsto (fun y => Real.sqrt (hh f a y)) (𝓝[≠] 0) (𝓝 (Real.sqrt (hh f a 0))) :=
    (hc.sqrt).tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : y ≠ 0 := hy
  simp only [slope_def_field, morseT, zero_mul, sub_zero]
  field_simp

/-- The explicit constant. -/
def ctOf (m M : ℝ) : ℝ := m / (2 * Real.sqrt (M / 2))

lemma ctOf_pos : 0 < ctOf m M := by
  unfold ctOf
  have h1 : 0 < M := lt_of_lt_of_le d.hm d.hmM
  have h2 : 0 < Real.sqrt (M / 2) := Real.sqrt_pos.2 (by linarith)
  exact div_pos d.hm (by linarith)

lemma deriv_lower {x : ℝ} (hx : x ∈ Ioo (-ρ) ρ) :
    ∃ D, HasDerivAt (morseT f a) D x ∧ ctOf m M ≤ D := by
  have hbd := d.hh_bounds hx
  have hMpos : 0 < M := lt_of_lt_of_le d.hm d.hmM
  set s := Real.sqrt (hh f a x) with hs
  set S := Real.sqrt (M / 2) with hS
  have hhpos := d.hh_pos hx
  have hspos : 0 < s := Real.sqrt_pos.2 hhpos
  have hSpos : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hsS : s ≤ S := Real.sqrt_le_sqrt hbd.2
  have hct : ctOf m M * s ≤ m / 2 := by
    unfold ctOf
    rw [← hS]
    calc m / (2 * S) * s ≤ m / (2 * S) * S := by gcongr; exact (div_pos d.hm (by positivity)).le
      _ = m / 2 := by field_simp
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨s, d.hasDeriv_zero, ?_⟩
    -- `s >= sqrt (m/2)` and `S >= sqrt (m/2)`
    have hm2 : Real.sqrt (m / 2) ≤ s := Real.sqrt_le_sqrt hbd.1
    have hm2S : Real.sqrt (m / 2) ≤ S := Real.sqrt_le_sqrt (by linarith [d.hmM])
    have hsq : Real.sqrt (m / 2) ^ 2 = m / 2 := Real.sq_sqrt (by linarith [d.hm])
    have hq : 0 < Real.sqrt (m / 2) := Real.sqrt_pos.2 (by linarith [d.hm])
    unfold ctOf
    rw [← hS, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hm2 hm2S hq.le hspos.le]
  · refine ⟨-deriv f (a + x) / (2 * morseT f a x), d.hasDeriv_ne hx hx0, ?_⟩
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hxn : x ∈ Ioo (-ρ) 0 := ⟨hx.1, hneg⟩
      have hT : morseT f a x < 0 := d.morseT_neg_of_neg hxn
      have hG := (d.G1_neg hxn).2
      rw [le_div_iff_of_neg (by linarith)]
      have hTx : morseT f a x = x * s := rfl
      rw [hTx]
      nlinarith [mul_le_mul_of_nonpos_left hct hneg.le]
    · have hxp : x ∈ Ioo 0 ρ := ⟨hpos, hx.2⟩
      have hT : 0 < morseT f a x := d.morseT_pos_of_pos hxp
      have hG := (d.G1_pos hxp).1
      rw [le_div_iff₀ (by linarith)]
      have hTx : morseT f a x = x * s := rfl
      rw [hTx]
      nlinarith [mul_le_mul_of_nonneg_left hct hpos.le]

/-- **Morse lemma** (single function). -/
theorem main :
    ContDiffOn ℝ (n : WithTop ℕ∞) (morseT f a) (Ioo (-ρ) ρ) ∧ morseT f a 0 = 0 ∧
      ∀ x ∈ Ioo (-ρ) ρ, ctOf m M ≤ deriv (morseT f a) x ∧ DifferentiableAt ℝ (morseT f a) x ∧
        f (a + x) = f a - morseT f a x ^ 2 := by
  refine ⟨d.morseT_cd, morseT_zero, fun x hx => ?_⟩
  obtain ⟨D, hD, hle⟩ := d.deriv_lower hx
  exact ⟨by rw [hD.deriv]; exact hle, hD.differentiableAt, d.morseT_sq hx⟩

end MorseData

end FormalResearch.JacobiEigenvectors.TheoremA.SoftMorse

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.SoftMorse.MorseData.main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.SoftMorse.MorseData.main

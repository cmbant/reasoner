module

public import Mathlib
public import FormalResearch.Racah.P2LocalCalculusLeftNormal

/-!
# Local calculus on functions on `(-1,1)` (Weyl P2, `app:localgeneral`)

The concrete module for the abstract local calculus of `P2LocalCalculusLeftNormal`.

`Fn` is the real vector space of functions `f : ℝ → ℝ` that vanish outside `(-1,1)` and are `C^∞` on
`(-1,1)`; equality in `Fn` is equality of functions on `(-1,1)`.  On it:

* `xOp`: multiplication by `x`; `DOp`: `∂_x` (extended by `0`); `mulOp φ`: multiplication by a function
  `φ` smooth on `(-1,1)`;
* `Csm`: the subalgebra of multiplication operators by functions smooth on `(-1,1)`;
  `Crat`: the subalgebra of multiplication operators by functions `p(x)/(1-x²)^m`, `p` a polynomial
  (rational functions of `x` whose only possible poles are at `x = ±1`, as in the paper);
* `Hop Σ τ = -∂(1-x²)∂ + (Σ - 2τx)/(1-x²)`: the Wigner operator `𝖧₀` of `eq:H0`
  (`Σ = M²+σ²`, `τ = Mσ`), a left-normal operator.

The abstract hypotheses of `P2LocalCalculusLeftNormal` are verified for both `Csm` and `Crat`:
`[∂, x] = 1` (`DOp_xOp`), multipliers commute with `x`, and are stable under `c ↦ [∂, c]` (`comm_Csm`,
`comm_Crat`).  Not formalised here: the Wigner functions (`P2LocalCalculusWigner`).
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus.Fun

open Set Module
open scoped ContDiff

/-- The open interval `(-1,1)`. -/
abbrev Sx : Set ℝ := Ioo (-1 : ℝ) 1

lemma isOpen_Sx : IsOpen Sx := isOpen_Ioo

/-- Real functions vanishing off `(-1,1)` and smooth on `(-1,1)`. -/
def FS : Submodule ℝ (ℝ → ℝ) where
  carrier := {f | (∀ y, y ∉ Sx → f y = 0) ∧ ContDiffOn ℝ ∞ f Sx}
  add_mem' := fun ⟨h1, h2⟩ ⟨h3, h4⟩ => ⟨fun y hy => by simp [h1 y hy, h3 y hy], h2.add h4⟩
  zero_mem' := ⟨fun _ _ => rfl, contDiffOn_const⟩
  smul_mem' := fun c f ⟨h1, h2⟩ =>
    ⟨fun y hy => by simp [h1 y hy], (contDiffOn_const (c := c)).mul h2⟩

/-- The module of functions. -/
abbrev Fn := ↥FS

@[ext] lemma Fn.ext' {f g : Fn} (h : ∀ y, f.1 y = g.1 y) : f = g := Subtype.ext (funext h)

lemma Fn.zero_off (f : Fn) {y : ℝ} (hy : y ∉ Sx) : f.1 y = 0 := f.2.1 y hy

lemma Fn.diffAt (f : Fn) {y : ℝ} (hy : y ∈ Sx) : DifferentiableAt ℝ f.1 y :=
  (f.2.2.differentiableOn (by simp)).differentiableAt (isOpen_Sx.mem_nhds hy)

lemma Fn.contDiffOn_deriv (f : Fn) : ContDiffOn ℝ ∞ (deriv f.1) Sx :=
  f.2.2.deriv_of_isOpen isOpen_Sx (by simp)

/-- Multiplication by a function smooth on `(-1,1)`. -/
noncomputable def mulOp (φ : ℝ → ℝ) (hφ : ContDiffOn ℝ ∞ φ Sx) : End ℝ Fn where
  toFun f := ⟨fun y => φ y * f.1 y, fun y hy => by simp [f.zero_off hy], hφ.mul f.2.2⟩
  map_add' f g := Fn.ext' fun y => by simp [mul_add]
  map_smul' c f := Fn.ext' fun y => by simp [mul_left_comm]

@[simp] lemma mulOp_apply (φ : ℝ → ℝ) (hφ : ContDiffOn ℝ ∞ φ Sx) (f : Fn) (y : ℝ) :
    (mulOp φ hφ f).1 y = φ y * f.1 y := rfl

/-- Multiplication by `x`. -/
noncomputable def xOp : End ℝ Fn := mulOp (fun y => y) contDiffOn_id

/-- `∂_x f`, extended by `0` off `(-1,1)`, as an element of `Fn`. -/
noncomputable def DFun (f : Fn) : Fn :=
  ⟨fun y => if y ∈ Sx then deriv f.1 y else 0, fun y hy => by simp only [hy, ↓reduceIte],
    (f.contDiffOn_deriv).congr fun y hy => by simp only [hy, ↓reduceIte]⟩

lemma DFun_apply (f : Fn) {y : ℝ} (hy : y ∈ Sx) : (DFun f).1 y = deriv f.1 y := by
  show (if y ∈ Sx then deriv f.1 y else 0) = _
  simp only [hy, ↓reduceIte]

lemma DFun_apply_off (f : Fn) {y : ℝ} (hy : y ∉ Sx) : (DFun f).1 y = 0 := by
  show (if y ∈ Sx then deriv f.1 y else 0) = _
  simp only [hy, ↓reduceIte]

/-- `∂_x`, extended by `0` off `(-1,1)`. -/
noncomputable def DOp : End ℝ Fn where
  toFun := DFun
  map_add' f g := Fn.ext' fun y => by
    by_cases hy : y ∈ Sx
    · rw [DFun_apply _ hy]
      show _ = (DFun f).1 y + (DFun g).1 y
      rw [DFun_apply _ hy, DFun_apply _ hy]
      exact deriv_add (f.diffAt hy) (g.diffAt hy)
    · rw [DFun_apply_off _ hy]
      show _ = (DFun f).1 y + (DFun g).1 y
      rw [DFun_apply_off _ hy, DFun_apply_off _ hy, add_zero]
  map_smul' c f := Fn.ext' fun y => by
    by_cases hy : y ∈ Sx
    · rw [DFun_apply _ hy]
      show _ = c * (DFun f).1 y
      rw [DFun_apply _ hy]
      exact deriv_const_mul _ (f.diffAt hy)
    · rw [DFun_apply_off _ hy]
      show _ = c * (DFun f).1 y
      rw [DFun_apply_off _ hy, mul_zero]

lemma DOp_apply (f : Fn) {y : ℝ} (hy : y ∈ Sx) : (DOp f).1 y = deriv f.1 y := DFun_apply f hy

lemma DOp_apply_off (f : Fn) {y : ℝ} (hy : y ∉ Sx) : (DOp f).1 y = 0 := DFun_apply_off f hy

/-- `[∂, x] = 1`. -/
theorem DOp_xOp : DOp * xOp - xOp * DOp = 1 := by
  refine LinearMap.ext fun f => Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Module.End.one_apply]
    simp only [xOp, mulOp_apply]
    rw [DOp_apply _ hy, DOp_apply _ hy]
    have : HasDerivAt (fun z => z * f.1 z) (1 * f.1 y + y * deriv f.1 y) y :=
      (hasDerivAt_id y).mul (f.diffAt hy).hasDerivAt
    show deriv (fun z => z * f.1 z) y - y * deriv f.1 y = f.1 y
    rw [this.deriv]
    ring
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Module.End.one_apply, DOp_apply_off _ hy, xOp, mulOp_apply, Fn.zero_off _ hy]

/-! ### Multiplication operators -/

/-- Multiplication operators by functions smooth on `(-1,1)`. -/
def Csm : Subalgebra ℝ (End ℝ Fn) where
  carrier := {T | ∃ φ : ℝ → ℝ, ContDiffOn ℝ ∞ φ Sx ∧ ∀ (f : Fn) (y : ℝ), (T f).1 y = φ y * f.1 y}
  mul_mem' := fun {S T} ⟨φ, hφ, hS⟩ ⟨ψ, hψ, hT⟩ =>
    ⟨fun y => φ y * ψ y, hφ.mul hψ, fun f y => by
      simp only [Module.End.mul_apply, hS, hT]; ring⟩
  one_mem' := ⟨fun _ => 1, contDiffOn_const, fun f y => by simp⟩
  add_mem' := fun {S T} ⟨φ, hφ, hS⟩ ⟨ψ, hψ, hT⟩ =>
    ⟨fun y => φ y + ψ y, hφ.add hψ, fun f y => by simp [hS, hT, add_mul]⟩
  zero_mem' := ⟨fun _ => 0, contDiffOn_const, fun f y => by simp⟩
  algebraMap_mem' := fun c =>
    ⟨fun _ => c, contDiffOn_const, fun f y => by simp [Algebra.algebraMap_eq_smul_one]⟩

lemma mulOp_mem_Csm (φ : ℝ → ℝ) (hφ : ContDiffOn ℝ ∞ φ Sx) : mulOp φ hφ ∈ Csm :=
  ⟨φ, hφ, fun _ _ => rfl⟩

lemma xOp_mem_Csm : xOp ∈ Csm := mulOp_mem_Csm _ _

theorem comm_x_Csm {c : End ℝ Fn} (hc : c ∈ Csm) : xOp * c = c * xOp := by
  obtain ⟨φ, hφ, h⟩ := hc
  refine LinearMap.ext fun f => Fn.ext' fun y => ?_
  simp only [Module.End.mul_apply, h, xOp, mulOp_apply]
  ring

/-- `[∂, c]` of a smooth multiplier `φ` acts as the multiplier by `φ'`. -/
theorem comm_apply {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ ∞ φ Sx) {c : End ℝ Fn}
    (h : ∀ (f : Fn) (y : ℝ), (c f).1 y = φ y * f.1 y) (f : Fn) (y : ℝ) :
    ((DOp * c - c * DOp) f).1 y = deriv φ y * f.1 y := by
  by_cases hy : y ∈ Sx
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, h]
    rw [DOp_apply _ hy, DOp_apply _ hy]
    have hφd : DifferentiableAt ℝ φ y :=
      (hφ.differentiableOn (by simp)).differentiableAt (isOpen_Sx.mem_nhds hy)
    have hev : (fun z => (c f).1 z) =ᶠ[nhds y] fun z => φ z * f.1 z :=
      Filter.Eventually.of_forall fun z => h f z
    have hmul : HasDerivAt (fun z => φ z * f.1 z) (deriv φ y * f.1 y + φ y * deriv f.1 y) y :=
      hφd.hasDerivAt.mul (f.diffAt hy).hasDerivAt
    rw [hev.deriv_eq, hmul.deriv]
    ring
  · simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, h,
      DOp_apply_off _ hy, Fn.zero_off _ hy]
    simp

/-- `[∂, c]` of a smooth multiplier is the multiplier by its derivative. -/
theorem comm_Csm {c : End ℝ Fn} (hc : c ∈ Csm) : DOp * c - c * DOp ∈ Csm := by
  obtain ⟨φ, hφ, h⟩ := hc
  exact ⟨deriv φ, hφ.deriv_of_isOpen isOpen_Sx (by simp), comm_apply hφ h⟩

/-! ### Rational multipliers `p(x)/(1-x²)^m` -/

lemma contDiff_eval (p : Polynomial ℝ) : ContDiff ℝ ∞ (fun y : ℝ => p.eval y) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p (∞ : WithTop ℕ∞)
  convert this using 2 with y
  simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]


/-- `p(y)/(1-y²)^m` for `y ∈ (-1,1)`. -/
def IsRat (φ : ℝ → ℝ) : Prop :=
  ∃ (p : Polynomial ℝ) (m : ℕ), ∀ y ∈ Sx, φ y = p.eval y / (1 - y ^ 2) ^ m

lemma contDiffOn_of_isRat {φ : ℝ → ℝ} (h : IsRat φ) : ContDiffOn ℝ ∞ φ Sx := by
  obtain ⟨p, m, h⟩ := h
  have : ContDiffOn ℝ ∞ (fun y => p.eval y / (1 - y ^ 2) ^ m) Sx := by
    refine (contDiff_eval p).contDiffOn.div (by fun_prop) fun y hy => ?_
    have : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
    exact pow_ne_zero _ this
  exact this.congr h

/-- Multiplication operators by rational functions with poles only at `±1`. -/
def Crat : Subalgebra ℝ (End ℝ Fn) where
  carrier := {T | ∃ φ : ℝ → ℝ, IsRat φ ∧ ∀ (f : Fn) (y : ℝ), (T f).1 y = φ y * f.1 y}
  mul_mem' := fun {S T} ⟨φ, ⟨p, m, hp⟩, hS⟩ ⟨ψ, ⟨q, n, hq⟩, hT⟩ =>
    ⟨fun y => φ y * ψ y, ⟨p * q, m + n, fun y hy => by
      simp [hp y hy, hq y hy, pow_add, div_mul_div_comm]⟩, fun f y => by
      simp only [Module.End.mul_apply, hS, hT]; ring⟩
  one_mem' := ⟨fun _ => 1, ⟨1, 0, fun y hy => by simp⟩, fun f y => by simp⟩
  add_mem' := fun {S T} ⟨φ, ⟨p, m, hp⟩, hS⟩ ⟨ψ, ⟨q, n, hq⟩, hT⟩ =>
    ⟨fun y => φ y + ψ y, ⟨p * (1 - Polynomial.X ^ 2) ^ n + q * (1 - Polynomial.X ^ 2) ^ m, m + n,
      fun y hy => by
        have h1 : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
        simp only [hp y hy, hq y hy]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X, pow_add]
        field_simp⟩, fun f y => by simp [hS, hT, add_mul]⟩
  zero_mem' := ⟨fun _ => 0, ⟨0, 0, fun y hy => by simp⟩, fun f y => by simp⟩
  algebraMap_mem' := fun c =>
    ⟨fun _ => c, ⟨Polynomial.C c, 0, fun y hy => by simp⟩,
      fun f y => by simp [Algebra.algebraMap_eq_smul_one]⟩

lemma Crat_le_Csm : Crat ≤ Csm := fun T ⟨φ, hφ, h⟩ => ⟨φ, contDiffOn_of_isRat hφ, h⟩

lemma xOp_mem_Crat : xOp ∈ Crat :=
  ⟨fun y => y, ⟨Polynomial.X, 0, fun y hy => by simp⟩, fun _ _ => rfl⟩

theorem comm_x_Crat {c : End ℝ Fn} (hc : c ∈ Crat) : xOp * c = c * xOp :=
  comm_x_Csm (Crat_le_Csm hc)

/-- The derivative of a rational function with poles at `±1` only is again such a function. -/
theorem comm_Crat {c : End ℝ Fn} (hc : c ∈ Crat) : DOp * c - c * DOp ∈ Crat := by
  obtain ⟨φ, ⟨p, m, hp⟩, h⟩ := hc
  have hφ : ContDiffOn ℝ ∞ φ Sx := contDiffOn_of_isRat ⟨p, m, hp⟩
  refine ⟨deriv φ, ⟨Polynomial.derivative p * (1 - Polynomial.X ^ 2) +
      Polynomial.C (2 * (m : ℝ)) * Polynomial.X * p, m + 1, fun y hy => ?_⟩, comm_apply hφ h⟩
  have h1 : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]
  have hev : φ =ᶠ[nhds y] fun z => p.eval z / (1 - z ^ 2) ^ m :=
    Filter.eventually_of_mem (isOpen_Sx.mem_nhds hy) hp
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-(2 * y)) y := by
    have := (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_pow 2 y)
    convert this using 1; simp
  cases m with
  | zero =>
    have := (p.hasDerivAt y).div_const 1
    simp only [pow_zero, div_one] at this ⊢
    rw [(p.hasDerivAt y).deriv]
    simp
    field_simp
  | succ k =>
    have hq := (p.hasDerivAt y).div (hd.pow (k + 1)) (pow_ne_zero _ h1)
    rw [show deriv (fun z : ℝ => p.eval z / (1 - z ^ 2) ^ (k + 1)) y =
      deriv ((fun x => Polynomial.eval x p) / (fun z : ℝ => 1 - z ^ 2) ^ (k + 1)) y from rfl, hq.deriv]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_C]
    push_cast
    simp only [Pi.pow_apply]
    field_simp
    ring

end FormalResearch.Racah.LocalCalculus.Fun

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.DOp_xOp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.DOp_xOp

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.comm_Csm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.comm_Csm

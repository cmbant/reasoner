module

public import Mathlib
public import FormalResearch.Racah.P2LocalCalculusFun
public import FormalResearch.Wigner.WignerDODE
public import FormalResearch.Wigner.WignerDLadder

/-!
# Local calculus: the Wigner operator and the Wigner functions in `Fn` (Weyl P2, `eq:H0`, `eq:dODE`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:H0` (`𝖧₀ = -∂(1-x²)∂ + (Σ-2τx)/(1-x²)`),
`eq:dODE`, the Wigner rank recurrence.

* `Hop Σ τ` is `𝖧₀` as an operator on `Fn`, a left-normal operator over the rational multipliers
  (`Hop_mem_LN_rat`) and over the smooth ones (`Hop_mem_LN_sm`);
* `wigF L M σ` is `d^L_{Mσ}(arccos x)` as an element of `Fn`;
* `Hop_wigF`: `𝖧₀ d^L_{Mσ} = L(L+1) d^L_{Mσ}` for `Σ = M²+σ²`, `τ = Mσ` (from the Wigner ODE);
* `wigF_rank`: the Wigner rank recurrence in `Fn` (from `wignerSmallDx_rank_rec`).
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus.Fun

open Set Module FormalResearch.Wigner
open scoped ContDiff

lemma contDiffOn_one_sub_sq : ContDiffOn ℝ ∞ (fun y : ℝ => 1 - y ^ 2) Sx := by fun_prop

lemma ne_zero_one_sub_sq {y : ℝ} (hy : y ∈ Sx) : 1 - y ^ 2 ≠ 0 := by nlinarith [hy.1, hy.2]

lemma contDiffOn_V (S t : ℝ) : ContDiffOn ℝ ∞ (fun y : ℝ => (S - 2 * t * y) / (1 - y ^ 2)) Sx :=
  ContDiffOn.div (by fun_prop) (by fun_prop) fun _ hy => ne_zero_one_sub_sq hy

/-- The multiplier `1 - x²`. -/
noncomputable def m1 : End ℝ Fn := mulOp (fun y => 1 - y ^ 2) contDiffOn_one_sub_sq

/-- The multiplier `V = (Σ - 2τx)/(1-x²)`. -/
noncomputable def mV (S t : ℝ) : End ℝ Fn := mulOp (fun y => (S - 2 * t * y) / (1 - y ^ 2)) (contDiffOn_V S t)

/-- The Wigner operator `𝖧₀ = -∂(1-x²)∂ + (Σ-2τx)/(1-x²)` (`eq:H0`). -/
noncomputable def Hop (S t : ℝ) : End ℝ Fn := mV S t - DOp * m1 * DOp

lemma m1_mem_Crat : m1 ∈ Crat :=
  ⟨fun y => 1 - y ^ 2, ⟨1 - Polynomial.X ^ 2, 0, fun y hy => by simp⟩, fun _ _ => rfl⟩

lemma mV_mem_Crat (S t : ℝ) : mV S t ∈ Crat :=
  ⟨fun y => (S - 2 * t * y) / (1 - y ^ 2),
    ⟨Polynomial.C S - Polynomial.C (2 * t) * Polynomial.X, 1, fun y hy => by simp⟩, fun _ _ => rfl⟩

/-- `𝖧₀` is a left-normal operator over rational multipliers. -/
theorem Hop_mem_LN_rat (S t : ℝ) : Hop S t ∈ LN DOp Crat := by
  have hD : DOp ∈ LN DOp Crat := D_mem_LN
  unfold Hop
  exact LN_sub_mem (C_le_LN (mV_mem_Crat S t)) (LN_mul_mem (fun c hc => comm_Crat hc)
      (LN_mul_mem (fun c hc => comm_Crat hc) hD (C_le_LN m1_mem_Crat)) hD)

/-- `𝖧₀` is a left-normal operator over smooth multipliers. -/
theorem Hop_mem_LN_sm (S t : ℝ) : Hop S t ∈ LN DOp Csm := by
  have hD : DOp ∈ LN DOp Csm := D_mem_LN
  unfold Hop
  exact LN_sub_mem (C_le_LN (Crat_le_Csm (mV_mem_Crat S t))) (LN_mul_mem (fun c hc => comm_Csm hc)
      (LN_mul_mem (fun c hc => comm_Csm hc) hD (C_le_LN (Crat_le_Csm m1_mem_Crat))) hD)

lemma Hop_apply (S t : ℝ) (f : Fn) {y : ℝ} (hy : y ∈ Sx) :
    (Hop S t f).1 y = -deriv (fun z => (1 - z ^ 2) * deriv f.1 z) y +
      (S - 2 * t * y) / (1 - y ^ 2) * f.1 y := by
  have hev : (fun z => (m1 (DOp f)).1 z) =ᶠ[nhds y] fun z => (1 - z ^ 2) * deriv f.1 z := by
    filter_upwards [isOpen_Sx.mem_nhds hy] with z hz
    simp only [m1, mulOp_apply]
    rw [DOp_apply _ hz]
  show (mV S t f - DOp (m1 (DOp f))).1 y = _
  simp only [Submodule.coe_sub, Pi.sub_apply]
  rw [DOp_apply _ hy, hev.deriv_eq]
  rw [sub_eq_neg_add]
  rfl

/-- The Wigner-ODE criterion: if `f` solves `(1-x²)f'' - 2xf' + (λ - V)f = 0` on `(-1,1)`, then
`𝖧₀ f = λ f`. -/
theorem Hop_eq_smul (S t lam : ℝ) (f : Fn)
    (hode : ∀ y ∈ Sx, (1 - y ^ 2) * deriv (deriv f.1) y - 2 * y * deriv f.1 y +
      (lam - (S - 2 * t * y) / (1 - y ^ 2)) * f.1 y = 0) : Hop S t f = lam • f := by
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · rw [Hop_apply S t f hy]
    have hd2 : DifferentiableAt ℝ (deriv f.1) y := (f.contDiffOn_deriv.differentiableOn (by simp)).differentiableAt
      (isOpen_Sx.mem_nhds hy)
    have hprod : HasDerivAt (fun z => (1 - z ^ 2) * deriv f.1 z)
        ((-(2 * y)) * deriv f.1 y + (1 - y ^ 2) * deriv (deriv f.1) y) y := by
      have hq : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-(2 * y)) y := by
        have := (hasDerivAt_const y (1 : ℝ)).sub (hasDerivAt_pow 2 y)
        convert this using 1; simp
      exact hq.mul hd2.hasDerivAt
    rw [hprod.deriv]
    have := hode y hy
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
    linear_combination (-1 : ℝ) * this
  · have h0 : (Hop S t f).1 y = 0 := by
      simp only [Hop, LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply, Module.End.mul_apply,
        DOp_apply_off _ hy, mV, mulOp_apply, Fn.zero_off _ hy]
    rw [h0]
    simp [Fn.zero_off _ hy]

/-! ### Wigner functions -/

lemma contDiffOn_wigner (L M σ : ℚ) : ContDiffOn ℝ ∞ (wignerSmallDx L M σ) Sx := by
  intro y hy
  have h1 : ContDiffAt ℝ ∞ Real.arccos y :=
    Real.contDiffAt_arccos (by linarith [hy.1]) (by linarith [hy.2])
  exact ((wignerSmallD_contDiff L M σ (n := ∞)).contDiffAt.comp y h1).contDiffWithinAt

/-- `d^L_{Mσ}(arccos x)` as an element of `Fn` (zero outside `(-1,1)`). -/
noncomputable def wigF (L M σ : ℚ) : Fn :=
  ⟨fun y => if y ∈ Sx then wignerSmallDx L M σ y else 0, fun y hy => by simp only [hy, ↓reduceIte],
    (contDiffOn_wigner L M σ).congr fun y hy => by simp only [hy, ↓reduceIte]⟩

lemma wigF_apply (L M σ : ℚ) {y : ℝ} (hy : y ∈ Sx) : (wigF L M σ).1 y = wignerSmallDx L M σ y := by
  show (if y ∈ Sx then _ else _) = _
  simp only [hy, ↓reduceIte]

lemma wigF_eventually (L M σ : ℚ) {y : ℝ} (hy : y ∈ Sx) :
    (wigF L M σ).1 =ᶠ[nhds y] wignerSmallDx L M σ := by
  filter_upwards [isOpen_Sx.mem_nhds hy] with z hz
  exact wigF_apply L M σ hz

lemma deriv_wigF (L M σ : ℚ) {y : ℝ} (hy : y ∈ Sx) :
    deriv (wigF L M σ).1 y = deriv (wignerSmallDx L M σ) y :=
  (wigF_eventually L M σ hy).deriv_eq

lemma deriv_deriv_wigF (L M σ : ℚ) {y : ℝ} (hy : y ∈ Sx) :
    deriv (deriv (wigF L M σ).1) y = deriv (deriv (wignerSmallDx L M σ)) y := by
  have : deriv (wigF L M σ).1 =ᶠ[nhds y] deriv (wignerSmallDx L M σ) := by
    filter_upwards [isOpen_Sx.mem_nhds hy] with z hz
    exact deriv_wigF L M σ hz
  exact this.deriv_eq

/-- **`𝖧₀ d^L_{Mσ} = L(L+1) d^L_{Mσ}`** (`eq:H0`, `eq:dODE`), for `Σ = M²+σ²`, `τ = Mσ`. -/
theorem Hop_wigF (L M σ : ℚ) :
    Hop ((M : ℝ) ^ 2 + (σ : ℝ) ^ 2) ((M : ℝ) * σ) (wigF L M σ) =
      LocalCalculus.lam (L : ℝ) • wigF L M σ := by
  refine Hop_eq_smul _ _ _ _ fun y hy => ?_
  rw [deriv_deriv_wigF L M σ hy, deriv_wigF L M σ hy, wigF_apply L M σ hy]
  have := wignerSmallDx_ode L M σ hy
  unfold LocalCalculus.lam
  linear_combination this

/-- **The Wigner rank recurrence in `Fn`**:
`(2j+1)(λ_j x d_j - Mσ d_j) = j R_{j+1} d_{j+1} + (j+1) R_j d_{j-1}`. -/
theorem wigF_rank (j M σ : ℚ) :
    (2 * (j : ℝ) + 1) • (LocalCalculus.lam (j : ℝ) • xOp (wigF j M σ) - ((M : ℝ) * σ) • wigF j M σ) =
      ((j : ℝ) * wigR (j + 1) M σ) • wigF (j + 1) M σ +
        (((j : ℝ) + 1) * wigR j M σ) • wigF (j - 1) M σ := by
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · have h := wignerSmallDx_rank_rec j M σ ⟨hy.1.le, hy.2.le⟩
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sub, Pi.add_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul, xOp, mulOp_apply, wigF_apply _ M σ hy]
    unfold LocalCalculus.lam
    linear_combination h
  · simp [Fn.zero_off _ hy, xOp]

end FormalResearch.Racah.LocalCalculus.Fun

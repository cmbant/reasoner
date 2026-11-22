module

public import Mathlib
public import DLMFMathlib.Analysis.ODE.LinearGlobal
public import FormalResearch.JacobiEigenvectors.Engine.Defect

/-!
# Paper J, charts (WP1a shared helper): global `2 × 2` fundamental matrix for `y'' = q(s) y`

Builds the `2 × 2` fundamental solution matrix `odeFund q hq t₀ s : Matrix (Fin 2) (Fin 2) ℝ`
for the second-order ODE `y'' = q(s) y` (continuous `q : ℝ → ℝ`) with `odeFund q hq t₀ t₀ = 1`
using `ODE.exists_linear_ode` and `ODE.eq_of_linear_ode` (`DLMFMathlib/Analysis/ODE/`).

Used by both `Charts/WeberLadder.lean` (`lem:cha-weber-ladder`) and `Charts/PCLadder.lean` (`eq:cha-PC`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.Charts

open FormalResearch.JacobiEigenvectors.Engine

lemma exists_second_order_ode (q : ℝ → ℝ) (hq : Continuous q) (t₀ y₀ y₁ : ℝ) :
    ∃ f f' : ℝ → ℝ, f t₀ = y₀ ∧ f' t₀ = y₁ ∧
      ∀ s, HasDerivAt f (f' s) s ∧ HasDerivAt f' (q s * f s) s := by
  obtain ⟨f, f', h0, h1, hode⟩ :=
    ODE.exists_linear_ode (𝕜 := ℝ) (E := ℝ) (p := fun _ => (0 : ℝ)) continuous_const hq t₀ y₀ y₁
  refine ⟨f, f', h0, h1, fun s => ⟨(hode s).1, ?_⟩⟩
  simpa using (hode s).2

def odeFundCol0 (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) : ℝ → ℝ :=
  Classical.choose (exists_second_order_ode q hq t₀ 1 0)

def odeFundCol0' (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (exists_second_order_ode q hq t₀ 1 0))

def odeFundCol1 (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) : ℝ → ℝ :=
  Classical.choose (exists_second_order_ode q hq t₀ 0 1)

def odeFundCol1' (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) : ℝ → ℝ :=
  Classical.choose (Classical.choose_spec (exists_second_order_ode q hq t₀ 0 1))

/-- Fundamental solution matrix of `y'' = q(s) y` on `ℝ`, normalized to `1` at `t₀`. -/
def odeFund (q : ℝ → ℝ) (hq : Continuous q) (t₀ s : ℝ) : M2 :=
  !![odeFundCol0 q hq t₀ s, odeFundCol1 q hq t₀ s; odeFundCol0' q hq t₀ s, odeFundCol1' q hq t₀ s]

private lemma odeFund_col0_spec (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) :
    odeFundCol0 q hq t₀ t₀ = 1 ∧ odeFundCol0' q hq t₀ t₀ = 0 ∧
      ∀ s, HasDerivAt (odeFundCol0 q hq t₀) (odeFundCol0' q hq t₀ s) s ∧
        HasDerivAt (odeFundCol0' q hq t₀) (q s * odeFundCol0 q hq t₀ s) s :=
  Classical.choose_spec (Classical.choose_spec (exists_second_order_ode q hq t₀ 1 0))

private lemma odeFund_col1_spec (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) :
    odeFundCol1 q hq t₀ t₀ = 0 ∧ odeFundCol1' q hq t₀ t₀ = 1 ∧
      ∀ s, HasDerivAt (odeFundCol1 q hq t₀) (odeFundCol1' q hq t₀ s) s ∧
        HasDerivAt (odeFundCol1' q hq t₀) (q s * odeFundCol1 q hq t₀ s) s :=
  Classical.choose_spec (Classical.choose_spec (exists_second_order_ode q hq t₀ 0 1))

@[simp]
lemma odeFund_self (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) :
    odeFund q hq t₀ t₀ = 1 := by
  have c0 := odeFund_col0_spec q hq t₀
  have c1 := odeFund_col1_spec q hq t₀
  ext i j
  fin_cases i <;> fin_cases j <;> simp [odeFund, c0.1, c0.2.1, c1.1, c1.2.1]

lemma odeFund_hasDerivAt (q : ℝ → ℝ) (hq : Continuous q) (t₀ : ℝ) (j : Fin 2) (s : ℝ) :
    HasDerivAt (fun t => odeFund q hq t₀ t 0 j) (odeFund q hq t₀ s 1 j) s ∧
      HasDerivAt (fun t => odeFund q hq t₀ t 1 j) (q s * odeFund q hq t₀ s 0 j) s := by
  fin_cases j
  · exact (odeFund_col0_spec q hq t₀).2.2 s
  · exact (odeFund_col1_spec q hq t₀).2.2 s

/-- Any solution `(y, y')` of `y'' = q y` satisfies `(y s, y' s)ᵀ = odeFund q hq t₀ s *ᵥ (y t₀, y' t₀)ᵀ`. -/
theorem odeFund_mulVec {q : ℝ → ℝ} (hq : Continuous q) (t₀ : ℝ) {y y' : ℝ → ℝ}
    (hy : ∀ s, HasDerivAt y (y' s) s ∧ HasDerivAt y' (q s * y s) s) (s : ℝ) :
    ![y s, y' s] = colMul (odeFund q hq t₀ s) ![y t₀, y' t₀] := by
  have c0 := odeFund_col0_spec q hq t₀
  have c1 := odeFund_col1_spec q hq t₀
  let f1 := odeFundCol0 q hq t₀
  let f1' := odeFundCol0' q hq t₀
  let f2 := odeFundCol1 q hq t₀
  let f2' := odeFundCol1' q hq t₀
  let g : ℝ → ℝ := fun t => y t₀ * f1 t + y' t₀ * f2 t
  let g' : ℝ → ℝ := fun t => y t₀ * f1' t + y' t₀ * f2' t
  have hg : ∀ t, HasDerivAt g (g' t) t ∧ HasDerivAt g' ((0 : ℝ) • g' t + q t • g t) t := by
    intro t
    have h0t := c0.2.2 t
    have h1t := c1.2.2 t
    constructor
    · exact (h0t.1.const_mul (y t₀)).add (h1t.1.const_mul (y' t₀))
    · have hsum := (h0t.2.const_mul (y t₀)).add (h1t.2.const_mul (y' t₀))
      refine hsum.congr_deriv ?_
      change y t₀ * (q t * f1 t) + y' t₀ * (q t * f2 t) = (0 : ℝ) • g' t + q t • g t
      simp only [smul_eq_mul, g]; ring
  have hy' : ∀ t, HasDerivAt y (y' t) t ∧ HasDerivAt y' ((0 : ℝ) • y' t + q t • y t) t := fun t =>
    ⟨(hy t).1, by simpa using (hy t).2⟩
  have huniq := ODE.eq_of_linear_ode (𝕜 := ℝ) (E := ℝ) (p := fun _ => (0 : ℝ)) continuous_const hq hg hy'
    (t₀ := t₀) (by simp [g, f1, f2, c0.1, c1.1]) (by simp [g', f1', f2', c0.2.1, c1.2.1])
  have hg_s : g s = y s := congrFun huniq.1 s
  have hg'_s : g' s = y' s := congrFun huniq.2 s
  ext i
  fin_cases i
  · simp [colMul, odeFund, ← hg_s, g, f1, f2]; ring
  · simp [colMul, odeFund, ← hg'_s, g', f1', f2']; ring

/-- `odeFund` has determinant `1` everywhere. -/
theorem odeFund_det (q : ℝ → ℝ) (hq : Continuous q) (t₀ s : ℝ) :
    (odeFund q hq t₀ s).det = 1 := by
  have c0 := odeFund_col0_spec q hq t₀
  have c1 := odeFund_col1_spec q hq t₀
  let f1 := odeFundCol0 q hq t₀
  let f1' := odeFundCol0' q hq t₀
  let f2 := odeFundCol1 q hq t₀
  let f2' := odeFundCol1' q hq t₀
  let W : ℝ → ℝ := fun t => f1 t * f2' t - f2 t * f1' t
  have hWd : ∀ t, HasDerivAt W 0 t := fun t => by
    have h0t := c0.2.2 t
    have h1t := c1.2.2 t
    have hw := (h0t.1.mul h1t.2).sub (h1t.1.mul h0t.2)
    exact hw.congr_deriv (by ring)
  have hconst : W s = W t₀ := is_const_of_deriv_eq_zero (fun t => (hWd t).differentiableAt)
    (fun t => (hWd t).deriv) s t₀
  have hW0 : W t₀ = 1 := by simp [W, f1, f1', f2, f2', c0.1, c0.2.1, c1.1, c1.2.1]
  rw [hW0] at hconst
  simpa [odeFund, Matrix.det_fin_two, W, f1, f1', f2, f2'] using hconst

/-- Matrix uniqueness: if both columns of `M(s)` solve `y'' = q(s) y`, then
`M(s) = odeFund q hq t₀ s * M(t₀)`. -/
theorem odeFund_right_mul {q : ℝ → ℝ} (hq : Continuous q) (t₀ : ℝ) {M : ℝ → M2}
    (hM : ∀ (j : Fin 2) (s : ℝ),
      HasDerivAt (fun t => M t 0 j) (M s 1 j) s ∧ HasDerivAt (fun t => M t 1 j) (q s * M s 0 j) s)
    (s : ℝ) : M s = odeFund q hq t₀ s * M t₀ := by
  have col_eq : ∀ j : Fin 2, ![M s 0 j, M s 1 j] = colMul (odeFund q hq t₀ s) ![M t₀ 0 j, M t₀ 1 j] :=
    fun j => odeFund_mulVec hq t₀ (hM j) s
  ext i j
  have hi := congrFun (col_eq j) i
  fin_cases i <;> simp only [colMul, Matrix.mul_apply, Fin.sum_univ_two] at hi ⊢ <;> exact hi

/-- Reversal symmetry (SM3): if `q₁(-s) = q₂(s)`, then `Sg * odeFund q₂ hq₂ 0 s * Sg = odeFund q₁ hq₁ 0 (-s)`. -/
theorem odeFund_conj_sg {q₁ q₂ : ℝ → ℝ} (hq₁ : Continuous q₁) (hq₂ : Continuous q₂)
    (heq : ∀ s, q₁ (-s) = q₂ s) (s : ℝ) :
    Sg * odeFund q₂ hq₂ 0 s * Sg = odeFund q₁ hq₁ 0 (-s) := by
  let M : ℝ → M2 := fun t => Sg * odeFund q₁ hq₁ 0 (-t) * Sg
  have c0 := odeFund_col0_spec q₁ hq₁ 0
  have c1 := odeFund_col1_spec q₁ hq₁ 0
  let f1 := odeFundCol0 q₁ hq₁ 0
  let f1' := odeFundCol0' q₁ hq₁ 0
  let f2 := odeFundCol1 q₁ hq₁ 0
  let f2' := odeFundCol1' q₁ hq₁ 0
  have hM : ∀ (j : Fin 2) (t : ℝ),
      HasDerivAt (fun u => M u 0 j) (M t 1 j) t ∧ HasDerivAt (fun u => M u 1 j) (q₂ t * M t 0 j) t := by
    intro j t
    have e00' : (fun u => M u 0 0) = fun u => f1 (-u) := funext fun u => by
      simpa [M, odeFund, f1] using (sg_conj_entries (odeFund q₁ hq₁ 0 (-u))).1
    have e10' : (fun u => M u 1 0) = fun u => -f1' (-u) := funext fun u => by
      simpa [M, odeFund, f1'] using (sg_conj_entries (odeFund q₁ hq₁ 0 (-u))).2.2.1
    have e01' : (fun u => M u 0 1) = fun u => -f2 (-u) := funext fun u => by
      simpa [M, odeFund, f2] using (sg_conj_entries (odeFund q₁ hq₁ 0 (-u))).2.1
    have e11' : (fun u => M u 1 1) = fun u => f2' (-u) := funext fun u => by
      simpa [M, odeFund, f2'] using (sg_conj_entries (odeFund q₁ hq₁ 0 (-u))).2.2.2
    have hneg := (hasDerivAt_id t).neg
    fin_cases j
    · change HasDerivAt (fun u => M u 0 0) (M t 1 0) t ∧ HasDerivAt (fun u => M u 1 0) (q₂ t * M t 0 0) t
      rw [e00', e10']
      have d1 := (c0.2.2 (-t)).1.comp t hneg
      have d2 := ((c0.2.2 (-t)).2.comp t hneg).neg
      refine ⟨d1.congr_deriv (by rw [congrFun e10' t]; ring), d2.congr_deriv ?_⟩
      rw [congrFun e00' t, ← heq t]; ring
    · change HasDerivAt (fun u => M u 0 1) (M t 1 1) t ∧ HasDerivAt (fun u => M u 1 1) (q₂ t * M t 0 1) t
      rw [e01', e11']
      have d1 := ((c1.2.2 (-t)).1.comp t hneg).neg
      have d2 := (c1.2.2 (-t)).2.comp t hneg
      refine ⟨d1.congr_deriv (by rw [congrFun e11' t]; ring), d2.congr_deriv ?_⟩
      rw [congrFun e01' t, ← heq t]; ring
  have huniq := odeFund_right_mul hq₂ 0 hM s
  have hM0 : M 0 = 1 := by
    simp only [M, neg_zero, odeFund_self, Matrix.mul_one]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hM0, Matrix.mul_one] at huniq
  have hSg : Sg * Sg = (1 : M2) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Sg, Matrix.mul_apply, Fin.sum_univ_two]
  calc Sg * odeFund q₂ hq₂ 0 s * Sg
      = Sg * M s * Sg := by rw [← huniq]
    _ = (Sg * Sg) * odeFund q₁ hq₁ 0 (-s) * (Sg * Sg) := by simp only [M, Matrix.mul_assoc]
    _ = odeFund q₁ hq₁ 0 (-s) := by rw [hSg, Matrix.one_mul, Matrix.mul_one]

/-- Shift reparametrization: if `q₂(t) = q₁(t + δ)` for all `t`, then
`odeFund q₁ hq₁ 0 (s + δ) = odeFund q₂ hq₂ 0 s * odeFund q₁ hq₁ 0 δ`. -/
theorem odeFund_shift {q₁ q₂ : ℝ → ℝ} (hq₁ : Continuous q₁) (hq₂ : Continuous q₂)
    (δ : ℝ) (heq : ∀ t, q₂ t = q₁ (t + δ)) (s : ℝ) :
    odeFund q₁ hq₁ 0 (s + δ) = odeFund q₂ hq₂ 0 s * odeFund q₁ hq₁ 0 δ := by
  let M : ℝ → M2 := fun t => odeFund q₁ hq₁ 0 (t + δ)
  have c0 := odeFund_col0_spec q₁ hq₁ 0
  have c1 := odeFund_col1_spec q₁ hq₁ 0
  let f1 := odeFundCol0 q₁ hq₁ 0
  let f1' := odeFundCol0' q₁ hq₁ 0
  let f2 := odeFundCol1 q₁ hq₁ 0
  let f2' := odeFundCol1' q₁ hq₁ 0
  have hM : ∀ (j : Fin 2) (t : ℝ),
      HasDerivAt (fun u => M u 0 j) (M t 1 j) t ∧ HasDerivAt (fun u => M u 1 j) (q₂ t * M t 0 j) t := by
    intro j t
    have hshift : HasDerivAt (fun u : ℝ => u + δ) 1 t := (hasDerivAt_id t).add_const δ
    fin_cases j
    · change HasDerivAt (fun u => M u 0 0) (M t 1 0) t ∧ HasDerivAt (fun u => M u 1 0) (q₂ t * M t 0 0) t
      refine ⟨?_, ?_⟩
      · have d1 := (c0.2.2 (t + δ)).1.comp t hshift
        simpa [M, odeFund, f1, f1', Function.comp_def] using d1
      · have d2 := (c0.2.2 (t + δ)).2.comp t hshift
        simpa [M, odeFund, heq t, f1, f1', Function.comp_def] using d2
    · change HasDerivAt (fun u => M u 0 1) (M t 1 1) t ∧ HasDerivAt (fun u => M u 1 1) (q₂ t * M t 0 1) t
      refine ⟨?_, ?_⟩
      · have d1 := (c1.2.2 (t + δ)).1.comp t hshift
        simpa [M, odeFund, f2, f2', Function.comp_def] using d1
      · have d2 := (c1.2.2 (t + δ)).2.comp t hshift
        simpa [M, odeFund, heq t, f2, f2', Function.comp_def] using d2
  simpa [M, zero_add] using odeFund_right_mul hq₂ 0 hM s

/-- Specialization of `odeFund_shift` at `s = -δ`:
`odeFund q₂ hq₂ 0 (-δ) * odeFund q₁ hq₁ 0 δ = 1`. -/
theorem odeFund_shift_mul_cancel {q₁ q₂ : ℝ → ℝ} (hq₁ : Continuous q₁) (hq₂ : Continuous q₂)
    (δ : ℝ) (heq : ∀ t, q₂ t = q₁ (t + δ)) :
    odeFund q₂ hq₂ 0 (-δ) * odeFund q₁ hq₁ 0 δ = 1 := by
  have h := odeFund_shift hq₁ hq₂ δ heq (-δ)
  rw [neg_add_cancel, odeFund_self] at h
  exact h.symm

/-- ODE propagation along a rescaled parabolic-cylinder equation `f''(z) = (z²/4 + a) f(z)`:
for `0 < h` and `v = -a * h`, the fundamental matrix of `y''(s) = ((Z₀ + h s)²/4 - v) y(s)` over
`s = (Z₁ - Z₀) / h` transports `![f (Z₀ / √h), √h * deriv f (Z₀ / √h)]` to
`![f (Z₁ / √h), √h * deriv f (Z₁ / √h)]`. -/
theorem odeFund_pc_step {h a v Z₀ Z₁ : ℝ} (hh : 0 < h) (hv : v = -a * h) {f : ℝ → ℝ}
    (hf : ∀ z, HasDerivAt f (deriv f z) z)
    (hode : ∀ z, HasDerivAt (deriv f) ((z ^ 2 / 4 + a) * f z) z) :
    ![f (Z₁ / Real.sqrt h), Real.sqrt h * deriv f (Z₁ / Real.sqrt h)] =
      colMul (odeFund (fun t => (Z₀ + h * t) ^ 2 / 4 - v) (by fun_prop) 0 ((Z₁ - Z₀) / h))
        ![f (Z₀ / Real.sqrt h), Real.sqrt h * deriv f (Z₀ / Real.sqrt h)] := by
  have hs_pos : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
  let scale : ℝ → ℝ := fun t => (Z₀ + h * t) / Real.sqrt h
  have hscale_deriv : ∀ t, HasDerivAt scale (Real.sqrt h) t := fun t => by
    have hd : HasDerivAt (fun t : ℝ => Z₀ + h * t) h t := by
      simpa using ((hasDerivAt_id t).const_mul h).const_add Z₀
    refine (hd.div_const (Real.sqrt h)).congr_deriv ?_
    calc h / Real.sqrt h = (Real.sqrt h * Real.sqrt h) / Real.sqrt h := by rw [Real.mul_self_sqrt hh.le]
      _ = Real.sqrt h := mul_div_cancel_right₀ _ hs_pos.ne'
  let y : ℝ → ℝ := fun t => f (scale t)
  let y' : ℝ → ℝ := fun t => Real.sqrt h * deriv f (scale t)
  have hy : ∀ t, HasDerivAt y (y' t) t ∧ HasDerivAt y' (((Z₀ + h * t) ^ 2 / 4 - v) * y t) t := by
    intro t
    refine ⟨?_, ?_⟩
    · refine ((hf (scale t)).comp t (hscale_deriv t)).congr_deriv ?_
      dsimp [y']; ring
    · have hcomp := ((hode (scale t)).comp t (hscale_deriv t)).const_mul (Real.sqrt h)
      refine hcomp.congr_deriv ?_
      have hsq : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
      have hsc_sq : scale t ^ 2 = (Z₀ + h * t) ^ 2 / h := by
        dsimp [scale]; rw [div_pow, Real.sq_sqrt hh.le]
      dsimp [y]; rw [hsc_sq, hv]
      calc Real.sqrt h * (((Z₀ + h * t) ^ 2 / h / 4 + a) * f (scale t) * Real.sqrt h)
          = (Real.sqrt h * Real.sqrt h) * ((Z₀ + h * t) ^ 2 / h / 4 + a) * f (scale t) := by ring
        _ = h * ((Z₀ + h * t) ^ 2 / h / 4 + a) * f (scale t) := by rw [hsq]
        _ = ((Z₀ + h * t) ^ 2 / 4 - (-a * h)) * f (scale t) := by field_simp [hh.ne']; ring
  have hmv := odeFund_mulVec (by fun_prop) (0 : ℝ) hy ((Z₁ - Z₀) / h)
  have hs0 : scale 0 = Z₀ / Real.sqrt h := by dsimp [scale]; ring
  have hs1 : scale ((Z₁ - Z₀) / h) = Z₁ / Real.sqrt h := by
    dsimp [scale]; field_simp [hh.ne']; ring
  simpa only [y, y', hs0, hs1] using hmv

end FormalResearch.JacobiEigenvectors.Charts

end

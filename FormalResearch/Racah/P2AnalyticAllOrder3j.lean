module

public import Mathlib
public import FormalResearch.Racah.P2LocalCalculusWigner
public import FormalResearch.Racah.P2AnalyticAllOrder3jSeries

/-!
# All-order local calculus for the `3j` kernel: the operators `𝒢_{2r}` (Weyl P2, `thm:3jallorderlocal`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jallorderlocal`, `app:localgeneral`
(`prop:localcalculus`), `eq:3jB2r`, `eq:3jD2rrecursive`, `eq:3jpsi2r`, the `3j` instance
(`eq:3jrank`, `eq:3jrankpoly`, `eq:3jclosedform`).

For `M ± σ` integers (the integrality of the physical lattice, `SpecAdm`) and the Wigner functions
`d_n = d^{L₀+n}_{Mσ}(arccos x)` (`dv`), this file connects the abstract local calculus
(`P2LocalCalculusLeftNormal`, in the concrete module `Fn` of `P2LocalCalculusFun`) with the Taylor
coefficients `f_{2r}^{(n)}` of the exact germ (`P2AnalyticAllOrder3jSeries`):

* `allorder_operators`: there are left-normal differential operators `𝒢_r` (`r = 0, 1, …`, the paper's
  `𝒢_{2r} = t^{-r}`-coefficients `D̂_{2r}`), `𝒢_0 = 1`, with `[x, 𝒢_{r+1}] = 𝖡_{r+1}` (`eq:3jB2r`, `q = 0`,
  `e_s = c_s`, `√(1-z) = ∑ c_s z^s`), each `𝒢_r` a sum `∑ b_j(x) ∂_x^j` with coefficients smooth on
  `(-1,1)` (`LN DOp Csm`), such that for every rank `n`, every order `r` and every `x ∈ (-1,1)`
  `f_{2r}^{(n)}(x) = (𝒢_r d_n)(x)`, i.e. `Φ_L = ∑_r t^r 𝒢_r d_L` as formal series
  (`thm:3jallorderlocal`, the identification step; the operators do not depend on the rank).

The whole chain is formalised: forward uniqueness of the rank recurrence, the exact algebra of
`prop:localcalculus`, the Taylor coefficients of the closed form as formal series, and the Wigner ODE
and rank recurrence.  See the docstrings of `allorder_operators` and `threeJ_allorder_local` for what is
*not* formalised (the explicit multipliers `ψ_{2r}` and their rationality, `D̂_2`, `D̂_4` in closed form).
-/

@[expose] public section

namespace FormalResearch.Racah.LocalCalculus.Fun

open Set Module FormalResearch.Wigner FormalResearch.Racah
open scoped ContDiff

section Setup

variable (M σ : ℚ)

/-- The Wigner vector `d_n = d^{L₀+n}_{Mσ}(arccos x)` of rank index `n` (`L₀ = max(|M|,|σ|)`). -/
noncomputable def dv (n : ℕ) : Fn := wigF (max |M| |σ| + (n : ℚ)) M σ

/-- `Σ = M² + σ²`. -/
noncomputable def SigM : ℝ := (M : ℝ) ^ 2 + (σ : ℝ) ^ 2

/-- `τ = Mσ`. -/
noncomputable def TauM : ℝ := (M : ℝ) * σ

/-- `R_n = R_{L₀+n}`. -/
noncomputable def Rn (n : ℕ) : ℝ := Rk M σ (max |M| |σ| + (n : ℚ))

/-- `k₀ = L₀`. -/
noncomputable def kz : ℝ := ((max |M| |σ| : ℚ) : ℝ)

lemma cast_rank (n : ℕ) : (((max |M| |σ| + (n : ℚ) : ℚ)) : ℝ) = kz M σ + n := by
  unfold kz; push_cast; ring

lemma Rn_zero : Rn M σ 0 = 0 := by
  unfold Rn; simpa using Rk_L0 M σ

theorem Hop_dv (n : ℕ) :
    Hop (SigM M σ) (TauM M σ) (dv M σ n) = LocalCalculus.lam (kz M σ + n) • dv M σ n := by
  have := Hop_wigF (max |M| |σ| + (n : ℚ)) M σ
  rw [cast_rank] at this
  exact this

/-- The Wigner rank recurrence for the vectors `d_n` (with `d_{-1} = 0`, `R_0 = 0`). -/
theorem dv_rec (n : ℕ) :
    ((kz M σ + n) * Rn M σ (n + 1)) • dv M σ (n + 1) +
        ((kz M σ + n + 1) * Rn M σ n) • LocalCalculus.prevV (dv M σ) n =
      (2 * (kz M σ + n) + 1) • (LocalCalculus.lam (kz M σ + n) • xOp (dv M σ n) -
        TauM M σ • dv M σ n) := by
  have h := wigF_rank (max |M| |σ| + (n : ℚ)) M σ
  rw [cast_rank] at h
  have e1 : max |M| |σ| + (n : ℚ) + 1 = max |M| |σ| + ((n + 1 : ℕ) : ℚ) := by push_cast; ring
  have hR : wigR (max |M| |σ| + (n : ℚ) + 1) M σ = Rn M σ (n + 1) := by
    rw [e1, wigR_eq_Rk]; rfl
  have hR' : wigR (max |M| |σ| + (n : ℚ)) M σ = Rn M σ n := by
    rw [wigR_eq_Rk]; rfl
  rw [hR, hR', e1] at h
  cases n with
  | zero =>
    have h0 : Rn M σ 0 = 0 := Rn_zero M σ
    simp only [LocalCalculus.prevV, smul_zero, add_zero]
    rw [h0, mul_zero, zero_smul, add_zero] at h
    unfold TauM
    simpa [dv] using h.symm
  | succ n =>
    have e2 : max |M| |σ| + ((n + 1 : ℕ) : ℚ) - 1 = max |M| |σ| + (n : ℚ) := by push_cast; ring
    rw [e2] at h
    simp only [LocalCalculus.prevV]
    unfold TauM
    simpa [dv] using h.symm


/-! ### The extremal vector `d₀` -/

lemma seed3_ne_zero (M σ : ℚ) : seed3 M σ ≠ 0 := by
  unfold seed3
  refine mul_ne_zero (by split_ifs <;> simp) (Real.sqrt_ne_zero'.mpr (by positivity))

variable {M σ : ℚ} {α β : ℕ}

lemma dv_zero_apply (hα : |M - σ| = α) (hβ : |M + σ| = β) {y : ℝ} (hy : y ∈ Sx) :
    (dv M σ 0).1 y = seed3 M σ * Real.sqrt (((1 - y) / 2) ^ pPlus3 M σ * ((1 + y) / 2) ^ pMinus3 M σ) := by
  have h := dZero3_eq_wignerD M σ α β hα hβ (x := y) ⟨hy.1.le, hy.2.le⟩ 0
  rw [dZero3_zero] at h
  unfold dv
  rw [wigF_apply _ M σ hy]
  simpa using h.symm

lemma dv_zero_ne_zero (hα : |M - σ| = α) (hβ : |M + σ| = β) {y : ℝ} (hy : y ∈ Sx) :
    (dv M σ 0).1 y ≠ 0 := by
  rw [dv_zero_apply hα hβ hy]
  refine mul_ne_zero (seed3_ne_zero M σ) (Real.sqrt_ne_zero'.mpr ?_)
  have h1 : 0 < (1 - y) / 2 := by linarith [hy.2]
  have h2 : 0 < (1 + y) / 2 := by linarith [hy.1]
  positivity

lemma contDiffOn_div_dv0 (hα : |M - σ| = α) (hβ : |M + σ| = β) {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ ∞ g Sx) : ContDiffOn ℝ ∞ (fun y => g y / (dv M σ 0).1 y) Sx :=
  hg.div (dv M σ 0).2.2 fun y hy => dv_zero_ne_zero hα hβ hy

/-- The Wigner function `d₀` satisfies `∂ d₀ = w d₀` with `w = d₀'/d₀` smooth. -/
lemma DOp_dv_zero (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    DOp (dv M σ 0) = mulOp (fun y => deriv (dv M σ 0).1 y / (dv M σ 0).1 y)
      (contDiffOn_div_dv0 hα hβ (dv M σ 0).contDiffOn_deriv) (dv M σ 0) := by
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · rw [DOp_apply _ hy, mulOp_apply]
    have := dv_zero_ne_zero hα hβ hy
    field_simp
  · rw [DOp_apply_off _ hy, mulOp_apply, Fn.zero_off _ hy, mul_zero]

/-! ### The physical series as elements of `Fn` -/

/-- `f_{2r}^{(n)}` as an element of `Fn` (zero off `(-1,1)`). -/
noncomputable def physFn (M σ : ℚ) (n r : ℕ) : Fn :=
  ⟨fun y => if y ∈ Sx then f3even M σ n r y else 0, fun y hy => by simp only [hy, ↓reduceIte],
    ((analyticOnNhd_f3even M σ n r).contDiffOn isOpen_Sx.uniqueDiffOn).congr fun y hy => by simp only [hy, ↓reduceIte]⟩

lemma physFn_apply (n r : ℕ) {y : ℝ} (hy : y ∈ Sx) : (physFn M σ n r).1 y = f3even M σ n r y := by
  show (if y ∈ Sx then _ else _) = _
  simp only [hy, ↓reduceIte]

/-- Evaluation at a point of `(-1,1)`. -/
noncomputable def evAt (y : ℝ) : Fn →ₗ[ℝ] ℝ where
  toFun f := f.1 y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The physical series satisfy the rank recurrence in `Fn`.** -/
theorem physFn_rankDefect (hα : |M - σ| = α) (hβ : |M + σ| = β) (n : ℕ) :
    LocalCalculus.rankDefect (M := Fn) xOp (0 : Polynomial ℝ) c3 (TauM M σ) (kz M σ) (Rn M σ)
      (physFn M σ) n = 0 := by
  funext r
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · have hmap := LocalCalculus.rankDefect_map (evAt y) xOp (LinearMap.lsmul ℝ ℝ y)
      (fun v => rfl) (0 : Polynomial ℝ) c3 (TauM M σ) (kz M σ) (Rn M σ) (physFn M σ) n r
    have h := Gc3_rankDefect hα hβ hy n
    have e : (fun m s => evAt y (physFn M σ m s)) = fun m s => f3even M σ m s y := by
      funext m s; exact physFn_apply m s hy
    rw [e] at hmap
    have h2 := congrFun h r
    have key : evAt y (LocalCalculus.rankDefect (M := Fn) xOp (0 : Polynomial ℝ) c3 (TauM M σ) (kz M σ)
        (Rn M σ) (physFn M σ) n r) = 0 := by
      rw [hmap]
      exact h2
    exact key
  · rw [Fn.zero_off _ hy]
    rfl


lemma f3even_zero_zero_apply (hα : |M - σ| = α) (hβ : |M + σ| = β) {y : ℝ} (hy : y ∈ Sx) :
    f3even M σ 0 0 y = (dv M σ 0).1 y := by
  rw [f3even_zero, dZero3_eq_wignerD M σ α β hα hβ ⟨hy.1.le, hy.2.le⟩ 0]
  unfold dv
  rw [wigF_apply _ M σ hy]

/-- The multipliers `κ_r = f_{2r}^{(0)}/d₀` (`eq:3jpsi2r`). -/
noncomputable def kap (hα : |M - σ| = α) (hβ : |M + σ| = β) (r : ℕ) : End ℝ Fn :=
  mulOp (fun y => f3even M σ 0 r y / (dv M σ 0).1 y)
    (contDiffOn_div_dv0 hα hβ ((analyticOnNhd_f3even M σ 0 r).contDiffOn isOpen_Sx.uniqueDiffOn))

lemma kap_zero (hα : |M - σ| = α) (hβ : |M + σ| = β) : kap hα hβ 0 = 1 := by
  refine LinearMap.ext fun f => Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · show f3even M σ 0 0 y / (dv M σ 0).1 y * f.1 y = f.1 y
    rw [f3even_zero_zero_apply hα hβ hy, div_self (dv_zero_ne_zero hα hβ hy), one_mul]
  · show f3even M σ 0 0 y / (dv M σ 0).1 y * f.1 y = f.1 y
    rw [Fn.zero_off f hy, mul_zero]

lemma physFn_zero_eq_kap (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    physFn M σ 0 = fun r => kap hα hβ r (dv M σ 0) := by
  funext r
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · show _ = f3even M σ 0 r y / (dv M σ 0).1 y * (dv M σ 0).1 y
    rw [physFn_apply _ _ hy, div_mul_cancel₀ _ (dv_zero_ne_zero hα hβ hy)]
  · show _ = f3even M σ 0 r y / (dv M σ 0).1 y * (dv M σ 0).1 y
    rw [Fn.zero_off _ hy, Fn.zero_off _ hy, mul_zero]

/-- **`thm:3jallorderlocal`, the identification step** (case `L₀ > 0`, which includes all half-integer
labels).  See `allorder_operators`. -/
theorem allorder_operators_pos (hα : |M - σ| = α) (hβ : |M + σ| = β) (hL : 0 < max |M| |σ|) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r) ∧
      ∀ n r, ∀ y ∈ Sx, (G r (dv M σ n)).1 y = f3even M σ n r y := by
  have hk : 0 < kz M σ := by unfold kz; exact_mod_cast hL
  have hfwd : ∀ n : ℕ, (kz M σ + n) * Rn M σ (n + 1) ≠ 0 := by
    intro n
    have hR : 0 < Rn M σ (n + 1) := by
      unfold Rn
      refine Rk_pos M σ _ ?_
      have : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
      linarith
    have : 0 < kz M σ + n := by positivity
    exact (mul_pos this hR).ne'
  obtain ⟨G, hG0, hGm, hGB, hGκ, -, huniq⟩ := LocalCalculus.prop_localcalculus (D := DOp) (C := Csm)
    (x := xOp) DOp_xOp (fun c hc => comm_x_Csm hc) (fun c hc => comm_Csm hc) xOp_mem_Csm
    (Hop_mem_LN_sm (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 c3_zero (TauM M σ) (kz M σ) (Rn M σ)
    (Rn_zero M σ) hfwd (dv M σ) (Hop_dv M σ) (dv_rec M σ) (mulOp_mem_Csm _
      (contDiffOn_div_dv0 hα hβ (dv M σ 0).contDiffOn_deriv)) (DOp_dv_zero hα hβ) (kap hα hβ)
    (fun r => mulOp_mem_Csm _ _) (kap_zero hα hβ)
  have hu := huniq (physFn M σ) (physFn_rankDefect hα hβ) (physFn_zero_eq_kap hα hβ)
  refine ⟨G, hG0, hGm, hGB, fun n r y hy => ?_⟩
  have := congrFun (congrFun hu n) r
  rw [← physFn_apply (M := M) (σ := σ) n r hy, this]
  rfl

end Setup

end FormalResearch.Racah.LocalCalculus.Fun

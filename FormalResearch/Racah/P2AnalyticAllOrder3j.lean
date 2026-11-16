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


/-! ### The scalar case `M = σ = 0` (two starts) -/

lemma evAt_smulS (y : ℝ) (c : PowerSeries ℝ) (v : ℕ → Fn) (r : ℕ) :
    evAt y (LocalCalculus.smulS c v r) = LocalCalculus.smulS c (fun s => evAt y (v s)) r := by
  simp [LocalCalculus.smulS, map_sum]

lemma dv_zero_scalar_apply {y : ℝ} (hy : y ∈ Sx) : (dv 0 0 0).1 y = 1 := by
  have h := dv_zero_apply (M := 0) (σ := 0) (α := 0) (β := 0) (by simp) (by simp) hy
  rw [h]; simp [seed3, pPlus3, pMinus3]

lemma dv_one_scalar : dv 0 0 1 = xOp (dv 0 0 0) := by
  refine Fn.ext' fun y => ?_
  by_cases hy : y ∈ Sx
  · have h := dZero3_eq_wignerD 0 0 0 0 (by simp) (by simp) (x := y) ⟨hy.1.le, hy.2.le⟩ 1
    rw [dZero3_one_zero] at h
    show (wigF _ 0 0).1 y = y * (dv 0 0 0).1 y
    rw [wigF_apply _ 0 0 hy, dv_zero_scalar_apply hy, mul_one]
    simpa using h.symm
  · show (dv 0 0 1).1 y = y * (dv 0 0 0).1 y
    rw [Fn.zero_off _ hy, Fn.zero_off _ hy, mul_zero]

lemma f3even_zero_zero_pos (r : ℕ) (hr : 1 ≤ r) (y : ℝ) : f3even 0 0 0 r y = 0 := by
  rw [f3even_eq_coeff, show taylorSer (Gc3 0 0 0 y) = Psi 0 0 0 y from rfl, Psi_zero_zero_zero]
  simp [PowerSeries.coeff_one, show r ≠ 0 by omega]

/-- **`thm:3jallorderlocal`, the identification step, scalar case `M = σ = 0`** (two exact starts,
`prop:localcalculus` (c)). -/
theorem allorder_operators_zero :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 (TauM 0 0) G r) ∧
      ∀ n r, ∀ y ∈ Sx, (G r (dv 0 0 n)).1 y = f3even 0 0 n r y := by
  have hα : |(0 : ℚ) - 0| = ((0 : ℕ) : ℚ) := by simp
  have hβ : |(0 : ℚ) + 0| = ((0 : ℕ) : ℚ) := by simp
  obtain ⟨G, hG0, hGm, hGB, hGκ, -⟩ := LocalCalculus.local_calculus_start (D := DOp) (C := Csm)
    (x := xOp) DOp_xOp (fun c hc => comm_x_Csm hc) (fun c hc => comm_Csm hc) xOp_mem_Csm
    (Hop_mem_LN_sm (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 (TauM 0 0) (d0 := dv 0 0 0)
    (mulOp_mem_Csm _ (contDiffOn_div_dv0 hα hβ (dv 0 0 0).contDiffOn_deriv)) (DOp_dv_zero hα hβ)
    (kap hα hβ) (fun r => mulOp_mem_Csm _ _) (kap_zero hα hβ)
  -- `𝒢_{r+1} d₀ = 0`
  have hGz : ∀ r, G (r + 1) (dv 0 0 0) = 0 := by
    intro r
    rw [hGκ (r + 1)]
    refine Fn.ext' fun y => ?_
    show f3even 0 0 0 (r + 1) y / (dv 0 0 0).1 y * (dv 0 0 0).1 y = (0 : Fn).1 y
    rw [f3even_zero_zero_pos (r + 1) (by omega), zero_div, zero_mul]
    rfl
  have hk : kz 0 0 = 0 := by simp [kz]
  have hτ : TauM 0 0 = 0 := by simp [TauM]
  have hd0 : Hop (SigM 0 0) (TauM 0 0) (dv 0 0 0) = 0 := by
    rw [Hop_dv]; simp [hk, LocalCalculus.lam]
  have hd1 : Hop (SigM 0 0) (TauM 0 0) (xOp (dv 0 0 0)) = (2 : ℝ) • xOp (dv 0 0 0) := by
    rw [← dv_one_scalar, Hop_dv]; simp [hk, LocalCalculus.lam]; norm_num
  have hGB' : ∀ r, comm xOp (G (r + 1)) =
      Bop xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3 0 G r := by
    intro r; rw [hGB r]; unfold LocalCalculus.Bop; rw [hτ]
  have hstart := LocalCalculus.scalar_start_series xOp (Hop (SigM 0 0) (TauM 0 0)) (0 : Polynomial ℝ) c3
    c3_zero G hG0 (dv 0 0 0) hd0 hd1 hGz hGB'
  -- the physical second start
  have hphys : LocalCalculus.smulS (LocalCalculus.eta c3 1) (fun r => physFn 0 0 1 r) =
      LocalCalculus.smulS (LocalCalculus.eta c3 1) (LocalCalculus.serG G (xOp (dv 0 0 0))) := by
    rw [hstart]
    funext r
    refine Fn.ext' fun y => ?_
    by_cases hy : y ∈ Sx
    · have h1 := congrArg (PowerSeries.coeff r) (Psi_zero_zero_one hy)
      have hL : evAt y (LocalCalculus.smulS (LocalCalculus.eta c3 1) (fun r => physFn 0 0 1 r) r) =
          if r = 0 then y else 0 := by
        rw [evAt_smulS]
        have : (fun s => evAt y (physFn 0 0 1 s)) = fun s => f3even 0 0 1 s y :=
          funext fun s => physFn_apply (M := 0) (σ := 0) 1 s hy
        rw [this, coeff_smulS_real, mk_f3even, eta_c3, h1, PowerSeries.coeff_C]
      change evAt y _ = _
      rw [hL]
      by_cases hr0 : r = 0
      · subst hr0
        simp only [if_true]
        show y = y * (dv 0 0 0).1 y
        rw [dv_zero_scalar_apply hy, mul_one]
      · by_cases hr1 : r = 1
        · subst hr1
          simp [Fn.zero_off]
        · simp [hr0, hr1]
    · have h0 : ∀ (g : Fn), g.1 y = 0 := fun g => g.zero_off hy
      rw [h0, h0]
  have hstart1 : (fun r => physFn 0 0 1 r) = LocalCalculus.serG G (xOp (dv 0 0 0)) :=
    LocalCalculus.smulS_cancel _ (by
      rw [LocalCalculus.constantCoeff_eta c3 c3_zero]; exact one_ne_zero) hphys
  have hfwd : ∀ n : ℕ, (kz 0 0 + ((n + 1 : ℕ) : ℝ)) * Rn 0 0 (n + 2) ≠ 0 := by
    intro n
    have hR : 0 < Rn 0 0 (n + 2) := by
      unfold Rn
      refine Rk_pos 0 0 _ ?_
      have : (0 : ℚ) < ((n + 2 : ℕ) : ℚ) := by positivity
      simpa using this
    have : 0 < kz 0 0 + ((n + 1 : ℕ) : ℝ) := by rw [hk]; positivity
    exact (mul_pos this hR).ne'
  have hu := LocalCalculus.rank_unique_of_two_starts xOp (0 : Polynomial ℝ) c3 c3_zero (TauM 0 0) (kz 0 0)
    (Rn 0 0) hfwd (Φ := physFn 0 0) (Φ' := fun n => LocalCalculus.serG G (dv 0 0 n))
    (fun n => physFn_rankDefect hα hβ (n + 1))
    (fun n => LocalCalculus.local_calculus_ranks xOp _ (0 : Polynomial ℝ) c3 c3_zero G hG0 (TauM 0 0)
      (kz 0 0) (Rn 0 0) (dv 0 0) (Hop_dv 0 0) (dv_rec 0 0) hGB (n + 1))
    (by
      rw [physFn_zero_eq_kap hα hβ]
      funext r
      show kap hα hβ r (dv 0 0 0) = G r (dv 0 0 0)
      rw [hGκ r])
    (by
      show (fun r => physFn 0 0 1 r) = fun r => G r (dv 0 0 1)
      rw [hstart1, dv_one_scalar]; rfl)
  refine ⟨G, hG0, hGm, hGB, fun n r y hy => ?_⟩
  have := congrFun (congrFun hu n) r
  rw [← physFn_apply (M := 0) (σ := 0) n r hy, this]
  rfl


/-! ### The headline statements -/

/-- **`thm:3jallorderlocal`: the all-order local operators and their identification with the Taylor
coefficients of the exact kernel** (`prop:localcalculus` for `eq:3jrank`).

Let `M ± σ` be integers (`α = |M-σ|`, `β = |M+σ|`; the lattice of the finite `3j` problem), `L₀ = max(|M|,|σ|)`
and `d_n = d^{L₀+n}_{Mσ}(arccos x)` (`dv`).  There are differential operators `𝒢_0 = I, 𝒢_1, 𝒢_2, …`
(the paper's `D̂_{2r}`) on functions on `(-1,1)`, independent of the rank `n`, such that

* each `𝒢_r = ∑_j b_j(x) ∂_x^j` is a finite-order left-normal operator with coefficients `b_j` smooth on
  `(-1,1)` (`LN DOp Csm`), obtained by the recursion `𝒢_{r+1} = 𝒥(𝖡_{r+1}) + ψ_{r+1}` with `[x, 𝒢_{r+1}] = 𝖡_{r+1}`,
  `𝖡_{r+1} = ∑_{s ≤ r} c_{s+1} 𝒩_{s+1}[𝒢_{r-s}]` (`eq:3jB2r`, `Bop` with `q = 0`, `e_s = c_s`,
  `√(1-z) = ∑ c_s z^s`, `𝖧₀ = Hop (M²+σ²) (Mσ)`);
* for every rank `n`, order `r` and `x ∈ (-1,1)`: `f_{2r}^{(n)}(x) = (𝒢_r d_n)(x)`, where
  `f_{2r}^{(n)} = f3even M σ n r` is the `t^r` Taylor coefficient of the exact closed-form germ of
  `thm:3jeven`, `t = N⁻²`: that is, `Φ_{L₀+n} = ∑_r t^r 𝒢_r d_{L₀+n}` as formal series.

Every chamber is covered (the germ `Gc3` and the Wigner function `d^{L₀+n}_{Mσ}` are defined uniformly,
`dZero3_eq_wignerD`); the multipliers `ψ_r` are the ones fixed by the exact seed at the minimal rank
(`eq:3jpsi2r`; for `M = σ = 0` the two exact starts).  *Not formalised:* that the `ψ_r` (hence the
coefficients `b_j`) are rational functions of `x` with poles at `±1` only (the coefficients here are
smooth on `(-1,1)`), the Bernoulli closed form `eq:3jseedlogallorder`, and the explicit operators
`D̂_2`, `D̂_4` (`eq:D2hat`, `app:D4`). -/
theorem allorder_operators (hα : |M - σ| = α) (hβ : |M + σ| = β) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r) ∧
      ∀ n r, ∀ y ∈ Sx, (G r (dv M σ n)).1 y = f3even M σ n r y := by
  by_cases hL : max |M| |σ| = 0
  · have hM : M = 0 := abs_nonpos_iff.mp (hL ▸ le_max_left _ _)
    have hs : σ = 0 := abs_nonpos_iff.mp (hL ▸ le_max_right _ _)
    subst hM hs
    exact allorder_operators_zero
  · exact allorder_operators_pos hα hβ
      (lt_of_le_of_ne (le_trans (abs_nonneg M) (le_max_left _ _)) (Ne.symm hL))

/-- The test function `g = ∑_{k ≤ k_*} c_k u_{L₀+k}` of the paper's cutoff space
`𝒱_{L_*} = span{u_L}`, `u_L = √((2L+1)/2) d^L_{Mσ}(arccos x)`. -/
noncomputable def gTest (M σ : ℚ) (kmax : ℕ) (c : ℕ → ℝ) : Fn :=
  ∑ k ∈ Finset.range (kmax + 1),
    (c k * Real.sqrt ((2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) / 2)) • dv M σ k

/-- **`thm:3jallorderlocal` (all-order local differential form of the exact `3j` transmutation).**
Let `M ± σ` be integers, `L₀ = max(|M|,|σ|)`, `L_* = L₀ + k_*` a finite spectral cutoff, `K ⊆ (-1,1)`
compact and `R ∈ ℕ`.  There are rank-independent finite-order differential operators `D̂_{2r} = 𝒢_r`,
`D̂_0 = I` (as in `allorder_operators`: left-normal, with coefficients smooth on `(-1,1)`, built by the
recursion `eq:3jB2r`, `eq:3jD2rrecursive`), and constants `C, N₀` such that for every
`g = ∑_{k ≤ k_*} c_k u_{L₀+k}` in the unit ball of `𝒱_{L_*}` (`|c_k| ≤ 1`; the unit sphere of `ℓ²` is
contained in it) and every admissible `N ≥ N₀` and lattice point `μ` with `x_μ = 2μ/N ∈ K`,
`|(S_N g)(x_μ) - ∑_{r<R} N^{-2r} (D̂_{2r} g)(x_μ)| ≤ C N^{-2R}` (`eq:3jallorderoperator`),
where `(S_N g)(x_μ) = ∑_k c_k √((2L_k+1)/2) Φ_{L_k}(x_μ; N⁻¹)` (`S_N u_L = v_L = √((2L+1)/2) Φ_L`,
`prop_SN`) and `(D̂_{2r} g)` is the operator applied to `g` as a function on `(-1,1)`.
The proof: the exact expansion `thm:3jeven` of each `Φ_{L₀+k}` plus the identification
`f_{2r}^{(k)} = D̂_{2r} d_k` (`allorder_operators`), which is the content of the paper's proof.

*Differences from the paper's statement.* The operators have coefficients smooth on `(-1,1)` rather than
rational (not formalised, see `allorder_operators`); the statement is pointwise on the lattice points of `K`
(the `ℓ²(𝒳_N ∩ K, 2h)` version follows by summing at most `N` points and is not stated); `D̂_2`, `D̂_4` in closed
form (`eq:D2hat`, `thm:3jNNLO`) are not part of this statement. -/
theorem threeJ_allorder_local (hα : |M - σ| = α) (hβ : |M + σ| = β) (kmax : ℕ) {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) (R : ℕ) :
    ∃ G : ℕ → End ℝ Fn, G 0 = 1 ∧ (∀ r, G r ∈ LN DOp Csm) ∧
      (∀ r, comm xOp (G (r + 1)) =
        Bop xOp (Hop (SigM M σ) (TauM M σ)) (0 : Polynomial ℝ) c3 (TauM M σ) G r) ∧
      ∃ C N₀ : ℝ, ∀ c : ℕ → ℝ, (∀ k, |c k| ≤ 1) →
        ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) → 2 * (μ : ℝ) / N ∈ K →
          |∑ k ∈ Finset.range (kmax + 1), c k *
              Real.sqrt ((2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) / 2) *
              Phi3j (max |M| |σ| + (k : ℚ)) M σ N μ -
            ∑ r ∈ Finset.range R,
              (G r (gTest M σ kmax c)).1 (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)| ≤
            C / (N : ℝ) ^ (2 * R) := by
  obtain ⟨G, hG0, hGm, hGB, hGid⟩ := allorder_operators hα hβ
  refine ⟨G, hG0, hGm, hGB, ?_⟩
  have hex : ∀ k : ℕ, ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j (max |M| |σ| + (k : ℚ)) M σ N μ -
          ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)| ≤
        C / (N : ℝ) ^ (2 * R) := fun k =>
    Phi3j_even_expansion M σ (max |M| |σ| + (k : ℚ)) k rfl hK hKI R
  choose Ck Nk hCN using hex
  set w : ℕ → ℝ := fun k => Real.sqrt ((2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) / 2) with hw
  refine ⟨∑ k ∈ Finset.range (kmax + 1), w k * Ck k,
    ∑ k ∈ Finset.range (kmax + 1), max (Nk k) 0, fun c hc N μ hA hlat hN hxK => ?_⟩
  have hy : 2 * (μ : ℝ) / N ∈ Sx := hKI hxK
  have hNk : ∀ k ∈ Finset.range (kmax + 1), Nk k ≤ (N : ℝ) := fun k hk =>
    le_trans (le_trans (le_max_left _ _) (Finset.single_le_sum (f := fun k => max (Nk k) 0)
      (fun j _ => le_max_right _ _) hk)) hN
  -- the operator side
  have hop : ∀ r, (G r (gTest M σ kmax c)).1 (2 * (μ : ℝ) / N) =
      ∑ k ∈ Finset.range (kmax + 1), c k * w k * f3even M σ k r (2 * (μ : ℝ) / N) := by
    intro r
    unfold gTest
    rw [map_sum]
    simp only [map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hGid k r _ hy]
  have key : ∑ k ∈ Finset.range (kmax + 1), c k *
          Real.sqrt ((2 * (((max |M| |σ| + (k : ℚ) : ℚ)) : ℝ) + 1) / 2) *
          Phi3j (max |M| |σ| + (k : ℚ)) M σ N μ -
        ∑ r ∈ Finset.range R,
          (G r (gTest M σ kmax c)).1 (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r) =
      ∑ k ∈ Finset.range (kmax + 1), c k * w k *
        (Phi3j (max |M| |σ| + (k : ℚ)) M σ N μ -
          ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)) := by
    simp_rw [hop, Finset.sum_div, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    simp only [mul_div_assoc]
    rfl
  rw [key]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |c k| * w k * |Phi3j (max |M| |σ| + (k : ℚ)) M σ N μ -
          ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)|
      ≤ 1 * w k * (Ck k / (N : ℝ) ^ (2 * R)) := by
        exact mul_le_mul (mul_le_mul (hc k) le_rfl (Real.sqrt_nonneg _) zero_le_one)
          (hCN k N μ hA hlat (hNk k hk) hxK) (abs_nonneg _)
          (mul_nonneg zero_le_one (Real.sqrt_nonneg _))
    _ = w k * Ck k / (N : ℝ) ^ (2 * R) := by ring

end Setup

end FormalResearch.Racah.LocalCalculus.Fun

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_pos

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators_zero

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.allorder_operators' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.allorder_operators

/-- info: 'FormalResearch.Racah.LocalCalculus.Fun.threeJ_allorder_local' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.LocalCalculus.Fun.threeJ_allorder_local

module

public import Mathlib
public import FormalResearch.Racah.P2AnalyticTaylorSeries
public import FormalResearch.Racah.P2AnalyticCore
public import FormalResearch.Racah.P2LocalCalculusSeries
public import FormalResearch.Racah.P2AnalyticBulk3j
public import FormalResearch.Racah.P2AnalyticBridge3j

/-!
# The Taylor coefficients of the `3j` germ satisfy the deformed rank recurrence as formal series
(Weyl P2, `app:localgeneral`, "Link to the physical kernels"; `thm:3jallorderlocal`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `eq:3jrank`, `eq:3jrankpoly`, `eq:3jclosedform`,
`app:3j-allorder`, `eq:generalrankrec`.

For `M ± σ` integers and `x ∈ (-1,1)` the formal Taylor series `Ψ_n = ∑_r f_{2r}^{(n)}(x) t^r`
(`f_{2r}^{(n)} = f3even M σ n r`, `L = L₀ + n`) of the closed-form germ `G = Gc3` satisfy, at every rank,
the deformed Wigner rank recurrence
`(2L+1)[L(L+1)x - Mσ]Ψ_L = (L+1)R_L √(1-L²t) Ψ_{L-1} + L R_{L+1} √(1-(L+1)²t) Ψ_{L+1}`
(`eq:3jrank`) with `√(1-m²t) = ∑_s c_s m^{2s}t^s` the formal square root (`epsS`).  The proof is the one
of the paper's derivation of `eq:3jrankpoly`, run backwards in the ring `ℝ⟦t⟧`: `G = A(x,t) S_n(t) P̃_n(x,t)`
(`Gc3_eq`) with `S_n = Π_n^{-1/2}`, `Π_{n+1} = (1-(L_n+1)²t)Π_n`, hence `S_n = √(1-L_{n+1}²t) S_{n+1}`
(`sF_relation`), and `P̃` satisfies the polynomial recurrence `eq:3jrankpoly`
(`ptilde3_rank_poly`).

* `sqrt1m`, `epsS`: the formal series `√(1-z)` and `√(1-m²t)`, `epsS_sq`;
* `Psi_rank`, `Psi_rank_row0`: the formal rank recurrence for `Ψ_n`;
* `Gc3_rankDefect`: the same in the form `rankDefect = 0` of `P2LocalCalculusSeries`
  (module `ℝ`, `x` acting as multiplication by the point, `q = 0`, `e_s = c_s`).

The analytic input (analyticity of `G` in `t`) is only used through smoothness at `t = 0`.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Filter
open scoped ContDiff

/-! ### The formal square root `√(1-z)` -/

/-- The formal series `√(1-z) = ∑_s c_s z^s`, `c_s = (-1)^s binom(1/2, s)`. -/
noncomputable def sqrt1m : PowerSeries ℝ :=
  PowerSeries.rescale (-1 : ℝ) (PowerSeries.binomialSeries ℝ (1 / 2 : ℝ))

theorem sqrt1m_sq : sqrt1m ^ 2 = 1 - PowerSeries.X := by
  have h : PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) * PowerSeries.binomialSeries ℝ (1 / 2 : ℝ) =
      PowerSeries.binomialSeries ℝ ((1 : ℕ) : ℝ) := by
    rw [← PowerSeries.binomialSeries_add]; norm_num
  rw [PowerSeries.binomialSeries_nat] at h
  unfold sqrt1m
  rw [sq, ← map_mul, h]
  simp [PowerSeries.rescale_X, sub_eq_add_neg]

theorem coeff_zero_sqrt1m : PowerSeries.coeff 0 sqrt1m = 1 := by
  unfold sqrt1m
  rw [PowerSeries.coeff_rescale]
  simp

/-- `√(1 - m² t)` as a formal series. -/
noncomputable def epsS (m : ℝ) : PowerSeries ℝ := PowerSeries.rescale (m ^ 2) sqrt1m

theorem epsS_sq (m : ℝ) : epsS m ^ 2 = 1 - PowerSeries.C (m ^ 2) * PowerSeries.X := by
  unfold epsS
  rw [← map_pow, sqrt1m_sq]
  simp [PowerSeries.rescale_X]

theorem coeff_zero_epsS (m : ℝ) : PowerSeries.coeff 0 (epsS m) = 1 := by
  unfold epsS
  rw [PowerSeries.coeff_rescale]
  simp [coeff_zero_sqrt1m]

/-- The coefficients `e_s = c_s` of `eq:3jeseries` for `η(k) = √(1-k²t)`. -/
noncomputable def c3 (s : ℕ) : ℝ := PowerSeries.coeff s sqrt1m

theorem c3_zero : c3 0 = 1 := coeff_zero_sqrt1m

theorem eta_c3 (m : ℝ) : LocalCalculus.eta c3 m = epsS m := by
  ext n
  rw [LocalCalculus.coeff_eta]
  unfold epsS
  rw [PowerSeries.coeff_rescale, c3]
  ring

theorem eq_of_sq_eq_of_coeff {a b : PowerSeries ℝ} (h : a ^ 2 = b ^ 2)
    (hc : PowerSeries.coeff 0 a = PowerSeries.coeff 0 b) (h0 : PowerSeries.coeff 0 a ≠ 0) : a = b := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h1 | h1
  · exact h1
  · exfalso
    have := congrArg (PowerSeries.coeff 0) h1
    rw [map_neg] at this
    apply h0
    linarith

/-! ### Smoothness at `t = 0` of the building blocks -/

lemma contDiff_Ct_t (r : ℕ) (u : ℝ) : ContDiff ℝ ∞ (fun t => Ct r u t) :=
  (contDiff_Ct r).comp (contDiff_const.prodMk contDiff_id)

lemma contDiff_step3 (M σ : ℚ) (L : ℚ) (τ : ℝ) {a b : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) : ContDiff ℝ ∞ (fun t => step3 M σ L τ t (a t) (b t)) := by
  unfold step3
  fun_prop

lemma contDiff_ptilde3 (M σ : ℚ) (τ : ℝ) (k : ℕ) : ContDiff ℝ ∞ (fun t => ptilde3 M σ k τ t) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp only [ptilde3_zero]; exact contDiff_const
    | 1, _ =>
      by_cases h : max |M| |σ| = 0
      · simp only [ptilde3_one_of_eq _ _ _ _ h]; exact contDiff_const
      · simp only [ptilde3_one_of_ne _ _ _ _ h]
        exact contDiff_step3 M σ _ τ contDiff_const contDiff_const
    | k + 2, ih =>
      simp only [ptilde3_succ_succ]
      exact contDiff_step3 M σ _ τ (ih (k + 1) (by omega)) (ih k (by omega))

lemma constantCoeff_taylorSer (f : ℝ → ℝ) : PowerSeries.coeff 0 (taylorSer f) = f 0 := by
  rw [coeff_taylorSer]; simp

lemma taylorSer_sqrt_sq {g : ℝ → ℝ} (hg : SmoothAt0 g) (h0 : 0 < g 0) :
    taylorSer (fun t => Real.sqrt (g t)) ^ 2 = taylorSer g := by
  have hs : SmoothAt0 (fun t => Real.sqrt (g t)) := hg.sqrt h0.ne'
  have hev : ∀ᶠ t in nhds (0 : ℝ), 0 < g t := hg.continuousAt.eventually (lt_mem_nhds h0)
  rw [sq, ← taylorSer_mul hs hs]
  refine taylorSer_congr ?_
  filter_upwards [hev] with t ht
  exact Real.mul_self_sqrt ht.le

lemma taylorSer_inv_sqrt_sq {g : ℝ → ℝ} (hg : SmoothAt0 g) (h0 : 0 < g 0) :
    taylorSer (fun t => 1 / Real.sqrt (g t)) ^ 2 * taylorSer g = 1 := by
  have hs : SmoothAt0 (fun t => 1 / Real.sqrt (g t)) :=
    contDiffAt_const.div (hg.sqrt h0.ne') (Real.sqrt_pos.mpr h0).ne'
  have hev : ∀ᶠ t in nhds (0 : ℝ), 0 < g t := hg.continuousAt.eventually (lt_mem_nhds h0)
  rw [sq, ← taylorSer_mul hs hs, ← taylorSer_mul (hs.mul hs) hg, ← taylorSer_one]
  refine taylorSer_congr ?_
  filter_upwards [hev] with t ht
  have hp : Real.sqrt (g t) ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  calc 1 / Real.sqrt (g t) * (1 / Real.sqrt (g t)) * g t
      = 1 / Real.sqrt (g t) * (1 / Real.sqrt (g t)) * (Real.sqrt (g t) * Real.sqrt (g t)) := by
        rw [Real.mul_self_sqrt ht.le]
    _ = 1 := by field_simp

/-! ### The factorisation `G = A · S_n · P̃_n` -/

/-- The rank-independent factor `√(Ct p_+ ((1-x)/2) · Ct p_- ((1+x)/2))` of `Gc3`. -/
noncomputable def aF (M σ : ℚ) (y t : ℝ) : ℝ :=
  Real.sqrt (Ct (pPlus3 M σ) ((1 - y) / 2) t * Ct (pMinus3 M σ) ((1 + y) / 2) t)

/-- `Π_n(t) = Ct (2L_n+1) 1 t`. -/
noncomputable def piF (M σ : ℚ) (k : ℕ) (t : ℝ) : ℝ := Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 t

/-- `Π_n^{-1/2}`. -/
noncomputable def sF (M σ : ℚ) (k : ℕ) (t : ℝ) : ℝ := 1 / Real.sqrt (piF M σ k t)

/-- `P̃_{L₀+k}((1-x)/2; t)`. -/
noncomputable def pF (M σ : ℚ) (k : ℕ) (y t : ℝ) : ℝ := ptilde3 M σ k ((1 - y) / 2) t

theorem Gc3_eq (M σ : ℚ) (k : ℕ) (y t : ℝ) :
    Gc3 M σ k y t = aF M σ y t * sF M σ k t * pF M σ k y t := by
  unfold Gc3 aF sF pF piF
  ring

/-- `f_{2r}` is the `t^r` coefficient of the formal Taylor series of `t ↦ G(x,t)`. -/
theorem f3even_eq_coeff (M σ : ℚ) (k r : ℕ) (y : ℝ) :
    f3even M σ k r y = PowerSeries.coeff r (taylorSer (Gc3 M σ k y)) := by
  rw [coeff_taylorSer]; rfl

lemma Ct_zero_pos (r : ℕ) {u : ℝ} (hu : 0 < u) : 0 < Ct r u 0 := by
  rw [Ct_zero_t]; positivity

lemma smoothAt0_aF (M σ : ℚ) {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) : SmoothAt0 (aF M σ y) := by
  have h : SmoothAt0 (fun t => Ct (pPlus3 M σ) ((1 - y) / 2) t * Ct (pMinus3 M σ) ((1 + y) / 2) t) :=
    ((contDiff_Ct_t _ _).contDiffAt).mul (contDiff_Ct_t _ _).contDiffAt
  refine h.sqrt ?_
  have h1 := Ct_zero_pos (pPlus3 M σ) (u := (1 - y) / 2) (by linarith [hy.2])
  have h2 := Ct_zero_pos (pMinus3 M σ) (u := (1 + y) / 2) (by linarith [hy.1])
  exact (mul_pos h1 h2).ne'

lemma smoothAt0_piF (M σ : ℚ) (k : ℕ) : SmoothAt0 (piF M σ k) :=
  (contDiff_Ct_t _ _).contDiffAt

lemma piF_zero_pos (M σ : ℚ) (k : ℕ) : 0 < piF M σ k 0 := by
  unfold piF; rw [Ct_zero_t]; simp

lemma sF_zero (M σ : ℚ) (k : ℕ) : sF M σ k 0 = 1 := by
  unfold sF piF; rw [Ct_zero_t]; simp

lemma coeff_zero_mul' (a b : PowerSeries ℝ) :
    PowerSeries.coeff 0 (a * b) = PowerSeries.coeff 0 a * PowerSeries.coeff 0 b := by
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply]

lemma smoothAt0_sF (M σ : ℚ) (k : ℕ) : SmoothAt0 (sF M σ k) :=
  contDiffAt_const.div ((smoothAt0_piF M σ k).sqrt (piF_zero_pos M σ k).ne')
    (Real.sqrt_pos.mpr (piF_zero_pos M σ k)).ne'

lemma smoothAt0_pF (M σ : ℚ) (k : ℕ) (y : ℝ) : SmoothAt0 (pF M σ k y) :=
  (contDiff_ptilde3 M σ _ k).contDiffAt

/-- `Ψ_k = A · S_k · P_k` as formal series. -/
theorem taylorSer_Gc3 (M σ : ℚ) (k : ℕ) {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    taylorSer (Gc3 M σ k y) =
      taylorSer (aF M σ y) * taylorSer (sF M σ k) * taylorSer (pF M σ k y) := by
  have : Gc3 M σ k y = fun t => aF M σ y t * sF M σ k t * pF M σ k y t := funext (Gc3_eq M σ k y)
  rw [this, taylorSer_mul ((smoothAt0_aF M σ hy).mul (smoothAt0_sF M σ k)) (smoothAt0_pF M σ k y),
    taylorSer_mul (smoothAt0_aF M σ hy) (smoothAt0_sF M σ k)]

/-! ### The relation `S_n = √(1 - L_{n+1}² t) · S_{n+1}` -/

/-- `L₀ + n` as a real number, for integer `α = p_+`, `β = p_-`: `(p_+ + p_-)/2 + n`. -/
noncomputable def Lr (M σ : ℚ) (k : ℕ) : ℝ := ((pPlus3 M σ + pMinus3 M σ : ℕ) : ℝ) / 2 + k

lemma piF_succ (M σ : ℚ) (k : ℕ) (t : ℝ) :
    piF M σ (k + 1) t = (1 - (Lr M σ k + 1) ^ 2 * t) * piF M σ k t := by
  unfold piF
  have : pPlus3 M σ + pMinus3 M σ + 2 * (k + 1) + 1 = (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) + 2 := by
    ring
  rw [this, Ct_succ_succ]
  unfold Lr
  push_cast
  ring

theorem sF_relation (M σ : ℚ) (k : ℕ) :
    taylorSer (sF M σ k) = epsS (Lr M σ k + 1) * taylorSer (sF M σ (k + 1)) := by
  have h1 := taylorSer_inv_sqrt_sq (smoothAt0_piF M σ k) (piF_zero_pos M σ k)
  have h2 := taylorSer_inv_sqrt_sq (smoothAt0_piF M σ (k + 1)) (piF_zero_pos M σ (k + 1))
  have hpi : taylorSer (piF M σ (k + 1)) =
      (1 - PowerSeries.C ((Lr M σ k + 1) ^ 2) * PowerSeries.X) * taylorSer (piF M σ k) := by
    have : piF M σ (k + 1) = fun t => (1 - (Lr M σ k + 1) ^ 2 * t) * piF M σ k t :=
      funext (piF_succ M σ k)
    have hlin : taylorSer (fun t => 1 - (Lr M σ k + 1) ^ 2 * t) =
        1 - PowerSeries.C ((Lr M σ k + 1) ^ 2) * PowerSeries.X := by
      rw [taylorSer_sub (SmoothAt0.const 1) ((SmoothAt0.const _).mul SmoothAt0.id), taylorSer_const,
        taylorSer_C_mul SmoothAt0.id, taylorSer_id]
      simp
    rw [this, taylorSer_mul ((SmoothAt0.const 1).sub ((SmoothAt0.const _).mul SmoothAt0.id)) (smoothAt0_piF M σ k),
      hlin]
  have hsq : taylorSer (sF M σ k) ^ 2 = (epsS (Lr M σ k + 1) * taylorSer (sF M σ (k + 1))) ^ 2 := by
    have hne : taylorSer (piF M σ k) ≠ 0 := by
      intro h
      have := congrArg (PowerSeries.coeff 0) h
      rw [constantCoeff_taylorSer] at this
      exact (piF_zero_pos M σ k).ne' (by simpa using this)
    unfold sF at *
    rw [mul_pow, epsS_sq]
    rw [hpi] at h2
    apply mul_right_cancel₀ hne
    rw [h1]
    linear_combination (-1 : PowerSeries ℝ) * h2
  have h0 : ∀ j : ℕ, PowerSeries.coeff 0 (taylorSer (sF M σ j)) = 1 := fun j => by
    rw [constantCoeff_taylorSer, sF_zero]
  refine eq_of_sq_eq_of_coeff hsq ?_ ?_
  · rw [coeff_zero_mul', coeff_zero_epsS, h0, h0, one_mul]
  · rw [h0]; exact one_ne_zero


/-! ### The formal rank recurrence of the closed-form germ -/

/-- `L_n = L₀ + n` (real). -/
noncomputable def Lk (M σ : ℚ) (n : ℕ) : ℝ := ((max |M| |σ| + (n : ℚ) : ℚ) : ℝ)

lemma Lr_eq_Lk {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) (n : ℕ) :
    Lr M σ n = Lk M σ n := by
  have h1 : pPlus3 M σ = α := by unfold pPlus3; rw [hα]; exact Nat.floor_natCast α
  have h2 : pMinus3 M σ = β := by unfold pMinus3; rw [hβ]; exact Nat.floor_natCast β
  have h3 := hahn_alpha_add_beta M σ
  rw [hα, hβ] at h3
  have h3r : (α : ℝ) + β = 2 * ((max |M| |σ| : ℚ) : ℝ) := by exact_mod_cast h3
  unfold Lr Lk
  rw [h1, h2]
  simp only [Rat.cast_add, Rat.cast_natCast, Nat.cast_add]
  linarith

lemma Lk_succ (M σ : ℚ) (n : ℕ) : Lk M σ (n + 1) = Lk M σ n + 1 := by
  unfold Lk; push_cast; ring

/-- The formal Taylor series `Ψ_n = ∑_r f_{2r}^{(n)} t^r` of the germ. -/
noncomputable def Psi (M σ : ℚ) (k : ℕ) (y : ℝ) : PowerSeries ℝ := taylorSer (Gc3 M σ k y)

lemma mk_f3even (M σ : ℚ) (k : ℕ) (y : ℝ) :
    PowerSeries.mk (fun r => f3even M σ k r y) = Psi M σ k y := by
  ext r; rw [PowerSeries.coeff_mk, f3even_eq_coeff]; rfl

/-- **The formal rank recurrence of the germ** (`eq:3jrank` for the formal Taylor series, rows `L = L₀+k+1`):
`(2L+1)[L(L+1)x - Mσ]Ψ_L = (L+1)R_L √(1-L²t) Ψ_{L-1} + L R_{L+1} √(1-(L+1)²t) Ψ_{L+1}`
in `ℝ⟦t⟧`.  Derived from `eq:3jrankpoly` (`ptilde3_rank_poly`) and `S_n = √(1-L_{n+1}²t) S_{n+1}`. -/
theorem Psi_rank {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (k : ℕ) :
    PowerSeries.C ((2 * Lk M σ (k + 1) + 1) * (Lk M σ (k + 1) * (Lk M σ (k + 1) + 1) * y - (M : ℝ) * σ)) *
        Psi M σ (k + 1) y =
      PowerSeries.C ((Lk M σ (k + 1) + 1) * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ))) *
          epsS (Lk M σ (k + 1)) * Psi M σ k y +
        PowerSeries.C (Lk M σ (k + 1) * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1)) *
          epsS (Lk M σ (k + 1) + 1) * Psi M σ (k + 2) y := by
  set L := Lk M σ (k + 1) with hL
  have hpt : ∀ t : ℝ, (2 * L + 1) * (L * (L + 1) * y - (M : ℝ) * σ) * pF M σ (k + 1) y t =
      (L + 1) * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ)) * (1 - L ^ 2 * t) * pF M σ k y t +
        L * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1) * pF M σ (k + 2) y t := by
    intro t
    have h := ptilde3_rank_poly M σ k ((1 - y) / 2) t
    have e : (1 : ℝ) - 2 * ((1 - y) / 2) = y := by ring
    rw [e] at h
    exact h
  have hP : PowerSeries.C ((2 * L + 1) * (L * (L + 1) * y - (M : ℝ) * σ)) * taylorSer (pF M σ (k + 1) y) =
      PowerSeries.C ((L + 1) * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ))) *
          (1 - PowerSeries.C (L ^ 2) * PowerSeries.X) * taylorSer (pF M σ k y) +
        PowerSeries.C (L * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1)) * taylorSer (pF M σ (k + 2) y) := by
    have h1 := congrArg taylorSer (funext hpt)
    have sp := smoothAt0_pF M σ
    have s1 : SmoothAt0 (fun t => (1 - L ^ 2 * t)) := (SmoothAt0.const 1).sub ((SmoothAt0.const _).mul SmoothAt0.id)
    rw [taylorSer_C_mul (sp (k + 1) y)] at h1
    rw [taylorSer_add (((SmoothAt0.const _).mul s1).mul (sp k y)) ((SmoothAt0.const _).mul (sp (k + 2) y)),
      taylorSer_mul ((SmoothAt0.const _).mul s1) (sp k y), taylorSer_mul (SmoothAt0.const _) s1,
      taylorSer_const, taylorSer_C_mul (sp (k + 2) y),
      taylorSer_sub (SmoothAt0.const 1) ((SmoothAt0.const _).mul SmoothAt0.id), taylorSer_const,
      taylorSer_C_mul SmoothAt0.id, taylorSer_id] at h1
    simpa using h1
  have hSk : taylorSer (sF M σ k) = epsS L * taylorSer (sF M σ (k + 1)) := by
    have := sF_relation M σ k
    rw [Lr_eq_Lk hα hβ, ← Lk_succ] at this
    exact this
  have hS1 : taylorSer (sF M σ (k + 1)) = epsS (L + 1) * taylorSer (sF M σ (k + 2)) := by
    have := sF_relation M σ (k + 1)
    rw [Lr_eq_Lk hα hβ] at this
    exact this
  have heps := epsS_sq L
  unfold Psi
  rw [taylorSer_Gc3 M σ k hy, taylorSer_Gc3 M σ (k + 1) hy, taylorSer_Gc3 M σ (k + 2) hy, hSk]
  have hS1' : epsS (L + 1) * taylorSer (sF M σ (k + 2)) = taylorSer (sF M σ (k + 1)) := hS1.symm
  linear_combination (taylorSer (aF M σ y) * taylorSer (sF M σ (k + 1))) * hP -
    (PowerSeries.C ((L + 1) * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ))) * taylorSer (aF M σ y) *
      taylorSer (sF M σ (k + 1)) * taylorSer (pF M σ k y)) * heps -
    (PowerSeries.C (L * Rk M σ (max |M| |σ| + ((k + 1 : ℕ) : ℚ) + 1)) * taylorSer (aF M σ y) *
      taylorSer (pF M σ (k + 2) y)) * hS1'


/-- First row of the formal rank recurrence (the minimal rank `L₀`, where `R_{L₀} = 0`). -/
theorem Psi_rank_row0 {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    PowerSeries.C ((2 * Lk M σ 0 + 1) * (Lk M σ 0 * (Lk M σ 0 + 1) * y - (M : ℝ) * σ)) *
        Psi M σ 0 y =
      PowerSeries.C (Lk M σ 0 * Rk M σ (max |M| |σ| + ((1 : ℕ) : ℚ))) *
          epsS (Lk M σ 0 + 1) * Psi M σ 1 y := by
  by_cases h0 : max |M| |σ| = 0
  · have hM : M = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_left _ _)
    have hs : σ = 0 := abs_nonpos_iff.mp (h0 ▸ le_max_right _ _)
    subst hM hs
    have : Lk 0 0 0 = 0 := by simp [Lk]
    rw [this]; simp
  · have hpt : ∀ t : ℝ, (2 * Lk M σ 0 + 1) * (Lk M σ 0 * (Lk M σ 0 + 1) * y - (M : ℝ) * σ) *
          pF M σ 0 y t = Lk M σ 0 * Rk M σ (max |M| |σ| + ((1 : ℕ) : ℚ)) * pF M σ 1 y t := by
      intro t
      have h := ptilde3_rank_poly_row0 M σ ((1 - y) / 2) t h0
      have e : (1 : ℝ) - 2 * ((1 - y) / 2) = y := by ring
      rw [e] at h
      simpa [Lk, pF] using h
    have sp := smoothAt0_pF M σ
    have hP : PowerSeries.C ((2 * Lk M σ 0 + 1) * (Lk M σ 0 * (Lk M σ 0 + 1) * y - (M : ℝ) * σ)) *
        taylorSer (pF M σ 0 y) =
        PowerSeries.C (Lk M σ 0 * Rk M σ (max |M| |σ| + ((1 : ℕ) : ℚ))) * taylorSer (pF M σ 1 y) := by
      have h1 := congrArg taylorSer (funext hpt)
      rw [taylorSer_C_mul (sp 0 y), taylorSer_C_mul (sp 1 y)] at h1
      exact h1
    have hS0 : taylorSer (sF M σ 0) = epsS (Lk M σ 0 + 1) * taylorSer (sF M σ 1) := by
      have := sF_relation M σ 0
      rw [Lr_eq_Lk hα hβ] at this
      exact this
    unfold Psi
    rw [taylorSer_Gc3 M σ 0 hy, taylorSer_Gc3 M σ 1 hy, hS0]
    linear_combination (taylorSer (aF M σ y) * epsS (Lk M σ 0 + 1) * taylorSer (sF M σ 1)) * hP

theorem coeff_smulS_real (c : PowerSeries ℝ) (v : ℕ → ℝ) (r : ℕ) :
    LocalCalculus.smulS c v r = PowerSeries.coeff r (c * PowerSeries.mk v) := by
  rw [PowerSeries.coeff_mul]
  simp [LocalCalculus.smulS, PowerSeries.coeff_mk]

/-- **The germ's Taylor coefficients solve the deformed rank recurrence at every rank**
(`eq:3jrank` order by order): in the form `rankDefect = 0` of `P2LocalCalculusSeries`, for the
module `ℝ` with `x` acting as multiplication by the point `y`, `q = 0`, `τ = Mσ`, `e_s = c_s`
(`η(k) = √(1-k²t)`), ranks `k₀ + n` with `k₀ = L₀ = max(|M|,|σ|)` and `R_n = R_{L₀+n}`. -/
theorem Gc3_rankDefect {M σ : ℚ} {α β : ℕ} (hα : |M - σ| = α) (hβ : |M + σ| = β) {y : ℝ}
    (hy : y ∈ Set.Ioo (-1 : ℝ) 1) (n : ℕ) :
    LocalCalculus.rankDefect (M := ℝ) (LinearMap.lsmul ℝ ℝ y) 0 c3 ((M : ℝ) * σ)
        (((max |M| |σ| : ℚ)) : ℝ) (fun m => Rk M σ (max |M| |σ| + (m : ℚ)))
        (fun m r => f3even M σ m r y) n = 0 := by
  funext r
  have hk : ∀ m : ℕ, (((max |M| |σ| : ℚ)) : ℝ) + (m : ℝ) = Lk M σ m := fun m => by
    unfold Lk; push_cast; ring
  have hR0 : Rk M σ (max |M| |σ| + ((0 : ℕ) : ℚ)) = 0 := by simpa using Rk_L0 M σ
  have hcoef : ∀ (k r : ℕ), PowerSeries.coeff r (Psi M σ k y) = f3even M σ k r y := fun k r => by
    rw [f3even_eq_coeff]; rfl
  unfold LocalCalculus.rankDefect LocalCalculus.defectS
  simp only [hk, Polynomial.eval_zero, mul_zero, smul_eq_mul, LinearMap.lsmul_apply]
  rw [coeff_smulS_real, eta_c3, mk_f3even]
  cases n with
  | zero =>
    have h := congrArg (PowerSeries.coeff r) (Psi_rank_row0 hα hβ hy)
    simp only [PowerSeries.coeff_C_mul, mul_assoc, hcoef] at h
    rw [hR0]
    simp only [Nat.zero_add, Pi.zero_apply, zero_mul, mul_zero, sub_zero, LocalCalculus.lam]
    linear_combination h
  | succ m =>
    have h := congrArg (PowerSeries.coeff r) (Psi_rank hα hβ hy m)
    simp only [PowerSeries.coeff_C_mul, mul_assoc, hcoef, map_add] at h
    have e : max |M| |σ| + ((m + 1 + 1 : ℕ) : ℚ) = max |M| |σ| + ((m + 1 : ℕ) : ℚ) + 1 := by
      push_cast; ring
    rw [e, show m + 1 + 1 = m + 2 from rfl]
    simp only [LocalCalculus.prevS]
    rw [coeff_smulS_real, eta_c3, mk_f3even]
    simp only [Pi.zero_apply, zero_mul, sub_zero, LocalCalculus.lam]
    linear_combination h


/-! ### The scalar case `M = σ = 0` -/

lemma Gc3_zero_zero (y t : ℝ) : Gc3 0 0 0 y t = 1 := by
  simp [Gc3, pPlus3, pMinus3, Ct_zero, Ct_one, ptilde3_zero, seed3]

lemma Psi_zero_zero_zero (y : ℝ) : Psi 0 0 0 y = 1 := by
  unfold Psi
  have : Gc3 0 0 0 y = fun _ => 1 := funext (Gc3_zero_zero y)
  rw [this, taylorSer_one]

/-- **The second start** of the scalar case (`prop:localcalculus` (c)): `Φ_0 = 1` and
`√(1-t) Φ_1 = x`, i.e. `Φ_1 = x/√(1-t)`. -/
theorem Psi_zero_zero_one {y : ℝ} (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    epsS 1 * Psi 0 0 1 y = PowerSeries.C y := by
  have hA : taylorSer (aF 0 0 y) = 1 := by
    have : aF 0 0 y = fun _ => 1 := by
      funext t; simp [aF, pPlus3, pMinus3, Ct_zero]
    rw [this, taylorSer_one]
  have hS0 : taylorSer (sF 0 0 0) = 1 := by
    have : sF 0 0 0 = fun _ => 1 := by
      funext t; simp [sF, piF, pPlus3, pMinus3, Ct_one]
    rw [this, taylorSer_one]
  have hP : taylorSer (pF 0 0 1 y) = PowerSeries.C y := by
    have : pF 0 0 1 y = fun _ => y := by
      funext t
      simp only [pF]
      rw [ptilde3_one_of_eq _ _ _ _ (by simp)]
      ring
    rw [this, taylorSer_const]
  have hrel := sF_relation 0 0 0
  have hL : Lr 0 0 0 = 0 := by simp [Lr, pPlus3, pMinus3]
  rw [hL, zero_add, hS0] at hrel
  unfold Psi
  rw [taylorSer_Gc3 0 0 1 hy, hA, hP]
  linear_combination (PowerSeries.C y) * (-1 : PowerSeries ℝ) * hrel

end FormalResearch.Racah

/-- info: 'FormalResearch.Racah.Gc3_rankDefect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Gc3_rankDefect

/-- info: 'FormalResearch.Racah.Psi_rank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Psi_rank

/-- info: 'FormalResearch.Racah.Psi_zero_zero_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Racah.Psi_zero_zero_one

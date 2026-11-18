module

public import Mathlib

/-!
# Paper J engine, JE3: the Volterra kernel bounds and the transport equation (`lem:eng-kernel`, `lem:eng-transport`)

Source: Paper J, `Weyl/jacobi_eigenvectors/paper/parts/engine.tex`, Section 2, `lem:eng-kernel` (eq:eng-kernel) and
`lem:eng-transport` (b) (eq:eng-G8); the proof of the transport formula is the identity `2xS' + S = G` in the paper's
proof of `lem:eng-transport`.  Branch `agents/m7-m1-global-racah` of QIprojects.

## Statements formalised
* `kernel_bound_a` (`lem:eng-kernel`, first inequality): with `|φ¹_ν| ≤ K E_ν M_ν`, `|φ²_ν| ≤ K E_ν⁻¹ M_ν`
  (`ν ∈ {m,k}`) and `E_k ≤ C_E E_m`:
  `|φ¹_m φ²_k - φ²_m φ¹_k| E_k ≤ (1 + C_E²) K² E_m M_m M_k`.
* `kernel_bound_b` (`lem:eng-kernel`, second inequality): with `|s¹| ≤ ε' E_k M_k`, `|s²| ≤ ε' E_k⁻¹ M_k`,
  `|e| ≤ η E_k M_k`:  `|φ¹_m s² - φ²_m s¹| |e| ≤ (1 + C_E²) K ε' η E_m M_m M_k²`.
  (The paper's `ε', η` are nonnegative; this is derived from the hypotheses, not assumed.)
* `transport_alg` (`lem:eng-transport`(b), algebraic core): if `S` has derivative `S'` at `u`, `W` has derivative `W'`
  at `u`, `W u > 0`, and `2(u-u*) S'(u) + S(u) = f(u)/√(W u)`, then `B(u) = -4 S(u)/√(W u)` satisfies
  `q B' + (1/2) q' B = -2 f` at `u`, with `q = (u-u*) W` and its derivative `q' = W + (u-u*) W'`.
* `transport_key`: the analytic step, `S(u) = ∫_0^1 G((u-u*)t²) dt` with `G(y) = f(y)/√(W(y))` satisfies the
  derivative identity `2(u-u*)S' + S = G(u)` (differentiation under the integral sign and one integration by parts),
  for `f, W` of class `C¹` on an open interval containing `u*` and `u`, with `W > 0` there.

* `transport_solution`: the two combined: `B = -4S/√W` is differentiable at every point of the interval (also at `u*`)
  and solves `q B' + (1/2) q' B = -2 f` there (existence part of `lem:eng-transport`(b)).

Not formalised: the holomorphic dependence, the regularity statements of `lem:eng-transport` and of
`prop:eng-corr1`, and the bounded-solution uniqueness (`(b)` "exactly one solution bounded at `u*`").

Differences from the paper: none in the statements; the `ε', η ≥ 0` of `lem:eng-kernel` are derived.
-/

@[expose] public section

namespace FormalResearch.JE

/-- **Kernel bound I** (`lem:eng-kernel`, first line). -/
theorem kernel_bound_a (CE Em Ek Mm Mk K p1m p2m p1k p2k : ℝ) (hEm : 0 < Em) (hEk : 0 < Ek)
    (hMm : 0 < Mm) (hMk : 0 < Mk) (hCE : Ek ≤ CE * Em)
    (h1m : |p1m| ≤ K * Em * Mm) (h2m : |p2m| ≤ K * Em⁻¹ * Mm)
    (h1k : |p1k| ≤ K * Ek * Mk) (h2k : |p2k| ≤ K * Ek⁻¹ * Mk) :
    |p1m * p2k - p2m * p1k| * Ek ≤ (1 + CE ^ 2) * K ^ 2 * Em * Mm * Mk := by
  have hK : 0 ≤ K := by
    have : 0 ≤ K * Em * Mm := (abs_nonneg p1m).trans h1m
    have hEM : 0 < Em * Mm := mul_pos hEm hMm
    nlinarith
  have hsq : Ek ^ 2 * Em⁻¹ ≤ CE ^ 2 * Em := by
    have h2 : Ek ^ 2 ≤ CE ^ 2 * Em ^ 2 := by nlinarith
    calc Ek ^ 2 * Em⁻¹ ≤ CE ^ 2 * Em ^ 2 * Em⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hEm.le)
      _ = CE ^ 2 * Em := by field_simp
  have hA : |p1m * p2k| * Ek ≤ K ^ 2 * Em * Mm * Mk := by
    have hprod : |p1m| * |p2k| ≤ (K * Em * Mm) * (K * Ek⁻¹ * Mk) :=
      mul_le_mul h1m h2k (abs_nonneg _) (by positivity)
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right hprod hEk.le
    calc |p1m| * |p2k| * Ek ≤ (K * Em * Mm) * (K * Ek⁻¹ * Mk) * Ek := this
      _ = K ^ 2 * Em * Mm * Mk := by field_simp
  have hB : |p2m * p1k| * Ek ≤ CE ^ 2 * K ^ 2 * Em * Mm * Mk := by
    have hprod : |p2m| * |p1k| ≤ (K * Em⁻¹ * Mm) * (K * Ek * Mk) :=
      mul_le_mul h2m h1k (abs_nonneg _) (by positivity)
    rw [abs_mul]
    have hmul := mul_le_mul_of_nonneg_right hprod hEk.le
    have hfin : (K * Em⁻¹ * Mm) * (K * Ek * Mk) * Ek = K ^ 2 * Mm * Mk * (Ek ^ 2 * Em⁻¹) := by ring
    have hbound : K ^ 2 * Mm * Mk * (Ek ^ 2 * Em⁻¹) ≤ K ^ 2 * Mm * Mk * (CE ^ 2 * Em) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    calc |p2m| * |p1k| * Ek ≤ (K * Em⁻¹ * Mm) * (K * Ek * Mk) * Ek := hmul
      _ = K ^ 2 * Mm * Mk * (Ek ^ 2 * Em⁻¹) := hfin
      _ ≤ K ^ 2 * Mm * Mk * (CE ^ 2 * Em) := hbound
      _ = CE ^ 2 * K ^ 2 * Em * Mm * Mk := by ring
  have htri : |p1m * p2k - p2m * p1k| ≤ |p1m * p2k| + |p2m * p1k| := abs_sub _ _
  have := mul_le_mul_of_nonneg_right htri hEk.le
  nlinarith [hA, hB, this]

/-- **Kernel bound II** (`lem:eng-kernel`, second line). -/
theorem kernel_bound_b (CE Em Ek Mm Mk K p1m p2m s1 s2 e ε' η : ℝ) (hEm : 0 < Em) (hEk : 0 < Ek)
    (hMm : 0 < Mm) (hMk : 0 < Mk) (hCE : Ek ≤ CE * Em)
    (h1m : |p1m| ≤ K * Em * Mm) (h2m : |p2m| ≤ K * Em⁻¹ * Mm)
    (hs1 : |s1| ≤ ε' * Ek * Mk) (hs2 : |s2| ≤ ε' * Ek⁻¹ * Mk) (he : |e| ≤ η * Ek * Mk) :
    |p1m * s2 - p2m * s1| * |e| ≤ (1 + CE ^ 2) * K * ε' * η * Em * Mm * Mk ^ 2 := by
  have hK : 0 ≤ K := by
    have : 0 ≤ K * Em * Mm := (abs_nonneg p1m).trans h1m
    have hEM : 0 < Em * Mm := mul_pos hEm hMm
    nlinarith
  have hε : 0 ≤ ε' := by
    have h0 : 0 ≤ ε' * Ek * Mk := (abs_nonneg s1).trans hs1
    have hEM : 0 < Ek * Mk := mul_pos hEk hMk
    nlinarith
  have hη : 0 ≤ η := by
    have h0 : 0 ≤ η * Ek * Mk := (abs_nonneg e).trans he
    have hEM : 0 < Ek * Mk := mul_pos hEk hMk
    nlinarith
  have hsq : Ek ^ 2 * Em⁻¹ ≤ CE ^ 2 * Em := by
    have h2 : Ek ^ 2 ≤ CE ^ 2 * Em ^ 2 := by nlinarith
    calc Ek ^ 2 * Em⁻¹ ≤ CE ^ 2 * Em ^ 2 * Em⁻¹ :=
          mul_le_mul_of_nonneg_right h2 (inv_nonneg.mpr hEm.le)
      _ = CE ^ 2 * Em := by field_simp
  have hA : |p1m * s2| * |e| ≤ K * ε' * η * Em * Mm * Mk ^ 2 := by
    have hprod : |p1m| * |s2| ≤ (K * Em * Mm) * (ε' * Ek⁻¹ * Mk) :=
      mul_le_mul h1m hs2 (abs_nonneg _) (by positivity)
    rw [abs_mul]
    have hmul := mul_le_mul hprod he (abs_nonneg _) (by positivity)
    calc |p1m| * |s2| * |e| ≤ (K * Em * Mm) * (ε' * Ek⁻¹ * Mk) * (η * Ek * Mk) := hmul
      _ = K * ε' * η * Em * Mm * Mk ^ 2 := by field_simp
  have hB : |p2m * s1| * |e| ≤ CE ^ 2 * K * ε' * η * Em * Mm * Mk ^ 2 := by
    have hprod : |p2m| * |s1| ≤ (K * Em⁻¹ * Mm) * (ε' * Ek * Mk) :=
      mul_le_mul h2m hs1 (abs_nonneg _) (by positivity)
    rw [abs_mul]
    have hmul := mul_le_mul hprod he (abs_nonneg _) (by positivity)
    have hfin : (K * Em⁻¹ * Mm) * (ε' * Ek * Mk) * (η * Ek * Mk)
        = K * ε' * η * Mm * Mk ^ 2 * (Ek ^ 2 * Em⁻¹) := by ring
    have hbound : K * ε' * η * Mm * Mk ^ 2 * (Ek ^ 2 * Em⁻¹)
        ≤ K * ε' * η * Mm * Mk ^ 2 * (CE ^ 2 * Em) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    calc |p2m| * |s1| * |e| ≤ (K * Em⁻¹ * Mm) * (ε' * Ek * Mk) * (η * Ek * Mk) := hmul
      _ = K * ε' * η * Mm * Mk ^ 2 * (Ek ^ 2 * Em⁻¹) := hfin
      _ ≤ K * ε' * η * Mm * Mk ^ 2 * (CE ^ 2 * Em) := hbound
      _ = CE ^ 2 * K * ε' * η * Em * Mm * Mk ^ 2 := by ring
  have htri : |p1m * s2 - p2m * s1| ≤ |p1m * s2| + |p2m * s1| := abs_sub _ _
  have := mul_le_mul_of_nonneg_right htri (abs_nonneg e)
  nlinarith [hA, hB, this]

/-- **Transport, algebraic core** (`lem:eng-transport`(b)): if `2(u-u*)S'(u) + S(u) = f(u)/√W(u)`, then
`B = -4 S/√W` solves `q B' + (1/2) q' B = -2 f` at `u`, where `q = (u-u*) W`. -/
theorem transport_alg (ustar u : ℝ) (W f S : ℝ → ℝ) (W' S' : ℝ)
    (hWpos : 0 < W u) (hW : HasDerivAt W W' u) (hS : HasDerivAt S S' u)
    (hkey : 2 * (u - ustar) * S' + S u = f u / Real.sqrt (W u)) :
    HasDerivAt (fun v => -4 * S v / Real.sqrt (W v))
        ((-4 * S' * Real.sqrt (W u) - (-4 * S u) * (W' / (2 * Real.sqrt (W u)))) / (Real.sqrt (W u)) ^ 2) u ∧
    ((u - ustar) * W u) * ((-4 * S' * Real.sqrt (W u) - (-4 * S u) * (W' / (2 * Real.sqrt (W u))))
        / (Real.sqrt (W u)) ^ 2)
      + (1 / 2) * (W u + (u - ustar) * W') * (-4 * S u / Real.sqrt (W u)) = -2 * f u := by
  have hr : 0 < Real.sqrt (W u) := Real.sqrt_pos.mpr hWpos
  have hr2 : Real.sqrt (W u) ^ 2 = W u := Real.sq_sqrt hWpos.le
  have hsqrt : HasDerivAt (fun v => Real.sqrt (W v)) (W' / (2 * Real.sqrt (W u))) u := by
    have := hW.sqrt hWpos.ne'
    simpa using this
  have hnum : HasDerivAt (fun v => -4 * S v) (-4 * S') u := HasDerivAt.const_mul (-4) hS
  have hd := HasDerivAt.div hnum hsqrt hr.ne'
  refine ⟨hd, ?_⟩
  set r := Real.sqrt (W u) with hrdef
  have hWr : W u = r ^ 2 := hr2.symm
  rw [hWr]
  field_simp
  have hk : f u = r * (2 * (u - ustar) * S' + S u) := by
    rw [hkey]; field_simp
  rw [hk]
  ring

section Analytic

open MeasureTheory Set Filter Topology

/-- `G(y) = f(y)/√(W y)`, the function of `lem:eng-transport`(b). -/
noncomputable def transportG (f W : ℝ → ℝ) (y : ℝ) : ℝ := f y / Real.sqrt (W y)

/-- The derivative `G'(y)` of `transportG`, by the quotient rule. -/
noncomputable def transportGd (f f' W W' : ℝ → ℝ) (y : ℝ) : ℝ :=
  (f' y * Real.sqrt (W y) - f y * (W' y / (2 * Real.sqrt (W y)))) / (Real.sqrt (W y)) ^ 2

/-- `p(u,t) = u* + (u-u*) t²`, the segment point of `eq:eng-G8`. -/
def transportP (ustar u t : ℝ) : ℝ := ustar + (u - ustar) * t ^ 2

/-- `S(u) = ∫_0^1 G(u* + (u-u*) t²) dt`. -/
noncomputable def transportS (ustar : ℝ) (f W : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..1, transportG f W (transportP ustar u t)

lemma transportG_hasDerivAt (f f' W W' : ℝ → ℝ) (y : ℝ) (hW : 0 < W y)
    (hf : HasDerivAt f (f' y) y) (hWd : HasDerivAt W (W' y) y) :
    HasDerivAt (transportG f W) (transportGd f f' W W' y) y :=
  hf.div (hWd.sqrt hW.ne') (Real.sqrt_pos.mpr hW).ne'

lemma transportP_mem {lo hi ustar x t : ℝ} (hu : ustar ∈ Icc lo hi) (hx : x ∈ Icc lo hi)
    (ht : t ∈ Icc (0:ℝ) 1) : transportP ustar x t ∈ Icc lo hi := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨ht0, ht1⟩ := ht
  have hs0 : 0 ≤ t ^ 2 := sq_nonneg t
  have hs1 : t ^ 2 ≤ 1 := by nlinarith
  unfold transportP
  constructor <;> nlinarith

lemma transportP_one (ustar u : ℝ) : transportP ustar u 1 = u := by
  unfold transportP; ring

lemma transportP_hasDerivAt (ustar t : ℝ) (x : ℝ) :
    HasDerivAt (fun y => transportP ustar y t) (t ^ 2) x := by
  unfold transportP
  have := ((((hasDerivAt_id' x).sub_const ustar).mul_const (t ^ 2)).const_add ustar)
  exact this.congr_deriv (by ring)

lemma transportP_hasDerivAt_t (ustar u t : ℝ) :
    HasDerivAt (fun s => transportP ustar u s) (2 * (u - ustar) * t) t := by
  unfold transportP
  have := ((hasDerivAt_pow 2 t).const_mul (u - ustar)).const_add ustar
  exact this.congr_deriv (by norm_num; ring)

/-- **Transport formula, analytic step** (`lem:eng-transport`(b)): for `f, W` of class `C¹` on an open interval `(a,b)`
containing `u*` and `u`, with `W > 0` there, the function `S(u) = ∫_0^1 G(u*+(u-u*)t²) dt` is differentiable at `u`
with `2(u-u*) S'(u) + S(u) = G(u) = f(u)/√(W(u))`, where `S'(u) = ∫_0^1 G'(p(u,t)) t² dt`.  This is the identity
`2xS' + S = G` of the paper, proved by differentiation under the integral sign and one integration by parts. -/
theorem transport_key (a b ustar : ℝ) (hJ : ustar ∈ Ioo a b) (f f' W W' : ℝ → ℝ)
    (hWpos : ∀ y ∈ Ioo a b, 0 < W y) (hWd : ∀ y ∈ Ioo a b, HasDerivAt W (W' y) y)
    (hWc : ContinuousOn W' (Ioo a b))
    (hfd : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y) (hfc : ContinuousOn f' (Ioo a b))
    (u : ℝ) (hu : u ∈ Ioo a b) :
    HasDerivAt (transportS ustar f W)
        (∫ t in (0:ℝ)..1, transportGd f f' W W' (transportP ustar u t) * t ^ 2) u ∧
    2 * (u - ustar) * (∫ t in (0:ℝ)..1, transportGd f f' W W' (transportP ustar u t) * t ^ 2)
      + transportS ustar f W u = f u / Real.sqrt (W u) := by
  -- a compact interval K = [lo, hi] ⊂ (a,b) containing u* and a neighbourhood of u
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hu)
  set ε := δ / 2 with hεdef
  have hε : 0 < ε := by positivity
  have hup : u + ε ∈ Ioo a b := hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  have hdn : u - ε ∈ Ioo a b := hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith)
  set lo := min ustar (u - ε) with hlo
  set hi := max ustar (u + ε) with hhi
  have hKJ : Icc lo hi ⊆ Ioo a b := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    constructor
    · exact lt_of_lt_of_le (lt_min hJ.1 hdn.1) hz1
    · exact lt_of_le_of_lt hz2 (max_lt hJ.2 hup.2)
  have hustar_K : ustar ∈ Icc lo hi := ⟨min_le_left _ _, le_max_left _ _⟩
  have hu_K : ∀ x ∈ Ioo (u - ε) (u + ε), x ∈ Icc lo hi := by
    intro x hx
    exact ⟨le_trans (min_le_right _ _) (le_of_lt hx.1), le_trans (le_of_lt hx.2) (le_max_right _ _)⟩
  have hu_K' : u ∈ Icc lo hi := hu_K u ⟨by linarith, by linarith⟩
  have hsN : Ioo (u - ε) (u + ε) ∈ 𝓝 u := Ioo_mem_nhds (by linarith) (by linarith)
  have hIoc : ∀ t ∈ uIoc (0:ℝ) 1, t ∈ Icc (0:ℝ) 1 := fun t ht => by
    rw [uIoc_of_le zero_le_one] at ht; exact ⟨ht.1.le, ht.2⟩
  -- continuity and bounds on K
  have hfcK : ContinuousOn f (Icc lo hi) := fun z hz => (hfd z (hKJ hz)).continuousAt.continuousWithinAt
  have hWcK : ContinuousOn W (Icc lo hi) := fun z hz => (hWd z (hKJ hz)).continuousAt.continuousWithinAt
  have hfcK' : ContinuousOn f' (Icc lo hi) := hfc.mono (fun z hz => hKJ hz)
  have hWcK' : ContinuousOn W' (Icc lo hi) := hWc.mono (fun z hz => hKJ hz)
  have hWposK : ∀ z ∈ Icc lo hi, 0 < W z := fun z hz => hWpos z (hKJ hz)
  have hsqK : ContinuousOn (fun z => Real.sqrt (W z)) (Icc lo hi) := hWcK.sqrt
  have hsqpos : ∀ z ∈ Icc lo hi, 0 < Real.sqrt (W z) := fun z hz => Real.sqrt_pos.mpr (hWposK z hz)
  have hGdK : ContinuousOn (transportGd f f' W W') (Icc lo hi) := by
    unfold transportGd
    refine ContinuousOn.div ?_ (hsqK.pow 2) (fun z hz => pow_ne_zero 2 (hsqpos z hz).ne')
    exact (hfcK'.mul hsqK).sub (hfcK.mul (hWcK'.div (continuousOn_const.mul hsqK)
      (fun z hz => (mul_pos two_pos (hsqpos z hz)).ne')))
  have hGK : ContinuousOn (transportG f W) (Icc lo hi) :=
    hfcK.div hsqK (fun z hz => (hsqpos z hz).ne')
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := lo) (b := hi)).exists_bound_of_continuousOn hGdK
  -- the parameter curve stays in K
  have hpK : ∀ x ∈ Icc lo hi, ∀ t ∈ Icc (0:ℝ) 1, transportP ustar x t ∈ Icc lo hi :=
    fun x hx t ht => transportP_mem hustar_K hx ht
  -- (1) differentiability of S at u
  have hS : HasDerivAt (transportS ustar f W)
      (∫ t in (0:ℝ)..1, transportGd f f' W W' (transportP ustar u t) * t ^ 2) u := by
    unfold transportS
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun x t => transportG f W (transportP ustar x t))
      (F' := fun x t => transportGd f f' W W' (transportP ustar x t) * t ^ 2)
      (s := Ioo (u - ε) (u + ε)) (x₀ := u) (bound := fun _ => M)
      hsN ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
    · refine Filter.eventually_of_mem hsN ?_
      intro x hx
      have hc : ContinuousOn (fun t => transportG f W (transportP ustar x t)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        refine hGK.comp (by unfold transportP; fun_prop) ?_
        intro t ht
        exact hpK x (hu_K x hx) t ht
      exact (hc.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · have hc : ContinuousOn (fun t => transportG f W (transportP ustar u t)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        refine hGK.comp (by unfold transportP; fun_prop) ?_
        intro t ht
        exact hpK u hu_K' t ht
      exact hc.intervalIntegrable
    · have hc : ContinuousOn (fun t => transportGd f f' W W' (transportP ustar u t) * t ^ 2) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        refine ContinuousOn.mul ?_ (by fun_prop)
        refine hGdK.comp (by unfold transportP; fun_prop) ?_
        intro t ht
        exact hpK u hu_K' t ht
      exact (hc.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      have ht' : t ∈ Icc (0:ℝ) 1 := hIoc t ht
      have hsq1 : t ^ 2 ≤ 1 := by nlinarith [ht'.1, ht'.2]
      have hGd := hM _ (hpK x (hu_K x hx) t ht')
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]
      calc |transportGd f f' W W' (transportP ustar x t)| * t ^ 2
          ≤ |transportGd f f' W W' (transportP ustar x t)| * 1 :=
            mul_le_mul_of_nonneg_left hsq1 (abs_nonneg _)
        _ ≤ M := by simpa using (le_trans (le_of_eq (Real.norm_eq_abs _)) hGd)
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      have ht' : t ∈ Icc (0:ℝ) 1 := hIoc t ht
      have hG := transportG_hasDerivAt f f' W W' _ (hWposK _ (hpK x (hu_K x hx) t ht'))
        (hfd _ (hKJ (hpK x (hu_K x hx) t ht'))) (hWd _ (hKJ (hpK x (hu_K x hx) t ht')))
      exact hG.comp x (transportP_hasDerivAt ustar t x)
  refine ⟨hS, ?_⟩
  -- (2) the identity 2 (u-u*) S' + S = G(u), by integration by parts in t
  set x := u - ustar with hx
  set v : ℝ → ℝ := fun t => transportG f W (transportP ustar u t) with hvdef
  set v' : ℝ → ℝ := fun t => transportGd f f' W W' (transportP ustar u t) * (2 * x * t) with hv'def
  have hvd : ∀ t ∈ Ioo (0:ℝ) 1, HasDerivAt v (v' t) t := by
    intro t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := ⟨ht.1.le, ht.2.le⟩
    have hG := transportG_hasDerivAt f f' W W' _ (hWposK _ (hpK u hu_K' t ht'))
      (hfd _ (hKJ (hpK u hu_K' t ht'))) (hWd _ (hKJ (hpK u hu_K' t ht')))
    exact hG.comp t (transportP_hasDerivAt_t ustar u t)
  have hvc : ContinuousOn v (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine hGK.comp (by unfold transportP; fun_prop) ?_
    intro t ht
    exact hpK u hu_K' t ht
  have hv'c : ContinuousOn v' (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    refine ContinuousOn.mul ?_ (by fun_prop)
    refine hGdK.comp (by unfold transportP; fun_prop) ?_
    intro t ht
    exact hpK u hu_K' t ht
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0:ℝ)) (b := 1) (u := fun t => t) (v := v) (u' := fun _ => (1:ℝ)) (v' := v')
    continuousOn_id hvc
    (fun t _ => hasDerivAt_id t)
    (fun t ht => by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at ht
      exact hvd t ht)
    intervalIntegrable_const hv'c.intervalIntegrable
  have hL : ∫ t in (0:ℝ)..1, t * v' t = 2 * x * ∫ t in (0:ℝ)..1,
      transportGd f f' W W' (transportP ustar u t) * t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    simp only [hv'def]
    ring
  have hR : ∫ t in (0:ℝ)..1, (1:ℝ) * v t = transportS ustar f W u := by
    simp only [one_mul]
    rfl
  have hEnd : 1 * v 1 - 0 * v 0 = f u / Real.sqrt (W u) := by
    simp only [hvdef, transportP_one, one_mul, zero_mul, sub_zero]
    rfl
  have ibp' : ∫ t in (0:ℝ)..1, t * v' t = 1 * v 1 - 0 * v 0 - ∫ t in (0:ℝ)..1, (1:ℝ) * v t := ibp
  rw [hL, hR, hEnd] at ibp'
  linarith

/-- **Transport formula, assembled** (`lem:eng-transport`(b), `eq:eng-G8`, existence part): for `f, W` of class `C¹` on an
open interval `(a,b)` containing `u*`, with `W > 0`, the function `B(v) = -4 S(v)/√(W v)`,
`S(v) = ∫_0^1 G(u*+(v-u*)t²) dt`, `G = f/√W`, is differentiable at every `u ∈ (a,b)` (including `u = u*`, where `B` is
bounded) and solves `q B' + (1/2) q' B = -2 f` there, with `q = (u-u*) W`, `q' = W + (u-u*) W'`.  This combines
`transport_key` and `transport_alg`.  Not formalised: the uniqueness of the solution bounded at `u*` and part (a). -/
theorem transport_solution (a b ustar : ℝ) (hJ : ustar ∈ Ioo a b) (f f' W W' : ℝ → ℝ)
    (hWpos : ∀ y ∈ Ioo a b, 0 < W y) (hWd : ∀ y ∈ Ioo a b, HasDerivAt W (W' y) y)
    (hWc : ContinuousOn W' (Ioo a b))
    (hfd : ∀ y ∈ Ioo a b, HasDerivAt f (f' y) y) (hfc : ContinuousOn f' (Ioo a b))
    (u : ℝ) (hu : u ∈ Ioo a b) :
    ∃ B' : ℝ, HasDerivAt (fun v => -4 * transportS ustar f W v / Real.sqrt (W v)) B' u ∧
      ((u - ustar) * W u) * B' + (1 / 2) * (W u + (u - ustar) * W' u)
          * (-4 * transportS ustar f W u / Real.sqrt (W u)) = -2 * f u := by
  obtain ⟨hS, hkey⟩ := transport_key a b ustar hJ f f' W W' hWpos hWd hWc hfd hfc u hu
  obtain ⟨hd, heq⟩ := transport_alg ustar u W f (transportS ustar f W) (W' u)
    (∫ t in (0:ℝ)..1, transportGd f f' W W' (transportP ustar u t) * t ^ 2)
    (hWpos u hu) (hWd u hu) hS hkey
  exact ⟨_, hd, heq⟩

end Analytic

-- Axiom pins for the headline statements (checked at build time).
/-- info: 'FormalResearch.JE.kernel_bound_a' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.kernel_bound_a

/-- info: 'FormalResearch.JE.kernel_bound_b' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.kernel_bound_b

/-- info: 'FormalResearch.JE.transport_alg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.transport_alg

/-- info: 'FormalResearch.JE.transport_key' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.transport_key

/-- info: 'FormalResearch.JE.transport_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.transport_solution

/-- info: 'FormalResearch.JE.transportG_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JE.transportG_hasDerivAt

end FormalResearch.JE


end

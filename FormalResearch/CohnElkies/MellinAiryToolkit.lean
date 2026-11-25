module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Order.Interval.Set.Basic

/-!
# Mellin–Airy toolkit inequalities (Lemmas T.3 and T.4)

Source: `CFT/sign_uncertainty/paper/mellin_airy_toolkit.tex`,
Lemmas T.3 (`mat:T3`, eqs. `(L5.1)`/`cel:5.1` and `(L5.5)`/`cel:5.5`) and
T.4 (`mat:T4`, parts (a) `(O.11aw.5)`, (b) `(3.4)`, (c) `(3.6)–(3.7)`, (d), (e)/(f) `(M1)–(M2)`).

**Statements proved:**

* **Lemma T.4(a) (`(O.11aw.5)`):** for `x > 0`, `ceEll x = log(x / tanh x)` is strictly increasing,
  satisfies `ceEll x < x² / (3 √(1 + x²/3))` (`ceEll_lt`), and
  `ceEll' x > (2x) / (3 (1 + x²/3)^{3/2})` (`ceEll_deriv_gt`).
* **Lemma T.4(b) (`(3.4)`):** `ceHth x = log(tanh x / x) + x²/3` obeys `0 < ceHth x`,
  `ceHth x ≤ (2/15) x⁴` on `(0, 1]`, and `ceHth x < x⁴/3` on `[1, ∞)`.
* **Lemma T.4(c) (`(3.6)–(3.7)`):** `Φ'(τ; L) ≥ L / 2` for every `L > 0` and `|τ| ≤ τ_*(L)`
  (`edgePhiDeriv_ge`).
* **Lemma T.4(d)/(e)/(f) (`(M1)–(M2)`):**
  `|Φ''(τ)| ≤ min(π²/6 |τ|, |τ|⁻¹)` (`edgePhiDeriv2_abs_le`), `|Φ'''(τ)| ≤ π²/3` (`edgePhiDeriv3_abs_le`),
  `τ / (1 + τ²) ≤ m'(τ) ≤ (π²/6) τ / (1 + τ²)` (`m2_bounds`), and
  `m(τ) - m(τ/2) ≥ (3/8) τ² / (1 + τ²)` (`m1_bound`).
* **Lemma T.3(1) (`cel:5.1`):** `(3/4) σ/(1-σ) < π/sin(πσ) - 1/σ < 2 σ/(1-σ)` for `σ ∈ (0, 1)`
  (`stripG_deriv_bounds`).
* **Lemma T.3(3) (`cel:5.5`):** `Im g(σ + i t) = arctan(sinh(π t)/sin(π σ)) - arctan(t/σ) ≥
  min((1/5)(π/sin(π σ) - 1/σ) t, ...)` and global `≥ (1/7) min(g'(σ) t, 1, σ / t)` (`im_stripG_ge`).
-/

@[expose] public section

open Filter Topology Set Real

namespace FormalResearch.CohnElkies

/-! ### Hyperbolic elementary bounds by differentiation from `0` -/

/-- For `g : ℝ → ℝ` with `g 0 = 0`, `HasDerivAt g g' x` everywhere, and `0 ≤ g' x` (resp. `<`),
we get `0 ≤ g x` (resp. `<`) on `0 < x`. -/
private lemma pos_of_zero_of_deriv_pos {g g' : ℝ → ℝ} (h0 : g 0 = 0)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hpos : ∀ x > 0, 0 < g' x) {x : ℝ} (hx : 0 < x) :
    0 < g x := by
  have hmono : StrictMonoOn g (Ici 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hpos s hs
  rw [← h0]
  exact hmono le_rfl hx.le hx

private lemma nonneg_of_zero_of_deriv_nonneg {g : ℝ → ℝ} (g' : ℝ → ℝ) (h0 : g 0 = 0)
    (hnn : ∀ x ≥ 0, 0 ≤ g' x) (hd : ∀ x, HasDerivAt g (g' x) x) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ g x := by
  have hmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact (continuous_iff_continuousAt.mpr fun s => (hd s).continuousAt).continuousOn
    · intro s _; exact (hd s).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hd s).deriv]
      exact hnn s hs.le
  rw [← h0]
  exact hmono le_rfl hx hx

lemma sinh_gt_id {x : ℝ} (hx : 0 < x) : x < Real.sinh x := by
  have h : 0 < Real.sinh x - x :=
    pos_of_zero_of_deriv_pos (by simp)
      (fun u => (Real.hasDerivAt_sinh u).sub (hasDerivAt_id u))
      (fun u hu => by
        have hpos : 0 < (Real.exp u - 1) ^ 2 / (2 * Real.exp u) :=
          div_pos (sq_pos_of_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr hu))) (by positivity)
        have hch : Real.cosh u = 1 + (Real.exp u - 1) ^ 2 / (2 * Real.exp u) := by
          rw [Real.cosh_eq, Real.exp_neg]
          have he : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
          field_simp; ring
        linarith) hx
  linarith

lemma sinh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x := by
  rcases eq_or_lt_of_le hx with rfl | h
  · simp
  · linarith [sinh_gt_id h]

lemma coth_sub_inv_le {z : ℝ} (hz : 0 < z) :
    Real.cosh z / Real.sinh z - 1 / z ≤ z / 3 := by
  have hψ : ∀ u ≥ 0, 0 ≤ u * Real.cosh u - Real.sinh u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg (g := fun t => t * Real.cosh t - Real.sinh t)
      (fun s => s * Real.sinh s) (by simp)
      (fun s hs => mul_nonneg hs (sinh_nonneg_of_nonneg hs))
      (fun s =>
        (((hasDerivAt_id s).mul (Real.hasDerivAt_cosh s)).sub (Real.hasDerivAt_sinh s)).congr_deriv
          (by dsimp; ring))
      hu
  have hφ : 0 ≤ (3 + z ^ 2) * Real.sinh z - 3 * z * Real.cosh z := by
    refine nonneg_of_zero_of_deriv_nonneg
      (g := fun t => (3 + t ^ 2) * Real.sinh t - 3 * t * Real.cosh t)
      (fun s => s * (s * Real.cosh s - Real.sinh s)) (by simp)
      (fun s hs => mul_nonneg hs (hψ s hs)) (fun s => ?_) hz.le
    have hA : HasDerivAt (fun t => (3 + t ^ 2) * Real.sinh t)
        ((0 + 2 * s) * Real.sinh s + (3 + s ^ 2) * Real.cosh s) s :=
      (((hasDerivAt_const s 3).add (hasDerivAt_pow 2 s)).mul (Real.hasDerivAt_sinh s)).congr_deriv
        (by dsimp; ring)
    have hB : HasDerivAt (fun t => 3 * t * Real.cosh t)
        (3 * 1 * Real.cosh s + 3 * s * Real.sinh s) s :=
      ((hasDerivAt_id s).const_mul 3).mul (Real.hasDerivAt_cosh s)
    exact (hA.sub hB).congr_deriv (by ring)
  have hsh : 0 < Real.sinh z := by linarith [sinh_gt_id hz]
  rw [div_sub_div _ _ hsh.ne' hz.ne', div_le_div_iff₀ (mul_pos hsh hz) (by positivity)]
  nlinarith

lemma sinh_div_le_exp_sq_div_six {z : ℝ} (hz : 0 < z) :
    Real.sinh z / z ≤ Real.exp (z ^ 2 / 6) := by
  have hsh : ∀ u > 0, 0 < Real.sinh u := fun u hu => by linarith [sinh_gt_id hu]
  -- Check `z ^ 2 / 6 - log (sinh z / z)` is nondecreasing and `→ 0` at `0⁺`!
  let F : ℝ → ℝ := fun u => u ^ 2 / 6 - Real.log (Real.sinh u / u)
  have hF_deriv : ∀ u > 0, HasDerivAt F (u / 3 - (Real.cosh u / Real.sinh u - 1 / u)) u := by
    intro u hu
    have h1 : HasDerivAt (fun t : ℝ => Real.sinh t / t)
        ((Real.cosh u * u - Real.sinh u * 1) / u ^ 2) u :=
      (Real.hasDerivAt_sinh u).div (hasDerivAt_id u) hu.ne'
    have hq : Real.sinh u / u ≠ 0 := (div_pos (hsh u hu) hu).ne'
    have h2 : HasDerivAt (fun s => Real.log (Real.sinh s / s))
        (((Real.cosh u * u - Real.sinh u * 1) / u ^ 2) / (Real.sinh u / u)) u :=
      h1.log hq
    have hs : ((Real.cosh u * u - Real.sinh u * 1) / u ^ 2) / (Real.sinh u / u) =
        Real.cosh u / Real.sinh u - 1 / u := by
      have hsh0 := (hsh u hu).ne'
      have hu0 := hu.ne'
      field_simp
    rw [hs] at h2
    have hp : HasDerivAt (fun s : ℝ => s ^ 2 / 6) (u / 3) u := by
      convert (hasDerivAt_pow 2 u).div_const 6 using 1
      ring
    exact hp.sub h2
  have hF_mono : MonotoneOn F (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · refine ContinuousOn.sub ((continuous_pow 2).div_const 6).continuousOn ?_
      intro u hu
      exact ((Real.continuous_sinh.continuousAt.div continuousAt_id (ne_of_gt hu)).log
        (div_pos (hsh u hu) hu).ne').continuousWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      exact (hF_deriv u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ioi] at hu
      rw [(hF_deriv u hu).deriv]
      linarith [coth_sub_inv_le hu]
  have hF_lim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsh_lim : Tendsto (fun u => Real.sinh u / u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have hd : Tendsto (fun u : ℝ => slope Real.sinh 0 u) (𝓝[≠] (0 : ℝ)) (𝓝 (Real.cosh 0)) :=
        hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sinh 0)
      have hd_gt : Tendsto (fun u : ℝ => slope Real.sinh 0 u) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        have hle : (𝓝[>] (0 : ℝ)) ≤ 𝓝[≠] (0 : ℝ) := nhdsWithin_mono 0 (fun _ hx => ne_of_gt hx)
        simpa [Real.cosh_zero] using hd.mono_left hle
      have h1 : (fun u : ℝ => slope Real.sinh 0 u) =ᶠ[𝓝[>] (0 : ℝ)] fun u => Real.sinh u / u := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        simp [slope, Real.sinh_zero, div_eq_inv_mul]
      exact hd_gt.congr' h1
    have hlog := (Real.continuousAt_log one_ne_zero).tendsto.comp hsh_lim
    simp only [Real.log_one] at hlog
    have hp : Tendsto (fun u : ℝ => u ^ 2 / 6) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun u : ℝ => u ^ 2 / 6) := by fun_prop
      simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    simpa [F] using hp.sub hlog
  have hF_nn : 0 ≤ F z := by
    by_contra H
    rw [not_le] at H
    have hmem : Ioi (F z) ∈ 𝓝 (0 : ℝ) := Ioi_mem_nhds H
    have hev2 : ∀ᶠ u in 𝓝[>] (0 : ℝ), F z < F u ∧ u ∈ Ioo 0 z :=
      (hF_lim.eventually hmem).and (Ioo_mem_nhdsGT hz)
    obtain ⟨u, hFu, hu0, huz⟩ := hev2.exists
    have hle : F u ≤ F z := hF_mono hu0 hz huz.le
    linarith
  dsimp [F] at hF_nn
  rw [← Real.log_le_iff_le_exp (div_pos (hsh z hz) hz)]
  linarith

lemma sinh_taylor_lower {u : ℝ} (hu : 0 ≤ u) :
    u + u ^ 3 / 6 + u ^ 5 / 120 ≤ Real.sinh u := by
  have d5 : ∀ s ≥ 0, 0 ≤ Real.cosh s - 1 := fun s _ => by linarith [Real.one_le_cosh s]
  have d4 : ∀ s ≥ 0, 0 ≤ Real.sinh s - s := fun s hs =>
    nonneg_of_zero_of_deriv_nonneg (g := fun t => Real.sinh t - t) (fun t => Real.cosh t - 1)
      (by simp) d5 (fun t => (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)) hs
  have d3 : ∀ s ≥ 0, 0 ≤ Real.cosh s - (1 + s ^ 2 / 2) := fun s hs =>
    nonneg_of_zero_of_deriv_nonneg (g := fun t => Real.cosh t - (1 + t ^ 2 / 2))
      (fun t => Real.sinh t - t) (by simp) d4
      (fun t => ((Real.hasDerivAt_cosh t).sub
        ((hasDerivAt_const t 1).add ((hasDerivAt_pow 2 t).div_const 2))).congr_deriv (by dsimp; ring)) hs
  have d2 : ∀ s ≥ 0, 0 ≤ Real.sinh s - (s + s ^ 3 / 6) := fun s hs =>
    nonneg_of_zero_of_deriv_nonneg (g := fun t => Real.sinh t - (t + t ^ 3 / 6))
      (fun t => Real.cosh t - (1 + t ^ 2 / 2)) (by simp) d3
      (fun t => ((Real.hasDerivAt_sinh t).sub
        ((hasDerivAt_id t).add ((hasDerivAt_pow 3 t).div_const 6))).congr_deriv (by dsimp; ring)) hs
  have d1 : ∀ s ≥ 0, 0 ≤ Real.cosh s - (1 + s ^ 2 / 2 + s ^ 4 / 24) := fun s hs =>
    nonneg_of_zero_of_deriv_nonneg (g := fun t => Real.cosh t - (1 + t ^ 2 / 2 + t ^ 4 / 24))
      (fun t => Real.sinh t - (t + t ^ 3 / 6)) (by simp) d2
      (fun t => ((Real.hasDerivAt_cosh t).sub
        (((hasDerivAt_const t 1).add ((hasDerivAt_pow 2 t).div_const 2)).add
          ((hasDerivAt_pow 4 t).div_const 24))).congr_deriv (by dsimp; ring)) hs
  have d0 := nonneg_of_zero_of_deriv_nonneg
    (g := fun t => Real.sinh t - (t + t ^ 3 / 6 + t ^ 5 / 120))
    (fun t => Real.cosh t - (1 + t ^ 2 / 2 + t ^ 4 / 24)) (by simp) d1
    (fun t => ((Real.hasDerivAt_sinh t).sub
      (((hasDerivAt_id t).add ((hasDerivAt_pow 3 t).div_const 6)).add
        ((hasDerivAt_pow 5 t).div_const 120))).congr_deriv (by dsimp; ring)) hu
  linarith

/-! ### Lemma T.4(a) `(O.11aw.5)` -/

/-- `ℓ(x) = log(x coth x) = log(x / tanh x)` (`mellin_airy_toolkit.tex`, Lemma T.4). -/
noncomputable def ceEll (x : ℝ) : ℝ := Real.log (x / Real.tanh x)

lemma tanh_pos_of_pos {x : ℝ} (hx : 0 < x) : 0 < Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_pos (by linarith [sinh_gt_id hx]) (Real.cosh_pos x)

private lemma hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hch : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have h : HasDerivAt (fun t => Real.sinh t / Real.cosh t)
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x :=
    (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hch
  have h' : HasDerivAt Real.tanh
      ((Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2) x := by
    simpa only [← Real.tanh_eq_sinh_div_cosh] using h
  refine h'.congr_deriv ?_
  have hid := Real.cosh_sq_sub_sinh_sq x
  rw [sq, sq] at hid
  rw [hid]

lemma tanh_lt_id {x : ℝ} (hx : 0 < x) : Real.tanh x < x := by
  rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos x)]
  -- `sinh x < x * cosh x` iff `0 < x * cosh x - sinh x` (pos derivative `x * sinh x > 0`!)
  have h : 0 < x * Real.cosh x - Real.sinh x :=
    @pos_of_zero_of_deriv_pos (fun t => t * Real.cosh t - Real.sinh t) (fun t => t * Real.sinh t)
      (by simp)
      (fun u => (((hasDerivAt_id u).mul (Real.hasDerivAt_cosh u)).sub (Real.hasDerivAt_sinh u)).congr_deriv
        (by dsimp; ring))
      (fun u hu => mul_pos hu (by linarith [sinh_gt_id hu])) x hx
  linarith

lemma ceEll_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt ceEll (1 / x - 2 / Real.sinh (2 * x)) x := by
  unfold ceEll
  have h1 : HasDerivAt (fun s => Real.tanh s) (1 / Real.cosh x ^ 2) x :=
    hasDerivAt_tanh x
  have ht0 : Real.tanh x ≠ 0 := (tanh_pos_of_pos hx).ne'
  have hdiv := (hasDerivAt_id x).div h1 ht0
  have hlog := hdiv.log (div_pos hx (tanh_pos_of_pos hx)).ne'
  refine hlog.congr_deriv ?_
  dsimp only [Pi.div_apply, id_eq]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul]
  field_simp

lemma ceEll_strictMonoOn : StrictMonoOn ceEll (Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro x hx
    exact (ceEll_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi, mem_Ioi] at hx
    rw [(ceEll_hasDerivAt hx).deriv]
    have h1 : 2 * x < Real.sinh (2 * x) := sinh_gt_id (by linarith)
    have hsh : 0 < Real.sinh (2 * x) := by linarith
    rw [sub_pos, div_lt_div_iff₀ hsh hx]
    linarith

lemma ceEll_tendsto_zero : Tendsto ceEll (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hsh : Tendsto (fun x => Real.sinh x / x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hd : Tendsto (fun t : ℝ => t⁻¹ • (Real.sinh (0 + t) - Real.sinh 0)) (𝓝[≠] (0 : ℝ))
        (𝓝 (Real.cosh 0)) :=
      (Real.hasDerivAt_sinh 0).tendsto_slope_zero
    have h1 : (fun t : ℝ => t⁻¹ • (Real.sinh (0 + t) - Real.sinh 0)) =ᶠ[𝓝[>] (0 : ℝ)]
        fun x => Real.sinh x / x := by
      filter_upwards [self_mem_nhdsWithin] with x _
      simp [Real.sinh_zero, div_eq_inv_mul]
    have hgt : Tendsto (fun t : ℝ => t⁻¹ • (Real.sinh (0 + t) - Real.sinh 0))
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.cosh 0)) :=
      hd.mono_left (nhdsWithin_mono 0 (fun _ h => ne_of_gt h))
    simpa [Real.cosh_zero] using hgt.congr' h1
  have hch : Tendsto Real.cosh (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa [Real.cosh_zero] using
      (Real.continuous_cosh.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hratio : Tendsto (fun x => x / Real.tanh x) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h1 : Tendsto (fun x => Real.cosh x / (Real.sinh x / x)) (𝓝[>] (0 : ℝ)) (𝓝 (1 / 1)) :=
      hch.div hsh one_ne_zero
    rw [div_one] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    rw [Real.tanh_eq_sinh_div_cosh]
    have hx0 : x ≠ 0 := hx.ne'
    have hch0 : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
    have hsh0 : Real.sinh x ≠ 0 := (by linarith [sinh_gt_id hx] : 0 < Real.sinh x).ne'
    field_simp
  have hlog : Tendsto (fun x => Real.log (x / Real.tanh x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  exact hlog

/-- **Lemma T.4(a) (`(O.11aw.5)`, upper bound):** for `x > 0`, `log(x / tanh x) < x² / (3 √(1 + x²/3))`. -/
theorem ceEll_lt {x : ℝ} (hx : 0 < x) :
    ceEll x < x ^ 2 / (3 * Real.sqrt (1 + x ^ 2 / 3)) := by
  let U : ℝ → ℝ := fun t => t * (2 + t) / (1 + t) ^ (3 / 2 : ℝ)
  have hU_gt : ∀ t > 0, 1 - Real.exp (-2 * t) < U t := by
    intro t ht
    let G : ℝ → ℝ := fun s => U s - (1 - Real.exp (-2 * s))
    have hG_deriv : ∀ s > 0,
        HasDerivAt G ((2 + s + s ^ 2 / 2) / (1 + s) ^ (5 / 2 : ℝ) - 2 * Real.exp (-2 * s)) s := by
      intro s hs
      have hs1 : 0 < 1 + s := by linarith
      have hnum : HasDerivAt (fun u => u * (2 + u)) (2 + 2 * s) s :=
        ((hasDerivAt_id s).mul ((hasDerivAt_const s 2).add (hasDerivAt_id s))).congr_deriv
          (by dsimp; ring)
      have hden : HasDerivAt (fun u => (1 + u) ^ (3 / 2 : ℝ)) ((3 / 2 : ℝ) * (1 + s) ^ (1 / 2 : ℝ)) s := by
        have h1 : HasDerivAt (fun u => 1 + u) 1 s := (hasDerivAt_id s).const_add 1
        have h2 := h1.rpow_const (p := (3 / 2 : ℝ)) (Or.inl hs1.ne')
        refine h2.congr_deriv ?_
        norm_num
      have hU_d := hnum.div hden (Real.rpow_pos_of_pos hs1 _).ne'
      have hexp_d : HasDerivAt (fun u => 1 - Real.exp (-2 * u)) (2 * Real.exp (-2 * s)) s := by
        have h1 : HasDerivAt (fun u => -2 * u) (-2) s := by
          simpa using (hasDerivAt_id s).const_mul (-2)
        convert (hasDerivAt_const s 1).sub h1.exp using 1
        ring
      refine (hU_d.sub hexp_d).congr_deriv ?_
      have hr12 : (1 + s) ^ (1 / 2 : ℝ) = Real.sqrt (1 + s) := Real.sqrt_eq_rpow _ |>.symm
      have hr32 : (1 + s) ^ (3 / 2 : ℝ) = (1 + s) * Real.sqrt (1 + s) := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hs1, Real.rpow_one, Real.sqrt_eq_rpow]
      have hr52 : (1 + s) ^ (5 / 2 : ℝ) = (1 + s) ^ 2 * Real.sqrt (1 + s) := by
        rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hs1, Real.rpow_two, Real.sqrt_eq_rpow]
      have hrn : Real.sqrt (1 + s) ≠ 0 := (Real.sqrt_pos.mpr hs1).ne'
      rw [hr12, hr32, hr52]
      field_simp
      ring
    have hG_pos_deriv : ∀ s > 0, 0 < (2 + s + s ^ 2 / 2) / (1 + s) ^ (5 / 2 : ℝ) - 2 * Real.exp (-2 * s) := by
      intro s hs
      have hs1 : 0 < 1 + s := by linarith
      have hexp_bd : (1 + s) ^ 2 ≤ Real.exp (2 * s) := by
        have h1 : 1 + s ≤ Real.exp s := by linarith [Real.add_one_le_exp s]
        calc (1 + s) ^ 2 = (1 + s) * (1 + s) := sq _
          _ ≤ Real.exp s * Real.exp s := mul_le_mul h1 h1 (by positivity) (Real.exp_pos s).le
          _ = Real.exp (2 * s) := by rw [← Real.exp_add, two_mul]
      have hexp_inv : 2 * Real.exp (-2 * s) ≤ 2 / (1 + s) ^ 2 := by
        rw [show (-2 * s : ℝ) = -(2 * s) by ring, Real.exp_neg, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (sq_pos_of_pos hs1) hexp_bd) two_pos.le
      have hpoly : 4 * (1 + s) < (2 + s + s ^ 2 / 2) ^ 2 := by
        nlinarith [sq_pos_of_pos hs, mul_pos hs (sq_pos_of_pos hs)]
      have hsqrt_lt : 2 * Real.sqrt (1 + s) < 2 + s + s ^ 2 / 2 := by
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 + s + s ^ 2 / 2)]
        have h1 : (2 * Real.sqrt (1 + s)) ^ 2 = 4 * (1 + s) := by
          rw [mul_pow, Real.sq_sqrt hs1.le]; ring
        rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * Real.sqrt (1 + s)), h1]
        exact Real.sqrt_lt_sqrt (by positivity) hpoly
      have hr52 : (1 + s) ^ (5 / 2 : ℝ) = (1 + s) ^ 2 * Real.sqrt (1 + s) := by
        rw [show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hs1, Real.rpow_two, Real.sqrt_eq_rpow]
      rw [hr52]
      have hdiv : 2 / (1 + s) ^ 2 < (2 + s + s ^ 2 / 2) / ((1 + s) ^ 2 * Real.sqrt (1 + s)) := by
        rw [div_lt_div_iff₀ (sq_pos_of_pos hs1) (by positivity)]
        nlinarith [sq_pos_of_pos hs1]
      linarith
    have hG_mono : StrictMonoOn G (Ici 0) := by
      refine strictMonoOn_of_deriv_pos (convex_Ici 0) ?_ ?_
      · refine ContinuousOn.sub ?_ (by fun_prop)
        intro s hs
        have hs1 : 0 < 1 + s := by linarith [hs.out]
        exact ((continuousAt_id.mul (by fun_prop)).div
          ((continuousAt_const.add continuousAt_id).rpow_const (Or.inl hs1.ne'))
          (Real.rpow_pos_of_pos hs1 _).ne').continuousWithinAt
      · intro s hs
        rw [interior_Ici] at hs
        rw [(hG_deriv s hs).deriv]
        exact hG_pos_deriv s hs
    have hG0 : G 0 = 0 := by simp [G, U]
    have hlt := hG_mono le_rfl ht.le ht
    rw [hG0] at hlt
    dsimp [G] at hlt
    linarith
  let R : ℝ → ℝ := fun s => s ^ 2 / (3 * Real.sqrt (1 + s ^ 2 / 3))
  let F : ℝ → ℝ := fun s => R s - ceEll s
  have hR_deriv : ∀ s > 0, HasDerivAt R (U (s ^ 2 / 3) / s) s := by
    intro s hs
    have h1 : HasDerivAt (fun u => 1 + u ^ 2 / 3) (2 * s / 3) s :=
      ((hasDerivAt_const s 1).add ((hasDerivAt_pow 2 s).div_const 3)).congr_deriv (by dsimp; ring)
    have hsqrt : HasDerivAt (fun u => Real.sqrt (1 + u ^ 2 / 3))
        ((2 * s / 3) / (2 * Real.sqrt (1 + s ^ 2 / 3))) s :=
      h1.sqrt (by positivity)
    have hdiv := (hasDerivAt_pow 2 s).div (hsqrt.const_mul 3) (by positivity)
    refine hdiv.congr_deriv ?_
    dsimp [U]
    have h1s : 0 < 1 + s ^ 2 / 3 := by positivity
    have hr32 : (1 + s ^ 2 / 3) ^ (3 / 2 : ℝ) = (1 + s ^ 2 / 3) * Real.sqrt (1 + s ^ 2 / 3) := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add h1s, Real.rpow_one, Real.sqrt_eq_rpow]
    have hrn : Real.sqrt (1 + s ^ 2 / 3) ≠ 0 := (Real.sqrt_pos.mpr h1s).ne'
    have hs0 : s ≠ 0 := hs.ne'
    rw [hr32]
    field_simp
    have hsq' : Real.sqrt ((3 + s ^ 2) / 3) ^ 2 = (3 + s ^ 2) / 3 := Real.sq_sqrt (by positivity)
    rw [hsq']
    ring
  have hF_mono : StrictMonoOn F (Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
    · refine ContinuousOn.sub ?_ (fun s hs => (ceEll_hasDerivAt hs).continuousAt.continuousWithinAt)
      intro s _
      have hden0 : 3 * Real.sqrt (1 + s ^ 2 / 3) ≠ 0 :=
        (mul_pos three_pos (Real.sqrt_pos.mpr (by positivity))).ne'
      have hcR : ContinuousAt R s :=
        ((continuous_pow 2).continuousAt).div
          (((continuousAt_const.add (((continuous_pow 2).continuousAt).div_const 3)).sqrt).const_mul 3)
          hden0
      exact hcR.continuousWithinAt
    · intro s hs
      rw [interior_Ioi, mem_Ioi] at hs
      have hFd : HasDerivAt F (U (s ^ 2 / 3) / s - (1 / s - 2 / Real.sinh (2 * s))) s :=
        (hR_deriv s hs).sub (ceEll_hasDerivAt hs)
      rw [hFd.deriv]
      have hsh : Real.sinh (2 * s) / (2 * s) ≤ Real.exp ((2 * s) ^ 2 / 6) :=
        sinh_div_le_exp_sq_div_six (by linarith)
      have hsh_pos : 0 < Real.sinh (2 * s) := by linarith [sinh_gt_id (by linarith : 0 < 2 * s)]
      have hinv : 1 / s - 2 / Real.sinh (2 * s) ≤ (1 - Real.exp (-2 * (s ^ 2 / 3))) / s := by
        have heq : (2 * s) ^ 2 / 6 = 2 * (s ^ 2 / 3) := by ring
        rw [heq] at hsh
        rw [show (-2 * (s ^ 2 / 3) : ℝ) = -(2 * (s ^ 2 / 3)) by ring, Real.exp_neg]
        have h1 : 2 / Real.sinh (2 * s) ≥ (Real.exp (2 * (s ^ 2 / 3)))⁻¹ / s := by
          have hinv' : 2 * s / Real.sinh (2 * s) ≥ (Real.exp (2 * (s ^ 2 / 3)))⁻¹ :=
            (inv_anti₀ (div_pos hsh_pos (by linarith)) hsh).trans_eq (by rw [inv_div])
          have h2 : (2 * s / Real.sinh (2 * s)) / s = 2 / Real.sinh (2 * s) := by
            have := hs.ne'; field_simp
          rw [← h2]
          exact div_le_div_of_nonneg_right hinv' hs.le
        rw [sub_div]
        linarith
      have hU := hU_gt (s ^ 2 / 3) (by positivity)
      have hdiv : (1 - Real.exp (-2 * (s ^ 2 / 3))) / s < U (s ^ 2 / 3) / s :=
        div_lt_div_of_pos_right hU hs
      linarith
  have hF_lim : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hR0 : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous R := (continuous_pow 2).div
        (((continuous_const.add ((continuous_pow 2).div_const 3)).sqrt).const_mul 3)
        (fun s => by positivity)
      have hR0' : Tendsto R (𝓝[>] (0 : ℝ)) (𝓝 (R 0)) :=
        (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
      simpa [R] using hR0'
    simpa [F] using hR0.sub ceEll_tendsto_zero
  by_contra H
  rw [not_lt] at H
  have hhalf : F (x / 2) < F x := hF_mono (mem_Ioi.mpr (by positivity)) (mem_Ioi.mpr hx) (by linarith)
  have hneg : F (x / 2) < 0 := by
    have : F x ≤ 0 := by dsimp [F, R]; linarith
    linarith
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), F (x / 2) < F s ∧ s ∈ Ioo 0 (x / 2) :=
    (hF_lim.eventually (lt_mem_nhds hneg)).and (Ioo_mem_nhdsGT (by positivity : 0 < x / 2))
  obtain ⟨s, hFs, hs0, hsx⟩ := hev.exists
  have hle : F s < F (x / 2) := hF_mono (mem_Ioi.mpr hs0) (mem_Ioi.mpr (by positivity)) hsx
  linarith

/-- **Lemma T.4(a) (`(O.11aw.5)`, derivative lower bound):**
for `x > 0`, `ℓ'(x) > (2 x) / (3 (1 + x²/3)^{3/2})`. -/
theorem ceEll_deriv_gt {x : ℝ} (hx : 0 < x) :
    2 * x / (3 * (1 + x ^ 2 / 3) ^ (3 / 2 : ℝ)) < 1 / x - 2 / Real.sinh (2 * x) := by
  set t : ℝ := x ^ 2 / 3
  have ht : 0 < t := by positivity
  have hsh := sinh_taylor_lower (by linarith : 0 ≤ 2 * x)
  have hpoly : 2 * x * (1 + 2 * t + 6 / 5 * t ^ 2) ≤ Real.sinh (2 * x) := by
    have heq : 2 * x + (2 * x) ^ 3 / 6 + (2 * x) ^ 5 / 120 =
        2 * x * (1 + 2 * t + 6 / 5 * t ^ 2) := by
      dsimp [t]; ring
    linarith
  have hinv : 1 / x - 2 / Real.sinh (2 * x) ≥
      (2 * x / 3) * ((1 + 3 / 5 * t) / (1 + 2 * t + 6 / 5 * t ^ 2)) := by
    have hp_pos : 0 < 2 * x * (1 + 2 * t + 6 / 5 * t ^ 2) := by positivity
    have h2 : 2 / Real.sinh (2 * x) ≤ 2 / (2 * x * (1 + 2 * t + 6 / 5 * t ^ 2)) :=
      div_le_div_of_nonneg_left zero_le_two hp_pos hpoly
    have hid : 1 / x - 2 / (2 * x * (1 + 2 * t + 6 / 5 * t ^ 2)) =
        (2 * x / 3) * ((1 + 3 / 5 * t) / (1 + 2 * t + 6 / 5 * t ^ 2)) := by
      have hx0 : x ≠ 0 := hx.ne'
      have hden0 : 1 + 2 * t + 6 / 5 * t ^ 2 ≠ 0 := by positivity
      dsimp [t]
      field_simp
      ring
    linarith
  -- Compare `(1 + 3/5 t) / (1 + 2t + 6/5 t²)` against `(1 + t)^{-3/2}`:
  have hsq : (1 + 2 * t + 6 / 5 * t ^ 2) ^ 2 < (1 + 3 / 5 * t) ^ 2 * (1 + t) ^ 3 := by
    have heq : (1 + 3 / 5 * t) ^ 2 * (1 + t) ^ 3 - (1 + 2 * t + 6 / 5 * t ^ 2) ^ 2 =
        t / 25 * (9 * t ^ 4 + 21 * t ^ 3 + 22 * t ^ 2 + 14 * t + 5) := by ring
    have hpos : 0 < t / 25 * (9 * t ^ 4 + 21 * t ^ 3 + 22 * t ^ 2 + 14 * t + 5) := by positivity
    linarith
  have ht1 : 0 < 1 + t := by linarith
  have hr32 : (1 + t) ^ (3 / 2 : ℝ) = (1 + t) * Real.sqrt (1 + t) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add ht1, Real.rpow_one, Real.sqrt_eq_rpow]
  have hr_sq : ((1 + t) ^ (3 / 2 : ℝ)) ^ 2 = (1 + t) ^ 3 := by
    rw [hr32, mul_pow, Real.sq_sqrt ht1.le]; ring
  have hcmp : 1 / (1 + t) ^ (3 / 2 : ℝ) < (1 + 3 / 5 * t) / (1 + 2 * t + 6 / 5 * t ^ 2) := by
    rw [div_lt_div_iff₀ (Real.rpow_pos_of_pos ht1 _) (by positivity), one_mul]
    have hprod_lt : (1 + 2 * t + 6 / 5 * t ^ 2) ^ 2 <
        ((1 + 3 / 5 * t) * (1 + t) ^ (3 / 2 : ℝ)) ^ 2 := by
      rw [mul_pow, hr_sq]
      exact hsq
    rw [← Real.sqrt_sq (by positivity : 0 ≤ 1 + 2 * t + 6 / 5 * t ^ 2),
      ← Real.sqrt_sq (by positivity : 0 ≤ (1 + 3 / 5 * t) * (1 + t) ^ (3 / 2 : ℝ))]
    exact Real.sqrt_lt_sqrt (by positivity) hprod_lt
  calc 2 * x / (3 * (1 + t) ^ (3 / 2 : ℝ))
      = (2 * x / 3) * (1 / (1 + t) ^ (3 / 2 : ℝ)) := by ring
    _ < (2 * x / 3) * ((1 + 3 / 5 * t) / (1 + 2 * t + 6 / 5 * t ^ 2)) :=
        mul_lt_mul_of_pos_left hcmp (by positivity)
    _ ≤ 1 / x - 2 / Real.sinh (2 * x) := hinv

/-! ### Lemma T.4(b), (c), (d), (f) -/

/-- `h_th(x) = log(tanh x / x) + x² / 3` (`mellin_airy_toolkit.tex`, Lemma T.4(b)). -/
noncomputable def ceHth (x : ℝ) : ℝ := Real.log (Real.tanh x / x) + x ^ 2 / 3

lemma ceHth_pos {x : ℝ} (hx : 0 < x) : 0 < ceHth x := by
  have h1 : ceEll x < x ^ 2 / 3 := by
    have hsq : 1 < Real.sqrt (1 + x ^ 2 / 3) := by
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ < Real.sqrt (1 + x ^ 2 / 3) := Real.sqrt_lt_sqrt zero_le_one (by linarith [sq_pos_of_pos hx])
    calc ceEll x < x ^ 2 / (3 * Real.sqrt (1 + x ^ 2 / 3)) := ceEll_lt hx
      _ < x ^ 2 / (3 * 1) := div_lt_div_of_pos_left (sq_pos_of_pos hx) (by norm_num) (by linarith)
      _ = x ^ 2 / 3 := by ring
  have hlog : Real.log (Real.tanh x / x) = -ceEll x := by
    unfold ceEll
    rw [← Real.log_inv, inv_div]
  dsimp [ceHth]
  linarith

lemma tanh_le_taylor_five {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.tanh x ≤ x - x ^ 3 / 3 + 2 / 15 * x ^ 5 := by
  let P : ℝ → ℝ := fun u => u - u ^ 3 / 3 + 2 / 15 * u ^ 5
  let D : ℝ → ℝ := fun u => P u - Real.tanh u
  have hP_nn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ P u := fun u hu => by
    dsimp [P]
    have hu0 : 0 ≤ u := hu.1
    have hpow : u ^ 3 ≤ u := by simpa using pow_le_pow_of_le_one hu.1 hu.2 (by decide : 1 ≤ 3)
    have h2 : 0 ≤ 2 / 15 * u ^ 5 := mul_nonneg (by norm_num) (pow_nonneg hu0 5)
    linarith
  have hP_deriv : ∀ u, HasDerivAt P (1 - u ^ 2 + 2 / 3 * u ^ 4) u := fun u => by
    have h1 : HasDerivAt (fun s : ℝ => s - s ^ 3 / 3) (1 - 3 * u ^ 2 / 3) u :=
      (hasDerivAt_id u).sub ((hasDerivAt_pow 3 u).div_const 3)
    have h2 : HasDerivAt (fun s : ℝ => 2 / 15 * s ^ 5) (2 / 15 * (5 * u ^ 4)) u :=
      (hasDerivAt_pow 5 u).const_mul (2 / 15)
    convert h1.add h2 using 1
    ring
  have hD_deriv : ∀ u, HasDerivAt D (1 - u ^ 2 + 2 / 3 * u ^ 4 - (1 - Real.tanh u ^ 2)) u := by
    intro u
    have ht : HasDerivAt Real.tanh (1 - Real.tanh u ^ 2) u := by
      convert hasDerivAt_tanh u using 1
      rw [Real.tanh_eq_sinh_div_cosh]
      have hch : Real.cosh u ≠ 0 := (Real.cosh_pos u).ne'
      have hsq : Real.cosh u ^ 2 - Real.sinh u ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq u
      field_simp
      linarith
    exact (hP_deriv u).sub ht
  have hP_ric : ∀ u : ℝ, 1 - P u ^ 2 ≤ 1 - u ^ 2 + 2 / 3 * u ^ 4 := by
    intro u
    have heq : (1 - u ^ 2 + 2 / 3 * u ^ 4) - (1 - P u ^ 2) =
        u ^ 6 / 225 * (4 * u ^ 4 - 20 * u ^ 2 + 85) := by
      dsimp [P]; ring
    have hq : 0 ≤ 4 * u ^ 4 - 20 * u ^ 2 + 85 := by
      nlinarith [sq_nonneg (2 * u ^ 2 - 5)]
    have hp : 0 ≤ u ^ 6 / 225 * (4 * u ^ 4 - 20 * u ^ 2 + 85) :=
      mul_nonneg (by positivity) hq
    linarith
  have hD0 : D 0 = 0 := by simp [D, P, Real.tanh_zero]
  by_contra H
  rw [not_le] at H
  have hDx : D x < 0 := by dsimp [D, P]; linarith
  let S : Set ℝ := {t ∈ Icc (0 : ℝ) x | 0 ≤ D t}
  have hS_ne : S.Nonempty := ⟨0, ⟨⟨le_rfl, hx0⟩, by linarith [hD0]⟩⟩
  have hS_bdd : BddAbove S := ⟨x, fun t ht => ht.1.2⟩
  set a : ℝ := sSup S
  have ha_ge : 0 ≤ a := le_csSup hS_bdd ⟨⟨le_rfl, hx0⟩, by linarith [hD0]⟩
  have ha_le : a ≤ x := csSup_le hS_ne fun t ht => ht.1.2
  have hD_cont : Continuous D :=
    (continuous_iff_continuousAt.mpr fun u => (hD_deriv u).continuousAt)
  have ha_mem : 0 ≤ D a := by
    have hc : IsClosed S :=
      (isClosed_Icc.inter (isClosed_le continuous_const hD_cont))
    exact (hc.csSup_mem hS_ne hS_bdd).2
  have ha_lt : a < x := lt_of_le_of_ne ha_le (fun h => by rw [h] at ha_mem; linarith)
  have hD_neg : ∀ t ∈ Ioo a x, D t < 0 := by
    intro t ht
    by_contra ht0
    rw [not_lt] at ht0
    have hmem : t ∈ S := ⟨⟨by linarith [ht.1], ht.2.le⟩, ht0⟩
    have := le_csSup hS_bdd hmem
    linarith [ht.1]
  have hmono : MonotoneOn D (Icc a x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a x) hD_cont.continuousOn
      (fun u _ => (hD_deriv u).differentiableAt.differentiableWithinAt) ?_
    intro u hu
    rw [interior_Icc] at hu
    rw [(hD_deriv u).deriv]
    have hDu : D u < 0 := hD_neg u hu
    have hPu : 0 ≤ P u := hP_nn u ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have htu : 0 ≤ Real.tanh u := by
      rcases eq_or_lt_of_le (by linarith [hu.1] : 0 ≤ u) with rfl | hpos
      · simp [Real.tanh_zero]
      · exact (tanh_pos_of_pos hpos).le
    have hric := hP_ric u
    have hdiff : 0 ≤ (Real.tanh u + P u) * (Real.tanh u - P u) :=
      mul_nonneg (add_nonneg htu hPu) (by dsimp [D] at hDu; linarith)
    linarith [show Real.tanh u ^ 2 - P u ^ 2 = (Real.tanh u + P u) * (Real.tanh u - P u) by ring]
  have := hmono ⟨le_rfl, ha_le⟩ ⟨ha_le, le_rfl⟩ ha_le
  linarith

/-- **Lemma T.4(b) (`(3.4)`, small-`x` and large-`x` upper bounds on `h_th`):** -/
theorem ceHth_le_of_le_one {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ceHth x ≤ 2 / 15 * x ^ 4 := by
  have ht : Real.tanh x / x ≤ 1 - x ^ 2 / 3 + 2 / 15 * x ^ 4 := by
    rw [div_le_iff₀ hx0]
    calc Real.tanh x ≤ x - x ^ 3 / 3 + 2 / 15 * x ^ 5 := tanh_le_taylor_five hx0.le hx1
      _ = (1 - x ^ 2 / 3 + 2 / 15 * x ^ 4) * x := by ring
  have hlog : Real.log (Real.tanh x / x) ≤ (1 - x ^ 2 / 3 + 2 / 15 * x ^ 4) - 1 := by
    have hq : 0 < Real.tanh x / x := div_pos (tanh_pos_of_pos hx0) hx0
    exact (Real.log_le_sub_one_of_pos hq).trans (by linarith)
  unfold ceHth
  linarith

theorem ceHth_lt_of_ge_one {x : ℝ} (hx1 : 1 ≤ x) :
    ceHth x < x ^ 4 / 3 := by
  have hx0 : 0 < x := by linarith
  have hlog : Real.log (Real.tanh x / x) < 0 :=
    Real.log_neg (div_pos (tanh_pos_of_pos hx0) hx0) ((div_lt_one hx0).mpr (tanh_lt_id hx0))
  have hx2_ge : 1 ≤ x ^ 2 := by nlinarith
  have hx24 : x ^ 2 ≤ x ^ 4 := by nlinarith [sq_nonneg x]
  unfold ceHth
  linarith

/-- Monotone-region edge cutoff `τ_*(L)` (`mellin_airy_toolkit.tex`, eq. `(3.6)`). -/
noncomputable def tauStar (L : ℝ) : ℝ :=
  if L ≤ 1 then Real.sqrt L / π else Real.exp ((L - 1) / 2) / π

/-- Edge phase derivative `Φ'(τ; L) = L + log(tanh(π τ / 2) / (π τ / 2))` (even in `τ`). -/
noncomputable def edgePhiDeriv (L τ : ℝ) : ℝ :=
  L + if τ = 0 then 0 else Real.log (Real.tanh (π * |τ| / 2) / (π * |τ| / 2))

/-- **Lemma T.4(c) (eq. `(3.7)`):** `Φ'(τ; L) ≥ L / 2` for all `L > 0` and `|τ| ≤ τ_*(L)`. -/
theorem edgePhiDeriv_ge {L τ : ℝ} (hL : 0 < L) (hτ : |τ| ≤ tauStar L) :
    L / 2 ≤ edgePhiDeriv L τ := by
  unfold edgePhiDeriv
  split_ifs with h0
  · linarith
  · have hx0 : 0 < π * |τ| / 2 := div_pos (mul_pos Real.pi_pos (abs_pos.mpr h0)) two_pos
    have hlog_eq : Real.log (Real.tanh (π * |τ| / 2) / (π * |τ| / 2)) = -ceEll (π * |τ| / 2) := by
      unfold ceEll; rw [← Real.log_inv, inv_div]
    rw [hlog_eq]
    by_cases hL1 : L ≤ 1
    · have hτ_le : |τ| ≤ Real.sqrt L / π := by simpa [tauStar, hL1] using hτ
      have hx_le : π * |τ| / 2 ≤ Real.sqrt L / 2 := by
        have := mul_le_mul_of_nonneg_left hτ_le Real.pi_pos.le
        rw [mul_div_cancel₀ _ Real.pi_ne_zero] at this
        linarith
      have hmono : ceEll (π * |τ| / 2) < (π * |τ| / 2) ^ 2 / 3 := by
        have h1 := ceEll_lt hx0
        have h2 : 1 < Real.sqrt (1 + (π * |τ| / 2) ^ 2 / 3) := by
          calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
            _ < Real.sqrt (1 + (π * |τ| / 2) ^ 2 / 3) :=
                Real.sqrt_lt_sqrt zero_le_one (by linarith [sq_pos_of_pos hx0])
        have h3 : (π * |τ| / 2) ^ 2 / (3 * Real.sqrt (1 + (π * |τ| / 2) ^ 2 / 3)) <
            (π * |τ| / 2) ^ 2 / 3 :=
          div_lt_div_of_pos_left (sq_pos_of_pos hx0) (by norm_num) (by linarith)
        linarith
      have hsq : (π * |τ| / 2) ^ 2 / 3 ≤ L / 12 := by
        have : (π * |τ| / 2) ^ 2 ≤ (Real.sqrt L / 2) ^ 2 :=
          pow_le_pow_left₀ hx0.le hx_le 2
        simp only [div_pow, Real.sq_sqrt hL.le] at this
        linarith
      linarith
    · have hLgt : 1 < L := not_le.mp hL1
      have hτ_le : |τ| ≤ Real.exp ((L - 1) / 2) / π := by simpa [tauStar, hL1] using hτ
      set xStar : ℝ := Real.exp ((L - 1) / 2) / 2
      have hxStar : 1 / 2 ≤ xStar := by
        have : 1 ≤ Real.exp ((L - 1) / 2) := Real.one_le_exp (by linarith)
        dsimp [xStar]; linarith
      have hx_le : π * |τ| / 2 ≤ xStar := by
        have := mul_le_mul_of_nonneg_left hτ_le Real.pi_pos.le
        rw [mul_div_cancel₀ _ Real.pi_ne_zero] at this
        dsimp [xStar]; linarith
      have hce_mono : ceEll (π * |τ| / 2) ≤ ceEll xStar :=
        ceEll_strictMonoOn.monotoneOn (mem_Ioi.mpr hx0) (mem_Ioi.mpr (by linarith)) hx_le
      -- Compute `-ceEll xStar = log(tanh xStar) - log xStar ≥ log(tanh(1/2)) - log xStar`
      have hth_half : Real.tanh (1 / 2 : ℝ) ≤ Real.tanh xStar := by
        have htmono : Monotone Real.tanh := monotone_of_deriv_nonneg
          (fun s => (hasDerivAt_tanh s).differentiableAt)
          fun s => by rw [(hasDerivAt_tanh s).deriv]; positivity
        exact htmono hxStar
      -- Bound `2 * tanh (1/2) > exp(-1/2)`:
      have hexp1 : (2.7 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hexp2 : Real.exp (1 / 2 : ℝ) ≥ 3 / 2 := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
      have htanh_val : Real.tanh (1 / 2 : ℝ) = (Real.exp 1 - 1) / (Real.exp 1 + 1) := by
        rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
        have h2 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
          rw [← Real.exp_add]; ring_nf
        have hpos : Real.exp (-(1 / 2 : ℝ)) = (Real.exp (1 / 2 : ℝ))⁻¹ := Real.exp_neg _
        have hne : Real.exp (1 / 2 : ℝ) ≠ 0 := (Real.exp_pos _).ne'
        rw [← h2, hpos]
        field_simp
      have h2t_lb : Real.exp (-1 / 2 : ℝ) ≤ 2 * Real.tanh (1 / 2 : ℝ) := by
        have he1 : Real.exp (-1 / 2 : ℝ) ≤ 2 / 3 := by
          rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.exp_neg]
          exact inv_anti₀ (by norm_num) hexp2 |>.trans (by norm_num)
        have he2 : (2 / 3 : ℝ) ≤ 2 * Real.tanh (1 / 2 : ℝ) := by
          rw [htanh_val, ← mul_div_assoc, le_div_iff₀ (by linarith)]
          nlinarith
        linarith
      have hlog_x : -ceEll xStar = Real.log (2 * Real.tanh xStar) - (L - 1) / 2 := by
        unfold ceEll
        have h2t : xStar / Real.tanh xStar = Real.exp ((L - 1) / 2) / (2 * Real.tanh xStar) := by
          dsimp [xStar]; ring
        rw [h2t, Real.log_div (Real.exp_pos _).ne' (mul_pos two_pos (tanh_pos_of_pos (by linarith))).ne',
          Real.log_exp]
        ring
      have hlog_tanh : (-1 / 2 : ℝ) ≤ Real.log (2 * Real.tanh xStar) := by
        rw [← Real.log_exp (-1 / 2 : ℝ)]
        exact Real.log_le_log (Real.exp_pos _) (h2t_lb.trans (by linarith))
      linarith

/-! ### Lemma T.4(d)/(e)/(f) (`Φ''`, `Φ'''`, `(M1)`, `(M2)`) -/

/-- `Φ''(τ)` for `τ ≠ 0` (`mellin_airy_toolkit.tex`, Lemma T.4(d)). -/
noncomputable def edgePhiDeriv2 (τ : ℝ) : ℝ :=
  -π * (Real.sinh (π * τ) - π * τ) / (π * τ * Real.sinh (π * τ))

/-- `Φ'''(τ)` for `τ ≠ 0` (`mellin_airy_toolkit.tex`, Lemma T.4(d)). -/
noncomputable def edgePhiDeriv3 (τ : ℝ) : ℝ :=
  π ^ 2 * (1 / (π * τ) ^ 2 - Real.cosh (π * τ) / Real.sinh (π * τ) ^ 2)

lemma six_sinh_sub_le_sq_sinh {y : ℝ} (hy : 0 ≤ y) :
    6 * (Real.sinh y - y) ≤ y ^ 2 * Real.sinh y := by
  -- Difference has derivative `y² cosh y + 2 y sinh y - 6 cosh y + 6` ... better: direct Taylor `sinh y - y ≤ ...`!
  -- Wait: `d/dy(y² sinh y - 6 sinh y + 6 y) = (y² - 6) cosh y + 2 y sinh y + 6`
  -- `d² = 2y cosh y + (y² - 6) sinh y + 2 sinh y + 2y cosh y = 4 y cosh y + (y² - 4) sinh y`
  -- `d³ = 4 cosh y + 4 y sinh y + 2 y sinh y + (y² - 4) cosh y = y² cosh y + 6 y sinh y ≥ 0`!!
  let d0 : ℝ → ℝ := fun u => u ^ 2 * Real.sinh u - 6 * (Real.sinh u - u)
  let d1 : ℝ → ℝ := fun u => (u ^ 2 - 6) * Real.cosh u + 2 * u * Real.sinh u + 6
  let d2 : ℝ → ℝ := fun u => 4 * u * Real.cosh u + (u ^ 2 - 4) * Real.sinh u
  let d3 : ℝ → ℝ := fun u => u ^ 2 * Real.cosh u + 6 * u * Real.sinh u
  have hd3 : ∀ u ≥ 0, 0 ≤ d3 u := fun u hu => by
    dsimp [d3]
    exact add_nonneg (mul_nonneg (sq_nonneg u) (Real.cosh_pos u).le)
      (mul_nonneg (mul_nonneg (by norm_num) hu) (sinh_nonneg_of_nonneg hu))
  have hd2 : ∀ u ≥ 0, 0 ≤ d2 u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg d3 (by simp [d2]) hd3 (fun s => by
      have hA : HasDerivAt (fun t => 4 * t * Real.cosh t) (4 * Real.cosh s + 4 * s * Real.sinh s) s :=
        (((hasDerivAt_id s).const_mul 4).mul (Real.hasDerivAt_cosh s)).congr_deriv (by dsimp; ring)
      have hB : HasDerivAt (fun t => (t ^ 2 - 4) * Real.sinh t)
          (2 * s * Real.sinh s + (s ^ 2 - 4) * Real.cosh s) s :=
        (((hasDerivAt_pow 2 s).sub (hasDerivAt_const s 4)).mul (Real.hasDerivAt_sinh s)).congr_deriv
          (by dsimp; ring)
      exact (hA.add hB).congr_deriv (by dsimp [d3]; ring)) hu
  have hd1 : ∀ u ≥ 0, 0 ≤ d1 u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg d2 (by simp [d1]) hd2 (fun s => by
      have hA : HasDerivAt (fun t => (t ^ 2 - 6) * Real.cosh t)
          (2 * s * Real.cosh s + (s ^ 2 - 6) * Real.sinh s) s :=
        (((hasDerivAt_pow 2 s).sub (hasDerivAt_const s 6)).mul (Real.hasDerivAt_cosh s)).congr_deriv
          (by dsimp; ring)
      have hB : HasDerivAt (fun t => 2 * t * Real.sinh t) (2 * Real.sinh s + 2 * s * Real.cosh s) s :=
        (((hasDerivAt_id s).const_mul 2).mul (Real.hasDerivAt_sinh s)).congr_deriv (by dsimp; ring)
      exact ((hA.add hB).add (hasDerivAt_const s 6)).congr_deriv (by dsimp [d2]; ring)) hu
  have h0 := nonneg_of_zero_of_deriv_nonneg (g := d0) d1 (by dsimp [d0]; simp) hd1 (fun s => by
    have hA : HasDerivAt (fun t => t ^ 2 * Real.sinh t)
        (2 * s * Real.sinh s + s ^ 2 * Real.cosh s) s :=
      ((hasDerivAt_pow 2 s).mul (Real.hasDerivAt_sinh s)).congr_deriv (by simp [pow_one])
    have hB : HasDerivAt (fun t => 6 * (Real.sinh t - t)) (6 * (Real.cosh s - 1)) s :=
      ((Real.hasDerivAt_sinh s).sub (hasDerivAt_id s)).const_mul 6
    exact (hA.sub hB).congr_deriv (by dsimp [d1]; ring)) hy
  dsimp [d0] at h0; linarith

/-- **Lemma T.4(d) (`Φ''` upper bound):** for `τ ≠ 0`, `|Φ''(τ)| ≤ min (π²/6 |τ|, |τ|⁻¹)`. -/
theorem edgePhiDeriv2_abs_le {τ : ℝ} (hτ : τ ≠ 0) :
    |edgePhiDeriv2 τ| ≤ min (π ^ 2 / 6 * |τ|) |τ|⁻¹ := by
  have hodd : ∀ t, edgePhiDeriv2 (-t) = -edgePhiDeriv2 t := fun t => by
    unfold edgePhiDeriv2
    simp only [mul_neg, Real.sinh_neg]
    ring
  wlog hpos : 0 < τ generalizing τ
  · rcases lt_or_gt_of_ne hτ with hlt | hgt
    · have := this (neg_ne_zero.mpr hτ) (neg_pos.mpr hlt)
      simpa [hodd, abs_neg] using this
    · exact this hτ hgt
  set y : ℝ := π * τ
  have hy : 0 < y := mul_pos Real.pi_pos hpos
  have hsh : 0 < Real.sinh y := by linarith [sinh_gt_id hy]
  have hsh_ge : y ≤ Real.sinh y := (sinh_gt_id hy).le
  have hval : |edgePhiDeriv2 τ| = π * (Real.sinh y - y) / (y * Real.sinh y) := by
    unfold edgePhiDeriv2
    rw [show -π * (Real.sinh (π * τ) - π * τ) / (π * τ * Real.sinh (π * τ)) =
        -(π * (Real.sinh y - y) / (y * Real.sinh y)) by dsimp [y]; ring, abs_neg,
      abs_of_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (mul_pos hy hsh).le)]
  rw [hval, abs_of_pos hpos, le_min_iff]
  constructor
  · have h6 := six_sinh_sub_le_sq_sinh hy.le
    calc π * (Real.sinh y - y) / (y * Real.sinh y)
        ≤ π * (y ^ 2 * Real.sinh y / 6) / (y * Real.sinh y) := by gcongr; linarith
      _ = π ^ 2 / 6 * τ := by dsimp [y]; field_simp
  · have h1 : Real.sinh y - y ≤ Real.sinh y := by linarith
    calc π * (Real.sinh y - y) / (y * Real.sinh y)
        ≤ π * Real.sinh y / (y * Real.sinh y) := by gcongr
      _ = τ⁻¹ := by dsimp [y]; field_simp

/-- **Lemma T.4(e) (`P3` / `M2` lower bound):** for `τ ≠ 0`, `|τ| / (1 + τ²) ≤ π² |τ| / (6 + π² τ²) ≤ |Φ''(τ)|`. -/
theorem edgePhiDeriv2_abs_ge {τ : ℝ} (hτ : τ ≠ 0) :
    |τ| / (1 + τ ^ 2) ≤ π ^ 2 * |τ| / (6 + π ^ 2 * τ ^ 2) ∧
      π ^ 2 * |τ| / (6 + π ^ 2 * τ ^ 2) ≤ |edgePhiDeriv2 τ| := by
  have hodd : ∀ t, edgePhiDeriv2 (-t) = -edgePhiDeriv2 t := fun t => by
    unfold edgePhiDeriv2; simp only [mul_neg, Real.sinh_neg]; ring
  wlog hpos : 0 < τ generalizing τ
  · rcases lt_or_gt_of_ne hτ with hlt | hgt
    · have := this (neg_ne_zero.mpr hτ) (neg_pos.mpr hlt)
      simpa [hodd, abs_neg, neg_sq] using this
    · exact this hτ hgt
  set y : ℝ := π * τ
  have hy : 0 < y := mul_pos Real.pi_pos hpos
  have hsh : 0 < Real.sinh y := by linarith [sinh_gt_id hy]
  have hpi2 : (6 : ℝ) ≤ π ^ 2 := by nlinarith [Real.pi_gt_three]
  constructor
  · rw [abs_of_pos hpos, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg τ, hpi2]
  · have hval : |edgePhiDeriv2 τ| = π * (Real.sinh y - y) / (y * Real.sinh y) := by
      unfold edgePhiDeriv2
      rw [show -π * (Real.sinh (π * τ) - π * τ) / (π * τ * Real.sinh (π * τ)) =
          -(π * (Real.sinh y - y) / (y * Real.sinh y)) by dsimp [y]; ring, abs_neg,
        abs_of_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le (by linarith [sinh_gt_id hy])) (mul_pos hy hsh).le)]
    have h6 : y ^ 3 ≤ 6 * (Real.sinh y - y) := by linarith [sinh_taylor_lower hy.le, pow_pos hy 5]
    rw [hval, abs_of_pos hpos, show π ^ 2 * τ / (6 + π ^ 2 * τ ^ 2) = π * (y / (6 + y ^ 2)) by
      dsimp [y]; ring, mul_div_assoc π (Real.sinh y - y)]
    refine mul_le_mul_of_nonneg_left ?_ Real.pi_pos.le
    rw [div_le_div_iff₀ (by positivity) (mul_pos hy hsh)]
    nlinarith

/-- **Lemma T.4(d) (`Φ'''` upper bound):** for `τ ≠ 0`, `|Φ'''(τ)| ≤ π² / 3`. -/
theorem edgePhiDeriv3_abs_le {τ : ℝ} (hτ : τ ≠ 0) :
    |edgePhiDeriv3 τ| ≤ π ^ 2 / 3 := by
  have heven : ∀ t, edgePhiDeriv3 (-t) = edgePhiDeriv3 t := fun t => by
    unfold edgePhiDeriv3; simp only [mul_neg, neg_sq, Real.cosh_neg, Real.sinh_neg]
  wlog hpos : 0 < τ generalizing τ
  · rcases lt_or_gt_of_ne hτ with hlt | hgt
    · have := this (neg_ne_zero.mpr hτ) (neg_pos.mpr hlt)
      simpa [heven] using this
    · exact this hτ hgt
  set y : ℝ := π * τ
  have hy : 0 < y := mul_pos Real.pi_pos hpos
  have hsh : 0 < Real.sinh y := by linarith [sinh_gt_id hy]
  -- Prove `-1/6 ≤ 1/y² - cosh y / sinh² y ≤ 1/3`!
  -- Upper: `1/y² - cosh y / sinh² y ≤ 1/y² - 1/sinh² y ≤ 1/3` iff `3(sinh² y - y²) ≤ y² sinh² y`.
  -- Notice `sinh² y = (cosh(2y) - 1)/2`! So `3(cosh(2y) - 1 - 2 y²) ≤ y² (cosh(2y) - 1)`!
  have hup_poly : 3 * (Real.sinh y ^ 2 - y ^ 2) ≤ y ^ 2 * Real.sinh y ^ 2 := by
    -- With `z = 2 y`: `d/dy(y² sinh² y - 3 sinh² y + 3 y²) = (2y² - 6) sinh y cosh y + 2y sinh² y + 6y` ...
    -- Even easier via `6 * (sinh y - y) ≤ y² sinh y` (`h6`!) and `sinh y + y ≤ ...`:
    -- Wait: check directly with `d0(y) = (y² - 3) sinh² y + 3 y²`:
    -- Wait: `(cosh(2y) - 1)` has positive Taylor coefficients `(2y)^{2k}/(2k)!`!
    -- Compare `d0(u) = (u² - 3) * sinh u ^ 2 + 3 * u ^ 2`:
    -- `d0' = 2 u sinh² u + (u² - 3) * sinh(2u) + 6 u`? No, check `6 <= 2k(2k-1)` needs `d/du` 4 times or `d1, d2, d3`!
    -- Let `F(u) = (u² - 3) * (Real.cosh (2 * u) - 1) / 2 + 3 * u²`? Even simpler without `/2`:
    -- `G0(u) = (u² - 3) * Real.cosh (2 * u) + 5 * u² + 3` (= `2 * (y² sinh² y - 3 sinh² y + 3 y²)`!).
    -- Check: `G0(0) = 0`, `G1(u) = 2u cosh(2u) + 2(u²-3) sinh(2u) + 10u`, `G1(0) = 0`,
    -- `G2(u) = 2 cosh(2u) + 4u sinh(2u) + 4u sinh(2u) + 4(u²-3) cosh(2u) + 10 = (4u² - 10) cosh(2u) + 8u sinh(2u) + 10`, `G2(0) = 0`,
    -- `G3(u) = 8u cosh(2u) + (8u² - 20) sinh(2u) + 8 sinh(2u) + 16u cosh(2u) = 24u cosh(2u) + (8u² - 12) sinh(2u)`, `G3(0) = 0`,
    -- `G4(u) = 24 cosh(2u) + 48u sinh(2u) + 16u sinh(2u) + (16u² - 24) cosh(2u) = 16 u² cosh(2u) + 64 u sinh(2u) ≥ 0`!!
    let G0 : ℝ → ℝ := fun u => (u ^ 2 - 3) * Real.cosh (2 * u) + 5 * u ^ 2 + 3
    let G1 : ℝ → ℝ := fun u => 2 * u * Real.cosh (2 * u) + 2 * (u ^ 2 - 3) * Real.sinh (2 * u) + 10 * u
    let G2 : ℝ → ℝ := fun u => (4 * u ^ 2 - 10) * Real.cosh (2 * u) + 8 * u * Real.sinh (2 * u) + 10
    let G3 : ℝ → ℝ := fun u => 24 * u * Real.cosh (2 * u) + (8 * u ^ 2 - 12) * Real.sinh (2 * u)
    let G4 : ℝ → ℝ := fun u => 16 * u ^ 2 * Real.cosh (2 * u) + 64 * u * Real.sinh (2 * u)
    have h4 : ∀ u ≥ 0, 0 ≤ G4 u := fun u hu => by
      dsimp [G4]
      exact add_nonneg (mul_nonneg (by positivity) (Real.cosh_pos _).le)
        (mul_nonneg (by positivity) (sinh_nonneg_of_nonneg (by linarith)))
    have h3 : ∀ u ≥ 0, 0 ≤ G3 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg G4 (by norm_num [G3]) h4 (fun s => by
        have hc : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
          ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hs : HasDerivAt (fun t => Real.sinh (2 * t)) (2 * Real.cosh (2 * s)) s :=
          ((Real.hasDerivAt_sinh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hd := (((hasDerivAt_id s).const_mul 24).mul hc).add
          ((((hasDerivAt_pow 2 s).const_mul 8).sub (hasDerivAt_const s 12)).mul hs)
        exact hd.congr_deriv (by dsimp [G4]; ring)) hu
    have h2 : ∀ u ≥ 0, 0 ≤ G2 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg G3 (by norm_num [G2]) h3 (fun s => by
        have hc : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
          ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hs : HasDerivAt (fun t => Real.sinh (2 * t)) (2 * Real.cosh (2 * s)) s :=
          ((Real.hasDerivAt_sinh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hd := (((((hasDerivAt_pow 2 s).const_mul 4).sub (hasDerivAt_const s 10)).mul hc).add
          (((hasDerivAt_id s).const_mul 8).mul hs)).add (hasDerivAt_const s 10)
        exact hd.congr_deriv (by dsimp [G3]; ring)) hu
    have h1 : ∀ u ≥ 0, 0 ≤ G1 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg G2 (by norm_num [G1]) h2 (fun s => by
        have hc : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
          ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hs : HasDerivAt (fun t => Real.sinh (2 * t)) (2 * Real.cosh (2 * s)) s :=
          ((Real.hasDerivAt_sinh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hd := ((((hasDerivAt_id s).const_mul 2).mul hc).add
          ((((hasDerivAt_pow 2 s).sub (hasDerivAt_const s 3)).const_mul 2).mul hs)).add
          ((hasDerivAt_id s).const_mul 10)
        exact hd.congr_deriv (by dsimp [G2]; simp only [pow_one]; ring)) hu
    have h0 := nonneg_of_zero_of_deriv_nonneg (g := G0) G1 (by simp [G0]) h1 (fun s => by
      have hc : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
        ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
      have hd := ((((hasDerivAt_pow 2 s).sub (hasDerivAt_const s 3)).mul hc).add
        ((hasDerivAt_pow 2 s).const_mul 5)).add (hasDerivAt_const s 3)
      exact hd.congr_deriv (by dsimp [G1]; simp only [pow_one]; ring)) hy.le
    have hch2 : Real.cosh (2 * y) = 2 * Real.sinh y ^ 2 + 1 := by
      have := Real.cosh_sq_sub_sinh_sq y
      rw [Real.cosh_two_mul]
      nlinarith
    dsimp [G0] at h0
    rw [hch2] at h0
    linarith
  have hlo_poly : 6 * y ^ 2 * Real.cosh y ≤ (6 + y ^ 2) * Real.sinh y ^ 2 := by
    -- Notice `2 * ((6 + y²) sinh² y - 6 y² cosh y) = (6 + y²) cosh(2y) - 12 y² cosh y + (-6 - y²)`!
    -- Better: `cosh y ≤ cosh(2y)`? No, differentiate `H0(u) = (6 + u²) sinh² u - 6 u² cosh u`:
    -- Wait: `(6 + u²) * (cosh(2u) - 1) - 12 u² cosh u` has derivatives:
    -- `H0(u) = (6 + u²) * cosh(2u) - 12 u² cosh u - u² - 6`,
    -- `H1(u) = 2u cosh(2u) + (12 + 2u²) sinh(2u) - 24 u cosh u - 12 u² sinh u - 2u`,
    -- `H2(u) = (26 + 4u²) cosh(2u) + 8u sinh(2u) - (24 + 12u²) cosh u - 48u sinh u - 2`,
    --Wait: look at the Maclaurin check in paper: `g ≥ -1/6` follows from `3 (sinh² y - y²) ≥ ...`? No!
    -- Check Taylor of `cosh u = 1 + u²/2 + u⁴/24 + ...`: wait `12 u² cosh u` grows slower than `cosh(2u)`!
    -- Even easier: let `f(u) = u * √(6 / (6 + u²))` vs `tanh u`?! No, we ALREADY proved `coth z - 1/z ≤ z/3` AND `six_sinh_sub_le_sq_sinh`!
    -- Look at `six_sinh_sub_le_sq_sinh`: Wait — `(6 + u²) sinh² u - 6 u² cosh u`:
    -- Compute `H0(u) = (6 + u²) (Real.cosh (2 * u) - 1) - 12 * u² * Real.cosh u`:
    --Wait: `sinh² u = (cosh(2u) - 1)/2`, check `H3(u)` and `H4(u)` at `0`:
    -- `H0 = (6+u²) cosh(2u) - 12 u² cosh u - u² - 6` -> `H0(0)=0`.
    -- `H1 = 2u cosh(2u) + 2(6+u²) sinh(2u) - 24u cosh u - 12u² sinh u - 2u` -> `H1(0)=0`.
    -- `H2 = (26 + 4u²) cosh(2u) + 8u sinh(2u) - (24 + 12u²) cosh u - 48u sinh u - 2` -> `H2(0)=0`.
    -- `H3 = 16u cosh(2u) + (60 + 8u²) sinh(2u) - 72u cosh u - (72 + 12u²) sinh u` -> `H3(0)=0`.
    -- `H4 = (136 + 16u²) cosh(2u) + 64u sinh(2u) - (144 + 12u²) cosh u - 96u sinh u` -> `H4(0) = -8`?! WAIT: why `-8`?!
    -- At `u = 0`, coefficient of `u⁴`: in `(6+u²) sinh² u = (6+u²)(u² + u⁴/3 + ...)` it is `2 + 1 = 3` (`×2 = 6`); in `6 u² cosh u = 6u²(1 + u²/2 + ...)` it is `3` (`×2 = 6`)!
    -- So `H4(0) = 24 * (3 - 3) = 0`!! WHY did my quick differentiation get `-8`? Because `2*(6+u²) -> 12+2u²` in `H1`, `2*(12+2u²) = 24 + 4u²`, plus `2 = 26`, so `(26+4u²)`, `H2 -> (8u) + 2(26+4u²) = 52 + 8u² + ...`!
    -- Let's check exact coefficients!
    -- Actually, look at the `k`-th derivative via the identity `12 u² cosh u = ...`:
    -- Even BETTER! What is `12 * y² cosh y ≤ 2 * (6 + y²) sinh² y` WITHOUT 5th derivatives?!
    -- Factor out `sinh y`? Wait: for `y ≥ 2`, `2 sinh² y = cosh(2y) - 1`, and `cosh y` vs `sinh² y`:
    -- Wait: `(cosh u - 1) = 2 sinh²(u/2)`!
    -- On `u ≥ 0`, compare `sinh u` and `u cosh u`... Wait: `H0` ONLY needs 4th derivative `H4(u)` where `(136 - 144)` WAS just a typo in my mental `H3`! Look carefully:
    -- `H0(u) = (6 + u²) * cosh(2u) - 12 u² * cosh u - u² - 6`
    -- `H1(u) = 2 u cosh(2u) + 2(6 + u²) sinh(2u) - 24 u cosh u - 12 u² sinh u - 2 u`
    -- `H2(u) = 2 cosh(2u) + 4 u sinh(2u) + 4 u sinh(2u) + 4(6 + u²) cosh(2u) - 24 cosh u - 24 u sinh u - 24 u sinh u - 12 u² cosh u - 2`
    --       `= (26 + 4u²) cosh(2u) + 8 u sinh(2u) - (24 + 12u²) cosh u - 48 u sinh u - 2`
    -- `H3(u) = 8 u cosh(2u) + 2(26 + 4u²) sinh(2u) + 8 sinh(2u) + 16 u cosh(2u) - 24 u cosh u - (24 + 12u²) sinh u - 48 sinh u - 48 u cosh u`
    --       `= 24 u cosh(2u) + (60 + 8u²) sinh(2u) - 72 u cosh u - (72 + 12u²) sinh u`
    -- Check `H3(0) = 0`!
    -- `H4(u) = 24 cosh(2u) + 48 u sinh(2u) + 16 u sinh(2u) + 2(60 + 8u²) cosh(2u) - 72 cosh u - 72 u sinh u - 24 u sinh u - (72 + 12u²) cosh u`
    --       `= (144 + 16u²) cosh(2u) + 64 u sinh(2u) - (144 + 12u²) cosh u - 96 u sinh u`!!
    -- YES!! `144 - 144 = 0` AT `u = 0`!
    -- AND rewrite `cosh(2u) = 2 cosh² u - 1 ≥ ...` and `sinh(2u) = 2 sinh u cosh u`!
    -- CHECK `H4(u)`!!
    -- `(144 + 16u²) cosh(2u) + 64 u sinh(2u) - (144 + 12u²) cosh u - 96 u sinh u`
    -- Notice `64 u sinh(2u) - 96 u sinh u = 32 u sinh u * (4 cosh u - 3) ≥ 32 u sinh u * 1 ≥ 0`!!
    -- AND `(144 + 16u²) cosh(2u) - (144 + 12u²) cosh u`: since `cosh(2u) ≥ cosh u ≥ 1` and `16 u² ≥ 12 u²`,
    -- `144 (cosh(2u) - cosh u) + u² (16 cosh(2u) - 12 cosh u) ≥ 0`!!
    -- SO `H4(u) ≥ 0` FOR EVERY `u ≥ 0` DIRECTLY FROM `cosh(2u) ≥ cosh u ≥ 1` AND `sinh(2u) = 2 sinh u cosh u`!!
    let H0 : ℝ → ℝ := fun u => (6 + u ^ 2) * Real.cosh (2 * u) - 12 * u ^ 2 * Real.cosh u - u ^ 2 - 6
    let H1 : ℝ → ℝ := fun u =>
      2 * u * Real.cosh (2 * u) + 2 * (6 + u ^ 2) * Real.sinh (2 * u) -
        24 * u * Real.cosh u - 12 * u ^ 2 * Real.sinh u - 2 * u
    let H2 : ℝ → ℝ := fun u =>
      (26 + 4 * u ^ 2) * Real.cosh (2 * u) + 8 * u * Real.sinh (2 * u) -
        (24 + 12 * u ^ 2) * Real.cosh u - 48 * u * Real.sinh u - 2
    let H3 : ℝ → ℝ := fun u =>
      24 * u * Real.cosh (2 * u) + (60 + 8 * u ^ 2) * Real.sinh (2 * u) -
        72 * u * Real.cosh u - (72 + 12 * u ^ 2) * Real.sinh u
    let H4 : ℝ → ℝ := fun u =>
      (144 + 16 * u ^ 2) * Real.cosh (2 * u) + 64 * u * Real.sinh (2 * u) -
        (144 + 12 * u ^ 2) * Real.cosh u - 96 * u * Real.sinh u
    have h4 : ∀ u ≥ 0, 0 ≤ H4 u := by
      intro u hu
      have hch1 : 1 ≤ Real.cosh u := Real.one_le_cosh u
      have hch2 : Real.cosh u ≤ Real.cosh (2 * u) := by
        rw [Real.cosh_two_mul]
        nlinarith [sq_nonneg (Real.cosh u - 1), Real.cosh_sq_sub_sinh_sq u]
      have hsh_eq : Real.sinh (2 * u) = 2 * Real.sinh u * Real.cosh u := Real.sinh_two_mul u
      have hsh_nn : 0 ≤ Real.sinh u := sinh_nonneg_of_nonneg hu
      dsimp [H4]
      rw [hsh_eq]
      have hterm1 : 0 ≤ 144 * (Real.cosh (2 * u) - Real.cosh u) := by linarith
      have hterm2 : 0 ≤ u ^ 2 * (16 * Real.cosh (2 * u) - 12 * Real.cosh u) :=
        mul_nonneg (sq_nonneg u) (by linarith)
      have hterm3 : 0 ≤ 32 * u * Real.sinh u * (4 * Real.cosh u - 3) :=
        mul_nonneg (mul_nonneg (by positivity) hsh_nn) (by linarith)
      linarith
    have h3 : ∀ u ≥ 0, 0 ≤ H3 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg H4 (by norm_num [H3]) h4 (fun s => by
        have hc2 : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
          ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hs2 : HasDerivAt (fun t => Real.sinh (2 * t)) (2 * Real.cosh (2 * s)) s :=
          ((Real.hasDerivAt_sinh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hA := ((hasDerivAt_id s).const_mul 24).mul hc2
        have hB := (((hasDerivAt_const s 60).add ((hasDerivAt_pow 2 s).const_mul 8)).mul hs2)
        have hC := ((hasDerivAt_id s).const_mul 72).mul (Real.hasDerivAt_cosh s)
        have hD := (((hasDerivAt_const s 72).add ((hasDerivAt_pow 2 s).const_mul 12)).mul (Real.hasDerivAt_sinh s))
        exact (((hA.add hB).sub hC).sub hD).congr_deriv (by dsimp [H4]; ring)) hu
    have h2 : ∀ u ≥ 0, 0 ≤ H2 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg H3 (by norm_num [H2]) h3 (fun s => by
        have hc2 : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
          ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hs2 : HasDerivAt (fun t => Real.sinh (2 * t)) (2 * Real.cosh (2 * s)) s :=
          ((Real.hasDerivAt_sinh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hA := (((hasDerivAt_const s 26).add ((hasDerivAt_pow 2 s).const_mul 4)).mul hc2)
        have hB := ((hasDerivAt_id s).const_mul 8).mul hs2
        have hC := (((hasDerivAt_const s 24).add ((hasDerivAt_pow 2 s).const_mul 12)).mul (Real.hasDerivAt_cosh s))
        have hD := ((hasDerivAt_id s).const_mul 48).mul (Real.hasDerivAt_sinh s)
        exact ((((hA.add hB).sub hC).sub hD).sub (hasDerivAt_const s 2)).congr_deriv (by dsimp [H3]; ring)) hu
    have h1 : ∀ u ≥ 0, 0 ≤ H1 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg H2 (by norm_num [H1]) h2 (fun s => by
        have hc2 : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
          ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hs2 : HasDerivAt (fun t => Real.sinh (2 * t)) (2 * Real.cosh (2 * s)) s :=
          ((Real.hasDerivAt_sinh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
        have hA := ((hasDerivAt_id s).const_mul 2).mul hc2
        have hB := (((hasDerivAt_const s 6).add (hasDerivAt_pow 2 s)).const_mul 2).mul hs2
        have hC := ((hasDerivAt_id s).const_mul 24).mul (Real.hasDerivAt_cosh s)
        have hD := ((hasDerivAt_pow 2 s).const_mul 12).mul (Real.hasDerivAt_sinh s)
        have hE := (hasDerivAt_id s).const_mul 2
        exact ((((hA.add hB).sub hC).sub hD).sub hE).congr_deriv
          (by dsimp [H2]; simp only [pow_one]; ring)) hu
    have h0 := nonneg_of_zero_of_deriv_nonneg (g := H0) H1 (by simp [H0]) h1 (fun s => by
      have hc2 : HasDerivAt (fun t => Real.cosh (2 * t)) (2 * Real.sinh (2 * s)) s :=
        ((Real.hasDerivAt_cosh (2 * s)).comp s ((hasDerivAt_id s).const_mul 2)).congr_deriv (by ring)
      have hA := ((hasDerivAt_const s 6).add (hasDerivAt_pow 2 s)).mul hc2
      have hB := ((hasDerivAt_pow 2 s).const_mul 12).mul (Real.hasDerivAt_cosh s)
      exact (((hA.sub hB).sub (hasDerivAt_pow 2 s)).sub (hasDerivAt_const s 6)).congr_deriv
        (by dsimp [H1]; simp only [pow_one]; ring)) hy.le
    have hch2 : Real.cosh (2 * y) = 2 * Real.sinh y ^ 2 + 1 := by
      have := Real.cosh_sq_sub_sinh_sq y
      rw [Real.cosh_two_mul]
      nlinarith
    dsimp [H0] at h0
    rw [hch2] at h0
    linarith
  have hden_pos : 0 < y ^ 2 * Real.sinh y ^ 2 := mul_pos (sq_pos_of_pos hy) (sq_pos_of_pos hsh)
  have hup : 1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2 ≤ 1 / 3 := by
    have h1 : 1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2 ≤ 1 / y ^ 2 - 1 / Real.sinh y ^ 2 := by
      have := Real.one_le_cosh y
      gcongr
    have h2 : 1 / y ^ 2 - 1 / Real.sinh y ^ 2 ≤ 1 / 3 := by
      rw [div_sub_div _ _ (sq_pos_of_pos hy).ne' (sq_pos_of_pos hsh).ne',
        div_le_div_iff₀ hden_pos three_pos]
      linarith
    linarith
  have hlo : -1 / 6 ≤ 1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2 := by
    rw [div_sub_div _ _ (sq_pos_of_pos hy).ne' (sq_pos_of_pos hsh).ne',
      le_div_iff₀ hden_pos]
    linarith
  have habs_g : |1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2| ≤ 1 / 3 :=
    abs_le.mpr ⟨by linarith, hup⟩
  unfold edgePhiDeriv3
  rw [abs_mul, abs_of_pos (sq_pos_of_pos Real.pi_pos)]
  calc π ^ 2 * |1 / y ^ 2 - Real.cosh y / Real.sinh y ^ 2|
      ≤ π ^ 2 * (1 / 3) := by gcongr
    _ = π ^ 2 / 3 := by ring

/-- **Lemma T.4(f) (`M2`):** for `τ > 0`, `m(τ) := ceEll (π τ / 2)` satisfies
`τ / (1 + τ²) ≤ m'(τ) ≤ (π²/6) τ / (1 + τ²)`. -/
theorem m2_bounds {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun s => ceEll (π * s / 2)) (-edgePhiDeriv2 τ) τ ∧
      τ / (1 + τ ^ 2) ≤ -edgePhiDeriv2 τ ∧
      -edgePhiDeriv2 τ ≤ (π ^ 2 / 6) * (τ / (1 + τ ^ 2)) := by
  have harg : 0 < π * τ / 2 := by positivity
  have hd : HasDerivAt (fun s => ceEll (π * s / 2)) (-edgePhiDeriv2 τ) τ := by
    have h1 : HasDerivAt (fun s => π * s / 2) (π / 2) τ := by
      simpa using ((hasDerivAt_id τ).const_mul π).div_const 2
    refine ((ceEll_hasDerivAt harg).comp τ h1).congr_deriv ?_
    unfold edgePhiDeriv2
    have hsh : Real.sinh (π * τ) ≠ 0 := (by linarith [sinh_gt_id (mul_pos Real.pi_pos hτ)] : 0 < Real.sinh (π * τ)).ne'
    have hτ0 : τ ≠ 0 := hτ.ne'
    rw [show 2 * (π * τ / 2) = π * τ by ring]
    field_simp
  have hneg : 0 ≤ -edgePhiDeriv2 τ := by
    unfold edgePhiDeriv2
    have hsh : 0 < Real.sinh (π * τ) := by linarith [sinh_gt_id (mul_pos Real.pi_pos hτ)]
    have hsub : 0 ≤ Real.sinh (π * τ) - π * τ := by linarith [sinh_gt_id (mul_pos Real.pi_pos hτ)]
    have : -(-π * (Real.sinh (π * τ) - π * τ) / (π * τ * Real.sinh (π * τ))) =
        π * (Real.sinh (π * τ) - π * τ) / (π * τ * Real.sinh (π * τ)) := by ring
    rw [this]
    positivity
  have hlo := (edgePhiDeriv2_abs_ge hτ.ne').1.trans (edgePhiDeriv2_abs_ge hτ.ne').2
  rw [abs_of_pos hτ, ← abs_neg (edgePhiDeriv2 τ), abs_of_nonneg hneg] at hlo
  -- Upper bound `(M2)` from `(144)`: `π² (y² sinh y - 6 (sinh y - y)) ≥ 6 y² (sinh y - y)`!
  -- Wait: let's check `y = π τ`: `(-edgePhiDeriv2 τ) * (1 + τ²) / τ = (π² + y²)(sinh y - y) / (y² sinh y) ≤ π² / 6`
  -- `iff 6 (π² + y²)(sinh y - y) ≤ π² y² sinh y` `iff 6 y² (sinh y - y) ≤ π² [y² sinh y - 6(sinh y - y)]`!
  -- Wait: note `y² sinh y - 6(sinh y - y)` is `d0(y) ≥ 0`, AND does `(π² - 6)` give `π²/6`?
  -- Wait: `6 (π² + y²) (sinh y - y) ≤ π² y² sinh y` iff `6 π² (sinh y - y) ≤ (π² - 6) y² sinh y + 6 y³`!!
  -- Even stronger: prove `(6 + y²) * ...`: check `(π² - 6) * 2k(2k+1) ≥ 6 π²` is `3.8696 * 20 ≥ 59.2`!
  -- Or simply differentiate `M0(y) = π² y² sinh y - 6(π² + y²)(sinh y - y)` (`π² > 9.869 > 6`)!
  -- Check `M0(0)=0`, `M1(0)=0`, `M2(0)=0`, `M3(0) = 6 (π² - 6) * 0 ...`:
  -- Wait: `M0(y) = ((π² - 6) y² - 6 π²) sinh y + 6 (π² + y²) y`!
  -- `M0(0)=0`.
  -- `M1(y) = 2(π² - 6) y sinh y + ((π² - 6) y² - 6 π²) cosh y + 6 π² + 18 y²` -> `M1(0) = 0`!
  -- `M2(y) = 2(π² - 6) sinh y + 4(π² - 6) y cosh y + ((π² - 6) y² - 6 π²) sinh y + 36 y`
  --       `= ((π² - 6) y² - 4 π² - 12) sinh y + 4(π² - 6) y cosh y + 36 y` -> `M2(0) = 0`!
  -- `M3(y) = 6(π² - 6) y sinh y + ((π² - 6) y² - 16) cosh y + 36`? Wait:
  -- check `y^3` term in `M0(y)`: `((π² - 6) y² - 6π²)(y + y³/6 + y⁵/120) + 6π² y + 6 y³`:
  -- `y³` coefficient is `(π² - 6) - π² + 6 = 0`!! So `M3(0) = 0` TOO (`2 * 6 - 16` check: `(π²-6)*0 - (4π²+12) + 4(π²-6) + 36 = -4π² - 12 + 4π² - 24 + 36 = 0`!!)!
  -- `M3(y) = 6(π² - 6) y sinh y + ((π² - 6) y² + (4 π² - 36? wait: -4π² - 12 + 4π² - 24 = -36)) cosh y + 36`!!
  -- CHECK `M3(0) = -36 + 36 = 0`!
  -- `M4(y) = 6(π² - 6) sinh y + 6(π² - 6) y cosh y + 2(π² - 6) y cosh y + ((π² - 6) y² - 36) sinh y`
  --       `= ((π² - 6) y² + 6 π² - 72) sinh y + 8 (π² - 6) y cosh y`? Wait `6 π² - 72 ≈ 59 - 72 < 0`! Oh, so differentiate 1 more time `M5`:
  -- Wait at `y=0`: `y⁵` coeff in `M0` is `((π²-6)/6 - 6π²/120) = (20 π² - 120 - 6π²)/120 = (14π² - 120)/120 ≈ 18/120 > 0`!
  -- Look at `M4(y)` at `y = 0`: `M4(0) = 0`, and `M5(y) = (20(π² - 6) - 36? no: 2(π²-6) y sinh y + ((π²-6)y² + 6π² - 72) cosh y + 8(π²-6) cosh y + 8(π²-6) y sinh y)`
  -- `= 10 (π² - 6) y sinh y + ((π² - 6) y² + 14 π² - 120) cosh y`!!
  -- AND `14 * π² - 120 > 14 * (3.14)^2 - 120 = 14 * 9.8596 - 120 = 138.034 - 120 > 0`!!
  -- AND `π² - 6 > 0` (`3.14^2 = 9.8596 > 6`)!!
  -- SO `M5(y) ≥ 0` FOR ALL `y ≥ 0` AUTOMATICALLY!!
  have hMup : -edgePhiDeriv2 τ ≤ (π ^ 2 / 6) * (τ / (1 + τ ^ 2)) := by
    set y : ℝ := π * τ
    have hy : 0 < y := mul_pos Real.pi_pos hτ
    have hsh : 0 < Real.sinh y := by linarith [sinh_gt_id hy]
    have hc_pi : 14 * π ^ 2 - 120 > 0 := by nlinarith [Real.pi_gt_three, show (3.14 : ℝ) < π by linarith [Real.pi_gt_d2]]
    have hpi6 : π ^ 2 - 6 > 0 := by nlinarith [Real.pi_gt_three]
    let M0 : ℝ → ℝ := fun u => ((π ^ 2 - 6) * u ^ 2 - 6 * π ^ 2) * Real.sinh u + 6 * π ^ 2 * u + 6 * u ^ 3
    let M1 : ℝ → ℝ := fun u =>
      2 * (π ^ 2 - 6) * u * Real.sinh u + ((π ^ 2 - 6) * u ^ 2 - 6 * π ^ 2) * Real.cosh u + 6 * π ^ 2 + 18 * u ^ 2
    let M2 : ℝ → ℝ := fun u =>
      ((π ^ 2 - 6) * u ^ 2 - 4 * π ^ 2 - 12) * Real.sinh u + 4 * (π ^ 2 - 6) * u * Real.cosh u + 36 * u
    let M3 : ℝ → ℝ := fun u =>
      6 * (π ^ 2 - 6) * u * Real.sinh u + ((π ^ 2 - 6) * u ^ 2 - 36) * Real.cosh u + 36
    let M4 : ℝ → ℝ := fun u =>
      ((π ^ 2 - 6) * u ^ 2 + 6 * π ^ 2 - 72) * Real.sinh u + 8 * (π ^ 2 - 6) * u * Real.cosh u
    let M5 : ℝ → ℝ := fun u =>
      10 * (π ^ 2 - 6) * u * Real.sinh u + ((π ^ 2 - 6) * u ^ 2 + 14 * π ^ 2 - 120) * Real.cosh u
    have hm5 : ∀ u ≥ 0, 0 ≤ M5 u := fun u hu => by
      dsimp [M5]
      refine add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hpi6.le) hu) (sinh_nonneg_of_nonneg hu))
        (mul_nonneg ?_ (Real.cosh_pos u).le)
      have : 0 ≤ (π ^ 2 - 6) * u ^ 2 := mul_nonneg hpi6.le (sq_nonneg u)
      linarith
    have hm4 : ∀ u ≥ 0, 0 ≤ M4 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg (g := M4) M5 (by simp [M4]) hm5 (fun s => by
        have hA : HasDerivAt (fun t => ((π ^ 2 - 6) * t ^ 2 + 6 * π ^ 2 - 72) * Real.sinh t)
            (2 * (π ^ 2 - 6) * s * Real.sinh s + ((π ^ 2 - 6) * s ^ 2 + 6 * π ^ 2 - 72) * Real.cosh s) s :=
          ((((((hasDerivAt_pow 2 s).const_mul (π ^ 2 - 6)).add
            (hasDerivAt_const s (6 * π ^ 2))).sub (hasDerivAt_const s 72)).mul
              (Real.hasDerivAt_sinh s))).congr_deriv
                (by simp only [Pi.add_apply, Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
                  add_zero, sub_zero]; ring)
        have hB : HasDerivAt (fun t => 8 * (π ^ 2 - 6) * t * Real.cosh t)
            (8 * (π ^ 2 - 6) * Real.cosh s + 8 * (π ^ 2 - 6) * s * Real.sinh s) s :=
          (((hasDerivAt_id s).const_mul (8 * (π ^ 2 - 6))).mul (Real.hasDerivAt_cosh s)).congr_deriv
            (by simp)
        exact (hA.add hB).congr_deriv (by dsimp [M5]; ring)) hu
    have hm3 : ∀ u ≥ 0, 0 ≤ M3 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg (g := M3) M4 (by simp [M3]) hm4 (fun s => by
        have hA : HasDerivAt (fun t => 6 * (π ^ 2 - 6) * t * Real.sinh t)
            (6 * (π ^ 2 - 6) * Real.sinh s + 6 * (π ^ 2 - 6) * s * Real.cosh s) s :=
          (((hasDerivAt_id s).const_mul (6 * (π ^ 2 - 6))).mul (Real.hasDerivAt_sinh s)).congr_deriv
            (by simp)
        have hB : HasDerivAt (fun t => ((π ^ 2 - 6) * t ^ 2 - 36) * Real.cosh t)
            (2 * (π ^ 2 - 6) * s * Real.cosh s + ((π ^ 2 - 6) * s ^ 2 - 36) * Real.sinh s) s :=
          ((((hasDerivAt_pow 2 s).const_mul (π ^ 2 - 6)).sub (hasDerivAt_const s 36)).mul
            (Real.hasDerivAt_cosh s)).congr_deriv
              (by simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero]; ring)
        exact ((hA.add hB).add (hasDerivAt_const s 36)).congr_deriv (by dsimp [M4]; ring)) hu
    have hm2 : ∀ u ≥ 0, 0 ≤ M2 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg (g := M2) M3 (by simp [M2]) hm3 (fun s => by
        have hA : HasDerivAt (fun t => ((π ^ 2 - 6) * t ^ 2 - 4 * π ^ 2 - 12) * Real.sinh t)
            (2 * (π ^ 2 - 6) * s * Real.sinh s + ((π ^ 2 - 6) * s ^ 2 - 4 * π ^ 2 - 12) * Real.cosh s) s :=
          ((((((hasDerivAt_pow 2 s).const_mul (π ^ 2 - 6)).sub (hasDerivAt_const s (4 * π ^ 2))).sub
            (hasDerivAt_const s 12)).mul (Real.hasDerivAt_sinh s))).congr_deriv
              (by simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero]; ring)
        have hB : HasDerivAt (fun t => 4 * (π ^ 2 - 6) * t * Real.cosh t)
            (4 * (π ^ 2 - 6) * Real.cosh s + 4 * (π ^ 2 - 6) * s * Real.sinh s) s :=
          (((hasDerivAt_id s).const_mul (4 * (π ^ 2 - 6))).mul (Real.hasDerivAt_cosh s)).congr_deriv
            (by simp)
        exact ((hA.add hB).add ((hasDerivAt_id s).const_mul 36)).congr_deriv (by dsimp [M3]; ring)) hu
    have hm1 : ∀ u ≥ 0, 0 ≤ M1 u := fun u hu =>
      nonneg_of_zero_of_deriv_nonneg (g := M1) M2 (by simp [M1]) hm2 (fun s => by
        have hA : HasDerivAt (fun t => 2 * (π ^ 2 - 6) * t * Real.sinh t)
            (2 * (π ^ 2 - 6) * Real.sinh s + 2 * (π ^ 2 - 6) * s * Real.cosh s) s :=
          (((hasDerivAt_id s).const_mul (2 * (π ^ 2 - 6))).mul (Real.hasDerivAt_sinh s)).congr_deriv
            (by simp)
        have hB : HasDerivAt (fun t => ((π ^ 2 - 6) * t ^ 2 - 6 * π ^ 2) * Real.cosh t)
            (2 * (π ^ 2 - 6) * s * Real.cosh s + ((π ^ 2 - 6) * s ^ 2 - 6 * π ^ 2) * Real.sinh s) s :=
          ((((hasDerivAt_pow 2 s).const_mul (π ^ 2 - 6)).sub (hasDerivAt_const s (6 * π ^ 2))).mul
            (Real.hasDerivAt_cosh s)).congr_deriv
              (by simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero]; ring)
        exact (((hA.add hB).add (hasDerivAt_const s (6 * π ^ 2))).add
          ((hasDerivAt_pow 2 s).const_mul 18)).congr_deriv
            (by dsimp [M2]; simp only [pow_one]; ring)) hu
    have hm0 := nonneg_of_zero_of_deriv_nonneg (g := M0) M1 (by simp [M0]) hm1 (fun s => by
      have hA : HasDerivAt (fun t => ((π ^ 2 - 6) * t ^ 2 - 6 * π ^ 2) * Real.sinh t)
          (2 * (π ^ 2 - 6) * s * Real.sinh s + ((π ^ 2 - 6) * s ^ 2 - 6 * π ^ 2) * Real.cosh s) s :=
        ((((hasDerivAt_pow 2 s).const_mul (π ^ 2 - 6)).sub (hasDerivAt_const s (6 * π ^ 2))).mul
          (Real.hasDerivAt_sinh s)).congr_deriv
            (by simp only [Pi.sub_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one, sub_zero]; ring)
      exact ((hA.add ((hasDerivAt_id s).const_mul (6 * π ^ 2))).add
        ((hasDerivAt_pow 3 s).const_mul 6)).congr_deriv (by dsimp [M1]; ring)) hy.le
    unfold edgePhiDeriv2
    rw [show -(-π * (Real.sinh (π * τ) - π * τ) / (π * τ * Real.sinh (π * τ))) =
        π * (Real.sinh y - y) / (y * Real.sinh y) by dsimp [y]; ring]
    rw [show (π ^ 2 / 6) * (τ / (1 + τ ^ 2)) = π ^ 3 * y / (6 * (π ^ 2 + y ^ 2)) by
      dsimp [y]; field_simp]
    rw [div_le_div_iff₀ (mul_pos hy hsh) (by positivity)]
    dsimp [M0] at hm0
    have heq : (π ^ 3 * y) * (y * Real.sinh y) - (π * (Real.sinh y - y)) * (6 * (π ^ 2 + y ^ 2)) =
        π * (((π ^ 2 - 6) * y ^ 2 - 6 * π ^ 2) * Real.sinh y + 6 * π ^ 2 * y + 6 * y ^ 3) := by
      ring
    have hpos : 0 ≤ π * (((π ^ 2 - 6) * y ^ 2 - 6 * π ^ 2) * Real.sinh y + 6 * π ^ 2 * y + 6 * y ^ 3) :=
      mul_nonneg Real.pi_pos.le hm0
    linarith
  exact ⟨hd, hlo, hMup⟩

/-- **Lemma T.4(f) (`M1`):** for `τ > 0`, `m(τ) - m(τ / 2) ≥ (3 / 8) * τ² / (1 + τ²)`. -/
theorem m1_bound {τ : ℝ} (hτ : 0 < τ) :
    3 / 8 * τ ^ 2 / (1 + τ ^ 2) ≤ ceEll (π * τ / 2) - ceEll (π * (τ / 2) / 2) := by
  -- Proof of (M1) from `mellin_airy_toolkit.tex` l. 144:
  -- `m(x) - m(x/2) ≥ ∫_{x/2}^x s / (1 + s²) ds = (1/2) log((1 + x²)/(1 + x²/4)) ≥ (3/8) x²/(1 + x²)`.
  let φ : ℝ → ℝ := fun s => ceEll (π * s / 2) - 1 / 2 * Real.log (1 + s ^ 2)
  have hφ_mono : MonotoneOn φ (Ioi 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
    · refine ContinuousOn.sub ?_ ?_
      · intro s hs; exact (m2_bounds hs).1.continuousAt.continuousWithinAt
      · intro s _
        refine ContinuousAt.continuousWithinAt (ContinuousAt.mul continuousAt_const ?_)
        exact (Real.continuousAt_log (by positivity)).comp (by fun_prop)
    · intro s hs
      rw [interior_Ioi, mem_Ioi] at hs
      exact ((m2_bounds hs).1.sub (by
        have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s :=
          ((hasDerivAt_const s 1).add (hasDerivAt_pow 2 s)).congr_deriv (by simp [pow_one])
        exact ((h1.log (by positivity)).const_mul (1 / 2)))).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ioi, mem_Ioi] at hs
      have hm := m2_bounds hs
      have hd : HasDerivAt φ (-edgePhiDeriv2 s - s / (1 + s ^ 2)) s := by
        have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * s) s :=
          ((hasDerivAt_const s 1).add (hasDerivAt_pow 2 s)).congr_deriv (by simp [pow_one])
        have h2 := (h1.log (by positivity)).const_mul (1 / 2)
        exact (hm.1.sub h2).congr_deriv (by ring)
      rw [hd.deriv]
      linarith [hm.2.1]
  have hdiff : 1 / 2 * Real.log (1 + τ ^ 2) - 1 / 2 * Real.log (1 + (τ / 2) ^ 2) ≤
      ceEll (π * τ / 2) - ceEll (π * (τ / 2) / 2) := by
    have := hφ_mono (mem_Ioi.mpr (by positivity : 0 < τ / 2)) (mem_Ioi.mpr hτ) (by linarith)
    dsimp [φ] at this
    linarith
  -- Now prove `3/8 * u / (1 + u) ≤ (1/2) * log((1 + u)/(1 + u/4))` on `u ≥ 0` (`u = τ²`):
  let ψ : ℝ → ℝ := fun u =>
    (1 / 2 * Real.log (1 + u) - 1 / 2 * Real.log (1 + u / 4)) - 3 / 8 * u / (1 + u)
  have hψ_mono : MonotoneOn ψ (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · intro u hu
      have hu0 : 0 ≤ u := mem_Ici.mp hu
      have hu1 : 0 < 1 + u := by linarith
      have hu4 : 0 < 1 + u / 4 := by linarith
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.sub (ContinuousAt.sub ?_ ?_) ?_
      · exact ContinuousAt.mul continuousAt_const
          ((Real.continuousAt_log hu1.ne').comp (continuousAt_const.add continuousAt_id))
      · have hlog4 : ContinuousAt (fun x : ℝ => Real.log (1 + x / 4)) u :=
          ((((hasDerivAt_id u).div_const 4).const_add 1).log hu4.ne').continuousAt
        exact ContinuousAt.mul continuousAt_const hlog4
      · exact ContinuousAt.div (by fun_prop) (by fun_prop) hu1.ne'
    · intro u hu
      have hu0 : 0 ≤ u := (interior_subset hu : u ∈ Ici 0)
      have hu1 : 0 < 1 + u := by linarith
      have hu4 : 0 < 1 + u / 4 := by linarith
      have hd1 : HasDerivAt (fun s : ℝ => 1 / 2 * Real.log (1 + s)) (1 / (2 * (1 + u))) u :=
        ((((hasDerivAt_id u).const_add 1).log hu1.ne').const_mul (1 / 2 : ℝ)).congr_deriv
          (by dsimp; field_simp)
      have hd2 : HasDerivAt (fun s : ℝ => 1 / 2 * Real.log (1 + s / 4)) (1 / (2 * (4 + u))) u :=
        (((((hasDerivAt_id u).div_const 4).const_add 1).log hu4.ne').const_mul (1 / 2 : ℝ)).congr_deriv
          (by dsimp; field_simp)
      have hd3 : HasDerivAt (fun s : ℝ => 3 / 8 * s / (1 + s)) (3 / (8 * (1 + u) ^ 2)) u :=
        (((hasDerivAt_id u).const_mul (3 / 8 : ℝ)).div ((hasDerivAt_id u).const_add 1)
          hu1.ne').congr_deriv (by dsimp; field_simp; ring)
      exact ((hd1.sub hd2).sub hd3).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici, mem_Ioi] at hu
      have hu1 : 0 < 1 + u := by linarith
      have hu4 : 0 < 1 + u / 4 := by linarith
      have hd1 : HasDerivAt (fun s : ℝ => 1 / 2 * Real.log (1 + s)) (1 / (2 * (1 + u))) u :=
        ((((hasDerivAt_id u).const_add 1).log hu1.ne').const_mul (1 / 2 : ℝ)).congr_deriv
          (by dsimp; field_simp)
      have hd2 : HasDerivAt (fun s : ℝ => 1 / 2 * Real.log (1 + s / 4)) (1 / (2 * (4 + u))) u :=
        (((((hasDerivAt_id u).div_const 4).const_add 1).log hu4.ne').const_mul (1 / 2 : ℝ)).congr_deriv
          (by dsimp; field_simp)
      have hd3 : HasDerivAt (fun s : ℝ => 3 / 8 * s / (1 + s)) (3 / (8 * (1 + u) ^ 2)) u :=
        (((hasDerivAt_id u).const_mul (3 / 8 : ℝ)).div ((hasDerivAt_id u).const_add 1)
          hu1.ne').congr_deriv (by dsimp; field_simp; ring)
      have hd : HasDerivAt ψ (1 / (2 * (1 + u)) - 1 / (2 * (4 + u)) - 3 / (8 * (1 + u) ^ 2)) u :=
        (hd1.sub hd2).sub hd3
      rw [hd.deriv]
      have hden : 0 < (1 + u) ^ 2 * (4 + u) := by positivity
      have heq : 1 / (2 * (1 + u)) - 1 / (2 * (4 + u)) - 3 / (8 * (1 + u) ^ 2) =
          9 * u / (8 * (1 + u) ^ 2 * (4 + u)) := by
        field_simp; ring
      rw [heq]
      positivity
  have hψ_nn : 0 ≤ ψ (τ ^ 2) := by
    have h0 := hψ_mono le_rfl (sq_nonneg τ) (sq_nonneg τ)
    have hzero : ψ 0 = 0 := by simp [ψ]
    linarith
  dsimp [ψ] at hψ_nn
  have hsq : τ ^ 2 / 4 = (τ / 2) ^ 2 := by ring
  rw [hsq] at hψ_nn
  linarith

/-! ### Lemma T.3(1) `(cel:5.1)` and T.3(3) `(cel:5.5)` -/

/-- Taylor bounds on `sin` for `x ≥ 0`: `x - x³/6 ≤ sin x ≤ x - x³/6 + x⁵/120`. -/
lemma sin_taylor_lower_upper {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 6 ≤ Real.sin x ∧ Real.sin x ≤ x - x ^ 3 / 6 + x ^ 5 / 120 := by
  have d4 : ∀ u ≥ 0, 0 ≤ Real.cos u - (1 - u ^ 2 / 2) := fun u hu => by
    refine nonneg_of_zero_of_deriv_nonneg (g := fun s => Real.cos s - (1 - s ^ 2 / 2))
      (fun s => s - Real.sin s) (by simp)
      (fun s hs => by linarith [Real.sin_le hs])
      (fun s => ((Real.hasDerivAt_cos s).sub
        ((hasDerivAt_const s 1).sub ((hasDerivAt_pow 2 s).div_const 2))).congr_deriv (by dsimp; ring)) hu
  have d3 : ∀ u ≥ 0, 0 ≤ Real.sin u - (u - u ^ 3 / 6) := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg (g := fun s => Real.sin s - (s - s ^ 3 / 6))
      (fun s => Real.cos s - (1 - s ^ 2 / 2)) (by simp) d4
      (fun s => ((Real.hasDerivAt_sin s).sub
        ((hasDerivAt_id s).sub ((hasDerivAt_pow 3 s).div_const 6))).congr_deriv (by dsimp; ring)) hu
  have d5 : ∀ u ≥ 0, 0 ≤ (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg (g := fun s => (1 - s ^ 2 / 2 + s ^ 4 / 24) - Real.cos s)
      (fun s => Real.sin s - (s - s ^ 3 / 6)) (by simp)
      (fun s hs => by linarith [d3 s hs]) (fun s => by
        have h1 := ((hasDerivAt_const s 1).sub ((hasDerivAt_pow 2 s).div_const 2)).add
          ((hasDerivAt_pow 4 s).div_const 24)
        exact (h1.sub (Real.hasDerivAt_cos s)).congr_deriv (by dsimp; ring)) hu
  have d6 : ∀ u ≥ 0, 0 ≤ (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u := fun u hu =>
    nonneg_of_zero_of_deriv_nonneg (g := fun s => (s - s ^ 3 / 6 + s ^ 5 / 120) - Real.sin s)
      (fun s => (1 - s ^ 2 / 2 + s ^ 4 / 24) - Real.cos s) (by simp) d5
      (fun s => by
        have h1 := ((hasDerivAt_id s).sub ((hasDerivAt_pow 3 s).div_const 6)).add
          ((hasDerivAt_pow 5 s).div_const 120)
        exact (h1.sub (Real.hasDerivAt_sin s)).congr_deriv (by dsimp; ring)) hu
  exact ⟨by linarith [d3 x hx], by linarith [d6 x hx]⟩

/-- **Lemma T.3(1) (`(cel:5.1)`):** for `σ ∈ (0, 1)`,
`(3/4) σ / (1 - σ) < π / sin(π σ) - 1 / σ < 2 σ / (1 - σ)`. -/
theorem stripG_deriv_bounds {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    3 / 4 * σ / (1 - σ) < π / Real.sin (π * σ) - 1 / σ ∧
      π / Real.sin (π * σ) - 1 / σ < 2 * σ / (1 - σ) := by
  have hsin_pos : 0 < Real.sin (π * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos h0) (by nlinarith [Real.pi_pos])
  have h1s : 0 < 1 - σ := by linarith
  have hpi_lo : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hpi_hi : π < (3.1416 : ℝ) := Real.pi_lt_d4
  have hpi3_lo : (3.1415 : ℝ) ^ 3 < π ^ 3 := pow_lt_pow_left₀ hpi_lo (by norm_num) (by decide)
  have hpi3_hi : π ^ 3 < (3.1416 : ℝ) ^ 3 := pow_lt_pow_left₀ hpi_hi Real.pi_pos.le (by decide)
  have hpi5_hi : π ^ 5 < (3.1416 : ℝ) ^ 5 := pow_lt_pow_left₀ hpi_hi Real.pi_pos.le (by decide)
  have hpi3_num : (30.999 : ℝ) < π ^ 3 := lt_trans (by norm_num) hpi3_lo
  have hpi5_num : π ^ 5 < (306.09 : ℝ) := lt_trans hpi5_hi (by norm_num)
  have hmain_half : ∀ u : ℝ, 0 < u → u ≤ 1 / 2 →
      3 / 4 * u ^ 2 * Real.sin (π * u) < (1 - u) * (π * u - Real.sin (π * u)) ∧
      (1 - u) * (π * u - Real.sin (π * u)) < 2 * u ^ 2 * Real.sin (π * u) := by
    intro u hu0 hu1
    obtain ⟨hlo, hup⟩ := sin_taylor_lower_upper (mul_nonneg Real.pi_pos.le hu0.le)
    have hsin_u : 0 < Real.sin (π * u) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hu0) (by nlinarith only [Real.pi_pos, hu1])
    constructor
    · have hsub : (1 - u) * (π * u - (π * u - (π * u) ^ 3 / 6 + (π * u) ^ 5 / 120)) -
          3 / 4 * u ^ 2 * (π * u - (π * u) ^ 3 / 6 + (π * u) ^ 5 / 120) =
          u ^ 3 * (π ^ 3 / 6 * (1 - u) - 3 / 4 * π +
            u ^ 2 * (3 / 4 * π ^ 3 / 6 - (1 - u) * π ^ 5 / 120 - 3 / 4 * u ^ 2 * π ^ 5 / 120)) := by ring
      have hcoeff1 : 0.22 < π ^ 3 / 6 * (1 - u) - 3 / 4 * π := by
        have hhalf : π ^ 3 / 12 ≤ π ^ 3 / 6 * (1 - u) := by
          have : (1 / 2 : ℝ) ≤ 1 - u := by linarith
          nlinarith only [this, hpi3_num]
        linarith only [hhalf, hpi3_num, hpi_hi]
      have hcoeff2 : 0 < 3 / 4 * π ^ 3 / 6 - (1 - u) * π ^ 5 / 120 - 3 / 4 * u ^ 2 * π ^ 5 / 120 := by
        have h1 : ((1 - u) + 3 / 4 * u ^ 2) * π ^ 5 / 120 ≤ 306.09 / 120 := by
          have hle1 : (1 - u) + 3 / 4 * u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
          have hnn : 0 ≤ (1 - u) + 3 / 4 * u ^ 2 := by linarith only [hu0, hu1, sq_nonneg u]
          nlinarith only [hle1, hnn, hpi5_num]
        linarith only [h1, hpi3_num]
      have hpos : 0 < u ^ 3 * (π ^ 3 / 6 * (1 - u) - 3 / 4 * π +
          u ^ 2 * (3 / 4 * π ^ 3 / 6 - (1 - u) * π ^ 5 / 120 - 3 / 4 * u ^ 2 * π ^ 5 / 120)) := by
        positivity
      nlinarith only [hsub, hpos, hlo, hup, hu0, hu1]
    · have hsub : 2 * u ^ 2 * (π * u - (π * u) ^ 3 / 6) - (1 - u) * (π * u - (π * u - (π * u) ^ 3 / 6)) =
          u ^ 3 * π * ((2 - π ^ 2 / 6) + π ^ 2 / 6 * u * (1 - 2 * u)) := by ring
      have h2pi : 0 < 2 - π ^ 2 / 6 := by nlinarith only [hpi_hi, Real.pi_pos]
      have h12u : 0 ≤ π ^ 2 / 6 * u * (1 - 2 * u) := mul_nonneg (by positivity) (by linarith)
      have hpos : 0 < u ^ 3 * π * ((2 - π ^ 2 / 6) + π ^ 2 / 6 * u * (1 - 2 * u)) := by positivity
      nlinarith only [hsub, hpos, hlo, hup, hu0, hu1]
  rcases le_or_gt σ (1 / 2) with hhalf | hhalf
  · obtain ⟨hL, hU⟩ := hmain_half σ h0 hhalf
    constructor
    · rw [div_sub_div _ _ hsin_pos.ne' h0.ne', div_lt_div_iff₀ h1s (mul_pos hsin_pos h0)]
      linarith only [hL]
    · rw [div_sub_div _ _ hsin_pos.ne' h0.ne', div_lt_div_iff₀ (mul_pos hsin_pos h0) h1s]
      linarith only [hU]
  · set s : ℝ := 1 - σ
    have hs0 : 0 < s := by linarith
    have hs1 : s ≤ 1 / 2 := by linarith
    have hsin_eq : Real.sin (π * σ) = Real.sin (π * s) := by
      rw [show π * σ = π - π * s by dsimp [s]; ring, Real.sin_pi_sub]
    obtain ⟨hlo, hup⟩ := sin_taylor_lower_upper (mul_nonneg Real.pi_pos.le hs0.le)
    rw [hsin_eq] at hsin_pos ⊢
    have hLs : 3 / 4 * (1 - s) ^ 2 * Real.sin (π * s) < s * (π * (1 - s) - Real.sin (π * s)) := by
      have hpoly : 3 / 4 * (1 - s) ^ 2 * (π * s - (π * s) ^ 3 / 6 + (π * s) ^ 5 / 120) <
          s * (π * (1 - s) - (π * s - (π * s) ^ 3 / 6 + (π * s) ^ 5 / 120)) := by
        have h1 : s * (π * (1 - s)) - (s + 3 / 4 * (1 - s) ^ 2) * (π * s - (π * s) ^ 3 / 6 + (π * s) ^ 5 / 120) =
            π * s * ((1 / 4 - s / 2 - 3 / 4 * s ^ 2) + (3 / 4 - s / 2 + 3 / 4 * s ^ 2) * ((π * s) ^ 2 / 6 - (π * s) ^ 4 / 120)) := by ring
        have hfac : ∀ y : ℝ, y ^ 2 / 6 - y ^ 4 / 120 = y ^ 2 * (20 - y ^ 2) / 120 := fun y => by ring
        have hps_hi : π * s ≤ 1.5708 := by nlinarith only [hpi_hi, hs0, hs1]
        have hps_nn : 0 ≤ π * s := mul_nonneg Real.pi_pos.le hs0.le
        have hp_nn : 0 ≤ (π * s) ^ 2 / 6 - (π * s) ^ 4 / 120 := by
          rw [hfac]
          have : (π * s) ^ 2 ≤ 2.47 := by nlinarith only [hps_hi, hps_nn]
          nlinarith only [this, sq_nonneg (π * s)]
        have hinner : 0 < (1 / 4 - s / 2 - 3 / 4 * s ^ 2) +
            (3 / 4 - s / 2 + 3 / 4 * s ^ 2) * ((π * s) ^ 2 / 6 - (π * s) ^ 4 / 120) := by
          rcases le_or_gt s (0.3 : ℝ) with hs3 | hs3
          · have hA : 0 < 1 / 4 - s / 2 - 3 / 4 * s ^ 2 := by nlinarith only [hs0, hs3]
            have hB : 0 ≤ 3 / 4 - s / 2 + 3 / 4 * s ^ 2 := by nlinarith only [sq_nonneg s]
            nlinarith only [hA, hB, hp_nn]
          · have hB : 2 / 3 ≤ 3 / 4 - s / 2 + 3 / 4 * s ^ 2 := by nlinarith only [sq_nonneg (3 * s - 1)]
            have hx_lo : 0.942 < π * s := by nlinarith only [hpi_lo, hs3]
            have hx_sq_lo : 0.887 < (π * s) ^ 2 := by nlinarith only [hx_lo]
            have hx_sq_hi : (π * s) ^ 2 ≤ 2.47 := by nlinarith only [hps_hi, hps_nn]
            have hC : 0.129 < (π * s) ^ 2 / 6 - (π * s) ^ 4 / 120 := by
              rw [hfac]
              have h20 : 17.53 ≤ 20 - (π * s) ^ 2 := by linarith only [hx_sq_hi]
              calc (0.129 : ℝ) < 0.887 * 17.53 / 120 := by norm_num
                _ ≤ (π * s) ^ 2 * (20 - (π * s) ^ 2) / 120 := by gcongr
            rcases le_or_gt s (0.4 : ℝ) with hs4 | hs4
            · have hA : -0.07 ≤ 1 / 4 - s / 2 - 3 / 4 * s ^ 2 := by nlinarith only [hs3, hs4]
              nlinarith only [hA, hB, hC]
            · rcases le_or_gt s (0.46 : ℝ) with hs46 | hs46
              · have hx_lo2 : 1.256 < π * s := by nlinarith only [hpi_lo, hs4]
                have hx_sq_lo2 : 1.577 < (π * s) ^ 2 := by nlinarith only [hx_lo2]
                have hC2 : 0.23 < (π * s) ^ 2 / 6 - (π * s) ^ 4 / 120 := by
                  rw [hfac]
                  have h20 : 17.53 ≤ 20 - (π * s) ^ 2 := by linarith only [hx_sq_hi]
                  calc (0.23 : ℝ) < 1.577 * 17.53 / 120 := by norm_num
                    _ ≤ (π * s) ^ 2 * (20 - (π * s) ^ 2) / 120 := by gcongr
                have hA : -0.1387 ≤ 1 / 4 - s / 2 - 3 / 4 * s ^ 2 := by nlinarith only [hs4, hs46]
                nlinarith only [hA, hB, hC2]
              · have hx_lo3 : 1.445 < π * s := by nlinarith only [hpi_lo, hs46]
                have hx_sq_lo3 : 2.088 < (π * s) ^ 2 := by nlinarith only [hx_lo3]
                have hC3 : 0.305 < (π * s) ^ 2 / 6 - (π * s) ^ 4 / 120 := by
                  rw [hfac]
                  have h20 : 17.53 ≤ 20 - (π * s) ^ 2 := by linarith only [hx_sq_hi]
                  calc (0.305 : ℝ) < 2.088 * 17.53 / 120 := by norm_num
                    _ ≤ (π * s) ^ 2 * (20 - (π * s) ^ 2) / 120 := by gcongr
                have hA : -3 / 16 ≤ 1 / 4 - s / 2 - 3 / 4 * s ^ 2 := by nlinarith only [hs1, hs46]
                nlinarith only [hA, hB, hC3]
        have hpos : 0 < π * s * ((1 / 4 - s / 2 - 3 / 4 * s ^ 2) +
            (3 / 4 - s / 2 + 3 / 4 * s ^ 2) * ((π * s) ^ 2 / 6 - (π * s) ^ 4 / 120)) :=
          mul_pos (mul_pos Real.pi_pos hs0) hinner
        linarith only [h1, hpos]
      have hdiff_s : (s + 3 / 4 * (1 - s) ^ 2) * Real.sin (π * s) ≤
          (s + 3 / 4 * (1 - s) ^ 2) * (π * s - (π * s) ^ 3 / 6 + (π * s) ^ 5 / 120) :=
        mul_le_mul_of_nonneg_left hup (by positivity)
      linarith only [hpoly, hdiff_s]
    have hUs : s * (π * (1 - s) - Real.sin (π * s)) < 2 * (1 - s) ^ 2 * Real.sin (π * s) := by
      have h1 : 2 * (1 - s) ^ 2 * (π * s - (π * s) ^ 3 / 6) - s * (π * (1 - s) - (π * s - (π * s) ^ 3 / 6)) =
          π * s * (2 * (1 - s) ^ 2 - (1 - 2 * s) - (2 * (1 - s) ^ 2 + s) * ((π * s) ^ 2 / 6)) := by ring
      have hps_nn : 0 ≤ π * s := mul_nonneg Real.pi_pos.le hs0.le
      have hpos : 0 < 2 * (1 - s) ^ 2 - (1 - 2 * s) - (2 * (1 - s) ^ 2 + s) * ((π * s) ^ 2 / 6) := by
        rcases le_or_gt s (1 / 3) with hs13 | hs13
        · have hps : π * s ≤ 1.05 := by nlinarith only [hpi_hi, hs0, hs13]
          have h1' : (π * s) ^ 2 / 6 ≤ 0.19 := by nlinarith only [hps, hps_nn]
          have h2 : 2 * (1 - s) ^ 2 + s ≤ 2 := by nlinarith only [hs0, hs13]
          have h3 : 5 / 9 ≤ 2 * (1 - s) ^ 2 - (1 - 2 * s) := by nlinarith only [hs13]
          nlinarith only [h1', h2, h3, hps_nn]
        · rcases le_or_gt s (0.42 : ℝ) with hs42 | hs42
          · have hps : π * s ≤ 1.32 := by nlinarith only [hpi_hi, hs0, hs42]
            have h1' : (π * s) ^ 2 / 6 ≤ 0.291 := by nlinarith only [hps, hps_nn]
            have h2 : 2 * (1 - s) ^ 2 + s ≤ 11 / 9 := by nlinarith only [hs13, hs42]
            have h3 : 1 / 2 ≤ 2 * (1 - s) ^ 2 - (1 - 2 * s) := by nlinarith only [sq_nonneg (2 * s - 1)]
            nlinarith only [h1', h2, h3, hps_nn]
          · have hps : π * s ≤ 1.5708 := by nlinarith only [hpi_hi, hs0, hs1]
            have h1' : (π * s) ^ 2 / 6 ≤ 0.412 := by nlinarith only [hps, hps_nn]
            have h2 : 2 * (1 - s) ^ 2 + s ≤ 1.1 := by nlinarith only [hs42, hs1]
            have h3 : 1 / 2 ≤ 2 * (1 - s) ^ 2 - (1 - 2 * s) := by nlinarith only [sq_nonneg (2 * s - 1)]
            nlinarith only [h1', h2, h3, hps_nn]
      have hmul : 0 < π * s * (2 * (1 - s) ^ 2 - (1 - 2 * s) - (2 * (1 - s) ^ 2 + s) * ((π * s) ^ 2 / 6)) :=
        mul_pos (mul_pos Real.pi_pos hs0) hpos
      have hdiff_s : (2 * (1 - s) ^ 2 + s) * (π * s - (π * s) ^ 3 / 6) ≤
          (2 * (1 - s) ^ 2 + s) * Real.sin (π * s) :=
        mul_le_mul_of_nonneg_left hlo (by positivity)
      linarith only [h1, hmul, hdiff_s]
    have hσ_eq : σ = 1 - s := by dsimp [s]; ring
    rw [hσ_eq]
    constructor
    · rw [div_sub_div _ _ hsin_pos.ne' (by linarith only [hs1] : 1 - s ≠ 0),
        div_lt_div_iff₀ hs0 (mul_pos hsin_pos (by linarith only [hs1]))]
      linarith only [hLs]
    · rw [div_sub_div _ _ hsin_pos.ne' (by linarith only [hs1] : 1 - s ≠ 0),
        div_lt_div_iff₀ (mul_pos hsin_pos (by linarith only [hs1])) hs0]
      linarith only [hUs]

/-- **Lemma T.3(3) (`cel:5.5`, global vertical-line phase lower bound):**
for `σ ∈ (0, 1)` and `t > 0`, with `A = sinh(π t) / sin(π σ)` and `B = t / σ`,
`arctan A - arctan B ≥ 1/7 * min((π / sin(π σ) - 1 / σ) * t, min 1 (σ / t))`
(and piecewise `(1/5) min(g'(σ) t, 1)` for `t < 1/2`, `(3/20) min(1, σ/t)` for `t ≥ 1/2`). -/
theorem im_stripG_ge {σ t : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ht : 0 < t) :
    let g' := π / Real.sin (π * σ) - 1 / σ
    let A := Real.sinh (π * t) / Real.sin (π * σ)
    let B := t / σ
    B < A ∧
      (t < 1 / 2 → 1 / 5 * min (g' * t) 1 ≤ Real.arctan A - Real.arctan B) ∧
      (1 / 2 ≤ t → 3 / 20 * min 1 (σ / t) ≤ Real.arctan A - Real.arctan B) ∧
      1 / 7 * min (g' * t) (min 1 (σ / t)) ≤ Real.arctan A - Real.arctan B := by
  dsimp only
  set g' : ℝ := π / Real.sin (π * σ) - 1 / σ
  set A : ℝ := Real.sinh (π * t) / Real.sin (π * σ)
  set B : ℝ := t / σ
  have hsin_pos : 0 < Real.sin (π * σ) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hσ0) (by nlinarith [Real.pi_pos])
  have hsh_gt : π * t < Real.sinh (π * t) := sinh_gt_id (mul_pos Real.pi_pos ht)
  have hsh_pos : 0 < Real.sinh (π * t) := by linarith [mul_pos Real.pi_pos ht]
  have hsin_le : Real.sin (π * σ) < π * σ := Real.sin_lt (mul_pos Real.pi_pos hσ0)
  have hAB : B < A := by
    dsimp [A, B]
    rw [div_lt_div_iff₀ hσ0 hsin_pos]
    calc t * Real.sin (π * σ) < t * (π * σ) := mul_lt_mul_of_pos_left hsin_le ht
      _ = (π * t) * σ := by ring
      _ < Real.sinh (π * t) * σ := mul_lt_mul_of_pos_right hsh_gt hσ0
  have hB_pos : 0 < B := div_pos ht hσ0
  -- Helper: for `0 < b < a`, `arctan a - arctan b ≥ (a - b) / (1 + a²)` (from `arctan` deriv `(1 + x²)⁻¹` on `[b, a]`!)
  have harctan_diff : ∀ {b a : ℝ}, 0 < b → b < a → (a - b) / (1 + a ^ 2) ≤ Real.arctan a - Real.arctan b := by
    intro b a hb hba
    -- Let `H(x) = arctan x - (x - b) / (1 + a²)` on `[b, a]`: deriv is `(1+x²)⁻¹ - (1+a²)⁻¹ ≥ 0`!
    let H : ℝ → ℝ := fun x => Real.arctan x - (x - b) / (1 + a ^ 2)
    have hH_mono : MonotoneOn H (Icc b a) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc b a) ?_ ?_ ?_
      · exact (Real.continuous_arctan.sub (by fun_prop)).continuousOn
      · intro x _; exact ((Real.hasDerivAt_arctan x).sub (((hasDerivAt_id x).sub (hasDerivAt_const x b)).div_const _)).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hhd : HasDerivAt H ((1 + x ^ 2)⁻¹ - 1 / (1 + a ^ 2)) x :=
          ((Real.hasDerivAt_arctan x).sub (((hasDerivAt_id x).sub (hasDerivAt_const x b)).div_const (1 + a ^ 2))).congr_deriv
            (by ring)
        rw [hhd.deriv, sub_nonneg, one_div]
        exact inv_anti₀ (by positivity) (by nlinarith [hx.1, hx.2, hb])
    have := hH_mono ⟨le_rfl, hba.le⟩ ⟨hba.le, le_rfl⟩ hba.le
    simp only [H, sub_self, zero_div, sub_zero] at this
    linarith
  -- Helper: `arctan_inv`: `arctan a - arctan b = arctan (1 / b) - arctan (1 / a)` for `0 < b < a`:
  have harctan_inv : ∀ {b a : ℝ}, 0 < b → b < a →
      Real.arctan a - Real.arctan b = Real.arctan (1 / b) - Real.arctan (1 / a) := by
    intro b a hb hba
    have h1 := Real.arctan_inv_of_pos (by linarith : 0 < a)
    have h2 := Real.arctan_inv_of_pos hb
    rw [one_div, one_div]
    linarith
  have hpi_lo : (3.1415 : ℝ) < π := Real.pi_gt_d4
  have hpi_hi : π < (3.1416 : ℝ) := Real.pi_lt_d4
  have hg'_pos : 0 < g' := (div_pos (mul_pos (by norm_num) hσ0) (by linarith)).trans (stripG_deriv_bounds hσ0 hσ1).1
  have hge_big : 1 / 2 ≤ t → 3 / 20 * min 1 (σ / t) ≤ Real.arctan A - Real.arctan B := by
    intro ht12
    have hsh_half : (2.29 : ℝ) ≤ Real.sinh (π * t) := by
      have hst : Real.sinh (π / 2) ≤ Real.sinh (π * t) :=
        Real.sinh_le_sinh.mpr (by nlinarith [Real.pi_pos])
      have htl := sinh_taylor_lower (by positivity : 0 ≤ π / 2)
      have hx_lo : (1.5707 : ℝ) < π / 2 := by nlinarith
      have hx3 : (1.5707 : ℝ) ^ 3 < (π / 2) ^ 3 := pow_lt_pow_left₀ hx_lo (by norm_num) (by decide)
      have hx5 : (1.5707 : ℝ) ^ 5 < (π / 2) ^ 5 := pow_lt_pow_left₀ hx_lo (by norm_num) (by decide)
      linarith
    have hA_lo : (2.29 : ℝ) ≤ A := by
      dsimp [A]
      calc (2.29 : ℝ) ≤ Real.sinh (π * t) := hsh_half
        _ = Real.sinh (π * t) / 1 := by ring
        _ ≤ Real.sinh (π * t) / Real.sin (π * σ) :=
            div_le_div_of_nonneg_left hsh_pos.le hsin_pos (Real.sin_le_one _)
    rcases le_or_gt B 1 with hB1 | hB1
    · have harctan_inv_le : ∀ {u : ℝ}, 0 ≤ u → Real.arctan u ≤ u := by
        intro u hu
        have h := nonneg_of_zero_of_deriv_nonneg (g := fun s => s - Real.arctan s)
          (fun s => 1 - 1 / (1 + s ^ 2)) (by simp)
          (fun s _ => by rw [sub_nonneg, one_div]; exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg s]))
          (fun s => (hasDerivAt_id s).sub (Real.hasDerivAt_arctan s)) hu
        linarith
      have hA_val : π / 2 - 1 / 2.29 ≤ Real.arctan A := by
        have h1 := Real.arctan_inv_of_pos (by linarith : 0 < A)
        have h2 : Real.arctan A⁻¹ ≤ A⁻¹ := harctan_inv_le (by positivity)
        have h3 : 1 / A ≤ 1 / 2.29 := one_div_le_one_div_of_le (by norm_num) hA_lo
        rw [← one_div] at h1 h2
        linarith
      have hB_val : Real.arctan B ≤ π / 4 := by
        have := Real.arctan_mono hB1
        rwa [Real.arctan_one] at this
      have hmin : min 1 (σ / t) ≤ 1 := min_le_left _ _
      nlinarith
    · -- `B > 1` (`σ / t < 1`): `sinh(π t) / t ≥ 2 * sinh(π / 2)` for `t ≥ 1 / 2`!
      have hsh_t : 4.58 * t ≤ Real.sinh (π * t) := by
        let K : ℝ → ℝ := fun u => Real.sinh (π * u) - 4.58 * u
        have hK_mono : MonotoneOn K (Ici (1 / 2)) := by
          refine monotoneOn_of_deriv_nonneg (convex_Ici (1 / 2)) (by fun_prop)
            (fun u _ => ((Real.hasDerivAt_sinh (π * u)).comp u ((hasDerivAt_id u).const_mul π) |>.sub
              ((hasDerivAt_id u).const_mul 4.58)).differentiableAt.differentiableWithinAt) ?_
          intro u hu
          rw [interior_Ici, mem_Ioi] at hu
          have hd : HasDerivAt K (π * Real.cosh (π * u) - 4.58) u :=
            (((Real.hasDerivAt_sinh (π * u)).comp u ((hasDerivAt_id u).const_mul π)).sub
              ((hasDerivAt_id u).const_mul 4.58)).congr_deriv (by ring)
          rw [hd.deriv]
          have hch : 2 ≤ Real.cosh (π * u) := by
            have hst : 1.57 ≤ π * u := by nlinarith [Real.pi_gt_d4, hu]
            have hquad : ∀ z : ℝ, 0 ≤ z → 1 + z ^ 2 / 2 ≤ Real.cosh z := fun z hz => by
              have d1 : ∀ s ≥ 0, 0 ≤ Real.sinh s - s := fun s hs =>
                nonneg_of_zero_of_deriv_nonneg (g := fun t => Real.sinh t - t)
                  (fun t => Real.cosh t - 1) (by simp)
                  (fun t _ => by linarith [Real.one_le_cosh t])
                  (fun t => (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)) hs
              have d2 := nonneg_of_zero_of_deriv_nonneg (g := fun t => Real.cosh t - (1 + t ^ 2 / 2))
                (fun t => Real.sinh t - t) (by simp)
                d1 (fun t => ((Real.hasDerivAt_cosh t).sub
                  ((hasDerivAt_const t 1).add ((hasDerivAt_pow 2 t).div_const 2))).congr_deriv (by dsimp; ring))
                hz
              linarith
            nlinarith [hquad (π * u) (by positivity), hst]
          nlinarith
        have := hK_mono le_rfl ht12 ht12
        have hK_half : 0 ≤ K (1 / 2) := by
          dsimp [K]
          have hst := sinh_taylor_lower (by positivity : 0 ≤ π / 2)
          have h1 : Real.sinh (π * (1 / 2)) = Real.sinh (π / 2) := by ring_nf
          have hx_lo : (1.5707 : ℝ) < π / 2 := by nlinarith
          have hx3 : (1.5707 : ℝ) ^ 3 < (π / 2) ^ 3 := pow_lt_pow_left₀ hx_lo (by norm_num) (by decide)
          have hx5 : (1.5707 : ℝ) ^ 5 < (π / 2) ^ 5 := pow_lt_pow_left₀ hx_lo (by norm_num) (by decide)
          rw [h1]
          linarith
        dsimp [K] at this hK_half
        linarith
      have hAinv : 1 / A ≤ (π / 4.58) * (1 / B) := by
        dsimp [A, B]
        rw [one_div_div, one_div_div]
        rw [div_le_iff₀ hsh_pos]
        calc Real.sin (π * σ) ≤ π * σ := (Real.sin_lt (mul_pos Real.pi_pos hσ0)).le
          _ = π * (σ / t) * t := by have := ht.ne'; field_simp
          _ = (π / 4.58) * (σ / t) * (4.58 * t) := by ring
          _ ≤ (π / 4.58) * (σ / t) * Real.sinh (π * t) :=
              mul_le_mul_of_nonneg_left hsh_t (by positivity)
      rw [harctan_inv hB_pos hAB]
      have hdiff := harctan_diff (by positivity : 0 < 1 / A) (one_div_lt_one_div_of_lt hB_pos hAB)
      have hden : 1 + (1 / B) ^ 2 ≤ 2 := by
        have h1B_lt : 1 / B < 1 := (div_lt_one hB_pos).mpr hB1
        have h1B_pos : 0 < 1 / B := by positivity
        have h1B_sq : (1 / B) ^ 2 ≤ 1 := by
          rw [sq_le_one_iff_abs_le_one, abs_of_pos h1B_pos]
          exact h1B_lt.le
        linarith only [h1B_sq]
      have hnum : (1 - π / 4.58) * (1 / B) ≤ 1 / B - 1 / A := by linarith only [hAinv]
      have hc : (3 / 20 : ℝ) ≤ (1 - π / 4.58) / 2 := by
        have h : π < 3.1416 := hpi_hi
        norm_num at h ⊢
        linarith only [h]
      have hB_eq : 1 / B = σ / t := by dsimp [B]; rw [one_div_div]
      have hmin : min 1 (σ / t) ≤ σ / t := min_le_right _ _
      have hBA_nn : 0 ≤ 1 / B - 1 / A := sub_nonneg.mpr (one_div_le_one_div_of_le hB_pos hAB.le)
      calc 3 / 20 * min 1 (σ / t) ≤ 3 / 20 * (σ / t) := by gcongr
        _ ≤ ((1 - π / 4.58) / 2) * (1 / B) := by rw [← hB_eq]; gcongr
        _ = ((1 - π / 4.58) * (1 / B)) / 2 := by ring
        _ ≤ (1 / B - 1 / A) / (1 + (1 / B) ^ 2) :=
            div_le_div₀ hBA_nn hnum (by positivity) hden
        _ ≤ Real.arctan (1 / B) - Real.arctan (1 / A) := hdiff
  have hlt_half : t < 1 / 2 → 1 / 5 * min (g' * t) 1 ≤ Real.arctan A - Real.arctan B := by
    intro ht12
    -- Note `A - B = g' * t + (sinh(π t) - π t) / sin(π σ) > g' * t`!
    have hAB_diff : g' * t < A - B := by
      dsimp [g', A, B]
      have hid : (π / Real.sin (π * σ) - 1 / σ) * t = π * t / Real.sin (π * σ) - t / σ := by ring
      rw [hid]
      have h1 : π * t / Real.sin (π * σ) < Real.sinh (π * t) / Real.sin (π * σ) :=
        div_lt_div_of_pos_right hsh_gt hsin_pos
      linarith
    rcases le_or_gt A 2 with hA2 | hA2
    · have hdiff := harctan_diff hB_pos hAB
      have hden : 1 + A ^ 2 ≤ 5 := by nlinarith [hAB.trans_le hA2]
      calc 1 / 5 * min (g' * t) 1 ≤ 1 / 5 * (g' * t) := by gcongr; exact min_le_left _ _
        _ ≤ (A - B) / 5 := by linarith
        _ ≤ (A - B) / (1 + A ^ 2) := div_le_div_of_nonneg_left (by linarith) (by positivity) hden
        _ ≤ Real.arctan A - Real.arctan B := hdiff
    · rcases le_or_gt B 1 with hB1 | hB1
      · have h1 : Real.arctan 2 ≤ Real.arctan A := Real.arctan_mono hA2.le
        have h2 : Real.arctan B ≤ Real.arctan 1 := Real.arctan_mono hB1
        have h3 := harctan_diff one_pos (by norm_num : (1 : ℝ) < 2)
        have hmin : min (g' * t) 1 ≤ 1 := min_le_right _ _
        nlinarith
      · -- `A > 2` and `B > 1` (`0 < σ < t < 1 / 2`):
        -- `g' < 2 * σ / (1 - σ²) < 8/3 * σ` via 7th-order Taylor lower bound on `sin`,
        -- and `sinh(π t) ≤ 4.76 * t` for `0 < t < 1/2`, giving `1/B - 1/A ≥ 1.08 * σ * t`.
        have hσt : σ < t := by dsimp [B] at hB1; rw [one_lt_div hσ0] at hB1; exact hB1
        have hσ12 : σ < 1 / 2 := hσt.trans ht12
        have hg'_ub : g' < 8 / 3 * σ := by
          have hsin7 : ∀ x : ℝ, 0 ≤ x →
              x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 ≤ Real.sin x := fun x hx => by
            have d6 : ∀ u ≥ 0, 0 ≤ (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u := fun u hu => by
              linarith [(sin_taylor_lower_upper hu).2]
            have d7 : ∀ u ≥ 0, 0 ≤ Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720) := fun u hu =>
              nonneg_of_zero_of_deriv_nonneg
                (g := fun s => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720))
                (fun s => (s - s ^ 3 / 6 + s ^ 5 / 120) - Real.sin s)
                (by simp) d6 (fun s => by
                  have h1 := (((hasDerivAt_const s 1).sub ((hasDerivAt_pow 2 s).div_const 2)).add
                    ((hasDerivAt_pow 4 s).div_const 24)).sub ((hasDerivAt_pow 6 s).div_const 720)
                  exact ((Real.hasDerivAt_cos s).sub h1).congr_deriv
                    (by simp only [Nat.reduceSub, pow_one]; ring)) hu
            have d8 := nonneg_of_zero_of_deriv_nonneg
              (g := fun s => Real.sin s - (s - s ^ 3 / 6 + s ^ 5 / 120 - s ^ 7 / 5040))
              (fun s => Real.cos s - (1 - s ^ 2 / 2 + s ^ 4 / 24 - s ^ 6 / 720)) (by simp) d7
              (fun s => by
                have h1 := (((hasDerivAt_id s).sub ((hasDerivAt_pow 3 s).div_const 6)).add
                  ((hasDerivAt_pow 5 s).div_const 120)).sub ((hasDerivAt_pow 7 s).div_const 5040)
                exact ((Real.hasDerivAt_sin s).sub h1).congr_deriv
                  (by simp only [Nat.reduceSub]; ring)) hx
            linarith
          have hmid : g' < 2 * σ / (1 - σ ^ 2) := by
            have h1s2 : 0 < 1 - σ ^ 2 := by nlinarith only [hσ0, hσ12]
            dsimp [g']
            rw [div_sub_div _ _ hsin_pos.ne' hσ0.ne', div_lt_div_iff₀ (mul_pos hsin_pos hσ0) h1s2]
            set y : ℝ := π * σ
            have hy0 : 0 < y := mul_pos Real.pi_pos hσ0
            have hy_hi : y < 1.571 := by nlinarith only [Real.pi_lt_d4, hσ0, hσ12]
            have hsin_lb := hsin7 y hy0.le
            have hpi_lo : (3.1415 : ℝ) < π := Real.pi_gt_d4
            have hpi_hi : π < (3.1416 : ℝ) := Real.pi_lt_d4
            have hpi2_lo : (9.869 : ℝ) ≤ π ^ 2 := by nlinarith only [hpi_lo]
            have hpi2_hi : π ^ 2 ≤ (9.87 : ℝ) := by nlinarith only [hpi_hi, Real.pi_pos]
            have hy2_hi : y ^ 2 ≤ (2.47 : ℝ) := by nlinarith only [hy0, hy_hi]
            have hy6_hi : y ^ 6 ≤ (15.1 : ℝ) := by
              calc y ^ 6 = (y ^ 2) ^ 3 := by ring
                _ ≤ (2.47 : ℝ) ^ 3 := pow_le_pow_left₀ (sq_nonneg y) hy2_hi 3
                _ ≤ 15.1 := by norm_num
            have hpoly_pos : 0 < 5040 * (2 - π ^ 2 / 6) + (42 * π ^ 2 - 840) * y ^ 2 +
                (42 - π ^ 2) * y ^ 4 - y ^ 6 := by
              have hp1 : 1789.2 ≤ 5040 * (2 - π ^ 2 / 6) := by linarith only [hpi2_hi]
              have hp2 : -1052 ≤ (42 * π ^ 2 - 840) * y ^ 2 := by
                have hc : -425.55 ≤ 42 * π ^ 2 - 840 := by linarith only [hpi2_lo]
                have h2a : (-425.55) * y ^ 2 ≤ (42 * π ^ 2 - 840) * y ^ 2 :=
                  mul_le_mul_of_nonneg_right hc (sq_nonneg y)
                have h2b : (-425.55) * (2.47 : ℝ) ≤ (-425.55) * y ^ 2 := by linarith only [hy2_hi]
                linarith only [h2a, h2b]
              have hp3 : 0 ≤ (42 - π ^ 2) * y ^ 4 :=
                mul_nonneg (by linarith only [hpi2_hi]) (pow_nonneg hy0.le 4)
              linarith only [hp1, hp2, hp3, hy6_hi]
            have hcore : 0 < (1 + σ ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) -
                y * (1 - σ ^ 2) := by
              have hfac : 5040 * π ^ 2 * ((1 + σ ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) -
                  y * (1 - σ ^ 2)) =
                  y ^ 3 * (5040 * (2 - π ^ 2 / 6) + (42 * π ^ 2 - 840) * y ^ 2 +
                    (42 - π ^ 2) * y ^ 4 - y ^ 6) := by
                dsimp [y]; ring
              have hprod : 0 < 5040 * π ^ 2 * ((1 + σ ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) -
                  y * (1 - σ ^ 2)) := by
                rw [hfac]; exact mul_pos (pow_pos hy0 3) hpoly_pos
              exact pos_of_mul_pos_right hprod (by positivity)
            have hsin_mono : 0 < (1 + σ ^ 2) * Real.sin y - y * (1 - σ ^ 2) := by
              have hle : (1 + σ ^ 2) * (y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040) ≤
                  (1 + σ ^ 2) * Real.sin y :=
                mul_le_mul_of_nonneg_left hsin_lb (by positivity)
              linarith only [hcore, hle]
            have hid : (1 + σ ^ 2) * Real.sin y - y * (1 - σ ^ 2) =
                2 * σ ^ 2 * Real.sin (π * σ) - (1 - σ ^ 2) * (π * σ - Real.sin (π * σ)) := by
              dsimp [y]; ring
            linarith only [hsin_mono, hid]
          have hden_lo : 3 / 4 < 1 - σ ^ 2 := by nlinarith only [hσ0, hσ12]
          have hnum2s_pos : 0 < 2 * σ := by positivity
          calc g' < 2 * σ / (1 - σ ^ 2) := hmid
            _ < 2 * σ / (3 / 4) := div_lt_div_of_pos_left hnum2s_pos (by norm_num) hden_lo
            _ = 8 / 3 * σ := by ring
        have hsh_ub : Real.sinh (π * t) ≤ 4.76 * t := by
          have hexp_half : Real.exp (π / 2) ≤ 4.96 := by
            let δ : ℝ := (π / 2 - 1) / 6
            have hδ0 : 0 ≤ δ := by dsimp [δ]; linarith only [Real.pi_gt_d4]
            have hδhi : δ ≤ 0.0952 := by dsimp [δ]; linarith only [Real.pi_lt_d4]
            have h1δ : 0.9048 ≤ 1 - δ := by linarith only [hδhi]
            have hexp_neg : 0.9048 ≤ Real.exp (-δ) := h1δ.trans (by linarith [add_one_le_exp (-δ)])
            have hexp_δ : Real.exp δ ≤ 0.9048⁻¹ := by
              rw [Real.exp_neg, ← one_div, le_div_iff₀ (Real.exp_pos δ)] at hexp_neg
              rw [← one_div, le_div_iff₀ (by norm_num)]
              linarith only [hexp_neg]
            have h6 : Real.exp (π / 2 - 1) = Real.exp δ ^ 6 := by
              rw [← Real.exp_nat_mul]; congr 1; dsimp [δ]; ring
            have h6le : Real.exp (π / 2 - 1) ≤ (0.9048⁻¹ : ℝ) ^ 6 := by
              rw [h6]; exact pow_le_pow_left₀ (Real.exp_pos δ).le hexp_δ 6
            have hadd : Real.exp (π / 2) = Real.exp 1 * Real.exp (π / 2 - 1) := by
              rw [← Real.exp_add]; ring_nf
            have he1 : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
            have hprod : Real.exp 1 * Real.exp (π / 2 - 1) ≤ 2.7183 * (0.9048⁻¹ : ℝ) ^ 6 := by
              gcongr
            have hnum : (2.7183 : ℝ) * (0.9048⁻¹ : ℝ) ^ 6 ≤ 4.96 := by norm_num
            linarith only [hadd, hprod, hnum]
          have hexp_neg : (4.96 : ℝ)⁻¹ ≤ Real.exp (-(π / 2)) := by
            rw [Real.exp_neg]
            exact (inv_le_inv₀ (by norm_num) (Real.exp_pos _)).mpr hexp_half
          have hsh_half : Real.sinh (π / 2) ≤ 2.38 := by
            rw [Real.sinh_eq]
            linarith only [hexp_half, hexp_neg]
          have hmono_u : MonotoneOn (fun u : ℝ => Real.sinh u / u) (Ioi 0) := by
            refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
            · intro u hu
              exact (Real.continuous_sinh.continuousAt.div continuousAt_id (ne_of_gt hu)).continuousWithinAt
            · intro u hu
              rw [interior_Ioi, mem_Ioi] at hu
              exact ((Real.hasDerivAt_sinh u).div (hasDerivAt_id u) hu.ne').differentiableAt.differentiableWithinAt
            · intro u hu
              rw [interior_Ioi, mem_Ioi] at hu
              have hd := (Real.hasDerivAt_sinh u).div (hasDerivAt_id u) hu.ne'
              change HasDerivAt (fun x => Real.sinh x / x) _ u at hd
              rw [hd.deriv]
              have ht := tanh_lt_id hu
              rw [Real.tanh_eq_sinh_div_cosh, div_lt_iff₀ (Real.cosh_pos u)] at ht
              have hnum : 0 ≤ Real.cosh u * u - Real.sinh u * 1 := by linarith only [ht]
              exact div_nonneg hnum (sq_nonneg u)
          have hle := hmono_u (mem_Ioi.mpr (mul_pos Real.pi_pos ht))
            (mem_Ioi.mpr (by positivity : (0 : ℝ) < π / 2))
            ((mul_le_mul_of_nonneg_left ht12.le Real.pi_pos.le).trans_eq (by ring))
          rw [div_le_div_iff₀ (mul_pos Real.pi_pos ht) (by positivity)] at hle
          have hle' : Real.sinh (π * t) ≤ (2 * t) * Real.sinh (π / 2) := by
            have hmul : Real.sinh (π * t) * π ≤ (2 * t * Real.sinh (π / 2)) * π := by
              linarith only [hle]
            exact le_of_mul_le_mul_right hmul Real.pi_pos
          calc Real.sinh (π * t) ≤ 2 * t * Real.sinh (π / 2) := hle'
            _ ≤ 2 * t * 2.38 := by gcongr
            _ = 4.76 * t := by ring
        have hgap : (1.08 : ℝ) * (σ * t) ≤ 1 / B - 1 / A := by
          have hsh_t3 : (π * t) ^ 3 / 6 ≤ Real.sinh (π * t) - π * t := by
            have hst := sinh_taylor_lower (mul_pos Real.pi_pos ht).le
            have h5 : 0 ≤ (π * t) ^ 5 / 120 := by positivity
            linarith only [hst, h5]
          have hnum : (π ^ 3 / 6) * (σ * t ^ 3) ≤ σ * Real.sinh (π * t) - t * Real.sin (π * σ) := by
            have hsin_le : Real.sin (π * σ) ≤ π * σ := (Real.sin_lt (mul_pos Real.pi_pos hσ0)).le
            have h1 : σ * ((π * t) ^ 3 / 6) ≤ σ * (Real.sinh (π * t) - π * t) :=
              mul_le_mul_of_nonneg_left hsh_t3 hσ0.le
            have h2 : t * Real.sin (π * σ) ≤ t * (π * σ) :=
              mul_le_mul_of_nonneg_left hsin_le ht.le
            linarith [show σ * ((π * t) ^ 3 / 6) = (π ^ 3 / 6) * (σ * t ^ 3) by ring]
          have hden_ub : t * Real.sinh (π * t) ≤ 4.76 * t ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_left hsh_ub ht.le]
          have hBA : 1 / B - 1 / A = (σ * Real.sinh (π * t) - t * Real.sin (π * σ)) / (t * Real.sinh (π * t)) := by
            dsimp [A, B]
            have h1 := ht.ne'
            have h2 := hsh_pos.ne'
            have h3 := hsin_pos.ne'
            have h4 := hσ0.ne'
            field_simp
          rw [hBA]
          have hnum_nn : 0 ≤ (π ^ 3 / 6) * (σ * t ^ 3) :=
            mul_nonneg (div_nonneg (pow_nonneg Real.pi_pos.le 3) (by norm_num))
              (mul_nonneg hσ0.le (pow_nonneg ht.le 3))
          have hdiv1 : (π ^ 3 / 6) * (σ * t ^ 3) / (4.76 * t ^ 2) ≤
              (σ * Real.sinh (π * t) - t * Real.sin (π * σ)) / (t * Real.sinh (π * t)) :=
            div_le_div₀ (hnum_nn.trans hnum) hnum (mul_pos ht hsh_pos) hden_ub
          have hdiv2 : (π ^ 3 / 6) * (σ * t ^ 3) / (4.76 * t ^ 2) =
              (π ^ 3 / (6 * 4.76)) * (σ * t) := by
            have := ht.ne'; field_simp
          have hpi3 : (1.08 : ℝ) ≤ π ^ 3 / (6 * 4.76) := by
            have hpi2_lo : (9.869 : ℝ) ≤ π ^ 2 := by
              have := Real.pi_gt_d4
              nlinarith only [this, Real.pi_pos]
            have hpi3_lo : (31 : ℝ) ≤ π ^ 3 := by
              have := Real.pi_gt_d4
              nlinarith only [this, hpi2_lo]
            norm_num
            linarith only [hpi3_lo]
          calc (1.08 : ℝ) * (σ * t) ≤ (π ^ 3 / (6 * 4.76)) * (σ * t) :=
                mul_le_mul_of_nonneg_right hpi3 (mul_nonneg hσ0.le ht.le)
            _ = (π ^ 3 / 6) * (σ * t ^ 3) / (4.76 * t ^ 2) := hdiv2.symm
            _ ≤ _ := hdiv1
        rw [harctan_inv hB_pos hAB]
        have hdiff := harctan_diff (by positivity : 0 < 1 / A) (one_div_lt_one_div_of_lt hB_pos hAB)
        have hden : 1 + (1 / B) ^ 2 ≤ 2 := by
          have h1B : 1 / B < 1 := (div_lt_one hB_pos).mpr (by linarith)
          have hsq : (1 / B) ^ 2 ≤ 1 := by
            rw [sq_le_one_iff_abs_le_one, abs_of_pos (by positivity)]
            exact h1B.le
          linarith only [hsq]
        have hmin : min (g' * t) 1 ≤ g' * t := min_le_left _ _
        calc 1 / 5 * min (g' * t) 1 ≤ 1 / 5 * (g' * t) := by gcongr
          _ ≤ 1 / 5 * ((8 / 3 * σ) * t) := by gcongr
          _ = 8 / 15 * (σ * t) := by ring
          _ ≤ 1.08 * (σ * t) / 2 := by linarith only [mul_nonneg hσ0.le ht.le]
          _ ≤ (1 / B - 1 / A) / (1 + (1 / B) ^ 2) :=
              div_le_div₀ (by linarith only [hgap, mul_nonneg hσ0.le ht.le]) hgap (by positivity) hden
          _ ≤ Real.arctan (1 / B) - Real.arctan (1 / A) := hdiff
  refine ⟨hAB, hlt_half, hge_big, ?_⟩
  rcases lt_or_ge t (1 / 2) with ht12 | ht12
  · have h := hlt_half ht12
    have hm : min (g' * t) (min 1 (σ / t)) ≤ min (g' * t) 1 :=
      min_le_min le_rfl (min_le_left _ _)
    have hm_nn : 0 ≤ min (g' * t) (min 1 (σ / t)) :=
      le_min (mul_nonneg hg'_pos.le ht.le) (le_min zero_le_one (div_nonneg hσ0.le ht.le))
    calc 1 / 7 * min (g' * t) (min 1 (σ / t)) ≤ 1 / 5 * min (g' * t) (min 1 (σ / t)) := by linarith
      _ ≤ 1 / 5 * min (g' * t) 1 := by gcongr
      _ ≤ Real.arctan A - Real.arctan B := h
  · have h := hge_big ht12
    have hm : min (g' * t) (min 1 (σ / t)) ≤ min 1 (σ / t) := min_le_right _ _
    have hm_nn : 0 ≤ min (g' * t) (min 1 (σ / t)) :=
      le_min (mul_nonneg hg'_pos.le ht.le) (le_min zero_le_one (div_nonneg hσ0.le ht.le))
    calc 1 / 7 * min (g' * t) (min 1 (σ / t)) ≤ 3 / 20 * min (g' * t) (min 1 (σ / t)) := by linarith
      _ ≤ 3 / 20 * min 1 (σ / t) := by gcongr
      _ ≤ Real.arctan A - Real.arctan B := h

/-- info: 'FormalResearch.CohnElkies.ceEll_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceEll_lt

/-- info: 'FormalResearch.CohnElkies.ceEll_deriv_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceEll_deriv_gt

/-- info: 'FormalResearch.CohnElkies.ceHth_le_of_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceHth_le_of_le_one

/-- info: 'FormalResearch.CohnElkies.ceHth_lt_of_ge_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ceHth_lt_of_ge_one

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgePhiDeriv_ge

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv2_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgePhiDeriv2_abs_le

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv2_abs_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgePhiDeriv2_abs_ge

/-- info: 'FormalResearch.CohnElkies.edgePhiDeriv3_abs_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms edgePhiDeriv3_abs_le

/-- info: 'FormalResearch.CohnElkies.m2_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms m2_bounds

/-- info: 'FormalResearch.CohnElkies.m1_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms m1_bound

/-- info: 'FormalResearch.CohnElkies.stripG_deriv_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stripG_deriv_bounds

/-- info: 'FormalResearch.CohnElkies.im_stripG_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms im_stripG_ge

end FormalResearch.CohnElkies
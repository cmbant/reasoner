module

public import FormalResearch.Racah.P2AnalyticCarrier3j
public import FormalResearch.Racah.P2AnalyticTaylor

/-!
# The `3j` bulk expansion (Weyl P2, `thm:3jeven`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, `thm:3jeven` (`eq:3jevenexp`).

## Results

* `analyticAt_ptilde3`: `(τ,t) ↦ P̃_{L₀+k}(τ;t)` is real analytic on all of `ℝ²`.
* `Gc3Dom`, `analyticAt_Gc3`, `analyticOnNhd_Gc3`: the closed-form germ `Gc3 M σ k x t` is real
  analytic on the open set where its two radicands are positive; this set contains `(x,0)` for
  every `x ∈ (-1,1)`.
* `Gc3_analytic_box`: for compact `K ⊆ (-1,1)` there are `δ, ρ > 0` with `K ⊆ U := (-1+δ,1-δ)`,
  `closure U ⊆ (-1,1)`, and `Gc3` analytic on `U × (-ρ,ρ)` (the open interval `U` and radius `ρ`
  of `thm:3jeven`).
* `Phi3j_eq_Gc3_spec`: the exact identity `Φ_L^{M,σ}(x;1/N) = G(x, N⁻²)` at every admissible
  lattice point, with the hypotheses of the paper (`SpecAdm`, `Lat4`, `L ≤ N-1`).
* `f3even M σ k r x := taylorCoeff (fun x t => Gc3 M σ k x t) r x` (the paper's `f_{2r}`);
  `f3even_zero` (`f_0 = dZero3`), `analyticOnNhd_f3even` (analytic in `x ∈ (-1,1)`).
* `Phi3j_even_expansion` (**`thm:3jeven`, `eq:3jevenexp`**): for compact `K ⊆ (-1,1)` and every `R`
  there are `C, N₀` with `|Φ_L^{M,σ} - ∑_{r<R} f_{2r}(2μ/N) N^{-2r}| ≤ C N^{-2R}` for all
  admissible `N ≥ N₀` and lattice `μ` with `2μ/N ∈ K`.  The expansion is in `t = N⁻²`, so no
  odd power of `N⁻¹` occurs.
* `f3even_regge`, `f3even_negMσ`, `f3even_swap`: `cor:3jcoeffsym` (`eq:coeffRegge`,
  `eq:coeffSign`, `eq:coeffTranspose`), coefficientwise, from the exact symmetries of `Gc3`.
* `Phi3j_half_exact`, `Phi3j_half_expansion`: `rem:spinhalf`.
* `Phi3j_moving_point`: `rem:movingpoint`.

`f_0` is `dZero3` (the would-be Wigner `d`); its identification with the Wigner `d`-function is
not part of this file.
-/

@[expose] public section

namespace FormalResearch.Racah

open FormalResearch.Wigner Polynomial Set Filter Topology

/-! ### Analyticity of the carrier polynomials and of the germ

`P2AnalyticCore` cannot be imported together with `P2AnalyticCarrier3j` (both declare `Ct_pos` and
`Ct_zero_t`), so the two generic analytic lemmas needed are re-proved here under `_3j` names. -/

lemma analyticAt_Ct_comp_3j {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (r : ℕ)
    {u t : X → ℝ} {x : X} (hu : AnalyticAt ℝ u x) (ht : AnalyticAt ℝ t x) :
    AnalyticAt ℝ (fun y => Ct r (u y) (t y)) x := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r, ih with
    | 0, _ => simpa [Ct_zero] using analyticAt_const
    | 1, _ => simpa [Ct_one] using hu
    | r + 2, ih =>
      simp only [Ct_succ_succ]
      exact ((hu.pow 2).sub (analyticAt_const.mul ht)).mul (ih r (by omega))

lemma analyticAt_sqrt_comp_3j {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {g : X → ℝ} {p₀ : X} (hg : AnalyticAt ℝ g p₀) (h0 : 0 < g p₀) :
    AnalyticAt ℝ (fun p => Real.sqrt (g p)) p₀ := by
  have hlog : AnalyticAt ℝ (fun p => Real.log (g p)) p₀ :=
    (analyticAt_log h0).comp_of_eq hg rfl
  have h1 : AnalyticAt ℝ (fun p => Real.exp (Real.log (g p) / 2)) p₀ :=
    analyticAt_rexp.comp_of_eq hlog.div_const rfl
  refine h1.congr ?_
  filter_upwards [hg.continuousAt.eventually (lt_mem_nhds h0)] with p hp
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hp]
  ring_nf

lemma analyticAt_step3 (M σ L : ℚ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {τ t a b : X → ℝ} {x : X} (hτ : AnalyticAt ℝ τ x) (ht : AnalyticAt ℝ t x)
    (ha : AnalyticAt ℝ a x) (hb : AnalyticAt ℝ b x) :
    AnalyticAt ℝ (fun y => step3 M σ L (τ y) (t y) (a y) (b y)) x := by
  unfold step3
  have h1 : AnalyticAt ℝ (fun y => (2 * (L : ℝ) + 1) * ((L : ℝ) * ((L : ℝ) + 1) * (1 - 2 * τ y) -
      (M : ℝ) * σ)) x :=
    analyticAt_const.mul (((analyticAt_const.mul (analyticAt_const.sub
      (analyticAt_const.mul hτ)))).sub analyticAt_const)
  have h2 : AnalyticAt ℝ (fun y => ((L : ℝ) + 1) * Rk M σ L * (1 - (L : ℝ) ^ 2 * t y)) x :=
    analyticAt_const.mul (analyticAt_const.sub (analyticAt_const.mul ht))
  exact ((h1.mul ha).sub (h2.mul hb)).div_const


theorem analyticAt_ptilde3 (M σ : ℚ) (k : ℕ) (p : ℝ × ℝ) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => ptilde3 M σ k q.1 q.2) p := by
  have hτ : AnalyticAt ℝ (fun q : ℝ × ℝ => q.1) p := analyticAt_fst
  have ht : AnalyticAt ℝ (fun q : ℝ × ℝ => q.2) p := analyticAt_snd
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simpa [ptilde3] using analyticAt_const
    | 1, _ =>
      by_cases h : max |M| |σ| = 0
      · simp only [ptilde3, h, ite_true]
        exact analyticAt_const.sub (analyticAt_const.mul hτ)
      · simp only [ptilde3, h, ite_false]
        exact analyticAt_step3 M σ _ hτ ht analyticAt_const analyticAt_const
    | k + 2, ih =>
      simp only [ptilde3]
      exact analyticAt_step3 M σ _ hτ ht (ih (k + 1) (by omega)) (ih k (by omega))


/-- The open set on which both radicands of `Gc3` are positive. -/
def Gc3Dom (M σ : ℚ) (k : ℕ) : Set (ℝ × ℝ) :=
  {p | 0 < Ct (pPlus3 M σ) ((1 - p.1) / 2) p.2 * Ct (pMinus3 M σ) ((1 + p.1) / 2) p.2 ∧
    0 < Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 p.2}

lemma analyticAt_radicand_A (M σ : ℚ) (p : ℝ × ℝ) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Ct (pPlus3 M σ) ((1 - q.1) / 2) q.2 *
      Ct (pMinus3 M σ) ((1 + q.1) / 2) q.2) p := by
  have hx : AnalyticAt ℝ (fun q : ℝ × ℝ => q.1) p := analyticAt_fst
  have ht : AnalyticAt ℝ (fun q : ℝ × ℝ => q.2) p := analyticAt_snd
  exact (analyticAt_Ct_comp_3j _ ((analyticAt_const.sub hx).div_const) ht).mul
    (analyticAt_Ct_comp_3j _ ((analyticAt_const.add hx).div_const) ht)

lemma analyticAt_radicand_B (M σ : ℚ) (k : ℕ) (p : ℝ × ℝ) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 q.2) p :=
  analyticAt_Ct_comp_3j _ analyticAt_const analyticAt_snd

lemma Gc3Dom_isOpen (M σ : ℚ) (k : ℕ) : IsOpen (Gc3Dom M σ k) := by
  have hA : Continuous (fun q : ℝ × ℝ => Ct (pPlus3 M σ) ((1 - q.1) / 2) q.2 *
      Ct (pMinus3 M σ) ((1 + q.1) / 2) q.2) :=
    continuous_iff_continuousAt.mpr fun p => (analyticAt_radicand_A M σ p).continuousAt
  have hB : Continuous (fun q : ℝ × ℝ => Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 q.2) :=
    continuous_iff_continuousAt.mpr fun p => (analyticAt_radicand_B M σ k p).continuousAt
  exact (isOpen_lt continuous_const hA).inter (isOpen_lt continuous_const hB)

/-- `Gc3` is real analytic (jointly in `(x,t)`) at every point where the radicands are positive. -/
theorem analyticAt_Gc3 (M σ : ℚ) (k : ℕ) {p : ℝ × ℝ} (hp : p ∈ Gc3Dom M σ k) :
    AnalyticAt ℝ (fun q : ℝ × ℝ => Gc3 M σ k q.1 q.2) p := by
  have h1 := analyticAt_sqrt_comp_3j (analyticAt_radicand_A M σ p) hp.1
  have h2 := analyticAt_sqrt_comp_3j (analyticAt_radicand_B M σ k p) hp.2
  have h3 : 0 < Real.sqrt (Ct (pPlus3 M σ + pMinus3 M σ + 2 * k + 1) 1 p.2) :=
    Real.sqrt_pos.mpr hp.2
  have h4 := analyticAt_ptilde3 M σ k p
  have h5 : AnalyticAt ℝ (fun q : ℝ × ℝ => ptilde3 M σ k ((1 - q.1) / 2) q.2) p := by
    have := analyticAt_ptilde3 M σ k (((1 - p.1) / 2, p.2))
    have hc : AnalyticAt ℝ (fun q : ℝ × ℝ => (((1 - q.1) / 2, q.2) : ℝ × ℝ)) p :=
      (((analyticAt_const.sub analyticAt_fst).div_const : AnalyticAt ℝ
        (fun q : ℝ × ℝ => (1 - q.1) / 2) p)).prod analyticAt_snd
    exact this.comp_of_eq hc rfl
  exact (h1.div h2 h3.ne').mul h5

theorem analyticOnNhd_Gc3 (M σ : ℚ) (k : ℕ) :
    AnalyticOnNhd ℝ (fun q : ℝ × ℝ => Gc3 M σ k q.1 q.2) (Gc3Dom M σ k) :=
  fun _ hp => analyticAt_Gc3 M σ k hp

/-- `(x,0) ∈ Gc3Dom` for `x ∈ (-1,1)`: the radicands at `t = 0` are `((1∓x)/2)^p > 0` and `1`. -/
theorem mem_Gc3Dom_zero (M σ : ℚ) (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (x, (0 : ℝ)) ∈ Gc3Dom M σ k := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · simp only [Ct_zero_t]
    have : 0 < (1 - x) / 2 := by linarith
    have : 0 < (1 + x) / 2 := by linarith
    positivity
  · simp [Ct_zero_t]

/-- **Analyticity box** (`thm:3jeven`): for compact `K ⊆ (-1,1)` there are `δ, ρ > 0` such that
`K ⊆ U := (-1+δ, 1-δ)` (so `closure U ⊆ (-1,1)`) and `Gc3` is real analytic on `U × (-ρ, ρ)`. -/
theorem Gc3_analytic_box (M σ : ℚ) (k : ℕ) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ K ⊆ Ioo (-1 + δ) (1 - δ) ∧
      Icc (-1 + δ) (1 - δ) ⊆ Ioo (-1 : ℝ) 1 ∧
      AnalyticOnNhd ℝ (fun q : ℝ × ℝ => Gc3 M σ k q.1 q.2) (Ioo (-1 + δ) (1 - δ) ×ˢ Ioo (-ρ) ρ) := by
  obtain ⟨δ₀, hδ₀, hth⟩ := hK.exists_thickening_subset_open isOpen_Ioo hKI
  set δ := δ₀ / 2 with hδ
  have hδpos : 0 < δ := by positivity
  have hKU : K ⊆ Ioo (-1 + δ) (1 - δ) := by
    intro x hx
    have h1 : x + δ ∈ Metric.thickening δ₀ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨x, hx, ?_⟩
      rw [Real.dist_eq]; rw [abs_of_nonneg (by linarith)]; linarith
    have h2 : x - δ ∈ Metric.thickening δ₀ K := by
      rw [Metric.mem_thickening_iff]
      refine ⟨x, hx, ?_⟩
      rw [Real.dist_eq]; rw [abs_of_nonpos (by linarith)]; linarith
    have a1 := (hth h1).2
    have a2 := (hth h2).1
    constructor <;> linarith
  have hI : Icc (-1 + δ) (1 - δ) ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  obtain ⟨ρ, hρ, hρU⟩ := exists_tube (isCompact_Icc : IsCompact (Icc (-1 + δ) (1 - δ)))
    (Gc3Dom_isOpen M σ k)
    (fun p hp => by
      obtain ⟨hp1, hp2⟩ := hp
      have : p.2 = 0 := hp2
      have hp' : p = (p.1, (0 : ℝ)) := Prod.ext rfl this
      rw [hp']
      exact mem_Gc3Dom_zero M σ k (hI hp1))
  refine ⟨δ, ρ, hδpos, hρ, hKU, hI, ?_⟩
  refine (analyticOnNhd_Gc3 M σ k).mono ?_
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  exact hρU ⟨⟨hx.1.le, hx.2.le⟩, ⟨ht.1.le, ht.2.le⟩⟩


/-! ### The exact identity under the paper's hypotheses -/

/-- An admissible `(M,σ,N)` has `|M-σ|` and `|M+σ|` natural numbers (`p_+`, `p_-`). -/
lemma specAdm_alpha_beta {M σ N : ℚ} (hA : SpecAdm M σ N) :
    ∃ α β : ℕ, |M - σ| = α ∧ |M + σ| = β := by
  obtain ⟨⟨⟨p1, hp1⟩, ⟨p2, hp2⟩, -⟩, ⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ := hA
  unfold jMinus jPlus at hp1 hp2
  have hab : ∀ n : ℤ, ((n.natAbs : ℕ) : ℚ) = |(n : ℚ)| := by
    intro n; rw [Nat.cast_natAbs]; push_cast; rfl
  refine ⟨((q1 : ℤ) - p2).natAbs, ((p2 : ℤ) - q2).natAbs, ?_, ?_⟩
  · rw [hab]; congr 1; push_cast; linarith
  · rw [hab]; congr 1; push_cast; linarith

/-- **`Φ = G(x, N⁻²)`** at every admissible lattice point (`SpecAdm`, `Lat4`), for every rank
`L = L₀ + k ≤ N - 1` (`Phi3j_eq_Gc3` with `α, β` extracted from admissibility). -/
theorem Phi3j_eq_Gc3_spec (M σ N μ : ℚ) (hA : SpecAdm M σ N) (hN : 0 < N)
    (hlat : Lat4 M σ N μ) (k : ℕ) (hk : max |M| |σ| + k + 1 ≤ N) :
    Phi3j (max |M| |σ| + k) M σ N μ = Gc3 M σ k (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2) := by
  obtain ⟨α, β, hα, hβ⟩ := specAdm_alpha_beta hA
  exact Phi3j_eq_Gc3 M σ N μ α β hα hβ hA hN hlat k hk

/-! ### The Taylor coefficients `f_{2r}` -/

/-- The paper's `f_{2r}^{L,M,σ}(x)`, `L = L₀ + k`: the `t^r` Taylor coefficient of `t ↦ G(x,t)`
at `t = 0`. -/
noncomputable def f3even (M σ : ℚ) (k r : ℕ) (x : ℝ) : ℝ :=
  taylorCoeff (fun x t => Gc3 M σ k x t) r x

/-- `f_0 = dZero3` (the `t = 0` carrier; not identified with the Wigner `d` here). -/
theorem f3even_zero (M σ : ℚ) (k : ℕ) (x : ℝ) : f3even M σ k 0 x = dZero3 M σ k x := by
  simp [f3even, taylorCoeff, Gc3_zero]

/-- The coefficients `f_{2r}` are real analytic in `x ∈ (-1,1)`. -/
theorem analyticOnNhd_f3even (M σ : ℚ) (k r : ℕ) :
    AnalyticOnNhd ℝ (f3even M σ k r) (Ioo (-1 : ℝ) 1) := by
  have h := analyticOnNhd_taylorCoeff (Gc3Dom_isOpen M σ k) (analyticOnNhd_Gc3 M σ k) r
  exact (h.mono (fun x hx => mem_Gc3Dom_zero M σ k hx))

theorem continuousOn_f3even (M σ : ℚ) (k r : ℕ) : ContinuousOn (f3even M σ k r) (Ioo (-1 : ℝ) 1) :=
  (analyticOnNhd_f3even M σ k r).continuousOn

/-! ### `thm:3jeven` -/

/-- **`thm:3jeven`, `eq:3jevenexp`** (proved).  Fix `L = L₀ + k`, `M`, `σ`, a compact
`K ⊆ (-1,1)` and `R`.  There are `C, N₀` such that for every admissible `N ≥ N₀` and every
physical lattice point `μ` with `x = 2μ/N ∈ K`,
`|Φ_L^{M,σ}(x;N⁻¹) - ∑_{r<R} f_{2r}(x) N^{-2r}| ≤ C N^{-2R}`.
The expansion is in `t = N⁻²` (no odd power of `N⁻¹`), the coefficients `f_{2r} = f3even M σ k r`
are analytic in `x ∈ (-1,1)` with `f_0 = dZero3`; the rank bound `L ≤ N - 1` is part of `N ≥ N₀`. -/
theorem Phi3j_even_expansion (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) (R : ℕ) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) →
      2 * (μ : ℝ) / N ∈ K →
      |Phi3j L M σ N μ -
          ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)| ≤
        C / (N : ℝ) ^ (2 * R) := by
  subst hL
  have hKU : K ×ˢ ({0} : Set ℝ) ⊆ Gc3Dom M σ k := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    have : t = 0 := ht
    subst this
    exact mem_Gc3Dom_zero M σ k (hKI hx)
  obtain ⟨ρ, hρ, C, hC⟩ := taylor_uniform_of_analytic (Gc3Dom_isOpen M σ k)
    (analyticOnNhd_Gc3 M σ k) hK hKU R
  refine ⟨C, max (((max |M| |σ| + k + 1 : ℚ)) : ℝ) (max 1 (1 / ρ)), ?_⟩
  intro N μ hA hlat hN0 hx
  have hN1 : ((max |M| |σ| + k + 1 : ℚ) : ℝ) ≤ N := le_trans (le_max_left _ _) hN0
  have hN2 : max 1 (1 / ρ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN0
  have hk : max |M| |σ| + k + 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hN2)
  have hNq : 0 < N := by exact_mod_cast hNpos
  have ht : |1 / (N : ℝ) ^ 2| ≤ ρ := by
    rw [abs_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
    have h1 : 1 / ρ ≤ N := le_trans (le_max_right _ _) hN2
    have h2 : (1 : ℝ) ≤ N := le_trans (le_max_left _ _) hN2
    have h3 : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have h4 : 1 / ρ ≤ N ^ 2 := le_trans h1 h3
    rw [div_le_iff₀ hρ] at h4
    linarith
  have key := hC _ hx _ ht
  rw [Phi3j_eq_Gc3_spec M σ N μ hA hNq hlat k hk]
  have e1 : ∀ r : ℕ, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r) =
      taylorCoeff (fun x t => Gc3 M σ k x t) r (2 * (μ : ℝ) / N) * (1 / (N : ℝ) ^ 2) ^ r := by
    intro r
    unfold f3even
    rw [one_div, inv_pow, ← pow_mul, div_eq_mul_inv]
  simp only [e1]
  have e2 : |1 / (N : ℝ) ^ 2| ^ R = 1 / (N : ℝ) ^ (2 * R) := by
    rw [abs_of_nonneg (by positivity), one_div, inv_pow, ← pow_mul, one_div]
  rw [e2] at key
  calc _ ≤ C * (1 / (N : ℝ) ^ (2 * R)) := key
    _ = C / (N : ℝ) ^ (2 * R) := by ring


/-! ### `cor:3jcoeffsym`: coefficientwise symmetries -/

lemma pPlus3_regge (M σ : ℚ) : pPlus3 (-σ) (-M) = pPlus3 M σ := by
  unfold pPlus3; rw [show -σ - -M = -(σ - M) by ring, abs_neg, abs_sub_comm]

lemma pMinus3_regge (M σ : ℚ) : pMinus3 (-σ) (-M) = pMinus3 M σ := by
  unfold pMinus3; rw [show -σ + -M = -(M + σ) by ring, abs_neg]

lemma pPlus3_neg (M σ : ℚ) : pPlus3 (-M) (-σ) = pPlus3 M σ := by
  unfold pPlus3; rw [show -M - -σ = -(M - σ) by ring, abs_neg]

lemma pMinus3_neg (M σ : ℚ) : pMinus3 (-M) (-σ) = pMinus3 M σ := by
  unfold pMinus3; rw [show -M + -σ = -(M + σ) by ring, abs_neg]

lemma pPlus3_swap (M σ : ℚ) : pPlus3 σ M = pPlus3 M σ := by
  unfold pPlus3; rw [abs_sub_comm]

lemma pMinus3_swap (M σ : ℚ) : pMinus3 σ M = pMinus3 M σ := by
  unfold pMinus3; rw [add_comm]

/-- `ptilde3` for a pair `(M',σ')` with the same recursion data (`L₀`, `R_k`, `Mσ`) and a start
differing by the factor `s` is `s` times `ptilde3 M σ`. -/
lemma ptilde3_scale {M σ M' σ' : ℚ} (s : ℝ) (hmax : max |M'| |σ'| = max |M| |σ|)
    (hR : ∀ j : ℚ, Rk M' σ' j = Rk M σ j) (hprod : (M' : ℝ) * σ' = M * σ)
    (hseed : seed3 M' σ' = s * seed3 M σ) (hz : max |M| |σ| = 0 → s = 1) (k : ℕ) (τ t : ℝ) :
    ptilde3 M' σ' k τ t = s * ptilde3 M σ k τ t := by
  have hstep : ∀ (L : ℚ) (a b : ℝ), step3 M' σ' L τ t (s * a) (s * b) =
      s * step3 M σ L τ t a b := by
    intro L a b
    unfold step3
    rw [hR, hR, hprod]
    ring
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [ptilde3_zero, hseed]
    | 1, _ =>
      by_cases h : max |M| |σ| = 0
      · rw [ptilde3_one_of_eq _ _ _ _ h, ptilde3_one_of_eq _ _ _ _ (hmax.trans h), hz h]
        ring
      · rw [ptilde3_one_of_ne _ _ _ _ h, ptilde3_one_of_ne _ _ _ _ (by rwa [hmax]), hmax, hseed]
        have := hstep (max |M| |σ|) (seed3 M σ) 0
        simpa using this
    | k + 2, ih =>
      rw [ptilde3_succ_succ, ptilde3_succ_succ, hmax, ih (k + 1) (by omega), ih k (by omega),
        hstep]

lemma Rk_regge (M σ j : ℚ) : Rk (-σ) (-M) j = Rk M σ j := by
  unfold Rk; push_cast; rw [neg_sq, neg_sq, mul_comm]

lemma Rk_neg (M σ j : ℚ) : Rk (-M) (-σ) j = Rk M σ j := by
  unfold Rk; push_cast; rw [neg_sq, neg_sq]

lemma Rk_swap (M σ j : ℚ) : Rk σ M j = Rk M σ j := by
  unfold Rk; rw [mul_comm]

/-- `Gc3` depends on `(M,σ)` only through `p_±`, `L₀`, `R_k`, `Mσ` and the start `seed3`. -/
lemma Gc3_scale {M σ M' σ' : ℚ} (s : ℝ) (hp : pPlus3 M' σ' = pPlus3 M σ)
    (hm : pMinus3 M' σ' = pMinus3 M σ) (hmax : max |M'| |σ'| = max |M| |σ|)
    (hR : ∀ j : ℚ, Rk M' σ' j = Rk M σ j) (hprod : (M' : ℝ) * σ' = M * σ)
    (hseed : seed3 M' σ' = s * seed3 M σ) (hz : max |M| |σ| = 0 → s = 1) (k : ℕ) (x t : ℝ) :
    Gc3 M' σ' k x t = s * Gc3 M σ k x t := by
  unfold Gc3
  rw [hp, hm, ptilde3_scale s hmax hR hprod hseed hz]
  ring

lemma iteratedDeriv_const_mul_fun (c : ℝ) (g : ℝ → ℝ) (r : ℕ) :
    iteratedDeriv r (fun t => c * g t) = fun t => c * iteratedDeriv r g t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field', iteratedDeriv_succ]

lemma taylorCoeff_const_mul (c : ℝ) (g : ℝ → ℝ → ℝ) (r : ℕ) (z : ℝ) :
    taylorCoeff (fun z t => c * g z t) r z = c * taylorCoeff g r z := by
  unfold taylorCoeff
  rw [iteratedDeriv_const_mul_fun]
  ring

lemma f3even_scale {M σ M' σ' : ℚ} (s : ℝ) (hp : pPlus3 M' σ' = pPlus3 M σ)
    (hm : pMinus3 M' σ' = pMinus3 M σ) (hmax : max |M'| |σ'| = max |M| |σ|)
    (hR : ∀ j : ℚ, Rk M' σ' j = Rk M σ j) (hprod : (M' : ℝ) * σ' = M * σ)
    (hseed : seed3 M' σ' = s * seed3 M σ) (hz : max |M| |σ| = 0 → s = 1) (k r : ℕ) (x : ℝ) :
    f3even M' σ' k r x = s * f3even M σ k r x := by
  unfold f3even
  have : (fun x t => Gc3 M' σ' k x t) = fun x t => s * Gc3 M σ k x t := by
    funext x t; exact Gc3_scale s hp hm hmax hR hprod hseed hz k x t
  rw [this, taylorCoeff_const_mul]

/-- The sign `ε(M,σ) = (-1)^{p_+}` relating the seeds of `(M,σ)` and `(-M,-σ)`, `(σ,M)`. -/
lemma seed3_flip {M' σ' : ℚ} (M σ : ℚ) (hp : pPlus3 M' σ' = pPlus3 M σ) (hm : pMinus3 M' σ' = pMinus3 M σ)
    (hc : (σ' ≤ M') ↔ (M ≤ σ)) :
    seed3 M' σ' = (-1 : ℝ) ^ pPlus3 M σ * seed3 M σ := by
  unfold seed3
  rw [hp, hm]
  by_cases h1 : σ ≤ M <;> by_cases h2 : M ≤ σ
  · have he : M = σ := le_antisymm h2 h1
    have hp0 : pPlus3 M σ = 0 := by unfold pPlus3; rw [he]; simp
    have : (σ' ≤ M') := hc.mpr h2
    simp [this, h1, hp0]
  · have : ¬ (σ' ≤ M') := fun h => h2 (hc.mp h)
    have hsq : ((-1 : ℝ) ^ pPlus3 M σ) * ((-1 : ℝ) ^ pPlus3 M σ) = 1 := by
      rw [← mul_pow]; norm_num
    simp only [this, h1, ite_true, ite_false, one_mul]
    rw [← mul_assoc, hsq, one_mul]
  · have : (σ' ≤ M') := hc.mpr h2
    simp [this, h1]
  · exact absurd (le_total σ M) (by tauto)


/-- `(-1)^{p_+} = (-1)^{M-σ}` when `M - σ` is an integer `n`. -/
lemma neg_one_pow_pPlus3 {M σ : ℚ} {n : ℤ} (hn : M - σ = (n : ℚ)) :
    (-1 : ℝ) ^ pPlus3 M σ = (-1 : ℝ) ^ n := by
  have h1 : pPlus3 M σ = n.natAbs := by
    unfold pPlus3
    rw [hn, ← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    exact Nat.floor_natCast _
  rw [h1]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp
  · simp [zpow_neg, ← inv_pow]

/-- **`eq:coeffRegge` of `cor:3jcoeffsym`** (proved): `f_{2r}^{L,-σ,-M} = f_{2r}^{L,M,σ}`. -/
theorem f3even_regge (M σ : ℚ) (k r : ℕ) (x : ℝ) :
    f3even (-σ) (-M) k r x = f3even M σ k r x := by
  have := f3even_scale (M := M) (σ := σ) (M' := -σ) (σ' := -M) 1 (pPlus3_regge M σ)
    (pMinus3_regge M σ) (max_regge M σ) (Rk_regge M σ) (by push_cast; ring)
    (by rw [seed3_regge, one_mul]) (fun _ => rfl) k r x
  rwa [one_mul] at this

lemma max_abs_eq_zero_imp {M σ : ℚ} (h : max |M| |σ| = 0) : pPlus3 M σ = 0 := by
  have hM : M = 0 := abs_nonpos_iff.mp (h ▸ le_max_left _ _)
  have hs : σ = 0 := abs_nonpos_iff.mp (h ▸ le_max_right _ _)
  subst hM hs; simp [pPlus3]

/-- **`eq:coeffSign`** (proved): `f_{2r}^{L,-M,-σ} = (-1)^{M-σ} f_{2r}^{L,M,σ}`, with the sign
`(-1)^{p_+}`, `p_+ = |M-σ|` (`f3even_negMσ_zpow` for the sign written `(-1)^{M-σ}`). -/
theorem f3even_negMσ (M σ : ℚ) (k r : ℕ) (x : ℝ) :
    f3even (-M) (-σ) k r x = (-1 : ℝ) ^ pPlus3 M σ * f3even M σ k r x := by
  refine f3even_scale (M := M) (σ := σ) (M' := -M) (σ' := -σ) _ (pPlus3_neg M σ)
    (pMinus3_neg M σ) (by rw [abs_neg, abs_neg]) (Rk_neg M σ) (by push_cast; ring)
    (seed3_flip M σ (pPlus3_neg M σ) (pMinus3_neg M σ) neg_le_neg_iff)
    (fun h => by rw [max_abs_eq_zero_imp h]; simp) k r x


/-- **`eq:coeffTranspose`** (proved): `f_{2r}^{L,σ,M} = (-1)^{M-σ} f_{2r}^{L,M,σ}`
(sign `(-1)^{p_+}`). -/
theorem f3even_swap (M σ : ℚ) (k r : ℕ) (x : ℝ) :
    f3even σ M k r x = (-1 : ℝ) ^ pPlus3 M σ * f3even M σ k r x := by
  refine f3even_scale (M := M) (σ := σ) (M' := σ) (σ' := M) _ (pPlus3_swap M σ)
    (pMinus3_swap M σ) (max_comm _ _) (Rk_swap M σ) (by ring)
    (seed3_flip M σ (pPlus3_swap M σ) (pMinus3_swap M σ) Iff.rfl)
    (fun h => by rw [max_abs_eq_zero_imp h]; simp) k r x

/-- `eq:coeffSign` with the sign written `(-1)^{M-σ}` (`M - σ = n` an integer, as for every
admissible label pair). -/
theorem f3even_negMσ_zpow (M σ : ℚ) {n : ℤ} (hn : M - σ = (n : ℚ)) (k r : ℕ) (x : ℝ) :
    f3even (-M) (-σ) k r x = (-1 : ℝ) ^ n * f3even M σ k r x := by
  rw [f3even_negMσ, neg_one_pow_pPlus3 hn]

/-- `eq:coeffTranspose` with the sign written `(-1)^{M-σ}`. -/
theorem f3even_swap_zpow (M σ : ℚ) {n : ℤ} (hn : M - σ = (n : ℚ)) (k r : ℕ) (x : ℝ) :
    f3even σ M k r x = (-1 : ℝ) ^ n * f3even M σ k r x := by
  rw [f3even_swap, neg_one_pow_pPlus3 hn]


/-! ### The physical lattice lies in `[-1,1]` -/

lemma Lat4.two_mu_bounds {M σ N μ : ℚ} (h : Lat4 M σ N μ) :
    -(N - 1) ≤ 2 * μ ∧ 2 * μ ≤ N - 1 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ := h
  have h1 : (0 : ℚ) ≤ a := Nat.cast_nonneg a
  have h2 : (0 : ℚ) ≤ b := Nat.cast_nonneg b
  have h3 : (0 : ℚ) ≤ c := Nat.cast_nonneg c
  have h4 : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  unfold jMinus jPlus mMinus mPlus at *
  constructor <;> linarith

/-- The physical lattice point `x = 2μ/N` lies in `[-1,1]`. -/
lemma Lat4.x_mem_Icc {M σ N μ : ℚ} (h : Lat4 M σ N μ) (hN : 0 < N) :
    2 * (μ : ℝ) / N ∈ Icc (-1 : ℝ) 1 := by
  obtain ⟨h1, h2⟩ := h.two_mu_bounds
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1' : -((N : ℝ) - 1) ≤ 2 * μ := by exact_mod_cast h1
  have h2' : 2 * (μ : ℝ) ≤ (N : ℝ) - 1 := by exact_mod_cast h2
  constructor
  · rw [le_div_iff₀ hNr]; linarith
  · rw [div_le_iff₀ hNr]; linarith

/-! ### `rem:spinhalf` -/

lemma half_data {M σ : ℚ} (hM : M = 1 / 2 ∨ M = -1 / 2) (hσ : σ = 1 / 2 ∨ σ = -1 / 2) :
    max |M| |σ| = 1 / 2 ∧
      ((pPlus3 M σ = 0 ∧ pMinus3 M σ = 1) ∨ (pPlus3 M σ = 1 ∧ pMinus3 M σ = 0)) ∧
      (seed3 M σ = 1 ∨ seed3 M σ = -1) := by
  rcases hM with rfl | rfl <;> rcases hσ with rfl | rfl
  · refine ⟨by norm_num, Or.inl ⟨by norm_num [pPlus3], by norm_num [pMinus3]⟩,
      Or.inl (by norm_num [seed3, pPlus3, pMinus3])⟩
  · refine ⟨by norm_num, Or.inr ⟨by norm_num [pPlus3], by norm_num [pMinus3]⟩,
      Or.inr (by norm_num [seed3, pPlus3, pMinus3])⟩
  · refine ⟨by norm_num, Or.inr ⟨by norm_num [pPlus3], by norm_num [pMinus3]⟩,
      Or.inl (by norm_num [seed3, pPlus3, pMinus3])⟩
  · refine ⟨by norm_num, Or.inl ⟨by norm_num [pPlus3], by norm_num [pMinus3]⟩,
      Or.inl (by norm_num [seed3, pPlus3, pMinus3])⟩

lemma Ct_of_le_one {p : ℕ} (hp : p ≤ 1) (u t : ℝ) : Ct p u t = u ^ p := by
  interval_cases p <;> simp [Ct_zero, Ct_one]

/-- `rem:spinhalf`, germ form: for `M, σ ∈ {±1/2}` (`L₀ = 1/2`, `k = 0`) the germ is
`G(x,t) = dZero3(x) / √(1 - t/4)`, where `dZero3 M σ 0 x = ±√((1±x)/2)` is the explicit
`d^{1/2}_{Mσ}(arccos x)` (`√((1+x)/2)` for `M = σ`, `-√((1-x)/2)` for `(M,σ) = (1/2,-1/2)`,
`+√((1-x)/2)` for `(-1/2,1/2)`). -/
theorem Gc3_half {M σ : ℚ} (hM : M = 1 / 2 ∨ M = -1 / 2) (hσ : σ = 1 / 2 ∨ σ = -1 / 2)
    (x t : ℝ) : Gc3 M σ 0 x t = dZero3 M σ 0 x / Real.sqrt (1 - t / 4) := by
  obtain ⟨-, hp, -⟩ := half_data hM hσ
  have hsum : pPlus3 M σ + pMinus3 M σ = 1 := by rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hp1 : pPlus3 M σ ≤ 1 := by rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hm1 : pMinus3 M σ ≤ 1 := by rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hC : Ct (pPlus3 M σ + pMinus3 M σ + 2 * 0 + 1) 1 t = 1 - t / 4 := by
    rw [hsum]
    simp [Ct_succ_succ, Ct_zero]
    ring
  unfold Gc3
  rw [hC, dZero3_zero, Ct_of_le_one hp1, Ct_of_le_one hm1, ptilde3_zero]
  ring

/-- Elementary bound for the exact factor of `eq:spinhalfexact`: for `0 ≤ t ≤ 1`,
`|(1 - t/4)^{-1/2} - 1 - t/8 - 3t²/128| ≤ t³/64`. -/
lemma half_factor_bound {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |1 / Real.sqrt (1 - t / 4) - (1 + t / 8 + 3 * t ^ 2 / 128)| ≤ t ^ 3 / 64 := by
  set r := Real.sqrt (1 - t / 4) with hrdef
  have hr2 : r ^ 2 = 1 - t / 4 := Real.sq_sqrt (by linarith)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr8 : 4 / 5 ≤ r := by nlinarith
  have hrpos : 0 < r := by linarith
  set p : ℝ := 1 + t / 8 + 3 * t ^ 2 / 128 with hp
  set e : ℝ := 5 * t ^ 3 / 512 + 15 * t ^ 4 / 16384 + 9 * t ^ 5 / 65536 with he
  have hq2 : (p * r) ^ 2 = 1 - e := by rw [mul_pow, hr2, hp, he]; ring
  have he0 : 0 ≤ e := by rw [he]; positivity
  have het : e ≤ t ^ 3 / 80 := by
    have a1 : t ^ 4 ≤ t ^ 3 := by nlinarith [pow_nonneg h0 3]
    have a2 : t ^ 5 ≤ t ^ 3 := by nlinarith [pow_nonneg h0 3, pow_nonneg h0 4]
    rw [he]; nlinarith [pow_nonneg h0 3]
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hq0 : 0 ≤ p * r := mul_nonneg hp0 hr0
  have hq1 : p * r ≤ 1 := by nlinarith
  have hlow : 1 - e ≤ p * r := by nlinarith
  have hdiff : 1 / r - p = (1 - p * r) / r := by field_simp
  rw [hdiff, abs_of_nonneg (div_nonneg (by linarith) hr0), div_le_iff₀ hrpos]
  have : t ^ 3 / 80 ≤ t ^ 3 / 64 * r := by
    have := pow_nonneg h0 3
    nlinarith
  linarith

/-- **`rem:spinhalf`, `eq:spinhalfexact`** (proved; `L = 1/2`, `M, σ ∈ {±1/2}`), exact part:
`Φ_{1/2}^{M,σ}(x;1/N) = dZero3(x) / √(1 - 1/(4N²))` at every admissible lattice point,
`x = 2μ/N`, `N ≥ 3/2`. -/
theorem Phi3j_half_exact {M σ N μ : ℚ} (hM : M = 1 / 2 ∨ M = -1 / 2)
    (hσ : σ = 1 / 2 ∨ σ = -1 / 2) (hA : SpecAdm M σ N) (hlat : Lat4 M σ N μ) (hN : 3 / 2 ≤ N) :
    Phi3j (1 / 2) M σ N μ =
      dZero3 M σ 0 (2 * (μ : ℝ) / N) / Real.sqrt (1 - (1 / (N : ℝ) ^ 2) / 4) := by
  obtain ⟨hmax, -, -⟩ := half_data hM hσ
  have hNq : 0 < N := by linarith
  have := Phi3j_eq_Gc3_spec M σ N μ hA hNq hlat 0 (by rw [hmax]; push_cast; linarith)
  rw [hmax] at this
  push_cast at this
  rw [add_zero] at this
  rw [this, Gc3_half hM hσ]

/-- **`rem:spinhalf`, expansion**: with `d = dZero3 M σ 0 (2μ/N)`,
`|Φ_{1/2}^{M,σ} - d (1 + 1/(8N²) + 3/(128N⁴))| ≤ 1/(64 N⁶)` for `N ≥ 3/2`
(the `O(N⁻⁶)` of `eq:spinhalfexact`, with explicit constant). -/
theorem Phi3j_half_expansion {M σ N μ : ℚ} (hM : M = 1 / 2 ∨ M = -1 / 2)
    (hσ : σ = 1 / 2 ∨ σ = -1 / 2) (hA : SpecAdm M σ N) (hlat : Lat4 M σ N μ) (hN : 3 / 2 ≤ N) :
    |Phi3j (1 / 2) M σ N μ - dZero3 M σ 0 (2 * (μ : ℝ) / N) *
        (1 + 1 / (8 * (N : ℝ) ^ 2) + 3 / (128 * (N : ℝ) ^ 4))| ≤ 1 / (64 * (N : ℝ) ^ 6) := by
  obtain ⟨-, hp, hs⟩ := half_data hM hσ
  have hNq : 0 < N := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNq
  have hN32 : (3 / 2 : ℝ) ≤ N := by
    have h := (Rat.cast_le (K := ℝ)).mpr hN
    push_cast at h; exact h
  rw [Phi3j_half_exact hM hσ hA hlat hN]
  set d := dZero3 M σ 0 (2 * (μ : ℝ) / N) with hd
  have hx := hlat.x_mem_Icc hNq
  -- `|d| ≤ 1`
  have hdabs : |d| ≤ 1 := by
    rw [hd, dZero3_zero]
    have hτ0 : 0 ≤ (1 - 2 * (μ : ℝ) / N) / 2 := by linarith [hx.2]
    have hτ1 : (1 - 2 * (μ : ℝ) / N) / 2 ≤ 1 := by linarith [hx.1]
    have hτ0' : 0 ≤ (1 + 2 * (μ : ℝ) / N) / 2 := by linarith [hx.1]
    have hτ1' : (1 + 2 * (μ : ℝ) / N) / 2 ≤ 1 := by linarith [hx.2]
    rw [abs_mul]
    have hsd : |seed3 M σ| = 1 := by rcases hs with h | h <;> rw [h] <;> simp
    rw [hsd, one_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_one.mpr
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> simp <;> assumption
  set t : ℝ := 1 / (N : ℝ) ^ 2 with ht
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one (by positivity)]; nlinarith
  have hb := half_factor_bound ht0 ht1
  have e : d / Real.sqrt (1 - t / 4) - d * (1 + 1 / (8 * (N : ℝ) ^ 2) + 3 / (128 * (N : ℝ) ^ 4)) =
      d * (1 / Real.sqrt (1 - t / 4) - (1 + t / 8 + 3 * t ^ 2 / 128)) := by
    rw [ht]; field_simp
  rw [e, abs_mul]
  calc |d| * |1 / Real.sqrt (1 - t / 4) - (1 + t / 8 + 3 * t ^ 2 / 128)|
      ≤ 1 * (t ^ 3 / 64) := mul_le_mul hdabs hb (abs_nonneg _) zero_le_one
    _ = 1 / (64 * (N : ℝ) ^ 6) := by rw [ht]; field_simp


/-! ### `rem:movingpoint` -/

theorem analyticOnNhd_dZero3 (M σ : ℚ) (k : ℕ) :
    AnalyticOnNhd ℝ (dZero3 M σ k) (Ioo (-1 : ℝ) 1) := by
  have h : dZero3 M σ k = fun x => Gc3 M σ k x 0 := by funext x; rw [Gc3_zero]
  rw [h]
  intro x hx
  have h1 := analyticAt_Gc3 M σ k (mem_Gc3Dom_zero M σ k hx)
  exact h1.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl

/-- **`rem:movingpoint`** (proved, with `d` the `t = 0` carrier `dZero3`): along a lattice point
`x_N = 2μ/N` that moves with `N` (`|μ| ≤ B`, in particular `μ` fixed),
`Φ_L^{M,σ} = f_0(0) + (2μ/N) f_0'(0) + O(N⁻²)`, `f_0 = dZero3`.  The `N⁻¹` term comes from
moving the evaluation point. -/
theorem Phi3j_moving_point (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) (B : ℝ) :
    ∃ C N₀ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) → |(μ : ℝ)| ≤ B →
      |Phi3j L M σ N μ - dZero3 M σ k 0 - (2 * (μ : ℝ) / N) * deriv (dZero3 M σ k) 0| ≤
        C / (N : ℝ) ^ 2 := by
  have hKc : IsCompact (Icc (-1 / 2 : ℝ) (1 / 2)) := isCompact_Icc
  have hKI : Icc (-1 / 2 : ℝ) (1 / 2) ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx; constructor <;> linarith [hx.1, hx.2]
  obtain ⟨C₁, N₁, h₁⟩ := Phi3j_even_expansion M σ L k hL hKc hKI 1
  -- second-order Taylor bound for `dZero3` at `0`
  have hU : IsOpen ((univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1) := isOpen_univ.prod isOpen_Ioo
  have hAn : AnalyticOnNhd ℝ (fun q : ℝ × ℝ => dZero3 M σ k q.2)
      ((univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1) := by
    intro q hq
    exact (analyticOnNhd_dZero3 M σ k q.2 hq.2).comp_of_eq analyticAt_snd rfl
  have hK0 : ({0} : Set ℝ) ×ˢ ({0} : Set ℝ) ⊆ (univ : Set ℝ) ×ˢ Ioo (-1 : ℝ) 1 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    have : b = 0 := hb
    subst this
    exact ⟨trivial, by constructor <;> norm_num⟩
  obtain ⟨ρ, hρ, C₂, h₂⟩ := taylor_uniform_of_analytic hU hAn isCompact_singleton hK0 2
  set ρ' := min ρ (1 / 2) with hρ'
  have hρ'pos : 0 < ρ' := lt_min hρ (by norm_num)
  refine ⟨C₁ + 4 * |C₂| * B ^ 2, max (max N₁ 1) (2 * B / ρ'), ?_⟩
  intro N μ hA hlat hN hμ
  have hN1 : N₁ ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN1' : (1 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2 : 2 * B / ρ' ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hμ
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1'
  have hx : |2 * (μ : ℝ) / N| ≤ ρ' := by
    rw [abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos, abs_mul, abs_two]
    rw [div_le_iff₀ hρ'pos] at hN2
    nlinarith
  have hxK : 2 * (μ : ℝ) / N ∈ Icc (-1 / 2 : ℝ) (1 / 2) := by
    have h5 : ρ' ≤ 1 / 2 := min_le_right _ _
    have := abs_le.mp (hx.trans h5)
    constructor <;> linarith [this.1, this.2]
  have e1 := h₁ N μ hA hlat hN1 hxK
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, div_one, f3even_zero] at e1
  have e2 := h₂ 0 rfl (2 * (μ : ℝ) / N) (hx.trans (min_le_left _ _))
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, taylorCoeff,
    iteratedDeriv_zero, iteratedDeriv_one, pow_zero, pow_one, Nat.factorial_zero,
    Nat.factorial_one, Nat.cast_one, div_one] at e2
  have e3 : |2 * (μ : ℝ) / N| ^ 2 ≤ 4 * B ^ 2 / (N : ℝ) ^ 2 := by
    rw [abs_div, abs_of_pos hNpos, div_pow, abs_mul, abs_two, mul_pow]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    nlinarith [abs_nonneg (μ : ℝ)]
  have e4 : |dZero3 M σ k (2 * (μ : ℝ) / N) - dZero3 M σ k 0 -
      deriv (dZero3 M σ k) 0 * (2 * (μ : ℝ) / N)| ≤ |C₂| * (4 * B ^ 2 / (N : ℝ) ^ 2) := by
    have e2' : |dZero3 M σ k (2 * (μ : ℝ) / N) - dZero3 M σ k 0 -
        deriv (dZero3 M σ k) 0 * (2 * (μ : ℝ) / N)| ≤ C₂ * |2 * (μ : ℝ) / N| ^ 2 := by
      have : dZero3 M σ k (2 * (μ : ℝ) / N) - dZero3 M σ k 0 -
          deriv (dZero3 M σ k) 0 * (2 * (μ : ℝ) / N) =
          dZero3 M σ k (2 * (μ : ℝ) / N) - (dZero3 M σ k 0 * 1 +
            deriv (fun t => dZero3 M σ k t) 0 * (2 * (μ : ℝ) / N)) := by ring
      rw [this]; exact e2
    refine le_trans e2' ?_
    calc C₂ * |2 * (μ : ℝ) / N| ^ 2 ≤ |C₂| * |2 * (μ : ℝ) / N| ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left e3 (abs_nonneg _)
  have e5 : |Phi3j L M σ N μ - dZero3 M σ k 0 - (2 * (μ : ℝ) / N) * deriv (dZero3 M σ k) 0| ≤
      |Phi3j L M σ N μ - dZero3 M σ k (2 * (μ : ℝ) / N)| +
        |dZero3 M σ k (2 * (μ : ℝ) / N) - dZero3 M σ k 0 -
          deriv (dZero3 M σ k) 0 * (2 * (μ : ℝ) / N)| := by
    refine le_trans (le_of_eq ?_) (abs_add_le _ _)
    congr 1; ring
  refine le_trans e5 ?_
  have : (C₁ + 4 * |C₂| * B ^ 2) / (N : ℝ) ^ 2 =
      C₁ / (N : ℝ) ^ 2 + |C₂| * (4 * B ^ 2 / (N : ℝ) ^ 2) := by ring
  rw [this]
  exact add_le_add (by simpa using e1) e4


/-! ### `thm:3jeven` as one statement -/

/-- **`thm:3jeven`, packaged as in the paper** (proved).  For `L = L₀ + k` and compact
`K ⊆ (-1,1)` there are an open interval `U = (-1+δ, 1-δ) ⊇ K` with `closure U ⊆ (-1,1)`, a radius
`ρ > 0`, a function `G = Gc3 M σ k` real analytic on `U × (-ρ,ρ)`, and `N₀` such that
* `Φ_L^{M,σ}(x;1/N) = G(x, N⁻²)` at every admissible lattice point with `N ≥ N₀`, `x = 2μ/N ∈ K`
  (and then `N⁻² < ρ`, `x ∈ U`);
* `G(x,0) = dZero3 M σ k x` for all `x` (`= d^L_{Mσ}(arccos x)` in the paper; not identified here);
* for every `R` the uniform expansion `eq:3jevenexp` holds with `f_{2r} = f3even M σ k r`. -/
theorem Phi3j_thm_3jeven (M σ L : ℚ) (k : ℕ) (hL : L = max |M| |σ| + k) {K : Set ℝ}
    (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ δ ρ N₀ : ℝ, 0 < δ ∧ 0 < ρ ∧ K ⊆ Ioo (-1 + δ) (1 - δ) ∧
      Icc (-1 + δ) (1 - δ) ⊆ Ioo (-1 : ℝ) 1 ∧
      AnalyticOnNhd ℝ (fun q : ℝ × ℝ => Gc3 M σ k q.1 q.2)
        (Ioo (-1 + δ) (1 - δ) ×ˢ Ioo (-ρ) ρ) ∧
      (∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₀ ≤ (N : ℝ) → 2 * (μ : ℝ) / N ∈ K →
        (2 * (μ : ℝ) / N, 1 / (N : ℝ) ^ 2) ∈ Ioo (-1 + δ) (1 - δ) ×ˢ Ioo (-ρ) ρ ∧
          Phi3j L M σ N μ = Gc3 M σ k (2 * (μ : ℝ) / N) (1 / (N : ℝ) ^ 2)) ∧
      (∀ x : ℝ, Gc3 M σ k x 0 = dZero3 M σ k x) ∧
      (∀ R : ℕ, ∃ C N₁ : ℝ, ∀ N μ : ℚ, SpecAdm M σ N → Lat4 M σ N μ → N₁ ≤ (N : ℝ) →
        2 * (μ : ℝ) / N ∈ K →
        |Phi3j L M σ N μ -
            ∑ r ∈ Finset.range R, f3even M σ k r (2 * (μ : ℝ) / N) / (N : ℝ) ^ (2 * r)| ≤
          C / (N : ℝ) ^ (2 * R)) := by
  obtain ⟨δ, ρ, hδ, hρ, hKU, hI, hAn⟩ := Gc3_analytic_box M σ k hK hKI
  refine ⟨δ, ρ, max (((max |M| |σ| + k + 1 : ℚ)) : ℝ) (max 1 (2 / ρ)), hδ, hρ, hKU, hI, hAn,
    ?_, fun x => Gc3_zero M σ k x, fun R => Phi3j_even_expansion M σ L k hL hK hKI R⟩
  intro N μ hA hlat hN0 hx
  subst hL
  have hN1 : ((max |M| |σ| + k + 1 : ℚ) : ℝ) ≤ N := le_trans (le_max_left _ _) hN0
  have hN2 : max 1 (2 / ρ) ≤ (N : ℝ) := le_trans (le_max_right _ _) hN0
  have hk : max |M| |σ| + k + 1 ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) hN2)
  have hNq : 0 < N := by exact_mod_cast hNpos
  refine ⟨⟨hKU hx, ?_, ?_⟩, Phi3j_eq_Gc3_spec M σ N μ hA hNq hlat k hk⟩
  · have : (0 : ℝ) < 1 / (N : ℝ) ^ 2 := by positivity
    linarith
  · have h1 : 2 / ρ ≤ N := le_trans (le_max_right _ _) hN2
    have h2 : (1 : ℝ) ≤ N := le_trans (le_max_left _ _) hN2
    have h3 : (N : ℝ) ≤ N ^ 2 := by nlinarith
    have h4 : 2 / ρ ≤ N ^ 2 := le_trans h1 h3
    rw [div_le_iff₀ hρ] at h4
    rw [div_lt_iff₀ (by positivity)]
    linarith

/-- info: 'FormalResearch.Racah.analyticAt_Gc3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticAt_Gc3

/-- info: 'FormalResearch.Racah.Gc3_analytic_box' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gc3_analytic_box

/-- info: 'FormalResearch.Racah.Phi3j_eq_Gc3_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_eq_Gc3_spec

/-- info: 'FormalResearch.Racah.f3even_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_zero

/-- info: 'FormalResearch.Racah.analyticOnNhd_f3even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms analyticOnNhd_f3even

/-- info: 'FormalResearch.Racah.Phi3j_even_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_even_expansion

/-- info: 'FormalResearch.Racah.Phi3j_thm_3jeven' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_thm_3jeven

/-- info: 'FormalResearch.Racah.f3even_regge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_regge

/-- info: 'FormalResearch.Racah.f3even_negMσ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_negMσ

/-- info: 'FormalResearch.Racah.f3even_swap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_swap

/-- info: 'FormalResearch.Racah.f3even_negMσ_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_negMσ_zpow

/-- info: 'FormalResearch.Racah.f3even_swap_zpow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms f3even_swap_zpow

/-- info: 'FormalResearch.Racah.Gc3_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Gc3_half

/-- info: 'FormalResearch.Racah.Phi3j_half_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_half_exact

/-- info: 'FormalResearch.Racah.Phi3j_half_expansion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_half_expansion

/-- info: 'FormalResearch.Racah.Phi3j_moving_point' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi3j_moving_point

end FormalResearch.Racah

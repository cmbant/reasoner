module

public import FormalResearch.Special.AiryKernelOpBounds

/-!
# The Airy kernel operator on `(u, ∞)`: Hilbert–Schmidt, trace, positivity

Let `K_u f(x) = ∫_u^∞ K(x,y) f(y) dy` on `L²(u,∞)`.  Mathlib has no theory of trace-class or Hilbert–Schmidt
integral operators, so this module proves the *integral* statements behind the operator-theoretic ones and
nothing more:

* **Hilbert–Schmidt**: `airyKer²` is integrable on `(u,∞)²` (`integrable_airyKer_sq`), and
  `∫∫_{(u,∞)²} K(x,y)² dx dy ≤ N_Ai(u)²` (`integral_airyKer_sq_le`), from `K(x,y)² ≤ K(x,x)K(y,y)`.
* **Trace**: `K(s,s)` is integrable on `(u,∞)` with `∫_u^∞ K(s,s) ds = N_Ai(u) < ∞`
  (`integrableOn_Ioi_airyKer_diag`, `integral_Ioi_airyKer_diag` in `AiryKernelOpBounds`).
* **Self-adjointness** is the symmetry `airyKer_comm`.
* **Positive semidefiniteness**: for `g` measurable, bounded, supported in a compact interval,
  `∫∫ g(x) K(x,y) g(y) dx dy = ∫_0^∞ (∫ g(x) Ai(x+t) dx)² dt ≥ 0`
  (`airyKer_quadForm_eq`, `airyKer_quadForm_nonneg`, from `K(x,y) = ∫_0^∞ Ai(x+t)Ai(y+t)dt` and Fubini); in
  particular for `f` continuous with compact support, restricted to `(u,∞)`
  (`airyKer_quadForm_nonneg_Ioi`).

The bound `∫(K_u f)² ≤ N_Ai(u)² ∫f²` and positivity on all of `L²` are in `AiryKernelOpL2` (function level).

**Not formalised:** `K_u` as an element of `Lp ℝ 2 →L[ℝ] Lp ℝ 2`, the factorisation `K_u = A_u A_u^*` as operators, the spectral statements (trace-class norm
equal to the trace, eigenvalue decay, Fredholm determinant).  The Hilbert–Schmidt-tail form of the decay of the factor kernel `Ai(s+ζ)`
(rank-`m` separated approximations with error `≤ C e^{-cm}`) is proved in `AiryRankDecay`; the passage to singular values and eigenvalues is not.
-/

@[expose] public section

open Filter Topology MeasureTheory Set

namespace FormalResearch.Special

/-! ### Hilbert–Schmidt and trace -/

lemma abs_airyKer_le (x y : ℝ) : |airyKer x y| ≤ (airyKer x x + airyKer y y) / 2 := by
  refine abs_le_of_sq_le_sq ?_ (by linarith [airyKer_diag_nonneg x, airyKer_diag_nonneg y])
  nlinarith [airyKer_sq_le x y, sq_nonneg (airyKer x x - airyKer y y)]

/-- **Hilbert–Schmidt**: `K(x,y)²` is integrable on `(u,∞)²`. -/
theorem integrable_airyKer_sq (u : ℝ) :
    Integrable (fun p : ℝ × ℝ => airyKer p.1 p.2 ^ 2)
      ((volume.restrict (Ioi u)).prod (volume.restrict (Ioi u))) := by
  have hd := integrableOn_Ioi_airyKer_diag u
  refine Integrable.mono' (hd.mul_prod hd) ?_ ?_
  · exact (measurable_airyKer.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact airyKer_sq_le p.1 p.2

/-- **Hilbert–Schmidt norm bound**: `∫∫_{(u,∞)²} K(x,y)² dx dy ≤ N_Ai(u)²`, with
`N_Ai(u) = (2u²Ai² - 2uAi'² - AiAi')/3 = Tr K_u`. -/
theorem integral_airyKer_sq_le (u : ℝ) :
    ∫ p : ℝ × ℝ, airyKer p.1 p.2 ^ 2
        ∂((volume.restrict (Ioi u)).prod (volume.restrict (Ioi u))) ≤ airyN u ^ 2 := by
  have hd := integrableOn_Ioi_airyKer_diag u
  have h := integral_mono (integrable_airyKer_sq u) (hd.mul_prod hd)
    (fun p => airyKer_sq_le p.1 p.2)
  refine h.trans (le_of_eq ?_)
  have e := integral_prod_mul (μ := volume.restrict (Ioi u)) (ν := volume.restrict (Ioi u))
    (fun s => airyKer s s) (fun s => airyKer s s)
  refine e.trans ?_
  rw [integral_Ioi_airyKer_diag, sq]

/-- Iterated form of the Hilbert–Schmidt bound. -/
theorem integral_integral_airyKer_sq_le (u : ℝ) :
    ∫ x in Ioi u, ∫ y in Ioi u, airyKer x y ^ 2 ≤ airyN u ^ 2 := by
  have := integral_airyKer_sq_le u
  rwa [integral_prod _ (integrable_airyKer_sq u)] at this

/-! ### Positivity of the quadratic form -/

section Quad

variable {g : ℝ → ℝ} {M a b : ℝ}

/-- The integrand of the Gram factorisation, `g(x)Ai(x+t) · g(y)Ai(y+t)` at `p = (x,y)`. -/
private noncomputable def psi (g : ℝ → ℝ) (p : ℝ × ℝ) (t : ℝ) : ℝ :=
  (g p.1 * airyAi (p.1 + t)) * (g p.2 * airyAi (p.2 + t))

private lemma psi_eq (g : ℝ → ℝ) (p : ℝ × ℝ) (t : ℝ) :
    psi g p t = (g p.1 * g p.2) * (airyAi (p.1 + t) * airyAi (p.2 + t)) := by
  unfold psi; ring

private lemma integrableOn_psi (g : ℝ → ℝ) (p : ℝ × ℝ) :
    IntegrableOn (fun t => psi g p t) (Ioi 0) := by
  simp_rw [psi_eq]
  exact (integrableOn_airyAi_shift_mul p.1 p.2).const_mul _

private lemma integral_psi (g : ℝ → ℝ) (p : ℝ × ℝ) :
    ∫ t in Ioi 0, psi g p t = g p.1 * airyKer p.1 p.2 * g p.2 := by
  simp_rw [psi_eq]
  rw [integral_const_mul, ← airyKer_eq_integral]; ring

private lemma measurable_psi (hg : Measurable g) :
    Measurable (Function.uncurry (psi g)) := by
  have h1 : Measurable (fun q : (ℝ × ℝ) × ℝ => g q.1.1 * airyAi (q.1.1 + q.2)) :=
    (hg.comp (measurable_fst.comp measurable_fst)).mul
      (continuous_airyAi.measurable.comp
        ((measurable_fst.comp measurable_fst).add measurable_snd))
  have h2 : Measurable (fun q : (ℝ × ℝ) × ℝ => g q.1.2 * airyAi (q.1.2 + q.2)) :=
    (hg.comp (measurable_snd.comp measurable_fst)).mul
      (continuous_airyAi.measurable.comp
        ((measurable_snd.comp measurable_fst).add measurable_snd))
  exact h1.mul h2

private lemma integral_norm_psi_le (hM : ∀ x, |g x| ≤ M) (hs : ∀ x, x ∉ Icc a b → g x = 0)
    (p : ℝ × ℝ) :
    ∫ t in Ioi 0, ‖psi g p t‖ ≤
      (Icc a b ×ˢ Icc a b).indicator (fun _ => M ^ 2 * airyKer a a) p := by
  by_cases hp : p ∈ Icc a b ×ˢ Icc a b
  · rw [indicator_of_mem hp]
    obtain ⟨h1, h2⟩ := hp
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
    have hK1 : airyKer p.1 p.1 ≤ airyKer a a := antitone_airyKer_diag h1.1
    have hK2 : airyKer p.2 p.2 ≤ airyKer a a := antitone_airyKer_diag h2.1
    have hgg : |g p.1 * g p.2| ≤ M ^ 2 := by
      rw [abs_mul, sq]
      exact mul_le_mul (hM _) (hM _) (abs_nonneg _) hM0
    have hint := (integrableOn_airyAi_shift_sq p.1).add (integrableOn_airyAi_shift_sq p.2)
    have hle : ∀ t ∈ Ioi (0 : ℝ), ‖psi g p t‖ ≤
        |g p.1 * g p.2| * ((airyAi (p.1 + t) ^ 2 + airyAi (p.2 + t) ^ 2) / 2) := by
      intro t _
      rw [psi_eq, Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (airyAi (p.1 + t) + airyAi (p.2 + t)),
        sq_nonneg (airyAi (p.1 + t) - airyAi (p.2 + t))]
    have hint2 : IntegrableOn (fun t => |g p.1 * g p.2| *
        ((airyAi (p.1 + t) ^ 2 + airyAi (p.2 + t) ^ 2) / 2)) (Ioi 0) :=
      (hint.div_const 2).const_mul _
    calc ∫ t in Ioi 0, ‖psi g p t‖
        ≤ ∫ t in Ioi 0, |g p.1 * g p.2| * ((airyAi (p.1 + t) ^ 2 + airyAi (p.2 + t) ^ 2) / 2) :=
          setIntegral_mono_on (integrableOn_psi g p).norm hint2 measurableSet_Ioi hle
      _ = |g p.1 * g p.2| * ((airyKer p.1 p.1 + airyKer p.2 p.2) / 2) := by
          rw [integral_const_mul, integral_div, integral_add (integrableOn_airyAi_shift_sq p.1)
            (integrableOn_airyAi_shift_sq p.2), ← airyKer_self_eq_integral,
            ← airyKer_self_eq_integral]
      _ ≤ M ^ 2 * airyKer a a := by
          have hKa := airyKer_diag_nonneg a
          have hsum : (airyKer p.1 p.1 + airyKer p.2 p.2) / 2 ≤ airyKer a a := by linarith
          have hnn : 0 ≤ (airyKer p.1 p.1 + airyKer p.2 p.2) / 2 := by
            linarith [airyKer_diag_nonneg p.1, airyKer_diag_nonneg p.2]
          exact mul_le_mul hgg hsum hnn (sq_nonneg M)
  · rw [indicator_of_notMem hp]
    have : g p.1 = 0 ∨ g p.2 = 0 := by
      by_contra hc
      push Not at hc
      exact hp ⟨by_contra fun h => hc.1 (hs _ h), by_contra fun h => hc.2 (hs _ h)⟩
    have h0 : ∀ t, psi g p t = 0 := by
      intro t; unfold psi; rcases this with h | h <;> simp [h]
    simp [h0]

private lemma integrable_psi (hg : Measurable g) (hM : ∀ x, |g x| ≤ M)
    (hs : ∀ x, x ∉ Icc a b → g x = 0) :
    Integrable (Function.uncurry (psi g))
      ((volume.prod volume : Measure (ℝ × ℝ)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  rw [integrable_prod_iff (measurable_psi hg).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun p => integrableOn_psi g p, ?_⟩
  have hbox : Integrable ((Icc a b ×ˢ Icc a b).indicator (fun _ => M ^ 2 * airyKer a a))
      (volume.prod volume : Measure (ℝ × ℝ)) := by
    refine (integrable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr ?_
    refine integrableOn_const ?_
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
  refine Integrable.mono' hbox ?_ ?_
  · exact ((measurable_psi hg).norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun p => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (setIntegral_nonneg measurableSet_Ioi
      fun _ _ => norm_nonneg _)]
    exact integral_norm_psi_le hM hs p

/-- **The Airy kernel form is a Gram form**:
`∫∫ g(x) K(x,y) g(y) dx dy = ∫_0^∞ (∫ g(x) Ai(x+t) dx)² dt` for `g` measurable, bounded and supported in a
compact interval. -/
theorem airyKer_quadForm_eq (hg : Measurable g) (hM : ∀ x, |g x| ≤ M)
    (hs : ∀ x, x ∉ Icc a b → g x = 0) :
    ∫ x, ∫ y, g x * airyKer x y * g y =
      ∫ t in Ioi 0, (∫ x, g x * airyAi (x + t)) ^ 2 := by
  have hi := integrable_psi hg hM hs
  have hswap := integral_integral_swap (f := psi g) (μ := (volume.prod volume : Measure (ℝ × ℝ)))
    (ν := volume.restrict (Ioi (0 : ℝ))) hi
  have hL : ∀ p : ℝ × ℝ, ∫ t in Ioi 0, psi g p t = g p.1 * airyKer p.1 p.2 * g p.2 :=
    integral_psi g
  have hR : ∀ t : ℝ, ∫ p : ℝ × ℝ, psi g p t ∂(volume.prod volume) =
      (∫ x, g x * airyAi (x + t)) ^ 2 := by
    intro t
    have := integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (fun x => g x * airyAi (x + t)) (fun x => g x * airyAi (x + t))
    rw [sq]; exact this
  simp_rw [hL, hR] at hswap
  rw [← hswap]
  have hint : Integrable (fun p : ℝ × ℝ => g p.1 * airyKer p.1 p.2 * g p.2)
      (volume.prod volume) := by
    have := hi.integral_prod_left
    simpa [hL] using this
  have := integral_prod (fun p : ℝ × ℝ => g p.1 * airyKer p.1 p.2 * g p.2) hint
  exact this.symm

/-- **Positive semidefiniteness of `K`**: `∫∫ g(x) K(x,y) g(y) dx dy ≥ 0` for `g` measurable, bounded and
supported in a compact interval. -/
theorem airyKer_quadForm_nonneg (hg : Measurable g) (hM : ∀ x, |g x| ≤ M)
    (hs : ∀ x, x ∉ Icc a b → g x = 0) :
    0 ≤ ∫ x, ∫ y, g x * airyKer x y * g y := by
  rw [airyKer_quadForm_eq hg hM hs]
  exact setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _

end Quad

/-- **Positive semidefiniteness of `K_u` on continuous compactly supported functions**:
`∫_u^∞ ∫_u^∞ f(x) K(x,y) f(y) dy dx ≥ 0`. -/
theorem airyKer_quadForm_nonneg_Ioi {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (u : ℝ) : 0 ≤ ∫ x in Ioi u, ∫ y in Ioi u, f x * airyKer x y * f y := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨b, hb⟩ := hc.isCompact.bddAbove
  obtain ⟨a, ha⟩ := hc.isCompact.bddBelow
  set g := (Ioi u).indicator f with hg
  have hgm : Measurable g := hf.measurable.indicator measurableSet_Ioi
  have hgM : ∀ x, |g x| ≤ M := by
    intro x
    by_cases hx : x ∈ Ioi u
    · rw [hg, indicator_of_mem hx]; simpa using hM x
    · rw [hg, indicator_of_notMem hx]; simpa using (abs_nonneg (f x)).trans (by simpa using hM x)
  have hgs : ∀ x, x ∉ Icc a b → g x = 0 := by
    intro x hx
    by_cases hxu : x ∈ Ioi u
    · rw [hg, indicator_of_mem hxu]
      by_contra h
      exact hx ⟨ha (subset_tsupport f h), hb (subset_tsupport f h)⟩
    · rw [hg, indicator_of_notMem hxu]
  have h := airyKer_quadForm_nonneg hgm hgM hgs
  have e : ∀ x, ∫ y, g x * airyKer x y * g y =
      (Ioi u).indicator (fun x => ∫ y in Ioi u, f x * airyKer x y * f y) x := by
    intro x
    by_cases hx : x ∈ Ioi u
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Ioi]
      congr 1; funext y
      by_cases hy : y ∈ Ioi u
      · simp [hg, indicator_of_mem hx, indicator_of_mem hy]
      · simp [hg, indicator_of_notMem hy]
    · rw [indicator_of_notMem hx]; simp [hg, indicator_of_notMem hx]
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_indicator measurableSet_Ioi] at h
  exact h

/-- info: 'FormalResearch.Special.integral_airyKer_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.integral_airyKer_sq_le

/-- info: 'FormalResearch.Special.airyKer_quadForm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_quadForm_eq

/-- info: 'FormalResearch.Special.airyKer_quadForm_nonneg_Ioi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyKer_quadForm_nonneg_Ioi

end FormalResearch.Special

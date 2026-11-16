module

public import FormalResearch.Special.LangerPhi
public import FormalResearch.Special.LangerHadamard

/-!
# The Langer coordinate at a simple turning point

Module M3 of the discrete-to-Airy plan.  This is the "turning-point coefficient Taylor lemma" behind
Geronimo–Bruno–Van Assche Thm 3.8 as used in the hypotheses check of W1 `estimates.tex` (the passage
"`η²`, `η²/(t-t_*)` and `sinh²η/(t-t_*)` are `C³` across the turn") and P3 `weyl_midpoint_semiclassics_appendices.tex`
(`prop:airy2-amplitude`, `eq:general-airy-varpi-local`, eikonal `cosh(ζ^{1/2}ζ') = u`).

Setting: `u = (E - b)/(2a)` (`cosh η = u` on the forbidden side), `u(q*) = 1`, `u'(q*) > 0`.

* `LangerPhi.lean`: `langerPhi z = arcosh(1+z)²` (`z ≥ 0`), `-arccos(1+z)²` (`z < 0`) is the **analytic** inverse of
  the entire function `langerP w = cosh √w - 1 = ∑_{n≥1} wⁿ/(2n)!` (`analyticAt_langerPhi`), with
  `Φ'(0) = 2`, `Φ''(0) = -2/3`, `Φ'''(0) = 8/15` (series `2z - z²/3 + 4z³/45 - …`).
* `LangerHadamard.lean`: Hadamard's lemma for `C^k` functions (`contDiffAt_dslope`), via the parametric
  integral `∫₀¹ w(t) K(c + t(q-c)) dt` (`contDiffOn_hadInt`); not in Mathlib.
* This file: `F = Φ(u - 1)` is `C^{m+1}` (`contDiffAt_langerF`), and the Langer coordinate `ζ` with
  `ζ ζ'² = F` is `C^{m+1}` (`langerZetaOf_spec`, `langerZeta_spec`), `ζ'(q*) = (2u'(q*))^{1/3}`, `ζ' > 0`,
  `ζ/(q - q*)` is `C^m` and positive; `ζ = ±(3/2 ∫√|F|)^{2/3}` (`langerZetaOf_integral`); and
  `|ζ|/|u²-1|` (the fourth power of the positive amplitude `g = (4|ζ|/|D̄|)^{1/4}`, `D̄ = 4a²(1-u²)`) is `C^m`
  and positive (`langerAmpRatio_spec`, `langerAmp_of_coeff`).
  [`LangerJets.lean`: `F'' = 2u'' - (2/3)u'²`, `F''' = 2u''' - 2u'u'' + (8/15)u'³`.]

**Regularity proved (honest statement).**  `u ∈ C^{m+1}` near `q*` (`m ≥ 1`) gives `F = Φ(u-1) ∈ C^{m+1}` and
`ζ ∈ C^{m+1}` (for `u ∈ C⁴`, `ζ ∈ C⁴`; the papers only need `C³`), the positive quotient `ζ/(q-q*)` in `C^m`
and `|ζ|/|u²-1|` in `C^m`.  The loss of one derivative occurs only in the Hadamard quotients `G = F/(q-q*)`,
`M = ∫₀¹ √t √G(q*+t(q-q*)) dt`, while `ζ' = √G/(3M/2)^{1/3}` is `C^m` so that `ζ` itself is `C^{m+1}`.
Applying the theorems for every `m` gives `ζ ∈ C^∞` for `u ∈ C^∞`.  **Not proved:** analyticity of `ζ` for
analytic `u` (true, but the parametric-integral route used here does not give it; it would need an analytic
Hadamard quotient and an analytic parametric integral), uniformity of constants over the papers' compact
parameter families, and everything involving the discrete chain (modules M4-M6: `AiryParametrix*`, `AiryRecessive*`, `AiryWindow*`;
the amplitude relation `g²Aζ'Sh(ζζ'²) = 1` of `airyParametrix_defect` is not derived from this module).

**Numerical checks (mpmath, 30 digits; scratch only).**  (i) `Φ`-series coefficients `2, -1/3, 4/45, -1/35`
against `sympy`; (ii) `u = 1 + 0.7s + 0.3s² + 0.5s³`: `ζ'(0) = (2·0.7)^{1/3}` from the numerical integral
(`1.1186889` both sides, one-sided slopes agree), `ζ ζ'² = Φ(u-1)` at `s = ±0.1`, and `ζ/(u²-1) → (2u')^{-2/3}`;
(iii) the model chain of the plan (`a = 1`, `u = cosh√(F₁t)`): `ζ = F₁^{1/3} t` exactly, `Φ(u-1) = F₁ t`, and
`ζ/(u²-1) = F₁^{1/3} t / sinh²√(F₁t)` on both sides of `t = 0`.
-/

@[expose] public section

open Filter Topology Set MeasureTheory Metric

namespace FormalResearch.Special

lemma contDiffAt_succ_of_hasDerivAt {f D : ℝ → ℝ} {x : ℝ} {n : ℕ}
    (h : ∀ᶠ y in 𝓝 x, HasDerivAt f (D y) y) (hD : ContDiffAt ℝ n D x) :
    ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f x := by
  rw [Nat.cast_succ, contDiffAt_succ_iff_hasFDerivAt]
  refine ⟨fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (D y),
    ⟨_, h, fun y hy => hy.hasFDerivAt⟩, ?_⟩
  have : (fun y => ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (D y)) =
      fun y => D y • (1 : ℝ →L[ℝ] ℝ) := by
    funext y; ext; simp
  rw [this]
  exact hD.smul contDiffAt_const

/-- `∫₀¹ √t dt = 2/3`. -/
lemma integral_sqrt_zero_one : ∫ t in (0 : ℝ)..1, √t = 2 / 3 := by
  have : (fun t : ℝ => √t) = fun t => t ^ (1 / 2 : ℝ) := by
    funext t; rw [Real.sqrt_eq_rpow]
  rw [this, integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- The Euler-type identity `(3/2) M + (q-c) M' = K(q)` for `M = ∫₀¹ √t K(c + t(q-c)) dt`. -/
lemma hadInt_sqrt_ode {K : ℝ → ℝ} {c ρ q : ℝ} (hK : ContDiffOn ℝ 1 K (ball c ρ))
    (hq : q ∈ ball c ρ) :
    3 / 2 * hadInt (fun t => √t) K c q
      + (q - c) * hadInt (fun t => t * √t) (deriv K) c q = K q := by
  have hKc : ContinuousOn K (ball c ρ) := hK.continuousOn
  have hK' : ContinuousOn (deriv K) (ball c ρ) :=
    hK.continuousOn_deriv_of_isOpen isOpen_ball le_rfl
  have h1 : ContinuousOn (fun t => √t * K (c + t * (q - c))) (Icc 0 1) :=
    hadInt_cont_t Real.continuous_sqrt hKc hq
  have h2 : ContinuousOn (fun t => (t * √t) * deriv K (c + t * (q - c))) (Icc 0 1) :=
    hadInt_cont_t (continuous_id.mul Real.continuous_sqrt) hK' hq
  set φ : ℝ → ℝ := fun t => (t * √t) * K (c + t * (q - c)) with hφ
  set f' : ℝ → ℝ := fun t => 3 / 2 * (√t * K (c + t * (q - c)))
    + (q - c) * ((t * √t) * deriv K (c + t * (q - c))) with hf'
  have hφc : ContinuousOn φ (Icc 0 1) :=
    hadInt_cont_t (continuous_id.mul Real.continuous_sqrt) hKc hq
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt φ (f' t) (Ioi t) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1.ne'
    have hs : HasDerivAt (fun t : ℝ => t * √t) (3 / 2 * √t) t := by
      have := (hasDerivAt_id t).mul (Real.hasDerivAt_sqrt ht0)
      refine this.congr_deriv ?_
      have hpos : 0 < √t := Real.sqrt_pos.2 ht.1
      have hsq : √t * √t = t := Real.mul_self_sqrt ht.1.le
      show (1 : ℝ) * √t + t * (1 / (2 * √t)) = 3 / 2 * √t
      field_simp
      nlinarith [hsq]
    have hKd : DifferentiableAt ℝ K (c + t * (q - c)) :=
      (hK.differentiableOn one_ne_zero).differentiableAt
        (isOpen_ball.mem_nhds (hadInt_mem_ball hq (Ioo_subset_Icc_self ht)))
    have h1 : HasDerivAt (fun t : ℝ => c + t * (q - c)) (q - c) t := by
      simpa using ((hasDerivAt_id t).mul_const (q - c)).const_add c
    have hc := hKd.hasDerivAt.comp t h1
    have := hs.mul hc
    refine (this.congr_deriv ?_).hasDerivWithinAt
    simp only [hf', Function.comp_apply]
    ring
  have hfc : ContinuousOn f' (Icc 0 1) := (continuousOn_const.mul h1).add (continuousOn_const.mul h2)
  have hint : IntervalIntegrable f' volume 0 1 := hfc.intervalIntegrable_of_Icc zero_le_one
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le zero_le_one hφc hderiv hint
  have hi1 : IntervalIntegrable (fun t => √t * K (c + t * (q - c))) volume 0 1 :=
    h1.intervalIntegrable_of_Icc zero_le_one
  have hi2 : IntervalIntegrable (fun t => (t * √t) * deriv K (c + t * (q - c))) volume 0 1 :=
    h2.intervalIntegrable_of_Icc zero_le_one
  have hsplit : ∫ t in (0 : ℝ)..1, f' t = 3 / 2 * hadInt (fun t => √t) K c q
      + (q - c) * hadInt (fun t => t * √t) (deriv K) c q := by
    simp only [hf']
    rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  rw [← hsplit, key]
  simp [hφ]


/-- `M(c) = (2/3) K(c)`. -/
lemma hadInt_sqrt_self (K : ℝ → ℝ) (c : ℝ) :
    hadInt (fun t => √t) K c c = 2 / 3 * K c := by
  simp only [hadInt, sub_self, mul_zero, add_zero]
  rw [intervalIntegral.integral_mul_const, integral_sqrt_zero_one]

/-- Cube root helper: `a = x^(1/3)` satisfies `a^3 = x` for `x ≥ 0`. -/
lemma rpow_third_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ (1 / 3 : ℝ)) ^ 3 = x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- Local regularity package for the Langer construction. -/
lemma langer_local {F : ℝ → ℝ} {c : ℝ} {m : ℕ}
    (hF : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F c) (hF1 : 0 < deriv F c) :
    ∃ ρ > 0, ContDiffOn ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F (ball c ρ) ∧
      (∀ q ∈ ball c ρ, 0 < dslope F c q) ∧
      ContDiffOn ℝ m (dslope F c) (ball c ρ) ∧
      ContDiffOn ℝ m (fun s => √(dslope F c s)) (ball c ρ) ∧
      ContDiffOn ℝ m (hadInt (fun t => √t) (fun s => √(dslope F c s)) c) (ball c ρ) ∧
      (∀ q ∈ ball c ρ, 0 < hadInt (fun t => √t) (fun s => √(dslope F c s)) c q) := by
  obtain ⟨ρ0, hρ0, hFb⟩ := exists_ball_contDiffOn hF
  have hG : ContDiffOn ℝ m (dslope F c) (ball c ρ0) := contDiffOn_dslope m hFb
  have hGc : ContinuousAt (dslope F c) c :=
    hG.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ0))
  have hGc0 : dslope F c c = deriv F c := dslope_same _ _
  have hev : ∀ᶠ q in 𝓝 c, 0 < dslope F c q ∧ q ∈ ball c ρ0 :=
    (hGc.eventually (lt_mem_nhds (by rw [hGc0]; exact hF1))).and
      (isOpen_ball.mem_nhds (mem_ball_self hρ0))
  obtain ⟨ρ1, hρ1, hb1⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hsub : ball c ρ1 ⊆ ball c ρ0 := fun q hq => (hb1 q hq).2
  have hK : ContDiffOn ℝ m (fun s => √(dslope F c s)) (ball c ρ1) :=
    (hG.mono hsub).sqrt fun q hq => (hb1 q hq).1.ne'
  have hM : ContDiffOn ℝ m (hadInt (fun t => √t) (fun s => √(dslope F c s)) c) (ball c ρ1) :=
    contDiffOn_hadInt m _ _ Real.continuous_sqrt hK
  have hMc : ContinuousAt (hadInt (fun t => √t) (fun s => √(dslope F c s)) c) c :=
    hM.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hρ1))
  have hMc0 : 0 < hadInt (fun t => √t) (fun s => √(dslope F c s)) c c := by
    rw [hadInt_sqrt_self]
    have : 0 < dslope F c c := (hb1 c (mem_ball_self hρ1)).1
    positivity
  obtain ⟨ρ2, hρ2, hb2⟩ := Metric.eventually_nhds_iff_ball.1
    (hMc.eventually (lt_mem_nhds hMc0))
  have hρ21 : ∀ q ∈ ball c (min ρ1 ρ2), q ∈ ball c ρ1 ∧ q ∈ ball c ρ2 := fun q hq =>
    ⟨ball_subset_ball (min_le_left _ _) hq, ball_subset_ball (min_le_right _ _) hq⟩
  refine ⟨min ρ1 ρ2, lt_min hρ1 hρ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hFb.mono (fun q hq => hsub (hρ21 q hq).1)
  · exact fun q hq => (hb1 q (hρ21 q hq).1).1
  · exact hG.mono (fun q hq => hsub (hρ21 q hq).1)
  · exact hK.mono (fun q hq => (hρ21 q hq).1)
  · exact hM.mono (fun q hq => (hρ21 q hq).1)
  · exact fun q hq => hb2 q (hρ21 q hq).2


/-- `a(q) = (3M(q)/2)^{1/3}`, where `M(q) = ∫₀¹ √t √(G(c + t(q-c))) dt`, `G = dslope F c`. -/
noncomputable def langerA (F : ℝ → ℝ) (c q : ℝ) : ℝ :=
  (3 / 2 * hadInt (fun t => √t) (fun s => √(dslope F c s)) c q) ^ (1 / 3 : ℝ)

/-- The Langer coordinate of a function `F` with a simple zero at `c`: `ζ = (q-c) a²`,
which is `(3/2 ∫_c^q √|F|)^{2/3}` with sign (see `langerZetaOf_spec`).  It takes junk values away from `c`:
all statements about it are local, on a ball about `c` where `dslope F c > 0`. -/
noncomputable def langerZetaOf (F : ℝ → ℝ) (c q : ℝ) : ℝ := (q - c) * langerA F c q ^ 2

lemma hasDerivAt_langer_aux {K : ℝ → ℝ} {c ρ q : ℝ} (hK : ContDiffOn ℝ 1 K (ball c ρ))
    (hq : q ∈ ball c ρ) (hM : 0 < hadInt (fun t => √t) K c q) :
    HasDerivAt
      (fun y => (y - c) * ((3 / 2 * hadInt (fun t => √t) K c y) ^ (1 / 3 : ℝ)) ^ 2)
      (K q / (3 / 2 * hadInt (fun t => √t) K c q) ^ (1 / 3 : ℝ)) q := by
  set M' := hadInt (fun t => t * √t) (deriv K) c q with hM'
  have hMd : HasDerivAt (hadInt (fun t => √t) K c) M' q :=
    hasDerivAt_hadInt Real.continuous_sqrt hK hq
  have ode := hadInt_sqrt_ode hK hq
  set M := hadInt (fun t => √t) K c q with hMdef
  have hx : 0 < 3 / 2 * M := by positivity
  set x := 3 / 2 * M with hxdef
  set a := x ^ (1 / 3 : ℝ) with hadef
  have ha3 : a ^ 3 = x := rpow_third_cube hx.le
  have ha0 : 0 < a := Real.rpow_pos_of_pos hx _
  have hxd : HasDerivAt (fun y => 3 / 2 * hadInt (fun t => √t) K c y) (3 / 2 * M') q :=
    hMd.const_mul _
  have had := hxd.rpow_const (p := 1 / 3) (Or.inl hx.ne')
  have hpow : x ^ (1 / 3 - 1 : ℝ) = a / x := by
    rw [Real.rpow_sub hx, Real.rpow_one]
  rw [hpow] at had
  have hζ := ((hasDerivAt_id q).sub_const c).mul (had.pow 2)
  refine hζ.congr_deriv ?_
  have e : (q - c) * M' = K q - a ^ 3 := by rw [ha3]; linarith
  have hxa : x = a ^ 3 := ha3.symm
  show 1 * a ^ 2 + (q - c) * (((2 : ℕ) : ℝ) * a ^ (2 - 1) * (3 / 2 * M' * (1 / 3) * (a / x)))
    = K q / a
  rw [hxa]
  push_cast
  field_simp
  linear_combination e


lemma langerZetaOf_zero (F : ℝ → ℝ) (c : ℝ) : langerZetaOf F c c = 0 := by
  simp [langerZetaOf]

/-- **Regularity of the Langer coordinate at a simple turning point (generic `F`).**
Let `F ∈ C^{m+1}` near `c`, `F c = 0`, `F' c > 0`, `m ≥ 1`.  Then `ζ = langerZetaOf F c` is `C^{m+1}`,
`ζ c = 0`, `ζ' c = (F' c)^{1/3}`, and near `c`: `ζ' > 0`, `ζ ζ'² = F`, `ζ` has the sign of `q - c`;
moreover `ζ/(q - c) = dslope ζ c` is `C^m` and positive. -/
theorem langerZetaOf_spec {F : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hF : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F c) (hF0 : F c = 0) (hF1 : 0 < deriv F c) :
    ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (langerZetaOf F c) c ∧
    deriv (langerZetaOf F c) c = (deriv F c) ^ (1 / 3 : ℝ) ∧
    (∀ᶠ q in 𝓝 c, HasDerivAt (langerZetaOf F c) (deriv (langerZetaOf F c) q) q ∧
      0 < deriv (langerZetaOf F c) q ∧
      langerZetaOf F c q * deriv (langerZetaOf F c) q ^ 2 = F q ∧
      ((0 < langerZetaOf F c q ↔ c < q) ∧ (langerZetaOf F c q < 0 ↔ q < c))) ∧
    ContDiffAt ℝ m (dslope (langerZetaOf F c) c) c ∧
    (∀ᶠ q in 𝓝 c, 0 < dslope (langerZetaOf F c) c q) := by
  obtain ⟨ρ, hρ, hFb, hGpos, hG, hK, hM, hMpos⟩ := langer_local hF hF1
  set K : ℝ → ℝ := fun s => √(dslope F c s) with hKdef
  have hK1 : ContDiffOn ℝ 1 K (ball c ρ) :=
    hK.of_le (by exact_mod_cast hm)
  have hball : ball c ρ ∈ 𝓝 c := isOpen_ball.mem_nhds (mem_ball_self hρ)
  have hder : ∀ q ∈ ball c ρ, HasDerivAt (langerZetaOf F c) (K q / langerA F c q) q :=
    fun q hq => hasDerivAt_langer_aux hK1 hq (hMpos q hq)
  have hMc : ContDiffAt ℝ m (hadInt (fun t => √t) K c) c := hM.contDiffAt hball
  have hApos : ∀ q ∈ ball c ρ, 0 < langerA F c q := fun q hq =>
    Real.rpow_pos_of_pos (by have := hMpos q hq; positivity) _
  have hA : ContDiffAt ℝ m (langerA F c) c := by
    refine ContDiffAt.rpow_const_of_ne (contDiffAt_const.mul hMc) ?_
    have := hMpos c (mem_ball_self hρ)
    positivity
  have hD : ContDiffAt ℝ m (fun q => K q / langerA F c q) c :=
    (hK.contDiffAt hball).div hA (hApos c (mem_ball_self hρ)).ne'
  have hsmooth := contDiffAt_succ_of_hasDerivAt (f := langerZetaOf F c)
    (Filter.mem_of_superset hball (fun q hq => hder q hq)) hD
  -- value at c
  have hKc : K c = √(deriv F c) := by simp only [hKdef, dslope_same]
  have hMc0 : 3 / 2 * hadInt (fun t => √t) K c c = K c := by
    rw [hadInt_sqrt_self]; ring
  have hac3 : langerA F c c ^ 3 = K c := by
    rw [langerA, ← hMc0]
    exact rpow_third_cube (by have := hMpos c (mem_ball_self hρ); positivity)
  have hac_pos := hApos c (mem_ball_self hρ)
  have hDc : K c / langerA F c c = langerA F c c ^ 2 := by
    rw [← hac3]; field_simp
  have hgpow : langerA F c c ^ 2 = (deriv F c) ^ (1 / 3 : ℝ) := by
    have h1 : langerA F c c = (deriv F c) ^ (1 / 6 : ℝ) := by
      rw [langerA, hMc0, hKc, Real.sqrt_eq_rpow, ← Real.rpow_mul hF1.le]; norm_num
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hF1.le]; norm_num
  have hdc : deriv (langerZetaOf F c) c = (deriv F c) ^ (1 / 3 : ℝ) := by
    rw [(hder c (mem_ball_self hρ)).deriv, hDc, hgpow]
  refine ⟨hsmooth, hdc, ?_, ?_, ?_⟩
  · filter_upwards [hball] with q hq
    have hd := (hder q hq).deriv
    have hKq : 0 < K q := Real.sqrt_pos.2 (hGpos q hq)
    have hAq := hApos q hq
    refine ⟨hd ▸ hder q hq, by rw [hd]; positivity, ?_, ?_⟩
    · rw [hd]
      have hsq : K q ^ 2 = dslope F c q := Real.sq_sqrt (hGpos q hq).le
      have hsub := sub_smul_dslope F c q
      rw [smul_eq_mul, hF0, sub_zero] at hsub
      rw [← hsub, ← hsq, langerZetaOf]
      field_simp
    · have ha2 : 0 < langerA F c q ^ 2 := by positivity
      rw [langerZetaOf]
      refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hcq
        have : q - c ≤ 0 := by linarith [not_lt.1 hcq]
        nlinarith [mul_nonneg (neg_nonneg.2 this) ha2.le]
      · have : 0 < q - c := by linarith
        positivity
      · by_contra hcq
        have : 0 ≤ q - c := by linarith [not_lt.1 hcq]
        nlinarith [mul_nonneg this ha2.le]
      · exact mul_neg_of_neg_of_pos (by linarith) ha2
  · have hEq : dslope (langerZetaOf F c) c =ᶠ[𝓝 c] fun q => langerA F c q ^ 2 := by
      filter_upwards [hball] with q hq
      by_cases hqc : q = c
      · subst hqc
        rw [dslope_same, (hder q hq).deriv, hDc]
      · rw [dslope_of_ne _ hqc, slope_def_field, langerZetaOf_zero, sub_zero, langerZetaOf]
        have : q - c ≠ 0 := sub_ne_zero.2 hqc
        field_simp
    exact (hA.pow 2).congr_of_eventuallyEq hEq
  · have hEq : dslope (langerZetaOf F c) c =ᶠ[𝓝 c] fun q => langerA F c q ^ 2 := by
      filter_upwards [hball] with q hq
      by_cases hqc : q = c
      · subst hqc
        rw [dslope_same, (hder q hq).deriv, hDc]
      · rw [dslope_of_ne _ hqc, slope_def_field, langerZetaOf_zero, sub_zero, langerZetaOf]
        have : q - c ≠ 0 := sub_ne_zero.2 hqc
        field_simp
    filter_upwards [hEq, hball] with q h1 hq
    rw [h1]; have := hApos q hq; positivity


/-- **The defining relation of the Langer coordinate** (W1 est:279, P3 A:1152): near `c`,
`(2/3) ζ^{3/2} = ∫_c^q √F` on the forbidden side `q ≥ c` and `(2/3) (-ζ)^{3/2} = ∫_q^c √(-F)` on the
allowed side `q ≤ c` (so `ζ = ±(3/2 ∫ √|F|)^{2/3}`, i.e. `langerZetaOf` is the paper's `ζ`). -/
theorem langerZetaOf_integral {F : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hF : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) F c) (hF0 : F c = 0) (hF1 : 0 < deriv F c) :
    ∀ᶠ q in 𝓝 c,
      (c ≤ q → 2 / 3 * (langerZetaOf F c q) ^ (3 / 2 : ℝ) = ∫ s in c..q, √(F s)) ∧
      (q ≤ c → 2 / 3 * (-langerZetaOf F c q) ^ (3 / 2 : ℝ) = ∫ s in q..c, √(-F s)) := by
  obtain ⟨-, -, hev, -, -⟩ := langerZetaOf_spec hm hF hF0 hF1
  obtain ⟨ρ1, hρ1, hb1⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨ρ2, hρ2, hFb, -⟩ := langer_local hF hF1
  set ζ := langerZetaOf F c with hζdef
  have hFc : ContinuousOn F (ball c (min ρ1 ρ2)) :=
    (hFb.continuousOn).mono (ball_subset_ball (min_le_right _ _))
  have hbd : ∀ q ∈ ball c (min ρ1 ρ2), q ∈ ball c ρ1 :=
    fun q hq => ball_subset_ball (min_le_left _ _) hq
  have hseg : ∀ {q s : ℝ}, q ∈ ball c (min ρ1 ρ2) → s ∈ uIcc c q → s ∈ ball c (min ρ1 ρ2) := by
    intro q s hq hs
    rw [mem_ball, Real.dist_eq] at hq ⊢
    rcases le_total c q with h | h
    · rw [uIcc_of_le h] at hs
      rw [abs_of_nonneg (by linarith [hs.1] : 0 ≤ s - c)]
      rw [abs_of_nonneg (by linarith : 0 ≤ q - c)] at hq
      linarith [hs.2]
    · rw [uIcc_of_ge h] at hs
      rw [abs_of_nonpos (by linarith [hs.2] : s - c ≤ 0)]
      rw [abs_of_nonpos (by linarith : q - c ≤ 0)] at hq
      linarith [hs.1]
  have hζc : ContinuousOn ζ (ball c ρ1) := fun q hq =>
    (hb1 q hq).1.continuousAt.continuousWithinAt
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (lt_min hρ1 hρ2))] with q hq
  have hq1 := hbd q hq
  have hz0 : ζ c = 0 := langerZetaOf_zero F c
  have hzc : ∀ s ∈ ball c ρ1, ContinuousAt ζ s := fun s hs => (hb1 s hs).1.continuousAt
  constructor
  · intro hcq
    rcases hcq.eq_or_lt with h | h
    · subst h; simp [hz0]
    · have hsub : ∀ s ∈ Icc c q, s ∈ ball c (min ρ1 ρ2) := fun s hs =>
        hseg hq (by rw [uIcc_of_le h.le]; exact hs)
      have hderiv : ∀ s ∈ Ioo c q, HasDerivAt (fun s => 2 / 3 * ζ s ^ (3 / 2 : ℝ)) (√(F s)) s := by
        intro s hs
        have hsb := hbd s (hsub s (Ioo_subset_Icc_self hs))
        obtain ⟨hd, hpos, hrel, hsign⟩ := hb1 s hsb
        have hζs : 0 < ζ s := hsign.1.2 hs.1
        refine ((hd.rpow_const (p := 3 / 2) (Or.inl hζs.ne')).const_mul (2 / 3)).congr_deriv ?_
        rw [← hrel, Real.sqrt_mul hζs.le, Real.sqrt_sq hpos.le, Real.sqrt_eq_rpow]
        norm_num
        ring
      have hcont : ContinuousOn (fun s => 2 / 3 * ζ s ^ (3 / 2 : ℝ)) (Icc c q) := fun s hs =>
        (continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
          (hzc s (hbd s (hsub s hs))))).continuousWithinAt
      have hint : IntervalIntegrable (fun s => √(F s)) volume c q :=
        (Real.continuous_sqrt.comp_continuousOn (hFc.mono hsub)).intervalIntegrable_of_Icc h.le
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.le hcont hderiv hint, hz0]
      simp
  · intro hcq
    rcases hcq.eq_or_lt with h | h
    · subst h; simp [hz0]
    · have hsub : ∀ s ∈ Icc q c, s ∈ ball c (min ρ1 ρ2) := fun s hs =>
        hseg hq (by rw [uIcc_of_ge h.le]; exact hs)
      have hderiv : ∀ s ∈ Ioo q c, HasDerivAt (fun s => 2 / 3 * (-ζ s) ^ (3 / 2 : ℝ))
          (-√(-F s)) s := by
        intro s hs
        have hsb := hbd s (hsub s (Ioo_subset_Icc_self hs))
        obtain ⟨hd, hpos, hrel, hsign⟩ := hb1 s hsb
        have hζs : ζ s < 0 := hsign.2.2 hs.2
        have hneg : 0 < -ζ s := by linarith
        have hnd : HasDerivAt (fun s => -ζ s) (-deriv ζ s) s := hd.neg
        refine ((hnd.rpow_const (p := 3 / 2) (Or.inl hneg.ne')).const_mul (2 / 3)).congr_deriv ?_
        have hF' : -F s = (-ζ s) * deriv ζ s ^ 2 := by rw [← hrel]; ring
        rw [hF', Real.sqrt_mul hneg.le, Real.sqrt_sq hpos.le, Real.sqrt_eq_rpow]
        norm_num
        ring
      have hcont : ContinuousOn (fun s => 2 / 3 * (-ζ s) ^ (3 / 2 : ℝ)) (Icc q c) := fun s hs =>
        (continuousAt_const.mul ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).comp
          (hzc s (hbd s (hsub s hs))).neg)).continuousWithinAt
      have hint : IntervalIntegrable (fun s => -√(-F s)) volume q c :=
        (Real.continuous_sqrt.comp_continuousOn (hFc.mono hsub).neg).neg.intervalIntegrable_of_Icc h.le
      have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.le hcont hderiv hint
      rw [intervalIntegral.integral_neg, hz0] at key
      simp at key
      linarith

/-- The Langer function of the rank-turn data: `F = Φ(u - 1)` with `Φ = langerPhi`, i.e. `F = η²` where
`cosh η = u` (`η² = -θ²` where `cos θ = u`, on the allowed side). -/
noncomputable def langerF (u : ℝ → ℝ) (q : ℝ) : ℝ := langerPhi (u q - 1)

/-- The Langer coordinate `ζ` (zero at the turning point `c`, positive on the forbidden side `q > c`):
`ζ ζ'² = F`, equivalently `(2/3) sgn(ζ) |ζ|^{3/2} = ∫_c^q √|F|` (`langerZeta_integral`); meaningful only near `c`. -/
noncomputable def langerZeta (u : ℝ → ℝ) (c : ℝ) : ℝ → ℝ := langerZetaOf (langerF u) c

lemma contDiffAt_langerF {u : ℝ → ℝ} {c : ℝ} {n : ℕ} (hu : ContDiffAt ℝ n u c) (h1 : u c = 1) :
    ContDiffAt ℝ n (langerF u) c := by
  have hΦ : ContDiffAt ℝ n langerPhi (u c - 1) := by
    rw [h1, sub_self]; exact analyticAt_langerPhi.contDiffAt
  exact hΦ.comp c (hu.sub contDiffAt_const)

lemma langerF_self {u : ℝ → ℝ} {c : ℝ} (h1 : u c = 1) : langerF u c = 0 := by
  simp [langerF, h1, langerPhi_zero]

lemma deriv_langerF {u : ℝ → ℝ} {c : ℝ} (hu : DifferentiableAt ℝ u c) (h1 : u c = 1) :
    deriv (langerF u) c = 2 * deriv u c := by
  have hΦ : HasDerivAt langerPhi 2 (u c - 1) := by
    rw [h1, sub_self, ← deriv_langerPhi_zero]
    exact analyticAt_langerPhi.differentiableAt.hasDerivAt
  have := hΦ.comp c (hu.hasDerivAt.sub_const 1)
  show deriv (fun q => langerPhi (u q - 1)) c = _
  exact this.deriv.trans (by ring)

/-- **Turning-point theorem (P3 A:1152 / W1 est:279).**  Let `u ∈ C^{m+1}` near `q*` (`m ≥ 1`) with
`u q* = 1`, `u' q* > 0`.  Then `F = Φ(u - 1)` and the Langer coordinate `ζ` are `C^{m+1}`; `ζ(q*) = 0`,
`ζ'(q*) = (2 u'(q*))^{1/3}`; near `q*`, `ζ' > 0`, `ζ ζ'² = Φ(u - 1)` and `ζ` has the sign of `q - q*`;
`ζ/(q - q*)` (`dslope`) is `C^m` and positive. -/
theorem langerZeta_spec {u : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hu : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u c) (h1 : u c = 1) (h2 : 0 < deriv u c) :
    ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (langerZeta u c) c ∧
    deriv (langerZeta u c) c = (2 * deriv u c) ^ (1 / 3 : ℝ) ∧
    (∀ᶠ q in 𝓝 c, HasDerivAt (langerZeta u c) (deriv (langerZeta u c) q) q ∧
      0 < deriv (langerZeta u c) q ∧
      langerZeta u c q * deriv (langerZeta u c) q ^ 2 = langerPhi (u q - 1) ∧
      ((0 < langerZeta u c q ↔ c < q) ∧ (langerZeta u c q < 0 ↔ q < c))) ∧
    ContDiffAt ℝ m (dslope (langerZeta u c) c) c ∧
    (∀ᶠ q in 𝓝 c, 0 < dslope (langerZeta u c) c q) := by
  have hF := contDiffAt_langerF hu h1
  have hd := deriv_langerF (hu.differentiableAt (by simp)) h1
  have hF1 : 0 < deriv (langerF u) c := by rw [hd]; linarith
  have := langerZetaOf_spec hm hF (langerF_self h1) hF1
  rw [hd] at this
  exact this


lemma dslope_sq_sub_one {u : ℝ → ℝ} {c : ℝ} (hu : DifferentiableAt ℝ u c) (h1 : u c = 1) (q : ℝ) :
    dslope (fun s => u s ^ 2 - 1) c q = (u q + 1) * dslope u c q := by
  by_cases hqc : q = c
  · subst hqc
    have : HasDerivAt (fun s => u s ^ 2 - 1) (2 * u q * deriv u q) q := by
      simpa using (hu.hasDerivAt.pow 2).sub_const 1
    rw [dslope_same, dslope_same, this.deriv, h1]; ring
  · rw [dslope_of_ne _ hqc, dslope_of_ne _ hqc, slope_def_field, slope_def_field, h1]
    have : q - c ≠ 0 := sub_ne_zero.2 hqc
    field_simp
    ring

/-- `ζ(q)/(u(q)² - 1)` (the quantity `4|ζ|/|D̄| = |ζ|/(a² |u² - 1|)` under the fourth root defining the
amplitude `g`; `D̄ = 4a² - (E-b)² = -4a² sinh²η = 4 a² (1 - u²)`), extended across `q = c` via `dslope`. -/
noncomputable def langerAmpRatio (u : ℝ → ℝ) (c q : ℝ) : ℝ :=
  dslope (langerZeta u c) c q / dslope (fun s => u s ^ 2 - 1) c q

/-- **Positive amplitude is `C^m` (the paper's "`sinh²η/(t-t*)` is `C^3` and positive").**  With
`u ∈ C^{m+1}`, `u c = 1`, `u' c > 0`: `sinh² η = u² - 1` (exactly; `η = arcosh u`, resp. `i arccos u`), and
`ζ/(u² - 1)` is `C^m`, positive near `c`, equal to `|ζ|/|u²-1|` for `q ≠ c`, with value `(2u'(c))^{-2/3}`
at `c`.  Consequently `g = (4|ζ|/|D̄|)^{1/4} = (ratio / a²)^{1/4}` is `C^m` and positive for any positive
`C^m` coefficient `a` (`langerAmp_of_coeff`). -/
theorem langerAmpRatio_spec {u : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hu : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u c) (h1 : u c = 1) (h2 : 0 < deriv u c) :
    ContDiffAt ℝ m (langerAmpRatio u c) c ∧ (∀ᶠ q in 𝓝 c, 0 < langerAmpRatio u c q) ∧
    langerAmpRatio u c c = (2 * deriv u c) ^ (-(2 / 3) : ℝ) ∧
    (∀ᶠ q in 𝓝 c, q ≠ c → langerAmpRatio u c q = |langerZeta u c q| / |u q ^ 2 - 1|) := by
  obtain ⟨hζ, hζ', hζev, hH, hHpos⟩ := langerZeta_spec hm hu h1 h2
  have hud : DifferentiableAt ℝ u c := hu.differentiableAt (by simp)
  have hum : ContDiffAt ℝ m u c := hu.of_le (by exact_mod_cast Nat.le_succ m)
  have hdu : ContDiffAt ℝ m (dslope u c) c := contDiffAt_dslope m hu
  have hden : dslope (fun s => u s ^ 2 - 1) c = fun q => (u q + 1) * dslope u c q :=
    funext (dslope_sq_sub_one hud h1)
  have hdenC : ContDiffAt ℝ m (dslope (fun s => u s ^ 2 - 1) c) c := by
    rw [hden]; exact (hum.add contDiffAt_const).mul hdu
  have hduc : dslope u c c = deriv u c := dslope_same _ _
  have hdupos : ∀ᶠ q in 𝓝 c, 0 < dslope u c q :=
    hdu.continuousAt.eventually (lt_mem_nhds (by rw [hduc]; exact h2))
  have hup : ∀ᶠ q in 𝓝 c, 0 < u q + 1 := by
    have := hum.continuousAt.eventually (lt_mem_nhds (show (0 : ℝ) - 1 < u c by rw [h1]; norm_num))
    filter_upwards [this] with q hq; linarith
  have hdenpos : ∀ᶠ q in 𝓝 c, 0 < dslope (fun s => u s ^ 2 - 1) c q := by
    filter_upwards [hdupos, hup] with q h1 h2
    rw [hden]; exact mul_pos h2 h1
  refine ⟨hH.div hdenC ?_, ?_, ?_, ?_⟩
  · rw [hden]; simp only [h1, hduc]; nlinarith
  · filter_upwards [hHpos, hdenpos] with q h1 h2
    exact div_pos h1 h2
  · have hden_c : dslope (fun s => u s ^ 2 - 1) c c = 2 * deriv u c := by
      rw [hden]; simp only [h1, hduc]; ring
    rw [langerAmpRatio, hden_c, dslope_same, hζ']
    have hx : 0 < 2 * deriv u c := by linarith
    have : (2 * deriv u c) ^ (-(2 / 3) : ℝ) = (2 * deriv u c) ^ (1 / 3 - 1 : ℝ) := by norm_num
    rw [this, Real.rpow_sub hx, Real.rpow_one]
  · filter_upwards [(hHpos.and hdenpos)] with q ⟨hq1, hq2⟩ hqc
    have hq : 0 < langerAmpRatio u c q := div_pos hq1 hq2
    have hform : langerAmpRatio u c q = langerZeta u c q / (u q ^ 2 - 1) := by
      simp only [langerAmpRatio]
      have hz : langerZeta u c c = 0 := langerZetaOf_zero _ _
      rw [dslope_of_ne _ hqc, dslope_of_ne _ hqc, slope_def_field, slope_def_field, hz, h1]
      have : q - c ≠ 0 := sub_ne_zero.2 hqc
      field_simp
      ring
    rw [hform] at hq ⊢
    rw [← abs_div, abs_of_pos hq]

/-- The amplitude `g = (4|ζ|/|D̄|)^{1/4}`, `D̄ = 4a² - (E - b)² = 4a²(1 - u²)` (`E - b = 2au`), is `C^m` and
positive across the turning point, for a positive `C^m` coefficient `a`. -/
theorem langerAmp_of_coeff {u a : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hu : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u c) (h1 : u c = 1) (h2 : 0 < deriv u c)
    (ha : ContDiffAt ℝ m a c) (ha0 : 0 < a c) :
    ContDiffAt ℝ m (fun q => (langerAmpRatio u c q / a q ^ 2) ^ (1 / 4 : ℝ)) c ∧
    (∀ᶠ q in 𝓝 c, 0 < (langerAmpRatio u c q / a q ^ 2) ^ (1 / 4 : ℝ)) ∧
    (∀ᶠ q in 𝓝 c, q ≠ c → ((langerAmpRatio u c q / a q ^ 2) ^ (1 / 4 : ℝ)) ^ 4 =
      4 * |langerZeta u c q| / |4 * a q ^ 2 * (1 - u q ^ 2)|) := by
  obtain ⟨hC, hpos, hval, habs⟩ := langerAmpRatio_spec hm hu h1 h2
  have hapos : ∀ᶠ q in 𝓝 c, 0 < a q := ha.continuousAt.eventually (lt_mem_nhds ha0)
  refine ⟨?_, ?_, ?_⟩
  · refine ContDiffAt.rpow_const_of_ne (hC.div (ha.pow 2) (by positivity)) ?_
    have : 0 < langerAmpRatio u c c := by rw [hval]; exact Real.rpow_pos_of_pos (by linarith) _
    exact (div_pos this (by positivity)).ne'
  · filter_upwards [hpos, hapos] with q h1 h2
    exact Real.rpow_pos_of_pos (div_pos h1 (by positivity)) _
  · filter_upwards [hpos, hapos, habs] with q hq haq hab hqc
    have hr := hab hqc
    have hdiv : 0 < langerAmpRatio u c q / a q ^ 2 := div_pos hq (by positivity)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdiv.le]
    norm_num
    have hne : |u q ^ 2 - 1| ≠ 0 := by
      intro h; rw [hr, h, div_zero] at hq; exact lt_irrefl _ hq
    rw [hr, abs_sub_comm 1 (u q ^ 2)]
    have := haq.ne'
    field_simp


/-- **The Langer coordinate of the rank-turn data** (`F = Φ(u-1)`): `(2/3) ζ^{3/2} = ∫_c^q √F` for `q ≥ c`
and `(2/3) (-ζ)^{3/2} = ∫_q^c √(-F)` for `q ≤ c`, i.e. `ζ = ±(3/2 ∫ η)^{2/3}` with `η² = F` (W1 est:277-278). -/
theorem langerZeta_integral {u : ℝ → ℝ} {c : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hu : ContDiffAt ℝ ((m + 1 : ℕ) : WithTop ℕ∞) u c) (h1 : u c = 1) (h2 : 0 < deriv u c) :
    ∀ᶠ q in 𝓝 c,
      (c ≤ q → 2 / 3 * (langerZeta u c q) ^ (3 / 2 : ℝ) = ∫ s in c..q, √(langerPhi (u s - 1))) ∧
      (q ≤ c → 2 / 3 * (-langerZeta u c q) ^ (3 / 2 : ℝ) = ∫ s in q..c, √(-langerPhi (u s - 1))) := by
  have hF := contDiffAt_langerF hu h1
  have hd := deriv_langerF (hu.differentiableAt (by simp)) h1
  have hF1 : 0 < deriv (langerF u) c := by rw [hd]; linarith
  exact langerZetaOf_integral hm hF (langerF_self h1) hF1

/-- info: 'FormalResearch.Special.langerZetaOf_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerZetaOf_spec

/-- info: 'FormalResearch.Special.langerZetaOf_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerZetaOf_integral

/-- info: 'FormalResearch.Special.langerZeta_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerZeta_spec

/-- info: 'FormalResearch.Special.langerZeta_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerZeta_integral

/-- info: 'FormalResearch.Special.langerAmpRatio_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerAmpRatio_spec

/-- info: 'FormalResearch.Special.langerAmp_of_coeff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.langerAmp_of_coeff

end FormalResearch.Special

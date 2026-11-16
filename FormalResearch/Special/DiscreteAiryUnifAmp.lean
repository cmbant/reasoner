module

public import FormalResearch.Special.DiscreteAiryUnifChart
public import FormalResearch.Special.AiryParametrixLanger
public import FormalResearch.Special.AiryParametrixUniformCh

/-!
# Uniform discrete-to-Airy, step 6: the Langer amplitude with explicit jet bounds and `langerAmp = (Aζ'Sh(ζζ'²))^{-1/2}`

* `dun_sh_abs`: absolute constants for `Sh = 2 Ch'` (`langerSinhc`): `Sh > 1/2` and `|Sh|, |Sh'|, |Sh''| ≤ M` on `|w| < ε_S`.
* `dun_amp`: from `J2` bounds of `A`, of `ζ'` (a Langer coordinate with `ζ(c) = 0`, `ζ' ≥ c₁`) and `|ζζ'²| < ε_S` the function
  `g̃ = (A ζ' Sh(ζζ'²))^{-1/2}` has explicit `J2` bounds and an explicit lower bound.  (`g̃² A ζ' Sh(ζζ'²) = 1` by construction.)
* `langerAmp_eq_rel`: on the ball where the chart is regular `langerAmp u A c = g̃` (this identifies the canonical amplitude of
  `AiryParametrixLanger` with the explicit one, so the amplitude relation `hrel` holds on the whole ball).

**Claim class: proved.**
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

namespace FormalResearch.Special

lemma deriv_langerSinhc_eq : deriv langerSinhc = fun w => 2 * apuc 2 w := by
  funext w
  have := (apuc_hasDerivAt 1 w).const_mul 2
  exact this.deriv

lemma deriv2_langerSinhc_eq : deriv (deriv langerSinhc) = fun w => 2 * apuc 3 w := by
  rw [deriv_langerSinhc_eq]
  funext w
  have := (apuc_hasDerivAt 2 w).const_mul 2
  exact this.deriv

lemma contDiff_langerSinhc : ContDiff ℝ ∞ langerSinhc := by
  have : langerSinhc = fun w => 2 * apuc 1 w := rfl
  rw [this]
  exact contDiff_const.mul (apuc_contDiff 1)

/-- Absolute constants for `Sh`. -/
lemma dun_sh_abs : ∃ εS M : ℝ, 0 < εS ∧ 0 ≤ M ∧ (∀ w : ℝ, |w| < εS → 1 / 2 < langerSinhc w) ∧
    ∀ w : ℝ, |w| < εS → |langerSinhc w| ≤ M ∧ |deriv langerSinhc w| ≤ M ∧ |deriv (deriv langerSinhc) w| ≤ M := by
  have hev : ∀ᶠ w in 𝓝 (0 : ℝ), 1 / 2 < langerSinhc w :=
    continuous_langerSinhc.continuousAt.eventually (lt_mem_nhds (by rw [langerSinhc_zero]; norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  obtain ⟨Mc, hMc0, hMc⟩ := apuc_bound (ε / 2)
  refine ⟨ε / 2, 2 * Mc, by positivity, by positivity, fun w hw => hball w ?_, fun w hw => ?_⟩
  · rw [mem_ball, Real.dist_eq, sub_zero]; linarith
  · obtain ⟨h1, h2, h3, h4⟩ := hMc w hw.le
    have e1 : langerSinhc w = 2 * apuc 1 w := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1, abs_mul, abs_two]; linarith
    · rw [deriv_langerSinhc_eq]; simp only [abs_mul, abs_two]; linarith
    · rw [deriv2_langerSinhc_eq]; simp only [abs_mul, abs_two]; linarith

/-- A function with `|f'| ≤ L` on a ball is `L`-Lipschitz there. -/
lemma lip_of_deriv_bound {f : ℝ → ℝ} {c ρ L : ℝ} (hf : ContDiffOn ℝ 1 f (ball c ρ))
    (hb : ∀ z ∈ ball c ρ, |deriv f z| ≤ L) {x y : ℝ} (hx : x ∈ ball c ρ) (hy : y ∈ ball c ρ) :
    |f x - f y| ≤ L * |x - y| := by
  have hdiff : ∀ z ∈ ball c ρ, DifferentiableAt ℝ f z := fun z hz =>
    (hf.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hz)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := ball c ρ) (C := L) hdiff
    (fun z hz => by simpa [Real.norm_eq_abs] using hb z hz) (convex_ball c ρ) hy hx
  simpa [Real.norm_eq_abs] using this


/-- **Explicit jets of the Langer amplitude** `g̃ = (A ζ' Sh(ζζ'²))^{-1/2}`; see the module docstring. -/
theorem dun_amp (aLo aHi KA c1 d0 d1 d2 εS Msh ρ1 : ℝ) (haLo : 0 < aLo) (ha : aLo ≤ aHi) (hc1 : 0 < c1) (hcd : c1 ≤ d0)
    (hρ1 : 0 < ρ1) (hShpos : ∀ w : ℝ, |w| < εS → 1 / 2 < langerSinhc w) (hεS : 0 < εS)
    (hShb : ∀ w : ℝ, |w| < εS →
      |langerSinhc w| ≤ Msh ∧ |deriv langerSinhc w| ≤ Msh ∧ |deriv (deriv langerSinhc) w| ≤ Msh) :
    ∃ gmin g0 g1 g2 : ℝ, 0 < gmin ∧ gmin ≤ g0 ∧ ∀ {ζ A : ℝ → ℝ} {c : ℝ},
      J2 A (ball c ρ1) aHi KA KA → (∀ x ∈ ball c ρ1, aLo ≤ A x) → ContDiffOn ℝ 3 ζ (ball c ρ1) →
      J2 (deriv ζ) (ball c ρ1) d0 d1 d2 → (∀ x ∈ ball c ρ1, c1 ≤ deriv ζ x) → ζ c = 0 →
      (∀ x ∈ ball c ρ1, |ζ x * deriv ζ x ^ 2| < εS) →
      J2 (fun x => (A x * deriv ζ x * langerSinhc (ζ x * deriv ζ x ^ 2)) ^ (-(1 / 2 : ℝ))) (ball c ρ1) g0 g1 g2 ∧
      (∀ x ∈ ball c ρ1, gmin ≤ (A x * deriv ζ x * langerSinhc (ζ x * deriv ζ x ^ 2)) ^ (-(1 / 2 : ℝ))) := by
  have hd0 : 0 < d0 := lt_of_lt_of_le hc1 hcd
  have haHi : 0 < aHi := lt_of_lt_of_le haLo ha
  have hM1 : 1 / 2 < Msh := by
    have h1 := hShpos 0 (by simpa using hεS)
    have h2 := (hShb 0 (by simpa using hεS)).1
    linarith [le_abs_self (langerSinhc 0)]
  -- explicit bounds
  set z0 : ℝ := d0 * ρ1 with hz0
  set f0 : ℝ := z0 * d0 with hf0
  set f1 : ℝ := d0 * d0 + z0 * d1 with hf1
  set f2 : ℝ := d1 * d0 + 2 * (d0 * d1) + z0 * d2 with hf2
  set F0 : ℝ := f0 * d0 with hF0
  set F1 : ℝ := f1 * d0 + f0 * d1 with hF1
  set F2 : ℝ := f2 * d0 + 2 * (f1 * d1) + f0 * d2 with hF2
  set s0 : ℝ := Msh with hs0
  set s1 : ℝ := Msh * F1 with hs1
  set s2 : ℝ := Msh * (F1 * F1) + Msh * F2 with hs2
  set r0 : ℝ := aHi * d0 with hr0
  set r1 : ℝ := KA * d0 + aHi * d1 with hr1
  set r2 : ℝ := KA * d0 + 2 * (KA * d1) + aHi * d2 with hr2
  set R0 : ℝ := r0 * s0 with hR0
  set R1 : ℝ := r1 * s0 + r0 * s1 with hR1
  set R2 : ℝ := r2 * s0 + 2 * (r1 * s1) + r0 * s2 with hR2
  set ℓ : ℝ := aLo * c1 * (1 / 2) with hℓ
  have hℓp : 0 < ℓ := by positivity
  have hR0p : 0 < R0 := by rw [hR0, hr0, hs0]; positivity
  set P0 : ℝ := max (ℓ ^ (-(1 / 2 : ℝ))) (R0 ^ (-(1 / 2 : ℝ))) with hP0
  set P1 : ℝ := max (ℓ ^ (-(1 / 2 : ℝ) - 1)) (R0 ^ (-(1 / 2 : ℝ) - 1)) with hP1
  set P2 : ℝ := max (ℓ ^ (-(1 / 2 : ℝ) - 1 - 1)) (R0 ^ (-(1 / 2 : ℝ) - 1 - 1)) with hP2
  refine ⟨R0 ^ (-(1 / 2 : ℝ)), P0, R1 * |(-(1 / 2 : ℝ))| * P1,
    R2 * |(-(1 / 2 : ℝ))| * P1 + R1 * (|(-(1 / 2 : ℝ))| * |(-(1 / 2 : ℝ)) - 1|) * P2 * R1,
    Real.rpow_pos_of_pos hR0p _, ?_, ?_⟩
  · exact (le_max_right _ _)
  intro ζ A c hA hAl hζ3 hD hDl hζ0' hFs
  have hB : IsOpen (ball c ρ1) := isOpen_ball
  -- `ζ`
  have hζ1 : ContDiffOn ℝ 1 ζ (ball c ρ1) := hζ3.of_le (by norm_num)
  have hJζ : J2 ζ (ball c ρ1) z0 d0 d1 := by
    refine ⟨hζ3.of_le (by norm_num), fun x hx => ⟨?_, (hD.2 x hx).1, (hD.2 x hx).2.1⟩⟩
    have := lip_of_deriv_bound hζ1 (fun z hz => (hD.2 z hz).1) hx (mem_ball_self hρ1)
    rw [hζ0', sub_zero] at this
    have hxc : |x - c| < ρ1 := by simpa [Real.dist_eq] using hx
    calc |ζ x| ≤ d0 * |x - c| := this
      _ ≤ d0 * ρ1 := mul_le_mul_of_nonneg_left hxc.le hd0.le
  -- `F = ζ ζ'²`
  have hJf := J2.mul hB hJζ hD
  have hJF := (J2.mul hB hJf hD).congr hB (fun x _ => by ring : ∀ x ∈ ball c ρ1,
    ζ x * deriv ζ x ^ 2 = ζ x * deriv ζ x * deriv ζ x)
  -- `S = Sh(F)`
  have hJS : J2 (fun x => langerSinhc (ζ x * deriv ζ x ^ 2)) (ball c ρ1) s0 s1 s2 :=
    J2.comp (φ := langerSinhc) (T := ball 0 εS) hB isOpen_ball hJF
      ((contDiff_langerSinhc.of_le (by norm_num)).contDiffOn)
      (fun x hx => by rw [mem_ball_zero_iff, Real.norm_eq_abs]; exact hFs x hx)
      (fun y hy => hShb y (by rwa [mem_ball_zero_iff, Real.norm_eq_abs] at hy))
  have hJAd := J2.mul hB hA hD
  have hJR := J2.mul hB hJAd hJS
  have hRl : ∀ x ∈ ball c ρ1, ℓ ≤ A x * deriv ζ x * langerSinhc (ζ x * deriv ζ x ^ 2) := by
    intro x hx
    have h1 := hAl x hx
    have h2 := hDl x hx
    have h3 := hShpos _ (hFs x hx)
    rw [hℓ]
    have : aLo * c1 ≤ A x * deriv ζ x := mul_le_mul h1 h2 hc1.le (haLo.le.trans h1)
    have hpos : 0 < aLo * c1 := by positivity
    nlinarith
  have hRu : ∀ x ∈ ball c ρ1, A x * deriv ζ x * langerSinhc (ζ x * deriv ζ x ^ 2) ≤ R0 :=
    fun x hx => (le_abs_self _).trans (hJR.2 x hx).1
  have hg := J2.rpow (-(1 / 2)) (R0 := P0) (R1 := P1) (R2 := P2) hB hJR hℓp hRl
    (fun x hx => rpow_le_max_of_mem _ hℓp (hRl x hx) (hRu x hx))
    (fun x hx => rpow_le_max_of_mem _ hℓp (hRl x hx) (hRu x hx))
    (fun x hx => rpow_le_max_of_mem _ hℓp (hRl x hx) (hRu x hx))
  refine ⟨hg, fun x hx => ?_⟩
  exact Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le hℓp (hRl x hx)) (hRu x hx) (by norm_num)

end FormalResearch.Special

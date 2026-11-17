module

public import FormalResearch.Special.AiryCftSignEqualityGrowth
public import FormalResearch.Special.AiryKernelOpBounds
public import FormalResearch.Special.AiryAsymReal

/-!
# Theorem B, equality case: `u₁ = a₁ ⇒ f = c · Ai²/(u - a₁)`, `c < 0`

CFT `AIRY_POISSON.md` §4 (Theorem B, "equality holds iff `f = c Ai²/(u - a₁)` with `c < 0`"; Proof 2, step 4; Proof 1 via the
Liouville argument).  Let `f` be entire, real on `ℝ`, `f ∈ L¹(ℝ)`, `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` for some real `ν`, `f ≢ 0`, `f ≥ 0` on
`(-∞, a₁]` and `∫ f ≤ 0`.  Then (**proved**, `airy_sign_equality`) there is a real `c < 0` with

`f(u) = c · Ai(u)²/(u - a₁)`  for `u ≠ a₁`   (equivalently `f = (-c) · airyExtremal`),

and conversely every such function satisfies the hypotheses (`airy_sign_equality_converse`, from `airyExtremal_attains`), so
`airy_sign_equality_iff` is the "iff" of the note's Theorem B.

Proof (assembling `AiryCftSignEquality`, `AiryCftSignEqualityDiv`, `AiryCftSignEqualityGrowth`):
1. `∫ f = 0`, `f(a_n) = 0` (`airy_sign_equality_samples`); `f'(a_n) = 0` for `n ≥ 2` (interior minimum on the band).
2. `(u - a₁) f = H Ai²` with `H` entire (`airy_eq_div`: second-order zeros of the numerator at the simple zeros of `Ai`).
3. `H = β + (u - a₁)(q₀ + q₁ u)` (`airy_eq_affine`: `‖H‖ ≲ r²` on the good circles, maximum modulus, Liouville).
4. Hence `f = -β·airyExtremal + (q₀ + q₁ u) Ai²` off `a₁`; `(q₀ + q₁x) Ai(x)² ∈ L¹(ℝ)` forces `q₀ = q₁ = 0`
   (`airy_poly_sq_not_integrable`: `∫_{-R}^{-M} Ai² = K(-R) - K(-M) ≥ √R/π - 1 - K(-M)`, with `K(x) = Ai'² - xAi²`, `airyKer_diag_neg`).
5. `f = λ·airyExtremal` with `λ = -β` real (compare at `0`, where `f` and `airyExtremal` are real and the latter nonzero) and `λ > 0` from
   `f ≥ 0` on the band and `airyExtremal > 0` at the midpoint of `(a₂, a₁)` (`f ≢ 0` gives `λ ≠ 0`).

(`∫ f = 0` is then `airyExtremal_integral`, or directly `airy_sign_equality_samples`.)

Sanity check only (mpmath, 30 digits): `∫_{-R}^0 Ai² = K(-R) - K(0)` agrees to 30 digits
with quadrature for `R = 4, 16, 100, 400` (values `0.578, 1.211, 3.116, 6.299` against `√R/π = 0.637, 1.273, 3.183, 6.366`), the growth
used in step 4.  Everything stated above is proved (the sign of `c` and the converse are part of the formal statement).  Not formalised: the note's Remark B.1 (tangent rigidity, the sign-unstable direction at vacuum equality), which uses
the equality case as a black box.  The proof above needs none of the note's other unformalised machinery (Airy–Poisson identity, Lemma H,
the node phase, the polynomial class `P·Ai + Q·Ai'`): it uses only `airyQ_mem_half` (`𝒢_N ⊂ 𝒢_{1/2}`), the good circles and the proved sample
vanishing, all already on `master`.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

/-- `Ai²` is not integrable on any half-line `(-∞, -M]` (indeed `∫_{-R}^{-M} Ai² = K(-R) - K(-M) → ∞`). -/
lemma airyAi_sq_not_integrableOn_Iic (M : ℝ) :
    ¬ IntegrableOn (fun x : ℝ => airyAi x ^ 2) (Iic (-M)) := by
  intro hI
  have hpi := Real.pi_pos
  set I : ℝ := ∫ x in Iic (-M), airyAi x ^ 2 with hIdef
  set B : ℝ := I + airyKer (-M) (-M) with hB
  set R : ℝ := (π * (|B| + 2)) ^ 2 + |M| + 1 with hR
  have hR1 : 1 ≤ R := by nlinarith [sq_nonneg (π * (|B| + 2)), abs_nonneg M]
  have hRM : M ≤ R := by nlinarith [sq_nonneg (π * (|B| + 2)), le_abs_self M]
  -- FTC
  have hd : ∀ x ∈ Set.uIcc (-R) (-M), HasDerivAt (fun x => -airyKer x x) (airyAi x ^ 2) x := by
    intro x _
    have h := (hasDerivAt_airyKer_diag x).neg
    rw [neg_neg] at h
    exact h
  have hc : Continuous (fun x : ℝ => airyAi x ^ 2) := (continuous_airyAi.pow 2)
  have hftc : ∫ x in (-R)..(-M), airyAi x ^ 2 = airyKer (-R) (-R) - airyKer (-M) (-M) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
    ring
  have hle : ∫ x in (-R)..(-M), airyAi x ^ 2 ≤ I := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_mono_set hI (Eventually.of_forall fun x => sq_nonneg _) ?_
    exact (Eventually.of_forall fun x hx => by
      have : x ≤ -M := hx.2
      exact this)
  have hK := airyKer_diag_neg hR1
  have h1 : √R / π - 1 / R ≤ airyKer (-R) (-R) := by
    have := (abs_le.1 hK).1; linarith
  have hsq : π * (|B| + 2) ≤ √R := by
    rw [show π * (|B| + 2) = √((π * (|B| + 2)) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_le_sqrt (by nlinarith [abs_nonneg M])
  have h2 : |B| + 2 ≤ √R / π := by rw [le_div_iff₀ hpi]; linarith
  have h3 : 1 / R ≤ 1 := by rw [div_le_one (by linarith)]; exact hR1
  have := le_abs_self B
  linarith

/-- **No polynomial multiple of `Ai²` is integrable on `ℝ`**: if `(q₀ + q₁ x) Ai(x)² ∈ L¹(ℝ)` then `q₀ = q₁ = 0`. -/
theorem airy_poly_sq_not_integrable {q₀ q₁ : ℂ}
    (hint : Integrable (fun x : ℝ => (q₀ + q₁ * (x : ℂ)) * (airyAi x : ℂ) ^ 2)) : q₀ = 0 ∧ q₁ = 0 := by
  by_contra hne
  -- a uniform lower bound `‖q₀ + q₁ x‖ ≥ δ > 0` on a half-line
  obtain ⟨δ, M, hδ, hM⟩ : ∃ δ M : ℝ, 0 < δ ∧ ∀ x : ℝ, x ≤ -M → δ ≤ ‖q₀ + q₁ * (x : ℂ)‖ := by
    by_cases h1 : q₁ = 0
    · have h0 : q₀ ≠ 0 := fun h0 => hne ⟨h0, h1⟩
      refine ⟨‖q₀‖, 0, norm_pos_iff.2 h0, fun x _ => ?_⟩
      simp [h1]
    · have hq1 : 0 < ‖q₁‖ := norm_pos_iff.2 h1
      refine ⟨1, (‖q₀‖ + 1) / ‖q₁‖, one_pos, fun x hx => ?_⟩
      have hx' : (‖q₀‖ + 1) / ‖q₁‖ ≤ |x| := by
        have := abs_of_nonpos (show x ≤ 0 from hx.trans (by
          have : 0 ≤ (‖q₀‖ + 1) / ‖q₁‖ := by positivity
          linarith))
        rw [this]; linarith
      have h2 : ‖q₀‖ + 1 ≤ ‖q₁‖ * |x| := by
        have := (div_le_iff₀ hq1).1 hx'
        linarith
      have h3 : ‖q₁ * (x : ℂ)‖ = ‖q₁‖ * |x| := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h4 : ‖q₁ * (x : ℂ)‖ - ‖q₀‖ ≤ ‖q₀ + q₁ * (x : ℂ)‖ := by
        have := norm_sub_le (q₀ + q₁ * (x : ℂ)) q₀
        rw [add_sub_cancel_left] at this
        linarith [norm_sub_norm_le (q₁ * (x : ℂ)) (-q₀), norm_neg q₀, norm_add_le q₀ (q₁ * (x : ℂ)),
          norm_sub_rev (q₀ + q₁ * (x : ℂ)) q₀]
      linarith
  apply airyAi_sq_not_integrableOn_Iic M
  have hI : IntegrableOn (fun x : ℝ => ‖(q₀ + q₁ * (x : ℂ)) * (airyAi x : ℂ) ^ 2‖ / δ) (Iic (-M)) :=
    (hint.norm.div_const δ).integrableOn
  refine Integrable.mono' hI ((continuous_airyAi.pow 2).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx => ?_)
  have hx' : x ≤ -M := hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), le_div_iff₀ hδ, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]
  have := hM x hx'
  nlinarith [sq_nonneg (airyAi x)]

/-- info: 'FormalResearch.Special.airy_poly_sq_not_integrable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_poly_sq_not_integrable

/-- `airyExtremal` is strictly positive on the band, away from the zeros of `Ai`: here at the midpoint of `(a₂, a₁)`. -/
lemma airyExtremal_pos_mid :
    ∃ x : ℝ, x ≤ airyZero 1 ∧ 0 < (airyExtremal (x : ℂ)).re := by
  set x : ℝ := (airyZero 1 + airyZero 2) / 2 with hx
  have h21 : airyZero 2 < airyZero 1 := airyZero_strictAnti (n := 1) le_rfl
  have hx1 : x < airyZero 1 := by rw [hx]; linarith
  have hx2 : airyZero 2 < x := by rw [hx]; linarith
  refine ⟨x, hx1.le, ?_⟩
  have hAi : airyAi x ≠ 0 := by
    intro h0
    have hc : airyAiC (x : ℂ) = 0 := by rw [airyAiC_ofReal, h0]; simp
    obtain ⟨n, hn, hxn⟩ := (airyAiC_eq_zero_iff _).1 hc
    have hxn' : x = airyZero n := by exact_mod_cast hxn
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this; linarith
    · have := airyZero_le_of_le (n := 2) (by norm_num) h
      linarith
  rw [airyExtremal_re]
  have : airyAi x ^ 2 / (x - airyZero 1) < 0 :=
    div_neg_of_pos_of_neg (by positivity) (by linarith)
  linarith

/-- **Theorem B, equality case.**  Let `f` be entire, real on `ℝ`, `f ∈ L¹(ℝ)`, `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` (any real `ν`), `f ≢ 0`,
`f ≥ 0` on `(-∞, a₁]` and `∫ f ≤ 0`.  Then `f = (-c) · airyExtremal`, i.e. `f(u) = c Ai(u)²/(u - a₁)`, for a real `c < 0`. -/
theorem airy_sign_equality {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hfi : Integrable (fun x : ℝ => f (x : ℂ)))
    {C ν : ℝ} (hC : 0 ≤ C) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hreal : ∀ x : ℝ, (f (x : ℂ)).im = 0) (hpos : ∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (f (x : ℂ)).re)
    (hint : (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0) (hne : ∃ z : ℂ, f z ≠ 0) :
    ∃ c : ℝ, c < 0 ∧ (∀ u : ℂ, f u = ((-c : ℝ) : ℂ) * airyExtremal u) ∧
      ∀ u : ℂ, u ≠ (airyZero 1 : ℂ) → f u = (c : ℂ) * airyAiC u ^ 2 / (u - (airyZero 1 : ℂ)) := by
  obtain ⟨-, hs⟩ := airy_sign_equality_samples hf hfi hC hb hreal hpos hint
  obtain ⟨H, hHd, hH⟩ := airy_eq_div hf hreal hpos hs
  obtain ⟨q₀, q₁, hHq⟩ := airy_eq_affine hf hfi hC hb hHd hH
  set a : ℝ := airyZero 1 with ha
  set β : ℂ := H (a : ℂ) with hβ
  -- the decomposition of `f` off `a₁`
  have hfu : ∀ u : ℂ, u ≠ (a : ℂ) → f u = -β * airyExtremal u + (q₀ + q₁ * u) * airyAiC u ^ 2 := by
    intro u hu
    have hsub : u - (a : ℂ) ≠ 0 := sub_ne_zero.2 hu
    have h1 := hH u
    rw [hHq u] at h1
    rw [airyExtremal_eq hu, ← ha]
    have key : f u = (β + (u - (a : ℂ)) * (q₀ + q₁ * u)) * airyAiC u ^ 2 / (u - (a : ℂ)) := by
      rw [eq_div_iff hsub]; linear_combination h1
    rw [key]
    field_simp
  -- integrability of the polynomial part
  have hpoly : Integrable (fun x : ℝ => (q₀ + q₁ * (x : ℂ)) * (airyAi x : ℂ) ^ 2) := by
    have hsum : Integrable (fun x : ℝ => f (x : ℂ) + β * airyExtremal (x : ℂ)) :=
      hfi.add (airyExtremal_integrable.const_mul β)
    refine hsum.congr ?_
    have hae : ∀ᵐ x : ℝ ∂volume, x ∉ ({a} : Set ℝ) := (Set.countable_singleton a).ae_notMem volume
    filter_upwards [hae] with x hx
    have hxa : (x : ℂ) ≠ (a : ℂ) := fun h => hx (by simpa using (Complex.ofReal_injective h))
    rw [hfu (x : ℂ) hxa, airyAiC_ofReal]
    ring
  obtain ⟨hq0, hq1⟩ := airy_poly_sq_not_integrable hpoly
  -- so `f = -β · airyExtremal` everywhere
  have hfE : ∀ u : ℂ, f u = -β * airyExtremal u := by
    intro u
    by_cases hu : u = (a : ℂ)
    · rw [hu, hs 1 le_rfl]
      have : airyExtremal (a : ℂ) = 0 := by
        unfold airyExtremal; rw [ha, airyAiC_airyZero]; simp
      rw [this]; simp
    · rw [hfu u hu, hq0, hq1]; simp
  -- `-β` is real: compare at `0`
  obtain ⟨e, he⟩ : ∃ e : ℝ, airyExtremal ((0 : ℝ) : ℂ) = (e : ℂ) := ⟨_, airyExtremal_ofReal 0⟩
  have he0 : e ≠ 0 := by
    intro h0
    have h1 := airyExtremal_re 0
    rw [he, h0] at h1
    simp only [Complex.ofReal_zero, Complex.zero_re] at h1
    have ha0 := airyAi_pos (le_refl (0 : ℝ))
    have hz := airyZero_neg 1
    have : 0 < airyAi 0 ^ 2 / (0 - airyZero 1) := div_pos (by positivity) (by linarith)
    linarith
  set lam : ℝ := (f ((0 : ℝ) : ℂ)).re / e with hlam
  have hlamE : ∀ u : ℂ, f u = (lam : ℂ) * airyExtremal u := by
    intro u
    have h0 := hfE ((0 : ℝ) : ℂ)
    rw [airy_real_cast hreal 0, he] at h0
    have hb' : -β = (lam : ℂ) := by
      rw [hlam]
      have : (e : ℂ) ≠ 0 := by exact_mod_cast he0
      push_cast
      field_simp
      linear_combination -h0
    rw [hfE u, hb']
  -- sign of `lam`
  obtain ⟨x₀, hx₀, hxpos⟩ := airyExtremal_pos_mid
  have hlam_nn : 0 ≤ lam := by
    have h1 := hpos x₀ hx₀
    rw [hlamE (x₀ : ℂ)] at h1
    have : (((lam : ℝ) : ℂ) * airyExtremal (x₀ : ℂ)).re = lam * (airyExtremal (x₀ : ℂ)).re := by
      simp [Complex.mul_re, airyExtremal_ofReal, Complex.ofReal_im]
    rw [this] at h1
    by_contra hneg
    push Not at hneg
    nlinarith
  have hlam_ne : lam ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := hne
    apply hz
    rw [hlamE z, h0]; simp
  have hlam_pos : 0 < lam := lt_of_le_of_ne hlam_nn (Ne.symm hlam_ne)
  refine ⟨-lam, by linarith, fun u => ?_, fun u hu => ?_⟩
  · rw [hlamE u]; simp
  · rw [hlamE u, airyExtremal_eq hu]
    push_cast
    ring

/-- info: 'FormalResearch.Special.airy_sign_equality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sign_equality

/-- **Converse.**  For real `c < 0`, `f = (-c) · airyExtremal` (that is `c Ai²/(u - a₁)`) satisfies every hypothesis of Theorem B
with `u₁ = a₁`, and `∫ f = 0`. -/
theorem airy_sign_equality_converse {c : ℝ} (hc : c < 0) :
    Differentiable ℂ (fun u : ℂ => ((-c : ℝ) : ℂ) * airyExtremal u) ∧
      Integrable (fun x : ℝ => ((-c : ℝ) : ℂ) * airyExtremal (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖((-c : ℝ) : ℂ) * airyExtremal u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (((-c : ℝ) : ℂ) * airyExtremal (x : ℂ)).im = 0) ∧
      (∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (((-c : ℝ) : ℂ) * airyExtremal (x : ℂ)).re) ∧
      (∫ x : ℝ, (((-c : ℝ) : ℂ) * airyExtremal (x : ℂ)).re) = 0 ∧
      (∃ z : ℂ, ((-c : ℝ) : ℂ) * airyExtremal z ≠ 0) := by
  obtain ⟨hd, hi, ⟨C, ν, hC, hb⟩, hr, hp, hint, ⟨z, hz⟩⟩ := airyExtremal_attains
  have hlam : (0 : ℝ) < -c := by linarith
  have hre : ∀ x : ℝ, (((-c : ℝ) : ℂ) * airyExtremal (x : ℂ)).re = (-c) * (airyExtremal (x : ℂ)).re := by
    intro x; simp [Complex.mul_re]
  refine ⟨(differentiable_const _).mul hd, hi.const_mul _, ⟨|(-c)| * C, ν, by positivity, fun u => ?_⟩,
    fun x => ?_, fun x hx => ?_, ?_, ⟨z, mul_ne_zero (by exact_mod_cast hlam.ne') hz⟩⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have := hb u
    calc |(-c)| * ‖airyExtremal u‖ ≤ |(-c)| * (C * (1 + ‖u‖) ^ ν * airyEnv u) := by gcongr
      _ = |(-c)| * C * (1 + ‖u‖) ^ ν * airyEnv u := by ring
  · simp [Complex.mul_im, hr x]
  · rw [hre]; exact mul_nonneg hlam.le (hp x hx)
  · simp_rw [hre]
    rw [integral_const_mul, hint]; simp

/-- **Theorem B, `u₁ = a₁` equality case, as an equivalence.**  An entire `f` is real on `ℝ`, in `L¹(ℝ)`, of the class growth, `≢ 0`,
`≥ 0` on `(-∞, a₁]` with `∫ f ≤ 0` **iff** `f = c Ai²/(u - a₁)` (that is `(-c) · airyExtremal`) with `c < 0`. -/
theorem airy_sign_equality_iff {f : ℂ → ℂ} :
    (Differentiable ℂ f ∧ Integrable (fun x : ℝ => f (x : ℂ)) ∧
      (∃ C ν : ℝ, 0 ≤ C ∧ ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) ∧
      (∀ x : ℝ, (f (x : ℂ)).im = 0) ∧ (∀ x : ℝ, x ≤ airyZero 1 → 0 ≤ (f (x : ℂ)).re) ∧
      (∫ x : ℝ, (f (x : ℂ)).re) ≤ 0 ∧ (∃ z : ℂ, f z ≠ 0)) ↔
    ∃ c : ℝ, c < 0 ∧ ∀ u : ℂ, f u = ((-c : ℝ) : ℂ) * airyExtremal u := by
  constructor
  · rintro ⟨hf, hfi, ⟨C, ν, hC, hb⟩, hreal, hpos, hint, hne⟩
    obtain ⟨c, hc, hfe, -⟩ := airy_sign_equality hf hfi hC hb hreal hpos hint hne
    exact ⟨c, hc, hfe⟩
  · rintro ⟨c, hc, hfe⟩
    have : f = fun u : ℂ => ((-c : ℝ) : ℂ) * airyExtremal u := funext hfe
    subst this
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := airy_sign_equality_converse hc
    exact ⟨h1, h2, h3, h4, h5, h6.le, h7⟩

/-- info: 'FormalResearch.Special.airy_sign_equality_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sign_equality_converse

/-- info: 'FormalResearch.Special.airy_sign_equality_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sign_equality_iff

end FormalResearch.Special

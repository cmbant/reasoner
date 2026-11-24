module

public import FormalResearch.SignUncertainty.MiddleBandPointwise
public import FormalResearch.SignUncertainty.MiddleBandCutoff
public import FormalResearch.SignUncertainty.MiddleBandTail
public import FormalResearch.SignUncertainty.MiddleBandVdc

/-!
# GT.2a: region lemmas for the cubic phase

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a` (shoulders, far zone, near zero).

* `cubic_two_ibp_gen`: general-exponent power version of `cubic_two_ibp_pw`: amplitude bounds `|a^{(r)}(x)| ≤ B x^{-s-r}` on
  `[α, β]`, `0 < α`, `|ψ'| ≥ q x²` give `|∫ a e^{iψ}| ≤ B C(q) α^{-(s+5)} / (s+5)`.

Status: proved, unconditional.
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.SignUncertainty

/-- The constant of `cubic_two_ibp_gen`. -/
noncomputable def cubicC (q : ℝ) : ℝ :=
  1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3) + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)

lemma cubicC_nonneg {q : ℝ} (hq : 0 < q) : 0 ≤ cubicC q := by
  unfold cubicC
  have t1 : 0 ≤ 1 / q ^ 2 := div_nonneg zero_le_one (pow_pos hq 2).le
  have t2 : 0 ≤ Real.pi ^ 2 / (2 * q ^ 3) :=
    div_nonneg (by positivity) (mul_pos (by norm_num) (pow_pos hq 3)).le
  have t3 : 0 ≤ Real.pi ^ 2 / (6 * q ^ 3) :=
    div_nonneg (by positivity) (mul_pos (by norm_num) (pow_pos hq 3)).le
  have t4 : 0 ≤ Real.pi ^ 4 / (12 * q ^ 4) :=
    div_nonneg (by positivity) (mul_pos (by norm_num) (pow_pos hq 4)).le
  linarith

/-- General-exponent power instance of `cubic_two_ibp_pw`: with `|a^{(r)}(x)| ≤ B x^{-s-r}` on `[α, β]`, `0 < α`, `-5 < s`, and
`|ψ'| ≥ q x²`, the integral is at most `B C(q) α^{-(s+5)}/(s+5)`. Classes: proved. -/
theorem cubic_two_ibp_gen {a : ℝ → ℂ} {a0 α β B q s : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hB : 0 ≤ B)
    (hq : 0 < q) (hs : -5 < s) (ha : ContDiff ℝ 2 a)
    (hsupp : ∀ x, x ∉ Set.Icc α β → a x = 0)
    (hb0 : ∀ x ∈ Set.Icc α β, ‖a x‖ ≤ B * x ^ (-s))
    (hb1 : ∀ x ∈ Set.Icc α β, ‖deriv a x‖ ≤ B * x ^ (-s - 1))
    (hb2 : ∀ x ∈ Set.Icc α β, ‖deriv (deriv a) x‖ ≤ B * x ^ (-s - 2))
    (hp : ∀ x ∈ Set.Icc α β, q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|) :
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      B * cubicC q * (α ^ (-(s + 5)) / (s + 5)) := by
  have hxpos : ∀ x ∈ Set.Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα (Set.mem_Icc.1 hx).1
  have hGid : ∀ x ∈ Set.Icc α β,
      (B * x ^ (-s - 2)) / (q * x ^ 2) ^ 2
        + 3 * (B * x ^ (-s - 1)) * (Real.pi ^ 2 * |x| / 6) / (q * x ^ 2) ^ 3
        + (B * x ^ (-s)) * (Real.pi ^ 2 / 6) / (q * x ^ 2) ^ 3
        + 3 * (B * x ^ (-s)) * (Real.pi ^ 2 * x / 6) ^ 2 / (q * x ^ 2) ^ 4
        = B * cubicC q * x ^ (-s - 6) := by
    intro x hx
    have hx0 : 0 < x := hxpos x hx
    have hqne : q ≠ 0 := hq.ne'
    have e2 : x ^ (-s - 2) = x ^ (-s - 6) * x ^ (4 : ℕ) := by
      rw [show (-s - 2) = (-s - 6) + ((4 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hx0, Real.rpow_natCast]
    have e1 : x ^ (-s - 1) = x ^ (-s - 6) * x ^ (5 : ℕ) := by
      rw [show (-s - 1) = (-s - 6) + ((5 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hx0, Real.rpow_natCast]
    have e0 : x ^ (-s) = x ^ (-s - 6) * x ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; push_cast; ring
    rw [e2, e1, e0, abs_of_pos hx0]
    unfold cubicC
    field_simp
    ring
  have hpow_Ici : IntegrableOn (fun x : ℝ => x ^ (-s - 6)) (Set.Ici α) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hα
  have hpow_int : IntegrableOn (fun x : ℝ => x ^ (-s - 6)) (Set.Icc α β) :=
    hpow_Ici.mono_set Set.Icc_subset_Ici_self
  have hint : IntegrableOn (fun x => (B * x ^ (-s - 2)) / (q * x ^ 2) ^ 2
        + 3 * (B * x ^ (-s - 1)) * (Real.pi ^ 2 * |x| / 6) / (q * x ^ 2) ^ 3
        + (B * x ^ (-s)) * (Real.pi ^ 2 / 6) / (q * x ^ 2) ^ 3
        + 3 * (B * x ^ (-s)) * (Real.pi ^ 2 * x / 6) ^ 2 / (q * x ^ 2) ^ 4) (Set.Icc α β) :=
    IntegrableOn.congr_fun (f := fun x => B * cubicC q * x ^ (-s - 6))
      (hpow_int.const_mul _) (fun x hx => (hGid x hx).symm) measurableSet_Icc
  have hpw := cubic_two_ibp_pw (a := a) (a0 := a0) (α := α) (β := β) hαβ ha hsupp
    (b0 := fun x => B * x ^ (-s)) (b1 := fun x => B * x ^ (-s - 1))
    (b2 := fun x => B * x ^ (-s - 2)) (p := fun x => q * x ^ 2) hb0 hb1 hb2
    (fun x hx => ⟨mul_pos hq (pow_pos (hxpos x hx) 2), hp x hx⟩) hint
  have hBC : 0 ≤ B * cubicC q := mul_nonneg hB (cubicC_nonneg hq)
  have hT : ∫ x in Set.Icc α β, x ^ (-s - 6) ≤ α ^ (-(s + 5)) / (s + 5) := by
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici α)] (fun x : ℝ => x ^ (-s - 6)) :=
      (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x hx =>
        Real.rpow_nonneg (by have := Set.mem_Ici.1 hx; linarith) _)
    calc ∫ x in Set.Icc α β, x ^ (-s - 6)
        ≤ ∫ x in Set.Ici α, x ^ (-s - 6) :=
          setIntegral_mono_set hpow_Ici hnn (ae_of_all _ fun x (hx : x ∈ Set.Icc α β) =>
            Set.Icc_subset_Ici_self hx)
      _ = ∫ x in Set.Ioi α, x ^ (-s - 6) := by rw [integral_Ici_eq_integral_Ioi]
      _ = ∫ x in Set.Ioi α, x ^ (-(s + 6)) := by
          congr 1; funext x; congr 1; ring
      _ = α ^ (1 - (s + 6)) / (s + 6 - 1) := mb_tail_pow hα (by linarith)
      _ = α ^ (-(s + 5)) / (s + 5) := by
          congr 1
          · congr 1; ring
          · ring
  have hI : ∫ x in Set.Icc α β, B * cubicC q * x ^ (-s - 6) ≤ B * cubicC q * (α ^ (-(s + 5)) / (s + 5)) := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hT hBC
  have hEq : ∫ x in Set.Icc α β, (B * x ^ (-s - 2)) / (q * x ^ 2) ^ 2
        + 3 * (B * x ^ (-s - 1)) * (Real.pi ^ 2 * |x| / 6) / (q * x ^ 2) ^ 3
        + (B * x ^ (-s)) * (Real.pi ^ 2 / 6) / (q * x ^ 2) ^ 3
        + 3 * (B * x ^ (-s)) * (Real.pi ^ 2 * x / 6) ^ 2 / (q * x ^ 2) ^ 4
      = ∫ x in Set.Icc α β, B * cubicC q * x ^ (-s - 6) :=
    setIntegral_congr_fun measurableSet_Icc (fun x hx => hGid x hx)
  exact hpw.trans (hEq.le.trans hI)

/-- info: 'FormalResearch.SignUncertainty.cubic_two_ibp_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_two_ibp_gen


/-! ### Splitting at zero and reflecting the negative half -/

/-- The oscillatory integral `∫ a e^{iψ}`, `ψ(x) = a0 x - π² x³/36`. -/
noncomputable def oscInt (a0 : ℝ) (a : ℝ → ℂ) : ℂ :=
  ∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))

/-- Positive part `a · 1_{x>0}` of an amplitude vanishing near `0`. -/
noncomputable def posPart (a : ℝ → ℂ) (x : ℝ) : ℂ := if 0 < x then a x else 0

/-- Negative part `a · 1_{x<0}` of an amplitude vanishing near `0`. -/
noncomputable def negPart (a : ℝ → ℂ) (x : ℝ) : ℂ := if x < 0 then a x else 0

lemma posPart_eventuallyEq {a : ℝ → ℂ} {α : ℝ} (hα : 0 < α) (hz : ∀ x, |x| < α → a x = 0) (x : ℝ) :
    posPart a =ᶠ[nhds x] fun y => if 0 < x then a y else 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : ∀ᶠ y in nhds x, y < 0 := Iio_mem_nhds hx
    filter_upwards [this] with y hy
    simp [posPart, not_lt.2 hy.le, not_lt.2 hx.le]
  · subst hx
    have : ∀ᶠ y in nhds (0 : ℝ), |y| < α := by
      have : Metric.ball (0 : ℝ) α ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hα
      filter_upwards [this] with y hy using by simpa [Real.dist_eq] using hy
    filter_upwards [this] with y hy
    simp [posPart, hz y hy]
  · have : ∀ᶠ y in nhds x, 0 < y := Ioi_mem_nhds hx
    filter_upwards [this] with y hy
    simp [posPart, hy, hx]

lemma posPart_contDiff {a : ℝ → ℂ} {α : ℝ} (hα : 0 < α) (hz : ∀ x, |x| < α → a x = 0) (ha : ContDiff ℝ 2 a) :
    ContDiff ℝ 2 (posPart a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : posPart a =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [posPart, not_lt.2 (le_of_lt (show y < 0 from hy))]
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · subst hx
    have : posPart a =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
      have : Metric.ball (0 : ℝ) α ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hα
      filter_upwards [this] with y hy
      have hy' : |y| < α := by simpa [Real.dist_eq] using hy
      simp [posPart, hz y hy']
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · have : posPart a =ᶠ[nhds x] a := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [posPart, show 0 < y from hy]
    exact (ha.contDiffAt).congr_of_eventuallyEq this

lemma negPart_contDiff {a : ℝ → ℂ} {α : ℝ} (hα : 0 < α) (hz : ∀ x, |x| < α → a x = 0) (ha : ContDiff ℝ 2 a) :
    ContDiff ℝ 2 (negPart a) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : negPart a =ᶠ[nhds x] a := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [negPart, show y < 0 from hy]
    exact (ha.contDiffAt).congr_of_eventuallyEq this
  · subst hx
    have : negPart a =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
      have : Metric.ball (0 : ℝ) α ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hα
      filter_upwards [this] with y hy
      have hy' : |y| < α := by simpa [Real.dist_eq] using hy
      simp [negPart, hz y hy']
    exact (contDiffAt_const).congr_of_eventuallyEq this
  · have : negPart a =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [negPart, not_lt.2 (le_of_lt (show 0 < y from hy))]
    exact (contDiffAt_const).congr_of_eventuallyEq this


lemma deriv_posPart {f : ℝ → ℂ} {α : ℝ} (hα : 0 < α) (hz : ∀ x, |x| < α → f x = 0) :
    deriv (posPart f) = posPart (deriv f) := by
  funext x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : posPart f =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [posPart, not_lt.2 (le_of_lt (show y < 0 from hy))]
    rw [this.deriv_eq]; simp [posPart, not_lt.2 hx.le]
  · subst hx
    have : posPart f =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
      have : Metric.ball (0 : ℝ) α ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hα
      filter_upwards [this] with y hy
      have hy' : |y| < α := by simpa [Real.dist_eq] using hy
      simp [posPart, hz y hy']
    rw [this.deriv_eq]; simp [posPart]
  · have : posPart f =ᶠ[nhds x] f := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [posPart, show 0 < y from hy]
    rw [this.deriv_eq]; simp [posPart, hx]

lemma deriv_negPart {f : ℝ → ℂ} {α : ℝ} (hα : 0 < α) (hz : ∀ x, |x| < α → f x = 0) :
    deriv (negPart f) = negPart (deriv f) := by
  funext x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have : negPart f =ᶠ[nhds x] f := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      simp [negPart, show y < 0 from hy]
    rw [this.deriv_eq]; simp [negPart, hx]
  · subst hx
    have : negPart f =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
      have : Metric.ball (0 : ℝ) α ∈ nhds (0 : ℝ) := Metric.ball_mem_nhds _ hα
      filter_upwards [this] with y hy
      have hy' : |y| < α := by simpa [Real.dist_eq] using hy
      simp [negPart, hz y hy']
    rw [this.deriv_eq]; simp [negPart]
  · have : negPart f =ᶠ[nhds x] fun _ => (0 : ℂ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      simp [negPart, not_lt.2 (le_of_lt (show 0 < y from hy))]
    rw [this.deriv_eq]; simp [negPart, not_lt.2 hx.le]

/-- A function vanishing on `(-α, α)` has a derivative vanishing there. -/
lemma deriv_zero_near {f : ℝ → ℂ} {α : ℝ} (hz : ∀ x, |x| < α → f x = 0) {x : ℝ} (hx : |x| < α) :
    deriv f x = 0 := by
  have : f =ᶠ[nhds x] fun _ => (0 : ℂ) := by
    have hm : Metric.ball x (α - |x|) ∈ nhds x := Metric.ball_mem_nhds _ (by linarith)
    filter_upwards [hm] with y hy
    apply hz
    have : |y - x| < α - |x| := by simpa [Real.dist_eq] using hy
    have := abs_sub_abs_le_abs_sub y x
    linarith [abs_nonneg (y - x)]
  rw [this.deriv_eq]; simp


/-- Reflection `y ↦ conj (a (-y))`. -/
noncomputable def reflA (a : ℝ → ℂ) (y : ℝ) : ℂ := star (a (-y))

lemma norm_oscInt_reflA (a0 : ℝ) (a : ℝ → ℂ) : ‖oscInt a0 (reflA a)‖ = ‖oscInt a0 a‖ := by
  unfold oscInt reflA
  have hrefl : ∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ)) =
      star (∫ y, star (a (-y)) * Complex.exp (Complex.I * ((a0 * y - Real.pi ^ 2 / 36 * y ^ 3 : ℝ) : ℂ))) := by
    rw [← integral_neg_eq_self, RCLike.star_def, ← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have hexp : Complex.exp (Complex.I * ((a0 * -y - Real.pi ^ 2 / 36 * (-y) ^ 3 : ℝ) : ℂ)) =
        (starRingEnd ℂ) (Complex.exp (Complex.I * ((a0 * y - Real.pi ^ 2 / 36 * y ^ 3 : ℝ) : ℂ))) := by
      rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
      congr 1
      push_cast
      ring
    simp only [map_mul, Complex.conj_conj, hexp]
  rw [hrefl, norm_star]

lemma reflA_contDiff {a : ℝ → ℂ} (ha : ContDiff ℝ 2 a) : ContDiff ℝ 2 (reflA a) :=
  (Complex.conjCLE.contDiff.comp (ha.comp contDiff_neg) : ContDiff ℝ 2 (fun y => Complex.conjCLE (a (-y))))

lemma deriv_reflA {a : ℝ → ℂ} (ha : Differentiable ℝ a) (y : ℝ) :
    deriv (reflA a) y = -star (deriv a (-y)) := mbt_deriv_reflect ha y

lemma norm_deriv_reflA {a : ℝ → ℂ} (ha : ContDiff ℝ 2 a) (y : ℝ) :
    ‖deriv (reflA a) y‖ = ‖deriv a (-y)‖ := by
  rw [deriv_reflA (ha.differentiable (by norm_num)), norm_neg, norm_star]

lemma norm_deriv2_reflA {a : ℝ → ℂ} (ha : ContDiff ℝ 2 a) (y : ℝ) :
    ‖deriv (deriv (reflA a)) y‖ = ‖deriv (deriv a) (-y)‖ := by
  have haD : Differentiable ℝ a := ha.differentiable (by norm_num)
  have hda : ContDiff ℝ 1 (deriv a) := ha.deriv'
  have hdaD : Differentiable ℝ (deriv a) := hda.differentiable (by norm_num)
  have hd1' : deriv (reflA a) = fun y => -star (deriv a (-y)) := funext (deriv_reflA haD)
  rw [hd1']
  have := mbt_deriv_reflect hdaD y
  have h3 : deriv (fun y => -star (deriv a (-y))) y = -deriv (fun y => star (deriv a (-y))) y := by
    rw [deriv.fun_neg]
  rw [h3, this, neg_neg, norm_star]

/-- **Split and reflect.** An amplitude `a ∈ C²` vanishing for `|x| < α` and for `|x| > β` splits as `b₊ + b₋'` with `b₊ = a` on
`(0, ∞)`, `b₋ = conj a(-·)` on `(0, ∞)`, both supported in `[α, β]`, and `‖osc a‖ ≤ ‖osc b₊‖ + ‖osc b₋‖`. -/
theorem split_refl {a : ℝ → ℂ} {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (ha : ContDiff ℝ 2 a)
    (hz : ∀ x, |x| < α → a x = 0) (hβ : ∀ x, β < |x| → a x = 0) (a0 : ℝ) :
    ∃ bp bm : ℝ → ℂ, ContDiff ℝ 2 bp ∧ ContDiff ℝ 2 bm ∧ (∀ x, x ∉ Set.Icc α β → bp x = 0) ∧
      (∀ x, x ∉ Set.Icc α β → bm x = 0) ∧
      (∀ x ∈ Set.Icc α β, ‖bp x‖ = ‖a x‖ ∧ ‖deriv bp x‖ = ‖deriv a x‖ ∧
        ‖deriv (deriv bp) x‖ = ‖deriv (deriv a) x‖) ∧
      (∀ x ∈ Set.Icc α β, ‖bm x‖ = ‖a (-x)‖ ∧ ‖deriv bm x‖ = ‖deriv a (-x)‖ ∧
        ‖deriv (deriv bm) x‖ = ‖deriv (deriv a) (-x)‖) ∧
      ‖oscInt a0 a‖ ≤ ‖oscInt a0 bp‖ + ‖oscInt a0 bm‖ := by
  have hα0 : (0 : ℝ) < α := hα
  set bp := posPart a with hbp
  set nm := negPart a with hnm
  have hpC : ContDiff ℝ 2 bp := posPart_contDiff hα hz ha
  have hnC : ContDiff ℝ 2 nm := negPart_contDiff hα hz ha
  have hda0 : ∀ x, |x| < α → deriv a x = 0 := fun x hx => deriv_zero_near hz hx
  have hdp : deriv bp = posPart (deriv a) := deriv_posPart hα hz
  have hdn : deriv nm = negPart (deriv a) := deriv_negPart hα hz
  have hddp : deriv (deriv bp) = posPart (deriv (deriv a)) := by rw [hdp]; exact deriv_posPart hα hda0
  have hddn : deriv (deriv nm) = negPart (deriv (deriv a)) := by rw [hdn]; exact deriv_negPart hα hda0
  have hzero : ∀ x, 0 < x → x ∉ Set.Icc α β → a x = 0 ∧ a (-x) = 0 := by
    intro x h0 hx
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact ⟨hz x (by rw [abs_of_pos h0]; exact hx), hz (-x) (by rw [abs_neg, abs_of_pos h0]; exact hx)⟩
    · exact ⟨hβ x (by rw [abs_of_pos h0]; exact hx), hβ (-x) (by rw [abs_neg, abs_of_pos h0]; exact hx)⟩
  have hbpz : ∀ x, x ∉ Set.Icc α β → bp x = 0 := by
    intro x hx
    simp only [hbp, posPart]
    split_ifs with h0
    · exact (hzero x h0 hx).1
    · rfl
  have hbmz : ∀ x, x ∉ Set.Icc α β → reflA nm x = 0 := by
    intro x hx
    simp only [reflA, hnm, negPart]
    split_ifs with h0
    · have h1 : 0 < x := by linarith
      rw [(hzero x h1 hx).2]; simp
    · simp
  have hIcc : ∀ x ∈ Set.Icc α β, 0 < x := fun x hx => lt_of_lt_of_le hα hx.1
  have hdecomp : ∀ x, a x = bp x + nm x := by
    intro x
    simp only [hbp, hnm, posPart, negPart]
    rcases lt_trichotomy x 0 with h | h | h
    · simp [not_lt.2 h.le, h]
    · subst h; simp [hz 0 (by simpa using hα)]
    · simp [h, not_lt.2 h.le]
  have hint : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → (∀ x, x ∉ Set.Icc (-β) β → f x = 0) →
      Integrable (fun x => f x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))) := by
    intro f hf hfz
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact hf.continuous.mul (by fun_prop)
    · refine HasCompactSupport.intro (isCompact_Icc (a := -β) (b := β)) (fun x hx => ?_)
      simp [hfz x hx]
  have hnz : ∀ x, x ∉ Set.Icc (-β) β → nm x = 0 := by
    intro x hx
    simp only [hnm, negPart]
    split_ifs with h0
    · apply hβ
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rw [abs_of_neg h0]
      rcases hx with hx | hx <;> linarith
    · rfl
  have hpz : ∀ x, x ∉ Set.Icc (-β) β → bp x = 0 := by
    intro x hx
    simp only [hbp, posPart]
    split_ifs with h0
    · apply hβ
      simp only [Set.mem_Icc, not_and_or, not_le] at hx
      rw [abs_of_pos h0]
      rcases hx with hx | hx <;> linarith
    · rfl
  have hI1 := hint bp hpC hpz
  have hI2 := hint nm hnC hnz
  refine ⟨bp, reflA nm, hpC, reflA_contDiff hnC, hbpz, hbmz, ?_, ?_, ?_⟩
  · intro x hx
    have h0 := hIcc x hx
    have e0 : bp x = a x := by simp [hbp, posPart, h0]
    have e1 : deriv bp x = deriv a x := by rw [hdp]; simp [posPart, h0]
    have e2 : deriv (deriv bp) x = deriv (deriv a) x := by rw [hddp]; simp [posPart, h0]
    rw [e0, e1, e2]; exact ⟨rfl, rfl, rfl⟩
  · intro x hx
    have h0 : -x < 0 := by linarith [hIcc x hx]
    refine ⟨?_, ?_, ?_⟩
    · simp [reflA, hnm, negPart, h0]
    · rw [norm_deriv_reflA hnC, hdn]; simp [negPart, h0]
    · rw [norm_deriv2_reflA hnC, hddn]; simp [negPart, h0]
  · have hsum : oscInt a0 a = oscInt a0 bp + oscInt a0 nm := by
      unfold oscInt
      rw [← integral_add hI1 hI2]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show a x * _ = bp x * _ + nm x * _
      rw [hdecomp x]; ring
    rw [hsum, norm_oscInt_reflA a0 nm]
    exact norm_add_le _ _


/-- Two-sided form of `cubic_two_ibp_gen`: `a ∈ C²` vanishing for `|x| < α` and `|x| > β`, `|a^{(r)}(x)| ≤ B |x|^{-s-r}` and
`|ψ'(x)| ≥ q x²` for `α ≤ |x| ≤ β`. -/
theorem ibp_gen_sym {a : ℝ → ℂ} {a0 α β B q s : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hB : 0 ≤ B)
    (hq : 0 < q) (hs : -5 < s) (ha : ContDiff ℝ 2 a)
    (hz : ∀ x, |x| < α → a x = 0) (hβ : ∀ x, β < |x| → a x = 0)
    (hb0 : ∀ x, α ≤ |x| → |x| ≤ β → ‖a x‖ ≤ B * |x| ^ (-s))
    (hb1 : ∀ x, α ≤ |x| → |x| ≤ β → ‖deriv a x‖ ≤ B * |x| ^ (-s - 1))
    (hb2 : ∀ x, α ≤ |x| → |x| ≤ β → ‖deriv (deriv a) x‖ ≤ B * |x| ^ (-s - 2))
    (hp : ∀ x, α ≤ |x| → |x| ≤ β → q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|) :
    ‖oscInt a0 a‖ ≤ 2 * (B * cubicC q * (α ^ (-(s + 5)) / (s + 5))) := by
  obtain ⟨bp, bm, hpC, hmC, hpz, hmz, hpn, hmn, hsum⟩ := split_refl hα hαβ ha hz hβ a0
  have hmem : ∀ x ∈ Set.Icc α β, α ≤ |x| ∧ |x| ≤ β ∧ |-x| = |x| ∧ x = |x| := by
    intro x hx
    have h0 : 0 < x := lt_of_lt_of_le hα hx.1
    rw [abs_of_pos h0]
    exact ⟨hx.1, hx.2, by rw [abs_neg, abs_of_pos h0], rfl⟩
  have h1 := cubic_two_ibp_gen (a := bp) (a0 := a0) hα hαβ hB hq hs hpC hpz
    (fun x hx => by
      obtain ⟨h1, h2, -, h4⟩ := hmem x hx
      rw [(hpn x hx).1]; have := hb0 x h1 h2; rwa [← h4] at this)
    (fun x hx => by
      obtain ⟨h1, h2, -, h4⟩ := hmem x hx
      rw [(hpn x hx).2.1]; have := hb1 x h1 h2; rwa [← h4] at this)
    (fun x hx => by
      obtain ⟨h1, h2, -, h4⟩ := hmem x hx
      rw [(hpn x hx).2.2]; have := hb2 x h1 h2; rwa [← h4] at this)
    (fun x hx => by
      obtain ⟨h1, h2, -, -⟩ := hmem x hx
      have := hp x h1 h2
      simpa using this)
  have h2 := cubic_two_ibp_gen (a := bm) (a0 := a0) hα hαβ hB hq hs hmC hmz
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4⟩ := hmem x hx
      rw [(hmn x hx).1]; have := hb0 (-x) (by rw [h3]; exact h1) (by rw [h3]; exact h2)
      rwa [h3, ← h4] at this)
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4⟩ := hmem x hx
      rw [(hmn x hx).2.1]; have := hb1 (-x) (by rw [h3]; exact h1) (by rw [h3]; exact h2)
      rwa [h3, ← h4] at this)
    (fun x hx => by
      obtain ⟨h1, h2, h3, h4⟩ := hmem x hx
      rw [(hmn x hx).2.2]; have := hb2 (-x) (by rw [h3]; exact h1) (by rw [h3]; exact h2)
      rwa [h3, ← h4] at this)
    (fun x hx => by
      obtain ⟨h1, h2, -, -⟩ := hmem x hx
      have := hp x h1 h2
      simpa using this)
  unfold oscInt at hsum h1 h2 ⊢
  linarith


lemma oscInt_eq_interval {b : ℝ → ℂ} {α β : ℝ} (hαβ : α ≤ β) (a0 : ℝ) (hb : ∀ x, x ∉ Set.Icc α β → b x = 0) :
    oscInt a0 b = ∫ x in α..β, b x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ)) := by
  unfold oscInt
  rw [intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by simp [hb x hx])).symm

/-- Two-sided van der Corput bound (second-derivative test) for `ψ' ` monotone on each half-line: `a ∈ C²` vanishing for
`|x| < α`, `|x| > β`, `|a| ≤ M`, `|a'(x)| ≤ d(|x|)` with `∫_α^β d ≤ V`. -/
theorem vdc_sym {a : ℝ → ℂ} {a0 α β M V : ℝ} {d : ℝ → ℝ} (hα : 0 < α) (hαβ : α ≤ β) (ha : ContDiff ℝ 2 a)
    (hz : ∀ x, |x| < α → a x = 0) (hβ : ∀ x, β < |x| → a x = 0)
    (hM : ∀ x, ‖a x‖ ≤ M) (hd : ∀ x, α ≤ |x| → |x| ≤ β → ‖deriv a x‖ ≤ d |x|)
    (hdi : IntegrableOn d (Set.Icc α β)) (hV : ∫ x in Set.Icc α β, d x ≤ V) :
    ‖oscInt a0 a‖ ≤ 2 * (8 * (M + V) / Real.sqrt (Real.pi ^ 2 * α / 6)) := by
  obtain ⟨bp, bm, hpC, hmC, hpz, hmz, hpn, hmn, hsum⟩ := split_refl hα hαβ ha hz hβ a0
  have hmem : ∀ x ∈ Set.Icc α β, α ≤ |x| ∧ |x| ≤ β ∧ |-x| = |x| ∧ x = |x| := by
    intro x hx
    have h0 : 0 < x := lt_of_lt_of_le hα hx.1
    rw [abs_of_pos h0]
    exact ⟨hx.1, hx.2, by rw [abs_neg, abs_of_pos h0], rfl⟩
  have hVn : ∀ {f : ℝ → ℂ}, ContDiff ℝ 2 f → (∀ x ∈ Set.Icc α β, ‖deriv f x‖ ≤ d x) →
      ∫ x in Set.Icc α β, ‖deriv f x‖ ≤ V := by
    intro f hf hfd
    have hcont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
    have hi : IntegrableOn (fun x => ‖deriv f x‖) (Set.Icc α β) := hcont.norm.integrableOn_Icc
    exact (setIntegral_mono_on hi hdi measurableSet_Icc hfd).trans hV
  have h1 := cubic_vdc_pos (a0 := a0) (M := M) (V := V) hα hαβ (h := bp) (hpC.of_le (by norm_num))
    (fun x hx => by rw [(hpn x hx).1]; exact hM x)
    (hVn hpC (fun x hx => by
      obtain ⟨h1, h2, -, h4⟩ := hmem x hx
      rw [(hpn x hx).2.1]; have := hd x h1 h2; rwa [← h4] at this))
  have h2 := cubic_vdc_pos (a0 := a0) (M := M) (V := V) hα hαβ (h := bm) (hmC.of_le (by norm_num))
    (fun x hx => by rw [(hmn x hx).1]; exact hM _)
    (hVn hmC (fun x hx => by
      obtain ⟨h1, h2, h3, h4⟩ := hmem x hx
      rw [(hmn x hx).2.1]; have := hd (-x) (by rw [h3]; exact h1) (by rw [h3]; exact h2)
      rwa [h3, ← h4] at this))
  rw [← oscInt_eq_interval hαβ a0 hpz] at h1
  rw [← oscInt_eq_interval hαβ a0 hmz] at h2
  linarith

end FormalResearch.SignUncertainty

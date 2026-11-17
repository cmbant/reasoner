module

public import FormalResearch.Special.LatticeSumII

/-!
# `lem:latticesum` (ii), abstract form

`‖∑_{x∈S} φ(x) - ∫_{-X}^{X} φ(s) t₀'(s) ds‖ ≤ (1+2ε) C_φ e^{-κX} + 2ε C_φ'/κ + B_{(i)}(φ')`,
with `φ' = deriv φ`, `C_φ' = C_φ e^{κr₀}/r₀` (Cauchy), `B_{(i)}` the bound of `latticeI_bound` for `φ'`
on the strip `|Im s| ≤ y₀ - r₀`.  See `LatticeSumII` for the structure of the argument.
-/

@[expose] public section

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma LevelData.mono_strip {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (h : LevelData τ0 X y0 m M K ε t S) {y1 : ℝ} (hy1 : 0 < y1) (hle : y1 ≤ y0) :
    LevelData τ0 X y1 m M K ε t S where
  cal := h.cal.mono hy1 hle
  eps := h.eps
  cont := h.cont
  mono := h.mono
  close := h.close
  mem := h.mem

end FormalResearch.Special.Lattice

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

/-- The exact identity behind (ii): the sum minus the smooth integral, with explicit boundary
coefficients and the two correction integrals. -/
theorem sum_minus_integral_identity {X : ℝ} (hX : 0 < X) {S : Finset ℝ} {t t0 t0' : ℝ → ℝ}
    (hcount : ∀ s ∈ Icc (-X) X,
      (((S.filter (fun x => x ≤ s)).card : ℕ) : ℤ) = ⌊t s⌋ - ⌈t (-X)⌉ + 1)
    (hS : ∀ x ∈ S, x ∈ Icc (-X) X) {Φ Φ' : ℝ → ℂ} (hΦc : Continuous Φ)
    (hΦd : ∀ s ∈ Icc (-X) X, HasDerivAt Φ (Φ' s) s) (hΦ'c : ContinuousOn Φ' (Icc (-X) X))
    (ht0 : ∀ s ∈ Icc (-X) X, HasDerivAt t0 (t0' s) s) (ht0'c : ContinuousOn t0' (Icc (-X) X))
    (htc : Continuous t)
    (hfr : IntervalIntegrable (fun s => Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ)) volume (-X) X) :
    ∑ x ∈ S, Φ x - ∫ s in (-X)..X, Φ s * (t0' s : ℂ) =
      Φ X * ((⌊t X⌋ - t0 X + 1 / 2 : ℝ) : ℂ) + Φ (-X) * ((1 / 2 - ⌈t (-X)⌉ + t0 (-X) : ℝ) : ℂ)
      - (∫ s in (-X)..X, Φ' s * ((t s - t0 s : ℝ) : ℂ)) +
      ∫ s in (-X)..X, Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ) := by
  have hle : -X ≤ X := by linarith
  have hsbp := sum_by_parts hS hΦc hΦd hΦ'c hX.le
  have ht0c : ContinuousOn t0 (Icc (-X) X) := fun s hs => (ht0 s hs).continuousAt.continuousWithinAt
  have iΦ' : IntervalIntegrable Φ' volume (-X) X := hΦ'c.intervalIntegrable_of_Icc hle
  have iΦt0' : IntervalIntegrable (fun s => Φ s * (t0' s : ℂ)) volume (-X) X :=
    (hΦc.continuousOn.mul (Complex.continuous_ofReal.comp_continuousOn ht0'c)).intervalIntegrable_of_Icc hle
  have iA1 : IntervalIntegrable (fun s => Φ' s * (t0 s : ℂ)) volume (-X) X :=
    (hΦ'c.mul (Complex.continuous_ofReal.comp_continuousOn ht0c)).intervalIntegrable_of_Icc hle
  have iA2 : IntervalIntegrable (fun s => Φ' s * ((t s - t0 s : ℝ) : ℂ)) volume (-X) X :=
    (hΦ'c.mul (Complex.continuous_ofReal.comp_continuousOn
      (htc.continuousOn.sub ht0c))).intervalIntegrable_of_Icc hle
  -- IBP for A1
  have hibp : ∫ s in (-X)..X, (t0 s : ℂ) * Φ' s =
      (t0 X : ℂ) * Φ X - (t0 (-X) : ℂ) * Φ (-X) - ∫ s in (-X)..X, (t0' s : ℂ) * Φ s := by
    refine intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := fun s => (t0 s : ℂ))
      (u' := fun s => (t0' s : ℂ)) (v := Φ) (v' := Φ') ?_ ?_ ?_ iΦ'
    · intro s hs; rw [uIcc_of_le hle] at hs; exact (ht0 s hs).ofReal_comp
    · intro s hs; rw [uIcc_of_le hle] at hs; exact hΦd s hs
    · exact (Complex.continuous_ofReal.comp_continuousOn ht0'c).intervalIntegrable_of_Icc hle
  -- the counting function decomposes
  set c : ℤ := ⌈t (-X)⌉ with hc
  have hdec : ∀ s ∈ uIcc (-X) X, Φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) =
      Φ' s * (t0 s : ℂ) + Φ' s * ((t s - t0 s : ℝ) : ℂ) -
        Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ) + ((1 / 2 - c : ℝ) : ℂ) * Φ' s := by
    intro s hs
    rw [uIcc_of_le hle] at hs
    have h1 := hcount s hs
    have h2 : (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) = ((⌊t s⌋ - c + 1 : ℤ) : ℂ) := by
      rw [← h1]; norm_cast
    rw [h2]
    have h3 : (⌊t s⌋ : ℝ) = t s - Int.fract (t s) := by
      rw [Int.fract]; ring
    have h4 : ((⌊t s⌋ : ℤ) : ℂ) = ((t s - Int.fract (t s) : ℝ) : ℂ) := by
      rw [← h3]; norm_cast
    push_cast at h4 ⊢
    rw [h4]
    ring
  have hN : ∫ s in (-X)..X, Φ' s * (((S.filter (fun x => x ≤ s)).card : ℕ) : ℂ) =
      (∫ s in (-X)..X, Φ' s * (t0 s : ℂ)) + (∫ s in (-X)..X, Φ' s * ((t s - t0 s : ℝ) : ℂ)) -
        (∫ s in (-X)..X, Φ' s * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ)) +
        ((1 / 2 - c : ℝ) : ℂ) * (Φ X - Φ (-X)) := by
    rw [intervalIntegral.integral_congr hdec]
    rw [intervalIntegral.integral_add ((iA1.add iA2).sub hfr) (iΦ'.const_mul _),
      intervalIntegral.integral_sub (iA1.add iA2) hfr, intervalIntegral.integral_add iA1 iA2,
      intervalIntegral.integral_const_mul]
    have hF : ∫ s in (-X)..X, Φ' s = Φ X - Φ (-X) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => by
        rw [uIcc_of_le hle] at hs; exact hΦd s hs) iΦ'
    rw [hF]
  have hA1 : ∫ s in (-X)..X, Φ' s * (t0 s : ℂ) =
      (t0 X : ℂ) * Φ X - (t0 (-X) : ℂ) * Φ (-X) - ∫ s in (-X)..X, Φ s * (t0' s : ℂ) := by
    have e1 : (fun s => Φ' s * (t0 s : ℂ)) = fun s => (t0 s : ℂ) * Φ' s := by ext s; ring
    have e2 : (fun s => Φ s * (t0' s : ℂ)) = fun s => (t0' s : ℂ) * Φ s := by ext s; ring
    rw [e1, e2]; exact hibp
  have hcardX : ((S.card : ℕ) : ℂ) = ((⌊t X⌋ - c + 1 : ℤ) : ℂ) := by
    have h1 := hcount X ⟨hle, le_rfl⟩
    have : S.filter (fun x => x ≤ X) = S := by
      ext x; simp only [Finset.mem_filter, and_iff_left_iff_imp]; intro hx; exact (hS x hx).2
    rw [this] at h1
    rw [← h1]; norm_cast
  rw [hsbp, hN, hA1, hcardX]
  push_cast
  ring

end FormalResearch.Special.Lattice

namespace FormalResearch.Special.Lattice

open Filter Topology Set Complex MeasureTheory intervalIntegral

lemma intervalIntegrable_mul_fract {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℂ} {C : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hC : ∀ s ∈ Icc a b, ‖g s‖ ≤ C) {t : ℝ → ℝ} (ht : Continuous t) :
    IntervalIntegrable (fun s => g s * (((Int.fract (t s) - 1 / 2 : ℝ)) : ℂ)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hm : AEStronglyMeasurable (fun s : ℝ => g s * (((Int.fract (t s) - 1 / 2 : ℝ)) : ℂ))
      (volume.restrict (Icc a b)) := by
    refine (hg.aestronglyMeasurable measurableSet_Icc).mul ?_
    refine (Complex.measurable_ofReal.comp_aemeasurable ?_).aestronglyMeasurable
    exact (measurable_fract.comp ht.measurable).aemeasurable.sub_const (1 / 2 : ℝ)
  show Integrable _ (volume.restrict (Icc a b))
  refine Integrable.of_bound hm (C * (1 / 2)) ?_
  refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall (fun s hs => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : |Int.fract (t s) - 1 / 2| ≤ 1 / 2 := by
    have := Int.fract_nonneg (t s); have := Int.fract_lt_one (t s)
    rw [abs_le]; constructor <;> linarith
  have h0 : 0 ≤ C := (norm_nonneg _).trans (hC s hs)
  exact mul_le_mul (hC s hs) h1 (abs_nonneg _) h0

/-- **`lem:latticesum` (ii)**, abstract form (explicit constants). -/
theorem latticeII_bound {τ0 : ℂ → ℂ} {X y0 m M K ε : ℝ} {t : ℝ → ℝ} {S : Finset ℝ}
    (hd : LevelData τ0 X y0 m M K ε t S) {φ : ℂ → ℂ} {Cφ κ y1 r r0 : ℝ} (hκ : 0 < κ)
    (hCφ : 0 ≤ Cφ) (hy1 : 0 < y1) (hr : 0 < r) (hr0 : 0 < r0) (hyr : y1 + r + r0 ≤ y0)
    (hφd : DifferentiableOn ℂ φ {s | |s.im| ≤ y0})
    (hφb : ∀ s : ℂ, |s.im| ≤ y0 → ‖φ s‖ ≤ Cφ * Real.exp (-κ * |s.re|)) :
    ‖∑ x ∈ S, φ (x : ℂ) - ∫ s in (-X)..X, φ (s : ℂ) * ((CalPhase.realDeriv τ0 s : ℝ) : ℂ)‖ ≤
      (1 / 2 + ε) * (2 * (Cφ * Real.exp (-κ * X))) +
      ε * (Cφ * Real.exp (κ * r0) / r0 * (2 / κ)) +
      (Cφ * Real.exp (κ * r0) / r0 * wconst κ * ε * (1 + 4 * (M + 2 * ε + 1) / m) +
        (Cφ * Real.exp (κ * r0) / r0 * Real.exp (-κ * X) / m +
          1 / 12 * (2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K * y1 * Real.exp (-κ * X) +
            2 * smoothCw (Cφ * Real.exp (κ * r0) / r0) κ r m K / κ *
              Real.exp (-(2 * Real.pi * m * y1))))) := by
  have h := hd.cal
  have hX := h.hX
  have hy0 : 0 < y0 := h.hy0
  have hm := h.hm
  have hle : -X ≤ X := by linarith
  set Cφ' : ℝ := Cφ * Real.exp (κ * r0) / r0 with hCφ'
  have hCφ'0 : 0 ≤ Cφ' := by positivity
  have hy0' : y0 - r0 ≤ y0 := by linarith
  have hy0'pos : 0 < y0 - r0 := by linarith
  have hsub : Icc (-X) X ⊆ Icc (-(X + 1)) (X + 1) := Icc_subset_Icc (by linarith) (by linarith)
  have hwin : ∀ s : ℝ, s ∈ Icc (-X) X → InWin X y0 (s : ℂ) := fun s hs =>
    CalPhase.inWin_real (by have := abs_le.mpr hs; linarith) hy0.le
  -- analyticity of φ at real points and on the smaller strip
  have hanaφ : ∀ z : ℂ, |z.im| ≤ y0 - r0 → AnalyticAt ℂ φ z := fun z hz =>
    hφd.analyticAt (strip_mem_nhds hr0 (by linarith : (y0 - r0) + r0 ≤ y0) hz)
  have hφ'b : ∀ s : ℂ, |s.im| ≤ y0 - r0 → ‖deriv φ s‖ ≤ Cφ' * Real.exp (-κ * |s.re|) := fun s hs => by
    have := norm_deriv_strip_le hr0 hκ.le hCφ hφd hφb (z := s) (by linarith)
    refine this.trans (le_of_eq ?_)
    rw [hCφ']; ring
  have hφ'd : DifferentiableOn ℂ (deriv φ) {s | |s.im| ≤ y0 - r0} := fun s hs =>
    (hanaφ s hs).deriv.differentiableAt.differentiableWithinAt
  have hφc : Continuous (fun s : ℝ => φ (s : ℂ)) := continuous_real_of_strip hy0 hφd
  have hφr : ∀ s : ℝ, ‖φ (s : ℂ)‖ ≤ Cφ * Real.exp (-κ * |s|) := fun s => by
    have := hφb (s : ℂ) (by simpa using hy0.le)
    simpa using this
  have hφ'r : ∀ s : ℝ, ‖deriv φ (s : ℂ)‖ ≤ Cφ' * Real.exp (-κ * |s|) := fun s => by
    have := hφ'b (s : ℂ) (by simpa using hy0'pos.le)
    simpa using this
  have hΦd : ∀ s ∈ Icc (-X) X, HasDerivAt (fun s : ℝ => φ (s : ℂ)) (deriv φ (s : ℂ)) s := fun s hs =>
    (hφd.differentiableAt (strip_mem_nhds hr0 (by linarith : (y0 - r0) + r0 ≤ y0)
      (by simpa using hy0'pos.le))).hasDerivAt.comp_ofReal
  have hΦ'c : ContinuousOn (fun s : ℝ => deriv φ (s : ℂ)) (Icc (-X) X) := fun s _ =>
    (((hanaφ (s : ℂ) (by simpa using hy0'pos.le)).deriv.continuousAt).comp (f := fun s : ℝ => (s : ℂ))
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have ht0 : ∀ s ∈ Icc (-X) X, HasDerivAt (realPhase τ0) (CalPhase.realDeriv τ0 s) s := fun s hs =>
    h.hasDerivAt_real (by have := abs_le.mpr hs; linarith)
  have ht0'c : ContinuousOn (CalPhase.realDeriv τ0) (Icc (-X) X) := h.continuousOn_deriv_re.mono hsub
  have hfr : IntervalIntegrable (fun s : ℝ => deriv φ (s : ℂ) *
      ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ)) volume (-X) X :=
    intervalIntegrable_mul_fract hle hΦ'c (C := Cφ') (fun s _ => (hφ'r s).trans (by
      have : Real.exp (-κ * |s|) ≤ 1 := by rw [Real.exp_le_one_iff]; nlinarith [abs_nonneg s]
      nlinarith)) hd.cont
  have hid := sum_minus_integral_identity hX (S := S) (t := t) (t0 := realPhase τ0)
    (t0' := CalPhase.realDeriv τ0)
    (fun s hs => hd.card_le_eq hs) (fun x hx => ((hd.mem x).mp hx).1) hφc hΦd hΦ'c ht0 ht0'c hd.cont hfr
  rw [hid]
  -- bounds on the four pieces
  have b1 : ‖φ (X : ℂ) * (((⌊t X⌋ : ℝ) - realPhase τ0 X + 1 / 2 : ℝ) : ℂ)‖ ≤
      (1 / 2 + ε) * (Cφ * Real.exp (-κ * X)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hc := abs_le.mp (hd.close X (by rw [abs_of_pos hX]; linarith))
    have hf := Int.fract_nonneg (t X); have hf1 := Int.fract_lt_one (t X)
    have hfl : (⌊t X⌋ : ℝ) = t X - Int.fract (t X) := by rw [Int.fract]; ring
    have : |(⌊t X⌋ : ℝ) - realPhase τ0 X + 1 / 2| ≤ 1 / 2 + ε := by
      rw [hfl, abs_le]; constructor <;> linarith [hc.1, hc.2]
    have h2 := hφr X
    rw [abs_of_pos hX] at h2
    calc _ ≤ (Cφ * Real.exp (-κ * X)) * (1 / 2 + ε) := mul_le_mul h2 this (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have b2 : ‖φ ((-X : ℝ) : ℂ) * (((1 / 2 - (⌈t (-X)⌉ : ℝ) + realPhase τ0 (-X) : ℝ)) : ℂ)‖ ≤
      (1 / 2 + ε) * (Cφ * Real.exp (-κ * X)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hc := abs_le.mp (hd.close (-X) (by rw [abs_neg, abs_of_pos hX]; linarith))
    have hc1 := Int.le_ceil (t (-X))
    have hc2 := Int.ceil_lt_add_one (t (-X))
    have : |1 / 2 - (⌈t (-X)⌉ : ℝ) + realPhase τ0 (-X)| ≤ 1 / 2 + ε := by
      rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
    have h2 := hφr (-X)
    rw [abs_neg, abs_of_pos hX] at h2
    calc _ ≤ (Cφ * Real.exp (-κ * X)) * (1 / 2 + ε) := mul_le_mul h2 this (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have b3 : ‖∫ s in (-X)..X, deriv φ (s : ℂ) * ((t s - realPhase τ0 s : ℝ) : ℂ)‖ ≤
      ε * (Cφ' * (2 / κ)) := by
    have hg : IntervalIntegrable (fun s : ℝ => Cφ' * ε * Real.exp (-κ * |s|)) volume (-X) X :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have h1 := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (a := -X) (b := X)
      (f := fun s : ℝ => deriv φ (s : ℂ) * ((t s - realPhase τ0 s : ℝ) : ℂ))
      (g := fun s : ℝ => Cφ' * ε * Real.exp (-κ * |s|)) hle
      (Filter.Eventually.of_forall (fun s hs => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hs' : |s| ≤ X + 1 := by
          rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
        have hc := hd.close s hs'
        calc ‖deriv φ (s : ℂ)‖ * |t s - realPhase τ0 s| ≤ (Cφ' * Real.exp (-κ * |s|)) * ε :=
              mul_le_mul (hφ'r s) hc (abs_nonneg _) (by positivity)
          _ = _ := by ring)) hg
    refine h1.trans ?_
    rw [intervalIntegral.integral_const_mul]
    have := integral_exp_neg_abs_le hκ hX.le
    have hn : 0 ≤ Cφ' * ε := mul_nonneg hCφ'0 hd.eps
    calc Cφ' * ε * ∫ x in (-X)..X, Real.exp (-κ * |x|) ≤ Cφ' * ε * (2 / κ) :=
          mul_le_mul_of_nonneg_left this hn
      _ = _ := by ring
  have b4 := latticeI_bound (hd.mono_strip hy0'pos hy0') (φ := deriv φ) (Cφ := Cφ') (κ := κ)
    (y1 := y1) (r := r) hκ hCφ'0 hy1 hr (by linarith) hφ'd hφ'b
  have hsum := norm_add_le
    (φ (X : ℂ) * (((⌊t X⌋ : ℝ) - realPhase τ0 X + 1 / 2 : ℝ) : ℂ) +
      φ ((-X : ℝ) : ℂ) * (((1 / 2 - (⌈t (-X)⌉ : ℝ) + realPhase τ0 (-X) : ℝ)) : ℂ) -
        ∫ s in (-X)..X, deriv φ (s : ℂ) * ((t s - realPhase τ0 s : ℝ) : ℂ))
    (∫ s in (-X)..X, deriv φ (s : ℂ) * ((Int.fract (t s) - 1 / 2 : ℝ) : ℂ))
  have hs2 := norm_sub_le
    (φ (X : ℂ) * (((⌊t X⌋ : ℝ) - realPhase τ0 X + 1 / 2 : ℝ) : ℂ) +
      φ ((-X : ℝ) : ℂ) * (((1 / 2 - (⌈t (-X)⌉ : ℝ) + realPhase τ0 (-X) : ℝ)) : ℂ))
    (∫ s in (-X)..X, deriv φ (s : ℂ) * ((t s - realPhase τ0 s : ℝ) : ℂ))
  have hs3 := norm_add_le (φ (X : ℂ) * (((⌊t X⌋ : ℝ) - realPhase τ0 X + 1 / 2 : ℝ) : ℂ))
    (φ ((-X : ℝ) : ℂ) * (((1 / 2 - (⌈t (-X)⌉ : ℝ) + realPhase τ0 (-X) : ℝ)) : ℂ))
  push_cast at *
  linarith

end FormalResearch.Special.Lattice

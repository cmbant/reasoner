module

public import FormalResearch.ModularBootstrap.FiveTerm.VirasoroG3XbLocal

/-!
# The third-order strip identity for `Ψ̂` (FIVE-0b)

For `F(s) = (Ψ̃(s) - p(s))/sin²(πs)` with the comparison function `p` of `VirasoroG3XbLocal`, `F` is holomorphic
on `0 < Re s < 1`, continuous off the corners and bounded by `C e^{-π|Im s|/2}`; Cauchy on the strip
(`strip_edge_cauchy`) gives `∫_ℝ (x_A + v_A - 2π sech πτ + √2 sech(πτ/2) + 2P₁ cosh πτ - P₂ sinh πτ sinh(πτ/2))
/ sinh²(πτ) dτ = 0`.  Proved.
-/

@[expose] public section

open Complex Filter Topology Metric Set MeasureTheory
open scoped Real

namespace FormalResearch.ModularBootstrap.FiveTerm

/-- `F(s) = (Ψ̃(s) - p(s)) / sin²(πs)`. -/
noncomputable def Fq (s : ℂ) : ℂ := (psiTil s - pG s) / Complex.sin ((π : ℂ) * s) ^ 2

lemma sin_pi_mul_ne_zero {s : ℂ} (hs : s ∈ unitStripCl \ {0, 1}) : Complex.sin ((π : ℂ) * s) ≠ 0 := by
  intro h
  obtain ⟨⟨h0, h1⟩, hne⟩ := hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs' : s = (k : ℂ) := by
    have : (π : ℂ) * s = (π : ℂ) * (k : ℂ) := by rw [hk]; ring
    exact mul_left_cancel₀ hpi this
  have hre : s.re = (k : ℝ) := by rw [hs']; simp
  have hk0 : (0 : ℤ) ≤ k := by
    have : (0 : ℝ) ≤ k := by rw [← hre]; exact h0
    exact_mod_cast this
  have hk1 : k ≤ (1 : ℤ) := by
    have : (k : ℝ) ≤ 1 := by rw [← hre]; exact h1
    exact_mod_cast this
  have : k = 0 ∨ k = 1 := by omega
  rcases this with h | h
  · apply hne.1; rw [hs', h]; simp
  · apply hne.2; rw [hs', h]; simp

lemma sin_pi_mul_ne_zero_strip {s : ℂ} (hs : s ∈ unitStrip) : Complex.sin ((π : ℂ) * s) ≠ 0 := by
  refine sin_pi_mul_ne_zero ⟨unitStrip_subset_cl hs, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
  constructor
  · intro h; rw [h] at hs; simp [unitStrip] at hs
  · intro h; rw [h] at hs; simp [unitStrip] at hs

lemma differentiableOn_Fq : DifferentiableOn ℂ Fq unitStrip := by
  intro s hs
  have h1 : DifferentiableAt ℂ psiHat s := differentiableOn_psiHat.differentiableAt (isOpen_unitStrip.mem_nhds hs)
  have h2 : DifferentiableAt ℂ pG s := (differentiable_pC _ _ _) s
  have h3 : DifferentiableAt ℂ (fun s : ℂ => Complex.sin ((π : ℂ) * s)) s :=
    (sin_pi_mul_hasDerivAt s).differentiableAt
  have hFq : Fq =ᶠ[𝓝 s] fun s => (psiHat s - pG s) / Complex.sin ((π : ℂ) * s) ^ 2 := by
    filter_upwards [isOpen_unitStrip.mem_nhds hs] with t ht
    unfold Fq; rw [psiTil_of_mem ht]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hFq
  exact (h1.sub h2).div (h3.pow 2) (pow_ne_zero 2 (sin_pi_mul_ne_zero_strip hs))

lemma continuousOn_Fq : ContinuousOn Fq (unitStripCl \ {0, 1}) := by
  have h1 : ContinuousOn (fun s => psiTil s - pG s) (unitStripCl \ {0, 1}) :=
    continuousOn_psiTil.sub (differentiable_pC _ _ _).continuous.continuousOn
  have h3 : ContinuousOn (fun s : ℂ => Complex.sin ((π : ℂ) * s) ^ 2) (unitStripCl \ {0, 1}) := by
    have : Continuous (fun s : ℂ => Complex.sin ((π : ℂ) * s) ^ 2) := by fun_prop
    exact this.continuousOn
  exact h1.div h3 (fun s hs => pow_ne_zero 2 (sin_pi_mul_ne_zero hs))

lemma cosh_le_exp_self {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

lemma sin_pi_mul_eq (s : ℂ) : Complex.sin ((π : ℂ) * s) = cC (1 / 2 - s) := by
  unfold cC
  rw [show (π : ℂ) * (1 / 2 - s) = (π : ℂ) / 2 - (π : ℂ) * s by ring, Complex.cos_pi_div_two_sub]

lemma sin_pi_half_eq (s : ℂ) : Complex.sin ((π : ℂ) * s / 2) = cC ((1 - s) / 2) := by
  unfold cC
  rw [show (π : ℂ) * ((1 - s) / 2) = (π : ℂ) / 2 - (π : ℂ) * s / 2 by ring, Complex.cos_pi_div_two_sub]

/-- Decay of `F` far from the real axis. -/
lemma Fq_far : ∃ C : ℝ, ∀ s ∈ unitStrip, 1 ≤ |s.im| → ‖Fq s‖ ≤ C * Real.exp (-(π / 2 * |s.im|)) := by
  obtain ⟨C0, hC0⟩ := psiHat_bound
  have hpi := Real.pi_pos
  set P0 : ℝ := (Psi0v + Psi1v) / 2 with hP0
  set P1 : ℝ := (Psi0v - Psi1v) / 2 with hP1
  refine ⟨16 * (|C0| + (|P0| + |P1| + |cP2|)), fun s hs hy => ?_⟩
  set y : ℝ := |s.im| with hy'
  set u : ℝ := Real.exp (π * y / 2) with hu
  have hy0 : 0 ≤ y := abs_nonneg _
  have hu1 : 1 ≤ u := Real.one_le_exp (by positivity)
  have hupos : 0 < u := by linarith
  have e1 : Real.exp (π * y) = u ^ 2 := by
    rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e3 : Real.exp (3 * π * y / 2) = u ^ 3 := by
    rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e4 : Real.exp (2 * π * y) = u ^ 4 := by
    rw [hu, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have e5 : Real.exp (-(π / 2 * y)) = u⁻¹ := by
    rw [hu, ← Real.exp_neg]; congr 1; ring
  -- norm of Ψ̃
  have hΨ : ‖psiTil s‖ ≤ C0 * u⁻¹ := by
    rw [psiTil_of_mem hs]
    have := hC0 s hs
    rwa [e5] at this
  -- norm of p
  have hcos : ‖Complex.cos ((π : ℂ) * s)‖ ≤ u ^ 2 := by
    have h1 : ‖cC s‖ ≤ Real.cosh (π * |s.im|) := norm_cC_le
    have h2 : Real.cosh (π * y) ≤ Real.exp (π * y) := cosh_le_exp_self (by positivity)
    calc ‖Complex.cos ((π : ℂ) * s)‖ = ‖cC s‖ := rfl
      _ ≤ _ := h1
      _ ≤ _ := h2
      _ = u ^ 2 := e1
  have hsin : ‖Complex.sin ((π : ℂ) * s)‖ ≤ u ^ 2 := by
    rw [sin_pi_mul_eq]
    have h1 : ‖cC (1 / 2 - s)‖ ≤ Real.cosh (π * |(1 / 2 - s).im|) := norm_cC_le
    have him : |(1 / 2 - s : ℂ).im| = y := by simp [hy']
    rw [him] at h1
    have h2 : Real.cosh (π * y) ≤ Real.exp (π * y) := cosh_le_exp_self (by positivity)
    linarith
  have hsin2 : ‖Complex.sin ((π : ℂ) * s / 2)‖ ≤ u := by
    rw [sin_pi_half_eq]
    have h1 : ‖cC ((1 - s) / 2)‖ ≤ Real.cosh (π * |((1 - s) / 2 : ℂ).im|) := norm_cC_le
    have him : |((1 - s) / 2 : ℂ).im| = y / 2 := by
      simp [hy', abs_div]
    rw [him] at h1
    have h2 : Real.cosh (π * (y / 2)) ≤ Real.exp (π * (y / 2)) := cosh_le_exp_self (by positivity)
    have : Real.exp (π * (y / 2)) = u := by rw [hu]; congr 1; ring
    linarith
  have hp : ‖pG s‖ ≤ (|P0| + |P1| + |cP2|) * u ^ 3 := by
    unfold pG pC
    have n1 : ‖((P0 : ℝ) : ℂ)‖ = |P0| := by simp
    have n2 : ‖((P1 : ℝ) : ℂ)‖ = |P1| := by simp
    have n3 : ‖((cP2 : ℝ) : ℂ)‖ = |cP2| := by simp
    have hu2 : u ^ 2 ≤ u ^ 3 := pow_le_pow_right₀ hu1 (by norm_num)
    have hu0 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
    calc ‖(P0 : ℂ) + (P1 : ℂ) * Complex.cos ((π : ℂ) * s) +
          (cP2 : ℂ) * (Complex.sin ((π : ℂ) * s) * Complex.sin ((π : ℂ) * s / 2))‖
        ≤ ‖(P0 : ℂ)‖ + ‖(P1 : ℂ) * Complex.cos ((π : ℂ) * s)‖ +
          ‖(cP2 : ℂ) * (Complex.sin ((π : ℂ) * s) * Complex.sin ((π : ℂ) * s / 2))‖ :=
          norm_add₃_le
      _ ≤ |P0| + |P1| * u ^ 2 + |cP2| * (u ^ 2 * u) := by
          rw [norm_mul, norm_mul, norm_mul, n1, n2, n3]
          gcongr
      _ ≤ |P0| * u ^ 3 + |P1| * u ^ 3 + |cP2| * u ^ 3 := by
          have : u ^ 2 * u = u ^ 3 := by ring
          rw [this]
          have := abs_nonneg P0
          nlinarith only [mul_le_mul_of_nonneg_left hu0 (abs_nonneg P0),
            mul_le_mul_of_nonneg_left hu2 (abs_nonneg P1)]
      _ = (|P0| + |P1| + |cP2|) * u ^ 3 := by ring
  -- denominator
  have hden : u ^ 4 / 16 ≤ ‖Complex.sin ((π : ℂ) * s)‖ ^ 2 := by
    have h1 : Real.sinh (π * |s.im|) ≤ ‖cC (1 / 2 - s)‖ := by
      have := norm_cC_ge (s := 1 / 2 - s)
      have him : |(1 / 2 - s : ℂ).im| = |s.im| := by simp
      rwa [him] at this
    rw [← sin_pi_mul_eq] at h1
    have h2 : Real.exp (π * y) / 4 ≤ Real.sinh (π * y) := by
      apply sinh_ge_exp
      nlinarith [Real.pi_gt_three]
    rw [e1] at h2
    have h3 : u ^ 2 / 4 ≤ ‖Complex.sin ((π : ℂ) * s)‖ := h2.trans h1
    have h4 : (u ^ 2 / 4) ^ 2 ≤ ‖Complex.sin ((π : ℂ) * s)‖ ^ 2 := by gcongr
    calc u ^ 4 / 16 = (u ^ 2 / 4) ^ 2 := by ring
      _ ≤ _ := h4
  have hnum : ‖psiTil s - pG s‖ ≤ C0 * u⁻¹ + (|P0| + |P1| + |cP2|) * u ^ 3 :=
    (norm_sub_le _ _).trans (add_le_add hΨ hp)
  have hC0nn : 0 ≤ C0 := by
    have := (norm_nonneg (psiTil s)).trans hΨ
    have hi : 0 < u⁻¹ := inv_pos.mpr hupos
    by_contra h
    have h' := not_le.mp h
    nlinarith
  have hKnn : 0 ≤ |P0| + |P1| + |cP2| := by positivity
  unfold Fq
  rw [norm_div, norm_pow]
  have hpos : 0 < u ^ 4 / 16 := by positivity
  rw [div_le_iff₀ (hpos.trans_le hden)]
  rw [e5]
  have hfinal : (C0 * u⁻¹ + (|P0| + |P1| + |cP2|) * u ^ 3) ≤
      16 * (|C0| + (|P0| + |P1| + |cP2|)) * u⁻¹ * (u ^ 4 / 16) := by
    have hu4 : u ^ 4 / 16 * 16 = u ^ 4 := by ring
    have hinv : u⁻¹ * u = 1 := inv_mul_cancel₀ hupos.ne'
    have hC : C0 * u⁻¹ ≤ |C0| * u ^ 3 := by
      have : u⁻¹ ≤ u ^ 3 := by
        calc u⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hu1
          _ ≤ u ^ 3 := one_le_pow₀ hu1
      calc C0 * u⁻¹ ≤ |C0| * u⁻¹ := by gcongr; exact le_abs_self _
        _ ≤ |C0| * u ^ 3 := by gcongr
    have : 16 * (|C0| + (|P0| + |P1| + |cP2|)) * u⁻¹ * (u ^ 4 / 16) =
        (|C0| + (|P0| + |P1| + |cP2|)) * u ^ 3 := by
      field_simp
    rw [this]
    nlinarith only [hC]
  have hcoef : 0 ≤ 16 * (|C0| + (|P0| + |P1| + |cP2|)) * u⁻¹ := by positivity
  calc ‖psiTil s - pG s‖ ≤ _ := hnum
    _ ≤ _ := hfinal
    _ ≤ 16 * (|C0| + (|P0| + |P1| + |cP2|)) * u⁻¹ * ‖Complex.sin ((π : ℂ) * s)‖ ^ 2 := by
        exact mul_le_mul_of_nonneg_left hden hcoef

/-- The mid-range region of the strip (away from the corners, `|Im s| ≤ 1`). -/
lemma Fq_mid {d0 d1 : ℝ} (h0 : 0 < d0) (h1 : 0 < d1) :
    ∃ M : ℝ, ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 1 → |s.im| ≤ 1 → d0 ≤ ‖s‖ → d1 ≤ ‖s - 1‖ → ‖Fq s‖ ≤ M := by
  set K : Set ℂ := {s : ℂ | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ 1 ∧ d0 ≤ ‖s‖ ∧ d1 ≤ ‖s - 1‖} with hK
  have hclosed : IsClosed K := by
    have a1 : IsClosed {s : ℂ | 0 ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
    have a2 : IsClosed {s : ℂ | s.re ≤ 1} := isClosed_le Complex.continuous_re continuous_const
    have a3 : IsClosed {s : ℂ | |s.im| ≤ 1} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have a4 : IsClosed {s : ℂ | d0 ≤ ‖s‖} := isClosed_le continuous_const continuous_norm
    have a5 : IsClosed {s : ℂ | d1 ≤ ‖s - 1‖} :=
      isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
    exact a1.inter (a2.inter (a3.inter (a4.inter a5)))
  have hbdd : Bornology.IsBounded K := by
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
    intro s hs
    obtain ⟨a, b, c, -, -⟩ := hs
    rw [mem_closedBall, dist_zero_right]
    have h1 : |s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 2 := by linarith
  have hcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hsub : K ⊆ unitStripCl \ {0, 1} := by
    intro s hs
    obtain ⟨a, b, -, c, d⟩ := hs
    refine ⟨⟨a, b⟩, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro h; rw [h] at c; simp at c; linarith
    · intro h; rw [h] at d; simp at d; linarith
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (continuousOn_Fq.mono hsub)
  exact ⟨M, fun s a b c d e => hM s ⟨a, b, c, d, e⟩⟩

/-- The decay bound `‖F(s)‖ ≤ C e^{-π|Im s|/2}` on the open strip. -/
lemma Fq_bound : ∃ C : ℝ, ∀ s ∈ unitStrip, ‖Fq s‖ ≤ C * Real.exp (-(π / 2 * |s.im|)) := by
  obtain ⟨C1, hC1⟩ := Fq_far
  obtain ⟨δ0, hδ0, M0, hM0⟩ := bound_zero
  obtain ⟨δ1, hδ1, M1, hM1⟩ := bound_one
  set d0 : ℝ := min δ0 1 with hd0
  set d1 : ℝ := min δ1 1 with hd1
  have hd0p : 0 < d0 := lt_min hδ0 one_pos
  have hd1p : 0 < d1 := lt_min hδ1 one_pos
  obtain ⟨Mm, hMm⟩ := Fq_mid hd0p hd1p
  set Mg : ℝ := max (max M0 M1) (max Mm 0) with hMg
  have hMg0 : 0 ≤ Mg := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨max C1 (Mg * Real.exp (π / 2)), fun s hs => ?_⟩
  have hpi := Real.pi_pos
  by_cases hy : 1 ≤ |s.im|
  · calc ‖Fq s‖ ≤ C1 * Real.exp (-(π / 2 * |s.im|)) := hC1 s hs hy
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · have hy' : |s.im| < 1 := not_le.mp hy
    have hbd : ‖Fq s‖ ≤ Mg := by
      by_cases hn0 : ‖s‖ < d0
      · have := hM0 s hs (lt_of_lt_of_le hn0 (min_le_left _ _))
        have e : Fq s = (psiHat s - pG s) / Complex.sin ((π : ℂ) * s) ^ 2 := by
          unfold Fq; rw [psiTil_of_mem hs]
        rw [e]
        exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
      · by_cases hn1 : ‖s - 1‖ < d1
        · have := hM1 s hs (lt_of_lt_of_le hn1 (min_le_left _ _))
          have e : Fq s = (psiHat s - pG s) / Complex.sin ((π : ℂ) * s) ^ 2 := by
            unfold Fq; rw [psiTil_of_mem hs]
          rw [e]
          exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
        · have := hMm s hs.1.le hs.2.le hy'.le (not_lt.mp hn0) (not_lt.mp hn1)
          exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
    have hexp : Real.exp (-(π / 2)) ≤ Real.exp (-(π / 2 * |s.im|)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [abs_nonneg s.im]
    have hE : Real.exp (π / 2) * Real.exp (-(π / 2)) = 1 := by
      rw [← Real.exp_add]; simp
    calc ‖Fq s‖ ≤ Mg := hbd
      _ = Mg * Real.exp (π / 2) * Real.exp (-(π / 2)) := by rw [mul_assoc, hE, mul_one]
      _ ≤ Mg * Real.exp (π / 2) * Real.exp (-(π / 2 * |s.im|)) := by gcongr
      _ ≤ _ := by gcongr; exact le_max_right _ _

/-! ### The edge values of `F` -/

/-- The constant term of `p`. -/
noncomputable def pP0 : ℝ := (Psi0v + Psi1v) / 2

/-- The coefficient of `cos πs` in `p`. -/
noncomputable def pP1 : ℝ := (Psi0v - Psi1v) / 2

lemma pG_eq : pG = pC pP0 pP1 cP2 := rfl

lemma cos_pi_left (τ : ℝ) : Complex.cos ((π : ℂ) * ((τ : ℂ) * Complex.I)) = ((Real.cosh (π * τ) : ℝ) : ℂ) := by
  rw [show (π : ℂ) * ((τ : ℂ) * Complex.I) = ((π * τ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh]

lemma sin_pi_left (τ : ℝ) :
    Complex.sin ((π : ℂ) * ((τ : ℂ) * Complex.I)) = ((Real.sinh (π * τ) : ℝ) : ℂ) * Complex.I := by
  rw [show (π : ℂ) * ((τ : ℂ) * Complex.I) = ((π * τ : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.sin_mul_I, ← Complex.ofReal_sinh]

lemma sin_pi_half_left (τ : ℝ) :
    Complex.sin ((π : ℂ) * ((τ : ℂ) * Complex.I) / 2) = ((Real.sinh (π * τ / 2) : ℝ) : ℂ) * Complex.I := by
  rw [show (π : ℂ) * ((τ : ℂ) * Complex.I) / 2 = ((π * τ / 2 : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.sin_mul_I, ← Complex.ofReal_sinh]

/-- Left edge value of `F`: a real number. -/
lemma Fq_left {τ : ℝ} (hτ : τ ≠ 0) :
    Fq ((τ : ℂ) * Complex.I) = ((-(fL τ - (pP0 + pP1 * Real.cosh (π * τ) -
      cP2 * (Real.sinh (π * τ) * Real.sinh (π * τ / 2)))) / Real.sinh (π * τ) ^ 2 : ℝ) : ℂ) := by
  have hs : Real.sinh (π * τ) ≠ 0 := by
    intro h
    have := Real.sinh_eq_zero.mp h
    rcases mul_eq_zero.mp this with h | h
    · exact Real.pi_ne_zero h
    · exact hτ h
  have hsC : ((Real.sinh (π * τ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold Fq
  rw [psiTil_left_eq hτ, pG_eq]
  unfold pC
  rw [cos_pi_left, sin_pi_left, sin_pi_half_left]
  have hI := Complex.I_sq
  push_cast
  field_simp
  linear_combination ((fL τ : ℂ) - pP0 - pP1 * Complex.cosh ((π : ℂ) * τ)) * (Complex.sinh ((π : ℂ) * τ))⁻¹ ^ 2 * hI

lemma sin_pi_right (τ : ℝ) :
    Complex.sin ((π : ℂ) * (1 + (τ : ℂ) * Complex.I)) = -(((Real.sinh (π * τ) : ℝ) : ℂ) * Complex.I) := by
  rw [show (π : ℂ) * (1 + (τ : ℂ) * Complex.I) = (π : ℂ) * ((τ : ℂ) * Complex.I) + (π : ℂ) by ring,
    Complex.sin_add_pi, sin_pi_left]

lemma cos_pi_right (τ : ℝ) :
    Complex.cos ((π : ℂ) * (1 + (τ : ℂ) * Complex.I)) = -((Real.cosh (π * τ) : ℝ) : ℂ) := by
  rw [show (π : ℂ) * (1 + (τ : ℂ) * Complex.I) = (π : ℂ) * ((τ : ℂ) * Complex.I) + (π : ℂ) by ring,
    Complex.cos_add_pi, cos_pi_left]

lemma sin_pi_half_right (τ : ℝ) :
    Complex.sin ((π : ℂ) * (1 + (τ : ℂ) * Complex.I) / 2) = ((Real.cosh (π * τ / 2) : ℝ) : ℂ) := by
  rw [show (π : ℂ) * (1 + (τ : ℂ) * Complex.I) / 2 = ((π * τ / 2 : ℝ) : ℂ) * Complex.I + (π : ℂ) / 2 by
    push_cast; ring, Complex.sin_add_pi_div_two, Complex.cos_mul_I, ← Complex.ofReal_cosh]

/-- Real part of the right edge value of `F`. -/
lemma Fq_right_re {τ : ℝ} (hτ : τ ≠ 0) :
    (Fq (1 + (τ : ℂ) * Complex.I)).re =
      (fR τ - (pP0 - pP1 * Real.cosh (π * τ))) / (-(Real.sinh (π * τ) ^ 2)) := by
  have hden : Complex.sin ((π : ℂ) * (1 + (τ : ℂ) * Complex.I)) ^ 2 =
      ((-(Real.sinh (π * τ) ^ 2) : ℝ) : ℂ) := by
    rw [sin_pi_right]
    have hI := Complex.I_sq
    push_cast
    linear_combination (Complex.sinh ((π : ℂ) * τ)) ^ 2 * hI
  have hnum : (psiTil (1 + (τ : ℂ) * Complex.I) - pG (1 + (τ : ℂ) * Complex.I)).re =
      fR τ - (pP0 - pP1 * Real.cosh (π * τ)) := by
    rw [Complex.sub_re, psiTil_right_re hτ, pG_eq]
    unfold pC
    rw [cos_pi_right, sin_pi_right, sin_pi_half_right]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_im, Complex.mul_im]
    ring
  unfold Fq
  rw [hden, Complex.div_ofReal_re, hnum]

/-- **The third-order strip identity.** -/
theorem xb_third_pre :
    Integrable (fun τ : ℝ => (xA τ + vA τ - 2 * π / Real.cosh (π * τ) + √2 / Real.cosh (π * τ / 2) +
        2 * pP1 * Real.cosh (π * τ) - cP2 * (Real.sinh (π * τ) * Real.sinh (π * τ / 2))) /
        Real.sinh (π * τ) ^ 2) ∧
    ∫ τ : ℝ, (xA τ + vA τ - 2 * π / Real.cosh (π * τ) + √2 / Real.cosh (π * τ / 2) +
        2 * pP1 * Real.cosh (π * τ) - cP2 * (Real.sinh (π * τ) * Real.sinh (π * τ / 2))) /
        Real.sinh (π * τ) ^ 2 = 0 := by
  obtain ⟨C, hC⟩ := Fq_bound
  obtain ⟨hiL, hiR, heq⟩ := strip_edge_cauchy (ε := π / 2) differentiableOn_Fq (by positivity)
    continuousOn_Fq hC
  have hae : ∀ᵐ τ : ℝ, τ ≠ 0 := by
    have := (Set.countable_singleton (0 : ℝ)).ae_notMem (volume : Measure ℝ)
    simpa using this
  have hE : ∀ τ : ℝ, τ ≠ 0 →
      (Fq ((τ : ℂ) * Complex.I)).re - (Fq (1 + (τ : ℂ) * Complex.I)).re =
      (xA τ + vA τ - 2 * π / Real.cosh (π * τ) + √2 / Real.cosh (π * τ / 2) +
        2 * pP1 * Real.cosh (π * τ) - cP2 * (Real.sinh (π * τ) * Real.sinh (π * τ / 2))) /
        Real.sinh (π * τ) ^ 2 := by
    intro τ hτ
    have hs : Real.sinh (π * τ) ≠ 0 := by
      intro h
      have := Real.sinh_eq_zero.mp h
      rcases mul_eq_zero.mp this with h | h
      · exact Real.pi_ne_zero h
      · exact hτ h
    rw [Fq_left hτ, Fq_right_re hτ, Complex.ofReal_re]
    unfold fL fR
    have : π * τ / 2 = π / 2 * τ := by ring
    field_simp
    ring
  have hL : Integrable (fun τ : ℝ => (Fq ((τ : ℂ) * Complex.I)).re) := hiL.re
  have hR : Integrable (fun τ : ℝ => (Fq (1 + (τ : ℂ) * Complex.I)).re) := hiR.re
  have hEq : (fun τ : ℝ => (Fq ((τ : ℂ) * Complex.I)).re - (Fq (1 + (τ : ℂ) * Complex.I)).re) =ᵐ[volume]
      fun τ : ℝ => (xA τ + vA τ - 2 * π / Real.cosh (π * τ) + √2 / Real.cosh (π * τ / 2) +
        2 * pP1 * Real.cosh (π * τ) - cP2 * (Real.sinh (π * τ) * Real.sinh (π * τ / 2))) /
        Real.sinh (π * τ) ^ 2 := by
    filter_upwards [hae] with τ hτ using hE τ hτ
  refine ⟨(hL.sub hR).congr hEq, ?_⟩
  rw [← integral_congr_ae hEq, integral_sub hL hR]
  have h1 := integral_re hiL
  have h2 := integral_re hiR
  exact sub_eq_zero.mpr (h1.trans ((congrArg Complex.re heq).trans h2.symm))

/-- **Third-order strip identity (Piece 3 at order three).**  For some real `B`,
`∫_ℝ (x_A + v_A - 2π sech(πτ) + √2 sech(πτ/2) + 2B cosh(πτ) - P sinh(πτ) sinh(πτ/2)) / sinh²(πτ) dτ = 0`
with `P = √2 (π²/2 + 4)/π² = -Ψ'(1)/π`, the integrand being integrable. -/
theorem xb_third : ∃ B : ℝ,
    Integrable (fun τ : ℝ => (xA τ + vA τ - 2 * π / Real.cosh (π * τ) + √2 / Real.cosh (π * τ / 2) +
        2 * B * Real.cosh (π * τ) - √2 * (π ^ 2 / 2 + 4) / π ^ 2 *
          (Real.sinh (π * τ) * Real.sinh (π * τ / 2))) / Real.sinh (π * τ) ^ 2) ∧
    ∫ τ : ℝ, (xA τ + vA τ - 2 * π / Real.cosh (π * τ) + √2 / Real.cosh (π * τ / 2) +
        2 * B * Real.cosh (π * τ) - √2 * (π ^ 2 / 2 + 4) / π ^ 2 *
          (Real.sinh (π * τ) * Real.sinh (π * τ / 2))) / Real.sinh (π * τ) ^ 2 = 0 :=
  ⟨pP1, xb_third_pre⟩

/-- info: 'FormalResearch.ModularBootstrap.FiveTerm.xb_third' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.FiveTerm.xb_third

end FormalResearch.ModularBootstrap.FiveTerm

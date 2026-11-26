module

public import FormalResearch.SignUncertainty.UctFloorEdge
public import FormalResearch.SignUncertainty.UctPosFloorWpos

/-!
# `uct:admiss` (M1)-(M3) for the lift symbol of a one-level seed (the floor summand of `fct:main-hankel`) (F2a)

Source: `CFT/sign_uncertainty/paper/constant_terms_five.tex`, proof of `fct:main-hankel`, Step 1 ("For the floor multiplier
`W_pos` of Lemma `uct:pos-floor`(2), the Neumann square `g_1'` is treated like `g_1`"). **Proved.**
-/

@[expose] public section

open Complex Filter Topology Metric Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Lipschitz bound of a holomorphic function on a closed half-unit ball inside an open set of holomorphy. -/
lemma lip_ball {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {z0 : ℂ}
    (hball : closedBall z0 (1 / 2) ⊆ U) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ z : ℂ, ‖z - z0‖ ≤ 1 / 2 → ‖f z - f z0‖ ≤ L * ‖z - z0‖ := by
  have hcont : ContinuousOn (deriv f) U := (hf.analyticOnNhd hU).deriv.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_closedBall z0 (1 / 2)).exists_bound_of_continuousOn (hcont.mono hball)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL z0 (mem_closedBall_self (by norm_num)))
  refine ⟨L, hL0, fun z hz => ?_⟩
  have hzb : z ∈ closedBall z0 (1 / 2) := by simpa [Complex.dist_eq] using hz
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (C := L) (s := closedBall z0 (1 / 2)) (x := z0) (y := z)
    (fun x hx => (hf.differentiableAt (hU.mem_nhds (hball hx))))
    (fun x hx => hL x hx) (convex_closedBall _ _) (mem_closedBall_self (by norm_num)) hzb
  simpa [norm_sub_rev] using this

/-- The Hölder-`1/2` bound at `0` of `N₁ + (kζ)^{1/2} N₂` for entire `N₁, N₂`. -/
lemma holder_sqrt0 {N1 N2 : ℂ → ℂ} (h1 : Differentiable ℂ N1) (h2 : Differentiable ℂ N2) {k : ℝ} (hk : 0 < k) :
    ∃ CH : ℝ, ∀ ζ : ℂ, ‖ζ‖ ≤ 1 / 2 →
      ‖(N1 ζ + ((k : ℂ) * ζ) ^ (1 / 2 : ℂ) * N2 ζ) - (N1 0 + ((k : ℂ) * 0) ^ (1 / 2 : ℂ) * N2 0)‖ ≤ CH * ‖ζ‖ ^ (1 / 2 : ℝ) := by
  obtain ⟨L, hL0, hL⟩ := lip_ball (U := univ) isOpen_univ h1.differentiableOn (z0 := 0) (by simp)
  have hc2 : Continuous N2 := h2.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_bound_of_continuousOn hc2.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self (by norm_num)))
  refine ⟨L + k ^ (1 / 2 : ℝ) * M, fun ζ hζ => ?_⟩
  by_cases hz : ζ = 0
  · subst hz; simp
  have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr hz
  have hζ1 : ‖ζ‖ ≤ 1 := hζ.trans (by norm_num)
  have e0 : ((k : ℂ) * 0) ^ (1 / 2 : ℂ) = 0 := by simp
  rw [e0, zero_mul, add_zero]
  have hy : ((k : ℂ) * ζ) ≠ 0 := mul_ne_zero (by exact_mod_cast hk.ne') hz
  have hn : ‖((k : ℂ) * ζ) ^ (1 / 2 : ℂ)‖ = k ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ) := by
    have := norm_cpow_ofReal_exponent hy (1 / 2)
    rw [show ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at this
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, Real.mul_rpow hk.le hζ0.le]
  have hsq : ‖ζ‖ ≤ ‖ζ‖ ^ (1 / 2 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_ge hζ0 hζ1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
    simpa using this
  have hl := hL ζ (by simpa using hζ)
  rw [sub_zero] at hl
  have hMζ := hM ζ (by simpa using hζ)
  calc ‖(N1 ζ + ((k : ℂ) * ζ) ^ (1 / 2 : ℂ) * N2 ζ) - N1 0‖
      = ‖(N1 ζ - N1 0) + ((k : ℂ) * ζ) ^ (1 / 2 : ℂ) * N2 ζ‖ := by ring_nf
    _ ≤ ‖N1 ζ - N1 0‖ + ‖((k : ℂ) * ζ) ^ (1 / 2 : ℂ)‖ * ‖N2 ζ‖ := (norm_add_le _ _).trans (by rw [norm_mul])
    _ ≤ L * ‖ζ‖ ^ (1 / 2 : ℝ) + (k ^ (1 / 2 : ℝ) * ‖ζ‖ ^ (1 / 2 : ℝ)) * M := by
        rw [hn]
        gcongr
        exact hl.trans (by gcongr)
    _ = _ := by ring

/-! ### The multiplier along the imaginary axis -/

/-- `τ ↦ E₁(i β τ)^m`, the lift multiplier along the imaginary axis of the strip. -/
noncomputable def bsMultLine (β : ℝ) (m : ℕ) (τ : ℝ) : ℂ := bsplineE1 (Complex.I * (β : ℂ) * (τ : ℂ)) ^ m

lemma bsMultLine_contDiff (β : ℝ) (m : ℕ) : ContDiff ℝ 2 (bsMultLine β m) := by
  have h : ContDiff ℝ ((2 : ℕ) : ℕ∞) (fun τ : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (τ : ℂ))) :=
    ((contDiff_bsplineE1.restrict_scalars ℝ).comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).of_le
      (by exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  have h' : ContDiff ℝ 2 (fun τ : ℝ => bsplineE1 (Complex.I * (β : ℂ) * (τ : ℂ))) := by exact_mod_cast h
  exact h'.pow m

lemma bsMultLine_bounds (m : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ, ∀ τ : ℝ, ‖bsMultLine β m τ‖ ≤ C ∧ ‖deriv (bsMultLine β m) τ‖ ≤ C ∧
      ‖deriv (deriv (bsMultLine β m)) τ‖ ≤ C := by
  obtain ⟨C0, hC0, b0⟩ := bsplineE1_imag_pow_deriv_bound m 0
  obtain ⟨C1, hC1, b1⟩ := bsplineE1_imag_pow_deriv_bound m 1
  obtain ⟨C2, hC2, b2⟩ := bsplineE1_imag_pow_deriv_bound m 2
  have hle : ∀ τ : ℝ, (1 + β * |τ|) ^ (-(m : ℝ)) ≤ 1 := fun τ =>
    Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [abs_nonneg τ]) (by simp)
  refine ⟨max (C0 * β ^ 0) (max (C1 * β ^ 1) (C2 * β ^ 2)), fun τ => ⟨?_, ?_, ?_⟩⟩
  · have := b0 hβ τ
    rw [iteratedDeriv_zero] at this
    refine (this.trans ?_).trans (le_max_left _ _)
    nlinarith [hle τ, pow_pos hβ 0, mul_pos hC0 (pow_pos hβ 0)]
  · have := b1 hβ τ
    rw [iteratedDeriv_one] at this
    refine (this.trans ?_).trans ((le_max_left _ _).trans (le_max_right _ _))
    nlinarith [hle τ, mul_pos hC1 (pow_pos hβ 1)]
  · have := b2 hβ τ
    have e2 : ∀ f : ℝ → ℂ, iteratedDeriv 2 f = deriv (deriv f) := fun f => by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [e2] at this
    refine (this.trans ?_).trans ((le_max_right _ _).trans (le_max_right _ _))
    nlinarith [hle τ, mul_pos hC2 (pow_pos hβ 2)]

/-! ### The right edge: Cauchy bounds along the reflected line -/

lemma one_add_sq_rpow_le (τ : ℝ) : (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) ≤ 4 * (1 + |τ|) ^ (-(2 : ℝ)) := by
  have hs : 0 < 1 + |τ| := by positivity
  have h1 : (1 + |τ|) ^ 2 * 2⁻¹ ≤ 1 + τ ^ 2 := by nlinarith [sq_abs τ, sq_nonneg (|τ| - 1)]
  have h2 : (1 + τ ^ 2) ^ (-(5 / 4 : ℝ)) ≤ ((1 + |τ|) ^ 2 * 2⁻¹) ^ (-(5 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
  have h3 : ((1 + |τ|) ^ 2 * 2⁻¹) ^ (-(5 / 4 : ℝ)) = (1 + |τ|) ^ (-(5 / 2 : ℝ)) * 2 ^ (5 / 4 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by norm_num), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hs.le]
    norm_num
  have h4 : (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 4 := by
    calc (2 : ℝ) ^ (5 / 4 : ℝ) ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by norm_num
  have h5 : (1 + |τ|) ^ (-(5 / 2 : ℝ)) ≤ (1 + |τ|) ^ (-(2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg τ]) (by norm_num)
  rw [h3] at h2
  have h6 : 0 ≤ (1 + |τ|) ^ (-(5 / 2 : ℝ)) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h4 h6]

/-- The reflected-line trace `τ ↦ W_X(c^{1/3}(1 - iτ))` is `C²` with `(1+|τ|)^{-2}` bounds (`o2_reflected_line_deriv_bound`). -/
theorem lift_reflected_bounds {X : ℝ → ℝ} (hX : HasU2 X) {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) {c : ℝ} (hc : 2 ≤ c) :
    ContDiff ℝ 2 (fun t : ℝ => liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) ∧
    ∃ C : ℝ, ∀ τ : ℝ,
      ‖liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (τ : ℂ)))‖ ≤ C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (fun t : ℝ => liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) τ‖ ≤
        C * (1 + |τ|) ^ (-(2 : ℝ)) ∧
      ‖deriv (deriv (fun t : ℝ => liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ))))) τ‖ ≤
        C * (1 + |τ|) ^ (-(2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hF := liftSymbol_differentiableOn hX δ m
  have hcd : ContDiff ℝ ((2 : ℕ) : ℕ∞) (fun t : ℝ => liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - Complex.I * (t : ℂ)))) :=
    (o2_reflected_line_contDiff hF hc0).of_le (by exact_mod_cast (le_top : ((2 : ℕ) : ℕ∞) ≤ ⊤))
  refine ⟨by exact_mod_cast hcd, ?_⟩
  obtain ⟨Cs, hCs, hb⟩ := hX.rhp
  have hbd : ∀ w : ℂ, 0 < w.re → ‖liftSymbol X δ m w‖ ≤ Cs * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := fun w hw => by
    unfold liftSymbol
    rw [norm_mul]
    calc ‖liftMultiplier δ m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ 1 * (Cs * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) :=
          mul_le_mul (norm_liftMultiplier_le_one hδ m hw.le) (hb w hw.le) (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  have key : ∀ (r : ℕ) (τ : ℝ), ‖iteratedDeriv r (fun t : ℝ => liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
      (1 - Complex.I * (t : ℂ)))) τ‖ ≤ (2 : ℝ) ^ ((r : ℝ) + 5 / 2) * (r.factorial : ℝ) * Cs * c ^ (-(5 / 6 : ℝ)) *
        (4 * (1 + |τ|) ^ (-(2 : ℝ))) := fun r τ =>
    (o2_reflected_line_deriv_bound hCs.le hF hbd hc τ r).trans (by
      have hp : 0 ≤ (2 : ℝ) ^ ((r : ℝ) + 5 / 2) * (r.factorial : ℝ) * Cs * c ^ (-(5 / 6 : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_left (one_add_sq_rpow_le τ) hp)
  set Kf : ℕ → ℝ := fun r : ℕ => (2 : ℝ) ^ ((r : ℝ) + 5 / 2) * (r.factorial : ℝ) * Cs * c ^ (-(5 / 6 : ℝ)) * 4 with hKf
  have hKf0 : ∀ r, 0 ≤ Kf r := fun r => by simp only [hKf]; positivity
  have e2 : ∀ f : ℝ → ℂ, iteratedDeriv 2 f = deriv (deriv f) := fun f => by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hP : ∀ τ : ℝ, 0 ≤ (1 + |τ|) ^ (-(2 : ℝ)) := fun τ => by positivity
  refine ⟨Kf 0 + Kf 1 + Kf 2, fun τ => ⟨?_, ?_, ?_⟩⟩
  · have := key 0 τ
    rw [iteratedDeriv_zero] at this
    have h0 := hKf0 0; have h1 := hKf0 1; have h2 := hKf0 2
    refine this.trans ?_
    nlinarith [mul_nonneg (add_nonneg h1 h2) (hP τ), show (2 : ℝ) ^ (((0 : ℕ) : ℝ) + 5 / 2) * ((Nat.factorial 0 : ℕ) : ℝ) * Cs * c ^ (-(5 / 6 : ℝ)) * (4 * (1 + |τ|) ^ (-(2 : ℝ))) = Kf 0 * (1 + |τ|) ^ (-(2 : ℝ)) by simp only [hKf]; ring]
  · have := key 1 τ
    rw [iteratedDeriv_one] at this
    have h0 := hKf0 0; have h1 := hKf0 1; have h2 := hKf0 2
    refine this.trans ?_
    nlinarith [mul_nonneg (add_nonneg h0 h2) (hP τ), show (2 : ℝ) ^ (((1 : ℕ) : ℝ) + 5 / 2) * ((Nat.factorial 1 : ℕ) : ℝ) * Cs * c ^ (-(5 / 6 : ℝ)) * (4 * (1 + |τ|) ^ (-(2 : ℝ))) = Kf 1 * (1 + |τ|) ^ (-(2 : ℝ)) by simp only [hKf]; ring]
  · have := key 2 τ
    rw [e2] at this
    have h0 := hKf0 0; have h1 := hKf0 1; have h2 := hKf0 2
    refine this.trans ?_
    nlinarith [mul_nonneg (add_nonneg h0 h1) (hP τ), show (2 : ℝ) ^ (((2 : ℕ) : ℝ) + 5 / 2) * ((Nat.factorial 2 : ℕ) : ℝ) * Cs * c ^ (-(5 / 6 : ℝ)) * (4 * (1 + |τ|) ^ (-(2 : ℝ))) = Kf 2 * (1 + |τ|) ^ (-(2 : ℝ)) by simp only [hKf]; ring]

/-! ### `StripAdmissFullData` of the lift symbol -/

/-- **(M1)-(M3) of `uct:admiss` for the lift symbol of a seed `X` with the `U.2` package, the square-root form
`T = A + y^{1/2} B` and the imaginary-axis bounds**, `ζ ↦ W_X(c^{1/3} ζ)` on the strip (`α = 1/2`), `c ≥ 8`, `δ > 0`. -/
theorem floorSym_stripAdmissFull {X : ℝ → ℝ} (hX : HasU2 X) {A B : ℂ → ℂ} (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hTAB : ∀ y : ℂ, 0 ≤ y.re → airyTwistedLaplaceC X y = A y + y ^ (1 / 2 : ℂ) * B y)
    (himag : ImagAxisBounds (airyTwistedLaplaceC X)) {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : 8 ≤ c) :
    StripAdmissFullData (1 / 2 : ℝ) (fun ζ => liftSymbol X δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ)) := by
  have hc0 : 0 < c := by linarith
  have ha2 : 2 ≤ c ^ (1 / 3 : ℝ) := by
    have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
    calc (2 : ℝ) = 8 ^ (1 / 3 : ℝ) := h8.symm
      _ ≤ c ^ (1 / 3 : ℝ) := Real.rpow_le_rpow (by norm_num) hc (by norm_num)
  have hc2 : 2 ≤ c := by linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = c ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← ha] at ha2 ⊢
  have ha0 : 0 < a := by linarith
  have hLD := liftSymbolData_of_hasU2 hX hδ.le m
  have hmapsOpen : ∀ ζ : ℂ, 0 < ζ.re → 0 < ((a : ℂ) * ζ).re := fun ζ h => by
    rw [Complex.re_ofReal_mul]; exact mul_pos ha0 h
  have hmapsClosed : ∀ ζ : ℂ, 0 ≤ ζ.re → 0 ≤ ((a : ℂ) * ζ).re := fun ζ h => by
    rw [Complex.re_ofReal_mul]; exact mul_nonneg ha0.le h
  have hFdiff : DifferentiableOn ℂ (fun ζ : ℂ => liftSymbol X δ m ((a : ℂ) * ζ)) {ζ : ℂ | 0 < ζ.re} :=
    hLD.diff.comp ((differentiableOn_const _).mul differentiableOn_id) (fun ζ hζ => hmapsOpen ζ hζ)
  -- (M1)
  have hM1 : StripM1 (fun ζ : ℂ => liftSymbol X δ m ((a : ℂ) * ζ)) := by
    refine ⟨hFdiff.mono (fun ζ hζ => hζ.1), ?_, ?_, ?_⟩
    · exact hLD.cont.comp ((continuous_const.mul continuous_id).continuousOn) (fun ζ hζ => hmapsClosed ζ hζ.1)
    · intro ζ _ _
      show liftSymbol X δ m ((a : ℂ) * starRingEnd ℂ ζ) = starRingEnd ℂ (liftSymbol X δ m ((a : ℂ) * ζ))
      rw [← liftSymbol_conj]; congr 1; simp [Complex.conj_ofReal]
    · obtain ⟨Bq, hBq⟩ := hLD.bound
      refine ⟨Bq, fun ζ h0 _ => ?_⟩
      have hb := hBq ((a : ℂ) * ζ) (hmapsClosed ζ h0)
      rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos ha0] at hb
      have hBq0 : 0 ≤ Bq := by
        have := (norm_nonneg _).trans (hBq 0 (by simp))
        simpa using this
      refine hb.trans ?_
      have h1 : 1 + |ζ.im| ≤ 1 + a * |ζ.im| := by nlinarith [abs_nonneg ζ.im]
      have h2 : (1 + a * |ζ.im|) ^ (-(5 / 2 : ℝ)) ≤ (1 + |ζ.im|) ^ (-(5 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
      have h3 : (1 + |ζ.im|) ^ (-(5 / 2 : ℝ)) ≤ (1 + |ζ.im|) ^ (-(2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg ζ.im]) (by norm_num)
      exact mul_le_mul_of_nonneg_left (h2.trans h3) hBq0
  -- the closed square-root form of `F`
  set k : ℝ := ceCs * a with hk
  have hk0 : 0 < k := mul_pos ceCs_pos ha0
  have hmult : Differentiable ℂ (fun ζ : ℂ => liftMultiplier δ m ((a : ℂ) * ζ)) := by
    unfold liftMultiplier
    exact (differentiable_bsplineE1.comp ((differentiable_const _).mul ((differentiable_const _).mul differentiable_id))).pow m
  have hkA : Differentiable ℂ (fun ζ : ℂ => A (((k : ℝ) : ℂ) * ζ)) :=
    hA.comp ((differentiable_const _).mul differentiable_id)
  have hkB : Differentiable ℂ (fun ζ : ℂ => B (((k : ℝ) : ℂ) * ζ)) :=
    hB.comp ((differentiable_const _).mul differentiable_id)
  have hform : ∀ ζ : ℂ, 0 ≤ ζ.re → liftSymbol X δ m ((a : ℂ) * ζ) =
      liftMultiplier δ m ((a : ℂ) * ζ) * A (((k : ℝ) : ℂ) * ζ) +
        (((k : ℝ) : ℂ) * ζ) ^ (1 / 2 : ℂ) * (liftMultiplier δ m ((a : ℂ) * ζ) * B (((k : ℝ) : ℂ) * ζ)) := by
    intro ζ hζ
    have hy : ((ceCs : ℂ) * ((a : ℂ) * ζ)) = ((k : ℝ) : ℂ) * ζ := by rw [hk]; push_cast; ring
    have hre : 0 ≤ ((ceCs : ℂ) * ((a : ℂ) * ζ)).re := by
      rw [Complex.re_ofReal_mul]; exact mul_nonneg ceCs_pos.le (hmapsClosed ζ hζ)
    unfold liftSymbol
    rw [hy] at hre ⊢
    rw [hTAB _ hre]; ring
  -- Hölder at `0`
  obtain ⟨CH0, hCH0⟩ := holder_sqrt0 (hmult.mul hkA) (hmult.mul hkB) hk0
  -- Hölder at `1`
  have hball : closedBall (1 : ℂ) (1 / 2) ⊆ {ζ : ℂ | 0 < ζ.re} := fun z hz => by
    have h1 : ‖z - 1‖ ≤ 1 / 2 := by simpa [Complex.dist_eq] using hz
    have h2 : |z.re - 1| ≤ 1 / 2 := by
      have := Complex.abs_re_le_norm (z - 1)
      simpa using this.trans h1
    have := (abs_le.mp h2).1
    show 0 < z.re
    linarith
  obtain ⟨L1, hL1, hL1b⟩ := lip_ball (isOpen_lt continuous_const Complex.continuous_re) hFdiff hball
  refine
    { toStripM1 := hM1
      holder1 := ⟨L1, fun ζ _ _ h => ?_⟩
      edge0 := ?_
      holder0 := ⟨CH0, fun ζ h0 _ hζ => ?_⟩
      edge1 := ?_ }
  · -- Hölder at `1`
    have hl := hL1b ζ (by rwa [norm_sub_rev] at h)
    rw [norm_sub_rev ζ 1] at hl
    have hy : 0 ≤ ‖1 - ζ‖ := norm_nonneg _
    have hy1 : ‖1 - ζ‖ ≤ ‖1 - ζ‖ ^ (1 / 2 : ℝ) := by
      rcases hy.eq_or_lt with h0 | h0
      · rw [← h0]; simp
      · have := Real.rpow_le_rpow_of_exponent_ge h0 (h.trans (by norm_num)) (by norm_num : (1 / 2 : ℝ) ≤ 1)
        simpa using this
    exact hl.trans (mul_le_mul_of_nonneg_left hy1 hL1)
  · -- (M3) at the left edge
    have hβ : 0 < ceCs * δ * a / m := by have := ceCs_pos; positivity
    obtain ⟨Cy, hCy⟩ := bsMultLine_bounds m hβ
    have hs : 2 < k := by nlinarith [ceCs_one_lt]
    refine stripEdge0_of_sqrt (bsMultLine_contDiff (ceCs * δ * a / m) m) hCy hA hB hTAB himag hs (fun τ => ?_)
    have e1 : (((ceCs * δ / m : ℝ) : ℂ) * ((a : ℂ) * ((τ : ℂ) * Complex.I))) =
        Complex.I * ((ceCs * δ * a / m : ℝ) : ℂ) * (τ : ℂ) := by push_cast; ring
    have e2 : ((ceCs : ℂ) * ((a : ℂ) * ((τ : ℂ) * Complex.I))) = yLine k τ := by
      rw [yLine_eq, hk]; push_cast; ring
    show liftSymbol X δ m ((a : ℂ) * ((τ : ℂ) * Complex.I)) = _
    unfold liftSymbol liftMultiplier bsMultLine
    rw [e1, e2]
  · -- Hölder at `0`
    calc ‖liftSymbol X δ m ((a : ℂ) * ζ) - liftSymbol X δ m ((a : ℂ) * 0)‖
        = ‖(liftMultiplier δ m ((a : ℂ) * ζ) * A (((k : ℝ) : ℂ) * ζ) +
            (((k : ℝ) : ℂ) * ζ) ^ (1 / 2 : ℂ) * (liftMultiplier δ m ((a : ℂ) * ζ) * B (((k : ℝ) : ℂ) * ζ))) -
          (liftMultiplier δ m ((a : ℂ) * 0) * A (((k : ℝ) : ℂ) * 0) +
            (((k : ℝ) : ℂ) * 0) ^ (1 / 2 : ℂ) * (liftMultiplier δ m ((a : ℂ) * 0) * B (((k : ℝ) : ℂ) * 0)))‖ := by
          rw [hform ζ h0, hform 0 (by simp)]
      _ ≤ CH0 * ‖ζ‖ ^ (1 / 2 : ℝ) := hCH0 ζ hζ
  · -- (M3) at the right edge
    obtain ⟨hcd, C, hC⟩ := lift_reflected_bounds hX hδ.le m hc2
    refine stripEdge0_of_smooth (by norm_num) hcd hC ?_
    funext τ
    show liftSymbol X δ m ((a : ℂ) * (1 - ((τ : ℂ) * Complex.I))) = _
    rw [ha]
    congr 2; ring

/-- **(M1)-(M3) for the `ε`-lift `W_F(c^{1/3} ζ) + ε W_D(c^{1/3}(1 - ζ))` of a one-level seed `a f₁ + b g₁ + c₀ g₁'`**
(`g₁'` through the transform `g̃₁'(i w̃) = E₃(w̃) + w̃^{1/2} E₄(w̃)`, `airySeedU2_sqForm`): the floor multiplier `W_pos` of
`uct:pos-floor` (2) satisfies `StripAdmissFullData (1/2)` for `c ≥ 8`. -/
theorem liftSymbol_airySeedU2_stripAdmissFull (p q r : ℝ) {ε : ℝ} {δ : ℝ} (hδ : 0 < δ) {m : ℕ} (hm : 0 < m) {c : ℝ}
    (hc : 8 ≤ c) :
    StripAdmissFullData (1 / 2 : ℝ) (fun ζ : ℂ =>
      liftSymbol (airySeedU2 p q r) δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ζ) +
        (ε : ℂ) * liftSymbol (airySeedU2 p q r) δ m (((c ^ (1 / 3 : ℝ) : ℝ) : ℂ) * (1 - ζ))) := by
  have hX := hasU2_airySeedU2 p q r
  obtain ⟨A, B, hA, hB, -, hTAB⟩ := (airySeedU2_sqForm p q r).closed hX.continuousOn
  have h0 := floorSym_stripAdmissFull hX hA hB hTAB (airySeedU2_imagAxisBounds p q r) hδ hm hc
  exact h0.add (h0.reflect.smul_real ε)

/-- info: 'FormalResearch.SignUncertainty.liftSymbol_airySeedU2_stripAdmissFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms liftSymbol_airySeedU2_stripAdmissFull

end FormalResearch.SignUncertainty

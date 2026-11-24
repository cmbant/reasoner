module

public import FormalResearch.SignUncertainty.MellinLiftGeneral
public import FormalResearch.CohnElkies.HighBandUniform

/-!
# The tail hypothesis of the general lift for `X = D + τ S` (M6, `ce_hb_lift` step (3))

The pair of `thm:ce-hb-lift` is the lift of the seeds `X_± = D_c ± S_c`, a one-level seed `D_c` plus the convolution source `S_c`.
`exists_hankelEigenfn_lift_general` needs the tail bound `|I_main[X] + σ I_dual[X]| ≲ ξ⁻¹ (log π²ξ)^{-3/2}`.
By linearity of `I_main`, `I_dual` in the seed (`iMain_add`, `iDual_add`, `iMain_const_mul`, `iDual_const_mul`, for `HasU2` seeds) it follows from
the tails of `D_c` (`iMain_add_iDual_tail`) and from separate tails of `I_main[S_c]` and `I_dual[S_c]`:

* `ConvTailData S δ₀ m c`: `HasU2 S` and `‖I_main[S](ξ)‖, ‖I_dual[S](ξ)‖ ≤ C ξ⁻¹ (log π²ξ)^{-3/2}` for large `ξ`.  This is a **hypothesis
  structure**: for `S = S_c` the two bounds are `O.12(7)` (far transfer, `c ξ I_main[S_c] = O(L^{-3/2})` for `L ≥ L_F`; the range
  `L ≤ L_F` is bounded by `middle_transfer_gt1`) and `GT.2b` with `A = C ε^{9/2}` (reflected line, `O.12(5)`), none yet formalised.
* `convTailData_of_oneLevel`: non-vacuity witness (every one-level seed satisfies it, from `iMain_add_iDual_tail` at `σ = ±1`).
* `exists_hankelEigenfn_lift_of_convTail`: for `D = airySeedU2 a b c₀`, `S` with `ConvTailData`, and `τ`, the seed `D + τ S` has a Hankel
  eigenfunction lift `f ∈ 𝒜_c^σ` with the edge representation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

lemma liftSymbol_add_seed {X Y : ℝ → ℝ} (hX : HasU2 X) (hY : HasU2 Y) (δ₀ : ℝ) (m : ℕ) {w : ℂ} (hw : 0 ≤ w.re) :
    liftSymbol (fun u => X u + Y u) δ₀ m w = liftSymbol X δ₀ m w + liftSymbol Y δ₀ m w := by
  unfold liftSymbol
  have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp [Complex.mul_re, mul_nonneg ceCs_pos.le hw]
  rw [airyTwistedLaplaceC_add (hX.integrable _ hre) (hY.integrable _ hre)]
  ring

lemma liftSymbol_const_mul_seed (b : ℝ) (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (w : ℂ) :
    liftSymbol (fun u => b * X u) δ₀ m w = (b : ℂ) * liftSymbol X δ₀ m w := by
  unfold liftSymbol
  rw [airyTwistedLaplaceC_const_mul]
  ring

theorem iMain_add {X Y : ℝ → ℝ} (hX : HasU2 X) (hY : HasU2 Y) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c ξ : ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) :
    iMain (fun u => X u + Y u) δ₀ m c ξ = iMain X δ₀ m c ξ + iMain Y δ₀ m c ξ := by
  unfold iMain
  have hpt : ∀ v : ℝ, iMainIntegrand (fun u => X u + Y u) δ₀ m c ξ v =
      iMainIntegrand X δ₀ m c ξ v + iMainIntegrand Y δ₀ m c ξ v := fun v => by
    unfold iMainIntegrand
    rw [liftSymbol_add_seed hX hY δ₀ m (by simp)]
    ring
  simp_rw [hpt]
  rw [integral_add (hX.integrable_iMainIntegrand hδ m hc hξ) (hY.integrable_iMainIntegrand hδ m hc hξ)]
  ring

theorem iDual_add {X Y : ℝ → ℝ} (hX : HasU2 X) (hY : HasU2 Y) {δ₀ : ℝ} (hδ : 0 ≤ δ₀) (m : ℕ) {c ξ : ℝ}
    (hc : 0 < c) (hξ : 0 < ξ) :
    iDual (fun u => X u + Y u) δ₀ m c ξ = iDual X δ₀ m c ξ + iDual Y δ₀ m c ξ := by
  unfold iDual
  have hpt : ∀ v : ℝ, iDualIntegrand (fun u => X u + Y u) δ₀ m c ξ v =
      iDualIntegrand X δ₀ m c ξ v + iDualIntegrand Y δ₀ m c ξ v := fun v => by
    unfold iDualIntegrand
    have hre : 0 ≤ ((((c ^ (1 / 3 : ℝ) : ℝ) : ℂ)) - (v : ℂ) * Complex.I).re := by
      simpa using Real.rpow_nonneg hc.le _
    rw [liftSymbol_add_seed hX hY δ₀ m hre]
    ring
  simp_rw [hpt]
  rw [integral_add (hX.integrable_iDualIntegrand hδ m hc hξ) (hY.integrable_iDualIntegrand hδ m hc hξ)]
  ring

theorem iMain_const_mul (b : ℝ) (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c ξ : ℝ) :
    iMain (fun u => b * X u) δ₀ m c ξ = (b : ℂ) * iMain X δ₀ m c ξ := by
  unfold iMain
  have hpt : ∀ v : ℝ, iMainIntegrand (fun u => b * X u) δ₀ m c ξ v = (b : ℂ) * iMainIntegrand X δ₀ m c ξ v := fun v => by
    unfold iMainIntegrand
    rw [liftSymbol_const_mul_seed]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  ring

theorem iDual_const_mul (b : ℝ) (X : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c ξ : ℝ) :
    iDual (fun u => b * X u) δ₀ m c ξ = (b : ℂ) * iDual X δ₀ m c ξ := by
  unfold iDual
  have hpt : ∀ v : ℝ, iDualIntegrand (fun u => b * X u) δ₀ m c ξ v = (b : ℂ) * iDualIntegrand X δ₀ m c ξ v := fun v => by
    unfold iDualIntegrand
    rw [liftSymbol_const_mul_seed]
    ring
  simp_rw [hpt]
  rw [integral_const_mul]
  ring

/-- Tails of `I_main[S]` and `I_dual[S]` separately (a hypothesis structure for the convolution source, see the module docstring). -/
structure ConvTailData (S : ℝ → ℝ) (δ₀ : ℝ) (m : ℕ) (c : ℝ) : Prop where
  hasU2 : HasU2 S
  main : ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
    ‖iMain S δ₀ m c ξ‖ ≤ C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))
  dual : ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
    ‖iDual S δ₀ m c ξ‖ ≤ C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))

/-- **Non-vacuity of `ConvTailData`**: every one-level seed obeys it (`iMain_add_iDual_tail` at `σ = ±1`, averaged). -/
theorem convTailData_of_oneLevel {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {K c : ℝ} (hK : 1 ≤ K) (hc : 2000 ≤ c)
    (hcK : 8 * K ^ 3 ≤ c) :
    ConvTailData (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c := by
  obtain ⟨C₁, hC₁, ξ₁, hξ₁, h₁⟩ := iMain_add_iDual_tail hm a b c₀ hK hc hcK 1 (Or.inl rfl)
  obtain ⟨C₂, hC₂, ξ₂, hξ₂, h₂⟩ := iMain_add_iDual_tail hm a b c₀ hK hc hcK (-1) (Or.inr rfl)
  refine ⟨hasU2_airySeedU2 a b c₀, ⟨(C₁ + C₂) / 2, by positivity, max ξ₁ ξ₂, lt_max_of_lt_left hξ₁, fun ξ hξ => ?_⟩,
    ⟨(C₁ + C₂) / 2, by positivity, max ξ₁ ξ₂, lt_max_of_lt_left hξ₁, fun ξ hξ => ?_⟩⟩
  · have e1 := h₁ ξ ((le_max_left _ _).trans hξ)
    have e2 := h₂ ξ ((le_max_right _ _).trans hξ)
    set Mn := iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ
    set Dn := iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ
    have hs : Mn = (1 / 2 : ℂ) * ((Mn + ((1 : ℝ) : ℂ) * Dn) + (Mn + ((-1 : ℝ) : ℂ) * Dn)) := by push_cast; ring
    calc ‖Mn‖ = ‖(1 / 2 : ℂ) * ((Mn + ((1 : ℝ) : ℂ) * Dn) + (Mn + ((-1 : ℝ) : ℂ) * Dn))‖ := by rw [← hs]
      _ ≤ (1 / 2) * (‖Mn + ((1 : ℝ) : ℂ) * Dn‖ + ‖Mn + ((-1 : ℝ) : ℂ) * Dn‖) := by
          rw [norm_mul]
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          rw [this]; gcongr; exact norm_add_le _ _
      _ ≤ (1 / 2) * (C₁ * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) +
            C₂ * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring
  · have e1 := h₁ ξ ((le_max_left _ _).trans hξ)
    have e2 := h₂ ξ ((le_max_right _ _).trans hξ)
    set Mn := iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ
    set Dn := iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ
    have hs : Dn = (1 / 2 : ℂ) * ((Mn + ((1 : ℝ) : ℂ) * Dn) - (Mn + ((-1 : ℝ) : ℂ) * Dn)) := by push_cast; ring
    calc ‖Dn‖ = ‖(1 / 2 : ℂ) * ((Mn + ((1 : ℝ) : ℂ) * Dn) - (Mn + ((-1 : ℝ) : ℂ) * Dn))‖ := by rw [← hs]
      _ ≤ (1 / 2) * (‖Mn + ((1 : ℝ) : ℂ) * Dn‖ + ‖Mn + ((-1 : ℝ) : ℂ) * Dn‖) := by
          rw [norm_mul]
          have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by simp
          rw [this]; gcongr; exact norm_sub_le _ _
      _ ≤ (1 / 2) * (C₁ * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) +
            C₂ * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by gcongr
      _ = _ := by ring

/-- The tail of the lift of `D + τ S`: from the tail of the one-level seed `D` and `ConvTailData S`. -/
theorem convTail_add {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {K c : ℝ} (hK : 1 ≤ K) (hc : 2000 ≤ c)
    (hcK : 8 * K ^ 3 ≤ c) {S : ℝ → ℝ} (hS : ConvTailData S (ceBeta1 * K * liftEps c / 2) m c) (τ : ℝ)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∀ ξ : ℝ, ξ₀ ≤ ξ →
      ‖iMain (fun u => airySeedU2 a b c₀ u + τ * S u) (ceBeta1 * K * liftEps c / 2) m c ξ +
          (σ : ℂ) * iDual (fun u => airySeedU2 a b c₀ u + τ * S u) (ceBeta1 * K * liftEps c / 2) m c ξ‖ ≤
        C * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hσn : ‖(σ : ℂ)‖ = 1 := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨CD, hCD, ξD, hξD, hD⟩ := iMain_add_iDual_tail hm a b c₀ hK hc hcK σ hσ
  obtain ⟨Cm, hCm, ξm, hξm, hM⟩ := hS.main
  obtain ⟨Cd, hCd, ξd, hξd, hDu⟩ := hS.dual
  refine ⟨CD + |τ| * (Cm + Cd), by positivity, max ξD (max ξm ξd), lt_max_of_lt_left hξD, fun ξ hξ => ?_⟩
  have hξ0 : 0 < ξ := lt_of_lt_of_le hξD ((le_max_left _ _).trans hξ)
  have eD := hD ξ ((le_max_left _ _).trans hξ)
  have eM := hM ξ (((le_max_left _ _).trans (le_max_right _ _)).trans hξ)
  have eDu := hDu ξ (((le_max_right _ _).trans (le_max_right _ _)).trans hξ)
  have hX := hasU2_airySeedU2 a b c₀
  have hY : HasU2 (fun u => τ * S u) := hS.hasU2.smul τ
  rw [iMain_add hX hY hδ m hc0 hξ0, iDual_add hX hY hδ m hc0 hξ0, iMain_const_mul, iDual_const_mul]
  have hsplit : iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ + (τ : ℂ) * iMain S (ceBeta1 * K * liftEps c / 2) m c ξ +
      (σ : ℂ) * (iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ + (τ : ℂ) * iDual S (ceBeta1 * K * liftEps c / 2) m c ξ) =
      (iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ + (σ : ℂ) * iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ) +
        (τ : ℂ) * (iMain S (ceBeta1 * K * liftEps c / 2) m c ξ + (σ : ℂ) * iDual S (ceBeta1 * K * liftEps c / 2) m c ξ) := by ring
  rw [hsplit]
  have hτ : ‖(τ : ℂ)‖ = |τ| := by simp
  calc _ ≤ ‖iMain (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ + (σ : ℂ) * iDual (airySeedU2 a b c₀) (ceBeta1 * K * liftEps c / 2) m c ξ‖ +
        ‖(τ : ℂ) * (iMain S (ceBeta1 * K * liftEps c / 2) m c ξ + (σ : ℂ) * iDual S (ceBeta1 * K * liftEps c / 2) m c ξ)‖ := norm_add_le _ _
    _ ≤ CD * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) +
        |τ| * (Cm * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ)) + Cd * ξ⁻¹ * Real.log (Real.pi ^ 2 * ξ) ^ (-(3 / 2 : ℝ))) := by
        refine add_le_add eD ?_
        rw [norm_mul, hτ]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg τ)
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, hσn, one_mul]
        exact add_le_add eM eDu
    _ = _ := by ring

/-- **The Hankel eigenfunction lift of `D + τ S`** (`D` one-level, `S` with `ConvTailData`). -/
theorem exists_hankelEigenfn_lift_of_convTail {m : ℕ} (hm : 3 ≤ m) (a b c₀ : ℝ) {K c : ℝ} (hK : 1 ≤ K)
    (hc : 2000 ≤ c) (hcK : 8 * K ^ 3 ≤ c) {S : ℝ → ℝ} (hS : ConvTailData S (ceBeta1 * K * liftEps c / 2) m c)
    (τ : ℝ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∃ f : ℝ → ℝ, IsHankelEigenfn c σ f ∧
      (∀ ξ : ℝ, 0 < ξ → ((c ^ (1 / 3 : ℝ) * hankelRho0 c (c * ξ) * f (c * ξ) : ℝ) : ℂ) =
        iMain (fun u => airySeedU2 a b c₀ u + τ * S u) (ceBeta1 * K * liftEps c / 2) m c ξ +
          (σ : ℂ) * iDual (fun u => airySeedU2 a b c₀ u + τ * S u) (ceBeta1 * K * liftEps c / 2) m c ξ) ∧
      f 0 = σ * ∫ Δ in Ioi (0 : ℝ), f Δ * hankelRho0 c Δ := by
  have hc0 : 0 < c := by linarith
  have hδ : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  obtain ⟨f, hf, hrep, hf0, -⟩ := exists_hankelEigenfn_lift_general
    ((hasU2_airySeedU2 a b c₀).add (hS.hasU2.smul τ)) hδ m (by linarith) hσ (convTail_add hm a b c₀ hK hc hcK hS τ hσ)
  exact ⟨f, hf, hrep, hf0⟩

/-- info: 'FormalResearch.SignUncertainty.iMain_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iMain_add

/-- info: 'FormalResearch.SignUncertainty.iDual_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iDual_add

/-- info: 'FormalResearch.SignUncertainty.iMain_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iMain_const_mul

/-- info: 'FormalResearch.SignUncertainty.iDual_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms iDual_const_mul

/-- info: 'FormalResearch.SignUncertainty.convTailData_of_oneLevel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convTailData_of_oneLevel

/-- info: 'FormalResearch.SignUncertainty.convTail_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms convTail_add

/-- info: 'FormalResearch.SignUncertainty.exists_hankelEigenfn_lift_of_convTail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_hankelEigenfn_lift_of_convTail

end FormalResearch.SignUncertainty

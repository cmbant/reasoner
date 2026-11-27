module

public import FormalResearch.SignUncertainty.AiryLaplaceGeneral
public import FormalResearch.SignUncertainty.GenRationalAiryTail
public import FormalResearch.SignUncertainty.GenRationalAiryU1
public import FormalResearch.SignUncertainty.MiddleBandPositivityDual
public import FormalResearch.SignUncertainty.MiddleBandE6
public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.CohnElkies.WindowSmoothConv
public import FormalResearch.SignUncertainty.CeLiftSign
public import FormalResearch.SignUncertainty.Gt1Interface
public import FormalResearch.SignUncertainty.UctPosFloorWpos
public import FormalResearch.SignUncertainty.UctAiryTransSmall

/-!
# Dual-line positivity and `O6FamilyEst` for generalized rational-Airy seeds (`lem:ce-dual-line`)

Source: `CFT/sign_uncertainty/paper/ce_lift_proofs.tex`, Lemma `lem:ce-dual-line` and `(eq:ce-dual-floors)`.

* `o6FamilyEst_of_genRational_family`: `O6FamilyEst` for any uniformly bounded family of finite linear
  combinations of generalized rational-Airy seeds (`HasGenRationalAiryCoeffs`), bundling `(e4)`, `(e5)`, `(e6)`
  over `(K, c)`.
* `airyTwistedLaplaceC_zero_eq`: exact evaluation `X̃(0) = k ∫_ℝ X(u) du`.
* `ce_dual_floors` (`eq:ce-dual-floors`): for any `X ∈ ℛ_Ai^gen` with `∫ X = 0`, `β_∞(X) < 0`, and
  `β_+(X) > 0`, there exist `0 < x₀ < B`, `c₁', d₀ > 0` with `c₁' √x ≤ X̃(c_s x)` on `[0, x₀]`
  and `d₀ (1 + x)^{-5/2} ≤ X̃(c_s x)` on `[B/2, ∞)`.
* `ce_dual_line` (`lem:ce-dual-line`): for `D_c = X + ε_c Z_c` with `Z_c` a uniformly bounded finite
  linear combination in `ℛ_Ai^gen` having positive mass and a positive floor on `J = [x₀/3, 2B]`, the weighted
  dual symbol `W_{D_c}(w) = M_ψ(w) (D_c)̃(i c_s w)` satisfies all dual-line positivity, small-`x` / tail floors,
  `hA1_D` local variation, and `hA2_D` strip bounds needed by `PreEdgeTangencyData` uniformly for large `c`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex
open scoped Real BigOperators

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies FormalResearch.Special

private lemma gt1Bounds_zero_fun : Gt1Bounds 0 (fun _ : ℝ => (0 : ℂ)) := by
  have hzero_deriv : ∀ k : ℕ, k ≠ 0 → iteratedDeriv k (fun _ : ℝ => (0 : ℂ)) = 0 := fun k hk => by
    rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨n, rfl⟩
    ext x
    rw [iteratedDeriv_succ']
    simp
  refine gt1Bounds_of_bounds (W := fun _ => (0 : ℂ)) (A := 0) ⟨contDiffOn_const, contDiffOn_const⟩
    ?_ ?_ (by simp) (fun v _ _ => by simp)
  · intro j hj _ v _ _
    rw [hzero_deriv j (by omega)]; simp
  · intro j _ v _
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · rw [hzero_deriv j hj]; simp

private lemma norm_cpow_half_eq {y : ℂ} :
    ‖y ^ (1 / 2 : ℂ)‖ = ‖y‖ ^ (1 / 2 : ℝ) := by
  by_cases hy0 : y = 0
  · simp [hy0]
  · rw [Complex.norm_cpow_of_ne_zero hy0]
    have hre : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    have him : (1 / 2 : ℂ).im = 0 := by norm_num
    rw [hre, him, mul_zero, Real.exp_zero, div_one]

private lemma e1r_lower {t : ℝ} (ht : 0 ≤ t) : (1 + t)⁻¹ ≤ uctE1r t := by
  rcases eq_or_lt_of_le ht with rfl | ht0
  · have : uctE1r 0 = 1 := by
      have h0 := uctE1r_cast 0
      simp only [Complex.ofReal_zero, bsplineE1_zero] at h0
      exact Complex.ofReal_injective h0.symm
    simp [this]
  · have hexp : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    have hexp' : Real.exp (-t) * (1 + t) ≤ 1 := by
      calc Real.exp (-t) * (1 + t) ≤ Real.exp (-t) * Real.exp t :=
            mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
        _ = 1 := by rw [← Real.exp_add]; simp
    have hmul := uctE1r_mul t
    have h1 : t ≤ (1 + t) * (1 - Real.exp (-t)) := by nlinarith
    rw [← hmul] at h1
    have h2 : (1 + t)⁻¹ * t ≤ uctE1r t * t := by
      calc (1 + t)⁻¹ * t = t * (1 + t)⁻¹ := by ring
        _ ≤ ((1 + t) * (uctE1r t * t)) * (1 + t)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = uctE1r t * t := by field_simp [show (1 + t) ≠ 0 by positivity]
    exact le_of_mul_le_mul_right h2 ht0

private lemma e1r_le_one {t : ℝ} (ht : 0 ≤ t) : uctE1r t ≤ 1 := by
  have h0 : uctE1r 0 = 1 := by
    have := uctE1r_cast 0
    simp only [Complex.ofReal_zero, bsplineE1_zero] at this
    exact Complex.ofReal_injective this.symm
  exact (uctE1r_anti ht).trans h0.le

private lemma hasU2_finset_sum {ι : Type*} (t : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ t, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i)) (α : ι → ℝ) :
    HasU2 (fun u => ∑ i ∈ t, α i * (B i (u : ℂ)).re) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
      have hz : (fun _ : ℝ => (0 : ℝ)) = airySeedU2 0 0 0 := funext fun u => by simp [airySeedU2]
      simpa using hz ▸ hasU2_airySeedU2 0 0 0
  | @insert a t' hat ih =>
      have hUa : HasU2 (fun u => α a * (B a (u : ℂ)).re) :=
        (hasU2_of_genRational (hB a (Finset.mem_insert_self a t'))).smul _
      have hUt : HasU2 (fun u => ∑ i ∈ t', α i * (B i (u : ℂ)).re) :=
        ih (fun i hi => hB i (Finset.mem_insert_of_mem hi))
      have hfn : (fun u : ℝ => ∑ i ∈ insert a t', α i * (B i (u : ℂ)).re) =
          fun u : ℝ => α a * (B a (u : ℂ)).re + ∑ i ∈ t', α i * (B i (u : ℂ)).re :=
        funext fun u => Finset.sum_insert hat
      rw [hfn]
      exact hUa.add hUt

private lemma airyTwistedLaplaceC_finset_sum {ι : Type*} (t : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ t, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i)) (α : ι → ℝ)
    {w : ℂ} (hw : 0 ≤ w.re) :
    airyTwistedLaplaceC (fun u => ∑ i ∈ t, α i * (B i (u : ℂ)).re) ((ceCs : ℂ) * w) =
      ∑ i ∈ t, (α i : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w) := by
  classical
  have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw
  induction t using Finset.induction_on with
  | empty => simp [airyTwistedLaplaceC]
  | @insert a t' hat ih =>
      have hUa : HasU2 (fun u => α a * (B a (u : ℂ)).re) :=
        (hasU2_of_genRational (hB a (Finset.mem_insert_self a t'))).smul _
      have hUt : HasU2 (fun u => ∑ i ∈ t', α i * (B i (u : ℂ)).re) :=
        hasU2_finset_sum t' B b₀₀ b₁₁ (fun i hi => hB i (Finset.mem_insert_of_mem hi)) α
      have hfn : (fun u : ℝ => ∑ i ∈ insert a t', α i * (B i (u : ℂ)).re) =
          fun u : ℝ => α a * (B a (u : ℂ)).re + ∑ i ∈ t', α i * (B i (u : ℂ)).re :=
        funext fun u => Finset.sum_insert hat
      rw [hfn, airyTwistedLaplaceC_add (hUa.integrable _ hre) (hUt.integrable _ hre),
        airyTwistedLaplaceC_const_mul, ih (fun i hi => hB i (Finset.mem_insert_of_mem hi)),
        Finset.sum_insert hat]

/-- `O6FamilyEst` for any uniformly bounded finite linear combination family
`F K c u = ∑ i ∈ s, α i K c * (B i u).re` with `B i ∈ ℛ_Ai^gen` and `m ≥ 3`. -/
theorem o6FamilyEst_of_genRational_family {ι : Type*} (s : Finset ι)
    (B : ι → ℂ → ℂ) (β₀₀ β₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (β₀₀ i) (β₁₁ i))
    (α : ι → ℝ → ℝ → ℝ) (R δ₁ : ℝ) (hR : 0 ≤ R) (hδ₁ : 0 < δ₁)
    (hα : ∀ i ∈ s, ∀ K c : ℝ, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c → |α i K c| ≤ R)
    {m : ℕ} (hm : 3 ≤ m) :
    O6FamilyEst m δ₁ (fun K c u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re)
      (fun K c => ∑ i ∈ s, α i K c * (β₀₀ i + β₁₁ i))
      (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ)) := by
  classical
  have hg0 : 0 < 2 * ceK * cA * ceCs ^ (1 / 2 : ℝ) := by
    have := ceK_pos; have := cA_pos; have := ceCs_pos; positivity
  have hF_cont : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      Continuous (fun u : ℝ => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) := by
    intro K c _ _ _ _
    induction s using Finset.induction_on with
    | empty => simpa using continuous_const
    | @insert a t hat ih =>
        have hc_a : Continuous (fun u : ℝ => α a K c * (B a (u : ℂ)).re) :=
          continuous_const.mul (Complex.continuous_re.comp
            ((hB a (Finset.mem_insert_self a t)).1.1.continuous.comp Complex.continuous_ofReal))
        have hc_t := ih (fun i hi => hB i (Finset.mem_insert_of_mem hi))
          (fun i hi => hα i (Finset.mem_insert_of_mem hi))
        have hfn : (fun u : ℝ => ∑ i ∈ insert a t, α i K c * (B i (u : ℂ)).re) =
            fun u : ℝ => α a K c * (B a (u : ℂ)).re + ∑ i ∈ t, α i K c * (B i (u : ℂ)).re :=
          funext fun u => Finset.sum_insert hat
        rw [hfn]; exact hc_a.add hc_t
  have hconv : ∀ {X : ℝ → ℝ}, Continuous X → ∀ {δ₀ : ℝ}, 0 < δ₀ → ∀ x : ℝ,
      windowSmooth δ₀ m X x = ∫ t in Icc (0 : ℝ) δ₀, X (x + t) * bspline m δ₀ t :=
    fun {_} hX {_} hδ x => windowSmooth_eq_bspline_integral hX hδ (by omega) x
  let α' : ι → ℝ → ℝ → ℝ := fun i K c =>
    if 1 ≤ K ∧ 2000 ≤ c ∧ 8 * K ^ 3 ≤ c ∧ (K / δ₁) ^ 3 ≤ c then α i K c else 0
  have hα' : ∀ i ∈ s, ∀ K c : ℝ, |α' i K c| ≤ R := by
    intro i hi K c
    dsimp [α']
    split_ifs with h
    · exact hα i hi K c h.1 h.2.1 h.2.2.1 h.2.2.2
    · simpa using hR
  have hα'_eq : ∀ {K c : ℝ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      ∀ i, α' i K c = α i K c := fun h1 h2 h3 h4 i => by
    dsimp [α']; simp [h1, h2, h3, h4]
  have he4 : ∃ C > 0, ∀ {K M₁ c ξ : ℝ}, 1 ≤ K → 1 ≤ M₁ → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      2000 ≤ c → 0 < ξ → 100 ≤ hbS c ξ → M₁ * (K ^ 2)⁻¹ * c ^ (2 / 3 : ℝ) ≤ hbS c ξ →
      ‖iMain (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((((∑ i ∈ s, α i K c * (β₀₀ i + β₁₁ i)) * (2 * ceK * cA * ceCs ^ (1 / 2 : ℝ))) *
              Real.sqrt Real.pi * hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ) : ℝ) : ℂ)‖ ≤
        C * (M₁ ^ (-((m : ℝ) / 2)) + K ^ (-(m : ℝ)) + hbS c ξ ^ (-(1 / 2 : ℝ))) *
          (hbA c ξ ^ (-(3 / 2 : ℝ)) / (2 * Real.pi * ξ)) := by
    obtain ⟨C4, hC4, h4⟩ := hb_estimate_genRational_family s B β₀₀ β₁₁ hB hR hα' (m := m) (by omega)
    refine ⟨C4, hC4, fun {K M₁ c ξ} hK hM₁ hc8 hcδ hc2k hξ hS100 hMS => ?_⟩
    have heqF : (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) =
        fun u => ∑ i ∈ s, α' i K c * (B i (u : ℂ)).re := by
      ext u; refine Finset.sum_congr rfl fun i _ => ?_; rw [hα'_eq hK hc2k hc8 hcδ]
    have heqB : (∑ i ∈ s, α i K c * (β₀₀ i + β₁₁ i)) = ∑ i ∈ s, α' i K c * (β₀₀ i + β₁₁ i) :=
      Finset.sum_congr rfl fun i _ => by rw [hα'_eq hK hc2k hc8 hcδ]
    rw [heqF, heqB]
    exact h4 hK hM₁ hc8 hc2k hξ hS100 hMS
  have hSym_exists : ∀ i ∈ s, ∃ C > 0, ∀ {δ₀ : ℝ} (m : ℕ) {w : ℂ}, 0 ≤ δ₀ → 0 ≤ w.re →
      ‖liftSymbol (fun u => (B i (u : ℂ)).re) δ₀ m w‖ ≤ C * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) :=
    fun i hi => hasU2_norm_liftSymbol_le_unif (hasU2_of_genRational (hB i hi))
  choose CSym hCSym_pos hCSym_bd using hSym_exists
  let CW : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CSym i hi else 0) + 1
  have hCW : 0 < CW := by
    have hsum_nn : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CSym i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs
      exact (hCSym_pos i hi).le
    positivity
  have hSym_sum : ∀ {K c δ₀ : ℝ} {w : ℂ}, 1 ≤ K → 2000 ≤ c → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      0 ≤ δ₀ → 0 ≤ w.re →
      ‖liftSymbol (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) δ₀ m w‖ ≤
        CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
    intro K c δ₀ w hK hc2k hc8 hcδ hδ0 hw
    have hsplit : liftSymbol (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) δ₀ m w =
        ∑ i ∈ s, (α i K c : ℂ) * liftSymbol (fun u => (B i (u : ℂ)).re) δ₀ m w := by
      unfold liftSymbol
      rw [airyTwistedLaplaceC_finset_sum s B β₀₀ β₁₁ hB (fun i => α i K c) hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [hsplit]
    calc ‖∑ i ∈ s, (α i K c : ℂ) * liftSymbol (fun u => (B i (u : ℂ)).re) δ₀ m w‖
        ≤ ∑ i ∈ s, ‖(α i K c : ℂ) * liftSymbol (fun u => (B i (u : ℂ)).re) δ₀ m w‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CSym i hi else 0) * (1 + |w.im|) ^ (-(5 / 2 : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          split_ifs
          exact mul_le_mul (hα i hi K c hK hc2k hc8 hcδ) (hCSym_bd i hi m hδ0 hw) (norm_nonneg _) hR
      _ = (R * ∑ i ∈ s, if hi : i ∈ s then CSym i hi else 0) * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) := by
          simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ CW * (1 + |w.im|) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by dsimp [CW]; linarith) (by positivity)
  have he5 : ∀ Sw : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ {K c ξ : ℝ}, 1 ≤ K → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c →
      32768 ≤ c → 0 < ξ → |hbS c ξ| ≤ Sw →
      ‖iMain (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) *
            windowSmooth (ceBeta1 * K * liftEps c / 2) m (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re)
              (-(ceBeta1 * hbS c ξ) - liftEps c / (2 * ceCs)) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (liftEps c ^ 2 + ((1 + (ceBeta1 * K * liftEps c / 2) * c ^ (1 / 3 : ℝ)) ^ m)⁻¹ * c ^ (-(1 / 2 : ℝ))) := by
    intro Sw
    obtain ⟨C5, hC5, hwt⟩ := window_translation m (by omega) Sw CW 1 hCW zero_lt_one
    refine ⟨C5, hC5, fun {K c ξ} hK hc8 hcδ hc32 hξ hSw => ?_⟩
    have hc2k : 2000 ≤ c := by linarith
    have hc0 : 0 < c := by linarith
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have hiDual0 : iDual (fun _ : ℝ => (0 : ℝ)) (ceBeta1 * K * liftEps c / 2) m c ξ = 0 := by
      simp [iDual, iDualIntegrand, liftSymbol, airyTwistedLaplaceC]
    have hD0 : ∀ {w : ℂ}, 0 ≤ w.re → ‖airyTwistedLaplaceC (fun _ : ℝ => (0 : ℝ)) ((ceCs : ℂ) * w)‖ ≤
        1 * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := fun {_} _ => by
      simp [airyTwistedLaplaceC]; positivity
    have hres := hwt (hasU2_finset_sum s B β₀₀ β₁₁ hB (fun i => α i K c))
      (hF_cont hK hc2k hc8 hcδ)
      (fun {δ₀ w} hδ hw => hSym_sum hK hc2k hc8 hcδ hδ hw) hD0 hδ0 hc32 hξ hSw
    simpa [hiDual0] using hres
  have hGt1_i : ∀ i ∈ s, ∃ A > 0, ∀ {δ₀ : ℝ}, δ₀ ∈ Icc (0 : ℝ) 2 →
      Gt1Bounds A (liftW (fun u => (B i (u : ℂ)).re) δ₀ m) :=
    fun i hi => gt1Bounds_of_genRational (hB i hi) hm
  choose AG hAG_pos hAG_bd using hGt1_i
  let A_tot : ℝ := R * ∑ i ∈ s, if hi : i ∈ s then AG i hi else 0
  have hA_tot : 0 ≤ A_tot := by
    have hsum_nn : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then AG i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs
      exact (hAG_pos i hi).le
    positivity
  have he6 : ∃ C : ℝ, 0 ≤ C ∧ ∀ {K c ξ L : ℝ}, 1 ≤ K → 8 * K ^ 3 ≤ c → (K / δ₁) ^ 3 ≤ c → 2000 ≤ c →
      0 < ξ → L = Real.log (Real.pi ^ 2 * ξ) → 0 < L → L ≤ 0.002 → 100 ≤ hbS c ξ →
      ‖iMain (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m c ξ -
          ((ceK * ceBeta1 / (Real.pi ^ 2 * ξ) : ℝ) : ℂ) *
            ((windowSmooth (ceBeta1 * K * liftEps c / 2) m (fun u => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re)
              (-(edgeKappa0 L * ceBeta1 * hbS c ξ + liftEps c / (2 * ceCs))) : ℝ) : ℂ)‖ ≤
        C * ξ⁻¹ * (hbS c ξ ^ (-(3 / 2 : ℝ)) * (liftEps c ^ 2 * hbS c ξ) + c ^ (-(5 / 2 : ℝ))) := by
    obtain ⟨ϑ, K1, K2, hϑ⟩ := prof_exists
    obtain ⟨C6, hC6, ho5⟩ := o5_e6 hϑ A_tot hA_tot
    refine ⟨C6, hC6, fun {K c ξ L} hK hc8 hcδ hc2k hξ hL hL0 hL2 hS100 => ?_⟩
    have hc0 : 0 < c := by linarith
    have hc2 : 2 ≤ c := by linarith
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have hδ2 : ceBeta1 * K * liftEps c / 2 ≤ 2 := by
      have h1 := ceBeta1_lt_eight
      have h2 := ce_delta_half hK hc0 hc8
      nlinarith [ceBeta1_pos]
    have hδ_mem : ceBeta1 * K * liftEps c / 2 ∈ Icc (0 : ℝ) 2 := ⟨hδ0, hδ2⟩
    have hGt1_sum : ∀ (t : Finset ι),
        (∀ i ∈ t, HasGenRationalAiryCoeffs (B i) (β₀₀ i) (β₁₁ i)) →
        ∀ (B_t : ι → ℝ),
        (∀ i ∈ t, 0 ≤ B_t i ∧ Gt1Bounds (B_t i) (liftW (fun u => (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m)) →
        (∀ i ∈ t, |α i K c| ≤ R) →
        Gt1Bounds (R * ∑ i ∈ t, B_t i) (liftW (fun u => ∑ i ∈ t, α i K c * (B i (u : ℂ)).re)
          (ceBeta1 * K * liftEps c / 2) m) := by
      intro t ht B_t hBt hαt
      induction t using Finset.induction_on with
      | empty =>
          have h0 : liftW (fun _ : ℝ => (0 : ℝ)) (ceBeta1 * K * liftEps c / 2) m = fun _ => 0 := by
            ext v; simp [liftW, liftSymbol, airyTwistedLaplaceC]
          simpa [h0] using gt1Bounds_zero_fun
      | @insert a t' hat' ih =>
          have hUa : HasU2 (fun u => α a K c * (B a (u : ℂ)).re) :=
            (hasU2_of_genRational (ht a (Finset.mem_insert_self a t'))).smul _
          have hUt : HasU2 (fun u => ∑ i ∈ t', α i K c * (B i (u : ℂ)).re) :=
            hasU2_finset_sum t' B β₀₀ β₁₁ (fun i hi => ht i (Finset.mem_insert_of_mem hi)) (fun i => α i K c)
          have hGt_t := ih (fun i hi => ht i (Finset.mem_insert_of_mem hi))
            (fun i hi => hBt i (Finset.mem_insert_of_mem hi))
            (fun i hi => hαt i (Finset.mem_insert_of_mem hi))
          have ha_bd := (hBt a (Finset.mem_insert_self a t')).2
          have hsmul : Gt1Bounds (R * B_t a) (fun v => (α a K c : ℂ) *
              liftW (fun u => (B a (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m v) := by
            refine Gt1Bounds.mono ?_ (Gt1Bounds.smul (α a K c : ℂ) ha_bd)
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hαt a (Finset.mem_insert_self a t'))
              (hBt a (Finset.mem_insert_self a t')).1
          have hW_eq : liftW (fun u => ∑ i ∈ insert a t', α i K c * (B i (u : ℂ)).re)
                (ceBeta1 * K * liftEps c / 2) m =
              fun v => (α a K c : ℂ) * liftW (fun u => (B a (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m v +
                liftW (fun u => ∑ i ∈ t', α i K c * (B i (u : ℂ)).re) (ceBeta1 * K * liftEps c / 2) m v := by
            ext v
            have hfn : (fun u : ℝ => ∑ i ∈ insert a t', α i K c * (B i (u : ℂ)).re) =
                fun u : ℝ => α a K c * (B a (u : ℂ)).re + ∑ i ∈ t', α i K c * (B i (u : ℂ)).re :=
              funext fun u => Finset.sum_insert hat'
            unfold liftW
            have hwre : 0 ≤ ((v : ℂ) * Complex.I).re := by simp
            rw [hfn, liftSymbol_add_seed hUa hUt _ m hwre, liftSymbol_const_mul_seed]
          rw [hW_eq, Finset.sum_insert hat', mul_add]
          exact hsmul.add hGt_t
    have hGt1_F := hGt1_sum s hB (fun i => if hi : i ∈ s then AG i hi else 0)
      (fun i hi => by
        split_ifs with hi'
        exact ⟨(hAG_pos i hi').le, hAG_bd i hi' hδ_mem⟩)
      (fun i hi => hα i hi K c hK hc2k hc8 hcδ)
    exact ho5 (hasU2_finset_sum s B β₀₀ β₁₁ hB (fun i => α i K c))
      (hF_cont hK hc2k hc8 hcδ) hδ0 hc2 hξ hL hL0 hL2 hS100 hGt1_F
  exact ⟨hg0, hF_cont, hconv, he4, he5, he6⟩

/-- Evaluation of `airyTwistedLaplaceC` at `w = 0`. -/
lemma airyTwistedLaplaceC_zero_eq (X : ℝ → ℝ) :
    airyTwistedLaplaceC X 0 = ((ceK * ∫ u : ℝ, X u : ℝ) : ℂ) := by
  unfold airyTwistedLaplaceC
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_div,
    Complex.exp_zero, mul_one, zero_mul]
  rw [integral_complex_ofReal]
  push_cast; rfl

/-- **`eq:ce-dual-floors` (`ce_lift_proofs.tex`):** positive-real dual-line floors near `x = 0` (`x^{1/2}`)
and at infinity (`(1 + x)^{-5/2}`) for any `F ∈ ℛ_Ai^gen` with `∫ X = 0`, `β_∞(F) < 0`, and
`β_+(F) > 0`. -/
theorem ce_dual_floors {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ} (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁)
    (hmass : ∫ u : ℝ, (F (u : ℂ)).re = 0)
    (hbinf : airyBetaInf F < 0) (hbplus : 0 < airyBetaPlus F) :
    ∃ x₀ B c₁' d₀ : ℝ, 0 < x₀ ∧ x₀ < B ∧ 0 < c₁' ∧ 0 < d₀ ∧
      (∀ x ∈ Icc (0 : ℝ) x₀, c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re) ∧
      (∀ x : ℝ, B / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re) := by
  let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
  obtain ⟨_, _, hβinf, _⟩ := hF.beta_eq
  have hβinf_neg : β₀₀ + β₁₁ < 0 := by linarith
  obtain ⟨C₀, hC₀, hexp⟩ := u1c_expansion_of_genRational hF ceCs ceCs_pos.le
  let c_lead : ℝ := -(β₀₀ + β₁₁) * (2 * ceK * cA) * Real.sqrt ceCs
  have hc_lead : 0 < c_lead := by
    have := ceK_pos; have := cA_pos; have := ceCs_pos; have : 0 < -(β₀₀ + β₁₁) := by linarith
    positivity
  let denom : ℝ := 2 * (C₀ * ceCs + 1)
  have hdenom : 0 < denom := by have := ceCs_pos; positivity
  let x₀ : ℝ := min 1 ((c_lead / denom) ^ 2)
  have hx₀ : 0 < x₀ := lt_min one_pos (by positivity)
  have hsmall : ∀ x ∈ Icc (0 : ℝ) x₀, (c_lead / 2) * Real.sqrt x ≤
      (airyTwistedLaplaceC X ((ceCs * x : ℝ) : ℂ)).re := by
    intro x ⟨hx0, hxx₀⟩
    have hx1 : x ≤ 1 := hxx₀.trans (min_le_left _ _)
    have hx_le : Real.sqrt x ≤ c_lead / denom := by
      have hsq : x ≤ (c_lead / denom) ^ 2 := hxx₀.trans (min_le_right _ _)
      exact (Real.sqrt_le_sqrt hsq).trans (Real.sqrt_sq (by positivity)).le
    let y : ℂ := ((ceCs * x : ℝ) : ℂ)
    have hyre : 0 ≤ y.re := by simp [y]; exact mul_nonneg ceCs_pos.le hx0
    have hynorm : ‖y‖ ≤ ceCs := by
      rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
      exact mul_le_of_le_one_right ceCs_pos.le hx1
    have h0eq : airyTwistedLaplaceC X 0 = 0 := by rw [airyTwistedLaplaceC_zero_eq]; simp [X, hmass]
    have hpow : (y ^ (1 / 2 : ℂ) : ℂ) = ((Real.sqrt (ceCs * x) : ℝ) : ℂ) := by
      dsimp [y]
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow (mul_nonneg ceCs_pos.le hx0), Real.sqrt_eq_rpow]
    have hbd : ‖airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) *
        ((Real.sqrt (ceCs * x) : ℝ) : ℂ)‖ ≤ C₀ * ‖y‖ := by
      have h1 := hexp hyre hynorm
      change ‖airyTwistedLaplaceC X y - airyTwistedLaplaceC X 0 +
          (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ ≤ C₀ * ‖y‖ at h1
      rwa [h0eq, sub_zero, hpow] at h1
    have hre_bd : |(airyTwistedLaplaceC X y).re + (β₀₀ + β₁₁) * (2 * ceK * cA) * Real.sqrt (ceCs * x)| ≤
        C₀ * (ceCs * x) := by
      have hab := Complex.abs_re_le_norm (airyTwistedLaplaceC X y +
        (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * ((Real.sqrt (ceCs * x) : ℝ) : ℂ))
      have hre_eq : (airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) *
            ((Real.sqrt (ceCs * x) : ℝ) : ℂ)).re =
          (airyTwistedLaplaceC X y).re + (β₀₀ + β₁₁) * (2 * ceK * cA) * Real.sqrt (ceCs * x) := by
        simp [Complex.add_re, Complex.mul_re]
      have hyabs : ‖y‖ = ceCs * x := by
        rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
      rw [hre_eq] at hab; rw [hyabs] at hbd; exact hab.trans hbd
    have hre_lower : c_lead * Real.sqrt x - C₀ * ceCs * x ≤ (airyTwistedLaplaceC X y).re := by
      have := (abs_le.mp hre_bd).1
      dsimp [c_lead]
      rw [Real.sqrt_mul ceCs_pos.le x] at this
      linarith
    have hx_err : C₀ * ceCs * x ≤ (c_lead / 2) * Real.sqrt x := by
      have h1 : C₀ * ceCs * Real.sqrt x ≤ (C₀ * ceCs + 1) * (c_lead / denom) := by
        calc C₀ * ceCs * Real.sqrt x ≤ (C₀ * ceCs + 1) * Real.sqrt x := by
              nlinarith [Real.sqrt_nonneg x]
          _ ≤ (C₀ * ceCs + 1) * (c_lead / denom) :=
              mul_le_mul_of_nonneg_left hx_le (by have := ceCs_pos; positivity)
      have h2 : (C₀ * ceCs + 1) * (c_lead / denom) = c_lead / 2 := by
        dsimp [denom]
        have hne : C₀ * ceCs + 1 ≠ 0 := by have := ceCs_pos; positivity
        field_simp [hne]
      calc C₀ * ceCs * x = C₀ * ceCs * (Real.sqrt x * Real.sqrt x) := by rw [Real.mul_self_sqrt hx0]
        _ = (C₀ * ceCs * Real.sqrt x) * Real.sqrt x := by ring
        _ ≤ (c_lead / 2) * Real.sqrt x := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg x)
    linarith
  let L_pos : ℝ := airyBetaPlus F * (2 / Real.sqrt Real.pi)
  have hL_pos : 0 < L_pos := by positivity
  have htend := airyLaplace_genRational_tendsto hF
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨Y0, hY0⟩ := htend (L_pos / 2) (by positivity)
  let Y : ℝ := max Y0 1
  have hY1 : 1 ≤ Y := le_max_right _ _
  have hY_floor : ∀ y : ℝ, Y ≤ y → (L_pos / 2) * y ^ (-(5 / 2 : ℝ)) ≤ airyLaplace X y := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le zero_lt_one (hY1.trans hy)
    have hdist := hY0 y (le_trans (le_max_left Y0 1) hy)
    rw [Real.dist_eq, abs_lt] at hdist
    have hup : L_pos / 2 ≤ y ^ (5 / 2 : ℝ) * airyLaplace X y := by
      have : -(L_pos / 2) < y ^ (5 / 2 : ℝ) * airyLaplace X y - L_pos := hdist.1
      linarith
    have hp := mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg hy0.le (-(5 / 2 : ℝ)))
    have hpow1 : y ^ (5 / 2 : ℝ) * airyLaplace X y * y ^ (-(5 / 2 : ℝ)) = airyLaplace X y := by
      calc y ^ (5 / 2 : ℝ) * airyLaplace X y * y ^ (-(5 / 2 : ℝ))
          = airyLaplace X y * (y ^ (5 / 2 : ℝ) * y ^ (-(5 / 2 : ℝ))) := by ring
        _ = airyLaplace X y * 1 := by rw [← Real.rpow_add hy0]; norm_num
        _ = airyLaplace X y := mul_one _
    linarith
  let B : ℝ := max (2 * x₀ + 2) (2 * Y / ceCs + 2)
  have hx₀B : x₀ < B := by have := le_max_left (2 * x₀ + 2) (2 * Y / ceCs + 2); linarith
  let M_scale : ℝ := max 1 ceCs
  have hM_scale : 0 < M_scale := by positivity
  let d₀ : ℝ := ceK * (L_pos / 2) * M_scale ^ (-(5 / 2 : ℝ))
  have hd₀ : 0 < d₀ := by have := ceK_pos; positivity
  refine ⟨x₀, B, c_lead / 2, d₀, hx₀, hx₀B, by positivity, hd₀, hsmall, fun x hx => ?_⟩
  have hBY : Y / ceCs ≤ B / 2 := by
    have h1 : 2 * (Y / ceCs) ≤ B := by
      have hmax : 2 * Y / ceCs + 2 ≤ B := le_max_right _ _
      linarith [show 2 * (Y / ceCs) = 2 * Y / ceCs by ring]
    linarith
  have hxY : Y ≤ ceCs * x := (div_le_iff₀' ceCs_pos).mp (hBY.trans hx)
  have hx0 : 0 ≤ x := by
    have : 0 ≤ Y / ceCs := div_nonneg (zero_le_one.trans hY1) ceCs_pos.le
    linarith
  have hce_scale : ceCs * x ≤ M_scale * (1 + x) :=
    mul_le_mul (le_max_right 1 ceCs) (by linarith) hx0 hM_scale.le
  have hrpow_cmp : M_scale ^ (-(5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (ceCs * x) ^ (-(5 / 2 : ℝ)) := by
    rw [← Real.mul_rpow hM_scale.le (by linarith)]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos ceCs_pos (lt_of_lt_of_le (div_pos (zero_lt_one.trans_le hY1) ceCs_pos) (hBY.trans hx)))
      hce_scale (by norm_num)
  have hlap := hY_floor (ceCs * x) hxY
  have hre_eq : (airyTwistedLaplaceC X ((ceCs * x : ℝ) : ℂ)).re = ceK * airyLaplace X (ceCs * x) := by
    rw [airyTwistedLaplaceC_ofReal, Complex.ofReal_re]; unfold airyTwistedLaplace airyLaplace; ring
  rw [hre_eq]
  calc d₀ * (1 + x) ^ (-(5 / 2 : ℝ))
      = ceK * ((L_pos / 2) * (M_scale ^ (-(5 / 2 : ℝ)) * (1 + x) ^ (-(5 / 2 : ℝ)))) := by
          dsimp [d₀]; ring
    _ ≤ ceK * ((L_pos / 2) * (ceCs * x) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrpow_cmp (by positivity)) ceK_pos.le
    _ ≤ ceK * airyLaplace X (ceCs * x) := mul_le_mul_of_nonneg_left hlap ceK_pos.le

private lemma airyTwistedLaplace_eq_ceK_airyLaplace (X : ℝ → ℝ) (y : ℝ) :
    airyTwistedLaplace X y = ceK * airyLaplace X y := by
  unfold airyTwistedLaplace airyLaplace; ring

private lemma liftEps_le_one_of_two_le {c : ℝ} (hc : 2 ≤ c) : liftEps c ≤ 1 := by
  have hc0 : 0 < c := by linarith
  have hcube := liftEps_cube_mul hc0
  by_contra hgt
  push Not at hgt
  have hpow : 1 < liftEps c ^ 3 := by simpa using pow_lt_pow_left₀ hgt zero_le_one (by norm_num : 3 ≠ 0)
  nlinarith

private lemma ceDualLine_hsmall_bound {X : ℝ → ℝ} (c₁' m_Z CZ_loc c_min : ℝ)
    (hX_small : ∀ x ∈ Icc (0 : ℝ) x₀, c₁' * Real.sqrt x ≤ airyTwistedLaplace X (ceCs * x))
    (Z : ℝ → ℝ → ℝ)
    (hZ0 : ∀ c : ℝ, c_min ≤ c → ceK * m_Z ≤ airyTwistedLaplace (Z c) 0)
    (hZ_loc : ∀ c x : ℝ, c_min ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      |airyTwistedLaplace (Z c) (ceCs * x) - airyTwistedLaplace (Z c) 0| ≤ CZ_loc * Real.sqrt x)
    {c x : ℝ} (hc_min : c_min ≤ c) (hc0 : 0 < c) (hx : x ∈ Icc (0 : ℝ) x₀)
    (hε : liftEps c * CZ_loc ≤ c₁' / 2) :
    (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
      airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
  have hX := hX_small x hx
  have hZ_lo : ceK * m_Z - CZ_loc * Real.sqrt x ≤ airyTwistedLaplace (Z c) (ceCs * x) := by
    have h1 := (abs_le.mp (hZ_loc c x hc_min hx)).1
    have h2 := hZ0 c hc_min
    linarith
  have hε0 := (liftEps_pos hc0).le
  have hmul : liftEps c * (ceK * m_Z - CZ_loc * Real.sqrt x) ≤ liftEps c * airyTwistedLaplace (Z c) (ceCs * x) :=
    mul_le_mul_of_nonneg_left hZ_lo hε0
  have h1 : (c₁' / 2) * Real.sqrt x ≤ (c₁' - liftEps c * CZ_loc) * Real.sqrt x :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg x)
  linarith

private lemma ceDualLine_htail_bound {X : ℝ → ℝ} (d₀ B₀ CZ_rhp c_min : ℝ)
    (hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace X (ceCs * x))
    (Z : ℝ → ℝ → ℝ)
    (hZ : ∀ c x : ℝ, c_min ≤ c → 0 ≤ x →
      |airyTwistedLaplace (Z c) (ceCs * x)| ≤ CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ)))
    {c x : ℝ} (hc_min : c_min ≤ c) (hc0 : 0 < c) (hxB : B₀ / 2 ≤ x) (hx0 : 0 ≤ x)
    (hε : liftEps c * CZ_rhp ≤ d₀ / 2) :
    (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
      airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
  have hX := hX_tail x hxB
  have hZ_lo : -(CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ))) ≤ airyTwistedLaplace (Z c) (ceCs * x) :=
    (abs_le.mp (hZ c x hc_min hx0)).1
  have hε0 := (liftEps_pos hc0).le
  have hpow : 0 ≤ (1 + x) ^ (-(5 / 2 : ℝ)) := by positivity
  have hmul : liftEps c * (-(CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ)))) ≤ liftEps c * airyTwistedLaplace (Z c) (ceCs * x) :=
    mul_le_mul_of_nonneg_left hZ_lo hε0
  have h1 : (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (d₀ - liftEps c * CZ_rhp) * (1 + x) ^ (-(5 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_right (by linarith) hpow
  linarith

private lemma ceDualLine_hA1_aux {X : ℝ → ℝ} {Z : ℝ → ℝ → ℝ} {D : ℝ → ℝ → ℝ}
    (hD_eq : ∀ c u, D c u = X u + liftEps c * Z c u)
    (hUX : HasU2 X) (hUZ : ∀ c, HasU2 (Z c)) (hUD : ∀ c, HasU2 (D c))
    {x₀ B₀ c₁' d₀ CX_loc CX_rhp CZ_rhp m_Z c₀ K M_small M_tail M : ℝ}
    (hx₀ : 0 < x₀) (hB₀ : 0 ≤ B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hCX_loc : 0 < CX_loc) (hCX_rhp : 0 ≤ CX_rhp) (hCZ_rhp : 0 < CZ_rhp) (hm_Z : 0 < m_Z)
    (hc₀_2 : 2 ≤ c₀)
    (hM_small_def : M_small = (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)))
    (hM_tail_def : M_tail = (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)))
    (hM_sm : M_small ≤ M) (hM_tl : M_tail ≤ M)
    (hX_loc : ∀ {w : ℂ}, 0 ≤ w.re → ‖w‖ ≤ x₀ + 2 → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ))
    (hX_rhp : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hZ_rhp : ∀ {c : ℝ} {w : ℂ}, c₀ ≤ c → 0 ≤ w.re → ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hD_small : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hD_tail : ∀ {c x : ℝ}, c₀ ≤ c → B₀ / 2 ≤ x →
      (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hWD_re : ∀ {c x : ℝ}, 0 ≤ x →
      (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re =
        uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)))
    (hK : 0 < K) (hm : 1 ≤ m)
    {c x y : ℝ} (hc : c₀ ≤ c) (hx : 0 < x) (hx_not : x ∉ Icc (x₀ / 3) (2 * B₀)) (hy : |y| ≤ x / 4) :
    ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I) -
        liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)‖ ≤
      4 * M * (|y| / x) * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
  have hc0 : 0 < c := by linarith
  set a : ℝ := ceCs * (ceBeta1 * K * liftEps c / 2) / m
  have ha0 : 0 < a := by have := ceCs_pos; have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  have hball_rel : ∀ w : ℂ, x / 2 ≤ w.re → ‖w - (x : ℂ)‖ ≤ x / 2 →
      ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w‖ ≤
        M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
    intro w hw_re hw_ball
    have hw0 : 0 ≤ w.re := by linarith
    have hM_pow : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ ≤
        (2 : ℝ) ^ m * uctE1r (a * x) ^ m := by
      refine (norm_liftMultiplier_le_pow (ceBeta1 * K * liftEps c / 2) m w).trans ?_
      have h1 : uctE1r (a * w.re) ≤ uctE1r (a * x / 2) := uctE1r_anti (by nlinarith)
      have h2 : uctE1r (a * x / 2) ≤ 2 * uctE1r (a * x) := uctE1r_half (by positivity)
      calc uctE1r (a * w.re) ^ m ≤ (2 * uctE1r (a * x)) ^ m :=
            pow_le_pow_left₀ (uctE1r_pos _).le (h1.trans h2) m
        _ = _ := by rw [mul_pow]
    have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
        airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
          (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) := by
      have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw0
      have hfn : D c = fun u => X u + liftEps c * Z c u := funext (hD_eq c)
      rw [hfn, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
        airyTwistedLaplaceC_const_mul]
    have hWD_norm : ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w‖ =
        ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ := by
      unfold liftSymbol; rw [norm_mul]
    have hcases : x < x₀ / 3 ∨ 2 * B₀ < x := by
      by_contra hcon; push Not at hcon; exact hx_not ⟨hcon.1, hcon.2⟩
    rcases hcases with hx_sm | hx_lg
    · have hwn : ‖w‖ ≤ 3 / 2 * x := by
        calc ‖w‖ = ‖(w - (x : ℂ)) + (x : ℂ)‖ := by ring_nf
          _ ≤ ‖w - (x : ℂ)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
          _ ≤ x / 2 + x := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]; linarith
          _ = 3 / 2 * x := by ring
      have hXw := hX_loc hw0 (by linarith)
      have hwn_sqrt : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt (3 / 2) * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) hx.le]
        exact Real.rpow_le_rpow (norm_nonneg w) hwn (by norm_num)
      have hZw := hZ_rhp hc hw0
      have h1w : 1 ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simp only [Complex.add_re, Complex.one_re] at this; linarith
      have hZw1 : ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp :=
        hZw.trans (mul_le_of_le_one_right hCZ_rhp.le (Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)))
      have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          CX_loc * Real.sqrt (3 / 2) * Real.sqrt x + liftEps c * CZ_rhp := by
        rw [hD_split]
        calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
            ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
          _ ≤ CX_loc * (Real.sqrt (3 / 2) * Real.sqrt x) + liftEps c * CZ_rhp := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
              exact add_le_add (hXw.trans (mul_le_mul_of_nonneg_left hwn_sqrt hCX_loc.le))
                (mul_le_mul_of_nonneg_left hZw1 (liftEps_pos hc0).le)
          _ = _ := by ring
      have hDs := hD_small hc ⟨hx.le, by linarith⟩
      have hterm1 : CX_loc * Real.sqrt (3 / 2) * Real.sqrt x ≤
          (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) := by
        have heq : (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) =
            CX_loc * Real.sqrt (3 / 2) * Real.sqrt x := by field_simp [hc₁'.ne']
        linarith
      have hterm2 : liftEps c * CZ_rhp ≤ (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by
        have := ceK_pos
        have heq : (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) = liftEps c * CZ_rhp := by
          field_simp [this.ne', hm_Z.ne']
        linarith
      have hMs1 := le_max_left (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
      have hMs2 := le_max_right (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
      have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
            ≤ (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) +
                (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by linarith
          _ ≤ max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
                ((c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c) := by
              rw [mul_add]
              exact add_le_add (mul_le_mul_of_nonneg_right hMs1 (by positivity))
                (mul_le_mul_of_nonneg_right hMs2 (by have := ceK_pos; have := liftEps_pos hc0; positivity))
          _ ≤ _ := mul_le_mul_of_nonneg_left hDs (by have := ceK_pos; positivity)
      rw [hWD_norm, hWD_re hx.le]
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ ((2 : ℝ) ^ m * uctE1r (a * x) ^ m) *
              (max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
            mul_le_mul hM_pow hD_rel (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (uctE1r_pos _).le _))
        _ = M_small * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            rw [hM_small_def]; dsimp [a]; ring
        _ ≤ M * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            have hnn1 : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
            have hnn2 : 0 ≤ ceK * m_Z * liftEps c := by have := ceK_pos; have := liftEps_pos hc0; positivity
            have hnn : 0 ≤ uctE1r (a * x) ^ m *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) :=
              mul_nonneg (pow_nonneg (uctE1r_pos _).le _) (le_trans (add_nonneg hnn1 hnn2) hDs)
            exact mul_le_mul_of_nonneg_right hM_sm hnn
    · have h1w_ge : 1 + x / 2 ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simp only [Complex.add_re, Complex.one_re] at this; linarith
      have hpow_w : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
        have h1 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (1 + x / 2) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by linarith) h1w_ge (by norm_num)
        have h2 : (1 + x / 2) ^ (-(5 / 2 : ℝ)) ≤ (2⁻¹ * (1 + x)) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
        have h3 : ((2 : ℝ)⁻¹) ^ (-(5 / 2 : ℝ)) = 2 ^ (5 / 2 : ℝ) := by
          rw [Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
        rw [Real.mul_rpow (by norm_num) (by linarith), h3] at h2
        exact h1.trans h2
      have hXw := (hX_rhp w hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCX_rhp)
      have hZw := (hZ_rhp hc hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCZ_rhp.le)
      have hε1 : liftEps c ≤ 1 := liftEps_le_one_of_two_le (hc₀_2.trans hc)
      have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          (CX_rhp + CZ_rhp) * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by
        rw [hD_split]
        calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
            ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
          _ ≤ CX_rhp * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) +
                1 * (CZ_rhp * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ)))) := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
              exact add_le_add hXw (mul_le_mul hε1 hZw (norm_nonneg _) zero_le_one)
          _ = _ := by ring
      have hDt := hD_tail (x := x) hc (by linarith [hB₀])
      have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have heq : (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) =
            (CX_rhp + CZ_rhp) * (2 ^ (5 / 2 : ℝ) * (1 + x) ^ (-(5 / 2 : ℝ))) := by field_simp [hd₀.ne']
        calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
            ≤ (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) := by linarith
          _ ≤ _ := mul_le_mul_of_nonneg_left hDt (by positivity)
      rw [hWD_norm, hWD_re hx.le]
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ ((2 : ℝ) ^ m * uctE1r (a * x) ^ m) *
              ((2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
            mul_le_mul hM_pow hD_rel (norm_nonneg _) (mul_nonneg (by positivity) (pow_nonneg (uctE1r_pos _).le _))
        _ = M_tail * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            rw [hM_tail_def]; dsimp [a]; ring
        _ ≤ M * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            have hnn : 0 ≤ uctE1r (a * x) ^ m *
                (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) :=
              mul_nonneg (pow_nonneg (uctE1r_pos _).le _) (le_trans (by positivity) hDt)
            exact mul_le_mul_of_nonneg_right hM_tl hnn
  have hv := local_variation_right (liftSymbol_differentiableOn (hUD c) (ceBeta1 * K * liftEps c / 2) m) hx
    (B := M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re) hball_rel y hy
  calc ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I) -
          liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)‖
      ≤ 4 * (M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re) / x * |y| := hv
    _ = 4 * M * (|y| / x) * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by ring

private lemma ceDualLine_hA2_aux {X : ℝ → ℝ} {Z : ℝ → ℝ → ℝ} {D : ℝ → ℝ → ℝ}
    (hD_eq : ∀ c u, D c u = X u + liftEps c * Z c u)
    (hUX : HasU2 X) (hUZ : ∀ c, HasU2 (Z c))
    {x₀ B₀ c₁' d₀ CX_loc CX_rhp CZ_rhp m_Z c₀ K M_tail M Λ_add_max : ℝ}
    (hx₀ : 0 < x₀) (hB₀ : 0 ≤ B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hCX_loc : 0 < CX_loc) (hCX_rhp : 0 ≤ CX_rhp) (hCZ_rhp : 0 < CZ_rhp) (hm_Z : 0 < m_Z)
    (hc₀_2 : 2 ≤ c₀)
    (hM_sm : (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) ≤ M)
    (hM_tail_def : M_tail = (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)))
    (hM_tl : M_tail ≤ M)
    (hL1 : CX_loc * Real.sqrt 3 ≤ Λ_add_max) (hL2 : CX_rhp ≤ Λ_add_max)
    (hX_loc : ∀ {w : ℂ}, 0 ≤ w.re → ‖w‖ ≤ x₀ + 2 → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ))
    (hX_rhp : ∀ w : ℂ, 0 ≤ w.re → ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hZ_rhp : ∀ {c : ℝ} {w : ℂ}, c₀ ≤ c → 0 ≤ w.re → ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)))
    (hD_small : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hD_tail : ∀ {c x : ℝ}, c₀ ≤ c → B₀ / 2 ≤ x →
      (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))
    (hWD_re : ∀ {c x : ℝ}, 0 ≤ x →
      (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re =
        uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)))
    (hK : 0 < K)
    {c x y : ℝ} (hc : c₀ ≤ c) (hx : 0 < x) (hx_not : x ∉ Icc (x₀ / 3) (2 * B₀)) :
    ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re +
        (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0) := by
  have hc0 : 0 < c := by linarith
  have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
    have := ceBeta1_pos; have := liftEps_pos hc0; positivity
  set w : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hw_re : w.re = x := by simp [w]
  have hw0 : 0 ≤ w.re := by linarith
  have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
      airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
        (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) := by
    have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw0
    have hfn : D c = fun u => X u + liftEps c * Z c u := funext (hD_eq c)
    rw [hfn, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
      airyTwistedLaplaceC_const_mul]
  set a : ℝ := ceCs * (ceBeta1 * K * liftEps c / 2) / m
  have hM_le : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ ≤ uctE1r (a * x) ^ m := by
    simpa [a, hw_re] using norm_liftMultiplier_le_pow (ceBeta1 * K * liftEps c / 2) m w
  have hM_le1 : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ ≤ 1 :=
    norm_liftMultiplier_le_one hδ0 m hw0
  have hcases : x < x₀ / 3 ∨ 2 * B₀ < x := by
    by_contra hcon; push Not at hcon; exact hx_not ⟨hcon.1, hcon.2⟩
  rcases hcases with hx_sm | hx_lg
  · have hx_lt_x0 : x < x₀ := by linarith
    have hZw : ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp := by
      have h1 := hZ_rhp hc hw0
      have h1w : 1 ≤ ‖1 + w‖ := by
        have := Complex.re_le_norm (1 + w)
        simp only [Complex.add_re, Complex.one_re, hw_re] at this; linarith
      exact h1.trans (mul_le_of_le_one_right hCZ_rhp.le (Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)))
    have hDs := hD_small hc ⟨hx.le, hx_lt_x0.le⟩
    have hC_le_M : CZ_rhp / (ceK * m_Z) ≤ M := by
      have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      have h1 : CZ_rhp / (ceK * m_Z) ≤
          (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) :=
        (le_max_right _ _).trans (le_mul_of_one_le_left (by have := ceK_pos; positivity) h2m)
      exact h1.trans hM_sm
    have hZ_to_WD : uctE1r (a * x) ^ m * (liftEps c * CZ_rhp) ≤
        M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
      rw [hWD_re hx.le]
      have hM_nn : 0 ≤ uctE1r (a * x) ^ m := pow_nonneg (uctE1r_pos _).le m
      have hterm2 : liftEps c * CZ_rhp ≤ (CZ_rhp / (ceK * m_Z)) *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have heq : (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) = liftEps c * CZ_rhp := by
          have := ceK_pos; field_simp [this.ne', hm_Z.ne']
        calc liftEps c * CZ_rhp = (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := heq.symm
          _ ≤ (CZ_rhp / (ceK * m_Z)) * ((c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c) := by
              have := ceK_pos
              exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hDs (by have := ceK_pos; positivity)
      have hnn_rhs : 0 ≤ uctE1r (a * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have := ceK_pos; have := liftEps_pos hc0
        exact mul_nonneg hM_nn (le_trans (by positivity) hDs)
      calc uctE1r (a * x) ^ m * (liftEps c * CZ_rhp)
          ≤ uctE1r (a * x) ^ m * ((CZ_rhp / (ceK * m_Z)) *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
            mul_le_mul_of_nonneg_left hterm2 hM_nn
        _ = (CZ_rhp / (ceK * m_Z)) * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            dsimp [a]; ring
        _ ≤ M * _ := mul_le_mul_of_nonneg_right hC_le_M hnn_rhs
    have hWD_Z_term : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
          ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤
        M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re := by
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
            ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
          ≤ uctE1r (a * x) ^ m * (liftEps c * CZ_rhp) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
            exact mul_le_mul hM_le (mul_le_mul_of_nonneg_left hZw (liftEps_pos hc0).le)
              (mul_nonneg (liftEps_pos hc0).le (norm_nonneg _)) (pow_nonneg (uctE1r_pos _).le _)
        _ ≤ _ := hZ_to_WD
    by_cases hy2 : x / 2 < |y|
    · rw [if_pos ⟨hx_lt_x0, hy2⟩]
      have hXw_add : ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
            ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 := by
        rcases le_or_gt |y| 1 with hy1 | hy1
        · rw [min_eq_left (Real.rpow_le_one (abs_nonneg y) hy1 (by norm_num))]
          have hwn : ‖w‖ ≤ x + |y| := by
            calc ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
              _ = x + |y| := by simp [abs_of_pos hx]
          have hwn3 : ‖w‖ ≤ 3 * |y| := by linarith
          have hXw := hX_loc hw0 (by linarith)
          have hsqrt3 : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt 3 * |y| ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) (abs_nonneg y)]
            exact Real.rpow_le_rpow (norm_nonneg w) hwn3 (by norm_num)
          calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖
              ≤ 1 * (CX_loc * (Real.sqrt 3 * |y| ^ (1 / 2 : ℝ))) :=
                mul_le_mul hM_le1 (hXw.trans (mul_le_mul_of_nonneg_left hsqrt3 hCX_loc.le))
                  (norm_nonneg _) zero_le_one
            _ = (CX_loc * Real.sqrt 3) * |y| ^ (1 / 2 : ℝ) := by ring
            _ ≤ Λ_add_max * |y| ^ (1 / 2 : ℝ) :=
                mul_le_mul_of_nonneg_right hL1 (by positivity)
        · rw [min_eq_right (Real.one_le_rpow hy1.le (by norm_num)), mul_one]
          have h1w : 1 ≤ ‖1 + w‖ := by
            have := Complex.re_le_norm (1 + w)
            simp only [Complex.add_re, Complex.one_re, hw_re] at this; linarith
          have hXw := (hX_rhp w hw0).trans
            (mul_le_of_le_one_right hCX_rhp (Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)))
          calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖
              ≤ 1 * CX_rhp := mul_le_mul hM_le1 hXw (norm_nonneg _) zero_le_one
            _ = CX_rhp := one_mul _
            _ ≤ Λ_add_max := hL2
      calc ‖liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w‖
          = ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ := by
              unfold liftSymbol; rw [norm_mul]
        _ ≤ ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
              (‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖) := by
            rw [hD_split]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
        _ = ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
              ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := by ring
        _ ≤ Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 +
              M * (liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m (x : ℂ)).re :=
            add_le_add hXw_add hWD_Z_term
        _ = _ := by ring
    · push Not at hy2
      rw [if_neg (fun h => absurd h.2 (not_lt.mpr hy2)), add_zero]
      have hwn : ‖w‖ ≤ 3 / 2 * x := by
        calc ‖w‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
          _ = x + |y| := by simp [abs_of_pos hx]
          _ ≤ 3 / 2 * x := by linarith
      have hXw := hX_loc hw0 (by linarith)
      have hwn_sqrt : ‖w‖ ^ (1 / 2 : ℝ) ≤ Real.sqrt (3 / 2) * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.mul_rpow (by norm_num) hx.le]
        exact Real.rpow_le_rpow (norm_nonneg w) hwn (by norm_num)
      have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          CX_loc * Real.sqrt (3 / 2) * Real.sqrt x + liftEps c * CZ_rhp := by
        rw [hD_split]
        calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
            ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
          _ ≤ CX_loc * (Real.sqrt (3 / 2) * Real.sqrt x) + liftEps c * CZ_rhp := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
              exact add_le_add (hXw.trans (mul_le_mul_of_nonneg_left hwn_sqrt hCX_loc.le))
                (mul_le_mul_of_nonneg_left hZw (liftEps_pos hc0).le)
          _ = _ := by ring
      have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
          max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
        have hterm1 : CX_loc * Real.sqrt (3 / 2) * Real.sqrt x ≤
            (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) := by
          have heq : (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) =
              CX_loc * Real.sqrt (3 / 2) * Real.sqrt x := by field_simp [hc₁'.ne']
          linarith
        have hterm2 : liftEps c * CZ_rhp ≤ (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by
          have := ceK_pos
          have heq : (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) = liftEps c * CZ_rhp := by
            field_simp [this.ne', hm_Z.ne']
          linarith
        have hMs1 := le_max_left (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
        have hMs2 := le_max_right (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
        calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
            ≤ (2 * CX_loc * Real.sqrt (3 / 2) / c₁') * ((c₁' / 2) * Real.sqrt x) +
                (CZ_rhp / (ceK * m_Z)) * (ceK * m_Z * liftEps c) := by linarith
          _ ≤ max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) *
                ((c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c) := by
              rw [mul_add]
              exact add_le_add (mul_le_mul_of_nonneg_right hMs1 (by positivity))
                (mul_le_mul_of_nonneg_right hMs2 (by have := ceK_pos; have := liftEps_pos hc0; positivity))
          _ ≤ _ := mul_le_mul_of_nonneg_left hDs (by have := ceK_pos; positivity)
      have hC_le_M : max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z)) ≤ M := by
        have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
        exact (le_mul_of_one_le_left (by have := ceK_pos; positivity) h2m).trans hM_sm
      rw [show liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w =
          liftMultiplier (ceBeta1 * K * liftEps c / 2) m w *
            airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) from rfl, norm_mul, hWD_re hx.le]
      calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ uctE1r (a * x) ^ m * (M *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            have hnn1 : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
            have hnn2 : 0 ≤ ceK * m_Z * liftEps c := by have := ceK_pos; have := liftEps_pos hc0; positivity
            exact mul_le_mul hM_le (hD_rel.trans (mul_le_mul_of_nonneg_right hC_le_M (le_trans (add_nonneg hnn1 hnn2) hDs)))
              (norm_nonneg _) (pow_nonneg (uctE1r_pos _).le _)
        _ = M * (uctE1r (a * x) ^ m *
              (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
            dsimp [a]; ring
  · have hnot : ¬ (x < x₀ ∧ x / 2 < |y|) := fun h => by linarith [h.1]
    rw [if_neg hnot, add_zero]
    have h1w_ge : 1 + x ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp only [Complex.add_re, Complex.one_re, hw_re] at this; linarith
    have hpow_w : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ (1 + x) ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1w_ge (by norm_num)
    have hXw := (hX_rhp w hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCX_rhp)
    have hZw := (hZ_rhp hc hw0).trans (mul_le_mul_of_nonneg_left hpow_w hCZ_rhp.le)
    have hε1 : liftEps c ≤ 1 := liftEps_le_one_of_two_le (hc₀_2.trans hc)
    have hDw : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
        (CX_rhp + CZ_rhp) * (1 + x) ^ (-(5 / 2 : ℝ)) := by
      rw [hD_split]
      calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
          ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
              ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
        _ ≤ CX_rhp * (1 + x) ^ (-(5 / 2 : ℝ)) + 1 * (CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ))) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
            exact add_le_add hXw (mul_le_mul hε1 hZw (norm_nonneg _) zero_le_one)
        _ = _ := by ring
    have hDt := hD_tail hc (by linarith [hB₀])
    have hD_rel : ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖ ≤
        M_tail * (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := by
      have hMt1 : CX_rhp + CZ_rhp ≤ M_tail * (d₀ / 2) := by
        rw [hM_tail_def]
        have h1 : 1 ≤ (2 : ℝ) ^ m * 2 ^ (5 / 2 : ℝ) := by
          have h2m : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
          have h25 : (1 : ℝ) ≤ (2 : ℝ) ^ (5 / 2 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
          nlinarith
        have heq : (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2)) * (d₀ / 2) =
            ((2 : ℝ) ^ m * 2 ^ (5 / 2 : ℝ)) * (CX_rhp + CZ_rhp) := by field_simp [hd₀.ne']
        rw [heq]
        exact le_mul_of_one_le_left (by positivity) h1
      calc ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
          ≤ (M_tail * (d₀ / 2)) * (1 + x) ^ (-(5 / 2 : ℝ)) :=
            hDw.trans (mul_le_mul_of_nonneg_right hMt1 (by positivity))
        _ = M_tail * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hDt (by rw [hM_tail_def]; positivity)
    rw [show liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w =
        liftMultiplier (ceBeta1 * K * liftEps c / 2) m w *
          airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) from rfl, norm_mul, hWD_re hx.le]
    calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ * ‖airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w)‖
        ≤ uctE1r (a * x) ^ m * (M *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) :=
          mul_le_mul hM_le (hD_rel.trans (mul_le_mul_of_nonneg_right hM_tl (le_trans (by positivity) hDt)))
            (norm_nonneg _) (pow_nonneg (uctE1r_pos _).le _)
      _ = M * (uctE1r (a * x) ^ m *
            (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) := by
          dsimp [a]; ring

/-- **`lem:ce-dual-line` (`ce_lift_proofs.tex`):** uniform dual-line positivity, small-`x` / tail
floors, `hA1_D` local variation, and `hA2_D` strip bounds for `W_{D_c}` when `D_c = X + ε_c Z_c`
is formed from a floor-satisfying `X ∈ ℛ_Ai^gen` and a uniformly bounded finite linear combination
family `Z_c` in `ℛ_Ai^gen` with positive mass and positive `J`-floor. -/
theorem ce_dual_line {F : ℂ → ℂ} {β₀₀ β₁₁ : ℝ}
    (hF : HasGenRationalAiryCoeffs F β₀₀ β₁₁)
    (hmass : ∫ u : ℝ, (F (u : ℂ)).re = 0)
    (hnonneg : ∀ y : ℝ, 0 < y → 0 ≤ airyLaplace (fun u => (F (u : ℂ)).re) y)
    {ι : Type*} (s : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
    (hB : ∀ i ∈ s, HasGenRationalAiryCoeffs (B i) (b₀₀ i) (b₁₁ i))
    (α : ι → ℝ → ℝ) (R c_min m_Z z₀ : ℝ) (hR : 0 ≤ R) (hc_min : 2 ≤ c_min)
    (hm_Z : 0 < m_Z) (hz₀ : 0 < z₀)
    (hα : ∀ i ∈ s, ∀ c : ℝ, c_min ≤ c → |α i c| ≤ R)
    (hZ_mass : ∀ c : ℝ, c_min ≤ c → m_Z ≤ ∫ u : ℝ, ∑ i ∈ s, α i c * (B i (u : ℂ)).re)
    {x₀ B₀ c₁' d₀ : ℝ} (hx₀ : 0 < x₀) (hx₀B : x₀ < B₀) (hc₁' : 0 < c₁') (hd₀ : 0 < d₀)
    (hX_small : ∀ x ∈ Icc (0 : ℝ) x₀,
      c₁' * Real.sqrt x ≤ (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    (hX_tail : ∀ x : ℝ, B₀ / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
      (airyTwistedLaplaceC (fun u => (F (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    (hZ_J : ∀ c : ℝ, c_min ≤ c → ∀ x ∈ Icc (x₀ / 3) (2 * B₀), z₀ ≤
      (airyTwistedLaplaceC (fun u => ∑ i ∈ s, α i c * (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ)).re)
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 1 ≤ m) :
    let X : ℝ → ℝ := fun u => (F (u : ℂ)).re
    let Z : ℝ → ℝ → ℝ := fun c u => ∑ i ∈ s, α i c * (B i (u : ℂ)).re
    let D : ℝ → ℝ → ℝ := fun c u => X u + liftEps c * Z c u
    let W_D : ℝ → ℂ → ℂ := fun c w => liftSymbol (D c) (ceBeta1 * K * liftEps c / 2) m w
    ∃ c₀ M Λ Λ_add_max b c_J d_tail K_D : ℝ,
      c_min ≤ c₀ ∧ 1 ≤ M ∧ 1 ≤ Λ ∧ 0 ≤ Λ_add_max ∧ 0 < b ∧ 0 < c_J ∧ 0 < d_tail ∧ 0 ≤ K_D ∧
      (∀ {c : ℝ}, c₀ ≤ c → DifferentiableOn ℂ (W_D c) {w : ℂ | 0 < w.re}) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 0 < x → (W_D c (x : ℂ)).im = 0) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → 0 ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 0 < x → x < x₀ → x ∉ Icc (x₀ / 3) (2 * B₀) →
        b * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → 2 * B₀ ≤ x → x ≤ c ^ (1 / 3 : ℝ) →
        d_tail * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (x₀ / 3) (2 * B₀) → x ≤ c ^ (1 / 3 : ℝ) →
        c_J * c ^ (-(1 / 3 : ℝ)) ≤ (W_D c (x : ℂ)).re) ∧
      (∀ {c x y : ℝ}, c₀ ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → x ∉ Icc (x₀ / 3) (2 * B₀) → |y| ≤ x / 4 →
        ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I) - W_D c (x : ℂ)‖ ≤ 4 * M * (|y| / x) * (W_D c (x : ℂ)).re) ∧
      (∀ {c x y : ℝ}, c₀ ≤ c → 0 < x → x ≤ c ^ (1 / 3 : ℝ) → x ∉ Icc (x₀ / 3) (2 * B₀) →
        ‖W_D c ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Λ * (W_D c (x : ℂ)).re +
          (if x < x₀ ∧ x / 2 < |y| then Λ_add_max * min (|y| ^ (1 / 2 : ℝ)) 1 else 0)) ∧
      (∀ {c : ℝ} {w : ℂ}, c₀ ≤ c → 0 < w.re → ‖W_D c w‖ ≤ K_D) := by
  classical
  intro X Z D W_D
  have hB₀_pos : 0 ≤ B₀ := by linarith
  have hUX : HasU2 X := hasU2_of_genRational hF
  obtain ⟨CX_rhp, hCX_rhp, hX_rhp⟩ := hUX.rhp
  have hUZ : ∀ c : ℝ, HasU2 (Z c) := fun c => hasU2_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c)
  have hUD : ∀ c : ℝ, HasU2 (D c) := fun c => hUX.add ((hUZ c).smul (liftEps c))
  have hZ_split : ∀ (c : ℝ) {w : ℂ}, 0 ≤ w.re →
      airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w) :=
    fun c {_} hw => airyTwistedLaplaceC_finset_sum s B b₀₀ b₁₁ hB (fun i => α i c) hw
  have hZ_rhp_i : ∀ i ∈ s, ∃ Ci > 0, ∀ w : ℂ, 0 ≤ w.re →
      ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ ≤ Ci * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
    fun i hi => (hasU2_of_genRational (hB i hi)).rhp
  choose CZi hCZi_pos hCZi_bd using hZ_rhp_i
  let CZ_rhp : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0) + 1
  have hCZ_rhp : 0 < CZ_rhp := by
    have : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs; exact (hCZi_pos i hi).le; exact le_rfl
    positivity
  have hZ_rhp : ∀ {c : ℝ} {w : ℂ}, c_min ≤ c → 0 ≤ w.re →
      ‖airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
    intro c w hc hw
    rw [hZ_split c hw]
    have hnn : 0 ≤ ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by positivity
    calc ‖∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖
        ≤ ∑ i ∈ s, ‖(α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs : ℂ) * w)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CZi i hi else 0) * ‖1 + w‖ ^ (-(5 / 2 : ℝ))) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          split_ifs with hi'
          · exact mul_le_mul (hα i hi c hc) (hCZi_bd i hi w hw) (norm_nonneg _) hR
          · exact absurd hi hi'
      _ = (R * ∑ i ∈ s, if hi : i ∈ s then CZi i hi else 0) * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) := by
          simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ CZ_rhp * ‖1 + w‖ ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right (by dsimp [CZ_rhp]; linarith) hnn
  let Rloc : ℝ := ceCs * (x₀ + 2)
  have hRloc : 0 ≤ Rloc := by have := ceCs_pos; positivity
  obtain ⟨CX_e, hCX_e, hexpX⟩ := u1c_expansion_of_genRational hF Rloc hRloc
  let CX_loc : ℝ := |(β₀₀ + β₁₁) * (2 * ceK * cA)| * Real.sqrt ceCs + CX_e * ceCs * Real.sqrt (x₀ + 2) + 1
  have hCX_loc : 0 < CX_loc := by have := ceCs_pos; positivity
  have hX_loc : ∀ {w : ℂ}, 0 ≤ w.re → ‖w‖ ≤ x₀ + 2 →
      ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ) := by
    intro w hw hwn
    let y : ℂ := (ceCs : ℂ) * w
    have hyre : 0 ≤ y.re := by simp [y]; exact mul_nonneg ceCs_pos.le hw
    have hyn : ‖y‖ ≤ Rloc := by
      rw [show y = (ceCs : ℂ) * w from rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos]
      exact mul_le_mul_of_nonneg_left hwn ceCs_pos.le
    have h0 : airyTwistedLaplaceC X 0 = 0 := by rw [airyTwistedLaplaceC_zero_eq]; simp [X, hmass]
    have hbd := hexpX hyre hyn
    rw [h0, sub_zero] at hbd
    have hyn_eq : ‖y‖ = ceCs * ‖w‖ := by
      rw [show y = (ceCs : ℂ) * w from rfl, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ceCs_pos]
    have hsqrt_y : ‖y ^ (1 / 2 : ℂ)‖ = Real.sqrt ceCs * ‖w‖ ^ (1 / 2 : ℝ) := by
      rw [norm_cpow_half_eq, hyn_eq, Real.mul_rpow ceCs_pos.le (norm_nonneg w), ← Real.sqrt_eq_rpow]
    have hwn_pow : ‖w‖ ≤ Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ) := by
      calc ‖w‖ = ‖w‖ ^ (1 / 2 : ℝ) * ‖w‖ ^ (1 / 2 : ℝ) := by
            rw [← Real.rpow_add_of_nonneg (norm_nonneg w) (by norm_num) (by norm_num)]; norm_num
        _ ≤ Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (norm_nonneg w) hwn (by norm_num)) (by positivity)
    have hterm2 : ‖(((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ =
        |(β₀₀ + β₁₁) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖airyTwistedLaplaceC X y‖
        = ‖(airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)) -
            (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := by ring_nf
      _ ≤ ‖airyTwistedLaplaceC X y + (((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ +
            ‖(((β₀₀ + β₁₁) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := norm_sub_le _ _
      _ ≤ CX_e * ‖y‖ + |(β₀₀ + β₁₁) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
          rw [hterm2]; exact add_le_add hbd le_rfl
      _ = CX_e * ceCs * ‖w‖ + |(β₀₀ + β₁₁) * (2 * ceK * cA)| * Real.sqrt ceCs * ‖w‖ ^ (1 / 2 : ℝ) := by
          rw [hyn_eq, hsqrt_y]; ring
      _ ≤ (CX_e * ceCs * Real.sqrt (x₀ + 2) + |(β₀₀ + β₁₁) * (2 * ceK * cA)| * Real.sqrt ceCs) *
            ‖w‖ ^ (1 / 2 : ℝ) := by
          have h1 : CX_e * ceCs * ‖w‖ ≤ CX_e * ceCs * Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ) := by
            calc CX_e * ceCs * ‖w‖ ≤ CX_e * ceCs * (Real.sqrt (x₀ + 2) * ‖w‖ ^ (1 / 2 : ℝ)) :=
                  mul_le_mul_of_nonneg_left hwn_pow (by have := ceCs_pos; positivity)
              _ = _ := by ring
          linarith
      _ ≤ CX_loc * ‖w‖ ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by dsimp [CX_loc]; linarith) (by positivity)
  have hZ_loc_i : ∀ i ∈ s, ∃ Ci > 0, ∀ x ∈ Icc (0 : ℝ) x₀,
      ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) -
        airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0‖ ≤ Ci * Real.sqrt x := by
    intro i hi
    obtain ⟨Ci_e, hCi_e, hexp_i⟩ := u1c_expansion_of_genRational (hB i hi) Rloc hRloc
    have hCpos : 0 < |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs + Ci_e * ceCs * Real.sqrt x₀ + 1 := by
      have := ceCs_pos; positivity
    refine ⟨|(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs + Ci_e * ceCs * Real.sqrt x₀ + 1,
      hCpos, fun x ⟨hx0, hxx₀⟩ => ?_⟩
    let y : ℂ := ((ceCs * x : ℝ) : ℂ)
    have hyre : 0 ≤ y.re := by simp [y]; exact mul_nonneg ceCs_pos.le hx0
    have hyn : ‖y‖ ≤ Rloc := by
      rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
      exact mul_le_mul_of_nonneg_left (by linarith) ceCs_pos.le
    have hbd := hexp_i hyre hyn
    have hyn_eq : ‖y‖ = ceCs * x := by
      rw [show y = ((ceCs * x : ℝ) : ℂ) from rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg ceCs_pos.le hx0)]
    have hsqrt_y : ‖y ^ (1 / 2 : ℂ)‖ = Real.sqrt ceCs * Real.sqrt x := by
      rw [norm_cpow_half_eq, hyn_eq, Real.mul_rpow ceCs_pos.le hx0, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have hx_pow : x ≤ Real.sqrt x₀ * Real.sqrt x := by
      calc x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0).symm
        _ ≤ Real.sqrt x₀ * Real.sqrt x := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hxx₀) (Real.sqrt_nonneg x)
    have hterm2 : ‖(((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ =
        |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) y -
            airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0‖
        = ‖(airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) y -
              airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0 +
              (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)) -
            (((b₀₀ i + b₁₁ i) * (2 * ceK * cA) : ℝ) : ℂ) * y ^ (1 / 2 : ℂ)‖ := by ring_nf
      _ ≤ Ci_e * ‖y‖ + |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * ‖y ^ (1 / 2 : ℂ)‖ := by
          refine (norm_sub_le _ _).trans ?_; rw [hterm2]; exact add_le_add hbd le_rfl
      _ = Ci_e * ceCs * x + |(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs * Real.sqrt x := by
          rw [hyn_eq, hsqrt_y]; ring
      _ ≤ (|(b₀₀ i + b₁₁ i) * (2 * ceK * cA)| * Real.sqrt ceCs + Ci_e * ceCs * Real.sqrt x₀ + 1) *
            Real.sqrt x := by
          have h1 : Ci_e * ceCs * x ≤ Ci_e * ceCs * Real.sqrt x₀ * Real.sqrt x := by
            calc Ci_e * ceCs * x ≤ Ci_e * ceCs * (Real.sqrt x₀ * Real.sqrt x) :=
                  mul_le_mul_of_nonneg_left hx_pow (by have := ceCs_pos; positivity)
              _ = _ := by ring
          linarith [Real.sqrt_nonneg x]
  choose CZ_loc_i hCZ_loc_pos hCZ_loc_bd using hZ_loc_i
  let CZ_loc : ℝ := R * (∑ i ∈ s, if hi : i ∈ s then CZ_loc_i i hi else 0) + 1
  have hCZ_loc : 0 < CZ_loc := by
    have : 0 ≤ ∑ i ∈ s, if hi : i ∈ s then CZ_loc_i i hi else 0 := by
      refine Finset.sum_nonneg fun i hi => ?_
      split_ifs; exact (hCZ_loc_pos i hi).le; exact le_rfl
    positivity
  have hZ_loc : ∀ c x : ℝ, c_min ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      |airyTwistedLaplace (Z c) (ceCs * x) - airyTwistedLaplace (Z c) 0| ≤ CZ_loc * Real.sqrt x := by
    intro c x hc hx
    have hsplit_x : airyTwistedLaplaceC (Z c) ((ceCs * x : ℝ) : ℂ) =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) := by
      have h0 := hZ_split c (w := (x : ℂ)) (by simp; exact hx.1)
      have hcx : (ceCs : ℂ) * (x : ℂ) = ((ceCs * x : ℝ) : ℂ) := by push_cast; ring
      rw [← hcx]; exact h0
    have hsplit_0 : airyTwistedLaplaceC (Z c) 0 =
        ∑ i ∈ s, (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0 := by
      have h0 := hZ_split c (w := 0) le_rfl
      rwa [mul_zero] at h0
    have hbd_c : ‖airyTwistedLaplaceC (Z c) ((ceCs * x : ℝ) : ℂ) - airyTwistedLaplaceC (Z c) 0‖ ≤
        CZ_loc * Real.sqrt x := by
      rw [hsplit_x, hsplit_0, ← Finset.sum_sub_distrib]
      calc ‖∑ i ∈ s, ((α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) -
              (α i c : ℂ) * airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0)‖
          ≤ ∑ i ∈ s, ‖(α i c : ℂ) * (airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) ((ceCs * x : ℝ) : ℂ) -
              airyTwistedLaplaceC (fun u => (B i (u : ℂ)).re) 0)‖ := by
            refine (norm_sum_le _ _).trans (le_of_eq ?_); congr 1; ext i; rw [mul_sub]
        _ ≤ ∑ i ∈ s, R * ((if hi : i ∈ s then CZ_loc_i i hi else 0) * Real.sqrt x) := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            split_ifs with hi'
            · exact mul_le_mul (hα i hi c hc) (hCZ_loc_bd i hi x hx) (norm_nonneg _) hR
            · exact absurd hi hi'
        _ = (R * ∑ i ∈ s, if hi : i ∈ s then CZ_loc_i i hi else 0) * Real.sqrt x := by
            simp_rw [← mul_assoc, ← Finset.sum_mul, ← Finset.mul_sum]
        _ ≤ CZ_loc * Real.sqrt x :=
            mul_le_mul_of_nonneg_right (by dsimp [CZ_loc]; linarith) (Real.sqrt_nonneg x)
    rw [airyTwistedLaplaceC_ofReal, show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm,
      airyTwistedLaplaceC_ofReal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hbd_c
    exact hbd_c
  let E_max : ℝ := max (2 * CZ_loc / c₁') (2 * CZ_rhp / d₀)
  have hE_max : 0 < E_max := by positivity
  let c₀ : ℝ := max c_min (max ((E_max + 1) ^ 3) ((2 * B₀ + 1) ^ 3))
  have hc₀_min : c_min ≤ c₀ := le_max_left _ _
  have hc₀_2 : 2 ≤ c₀ := hc_min.trans hc₀_min
  have hε_small : ∀ {c : ℝ}, c₀ ≤ c → liftEps c * CZ_loc ≤ c₁' / 2 ∧ liftEps c * CZ_rhp ≤ d₀ / 2 ∧
      2 * B₀ ≤ c ^ (1 / 3 : ℝ) := by
    intro c hc
    have hE3 : (E_max + 1) ^ 3 ≤ c := (le_max_left _ _).trans ((le_max_right _ _).trans hc)
    have hB3 : (2 * B₀ + 1) ^ 3 ≤ c := (le_max_right _ _).trans ((le_max_right _ _).trans hc)
    have hc0 : 0 < c := by linarith
    have hcube := liftEps_cube_mul hc0
    have hinv : liftEps c ≤ (E_max + 1)⁻¹ := by
      have hpow : liftEps c ^ 3 ≤ ((E_max + 1)⁻¹) ^ 3 := by
        rw [inv_pow]
        have : c⁻¹ ≤ ((E_max + 1) ^ 3)⁻¹ := inv_anti₀ (by positivity) hE3
        have hce : liftEps c ^ 3 = c⁻¹ := by
          calc liftEps c ^ 3 = (liftEps c ^ 3 * c) * c⁻¹ := by field_simp [hc0.ne']
            _ = c⁻¹ := by rw [hcube, one_mul]
        linarith
      by_contra hlt; push Not at hlt
      exact absurd (pow_lt_pow_left₀ hlt (by positivity) (by norm_num : 3 ≠ 0)) (by linarith)
    have h1 : liftEps c * CZ_loc ≤ c₁' / 2 := by
      have hE1 : 2 * CZ_loc / c₁' ≤ E_max := le_max_left _ _
      have h2 : liftEps c * (2 * CZ_loc / c₁') ≤ 1 := by
        calc liftEps c * (2 * CZ_loc / c₁') ≤ (E_max + 1)⁻¹ * E_max :=
              mul_le_mul hinv hE1 (by positivity) (by positivity)
          _ ≤ 1 := by rw [inv_mul_le_one₀ (by positivity)]; linarith
      have : liftEps c * CZ_loc = (c₁' / 2) * (liftEps c * (2 * CZ_loc / c₁')) := by
        field_simp [hc₁'.ne']
      rw [this]; nlinarith [hc₁']
    have h2 : liftEps c * CZ_rhp ≤ d₀ / 2 := by
      have hE2 : 2 * CZ_rhp / d₀ ≤ E_max := le_max_right _ _
      have h2' : liftEps c * (2 * CZ_rhp / d₀) ≤ 1 := by
        calc liftEps c * (2 * CZ_rhp / d₀) ≤ (E_max + 1)⁻¹ * E_max :=
              mul_le_mul hinv hE2 (by positivity) (by positivity)
          _ ≤ 1 := by rw [inv_mul_le_one₀ (by positivity)]; linarith
      have : liftEps c * CZ_rhp = (d₀ / 2) * (liftEps c * (2 * CZ_rhp / d₀)) := by
        field_simp [hd₀.ne']
      rw [this]; nlinarith [hd₀]
    have h3 : 2 * B₀ ≤ c ^ (1 / 3 : ℝ) := by
      have hp3 : (c ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = c := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
      have hBpos : 0 ≤ 2 * B₀ := by linarith
      have hpow : (2 * B₀) ^ 3 ≤ (c ^ (1 / 3 : ℝ)) ^ 3 := by
        rw [hp3]
        calc (2 * B₀) ^ 3 ≤ (2 * B₀ + 1) ^ 3 := pow_le_pow_left₀ hBpos (by linarith) 3
          _ ≤ c := hB3
      by_contra hlt; push Not at hlt
      exact absurd (pow_lt_pow_left₀ hlt (Real.rpow_nonneg hc0.le _) (by norm_num : 3 ≠ 0)) (by linarith)
    exact ⟨h1, h2, h3⟩
  let a_cap : ℝ := ceCs * ceBeta1 * K / (2 * (m : ℝ))
  have ha_cap : 0 < a_cap := by have := ceCs_pos; have := ceBeta1_pos; positivity
  let k_mult : ℝ := (1 + a_cap)⁻¹ ^ m
  have hk_mult : 0 < k_mult := by positivity
  have hmult_floor : ∀ {c x : ℝ}, c₀ ≤ c → 0 ≤ x → x ≤ c ^ (1 / 3 : ℝ) →
      k_mult ≤ uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m := by
    intro c x hc hx hx_top
    have hc0 : 0 < c := by linarith
    have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hε_c : liftEps c * c ^ (1 / 3 : ℝ) = 1 := by
      have hpow : (liftEps c * c ^ (1 / 3 : ℝ)) ^ 3 = 1 := by
        have hp3 : (c ^ (1 / 3 : ℝ)) ^ (3 : ℕ) = c := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc0.le]; norm_num
        calc (liftEps c * c ^ (1 / 3 : ℝ)) ^ 3 = liftEps c ^ 3 * (c ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by ring
          _ = liftEps c ^ 3 * c := by rw [hp3]
          _ = 1 := liftEps_cube_mul hc0
      have hn : 0 ≤ liftEps c * c ^ (1 / 3 : ℝ) := mul_nonneg (liftEps_pos hc0).le (Real.rpow_nonneg hc0.le _)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact absurd (pow_lt_pow_left₀ hlt hn (by norm_num : 3 ≠ 0)) (by linarith)
      · exact absurd (pow_lt_pow_left₀ hgt zero_le_one (by norm_num : 3 ≠ 0)) (by linarith)
    have hx_le : liftEps c * x ≤ 1 := by
      calc liftEps c * x ≤ liftEps c * c ^ (1 / 3 : ℝ) :=
            mul_le_mul_of_nonneg_left hx_top (liftEps_pos hc0).le
        _ = 1 := hε_c
    have hprod_le : ceCs * (ceBeta1 * K * liftEps c / 2) / m * x ≤ a_cap := by
      calc ceCs * (ceBeta1 * K * liftEps c / 2) / m * x = a_cap * (liftEps c * x) := by
            dsimp [a_cap]; field_simp [hm0]
        _ ≤ a_cap * 1 := mul_le_mul_of_nonneg_left hx_le ha_cap.le
        _ = a_cap := mul_one _
    have hnn : 0 ≤ ceCs * (ceBeta1 * K * liftEps c / 2) / m * x := by
      have := ceCs_pos; have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    exact pow_le_pow_left₀ (by positivity) ((inv_anti₀ (by positivity) (by linarith)).trans (e1r_lower hnn)) m
  have hWD_real : ∀ {c x : ℝ}, 0 ≤ x →
      W_D c (x : ℂ) = (((uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
          (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x))) : ℝ) : ℂ) := by
    intro c x hx
    dsimp [W_D]
    have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * (x : ℂ)) =
        airyTwistedLaplaceC X ((ceCs : ℂ) * (x : ℂ)) +
          (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * (x : ℂ)) := by
      have hre : 0 ≤ ((ceCs : ℂ) * (x : ℂ)).re := by simp; exact mul_nonneg ceCs_pos.le hx
      have : D c = fun u => X u + liftEps c * Z c u := rfl
      rw [this, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
        airyTwistedLaplaceC_const_mul]
    unfold liftSymbol liftMultiplier
    rw [hD_split]
    have h1 : (((ceCs * (ceBeta1 * K * liftEps c / 2) / (m : ℝ) : ℝ) : ℂ) * (x : ℂ)) =
        ((ceCs * (ceBeta1 * K * liftEps c / 2) / m * x : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) := by push_cast; ring
    rw [h1, h2, uctE1r_cast, airyTwistedLaplaceC_ofReal, airyTwistedLaplaceC_ofReal]
    push_cast; ring
  have hWD_re : ∀ {c x : ℝ}, 0 ≤ x → (W_D c (x : ℂ)).re =
      uctE1r (ceCs * (ceBeta1 * K * liftEps c / 2) / m * x) ^ m *
        (airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x)) := fun {c x} hx => by
    rw [hWD_real hx, Complex.ofReal_re]
  have hWD_im : ∀ {c x : ℝ}, 0 ≤ x → (W_D c (x : ℂ)).im = 0 := fun {c x} hx => by
    rw [hWD_real hx, Complex.ofReal_im]
  have hX_small_r : ∀ x ∈ Icc (0 : ℝ) x₀, c₁' * Real.sqrt x ≤ airyTwistedLaplace X (ceCs * x) := by
    intro x hx
    have h := hX_small x hx
    rwa [airyTwistedLaplaceC_ofReal, Complex.ofReal_re] at h
  have hX_tail_r : ∀ x : ℝ, B₀ / 2 ≤ x → d₀ * (1 + x) ^ (-(5 / 2 : ℝ)) ≤ airyTwistedLaplace X (ceCs * x) := by
    intro x hx
    have h := hX_tail x hx
    rwa [airyTwistedLaplaceC_ofReal, Complex.ofReal_re] at h
  have hZ0_r : ∀ c : ℝ, c_min ≤ c → ceK * m_Z ≤ airyTwistedLaplace (Z c) 0 := by
    intro c hc
    have heq := airyTwistedLaplaceC_zero_eq (Z c)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm, airyTwistedLaplaceC_ofReal] at heq
    have hre := Complex.ofReal_injective heq
    rw [hre]; exact mul_le_mul_of_nonneg_left (hZ_mass c hc) ceK_pos.le
  have hZ_r : ∀ c x : ℝ, c_min ≤ c → 0 ≤ x →
      |airyTwistedLaplace (Z c) (ceCs * x)| ≤ CZ_rhp * (1 + x) ^ (-(5 / 2 : ℝ)) := by
    intro c x hc hx0
    have h1 := hZ_rhp hc (w := (x : ℂ)) (by simpa using hx0)
    rw [show ((ceCs : ℂ) * (x : ℂ)) = ((ceCs * x : ℝ) : ℂ) by push_cast; ring,
      airyTwistedLaplaceC_ofReal, Complex.norm_real, Real.norm_eq_abs,
      show (1 : ℂ) + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs] at h1
    have h1p : |1 + x| = 1 + x := abs_of_nonneg (by linarith)
    rw [h1p] at h1
    exact h1
  have hD_small : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (0 : ℝ) x₀ →
      (c₁' / 2) * Real.sqrt x + ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
    intro c x hc hx
    exact ceDualLine_hsmall_bound c₁' m_Z CZ_loc c_min hX_small_r Z hZ0_r hZ_loc
      (hc₀_min.trans hc) (by linarith) hx (hε_small hc).1
  have hD_tail : ∀ {c x : ℝ}, c₀ ≤ c → B₀ / 2 ≤ x →
      (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
    intro c x hc hx
    exact ceDualLine_htail_bound d₀ B₀ CZ_rhp c_min hX_tail_r Z hZ_r
      (hc₀_min.trans hc) (by linarith) hx (by linarith) (hε_small hc).2.1
  have hD_J : ∀ {c x : ℝ}, c₀ ≤ c → x ∈ Icc (x₀ / 3) (2 * B₀) →
      z₀ * liftEps c ≤ airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
    intro c x hc hx
    have h0 : 0 < c := by linarith
    have hX : 0 ≤ airyTwistedLaplace X (ceCs * x) := by
      rw [airyTwistedLaplace_eq_ceK_airyLaplace]
      exact mul_nonneg ceK_pos.le (hnonneg (ceCs * x) (mul_pos ceCs_pos (by linarith [hx.1])))
    have hZ := hZ_J c (hc₀_min.trans hc) x hx
    rw [airyTwistedLaplaceC_ofReal, Complex.ofReal_re] at hZ
    have hmul : liftEps c * z₀ ≤ liftEps c * airyTwistedLaplace (Z c) (ceCs * x) :=
      mul_le_mul_of_nonneg_left hZ (liftEps_pos h0).le
    linarith
  let b : ℝ := k_mult * (ceK * m_Z)
  let c_J : ℝ := k_mult * z₀
  let d_tail : ℝ := k_mult * (d₀ / 2)
  let M_small : ℝ := (2 : ℝ) ^ m * max (2 * CX_loc * Real.sqrt (3 / 2) / c₁') (CZ_rhp / (ceK * m_Z))
  let M_tail : ℝ := (2 : ℝ) ^ m * (2 ^ (5 / 2 : ℝ) * (CX_rhp + CZ_rhp) / (d₀ / 2))
  let M : ℝ := max 1 (max M_small M_tail)
  let Λ_add_max : ℝ := max (CX_loc * Real.sqrt 3) CX_rhp
  let K_D : ℝ := CX_rhp + CZ_rhp
  refine ⟨c₀, M, M, Λ_add_max, b, c_J, d_tail, K_D, hc₀_min, le_max_left _ _, le_max_left _ _,
    by positivity, by have := ceK_pos; positivity, by positivity, by positivity, by positivity,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c _; exact liftSymbol_differentiableOn (hUD c) _ m
  · intro c x _ hx; exact hWD_im hx.le
  · intro c x hc hx hx_top
    rw [hWD_re hx.le]
    refine mul_nonneg (pow_nonneg (uctE1r_pos _).le m) ?_
    rcases le_or_gt x (x₀ / 3) with h1 | h1
    · have hDs := hD_small hc ⟨hx.le, by linarith⟩
      have h0 : 0 < c := by linarith
      have hnn1 : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
      have hnn2 : 0 ≤ ceK * m_Z * liftEps c := by have := ceK_pos; have := liftEps_pos h0; positivity
      linarith
    · rcases le_or_gt x (2 * B₀) with h2 | h2
      · have hDJ := hD_J hc ⟨h1.le, h2⟩
        have h0 : 0 < c := by linarith
        have hnn : 0 ≤ z₀ * liftEps c := mul_nonneg hz₀.le (liftEps_pos h0).le
        exact hnn.trans hDJ
      · have hDt := hD_tail hc (by linarith [hB₀_pos])
        have : 0 ≤ (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ)) := by positivity
        linarith
  · intro c x hc hx hx_lt _
    rw [hWD_re hx.le]
    have hc0 : 0 < c := by linarith
    have hx_le_c : x ≤ c ^ (1 / 3 : ℝ) := by linarith [(hε_small hc).2.2]
    have hmult := hmult_floor hc hx.le hx_le_c
    have hDs := hD_small hc ⟨hx.le, hx_lt.le⟩
    have hle1 : ceK * m_Z * liftEps c ≤
        airyTwistedLaplace X (ceCs * x) + liftEps c * airyTwistedLaplace (Z c) (ceCs * x) := by
      have : 0 ≤ (c₁' / 2) * Real.sqrt x := by positivity
      linarith
    have hb_eq : b * c ^ (-(1 / 3 : ℝ)) = k_mult * (ceK * m_Z * liftEps c) := by
      unfold liftEps; dsimp [b]; ring
    rw [hb_eq]
    exact mul_le_mul hmult hle1 (by have := ceK_pos; have := liftEps_pos hc0; positivity)
      (pow_nonneg (uctE1r_pos _).le _)
  · intro c x hc hxB hx_top
    rw [hWD_re (by linarith)]
    have hmult := hmult_floor hc (by linarith) hx_top
    have hDt := hD_tail hc (by linarith [hB₀_pos])
    dsimp [d_tail]
    calc k_mult * (d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))
        = k_mult * ((d₀ / 2) * (1 + x) ^ (-(5 / 2 : ℝ))) := by ring
      _ ≤ _ := mul_le_mul hmult hDt (by positivity) (pow_nonneg (uctE1r_pos _).le _)
  · intro c x hc hxJ hx_top
    rw [hWD_re (by linarith [hxJ.1])]
    have hc0 : 0 < c := by linarith
    have hmult := hmult_floor hc (by linarith [hxJ.1]) hx_top
    have hDJ := hD_J hc hxJ
    have hcj_eq : c_J * c ^ (-(1 / 3 : ℝ)) = k_mult * (z₀ * liftEps c) := by
      unfold liftEps; dsimp [c_J]; ring
    rw [hcj_eq]
    exact mul_le_mul hmult hDJ (by have := liftEps_pos hc0; positivity) (pow_nonneg (uctE1r_pos _).le _)
  · intro c x y hc hx _ hx_not hy
    exact ceDualLine_hA1_aux (fun c u => rfl) hUX hUZ hUD hx₀ hB₀_pos hc₁' hd₀ hCX_loc hCX_rhp.le
      hCZ_rhp hm_Z hc₀_2 rfl rfl ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)) hX_loc hX_rhp
      (fun hc' => hZ_rhp (hc₀_min.trans hc')) hD_small hD_tail hWD_re (by linarith) hm hc hx hx_not hy
  · intro c x y hc hx _ hx_not
    exact ceDualLine_hA2_aux (fun c u => rfl) hUX hUZ hx₀ hB₀_pos hc₁' hd₀ hCX_loc hCX_rhp.le
      hCZ_rhp hm_Z hc₀_2 ((le_max_left _ _).trans (le_max_right _ _)) rfl
      ((le_max_right _ _).trans (le_max_right _ _)) (le_max_left _ _) (le_max_right _ _)
      hX_loc hX_rhp (fun hc' => hZ_rhp (hc₀_min.trans hc')) hD_small hD_tail hWD_re (by linarith)
      hc hx hx_not
  · intro c w hc hw
    have hc0 : 0 < c := by linarith
    have hδ0 : 0 ≤ ceBeta1 * K * liftEps c / 2 := by
      have := ceBeta1_pos; have := liftEps_pos hc0; positivity
    have h1w : 1 ≤ ‖1 + w‖ := by
      have := Complex.re_le_norm (1 + w)
      simp only [Complex.add_re, Complex.one_re] at this; linarith
    have hpow1 : ‖1 + w‖ ^ (-(5 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1w (by norm_num)
    have hXw := (hX_rhp w hw.le).trans (mul_le_of_le_one_right hCX_rhp.le hpow1)
    have hZw := (hZ_rhp (hc₀_min.trans hc) hw.le).trans (mul_le_of_le_one_right hCZ_rhp.le hpow1)
    have hε1 : liftEps c ≤ 1 := liftEps_le_one_of_two_le (hc₀_2.trans hc)
    have hD_split : airyTwistedLaplaceC (D c) ((ceCs : ℂ) * w) =
        airyTwistedLaplaceC X ((ceCs : ℂ) * w) +
          (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w) := by
      have hre : 0 ≤ ((ceCs : ℂ) * w).re := by simp; exact mul_nonneg ceCs_pos.le hw.le
      have : D c = fun u => X u + liftEps c * Z c u := rfl
      rw [this, airyTwistedLaplaceC_add (hUX.integrable _ hre) (((hUZ c).smul _).integrable _ hre),
        airyTwistedLaplaceC_const_mul]
    dsimp [W_D, liftSymbol]
    rw [norm_mul, hD_split]
    calc ‖liftMultiplier (ceBeta1 * K * liftEps c / 2) m w‖ *
          ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
        ≤ 1 * (CX_rhp + 1 * CZ_rhp) := by
          refine mul_le_mul (norm_liftMultiplier_le_one hδ0 m hw.le) ?_ (norm_nonneg _) zero_le_one
          calc ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w) + (liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖
              ≤ ‖airyTwistedLaplaceC X ((ceCs : ℂ) * w)‖ +
                  ‖(liftEps c : ℂ) * airyTwistedLaplaceC (Z c) ((ceCs : ℂ) * w)‖ := norm_add_le _ _
            _ ≤ CX_rhp + 1 * CZ_rhp := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (liftEps_pos hc0)]
                exact add_le_add hXw (mul_le_mul hε1 hZw (norm_nonneg _) zero_le_one)
      _ = CX_rhp + CZ_rhp := by ring

/-- info: 'FormalResearch.SignUncertainty.o6FamilyEst_of_genRational_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms o6FamilyEst_of_genRational_family

/-- info: 'FormalResearch.SignUncertainty.ce_dual_floors' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_dual_floors

/-- info: 'FormalResearch.SignUncertainty.ce_dual_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ce_dual_line

end FormalResearch.SignUncertainty

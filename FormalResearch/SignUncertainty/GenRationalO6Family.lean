module

public import FormalResearch.SignUncertainty.GenRationalAiryTail
public import FormalResearch.SignUncertainty.GenRationalAiryU1
public import FormalResearch.SignUncertainty.MiddleBandPositivityDual
public import FormalResearch.SignUncertainty.MiddleBandE6
public import FormalResearch.SignUncertainty.WindowTranslation
public import FormalResearch.CohnElkies.WindowSmoothConv
public import FormalResearch.SignUncertainty.CeLiftSign
public import FormalResearch.SignUncertainty.Gt1Interface

/-!
# `O6FamilyEst` for finite linear combinations of generalized rational-Airy seeds

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex` and `ce_lift_proofs.tex`.

* `hasU2_finset_sum`: `HasU2` closure for finite real linear combinations in `ℛ_Ai^gen`.
* `airyTwistedLaplaceC_finset_sum`: linearity of `airyTwistedLaplaceC` on finite combinations in `ℛ_Ai^gen`.
* `o6FamilyEst_of_genRational_family`: `O6FamilyEst` for any uniformly bounded family of finite linear
  combinations of generalized rational-Airy seeds (`HasGenRationalAiryCoeffs`), bundling `(e4)`, `(e5)`, `(e6)`
  over `(K, c)`.
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

/-- `HasU2` closure for finite real linear combinations of generalized rational-Airy seeds. -/
lemma hasU2_finset_sum {ι : Type*} (t : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
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

/-- Linearity of `airyTwistedLaplaceC` on finite linear combinations of generalized rational-Airy seeds. -/
lemma airyTwistedLaplaceC_finset_sum {ι : Type*} (t : Finset ι) (B : ι → ℂ → ℂ) (b₀₀ b₁₁ : ι → ℝ)
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
    (α : ι → ℝ → ℝ → ℝ) (R δ₁ : ℝ) (hR : 0 ≤ R) (_hδ₁ : 0 < δ₁)
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
    have heqF : (fun u : ℝ => ∑ i ∈ s, α i K c * (B i (u : ℂ)).re) =
        fun u : ℝ => ∑ i ∈ s, α' i K c * (B i (u : ℂ)).re := by
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
        split_ifs
        exact ⟨(hAG_pos i hi).le, hAG_bd i hi hδ_mem⟩)
      (fun i hi => hα i hi K c hK hc2k hc8 hcδ)
    exact ho5 (hasU2_finset_sum s B β₀₀ β₁₁ hB (fun i => α i K c))
      (hF_cont hK hc2k hc8 hcδ) hδ0 hc2 hξ hL hL0 hL2 hS100 hGt1_F
  exact ⟨hg0, hF_cont, hconv, he4, he5, he6⟩

/-- info: 'FormalResearch.SignUncertainty.o6FamilyEst_of_genRational_family' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms o6FamilyEst_of_genRational_family

end FormalResearch.SignUncertainty

module

public import FormalResearch.ModularBootstrap.Spin.SpinS4CalAdjoint

/-!
# SPIN-S4 Corollary `s4:2.3` (Calibrated Vacuum Remainder)

Proves:
1. `spinS4_2_1_all_quads`: four-quadrant extension of `spinS4_2_1` by `D_4` symmetry.
2. `spinCalInt_eq_spinRc`: exact calibrated adjoint formula for `spinCalInt c Φ`.
3. `spinRc_near_tip_bound`: near-tip bound `|R_c(ξ, d) - 1| ≤ C_near δ_n` on the gap disc.
4. **`spinS4_2_3 : SpinS4_2_3`** (`spinning_s4.tex`, Corollary 2.3).
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.ModularBootstrap.Spin

open FormalResearch.ModularBootstrap

/-! ### Elementary `n`-scale helpers for `c ≥ 40` -/

lemma deltaN_ge_inv {n : ℝ} (hn : 39 ≤ n) :
    n⁻¹ ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n := by
  have hn_pos : 0 < n := by linarith
  have hlog : 1 ≤ Real.log n := by
    rw [← Real.exp_le_exp, Real.exp_log hn_pos]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hrpow : n ^ (-(1 / 3 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
  have hpow_eq : n⁻¹ = n ^ (-(2 / 3 : ℝ)) * n ^ (-(1 / 3 : ℝ)) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hn_pos]; congr 1; norm_num
  rw [hpow_eq]
  exact mul_le_mul_of_nonneg_left (hrpow.trans hlog) (Real.rpow_nonneg hn_pos.le _)

lemma deltaN_le_three_rpow {n : ℝ} (hn : 1 ≤ n) :
    n ^ (-(2 / 3 : ℝ)) * Real.log n ≤ 3 * n ^ (-(1 / 3 : ℝ)) := by
  have hn_pos : 0 < n := by linarith
  have h13_pos : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
  have hlog_le : Real.log n ≤ 3 * n ^ (1 / 3 : ℝ) := by
    have h1 := Real.log_le_sub_one_of_pos h13_pos
    rw [Real.log_rpow hn_pos] at h1
    linarith
  have hmul : n ^ (-(2 / 3 : ℝ)) * Real.log n ≤ n ^ (-(2 / 3 : ℝ)) * (3 * n ^ (1 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_le (Real.rpow_nonneg hn_pos.le _)
  have hcomb : n ^ (-(2 / 3 : ℝ)) * (3 * n ^ (1 / 3 : ℝ)) = 3 * n ^ (-(1 / 3 : ℝ)) := by
    rw [show n ^ (-(2 / 3 : ℝ)) * (3 * n ^ (1 / 3 : ℝ)) =
      3 * (n ^ (-(2 / 3 : ℝ)) * n ^ (1 / 3 : ℝ)) by ring, ← Real.rpow_add hn_pos]
    congr 2; norm_num
  exact hmul.trans_eq hcomb

lemma deltaN_le_one {n : ℝ} (hn : 39 ≤ n) :
    n ^ (-(2 / 3 : ℝ)) * Real.log n ≤ 1 := by
  have hn_pos : 0 < n := by linarith
  have h1 := deltaN_le_three_rpow (by linarith : (1 : ℝ) ≤ n)
  have hinv : n ^ (-(1 / 3 : ℝ)) ≤ 1 / 3 := by
    have h27 : (3 : ℝ) ≤ n ^ (1 / 3 : ℝ) := by
      have hpow : (3 : ℝ) ^ (3 : ℕ) ≤ (n ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hn_pos.le]
        norm_num; linarith
      exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hn_pos.le _) hpow
    rw [Real.rpow_neg hn_pos.le]
    exact (inv_anti₀ (by norm_num) h27).trans (by norm_num)
  linarith

lemma coeff_deltaN_le {n K B : ℝ} (hK : 0 ≤ K) (hB : 0 < B)
    (hn : max 39 ((3 * K / B) ^ 3) ≤ n) :
    K * (n ^ (-(2 / 3 : ℝ)) * Real.log n) ≤ B := by
  have h39 : (39 : ℝ) ≤ n := (le_max_left (39 : ℝ) ((3 * K / B) ^ 3)).trans hn
  have hn_pos : 0 < n := by linarith
  have hcub : (3 * K / B) ^ 3 ≤ n := (le_max_right _ _).trans hn
  have h13 : 3 * K / B ≤ n ^ (1 / 3 : ℝ) := by
    have hpow : (3 * K / B) ^ (3 : ℕ) ≤ (n ^ (1 / 3 : ℝ)) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast (n ^ (1 / 3 : ℝ)) 3, ← Real.rpow_mul hn_pos.le]
      norm_num; exact hcub
    exact le_of_pow_le_pow_left₀ (by norm_num) (Real.rpow_nonneg hn_pos.le _) hpow
  have h3d := deltaN_le_three_rpow (by linarith : (1 : ℝ) ≤ n)
  have hmul : K * (3 * n ^ (-(1 / 3 : ℝ))) ≤ B := by
    rw [Real.rpow_neg hn_pos.le]
    have hdiv : 3 * K ≤ B * n ^ (1 / 3 : ℝ) := by
      have h1 := (div_le_iff₀ hB).mp h13; linarith
    have h13_pos : 0 < n ^ (1 / 3 : ℝ) := Real.rpow_pos_of_pos hn_pos _
    calc K * (3 * (n ^ (1 / 3 : ℝ))⁻¹) = (3 * K) * (n ^ (1 / 3 : ℝ))⁻¹ := by ring
      _ ≤ (B * n ^ (1 / 3 : ℝ)) * (n ^ (1 / 3 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hdiv (inv_nonneg.mpr h13_pos.le)
      _ = B := by field_simp [h13_pos.ne']
  exact (mul_le_mul_of_nonneg_left h3d hK).trans hmul

/-! ### Four-quadrant extension of `spinS4_2_1` -/

lemma spinS4_2_1_all_quads {C_x p : ℝ} (hp : 0 < p) :
    ∃ K_p C_p c₀ : ℝ, 0 < K_p ∧ 0 < C_p ∧ 40 ≤ c₀ ∧
      ∀ {c : ℝ}, c₀ ≤ c →
        let n := c - 1
        let a := n / 12
        let δ := K_p * n ^ (-(2 / 3 : ℝ)) * Real.log n
        ∀ {x₁ : ℝ}, 0 ≤ x₁ → x₁ ≤ xiStar + C_x * n ^ (-(2 / 3 : ℝ)) →
          ∀ {Φ : ℝ × ℝ → ℝ}, SpinTestClass a Φ → spinM2 a Φ = 1 →
            ∫ q in {q : ℝ × ℝ | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ spinLongDist q < xiStar - δ},
              |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤
                4 * C_p * n ^ (-p) := by
  obtain ⟨K_p, C_p, c₀, hK_pos, hC_pos, hc0, h21⟩ := spinS4_2_1 (C_x := C_x) hp
  refine ⟨K_p, C_p, c₀, hK_pos, hC_pos, hc0, ?_⟩
  intro c hc n a δ x₁ hx10 hx1_ub Φ hΦ hM2
  have ha0 : 0 < a := by dsimp [a, n]; linarith
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  let E : Set (ℝ × ℝ) := {q | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ spinLongDist q < xiStar - δ}
  let E_pp : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧
    (q.1 + q.2) / 2 < xiStar - δ}
  let g : ℝ × ℝ → ℝ := fun q => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2
  have hg_nl : ∀ x y : ℝ, g (-x, y) = g (x, y) := fun x y => by
    dsimp [g]; rw [spinG_d4_neg_left hΦ, spinWc_even]
  have hg_nr : ∀ x y : ℝ, g (x, -y) = g (x, y) := fun x y => by
    dsimp [g]; rw [spinG_d4_neg_right hΦ, spinWc_even]
  have hpp_bd : ∫ q in E_pp, g q ≤ C_p * n ^ (-p) := h21 hc hx10 hx1_ub hΦ hM2
  let E1 : Set (ℝ × ℝ) := {q ∈ E | 0 < q.1 ∧ 0 < q.2}
  let E2 : Set (ℝ × ℝ) := {q ∈ E | q.1 < 0 ∧ 0 < q.2}
  let E3 : Set (ℝ × ℝ) := {q ∈ E | 0 < q.1 ∧ q.2 < 0}
  let E4 : Set (ℝ × ℝ) := {q ∈ E | q.1 < 0 ∧ q.2 < 0}
  have hE1_eq : E1 = E_pp := by
    ext q
    simp only [E1, E, E_pp, Set.mem_sep_iff, Set.mem_ofPred_eq, spinLongDist]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp1, hp2⟩
      rw [abs_of_pos hp1, abs_of_pos hp2] at h2
      exact ⟨hp1, hp2, h1, by linarith⟩
    · rintro ⟨hp1, hp2, h1, h2⟩
      exact ⟨⟨h1, by rw [abs_of_pos hp1, abs_of_pos hp2]; linarith⟩, hp1, hp2⟩
  have hmeas_E : MeasurableSet E := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) / 2) := by fun_prop
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet.inter
      (isOpen_lt h2 continuous_const).measurableSet
  have hmE1 : MeasurableSet E1 := hmeas_E.inter
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  have hmE2 : MeasurableSet E2 := hmeas_E.inter
    ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_const continuous_snd).measurableSet)
  have hmE3 : MeasurableSet E3 := hmeas_E.inter
    ((isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet)
  have hmE4 : MeasurableSet E4 := hmeas_E.inter
    ((isOpen_lt continuous_fst continuous_const).measurableSet.inter
      (isOpen_lt continuous_snd continuous_const).measurableSet)
  have h_quad : ∀ (e : ℝ × ℝ ≃ᵐ ℝ × ℝ),
      Measure.map e (volume : Measure (ℝ × ℝ)) = volume →
      (∀ q : ℝ × ℝ, g (e q) = g q) →
      ∀ (S : Set (ℝ × ℝ)), MeasurableSet S → (∀ q, q ∈ S ↔ e q ∈ E1) →
      ∫ q in S, g q = ∫ q in E1, g q := by
    intro e hmp he_g S hS hSE
    rw [← integral_indicator hS]
    have hind : ∫ q : ℝ × ℝ, S.indicator g q = ∫ q : ℝ × ℝ, E1.indicator g (e q) := by
      refine integral_congr_ae (Eventually.of_forall fun q => ?_)
      by_cases hq : q ∈ S
      · have hq' : e q ∈ E1 := (hSE q).mp hq
        simp only [Set.indicator_of_mem hq, Set.indicator_of_mem hq', he_g q]
      · have hq' : e q ∉ E1 := fun h => hq ((hSE q).mpr h)
        simp [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
    have hmap := integral_map_equiv (μ := (volume : Measure (ℝ × ℝ))) e (E1.indicator g)
    rw [hmp] at hmap
    rw [hind, hmap.symm, integral_indicator hmE1]
  have hE2_eq : ∫ q in E2, g q = ∫ q in E1, g q := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.refl ℝ)
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      rw [Measure.volume_eq_prod]
      have he : (⇑e : ℝ × ℝ → ℝ × ℝ) = Prod.map Neg.neg id := rfl
      rw [he, ← Measure.map_prod_map _ _ measurable_neg measurable_id,
        Measure.map_neg_eq_self, Measure.map_id]
    refine h_quad e hmp (fun q => by change g (-q.1, q.2) = g q; exact hg_nl q.1 q.2) E2 hmE2
      (fun q => by
        change (q ∈ E ∧ q.1 < 0 ∧ 0 < q.2) ↔ ((-q.1, q.2) ∈ E ∧ 0 < -q.1 ∧ 0 < q.2)
        dsimp [E, spinLongDist]
        simp only [Set.mem_ofPred_eq, neg_sq, abs_neg, Left.neg_pos_iff])
  have hE3_eq : ∫ q in E3, g q = ∫ q in E1, g q := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      rw [Measure.volume_eq_prod]
      have he : (⇑e : ℝ × ℝ → ℝ × ℝ) = Prod.map id Neg.neg := rfl
      rw [he, ← Measure.map_prod_map _ _ measurable_id measurable_neg,
        Measure.map_id, Measure.map_neg_eq_self]
    refine h_quad e hmp (fun q => by change g (q.1, -q.2) = g q; exact hg_nr q.1 q.2) E3 hmE3
      (fun q => by
        change (q ∈ E ∧ 0 < q.1 ∧ q.2 < 0) ↔ ((q.1, -q.2) ∈ E ∧ 0 < q.1 ∧ 0 < -q.2)
        dsimp [E, spinLongDist]
        simp only [Set.mem_ofPred_eq, neg_sq, abs_neg, Left.neg_pos_iff])
  have hE4_eq : ∫ q in E4, g q = ∫ q in E1, g q := by
    let e : ℝ × ℝ ≃ᵐ ℝ × ℝ := (MeasurableEquiv.neg ℝ).prodCongr (MeasurableEquiv.neg ℝ)
    have hmp : Measure.map e (volume : Measure (ℝ × ℝ)) = volume := by
      rw [Measure.volume_eq_prod]
      have he : (⇑e : ℝ × ℝ → ℝ × ℝ) = Prod.map Neg.neg Neg.neg := rfl
      rw [he, ← Measure.map_prod_map _ _ measurable_neg measurable_neg, Measure.map_neg_eq_self]
    refine h_quad e hmp (fun q => by change g (-q.1, -q.2) = g q; rw [hg_nl, hg_nr]) E4 hmE4
      (fun q => by
        change (q ∈ E ∧ q.1 < 0 ∧ q.2 < 0) ↔ ((-q.1, -q.2) ∈ E ∧ 0 < -q.1 ∧ 0 < -q.2)
        dsimp [E, spinLongDist]
        simp only [Set.mem_ofPred_eq, neg_sq, abs_neg, Left.neg_pos_iff])
  have hax : volume {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0} = 0 := by
    have h1 : volume {q : ℝ × ℝ | q.1 = 0} = 0 := by
      have : {q : ℝ × ℝ | q.1 = 0} = {(0 : ℝ)} ×ˢ Set.univ := by ext q; simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
    have h2 : volume {q : ℝ × ℝ | q.2 = 0} = 0 := by
      have : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ {(0 : ℝ)} := by ext q; simp
      rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    exact measure_union_null h1 h2
  have hae_E : E =ᵐ[volume] E1 ∪ E2 ∪ E3 ∪ E4 := by
    filter_upwards [compl_mem_ae_iff.mpr hax] with q hq
    have hq1 : q.1 ≠ 0 := fun h => hq (Or.inl h)
    have hq2 : q.2 ≠ 0 := fun h => hq (Or.inr h)
    simp only [Set.mem_union, E1, E2, E3, E4, Set.mem_sep_iff]
    constructor
    · intro hE
      rcases lt_or_gt_of_ne hq1 with h1 | h1 <;> rcases lt_or_gt_of_ne hq2 with h2 | h2
      · right; exact ⟨hE, h1, h2⟩
      · left; left; right; exact ⟨hE, h1, h2⟩
      · left; right; exact ⟨hE, h1, h2⟩
      · left; left; left; exact ⟨hE, h1, h2⟩
    · rintro (((⟨hE, _⟩ | ⟨hE, _⟩) | ⟨hE, _⟩) | ⟨hE, _⟩) <;> exact hE
  have hd12 : Disjoint E1 E2 := Set.disjoint_left.mpr fun q h1 h2 => absurd h1.2.1 h2.2.1.not_gt
  have hd123 : Disjoint (E1 ∪ E2) E3 := Set.disjoint_left.mpr fun q h12 h3 =>
    h12.elim (fun h => absurd h.2.2 h3.2.2.not_gt) (fun h => absurd h.2.2 h3.2.2.not_gt)
  have hd1234 : Disjoint (E1 ∪ E2 ∪ E3) E4 := Set.disjoint_left.mpr fun q h123 h4 => by
    rcases h123 with (h | h) | h
    · exact absurd h.2.1 h4.2.1.not_gt
    · exact absurd h.2.2 h4.2.2.not_gt
    · exact absurd h.2.1 h4.2.1.not_gt
  have hu : ∀ {S T : Set (ℝ × ℝ)}, Disjoint S T → MeasurableSet S → MeasurableSet T →
      ∫ q in S ∪ T, g q = (∫ q in S, g q) + ∫ q in T, g q := by
    intro S T hd hS hT
    rw [← integral_indicator (hS.union hT), ← integral_indicator hS, ← integral_indicator hT,
      ← integral_add (hG_int.indicator hS) (hG_int.indicator hT)]
    congr 1; ext q
    by_cases h1 : q ∈ S <;> by_cases h2 : q ∈ T
    · exact absurd h2 (Set.disjoint_left.mp hd h1)
    · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1,
        Set.indicator_of_notMem h2, add_zero]
    · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1,
        Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
        Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hu1 := hu hd12 hmE1 hmE2
  have hu2 := hu hd123 (hmE1.union hmE2) hmE3
  have hu3 := hu hd1234 ((hmE1.union hmE2).union hmE3) hmE4
  have hcongr : ∫ q in E, g q = ∫ q in E1 ∪ E2 ∪ E3 ∪ E4, g q := setIntegral_congr_set hae_E
  have hsum : ∫ q in E, g q = 4 * ∫ q in E1, g q := by
    rw [hcongr, hu3, hu2, hu1, hE2_eq, hE3_eq, hE4_eq]; ring
  rw [hsum, hE1_eq]
  linarith

/-! ### Exact adjoint identity for `spinCalInt` and near-tip `R_c` bound -/

lemma spinCalInt_eq_spinRc {c : ℝ} (hc : 40 ≤ c) {Φ : ℝ × ℝ → ℝ}
    (hΦ : SpinTestClass ((c - 1) / 12) Φ) :
    let n := c - 1
    let a := n / 12
    spinCalInt c Φ =
      ∫ p : ℝ × ℝ, spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) *
        spinG a Φ p.1 p.2 * spinWc a p.1 * spinWc a p.2 := by
  intro n a
  have hadj := spinCal_adjoint_identity hc hΦ
    (F := fun p : ℝ × ℝ => spinG a Φ p.1 p.2)
    (by unfold spinG; exact (hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable)
    (fun p => le_rfl)
    (fun x y => spinG_d4_neg_left hΦ x y)
    (fun x y => spinG_d4_neg_right hΦ x y)
    (φ := fun _ : ℝ => (1 : ℝ)) measurable_const zero_le_one (fun _ => by norm_num)
  have hcal : spinCalInt c Φ =
      ∫ b : ℝ, a * Real.exp (n * spinL b) * 1 *
        (4 * spinCalF xiStar ^ 2 * ∫ d : ℝ, spinHbCalReal b d * spinG a Φ (b + d) (b - d)) := by
    unfold spinCalInt
    refine integral_congr_ae (Eventually.of_forall fun b => ?_)
    dsimp only
    have ha2 : 2 < a := by dsimp [a, n]; linarith
    change a * Real.exp (n * spinL b) * (spinGcal a Φ (b : ℂ)).re = _
    rw [spinGcal_re_ofReal (by linarith : (0 : ℝ) ≤ (c - 1) / 12) hΦ b]
    ring
  rw [hcal, hadj.2.2]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  unfold spinRc; ring

lemma spinRc_near_tip_bound (K_p C_x_pos : ℝ) (hKp : 0 < K_p) (hCx : 1 ≤ C_x_pos) :
    ∃ (C_near c₀ : ℝ), 0 < C_near ∧ 40 ≤ c₀ ∧
      ∀ {c x₁ : ℝ}, c₀ ≤ c →
        let n := c - 1
        let a := n / 12
        let δ_n := n ^ (-(2 / 3 : ℝ)) * Real.log n
        0 ≤ x₁ → x₁ ≤ xiStar + C_x_pos * n ^ (-(2 / 3 : ℝ)) →
        ∀ p : ℝ × ℝ, (p.1 ^ 2 + p.2 ^ 2) / 2 < x₁ ^ 2 →
          xiStar - K_p * δ_n ≤ spinLongDist p →
          |spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) - 1| ≤ C_near * δ_n := by
  obtain ⟨_C_c1, C₁, r₀, _hCc1, hC1_pos, hr₀_pos, hC1⟩ := scalC1
  let K_b : ℝ := K_p + C_x_pos + 1
  have hKb_pos : 0 < K_b := by dsimp [K_b]; linarith
  let B_d : ℝ := (r₀ / 2) ^ 2 / (2 * (xiStar + 1))
  have hBd_pos : 0 < B_d := div_pos (sq_pos_of_pos (half_pos hr₀_pos)) (by positivity [xiStar_pos])
  let B_min : ℝ := min (min (r₀ / 2) 1) B_d
  have hBm_pos : 0 < B_min := lt_min (lt_min (half_pos hr₀_pos) one_pos) hBd_pos
  let c₀ : ℝ := max 40 (1 + max 39 ((3 * K_b / B_min) ^ 3))
  let C_near : ℝ := C₁ * (K_b ^ 2 + 2 * (xiStar + 1) * K_b + 1)
  have hCnear_pos : 0 < C_near := by
    dsimp [C_near]
    exact mul_pos hC1_pos (by positivity [xiStar_pos])
  refine ⟨C_near, c₀, hCnear_pos, le_max_left _ _, ?_⟩
  intro c x₁ hc n a δ_n hx10 hx1_ub p hp_disc hp_xi
  have hc40 : 40 ≤ c := (le_max_left _ _).trans hc
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hn_max : max 39 ((3 * K_b / B_min) ^ 3) ≤ n := by
    have := (le_max_right (40 : ℝ) _).trans hc; dsimp [n]; linarith
  have hn39 : 39 ≤ n := (le_max_left _ _).trans hn_max
  have hinv_le : n⁻¹ ≤ δ_n := deltaN_ge_inv hn39
  have hδn_le1 : δ_n ≤ 1 := deltaN_le_one hn39
  have hKbδ : K_b * δ_n ≤ B_min := coeff_deltaN_le hKb_pos.le hBm_pos hn_max
  have hn_log : 1 ≤ Real.log n := by
    rw [← Real.exp_le_exp, Real.exp_log hn_pos]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  set ξ := spinLongDist p
  set d := (|p.1| - |p.2|) / 2
  have hξ_nn : 0 ≤ ξ := by dsimp [ξ, spinLongDist]; positivity
  have hd_le_ξ : |d| ≤ ξ := by
    dsimp [d, ξ, spinLongDist]
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rcases le_total |p.1| |p.2| with h | h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]; linarith [abs_nonneg p.1]
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]; linarith [abs_nonneg p.2]
  have hsq_sum : ξ ^ 2 + d ^ 2 = (p.1 ^ 2 + p.2 ^ 2) / 2 := by
    dsimp [ξ, d, spinLongDist]
    calc ((1 / 2 : ℝ) * (|p.1| + |p.2|)) ^ 2 + ((|p.1| - |p.2|) / 2) ^ 2
        = (|p.1| ^ 2 + |p.2| ^ 2) / 2 := by ring
      _ = (p.1 ^ 2 + p.2 ^ 2) / 2 := by rw [sq_abs, sq_abs]
  have hξ_lt_x1 : ξ < x₁ := by
    have : ξ ^ 2 < x₁ ^ 2 := by linarith [sq_nonneg d, hp_disc]
    by_contra hle; push Not at hle
    exact absurd this (not_lt_of_ge (sq_le_sq' (by linarith) hle))
  have hCxδ : C_x_pos * n ^ (-(2 / 3 : ℝ)) ≤ C_x_pos * δ_n := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith)
    dsimp [δ_n]
    calc n ^ (-(2 / 3 : ℝ)) = n ^ (-(2 / 3 : ℝ)) * 1 := (mul_one _).symm
      _ ≤ n ^ (-(2 / 3 : ℝ)) * Real.log n :=
          mul_le_mul_of_nonneg_left hn_log (Real.rpow_nonneg hn_pos.le _)
  have hx1_bnd : x₁ ≤ xiStar + K_b * δ_n := by
    have h1 : C_x_pos ≤ K_b := by dsimp [K_b]; linarith
    have h2 := mul_le_mul_of_nonneg_right h1 (by positivity : 0 ≤ δ_n)
    linarith
  have hξ_dev : |ξ - xiStar| ≤ K_b * δ_n := by
    rw [abs_le]; constructor
    · have : K_p ≤ K_b := by dsimp [K_b]; linarith
      have : K_p * δ_n ≤ K_b * δ_n := mul_le_mul_of_nonneg_right this (by positivity)
      linarith
    · linarith
  have hx1_pξ : x₁ + ξ ≤ 2 * (xiStar + 1) := by
    have : K_b * δ_n ≤ 1 := hKbδ.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    linarith [xiStar_pos]
  have hx1_mξ : x₁ - ξ ≤ K_b * δ_n := by
    have : K_p ≤ K_b - C_x_pos := by dsimp [K_b]; linarith
    have h1 : K_p * δ_n + C_x_pos * δ_n ≤ K_b * δ_n := by nlinarith
    linarith
  have hd_sq : d ^ 2 ≤ 2 * (xiStar + 1) * (K_b * δ_n) := by
    have hlt : d ^ 2 < 2 * (xiStar + 1) * (K_b * δ_n) :=
      calc d ^ 2 < x₁ ^ 2 - ξ ^ 2 := by linarith [hp_disc, hsq_sum]
        _ = (x₁ - ξ) * (x₁ + ξ) := by ring
        _ ≤ (K_b * δ_n) * (2 * (xiStar + 1)) :=
            mul_le_mul hx1_mξ hx1_pξ (by linarith [hx10, hξ_nn]) (by positivity)
        _ = 2 * (xiStar + 1) * (K_b * δ_n) := by ring
    exact hlt.le
  have hd_abs : |d| ≤ r₀ / 2 := by
    have hd_bd : K_b * δ_n ≤ B_d := hKbδ.trans (min_le_right _ _)
    have hsq : d ^ 2 ≤ (r₀ / 2) ^ 2 := by
      calc d ^ 2 ≤ 2 * (xiStar + 1) * (K_b * δ_n) := hd_sq
        _ ≤ 2 * (xiStar + 1) * B_d := mul_le_mul_of_nonneg_left hd_bd (by positivity [xiStar_pos])
        _ = (r₀ / 2) ^ 2 := by
            dsimp [B_d]; have hne : (2 * (xiStar + 1) : ℝ) ≠ 0 := by positivity [xiStar_pos]
            exact mul_div_cancel₀ _ hne
    exact abs_le.mpr (abs_le_of_sq_le_sq' hsq (half_pos hr₀_pos).le)
  have hξ_abs : |ξ - xiStar| ≤ r₀ / 2 :=
    hξ_dev.trans (hKbδ.trans (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hsum_r0 : |ξ - xiStar| + |d| ≤ r₀ := by linarith
  have hscal := (hC1 hc40 ξ d hd_le_ξ).2 hsum_r0
  have hξ_sq : (ξ - xiStar) ^ 2 ≤ K_b ^ 2 * δ_n := by
    have h1 : (ξ - xiStar) ^ 2 ≤ (K_b * δ_n) ^ 2 := by
      rw [← sq_abs (ξ - xiStar)]
      exact pow_le_pow_left₀ (abs_nonneg _) hξ_dev 2
    have h2 : K_b ^ 2 * δ_n * δ_n ≤ K_b ^ 2 * δ_n * 1 :=
      mul_le_mul_of_nonneg_left hδn_le1 (by positivity)
    linarith
  calc |spinRc a ξ d - 1|
      ≤ C₁ * ((ξ - xiStar) ^ 2 + d ^ 2 + n⁻¹) := hscal
    _ ≤ C₁ * (K_b ^ 2 * δ_n + 2 * (xiStar + 1) * (K_b * δ_n) + δ_n) := by gcongr
    _ = C_near * δ_n := by dsimp [C_near]; ring

/-! ### Proof of `s4:2.3` (`SpinS4_2_3`) -/

/-- **`s4:2.3` (`spinning_s4.tex`, Corollary 2.3): calibrated vacuum remainder.** -/
theorem spinS4_2_3 : SpinS4_2_3 := by
  intro C_x
  obtain ⟨c_σ, C_rc, hcσ_pos, hCrc_pos, hRc_bd⟩ := spinS4_2_2_abs_bound
  obtain ⟨K_2, C_2, c₀₂, hK2_pos, hC2_pos, hc02, h21_all⟩ :=
    spinS4_2_1_all_quads (C_x := max C_x 1) (p := 2) (by norm_num)
  obtain ⟨C_near, c₀_n, hCnear_pos, hc0n, hnear⟩ :=
    spinRc_near_tip_bound K_2 (max C_x 1) hK2_pos (le_max_right C_x 1)
  let c₀ : ℝ := max (max c₀₂ c₀_n) (1 + max 39 C_rc)
  have hc0_ge40 : 40 ≤ c₀ := le_trans hc02 (le_trans (le_max_left _ _) (le_max_left _ _))
  let C : ℝ := C_rc + 12 * C_2 + C_near
  refine ⟨c_σ, C, c₀, hcσ_pos, by positivity, hc0_ge40, ?_⟩
  intro c x₁ hc n a δ_n hx10 hx1_ub Φ hΦ hM2 hgap
  have hc40 : 40 ≤ c := hc0_ge40.trans hc
  have hc02' : c₀₂ ≤ c := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hc
  have hc0n' : c₀_n ≤ c := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hc
  have ha2 : 2 < a := by dsimp [a, n]; linarith
  have ha0 : 0 < a := by linarith
  have hn_pos : 0 < n := by dsimp [n]; linarith
  have hn39 : 39 ≤ n := by
    have := (le_max_right (max c₀₂ c₀_n) _).trans hc
    dsimp [n]; linarith [le_max_left (39 : ℝ) C_rc]
  have hCrc_n : C_rc / n ≤ 1 := (div_le_one hn_pos).mpr (by
    have := (le_max_right (max c₀₂ c₀_n) _).trans hc
    dsimp [n]; linarith [le_max_right (39 : ℝ) C_rc])
  have hinv_le : n⁻¹ ≤ δ_n := deltaN_ge_inv hn39
  have hn2_le : n ^ (-2 : ℝ) ≤ δ_n := by
    have : n ^ (-2 : ℝ) ≤ n⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    exact this.trans hinv_le
  have hδn_nn : 0 ≤ δ_n := le_trans (inv_nonneg.mpr hn_pos.le) hinv_le
  have hx1_ub' : x₁ ≤ xiStar + max C_x 1 * n ^ (-(2 / 3 : ℝ)) :=
    hx1_ub.trans (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg hn_pos.le _)) _)
  have hcal := spinCalInt_eq_spinRc hc40 hΦ
  have hvac := spinPhiVac_eq_spinWc ha0 Φ
  have hG_int : Integrable (fun q : ℝ × ℝ => |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2) :=
    integrable_spinG_wc ha0 hΦ
  have hG_meas : Measurable (fun q : ℝ × ℝ => spinG a Φ q.1 q.2) := by
    unfold spinG
    exact (hΦ.cont.comp ((continuous_const.mul continuous_fst).prodMk
      (continuous_const.mul continuous_snd))).measurable
  have hWc_meas : Continuous (spinWc a) := by unfold spinWc spinV1; fun_prop
  have hG_signed_int : Integrable (fun q : ℝ × ℝ =>
      spinG a Φ q.1 q.2 * spinWc a q.1 * spinWc a q.2) := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hG_meas.mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (spinWc_nonneg ha2.le _),
        abs_of_nonneg (spinWc_nonneg ha2.le _)]
  have hRc_int : Integrable (fun p : ℝ × ℝ =>
      spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) *
        spinG a Φ p.1 p.2 * spinWc a p.1 * spinWc a p.2) := by
    refine (hG_int.const_mul (1 + C_rc / n)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((((measurable_spinRc1 a).add (measurable_spinRc2 a)).mul hG_meas |>.mul
        (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · have hbd := (hRc_bd hc40 p).2.2
      rw [← show spinLongDist p = (|p.1| + |p.2|) / 2 by unfold spinLongDist; ring] at hbd
      change |spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| ≤ 1 + C_rc / n at hbd
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg (spinWc_nonneg ha2.le _), abs_of_nonneg (spinWc_nonneg ha2.le _)]
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      calc |spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| * |spinG a Φ p.1 p.2| *
              spinWc a p.1 * spinWc a p.2
          ≤ (1 + C_rc / n) * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = (1 + C_rc / n) * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by ring
  let Gp : ℝ × ℝ → ℝ := fun q => max (spinG a Φ q.1 q.2) 0
  let Gm : ℝ × ℝ → ℝ := fun q => max (-spinG a Φ q.1 q.2) 0
  have hGp_int : Integrable (fun q : ℝ × ℝ => Gp q * spinWc a q.1 * spinWc a q.2) := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hG_meas.max measurable_const).mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_max_right _ _),
        abs_of_nonneg (spinWc_nonneg ha2.le _), abs_of_nonneg (spinWc_nonneg ha2.le _)]
      have h1 : Gp p ≤ |spinG a Φ p.1 p.2| := max_le (le_abs_self _) (abs_nonneg _)
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      gcongr
  have hGm_int : Integrable (fun q : ℝ × ℝ => Gm q * spinWc a q.1 * spinWc a q.2) := by
    refine hG_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact (((hG_meas.neg.max measurable_const).mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_max_right _ _),
        abs_of_nonneg (spinWc_nonneg ha2.le _), abs_of_nonneg (spinWc_nonneg ha2.le _)]
      have h1 : Gm p ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      gcongr
  have hRc_p_int : Integrable (fun p : ℝ × ℝ =>
      (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) *
        Gp p * spinWc a p.1 * spinWc a p.2) := by
    refine (hG_int.const_mul (2 + C_rc / n)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((((measurable_const.sub ((measurable_spinRc1 a).add (measurable_spinRc2 a))).mul
        (hG_meas.max measurable_const)).mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · have hrc := (hRc_bd hc40 p).2.2
      rw [← show spinLongDist p = (|p.1| + |p.2|) / 2 by unfold spinLongDist; ring] at hrc
      change |spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| ≤ 1 + C_rc / n at hrc
      have hbd : |1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| ≤ 2 + C_rc / n :=
        (abs_sub_le _ 0 _).trans (by rw [sub_zero, zero_sub, abs_neg, abs_one]; linarith)
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      have hGp_le : |Gp p| ≤ |spinG a Φ p.1 p.2| := by
        rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (le_abs_self _) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2]
      calc |1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| * |Gp p| * spinWc a p.1 * spinWc a p.2
          ≤ (2 + C_rc / n) * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = (2 + C_rc / n) * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by ring
  have hRc_m_int : Integrable (fun p : ℝ × ℝ =>
      (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) *
        Gm p * spinWc a p.1 * spinWc a p.2) := by
    refine (hG_int.const_mul (2 + C_rc / n)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((((measurable_const.sub ((measurable_spinRc1 a).add (measurable_spinRc2 a))).mul
        (hG_meas.neg.max measurable_const)).mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · have hrc := (hRc_bd hc40 p).2.2
      rw [← show spinLongDist p = (|p.1| + |p.2|) / 2 by unfold spinLongDist; ring] at hrc
      change |spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| ≤ 1 + C_rc / n at hrc
      have hbd : |1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| ≤ 2 + C_rc / n :=
        (abs_sub_le _ 0 _).trans (by rw [sub_zero, zero_sub, abs_neg, abs_one]; linarith)
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      have hGm_le : |Gm p| ≤ |spinG a Φ p.1 p.2| := by
        rw [abs_of_nonneg (le_max_right _ _)]; exact max_le (neg_le_abs _) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg hw1, abs_of_nonneg hw2]
      calc |1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)| * |Gm p| * spinWc a p.1 * spinWc a p.2
          ≤ (2 + C_rc / n) * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = (2 + C_rc / n) * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by ring
  have hV_int : Integrable (fun p : ℝ × ℝ =>
      min (spinTransDist p ^ 2) 1 * Gp p * spinWc a p.1 * spinWc a p.2) := by
    refine hGp_int.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hcT : Continuous spinTransDist := by unfold spinTransDist; fun_prop
      exact (((((hcT.pow 2).min continuous_const).measurable.mul
        (hG_meas.max measurable_const)).mul (hWc_meas.comp continuous_fst).measurable).mul
        (hWc_meas.comp continuous_snd).measurable).aestronglyMeasurable
    · have hmn0 : 0 ≤ min (spinTransDist p ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
      have hmn1 : min (spinTransDist p ^ 2) 1 ≤ 1 := min_le_right _ _
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      have hGp0 := le_max_right (spinG a Φ p.1 p.2) 0
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
        abs_of_nonneg hmn0, abs_of_nonneg hGp0, abs_of_nonneg hw1, abs_of_nonneg hw2]
      calc min (spinTransDist p ^ 2) 1 * Gp p * spinWc a p.1 * spinWc a p.2
          ≤ 1 * Gp p * spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = Gp p * spinWc a p.1 * spinWc a p.2 := by ring
  have hdiff_eq : spinCalInt c Φ + spinPhiVac a Φ =
      (∫ p : ℝ × ℝ, (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) *
        Gm p * spinWc a p.1 * spinWc a p.2) -
      (∫ p : ℝ × ℝ, (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) *
        Gp p * spinWc a p.1 * spinWc a p.2) := by
    rw [hcal, hvac, ← sub_eq_add_neg, ← integral_sub hRc_int hG_signed_int,
      ← integral_sub hRc_m_int hRc_p_int]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    have hsplit : spinG a Φ p.1 p.2 = Gp p - Gm p := by
      dsimp [Gp, Gm]; rcases le_total (spinG a Φ p.1 p.2) 0 with h | h
      · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]; ring
      · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]; ring
    dsimp only; rw [hsplit]; ring
  have hpos_int_bd : c_σ * spinPosAngVar a Φ - C_rc / n ≤
      ∫ p : ℝ × ℝ, (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) *
        Gp p * spinWc a p.1 * spinWc a p.2 := by
    have hpt_le : ∀ p : ℝ × ℝ,
        c_σ * (min (spinTransDist p ^ 2) 1 * Gp p * spinWc a p.1 * spinWc a p.2) -
          (C_rc / n) * (Gp p * spinWc a p.1 * spinWc a p.2) ≤
        (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) * Gp p * spinWc a p.1 * spinWc a p.2 := by
      intro p
      have h1 := (hRc_bd hc40 p).1
      rw [← show spinLongDist p = (|p.1| + |p.2|) / 2 by unfold spinLongDist; ring] at h1
      change c_σ * min (spinTransDist p ^ 2) 1 - C_rc / n ≤
        1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) at h1
      have hcoef := mul_le_mul_of_nonneg_right h1
        (mul_nonneg (mul_nonneg (le_max_right (spinG a Φ p.1 p.2) 0) (spinWc_nonneg ha2.le p.1))
          (spinWc_nonneg ha2.le p.2))
      linarith
    have hlin : ∫ p : ℝ × ℝ, (c_σ * (min (spinTransDist p ^ 2) 1 * Gp p * spinWc a p.1 * spinWc a p.2) -
          (C_rc / n) * (Gp p * spinWc a p.1 * spinWc a p.2)) =
        c_σ * spinPosAngVar a Φ - (C_rc / n) * ∫ p : ℝ × ℝ, Gp p * spinWc a p.1 * spinWc a p.2 := by
      rw [integral_sub (hV_int.const_mul c_σ) (hGp_int.const_mul (C_rc / n)),
        integral_const_mul, integral_const_mul]; rfl
    have hint_le := integral_mono ((hV_int.const_mul c_σ).sub (hGp_int.const_mul (C_rc / n)))
      hRc_p_int hpt_le
    have hlin_le : c_σ * spinPosAngVar a Φ - (C_rc / n) * ∫ p : ℝ × ℝ, Gp p * spinWc a p.1 * spinWc a p.2 ≤
        ∫ p : ℝ × ℝ, (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) *
          Gp p * spinWc a p.1 * spinWc a p.2 :=
      hlin.symm.trans_le hint_le
    have hGp_le1 : ∫ p : ℝ × ℝ, Gp p * spinWc a p.1 * spinWc a p.2 ≤ 1 := by
      rw [← hM2, spinM2_eq_spinWc ha0 Φ]
      refine integral_mono hGp_int hG_int fun p => ?_
      have h1 : Gp p ≤ |spinG a Φ p.1 p.2| := max_le (le_abs_self _) (abs_nonneg _)
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      gcongr
    have hCr_nn : 0 ≤ C_rc / n := div_nonneg hCrc_pos.le hn_pos.le
    nlinarith
  let δ := K_2 * δ_n
  let E_far : Set (ℝ × ℝ) := {q | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ spinLongDist q < xiStar - δ}
  let E_near : Set (ℝ × ℝ) := {q | (q.1 ^ 2 + q.2 ^ 2) / 2 < x₁ ^ 2 ∧ xiStar - δ ≤ spinLongDist q}
  have hm_far : MeasurableSet E_far := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) / 2) := by fun_prop
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet.inter
      (isOpen_lt h2 continuous_const).measurableSet
  have hm_near : MeasurableSet E_near := by
    have h1 : Continuous (fun q : ℝ × ℝ => (q.1 ^ 2 + q.2 ^ 2) / 2) := by fun_prop
    have h2 : Continuous spinLongDist := by unfold spinLongDist; fun_prop
    exact (isOpen_lt h1 continuous_const).measurableSet.inter
      (isClosed_le continuous_const h2).measurableSet
  have hGm_supp : ∀ p : ℝ × ℝ, p ∉ E_far ∪ E_near → Gm p = 0 := by
    intro p hp
    have hge : x₁ ^ 2 ≤ (p.1 ^ 2 + p.2 ^ 2) / 2 := by
      by_contra hlt; push_neg at hlt
      rcases lt_or_ge (spinLongDist p) (xiStar - δ) with hL | hL
      · exact hp (Or.inl ⟨hlt, hL⟩)
      · exact hp (Or.inr ⟨hlt, hL⟩)
    have hnonneg : 0 ≤ spinG a Φ p.1 p.2 := by
      have hxid : x₁ ^ 2 ≤ ((p.1 + p.2) / 2) ^ 2 + ((p.1 - p.2) / 2) ^ 2 := by linarith
      have h := hgap ((p.1 + p.2) / 2) ((p.1 - p.2) / 2) hxid
      rwa [show (p.1 + p.2) / 2 + (p.1 - p.2) / 2 = p.1 by ring,
        show (p.1 + p.2) / 2 - (p.1 - p.2) / 2 = p.2 by ring] at h
    dsimp [Gm]; exact max_eq_right (neg_nonpos.mpr hnonneg)
  let hm_fn : ℝ × ℝ → ℝ := fun p =>
    (1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2)) * Gm p * spinWc a p.1 * spinWc a p.2
  have hm_split : ∫ p : ℝ × ℝ, hm_fn p = (∫ p in E_far, hm_fn p) + ∫ p in E_near, hm_fn p := by
    have hd : Disjoint E_far E_near := Set.disjoint_left.mpr fun p h1 h2 => not_le_of_gt h1.2 h2.2
    have hfull : ∫ p : ℝ × ℝ, hm_fn p = ∫ p in E_far ∪ E_near, hm_fn p := by
      rw [← integral_indicator (hm_far.union hm_near)]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      by_cases hp : p ∈ E_far ∪ E_near
      · simp [Set.indicator_of_mem hp]
      · simp [Set.indicator_of_notMem hp, hm_fn, hGm_supp p hp]
    rw [hfull, ← integral_indicator (hm_far.union hm_near), ← integral_indicator hm_far,
      ← integral_indicator hm_near, ← integral_add (hRc_m_int.indicator hm_far) (hRc_m_int.indicator hm_near)]
    congr 1; ext p
    by_cases h1 : p ∈ E_far <;> by_cases h2 : p ∈ E_near
    · exact absurd h2 (Set.disjoint_left.mp hd h1)
    · rw [Set.indicator_of_mem (Or.inl h1), Set.indicator_of_mem h1,
        Set.indicator_of_notMem h2, add_zero]
    · rw [Set.indicator_of_mem (Or.inr h2), Set.indicator_of_notMem h1,
        Set.indicator_of_mem h2, zero_add]
    · rw [Set.indicator_of_notMem (by rintro (h | h) <;> contradiction),
        Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, add_zero]
  have hfar_bd : ∫ p in E_far, hm_fn p ≤ 12 * C_2 * n ^ (-2 : ℝ) := by
    have hpt : ∀ p : ℝ × ℝ, p ∈ E_far →
        hm_fn p ≤ 3 * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by
      intro p _
      have hrc1 := (abs_le.mp (hRc_bd hc40 p).2.2).1
      rw [← show spinLongDist p = (|p.1| + |p.2|) / 2 by unfold spinLongDist; ring] at hrc1
      have h1 : 1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) ≤ 3 := by
        linarith [hrc1, hCrc_n]
      have hGm_nn : 0 ≤ Gm p := le_max_right _ _
      have hGm_le : Gm p ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      calc hm_fn p
          ≤ 3 * Gm p * spinWc a p.1 * spinWc a p.2 := by dsimp [hm_fn]; gcongr
        _ ≤ 3 * |spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2 := by gcongr
        _ = 3 * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) := by ring
    have hint1 : ∫ p in E_far, hm_fn p ≤
        ∫ p in E_far, 3 * (|spinG a Φ p.1 p.2| * spinWc a p.1 * spinWc a p.2) :=
      setIntegral_mono_on hRc_m_int.integrableOn (hG_int.const_mul 3).integrableOn hm_far hpt
    rw [integral_const_mul] at hint1
    have h21_bd : ∫ q in E_far, |spinG a Φ q.1 q.2| * spinWc a q.1 * spinWc a q.2 ≤
        4 * C_2 * n ^ (-2 : ℝ) := by
      simpa [E_far, δ, δ_n, a, n, mul_assoc] using h21_all hc02' hx10 hx1_ub' hΦ hM2
    linarith
  have hnear_bd : ∫ p in E_near, hm_fn p ≤ C_near * δ_n := by
    have hpt : ∀ p : ℝ × ℝ, p ∈ E_near →
        hm_fn p ≤ (C_near * δ_n) * (Gm p * spinWc a p.1 * spinWc a p.2) := by
      intro p hp
      have h1 := (abs_le.mp (hnear hc0n' hx10 hx1_ub' p hp.1 hp.2)).1
      have hle : 1 - spinRc a (spinLongDist p) ((|p.1| - |p.2|) / 2) ≤ C_near * δ_n := by linarith
      have hGm_nn : 0 ≤ Gm p := le_max_right _ _
      have hw1 := spinWc_nonneg ha2.le p.1
      have hw2 := spinWc_nonneg ha2.le p.2
      calc hm_fn p
          ≤ (C_near * δ_n) * Gm p * spinWc a p.1 * spinWc a p.2 := by
            dsimp [hm_fn]; gcongr
        _ = (C_near * δ_n) * (Gm p * spinWc a p.1 * spinWc a p.2) := by ring
    have hint1 : ∫ p in E_near, hm_fn p ≤
        ∫ p in E_near, (C_near * δ_n) * (Gm p * spinWc a p.1 * spinWc a p.2) :=
      setIntegral_mono_on hRc_m_int.integrableOn (hGm_int.const_mul _).integrableOn hm_near hpt
    rw [integral_const_mul] at hint1
    have hGm_le1 : ∫ p in E_near, Gm p * spinWc a p.1 * spinWc a p.2 ≤ 1 := by
      have h1 : ∫ p in E_near, Gm p * spinWc a p.1 * spinWc a p.2 ≤
          ∫ p : ℝ × ℝ, Gm p * spinWc a p.1 * spinWc a p.2 :=
        setIntegral_le_integral hGm_int (Eventually.of_forall fun p =>
          mul_nonneg (mul_nonneg (le_max_right _ _) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _))
      have h2 : ∫ p : ℝ × ℝ, Gm p * spinWc a p.1 * spinWc a p.2 ≤ 1 := by
        rw [← hM2, spinM2_eq_spinWc ha0 Φ]
        refine integral_mono hGm_int hG_int fun p => ?_
        have h3 : Gm p ≤ |spinG a Φ p.1 p.2| := max_le (neg_le_abs _) (abs_nonneg _)
        have hw1 := spinWc_nonneg ha2.le p.1
        have hw2 := spinWc_nonneg ha2.le p.2
        gcongr
      exact h1.trans h2
    have hCn_nn : 0 ≤ C_near * δ_n := mul_nonneg hCnear_pos.le hδn_nn
    nlinarith
  have hneg_bd : ∫ p : ℝ × ℝ, hm_fn p ≤ (12 * C_2 + C_near) * δ_n := by
    have h12 : 12 * C_2 * n ^ (-2 : ℝ) ≤ 12 * C_2 * δ_n :=
      mul_le_mul_of_nonneg_left hn2_le (by positivity)
    linarith [hm_split, hfar_bd, hnear_bd]
  have hCrc_bd : C_rc / n ≤ C_rc * δ_n := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv_le hCrc_pos.le
  have hmain : spinCalInt c Φ ≤ -spinPhiVac a Φ - c_σ * spinPosAngVar a Φ + C * δ_n := by
    dsimp [C]; linarith
  have hV_nn : 0 ≤ spinPosAngVar a Φ := by
    refine integral_nonneg fun p => ?_
    exact mul_nonneg (mul_nonneg (mul_nonneg (le_min (sq_nonneg _) zero_le_one)
      (le_max_right _ _)) (spinWc_nonneg ha2.le _)) (spinWc_nonneg ha2.le _)
  refine ⟨hmain, by nlinarith, fun hvac_lb => ?_⟩
  have hneg_vac : -spinPhiVac a Φ ≤ δ_n := by
    have h1 : -spinPhiVac a Φ ≤ (c - 1)⁻¹ := by linarith
    exact h1.trans (by dsimp [δ_n, n]; exact hinv_le)
  nlinarith

/-- info: 'FormalResearch.ModularBootstrap.Spin.spinS4_2_3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.ModularBootstrap.Spin.spinS4_2_3

end FormalResearch.ModularBootstrap.Spin

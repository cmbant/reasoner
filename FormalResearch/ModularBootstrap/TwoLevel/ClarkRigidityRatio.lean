module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityFamily

/-!
# Lemma R for the Clark windows (`virasoro_two_level.tex`, `gt:2.6`)

`win_ratio_bounds`: for `|u| ≤ R` there is `k₂` such that for `k₀ ≥ k₂` and `K ≥ k₀` (with `u ≠ a_k`, `k₀ < k ≤ K`)
`F_K(u)/ρ_K` is within a factor `4` of `F_{k₀}(u)/ρ_{k₀}`, where `ρ_K = w_2(K)` is `windowWeight α K 2` and `F_K` the
window of `clarkDatum α p q m K` (`K ≥ m`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

lemma windowWeight_two_succ (α : ℝ) {K : ℕ} (hK : 2 ≤ K) :
    windowWeight α (K + 1) 2 * (clarkNode α 2 - airyZero (K + 1)) ^ 2 =
      windowWeight α K 2 * (clarkNode α 2 - clarkNode α (K + 1)) ^ 2 := by
  unfold windowWeight
  simp only [true_or, ↓reduceIte]
  rw [windowDr_succ, Finset.prod_Icc_succ_top (by omega)]
  have h1 : windowDr K (clarkNode α 2) ≠ 0 := windowDr_node_ne α K (by norm_num)
  have h2 : clarkNode α 2 - airyZero (K + 1) ≠ 0 :=
    sub_ne_zero.mpr (clarkNode_ne_airyZero α (by norm_num) (by omega))
  have h3 : cotC α ^ 2 - clarkNode α 2 ≠ 0 := (cot_sq_sub_pos α (n := 2) (by norm_num)).ne'
  field_simp

lemma ratio_alg {W1 W0 ρ1 ρ0 u z z2 a : ℝ} (hρ0 : ρ0 ≠ 0) (ha : u - a ≠ 0)
    (hza : z2 - a ≠ 0) (hzz : z2 - z ≠ 0) (hw : W1 * (u - a) ^ 2 = W0 * (u - z) ^ 2)
    (hr : ρ1 * (z2 - a) ^ 2 = ρ0 * (z2 - z) ^ 2) :
    W1 / ρ1 = (W0 / ρ0) * (((-z - -u) * (-a - -z2)) / ((-a - -u) * (-z - -z2))) ^ 2 := by
  have h1 : W1 = W0 * (u - z) ^ 2 / (u - a) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 ha)]; exact hw
  have h2 : ρ1 = ρ0 * (z2 - z) ^ 2 / (z2 - a) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hza)]; exact hr
  have h3 : (-z - -u) = u - z := by ring
  have h4 : (-a - -z2) = z2 - a := by ring
  have h5 : (-a - -u) = u - a := by ring
  have h6 : (-z - -z2) = z2 - z := by ring
  rw [h3, h4, h5, h6, h1, h2]
  field_simp

lemma ratio_step (α p q : ℝ) (m : ℕ) {K : ℕ} (hK : max m 3 ≤ K) {u : ℝ} (hu : u ≠ airyZero (K + 1)) :
    (clarkDatum α p q m (K + 1)).win u / windowWeight α (K + 1) 2 =
      ((clarkDatum α p q m K).win u / windowWeight α K 2) *
        ratioFac (fun k => -airyZero k) (fun k => -clarkNode α k) (-u) (-clarkNode α 2) (K + 1) ^ 2 := by
  have hK3 : 3 ≤ K := (le_max_right _ _).trans hK
  have hmK : m ≤ K := (le_max_left _ _).trans hK
  have hsite : (clarkDatum α p q m (K + 1)).s (K + 1) = clarkNode α (K + 1) :=
    clarkDatum_s_of_ne α p q (by omega)
  have hw0 := IdealDatum.win_succ (clarkDatum α p q m K) (clarkDatum α p q m (K + 1)) rfl rfl rfl
    (fun k _ => rfl) (show 2 ≤ K by omega) u
  have hw : (clarkDatum α p q m (K + 1)).win u * (u - airyZero (K + 1)) ^ 2 =
      (clarkDatum α p q m K).win u * (u - clarkNode α (K + 1)) ^ 2 := by
    rw [← hsite]; exact hw0
  have hw2 := windowWeight_two_succ α (K := K) (by omega)
  have hρK : 0 < windowWeight α K 2 := windowWeight_pos α hK3 (Or.inl rfl)
  have hρK1 : 0 < windowWeight α (K + 1) 2 := windowWeight_pos α (by omega) (Or.inl rfl)
  have hua : u - airyZero (K + 1) ≠ 0 := sub_ne_zero.mpr hu
  have hza : clarkNode α 2 - airyZero (K + 1) ≠ 0 :=
    sub_ne_zero.mpr (clarkNode_ne_airyZero α (by norm_num) (by omega))
  have hzz : clarkNode α 2 - clarkNode α (K + 1) ≠ 0 :=
    sub_ne_zero.mpr (clarkNode_lt_of_lt (n := 2) (m := K + 1) (by norm_num) (by omega) α).ne'
  have := ratio_alg hρK.ne' hua hza hzz hw hw2
  rw [this]
  unfold ratioFac
  rfl

lemma ratio_tele (α p q : ℝ) (m : ℕ) {k₀ : ℕ} (hk₀ : max m 3 ≤ k₀) {u : ℝ} :
    ∀ K, k₀ ≤ K → (∀ k ∈ Finset.Ioc k₀ K, u ≠ airyZero k) →
      (clarkDatum α p q m K).win u / windowWeight α K 2 =
        ((clarkDatum α p q m k₀).win u / windowWeight α k₀ 2) *
          ∏ k ∈ Finset.Ioc k₀ K,
            ratioFac (fun k => -airyZero k) (fun k => -clarkNode α k) (-u) (-clarkNode α 2) k ^ 2 := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => intro _; simp
  | succ K hK ih =>
    intro hu
    rw [Finset.prod_Ioc_succ_top hK, ← mul_assoc,
      ← ih (fun k hk => hu k (Finset.Ioc_subset_Ioc_right (Nat.le_succ K) hk)),
      ratio_step α p q m (hk₀.trans hK) (hu (K + 1) (Finset.mem_Ioc.2 ⟨by omega, le_rfl⟩))]

/-- **Lemma R for the windows**: `F_K(u)/ρ_K` is within a factor `4` of `F_{k₀}(u)/ρ_{k₀}`, uniformly for `|u| ≤ R`. -/
theorem win_ratio_bounds (α p q : ℝ) (m : ℕ) {k0 : ℕ}
    (h : NodeHyp (fun k => -airyZero k) (fun k => -clarkNode α k) k0) (R : ℝ) :
    ∃ k₂ : ℕ, max m 3 ≤ k₂ ∧ ∀ k₀, k₂ ≤ k₀ → ∀ K, k₀ ≤ K → ∀ u : ℝ, |u| ≤ R →
      (∀ k ∈ Finset.Ioc k₀ K, u ≠ airyZero k) → 0 ≤ (clarkDatum α p q m k₀).win u →
      (1 / 4) * ((clarkDatum α p q m k₀).win u / windowWeight α k₀ 2) ≤
          (clarkDatum α p q m K).win u / windowWeight α K 2 ∧
        (clarkDatum α p q m K).win u / windowWeight α K 2 ≤
          4 * ((clarkDatum α p q m k₀).win u / windowWeight α k₀ 2) := by
  obtain ⟨k₂', hk₂', hprod⟩ := h.ratioFac_prod_uniform (max R |clarkNode α 2|)
  refine ⟨max k₂' (max m 3), le_max_right _ _, fun k₀ hk₀ K hK u hu hne hw => ?_⟩
  have hk₀' : max m 3 ≤ k₀ := (le_max_right _ _).trans hk₀
  have hρ : 0 < windowWeight α k₀ 2 := windowWeight_pos α ((le_max_right _ _).trans hk₀') (Or.inl rfl)
  obtain ⟨hlo, hhi⟩ := hprod (-u) (-clarkNode α 2) (by rw [abs_neg]; exact hu.trans (le_max_left _ _))
    (by rw [abs_neg]; exact le_max_right _ _) k₀ ((le_max_left _ _).trans hk₀) K hK
  rw [ratio_tele α p q m hk₀' K hK hne, Finset.prod_pow]
  set x := (clarkDatum α p q m k₀).win u / windowWeight α k₀ 2 with hx
  have hx0 : 0 ≤ x := div_nonneg hw hρ.le
  set P := ∏ k ∈ Finset.Ioc k₀ K,
    ratioFac (fun k => -airyZero k) (fun k => -clarkNode α k) (-u) (-clarkNode α 2) k with hP
  constructor
  · nlinarith [mul_nonneg hx0 (sq_nonneg (P - 1 / 2)), mul_nonneg hx0 (sub_nonneg.2 hlo)]
  · nlinarith [mul_nonneg hx0 (sub_nonneg.2 hhi), mul_nonneg hx0 (sub_nonneg.2 hlo)]

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.win_ratio_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms win_ratio_bounds

end FormalResearch.ModularBootstrap.TwoLevel

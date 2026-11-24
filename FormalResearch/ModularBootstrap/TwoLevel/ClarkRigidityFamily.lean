module

public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityData
public import FormalResearch.ModularBootstrap.TwoLevel.ClarkRigidityProducts

/-!
# The Clark families of ideal windows (`virasoro_two_level.tex`, `gt:2.6`)

`clarkDatum α p q m K` has zeros `p, q`, double zeros at the Clark nodes `z_k` (`3 ≤ k ≤ K`), except at `k = m`, where
the site is the Airy zero `a_m` (an ideal pair).  Its window satisfies the splitting identity (`win_succ`)
`F_{K+1}(u) (u - a_{K+1})² = F_K(u)(u - z_{K+1})²` for `K ≥ m`, and the weight `ρ_K = w_2(K)` of `WindowOptimum`
satisfies the same recursion at `u = z_2`.  Hence (`ratio_tele`, `win_ratio_bounds`) for `|u| ≤ R` and `K ≥ k₀ ≥ k₂(R)`,
`F_K(u)/ρ_K` is within a factor `4` of `F_{k₀}(u)/ρ_{k₀}`, uniformly in `u` and `K` (Lemma R, `ratioFac_prod_uniform`).

All results are proved unconditionally.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.TwoLevel

open FormalResearch.Special FormalResearch.SignUncertainty
open FormalResearch.ModularBootstrap.Upper.Rigidity

namespace IdealDatum

/-- The splitting identity: adding the site `s_{K+1}` to a datum. -/
lemma win_succ (δ δ' : IdealDatum) (hp : δ'.p = δ.p) (hq : δ'.q = δ.q) (hK : δ'.K = δ.K + 1)
    (hs : ∀ k ∈ Finset.Icc 3 δ.K, δ'.s k = δ.s k) (hK3 : 2 ≤ δ.K) (x : ℝ) :
    δ'.win x * (x - airyZero (δ.K + 1)) ^ 2 = δ.win x * (x - δ'.s (δ.K + 1)) ^ 2 := by
  have hNr : ∀ y, δ'.Nr y = δ.Nr y * (y - δ'.s (δ.K + 1)) ^ 2 := by
    intro y
    unfold Nr
    rw [hp, hq, hK, Finset.prod_Icc_succ_top (by omega)]
    have : ∏ k ∈ Finset.Icc 3 δ.K, (y - δ'.s k) ^ 2 = ∏ k ∈ Finset.Icc 3 δ.K, (y - δ.s k) ^ 2 :=
      Finset.prod_congr rfl fun k hk => by rw [hs k hk]
    rw [this]; ring
  have hdense : Dense {y : ℝ | windowDr δ.K y ≠ 0} := by
    have h1 : Dense ((Set.univ : Set ℝ) \ (airyZero '' (Finset.Icc 1 δ.K : Set ℕ))) :=
      dense_univ.sdiff_finite ((Finset.Icc 1 δ.K).finite_toSet.image _)
    refine h1.mono fun y hy => ?_
    simp only [Set.mem_sdiff, mem_univ, true_and, mem_image, not_exists, not_and] at hy
    show windowDr δ.K y ≠ 0
    intro h0
    obtain ⟨j, hj, hjy⟩ := (δ.windowDr_eq_zero_iff).1 h0
    exact hy j (by simpa using hj) hjy.symm
  have hc1 : Continuous fun y => δ'.win y * (y - airyZero (δ.K + 1)) ^ 2 :=
    δ'.continuous_win.mul (by fun_prop)
  have hc2 : Continuous fun y => δ.win y * (y - δ'.s (δ.K + 1)) ^ 2 :=
    δ.continuous_win.mul (by fun_prop)
  have := Continuous.ext_on hdense hc1 hc2 (fun y hy => by
    have hy' : windowDr δ.K y ≠ 0 := hy
    have h' := δ'.win_spec y
    have h := δ.win_spec y
    rw [hK, windowDr_succ, hNr] at h'
    apply mul_left_cancel₀ (pow_ne_zero 2 hy')
    linear_combination h' - (y - δ'.s (δ.K + 1)) ^ 2 * h)
  exact congrFun this x

end IdealDatum

/-- The datum with zeros `p, q`, sites `z_k` (`3 ≤ k ≤ K`) except the Airy zero `a_m` at `k = m`. -/
noncomputable def clarkDatum (α p q : ℝ) (m K : ℕ) : IdealDatum :=
  ⟨p, q, K, fun k => if k = m then airyZero k else clarkNode α k⟩

lemma clarkDatum_s_of_ne (α p q : ℝ) {m K k : ℕ} (hk : k ≠ m) :
    (clarkDatum α p q m K).s k = clarkNode α k := by
  simp [clarkDatum, hk]

lemma clarkDatum_s_self (α p q : ℝ) (m K : ℕ) : (clarkDatum α p q m K).s m = airyZero m := by
  simp [clarkDatum]

lemma clarkDatum_adm (α : ℝ) {p q : ℝ} {m K : ℕ} (hqp : q < p) (hq : q < 0) (hK : 2 ≤ K)
    (hm : m = 0 ∨ (3 ≤ m ∧ m ≤ K)) : (clarkDatum α p q m K).Adm := by
  have hmk : ∀ k, 3 ≤ k → k ≤ K → k ≠ m ∨ (3 ≤ m ∧ m ≤ K) := by
    intro k hk3 hkK
    by_cases h : k = m
    · subst h; exact Or.inr ⟨hk3, hkK⟩
    · exact Or.inl h
  refine ⟨hqp, hq, hK, ?_, ?_, ?_⟩
  · intro k hk3 hkK
    by_cases h : k = m
    · rw [h, clarkDatum_s_self]; exact airyZero_neg m
    · rw [clarkDatum_s_of_ne α p q h]; exact clarkNode_neg_of_two_le α (by omega)
  · intro j k hj3 hjK hk3 hkK hjk
    by_contra hne
    by_cases hjm : j = m <;> by_cases hkm : k = m
    · exact hne (hjm.trans hkm.symm)
    · rw [hjm, clarkDatum_s_self, clarkDatum_s_of_ne α p q hkm] at hjk
      subst hjm
      exact clarkNode_ne_airyZero α (by omega) (by omega) hjk.symm
    · rw [hkm, clarkDatum_s_self, clarkDatum_s_of_ne α p q hjm] at hjk
      subst hkm
      exact clarkNode_ne_airyZero α (by omega) (by omega) hjk
    · rw [clarkDatum_s_of_ne α p q hjm, clarkDatum_s_of_ne α p q hkm] at hjk
      rcases lt_or_gt_of_ne hne with hl | hl
      · have := clarkNode_lt_of_lt (n := j) (m := k) (by omega) hl α; linarith
      · have := clarkNode_lt_of_lt (n := k) (m := j) (by omega) hl α; linarith
  · intro k hk3 hkK j hj hkj
    by_cases h : k = m
    · rw [h, clarkDatum_s_self] at hkj
      have := airyZero_inj (by omega) (by omega) hkj
      omega
    · rw [clarkDatum_s_of_ne α p q h] at hkj
      exact clarkNode_ne_airyZero α (by omega) (by omega) hkj

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.IdealDatum.win_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IdealDatum.win_succ

/-- info: 'FormalResearch.ModularBootstrap.TwoLevel.clarkDatum_adm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms clarkDatum_adm

end FormalResearch.ModularBootstrap.TwoLevel

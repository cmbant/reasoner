module

public import FormalResearch.SignUncertainty.ShellGapLaplace

/-!
# Mass transport for the limit profile (`thm:ce-shell-gap`)

`mass_transport`: let `Φ_k → Q` locally uniformly, `∫ Φ_k = 0`, `∫ |Φ_k| = 1`, `Φ_k ≥ 0` on every fixed
half line `u ≤ a < u_*` for large `k`, and with uniformly small absolute mass on `u > b` for large `b`.
Then `‖Q‖₁ ≤ 1`, `∫ Q ≤ 0` and `∫_{u_*}^∞ Q_- ≥ 1/2`.
(Here `Φ_k = 2 Ψ_{q_k}/M[2 q_k]`, whose negative part lives below the threshold `T_k`, i.e. at `u > u_* - o(1)`.)
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

lemma integral_split3 {f : ℝ → ℝ} (hf : Integrable f) {a b : ℝ} (hab : a ≤ b) :
    ∫ u, f u = (∫ u in Iic a, f u) + (∫ u in Icc a b, f u) + ∫ u in Ioi b, f u := by
  have h1 := integral_add_compl (μ := volume) (measurableSet_Iic (a := a)) hf
  rw [compl_Iic] at h1
  have h2 : ∫ u in Ioi a, f u = (∫ u in Ioc a b, f u) + ∫ u in Ioi b, f u := by
    rw [← Ioc_union_Ioi_eq_Ioi hab]
    refine setIntegral_union ?_ measurableSet_Ioi hf.integrableOn hf.integrableOn
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx')
  rw [integral_Icc_eq_integral_Ioc, ← h1, h2]
  ring

lemma integral_le_of_Icc {f : ℝ → ℝ} (hf : Integrable f) {C : ℝ}
    (h : ∀ᶠ n : ℕ in atTop, ∫ u in Icc (-(n : ℝ)) n, f u ≤ C) : ∫ u, f u ≤ C := by
  have hmono : Monotone (fun n : ℕ => Icc (-(n : ℝ)) n) := fun m n hmn =>
    Icc_subset_Icc (neg_le_neg (by exact_mod_cast hmn)) (by exact_mod_cast hmn)
  have hU : (⋃ n : ℕ, Icc (-(n : ℝ)) n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact mem_iUnion.2 ⟨n, abs_le.mp hn⟩
  have ht := tendsto_setIntegral_of_monotone (μ := volume) (f := f)
    (fun n => measurableSet_Icc) hmono (by rw [hU]; exact hf.integrableOn)
  rw [hU, Measure.restrict_univ] at ht
  exact le_of_tendsto ht h

lemma tendstoUniformlyOn_lip {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ} {s : Set ℝ}
    (h : TendstoUniformlyOn F f atTop s) {φ : ℝ → ℝ} (hφ : ∀ x y, |φ x - φ y| ≤ |x - y|) :
    TendstoUniformlyOn (fun k x => φ (F k x)) (fun x => φ (f x)) atTop s := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with k hk x hx
  have h1 := hk x hx
  rw [Real.dist_eq] at h1 ⊢
  exact lt_of_le_of_lt (hφ _ _) h1

lemma abs_lip : ∀ x y : ℝ, abs (abs x - abs y) ≤ abs (x - y) := fun x y =>
  abs_abs_sub_abs_le_abs_sub x y

lemma negpart_lip : ∀ x y : ℝ, |max (-x) 0 - max (-y) 0| ≤ |x - y| := fun x y => by
  have := abs_max_sub_max_le_abs (-x) (-y) 0
  rwa [show -x - -y = -(x - y) by ring, abs_neg] at this

theorem mass_transport {Φ : ℕ → ℝ → ℝ} {Q : ℝ → ℝ} {ustar : ℝ}
    (hQc : Continuous Q) (hQi : Integrable Q) (hΦi : ∀ k, Integrable (Φ k))
    (hloc : TendstoLocallyUniformlyOn Φ Q atTop univ)
    (hzero : ∀ k, ∫ u, Φ k u = 0) (habs : ∀ k, ∫ u, |Φ k u| = 1)
    (hleft : ∀ a < ustar, ∀ᶠ k in atTop, ∀ u ≤ a, 0 ≤ Φ k u)
    (htail : ∀ δ > 0, ∃ b₀ : ℝ, ∀ b ≥ b₀, ∀ᶠ k in atTop, ∫ u in Ioi b, |Φ k u| ≤ δ) :
    (∫ u, |Q u| ≤ 1) ∧ (∫ u, Q u ≤ 0) ∧ (1 / 2 ≤ ∫ u in Ioi ustar, max (-Q u) 0) := by
  have hU : ∀ a b : ℝ, TendstoUniformlyOn Φ Q atTop (Icc a b) := fun a b =>
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
      (hloc.mono (subset_univ _))
  have hQabs : Integrable (fun u => |Q u|) := hQi.abs
  have hQneg : Integrable (fun u => max (-Q u) 0) := hQi.neg.pos_part
  -- (A) the L¹ bound
  have hA : ∫ u, |Q u| ≤ 1 := by
    refine integral_le_of_Icc hQabs (Eventually.of_forall fun n => ?_)
    have hlim := setIntegral_Icc_tendsto_unif (g := fun k u => |Φ k u|) (G := fun u => |Q u|)
      (a := -(n : ℝ)) (b := n) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
      (tendstoUniformlyOn_lip (hU _ _) abs_lip)
      (Eventually.of_forall fun k => (hΦi k).abs.integrableOn) hQabs.integrableOn
    refine le_of_tendsto hlim (Eventually.of_forall fun k => ?_)
    rw [← habs k]
    exact setIntegral_le_integral (hΦi k).abs (Eventually.of_forall fun u => abs_nonneg _)
  refine ⟨hA, ?_, ?_⟩
  · -- (B) ∫ Q ≤ 0
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨b₀, hb₀⟩ := htail δ hδ
    suffices h : ∫ u, Q u ≤ δ by linarith
    refine integral_le_of_Icc hQi ?_
    have hn1 : ∀ᶠ n : ℕ in atTop, b₀ ≤ (n : ℝ) ∧ -(n : ℝ) < ustar := by
      obtain ⟨N1, hN1⟩ := exists_nat_ge b₀
      obtain ⟨N2, hN2⟩ := exists_nat_gt (-ustar)
      filter_upwards [eventually_ge_atTop (max N1 N2)] with n hn
      have h1 : (N1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) hn
      have h2 : (N2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
      exact ⟨le_trans hN1 h1, by linarith⟩
    filter_upwards [hn1] with n hn
    obtain ⟨hnb, hna⟩ := hn
    have hab : -(n : ℝ) ≤ n := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have hlim := setIntegral_Icc_tendsto_unif (g := Φ) (G := Q) hab (hU _ _)
      (Eventually.of_forall fun k => (hΦi k).integrableOn) hQi.integrableOn
    refine le_of_tendsto hlim ?_
    filter_upwards [hleft _ hna, hb₀ _ hnb] with k hk1 hk2
    have hs := integral_split3 (hΦi k) hab
    rw [hzero k] at hs
    have h1 : 0 ≤ ∫ u in Iic (-(n : ℝ)), Φ k u :=
      setIntegral_nonneg measurableSet_Iic fun u hu => hk1 u hu
    have h2 : ∫ u in Ioi (n : ℝ), -|Φ k u| ≤ ∫ u in Ioi (n : ℝ), Φ k u :=
      setIntegral_mono_on (hΦi k).abs.neg.integrableOn (hΦi k).integrableOn measurableSet_Ioi
        fun u _ => by linarith [neg_abs_le (Φ k u)]
    rw [integral_neg] at h2
    linarith
  · -- (C) negative mass
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
      (f := Q) (s := Icc (ustar - 1) ustar) hQc.continuousOn
    have hQC : ∀ u ∈ Icc (ustar - 1) ustar, max (-Q u) 0 ≤ |C| := by
      intro u hu
      have h1 := hC u hu
      rw [Real.norm_eq_abs] at h1
      refine max_le ?_ (abs_nonneg _)
      calc -Q u ≤ |Q u| := neg_le_abs _
        _ ≤ C := h1
        _ ≤ |C| := le_abs_self _
    have key : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ δ : ℝ, 0 < δ →
        1 / 2 ≤ s * |C| + (∫ u in Ioi ustar, max (-Q u) 0) + δ := by
      intro s hs0 hs1 δ hδ
      obtain ⟨b₀, hb₀⟩ := htail δ hδ
      set a : ℝ := ustar - s with ha
      set b : ℝ := max b₀ ustar with hb
      have hab : a ≤ b := by
        have : ustar ≤ b := le_max_right _ _
        linarith
      have hlim := setIntegral_Icc_tendsto_unif (g := fun k u => max (-Φ k u) 0)
        (G := fun u => max (-Q u) 0) hab (tendstoUniformlyOn_lip (hU a b) negpart_lip)
        (Eventually.of_forall fun k => (hΦi k).neg.pos_part.integrableOn) hQneg.integrableOn
      have hge : 1 / 2 - δ ≤ ∫ u in Icc a b, max (-Q u) 0 := by
        refine ge_of_tendsto hlim ?_
        filter_upwards [hleft a (by linarith), hb₀ b (le_max_left _ _)] with k hk1 hk2
        have hψ : ∫ u, max (-Φ k u) 0 = 1 / 2 := by
          have e : (fun u => max (-Φ k u) 0) = fun u => (|Φ k u| - Φ k u) / 2 := by
            funext u
            rcases le_total 0 (Φ k u) with h | h
            · rw [abs_of_nonneg h, max_eq_right (by linarith)]; ring
            · rw [abs_of_nonpos h, max_eq_left (by linarith)]; ring
          rw [e, integral_div, integral_sub (hΦi k).abs (hΦi k), habs k, hzero k]
          norm_num
        have hs3 := integral_split3 (f := fun u => max (-Φ k u) 0) (hΦi k).neg.pos_part hab
        rw [hψ] at hs3
        have h1 : ∫ u in Iic a, max (-Φ k u) 0 = 0 := by
          rw [setIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ℝ))
            (fun u hu => max_eq_right (by linarith [hk1 u hu]))]
          simp
        have h3 : ∫ u in Ioi b, max (-Φ k u) 0 ≤ ∫ u in Ioi b, |Φ k u| :=
          setIntegral_mono_on (hΦi k).neg.pos_part.integrableOn (hΦi k).abs.integrableOn
            measurableSet_Ioi fun u _ => max_le (neg_le_abs _) (abs_nonneg _)
        linarith
      have hsub : Icc a b ⊆ Icc a ustar ∪ Ioi ustar := by
        intro x hx
        by_cases h : x ≤ ustar
        · exact Or.inl ⟨hx.1, h⟩
        · exact Or.inr (not_le.mp h)
      have hnn : 0 ≤ᵐ[volume.restrict (Icc a ustar ∪ Ioi ustar)] fun u => max (-Q u) 0 :=
        Eventually.of_forall fun u => le_max_right _ _
      have hdisj : Disjoint (Icc a ustar) (Ioi ustar) := by
        rw [Set.disjoint_left]
        intro x hx hx'
        exact absurd hx.2 (not_le.2 hx')
      have hup : ∫ u in Icc a b, max (-Q u) 0 ≤
          (∫ u in Icc a ustar, max (-Q u) 0) + ∫ u in Ioi ustar, max (-Q u) 0 := by
        rw [← setIntegral_union hdisj measurableSet_Ioi hQneg.integrableOn hQneg.integrableOn]
        exact setIntegral_mono_set hQneg.integrableOn hnn hsub.eventuallySubset
      have hmid : ∫ u in Icc a ustar, max (-Q u) 0 ≤ s * |C| := by
        have h1 : ∫ u in Icc a ustar, max (-Q u) 0 ≤ ∫ _u in Icc a ustar, |C| :=
          setIntegral_mono_on hQneg.integrableOn continuousOn_const.integrableOn_Icc
            measurableSet_Icc fun u hu => hQC u ⟨by linarith [hu.1], hu.2⟩
        refine h1.trans (le_of_eq ?_)
        rw [setIntegral_const, smul_eq_mul, Measure.real_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith)]
        rw [ha]; ring
      linarith
    by_contra hlt
    rw [not_le] at hlt
    set g : ℝ := 1 / 2 - ∫ u in Ioi ustar, max (-Q u) 0 with hg
    have hg0 : 0 < g := by linarith
    have hC1 : 0 < 4 * (|C| + 1) := by positivity
    set s : ℝ := min 1 (g / (4 * (|C| + 1))) with hs
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hs2 : s ≤ g / (4 * (|C| + 1)) := min_le_right _ _
    have k1 := key s hs0 hs1 (g / 4) (by positivity)
    have : s * |C| ≤ g / 4 := by
      calc s * |C| ≤ g / (4 * (|C| + 1)) * |C| :=
            mul_le_mul_of_nonneg_right hs2 (abs_nonneg _)
        _ ≤ g / (4 * (|C| + 1)) * (|C| + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = g / 4 := by field_simp
    linarith

/-- info: 'FormalResearch.SignUncertainty.mass_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mass_transport

end FormalResearch.SignUncertainty

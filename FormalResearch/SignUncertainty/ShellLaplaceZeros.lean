module

public import FormalResearch.SignUncertainty.ShellLaplaceBase

/-!
# Airy–Laplace Positive Zero Multiplicity & `m = 3` Trichotomy (`ce_shells.tex` Corollary H.14b)

Source: `CFT/sign_uncertainty/paper/ce_shells.tex` (PR 240, commit `c3d8c90fe`).

Weighted Rolle multiplicity bound `≤ m - 1` (`laplace_zero_multiplicity_le`,
`laplace_zero_analyticOrder_le`), positivity near `0⁺` via `at47_block_integral`,
odd-`m` large-`y` positivity, and the `m = 3` trichotomy classification.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Metric Set
open scoped Real ENNReal Polynomial

namespace FormalResearch.SignUncertainty

open FormalResearch.Special
open FormalResearch.Analysis
open FormalResearch.Montel

/-! ### Section 4: Positive Zero Multiplicity, Near-Zero/Odd-`m` Sign, and `m = 3` Classification (`H.14b`) -/

private lemma rolle_shift_step {f : ℝ → ℝ} {t a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hf0a : f a = 0) (hf0b : f b = 0)
    (hfd : DifferentiableOn ℝ f (Ioo a b)) :
    ∃ c ∈ Ioo a b, deriv f c - t * f c = 0 := by
  let φ : ℝ → ℝ := fun y => Real.exp (-t * y) * f y
  have hφc : ContinuousOn φ (Icc a b) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hfc
  have hφab : φ a = φ b := by simp [φ, hf0a, hf0b]
  have hderiv : ∀ x ∈ Ioo a b,
      HasDerivAt φ (Real.exp (-t * x) * (deriv f x - t * f x)) x := by
    intro x hx
    have hdF : HasDerivAt f (deriv f x) x :=
      ((hfd x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
    have hdE : HasDerivAt (fun y => Real.exp (-t * y)) (-t * Real.exp (-t * x)) x := by
      simpa [mul_comm] using ((hasDerivAt_id x).const_mul (-t)).exp
    exact (hdE.mul hdF).congr_deriv (by ring)
  obtain ⟨c, hc, h0⟩ := exists_hasDerivAt_eq_zero hab hφc hφab hderiv
  exact ⟨c, hc, (mul_eq_zero.mp h0).resolve_left (Real.exp_pos _).ne'⟩

private lemma contDiffOn_shift {g : ℝ → ℝ} {t : ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Ioi 0)) :
    ∀ n : ℕ, ContDiffOn ℝ n (fun y => deriv g y - t * g y) (Ioi 0) := fun n =>
  ((hg (n + 1)).deriv_of_isOpen isOpen_Ioi le_rfl).sub (contDiffOn_const.mul (hg n))

private lemma iteratedDeriv_shift {g : ℝ → ℝ} {t z : ℝ} (hz : 0 < z)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Ioi 0)) (k : ℕ) :
    iteratedDeriv k (fun y => deriv g y - t * g y) z =
      iteratedDeriv (k + 1) g z - t * iteratedDeriv k g z := by
  have hdg : ContDiffAt ℝ k (deriv g) z :=
    ((hg (k + 1)).deriv_of_isOpen isOpen_Ioi le_rfl).contDiffAt (isOpen_Ioi.mem_nhds hz)
  have htg : ContDiffAt ℝ k (fun y => t * g y) z :=
    contDiffAt_const.mul ((hg k).contDiffAt (isOpen_Ioi.mem_nhds hz))
  change iteratedDeriv k (deriv g - fun y => t * g y) z = _
  rw [iteratedDeriv_sub hdg htg, ← iteratedDeriv_succ', iteratedDeriv_const_mul_field]

private lemma exists_inter_zeros {g : ℝ → ℝ} {t : ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Ioi 0)) :
    ∀ (zs : List ℝ), zs.Pairwise (· ≤ ·) → zs.Nodup →
      (∀ z ∈ zs, 0 < z ∧ g z = 0) →
      ∃ W : Finset ℝ,
        W.card = zs.length - 1 ∧
        (∀ w ∈ W, 0 < w ∧ deriv g w - t * g w = 0 ∧ w ∉ zs) ∧
        (∀ a0 : ℝ, (∀ z ∈ zs, a0 ≤ z) → ∀ w ∈ W, a0 < w)
  | [], _, _, _ => ⟨∅, by simp⟩
  | [_], _, _, _ => ⟨∅, by simp⟩
  | a :: b :: rest, hp, hnd, hz => by
    have hp_cons := List.pairwise_cons.mp hp
    have hnd_cons := List.nodup_cons.mp hnd
    have hab_le : a ≤ b := hp_cons.1 b (by simp)
    have hab_ne : a ≠ b := fun h => hnd_cons.1 (by simp [h])
    have hab : a < b := lt_of_le_of_ne hab_le hab_ne
    have ha0 : 0 < a := (hz a (by simp)).1
    have hga : g a = 0 := (hz a (by simp)).2
    have hgb : g b = 0 := (hz b (by simp)).2
    have hIcc : Icc a b ⊆ Ioi 0 := fun x hx => ha0.trans_le hx.1
    have hIoo : Ioo a b ⊆ Ioi 0 := fun x hx => ha0.trans hx.1
    obtain ⟨w, hw_mem, hw_eq⟩ := rolle_shift_step hab
      ((hg 1).continuousOn.mono hIcc) hga hgb (((hg 1).differentiableOn (by norm_num)).mono hIoo)
    obtain ⟨W', hW'card, hW'prop, hW'lb⟩ := exists_inter_zeros hg (b :: rest) hp_cons.2 hnd_cons.2
      (fun z hz' => hz z (by simp [hz']))
    have hb_lb : ∀ z ∈ b :: rest, b ≤ z := by
      intro z hz'
      rcases List.mem_cons.mp hz' with rfl | hz''
      · exact le_rfl
      · exact (List.pairwise_cons.mp hp_cons.2).1 z hz''
    have hw_not_W' : w ∉ W' := fun hw => absurd (hW'lb b hb_lb w hw) (not_lt.mpr hw_mem.2.le)
    refine ⟨insert w W', ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hw_not_W', hW'card]; simp
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · refine ⟨ha0.trans hw_mem.1, hw_eq, fun hmem => ?_⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact absurd hw_mem.1 (lt_irrefl _)
        · exact absurd (hb_lb x hmem') (not_le.mpr hw_mem.2)
      · obtain ⟨hx0, hxg, hx_not⟩ := hW'prop x hx'
        refine ⟨hx0, hxg, fun hmem => ?_⟩
        rcases List.mem_cons.mp hmem with rfl | hmem'
        · exact absurd (hW'lb b hb_lb x hx') (not_lt.mpr hab.le)
        · exact hx_not hmem'
    · intro a0 ha0_lb x hx
      have ha0_a : a0 ≤ a := ha0_lb a (by simp)
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact ha0_a.trans_lt hw_mem.1
      · exact (ha0_a.trans hab.le).trans_lt (hW'lb b hb_lb x hx')

private lemma weighted_rolle_step {g : ℝ → ℝ} {t : ℝ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n g (Ioi 0))
    (Z : Finset ℝ) (m : ℝ → ℕ)
    (hm : ∀ z ∈ Z, 0 < z ∧ 1 ≤ m z ∧ ∀ k < m z, iteratedDeriv k g z = 0) :
    ∃ (Z₁ : Finset ℝ) (m₁ : ℝ → ℕ),
      (∀ z ∈ Z₁, 0 < z ∧ 1 ≤ m₁ z ∧
        ∀ k < m₁ z, iteratedDeriv k (fun y => deriv g y - t * g y) z = 0) ∧
      (Z.Nonempty → ∑ z ∈ Z, m z ≤ (∑ z ∈ Z₁, m₁ z) + 1) := by
  let zs := Z.sort (· ≤ ·)
  obtain ⟨W, hWcard, hWprop, _⟩ := exists_inter_zeros (t := t) hg zs
    (Z.pairwise_sort (· ≤ ·)) (Z.sort_nodup (· ≤ ·)) fun z hz => by
      have hzZ : z ∈ Z := (Finset.mem_sort (· ≤ ·)).mp hz
      have hmz := hm z hzZ
      exact ⟨hmz.1, by simpa using hmz.2.2 0 hmz.2.1⟩
  let Z_stay := Z.filter (fun z => 2 ≤ m z)
  let m₁ : ℝ → ℕ := fun z => if z ∈ Z then m z - 1 else 1
  have hdisj : Disjoint Z_stay W := Finset.disjoint_left.mpr fun z hzZ hzW =>
    (hWprop z hzW).2.2 ((Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_filter.mp hzZ).1)
  refine ⟨Z_stay ∪ W, m₁, fun z hz => ?_, fun hZ => ?_⟩
  · rcases Finset.mem_union.mp hz with hzS | hzW
    · have hzZ := (Finset.mem_filter.mp hzS).1
      have hm2 := (Finset.mem_filter.mp hzS).2
      have hmz := hm z hzZ
      refine ⟨hmz.1, ?_, fun k hk => ?_⟩
      · dsimp [m₁]; rw [ite_eq_left_iff.mpr (fun h => absurd hzZ h)]; omega
      · dsimp [m₁] at hk; rw [ite_eq_left_iff.mpr (fun h => absurd hzZ h)] at hk
        rw [iteratedDeriv_shift hmz.1 hg k, hmz.2.2 (k + 1) (by omega),
          hmz.2.2 k (by omega), mul_zero, sub_zero]
    · have hW := hWprop z hzW
      have hz_notZ : z ∉ Z := fun h => hW.2.2 ((Finset.mem_sort (· ≤ ·)).mpr h)
      refine ⟨hW.1, ?_, fun k hk => ?_⟩
      · dsimp [m₁]; rw [ite_eq_right_iff.mpr (fun h => absurd h hz_notZ)]
      · dsimp [m₁] at hk; rw [ite_eq_right_iff.mpr (fun h => absurd h hz_notZ)] at hk
        have hk0 : k = 0 := by omega
        subst hk0; simpa using hW.2.1
  · rw [Finset.sum_union hdisj]
    have hsum1 : ∑ z ∈ Z_stay, m₁ z = ∑ z ∈ Z, (m z - 1) := by
      have hcongr : ∑ z ∈ Z_stay, m₁ z = ∑ z ∈ Z_stay, (m z - 1) :=
        Finset.sum_congr rfl fun z hz => by
          dsimp [m₁]; rw [ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_filter.mp hz).1 h)]
      rw [hcongr]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun z hzZ hz_not => ?_
      have h1 : m z = 1 := by
        have := (hm z hzZ).2.1
        by_contra hne
        exact hz_not (Finset.mem_filter.mpr ⟨hzZ, by omega⟩)
      simp [h1]
    have hsum2 : ∑ w ∈ W, m₁ w = W.card := by
      calc ∑ w ∈ W, m₁ w = ∑ _ ∈ W, 1 := Finset.sum_congr rfl fun w hw => by
            have hz_notZ : w ∉ Z := fun h => (hWprop w hw).2.2 ((Finset.mem_sort (· ≤ ·)).mpr h)
            dsimp [m₁]; rw [ite_eq_right_iff.mpr (fun h => absurd h hz_notZ)]
        _ = W.card := by simp
    have hsumZ : ∑ z ∈ Z, m z = (∑ z ∈ Z, (m z - 1)) + Z.card := by
      have hpt : ∀ z ∈ Z, m z = (m z - 1) + 1 := fun z hz => by have := (hm z hz).2.1; omega
      calc ∑ z ∈ Z, m z = ∑ z ∈ Z, ((m z - 1) + 1) := Finset.sum_congr rfl hpt
        _ = (∑ z ∈ Z, (m z - 1)) + Z.card := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    have hZc : 1 ≤ Z.card := Finset.Nonempty.card_pos hZ
    rw [hsum1, hsum2, hWcard, Finset.length_sort, hsumZ]
    omega

private lemma weighted_rolle_step_from_zero {f : ℝ → ℝ} {t : ℝ}
    (hf_cont : ContinuousOn f (Ici 0)) (hf0 : f 0 = 0)
    (hf : ∀ n : ℕ, ContDiffOn ℝ n f (Ioi 0))
    (Z : Finset ℝ) (hZ : Z.Nonempty) (m : ℝ → ℕ)
    (hm : ∀ z ∈ Z, 0 < z ∧ 1 ≤ m z ∧ ∀ k < m z, iteratedDeriv k f z = 0) :
    ∃ (Z₁ : Finset ℝ) (m₁ : ℝ → ℕ),
      (∀ z ∈ Z₁, 0 < z ∧ 1 ≤ m₁ z ∧
        ∀ k < m₁ z, iteratedDeriv k (fun y => deriv f y - t * f y) z = 0) ∧
      ∑ z ∈ Z, m z ≤ ∑ z ∈ Z₁, m₁ z := by
  let zs := Z.sort (· ≤ ·)
  obtain ⟨W, hWcard, hWprop, hWlb⟩ := exists_inter_zeros (t := t) hf zs
    (Z.pairwise_sort (· ≤ ·)) (Z.sort_nodup (· ≤ ·)) fun z hz => by
      have hzZ : z ∈ Z := (Finset.mem_sort (· ≤ ·)).mp hz
      have hmz := hm z hzZ
      exact ⟨hmz.1, by simpa using hmz.2.2 0 hmz.2.1⟩
  let z₀ := Z.min' hZ
  have hz₀Z : z₀ ∈ Z := Z.min'_mem hZ
  have hz₀_pos : 0 < z₀ := (hm z₀ hz₀Z).1
  have hfz₀ : f z₀ = 0 := by simpa using (hm z₀ hz₀Z).2.2 0 (hm z₀ hz₀Z).2.1
  obtain ⟨w₀, hw₀_mem, hw₀_eq⟩ := rolle_shift_step hz₀_pos
    (hf_cont.mono Icc_subset_Ici_self) hf0 hfz₀
    (((hf 1).differentiableOn (by norm_num)).mono Ioo_subset_Ioi_self)
  have hw₀_notZ : w₀ ∉ Z := fun h => absurd (Z.min'_le w₀ h) (not_le.mpr hw₀_mem.2)
  have hw₀_notW : w₀ ∉ W := fun h => by
    have hz₀_lb : ∀ z ∈ zs, z₀ ≤ z := fun z hz => Z.min'_le z ((Finset.mem_sort (· ≤ ·)).mp hz)
    exact absurd (hWlb z₀ hz₀_lb w₀ h) (not_lt.mpr hw₀_mem.2.le)
  let W₀ := insert w₀ W
  let Z_stay := Z.filter (fun z => 2 ≤ m z)
  let m₁ : ℝ → ℕ := fun z => if z ∈ Z then m z - 1 else 1
  have hdisj : Disjoint Z_stay W₀ := Finset.disjoint_left.mpr fun z hzS hzW => by
    have hzZ := (Finset.mem_filter.mp hzS).1
    rcases Finset.mem_insert.mp hzW with rfl | hzW'
    · exact hw₀_notZ hzZ
    · exact (hWprop z hzW').2.2 ((Finset.mem_sort (· ≤ ·)).mpr hzZ)
  refine ⟨Z_stay ∪ W₀, m₁, fun z hz => ?_, ?_⟩
  · rcases Finset.mem_union.mp hz with hzS | hzW
    · have hzZ := (Finset.mem_filter.mp hzS).1
      have hm2 := (Finset.mem_filter.mp hzS).2
      have hmz := hm z hzZ
      refine ⟨hmz.1, ?_, fun k hk => ?_⟩
      · dsimp [m₁]; rw [ite_eq_left_iff.mpr (fun h => absurd hzZ h)]; omega
      · dsimp [m₁] at hk; rw [ite_eq_left_iff.mpr (fun h => absurd hzZ h)] at hk
        rw [iteratedDeriv_shift hmz.1 hf k, hmz.2.2 (k + 1) (by omega),
          hmz.2.2 k (by omega), mul_zero, sub_zero]
    · rcases Finset.mem_insert.mp hzW with rfl | hzW'
      · refine ⟨hw₀_mem.1, ?_, fun k hk => ?_⟩
        · dsimp [m₁]; rw [ite_eq_right_iff.mpr (fun h => absurd h hw₀_notZ)]
        · dsimp [m₁] at hk; rw [ite_eq_right_iff.mpr (fun h => absurd h hw₀_notZ)] at hk
          have hk0 : k = 0 := by omega
          subst hk0; simpa using hw₀_eq
      · have hW := hWprop z hzW'
        have hz_notZ : z ∉ Z := fun h => hW.2.2 ((Finset.mem_sort (· ≤ ·)).mpr h)
        refine ⟨hW.1, ?_, fun k hk => ?_⟩
        · dsimp [m₁]; rw [ite_eq_right_iff.mpr (fun h => absurd h hz_notZ)]
        · dsimp [m₁] at hk; rw [ite_eq_right_iff.mpr (fun h => absurd h hz_notZ)] at hk
          have hk0 : k = 0 := by omega
          subst hk0; simpa using hW.2.1
  · rw [Finset.sum_union hdisj]
    have hsum1 : ∑ z ∈ Z_stay, m₁ z = ∑ z ∈ Z, (m z - 1) := by
      have hcongr : ∑ z ∈ Z_stay, m₁ z = ∑ z ∈ Z_stay, (m z - 1) :=
        Finset.sum_congr rfl fun z hz => by
          dsimp [m₁]; rw [ite_eq_left_iff.mpr (fun h => absurd (Finset.mem_filter.mp hz).1 h)]
      rw [hcongr]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun z hzZ hz_not => ?_
      have h1 : m z = 1 := by
        have := (hm z hzZ).2.1
        by_contra hne
        exact hz_not (Finset.mem_filter.mpr ⟨hzZ, by omega⟩)
      simp [h1]
    have hsum2 : ∑ w ∈ W₀, m₁ w = W₀.card := by
      calc ∑ w ∈ W₀, m₁ w = ∑ _ ∈ W₀, 1 := Finset.sum_congr rfl fun w hw => by
            have hz_notZ : w ∉ Z := by
              rcases Finset.mem_insert.mp hw with rfl | hw'
              · exact hw₀_notZ
              · exact fun h => (hWprop w hw').2.2 ((Finset.mem_sort (· ≤ ·)).mpr h)
            dsimp [m₁]; rw [ite_eq_right_iff.mpr (fun h => absurd h hz_notZ)]
        _ = W₀.card := by simp
    have hsumZ : ∑ z ∈ Z, m z = (∑ z ∈ Z, (m z - 1)) + Z.card := by
      have hpt : ∀ z ∈ Z, m z = (m z - 1) + 1 := fun z hz => by have := (hm z hz).2.1; omega
      calc ∑ z ∈ Z, m z = ∑ z ∈ Z, ((m z - 1) + 1) := Finset.sum_congr rfl hpt
        _ = (∑ z ∈ Z, (m z - 1)) + Z.card := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
    have hW₀c : W₀.card = Z.card := by
      have hZc : 1 ≤ Z.card := Finset.Nonempty.card_pos hZ
      rw [Finset.card_insert_of_notMem hw₀_notW, hWcard, Finset.length_sort]
      omega
    rw [hsum1, hsum2, hW₀c, hsumZ]

private lemma exists_zero_laplaceApply_of_gt :
    ∀ (L : List ℝ) (g : ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n g (Ioi 0)) →
      ∀ (Z : Finset ℝ) (m : ℝ → ℕ),
        (∀ z ∈ Z, 0 < z ∧ 1 ≤ m z ∧ ∀ k < m z, iteratedDeriv k g z = 0) →
        L.length < ∑ z ∈ Z, m z →
        ∃ y : ℝ, 0 < y ∧ laplaceApply L g y = 0
  | [], g, _, Z, m, hm, hgt => by
    have hZ : Z.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty] at hgt
      omega
    obtain ⟨z, hzZ⟩ := hZ
    have hmz := hm z hzZ
    refine ⟨z, hmz.1, ?_⟩
    change g z = 0
    simpa using hmz.2.2 0 hmz.2.1
  | t :: L, g, hg, Z, m, hm, hgt => by
    have hZ : Z.Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty] at hgt
      omega
    obtain ⟨Z₁, m₁, hm₁, hsum⟩ := weighted_rolle_step (t := t) hg Z m hm
    have hgt₁ : L.length < ∑ z ∈ Z₁, m₁ z := by simp at hgt; have := hsum hZ; omega
    obtain ⟨y, hy, hy0⟩ := exists_zero_laplaceApply_of_gt L (fun y => deriv g y - t * g y)
      (contDiffOn_shift hg) Z₁ m₁ hm₁ hgt₁
    exact ⟨y, hy, hy0⟩

/-- **Corollary H.14b (`thm:ce-laplace-zeros`, multiplicity bound via `iteratedDeriv`)**:
for any Hermite–Biehler configuration with `m = D.S.card` levels, the total multiplicity
of positive zeros of `shellLaplaceF D` is at most `m - 1`. -/
theorem laplace_zero_multiplicity_le (D : ShellHBData) (Z : Finset ℝ)
    (hZ : ∀ z ∈ Z, 0 < z) (mult : ℝ → ℕ)
    (hmult : ∀ z ∈ Z, ∀ k < mult z, iteratedDeriv k (shellLaplaceF D) z = 0) :
    ∑ z ∈ Z, mult z ≤ D.S.card - 1 := by
  let Z' := Z.filter (fun z => 0 < mult z)
  have hsum_eq : ∑ z ∈ Z, mult z = ∑ z ∈ Z', mult z := by
    symm; refine Finset.sum_subset (Finset.filter_subset _ _) fun z hzZ hz_not => ?_
    by_contra hne
    exact hz_not (Finset.mem_filter.mpr ⟨hzZ, Nat.pos_of_ne_zero hne⟩)
  rw [hsum_eq]
  by_cases hZ' : Z'.Nonempty
  · by_contra hgt
    push Not at hgt
    let L := D.S.toList
    have hL_nodup : L.Nodup := Finset.nodup_toList D.S
    have hL_len : L.length = D.S.card := Finset.length_toList D.S
    have hL_mem : ∀ t, t ∈ L ↔ t ∈ D.S := fun _ => Finset.mem_toList
    have hL_pos : 0 < L.length := by rw [hL_len]; exact Finset.Nonempty.card_pos D.S_nonempty
    cases hL : L with
    | nil => simp [hL] at hL_pos
    | cons t₁ L' =>
      have hmZ' : ∀ z ∈ Z', 0 < z ∧ 1 ≤ mult z ∧
          ∀ k < mult z, iteratedDeriv k (shellLaplaceF D) z = 0 := fun z hz =>
        ⟨hZ z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2,
          hmult z (Finset.mem_filter.mp hz).1⟩
      obtain ⟨Z₁, m₁, hm₁, hsum₁⟩ := weighted_rolle_step_from_zero
        (shellLaplaceF_continuousOn D) (shellLaplaceF_zero D) (shellLaplaceF_contDiffOn D)
        Z' hZ' mult hmZ'
      have hL'_len : L'.length = D.S.card - 1 := by
        have := congrArg List.length hL; simp [hL_len] at this; omega
      have hgt₁ : L'.length < ∑ z ∈ Z₁, m₁ z := by omega
      obtain ⟨y, hy, hy0⟩ := exists_zero_laplaceApply_of_gt L'
        (fun y => deriv (shellLaplaceF D) y - t₁ * shellLaplaceF D y)
        (contDiffOn_shift (shellLaplaceF_contDiffOn D)) Z₁ m₁ hm₁ hgt₁
      have hy_L : laplaceApply L (shellLaplaceF D) y = 0 := by rw [hL]; exact hy0
      obtain ⟨hode, hint_pos⟩ := laplace_ode_identity D (L := L) hL_nodup hL_mem hy
      rw [hy_L] at hode
      have hne : ((-1 : ℝ) ^ (D.S.card + 1)) * _ ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) hint_pos.ne'
      exact hne hode.symm
  · rw [Finset.not_nonempty_iff_eq_empty.mp hZ', Finset.sum_empty]
    exact Nat.zero_le _

/-- Complex Laplace transform on `{w : ℂ | 0 < w.re}` for `analyticOrderNatAt`. -/
noncomputable def shellLaplaceFC (D : ShellHBData) (w : ℂ) : ℂ :=
  ∫ u : ℝ, ((-(D.G (u : ℂ)).re : ℝ) : ℂ) * Complex.exp (w * (u : ℂ))

private lemma shellLaplaceFC_eqOn_real (D : ShellHBData) {y : ℝ} :
    shellLaplaceFC D (y : ℂ) = (shellLaplaceF D y : ℂ) := by
  unfold shellLaplaceFC shellLaplaceF
  have heq : (fun u : ℝ => ((-(D.G (u : ℂ)).re : ℝ) : ℂ) * Complex.exp ((y : ℂ) * (u : ℂ))) =
      fun u : ℝ => ((-(D.G (u : ℂ)).re * Real.exp (y * u) : ℝ) : ℂ) := by
    ext u; rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  rw [heq]
  exact integral_ofReal

private lemma iteratedDeriv_complex_eq_real {g : ℂ → ℂ} {f : ℝ → ℝ}
    (hg : DifferentiableOn ℂ g {w : ℂ | 0 < w.re})
    (heq : ∀ y : ℝ, 0 < y → g (y : ℂ) = (f y : ℂ)) :
    ∀ k : ℕ, ∀ y : ℝ, 0 < y →
      iteratedDeriv k g (y : ℂ) = ((iteratedDeriv k f y : ℝ) : ℂ) := by
  have hisOpen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  suffices h : ∀ k : ℕ, DifferentiableOn ℂ (deriv^[k] g) {w : ℂ | 0 < w.re} ∧
      ∀ y : ℝ, 0 < y → (deriv^[k] g) (y : ℂ) = ((deriv^[k] f y : ℝ) : ℂ) by
    intro k y hy
    simpa [iteratedDeriv_eq_iterate] using (h k).2 y hy
  intro k
  induction k with
  | zero => exact ⟨hg, heq⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨ih.1.deriv hisOpen, fun y hy => ?_⟩
    rw [Function.iterate_succ_apply']
    have hd_g : HasDerivAt (deriv^[k] g) (deriv (deriv^[k] g) (y : ℂ)) (y : ℂ) :=
      ((ih.1 (y : ℂ) (by simpa using hy)).differentiableAt (hisOpen.mem_nhds (by simpa using hy))).hasDerivAt
    have hd_comp : HasDerivAt (fun x : ℝ => (deriv^[k] g) (x : ℂ))
        (deriv (deriv^[k] g) (y : ℂ)) y := by
      simpa using hd_g.comp_ofReal
    have hev : (fun x : ℝ => (deriv^[k] g) (x : ℂ)) =ᶠ[𝓝 y]
        fun x : ℝ => ((deriv^[k] f x : ℝ) : ℂ) :=
      Filter.Eventually.mono (isOpen_Ioi.mem_nhds hy) fun x hx => ih.2 x hx
    have hd_fC : HasDerivAt (fun x : ℝ => ((deriv^[k] f x : ℝ) : ℂ))
        (deriv (deriv^[k] g) (y : ℂ)) y := hd_comp.congr_of_eventuallyEq hev.symm
    have hd_re : HasDerivAt (deriv^[k] f) (deriv (deriv^[k] g) (y : ℂ)).re y :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y hd_fC).congr_of_eventuallyEq
        (Eventually.of_forall fun x => by simp)
    have hd_im : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (deriv (deriv^[k] g) (y : ℂ)).im y :=
      (Complex.imCLM.hasFDerivAt.comp_hasDerivAt y hd_fC).congr_of_eventuallyEq
        (Eventually.of_forall fun x => by simp)
    have him0 : (deriv (deriv^[k] g) (y : ℂ)).im = 0 :=
      hd_im.unique (hasDerivAt_const y (0 : ℝ))
    exact Complex.ext (hd_re.unique hd_re.differentiableAt.hasDerivAt) him0

/-- **Corollary H.14b (`thm:ce-laplace-zeros`, complex `analyticOrderNatAt` bound)**:
on `0 < w.re`, `shellLaplaceFC D` is analytic and the sum of `analyticOrderNatAt` over any
finite set `Z` of positive real zeros is at most `D.S.card - 1`. -/
theorem laplace_zero_analyticOrder_le (D : ShellHBData) (Z : Finset ℝ)
    (hZ : ∀ z ∈ Z, 0 < z) :
    ∑ z ∈ Z, analyticOrderNatAt (shellLaplaceFC D) (z : ℂ) ≤ D.S.card - 1 := by
  have hDiff : DifferentiableOn ℂ (shellLaplaceFC D) {w : ℂ | 0 < w.re} :=
    D.G_inAiryClass.to_polyLeftAiryRightBound.neg.holomorphic_right
  have hisOpen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hAn : AnalyticOnNhd ℂ (shellLaplaceFC D) {w : ℂ | 0 < w.re} :=
    hDiff.analyticOnNhd hisOpen
  have hiter := iteratedDeriv_complex_eq_real hDiff (fun y _ => shellLaplaceFC_eqOn_real D)
  have hnot_top : ∀ z ∈ Z, analyticOrderAt (shellLaplaceFC D) (z : ℂ) ≠ ⊤ := by
    intro z hz htop
    have hz_pos := hZ z hz
    have hev0 : ∀ᶠ w in 𝓝 (z : ℂ), shellLaplaceFC D w = 0 := analyticOrderAt_eq_top.mp htop
    have hall0 : ∀ k : ℕ, iteratedDeriv k (shellLaplaceF D) z = 0 := by
      intro k
      have hkc : iteratedDeriv k (shellLaplaceFC D) (z : ℂ) = 0 := by
        rw [EventuallyEq.iteratedDeriv_eq k hev0]
        simp
      rw [hiter k z hz_pos] at hkc
      exact Complex.ofReal_eq_zero.mp hkc
    have hL_zero : ∀ (L : List ℝ) (g : ℝ → ℝ),
        (∀ n : ℕ, ContDiffOn ℝ n g (Ioi 0)) →
        (∀ k : ℕ, iteratedDeriv k g z = 0) →
        laplaceApply L g z = 0 := by
      intro L
      induction L with
      | nil => intro g _ hg0; change g z = 0; simpa using hg0 0
      | cons t L ih =>
        intro g hg hg0
        exact ih (fun y => deriv g y - t * g y) (contDiffOn_shift hg) fun k => by
          rw [iteratedDeriv_shift hz_pos hg k, hg0 (k + 1), hg0 k, mul_zero, sub_zero]
    let L := D.S.toList
    have h0 := hL_zero L (shellLaplaceF D) (shellLaplaceF_contDiffOn D) hall0
    obtain ⟨hode, hint_pos⟩ := laplace_ode_identity D (L := L)
      (Finset.nodup_toList D.S) (fun _ => Finset.mem_toList) hz_pos
    rw [h0] at hode
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hint_pos.ne' hode.symm
  refine laplace_zero_multiplicity_le D Z hZ (fun z => analyticOrderNatAt (shellLaplaceFC D) (z : ℂ))
    fun z hz k hk => ?_
  have hz_pos := hZ z hz
  have han : AnalyticAt ℂ (shellLaplaceFC D) (z : ℂ) := hAn (z : ℂ) (by simpa using hz_pos)
  have hle : (analyticOrderNatAt (shellLaplaceFC D) (z : ℂ) : ℕ∞) ≤
      analyticOrderAt (shellLaplaceFC D) (z : ℂ) := by
    rw [Nat.cast_analyticOrderNatAt (hnot_top z hz)]
  have hkc := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han).mp hle k hk
  rw [hiter k z hz_pos] at hkc
  exact Complex.ofReal_eq_zero.mp hkc

/-- **Corollary H.14b (`thm:ce-laplace-zeros`, positive near `0+`)**:
`shellLaplaceF D y > 0` for all sufficiently small `y > 0`. -/
theorem laplace_pos_near_zero (D : ShellHBData) :
    ∃ y₀ : ℝ, 0 < y₀ ∧ ∀ y : ℝ, 0 < y → y ≤ y₀ → 0 < shellLaplaceF D y := by
  rcases D.m_eq with ⟨_, hm1⟩ | ⟨hQ, hm_at47⟩
  · exact ⟨1, zero_lt_one, fun y hy _ => shellLaplaceF_m1_pos D hm1 hy⟩
  · have hGre_int : Integrable (fun u : ℝ => (D.G (u : ℂ)).re) := by simpa using D.G_int.re
    have hGre_zero : ∫ u : ℝ, (D.G (u : ℂ)).re = 0 := by
      have := integral_re D.G_int
      simp only [RCLike.re_to_complex] at this
      rw [D.G_integral_zero, Complex.zero_re] at this
      exact this
    have hF_sub : ∀ y : ℝ, 0 ≤ y →
        shellLaplaceF D y = ∫ u : ℝ, (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) := by
      intro y hy
      have hGexp : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * Real.exp (y * u)) := by
        simpa using (D.G_inAiryClass.integrable_exp_nonneg hy)
      have heq_sub : (fun u : ℝ => -(D.G (u : ℂ)).re * Real.exp (y * u)) =
          fun (u : ℝ) => (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) - (D.G (u : ℂ)).re := by
        ext u; ring
      have heq_f : (fun u : ℝ => (D.G (u : ℂ)).re * (1 - Real.exp (y * u))) =
          fun (u : ℝ) => (D.G (u : ℂ)).re - (D.G (u : ℂ)).re * Real.exp (y * u) := by
        ext u; ring
      unfold shellLaplaceF
      rw [heq_sub, integral_sub]
      · rw [hGre_zero, sub_zero]
      · rw [heq_f]; exact hGre_int.sub hGexp
      · exact hGre_int
    have htm_neg : D.tm < 0 :=
      D.tm_le_airyZero_one.trans_lt (airyZero_one.2.trans (by norm_num))
    let M_pos := max (D.S.max' D.S_nonempty) 0
    have hG2_int : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * Real.exp (2 * u)) := by
      simpa using (D.G_inAiryClass.integrable_exp_nonneg (by norm_num : (0 : ℝ) ≤ 2))
    let C_right : ℝ := |D.tm| * (∫ u : ℝ, ‖D.G (u : ℂ)‖) +
        (M_pos * Real.exp M_pos) * (∫ u : ℝ, ‖D.G (u : ℂ)‖) +
        ∫ u in Ioi M_pos, |(D.G (u : ℂ)).re| * Real.exp (2 * u)
    have hC_right_nn : 0 ≤ C_right := by
      have h1 : 0 ≤ ∫ u : ℝ, ‖D.G (u : ℂ)‖ := integral_nonneg fun _ => norm_nonneg _
      have h2 : 0 ≤ ∫ u in Ioi M_pos, |(D.G (u : ℂ)).re| * Real.exp (2 * u) :=
        setIntegral_nonneg measurableSet_Ioi fun u _ =>
          mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
      have hM : 0 ≤ M_pos := le_max_right _ _
      positivity
    have hright_bound : ∀ y : ℝ, 0 < y → y ≤ 1 →
        ∫ u in Ioi D.tm, |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤ C_right * y := by
      intro y hy0 hy1
      have hGexp : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * Real.exp (y * u)) := by
        simpa using (D.G_inAiryClass.integrable_exp_nonneg hy0.le)
      have hint_abs : Integrable (fun u : ℝ => |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))|) :=
        ((hGre_int.sub hGexp).congr (Eventually.of_forall fun u => by dsimp only [Pi.sub_apply]; ring)).abs
      have hsp1 : Ioi D.tm = Ioc D.tm 0 ∪ Ioi 0 := (Set.Ioc_union_Ioi_eq_Ioi htm_neg.le).symm
      have hsp2 : Ioi (0 : ℝ) = Ioc 0 M_pos ∪ Ioi M_pos :=
        (Set.Ioc_union_Ioi_eq_Ioi (le_max_right _ _)).symm
      have hi_1 : ∫ u in Ioc D.tm 0, |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤
          (|D.tm| * ∫ u : ℝ, ‖D.G (u : ℂ)‖) * y := by
        have hdom : IntegrableOn (fun u : ℝ => (|D.tm| * y) * ‖D.G (u : ℂ)‖) (Ioc D.tm 0) :=
          (D.G_int.norm.const_mul _).integrableOn
        have hpt : ∀ u ∈ Ioc D.tm 0,
            |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤ (|D.tm| * y) * ‖D.G (u : ℂ)‖ := by
          intro u hu
          have hyu_nonpos : y * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hy0.le hu.2
          have hexp1 : Real.exp (y * u) ≤ 1 := Real.exp_le_one_iff.mpr hyu_nonpos
          have hexp_lb : 1 + y * u ≤ Real.exp (y * u) := by linarith [Real.add_one_le_exp (y * u)]
          have hfac : |1 - Real.exp (y * u)| ≤ |D.tm| * y := by
            rw [abs_of_nonneg (sub_nonneg.mpr hexp1)]
            have hneg_u : -u ≤ |D.tm| := by rw [abs_of_neg htm_neg]; linarith [hu.1]
            nlinarith
          calc |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))|
              = |(D.G (u : ℂ)).re| * |1 - Real.exp (y * u)| := abs_mul _ _
            _ ≤ ‖D.G (u : ℂ)‖ * (|D.tm| * y) :=
                mul_le_mul (Complex.abs_re_le_norm _) hfac (abs_nonneg _) (norm_nonneg _)
            _ = (|D.tm| * y) * ‖D.G (u : ℂ)‖ := by ring
        have hm := setIntegral_mono_on hint_abs.integrableOn hdom measurableSet_Ioc hpt
        rw [integral_const_mul] at hm
        have hle := setIntegral_le_integral (s := Ioc D.tm 0) D.G_int.norm
          (Eventually.of_forall fun _ => norm_nonneg _)
        calc ∫ u in Ioc D.tm 0, |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))|
            ≤ (|D.tm| * y) * ∫ u in Ioc D.tm 0, ‖D.G (u : ℂ)‖ := hm
          _ ≤ (|D.tm| * y) * ∫ u : ℝ, ‖D.G (u : ℂ)‖ := by gcongr
          _ = (|D.tm| * ∫ u : ℝ, ‖D.G (u : ℂ)‖) * y := by ring
      have hi_2 : ∫ u in Ioc 0 M_pos, |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤
          ((M_pos * Real.exp M_pos) * ∫ u : ℝ, ‖D.G (u : ℂ)‖) * y := by
        have hdom : IntegrableOn (fun u : ℝ => (y * (M_pos * Real.exp M_pos)) * ‖D.G (u : ℂ)‖)
            (Ioc 0 M_pos) := (D.G_int.norm.const_mul _).integrableOn
        have hpt : ∀ u ∈ Ioc 0 M_pos,
            |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤
              (y * (M_pos * Real.exp M_pos)) * ‖D.G (u : ℂ)‖ := by
          intro u hu
          have hyu_nn : 0 ≤ y * u := mul_nonneg hy0.le hu.1.le
          have hexp_ge1 : 1 ≤ Real.exp (y * u) := Real.one_le_exp hyu_nn
          have h_aux : Real.exp (y * u) - 1 ≤ (y * u) * Real.exp (y * u) := by
            have h1 := Real.add_one_le_exp (-(y * u))
            have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (y * u)).le
            rw [add_mul, one_mul, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne'] at h2
            linarith
          have hfac : |1 - Real.exp (y * u)| ≤ y * (M_pos * Real.exp M_pos) := by
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hexp_ge1)]
            have hu_le : u ≤ M_pos := hu.2
            have he_le : Real.exp (y * u) ≤ Real.exp M_pos :=
              Real.exp_le_exp.mpr (by nlinarith [hu.1])
            calc Real.exp (y * u) - 1 ≤ (y * u) * Real.exp (y * u) := h_aux
              _ = y * (u * Real.exp (y * u)) := by ring
              _ ≤ y * (M_pos * Real.exp M_pos) := by gcongr
          calc |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))|
              = |(D.G (u : ℂ)).re| * |1 - Real.exp (y * u)| := abs_mul _ _
            _ ≤ ‖D.G (u : ℂ)‖ * (y * (M_pos * Real.exp M_pos)) :=
                mul_le_mul (Complex.abs_re_le_norm _) hfac (abs_nonneg _) (norm_nonneg _)
            _ = (y * (M_pos * Real.exp M_pos)) * ‖D.G (u : ℂ)‖ := by ring
        have hm := setIntegral_mono_on hint_abs.integrableOn hdom measurableSet_Ioc hpt
        rw [integral_const_mul] at hm
        have hle := setIntegral_le_integral (s := Ioc 0 M_pos) D.G_int.norm
          (Eventually.of_forall fun _ => norm_nonneg _)
        calc ∫ u in Ioc 0 M_pos, |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))|
            ≤ (y * (M_pos * Real.exp M_pos)) * ∫ u in Ioc 0 M_pos, ‖D.G (u : ℂ)‖ := hm
          _ ≤ (y * (M_pos * Real.exp M_pos)) * ∫ u : ℝ, ‖D.G (u : ℂ)‖ := by gcongr
          _ = ((M_pos * Real.exp M_pos) * ∫ u : ℝ, ‖D.G (u : ℂ)‖) * y := by ring
      have hG2_abs_int : IntegrableOn (fun u : ℝ => |(D.G (u : ℂ)).re| * Real.exp (2 * u)) (Ioi M_pos) := by
        have heq_sign : EqOn (fun u : ℝ => |(D.G (u : ℂ)).re| * Real.exp (2 * u))
            (fun u : ℝ => ((-1 : ℝ) ^ D.S.card) * ((D.G (u : ℂ)).re * Real.exp (2 * u))) (Ioi M_pos) := by
          intro u hu
          have hmax : D.S.max' D.S_nonempty < u := (le_max_left _ _).trans_lt (mem_Ioi.mp hu)
          obtain ⟨hform, hNsq, hden⟩ := D.G_re_tail hmax
          have hpos_rhs : 0 ≤ (-1 : ℝ) ^ D.S.card * (D.G (u : ℂ)).re := by
            rw [hform, mul_div_assoc, ← mul_assoc, ← mul_pow, mul_neg_one, neg_neg, one_pow, one_mul]
            exact div_nonneg hNsq.le hden.le
          have habs : |(D.G (u : ℂ)).re| = (-1 : ℝ) ^ D.S.card * (D.G (u : ℂ)).re := by
            rcases neg_one_pow_eq_or ℝ D.S.card with h1 | hm1'
            · rw [h1, one_mul] at hpos_rhs ⊢; exact abs_of_nonneg hpos_rhs
            · rw [hm1', neg_one_mul] at hpos_rhs ⊢; exact abs_of_nonpos (by linarith)
          dsimp only; rw [habs]; ring
        exact ((hG2_int.const_mul ((-1 : ℝ) ^ D.S.card)).integrableOn).congr_fun
          (fun u hu => (heq_sign hu).symm) measurableSet_Ioi
      have hi_3 : ∫ u in Ioi M_pos, |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤
          (∫ u in Ioi M_pos, |(D.G (u : ℂ)).re| * Real.exp (2 * u)) * y := by
        have hpt : ∀ u ∈ Ioi M_pos,
            |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))| ≤
              y * (|(D.G (u : ℂ)).re| * Real.exp (2 * u)) := by
          intro u hu
          have hu0 : 0 ≤ u := (le_max_right _ _).trans (mem_Ioi.mp hu).le
          have hyu_nn : 0 ≤ y * u := mul_nonneg hy0.le hu0
          have h_aux : Real.exp (y * u) - 1 ≤ (y * u) * Real.exp (y * u) := by
            have h1 := Real.add_one_le_exp (-(y * u))
            have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (y * u)).le
            rw [add_mul, one_mul, Real.exp_neg, inv_mul_cancel₀ (Real.exp_pos _).ne'] at h2
            linarith
          have hu_exp : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
          have hfac : |1 - Real.exp (y * u)| ≤ y * Real.exp (2 * u) := by
            rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hyu_nn))]
            have he1 : Real.exp (y * u) ≤ Real.exp u := Real.exp_le_exp.mpr (by nlinarith)
            calc Real.exp (y * u) - 1 ≤ y * (u * Real.exp (y * u)) := by nlinarith
              _ ≤ y * (Real.exp u * Real.exp u) := by gcongr
              _ = y * Real.exp (2 * u) := by rw [← Real.exp_add]; ring_nf
          calc |(D.G (u : ℂ)).re * (1 - Real.exp (y * u))|
              = |(D.G (u : ℂ)).re| * |1 - Real.exp (y * u)| := abs_mul _ _
            _ ≤ |(D.G (u : ℂ)).re| * (y * Real.exp (2 * u)) := by gcongr
            _ = y * (|(D.G (u : ℂ)).re| * Real.exp (2 * u)) := by ring
        have hm := setIntegral_mono_on hint_abs.integrableOn (hG2_abs_int.const_mul y)
          measurableSet_Ioi hpt
        rw [integral_const_mul] at hm
        linarith
      have hu1 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint_abs.integrableOn (s := Ioc D.tm 0)) (hint_abs.integrableOn (s := Ioi 0))
      have hu2 := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hint_abs.integrableOn (s := Ioc 0 M_pos)) (hint_abs.integrableOn (s := Ioi M_pos))
      rw [← hsp1] at hu1
      rw [← hsp2] at hu2
      dsimp [C_right]
      linarith
    obtain ⟨c0, R0, hc0, hR0, hblock⟩ := at47_block_integral D.P D.Q hQ
    let T_max := D.S.sup' D.S_nonempty (fun t => |t|)
    let R₁ := max R0 (max (1 + T_max) (1 + |D.tm|))
    have hR₁_pos : 0 < R₁ := lt_of_lt_of_le (by linarith [hR0]) (le_max_left _ _)
    let c_low : ℝ := (c0 / 4) / (4 ^ D.S.card)
    have hc_low_pos : 0 < c_low := div_pos (by positivity) (by positivity)
    have hleft_bound : ∀ y : ℝ, 0 < y → y ≤ 1 / R₁ →
        c_low * √y ≤ ∫ u in Iic D.tm, (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) := by
      intro y hy0 hyR
      let R := 1 / y
      have hR_ge : R₁ ≤ R := by
        dsimp [R]; rw [le_div_iff₀ hy0]
        linarith [(le_div_iff₀ hR₁_pos).mp hyR]
      have hRR0 : R0 ≤ R := (le_max_left _ _).trans hR_ge
      have hRT : 1 + T_max ≤ R := ((le_max_left _ _).trans (le_max_right _ _)).trans hR_ge
      have hRtm : 1 + |D.tm| ≤ R := ((le_max_right _ _).trans (le_max_right _ _)).trans hR_ge
      have hR_pos : 0 < R := div_pos one_pos hy0
      have hGexp : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * Real.exp (y * u)) := by
        simpa using (D.G_inAiryClass.integrable_exp_nonneg hy0.le)
      have hint_main : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * (1 - Real.exp (y * u))) :=
        (hGre_int.sub hGexp).congr (Eventually.of_forall fun u => by dsimp only [Pi.sub_apply]; ring)
      have hsub_Iic : Icc (-(2 * R)) (-R) ⊆ Iic D.tm := fun u hu => by
        have : -|D.tm| ≤ D.tm := neg_abs_le _
        exact mem_Iic.mpr (by linarith [hu.2, hRtm])
      have hnn_Iic : ∀ u ∈ Iic D.tm, 0 ≤ (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) := by
        intro u hu
        have hGnn := D.G_nonneg_left u hu
        have hu0 : u ≤ 0 := (mem_Iic.mp hu).trans htm_neg.le
        have hexp1 : Real.exp (y * u) ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hy0.le hu0)
        exact mul_nonneg hGnn (sub_nonneg.mpr hexp1)
      have hmono1 : ∫ u in Icc (-(2 * R)) (-R), (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) ≤
          ∫ u in Iic D.tm, (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) :=
        setIntegral_mono_set hint_main.integrableOn
          (ae_restrict_of_forall_mem measurableSet_Iic hnn_Iic)
          (Eventually.of_forall hsub_Iic)
      have hexp_half : ∀ u ∈ Icc (-(2 * R)) (-R), (1 / 2 : ℝ) * (D.G (u : ℂ)).re ≤
          (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) := by
        intro u hu
        have hyu : y * u ≤ -1 := by
          have := mul_le_mul_of_nonneg_left hu.2 hy0.le
          have hyR_eq : y * (-R) = -1 := by dsimp [R]; field_simp [hy0.ne']
          linarith
        have hexp_e : Real.exp (y * u) ≤ Real.exp (-1) := Real.exp_le_exp.mpr hyu
        have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        have he_neg1 : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg, inv_eq_one_div]
          exact one_div_le_one_div_of_le zero_lt_two he1
        have hGnn := D.G_nonneg_left u (hsub_Iic hu)
        nlinarith
      have hG_lb : ∀ u ∈ Icc (-(2 * R)) (-R),
          (at47_Nf D.P D.Q u ^ 2) / (4 ^ D.S.card * R ^ D.S.card) ≤ (D.G (u : ℂ)).re := by
        intro u hu
        have hprod_eq := D.G_prod_eq (u : ℂ)
        have hre_prod : (D.G (u : ℂ)).re * ∏ t ∈ D.S, (t - u) = at47_Nf D.P D.Q u ^ 2 := by
          have h1 := congrArg Complex.re hprod_eq
          have him : (D.G (u : ℂ)).im = 0 := D.G_real u
          have hpr_C : at47_pr D.S (u : ℂ) = ((∏ t ∈ D.S, (u - t) : ℝ) : ℂ) := by
            unfold at47_pr; push_cast; rfl
          have hpr_re : (at47_pr D.S (u : ℂ)).re = ∏ t ∈ D.S, (u - t) := by
            rw [hpr_C, Complex.ofReal_re]
          have hpr_im : (at47_pr D.S (u : ℂ)).im = 0 := by
            rw [hpr_C, Complex.ofReal_im]
          have hN_C : airyPQN D.P D.Q (u : ℂ) = (at47_Nf D.P D.Q u : ℂ) := by
            unfold airyPQN at47_Nf
            rw [airyPQc_ofReal, airyPQc_ofReal, airyAiC_ofReal, deriv_airyAiC_ofReal]
            push_cast; rfl
          have hflip : (-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (u - t) = ∏ t ∈ D.S, (t - u) := by
            have h2 : ∏ t ∈ D.S, (t - u) = ∏ t ∈ D.S, ((-1 : ℝ) * (u - t)) :=
              Finset.prod_congr rfl fun t _ => by ring
            rw [h2, Finset.prod_mul_distrib, Finset.prod_const]
          rw [Complex.mul_re, him, hpr_im, mul_zero, sub_zero, hpr_re] at h1
          have hrhs : ((((-1 : ℝ) ^ D.S.card : ℝ) : ℂ) * airyPQN D.P D.Q (u : ℂ) ^ 2).re =
              (-1 : ℝ) ^ D.S.card * at47_Nf D.P D.Q u ^ 2 := by
            rw [hN_C, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
          rw [hrhs] at h1
          calc (D.G (u : ℂ)).re * ∏ t ∈ D.S, (t - u)
              = (D.G (u : ℂ)).re * ((-1 : ℝ) ^ D.S.card * ∏ t ∈ D.S, (u - t)) := by rw [hflip]
            _ = (-1 : ℝ) ^ D.S.card * ((D.G (u : ℂ)).re * ∏ t ∈ D.S, (u - t)) := by ring
            _ = (-1 : ℝ) ^ D.S.card * ((-1 : ℝ) ^ D.S.card * at47_Nf D.P D.Q u ^ 2) := by rw [h1]
            _ = ((-1 : ℝ) * (-1)) ^ D.S.card * at47_Nf D.P D.Q u ^ 2 := by
                rw [← mul_assoc, ← mul_pow]
            _ = at47_Nf D.P D.Q u ^ 2 := by norm_num
        have hden_pos : 0 < ∏ t ∈ D.S, (t - u) := by
          refine Finset.prod_pos fun t ht => ?_
          have ht_le : |t| ≤ T_max := Finset.le_sup' (fun s => |s|) ht
          linarith [neg_abs_le t, hu.2, hRT]
        have hden_le : ∏ t ∈ D.S, (t - u) ≤ 4 ^ D.S.card * R ^ D.S.card := by
          rw [← mul_pow]
          calc ∏ t ∈ D.S, (t - u) ≤ ∏ _t ∈ D.S, (4 * R) := by
                refine Finset.prod_le_prod₀ (fun t ht => ?_) (fun t ht => ?_)
                · have ht_le : |t| ≤ T_max := Finset.le_sup' (fun s => |s|) ht
                  linarith [neg_abs_le t, hu.2, hRT]
                · have ht_le : |t| ≤ T_max := Finset.le_sup' (fun s => |s|) ht
                  linarith [le_abs_self t, hu.1, hRT]
            _ = (4 * R) ^ D.S.card := by simp
        have hG_eq_div : at47_Nf D.P D.Q u ^ 2 / ∏ t ∈ D.S, (t - u) = (D.G (u : ℂ)).re := by
          rw [← hre_prod, mul_div_cancel_right₀ _ hden_pos.ne']
        rw [← hG_eq_div]
        exact div_le_div_of_nonneg_left (sq_nonneg _) hden_pos hden_le
      have hG_Icc_int : IntegrableOn (fun u : ℝ => (D.G (u : ℂ)).re) (Icc (-(2 * R)) (-R)) :=
        hGre_int.integrableOn
      have hN_cont : ContinuousOn (fun u : ℝ => at47_Nf D.P D.Q u ^ 2) (Icc (-(2 * R)) (-R)) := by
        unfold at47_Nf
        have := continuous_airyAi; have := continuous_airyAi'
        have := Polynomial.continuous D.P (R := ℝ)
        have := Polynomial.continuous D.Q (R := ℝ)
        fun_prop
      have hN_int : IntegrableOn (fun u : ℝ => at47_Nf D.P D.Q u ^ 2 / (4 ^ D.S.card * R ^ D.S.card))
          (Icc (-(2 * R)) (-R)) := (hN_cont.div_const _).integrableOn_Icc
      have h2 := setIntegral_mono_on (hG_Icc_int.const_mul (1 / 2))
        hint_main.integrableOn measurableSet_Icc hexp_half
      have h3 := setIntegral_mono_on hN_int hG_Icc_int measurableSet_Icc hG_lb
      rw [integral_const_mul] at h2
      rw [integral_div] at h3
      have hblk := hblock R hRR0
      have hint_eq : ∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2 =
          ∫ u in (-(2 * R))..(-R), at47_Nf D.P D.Q u ^ 2 := by
        rw [intervalIntegral.integral_of_le (by linarith),
          MeasureTheory.integral_Icc_eq_integral_Ioc]
      have hm_eq_e : D.S.card = at47_e D.P D.Q + 2 := hm_at47.trans (at47_m_eq D.P D.Q)
      have hpow_alg : (R * (R ^ (at47_e D.P D.Q) * √R)) / R ^ D.S.card = √y := by
        rw [hm_eq_e, pow_add, pow_two]
        have hsqrt_eq : √R * √y = 1 := by
          rw [← Real.sqrt_mul hR_pos.le]; dsimp [R]; rw [one_div_mul_cancel hy0.ne', Real.sqrt_one]
        have hRp : R ^ (at47_e D.P D.Q) ≠ 0 := pow_ne_zero _ hR_pos.ne'
        have hsqR : √R * √R = R := Real.mul_self_sqrt hR_pos.le
        calc (R * (R ^ (at47_e D.P D.Q) * √R)) / (R ^ (at47_e D.P D.Q) * (R * R))
            = √R / R := by field_simp [hRp, hR_pos.ne']
          _ = √y := by
              conv_lhs => rhs; rw [← hsqR]
              field_simp [(Real.sqrt_pos.mpr hR_pos).ne']
              exact hsqrt_eq.symm
      rw [← hint_eq] at hblk
      have hcomb : c_low * √y ≤ (1 / 2 : ℝ) * ∫ u in Icc (-(2 * R)) (-R), (D.G (u : ℂ)).re := by
        have hr_pow : R * (R ^ (at47_e D.P D.Q) * √R) = R ^ (at47_e D.P D.Q + 1) * √R := by
          rw [pow_succ]; ring
        have hstep1 : c_low * √y ≤ (∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
            (4 * 4 ^ D.S.card * R ^ D.S.card) := by
          calc c_low * √y = (c0 * (R ^ (at47_e D.P D.Q + 1) * √R)) /
                (4 * 4 ^ D.S.card * R ^ D.S.card) := by
                  rw [← hpow_alg, hr_pow]; dsimp [c_low]; field_simp
            _ ≤ (∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
                (4 * 4 ^ D.S.card * R ^ D.S.card) := div_le_div_of_nonneg_right hblk (by positivity)
        have hint_nn : 0 ≤ (∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
            (4 ^ D.S.card * R ^ D.S.card) :=
          div_nonneg (setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _) (by positivity)
        have hstep2 : (∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
            (4 * 4 ^ D.S.card * R ^ D.S.card) ≤
            (1 / 2 : ℝ) * ((∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
              (4 ^ D.S.card * R ^ D.S.card)) := by
          have heq4 : (∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
              (4 * 4 ^ D.S.card * R ^ D.S.card) =
              (1 / 4 : ℝ) * ((∫ u in Icc (-(2 * R)) (-R), at47_Nf D.P D.Q u ^ 2) /
                (4 ^ D.S.card * R ^ D.S.card)) := by ring
          rw [heq4]
          exact mul_le_mul_of_nonneg_right (by norm_num) hint_nn
        exact hstep1.trans (hstep2.trans (mul_le_mul_of_nonneg_left h3 (by norm_num)))
      exact hcomb.trans (h2.trans hmono1)
    let y₀ := min 1 (min (1 / R₁) ((c_low / (2 * (C_right + 1))) ^ 2))
    have hy₀_pos : 0 < y₀ := lt_min zero_lt_one (lt_min (one_div_pos.mpr hR₁_pos) (by positivity))
    refine ⟨y₀, hy₀_pos, fun y hy0 hyy₀ => ?_⟩
    have hy1 : y ≤ 1 := hyy₀.trans (min_le_left _ _)
    have hyR : y ≤ 1 / R₁ := hyy₀.trans ((min_le_right _ _).trans (min_le_left _ _))
    have hyc : y ≤ (c_low / (2 * (C_right + 1))) ^ 2 :=
      hyy₀.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hGexp : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * Real.exp (y * u)) := by
      simpa using (D.G_inAiryClass.integrable_exp_nonneg hy0.le)
    have hint_main : Integrable (fun u : ℝ => (D.G (u : ℂ)).re * (1 - Real.exp (y * u))) :=
      (hGre_int.sub hGexp).congr (Eventually.of_forall fun u => by dsimp only [Pi.sub_apply]; ring)
    have hsp := integral_add_compl (measurableSet_Iic (a := D.tm)) hint_main
    rw [compl_Iic] at hsp
    have hr_bd : C_right * y ≥ -∫ u in Ioi D.tm, (D.G (u : ℂ)).re * (1 - Real.exp (y * u)) := by
      have h1 := norm_integral_le_integral_norm
        (fun u => (D.G (u : ℂ)).re * (1 - Real.exp (y * u))) (μ := volume.restrict (Ioi D.tm))
      simp only [Real.norm_eq_abs] at h1
      have h2 := neg_le_abs (∫ u in Ioi D.tm, (D.G (u : ℂ)).re * (1 - Real.exp (y * u)))
      linarith [hright_bound y hy0 hy1]
    have h_sqrt : √y ≤ c_low / (2 * (C_right + 1)) :=
      (Real.sqrt_le_iff.mpr ⟨by positivity, hyc⟩)
    have hgap : C_right * y < c_low * √y := by
      have h_mul : (C_right + 1) * √y ≤ c_low / 2 := by linarith [(le_div_iff₀ (by positivity)).mp h_sqrt]
      have h1 : (C_right + 1) * y < c_low * √y := by
        calc (C_right + 1) * y = ((C_right + 1) * √y) * √y := by
              rw [mul_assoc, Real.mul_self_sqrt hy0.le]
          _ ≤ (c_low / 2) * √y := by gcongr
          _ < c_low * √y := by nlinarith [Real.sqrt_pos.mpr hy0, hc_low_pos]
      nlinarith [hy0]
    rw [hF_sub y hy0.le, ← hsp]
    linarith [hleft_bound y hy0 hyR]

/-- **Corollary H.14b (`thm:ce-laplace-zeros`, large-`y` positivity for odd `m`)**:
whenever `Odd D.S.card`, `shellLaplaceF D y > 0` for all sufficiently large `y`. -/
theorem laplace_pos_large_of_odd (D : ShellHBData) (hOdd : Odd D.S.card) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, Y ≤ y → 0 < shellLaplaceF D y := by
  have hGre_neg_int : Integrable (fun u : ℝ => -(D.G (u : ℂ)).re) :=
    (by simpa using D.G_int.re : Integrable (fun u : ℝ => (D.G (u : ℂ)).re)).neg
  have hGre_neg_exp : ∀ y : ℝ, 0 ≤ y →
      Integrable (fun u : ℝ => -(D.G (u : ℂ)).re * Real.exp (y * u)) := fun y hy =>
    (D.G_inAiryClass.integrable_exp_nonneg hy).neg.congr
      (Eventually.of_forall fun u => by simp only [Pi.neg_apply]; ring)
  let M : ℝ := D.S.max' D.S_nonempty + 1
  let x₀ : ℝ := M + 1
  have htail : ∀ u : ℝ, D.S.max' D.S_nonempty < u → 0 < -(D.G (u : ℂ)).re := by
    intro u hu
    obtain ⟨hform, hNsq, hden⟩ := D.G_re_tail hu
    rw [hform, hOdd.neg_one_pow, neg_one_mul, neg_div, neg_neg]
    exact div_pos hNsq hden
  exact laplace_pos_eventually_of_nonneg_tail
    D.G_inAiryClass.to_polyLeftAiryRightBound.1.neg hGre_neg_int hGre_neg_exp
    (by linarith : D.S.max' D.S_nonempty + 1 < D.S.max' D.S_nonempty + 2)
    (fun u hu => (htail u (by linarith)).le)
    (htail (D.S.max' D.S_nonempty + 2) (by linarith))

/-- **Corollary H.14b (`thm:ce-laplace-zeros`, `m = 3` trichotomy for `shellLaplaceF`)**:
for any Hermite–Biehler configuration with `m = 3`, `F_N = shellLaplaceF D` is either:
(1) strictly positive on `(0, ∞)`,
(2) positive on `(0, ∞) \ {a}` with a single double zero at `a > 0`, or
(3) negative on `(a, b)` (`0 < a < b`) and positive on `(0, a) ∪ (b, ∞)` with simple
    zeros at `a` and `b`. -/
theorem laplace_m3_classification (D : ShellHBData) (hm3 : D.S.card = 3) :
    (∀ y : ℝ, 0 < y → 0 < shellLaplaceF D y) ∨
    (∃ a : ℝ, 0 < a ∧ shellLaplaceF D a = 0 ∧ deriv (shellLaplaceF D) a = 0 ∧
      iteratedDeriv 2 (shellLaplaceF D) a ≠ 0 ∧
      ∀ y : ℝ, 0 < y → y ≠ a → 0 < shellLaplaceF D y) ∨
    (∃ a b : ℝ, 0 < a ∧ a < b ∧
      shellLaplaceF D a = 0 ∧ deriv (shellLaplaceF D) a < 0 ∧
      shellLaplaceF D b = 0 ∧ 0 < deriv (shellLaplaceF D) b ∧
      (∀ y : ℝ, 0 < y → y < a → 0 < shellLaplaceF D y) ∧
      (∀ y : ℝ, a < y → y < b → shellLaplaceF D y < 0) ∧
      (∀ y : ℝ, b < y → 0 < shellLaplaceF D y)) := by
  let F := shellLaplaceF D
  by_cases hall : ∀ y : ℝ, 0 < y → 0 < F y
  · exact Or.inl hall
  right
  push Not at hall
  obtain ⟨y_neg, hy_neg_pos, hy_neg_le⟩ := hall
  obtain ⟨y₀, hy₀_pos, hy₀⟩ := laplace_pos_near_zero D
  have hOdd : Odd D.S.card := by rw [hm3]; decide
  obtain ⟨Y, hY_pos, hY⟩ := laplace_pos_large_of_odd D hOdd
  let S₀ : Set ℝ := {y : ℝ | 0 < y ∧ F y ≤ 0}
  have hS₀_ne : S₀.Nonempty := ⟨y_neg, hy_neg_pos, hy_neg_le⟩
  have hS₀_lb : ∀ y ∈ S₀, y₀ ≤ y := fun y ⟨hy, hFy⟩ => by
    by_contra hlt; push Not at hlt; exact absurd (hy₀ y hy hlt.le) (not_lt.mpr hFy)
  have hS₀_ub : ∀ y ∈ S₀, y ≤ Y := fun y ⟨_, hFy⟩ => by
    by_contra hgt; push Not at hgt; exact absurd (hY y hgt.le) (not_lt.mpr hFy)
  have hS₀_bddB : BddBelow S₀ := ⟨y₀, hS₀_lb⟩
  have hS₀_bddA : BddAbove S₀ := ⟨Y, hS₀_ub⟩
  let a := sInf S₀
  let b := sSup S₀
  have ha_ge : y₀ ≤ a := le_csInf hS₀_ne hS₀_lb
  have hb_le : b ≤ Y := csSup_le hS₀_ne hS₀_ub
  have ha_le_b : a ≤ b :=
    (csInf_le hS₀_bddB ⟨hy_neg_pos, hy_neg_le⟩).trans (le_csSup hS₀_bddA ⟨hy_neg_pos, hy_neg_le⟩)
  have ha_pos : 0 < a := hy₀_pos.trans_le ha_ge
  have hb_pos : 0 < b := ha_pos.trans_le ha_le_b
  have hFcont : ContinuousOn F (Ioi 0) := (shellLaplaceF_continuousOn D).mono Ioi_subset_Ici_self
  have ha_left : ∀ y : ℝ, 0 < y → y < a → 0 < F y := fun y hy hy_a => by
    by_contra hle; push Not at hle
    exact absurd (csInf_le hS₀_bddB ⟨hy, hle⟩) (not_le.mpr hy_a)
  have hb_right : ∀ y : ℝ, b < y → 0 < F y := fun y hb_y => by
    by_contra hle; push Not at hle
    exact absurd (le_csSup hS₀_bddA ⟨hb_pos.trans hb_y, hle⟩) (not_le.mpr hb_y)
  have hFa_le : F a ≤ 0 := by
    have : (𝓝[S₀] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (csInf_mem_closure hS₀_ne hS₀_bddB)
    have hcontA : ContinuousAt F a := (hFcont a ha_pos).continuousAt (isOpen_Ioi.mem_nhds ha_pos)
    exact le_of_tendsto (hcontA.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ (hy : _ ∈ S₀) => hy.2)
  have hFb_le : F b ≤ 0 := by
    have : (𝓝[S₀] b).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (csSup_mem_closure hS₀_ne hS₀_bddA)
    have hcontB : ContinuousAt F b := (hFcont b hb_pos).continuousAt (isOpen_Ioi.mem_nhds hb_pos)
    exact le_of_tendsto (hcontB.tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun _ (hy : _ ∈ S₀) => hy.2)
  have hFa_ge : 0 ≤ F a := by
    have ht : Tendsto F (𝓝[<] a) (𝓝 (F a)) :=
      ((hFcont a ha_pos).continuousAt (isOpen_Ioi.mem_nhds ha_pos)).tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT ha_pos] with y hy
    exact (ha_left y hy.1 hy.2).le
  have hFb_ge : 0 ≤ F b := by
    have ht : Tendsto F (𝓝[>] b) (𝓝 (F b)) :=
      ((hFcont b hb_pos).continuousAt (isOpen_Ioi.mem_nhds hb_pos)).tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hb_right y hy).le
  have hFa : F a = 0 := le_antisymm hFa_le hFa_ge
  have hFb : F b = 0 := le_antisymm hFb_le hFb_ge
  rcases eq_or_lt_of_le ha_le_b with hab_eq | hab
  · have hda : deriv F a = 0 := by
      have hmin : IsLocalMin F a := by
        filter_upwards [isOpen_Ioi.mem_nhds ha_pos] with y hy
        rcases lt_trichotomy y a with h | rfl | h
        · exact hFa.symm ▸ (ha_left y hy h).le
        · exact le_rfl
        · exact hFa.symm ▸ (hb_right y (hab_eq ▸ h)).le
      exact hmin.deriv_eq_zero
    refine Or.inl ⟨a, ha_pos, hFa, hda, fun h2 => ?_, fun y hy hne => ?_⟩
    · have hmult := laplace_zero_multiplicity_le D {a} (by simpa using ha_pos) (fun _ => 3)
        fun z hz k hk => by
          have hz_eq := Finset.mem_singleton.mp hz; subst hz_eq
          interval_cases k
          · simpa using hFa
          · simpa using hda
          · exact h2
      simp [hm3] at hmult
    · rcases lt_or_gt_of_ne hne with h | h
      · exact ha_left y hy h
      · exact hb_right y (hab_eq ▸ h)
  · right
    have hd_a_ne : deriv F a ≠ 0 := by
      intro hda
      have hmult := laplace_zero_multiplicity_le D {a, b}
        (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | h
          · exact ha_pos
          · have hzb := Finset.mem_singleton.mp h; subst hzb; exact hb_pos)
        (fun z => if z = a then 2 else 1)
        fun z hz k hk => by
          rcases Finset.mem_insert.mp hz with rfl | h
          · rw [ite_eq_left_iff.mpr (fun heq => absurd rfl heq)] at hk
            interval_cases k
            · simpa using hFa
            · simpa using hda
          · have hzb : z = b := Finset.mem_singleton.mp h; subst hzb
            rw [ite_eq_right_iff.mpr (fun heq => absurd heq hab.ne')] at hk
            have hk0 : k = 0 := by omega
            subst hk0; simpa using hFb
      rw [Finset.sum_pair hab.ne,
        ite_eq_left_iff.mpr (fun h => absurd rfl h),
        ite_eq_right_iff.mpr (fun h => absurd h hab.ne'), hm3] at hmult
      omega
    have hd_b_ne : deriv F b ≠ 0 := by
      intro hdb
      have hmult := laplace_zero_multiplicity_le D {a, b}
        (fun z hz => by
          rcases Finset.mem_insert.mp hz with rfl | h
          · exact ha_pos
          · have hzb := Finset.mem_singleton.mp h; subst hzb; exact hb_pos)
        (fun z => if z = b then 2 else 1)
        fun z hz k hk => by
          rcases Finset.mem_insert.mp hz with rfl | h
          · rw [ite_eq_right_iff.mpr (fun heq => absurd heq hab.ne)] at hk
            have hk0 : k = 0 := by omega
            subst hk0; simpa using hFa
          · have hzb : z = b := Finset.mem_singleton.mp h; subst hzb
            rw [ite_eq_left_iff.mpr (fun heq => absurd rfl heq)] at hk
            interval_cases k
            · simpa using hFb
            · simpa using hdb
      rw [Finset.sum_pair hab.ne,
        ite_eq_right_iff.mpr (fun h => absurd h hab.ne),
        ite_eq_left_iff.mpr (fun h => absurd rfl h), hm3] at hmult
      omega
    have hdF_a : HasDerivAt F (deriv F a) a :=
      (((shellLaplaceF_contDiffOn D 1).differentiableOn (by norm_num) a ha_pos).differentiableAt
        (isOpen_Ioi.mem_nhds ha_pos)).hasDerivAt
    have hdF_b : HasDerivAt F (deriv F b) b :=
      (((shellLaplaceF_contDiffOn D 1).differentiableOn (by norm_num) b hb_pos).differentiableAt
        (isOpen_Ioi.mem_nhds hb_pos)).hasDerivAt
    have hd_a_neg : deriv F a < 0 := by
      refine lt_of_le_of_ne ?_ hd_a_ne
      have ht := hdF_a.tendsto_slope_zero.mono_left
        (nhdsWithin_mono (0 : ℝ) (s := Iio 0) fun _ hx => ne_of_lt hx)
      rw [hFa] at ht
      refine le_of_tendsto ht ?_
      filter_upwards [Ioo_mem_nhdsLT (neg_lt_zero.mpr ha_pos)] with t ht0
      have hpos_F : 0 < F (a + t) := ha_left (a + t) (by linarith [ht0.1]) (by linarith [ht0.2])
      rw [sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr ht0.2.le) hpos_F.le
    have hd_b_pos : 0 < deriv F b := by
      refine lt_of_le_of_ne ?_ hd_b_ne.symm
      have ht := hdF_b.tendsto_slope_zero.mono_left
        (nhdsWithin_mono (0 : ℝ) (s := Ioi 0) fun _ hx => ne_of_gt hx)
      rw [hFb] at ht
      refine ge_of_tendsto ht ?_
      filter_upwards [self_mem_nhdsWithin] with t ht0
      have hpos_F : 0 < F (b + t) := hb_right (b + t) (by linarith [mem_Ioi.mp ht0])
      rw [sub_zero]
      exact mul_nonneg (inv_nonneg.mpr (mem_Ioi.mp ht0).le) hpos_F.le
    refine ⟨a, b, ha_pos, hab, hFa, hd_a_neg, hFb, hd_b_pos, ha_left, ?_, hb_right⟩
    intro y hay hyb
    by_contra hnn
    push Not at hnn
    have ht := hdF_a.tendsto_slope_zero.mono_left
      (nhdsWithin_mono (0 : ℝ) (s := Ioi 0) fun _ hx => ne_of_gt hx)
    rw [hFa] at ht
    have hev_neg : ∀ᶠ t : ℝ in 𝓝[>] 0, t⁻¹ * (F (a + t) - 0) < 0 := ht.eventually (eventually_lt_nhds hd_a_neg)
    have hev_small : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 (y - a) :=
      Ioo_mem_nhdsGT (sub_pos.mpr hay)
    obtain ⟨t, ht_neg, ht_mem⟩ := (hev_neg.and hev_small).exists
    have hFt_neg : F (a + t) < 0 := by
      rw [sub_zero] at ht_neg
      have hinv : 0 < t⁻¹ := inv_pos.mpr ht_mem.1
      nlinarith
    have hc_le : a + t ≤ y := by linarith [ht_mem.2]
    have hIcc_pos : Icc (a + t) y ⊆ Ioi 0 := fun u hu => ha_pos.trans ((lt_add_of_pos_right a ht_mem.1).trans_le hu.1)
    obtain ⟨c, hc_mem, hFc0⟩ := intermediate_value_Icc hc_le (hFcont.mono hIcc_pos) ⟨hFt_neg.le, hnn⟩
    have hac : a < c := (lt_add_of_pos_right a ht_mem.1).trans_le hc_mem.1
    have hcb : c < b := hc_mem.2.trans_lt hyb
    have hmult := laplace_zero_multiplicity_le D {a, c, b}
      (fun z hz => by
        rcases Finset.mem_insert.mp hz with rfl | h
        · exact ha_pos
        · rcases Finset.mem_insert.mp h with rfl | h'
          · exact ha_pos.trans hac
          · have hzb := Finset.mem_singleton.mp h'; subst hzb; exact hb_pos)
      (fun _ => 1)
      fun z hz k hk => by
        have hk0 : k = 0 := by omega
        subst hk0
        rcases Finset.mem_insert.mp hz with rfl | h
        · simpa using hFa
        · rcases Finset.mem_insert.mp h with rfl | h'
          · simpa using hFc0
          · have hzb := Finset.mem_singleton.mp h'; subst hzb; simpa using hFb
    have hc_not : c ∉ ({b} : Finset ℝ) := by simp [hcb.ne]
    have ha_not : a ∉ insert c ({b} : Finset ℝ) := by simp [hac.ne, hab.ne]
    rw [Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_insert_of_notMem ha_not, Finset.card_insert_of_notMem hc_not,
      Finset.card_singleton, hm3] at hmult
    omega

/-- **Corollary H.14b (`thm:ce-laplace-zeros`, `m = 3` trichotomy for `airyLaplace (-G_N)`)**:
since `airyLaplace (-G_N) y = exp(-y³/12) * shellLaplaceF D y`, the exact same trichotomy
holds for `airyLaplace (fun u => -(D.G (u : ℂ)).re)`. -/
theorem laplace_airyLaplace_m3_classification (D : ShellHBData) (hm3 : D.S.card = 3) :
    let L := fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y
    (∀ y : ℝ, 0 < y → 0 < L y) ∨
    (∃ a : ℝ, 0 < a ∧ L a = 0 ∧ deriv L a = 0 ∧
      iteratedDeriv 2 L a ≠ 0 ∧
      ∀ y : ℝ, 0 < y → y ≠ a → 0 < L y) ∨
    (∃ a b : ℝ, 0 < a ∧ a < b ∧
      L a = 0 ∧ deriv L a < 0 ∧
      L b = 0 ∧ 0 < deriv L b ∧
      (∀ y : ℝ, 0 < y → y < a → 0 < L y) ∧
      (∀ y : ℝ, a < y → y < b → L y < 0) ∧
      (∀ y : ℝ, b < y → 0 < L y)) := by
  let e : ℝ → ℝ := fun y => Real.exp (-(y ^ 3) / 12)
  have hL_eq : ∀ y : ℝ, airyLaplace (fun u => -(D.G (u : ℂ)).re) y = e y * shellLaplaceF D y := fun _ => rfl
  have hL_fn : (fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y) = fun y => e y * shellLaplaceF D y := rfl
  have he_pos : ∀ y : ℝ, 0 < e y := fun y => Real.exp_pos _
  have he_cd : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) e := by
    dsimp [e]; rw [show ((1 : WithTop ℕ∞) + 1) = ((2 : ℕ) : WithTop ℕ∞) from rfl]; fun_prop
  have hderiv_L : ∀ y : ℝ, 0 < y →
      deriv (fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y) y =
        deriv e y * shellLaplaceF D y + e y * deriv (shellLaplaceF D) y := by
    intro y hy
    have hde : HasDerivAt e (deriv e y) y := (he_cd.differentiable (by norm_num) y).hasDerivAt
    have hdF : HasDerivAt (shellLaplaceF D) (deriv (shellLaplaceF D) y) y :=
      (((shellLaplaceF_contDiffOn D 1).differentiableOn (by norm_num) y hy).differentiableAt
        (isOpen_Ioi.mem_nhds hy)).hasDerivAt
    rw [hL_fn]
    exact (hde.mul hdF).deriv
  dsimp only
  rcases laplace_m3_classification D hm3 with hall | ⟨a, ha, hFa, hda, h2a, hpos⟩ |
      ⟨a, b, ha, hab, hFa, hda, hFb, hdb, h1, h2, h3⟩
  · exact Or.inl fun y hy => by rw [hL_eq]; exact mul_pos (he_pos y) (hall y hy)
  · refine Or.inr (Or.inl ⟨a, ha, ?_, ?_, ?_, fun y hy hne => ?_⟩)
    · rw [hL_eq, hFa, mul_zero]
    · rw [hderiv_L a ha, hFa, hda]; ring
    · have hev_dL : deriv (fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y) =ᶠ[𝓝 a]
          fun y => deriv e y * shellLaplaceF D y + e y * deriv (shellLaplaceF D) y :=
        Filter.Eventually.mono (isOpen_Ioi.mem_nhds ha) hderiv_L
      have hde2 : HasDerivAt (deriv e) (deriv (deriv e) a) a :=
        ((contDiff_succ_iff_deriv.mp he_cd).2.2.differentiable (by norm_num) a).hasDerivAt
      have hdF : HasDerivAt (shellLaplaceF D) (deriv (shellLaplaceF D) a) a :=
        (((shellLaplaceF_contDiffOn D 2).differentiableOn (by norm_num) a ha).differentiableAt
          (isOpen_Ioi.mem_nhds ha)).hasDerivAt
      have hde : HasDerivAt e (deriv e a) a := (he_cd.differentiable (by norm_num) a).hasDerivAt
      have hdF2 : HasDerivAt (deriv (shellLaplaceF D)) (deriv (deriv (shellLaplaceF D)) a) a :=
        ((((shellLaplaceF_contDiffOn D 2).deriv_of_isOpen (m := (1 : WithTop ℕ∞)) isOpen_Ioi
          (by norm_num)).differentiableOn (by norm_num) a ha).differentiableAt
          (isOpen_Ioi.mem_nhds ha)).hasDerivAt
      have hprod : HasDerivAt (fun y => deriv e y * shellLaplaceF D y + e y * deriv (shellLaplaceF D) y)
          ((deriv (deriv e) a * shellLaplaceF D a + deriv e a * deriv (shellLaplaceF D) a) +
            (deriv e a * deriv (shellLaplaceF D) a + e a * deriv (deriv (shellLaplaceF D)) a)) a :=
        (hde2.mul hdF).add (hde.mul hdF2)
      have h2_eq : iteratedDeriv 2 (fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y) a =
          e a * iteratedDeriv 2 (shellLaplaceF D) a := by
        rw [show iteratedDeriv 2 (fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y) a =
              deriv (deriv (fun y => airyLaplace (fun u => -(D.G (u : ℂ)).re) y)) a by
                simp [iteratedDeriv_eq_iterate],
          EventuallyEq.deriv_eq hev_dL, hprod.deriv, hFa, hda]
        have hF2 : iteratedDeriv 2 (shellLaplaceF D) a = deriv (deriv (shellLaplaceF D)) a := by
          simp [iteratedDeriv_eq_iterate]
        rw [hF2]; ring
      rw [h2_eq]
      exact mul_ne_zero (he_pos a).ne' h2a
    · rw [hL_eq]; exact mul_pos (he_pos y) (hpos y hy hne)
  · refine Or.inr (Or.inr ⟨a, b, ha, hab, ?_, ?_, ?_, ?_, fun y hy hya => ?_,
        fun y hay hyb => ?_, fun y hby => ?_⟩)
    · rw [hL_eq, hFa, mul_zero]
    · rw [hderiv_L a ha, hFa, mul_zero, zero_add]
      exact mul_neg_of_pos_of_neg (he_pos a) hda
    · rw [hL_eq, hFb, mul_zero]
    · rw [hderiv_L b (ha.trans hab), hFb, mul_zero, zero_add]
      exact mul_pos (he_pos b) hdb
    · rw [hL_eq]; exact mul_pos (he_pos y) (h1 y hy hya)
    · rw [hL_eq]; exact mul_neg_of_pos_of_neg (he_pos y) (h2 y hay hyb)
    · rw [hL_eq]; exact mul_pos (he_pos y) (h3 y hby)


/-- info: 'FormalResearch.SignUncertainty.laplace_zero_multiplicity_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_zero_multiplicity_le

/-- info: 'FormalResearch.SignUncertainty.laplace_zero_analyticOrder_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_zero_analyticOrder_le

/-- info: 'FormalResearch.SignUncertainty.laplace_pos_near_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_pos_near_zero

/-- info: 'FormalResearch.SignUncertainty.laplace_pos_large_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_pos_large_of_odd

/-- info: 'FormalResearch.SignUncertainty.laplace_m3_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_m3_classification

/-- info: 'FormalResearch.SignUncertainty.laplace_airyLaplace_m3_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms laplace_airyLaplace_m3_classification

end FormalResearch.SignUncertainty

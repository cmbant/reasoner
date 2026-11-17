module

public import FormalResearch.Special.AiryThm47Exist
public import FormalResearch.Special.AiryZeroOrder
public import FormalResearch.Special.AiryCftZeros

/-!
# Existence of the `m` largest zeros of `N = P Ai + Q Ai'` (Theorem 4.7)

* `at47_sign_flip`: if `g` is `C¹` on `[a,b]`, `g(a) = g(b) = 0`, `g ≠ 0` on `(a,b)` and `g'(a), g'(b) ≠ 0`, then `g'(a) g'(b) < 0`.
* `at47_zero_between`: for consecutive zeros `a_{n+1} < a_n` of `Ai` far enough on the negative axis, `N` has a zero in between
  (the signs `N(a_k) = Q(a_k) Ai'(a_k)` alternate, `Q` having constant sign far to the left); hence the zero set of `N` is unbounded below.
* `at47_exists_top_zeros`: with the finiteness of the zero set in bounded sets and the absence of zeros far to the right
  (`airyPQ_zeros_finite`, `airyPQ_no_zero_sector`), `N` has a set `S` of exactly `m` zeros such that every other zero lies below all
  of `S` (the `m` largest zeros `t_1 > ⋯ > t_m`).
All proved: this removes the hypothesis on `S` of `at47_uniqueness` and `at47_existence` (`at47_top_zeros_min`).
-/

@[expose] public section

open Complex Polynomial Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma at47_deriv_right_nonneg {g : ℝ → ℝ} {a b g' : ℝ} (hg : HasDerivAt g g' a) (ha : g a = 0) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < g x) : 0 ≤ g' := by
  by_contra hneg
  push Not at hneg
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hs' : Tendsto (slope g a) (𝓝[>] a) (𝓝 g') := hs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have h1 : ∀ᶠ x in 𝓝[>] a, slope g a x < 0 := hs'.eventually (gt_mem_nhds hneg)
  have h2 : ∀ᶠ x in 𝓝[>] a, x ∈ Ioo a b := Ioo_mem_nhdsGT hab
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  have hx3 := hpos x hx2
  rw [slope_def_field, ha, sub_zero] at hx1
  have : 0 < g x / (x - a) := div_pos hx3 (by linarith [hx2.1])
  linarith

lemma at47_deriv_left_nonpos {g : ℝ → ℝ} {a b g' : ℝ} (hg : HasDerivAt g g' b) (hb : g b = 0) (hab : a < b)
    (hpos : ∀ x ∈ Ioo a b, 0 < g x) : g' ≤ 0 := by
  by_contra hneg
  push Not at hneg
  have hs := hasDerivAt_iff_tendsto_slope.mp hg
  have hs' : Tendsto (slope g b) (𝓝[<] b) (𝓝 g') := hs.mono_left (nhdsWithin_mono _ fun x hx => ne_of_lt hx)
  have h1 : ∀ᶠ x in 𝓝[<] b, 0 < slope g b x := hs'.eventually (lt_mem_nhds hneg)
  have h2 : ∀ᶠ x in 𝓝[<] b, x ∈ Ioo a b := Ioo_mem_nhdsLT hab
  obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
  have hx3 := hpos x hx2
  rw [slope_def_field, hb, sub_zero] at hx1
  have : g x / (x - b) < 0 := div_neg_of_pos_of_neg hx3 (by linarith [hx2.2])
  linarith

lemma at47_const_sign {g : ℝ → ℝ} (hc : Continuous g) {a b : ℝ} (hne : ∀ x ∈ Ioo a b, g x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < g x) ∨ (∀ x ∈ Ioo a b, g x < 0) := by
  by_cases hab : a < b
  · have hm : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    rcases lt_or_gt_of_ne (hne _ hm) with h | h
    · right
      intro x hx
      by_contra hge
      push Not at hge
      have := intermediate_value_uIcc (a := x) (b := (a + b) / 2) hc.continuousOn
      have h0 : (0 : ℝ) ∈ uIcc (g x) (g ((a + b) / 2)) := by
        rw [mem_uIcc]; right; exact ⟨h.le, hge⟩
      obtain ⟨y, hy, hy0⟩ := this h0
      have hy' : y ∈ Ioo a b := by
        rcases le_total x ((a + b) / 2) with hh | hh
        · rw [uIcc_of_le hh] at hy; exact ⟨by linarith [hx.1, hy.1], by linarith [hm.2, hy.2]⟩
        · rw [uIcc_of_ge hh] at hy; exact ⟨by linarith [hm.1, hy.1], by linarith [hx.2, hy.2]⟩
      exact hne y hy' hy0
    · left
      intro x hx
      by_contra hle
      push Not at hle
      have := intermediate_value_uIcc (a := x) (b := (a + b) / 2) hc.continuousOn
      have h0 : (0 : ℝ) ∈ uIcc (g x) (g ((a + b) / 2)) := by
        rw [mem_uIcc]; left; exact ⟨hle, h.le⟩
      obtain ⟨y, hy, hy0⟩ := this h0
      have hy' : y ∈ Ioo a b := by
        rcases le_total x ((a + b) / 2) with hh | hh
        · rw [uIcc_of_le hh] at hy; exact ⟨by linarith [hx.1, hy.1], by linarith [hm.2, hy.2]⟩
        · rw [uIcc_of_ge hh] at hy; exact ⟨by linarith [hm.1, hy.1], by linarith [hx.2, hy.2]⟩
      exact hne y hy' hy0
  · left; intro x hx; exact absurd (hx.1.trans hx.2) hab

theorem at47_sign_flip {g : ℝ → ℝ} {g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) {a b : ℝ} (hab : a < b)
    (ha : g a = 0) (hb : g b = 0) (hne : ∀ x ∈ Ioo a b, g x ≠ 0) (ha' : g' a ≠ 0) (hb' : g' b ≠ 0) :
    g' a * g' b < 0 := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hg x).continuousAt
  rcases at47_const_sign hc hne with hp | hn
  · have h1 := at47_deriv_right_nonneg (hg a) ha hab hp
    have h2 := at47_deriv_left_nonpos (hg b) hb hab hp
    have h1' : 0 < g' a := lt_of_le_of_ne h1 (Ne.symm ha')
    have h2' : g' b < 0 := lt_of_le_of_ne h2 hb'
    nlinarith
  · have hp : ∀ x ∈ Ioo a b, 0 < (fun x => -g x) x := fun x hx => by simpa using hn x hx
    have hg2 : ∀ x, HasDerivAt (fun x => -g x) (-g' x) x := fun x => (hg x).neg
    have h1 := at47_deriv_right_nonneg (hg2 a) (by simp [ha]) hab hp
    have h2 := at47_deriv_left_nonpos (hg2 b) (by simp [hb]) hab hp
    have h1' : 0 < -g' a := lt_of_le_of_ne h1 (by intro h; apply ha'; linarith)
    have h2' : -g' b < 0 := lt_of_le_of_ne h2 (by intro h; apply hb'; linarith)
    nlinarith

lemma at47_airyAi'_zero_ne (n : ℕ) : airyAi' (airyZero n) ≠ 0 := by
  have h := airyZero_deriv_ne_zero n
  rw [deriv_airyAiC_ofReal] at h
  intro h0; apply h; rw [h0]; simp

/-- Between consecutive zeros of `Ai` far to the left, `N` has a zero. -/
lemma at47_zero_between {P Q : ℝ[X]} (hQ : Q ≠ 0) :
    ∃ T : ℝ, ∀ n : ℕ, 1 ≤ n → airyZero n ≤ -T →
      ∃ x : ℝ, airyZero (n + 1) ≤ x ∧ x ≤ airyZero n ∧ at47_Nf P Q x = 0 := by
  obtain ⟨T0, hT0, hQT⟩ := airyPQ_far_ex hQ
  refine ⟨T0, fun n hn hnT => ?_⟩
  set a := airyZero (n + 1) with ha
  set b := airyZero n with hb
  have hab : a < b := airyZero_strictAnti hn
  have hbT : b ≤ -T0 := hnT
  have haT : a ≤ -T0 := hab.le.trans hbT
  have hflip := at47_sign_flip (g := airyAi) (g' := airyAi') hasDerivAt_airyAi hab (airyAi_airyZero (n + 1))
    (airyAi_airyZero n)
    (fun x hx h0 => by
      have := airyZero_next hn h0 hx.2
      linarith [hx.1])
    (at47_airyAi'_zero_ne (n + 1)) (at47_airyAi'_zero_ne n)
  -- `Q` has constant sign
  have hQc : Continuous (fun x : ℝ => Q.eval x) := Polynomial.continuous Q
  have hQab : 0 < Q.eval a * Q.eval b := by
    by_contra hcon
    push Not at hcon
    have hqa := hQT a haT
    have hqb := hQT b hbT
    have h0 : (0 : ℝ) ∈ uIcc (Q.eval a) (Q.eval b) := by
      rw [mem_uIcc]
      rcases lt_or_gt_of_ne hqa with h1 | h1
      · left; refine ⟨h1.le, ?_⟩; by_contra h2; push Not at h2; nlinarith
      · right; refine ⟨?_, h1.le⟩; by_contra h2; push Not at h2; nlinarith
    obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc (a := a) (b := b) hQc.continuousOn h0
    rw [uIcc_of_le hab.le] at hy
    exact hQT y (by linarith [hy.2]) hy0
  have hNa : at47_Nf P Q a = Q.eval a * airyAi' a := by
    unfold at47_Nf; rw [airyAi_airyZero (n + 1)]; ring
  have hNb : at47_Nf P Q b = Q.eval b * airyAi' b := by
    unfold at47_Nf; rw [airyAi_airyZero n]; ring
  have hNp : at47_Nf P Q a * at47_Nf P Q b < 0 := by
    rw [hNa, hNb]
    have : Q.eval a * airyAi' a * (Q.eval b * airyAi' b) = (Q.eval a * Q.eval b) * (airyAi' a * airyAi' b) := by ring
    rw [this]
    exact mul_neg_of_pos_of_neg hQab hflip
  have hNc : Continuous (at47_Nf P Q) := by
    unfold at47_Nf
    have := continuous_airyAi; have := continuous_airyAi'
    have hP := Polynomial.continuous P (R := ℝ)
    fun_prop
  have h0 : (0 : ℝ) ∈ uIcc (at47_Nf P Q a) (at47_Nf P Q b) := by
    rw [mem_uIcc]
    rcases lt_or_gt_of_ne (show at47_Nf P Q a ≠ 0 from fun h => by rw [h] at hNp; simp at hNp) with h1 | h1
    · left; refine ⟨h1.le, ?_⟩; by_contra h2; push Not at h2; nlinarith
    · right; refine ⟨?_, h1.le⟩; by_contra h2; push Not at h2; nlinarith
  obtain ⟨y, hy, hy0⟩ := intermediate_value_uIcc (a := a) (b := b) hNc.continuousOn h0
  rw [uIcc_of_le hab.le] at hy
  exact ⟨y, hy.1, hy.2, hy0⟩

/-- The real zero set of `N` is unbounded below. -/
lemma at47_zeros_unbounded {P Q : ℝ[X]} (hQ : Q ≠ 0) (L : ℝ) : ∃ x : ℝ, at47_Nf P Q x = 0 ∧ x < L := by
  obtain ⟨T, hT⟩ := at47_zero_between (P := P) hQ
  obtain ⟨n, hn2, hnR⟩ := airyZero_exists_abs_ge (max T (-L + 1))
  have hnT : airyZero n ≤ -T := by linarith [le_max_left T (-L + 1)]
  obtain ⟨x, -, hx2, hx0⟩ := hT n (by omega) hnT
  refine ⟨x, hx0, ?_⟩
  linarith [le_max_right T (-L + 1)]

/-- Order theory: from an infinite set of reals, bounded above and finite above every level, the `m` largest elements. -/
lemma at47_top_finset {Z : Set ℝ} (hinf : Z.Infinite) (hfin : ∀ a : ℝ, (Z ∩ Ici a).Finite) (m : ℕ) :
    ∃ S : Finset ℝ, S.card = m ∧ (∀ t ∈ S, t ∈ Z) ∧ ∀ x ∈ Z, x ∉ S → ∀ t ∈ S, x < t := by
  classical
  induction m with
  | zero => exact ⟨∅, by simp, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨S, hc, hZ, htop⟩ := ih
    have hW : (Z \ (S : Set ℝ)).Infinite := hinf.sdiff S.finite_toSet
    obtain ⟨w0, hw0⟩ := hW.nonempty
    have hWfin : ((Z \ (S : Set ℝ)) ∩ Ici w0).Finite := (hfin w0).subset fun x hx => ⟨hx.1.1, hx.2⟩
    have hne : (hWfin.toFinset).Nonempty := ⟨w0, by simp [hw0]⟩
    set x := hWfin.toFinset.max' hne with hxdef
    have hxmem : x ∈ hWfin.toFinset := Finset.max'_mem _ _
    have hxW : x ∈ Z \ (S : Set ℝ) := by simpa using (Set.Finite.mem_toFinset hWfin).mp hxmem |>.1
    have hxmax : ∀ y ∈ Z \ (S : Set ℝ), y ≤ x := by
      intro y hy
      by_cases hyw : w0 ≤ y
      · exact Finset.le_max' _ y (by simpa using ⟨hy, hyw⟩)
      · push Not at hyw
        exact hyw.le.trans (Finset.le_max' _ w0 (by simp [hw0]))
    refine ⟨insert x S, ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem (by simpa using hxW.2), hc]
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hxW.1
      · exact hZ t ht
    · intro y hyZ hyS t ht
      have hyS' : y ∉ S := fun h => hyS (Finset.mem_insert_of_mem h)
      have hyx : y < x := by
        refine lt_of_le_of_ne (hxmax y ⟨hyZ, by simpa using hyS'⟩) ?_
        intro h; exact hyS (by rw [h]; exact Finset.mem_insert_self _ _)
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact hyx
      · exact htop y hyZ hyS' t ht

/-- **The `m` largest zeros exist.**  For Hermite-Biehler `(P, Q)`, `Q ≠ 0`, `N = P Ai + Q Ai'` has a set `S` of `m` zeros (any `m`)
such that every other zero lies below all elements of `S`. -/
theorem at47_exists_top_zeros {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) (m : ℕ) :
    ∃ S : Finset ℝ, S.card = m ∧ (∀ t ∈ S, airyPQN P Q (t : ℂ) = 0) ∧
      ∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ S → ∀ t ∈ S, x < t := by
  set Z : Set ℝ := {x : ℝ | airyPQN P Q (x : ℂ) = 0} with hZ
  have hZN : ∀ x : ℝ, x ∈ Z ↔ at47_Nf P Q x = 0 := by
    intro x
    simp only [hZ, mem_ofPred_eq, airyPQN_ofReal]
    exact_mod_cast Iff.rfl
  have hinf : Z.Infinite := by
    intro hfin
    obtain ⟨L, hL⟩ := hfin.bddBelow
    obtain ⟨x, hx0, hxL⟩ := at47_zeros_unbounded (P := P) hQ L
    exact absurd (hL ((hZN x).mpr hx0)) (not_le.mpr hxL)
  obtain ⟨T, hT1, hT⟩ := airyPQ_no_zero_sector P Q (Or.inr hQ)
  have hfin : ∀ a : ℝ, (Z ∩ Ici a).Finite := by
    intro a
    have h1 := airyPQ_zeros_finite hHB (max |a| T)
    refine (h1.preimage (Complex.ofReal_injective.injOn)).subset fun x hx => ?_
    refine ⟨hx.1, ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs]
    have hxa : a ≤ x := hx.2
    by_cases hxT : T ≤ x
    · exfalso
      refine hT (x : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hxT) ?_ hx.1
      rw [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · push Not at hxT
      rw [abs_le]
      constructor
      · linarith [neg_abs_le a, le_max_left |a| T]
      · linarith [le_max_right |a| T]
  obtain ⟨S, hc, hZS, htop⟩ := at47_top_finset hinf hfin m
  exact ⟨S, hc, hZS, htop⟩

/-- info: 'FormalResearch.Special.at47_exists_top_zeros' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_exists_top_zeros

/-- **The `m` largest zeros and their minimum** for `m = at47_m P Q`: the hypotheses (`S`, `tm`) of `at47_existence`, `at47_uniqueness`
and `at47_no_admissible_above` are satisfiable for every Hermite-Biehler pair with `Q ≠ 0`.  (`S = {t_1 > ⋯ > t_m}`, `tm = t_m`.) -/
theorem at47_top_zeros_min {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    ∃ (S : Finset ℝ) (tm : ℝ), S.card = at47_m P Q ∧ (∀ t ∈ S, airyPQN P Q (t : ℂ) = 0) ∧
      (∀ x : ℝ, airyPQN P Q (x : ℂ) = 0 → x ∉ S → ∀ t ∈ S, x < t) ∧ tm ∈ S ∧ ∀ t ∈ S, tm ≤ t := by
  obtain ⟨S, hc, hz, htop⟩ := at47_exists_top_zeros hHB hQ (at47_m P Q)
  have hne : S.Nonempty := by
    rw [← Finset.card_pos, hc]
    have : 2 * Q.natDegree + 2 ≤ at47_m P Q := at47_m_ge_Q P Q
    omega
  exact ⟨S, S.min' hne, hc, hz, htop, Finset.min'_mem _ _, fun t ht => Finset.min'_le _ _ ht⟩

/-- info: 'FormalResearch.Special.at47_top_zeros_min' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.at47_top_zeros_min

end FormalResearch.Special

module

public import FormalResearch.SignUncertainty.CeCanonicalDefs

/-!
# Existence of the zero enumeration `t_1 > t_2 > ⋯` of `N = P Ai + Q Ai'` (setup of `thm:ce-canonical-iff`)

Source: `CFT/common/clark_airy.tex`, `gt:1.0p` (3) and `eq:hb-profile` (the zeros of a Hermite–Biehler profile `N`
are real, simple, bounded above and unbounded below).

* `exists_strictAnti_enum`: a set `Z ⊆ ℝ` that is infinite and finite above every level is the range of a strictly
  decreasing sequence `t : ℕ → ℝ` (order theory).
* `hb_zeroSet_infinite`, `hb_zeroSet_finite_above`: for Hermite–Biehler `(P, Q)` the real zero set of `N` is infinite
  (unbounded below: `Q ≠ 0` by `at47_zeros_unbounded`, `Q = 0` since `N = P Ai` vanishes at every `a_n`) and finite
  above every level (`airyPQ_zeros_finite`, `airyPQ_no_zero_sector`), and the enumeration is unique (`IsHbZeroEnum.unique`).
* **`exists_isHbZeroEnum`**: `∃ t, IsHbZeroEnum P Q t` for every Hermite–Biehler `(P, Q)`; so the hypothesis `ht` of
  `thm_ce_canonical_iff` is satisfiable for every `D : ShellHBData`. `hbZeroEnum D` is a chosen such `t`.
-/

@[expose] public section

open Complex Polynomial Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-- Order theory: an infinite set of reals that is finite above every level is the range of a strictly decreasing
sequence (`t n` is the `(n+1)`-st largest element). -/
theorem exists_strictAnti_enum {Z : Set ℝ} (hinf : Z.Infinite) (hfin : ∀ a : ℝ, (Z ∩ Ici a).Finite) :
    ∃ t : ℕ → ℝ, StrictAnti t ∧ ∀ x : ℝ, x ∈ Z ↔ ∃ n, t n = x := by
  classical
  -- `c z` = number of elements of `Z` strictly above `z`
  let c : ℝ → ℕ := fun z => (Z ∩ Ioi z).ncard
  have hfin' : ∀ z : ℝ, (Z ∩ Ioi z).Finite := fun z => (hfin z).subset fun x hx => ⟨hx.1, le_of_lt hx.2⟩
  have hc_lt : ∀ z w : ℝ, z ∈ Z → w ∈ Z → z < w → c w < c z := by
    intro z w hz hw hzw
    exact Set.ncard_lt_ncard ⟨fun x hx => ⟨hx.1, hzw.trans hx.2⟩,
      fun h => lt_irrefl w (h ⟨hw, hzw⟩).2⟩ (hfin' z)
  have hsurj : ∀ n : ℕ, ∃ z ∈ Z, c z = n := by
    intro n
    obtain ⟨S, hcard, hSZ, htop⟩ := at47_top_finset hinf hfin (n + 1)
    have hne : S.Nonempty := by rw [← Finset.card_pos, hcard]; omega
    refine ⟨S.min' hne, hSZ _ (Finset.min'_mem _ _), ?_⟩
    have hset : Z ∩ Ioi (S.min' hne) = ((S.erase (S.min' hne) : Finset ℝ) : Set ℝ) := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨hxZ, hx⟩
        have hxS : x ∈ S := by
          by_contra hxS
          exact absurd (htop x hxZ hxS _ (Finset.min'_mem _ _)) (not_lt.mpr hx.le)
        exact ⟨hxS, hx.ne'⟩
      · rintro ⟨hxS, hxne⟩
        exact ⟨hSZ x hxS, lt_of_le_of_ne (Finset.min'_le _ _ hxS) (Ne.symm hxne)⟩
    show (Z ∩ Ioi (S.min' hne)).ncard = n
    rw [hset, Set.ncard_coe_finset, Finset.card_erase_of_mem (Finset.min'_mem _ _), hcard]
    rfl
  choose t htZ htc using hsurj
  have hinj : ∀ x y : ℝ, x ∈ Z → y ∈ Z → c x = c y → x = y := by
    intro x y hx hy h
    rcases lt_trichotomy x y with hxy | hxy | hxy
    · exact absurd h (hc_lt x y hx hy hxy).ne'
    · exact hxy
    · exact absurd h (hc_lt y x hy hx hxy).ne
  refine ⟨t, fun a b hab => ?_, fun x => ⟨fun hx => ⟨c x, hinj _ _ (htZ _) hx (htc _)⟩, ?_⟩⟩
  · by_contra hcon
    rcases (not_lt.mp hcon).lt_or_eq with hlt | heq
    · have := hc_lt _ _ (htZ a) (htZ b) hlt
      rw [htc, htc] at this
      omega
    · have := htc b
      rw [← heq, htc] at this
      omega
  · rintro ⟨n, rfl⟩
    exact htZ n

/-- The real zero set of `N = P Ai + Q Ai'` of a Hermite–Biehler pair is infinite. -/
theorem hb_zeroSet_infinite {P Q : ℝ[X]} :
    {x : ℝ | at47_Nf P Q x = 0}.Infinite := by
  intro hfin
  obtain ⟨L, hL⟩ := hfin.bddBelow
  by_cases hQ : Q = 0
  · obtain ⟨n, -, hn⟩ := airyZero_exists_abs_ge (-L + 1)
    have h0 : at47_Nf P Q (airyZero n) = 0 := by
      simp [at47_Nf, hQ, airyAi_airyZero]
    linarith [hL h0]
  · obtain ⟨x, hx0, hxL⟩ := at47_zeros_unbounded (P := P) hQ L
    exact absurd (hL hx0) (not_le.mpr hxL)

/-- The real zero set of `N` of a Hermite–Biehler pair is finite above every level
(`gt:1.0p` (3): outside a bounded set the zeros are absent on the right). -/
theorem hb_zeroSet_finite_above {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (a : ℝ) :
    ({x : ℝ | at47_Nf P Q x = 0} ∩ Ici a).Finite := by
  have hPQ : P ≠ 0 ∨ Q ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨rfl, rfl⟩ := h
    exact hHB.F_ne_zero (by simp [airyPQF])
  obtain ⟨T, hT1, hT⟩ := airyPQ_no_zero_sector P Q hPQ
  have h1 := airyPQ_zeros_finite hHB (max |a| T)
  refine (h1.preimage (Complex.ofReal_injective.injOn)).subset fun x hx => ?_
  have hx0 : airyPQN P Q (x : ℂ) = 0 := by
    rw [airyPQN_ofReal]; exact_mod_cast hx.1
  refine ⟨hx0, ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  have hxa : a ≤ x := hx.2
  by_cases hxT : T ≤ x
  · exfalso
    refine hT (x : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; exact hxT) ?_ hx0
    rw [Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · push Not at hxT
    rw [abs_le]
    constructor
    · linarith [neg_abs_le a, le_max_left |a| T]
    · linarith [le_max_right |a| T]

/-- **Zero enumeration (setup of `thm:ce-canonical-iff`).** For every Hermite–Biehler pair `(P, Q)` there is a
strictly decreasing `t : ℕ → ℝ` (`t j = t_{j+1}`) whose range is exactly the real zero set of
`N = P Ai + Q Ai'`. Proved unconditionally: `gt:1.0p` (3) and `eq:hb-profile`. -/
theorem exists_isHbZeroEnum {P Q : ℝ[X]} (hHB : AiryPQHB P Q) : ∃ t : ℕ → ℝ, IsHbZeroEnum P Q t := by
  obtain ⟨t, ht, hr⟩ := exists_strictAnti_enum (hb_zeroSet_infinite) (hb_zeroSet_finite_above hHB)
  exact ⟨t, ht, fun x => hr x⟩

/-- The zero enumeration is unique: two strictly decreasing sequences with the same range (the zero set of `N`)
coincide. -/
theorem IsHbZeroEnum.unique {P Q : ℝ[X]} {t t' : ℕ → ℝ} (h : IsHbZeroEnum P Q t) (h' : IsHbZeroEnum P Q t') :
    t = t' := by
  funext n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨j, hj⟩ := (h'.2 (t n)).1 ((h.2 (t n)).2 ⟨n, rfl⟩)
    obtain ⟨i, hi⟩ := (h.2 (t' n)).1 ((h'.2 (t' n)).2 ⟨n, rfl⟩)
    rcases lt_trichotomy j n with hjn | rfl | hjn
    · exact absurd (by rw [← ih j hjn] at hj; exact hj) (ne_of_gt (h.1 hjn))
    · exact hj.symm
    · rcases lt_trichotomy i n with hin | rfl | hin
      · exact absurd (by rw [ih i hin] at hi; exact hi) (ne_of_gt (h'.1 hin))
      · exact hi
      · exfalso
        have h1 : t' j < t' n := h'.1 hjn
        have h2 : t i < t n := h.1 hin
        rw [hj] at h1
        rw [hi] at h2
        linarith

/-- A chosen zero enumeration `t_1 > t_2 > ⋯` of the Hermite–Biehler configuration `D`
(`IsHbZeroEnum`; see `exists_isHbZeroEnum`). -/
noncomputable def hbZeroEnum (D : ShellHBData) : ℕ → ℝ := Classical.choose (exists_isHbZeroEnum D.hHB)

/-- `hbZeroEnum D` is a zero enumeration of `N`. -/
theorem hbZeroEnum_spec (D : ShellHBData) : IsHbZeroEnum D.P D.Q (hbZeroEnum D) :=
  Classical.choose_spec (exists_isHbZeroEnum D.hHB)

/-- info: 'FormalResearch.SignUncertainty.exists_isHbZeroEnum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_isHbZeroEnum

/-- info: 'FormalResearch.SignUncertainty.IsHbZeroEnum.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsHbZeroEnum.unique

end FormalResearch.SignUncertainty

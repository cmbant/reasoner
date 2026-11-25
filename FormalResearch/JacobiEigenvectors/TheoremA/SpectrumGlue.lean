module

public import Mathlib

/-!
# Paper J, Layer 2: abstract analysis for the assembly of `thm:smo-spec` (matching, gluing, density; L2.S5, L2.S6)

Source: Paper J `app_thmA.tex`, proof of `thm:smo-spec`: paragraphs "Density" and "Matching" (the abstract argument), and the
gluing of the local coefficients `S^I_l` (`I` an interval of the cover) into functions `S_l in C^{M+1}`.  Nothing here mentions a
Jacobi matrix, a chart or an eigenvalue: the point sets `Ev N` stand for the eigenvalues, `hs N` for the step `h = L/(N+1)`.

## Proved here (axiom-pinned)

* `matching_core` (**the paragraph "Matching"**): if `d_0, ..., d_M` are Lipschitz and bounded on `[a, b]`, `sum_j h^j d_j(x) = O(h^{M+1})` at the points `x`
  of `Ev N subset [a, b]`, and `Ev N` is `O(h)`-dense in the open interval `(a, b)` (for each point, for `N` large), then all `d_j` vanish on `[a, b]`.
  This is `unique_core` of `SpectrumUnique.lean` without the flatness at the end points (no function is given outside `[a, b]`; the induction uses
  that the lower `d_i` vanish on the whole of `[a, b]`).
* `glue_contDiffOn`, `glue_iteratedDeriv` (**gluing**): finitely many closed intervals `[a_i, b_i] subset [A, B]` covering `[A, B]` in the
  sense that every `x in [A, B]` is in the relative interior (in `[A, B]`) of some `[a_i, b_i]`, with `C^n` functions `f_i` agreeing on the overlaps,
  give one `g` with `g = f_i` on `[a_i, b_i]`, `g in C^n([A, B])`, and `iteratedDerivWithin k g [A,B] x` equal to the `k`-th derivative of one
  of the `f_i` (so the `C^n` norm of `g` is the maximum of those of the `f_i`).
* `exists_nominal`, `density_core` (**the paragraph "Density"**, abstract form): if `Phi` has slope `>= c` in absolute value on `U` and the
  `N + 1` points `x_k in U` satisfy `Phi(x_k) = pi h (k + 1/2) + O(h)`, then every `Y in U` with `Phi(Y) in [0, pi L]` is within `C h` of some `x_k`.
* `abs_sub_ge_of_deriv_le` : `f' <= -c` on an interval gives `c |x - y| <= |f x - f y|` (mean value theorem).

## Differences from the paper

The paper takes the intervals of the cover "consecutive ones overlapping in intervals of positive length"; here this is the explicit
hypothesis `hcov` of `glue_contDiffOn` (every point of `[A, B]` is in the relative interior of some `[a_i, b_i]`), which is what the smoothness of the glued
function uses.  The uniform lower bound for the slope `|Phi'| >= c` is a hypothesis of `density_core` (the paper's "`S_0^I` is `C^1` with `d_X S_0^I <= -c`").

## Not formalised

The identification of `Ev N` with the eigenvalues (done in `SpectrumAssembly.lean`).
-/

@[expose] public section

noncomputable section

namespace FormalResearch.JacobiEigenvectors.TheoremA

open Finset Set

/-! ### Matching on an overlap -/

/-- **Matching** (paragraph "Matching" of the proof of `thm:smo-spec`).  See the module docstring. -/
theorem matching_core (a b : ℝ) (hab : a < b) (M : ℕ) (d : ℕ → ℝ → ℝ) (Lip Cn : ℝ)
    (hbd : ∀ j ≤ M, ∀ x ∈ Icc a b, |d j x| ≤ Cn)
    (hlip : ∀ j ≤ M, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, |d j x - d j y| ≤ Lip * |x - y|)
    (hs : ℕ → ℝ) (hspos : ∀ N, 0 < hs N) (hs0 : ∀ ε > 0, ∃ N0, ∀ N ≥ N0, hs N < ε)
    (Ev : ℕ → Set ℝ) (C h0 CD : ℝ) (hh0 : 0 < h0)
    (hEv : ∀ N, ∀ x ∈ Ev N, x ∈ Icc a b)
    (hrule : ∀ N, hs N ≤ h0 → ∀ x ∈ Ev N, |∑ j ∈ range (M + 1), hs N ^ j * d j x| ≤ C * hs N ^ (M + 1))
    (hdense : ∀ X ∈ Ioo a b, ∃ N0, ∀ N ≥ N0, ∃ x ∈ Ev N, |x - X| ≤ CD * hs N) :
    ∀ j ≤ M, ∀ X ∈ Icc a b, d j X = 0 := by
  have hCn : 0 ≤ Cn := (abs_nonneg _).trans (hbd 0 (Nat.zero_le _) a ⟨le_rfl, hab.le⟩)
  have hLip : 0 ≤ Lip := by
    have := hlip 0 (Nat.zero_le _) a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
    have h2 : 0 < |a - b| := abs_pos.mpr (by linarith)
    by_contra hneg
    rw [not_le] at hneg
    nlinarith [abs_nonneg (d 0 a - d 0 b)]
  have hinterior : ∀ j ≤ M, (∀ X ∈ Ioo a b, d j X = 0) → ∀ X ∈ Icc a b, d j X = 0 := by
    intro j hj hI X hX
    by_contra hne
    have hpos : 0 < |d j X| := abs_pos.mpr hne
    obtain ⟨s, hs0', hs1', hsL⟩ : ∃ s : ℝ, 0 < s ∧ s < (b - a) / 2 ∧ Lip * s < |d j X| := by
      refine ⟨min ((b - a) / 4) (|d j X| / (2 * (Lip + 1))), lt_min (by linarith) (by positivity), ?_, ?_⟩
      · exact (min_le_left _ _).trans_lt (by linarith)
      · have h1 : min ((b - a) / 4) (|d j X| / (2 * (Lip + 1))) ≤ |d j X| / (2 * (Lip + 1)) := min_le_right _ _
        have h2 : Lip * (|d j X| / (2 * (Lip + 1))) < |d j X| := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left h1 hLip) h2
    rcases le_total X ((a + b) / 2) with h1 | h1
    · have hmem : X + s ∈ Ioo a b := ⟨by linarith [hX.1], by linarith⟩
      have := hlip j hj X hX (X + s) (Ioo_subset_Icc_self hmem)
      rw [hI _ hmem, sub_zero] at this
      have h5 : |X - (X + s)| = s := by rw [show X - (X + s) = -s by ring, abs_neg, abs_of_pos hs0']
      rw [h5] at this
      linarith
    · have hmem : X - s ∈ Ioo a b := ⟨by linarith, by linarith [hX.2]⟩
      have := hlip j hj X hX (X - s) (Ioo_subset_Icc_self hmem)
      rw [hI _ hmem, sub_zero] at this
      have h5 : |X - (X - s)| = s := by rw [show X - (X - s) = s by ring, abs_of_pos hs0']
      rw [h5] at this
      linarith
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hjM
  apply hinterior j hjM
  intro X hX
  obtain ⟨N1, hN1⟩ := hdense X hX
  obtain ⟨K, hK⟩ : ∃ x : ℝ, x = |C| + M * Cn := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  obtain ⟨CD', hCD'⟩ : ∃ x : ℝ, x = |CD| := ⟨_, rfl⟩
  have hCD0 : 0 ≤ CD' := by rw [hCD']; exact abs_nonneg _
  have key : ∀ N ≥ N1, hs N ≤ min 1 h0 → |d j X| ≤ (K + Lip * CD') * hs N := by
    intro N hN hsN
    have hpos := hspos N
    have h1 : hs N ≤ 1 := hsN.trans (min_le_left _ _)
    have hh0N : hs N ≤ h0 := hsN.trans (min_le_right _ _)
    obtain ⟨x, hxE, hxX⟩ := hN1 N hN
    have hxI := hEv N x hxE
    have hxX' : |x - X| ≤ CD' * hs N := hxX.trans (mul_le_mul_of_nonneg_right (by rw [hCD']; exact le_abs_self _) hpos.le)
    have hterm : ∀ i ∈ (range (M + 1)).erase j, |hs N ^ i * d i x| ≤ Cn * hs N ^ (j + 1) := by
      intro i hi
      have hij : i ≠ j := (Finset.mem_erase.mp hi).1
      have hiM : i ≤ M := by have := (Finset.mem_erase.mp hi).2; have := Finset.mem_range.mp this; omega
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · rw [ih i hlt (by omega) x hxI, mul_zero, abs_zero]
        exact mul_nonneg hCn (pow_nonneg hpos.le _)
      · rw [abs_mul, abs_of_pos (pow_pos hpos _)]
        calc hs N ^ i * |d i x| ≤ hs N ^ (j + 1) * Cn :=
              mul_le_mul (pow_le_pow_of_le_one hpos.le h1 (by omega)) (hbd i hiM x hxI) (abs_nonneg _) (pow_nonneg hpos.le _)
          _ = Cn * hs N ^ (j + 1) := by ring
    have hsumE : |∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x| ≤ M * (Cn * hs N ^ (j + 1)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ (range (M + 1)).erase j, |hs N ^ i * d i x|
          ≤ ∑ i ∈ (range (M + 1)).erase j, Cn * hs N ^ (j + 1) := Finset.sum_le_sum hterm
        _ = M * (Cn * hs N ^ (j + 1)) := by
            rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_range.mpr (show j < M + 1 by omega)), Finset.card_range, nsmul_eq_mul]
            simp
    have hdecomp : hs N ^ j * d j x = (∑ i ∈ range (M + 1), hs N ^ i * d i x) - ∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x := by
      have := Finset.add_sum_erase (range (M + 1)) (fun i => hs N ^ i * d i x) (Finset.mem_range.mpr (show j < M + 1 by omega))
      linarith
    have hrx := hrule N hh0N x hxE
    have hCle : C * hs N ^ (M + 1) ≤ |C| * hs N ^ (j + 1) :=
      (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hpos.le _)).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hpos.le h1 (by omega)) (abs_nonneg _))
    have hA : hs N ^ j * |d j x| ≤ K * hs N ^ (j + 1) := by
      rw [← abs_of_pos (pow_pos hpos j), ← abs_mul, hdecomp]
      calc |(∑ i ∈ range (M + 1), hs N ^ i * d i x) - ∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x|
          ≤ |∑ i ∈ range (M + 1), hs N ^ i * d i x| + |∑ i ∈ (range (M + 1)).erase j, hs N ^ i * d i x| := abs_sub _ _
        _ ≤ |C| * hs N ^ (j + 1) + M * (Cn * hs N ^ (j + 1)) := add_le_add (hrx.trans hCle) hsumE
        _ = K * hs N ^ (j + 1) := by rw [hK]; ring
    have hAj : |d j x| ≤ K * hs N := by
      have h3 : hs N ^ j * |d j x| ≤ hs N ^ j * (K * hs N) := by
        calc hs N ^ j * |d j x| ≤ K * hs N ^ (j + 1) := hA
          _ = hs N ^ j * (K * hs N) := by rw [pow_succ]; ring
      exact le_of_mul_le_mul_left h3 (pow_pos hpos j)
    have hXI : X ∈ Icc a b := Ioo_subset_Icc_self hX
    calc |d j X| = |d j X - d j x + d j x| := by ring_nf
      _ ≤ |d j X - d j x| + |d j x| := abs_add_le _ _
      _ ≤ Lip * (CD' * hs N) + K * hs N := by
          refine add_le_add ?_ hAj
          have := hlip j hjM X hXI x hxI
          rw [abs_sub_comm] at hxX'
          exact this.trans (mul_le_mul_of_nonneg_left hxX' hLip)
      _ = (K + Lip * CD') * hs N := by ring
  by_contra hne
  have hpos' : 0 < |d j X| := abs_pos.mpr hne
  have hden : 0 < K + Lip * CD' + 1 := by nlinarith [mul_nonneg hLip hCD0]
  obtain ⟨N0, hN0⟩ := hs0 (min (min 1 h0) (|d j X| / (K + Lip * CD' + 1)))
    (lt_min (lt_min one_pos hh0) (div_pos hpos' hden))
  have hN := hN0 (max N0 N1) (le_max_left _ _)
  have hk := key (max N0 N1) (le_max_right _ _) (hN.le.trans (min_le_left _ _))
  have hlt : hs (max N0 N1) < |d j X| / (K + Lip * CD' + 1) := hN.trans_le (min_le_right _ _)
  rw [lt_div_iff₀ hden] at hlt
  nlinarith [mul_nonneg hLip hCD0, hspos (max N0 N1)]

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.matching_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.matching_core

/-! ### Gluing -/

/-- A closed interval `[a, b] subset [A, B]` is a neighbourhood of `x` in `[A, B]` when `x` is in its relative interior. -/
lemma Icc_mem_nhdsWithin_Icc {A B a b x : ℝ} (hx : x ∈ Icc A B) (h1 : a ≤ x) (h2 : x ≤ b) (h3 : a < x ∨ a = A)
    (h4 : x < b ∨ b = B) : Icc a b ∈ nhdsWithin x (Icc A B) := by
  have hl : Ici a ∈ nhdsWithin x (Icc A B) := by
    rcases h3 with h | h
    · exact mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds h)
    · subst h
      exact Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => hy.1)
  have hr : Iic b ∈ nhdsWithin x (Icc A B) := by
    rcases h4 with h | h
    · exact mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds h)
    · subst h
      exact Filter.mem_of_superset self_mem_nhdsWithin (fun y hy => hy.2)
  have := Filter.inter_mem hl hr
  rwa [Ici_inter_Iic] at this

/-- **Gluing of local `C^n` functions** (see the module docstring). -/
theorem glue_contDiffOn {ι : Type*} (n : ℕ) (A B : ℝ) (a b : ι → ℝ) (f : ι → ℝ → ℝ)
    (hsub : ∀ i, A ≤ a i ∧ a i < b i ∧ b i ≤ B)
    (hreg : ∀ i, ContDiffOn ℝ (n : WithTop ℕ∞) (f i) (Icc (a i) (b i)))
    (hagree : ∀ i j, ∀ x ∈ Icc (a i) (b i), x ∈ Icc (a j) (b j) → f i x = f j x)
    (hcov : ∀ x ∈ Icc A B, ∃ i, a i ≤ x ∧ x ≤ b i ∧ (a i < x ∨ a i = A) ∧ (x < b i ∨ b i = B)) :
    ∃ g : ℝ → ℝ, (∀ i, ∀ x ∈ Icc (a i) (b i), g x = f i x) ∧ ContDiffOn ℝ (n : WithTop ℕ∞) g (Icc A B) ∧
      ∀ k : ℕ, ∀ x ∈ Icc A B, ∃ i, x ∈ Icc (a i) (b i) ∧
        iteratedDerivWithin k g (Icc A B) x = iteratedDerivWithin k (f i) (Icc (a i) (b i)) x := by
  classical
  let g : ℝ → ℝ := fun x => if h : ∃ i, x ∈ Icc (a i) (b i) then f h.choose x else 0
  have hg : ∀ i, ∀ x ∈ Icc (a i) (b i), g x = f i x := by
    intro i x hx
    have hex : ∃ j, x ∈ Icc (a j) (b j) := ⟨i, hx⟩
    simp only [g, dite_cond_eq_true (eq_true hex)]
    exact hagree _ _ x hex.choose_spec hx
  have hnhds : ∀ x ∈ Icc A B, ∃ i, x ∈ Icc (a i) (b i) ∧ Icc (a i) (b i) ∈ nhdsWithin x (Icc A B) := by
    intro x hx
    obtain ⟨i, h1, h2, h3, h4⟩ := hcov x hx
    exact ⟨i, ⟨h1, h2⟩, Icc_mem_nhdsWithin_Icc hx h1 h2 h3 h4⟩
  refine ⟨g, hg, ?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro x hx
    obtain ⟨i, hxi, hmem⟩ := hnhds x hx
    obtain ⟨u, hu, hxu, hsub'⟩ := mem_nhdsWithin.mp hmem
    refine ⟨u, hu, hxu, ?_⟩
    refine ((hreg i).mono (fun y (hy : y ∈ Icc A B ∩ u) => hsub' ⟨hy.2, hy.1⟩)).congr (fun y hy => hg i y (hsub' ⟨hy.2, hy.1⟩))
  · intro k x hx
    obtain ⟨i, hxi, hmem⟩ := hnhds x hx
    refine ⟨i, hxi, ?_⟩
    have hIA : Icc (a i) (b i) ⊆ Icc A B := fun y hy => ⟨by linarith [hy.1, (hsub i).1], by linarith [hy.2, (hsub i).2.2]⟩
    have h1 := iteratedFDerivWithin_inter' (𝕜 := ℝ) (f := g) (n := k) hmem
    rw [inter_eq_right.mpr hIA] at h1
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDerivWithin_eq_iteratedFDerivWithin, ← h1]
    rw [iteratedFDerivWithin_congr (fun y hy => hg i y hy) hxi k]

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.glue_contDiffOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.glue_contDiffOn

/-! ### Density -/

/-- The mean value theorem: a function with `f' <= -c` on an open interval is bi-Lipschitz from below on the closed one. -/
lemma abs_sub_ge_of_deriv_le {f : ℝ → ℝ} {p q c : ℝ} (hf : ContinuousOn f (Icc p q))
    (hdiff : ∀ z ∈ Ioo p q, DifferentiableAt ℝ f z) (hder : ∀ z ∈ Ioo p q, deriv f z ≤ -c) (hc : 0 ≤ c)
    {x y : ℝ} (hx : x ∈ Icc p q) (hy : y ∈ Icc p q) : c * |x - y| ≤ |f x - f y| := by
  wlog hxy : x ≤ y generalizing x y
  · have := this hy hx (le_of_not_ge hxy)
    rwa [abs_sub_comm, abs_sub_comm (f y)] at this
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · simp
  · have hsub : Icc x y ⊆ Icc p q := Icc_subset_Icc hx.1 hy.2
    obtain ⟨z, hz, hfz⟩ := exists_deriv_eq_slope f hlt (hf.mono hsub)
      (fun z hz => (hdiff z ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩).differentiableWithinAt)
    have hzd := hder z ⟨by linarith [hz.1, hx.1], by linarith [hz.2, hy.2]⟩
    have h2 : f y - f x ≤ -c * (y - x) := by
      rw [eq_div_iff (by linarith)] at hfz
      nlinarith
    rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_of_nonneg (by nlinarith : 0 ≤ f x - f y)]
    nlinarith

/-- Every `v in [0, pi h (N+1)]` is within `pi h` of a nominal point `pi h (k + 1/2)`, `0 <= k <= N`. -/
lemma exists_nominal {v h : ℝ} {N : ℕ} (hh : 0 < h) (hv0 : 0 ≤ v) (hv : v ≤ Real.pi * h * ((N : ℝ) + 1)) :
    ∃ k : ℕ, k ≤ N ∧ |v - Real.pi * h * ((k : ℝ) + 1 / 2)| ≤ Real.pi * h := by
  have hph : 0 < Real.pi * h := mul_pos Real.pi_pos hh
  set w := v / (Real.pi * h) with hw
  have hw0 : 0 ≤ w := div_nonneg hv0 hph.le
  have hwN : w ≤ (N : ℝ) + 1 := by rw [hw, div_le_iff₀ hph]; linarith
  have hvw : v = Real.pi * h * w := by rw [hw]; field_simp
  have key : ∃ k : ℕ, k ≤ N ∧ |w - ((k : ℝ) + 1 / 2)| ≤ 1 := by
    rcases le_or_gt ⌊w⌋₊ N with hk | hk
    · refine ⟨⌊w⌋₊, hk, ?_⟩
      have h1 := Nat.floor_le hw0
      have h2 := Nat.lt_floor_add_one w
      rw [abs_le]; constructor <;> linarith
    · refine ⟨N, le_rfl, ?_⟩
      have h1 : ((N : ℝ) + 1) ≤ w := by
        have : (N + 1 : ℕ) ≤ ⌊w⌋₊ := hk
        have h3 := (Nat.le_floor_iff hw0).mp this
        push_cast at h3
        exact h3
      rw [abs_le]; constructor <;> linarith
  obtain ⟨k, hkN, hk⟩ := key
  refine ⟨k, hkN, ?_⟩
  have e : v - Real.pi * h * ((k : ℝ) + 1 / 2) = Real.pi * h * (w - ((k : ℝ) + 1 / 2)) := by rw [hvw]; ring
  rw [e, abs_mul, abs_of_pos hph]
  calc Real.pi * h * |w - ((k : ℝ) + 1 / 2)| ≤ Real.pi * h * 1 := mul_le_mul_of_nonneg_left hk hph.le
    _ = Real.pi * h := mul_one _

/-- **Density** (paragraph "Density", abstract form).  `Phi` is bi-Lipschitz from below with constant `c` on `U`; the `N + 1` points `x_k in U` satisfy
`Phi(x_k) = pi h (k + 1/2) + O(h)`, `h (N + 1) = L`.  Then every `Y in U` with `Phi(Y) in [0, pi L]` is within `(C + pi)/c * h` of some `x_k`. -/
theorem density_core (Phi : ℝ → ℝ) (U : Set ℝ) {c : ℝ} (hc : 0 < c)
    (hslope : ∀ x ∈ U, ∀ y ∈ U, c * |x - y| ≤ |Phi x - Phi y|)
    {N : ℕ} {h L C : ℝ} (hh : 0 < h) (hL : h * ((N : ℝ) + 1) = L) (xs : Fin (N + 1) → ℝ) (hxU : ∀ k, xs k ∈ U)
    (hrule : ∀ k : Fin (N + 1), |Phi (xs k) - Real.pi * h * (((k : ℕ) : ℝ) + 1 / 2)| ≤ C * h)
    {Y : ℝ} (hY : Y ∈ U) (hS0 : 0 ≤ Phi Y) (hS1 : Phi Y ≤ Real.pi * L) :
    ∃ k : Fin (N + 1), |xs k - Y| ≤ (C + Real.pi) / c * h := by
  obtain ⟨k, hkN, hk⟩ := exists_nominal (v := Phi Y) (N := N) hh hS0 (by rw [← hL] at hS1; linarith)
  refine ⟨⟨k, Nat.lt_succ_of_le hkN⟩, ?_⟩
  have h1 := hslope (xs ⟨k, Nat.lt_succ_of_le hkN⟩) (hxU _) Y hY
  have h2 := hrule ⟨k, Nat.lt_succ_of_le hkN⟩
  have h3 : |Phi (xs ⟨k, Nat.lt_succ_of_le hkN⟩) - Phi Y| ≤ (C + Real.pi) * h := by
    have e : Phi (xs ⟨k, Nat.lt_succ_of_le hkN⟩) - Phi Y
        = (Phi (xs ⟨k, Nat.lt_succ_of_le hkN⟩) - Real.pi * h * ((k : ℝ) + 1 / 2))
          + (Real.pi * h * ((k : ℝ) + 1 / 2) - Phi Y) := by ring
    rw [e]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ C * h + Real.pi * h := add_le_add h2 (by rw [abs_sub_comm]; exact hk)
      _ = (C + Real.pi) * h := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.abs_sub_ge_of_deriv_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.abs_sub_ge_of_deriv_le

/-- info: 'FormalResearch.JacobiEigenvectors.TheoremA.density_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.JacobiEigenvectors.TheoremA.density_core

end FormalResearch.JacobiEigenvectors.TheoremA

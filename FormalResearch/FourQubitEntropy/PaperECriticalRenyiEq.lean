import FormalResearch.FourQubitEntropy.PaperECriticalRenyiGrouping

/-!
# Equality cases of the binary-grouping lemma and of the cubic Rényi bound

Paper E, `renyi_cubic_bound.tex`.

* `Jf_pos`: `J(a) > 0` for `a ∈ (0,1)`, `a ≠ 1/2` (the strict form of the analytic core `Jf_nonneg`).
* `renyi_grouping_eq_iff` (`lem:fqe-renyi-grouping`, equality case): for `0 < a < 1` equality in (BG) holds
  iff `a = 1/2` and `H_{q_b}(u) = H_{q_b}(v)`.
* `renyi_binary_eq_iff`: `H_{q_b}(a, 1-a) = 4a(1-a)` iff `a ∈ {0, 1/2, 1}`.
* `renyi_cubic_eq_iff` (`prop:fqe-cubic-bound`, equality case): for `q ≥ q_b`, equality in (CB) holds exactly
  at pure, uniform-two and uniform-four spectra.

Proved, axiom-free.
-/

open Real

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

/-- **`J > 0` on `(1/2, 1)`**: a zero would be an interior minimum, and the minimum principle argument of
`Jf_nonneg_right` then forces `J(1) < 0`. -/
theorem Jf_pos_right {a : ℝ} (ha : 1 / 2 < a) (ha1 : a < 1) : 0 < Jf a := by
  by_contra hneg
  push Not at hneg
  have hJ0 : Jf a = 0 := le_antisymm hneg (Jf_nonneg (by linarith) ha1.le)
  have hloc : IsLocalMin Jf a := by
    filter_upwards [Icc_mem_nhds (show (0 : ℝ) < a by linarith) ha1] with x hx
    rw [hJ0]; exact Jf_nonneg hx.1 hx.2
  have hder := hasDerivAt_Jf (show 0 < a by linarith) ha1
  have hz := hloc.hasDerivAt_eq_zero hder
  have hPhi : Phi a = 0 := by
    have : 0 < 6 * a * (1 - a) := by
      have : 0 < 1 - a := by linarith
      positivity
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h this.ne'
    · exact h
  have hanti : StrictAntiOn Jf (Set.Icc a 1) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc a 1)
      (Jf_continuousOn.mono (fun x hx => ⟨by linarith [hx.1], hx.2⟩)) ?_
    intro x hx
    rw [interior_Icc] at hx
    obtain ⟨hxc, hx1⟩ := hx
    have hx0 : 0 < x := by linarith
    rw [(hasDerivAt_Jf hx0 hx1).deriv]
    have hs : 0 < Real.log a - Real.log (1 - a) := by
      rw [sub_pos]; exact Real.log_lt_log (by linarith) (by linarith)
    have hsx : Real.log a - Real.log (1 - a) < Real.log x - Real.log (1 - x) := by
      have h1 : Real.log a < Real.log x := Real.log_lt_log (by linarith) hxc
      have h2 : Real.log (1 - x) < Real.log (1 - a) := Real.log_lt_log (by linarith) (by linarith)
      linarith
    have hfc : ff (Real.log a - Real.log (1 - a)) ≤ 0 := by
      rw [← Phi_eq_ff (by linarith) ha1, hPhi]
    have := ff_neg_beyond hs hfc hsx
    rw [← Phi_eq_ff hx0 hx1] at this
    have : 0 < 6 * x * (1 - x) := by
      have : 0 < 1 - x := by linarith
      positivity
    nlinarith
  have := hanti ⟨le_refl a, ha1.le⟩ ⟨ha1.le, le_refl 1⟩ ha1
  rw [Jf_one] at this
  linarith

theorem Jf_pos {a : ℝ} (h0 : 0 < a) (h1 : a < 1) (hne : a ≠ 1 / 2) : 0 < Jf a := by
  rcases lt_or_gt_of_ne hne with h | h
  · rw [← Jf_symm]; exact Jf_pos_right (by linarith) (by linarith)
  · exact Jf_pos_right h h1


/-- Equality in the log-sum inequality: `w ln A + (1-w) ln B + h(w) = ln(A+B)` iff `A (1-w) = B w`. -/
theorem log_add_eq_iff {A B w : ℝ} (hA : 0 < A) (hB : 0 < B) (hw0 : 0 < w) (hw1 : w < 1) :
    w * Real.log A + (1 - w) * Real.log B + Real.binEntropy w = Real.log (A + B) ↔
      A * (1 - w) = B * w := by
  have h1w : 0 < 1 - w := by linarith
  have hb : Real.binEntropy w = -(w * Real.log w) - (1 - w) * Real.log (1 - w) := by
    unfold Real.binEntropy; rw [Real.log_inv, Real.log_inv]; ring
  have e : w * (A / w) + (1 - w) * (B / (1 - w)) = A + B := by field_simp
  have hx : A / w ∈ Set.Ioi (0 : ℝ) := div_pos hA hw0
  have hy : B / (1 - w) ∈ Set.Ioi (0 : ℝ) := div_pos hB h1w
  have hlogs : w * Real.log (A / w) + (1 - w) * Real.log (B / (1 - w))
      = w * Real.log A + (1 - w) * Real.log B + Real.binEntropy w := by
    rw [Real.log_div hA.ne' hw0.ne', Real.log_div hB.ne' h1w.ne', hb]; ring
  constructor
  · intro h
    by_contra hne
    have hxy : A / w ≠ B / (1 - w) := by
      intro h'
      apply hne
      rw [div_eq_div_iff hw0.ne' h1w.ne'] at h'
      linarith
    have hc := strictConcaveOn_log_Ioi.2 hx hy hxy hw0 h1w (by ring)
    simp only [smul_eq_mul] at hc
    rw [e, hlogs] at hc
    linarith
  · intro h
    have hxy : B / (1 - w) = A / w := by
      rw [div_eq_div_iff h1w.ne' hw0.ne']; linarith
    have hAB : A + B = A / w := by rw [← e, hxy]; ring
    rw [← hlogs, hxy, hAB]
    ring


section Grouping

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Equality case of the binary grouping lemma** (`lem:fqe-renyi-grouping`): for `0 < a < 1`,
equality in (BG) holds iff `a = 1/2` and `H_{q_b}(u) = H_{q_b}(v)`. -/
theorem renyi_grouping_eq_iff {u : ι → ℝ} {v : κ → ℝ} (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hus : ∑ i, u i = 1) (hvs : ∑ j, v j = 1) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    renyiSpec qb (Sum.elim (fun i => a * u i) (fun j => (1 - a) * v j)) =
        4 * a * (1 - a) + wf a * renyiSpec qb u + (1 - wf a) * renyiSpec qb v ↔
      a = 1 / 2 ∧ renyiSpec qb u = renyiSpec qb v := by
  have hr : 0 < rb := by unfold rb; have := four_Lg_sub_one_pos; positivity
  have hq : qb = rb + 1 := qb_eq_rb_add_one
  have hq0 : 0 < qb := by linarith
  have hL : 0 < Lg := by have := Lg_gt; linarith
  have h4 : 4 * Lg * rb = qb := by
    unfold rb qb; have := four_Lg_sub_one_pos; field_simp
  have hSu := sum_rpow_pos_of_prob hu hus hq0
  have hSv := sum_rpow_pos_of_prob hv hvs hq0
  set Su := ∑ i, u i ^ qb with hSu_def
  set Sv := ∑ j, v j ^ qb with hSv_def
  have hden : (1 - qb) = -rb := by linarith
  have hlogb : ∀ x : ℝ, Real.logb 2 x = Real.log x / Lg := fun x => rfl
  have hHu : renyiSpec qb u = -Real.log Su / (Lg * rb) := by
    unfold renyiSpec; rw [hlogb, hden, ← hSu_def]; field_simp
  have hHv : renyiSpec qb v = -Real.log Sv / (Lg * rb) := by
    unfold renyiSpec; rw [hlogb, hden, ← hSv_def]; field_simp
  have hcat : ∑ x, (Sum.elim (fun i => a * u i) (fun j => (1 - a) * v j) x) ^ qb
      = a ^ qb * Su + (1 - a) ^ qb * Sv := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hSu_def, hSv_def, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => Real.mul_rpow ha0.le (hu i)
    · exact Finset.sum_congr rfl fun j _ => Real.mul_rpow (by linarith) (hv j)
  have hHc : renyiSpec qb (Sum.elim (fun i => a * u i) (fun j => (1 - a) * v j))
      = -Real.log (a ^ qb * Su + (1 - a) ^ qb * Sv) / (Lg * rb) := by
    unfold renyiSpec; rw [hlogb, hcat, hden]; field_simp
  rw [hHc, hHu, hHv]
  have hLr : 0 < Lg * rb := mul_pos hL hr
  have h1a : 0 < 1 - a := by linarith
  have hA : 0 < a ^ qb * Su := mul_pos (Real.rpow_pos_of_pos ha0 _) hSu
  have hB : 0 < (1 - a) ^ qb * Sv := mul_pos (Real.rpow_pos_of_pos h1a _) hSv
  have hw0 := wf_pos ha0 ha1
  have hw1 := wf_lt_one ha0 ha1
  have hls := log_add_ge hA hB hw0 hw1
  have hlse := log_add_eq_iff hA hB hw0 hw1
  rw [Real.log_mul (Real.rpow_pos_of_pos ha0 _).ne' hSu.ne', Real.log_mul
    (Real.rpow_pos_of_pos h1a _).ne' hSv.ne', Real.log_rpow ha0, Real.log_rpow h1a] at hls hlse
  have hJ := Jf_nonneg ha0.le ha1.le
  unfold Jf at hJ
  -- the equation, multiplied out
  have heq : (-Real.log (a ^ qb * Su + (1 - a) ^ qb * Sv) / (Lg * rb)
        = 4 * a * (1 - a) + wf a * (-Real.log Su / (Lg * rb)) + (1 - wf a) * (-Real.log Sv / (Lg * rb)))
      ↔ Real.log (a ^ qb * Su + (1 - a) ^ qb * Sv)
        = wf a * Real.log Su + (1 - wf a) * Real.log Sv - qb * a * (1 - a) := by
    rw [div_eq_iff hLr.ne']
    have e : (4 * a * (1 - a) + wf a * (-Real.log Su / (Lg * rb)) + (1 - wf a) * (-Real.log Sv / (Lg * rb)))
        * (Lg * rb) = qb * a * (1 - a) - wf a * Real.log Su - (1 - wf a) * Real.log Sv := by
      field_simp; rw [← h4]; ring
    rw [e]
    constructor <;> intro h <;> linarith
  rw [heq]
  have hJ' : 0 ≤ Jf a := Jf_nonneg ha0.le ha1.le
  have hJeq : Jf a = qb * (wf a * Real.log a + (1 - wf a) * Real.log (1 - a))
      + Real.binEntropy (wf a) + qb * a * (1 - a) := rfl
  have hSS : ∀ x y : ℝ, 0 < x → 0 < y → (-Real.log x / (Lg * rb) = -Real.log y / (Lg * rb) ↔ x = y) := by
    intro x y hx hy
    rw [div_left_inj' hLr.ne', neg_inj]
    exact ⟨fun h => Real.log_injOn_pos (Set.mem_Ioi.2 hx) (Set.mem_Ioi.2 hy) h, fun h => by rw [h]⟩
  have hw12 : wf (1 / 2) = 1 / 2 := by unfold wf; norm_num
  constructor
  · intro h
    have hne : a = 1 / 2 := by
      by_contra hne
      have := Jf_pos ha0 ha1 hne
      nlinarith
    refine ⟨hne, ?_⟩
    subst hne
    have hX : wf (1 / 2) * (qb * Real.log (1 / 2) + Real.log Su)
        + (1 - wf (1 / 2)) * (qb * Real.log (1 - 1 / 2) + Real.log Sv) + Real.binEntropy (wf (1 / 2))
        = Real.log ((1 / 2) ^ qb * Su + (1 - 1 / 2) ^ qb * Sv) := by
      have := Jf_half
      rw [hJeq] at this
      linarith
    have hAB := hlse.mp hX
    rw [hw12] at hAB
    have hpos : 0 < ((1 : ℝ) / 2) ^ qb := Real.rpow_pos_of_pos (by norm_num) _
    have : Su = Sv := by
      have h1 : ((1 : ℝ) - 1 / 2) = 1 / 2 := by norm_num
      rw [h1] at hAB
      have := mul_left_cancel₀ hpos.ne' (show (1 / 2 : ℝ) ^ qb * (Su * (1 / 2)) = (1 / 2) ^ qb * (Sv * (1 / 2)) by
        linarith)
      linarith
    exact (hSS _ _ hSu hSv).mpr this
  · rintro ⟨hα, hH⟩
    subst hα
    have hSuv : Su = Sv := (hSS _ _ hSu hSv).mp hH
    have hX : wf (1 / 2) * (qb * Real.log (1 / 2) + Real.log Su)
        + (1 - wf (1 / 2)) * (qb * Real.log (1 - 1 / 2) + Real.log Sv) + Real.binEntropy (wf (1 / 2))
        = Real.log ((1 / 2) ^ qb * Su + (1 - 1 / 2) ^ qb * Sv) := by
      refine hlse.mpr ?_
      rw [hw12, hSuv]
      norm_num
    have := Jf_half
    rw [hJeq] at this
    linarith

end Grouping


theorem qb_pos : 0 < qb := by
  have hr : 0 < rb := by unfold rb; have := four_Lg_sub_one_pos; positivity
  rw [qb_eq_rb_add_one]; linarith

theorem one_lt_qb : 1 < qb := by
  have hr : 0 < rb := by unfold rb; have := four_Lg_sub_one_pos; positivity
  rw [qb_eq_rb_add_one]; linarith

/-- `H_q` of the pure spectrum `(0, 1)` vanishes. -/
theorem renyiSpec_pure_pair {q : ℝ} (hq : 0 < q) : renyiSpec q ![0, 1] = 0 := by
  unfold renyiSpec
  simp [Fin.sum_univ_two, Real.zero_rpow hq.ne']

theorem renyiSpec_pure_pair' {q : ℝ} (hq : 0 < q) : renyiSpec q ![1, 0] = 0 := by
  unfold renyiSpec
  simp [Fin.sum_univ_two, Real.zero_rpow hq.ne']

/-- **Equality case of the binary bound**: `H_{q_b}(a, 1-a) = 4a(1-a)` iff `a ∈ {0, 1/2, 1}`. -/
theorem renyi_binary_eq_iff {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    renyiSpec qb ![a, 1 - a] = 4 * a * (1 - a) ↔ a = 0 ∨ a = 1 / 2 ∨ a = 1 := by
  rcases eq_or_lt_of_le ha0 with h0 | h0
  · subst h0
    simp only [true_or, iff_true]
    have := renyiSpec_pure_pair qb_pos
    simpa using this
  rcases eq_or_lt_of_le ha1 with h1 | h1
  · subst h1
    simp only [or_true, iff_true]
    have := renyiSpec_pure_pair' qb_pos
    simpa using this
  have hg := renyi_grouping_eq_iff (u := fun _ : Unit => (1 : ℝ)) (v := fun _ : Unit => (1 : ℝ))
    (fun _ => zero_le_one) (fun _ => zero_le_one) (by simp) (by simp) h0 h1
  have h00 : renyiSpec qb (fun _ : Unit => (1 : ℝ)) = 0 := by unfold renyiSpec; simp
  have e : renyiSpec qb (Sum.elim (fun _ : Unit => a * 1) (fun _ : Unit => (1 - a) * 1)) =
      renyiSpec qb ![a, 1 - a] := by
    unfold renyiSpec
    simp [Fintype.sum_sum_type, Fin.sum_univ_two]
  simp only [mul_one] at hg e
  rw [e, h00] at hg
  simp only [mul_zero, add_zero] at hg
  rw [hg]
  constructor
  · rintro ⟨h, -⟩; exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact absurd h h0.ne'
    · exact ⟨h, trivial⟩
    · exact absurd h h1.ne


/-! ### The cubic bound: equality cases -/

/-- A pure, uniform-two or uniform-four spectrum on four points. -/
def PureOrUniform (l : Fin 4 → ℝ) : Prop :=
  (∃ i, l i = 1 ∧ ∀ j, j ≠ i → l j = 0) ∨
  (∃ i j, i ≠ j ∧ l i = 1 / 2 ∧ l j = 1 / 2 ∧ ∀ k, k ≠ i → k ≠ j → l k = 0) ∨
  (∀ i, l i = 1 / 4)

theorem sum_two_support {f : Fin 4 → ℝ} {i j : Fin 4} (hij : i ≠ j)
    (h : ∀ k, k ≠ i → k ≠ j → f k = 0) : ∑ k, f k = f i + f j := by
  rw [← Finset.sum_pair hij]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact h k hk.1 hk.2

/-- The three families attain the cubic bound at every order `q > 1`. -/
theorem renyi_cubic_eq_of_pureOrUniform {q : ℝ} (hq : 1 < q) {l : Fin 4 → ℝ} (h : PureOrUniform l) :
    renyiSpec q l = 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3 := by
  have hq0 : 0 < q := by linarith
  have hq1 : (1 - q) ≠ 0 := by linarith
  rcases h with ⟨i, hi, hj⟩ | ⟨i, j, hij, hi, hj, hk⟩ | hu
  · have hsum : ∀ n : ℝ, 0 < n → ∑ k, l k ^ n = 1 := by
      intro n hn
      rw [Finset.sum_eq_single i]
      · rw [hi]; simp
      · intro k _ hki; rw [hj k hki, Real.zero_rpow hn.ne']
      · simp
    have hsum' : ∀ n : ℕ, 0 < n → ∑ k, l k ^ n = 1 := by
      intro n hn
      rw [Finset.sum_eq_single i]
      · rw [hi]; simp
      · intro k _ hki; rw [hj k hki, zero_pow hn.ne']
      · simp
    unfold renyiSpec
    rw [hsum q hq0, hsum' 2 (by norm_num), hsum' 3 (by norm_num)]
    simp
    norm_num
  · have hsum : ∀ n : ℝ, 0 < n → ∑ k, l k ^ n = 2 * (1 / 2) ^ n := by
      intro n hn
      rw [sum_two_support hij (fun k hki hkj => by rw [hk k hki hkj, Real.zero_rpow hn.ne']), hi, hj]
      ring
    have hsum' : ∀ n : ℕ, 0 < n → ∑ k, l k ^ n = 2 * (1 / 2) ^ n := by
      intro n hn
      rw [sum_two_support hij (fun k hki hkj => by rw [hk k hki hkj, zero_pow hn.ne']), hi, hj]
      ring
    unfold renyiSpec
    rw [hsum q hq0, hsum' 2 (by norm_num), hsum' 3 (by norm_num)]
    have e : 2 * (1 / 2 : ℝ) ^ q = (2 : ℝ) ^ (1 - q) := by
      rw [Real.rpow_sub (by norm_num), Real.rpow_one, one_div, Real.inv_rpow (by norm_num)]
      field_simp
    rw [e, Real.logb_rpow (by norm_num) (by norm_num), div_self hq1]
    norm_num
  · have hsum : ∀ n : ℝ, 0 < n → ∑ k, l k ^ n = 4 * (1 / 4) ^ n := by
      intro n hn
      simp only [hu, Fin.sum_univ_four]
      ring
    have hsum' : ∀ n : ℕ, ∑ k, l k ^ n = 4 * (1 / 4) ^ n := by
      intro n
      simp only [hu, Fin.sum_univ_four]
      ring
    unfold renyiSpec
    rw [hsum q hq0, hsum' 2, hsum' 3]
    have e : 4 * (1 / 4 : ℝ) ^ q = (2 : ℝ) ^ (2 * (1 - q)) := by
      have h4 : (1 / 4 : ℝ) = ((2 : ℝ) ^ (2 : ℝ))⁻¹ := by norm_num
      rw [h4, Real.inv_rpow (by positivity), ← Real.rpow_mul (by norm_num), mul_sub, mul_one,
        Real.rpow_sub (by norm_num), Real.rpow_two]
      norm_num
      ring
    rw [e, Real.logb_rpow (by norm_num) (by norm_num)]
    field_simp
    norm_num


/-- `PureOrUniform` from the eleven explicit vectors. -/
theorem PureOrUniform.mk' (l : Fin 4 → ℝ)
    (h : (l 0 = 1 ∧ l 1 = 0 ∧ l 2 = 0 ∧ l 3 = 0) ∨ (l 0 = 0 ∧ l 1 = 1 ∧ l 2 = 0 ∧ l 3 = 0) ∨
      (l 0 = 0 ∧ l 1 = 0 ∧ l 2 = 1 ∧ l 3 = 0) ∨ (l 0 = 0 ∧ l 1 = 0 ∧ l 2 = 0 ∧ l 3 = 1) ∨
      (l 0 = 1 / 2 ∧ l 1 = 1 / 2 ∧ l 2 = 0 ∧ l 3 = 0) ∨ (l 0 = 1 / 2 ∧ l 1 = 0 ∧ l 2 = 1 / 2 ∧ l 3 = 0) ∨
      (l 0 = 1 / 2 ∧ l 1 = 0 ∧ l 2 = 0 ∧ l 3 = 1 / 2) ∨ (l 0 = 0 ∧ l 1 = 1 / 2 ∧ l 2 = 1 / 2 ∧ l 3 = 0) ∨
      (l 0 = 0 ∧ l 1 = 1 / 2 ∧ l 2 = 0 ∧ l 3 = 1 / 2) ∨ (l 0 = 0 ∧ l 1 = 0 ∧ l 2 = 1 / 2 ∧ l 3 = 1 / 2) ∨
      (l 0 = 1 / 4 ∧ l 1 = 1 / 4 ∧ l 2 = 1 / 4 ∧ l 3 = 1 / 4)) : PureOrUniform l := by
  rcases h with ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ |
    ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨0, a, fun j hj => by fin_cases j <;> simp_all⟩
  · exact Or.inl ⟨1, b, fun j hj => by fin_cases j <;> simp_all⟩
  · exact Or.inl ⟨2, c, fun j hj => by fin_cases j <;> simp_all⟩
  · exact Or.inl ⟨3, d, fun j hj => by fin_cases j <;> simp_all⟩
  · exact Or.inr (Or.inl ⟨0, 1, by decide, a, b, fun k h0 h1 => by fin_cases k <;> simp_all⟩)
  · exact Or.inr (Or.inl ⟨0, 2, by decide, a, c, fun k h0 h1 => by fin_cases k <;> simp_all⟩)
  · exact Or.inr (Or.inl ⟨0, 3, by decide, a, d, fun k h0 h1 => by fin_cases k <;> simp_all⟩)
  · exact Or.inr (Or.inl ⟨1, 2, by decide, b, c, fun k h0 h1 => by fin_cases k <;> simp_all⟩)
  · exact Or.inr (Or.inl ⟨1, 3, by decide, b, d, fun k h0 h1 => by fin_cases k <;> simp_all⟩)
  · exact Or.inr (Or.inl ⟨2, 3, by decide, c, d, fun k h0 h1 => by fin_cases k <;> simp_all⟩)
  · exact Or.inr (Or.inr fun i => by fin_cases i <;> simp_all)

/-- **Equality case of `prop:fqe-cubic-bound`** (at `q = q_b`): equality holds only at pure, uniform-two or
uniform-four spectra. -/
theorem pureOrUniform_of_cubic_eq_qb (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i) (hs : ∑ i, l i = 1)
    (hE : renyiSpec qb l = 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3) : PureOrUniform l := by
  rw [Fin.sum_univ_four] at hs
  obtain ⟨u0, hu0a, hu0b, hu0, hu1⟩ := split_pair (hl 0) (hl 1)
  obtain ⟨v0, hv0a, hv0b, hv0, hv1⟩ := split_pair (hl 2) (hl 3)
  set a := l 0 + l 1 with ha
  have ha0 : 0 ≤ a := by have := hl 0; have := hl 1; linarith
  have hb : l 2 + l 3 = 1 - a := by linarith
  rw [hb] at hv0 hv1
  have ha1 : a ≤ 1 := by have := hl 2; have := hl 3; linarith
  have hcat : renyiSpec qb l = renyiSpec qb (Sum.elim (fun i : Fin 2 => a * ![u0, 1 - u0] i)
      (fun j : Fin 2 => (1 - a) * ![v0, 1 - v0] j)) := by
    unfold renyiSpec
    simp [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_four, hu0, hu1, hv0, hv1]
    rw [add_assoc (l 0 ^ qb + l 1 ^ qb)]
  have hupos : ∀ i, 0 ≤ ![u0, 1 - u0] i := by intro i; fin_cases i <;> simp <;> linarith
  have hvpos : ∀ i, 0 ≤ ![v0, 1 - v0] i := by intro i; fin_cases i <;> simp <;> linarith
  have hus : ∑ i, ![u0, 1 - u0] i = 1 := by simp [Fin.sum_univ_two]
  have hvs : ∑ i, ![v0, 1 - v0] i = 1 := by simp [Fin.sum_univ_two]
  have hg := renyi_grouping (u := ![u0, 1 - u0]) (v := ![v0, 1 - v0]) hupos hvpos hus hvs ha0 ha1
  have hbu := renyi_binary_bound hu0a hu0b
  have hbv := renyi_binary_bound hv0a hv0b
  have hw0 : 0 ≤ wf a := by
    unfold wf; have : 0 ≤ 3 - 2 * a := by linarith
    positivity
  have hw1 : 0 ≤ 1 - wf a := by
    rw [one_sub_wf]; have : 0 ≤ 1 - a := by linarith
    positivity
  have e1 : a ^ 2 * (u0 * (1 - u0)) = l 0 * l 1 := by rw [← hu0, ← hu1]; ring
  have e2 : (1 - a) ^ 2 * (v0 * (1 - v0)) = l 2 * l 3 := by rw [← hv0, ← hv1]; ring
  have hEq : 4 * a * (1 - a) + wf a * (4 * u0 * (1 - u0)) + (1 - wf a) * (4 * v0 * (1 - v0))
      = 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3 := by
    rw [one_sub_wf]
    unfold wf
    simp only [Fin.sum_univ_four]
    have l3 : l 3 = 1 - l 0 - l 1 - l 2 := by linarith
    have : 4 * a * (1 - a) + a ^ 2 * (3 - 2 * a) * (4 * u0 * (1 - u0)) +
        (1 - a) ^ 2 * (1 + 2 * a) * (4 * v0 * (1 - v0)) =
        4 * a * (1 - a) + 4 * (3 - 2 * a) * (a ^ 2 * (u0 * (1 - u0))) +
        4 * (1 + 2 * a) * ((1 - a) ^ 2 * (v0 * (1 - v0))) := by ring
    rw [this, e1, e2, ha, l3]
    ring
  rw [hcat] at hE
  have hmul1 : wf a * renyiSpec qb ![u0, 1 - u0] ≤ wf a * (4 * u0 * (1 - u0)) :=
    mul_le_mul_of_nonneg_left hbu hw0
  have hmul2 : (1 - wf a) * renyiSpec qb ![v0, 1 - v0] ≤ (1 - wf a) * (4 * v0 * (1 - v0)) :=
    mul_le_mul_of_nonneg_left hbv hw1
  have hl0 : l 0 = a * u0 := hu0.symm
  have hl1 : l 1 = a * (1 - u0) := hu1.symm
  have hl2 : l 2 = (1 - a) * v0 := hv0.symm
  have hl3 : l 3 = (1 - a) * (1 - v0) := hv1.symm
  have hbin : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → renyiSpec qb ![x, 1 - x] = 4 * x * (1 - x) →
      x = 0 ∨ x = 1 / 2 ∨ x = 1 := fun x hx0 hx1 h => (renyi_binary_eq_iff hx0 hx1).mp h
  have hGH : renyiSpec qb (Sum.elim (fun i : Fin 2 => a * ![u0, 1 - u0] i)
      (fun j : Fin 2 => (1 - a) * ![v0, 1 - v0] j))
      = 4 * a * (1 - a) + wf a * (4 * u0 * (1 - u0)) + (1 - wf a) * (4 * v0 * (1 - v0)) :=
    hE.trans hEq.symm
  have hu_eq : wf a * renyiSpec qb ![u0, 1 - u0] = wf a * (4 * u0 * (1 - u0)) := by linarith
  have hv_eq : (1 - wf a) * renyiSpec qb ![v0, 1 - v0] = (1 - wf a) * (4 * v0 * (1 - v0)) := by
    linarith
  rcases eq_or_lt_of_le ha0 with h0 | h0
  · -- a = 0
    have hl0' : l 0 = 0 := by rw [hl0, ← h0]; ring
    have hl1' : l 1 = 0 := by rw [hl1, ← h0]; ring
    have ha0' : wf a = 0 := by rw [← h0]; unfold wf; norm_num
    have hveq : renyiSpec qb ![v0, 1 - v0] = 4 * v0 * (1 - v0) := by
      rw [ha0'] at hv_eq; linarith
    have hl2' : l 2 = v0 := by rw [hl2, ← h0]; ring
    have hl3' : l 3 = 1 - v0 := by rw [hl3, ← h0]; ring
    rcases hbin v0 hv0a hv0b hveq with h | h | h <;>
      · apply PureOrUniform.mk'
        rw [hl0', hl1', hl2', hl3', h]; norm_num
  rcases eq_or_lt_of_le ha1 with h1 | h1
  · -- a = 1
    have hl2' : l 2 = 0 := by rw [hl2, h1]; ring
    have hl3' : l 3 = 0 := by rw [hl3, h1]; ring
    have hw1' : wf a = 1 := by rw [h1]; unfold wf; norm_num
    have hueq : renyiSpec qb ![u0, 1 - u0] = 4 * u0 * (1 - u0) := by
      rw [hw1'] at hu_eq; linarith
    have hl0' : l 0 = u0 := by rw [hl0, h1]; ring
    have hl1' : l 1 = 1 - u0 := by rw [hl1, h1]; ring
    rcases hbin u0 hu0a hu0b hueq with h | h | h <;>
      · apply PureOrUniform.mk'
        rw [hl0', hl1', hl2', hl3', h]; norm_num
  -- 0 < a < 1
  have hw_pos : 0 < wf a := wf_pos h0 h1
  have hw_lt : wf a < 1 := wf_lt_one h0 h1
  have hueq : renyiSpec qb ![u0, 1 - u0] = 4 * u0 * (1 - u0) := by
    have := mul_left_cancel₀ hw_pos.ne' hu_eq; exact this
  have hveq : renyiSpec qb ![v0, 1 - v0] = 4 * v0 * (1 - v0) := by
    have hp : 0 < 1 - wf a := by linarith
    have := mul_left_cancel₀ hp.ne' hv_eq; exact this
  have hgeq : renyiSpec qb (Sum.elim (fun i : Fin 2 => a * ![u0, 1 - u0] i)
      (fun j : Fin 2 => (1 - a) * ![v0, 1 - v0] j))
      = 4 * a * (1 - a) + wf a * renyiSpec qb ![u0, 1 - u0] + (1 - wf a) * renyiSpec qb ![v0, 1 - v0] := by
    rw [hGH, hueq, hveq]
  obtain ⟨ha12, hHuv⟩ := (renyi_grouping_eq_iff hupos hvpos hus hvs h0 h1).mp hgeq
  rw [hueq, hveq] at hHuv
  have hl0' : l 0 = u0 / 2 := by rw [hl0, ha12]; ring
  have hl1' : l 1 = (1 - u0) / 2 := by rw [hl1, ha12]; ring
  have hl2' : l 2 = v0 / 2 := by rw [hl2, ha12]; ring
  have hl3' : l 3 = (1 - v0) / 2 := by rw [hl3, ha12]; ring
  rcases hbin u0 hu0a hu0b hueq with hu | hu | hu <;>
    rcases hbin v0 hv0a hv0b hveq with hv | hv | hv <;>
    first
    | (exfalso; rw [hu, hv] at hHuv; norm_num at hHuv; done)
    | (apply PureOrUniform.mk'; rw [hl0', hl1', hl2', hl3', hu, hv]; norm_num)

/-- **`prop:fqe-cubic-bound`, equality case**: for `q ≥ q_b` and a four-point probability vector, equality
in `H_q(λ) ≤ 10/3 - 6 Σλ² + (8/3) Σλ³` holds exactly at pure, uniform-two and uniform-four spectra. -/
theorem renyi_cubic_eq_iff {q : ℝ} (hq : qb ≤ q) (l : Fin 4 → ℝ) (hl : ∀ i, 0 ≤ l i)
    (hs : ∑ i, l i = 1) :
    renyiSpec q l = 10 / 3 - 6 * ∑ i, l i ^ 2 + 8 / 3 * ∑ i, l i ^ 3 ↔ PureOrUniform l := by
  constructor
  · intro h
    have h1 := renyiSpec_anti one_lt_qb hq hl hs
    have h2 := renyi_cubic_bound_qb l hl hs
    exact pureOrUniform_of_cubic_eq_qb l hl hs (le_antisymm h2 (h ▸ h1))
  · exact renyi_cubic_eq_of_pureOrUniform (lt_of_lt_of_le one_lt_qb hq)

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.renyi_cubic_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyi_cubic_eq_iff

/-- info: 'FormalResearch.FourQubitEntropy.PaperECritical.renyi_grouping_eq_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms renyi_grouping_eq_iff

end FormalResearch.FourQubitEntropy.PaperECritical

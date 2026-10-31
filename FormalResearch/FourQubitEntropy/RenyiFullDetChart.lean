import FormalResearch.FourQubitEntropy.RenyiFullDetMono
import FormalResearch.FourQubitEntropy.RenyiFullProps

/-!
# `lem:fqe-renyi-determinant`: the chart reduction, proved

Paper E, `lem:fqe-renyi-determinant` (`sup_renyi.tex`, `sec:sup-determinant`).  `DetReduction`
(`RenyiFullProps.lean`) is proved here, without hypothesis:

* `Zmono` (`RenyiFullDetMono.lean`): at fixed `p, t` and `1 < q < 2`, `Σ λᵢ^q` is nonincreasing in the
  determinant (Stieltjes representation);
* `lift_det`: a sorted spectrum `a > b ≥ c > e ≥ 0` (all four distinct, or the middle two equal) can be
  replaced, at the same `p, t`, by a sorted spectrum of strictly larger determinant: the quartic
  `∏(z - λᵢ) + δ` has four distinct real roots for small `δ > 0` (intermediate value theorem on the
  midpoints of the two gaps), and a cubic vanishing at four distinct points is zero (Vieta);
* `det_reduction`: a maximiser of the determinant on the compact set of sorted spectra with the given
  `p, t` has `c = e` (pattern `(a,b,c,c)`) or `a = b` (pattern `(a,a,b,c)`).
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open FormalResearch.FourQubitEntropy


theorem cubic_zero_of_four_roots {c0 c1 c2 c3 r1 r2 r3 r4 : ℝ}
    (h12 : r1 ≠ r2) (h13 : r1 ≠ r3) (h14 : r1 ≠ r4) (h23 : r2 ≠ r3) (h24 : r2 ≠ r4) (h34 : r3 ≠ r4)
    (e1 : c3 * r1 ^ 3 + c2 * r1 ^ 2 + c1 * r1 + c0 = 0)
    (e2 : c3 * r2 ^ 3 + c2 * r2 ^ 2 + c1 * r2 + c0 = 0)
    (e3 : c3 * r3 ^ 3 + c2 * r3 ^ 2 + c1 * r3 + c0 = 0)
    (e4 : c3 * r4 ^ 3 + c2 * r4 ^ 2 + c1 * r4 + c0 = 0) :
    c3 = 0 ∧ c2 = 0 ∧ c1 = 0 ∧ c0 = 0 := by
  have s12 : r1 - r2 ≠ 0 := sub_ne_zero.2 h12
  have s13 : r1 - r3 ≠ 0 := sub_ne_zero.2 h13
  have s14 : r1 - r4 ≠ 0 := sub_ne_zero.2 h14
  have s23 : r2 - r3 ≠ 0 := sub_ne_zero.2 h23
  have s24 : r2 - r4 ≠ 0 := sub_ne_zero.2 h24
  have s34 : r3 - r4 ≠ 0 := sub_ne_zero.2 h34
  -- first divided differences
  have q12 : c3 * (r1 ^ 2 + r1 * r2 + r2 ^ 2) + c2 * (r1 + r2) + c1 = 0 := by
    apply mul_left_cancel₀ s12; linear_combination e1 - e2
  have q23 : c3 * (r2 ^ 2 + r2 * r3 + r3 ^ 2) + c2 * (r2 + r3) + c1 = 0 := by
    apply mul_left_cancel₀ s23; linear_combination e2 - e3
  have q34 : c3 * (r3 ^ 2 + r3 * r4 + r4 ^ 2) + c2 * (r3 + r4) + c1 = 0 := by
    apply mul_left_cancel₀ s34; linear_combination e3 - e4
  -- second divided differences
  have t1 : c3 * (r1 + r2 + r3) + c2 = 0 := by
    apply mul_left_cancel₀ s13; linear_combination q12 - q23
  have t2 : c3 * (r2 + r3 + r4) + c2 = 0 := by
    apply mul_left_cancel₀ s24; linear_combination q23 - q34
  have hc3 : c3 = 0 := by
    apply mul_left_cancel₀ s14; linear_combination t1 - t2
  have hc2 : c2 = 0 := by rw [hc3] at t1; linarith
  have hc1 : c1 = 0 := by rw [hc3, hc2] at q12; linarith
  have hc0 : c0 = 0 := by rw [hc3, hc2, hc1] at e1; linarith
  exact ⟨hc3, hc2, hc1, hc0⟩

theorem exists_root_dec {g : ℝ → ℝ} (hg : Continuous g) {x y : ℝ} (hxy : x < y) (hx : 0 < g x)
    (hy : g y < 0) : ∃ r, x < r ∧ r < y ∧ g r = 0 := by
  have := intermediate_value_Icc' hxy.le hg.continuousOn
  obtain ⟨r, hr, hr0⟩ := this ⟨hy.le, hx.le⟩ |> fun h => by simpa using h
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_, hr0⟩
  · intro h; rw [← h] at hr0; linarith
  · intro h; rw [h] at hr0; linarith

theorem exists_root_inc {g : ℝ → ℝ} (hg : Continuous g) {x y : ℝ} (hxy : x < y) (hx : g x < 0)
    (hy : 0 < g y) : ∃ r, x < r ∧ r < y ∧ g r = 0 := by
  have := intermediate_value_Icc hxy.le hg.continuousOn
  obtain ⟨r, hr, hr0⟩ := this ⟨hx.le, hy.le⟩ |> fun h => by simpa using h
  refine ⟨r, lt_of_le_of_ne hr.1 ?_, lt_of_le_of_ne hr.2 ?_, hr0⟩
  · intro h; rw [← h] at hr0; linarith
  · intro h; rw [h] at hr0; linarith

/-- Lifting the quartic: four distinct roots `r₁ > r₂ > r₃ > r₄ > e` after adding a small `δ`. -/
theorem lift_roots {a b c e : ℝ} (hab : b < a) (hbc : c ≤ b) (hce : e < c) :
    ∃ δ r1 r2 r3 r4 : ℝ, 0 < δ ∧ r2 < r1 ∧ r3 < r2 ∧ r4 < r3 ∧ e < r4 ∧
      (r1 - a) * (r1 - b) * (r1 - c) * (r1 - e) + δ = 0 ∧
      (r2 - a) * (r2 - b) * (r2 - c) * (r2 - e) + δ = 0 ∧
      (r3 - a) * (r3 - b) * (r3 - c) * (r3 - e) + δ = 0 ∧
      (r4 - a) * (r4 - b) * (r4 - c) * (r4 - e) + δ = 0 := by
  set g0 : ℝ → ℝ := fun z => (z - a) * (z - b) * (z - c) * (z - e) with hg0
  have m1 : g0 ((a + b) / 2) < 0 := by
    simp only [hg0]
    have h1 : ((a + b) / 2 - a) < 0 := by linarith
    have h2 : 0 < ((a + b) / 2 - b) := by linarith
    have h3 : 0 < ((a + b) / 2 - c) := by linarith
    have h4 : 0 < ((a + b) / 2 - e) := by linarith
    have := mul_pos (mul_pos h2 h3) h4
    nlinarith
  have m2 : g0 ((c + e) / 2) < 0 := by
    simp only [hg0]
    have h1 : ((c + e) / 2 - a) < 0 := by linarith
    have h2 : ((c + e) / 2 - b) < 0 := by linarith
    have h3 : ((c + e) / 2 - c) < 0 := by linarith
    have h4 : 0 < ((c + e) / 2 - e) := by linarith
    have p12 := mul_pos_of_neg_of_neg h1 h2
    have p34 := mul_neg_of_neg_of_pos h3 h4
    have := mul_neg_of_pos_of_neg p12 p34
    nlinarith
  set δ : ℝ := min (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2)) / 2 with hδ
  have hδ0 : 0 < δ := by
    have := lt_min (neg_pos.2 m1) (neg_pos.2 m2)
    rw [hδ]; linarith
  have hδ1 : g0 ((a + b) / 2) + δ < 0 := by
    have := min_le_left (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2))
    have := min_le_right (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2))
    have h' : 0 < min (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2)) := lt_min (neg_pos.2 m1) (neg_pos.2 m2)
    rw [hδ]; linarith
  have hδ2 : g0 ((c + e) / 2) + δ < 0 := by
    have := min_le_left (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2))
    have := min_le_right (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2))
    have h' : 0 < min (-g0 ((a + b) / 2)) (-g0 ((c + e) / 2)) := lt_min (neg_pos.2 m1) (neg_pos.2 m2)
    rw [hδ]; linarith
  set g : ℝ → ℝ := fun z => g0 z + δ with hg
  have hcont : Continuous g := by
    simp only [hg, hg0]; fun_prop
  have ga : g a = δ := by simp [hg, hg0]
  have gb : g b = δ := by simp [hg, hg0]
  have gc : g c = δ := by simp [hg, hg0]
  have ge : g e = δ := by simp [hg, hg0]
  have gm1 : g ((a + b) / 2) < 0 := hδ1
  have gm2 : g ((c + e) / 2) < 0 := hδ2
  obtain ⟨r1, h1a, h1b, h1c⟩ := exists_root_inc hcont (by linarith : (a + b) / 2 < a) gm1 (by rw [ga]; exact hδ0)
  obtain ⟨r2, h2a, h2b, h2c⟩ := exists_root_dec hcont (by linarith : b < (a + b) / 2) (by rw [gb]; exact hδ0) gm1
  obtain ⟨r3, h3a, h3b, h3c⟩ := exists_root_inc hcont (by linarith : (c + e) / 2 < c) gm2 (by rw [gc]; exact hδ0)
  obtain ⟨r4, h4a, h4b, h4c⟩ := exists_root_dec hcont (by linarith : e < (c + e) / 2) (by rw [ge]; exact hδ0) gm2
  refine ⟨δ, r1, r2, r3, r4, hδ0, by linarith, by linarith, by linarith, by linarith, h1c, h2c, h3c, h4c⟩

/-- Sorted (antitone) four-point vectors. -/
def Sorted4 (l : Fin 4 → ℝ) : Prop := l 1 ≤ l 0 ∧ l 2 ≤ l 1 ∧ l 3 ≤ l 2

theorem lift_det {a b c e : ℝ} (hab : b < a) (hbc : c ≤ b) (hce : e < c) (he : 0 ≤ e)
    (hs : a + b + c + e = 1) :
    ∃ ν : Fin 4 → ℝ, IsProb4 ν ∧ Sorted4 ν ∧ pur ν = pur ![a, b, c, e] ∧
      cub ν = cub ![a, b, c, e] ∧ det4 ![a, b, c, e] < det4 ν := by
  obtain ⟨δ, r1, r2, r3, r4, hδ, o12, o23, o34, o4e, g1, g2, g3, g4⟩ := lift_roots hab hbc hce
  have key := cubic_zero_of_four_roots (c3 := (r1 + r2 + r3 + r4) - (a + b + c + e))
    (c2 := (a * b + a * c + a * e + b * c + b * e + c * e) -
      (r1 * r2 + r1 * r3 + r1 * r4 + r2 * r3 + r2 * r4 + r3 * r4))
    (c1 := (r1 * r2 * r3 + r1 * r2 * r4 + r1 * r3 * r4 + r2 * r3 * r4) -
      (a * b * c + a * b * e + a * c * e + b * c * e))
    (c0 := (a * b * c * e + δ) - r1 * r2 * r3 * r4)
    (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linear_combination g1) (by linear_combination g2) (by linear_combination g3)
    (by linear_combination g4)
  obtain ⟨k3, k2, k1, k0⟩ := key
  have hr4 : 0 < r4 := by linarith
  refine ⟨![r1, r2, r3, r4], ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp <;> linarith
  · simp [Fin.sum_univ_four]; linarith
  · simp; linarith
  · simp; linarith
  · simp; linarith
  · unfold pur; simp only [Fin.sum_univ_four]; simp
    linear_combination ((r1 + r2 + r3 + r4) + (a + b + c + e)) * k3 - 2 * (-k2)
  · unfold cub; simp only [Fin.sum_univ_four]; simp
    linear_combination ((r1 + r2 + r3 + r4) ^ 2 + (r1 + r2 + r3 + r4) * (a + b + c + e) +
      (a + b + c + e) ^ 2 - 3 * (a * b + a * c + a * e + b * c + b * e + c * e)) * k3
      + 3 * (r1 + r2 + r3 + r4) * k2 + 3 * k1
  · unfold det4; simp
    linarith


/-! ### Sorting and the compact set of sorted spectra -/

theorem exists_sorted4 (l : Fin 4 → ℝ) : ∃ σ : Equiv.Perm (Fin 4), Sorted4 (l ∘ σ) := by
  refine ⟨Tuple.sort (fun i => -l i), ?_⟩
  have hm := Tuple.monotone_sort (fun i => -l i)
  have h01 := hm (show (0 : Fin 4) ≤ 1 by decide)
  have h12 := hm (show (1 : Fin 4) ≤ 2 by decide)
  have h23 := hm (show (2 : Fin 4) ≤ 3 by decide)
  simp only [Function.comp_apply] at h01 h12 h23
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Function.comp_apply] <;> linarith

theorem pur_perm (l : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) : pur (l ∘ σ) = pur l := by
  unfold pur; exact Equiv.sum_comp σ (fun i => l i ^ 2)

theorem cub_perm (l : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) : cub (l ∘ σ) = cub l := by
  unfold cub; exact Equiv.sum_comp σ (fun i => l i ^ 3)

theorem det4_perm (l : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) : det4 (l ∘ σ) = det4 l := by
  have e : ∀ m : Fin 4 → ℝ, det4 m = ∏ i, m i := by
    intro m; unfold det4; simp [Fin.prod_univ_four, mul_assoc]
  rw [e, e]; exact Equiv.prod_comp σ l

theorem sum_rpow_perm (l : Fin 4 → ℝ) (σ : Equiv.Perm (Fin 4)) (q : ℝ) :
    ∑ i, (l ∘ σ) i ^ q = ∑ i, l i ^ q := Equiv.sum_comp σ (fun i => l i ^ q)

theorem isProb4_perm {l : Fin 4 → ℝ} (h : IsProb4 l) (σ : Equiv.Perm (Fin 4)) : IsProb4 (l ∘ σ) :=
  ⟨fun i => h.1 _, by rw [show ∑ i, (l ∘ σ) i = ∑ i, l i from Equiv.sum_comp σ l]; exact h.2⟩

/-- The compact set of sorted spectra with prescribed `p, t`. -/
def sortedK (p t : ℝ) : Set (Fin 4 → ℝ) :=
  {m | IsProb4 m ∧ Sorted4 m ∧ pur m = p ∧ cub m = t}

theorem continuous_pur : Continuous pur := by
  unfold pur; fun_prop

theorem continuous_cub : Continuous cub := by
  unfold cub; fun_prop

theorem continuous_det4 : Continuous det4 := by
  unfold det4; fun_prop

theorem isCompact_sortedK (p t : ℝ) : IsCompact (sortedK p t) := by
  apply isCompact_simplex4.of_isClosed_subset
  · have : sortedK p t = {m | IsProb4 m} ∩ ({m : Fin 4 → ℝ | m 1 ≤ m 0} ∩ {m | m 2 ≤ m 1} ∩
        {m | m 3 ≤ m 2} ∩ {m | pur m = p} ∩ {m | cub m = t}) := by
      ext m; simp only [sortedK, Sorted4, Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
    rw [this]
    have hs : IsClosed {m : Fin 4 → ℝ | IsProb4 m} := by
      have : {m : Fin 4 → ℝ | IsProb4 m} = simplex4 := rfl
      rw [this]; exact isCompact_simplex4.isClosed
    refine hs.inter ?_
    refine ((((isClosed_le (continuous_apply 1) (continuous_apply 0)).inter
      (isClosed_le (continuous_apply 2) (continuous_apply 1))).inter
      (isClosed_le (continuous_apply 3) (continuous_apply 2))).inter
      (isClosed_eq continuous_pur continuous_const)).inter
      (isClosed_eq continuous_cub continuous_const)
  · intro m hm; exact hm.1

/-- A determinant-maximiser of the sorted spectra with prescribed `(p, t)` has a repeated pair at
the top or at the bottom. -/
theorem maximiser_chart {p t : ℝ} {m : Fin 4 → ℝ} (hm : m ∈ sortedK p t)
    (hmax : ∀ m' ∈ sortedK p t, det4 m' ≤ det4 m) : m 2 = m 3 ∨ m 0 = m 1 := by
  obtain ⟨⟨h0, hs⟩, ⟨s1, s2, s3⟩, hp, ht⟩ := hm
  by_contra hcon
  push Not at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hab : m 1 < m 0 := lt_of_le_of_ne s1 (fun h => hne2 h.symm)
  have hce : m 3 < m 2 := lt_of_le_of_ne s3 (fun h => hne1 h.symm)
  have hvec : m = ![m 0, m 1, m 2, m 3] := by
    funext i; fin_cases i <;> simp
  have hsum : m 0 + m 1 + m 2 + m 3 = 1 := by simpa [Fin.sum_univ_four] using hs
  obtain ⟨ν, hν, hνs, hνp, hνt, hνd⟩ := lift_det hab s2 hce (h0 3) hsum
  have hmem : ν ∈ sortedK p t := ⟨hν, hνs, by rw [hνp, ← hvec]; exact hp, by rw [hνt, ← hvec]; exact ht⟩
  have := hmax ν hmem
  rw [← hvec] at hνd
  linarith

/-- **`lem:fqe-renyi-determinant`**, the chart reduction used by the classical relaxation: for
`1 < q < 2`, every four-point spectrum has a sorted spectrum of pattern `(a,b,c,c)` or `(a,a,b,c)` with
the same `p, t` and no smaller `H_q`. -/
theorem det_reduction : DetReduction := by
  intro q h1 h2 l hl
  obtain ⟨σ, hσ⟩ := exists_sorted4 l
  have hl0 := isProb4_perm hl σ
  have hmem0 : (l ∘ σ) ∈ sortedK (pur l) (cub l) :=
    ⟨hl0, hσ, pur_perm l σ, cub_perm l σ⟩
  obtain ⟨m, hmK, hmmax⟩ := (isCompact_sortedK (pur l) (cub l)).exists_isMaxOn ⟨_, hmem0⟩
    continuous_det4.continuousOn
  have hmax : ∀ m' ∈ sortedK (pur l) (cub l), det4 m' ≤ det4 m := fun m' hm' => hmmax hm'
  obtain ⟨⟨h0, hs⟩, ⟨s1, s2, s3⟩, hp, ht⟩ := hmK
  have hdet : det4 l ≤ det4 m := by
    have := hmax _ hmem0
    rwa [det4_perm] at this
  have hZ : ∑ i, m i ^ q ≤ ∑ i, l i ^ q := by
    apply Zmono h1 h2 hl ⟨h0, hs⟩ hp.symm ht.symm hdet
  refine ⟨m, ⟨⟨h0, hs⟩, ?_⟩, hp, ht, ?_⟩
  · rcases maximiser_chart ⟨⟨h0, hs⟩, ⟨s1, s2, s3⟩, hp, ht⟩ hmax with h | h
    · refine ⟨m 0, m 1, m 2, h0 2, s2, s1, Or.inl ?_⟩
      funext i; fin_cases i <;> simp [h]
    · refine ⟨m 0, m 2, m 3, h0 3, s3, s2.trans s1, Or.inr ?_⟩
      funext i; fin_cases i <;> simp [h]
  · unfold renyiSpec
    have hlpos : 0 < ∑ i, l i ^ q := sum_rpow_pos hl.1 hl.2
    have hmpos : 0 < ∑ i, m i ^ q := sum_rpow_pos h0 hs
    have hlog : Real.logb 2 (∑ i, m i ^ q) ≤ Real.logb 2 (∑ i, l i ^ q) :=
      Real.logb_le_logb_of_le (by norm_num) hmpos hZ
    exact div_le_div_of_nonpos_of_le (by linarith) hlog


/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.Zmono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Zmono

/-- info: 'FormalResearch.FourQubitEntropy.RenyiFull.det_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms det_reduction

end FormalResearch.FourQubitEntropy.RenyiFull

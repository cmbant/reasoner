import FormalResearch.FourQubitEntropy.PaperEGapSignedPerm
import FormalResearch.FourQubitEntropy.PaperETwoFlatEq
import FormalResearch.FourQubitEntropy.RenyiRankTwoSharp
import FormalResearch.FourQubitEntropy.PaperEGapCutLU

/-!
# `prop:fqe-two-flat-rigidity`: identification with the cluster-to-Bell family (QF)

Paper E, `renyi_uncapped_reduction.tex`.  A unit pure four-qubit state with two maximally mixed balanced
cuts (purity `1/4`) has, in a critical normal form `ψ ≃ G(v)`, the third cut with amplitudes `w ∈ {v, H₊v,
H₋v}` satisfying `|Σ w_k²|² = 2 Σ|w_k|⁴ - 1`, the equality case `Δ_k = 0` of `(TF)`.

* `two_sparse_QF`: such a `w` has two nonzero entries of opposite-phase squares, hence `G(w)` is locally
  unitarily equivalent to `G(x, i y, 0, 0) = ψ_{x,y}` (`quadFam_eq_Gv`, signed permutations of the magic
  diagonal: `PaperEGapSignedPerm.lean`);
* `two_flat_QF_12_13`, `two_flat_QF_12_14`, `two_flat_QF_13_14`, `two_flat_QF`: `ψ` is, up to `LUEquiv` and
  the exchange of qubits `2,3` or `2,4` (a permutation of the three cuts), the family
  `eq:fqe-quadratic-family`, with `x² ≥ 1/2`;
* `quadFam_two_flat`: conversely both crossed cuts of `ψ_{x,y}` have purity `1/4`;
* `renyi_of_QF`, `two_flat_renyi`: the exact Rényi envelope of `prop:fqe-renyi-rank-two` for all `q > 0`,
  `E_q = 4/3 + H_q(a,1-a)/3 ≤ 5/3`, `a = x²`.
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.PaperECritical
open FormalResearch.FourQubitEntropy

set_option maxHeartbeats 4000000 in
theorem quadFam_eq_Gv (x y : ℝ) : quadFam x y = Gv (qfVec x y) := by
  have hrt2 : rt ^ 2 = 1 / 2 := by rw [pow_two]; exact rt_mul_rt
  have hI3 : Complex.I ^ 3 = -Complex.I := by
    rw [pow_succ, Complex.I_sq]; ring
  funext a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
  simp [quadFam, Gv, ofZmat, qfVec, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    magicB, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
  first | done | linear_combination (-(x : ℂ)) * hrt2 |
    (ring_nf; simp only [hrt2, hI3]; ring)

theorem three_zero (p q r : ℝ) (pq : p * q = 0) (pr : p * r = 0) (qr : q * r = 0) :
    (q = 0 ∧ r = 0) ∨ (p = 0 ∧ r = 0) ∨ (p = 0 ∧ q = 0) := by
  by_cases hp : p = 0
  · by_cases hq : q = 0
    · exact Or.inr (Or.inr ⟨hp, hq⟩)
    · exact Or.inr (Or.inl ⟨hp, (mul_eq_zero.mp qr).resolve_left hq⟩)
  · exact Or.inl ⟨(mul_eq_zero.mp pq).resolve_left hp, (mul_eq_zero.mp pr).resolve_left hp⟩

/-- At most one entry besides the largest is nonzero (from the vanishing of `2 e₂`). -/
theorem exists_single_other (w : Ix → ℂ) (i : Ix)
    (hcc : crossCost w i ≤ 0) : ∃ jj, jj ≠ i ∧ ∀ m, m ≠ i → m ≠ jj → Complex.normSq (w m) = 0 := by
  obtain ⟨j, k, l, hj, hk, hl, hjk, hjl, hkl⟩ := exists_three_others i
  rw [crossCost_eq w i j k l hj hk hl hjk hjl hkl] at hcc
  have a1 := Complex.normSq_nonneg (w j)
  have a2 := Complex.normSq_nonneg (w k)
  have a3 := Complex.normSq_nonneg (w l)
  have p1 : Complex.normSq (w j) * Complex.normSq (w k) = 0 := by
    nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]
  have p2 : Complex.normSq (w j) * Complex.normSq (w l) = 0 := by
    nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]
  have p3 : Complex.normSq (w k) * Complex.normSq (w l) = 0 := by
    nlinarith [mul_nonneg a1 a2, mul_nonneg a1 a3, mul_nonneg a2 a3]
  have hm : ∀ m, m ≠ i → m = j ∨ m = k ∨ m = l := fun m hm => by
    have := Finset.mem_erase.mpr ⟨hm, Finset.mem_univ m⟩
    rw [univ_erase_eq i j k l hj hk hl hjk hjl hkl] at this
    simpa using this
  rcases three_zero _ _ _ p1 p2 p3 with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨j, hj, fun m hmi hmj => ?_⟩
    rcases hm m hmi with rfl | rfl | rfl
    · exact absurd rfl hmj
    · exact h1
    · exact h2
  · refine ⟨k, hk, fun m hmi hmk => ?_⟩
    rcases hm m hmi with rfl | rfl | rfl
    · exact h1
    · exact absurd rfl hmk
    · exact h2
  · refine ⟨l, hl, fun m hml hmi => ?_⟩
    rcases hm m hml with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact absurd rfl hmi

/-- **The cluster-to-Bell normal form (scalar-to-LU core).**  A unit vector `w` of cut amplitudes whose
squares satisfy the crossed-purity identity `|Σ w_k²|² = 2 Σ|w_k|⁴ - 1` (the case `Δ_k = 0` of `(TF)`)
gives a state `G(w)` in the orbit of `G(x, i y, 0, 0)` with `x² + y² = 1`, `x² ≥ 1/2`. -/
theorem two_sparse_QF (w : Ix → ℂ) (hn : ∑ k, Complex.normSq (w k) = 1)
    (hτ : Complex.normSq (∑ k, w k ^ 2) = 2 * ∑ k, Complex.normSq (w k) ^ 2 - 1) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ 1 / 2 ≤ x ^ 2 ∧ 0 ≤ y ∧ LUEquiv (quadFam x y) (Gv w) := by
  set p : ℝ := ∑ k, Complex.normSq (w k) ^ 2 with hp
  have hτ0 := Complex.normSq_nonneg (∑ k, w k ^ 2)
  obtain ⟨i, hi⟩ := exists_big_entry w hn (by linarith)
  have core := two_flat_core w hn (p + 1 / 2) (by linarith) i hi
  have hcc : crossCost w i ≤ 0 := by unfold crossCost; linarith
  have h2 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (w j) = 1 - Complex.normSq (w i) := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hn]
  have h3 : ∑ j ∈ Finset.univ.erase i, Complex.normSq (w j) ^ 2 = p - Complex.normSq (w i) ^ 2 := by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  have hcc' : crossCost w i = (1 - Complex.normSq (w i)) ^ 2 - (p - Complex.normSq (w i) ^ 2) := by
    unfold crossCost; rw [h2, h3]
  have hcc0 : 0 ≤ crossCost w i := by
    obtain ⟨j, k, l, hj, hk, hl, hjk, hjl, hkl⟩ := exists_three_others i
    rw [crossCost_eq w i j k l hj hk hl hjk hjl hkl]
    have a1 := Complex.normSq_nonneg (w j)
    have a2 := Complex.normSq_nonneg (w k)
    have a3 := Complex.normSq_nonneg (w l)
    positivity
  have hlow := tau_lower w hn i hi
  have heq : Complex.normSq (∑ k, w k ^ 2) = (2 * Complex.normSq (w i) - 1) ^ 2 := by
    nlinarith
  have hopp := (tau_eq_iff w hn i hi).mp heq
  obtain ⟨jj, hjj, hz⟩ := exists_single_other w i hcc
  set a : ℝ := Complex.normSq (w i) with ha
  set b : ℝ := Complex.normSq (w jj) with hb
  have hab : a + b = 1 := by
    rw [← hn, Finset.sum_eq_add i jj (Ne.symm hjj)]
    · intro m _ hm
      exact hz m hm.1 hm.2
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro h; exact absurd (Finset.mem_univ _) h
  have hapos : 0 < a := by linarith
  have hb0 : 0 ≤ b := Complex.normSq_nonneg _
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt a := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = Real.sqrt b := ⟨_, rfl⟩
  have hx2 : x ^ 2 = a := by rw [hx]; exact Real.sq_sqrt hapos.le
  have hy2 : y ^ 2 = b := by rw [hy]; exact Real.sq_sqrt hb0
  have hy0 : 0 ≤ y := by rw [hy]; exact Real.sqrt_nonneg _
  have hxne : x ≠ 0 := fun h => by rw [h] at hx2; linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hxne
  obtain ⟨c, hcdef⟩ : ∃ c : ℂ, c = w i / x := ⟨_, rfl⟩
  have hwi : w i = c * x := by rw [hcdef]; field_simp
  have hc : (starRingEnd ℂ) c * c = 1 := by
    have : Complex.normSq c = 1 := by
      rw [hcdef, map_div₀, Complex.normSq_ofReal, ← ha]
      field_simp; nlinarith
    rw [← Complex.normSq_eq_conj_mul_self, this]; simp
  obtain ⟨t, ht0, ht⟩ := hopp jj hjj
  have hnorm : ∀ k, ‖w k ^ 2‖ = Complex.normSq (w k) := fun k => by
    rw [norm_pow, Complex.normSq_eq_norm_sq]
  have hbt : b = t * a := by
    have := congrArg norm ht
    rw [hnorm jj, norm_mul, norm_neg, Complex.norm_real, hnorm i,
      Real.norm_of_nonneg ht0] at this
    exact this
  have htb : (t : ℂ) * (a : ℂ) = (b : ℂ) := by exact_mod_cast hbt.symm
  have hsq : w jj ^ 2 = (c * Complex.I * y) ^ 2 := by
    have hy2C : (y : ℂ) ^ 2 = (b : ℂ) := by exact_mod_cast hy2
    have hx2C : (x : ℂ) ^ 2 = (a : ℂ) := by exact_mod_cast hx2
    rw [ht, hwi]
    calc -(t : ℂ) * (c * x) ^ 2 = -(c ^ 2) * ((t : ℂ) * (x : ℂ) ^ 2) := by ring
      _ = -(c ^ 2) * (b : ℂ) := by rw [hx2C, htb]
      _ = _ := by rw [mul_pow, mul_pow, hy2C, Complex.I_sq]; ring
  obtain ⟨sg, hsg, hwj⟩ : ∃ sg : ℝ, sg ^ 2 = 1 ∧ w jj = c * (sg : ℂ) * Complex.I * (y : ℂ) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨1, by norm_num, by rw [h]; simp⟩
    · exact ⟨-1, by norm_num, by rw [h]; simp⟩
  have hw : w = pairVec i jj c x y sg := by
    funext m
    by_cases hmi : m = i
    · subst hmi; simp [pairVec, hwi]
    · by_cases hmj : m = jj
      · subst hmj; simp [pairVec, hmi, hwj]
      · have := hz m hmi hmj
        simp [pairVec, hmi, hmj, Complex.normSq_eq_zero.mp this]
  refine ⟨x, y, by rw [hx2, hy2]; linarith, by rw [hx2]; linarith, hy0, ?_⟩
  rw [quadFam_eq_Gv, hw]
  exact LU_pair i jj (Ne.symm hjj) c hc x y sg hsg

/-- The crossed-purity identity in normal-form coordinates: `|Σ v_k²|² = 2 P - 2` with `P` the sum of the
three cut purities of `G(v)`. -/
theorem tau_eq_purity (v : Ix → ℂ) (hn : ∑ k, Complex.normSq (v k) = 1) :
    Complex.normSq (∑ k, v k ^ 2) =
      2 * (∑ k, Complex.normSq (v k) ^ 2 + ∑ k, Complex.normSq (wp v k) ^ 2 +
        ∑ k, Complex.normSq (wm v k) ^ 2) - 2 := by
  have hP := Gv_purity_tau v hn
  obtain ⟨c12, c13, c14⟩ := Gv_cutPurities v
  have hsum : purity (Gv v) = cutPurity12 (Gv v) + cutPurity13 (Gv v) + cutPurity14 (Gv v) := rfl
  rw [c12, c13, c14] at hsum
  linarith

theorem cutPurity12_swap24 (ψ : Psi) : cutPurity12 (swap24 ψ) = cutPurity14 ψ := by
  unfold cutPurity12 cutPurity14; rw [red14_eq_swap]

theorem cutPurity13_swap24 (ψ : Psi) : cutPurity13 (swap24 ψ) = cutPurity13 ψ := by
  unfold cutPurity13; rw [red13_swap24]

/-- **`prop:fqe-two-flat-rigidity`, identification with the cluster-to-Bell family (QF)**, cuts `12|34`
and `13|24` maximally mixed: up to local unitaries and the exchange of qubits `2,4` (which
interchanges the cuts `12|34` and `14|23`), `ψ` is the state `ψ_{x,y}` of `eq:fqe-quadratic-family`
(`quadFam x y`, the critical normal form `v = (x, i y, 0, 0)`), with `x² ≥ 1/2` the top Schmidt weight of
the remaining cut `14|23`. -/
theorem two_flat_QF_12_13 (ψ : Psi) (hn : normSqPsi ψ = 1) (h12 : cutPurity12 ψ = 1 / 4)
    (h13 : cutPurity13 ψ = 1 / 4) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ 1 / 2 ≤ x ^ 2 ∧ 0 ≤ y ∧ LUEquiv (quadFam x y) (swap24 ψ) := by
  have hW := blochSq_zero_of_cutPurity12 ψ hn h12
  obtain ⟨v, hv⟩ := critical_LU_Gv ψ hW
  have hnv : ∑ k, Complex.normSq (v k) = 1 := by
    rw [← Gv_n, ← normSqPsi_LUEquiv hv]; exact hn
  obtain ⟨e12, e13, -⟩ := cutPurities_LUEquiv hv
  obtain ⟨c12, c13, -⟩ := Gv_cutPurities v
  have h1 : ∑ k, Complex.normSq (v k) ^ 2 = 1 / 4 := by rw [← c12, ← e12]; exact h12
  have h2 : ∑ k, Complex.normSq (wp v k) ^ 2 = 1 / 4 := by rw [← c13, ← e13]; exact h13
  have hτ := tau_eq_purity v hnv
  obtain ⟨x, y, hxy, hx, hy, hLU⟩ := two_sparse_QF (wm v) ((wm_normSq_sum v).trans hnv)
    (by rw [wm_sq_sum, hτ, h1, h2]; ring)
  refine ⟨x, y, hxy, hx, hy, ?_⟩
  rw [← swap24_Gv] at hLU
  exact hLU.trans (LUEquiv.swap24 hv)

/-- Cuts `12|34` and `14|23` maximally mixed: up to local unitaries and the exchange of qubits `2,3`
(which interchanges `12|34` and `13|24`), `ψ` is in (QF). -/
theorem two_flat_QF_12_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (h12 : cutPurity12 ψ = 1 / 4)
    (h14 : cutPurity14 ψ = 1 / 4) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ 1 / 2 ≤ x ^ 2 ∧ 0 ≤ y ∧ LUEquiv (quadFam x y) (swap23 ψ) := by
  have hW := blochSq_zero_of_cutPurity12 ψ hn h12
  obtain ⟨v, hv⟩ := critical_LU_Gv ψ hW
  have hnv : ∑ k, Complex.normSq (v k) = 1 := by
    rw [← Gv_n, ← normSqPsi_LUEquiv hv]; exact hn
  obtain ⟨e12, -, e14⟩ := cutPurities_LUEquiv hv
  obtain ⟨c12, -, c14⟩ := Gv_cutPurities v
  have h1 : ∑ k, Complex.normSq (v k) ^ 2 = 1 / 4 := by rw [← c12, ← e12]; exact h12
  have h3 : ∑ k, Complex.normSq (wm v k) ^ 2 = 1 / 4 := by rw [← c14, ← e14]; exact h14
  have hτ := tau_eq_purity v hnv
  obtain ⟨x, y, hxy, hx, hy, hLU⟩ := two_sparse_QF (wp v) ((wp_normSq_sum v).trans hnv)
    (by rw [wp_sq_sum, hτ, h1, h3]; ring)
  refine ⟨x, y, hxy, hx, hy, ?_⟩
  rw [← swap23_Gv] at hLU
  exact hLU.trans (LUEquiv.swap23 hv)

/-- Cuts `13|24` and `14|23` maximally mixed: `ψ` itself is (up to local unitaries) in (QF), with
the rank-two cut `12|34`. -/
theorem two_flat_QF_13_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (h13 : cutPurity13 ψ = 1 / 4)
    (h14 : cutPurity14 ψ = 1 / 4) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ 1 / 2 ≤ x ^ 2 ∧ 0 ≤ y ∧ LUEquiv (quadFam x y) ψ := by
  obtain ⟨x, y, hxy, hx, hy, hLU⟩ := two_flat_QF_12_13 (swap24 ψ) (by rw [normSqPsi_swap24]; exact hn)
    (by rw [cutPurity12_swap24]; exact h14) (by rw [cutPurity13_swap24]; exact h13)
  exact ⟨x, y, hxy, hx, hy, hLU⟩

/-- **Two maximally mixed cuts, any pair**: up to local unitaries and a permutation of the three cuts
(the identity, `swap23` or `swap24`), the state is `ψ_{x,y}` of `eq:fqe-quadratic-family`. -/
theorem two_flat_QF (ψ : Psi) (hn : normSqPsi ψ = 1)
    (h : (cutPurity12 ψ = 1 / 4 ∧ cutPurity13 ψ = 1 / 4) ∨ (cutPurity12 ψ = 1 / 4 ∧ cutPurity14 ψ = 1 / 4) ∨
      (cutPurity13 ψ = 1 / 4 ∧ cutPurity14 ψ = 1 / 4)) :
    ∃ x y : ℝ, x ^ 2 + y ^ 2 = 1 ∧ 1 / 2 ≤ x ^ 2 ∧ 0 ≤ y ∧
      (LUEquiv (quadFam x y) ψ ∨ LUEquiv (quadFam x y) (swap23 ψ) ∨ LUEquiv (quadFam x y) (swap24 ψ)) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨x, y, a, b, c, d⟩ := two_flat_QF_12_13 ψ hn h1 h2
    exact ⟨x, y, a, b, c, Or.inr (Or.inr d)⟩
  · obtain ⟨x, y, a, b, c, d⟩ := two_flat_QF_12_14 ψ hn h1 h2
    exact ⟨x, y, a, b, c, Or.inr (Or.inl d)⟩
  · obtain ⟨x, y, a, b, c, d⟩ := two_flat_QF_13_14 ψ hn h1 h2
    exact ⟨x, y, a, b, c, Or.inl d⟩

/-- Along (QF), `E_q = 4/3 + H_q(x², 1-x²)/3 ≤ 5/3` for every order `q > 0`, `q ≠ 1`, and the von Neumann
case; for any state in a local-unitary orbit of `ψ_{x,y}` or its qubit exchanges. -/
theorem renyi_of_QF {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) (hx : 1 / 2 ≤ x ^ 2) {φ : Psi}
    (h : LUEquiv (quadFam x y) φ ∨ LUEquiv (quadFam x y) (swap23 φ) ∨
      LUEquiv (quadFam x y) (swap24 φ)) :
    (∀ q : ℝ, 0 < q → q ≠ 1 →
      meanRenyi q φ = 4 / 3 + renyiBin q (x ^ 2) / 3 ∧ 4 / 3 + renyiBin q (x ^ 2) / 3 ≤ 5 / 3) ∧
    (meanEntropy φ = 4 / 3 + entBin (x ^ 2) / 3 ∧ 4 / 3 + entBin (x ^ 2) / 3 ≤ 5 / 3) := by
  have hx1 : x ^ 2 ≤ 1 := by nlinarith [sq_nonneg y]
  have hx0 : 0 ≤ x ^ 2 := by positivity
  have hR : ∀ q : ℝ, 0 < q → q ≠ 1 → meanRenyi q φ = 4 / 3 + renyiBin q (x ^ 2) / 3 := by
    intro q hq0 hq1
    have hs := (renyi_rank_two_sharp hq0 hq1 hxy).2
    rcases h with h | h | h
    · rw [meanRenyi_LU q h, hs]
    · rw [← meanRenyi_swap23, meanRenyi_LU q h, hs]
    · rw [← meanRenyi_swap24, meanRenyi_LU q h, hs]
  have hE : meanEntropy φ = 4 / 3 + entBin (x ^ 2) / 3 := by
    have hs := entropy_rank_two_sharp hxy
    rcases h with h | h | h
    · rw [meanEntropy_LU h, hs]
    · rw [← meanEntropy_swap23, meanEntropy_LU h, hs]
    · rw [← meanEntropy_swap24, meanEntropy_LU h, hs]
  refine ⟨fun q hq0 hq1 => ⟨hR q hq0 hq1, ?_⟩, hE, ?_⟩
  · have := renyiBin_le_one hq0 hq1 hx0 hx1; linarith
  · have := entBin_le_one hx0 hx1; linarith

/-- **`prop:fqe-two-flat-rigidity`, Rényi consequence**: a unit state with two maximally mixed balanced
cuts has the exact Rényi envelope of `prop:fqe-renyi-rank-two` for all `q > 0`:
`E_q = 4/3 + H_q(a, 1-a)/3 ≤ 5/3` for some `a ∈ [1/2, 1]` (and likewise for the von Neumann case). -/
theorem two_flat_renyi (ψ : Psi) (hn : normSqPsi ψ = 1)
    (h : (cutPurity12 ψ = 1 / 4 ∧ cutPurity13 ψ = 1 / 4) ∨ (cutPurity12 ψ = 1 / 4 ∧ cutPurity14 ψ = 1 / 4) ∨
      (cutPurity13 ψ = 1 / 4 ∧ cutPurity14 ψ = 1 / 4)) :
    ∃ a : ℝ, 1 / 2 ≤ a ∧ a ≤ 1 ∧
      (∀ q : ℝ, 0 < q → q ≠ 1 →
        meanRenyi q ψ = 4 / 3 + renyiBin q a / 3 ∧ 4 / 3 + renyiBin q a / 3 ≤ 5 / 3) ∧
      (meanEntropy ψ = 4 / 3 + entBin a / 3 ∧ 4 / 3 + entBin a / 3 ≤ 5 / 3) := by
  obtain ⟨x, y, hxy, hx, hy, hLU⟩ := two_flat_QF ψ hn h
  exact ⟨x ^ 2, hx, by nlinarith [sq_nonneg y], renyi_of_QF hxy hx hLU⟩

/-- Converse: along (QF) the cuts `13|24` and `14|23` are maximally mixed (purity `1/4`). -/
theorem quadFam_two_flat {x y : ℝ} (hxy : x ^ 2 + y ^ 2 = 1) :
    cutPurity13 (quadFam x y) = 1 / 4 ∧ cutPurity14 (quadFam x y) = 1 / 4 := by
  have h : ((x ^ 2 + y ^ 2) / 4 : ℝ) = 1 / 4 := by rw [hxy]
  refine ⟨?_, ?_⟩
  · unfold cutPurity13; rw [red13_quadFam, h]
    simp [Matrix.trace, Matrix.diag, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
  · unfold cutPurity14; rw [red14_quadFam, h]
    simp [Matrix.trace, Matrix.diag, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

end FormalResearch.FourQubitEntropy.PaperECritical

#print axioms FormalResearch.FourQubitEntropy.PaperECritical.quadFam_two_flat
#print axioms FormalResearch.FourQubitEntropy.PaperECritical.two_flat_QF
#print axioms FormalResearch.FourQubitEntropy.PaperECritical.two_flat_renyi
#print axioms FormalResearch.FourQubitEntropy.PaperECritical.two_flat_QF_12_13

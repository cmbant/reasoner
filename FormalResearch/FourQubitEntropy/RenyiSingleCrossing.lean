import FormalResearch.FourQubitEntropy.RenyiSingleCrossingVar

/-!
# Single crossing of the Rényi entropies: the lemma and the order transfer

Paper: `lem:fqe-renyi-single-crossing` (SX) and `cor:fqe-renyi-order-transfer`
(renyi_single_crossing.tex). **Both are proved, with no hypothesis.**

For `q > 1` and a four-point probability vector `l`: `v_q(l) - v_q(σ) ≤ κ_q (u_q(l) - u_q(σ))`, with
equality only for permutations of `σ = (1/2, 1/6, 1/6, 1/6)` (`single_crossing_statement`). The proof is
the paper's: maximise `φ = v_q - κ_q u_q` on the simplex.

* existence of a maximiser by compactness (`isCompact_simplex4`, `sxPhiVec_continuousOn`);
* a maximiser has full support (`IsSXMax.pos`: the right derivative of the mass transfer into a zero
  coordinate is `β > 0`, `RenyiSingleCrossingVar.lean`), satisfies `g(mᵢ) = g(mⱼ)` for the Lagrange
  function `g = g_C` (`IsSXMax.lagrange`) with common value `-βZ` (`IsSXMax.gval`);
* Rolle for `g`: `mᵢ < mⱼ` forces `B(mᵢ) < 0 < B(mⱼ)` for the bracket `B = g'/x^{q-2}`
  (`sxB_of_sxG_eq`); the second variation excludes two equal coordinates with `B > 0`
  (`IsSXMax.second_variation`, via a strictly monotone `g` on `[a-τ, a+τ]`, proved by a continuity
  argument for the Lagrange constant instead of a second derivative);
* hence a maximiser is uniform or a permutation of `(a, b, b, b)`; the one-large family lemma of
  `RenyiSingleCrossingFamily.lean` (`sxFamily_le`, `sxFamily_eq`) finishes (`IsSXMax.isHsPerm`).

Differences from the paper: the second variation `2g'(a)/Z > 0` is replaced by monotonicity of
`g_{C_τ}` on `[a-τ, a+τ]` for small `τ > 0` (the first variation is differentiated along the whole curve,
`sxPF_hasDerivAt`), which avoids a second derivative; the uniform vector is the case `z = 0` of the family.

Consequences, stated for four-point vectors and, for the three cut spectra of a unit four-qubit vector,
in terms of `meanRenyi` and `hsRenyi` (`meanRenyi_order_transfer`): `G_l` is nondecreasing on `(1, ∞)`
(`renyiG_monotoneOn_all`, strictly unless `l` is a permutation of `σ`, `renyiG_strictMonoOn_all`) and
`E_{q₁} ≤ h_{q₁} → E_q ≤ h_q` for `1 < q < q₁`, with the strict version and the equality case
(`renyi_order_transfer_all`).
-/

namespace FormalResearch.FourQubitEntropy

open Real Filter Topology

/-- `m` maximises `φ_q` over the simplex of four-point probability vectors. -/
def IsSXMax (q : ℝ) (m : Fin 4 → ℝ) : Prop :=
  IsProb4 m ∧ ∀ l : Fin 4 → ℝ, IsProb4 l → sxPhiVec q l ≤ sxPhiVec q m

/-- The Lagrange constant `C = 1 - q (v + κ)`. -/
noncomputable def sxC (q : ℝ) (m : Fin 4 → ℝ) : ℝ := 1 - q * (sxV q m + sxKappa q)

theorem sxV_perm (q : ℝ) (l : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) : sxV q (l ∘ e) = sxV q l := by
  unfold sxV
  rw [sxZ_perm]
  have := Equiv.sum_comp e (fun i => l i ^ q * Real.log (l i))
  simp only [Function.comp_apply]
  rw [this]

theorem sxC_perm (q : ℝ) (l : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) : sxC q (l ∘ e) = sxC q l := by
  unfold sxC; rw [sxV_perm]

theorem IsSXMax.perm {q : ℝ} {m : Fin 4 → ℝ} (hm : IsSXMax q m) (e : Equiv.Perm (Fin 4)) :
    IsSXMax q (m ∘ e) := by
  refine ⟨isProb4_perm hm.1 e, fun l hl => ?_⟩
  rw [sxPhiVec_perm]
  exact hm.2 l hl

theorem vec_eq_four (m : Fin 4 → ℝ) : m = ![m 0, m 1, m 2, m 3] := by
  funext i; fin_cases i <;> rfl

/-- `φ(m)` as a function of the first two coordinates. -/
theorem sxPhiVec_eq_PF (q : ℝ) (m : Fin 4 → ℝ) :
    sxPhiVec q m = sxPF q (sxh q (m 2) + sxh q (m 3)) (sxp q (m 2) + sxp q (m 3)) (m 0) (m 1) := by
  conv_lhs => rw [vec_eq_four m]
  exact sxPhiVec_four q _ _ _ _

theorem sxZ_eq_four (q : ℝ) (m : Fin 4 → ℝ) :
    sxZ q m = (sxp q (m 2) + sxp q (m 3)) + sxp q (m 0) + sxp q (m 1) := by
  unfold sxZ sxp
  simp only [Fin.sum_univ_four]; ring

theorem sxV_eq_four (q : ℝ) (m : Fin 4 → ℝ) :
    sxV q m = ((sxh q (m 2) + sxh q (m 3)) + sxh q (m 0) + sxh q (m 1)) / sxZ q m := by
  unfold sxV sxh
  congr 1
  simp only [Fin.sum_univ_four]; ring

/-- The transferred vector is admissible and has `φ` given by `sxPF`. -/
theorem IsSXMax.pair_le {q : ℝ} {m : Fin 4 → ℝ} (hm : IsSXMax q m) {τ : ℝ}
    (h0 : 0 ≤ m 0 + τ) (h1 : 0 ≤ m 1 - τ) :
    sxPF q (sxh q (m 2) + sxh q (m 3)) (sxp q (m 2) + sxp q (m 3)) (m 0 + τ) (m 1 - τ)
      ≤ sxPF q (sxh q (m 2) + sxh q (m 3)) (sxp q (m 2) + sxp q (m 3)) (m 0) (m 1) := by
  have hp : IsProb4 ![m 0 + τ, m 1 - τ, m 2, m 3] := by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i
      · simpa using h0
      · simpa using h1
      · exact hm.1.1 2
      · exact hm.1.1 3
    · have := hm.1.2
      simp only [Fin.sum_univ_four] at this ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.tail_cons]
      linarith
  have := hm.2 _ hp
  rw [sxPhiVec_four, sxPhiVec_eq_PF] at this
  exact this

theorem IsSXMax.lagrange01 {q : ℝ} {m : Fin 4 → ℝ} (hm : IsSXMax q m) (h0 : 0 < m 0) (h1 : 0 < m 1) :
    sxG q (sxC q m) (m 0) = sxG q (sxC q m) (m 1) := by
  have hZ : 0 < sxZ q m := sxZ_pos hm.1 q
  rw [sxZ_eq_four] at hZ
  have hd := sxPF_hasDerivAt q (sxh q (m 2) + sxh q (m 3)) (sxp q (m 2) + sxp q (m 3)) (m 0) (m 1) 0
    (by simpa using h0) (by simpa using h1) (by simpa using hZ)
  have hloc : IsLocalMax (fun τ => sxPF q (sxh q (m 2) + sxh q (m 3)) (sxp q (m 2) + sxp q (m 3))
      (m 0 + τ) (m 1 - τ)) 0 := by
    have hnb : Set.Ioo (-(min (m 0) (m 1))) (min (m 0) (m 1)) ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by have := lt_min h0 h1; linarith) (lt_min h0 h1)
    filter_upwards [hnb] with τ hτ
    have h2 := min_le_left (m 0) (m 1)
    have h3 := min_le_right (m 0) (m 1)
    have := hm.pair_le (τ := τ) (by linarith [hτ.1]) (by linarith [hτ.2])
    simpa using this
  have h0' := hloc.hasDerivAt_eq_zero hd
  have hZ' : sxp q (m 2) + sxp q (m 3) + sxp q (m 0 + 0) + sxp q (m 1 - 0) ≠ 0 := by
    simp only [add_zero, sub_zero]; exact hZ.ne'
  have hC : sxC q m = 1 - q * ((sxh q (m 2) + sxh q (m 3) + sxh q (m 0 + 0) + sxh q (m 1 - 0))
      / (sxp q (m 2) + sxp q (m 3) + sxp q (m 0 + 0) + sxp q (m 1 - 0)) + sxKappa q) := by
    unfold sxC; rw [sxV_eq_four, sxZ_eq_four]; simp only [add_zero, sub_zero]
  rw [← hC] at h0'
  simp only [add_zero, sub_zero] at h0'
  have := (div_eq_zero_iff.mp h0').resolve_right hZ.ne'
  linarith

theorem IsSXMax.lagrange {q : ℝ} {m : Fin 4 → ℝ} (hm : IsSXMax q m) {i j : Fin 4} (hij : i ≠ j)
    (hi : 0 < m i) (hj : 0 < m j) :
    sxG q (sxC q m) (m i) = sxG q (sxC q m) (m j) := by
  obtain ⟨e, he0, he1⟩ := exists_perm_pair i j hij
  have := (hm.perm e).lagrange01 (by simpa [he0] using hi) (by simpa [he1] using hj)
  simpa [sxC_perm, he0, he1] using this

/-! ### The Lagrange value and full support -/

theorem sxG_mul_self {q C x : ℝ} (hx : 0 ≤ x) (hq : 1 < q) :
    x * sxG q C x = x ^ q * (q * Real.log x + C) := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp [Real.zero_rpow (by linarith : q ≠ 0)]
  · unfold sxG
    have : x * x ^ (q - 1) = x ^ q := by rw [Real.rpow_sub_one h.ne']; field_simp
    rw [← mul_assoc, this]

theorem sum_mul_sxG {q : ℝ} (hq : 1 < q) (m : Fin 4 → ℝ) (hm : IsProb4 m) :
    ∑ k, m k * sxG q (sxC q m) (m k) = - sxBeta q * sxZ q m := by
  have hZ := (sxZ_pos hm q).ne'
  have e : ∀ k, m k * sxG q (sxC q m) (m k)
      = q * (m k ^ q * Real.log (m k)) + sxC q m * m k ^ q := by
    intro k; rw [sxG_mul_self (hm.1 k) hq]; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hV : ∑ k, m k ^ q * Real.log (m k) = sxV q m * sxZ q m := by
    unfold sxV; field_simp
  rw [hV]
  have hk := q_mul_sxKappa hq
  change q * (sxV q m * sxZ q m) + sxC q m * sxZ q m = _
  unfold sxC
  linear_combination (-(sxZ q m)) * hk

theorem IsSXMax.gval {q : ℝ} (hq : 1 < q) {m : Fin 4 → ℝ} (hm : IsSXMax q m) {i0 : Fin 4}
    (hi0 : 0 < m i0) : sxG q (sxC q m) (m i0) = - sxBeta q * sxZ q m := by
  have hs := sum_mul_sxG hq m hm.1
  have e : ∀ k, m k * sxG q (sxC q m) (m k) = m k * sxG q (sxC q m) (m i0) := by
    intro k
    rcases (hm.1.1 k).eq_or_lt with h | h
    · rw [← h]; simp
    · by_cases hk : k = i0
      · rw [hk]
      · rw [hm.lagrange hk h hi0]
  simp only [e, ← Finset.sum_mul, hm.1.2, one_mul] at hs
  exact hs

/-- Support: a maximiser has all coordinates positive. -/
theorem IsSXMax.pos {q : ℝ} (hq : 1 < q) {m : Fin 4 → ℝ} (hm : IsSXMax q m) (k : Fin 4) :
    0 < m k := by
  by_contra hk
  have hk0 : m k = 0 := le_antisymm (not_lt.mp hk) (hm.1.1 k)
  -- a positive coordinate
  obtain ⟨i0, hi0⟩ : ∃ i, 0 < m i := by
    by_contra h
    push Not at h
    have : ∑ i, m i = 0 := Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hm.1.1 i)
    linarith [hm.1.2]
  have hne : k ≠ i0 := by rintro rfl; linarith
  obtain ⟨e, he0, he1⟩ := exists_perm_pair k i0 hne
  have hm' := hm.perm e
  have h00 : (m ∘ e) 0 = 0 := by simpa [he0] using hk0
  have h11 : 0 < (m ∘ e) 1 := by simpa [he1] using hi0
  have hg := hm'.gval hq h11
  have hZ := sxZ_pos hm'.1 q
  set m' := m ∘ e with hm'def
  rw [sxZ_eq_four] at hZ
  have hZ0 : 0 < sxp q (m' 2) + sxp q (m' 3) + sxp q (m' 1) := by
    have := hZ; rw [h00, sxp_zero (by linarith)] at this; linarith
  have hd := sxPF_hasDerivWithinAt_zero hq (sxh q (m' 2) + sxh q (m' 3)) (sxp q (m' 2) + sxp q (m' 3))
    (m' 1) h11 (by linarith)
  have hC : sxC q m' = 1 - q * ((sxh q (m' 2) + sxh q (m' 3) + sxh q (m' 1))
      / (sxp q (m' 2) + sxp q (m' 3) + sxp q (m' 1)) + sxKappa q) := by
    unfold sxC; rw [sxV_eq_four, sxZ_eq_four, h00, sxh_zero, sxp_zero (by linarith)]
    simp only [add_zero]
  have hZ' : sxZ q m' = sxp q (m' 2) + sxp q (m' 3) + sxp q (m' 1) := by
    rw [sxZ_eq_four, h00, sxp_zero (by linarith)]; ring
  rw [← hC, hg, hZ'] at hd
  have hD : 0 < (- (-sxBeta q * (sxp q (m' 2) + sxp q (m' 3) + sxp q (m' 1))))
      / (sxp q (m' 2) + sxp q (m' 3) + sxp q (m' 1)) := by
    rw [neg_mul, neg_neg]
    exact div_pos (mul_pos (sxBeta_pos hq) hZ0) hZ0
  obtain ⟨τ, hτ0, hτ1, hlt⟩ := exists_gt_of_hasDerivWithinAt hd hD h11
  have := hm'.pair_le (τ := τ) (by rw [h00]; linarith) (by linarith)
  rw [h00] at this
  simp only [zero_add] at this
  simp only [sub_zero] at hlt
  exact absurd this (not_le.mpr hlt)

/-! ### The shape of `g`: Rolle and the bracket `B` -/

/-- The bracket `B_C(x) = (q-1)(q ln x + C) + q`, so that `g_C'(x) = x^{q-2} B_C(x)`. -/
noncomputable def sxB (q C x : ℝ) : ℝ := (q - 1) * (q * Real.log x + C) + q

theorem sxB_lt {q C x y : ℝ} (hq : 1 < q) (hx : 0 < x) (hxy : x < y) : sxB q C x < sxB q C y := by
  unfold sxB
  have := Real.log_lt_log hx hxy
  have h1 : 0 < q - 1 := by linarith
  have h2 : 0 < q := by linarith
  nlinarith [mul_pos h1 h2]

theorem sxG_strictMonoOn {q C u : ℝ} (hq : 1 < q) (hu : 0 < u) (hB : 0 < sxB q C u) :
    StrictMonoOn (sxG q C) (Set.Ici u) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici u)
  · intro x hx
    have hx' : 0 < x := lt_of_lt_of_le hu hx
    exact (sxG_hasDerivAt q C hx').continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx' : 0 < x := lt_trans hu hx
    rw [(sxG_hasDerivAt q C hx').deriv]
    have := sxB_lt (C := C) hq hu hx
    exact mul_pos (Real.rpow_pos_of_pos hx' _) (by unfold sxB at this hB; linarith)

/-- Rolle: if `g_C(u) = g_C(w)` with `0 < u < w`, then `B_C(u) < 0 < B_C(w)`. -/
theorem sxB_of_sxG_eq {q C u w : ℝ} (hq : 1 < q) (hu : 0 < u) (huw : u < w)
    (h : sxG q C u = sxG q C w) : sxB q C u < 0 ∧ 0 < sxB q C w := by
  have hd : ∀ x ∈ Set.Ioo u w, HasDerivAt (sxG q C)
      (x ^ (q - 2) * ((q - 1) * (q * Real.log x + C) + q)) x :=
    fun x hx => sxG_hasDerivAt q C (lt_trans hu hx.1)
  have hc : ContinuousOn (sxG q C) (Set.Icc u w) := fun x hx =>
    (sxG_hasDerivAt q C (lt_of_lt_of_le hu hx.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_zero huw hc h hd
  have hc0 : 0 < c := lt_trans hu hc1.1
  have hB0 : sxB q C c = 0 := by
    have := (mul_eq_zero.mp hc2).resolve_left (Real.rpow_pos_of_pos hc0 _).ne'
    exact this
  exact ⟨by have := sxB_lt (C := C) hq hu hc1.1; linarith,
    by have := sxB_lt (C := C) hq hc0 hc1.2; linarith⟩

/-! ### The second variation -/

theorem sxh_add_continuousAt (q : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun τ : ℝ => sxh q (x + τ)) 0 := by
  have h := (sxh_hasDerivAt q (x := x + 0) (by simpa using hx)).continuousAt
  exact h.comp_of_eq (continuousAt_const.add continuousAt_id) (by simp)

theorem sxh_sub_continuousAt (q : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun τ : ℝ => sxh q (x - τ)) 0 := by
  have h := (sxh_hasDerivAt q (x := x - 0) (by simpa using hx)).continuousAt
  exact h.comp_of_eq (continuousAt_const.sub continuousAt_id) (by simp)

theorem sxp_add_continuousAt (q : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun τ : ℝ => sxp q (x + τ)) 0 := by
  have h := (sxp_hasDerivAt q (x := x + 0) (by simpa using hx)).continuousAt
  exact h.comp_of_eq (continuousAt_const.add continuousAt_id) (by simp)

theorem sxp_sub_continuousAt (q : ℝ) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (fun τ : ℝ => sxp q (x - τ)) 0 := by
  have h := (sxp_hasDerivAt q (x := x - 0) (by simpa using hx)).continuousAt
  exact h.comp_of_eq (continuousAt_const.sub continuousAt_id) (by simp)

/-- At a maximiser with two equal coordinates `a`, `B_C(a) ≤ 0`. -/
theorem IsSXMax.second_variation01 {q : ℝ} (hq : 1 < q) {m : Fin 4 → ℝ} (hm : IsSXMax q m)
    (heq : m 0 = m 1) : sxB q (sxC q m) (m 0) ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have hp0 : ∀ k, 0 < m k := hm.pos hq
  set cW := sxh q (m 2) + sxh q (m 3) with hcW
  set cZ := sxp q (m 2) + sxp q (m 3) with hcZ
  have hZ : 0 < cZ + sxp q (m 0) + sxp q (m 1) := by
    have := sxZ_pos hm.1 q; rwa [sxZ_eq_four] at this
  set N : ℝ → ℝ := fun τ => cW + sxh q (m 0 + τ) + sxh q (m 1 - τ) with hN
  set Dn : ℝ → ℝ := fun τ => cZ + sxp q (m 0 + τ) + sxp q (m 1 - τ) with hDn
  set Ct : ℝ → ℝ := fun τ => 1 - q * (N τ / Dn τ + sxKappa q) with hCt
  have hN0 : N 0 = cW + sxh q (m 0) + sxh q (m 1) := by simp [hN]
  have hD0 : Dn 0 = cZ + sxp q (m 0) + sxp q (m 1) := by simp [hDn]
  have hDn0 : 0 < Dn 0 := by rw [hD0]; exact hZ
  have hNc : ContinuousAt N 0 :=
    ((continuousAt_const.add (sxh_add_continuousAt q (hp0 0))).add (sxh_sub_continuousAt q (hp0 1)))
  have hDc : ContinuousAt Dn 0 :=
    ((continuousAt_const.add (sxp_add_continuousAt q (hp0 0))).add (sxp_sub_continuousAt q (hp0 1)))
  have hCc : ContinuousAt Ct 0 :=
    continuousAt_const.sub (continuousAt_const.mul ((hNc.div hDc hDn0.ne').add continuousAt_const))
  have hCt0 : Ct 0 = sxC q m := by
    simp only [hCt, hN0, hD0]
    unfold sxC; rw [sxV_eq_four, sxZ_eq_four]
  have hlogc : ContinuousAt (fun τ : ℝ => Real.log (m 1 - τ)) 0 :=
    ContinuousAt.log (continuousAt_const.sub continuousAt_id) (by simpa using (hp0 1).ne')
  have hBc : ContinuousAt (fun τ : ℝ => (q - 1) * (q * Real.log (m 1 - τ) + Ct τ) + q) 0 :=
    (continuousAt_const.mul ((continuousAt_const.mul hlogc).add hCc)).add continuousAt_const
  have hB0 : (q - 1) * (q * Real.log (m 1 - 0) + Ct 0) + q > 0 := by
    rw [hCt0, sub_zero, ← heq]; exact hpos
  have E1 := hBc.eventually (lt_mem_nhds hB0)
  have E2 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < m 0 + τ :=
    (continuousAt_const.add continuousAt_id).eventually (lt_mem_nhds (by simpa using hp0 0))
  have E3 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < m 1 - τ :=
    (continuousAt_const.sub continuousAt_id).eventually (lt_mem_nhds (by simpa using hp0 1))
  have E4 : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < Dn τ := hDc.eventually (lt_mem_nhds hDn0)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.mp (E1.and (E2.and (E3.and E4)))
  set f : ℝ → ℝ := fun τ => sxPF q cW cZ (m 0 + τ) (m 1 - τ) with hf
  have hderiv : ∀ τ, |τ| < ε → HasDerivAt f
      ((sxG q (Ct τ) (m 0 + τ) - sxG q (Ct τ) (m 1 - τ)) / Dn τ) τ := by
    intro τ hτ
    obtain ⟨_, h2, h3, h4⟩ := hεP (by simpa [Real.dist_eq] using hτ)
    exact sxPF_hasDerivAt q cW cZ (m 0) (m 1) τ h2 h3 h4
  have hmono : StrictMonoOn f (Set.Icc 0 (ε / 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 (ε / 2))
    · intro τ hτ
      have : |τ| < ε := by
        rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
      exact (hderiv τ this).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτε : |τ| < ε := by rw [abs_lt]; constructor <;> linarith [hτ.1, hτ.2]
      rw [(hderiv τ hτε).deriv]
      obtain ⟨h1, h2, h3, h4⟩ := hεP (by simpa [Real.dist_eq] using hτε)
      have hBpos : 0 < sxB q (Ct τ) (m 1 - τ) := h1
      have hu := sxG_strictMonoOn hq h3 hBpos
      have hlt : m 1 - τ < m 0 + τ := by rw [heq]; linarith [hτ.1]
      have := hu (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hlt.le) hlt
      exact div_pos (by linarith) h4
  have hlt := hmono (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩)
    (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) (by linarith)
  obtain ⟨_, h2, h3, _⟩ := hεP (y := ε / 2) (by simp [abs_of_pos hε]; linarith)
  have hle := hm.pair_le (τ := ε / 2) h2.le h3.le
  simp only [hf, add_zero, sub_zero] at hlt
  exact absurd hle (not_le.mpr hlt)

theorem IsSXMax.second_variation {q : ℝ} (hq : 1 < q) {m : Fin 4 → ℝ} (hm : IsSXMax q m)
    {i j : Fin 4} (hij : i ≠ j) (heq : m i = m j) : sxB q (sxC q m) (m i) ≤ 0 := by
  obtain ⟨e, he0, he1⟩ := exists_perm_pair i j hij
  have := (hm.perm e).second_variation01 hq (by simpa [he0, he1] using heq)
  simpa [sxC_perm, he0] using this

/-! ### Every maximiser is a permutation of `σ` -/

theorem sxPhiVec_perm_hsSpec {q : ℝ} {l : Fin 4 → ℝ} (h : IsHsPerm l) :
    sxPhiVec q l = sxPhiVec q hsSpec := by
  obtain ⟨e, he⟩ := h
  have : l = hsSpec ∘ e := funext he
  rw [this, sxPhiVec_perm]

theorem IsHsPerm.isProb4 {l : Fin 4 → ℝ} (h : IsHsPerm l) : IsProb4 l := by
  obtain ⟨e, he⟩ := h
  have : l = hsSpec ∘ e := funext he
  rw [this]; exact isProb4_perm hsSpec_isProb e

/-- **Maximiser lemma.** For `q > 1`, every maximiser of `φ_q` on the simplex is a permutation of
`σ = (1/2, 1/6, 1/6, 1/6)`. -/
theorem IsSXMax.isHsPerm {q : ℝ} (hq : 1 < q) {m : Fin 4 → ℝ} (hm : IsSXMax q m) : IsHsPerm m := by
  have hp := hm.pos hq
  set C := sxC q m with hC
  have hG : ∀ i j, sxG q C (m i) = sxG q C (m j) := fun i j => by
    by_cases h : i = j
    · rw [h]
    · exact hm.lagrange h (hp i) (hp j)
  have hpair : ∀ i j, m i < m j → sxB q C (m i) < 0 ∧ 0 < sxB q C (m j) :=
    fun i j h => sxB_of_sxG_eq hq (hp i) h (hG i j)
  have hσ : sxPhiVec q hsSpec ≤ sxPhiVec q m := hm.2 _ hsSpec_isProb
  by_cases hex : ∃ i0, 0 < sxB q C (m i0)
  · obtain ⟨i0, hi0⟩ := hex
    have hmax : ∀ k, m k ≤ m i0 := fun k => by
      by_contra h; push Not at h
      exact absurd (hpair i0 k h).1 (not_lt.mpr hi0.le)
    have hothers : ∀ j, j ≠ i0 → sxB q C (m j) ≤ 0 := by
      intro j hj
      by_contra h; push Not at h
      have hmaxj : ∀ k, m k ≤ m j := fun k => by
        by_contra h'; push Not at h'
        exact absurd (hpair j k h').1 (not_lt.mpr h.le)
      have heq : m j = m i0 := le_antisymm (hmax j) (hmaxj i0)
      exact absurd (hm.second_variation hq hj heq) (not_le.mpr h)
    have hmin : ∀ j, j ≠ i0 → ∀ k, m j ≤ m k := fun j hj k => by
      by_contra h; push Not at h
      exact absurd (hpair k j h).2 (not_lt.mpr (hothers j hj))
    set e : Equiv.Perm (Fin 4) := Equiv.swap 0 i0 with he
    have hee : ∀ i, e (e i) = i := fun i => Equiv.swap_apply_self 0 i0 i
    have hne : ∀ j : Fin 4, j ≠ 0 → e j ≠ i0 := by
      intro j hj h
      apply hj
      have h1 : e i0 = 0 := Equiv.swap_apply_right 0 i0
      calc j = e (e j) := (hee j).symm
        _ = e i0 := by rw [h]
        _ = 0 := h1
    have h00 : (m ∘ e) 0 = m i0 := by simp [he]
    have h1e : ∀ j : Fin 4, j ≠ 0 → ∀ k : Fin 4, k ≠ 0 → (m ∘ e) j = (m ∘ e) k := fun j hj k hk =>
      le_antisymm (hmin _ (hne j hj) _) (hmin _ (hne k hk) _)
    set M := m i0 with hM
    set μ := (m ∘ e) 1 with hμ
    have hm' : m ∘ e = ![M, μ, μ, μ] := by
      funext i
      fin_cases i
      · exact h00
      · rfl
      · exact h1e 2 (by decide) 1 (by decide)
      · exact h1e 3 (by decide) 1 (by decide)
    have hprob := isProb4_perm hm.1 e
    rw [hm'] at hprob
    have hsum : M + 3 * μ = 1 := by
      have := hprob.2
      simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at this
      linarith
    have hMpos : 0 < M := hp i0
    have hμpos : 0 < μ := by
      have : (m ∘ e) 1 = m (e 1) := rfl
      rw [hμ, this]; exact hp _
    have hμM : μ ≤ M := by
      have : (m ∘ e) 1 = m (e 1) := rfl
      rw [hμ, this]; exact hmax _
    have hφ : sxPhiVec q m = sxPhiVec q ![M, μ, μ, μ] := by
      rw [← hm', sxPhiVec_perm]
    have hle := sxFamily_le hq hMpos hμpos hsum hμM
    have heq : sxPhiVec q ![M, μ, μ, μ] = sxPhiVec q hsSpec := by
      apply le_antisymm hle; rw [← hφ]; exact hσ
    obtain ⟨hM2, hμ6⟩ := sxFamily_eq hq hMpos hμpos hsum hμM heq
    refine ⟨e, fun i => ?_⟩
    have h1 : m i = (m ∘ e) (e i) := by simp [hee]
    rw [h1, hm', hM2, hμ6]
    generalize e i = k
    fin_cases k <;> simp [hsSpec]
  · push Not at hex
    have hall : ∀ i j, m i ≤ m j := fun i j => by
      by_contra h; push Not at h
      exact absurd (hpair j i h).2 (not_lt.mpr (hex i))
    have hc : ∀ i, m i = 1 / 4 := by
      have hconst : ∀ i, m i = m 0 := fun i => le_antisymm (hall i 0) (hall 0 i)
      have hs := hm.1.2
      simp only [Fin.sum_univ_four] at hs
      intro i; rw [hconst i]
      have h1 := hconst 1; have h2 := hconst 2; have h3 := hconst 3
      linarith
    have hm' : m = ![1 / 4, 1 / 4, 1 / 4, 1 / 4] := by
      funext i; fin_cases i <;> simp [hc]
    have hfam := sxPhiVec_family hq (a := 1 / 4) (b := 1 / 4) (by norm_num) (by norm_num) (by norm_num)
    rw [div_self (by norm_num), Real.log_one] at hfam
    have hlt : sxPhi q 0 < sxPhi q (Real.log 3) :=
      sxPhi_lt hq le_rfl (fun h => by have := sx_log3_pos; linarith)
    rw [hm', hfam, sxPhiVec_hsSpec hq] at hσ
    exact absurd hσ (not_le.mpr hlt)

/-! ### Existence of a maximiser and the lemma -/

theorem sxh_continuousOn {q : ℝ} (hq : 1 < q) : ContinuousOn (sxh q) (Set.Ici 0) := by
  intro x hx
  rcases (Set.mem_Ici.mp hx).eq_or_lt with h | h
  · subst h
    exact (continuousWithinAt_Ioi_iff_Ici).mp (sxh_hasDerivWithinAt_zero hq).continuousWithinAt
  · exact (sxh_hasDerivAt q h).continuousAt.continuousWithinAt

/-- The simplex of four-point probability vectors, as a set. -/
def simplex4 : Set (Fin 4 → ℝ) := {l | IsProb4 l}

theorem isCompact_simplex4 : IsCompact simplex4 := by
  apply IsCompact.of_isClosed_subset
    (isCompact_univ_pi (fun _ : Fin 4 => isCompact_Icc (a := (0 : ℝ)) (b := 1)))
  · have : simplex4 = (⋂ i, {l : Fin 4 → ℝ | 0 ≤ l i}) ∩ {l | ∑ i, l i = 1} := by
      ext l; simp [simplex4, IsProb4]
    rw [this]
    exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const)
  · intro l hl i _
    refine ⟨hl.1 i, ?_⟩
    calc l i ≤ ∑ j, l j :=
          Finset.single_le_sum (f := l) (fun j _ => hl.1 j) (Finset.mem_univ i)
      _ = 1 := hl.2

theorem sxPhiVec_continuousOn {q : ℝ} (hq : 1 < q) : ContinuousOn (sxPhiVec q) simplex4 := by
  have hZ : ContinuousOn (fun l : Fin 4 → ℝ => sxZ q l) simplex4 := by
    unfold sxZ
    apply Continuous.continuousOn
    exact continuous_finsetSum _ fun i _ =>
      (Real.continuous_rpow_const (by linarith)).comp (continuous_apply i)
  have hW : ContinuousOn (fun l : Fin 4 → ℝ => ∑ i, l i ^ q * Real.log (l i)) simplex4 := by
    apply continuousOn_finsetSum
    intro i _
    have : ContinuousOn (fun l : Fin 4 → ℝ => sxh q (l i)) simplex4 :=
      (sxh_continuousOn hq).comp (continuous_apply i).continuousOn (fun l hl => hl.1 i)
    exact this
  have hpos : ∀ l ∈ simplex4, sxZ q l ≠ 0 := fun l hl => (sxZ_pos hl q).ne'
  unfold sxPhiVec sxV sxU
  exact (hW.div hZ hpos).sub (continuousOn_const.mul (hZ.log hpos))

/-- **`lem:fqe-renyi-single-crossing`** (SX), with its equality case. For every `q > 1` and every
four-point probability vector `l`, `v_q(l) - v_q(σ) ≤ κ_q (u_q(l) - u_q(σ))`, with equality only if `l`
is a permutation of `σ = (1/2, 1/6, 1/6, 1/6)`. Proof: a maximiser of `φ = v_q - κ_q u_q` on the simplex
exists by compactness, is a permutation of `σ` (`IsSXMax.isHsPerm`: full support, Lagrange condition,
Rolle for `g`, the second variation, then the one-large family of
`RenyiSingleCrossingFamily.lean`), and `φ` is permutation invariant. -/
theorem single_crossing_statement : SingleCrossingStatement := by
  intro q hq l hl
  obtain ⟨m, hmΔ, hmax⟩ := isCompact_simplex4.exists_isMaxOn
    ⟨hsSpec, hsSpec_isProb⟩ (sxPhiVec_continuousOn hq)
  have hM : IsSXMax q m := ⟨hmΔ, fun l' hl' => hmax hl'⟩
  have hperm := hM.isHsPerm hq
  have hmσ : sxPhiVec q m = sxPhiVec q hsSpec := sxPhiVec_perm_hsSpec hperm
  have hle : sxPhiVec q l ≤ sxPhiVec q hsSpec := hmσ ▸ hM.2 l hl
  unfold sxPhiVec at hle
  refine ⟨by linarith, fun heq => ?_⟩
  have hEq : sxPhiVec q l = sxPhiVec q m := by unfold sxPhiVec at hmσ ⊢; linarith
  exact IsSXMax.isHsPerm hq ⟨hl, fun l' hl' => hEq ▸ hM.2 l' hl'⟩

/-! ### Order transfer, unconditionally -/

/-- **`cor:fqe-renyi-order-transfer`, monotonicity of `G_l`**: for every four-point spectrum `l`,
`G_l(q) = (q-1)(H_q(l) - H_q(σ))/(q tanh((q-1) ln 3/2))` is nondecreasing on `(1, ∞)`. -/
theorem renyiG_monotoneOn_all {l : Fin 4 → ℝ} (hl : IsProb4 l) :
    MonotoneOn (renyiG l) (Set.Ioi 1) :=
  renyiG_monotoneOn single_crossing_statement hl

/-- `G_l` is strictly increasing on `(1, ∞)` unless `l` is a permutation of `σ`. -/
theorem renyiG_strictMonoOn_all {l : Fin 4 → ℝ} (hl : IsProb4 l) (hn : ¬ IsHsPerm l) :
    StrictMonoOn (renyiG l) (Set.Ioi 1) :=
  renyiG_strictMonoOn single_crossing_statement hl hn

/-- **`cor:fqe-renyi-order-transfer`, the triple transfer** for three four-point spectra, `1 < q < q₁`:
`E_{q₁} ≤ h_{q₁} → E_q ≤ h_q`; `E_{q₁} < h_{q₁} → E_q < h_q`; and `E_{q₁} ≤ h_{q₁}`, `E_q = h_q` force
all three spectra to be permutations of `σ`. -/
theorem renyi_order_transfer_all {l₁ l₂ l₃ : Fin 4 → ℝ}
    (h₁ : IsProb4 l₁) (h₂ : IsProb4 l₂) (h₃ : IsProb4 l₃) {q q₁ : ℝ} (hq : 1 < q) (hqq : q < q₁) :
    (renyiE q₁ l₁ l₂ l₃ ≤ renyiSpec q₁ hsSpec → renyiE q l₁ l₂ l₃ ≤ renyiSpec q hsSpec) ∧
    (renyiE q₁ l₁ l₂ l₃ < renyiSpec q₁ hsSpec → renyiE q l₁ l₂ l₃ < renyiSpec q hsSpec) ∧
    (renyiE q₁ l₁ l₂ l₃ ≤ renyiSpec q₁ hsSpec → renyiE q l₁ l₂ l₃ = renyiSpec q hsSpec →
      IsHsPerm l₁ ∧ IsHsPerm l₂ ∧ IsHsPerm l₃) :=
  renyi_order_transfer single_crossing_statement h₁ h₂ h₃ hq hqq

/-! ### The three cut spectra of a state -/

/-- A fixed enumeration of the four cut eigenvalue indices by `Fin 4`. -/
noncomputable def cutEquiv : Fin 2 × Fin 2 ≃ Fin 4 := Fintype.equivFinOfCardEq (by simp)

/-- A cut spectrum on `Fin 2 × Fin 2` as a four-point vector. -/
noncomputable def spec4 (l : Fin 2 × Fin 2 → ℝ) : Fin 4 → ℝ := l ∘ cutEquiv.symm

theorem isProb4_spec4 {l : Fin 2 × Fin 2 → ℝ} (h : IsProb l) : IsProb4 (spec4 l) :=
  ⟨fun i => h.1 _, by
    have := Equiv.sum_comp cutEquiv.symm l
    unfold spec4; simp only [Function.comp_apply]; rw [this]; exact h.2⟩

theorem renyiSpec_spec4 (q : ℝ) (l : Fin 2 × Fin 2 → ℝ) : renyiSpec q (spec4 l) = renyiSpec q l := by
  unfold renyiSpec spec4
  have := Equiv.sum_comp cutEquiv.symm (fun i => l i ^ q)
  simp only [Function.comp_apply]; rw [this]

/-- **`cor:fqe-renyi-order-transfer` for states.** For a unit four-qubit vector `ψ` and `1 < q < q₁`
(`E_q = meanRenyi q ψ`, `h_q = hsRenyi q`): `E_{q₁} ≤ h_{q₁} → E_q ≤ h_q`; `E_{q₁} < h_{q₁} →
E_q < h_q`; and `E_{q₁} ≤ h_{q₁}`, `E_q = h_q` force the three cut spectra to be permutations of
`σ`. -/
theorem meanRenyi_order_transfer {ψ : Psi} (hψ : normSqPsi ψ = 1) {q q₁ : ℝ} (hq : 1 < q)
    (hqq : q < q₁) :
    (meanRenyi q₁ ψ ≤ hsRenyi q₁ → meanRenyi q ψ ≤ hsRenyi q) ∧
    (meanRenyi q₁ ψ < hsRenyi q₁ → meanRenyi q ψ < hsRenyi q) ∧
    (meanRenyi q₁ ψ ≤ hsRenyi q₁ → meanRenyi q ψ = hsRenyi q →
      IsHsPerm (spec4 (red12_herm ψ).eigenvalues) ∧ IsHsPerm (spec4 (red13_herm ψ).eigenvalues) ∧
        IsHsPerm (spec4 (red14_herm ψ).eigenvalues)) := by
  have p1 := isProb4_spec4 (isProb12 hψ)
  have p2 := isProb4_spec4 (isProb13 hψ)
  have p3 := isProb4_spec4 (isProb14 hψ)
  have hE : ∀ r, meanRenyi r ψ = renyiE r (spec4 (red12_herm ψ).eigenvalues)
      (spec4 (red13_herm ψ).eigenvalues) (spec4 (red14_herm ψ).eigenvalues) := by
    intro r
    unfold meanRenyi renyiE
    rw [renyiCut_eq_renyiSpec, renyiCut_eq_renyiSpec, renyiCut_eq_renyiSpec,
      renyiSpec_spec4, renyiSpec_spec4, renyiSpec_spec4]
  have hH : ∀ r, hsRenyi r = renyiSpec r hsSpec := hsRenyi_eq
  simp only [hE, hH]
  exact renyi_order_transfer_all p1 p2 p3 hq hqq

end FormalResearch.FourQubitEntropy

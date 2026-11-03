import FormalResearch.PPTThreeQubit.SurfacePPTFactor
import FormalResearch.PPTThreeQubit.SurfaceExtreme

/-!
# The rank-five surface: positivity and the fully-PPT property

Source: `ResearchNotes/QI/finite_copy_invariant_inference/ppt_three_qubit/rank_five_surface.tex`,
`thm:ppt3-orbit` (proof, "Rank and PPT": `eq:ppt3-surface-simpledet`, `eq:ppt3-surface-minors`)
and `cor:ppt3-extreme5` (PPT part).

Covered (proved, no numerical input):
* `rhoQ_posSemidef`: `ρ_τ = ρ(1, τ, 1)` is positive semidefinite on the window, via the
  decomposition with the Schur complement `(τV - G²)/τ = 2Q²κ(Q²-3)/τ ≥ 0`
  (`eq:ppt3-surface-simpledet`);
* `posSemidef_ptA_rhoQ`: `ρ_τ^{T_A}` is positive semidefinite, from the explicit `LDL*`
  factorization of `SurfacePPTFactor.lean` with pivots `1, E, ·, 1/τ, ·` (the zero fourth even and
  the zero third and fourth odd pivots are the rank deficiency of the two parity blocks);
* `ptA_conj_filterDiag`: `(F ρ F†)^{T_A} = F ρ^{T_A} F†` for the real diagonal filter
  `F = F_λ`, which reduces `a` to `a = 1` (`rhoSurface_filter`);
* `rhoSurface_cycShift`: cyclic invariance, so `T_B`, `T_C` follow from `T_A`;
* `ppt3_orbit_ppt` / `ppt3_orbit_ppt_gme`: for `1/√3 < τ < 1` and every `a > 0`, `ρ_{τ,a}` is
  positive semidefinite and fully PPT (and GME);
* `sigma5_ppt_gme`: the same for `σ` of `cor:ppt3-extreme5` (`τ = 48/55`, `a = 2`).
Not covered: the rank profile `(5,5,5,5)`, part (a) beyond cyclic invariance, part (c) of
`thm:ppt3-orbit`, extremality of `σ`.
-/

namespace FormalResearch.PPTThreeQubit

open Matrix ComplexOrder

noncomputable section

/-! ### Positivity of `ρ_Q` -/

theorem qT_pos {Q : ℝ} (hQ : 1 < Q) : 0 < qT Q := by
  unfold qT
  apply div_pos <;> nlinarith

theorem qE_nonneg {Q : ℝ} (hk : qk Q ≤ 0) : 0 ≤ qE Q := by
  unfold qE; linarith

theorem qO_nonneg {Q : ℝ} (hQ : 1 < Q) (hk : qk Q ≤ 0) : 0 ≤ qO Q := by
  unfold qO
  apply div_nonneg (by linarith)
  have : 0 < Q ^ 2 - 1 := by nlinarith
  positivity

/-- `τV - G² = 2Q²κ(Q²-3) = -(Q²-3) k/2` (`eq:ppt3-surface-simpledet`). -/
theorem qT_mul_qV_sub {Q : ℝ} (hQ : 0 < Q) :
    qT Q * qV Q - qG Q ^ 2 = -((Q ^ 2 - 3) * qk Q) / 2 := by
  unfold qT qV qG qk
  field_simp
  ring

/-- `ρ_Q = uu† + E ee† + O oo† + τ ff† + ((τV - G²)/τ) vv†`, `f = w + (G/τ) v`. -/
theorem rhoQ_eq_sum {Q : ℝ} (hQ : 1 < Q) :
    rhoQ Q = vecMulVec (uVec 1) (star (uVec 1)) + (qE Q : ℂ) • vecMulVec eVec (star eVec) +
      (qO Q : ℂ) • vecMulVec oVec (star oVec) +
      (qT Q : ℂ) • vecMulVec (wVec + ((qG Q / qT Q : ℝ) : ℂ) • vVec)
        (star (wVec + ((qG Q / qT Q : ℝ) : ℂ) • vVec)) +
      (((qT Q * qV Q - qG Q ^ 2) / qT Q : ℝ) : ℂ) • vecMulVec vVec (star vVec) := by
  have hT : qT Q ≠ 0 := (qT_pos hQ).ne'
  have hT' : (qT Q : ℂ) ≠ 0 := by exact_mod_cast hT
  ext i j
  simp only [rhoQ_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul', Complex.star_def,
    Complex.conj_ofReal]
  push_cast
  field_simp
  ring

/-- `ρ_τ = ρ(1, τ, 1)` is positive semidefinite for `Q > 1`, `Q² ≥ 3`, `k(Q) ≤ 0`
(`eq:ppt3-surface-simpledet`). -/
theorem rhoQ_posSemidef {Q : ℝ} (hQ : 1 < Q) (h3 : 3 ≤ Q ^ 2) (hk : qk Q ≤ 0) :
    (rhoQ Q).PosSemidef := by
  rw [rhoQ_eq_sum hQ]
  have hT := qT_pos hQ
  have hdet : 0 ≤ (qT Q * qV Q - qG Q ^ 2) / qT Q := by
    rw [qT_mul_qV_sub (by linarith)]
    apply div_nonneg _ hT.le
    have : 0 ≤ (Q ^ 2 - 3) * (-qk Q) := mul_nonneg (by linarith) (by linarith)
    linarith
  refine Matrix.PosSemidef.add (Matrix.PosSemidef.add (Matrix.PosSemidef.add
    (Matrix.PosSemidef.add (posSemidef_vecMulVec_self_star _) ?_) ?_) ?_) ?_
  · exact (posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr (qE_nonneg hk))
  · exact (posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr (qO_nonneg hQ hk))
  · exact (posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr hT.le)
  · exact (posSemidef_vecMulVec_self_star _).smul (Complex.zero_le_real.mpr hdet)

/-! ### Positivity of the partial transposes of `ρ_Q` -/

theorem dpivQ_nonneg {Q : ℝ} (hQ : 1 < Q) (h3 : 3 ≤ Q ^ 2) (hk : qk Q ≤ 0) (k : Fin 5) :
    0 ≤ dpivQ Q k := by
  have hN : 0 < Q ^ 2 - 1 := by nlinarith
  have hQ0 : 0 < Q := by linarith
  have hk' : 0 ≤ -qk Q := by linarith
  fin_cases k <;> simp only [dpivQ] <;> simp
  · linarith
  · apply div_nonneg _ (by positivity)
    have : 0 ≤ (Q ^ 2 - 3) * (Q ^ 4 + 3) * (-qk Q) :=
      mul_nonneg (mul_nonneg (by linarith) (by positivity)) hk'
    linarith
  · positivity
  · apply div_nonneg _ (by positivity)
    have : 0 ≤ 3 * (Q ^ 2 - 1) * (-qk Q) := by positivity
    linarith

/-- `ρ_τ^{T_A}` is positive semidefinite on the window. -/
theorem posSemidef_ptA_rhoQ {Q : ℝ} (hQ : 1 < Q) (h3 : 3 ≤ Q ^ 2) (hk : qk Q ≤ 0) :
    (ptA (rhoQ Q)).PosSemidef := by
  have hQ0 : Q ≠ 0 := by positivity
  have hN : Q ^ 2 - 1 ≠ 0 := by nlinarith
  have e : ptA (rhoQ Q) = ∑ k, dpivQ Q k • vecMulVec (lq Q k) (star (lq Q k)) := by
    ext i j
    rw [ptA_rhoQ_entry Q hQ0 hN i j]
    simp only [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, Pi.star_apply,
      Complex.real_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e]
  exact Matrix.posSemidef_sum _ fun k _ =>
    (posSemidef_vecMulVec_self_star _).smul (dpivQ_nonneg hQ h3 hk k)

/-! ### From `τ` to the coordinate `Q` -/

/-- The weights of `ρ(1, τ, 1)` in the coordinate `Q = τ + √(1+τ²)`: `ρ_τ = ρ_Q` for
`0 < τ < 1` (the simplified weights of the proof of `thm:ppt3-orbit`). -/
theorem rhoSurface_one_eq {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∃ Q : ℝ, 1 < Q ∧ τ = qT Q ∧ rhoSurface 1 τ 1 = rhoQ Q := by
  obtain ⟨Q, hQ, hQ1, ht', hh'⟩ := Q_coords hτ0 (surfH_sq τ) (surfH_pos τ)
  have hQ0 : Q ≠ 0 := by positivity
  have hN : Q ^ 2 - 1 ≠ 0 := by nlinarith
  have hT : τ = qT Q := ht'
  have hO : wO 1 τ = qO Q := by
    rw [wO_one, ht']; unfold qO qk; field_simp; ring
  have hE : wE 1 τ 1 = qE Q := by
    rw [wE_one, ← hQ, ht']; unfold qE qk; field_simp; ring
  have hG : wG 1 τ 1 = qG Q := by
    rw [wG_one, ← hQ, ht']; unfold qG; field_simp; ring
  have hV : wV 1 τ 1 = qV Q := by
    rw [wV_one hτ0 hτ1, ← hQ, ht']; unfold qV; field_simp; ring
  refine ⟨Q, hQ1, hT, ?_⟩
  rw [rhoSurface_eq, hO, hE, hG, hV, show (1 : ℝ) / 1 = 1 by norm_num, hT]
  simp [rhoQ]

/-- The window `1/√3 < τ < 1` in the coordinate `Q`: `Q > 1`, `Q² > 3` and `k(Q) < 0`. -/
theorem window_Q {τ : ℝ} (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1) :
    ∃ Q : ℝ, 1 < Q ∧ 3 < Q ^ 2 ∧ qk Q < 0 ∧ rhoSurface 1 τ 1 = rhoQ Q := by
  have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hτ0 : 0 < τ := lt_trans (by positivity) h1
  have hst : 1 < Real.sqrt 3 * τ := by rwa [div_lt_iff₀ hs0, mul_comm] at h1
  have h3τ : 1 < 3 * τ ^ 2 := by nlinarith
  obtain ⟨Q, hQ1, hT, hr⟩ := rhoSurface_one_eq hτ0 h2
  have hQ0 : 0 < Q := by linarith
  have hk : qk Q = -4 * Q ^ 2 * (1 - τ ^ 2) := by
    rw [hT]; unfold qT qk; field_simp; ring
  have hτQ : τ * (2 * Q) = Q ^ 2 - 1 := by rw [hT]; unfold qT; field_simp
  refine ⟨Q, hQ1, ?_, ?_, hr⟩
  · by_contra hc
    have hc := not_lt.mp hc
    have e : 3 * (Q ^ 2 - 1) ^ 2 = 12 * Q ^ 2 * τ ^ 2 := by
      rw [← hτQ]; ring
    have : 4 * Q ^ 2 < 3 * (Q ^ 2 - 1) ^ 2 := by
      rw [e]; nlinarith [pow_pos hQ0 2]
    nlinarith [mul_nonneg (by nlinarith : (0 : ℝ) ≤ 3 * Q ^ 2 - 1) (by linarith : (0 : ℝ) ≤ 3 - Q ^ 2)]
  · rw [hk]
    have : 0 < 1 - τ ^ 2 := by nlinarith
    have : 0 < Q ^ 2 * (1 - τ ^ 2) := by positivity
    linarith

/-! ### The local filter commutes with the partial transpose on `A` -/

theorem ptA_smul (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ) : ptA (c • M) = c • ptA M := by
  ext i j; simp [ptA]

theorem ptB_smul (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ) : ptB (c • M) = c • ptB M := by
  ext i j; simp [ptB]

theorem ptC_smul (c : ℂ) (M : Matrix (Fin 8) (Fin 8) ℂ) : ptC (c • M) = c • ptC M := by
  ext i j; simp [ptC]

/-- For the real diagonal filter `F_λ`, `(F M F†)^{T_A} = F M^{T_A} F†`. -/
theorem ptA_conj_filterDiag (lam : ℝ) (M : Matrix (Fin 8) (Fin 8) ℂ) :
    ptA (diagonal (filterDiag lam) * M * (diagonal (filterDiag lam))ᴴ) =
      diagonal (filterDiag lam) * ptA M * (diagonal (filterDiag lam))ᴴ := by
  have hs : ∀ i : Fin 8, star (filterDiag lam i) = filterDiag lam i := fun i => by
    simp [filterDiag]
  ext i j
  simp only [ptA, of_apply, diagonal_conjTranspose, diagonal_mul, mul_diagonal, Pi.star_apply, hs]
  fin_cases i <;> fin_cases j <;> simp [filterDiag] <;> ring

/-! ### Cyclic invariance of `ρ(α, W, A)` -/

theorem uVec_cycShift_s (s : ℝ) : uVec s ∘ cycShift = uVec s := by
  funext i; fin_cases i <;> simp [cycShift, uVec]

/-- `ρ(α, W, A)` is invariant under the cyclic shift of the qubits (`thm:ppt3-orbit`(a)). -/
theorem rhoSurface_cycShift (α W A : ℝ) :
    (rhoSurface α W A).submatrix cycShift cycShift = rhoSurface α W A := by
  ext i j
  rw [submatrix_apply, rhoSurface_eq]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  have key : ∀ x y : Fin 8 → ℂ, vecMulVec x (star y) (cycShift i) (cycShift j) =
      vecMulVec (x ∘ cycShift) (star (y ∘ cycShift)) i j := fun x y => rfl
  simp only [key, uVec_cycShift_s, vVec_cycShift, wVec_cycShift, eVec_cycShift, oVec_cycShift,
    vecMulVec_phase _ ω_sq_mul_star]

/-! ### The fully-PPT property of the orbit -/

/-- **`thm:ppt3-orbit`, PPT part, `a = 1`.** -/
theorem ppt3_orbit_ppt_one {τ : ℝ} (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1) :
    (rhoSurface 1 τ 1).PosSemidef ∧ (ptA (rhoSurface 1 τ 1)).PosSemidef := by
  obtain ⟨Q, hQ, h3, hk, hr⟩ := window_Q h1 h2
  rw [hr]
  exact ⟨rhoQ_posSemidef hQ h3.le hk.le, posSemidef_ptA_rhoQ hQ h3.le hk.le⟩

/-- The filter reduction of `thm:ppt3-orbit`(b) for positivity and the partial transpose on `A`. -/
theorem ppt3_orbit_posSemidef_ptA {τ : ℝ} (a : ℝ) (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1)
    (ha : 0 < a) :
    (rhoSurface 1 τ a).PosSemidef ∧ (ptA (rhoSurface 1 τ a)).PosSemidef := by
  have hτ0 : 0 < τ := lt_trans (by positivity) h1
  have hl : (Real.sqrt a⁻¹) ^ 2 = a⁻¹ := Real.sq_sqrt (inv_nonneg.mpr ha.le)
  have hf := rhoSurface_filter one_pos hτ0 h2 ha hl
  rw [mul_one] at hf
  obtain ⟨hP, hPA⟩ := ppt3_orbit_ppt_one h1 h2
  have ha' : (0 : ℂ) ≤ (a : ℂ) := Complex.zero_le_real.mpr ha.le
  rw [hf, ptA_smul, ptA_conj_filterDiag]
  exact ⟨(hP.mul_mul_conjTranspose_same _).smul ha', (hPA.mul_mul_conjTranspose_same _).smul ha'⟩

/-- **`thm:ppt3-orbit`, PPT part.**  For `1/√3 < τ < 1` and every `a > 0` the (unnormalised)
operator `ρ_{τ,a} = ρ(1, τ, a)` is positive semidefinite and fully PPT: all three partial
transposes are positive semidefinite.  Proof: the explicit `LDL*` factorization of
`ρ_τ^{T_A}` at `a = 1` (`posSemidef_ptA_rhoQ`), the local filter for general `a`
(`ptA_conj_filterDiag`, `rhoSurface_filter`) and cyclic invariance for `T_B`, `T_C`
(`rhoSurface_cycShift`).  Rank statements are not covered. -/
theorem ppt3_orbit_ppt {τ : ℝ} (a : ℝ) (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1) (ha : 0 < a) :
    (rhoSurface 1 τ a).PosSemidef ∧ IsPPT3 (rhoSurface 1 τ a) := by
  obtain ⟨hP, hPA⟩ := ppt3_orbit_posSemidef_ptA a h1 h2 ha
  refine ⟨hP, hPA, ?_, ?_⟩
  · rw [ptB_eq_of_shift_invariant _ (rhoSurface_cycShift 1 τ a)]
    exact hPA.submatrix _
  · rw [ptC_eq_of_shift_invariant _ (rhoSurface_cycShift 1 τ a)]
    exact hPA.submatrix _

/-- **`thm:ppt3-orbit`, PPT and GME.**  For `1/√3 < τ < 1` and every `a > 0`, `ρ_{τ,a}` is a
positive semidefinite, fully-PPT, genuinely multipartite entangled operator (unnormalised;
normalisation by the trace does not affect any of the three properties). -/
theorem ppt3_orbit_ppt_gme {τ : ℝ} (a : ℝ) (h1 : 1 / Real.sqrt 3 < τ) (h2 : τ < 1) (ha : 0 < a) :
    (rhoSurface 1 τ a).PosSemidef ∧ IsPPT3 (rhoSurface 1 τ a) ∧ IsGME (rhoSurface 1 τ a) :=
  ⟨(ppt3_orbit_ppt a h1 h2 ha).1, (ppt3_orbit_ppt a h1 h2 ha).2, ppt3_orbit_gme a h1 h2 ha⟩

/-! ### The explicit rational member `σ` -/

/-- Homogeneity at the member `(55, 48, 110)`: `ρ(55, 48, 110) = 55 ρ(1, 48/55, 2)`. -/
theorem rhoSurface_55_48_110 : rhoSurface 55 48 110 = (55 : ℂ) • rhoSurface 1 (48 / 55) 2 := by
  have h73 : surfH 55 48 = 73 := by
    unfold surfH
    rw [show (55 : ℝ) ^ 2 + 48 ^ 2 = 73 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h73' : surfH 1 (48 / 55) = 73 / 55 := by
    unfold surfH
    rw [show (1 : ℝ) ^ 2 + (48 / 55) ^ 2 = (73 / 55) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hE : wE 55 48 110 = 55 * wE 1 (48 / 55) 2 := by
    unfold wE; rw [h73, h73']; norm_num
  have hG : wG 55 48 110 = 55 * wG 1 (48 / 55) 2 := by
    unfold wG; rw [hE]; norm_num; ring
  have hV : wV 55 48 110 = 55 * wV 1 (48 / 55) 2 := by
    unfold wV; rw [hE]; norm_num; ring
  have hO : wO 55 48 = 55 * wO 1 (48 / 55) := by
    unfold wO; norm_num
  rw [rhoSurface_eq, rhoSurface_eq, hE, hG, hV, hO,
    show (55 : ℝ) / 110 = 1 / 2 by norm_num]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- `σ` is the member `ρ(1, 48/55, 2)` of the orbit up to a positive scalar. -/
theorem sigma5_eq_orbit :
    sigma5 = ((55 * 30000 / 16323219 : ℝ) : ℂ) • rhoSurface 1 (48 / 55) 2 := by
  rw [sigma5_eq_member, rhoSurface_55_48_110, smul_smul]
  congr 1
  push_cast
  ring

theorem window_48_55 : 1 / Real.sqrt 3 < 48 / 55 := by
  have hs0 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have h : (55 / 48 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  rw [div_lt_div_iff₀ hs0 (by norm_num)]
  nlinarith

/-- **`cor:ppt3-extreme5`, PPT and GME parts.**  The rational state `σ = N/16323219` is positive
semidefinite, fully PPT and genuinely multipartite entangled (`τ = 48/55`, `a = 2`).  Rank five
and extremality are not covered. -/
theorem sigma5_ppt_gme : sigma5.PosSemidef ∧ IsPPT3 sigma5 ∧ IsGME sigma5 := by
  obtain ⟨hP, hPPT⟩ := ppt3_orbit_ppt 2 window_48_55 (by norm_num) (by norm_num)
  rw [sigma5_eq_orbit]
  have hc : (0 : ℝ) ≤ 55 * 30000 / 16323219 := by norm_num
  have hc' : (0 : ℂ) ≤ ((55 * 30000 / 16323219 : ℝ) : ℂ) := Complex.zero_le_real.mpr hc
  refine ⟨hP.smul hc', ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [ptA_smul]; exact hPPT.1.smul hc'
  · rw [ptB_smul]; exact hPPT.2.1.smul hc'
  · rw [ptC_smul]; exact hPPT.2.2.smul hc'
  · rw [← sigma5_eq_orbit]; exact sigma5_gme

end

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_orbit_ppt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_orbit_ppt

/-- info: 'FormalResearch.PPTThreeQubit.ppt3_orbit_ppt_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ppt3_orbit_ppt_gme

/-- info: 'FormalResearch.PPTThreeQubit.sigma5_ppt_gme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma5_ppt_gme

end FormalResearch.PPTThreeQubit

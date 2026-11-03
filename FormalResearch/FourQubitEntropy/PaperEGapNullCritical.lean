module

public import FormalResearch.FourQubitEntropy.PaperEGapNullBlochQH
public import FormalResearch.FourQubitEntropy.PaperEGapNullExists
public import FormalResearch.FourQubitEntropy.PaperEGapNullScalar
public import FormalResearch.FourQubitEntropy.CriticalOrbitMain
public import FormalResearch.FourQubitEntropy.CriticalOrbitUpper
public import FormalResearch.FourQubitEntropy.Checks
public import FormalResearch.FourQubitEntropy.PaperECriticalTwoFlat

/-!
# `thm:fqe-critical-orbit-sharp`: the null-critical refinement `eq:fqe-null-critical-sharp`

Paper E, `critical_orbit_stability.tex` / `lu_orbit_stability.tex`.  For every critical unit pure
four-qubit state with `τ = 0` (equivalently `P = 1`),
`Φ ≥ (2+√3)/6`, `Q ≥ 3/(4-√3) (1 - Φ) ≥ (3+√3)/4 d²`, and these are attained by the cluster state.

Proof (the paper's elementary one, no `thm:fqe-global-overlap`): `Σ v_k² = 0` makes the auxiliary vector `B v`
a product `a ⊗ b` (`exists_vOf`); in the Bloch vectors `r, s` of `a, b` the 32 overlaps are
`(1 + ε·r/√3)(1 + η·s/√3)/4` over the cube pairs of opposite parity (`qH_vOf`), and
`Q = 1/2 + (27/2) r₁r₂r₃s₁s₂s₃` (`Qv_vOf`); the real inequalities are `null_exists_pair`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- The sign pattern `ε` of the `a`-th representative, as Booleans. -/
def tabE : Fin 32 → Fin 3 → Bool :=
![![false, false, false],
  ![true, false, false],
  ![false, true, false],
  ![true, true, false],
  ![false, false, true],
  ![true, false, true],
  ![false, true, true],
  ![true, true, true],
  ![true, false, true],
  ![false, false, true],
  ![true, false, false],
  ![false, false, false],
  ![true, true, true],
  ![false, true, true],
  ![true, true, false],
  ![false, true, false],
  ![true, true, false],
  ![true, false, false],
  ![true, true, true],
  ![true, false, true],
  ![false, true, false],
  ![false, false, false],
  ![false, true, true],
  ![false, false, true],
  ![false, true, true],
  ![false, true, false],
  ![false, false, true],
  ![false, false, false],
  ![true, true, true],
  ![true, true, false],
  ![true, false, true],
  ![true, false, false]]

/-- The sign pattern `η` of the `a`-th representative, as Booleans. -/
def tabH : Fin 32 → Fin 3 → Bool :=
![![false, true, false],
  ![true, true, false],
  ![false, false, false],
  ![true, false, false],
  ![false, true, true],
  ![true, true, true],
  ![false, false, true],
  ![true, false, true],
  ![true, false, false],
  ![false, false, false],
  ![true, false, true],
  ![false, false, true],
  ![true, true, false],
  ![false, true, false],
  ![true, true, true],
  ![false, true, true],
  ![false, false, true],
  ![false, true, true],
  ![false, false, false],
  ![false, true, false],
  ![true, false, true],
  ![true, true, true],
  ![true, false, false],
  ![true, true, false],
  ![true, true, true],
  ![true, true, false],
  ![true, false, true],
  ![true, false, false],
  ![false, true, true],
  ![false, true, false],
  ![false, false, true],
  ![false, false, false]]

theorem epsT_eq (a : Fin 32) (j : Fin 3) : epsT a j = sg (tabE a j) := by
  fin_cases a <;> fin_cases j <;> simp [epsT, tabE, sg]

theorem etaT_eq (a : Fin 32) (j : Fin 3) : etaT a j = sg (tabH a j) := by
  fin_cases a <;> fin_cases j <;> simp [etaT, tabH, sg]

theorem tab_surj : ∀ b b' : Fin 3 → Bool, Parity b b' = true → ∃ a : Fin 32, tabE a = b ∧ tabH a = b' := by
  decide

theorem bl_unit {a0 a1 : ℂ} (h : Complex.normSq a0 + Complex.normSq a1 = 1) :
    bl a0 a1 0 ^ 2 + bl a0 a1 1 ^ 2 + bl a0 a1 2 ^ 2 = 1 := by
  have : bl a0 a1 0 ^ 2 + bl a0 a1 1 ^ 2 + bl a0 a1 2 ^ 2 =
      (Complex.normSq a0 + Complex.normSq a1) ^ 2 := by
    simp only [bl, Complex.normSq_apply]; simp; ring
  rw [this, h]; norm_num

/-- **Null-critical core**: for a unit `v` with `Σ v_k² = 0` some representative overlap `q_η = qH a v`
satisfies `q_η ≥ (2+√3)/6` and `Q ≥ 3/(4-√3) (1 - q_η)`. -/
theorem null_core {v : V} (hn : Nv v = 1) (hτ : ∑ k, v k ^ 2 = 0) :
    ∃ a : Fin 32, (2 + Real.sqrt 3) / 6 ≤ qH a v ∧
      3 / (4 - Real.sqrt 3) * (1 - qH a v) ≤ Qv v := by
  obtain ⟨a0, a1, b0, b1, ha, hb, rfl⟩ := exists_vOf v hn hτ
  obtain ⟨b, b', hpar, h1, h2⟩ := null_exists_pair (bl a0 a1) (bl b0 b1) (bl_unit ha) (bl_unit hb)
  obtain ⟨a, hE, hH⟩ := tab_surj b b' hpar
  have hq : qH a (vOf a0 a1 b0 b1) = Fpair b b' (bl a0 a1) (bl b0 b1) := by
    rw [qH_vOf a a0 a1 b0 b1 ha hb]
    have e1 : dotv (epsT a) (bl a0 a1) = dotS b (bl a0 a1) := by
      rw [← hE]; simp only [dotv, dotS, epsT_eq]
    have e2 : dotv (etaT a) (bl b0 b1) = dotS b' (bl b0 b1) := by
      rw [← hH]; simp only [dotv, dotS, etaT_eq]
    rw [e1, e2]; rfl
  refine ⟨a, by rw [hq]; exact h1, ?_⟩
  rw [hq, Qv_vOf a0 a1 b0 b1 ha hb]
  exact h2

/-- For a critical unit state, `τ = 0` is equivalent to `P = 1`. -/
theorem critical_tau_zero_iff_purity {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    spinFlipForm ψ = 0 ↔ purity ψ = 1 := by
  have h := purity_identity_exact ψ
  rw [hψ, hW] at h
  constructor
  · intro h0; rw [h0] at h; simp at h; linarith
  · intro h1
    have : Complex.normSq (spinFlipForm ψ) = 0 := by linarith
    exact Complex.normSq_eq_zero.mp this

/-- The distance coefficient from the fidelity floor: `(3+√3)/4 · d² ≤ 3/(4-√3) (1 - Φ)` once
`Φ ≥ (2+√3)/6`. -/
theorem dist_coeff {Φ : ℝ} (hΦ : (2 + Real.sqrt 3) / 6 ≤ Φ) (hΦ1 : Φ ≤ 1) :
    (3 + Real.sqrt 3) / 4 * (2 - 2 * Real.sqrt Φ) ≤ 3 / (4 - Real.sqrt 3) * (1 - Φ) := by
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  set c := Real.sqrt 3 with hcdef
  have h4 : 0 < 4 - c := by linarith
  have hx : 1 + c / 3 ≤ 2 * Real.sqrt Φ := by
    have h0 : 0 ≤ Φ := by nlinarith
    have : (1 + c / 3) ^ 2 / 4 ≤ Φ := by rw [f0_eq]; exact hΦ
    have hs : (1 + c / 3) / 2 ≤ Real.sqrt Φ := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    linarith
  have hx1 : Real.sqrt Φ ≤ 1 := by
    rw [Real.sqrt_le_one]; exact hΦ1
  have hxx : Real.sqrt Φ * Real.sqrt Φ = Φ := Real.mul_self_sqrt (by nlinarith)
  set x := Real.sqrt Φ with hxdef
  rw [show 3 / (4 - c) * (1 - Φ) = 3 * (1 - Φ) / (4 - c) by ring, le_div_iff₀ h4]
  -- (3+c)/4 (2-2x)(4-c) ≤ 3 (1 - x²) = 3 (1-x)(1+x)
  have hd : 0 ≤ 1 - x := by linarith
  have key : (3 + c) / 4 * (2 - 2 * x) * (4 - c) ≤ 3 * (1 - Φ) := by
    rw [← hxx]
    have : (3 + c) / 4 * (2 - 2 * x) * (4 - c) = (1 - x) * ((3 + c) * (4 - c) / 2) := by ring
    rw [this]
    have h5 : (3 + c) * (4 - c) = 9 + c := by nlinarith
    rw [h5]
    nlinarith [mul_nonneg hd (by linarith : (0:ℝ) ≤ 2 * x - (1 + c / 3))]
  exact key

/-- **`eq:fqe-null-critical-sharp`** (`thm:fqe-critical-orbit-sharp`, null-critical refinement): for every
critical unit pure four-qubit state with `τ = 0` (equivalently `P = 1`),
`Φ ≥ (2+√3)/6`, `Q ≥ 3/(4-√3) (1 - Φ)` and `3/(4-√3) (1 - Φ) ≥ (3+√3)/4 d²`, with `d² = 2 - 2√Φ`.
Proved without `thm:fqe-global-overlap`. -/
theorem null_critical_sharp {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hτ : spinFlipForm ψ = 0) :
    (2 + Real.sqrt 3) / 6 ≤ Phi ψ ∧ 3 / (4 - Real.sqrt 3) * (1 - Phi ψ) ≤ sexticQ ψ ∧
      (3 + Real.sqrt 3) / 4 * dist2 ψ ≤ 3 / (4 - Real.sqrt 3) * (1 - Phi ψ) := by
  obtain ⟨v, hv, hN, hQ⟩ := critical_normal_vector hψ hW
  have hP : purity ψ = 1 := (critical_tau_zero_iff_purity hψ hW).mp hτ
  have hsum : ∑ k, v k ^ 2 = 0 := by
    have h1 := Gv_purity_tau v hN
    have hpur : purity ψ = purity (Gv v) := by
      obtain ⟨e12, e13, e14⟩ := cutPurities_LUEquiv hv
      rw [purity_eq_cuts, purity_eq_cuts, e12, e13, e14]
    have : Complex.normSq (∑ k, v k ^ 2) = 0 := by linarith
    exact Complex.normSq_eq_zero.mp this
  obtain ⟨a, h1, h2⟩ := null_core hN hsum
  have hle := qH_le_Phi hv hψ a
  have hc := sqrt3_facts
  have h4 : 0 < 4 - Real.sqrt 3 := by linarith [hc.2.2]
  have hpos : 0 < 3 / (4 - Real.sqrt 3) := div_pos (by norm_num) h4
  have hΦ : (2 + Real.sqrt 3) / 6 ≤ Phi ψ := le_trans h1 hle
  refine ⟨hΦ, ?_, ?_⟩
  · rw [hQ]
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - Phi ψ ≤ 1 - qH a v) hpos.le
    linarith
  · unfold dist2
    exact dist_coeff hΦ (Phi_le_one hψ)

/-- The distance form: `Q ≥ (3+√3)/4 · d²` on null-critical states. -/
theorem null_critical_distance {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hτ : spinFlipForm ψ = 0) : (3 + Real.sqrt 3) / 4 * dist2 ψ ≤ sexticQ ψ := by
  obtain ⟨-, h2, h3⟩ := null_critical_sharp hψ hW hτ
  linarith

theorem Fpair_aux (e f : ℝ) :
    (1 + -e / Real.sqrt 3) * (1 + -f / Real.sqrt 3) / 4 =
      (1 + -e * Real.sqrt 3 / 3) * (1 + -f * Real.sqrt 3 / 3) / 4 := by
  rw [div_s3, div_s3]

/-! ### Attainment by the cluster state -/

/-- The critical normal vector `(1, i, 0, 0)/√2` of the cluster state, as `B†(a ⊗ b)` with
`a = b = (1, -1)/√2`. -/
noncomputable def clusterV : V := vOf rt (-rt) rt (-rt)

theorem normSq_rt_add : Complex.normSq rt + Complex.normSq (-rt) = 1 := by
  rw [Complex.normSq_neg, normSq_rt]; norm_num

theorem clusterV_N : Nv clusterV = 1 := by
  unfold clusterV; rw [Nv_vOf, normSq_rt_add]; norm_num

theorem clusterV_sum : ∑ k, clusterV k ^ 2 = 0 := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only [clusterV, vOf, uOf, Fintype.sum_prod_type, Fin.sum_univ_two]
  linear_combination (4 * rt ^ 6) * hI

theorem clusterV_Q : Qv clusterV = 1 / 2 := by
  unfold clusterV
  rw [Qv_vOf rt (-rt) rt (-rt) normSq_rt_add normSq_rt_add]
  have : bl rt (-rt) 1 = 0 := by simp [bl, rt_im]
  rw [this]; ring

theorem clusterV_le (a : Fin 32) : qH a clusterV ≤ (2 + Real.sqrt 3) / 6 := by
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  unfold clusterV
  rw [qH_vOf a rt (-rt) rt (-rt) normSq_rt_add normSq_rt_add]
  have h1 : bl rt (-rt) 1 = 0 := by simp [bl, rt_im]
  have h2 : bl rt (-rt) 2 = 0 := by simp [bl, rt_im, normSq_rt]
  have h0 : bl rt (-rt) 0 = -1 := by
    simp [bl, rt_im]; nlinarith [rt_sq]
  have hε : epsT a 0 ^ 2 = 1 := by rw [epsT_eq]; exact (by cases tabE a 0 <;> simp [sg])
  have hη : etaT a 0 ^ 2 = 1 := by rw [etaT_eq]; exact (by cases tabH a 0 <;> simp [sg])
  have hd1 : dotv (epsT a) (bl rt (-rt)) = -epsT a 0 := by simp [dotv, h0, h1, h2]
  have hd2 : dotv (etaT a) (bl rt (-rt)) = -etaT a 0 := by simp [dotv, h0, h1, h2]
  rw [hd1, hd2, Fpair_aux]
  have he := eq_or_eq_neg_of_sq_eq_sq (epsT a 0) 1 (by rw [hε]; norm_num)
  have hh := eq_or_eq_neg_of_sq_eq_sq (etaT a 0) 1 (by rw [hη]; norm_num)
  have hA : 0 ≤ 1 - Real.sqrt 3 / 3 := by linarith
  have hB : 0 ≤ 1 + Real.sqrt 3 / 3 := by linarith
  rw [← f0_eq]
  rcases he with he | he <;> rcases hh with hh | hh <;> rw [he, hh] <;> nlinarith [mul_nonneg hA hB, mul_nonneg hA hA, hc]

/-- **Optimality in `eq:fqe-null-critical-sharp`**: the cluster state `ψ = G(1, i, 0, 0)/√2` is a critical
unit state with `τ = 0` and `Φ = (2+√3)/6`, `Q = 1/2`, attaining all three bounds with equality. -/
theorem null_critical_attained :
    ∃ ψ : Psi, normSqPsi ψ = 1 ∧ blochSq ψ = 0 ∧ spinFlipForm ψ = 0 ∧
      Phi ψ = (2 + Real.sqrt 3) / 6 ∧ sexticQ ψ = 1 / 2 ∧
      3 / (4 - Real.sqrt 3) * (1 - Phi ψ) = sexticQ ψ ∧
      (3 + Real.sqrt 3) / 4 * dist2 ψ = sexticQ ψ := by
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  set c := Real.sqrt 3 with hcdef
  have hGn : normSqPsi (Gv clusterV) = 1 := by rw [Gv_n]; exact clusterV_N
  have hW : blochSq (Gv clusterV) = 0 := blochSq_zero_of_LU_Gv clusterV _ (LUEquiv.refl _)
  have hτ : spinFlipForm (Gv clusterV) = 0 := by
    have : spinFlipForm (Gv clusterV) = ∑ k, clusterV k ^ 2 := by
      rw [spinFlip_coord, coord_Gv, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      simp [Matrix.trace, pow_two]
    rw [this]; exact clusterV_sum
  have hQ : sexticQ (Gv clusterV) = 1 / 2 := by rw [sexticQ_Gv, clusterV_Q]
  obtain ⟨a, h1, -⟩ := null_core clusterV_N clusterV_sum
  have hle := qH_le_Phi (LUEquiv.refl (Gv clusterV)) hGn a
  have hup : Phi (Gv clusterV) ≤ (2 + c) / 6 := Phi_Gv_le clusterV_le
  have hΦ : Phi (Gv clusterV) = (2 + c) / 6 := le_antisymm hup (le_trans h1 hle)
  refine ⟨Gv clusterV, hGn, hW, hτ, hΦ, hQ, ?_, ?_⟩
  · rw [hΦ, hQ]
    have h4 : 0 < 4 - c := by linarith
    rw [show 3 / (4 - c) * (1 - (2 + c) / 6) = 3 * (1 - (2 + c) / 6) / (4 - c) by ring,
      div_eq_iff h4.ne']
    ring
  · unfold dist2
    rw [hΦ, hQ, ← f0_eq]
    have hs : Real.sqrt ((1 + c / 3) ^ 2 / 4) = (1 + c / 3) / 2 := by
      rw [show (1 + c / 3) ^ 2 / 4 = ((1 + c / 3) / 2) ^ 2 by ring]
      exact Real.sqrt_sq (by linarith)
    rw [hs]
    nlinarith [hc]

/-- The same statement under the hypothesis `P = 1` (equivalent to `τ = 0` on the critical locus). -/
theorem null_critical_sharp_of_purity {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0)
    (hP : purity ψ = 1) :
    (2 + Real.sqrt 3) / 6 ≤ Phi ψ ∧ 3 / (4 - Real.sqrt 3) * (1 - Phi ψ) ≤ sexticQ ψ ∧
      (3 + Real.sqrt 3) / 4 * dist2 ψ ≤ 3 / (4 - Real.sqrt 3) * (1 - Phi ψ) :=
  null_critical_sharp hψ hW ((critical_tau_zero_iff_purity hψ hW).mpr hP)

end FormalResearch.FourQubitEntropy.CO

#print axioms FormalResearch.FourQubitEntropy.CO.null_critical_sharp
#print axioms FormalResearch.FourQubitEntropy.CO.null_critical_distance
#print axioms FormalResearch.FourQubitEntropy.CO.null_critical_attained
#print axioms FormalResearch.FourQubitEntropy.CO.critical_tau_zero_iff_purity

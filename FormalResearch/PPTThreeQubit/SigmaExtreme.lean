module

public import FormalResearch.PPTThreeQubit.SigmaExtremeData
public import FormalResearch.PPTThreeQubit.ExtremeCriterion
public import FormalResearch.PPTThreeQubit.SurfaceExtreme
public import FormalResearch.PPTThreeQubit.SurfacePPT
public import FormalResearch.PPTThreeQubit.Chirality

/-!
# `σ` is an extreme fully-PPT state (`cor:ppt3-extreme5`, the rational member)

Transfer of the exact `ℚ(ω)` certificate of `SigmaExtremeData` to `ℂ` and the extremality theorem
`sigma5_extreme : sigma5 ∈ fullyPPT3.extremePoints ℝ` (supported-face criterion, `MatrixAnalysis.ExtremeCriterion`).
-/

@[expose] public section

namespace FormalResearch.PPTThreeQubit

open Matrix

/-! ### Transfer to `ℂ` -/

theorem φω_mk (a b : ℚ) : φω ⟨a, b⟩ = (a : ℂ) + (b : ℂ) * ω := by
  simp [φω, QuadraticAlgebra.lift_apply_apply, Rat.smul_def]

theorem φω_star (z : Kω) : φω (star z) = star (φω z) := by
  obtain ⟨x, y⟩ := z
  rw [QuadraticAlgebra.star_mk, φω_mk, φω_mk]
  simp only [star_add, star_mul', Complex.star_def, map_ratCast]
  have h : starRingEnd ℂ ω = ω ^ 2 := star_ω
  rw [h]
  push_cast
  linear_combination (-(y : ℂ)) * ω_sq_add_ω_add_one

theorem Bω_map : Bω.map φω = Bs (1 / 2) := by
  ext i a
  fin_cases i <;> fin_cases a <;>
    simp [Bω, Bs, bCols, uVec, vVec, wVec, eVec, oVec, φω_mk] <;>
    first | rfl | (push_cast; linear_combination ω_sq_add_ω_add_one) |
      (push_cast; linear_combination (-1 : ℂ) * ω_sq_add_ω_add_one) | (push_cast; ring)

theorem Xω_map : Xω.map φω = Xsigma := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xω, Xsigma, surfXw, φω_mk] <;> norm_num

/-! ### Solving the face system -/

theorem sum_idx (m : ℕ) (hm : m < 25) (Y : Matrix (Fin 5) (Fin 5) ℂ) (c : ℂ) :
    ∑ a : Fin 5, ∑ b : Fin 5, (if a.val * 5 + b.val = m then c else 0) * Y a b =
      c * Y (fin5 (m / 5)) (fin5 m) := by
  interval_cases m <;> simp [Fin.sum_univ_five, fin5]

theorem sum3_move {ι κ ℓ : Type*} [Fintype ι] [Fintype κ] [Fintype ℓ] (f : ι → κ → ℓ → ℂ) :
    ∑ a, ∑ b, ∑ r, f a b r = ∑ r, ∑ a, ∑ b, f a b r := by
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  rw [Finset.sum_comm]

theorem face_solve (Y : Matrix (Fin 5) (Fin 5) ℂ)
    (hrow : ∀ r : Fin 24, ∑ a, ∑ b, φω (rowCoef (selRow r) a b) * Y a b = 0) (t : Fin 24) :
    φω (Xω 0 0) * Y (fin5 ((t.val + 1) / 5)) (fin5 (t.val + 1)) =
      φω (Xω (fin5 ((t.val + 1) / 5)) (fin5 (t.val + 1))) * Y 0 0 := by
  have hφ : ∀ a b, φω (tgtK t a b) = ∑ r : Fin 24, φω (lamK t r) * φω (rowCoef (selRow r) a b) := by
    intro a b
    rw [← cert t a b]
    simp only [map_sum, map_mul]
  have h1 : ∑ a, ∑ b, φω (tgtK t a b) * Y a b = 0 := by
    simp_rw [hφ, Finset.sum_mul]
    rw [sum3_move]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := hrow r
    calc ∑ a, ∑ b, φω (lamK t r) * φω (rowCoef (selRow r) a b) * Y a b
        = φω (lamK t r) * ∑ a, ∑ b, φω (rowCoef (selRow r) a b) * Y a b := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
      _ = 0 := by rw [this, mul_zero]
  have e1 := sum_idx (t.val + 1) (by omega) Y (φω (Xω 0 0))
  have e2 : ∑ a : Fin 5, ∑ b : Fin 5,
      (if a = 0 ∧ b = 0 then φω (Xω (fin5 ((t.val + 1) / 5)) (fin5 (t.val + 1))) else 0) * Y a b =
      φω (Xω (fin5 ((t.val + 1) / 5)) (fin5 (t.val + 1))) * Y 0 0 := by
    simp [Fin.sum_univ_five]
  have h2 : ∑ a, ∑ b, φω (tgtK t a b) * Y a b =
      ∑ a : Fin 5, ∑ b : Fin 5, (if a.val * 5 + b.val = t.val + 1 then φω (Xω 0 0) else 0) * Y a b -
      ∑ a : Fin 5, ∑ b : Fin 5,
        (if a = 0 ∧ b = 0 then φω (Xω (fin5 ((t.val + 1) / 5)) (fin5 (t.val + 1))) else 0) * Y a b := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [tgtK, map_sub, apply_ite φω, map_zero, sub_mul]
  rw [h2, e1, e2] at h1
  exact sub_eq_zero.mp h1

theorem Bs_ker_zero (c : Fin 5 → ℂ) (h : Bs (1 / 2) *ᵥ c = 0) : c = 0 := by
  rw [Bs_mulVec] at h
  have h0 := congrFun h 0
  have h7 := congrFun h 7
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h2 := congrFun h 2
  simp at h0 h7 h3 h4 h2
  have hc4 : c 4 = 0 := by
    have : (ω - 1) * c 4 = 0 := by linear_combination h2 - h4
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' ω_ne_one
    · exact h'
  have hc2 : c 2 = 0 := by rw [hc4] at h4; simpa using h4
  have hc3 : c 3 = 0 := by rw [h0] at h3; simpa using h3
  ext i
  fin_cases i <;> simp [h0, h7, hc2, hc3, hc4]

theorem Bs_injective : Function.Injective (Bs (1 / 2)).mulVec := by
  intro x y hxy
  have : Bs (1 / 2) *ᵥ (x - y) = 0 := by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy
  exact sub_eq_zero.mp (Bs_ker_zero _ this)

/-- The kernel vectors of `ptG c σ`, as complex vectors. -/
noncomputable def kC (c κ : Fin 3) : Fin 8 → ℂ := fun j => φω (kerV c κ j)

/-- Every Hermitian `Y` killed by the 9 kernel conditions satisfies the 24 selected row equations. -/
theorem rowEq (Y : Matrix (Fin 5) (Fin 5) ℂ) (hY : ∀ c κ : Fin 3,
    ptG c (Bs (1 / 2) * Y * (Bs (1 / 2))ᴴ) *ᵥ kC c κ = 0) (c κ : Fin 3) (i : Fin 8) :
    ∑ a, ∑ b, φω (coefD c Bω (kerV c κ) i a b) * Y a b = 0 := by
  have h := congrFun (hY c κ) i
  rw [← Bω_map, mulVec_ptG_sandwich] at h
  simp only [Pi.zero_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  exact (coefD_map φω.toRingHom φω_star c Bω (kerV c κ) i a b).symm

theorem hrow_of (Y : Matrix (Fin 5) (Fin 5) ℂ) (hH : Y.IsHermitian) (hY : ∀ c κ : Fin 3,
    ptG c (Bs (1 / 2) * Y * (Bs (1 / 2))ᴴ) *ᵥ kC c κ = 0) (r : Fin 24) :
    ∑ a, ∑ b, φω (rowCoef (selRow r) a b) * Y a b = 0 := by
  unfold rowCoef
  split_ifs with hk
  · exact rowEq Y hY _ _ _
  · have e := rowEq Y hY (fin3 (selRow r).2.1) (fin3 (selRow r).2.2.1) (fin8 (selRow r).2.2.2)
    have : ∑ a, ∑ b, φω (star (coefD (fin3 (selRow r).2.1) Bω (kerV (fin3 (selRow r).2.1)
        (fin3 (selRow r).2.2.1)) (fin8 (selRow r).2.2.2) b a)) * Y a b =
        star (∑ a, ∑ b, φω (coefD (fin3 (selRow r).2.1) Bω (kerV (fin3 (selRow r).2.1)
          (fin3 (selRow r).2.2.1)) (fin8 (selRow r).2.2.2) a b) * Y a b) := by
      rw [star_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [star_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [star_mul', φω_star, hH.apply b a]
    rw [this, e, star_zero]

theorem fin5_idx (i j : Fin 5) : fin5 ((i.val * 5 + j.val) / 5) = i ∧ fin5 (i.val * 5 + j.val) = j := by
  fin_cases i <;> fin_cases j <;> decide

theorem Xsigma_eq (i j : Fin 5) : Xsigma i j = φω (Xω i j) := by
  rw [← Xω_map]; rfl

theorem Xsigma_00_ne : Xsigma 0 0 ≠ 0 := by
  simp [Xsigma, surfXw]

theorem trace_sigma5 : sigma5.trace = 1 := by
  simp only [sigma5, Nsigma, Matrix.trace, Matrix.diag, Matrix.smul_apply, Matrix.add_apply,
    vecMulVec_apply, Pi.star_apply, Fin.sum_univ_eight, smul_eq_mul]
  simp [uTilde, wVec, vVec, eVec, oVec, Complex.mul_conj, normSq_ω]
  have h : ω ^ 2 * (starRingEnd ℂ) ω ^ 2 = 1 := by
    rw [← mul_pow, Complex.mul_conj, normSq_ω]; simp
  rw [h]
  norm_num

/-- The kernel vectors lie in the kernels of the partial transposes of `σ`. -/
theorem kernel_sigma5 (c κ : Fin 3) : ptG c sigma5 *ᵥ kC c κ = 0 := by
  have h := kernel_check c κ
  have hm : sigma5 = (Bω * Xω * Bωᴴ).map φω := by
    rw [sigma5_eq, ← Bω_map, ← Xω_map]
    simp only [Matrix.map_mul]
    congr 1
    ext i j
    simp [φω_star]
  have hp : ptG c sigma5 = (ptG c (Bω * Xω * Bωᴴ)).map φω := by
    rw [hm]; fin_cases c <;> rfl
  rw [hp]
  ext i
  have e := (RingHom.map_mulVec φω.toRingHom (ptG c (Bω * Xω * Bωᴴ)) (kerV c κ) i).symm
  have h0 : (ptG c (Bω * Xω * Bωᴴ) *ᵥ kerV c κ) i = 0 := by rw [h]; rfl
  have h1 : φω.toRingHom ((ptG c (Bω * Xω * Bωᴴ) *ᵥ kerV c κ) i) = 0 := by rw [h0]; simp
  exact e.trans h1

theorem sigma5_null (Y : Matrix (Fin 5) (Fin 5) ℂ) (hH : Y.IsHermitian)
    (hY : ∀ c κ : Fin 3, ptG c (Bs (1 / 2) * Y * (Bs (1 / 2))ᴴ) *ᵥ kC c κ = 0) :
    ∃ a : ℂ, Y = a • Xsigma := by
  have hrow := hrow_of Y hH hY
  refine ⟨Y 0 0 / Xsigma 0 0, ?_⟩
  ext i j
  have hx := Xsigma_00_ne
  by_cases hij : i.val * 5 + j.val = 0
  · have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 0 := Fin.ext (by omega)
    subst hi; subst hj
    simp [hx]
  · let t : Fin 24 := ⟨i.val * 5 + j.val - 1, by omega⟩
    have ht : t.val + 1 = i.val * 5 + j.val := by simp only [t]; omega
    have h := face_solve Y hrow t
    rw [ht, (fin5_idx i j).1, (fin5_idx i j).2] at h
    rw [← Xsigma_eq, ← Xsigma_eq] at h
    simp only [Matrix.smul_apply, smul_eq_mul]
    field_simp
    linear_combination h

/-- **`cor:ppt3-extreme5`, the rational member**: the state `σ` of `eq:ppt3-sigma5` (`τ = 48/55`, `Q = 11/5`)
is an extreme point of the set of fully-PPT three-qubit states, by the supported-face criterion
(`ppt3_extreme_of_sandwich`): the 24 real-linear face equations from three kernel vectors
of each partial transpose force `Y ∝ X_σ`, certified in exact arithmetic over `ℚ(ω)`
(`SigmaExtremeData.cert`, `decide +kernel`). -/
theorem sigma5_extreme : sigma5 ∈ fullyPPT3.extremePoints ℝ := by
  obtain ⟨hps, hppt, -⟩ := sigma5_ppt_gme
  have hσ : sigma5 ∈ fullyPPT3 :=
    (mem_fullyPPT3_iff sigma5).mpr ⟨hps, trace_sigma5, hppt.1, hppt.2.1, hppt.2.2⟩
  refine ppt3_extreme_of_sandwich hσ (Bs (1 / 2)) Xsigma sigma5_eq Bs_injective
    (Set.range (kC 0)) (Set.range (kC 1)) (Set.range (kC 2)) ?_ ?_ ?_ ?_
  · rintro _ ⟨κ, rfl⟩; exact kernel_sigma5 0 κ
  · rintro _ ⟨κ, rfl⟩; exact kernel_sigma5 1 κ
  · rintro _ ⟨κ, rfl⟩; exact kernel_sigma5 2 κ
  · intro Y hH hA hB hC
    refine sigma5_null Y hH fun c κ => ?_
    fin_cases c
    · exact hA _ ⟨κ, rfl⟩
    · exact hB _ ⟨κ, rfl⟩
    · exact hC _ ⟨κ, rfl⟩

/-- info: 'FormalResearch.PPTThreeQubit.sigma5_extreme' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sigma5_extreme

end FormalResearch.PPTThreeQubit

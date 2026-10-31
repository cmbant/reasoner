import FormalResearch.FourQubitEntropy.PaperEOrbitDistance

/-!
# `lem:fqe-hs-fidelity-floor`: `Φ ≥ (1 + √τ)/6`, and the orbit-distance estimates without a floor hypothesis

Paper E, `global_overlap_certificate.tex`, `lem:fqe-hs-fidelity-floor` (used in `thm:fqe-global-overlap`):
for every unit pure four-qubit state, `Φ(ψ) ≥ (1+√τ(ψ))/6 ≥ 1/6`.

* `fidelity_floor`: **proved** as the paper states it.  Proof (the paper's): multiply `ψ` by a phase so that
  `s = tr(XᵀX) = ‖tr XᵀX‖ ≥ 0` in magic coordinates `X`; then `‖Re X‖_F² = (1+s)/2`
  (`re_part_norm`); a signed real SVD of `Re X` with `SO(4)` factors (`real_svd`, from `lem:fqe-real-gram`)
  is realised by local unitaries (`exists_LU_rotate`, `Real4.of_SO`), so a state `ψ''` in the LU class has
  magic matrix with real diagonal `D = (m,x,y,z)` (signed) on its real part; the two representatives of `𝓗` with
  large component at the position of `max|D|` and opposite sign patterns `±sgn D` give
  `Φ ≥ m²/2 + (|x|+|y|+|z|)²/6` (`Phi_ge_diag`), and `alg4` shows this is `≥ ‖D‖²/3 = (1+s)/6`.
  Signs of `D` cost nothing, so no orientation/`O(4)` bookkeeping is needed.
* `fidelityFloor_all : FidelityFloor ψ` for every unit `ψ`, hence the unconditional-except-`GlobalOverlap`
  versions `orbitDist_sq_le_Q_of_overlap`, `entropy_gap_orbit_stability_dist_of_overlap`,
  `majorant_gap_orbit_of_overlap`, `tsallis_gap_orbit_of_overlap` of the estimates of `PaperEOrbitDistance`.
* The τ-dependent constant of `eq:fqe-global-overlap-sharp`: `overlap_ge_dist_tau`,
  `orbitDist_sq_le_Q_tau`, `entropy_gap_dist_tau` (`(6+√(6(1+√τ)))/12`).

Not formalised: the local-radius clauses (`d ≤ 1/20 ⇒ δ ≥ 3d²/10` needs the matrix-logarithm Hessian estimate of
`entropy_orbit_hessian.tex`; `d ≤ 2⁻¹⁰ ⇒ Q ≥ 3d²` needs the transverse quadratic form of `Q`).  No hypothesis other
than `GlobalOverlap` (`thm:fqe-global-overlap`) remains in the global estimates.
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.OD
open CO PaperECritical

/-- Magic coordinates of a local unitary image: `X ↦ U₁ X U₂ᵀ` with `Uᵢ = Bᴴ (· ⊗ ·) B`. -/
theorem coord_localApply_gen (a b c d : Op1) (ψ : Psi) :
    magicCoord (zmat (localApply a b c d ψ)) =
      (magicBᴴ * kron a b * magicB) * magicCoord (zmat ψ) * (magicBᴴ * kron c d * magicB)ᵀ := by
  have hK1 : kron a b = magicB * (magicBᴴ * kron a b * magicB) * magicBᴴ := by
    calc kron a b = (magicB * magicBᴴ) * kron a b * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hK2 : kron c d = magicB * (magicBᴴ * kron c d * magicB) * magicBᴴ := by
    calc kron c d = (magicB * magicBᴴ) * kron c d * (magicB * magicBᴴ) := by
          rw [magicB_unitary']; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  set U1 := magicBᴴ * kron a b * magicB with hU1def
  set U2 := magicBᴴ * kron c d * magicB with hU2def
  have hT : (magicBᴴ)ᵀ = magicB.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  obtain ⟨X, hX⟩ : ∃ X, X = magicCoord (zmat ψ) := ⟨_, rfl⟩
  have hz : zmat ψ = magicB * X * magicBᵀ := by rw [hX]; exact zmat_eq_coord _
  rw [← hX, zmat_localApply, hz]
  unfold magicCoord
  conv_lhs => rw [hK1, hK2, Matrix.transpose_mul, Matrix.transpose_mul, hT]
  calc _ = (magicBᴴ * magicB) * U1 * (magicBᴴ * magicB) * X *
          (magicBᵀ * magicB.map (starRingEnd ℂ)) * U2ᵀ * (magicBᵀ * magicB.map (starRingEnd ℂ)) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [magicB_unitary, hBB]; simp only [Matrix.mul_one, Matrix.one_mul]

theorem frob_eq_trace (Z : Mat4) :
    ((∑ i, ∑ j, Complex.normSq (Z i j) : ℝ) : ℂ) = Matrix.trace (Z * Zᴴ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

theorem normSqPsi_eq_frob (ψ : Psi) : normSqPsi ψ = ∑ i, ∑ j, Complex.normSq (zmat ψ i j) := by
  unfold normSqPsi
  simp only [Fintype.sum_prod_type, zmat, Matrix.of_apply]

theorem frob_coord (ψ : Psi) :
    ∑ i, ∑ j, Complex.normSq (magicCoord (zmat ψ) i j) = normSqPsi ψ := by
  have h1 := frob_eq_trace (magicCoord (zmat ψ))
  have h2 := frob_eq_trace (zmat ψ)
  rw [coord_mul_conjTranspose, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    magicB_unitary', Matrix.one_mul] at h1
  rw [normSqPsi_eq_frob]
  have : (((∑ i, ∑ j, Complex.normSq (magicCoord (zmat ψ) i j) : ℝ)) : ℂ) =
      ((∑ i, ∑ j, Complex.normSq (zmat ψ i j) : ℝ) : ℂ) := by rw [h1, h2]
  exact_mod_cast this

theorem spin_sq_sum (ψ : Psi) :
    spinFlipForm ψ = ∑ i, ∑ j, (magicCoord (zmat ψ) i j) ^ 2 := by
  rw [spinFlip_coord]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem exists_phase_sq (t : ℂ) : ∃ θ : ℝ, Complex.exp (θ * Complex.I) ^ 2 * t = (‖t‖ : ℂ) := by
  refine ⟨-(Complex.arg t) / 2, ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I t
  have e : Complex.exp (((-(Complex.arg t) / 2 : ℝ) : ℂ) * Complex.I) ^ 2 =
      Complex.exp (-(Complex.arg t : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  calc Complex.exp (-(Complex.arg t : ℂ) * Complex.I) * t
      = Complex.exp (-(Complex.arg t : ℂ) * Complex.I) *
          (‖t‖ * Complex.exp (Complex.arg t * Complex.I)) := by rw [h]
    _ = ‖t‖ := by
      rw [mul_left_comm, ← Complex.exp_add]; simp

/-- Real/imaginary decomposition of a unit complex matrix with `∑ Y² = r` real. -/
theorem re_part_norm {Y : Mat4} (h1 : ∑ i, ∑ j, Complex.normSq (Y i j) = 1) {r : ℝ}
    (h2 : ∑ i, ∑ j, Y i j ^ 2 = (r : ℂ)) :
    ∑ i, ∑ j, (Y i j).re ^ 2 = (1 + r) / 2 := by
  have h3 := congrArg Complex.re h2
  simp only [Complex.re_sum, pow_two, Complex.mul_re, Complex.ofReal_re] at h3
  have e1 : ∀ i j, Complex.normSq (Y i j) = (Y i j).re ^ 2 + (Y i j).im ^ 2 := fun i j => by
    rw [Complex.normSq_apply]; ring
  simp only [e1, Finset.sum_add_distrib] at h1
  have e2 : ∑ i, ∑ j, ((Y i j).re * (Y i j).re - (Y i j).im * (Y i j).im) =
      ∑ i, ∑ j, (Y i j).re ^ 2 - ∑ i, ∑ j, (Y i j).im ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  linarith

/-- **Real SVD** (signed, with `SO(4)` factors) of a real `4×4` matrix, from `lem:fqe-real-gram`. -/
theorem real_svd (M : RMat4) :
    ∃ P Q : RMat4, Pᵀ * P = 1 ∧ Qᵀ * Q = 1 ∧ P.det = 1 ∧ Q.det = 1 ∧
      ∃ D : Fin 2 × Fin 2 → ℝ, P * M * Qᵀ = Matrix.diagonal D := by
  have h1 : ∀ i j, ((rc M * (rc M)ᴴ) i j).im = 0 := by
    intro i j
    rw [rc_conjTranspose, ← map_mul]
    simp [rc]
  have h2 : ∀ i j, (((rc M)ᴴ * rc M) i j).im = 0 := by
    intro i j
    rw [rc_conjTranspose, ← map_mul]
    simp [rc]
  obtain ⟨O₁, O₂, v, hO₁, hO₂, hd₁, hd₂, hZ⟩ := real_gram_square_SO (0, 0) (rc M) h1 h2
  have hO₁' : O₁ * O₁ᵀ = 1 := mul_eq_one_comm.mp hO₁
  have hO₂' : O₂ * O₂ᵀ = 1 := mul_eq_one_comm.mp hO₂
  have key : rc (O₁ᵀ * M * O₂) = Matrix.diagonal v := by
    have e1 : rc (O₁ᵀ * O₁) = 1 := by rw [hO₁]; simp
    have e2 : rc (O₂ᵀ * O₂) = 1 := by rw [hO₂]; simp
    rw [map_mul, map_mul, ← rc_transpose]
    have : (rc O₁)ᵀ * rc O₁ = 1 := by rw [rc_transpose]; rw [← map_mul]; exact e1
    have h3 : (rc O₂)ᵀ * rc O₂ = 1 := by rw [rc_transpose]; rw [← map_mul]; exact e2
    rw [hZ]
    calc (rc O₁)ᵀ * (rc O₁ * Matrix.diagonal v * (rc O₂)ᵀ) * rc O₂
        = ((rc O₁)ᵀ * rc O₁) * Matrix.diagonal v * ((rc O₂)ᵀ * rc O₂) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [this, h3]; simp
  refine ⟨O₁ᵀ, O₂ᵀ, ?_, ?_, ?_, ?_, fun j => (O₁ᵀ * M * O₂) j j, ?_⟩
  · rw [Matrix.transpose_transpose]; exact hO₁'
  · rw [Matrix.transpose_transpose]; exact hO₂'
  · rw [Matrix.det_transpose]; exact hd₁
  · rw [Matrix.det_transpose]; exact hd₂
  · rw [Matrix.transpose_transpose]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · have := congrFun (congrFun key i) j
      simp only [rc, RingHom.mapMatrix_apply, Matrix.map_apply, Complex.ofRealHom_eq_coe,
        Matrix.diagonal_apply, hij, ite_false] at this
      simp [Matrix.diagonal_apply, hij]
      exact_mod_cast this

theorem exists_LU_rotate {P Q : RMat4} (hP : Pᵀ * P = 1) (hdP : P.det = 1) (hQ : Qᵀ * Q = 1)
    (hdQ : Q.det = 1) {e : ℂ} (he : Complex.normSq e = 1) (ψ : Psi) :
    ∃ ψ'', LUEquiv ψ ψ'' ∧
      magicCoord (zmat ψ'') = rc P * (e • magicCoord (zmat ψ)) * (rc Q)ᵀ := by
  obtain ⟨a, b, ha, hb, hab⟩ := Real4.of_SO hP hdP
  obtain ⟨c, d, hc, hd, hcd⟩ := Real4.of_SO hQ hdQ
  have hee : (starRingEnd ℂ) e * e = 1 := by
    have : (Complex.normSq e : ℂ) = 1 := by rw [he]; simp
    rwa [Complex.normSq_eq_conj_mul_self] at this
  refine ⟨localApply (e • a) b c d ψ, ⟨e • a, b, c, d, ?_, hb, hc, hd, rfl⟩, ?_⟩
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ha]
    rw [show star e * e = 1 from hee, one_smul]
  · rw [coord_localApply_gen]
    have e1 : kron (e • a) b = e • kron a b := by unfold kron; rw [Matrix.smul_kronecker]
    rw [e1, Matrix.mul_smul, Matrix.smul_mul, hab, hcd]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rfl

/-! ### The sign vectors of `𝓗` -/

def epsZ : Fin 32 → Fin 4 → ℤ :=
  ![![0, 1, 1, 1],
    ![0, -1, 1, 1],
    ![0, 1, -1, 1],
    ![0, -1, -1, 1],
    ![0, 1, 1, -1],
    ![0, -1, 1, -1],
    ![0, 1, -1, -1],
    ![0, -1, -1, -1],
    ![1, 0, 1, 1],
    ![-1, 0, 1, 1],
    ![1, 0, -1, 1],
    ![-1, 0, -1, 1],
    ![1, 0, 1, -1],
    ![-1, 0, 1, -1],
    ![1, 0, -1, -1],
    ![-1, 0, -1, -1],
    ![1, 1, 0, 1],
    ![-1, 1, 0, 1],
    ![1, -1, 0, 1],
    ![-1, -1, 0, 1],
    ![1, 1, 0, -1],
    ![-1, 1, 0, -1],
    ![1, -1, 0, -1],
    ![-1, -1, 0, -1],
    ![1, 1, 1, 0],
    ![-1, 1, 1, 0],
    ![1, -1, 1, 0],
    ![-1, -1, 1, 0],
    ![1, 1, -1, 0],
    ![-1, 1, -1, 0],
    ![1, -1, -1, 0],
    ![-1, -1, -1, 0]]


theorem epsOf_eq (a : Fin 32) (j : Fin 4) : epsOf a j = (epsZ a j : ℝ) := by
  fin_cases a <;> fin_cases j <;> simp [epsOf, epsZ]

/-- Every position and every sign pattern on the other three coordinates occurs among the 32
representatives. -/
theorem eps_exists_aux : ∀ (i : Fin 4) (τ : Fin 4 → Bool), ∃ a : Fin 32, idxI a = i ∧
    ∀ j : Fin 4, j ≠ i → epsZ a j = if τ j then 1 else -1 := by
  decide

theorem eps_exists (p₀ : Fin 2 × Fin 2) (τ : Fin 2 × Fin 2 → Bool) :
    ∃ a : Fin 32, idxI a = pairIdx p₀ ∧
      ∀ p : Fin 2 × Fin 2, p ≠ p₀ → epsOf a (pairIdx p) = if τ p then 1 else -1 := by
  have hbij : Function.Bijective pairIdx := by
    constructor
    · intro p q h
      rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
      fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [pairIdx] at h ⊢
    · intro j
      fin_cases j
      · exact ⟨(0, 0), by simp [pairIdx]⟩
      · exact ⟨(0, 1), by simp [pairIdx]⟩
      · exact ⟨(1, 0), by simp [pairIdx]⟩
      · exact ⟨(1, 1), by simp [pairIdx]⟩
  set e := Equiv.ofBijective pairIdx hbij with he
  obtain ⟨a, ha1, ha2⟩ := eps_exists_aux (pairIdx p₀) (fun j => τ (e.symm j))
  refine ⟨a, ha1, fun p hp => ?_⟩
  have hne : pairIdx p ≠ pairIdx p₀ := fun h => hp (hbij.1 h)
  rw [epsOf_eq, ha2 _ hne]
  have : e.symm (pairIdx p) = p := by
    rw [he]; exact (Equiv.ofBijective pairIdx hbij).symm_apply_apply p
  simp only [this]
  split_ifs <;> simp

theorem pairIdx_inj : Function.Injective pairIdx := by
  intro p q h
  rcases p with ⟨a, b⟩; rcases q with ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> simp [pairIdx] at h ⊢

/-- Real and imaginary parts of the overlap `⟨G(η_a), χ⟩` with `idxI a` the position `p₀`. -/
theorem ip_eta_parts (a : Fin 32) (p₀ : Fin 2 × Fin 2) (ha : idxI a = pairIdx p₀) (χ : Psi) :
    (ip (Gv (etaV a)) χ).re =
        (magicCoord (zmat χ) p₀ p₀).re / Real.sqrt 2 +
          ∑ p, epsOf a (pairIdx p) / Real.sqrt 6 * (magicCoord (zmat χ) p p).im ∧
    (ip (Gv (etaV a)) χ).im =
        (magicCoord (zmat χ) p₀ p₀).im / Real.sqrt 2 -
          ∑ p, epsOf a (pairIdx p) / Real.sqrt 6 * (magicCoord (zmat χ) p p).re := by
  set X := magicCoord (zmat χ) with hX
  have hterm : ∀ p, (starRingEnd ℂ) (etaV a p) * X p p =
      (((if p = p₀ then 1 / Real.sqrt 2 else 0 : ℝ) : ℂ) -
        Complex.I * ((epsOf a (pairIdx p) / Real.sqrt 6 : ℝ) : ℂ)) * X p p := by
    intro p
    have : etaV a p = ((if p = p₀ then 1 / Real.sqrt 2 else 0 : ℝ) : ℂ) +
        Complex.I * ((epsOf a (pairIdx p) / Real.sqrt 6 : ℝ) : ℂ) := by
      simp only [etaV, etaC, ha]
      by_cases h : p = p₀
      · subst h; simp
      · have : pairIdx p ≠ pairIdx p₀ := fun h' => h (pairIdx_inj h')
        simp [h, this]
    rw [this, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [ip_Gv_coord, ← hX]
  simp only [hterm]
  have pw : ∀ (ρ e : ℝ) (z : ℂ), (((ρ : ℂ) - Complex.I * (e : ℂ)) * z).re = ρ * z.re + e * z.im ∧
      (((ρ : ℂ) - Complex.I * (e : ℂ)) * z).im = ρ * z.im - e * z.re := by
    intro ρ e z
    simp [Complex.mul_re, Complex.mul_im]
    ring
  have hρ : ∀ f : Fin 2 × Fin 2 → ℝ, ∑ p, (if p = p₀ then 1 / Real.sqrt 2 else 0 : ℝ) * f p =
      f p₀ / Real.sqrt 2 := by
    intro f
    simp [ite_mul, Finset.sum_ite_eq']
    ring
  constructor
  · rw [Complex.re_sum]
    rw [Finset.sum_congr rfl (fun p _ => (pw (if p = p₀ then 1 / Real.sqrt 2 else 0)
      (epsOf a (pairIdx p) / Real.sqrt 6) (X p p)).1)]
    rw [Finset.sum_add_distrib, hρ (fun p => (X p p).re)]
  · rw [Complex.im_sum]
    rw [Finset.sum_congr rfl (fun p _ => (pw (if p = p₀ then 1 / Real.sqrt 2 else 0)
      (epsOf a (pairIdx p) / Real.sqrt 6) (X p p)).2)]
    rw [Finset.sum_sub_distrib, hρ (fun p => (X p p).im)]

/-- **Diagonal overlap bound.** For a unit `χ` with magic coordinates `X`, every position `p₀` gives
`Φ(χ) ≥ (Re X_{p₀p₀})²/2 + (∑_{p ≠ p₀} |Re X_{pp}|)²/6`: average the squared overlaps with the two
representatives with large component at `p₀` and opposite sign patterns `±sgn(Re X_{pp})`. -/
theorem Phi_ge_diag {χ : Psi} (hχ : normSqPsi χ = 1) (p₀ : Fin 2 × Fin 2) :
    ((magicCoord (zmat χ) p₀ p₀).re) ^ 2 / 2 +
        (∑ p ∈ Finset.univ.erase p₀, |(magicCoord (zmat χ) p p).re|) ^ 2 / 6 ≤ Phi χ := by
  set X := magicCoord (zmat χ) with hX
  have hΦ : ∀ a : Fin 32, Complex.normSq (ip (Gv (etaV a)) χ) ≤ Phi χ := by
    intro a
    have := le_Phi hχ (orbit_etaV a)
    rwa [ip_comm χ, Complex.normSq_conj] at this
  obtain ⟨a₁, h1i, h1e⟩ := eps_exists p₀ (fun p => decide (0 ≤ (X p p).re))
  obtain ⟨a₂, h2i, h2e⟩ := eps_exists p₀ (fun p => !decide (0 ≤ (X p p).re))
  obtain ⟨hr1, hi1⟩ := ip_eta_parts a₁ p₀ h1i χ
  obtain ⟨hr2, hi2⟩ := ip_eta_parts a₂ p₀ h2i χ
  rw [← hX] at hr1 hi1 hr2 hi2
  have e0 : ∀ a : Fin 32, idxI a = pairIdx p₀ → epsOf a (pairIdx p₀) = 0 := by
    intro a ha; rw [← ha]; exact eps_self a
  have hneg : ∀ p, epsOf a₂ (pairIdx p) = - epsOf a₁ (pairIdx p) := by
    intro p
    by_cases hp : p = p₀
    · subst hp; rw [e0 a₁ h1i, e0 a₂ h2i]; simp
    · rw [h1e p hp, h2e p hp]
      by_cases h : 0 ≤ (X p p).re <;> simp [h]
  have hpos : ∀ p, p ≠ p₀ → epsOf a₁ (pairIdx p) * (X p p).re = |(X p p).re| := by
    intro p hp
    rw [h1e p hp]
    by_cases h : 0 ≤ (X p p).re
    · simp [h, abs_of_nonneg h]
    · simp [h, abs_of_neg (not_le.mp h)]
  set S : ℝ := ∑ p ∈ Finset.univ.erase p₀, |(X p p).re| with hS
  have hsum : ∑ p, epsOf a₁ (pairIdx p) * (X p p).re = S := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p₀), e0 a₁ h1i, zero_mul, zero_add]
    exact Finset.sum_congr rfl fun p hp => hpos p (Finset.ne_of_mem_erase hp)
  set C : ℝ := ∑ p, epsOf a₁ (pairIdx p) / Real.sqrt 6 * (X p p).im with hC
  have hC2 : ∑ p, epsOf a₂ (pairIdx p) / Real.sqrt 6 * (X p p).im = -C := by
    rw [hC, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hneg p]; ring
  have hT : ∑ p, epsOf a₁ (pairIdx p) / Real.sqrt 6 * (X p p).re = S / Real.sqrt 6 := by
    rw [← hsum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => by ring
  have hT2 : ∑ p, epsOf a₂ (pairIdx p) / Real.sqrt 6 * (X p p).re = -(S / Real.sqrt 6) := by
    rw [← hT, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hneg p]; ring
  rw [hC2] at hr2
  rw [hT] at hi1
  rw [hT2] at hi2
  have n1 := hΦ a₁
  have n2 := hΦ a₂
  rw [Complex.normSq_apply, hr1, hi1] at n1
  rw [Complex.normSq_apply, hr2, hi2] at n2
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs6 : 0 < Real.sqrt 6 := by positivity
  set A := (X p₀ p₀).re / Real.sqrt 2 with hA
  set B := (X p₀ p₀).im / Real.sqrt 2
  have hA2 : A ^ 2 = (X p₀ p₀).re ^ 2 / 2 := by rw [hA, div_pow, h2]
  have hT2' : (S / Real.sqrt 6) ^ 2 = S ^ 2 / 6 := by rw [div_pow, h6]
  nlinarith [sq_nonneg C, sq_nonneg B]

theorem alg3 {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hba : b ≤ a) (hca : c ≤ a)
    (hda : d ≤ a) : (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) / 3 ≤ a ^ 2 / 2 + (b + c + d) ^ 2 / 6 := by
  have key : b ^ 2 + c ^ 2 + d ^ 2 ≤ a ^ 2 + 2 * (b * c + b * d + c * d) := by
    rcases le_total c b with h1 | h1 <;> rcases le_total d b with h2 | h2 <;>
      rcases le_total d c with h3 | h3 <;>
      nlinarith [mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd, mul_self_le_mul_self hb hba,
        mul_self_le_mul_self hc hca, mul_self_le_mul_self hd hda]
  nlinarith [key]

theorem alg4 (u : Fin 2 × Fin 2 → ℝ) (p₀ : Fin 2 × Fin 2) (h0 : ∀ p, 0 ≤ u p)
    (hmax : ∀ p, u p ≤ u p₀) :
    (∑ p, u p ^ 2) / 3 ≤ u p₀ ^ 2 / 2 + (∑ p ∈ Finset.univ.erase p₀, u p) ^ 2 / 6 := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ p₀)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h00 := h0 (0, 0); have h01 := h0 (0, 1); have h10 := h0 (1, 0); have h11 := h0 (1, 1)
  have m00 := hmax (0, 0); have m01 := hmax (0, 1); have m10 := hmax (1, 0); have m11 := hmax (1, 1)
  fin_cases p₀ <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] at m00 m01 m10 m11 ⊢
  · have := alg3 h01 h10 h11 m01 m10 m11; nlinarith [this]
  · have := alg3 h00 h10 h11 m00 m10 m11; nlinarith [this]
  · have := alg3 h00 h01 h11 m00 m01 m11; nlinarith [this]
  · have := alg3 h00 h01 h10 m00 m01 m10; nlinarith [this]

theorem re_rotate (P Q : RMat4) (Y : Mat4) (p q : Fin 2 × Fin 2) :
    ((rc P * Y * (rc Q)ᵀ) p q).re = (P * Matrix.of (fun i j => (Y i j).re) * Qᵀ) p q := by
  simp only [Matrix.mul_apply, rc, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Complex.ofRealHom_eq_coe, Complex.re_sum, Matrix.of_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul, Complex.re_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Complex.mul_re]

theorem trace_transpose_mul_eq (A : RMat4) : Matrix.trace (Aᵀ * A) = ∑ i, ∑ j, A i j ^ 2 := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem sum_sq_diag_eq {P Q M : RMat4} (hP : Pᵀ * P = 1) (hQ : Qᵀ * Q = 1)
    {D : Fin 2 × Fin 2 → ℝ} (h : P * M * Qᵀ = Matrix.diagonal D) :
    ∑ p, D p ^ 2 = ∑ i, ∑ j, M i j ^ 2 := by
  have f1 : Matrix.trace ((Matrix.diagonal D)ᵀ * Matrix.diagonal D) = ∑ p, D p ^ 2 := by
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [← f1, ← h, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    ← trace_transpose_mul_eq]
  have e : Q * (Mᵀ * Pᵀ) * (P * M * Qᵀ) = Q * (Mᵀ * (Pᵀ * P) * M) * Qᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e, hP, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQ]
  simp

/-- **`lem:fqe-hs-fidelity-floor`** (HS fidelity floor from real singular values): for every unit
pure four-qubit state, `Φ(ψ) ≥ (1 + √τ(ψ))/6`.  Proof as in the paper: phase `s = tr(XᵀX) ≥ 0`,
real SVD of `Re X` (from `lem:fqe-real-gram`), two Hermitian-symmetric representatives, and
`½m² + (x+y+z)²/6 ≥ (m²+x²+y²+z²)/3`. -/
theorem fidelity_floor {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))) / 6 ≤ Phi ψ := by
  set X := magicCoord (zmat ψ) with hX
  set t := spinFlipForm ψ with ht
  obtain ⟨θ, hθ⟩ := exists_phase_sq t
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hen : Complex.normSq e = 1 := by
    rw [he, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; norm_num
  set Y : Mat4 := e • X with hY
  have hY1 : ∑ i, ∑ j, Complex.normSq (Y i j) = 1 := by
    have : ∀ i j, Complex.normSq (Y i j) = Complex.normSq (X i j) := fun i j => by
      simp only [hY, Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, hen, one_mul]
    simp only [this]
    rw [hX, frob_coord, hψ]
  have hY2 : ∑ i, ∑ j, Y i j ^ 2 = ((‖t‖ : ℝ) : ℂ) := by
    have : ∀ i j, Y i j ^ 2 = e ^ 2 * X i j ^ 2 := fun i j => by
      simp only [hY, Matrix.smul_apply, smul_eq_mul]; ring
    simp only [this, ← Finset.mul_sum]
    rw [← hθ, ht, spin_sq_sum]
  have hM := re_part_norm hY1 hY2
  set M : RMat4 := Matrix.of (fun i j => (Y i j).re) with hMdef
  obtain ⟨P, Q, hP, hQ, hdP, hdQ, D, hD⟩ := real_svd M
  obtain ⟨ψ'', hLU, hcoord⟩ := exists_LU_rotate hP hdP hQ hdQ hen ψ
  have hu'' : normSqPsi ψ'' = 1 := by rw [normSqPsi_LUEquiv hLU, hψ]
  have hΦ : Phi ψ'' = Phi ψ := Phi_LUEquiv hLU hψ
  have hc' : magicCoord (zmat ψ'') = rc P * Y * (rc Q)ᵀ := hcoord
  have hDre : ∀ p, (magicCoord (zmat ψ'') p p).re = D p := by
    intro p
    have h1 := re_rotate P Q Y p p
    have h2 := congrFun (congrFun hD p) p
    rw [hc', h1]
    rw [h2]
    simp
  have hsum : ∑ p, D p ^ 2 = (1 + ‖t‖) / 2 := by
    rw [sum_sq_diag_eq hP hQ hD]; exact hM
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_max_image Finset.univ (fun p => |D p|) Finset.univ_nonempty
  have h1 := Phi_ge_diag hu'' p₀
  simp only [hDre] at h1
  have h2 := alg4 (fun p => |D p|) p₀ (fun p => abs_nonneg _) (fun p => hp₀ p (Finset.mem_univ p))
  simp only [sq_abs] at h2 h1
  have h3 : Real.sqrt (Complex.normSq t) = ‖t‖ := by
    rw [Complex.norm_def]
  rw [h3, ← hΦ]
  rw [hsum] at h2
  linarith

theorem fidelityFloor_all {ψ : Psi} (hψ : normSqPsi ψ = 1) : FidelityFloor ψ := by
  have h := fidelity_floor hψ
  have h0 : 0 ≤ Real.sqrt (Complex.normSq (spinFlipForm ψ)) := Real.sqrt_nonneg _
  show 1 / 6 ≤ Phi ψ
  linarith

/-- `d² ≤ 2(1 - √((1+√τ)/6)) ≤ 2(1 - 1/√6)` (`lem:fqe-hs-fidelity-floor`, distance form). -/
theorem orbitDist_sq_le_tau {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    orbitDist ψ ^ 2 ≤ 2 * (1 - Real.sqrt ((1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))) / 6)) ∧
      2 * (1 - Real.sqrt ((1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))) / 6)) ≤
        2 * (1 - 1 / Real.sqrt 6) := by
  have h0 : 0 ≤ Real.sqrt (Complex.normSq (spinFlipForm ψ)) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · rw [orbitDist_sq hψ]
    have := Real.sqrt_le_sqrt (fidelity_floor hψ)
    linarith
  · have : 1 / Real.sqrt 6 ≤ Real.sqrt ((1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))) / 6) := by
      rw [one_div, ← Real.sqrt_inv]
      exact Real.sqrt_le_sqrt (by rw [inv_eq_one_div]; linarith)
    linarith

theorem overlap_ge_dist_tau {ψ : Psi} (hψ : normSqPsi ψ = 1) :
    (6 + Real.sqrt (6 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))) / 12 * orbitDist ψ ^ 2
      ≤ 1 - Phi ψ := by
  rw [one_sub_Phi_eq hψ]
  set s := Real.sqrt (Complex.normSq (spinFlipForm ψ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hfl := fidelity_floor hψ
  have h : Real.sqrt (6 * (1 + s)) / 6 ≤ Real.sqrt (Phi ψ) := by
    apply Real.le_sqrt_of_sq_le
    have : Real.sqrt (6 * (1 + s)) ^ 2 = 6 * (1 + s) := Real.sq_sqrt (by positivity)
    rw [div_pow, this]
    linarith
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- `Q ≥ ((6+√(6(1+√τ)))/12) d²` from `GlobalOverlap` (middle inequalities of
`eq:fqe-global-overlap-sharp`). -/
theorem orbitDist_sq_le_Q_tau {ψ : Psi} (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ) :
    (6 + Real.sqrt (6 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))) / 12 * orbitDist ψ ^ 2
      ≤ sexticQ ψ :=
  le_trans (overlap_ge_dist_tau hψ) hg

/-- Entropy gap with the `τ`-dependent constant: `δ ≥ k ((6+√(6(1+√τ)))/12) d²`. -/
theorem entropy_gap_dist_tau {ψ : Psi} (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ) :
    (Real.log 3 - 1) / (2 * Real.log 2) *
        ((6 + Real.sqrt (6 * (1 + Real.sqrt (Complex.normSq (spinFlipForm ψ))))) / 12 *
          orbitDist ψ ^ 2) ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ := by
  have h := entropy_gap_ge_of_overlap ψ hψ (orbitDist_sq_le_Q_tau hψ hg)
  rw [meanEntropy_M4] at h
  exact h

/-! ### The estimates of `PaperEOrbitDistance` with the floor discharged -/

theorem orbitDist_sq_le_Q_of_overlap {ψ : Psi} (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ) :
    (6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2 ≤ sexticQ ψ ∧
      orbitDist ψ ^ 2 ≤ 12 / (6 + Real.sqrt 6) * sexticQ ψ ∧ 7 / 10 < (6 + Real.sqrt 6) / 12 :=
  orbitDist_sq_le_Q hψ hg (fidelityFloor_all hψ)

/-- **`thm:fqe-orbit-stability`, global part**, for every unit state, conditional only on
`Q ≥ 1 - Φ` (`thm:fqe-global-overlap`): `δ ≥ k((6+√6)/12) d² > d²/20`. -/
theorem entropy_gap_orbit_stability_dist_of_overlap {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (hg : GlobalOverlap ψ) :
    orbitDist ψ ^ 2 ≤ 12 / (6 + Real.sqrt 6) * sexticQ ψ ∧
    (Real.log 3 - 1) / (2 * Real.log 2) * ((6 + Real.sqrt 6) / 12 * orbitDist ψ ^ 2)
        ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ ∧
      1 / 20 < (Real.log 3 - 1) / (2 * Real.log 2) * ((6 + Real.sqrt 6) / 12) ∧
      1 / 20 * orbitDist ψ ^ 2 ≤ 1 + Real.log 3 / (2 * Real.log 2) - meanEntropy ψ :=
  entropy_gap_orbit_stability_dist hψ hg (fidelityFloor_all hψ)

theorem majorant_gap_orbit_of_overlap {f : ℝ → ℝ} {a b c d : ℝ} (hM : Majorant f a b c d)
    (ha : 0 ≤ a) (hα : 0 ≤ -b - 17 * a / 12) {ψ : Psi} (hψ : normSqPsi ψ = 1)
    (hg : GlobalOverlap ψ) :
    (6 + Real.sqrt 6) / 12 / 3 * min ((-b - 17 * a / 12) / 6) (a / 12) * orbitDist ψ ^ 2 ≤
      meanSpec f M4 - meanSpec f ψ :=
  majorant_gap_orbit hM ha hα hψ hg (fidelityFloor_all hψ)

theorem tsallis_gap_orbit_of_overlap {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) {ψ : Psi}
    (hψ : normSqPsi ψ = 1) (hg : GlobalOverlap ψ) :
    0 < min ((-tsB q - 17 * tsA q / 12) / 6) (tsA q / 12) ∧
    (6 + Real.sqrt 6) / 12 / 3 * min ((-tsB q - 17 * tsA q / 12) / 6) (tsA q / 12) *
        orbitDist ψ ^ 2 ≤ tsallisCeiling q - meanTsallis q ψ :=
  tsallis_gap_orbit h0 h2 h1 hψ hg (fidelityFloor_all hψ)

/-! ### Axiom audit -/

/-- info: 'FormalResearch.FourQubitEntropy.OD.fidelity_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fidelity_floor

/-- info: 'FormalResearch.FourQubitEntropy.OD.fidelityFloor_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fidelityFloor_all

/-- info: 'FormalResearch.FourQubitEntropy.OD.overlap_ge_dist_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms overlap_ge_dist_tau

/-- info: 'FormalResearch.FourQubitEntropy.OD.entropy_gap_dist_tau' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_gap_dist_tau

/-- info: 'FormalResearch.FourQubitEntropy.OD.entropy_gap_orbit_stability_dist_of_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_gap_orbit_stability_dist_of_overlap

/-- info: 'FormalResearch.FourQubitEntropy.OD.majorant_gap_orbit_of_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms majorant_gap_orbit_of_overlap

/-- info: 'FormalResearch.FourQubitEntropy.OD.tsallis_gap_orbit_of_overlap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tsallis_gap_orbit_of_overlap

end FormalResearch.FourQubitEntropy.OD

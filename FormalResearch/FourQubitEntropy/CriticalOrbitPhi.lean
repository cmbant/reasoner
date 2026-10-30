import FormalResearch.FourQubitEntropy.CriticalOrbitNormal
import FormalResearch.FourQubitEntropy.PaperEGenConvexRoofEq
import FormalResearch.FourQubitEntropy.PaperECriticalSexticLU

/-!
# Critical-orbit stability: the HS fidelity `Φ` and the distance `d`

`Φ(ψ) = sup_{χ ∈ 𝓜} |⟨ψ, χ⟩|²` over the two LU orbits `𝓜` of `M₄` and `conj M₄`
(`lu_orbit_stability.tex`, Appendix `sec:fqe-orbit-stability`), and `d² = 2 - 2 √Φ`.  Unitary
local operators replace `SU(2)`, which changes `χ` only by a phase, so `|⟨ψ, χ⟩|²` is unchanged.

For `η_a` among the 32 representatives `𝓗` (`etaV`), `G(η_a)` lies in `𝓜` (`orbit_etaV`, by
`LU_M4_of_caseC`) and `|⟨G(v), G(η_a)⟩|² = qH a v` (`qH_eq_normSq_ip`); hence `qH a v ≤ Φ(ψ)` for
every `ψ` locally unitarily equivalent to `G(v)` (`qH_le_Phi`), and `1/4 ≤ Φ(ψ)` by the frame identity
`∑_a qH a v = 8 ‖v‖²` (`sum_qH`).
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- The two LU orbits `𝓜` of `M₄` and `conj M₄`. -/
def InOrbit (χ : Psi) : Prop := LUEquiv M4 χ ∨ LUEquiv (Psi.conj M4) χ

/-- `Φ(ψ) = sup_{χ ∈ 𝓜} |⟨ψ, χ⟩|²`. -/
noncomputable def Phi (ψ : Psi) : ℝ :=
  sSup {x : ℝ | ∃ χ, InOrbit χ ∧ x = Complex.normSq (ip ψ χ)}

/-- `d² = 2 - 2 √Φ`. -/
noncomputable def dist2 (ψ : Psi) : ℝ := 2 - 2 * Real.sqrt (Phi ψ)

theorem normSqPsi_InOrbit {χ : Psi} (h : InOrbit χ) : normSqPsi χ = 1 := by
  rcases h with h | h
  · rw [normSqPsi_LUEquiv h, M4_unit]
  · rw [normSqPsi_LUEquiv h, normSqPsi_conj, M4_unit]

theorem normSqPsi_nonneg' (ψ : Psi) : 0 ≤ normSqPsi ψ := by
  rw [normSqPsi_eq_sum]; exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Cauchy--Schwarz for unit vectors. -/
theorem normSq_ip_le {φ χ : Psi} (hφ : normSqPsi φ = 1) (hχ : normSqPsi χ = 1) :
    Complex.normSq (ip φ χ) ≤ 1 := by
  set s : ℂ := ip φ χ with hs
  have hφφ : ip φ φ = 1 := by rw [ip_self, hφ]; simp
  have hχχ : ip χ χ = 1 := by rw [ip_self, hχ]; simp
  have hχφ : ip χ φ = (starRingEnd ℂ) s := by rw [ip_comm χ φ, ← hs]
  have h : ip (χ - s • φ) (χ - s • φ) = 1 - (Complex.normSq s : ℂ) := by
    rw [ip_sub_smul_left, ip_sub_smul_right, ip_sub_smul_right, hχχ, hχφ, hφφ, ← hs,
      Complex.normSq_eq_conj_mul_self]
    ring
  rw [ip_self] at h
  have h2 : normSqPsi (χ - s • φ) = 1 - Complex.normSq s := by exact_mod_cast h
  have := normSqPsi_nonneg' (χ - s • φ)
  linarith

theorem InOrbit_M4 : InOrbit M4 := Or.inl (LUEquiv.refl _)

theorem le_Phi {ψ χ : Psi} (hψ : normSqPsi ψ = 1) (hχ : InOrbit χ) :
    Complex.normSq (ip ψ χ) ≤ Phi ψ := by
  refine le_csSup ⟨1, ?_⟩ ⟨χ, hχ, rfl⟩
  rintro _ ⟨χ', hχ', rfl⟩
  exact normSq_ip_le hψ (normSqPsi_InOrbit hχ')

theorem Phi_le_one {ψ : Psi} (hψ : normSqPsi ψ = 1) : Phi ψ ≤ 1 := by
  refine csSup_le ⟨_, M4, InOrbit_M4, rfl⟩ ?_
  rintro _ ⟨χ', hχ', rfl⟩
  exact normSq_ip_le hψ (normSqPsi_InOrbit hχ')

/-! ### The vectors `G(η_a)` -/

/-- The coordinates of `η_a`: `1/√2` at `i`, `ε_j i/√6` elsewhere. -/
noncomputable def etaC (a : Fin 32) : Fin 4 → ℂ := fun j =>
  (if j = idxI a then ((1 / Real.sqrt 2 : ℝ) : ℂ) else 0) +
    Complex.I * ((epsOf a j / Real.sqrt 6 : ℝ) : ℂ)

/-- The position of a pair in `Fin 4`. -/
def pairIdx (p : Fin 2 × Fin 2) : Fin 4 := ⟨2 * p.1.val + p.2.val, by omega⟩

theorem coord_pairIdx (v : V) (p : Fin 2 × Fin 2) : coord v (pairIdx p) = v p := by
  rcases p with ⟨a, b⟩; fin_cases a <;> fin_cases b <;> simp [coord, pairIdx]

/-- The vector `η_a` as a vector of `ℂ^{2×2}`. -/
noncomputable def etaV (a : Fin 32) : V := fun p => etaC a (pairIdx p)

theorem coord_etaV (a : Fin 32) (j : Fin 4) : coord (etaV a) j = etaC a j := by
  fin_cases j <;> simp [coord, etaV, pairIdx]

theorem eps_sq (a : Fin 32) (j : Fin 4) (h : j ≠ idxI a) : epsOf a j ^ 2 = 1 := by
  fin_cases a <;> fin_cases j <;> simp [epsOf, idxI] at h ⊢

theorem eps_self (a : Fin 32) : epsOf a (idxI a) = 0 := by
  fin_cases a <;> simp [epsOf, idxI]

theorem normSq_etaC (a : Fin 32) (j : Fin 4) :
    Complex.normSq (etaC a j) = if j = idxI a then 1 / 2 else 1 / 6 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  by_cases h : j = idxI a
  · simp [etaC, h, eps_self, Complex.normSq_apply]
  · have := eps_sq a j h
    simp [etaC, h, Complex.normSq_apply]
    field_simp
    nlinarith

theorem sq_etaC (a : Fin 32) (j : Fin 4) :
    etaC a j ^ 2 = if j = idxI a then 1 / 2 else -(1 / 6) := by
  have h2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  have h6 : (Real.sqrt 6 : ℂ) ^ 2 = 6 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; simp
  by_cases h : j = idxI a
  · simp [etaC, h, eps_self]
    field_simp
    exact h2
  · have := eps_sq a j h
    have hc : (epsOf a j : ℂ) ^ 2 = 1 := by exact_mod_cast this
    simp [etaC, h]
    field_simp
    rw [h6, hc, Complex.I_sq]
    ring

theorem orbit_etaV (a : Fin 32) : InOrbit (Gv (etaV a)) := by
  have hsumN : ∀ f : Fin 4 → ℝ, ∑ k : Fin 2 × Fin 2, f (pairIdx k) = ∑ j, f j := by
    intro f; simp [Fintype.sum_prod_type, Fin.sum_univ_four, pairIdx]; ring
  have hi : ∑ j : Fin 4, (if j = idxI a then (1 / 2 : ℝ) else 1 / 6) = 1 := by
    fin_cases a <;> simp [idxI, Fin.sum_univ_four] <;> norm_num
  have hn : ∑ k, Complex.normSq (etaV a k) = 1 := by
    have := hsumN (fun j => Complex.normSq (etaC a j))
    simp only [normSq_etaC] at this
    simp only [etaV, normSq_etaC]
    rw [this, hi]
  have hp : ∀ k, Complex.normSq (etaV a k) = 1 / 6 ∨ Complex.normSq (etaV a k) = 1 / 2 := by
    intro k
    simp only [etaV, normSq_etaC]
    split_ifs <;> simp
  have hs : ∑ k, etaV a k ^ 2 = 0 := by
    have hsumC : ∀ f : Fin 4 → ℂ, ∑ k : Fin 2 × Fin 2, f (pairIdx k) = ∑ j, f j := by
      intro f; simp [Fintype.sum_prod_type, Fin.sum_univ_four, pairIdx]; ring
    have := hsumC (fun j => etaC a j ^ 2)
    simp only [sq_etaC] at this
    simp only [etaV, sq_etaC]
    rw [this]
    fin_cases a <;> simp [idxI, Fin.sum_univ_four] <;> norm_num
  rcases LU_M4_of_caseC (etaV a) hn hp hs with h | h
  · exact Or.inl h
  · exact Or.inr h


/-! ### The overlap of two normal forms -/

theorem ip_eq_trace (φ χ : Psi) : ip φ χ = Matrix.trace ((zmat φ)ᴴ * zmat χ) := by
  simp only [ip, vecOf, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, zmat, Matrix.of_apply, Fintype.sum_prod_type, Complex.star_def,
    Fin.sum_univ_two]
  ring

theorem ip_Gv (v w : V) : ip (Gv v) (Gv w) = ∑ k, (starRingEnd ℂ) (v k) * w k := by
  rw [ip_eq_trace, zmat_Gv, zmat_Gv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    transpose_conjTranspose, Matrix.diagonal_conjTranspose]
  have hBB : magicBᵀ * magicB.map (starRingEnd ℂ) = 1 := unitary_transpose_mul magicB_unitary
  have key : magicB.map star * (Matrix.diagonal (star v) * magicBᴴ) *
      (magicB * Matrix.diagonal w * magicBᵀ) =
      magicB.map star * Matrix.diagonal (star v * w) * magicBᵀ := by
    calc _ = magicB.map star * Matrix.diagonal (star v) * (magicBᴴ * magicB) *
          Matrix.diagonal w * magicBᵀ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [magicB_unitary, Matrix.mul_one, Matrix.mul_assoc _ (Matrix.diagonal (star v)),
          Matrix.diagonal_mul_diagonal]
        rfl
  have hBB' : magicBᵀ * magicB.map star = 1 := hBB
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hBB', Matrix.one_mul, Matrix.trace_diagonal]
  simp [Pi.mul_apply, Complex.star_def]


theorem qH_eq_normSq_ip (v : V) (a : Fin 32) :
    qH a v = Complex.normSq (ip (Gv v) (Gv (etaV a))) := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num)]; norm_num
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs3 : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / Real.sqrt 2 := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 1 / Real.sqrt 6 := ⟨_, rfl⟩
  have hc2 : c ^ 2 = 1 / 2 := by rw [hc]; field_simp; linarith
  have hκ2 : κ ^ 2 = 1 / 6 := by
    rw [hκ, h6]; field_simp; nlinarith
  have hck : c * κ = Real.sqrt 3 / 6 := by
    rw [hc, hκ, h6]; field_simp; nlinarith
  rw [ip_Gv]
  have hsumC : ∀ f : Fin 4 → ℂ, ∑ k : Fin 2 × Fin 2, f (pairIdx k) = ∑ j, f j := by
    intro f; simp [Fintype.sum_prod_type, Fin.sum_univ_four, pairIdx]; ring
  have hconv : ∑ k, (starRingEnd ℂ) (v k) * etaV a k =
      ∑ j : Fin 4, (starRingEnd ℂ) (coord v j) * etaC a j := by
    rw [← hsumC (fun j => (starRingEnd ℂ) (coord v j) * etaC a j)]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [coord_pairIdx, etaV]
  rw [hconv]
  have hsplit : ∑ j : Fin 4, (starRingEnd ℂ) (coord v j) * etaC a j =
      (starRingEnd ℂ) (coord v (idxI a)) * (c : ℂ) +
        Complex.I * ∑ j : Fin 4, (starRingEnd ℂ) (coord v j) * ((epsOf a j * κ : ℝ) : ℂ) := by
    calc ∑ j : Fin 4, (starRingEnd ℂ) (coord v j) * etaC a j
        = ∑ j : Fin 4, (if j = idxI a then (starRingEnd ℂ) (coord v j) * (c : ℂ) else 0) +
          ∑ j : Fin 4, Complex.I * ((starRingEnd ℂ) (coord v j) * ((epsOf a j * κ : ℝ) : ℂ)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h : j = idxI a
          · simp only [etaC, h, ite_true, hc, hκ]; push_cast; ring
          · simp only [etaC, h, ite_false, hc, hκ]; push_cast; ring
      _ = _ := by
          rw [Finset.sum_ite_eq', ← Finset.mul_sum]
          simp
  rw [hsplit]
  set T : ℂ := ∑ j : Fin 4, (starRingEnd ℂ) (coord v j) * ((epsOf a j * κ : ℝ) : ℂ) with hT
  have hTre : T.re = κ * Sx a v := by
    rw [hT, Complex.re_sum]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, Sx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hTim : T.im = -(κ * Sy a v) := by
    rw [hT, Complex.im_sum]
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, add_zero, Sy, ← Finset.sum_neg_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hTre, hTim]
  unfold qH Aq Cq
  rw [Complex.normSq_apply]
  linear_combination (-((coord v (idxI a)).re ^ 2 + (coord v (idxI a)).im ^ 2)) * hc2 -
    (Sx a v ^ 2 + Sy a v ^ 2) * hκ2 -
    2 * ((coord v (idxI a)).re * Sy a v - (coord v (idxI a)).im * Sx a v) * hck


/-! ### Local unitary invariance -/

theorem ip_localApply {a b c d : Op1} (ha : aᴴ * a = 1) (hb : bᴴ * b = 1) (hc : cᴴ * c = 1)
    (hd : dᴴ * d = 1) (φ χ : Psi) :
    ip (localApply a b c d φ) (localApply a b c d χ) = ip φ χ := by
  have hK := kron_unitary ha hb
  have hL := kron_unitary hc hd
  have hLL : (kron c d)ᵀ * (kron c d).map star = 1 := unitary_transpose_mul hL
  rw [ip_eq_trace, ip_eq_trace, zmat_localApply, zmat_localApply, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, transpose_conjTranspose]
  have key : ((kron c d).map star * ((zmat φ)ᴴ * (kron a b)ᴴ)) *
      (kron a b * zmat χ * (kron c d)ᵀ) =
      (kron c d).map star * ((zmat φ)ᴴ * zmat χ) * (kron c d)ᵀ := by
    calc _ = (kron c d).map star * (zmat φ)ᴴ * ((kron a b)ᴴ * kron a b) * zmat χ * (kron c d)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hK, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hLL, Matrix.one_mul]

theorem purity_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) : purity ψ = purity φ := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact purity_localApply ha hb hc hd φ

theorem sexticQ_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) : sexticQ ψ = sexticQ φ := by
  unfold sexticQ
  rw [sexticF_LUEquiv h, normSqPsi_LUEquiv h, purity_LUEquiv h]

/-- Every overlap `qH a v` with a representative of `𝓗` is at most `Φ(ψ)`, for `ψ ≃ G(v)`. -/
theorem qH_le_Phi {v : V} {ψ : Psi} (hLU : LUEquiv (Gv v) ψ) (hψ : normSqPsi ψ = 1) (a : Fin 32) :
    qH a v ≤ Phi ψ := by
  obtain ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩ := hLU
  have hmem : InOrbit (localApply x y z w (Gv (etaV a))) := by
    rcases orbit_etaV a with h | h
    · exact Or.inl (h.trans ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩)
    · exact Or.inr (h.trans ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩)
  have := le_Phi hψ hmem
  rwa [ip_localApply hx hy hz hw, ← qH_eq_normSq_ip] at this

set_option maxHeartbeats 4000000 in
/-- The frame identity: the 32 overlaps `|⟨η, v⟩|²` sum to `8 ‖v‖²`. -/
theorem sum_qH (v : V) : ∑ a, qH a v = 8 * Nv v := by
  simp [qH, Aq, Cq, Sx, Sy, coord, epsOf, idxI, Fin.sum_univ_succ, Fin.sum_univ_four, Nv,
    Fintype.sum_prod_type, Fin.sum_univ_two, Complex.normSq_apply]
  ring

end FormalResearch.FourQubitEntropy.CO

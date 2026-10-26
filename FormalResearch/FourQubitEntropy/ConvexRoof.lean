import FormalResearch.FourQubitEntropy.RenyiRankTwo
import FormalResearch.FourQubitEntropy.Renyi

/-!
# Convex roofs: the mixed-state ceiling

For a mixed four-qubit state `ρ` and a functional `g` of pure states, the convex roof is
`E_g(ρ) = inf Σ_ℓ p_ℓ g(ψ_ℓ)` over finite ensembles `ρ = Σ p_ℓ |ψ_ℓ⟩⟨ψ_ℓ|` of unit vectors. If the
three cut functionals `g₂, g₃, g₄` satisfy `⅓ Σ g_j(ψ) ≤ C` on unit vectors then
`⅓ Σ E_{g_j}(ρ) ≤ C` for every mixed state: use one ensemble (the spectral decomposition of `ρ`)
for all three infima and average.

Paper: `cor:fqe-convex-roof` (spectral_corollaries.tex), the ceiling inequality for the von Neumann
entropy (the three bipartite entanglements of formation), the Tsallis entropies `0 < q < 2` and the
Rényi entropies `0 < q < 1`. The pure-only equality classification (singular-pencil argument) is not
formalized here.
-/

open scoped ComplexConjugate Matrix ComplexOrder

namespace FormalResearch.FourQubitEntropy

open Real

/-- Index set of the 16 basis states of four qubits. -/
abbrev Idx := Fin 2 × Fin 2 × Fin 2 × Fin 2

/-- Four-qubit density operators (as matrices). -/
abbrev Mat16 := Matrix Idx Idx ℂ

/-- The amplitude vector of a four-qubit vector. -/
def vecOf (ψ : Psi) : Idx → ℂ := fun x => ψ x.1 x.2.1 x.2.2.1 x.2.2.2

/-- The four-qubit vector with the given amplitude vector. -/
def psiOf (v : Idx → ℂ) : Psi := fun a b c d => v (a, b, c, d)

/-- The rank-one operator `|ψ⟩⟨ψ|`. -/
def projPsi (ψ : Psi) : Mat16 := Matrix.of fun x y => vecOf ψ x * conj (vecOf ψ y)

/-- The values `Σ_ℓ p_ℓ g(ψ_ℓ)` over all finite ensembles of unit vectors with `ρ = Σ p_ℓ |ψ_ℓ⟩⟨ψ_ℓ|`. -/
def ensembleValues (g : Psi → ℝ) (ρ : Mat16) : Set ℝ :=
  {v | ∃ (n : ℕ) (p : Fin n → ℝ) (ψ : Fin n → Psi), (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1 ∧
    (∀ l, normSqPsi (ψ l) = 1) ∧ ρ = ∑ l, (p l : ℂ) • projPsi (ψ l) ∧ v = ∑ l, p l * g (ψ l)}

/-- The convex roof of `g` at `ρ`. -/
noncomputable def convexRoof (g : Psi → ℝ) (ρ : Mat16) : ℝ := sInf (ensembleValues g ρ)

theorem normSqPsi_psiOf (v : Idx → ℂ) : normSqPsi (psiOf v) = ∑ x, Complex.normSq (v x) := by
  simp [normSqPsi, psiOf, Fintype.sum_prod_type]

theorem vecOf_psiOf (v : Idx → ℂ) : vecOf (psiOf v) = v := by
  funext x; rfl

/-- Every density matrix has an ensemble of unit vectors (its spectral decomposition). -/
theorem exists_ensemble {ρ : Mat16} (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    ∃ (n : ℕ) (p : Fin n → ℝ) (ψ : Fin n → Psi), (∀ l, 0 ≤ p l) ∧ ∑ l, p l = 1 ∧
      (∀ l, normSqPsi (ψ l) = 1) ∧ ρ = ∑ l, (p l : ℂ) • projPsi (ψ l) := by
  have hH := hρ.1
  set U : Mat16 := ((hH.eigenvectorUnitary : Matrix.unitaryGroup Idx ℂ) : Mat16) with hU
  have h1 : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hspec : ρ = U * Matrix.diagonal (fun i => ((hH.eigenvalues i : ℝ) : ℂ)) * star U := by
    have := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  let e : Idx ≃ Fin (Fintype.card Idx) := Fintype.equivFin Idx
  let col : Idx → Psi := fun k => psiOf (fun x => U x k)
  have hunit : ∀ k, normSqPsi (col k) = 1 := by
    intro k
    simp only [col, normSqPsi_psiOf]
    have := congrFun (congrFun h1 k) k
    simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] at this
    have h3 := congrArg Complex.re this
    simp only [Complex.re_sum, Complex.one_re] at h3
    rw [← h3]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Complex.normSq_apply, Complex.mul_re]
  refine ⟨Fintype.card Idx, fun l => hH.eigenvalues (e.symm l), fun l => col (e.symm l),
    fun l => hρ.eigenvalues_nonneg _, ?_, fun l => hunit _, ?_⟩
  · rw [Equiv.sum_comp e.symm (fun k => hH.eigenvalues k)]
    have h4 : (Matrix.trace ρ).re = ∑ i, hH.eigenvalues i := by
      rw [hH.trace_eq_sum_eigenvalues]; simp [Complex.re_sum]
    linarith
  · have hsum : ∑ l : Fin (Fintype.card Idx), ((hH.eigenvalues (e.symm l) : ℝ) : ℂ) • projPsi (col (e.symm l))
        = ∑ k, ((hH.eigenvalues k : ℝ) : ℂ) • projPsi (col k) :=
      Equiv.sum_comp e.symm (fun k => ((hH.eigenvalues k : ℝ) : ℂ) • projPsi (col k))
    rw [hsum]
    ext x y
    rw [congrFun (congrFun hspec x) y]
    simp [Matrix.mul_apply, Matrix.sum_apply, projPsi, vecOf, col, psiOf, Matrix.diagonal_apply,
      Matrix.star_apply]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- Any ensemble gives an upper bound for the convex roof (the values are bounded below by `0`). -/
theorem convexRoof_le_ensemble {g : Psi → ℝ} (hg : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g ψ) {ρ : Mat16}
    {n : ℕ} {p : Fin n → ℝ} {ψ : Fin n → Psi} (hp : ∀ l, 0 ≤ p l) (hs : ∑ l, p l = 1)
    (hu : ∀ l, normSqPsi (ψ l) = 1) (he : ρ = ∑ l, (p l : ℂ) • projPsi (ψ l)) :
    convexRoof g ρ ≤ ∑ l, p l * g (ψ l) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨n', p', ψ', hp', -, hu', -, rfl⟩
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hp' l) (hg _ (hu' l))
  · exact ⟨n, p, ψ, hp, hs, hu, he, rfl⟩

/-- **Mixed-state ceiling** (`cor:fqe-convex-roof`): if `⅓ (g₂ + g₃ + g₄) ≤ C` on unit vectors
(and the `g_j` are nonnegative there), the mean of the three convex roofs of any mixed state is at
most `C`. -/
theorem convexRoof_mean_le {g₂ g₃ g₄ : Psi → ℝ} (h₂ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₂ ψ)
    (h₃ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₃ ψ) (h₄ : ∀ ψ, normSqPsi ψ = 1 → 0 ≤ g₄ ψ) {C : ℝ}
    (hC : ∀ ψ, normSqPsi ψ = 1 → (g₂ ψ + g₃ ψ + g₄ ψ) / 3 ≤ C) {ρ : Mat16} (hρ : ρ.PosSemidef)
    (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof g₂ ρ + convexRoof g₃ ρ + convexRoof g₄ ρ) / 3 ≤ C := by
  obtain ⟨n, p, ψ, hp, hs, hu, he⟩ := exists_ensemble hρ htr
  have a2 := convexRoof_le_ensemble h₂ hp hs hu he
  have a3 := convexRoof_le_ensemble h₃ hp hs hu he
  have a4 := convexRoof_le_ensemble h₄ hp hs hu he
  have key : ∑ l, p l * g₂ (ψ l) + ∑ l, p l * g₃ (ψ l) + ∑ l, p l * g₄ (ψ l) ≤ 3 * C := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    calc ∑ l, (p l * g₂ (ψ l) + p l * g₃ (ψ l) + p l * g₄ (ψ l))
        ≤ ∑ l, p l * (3 * C) := by
          refine Finset.sum_le_sum fun l _ => ?_
          have := hC (ψ l) (hu l)
          nlinarith [hp l]
      _ = 3 * C := by rw [← Finset.sum_mul, hs]; ring
  linarith

/-! ### The von Neumann, Tsallis and Rényi roofs -/

theorem vnEntropy_nonneg {R : Mat4} (hR : R.IsHermitian) (hp : R.PosSemidef)
    (htr : (Matrix.trace R).re = 1) : 0 ≤ vnEntropy hR := by
  unfold vnEntropy
  refine div_nonneg (Finset.sum_nonneg fun i _ => ?_) (Real.log_pos (by norm_num)).le
  have hm := eigenvalue_mem_Icc hR hp htr i
  exact Real.negMulLog_nonneg hm.1 hm.2

theorem vnEntropy12_nonneg {ψ : Psi} (hψ : normSqPsi ψ = 1) : 0 ≤ vnEntropy (red12_herm ψ) :=
  vnEntropy_nonneg _ (red12_psd ψ) (by rw [trace_red12, hψ]; simp)
theorem vnEntropy13_nonneg {ψ : Psi} (hψ : normSqPsi ψ = 1) : 0 ≤ vnEntropy (red13_herm ψ) :=
  vnEntropy_nonneg _ (red13_psd ψ) (by rw [trace_red13, hψ]; simp)
theorem vnEntropy14_nonneg {ψ : Psi} (hψ : normSqPsi ψ = 1) : 0 ≤ vnEntropy (red14_herm ψ) :=
  vnEntropy_nonneg _ (red14_psd ψ) (by rw [trace_red14, hψ]; simp)

/-- **Convex roofs, von Neumann case** (`cor:fqe-convex-roof`): for every mixed four-qubit state, the
mean of the three bipartite entanglements of formation `E_F^{1j|\widehat{1j}}` is at most
`1 + ½ log₂ 3`. -/
theorem convexRoof_vn_le {ρ : Mat16} (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof (fun ψ => vnEntropy (red12_herm ψ)) ρ + convexRoof (fun ψ => vnEntropy (red13_herm ψ)) ρ
      + convexRoof (fun ψ => vnEntropy (red14_herm ψ)) ρ) / 3 ≤ 1 + Real.log 3 / (2 * Real.log 2) :=
  convexRoof_mean_le (fun _ h => vnEntropy12_nonneg h) (fun _ h => vnEntropy13_nonneg h)
    (fun _ h => vnEntropy14_nonneg h) (fun ψ h => meanEntropy_le ψ h) hρ htr

theorem tsallisCut_nonneg {q : ℝ} (h0 : 0 < q) (h1 : q ≠ 1) {R : Mat4}
    (hR : R.IsHermitian) (hp : R.PosSemidef) (htr : (Matrix.trace R).re = 1) : 0 ≤ tsallisCut q hR := by
  unfold tsallisCut
  have hs : ∑ i, hR.eigenvalues i = 1 := by rw [sum_eigenvalues_eq_trace, htr]
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · have := cutMoment_ge_one h0 hlt hR hp htr
    unfold cutMoment at this
    exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · have : ∑ i, hR.eigenvalues i ^ q ≤ 1 := by
      rw [← hs]
      refine Finset.sum_le_sum fun i _ => ?_
      have hm := eigenvalue_mem_Icc hR hp htr i
      have := Real.rpow_le_rpow_of_exponent_ge' hm.1 hm.2 (by norm_num : (0 : ℝ) ≤ 1) hgt.le
      simpa using this
    exact div_nonneg (by linarith) (by linarith)

/-- **Convex roofs, Tsallis case** (`cor:fqe-convex-roof`, `0 < q < 2`, `q ≠ 1`). -/
theorem convexRoof_tsallis_le {q : ℝ} (h0 : 0 < q) (h2 : q < 2) (h1 : q ≠ 1) {ρ : Mat16}
    (hρ : ρ.PosSemidef) (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof (fun ψ => tsallisCut q (red12_herm ψ)) ρ + convexRoof (fun ψ => tsallisCut q (red13_herm ψ)) ρ
      + convexRoof (fun ψ => tsallisCut q (red14_herm ψ)) ρ) / 3 ≤ tsallisCeiling q :=
  convexRoof_mean_le
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red12_psd ψ) (by rw [trace_red12, h]; simp))
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red13_psd ψ) (by rw [trace_red13, h]; simp))
    (fun ψ h => tsallisCut_nonneg h0 h1 _ (red14_psd ψ) (by rw [trace_red14, h]; simp))
    (fun ψ h => tsallis_le h0 h2 h1 ψ h) hρ htr

theorem renyiCut_nonneg {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {R : Mat4} (hR : R.IsHermitian)
    (hp : R.PosSemidef) (htr : (Matrix.trace R).re = 1) : 0 ≤ renyiCut q hR := by
  unfold renyiCut
  have := cutMoment_ge_one h0 h1 hR hp htr
  unfold cutMoment at this
  exact div_nonneg (Real.logb_nonneg (by norm_num) this) (by linarith)

/-- **Convex roofs, Rényi case** (`cor:fqe-convex-roof`, `0 < q < 1`). -/
theorem convexRoof_renyi_le {q : ℝ} (h0 : 0 < q) (h1 : q < 1) {ρ : Mat16} (hρ : ρ.PosSemidef)
    (htr : (Matrix.trace ρ).re = 1) :
    (convexRoof (fun ψ => renyiCut q (red12_herm ψ)) ρ + convexRoof (fun ψ => renyiCut q (red13_herm ψ)) ρ
      + convexRoof (fun ψ => renyiCut q (red14_herm ψ)) ρ) / 3 ≤
      Real.logb 2 ((2 : ℝ) ^ (-q) + 3 * (6 : ℝ) ^ (-q)) / (1 - q) :=
  convexRoof_mean_le
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red12_psd ψ) (by rw [trace_red12, h]; simp))
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red13_psd ψ) (by rw [trace_red13, h]; simp))
    (fun ψ h => renyiCut_nonneg h0 h1 _ (red14_psd ψ) (by rw [trace_red14, h]; simp))
    (fun ψ h => renyi_le h0 h1 ψ h) hρ htr

/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_mean_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms convexRoof_mean_le

/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_vn_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_vn_le

/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_tsallis_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_tsallis_le

/-- info: 'FormalResearch.FourQubitEntropy.convexRoof_renyi_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sexticDefect_check._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms convexRoof_renyi_le

end FormalResearch.FourQubitEntropy

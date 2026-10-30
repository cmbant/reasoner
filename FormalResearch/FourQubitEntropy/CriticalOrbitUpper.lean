import FormalResearch.FourQubitEntropy.CriticalOrbitLocal
import FormalResearch.FourQubitEntropy.CriticalOrbitConj
import FormalResearch.FourQubitEntropy.CriticalOrbitBirkhoff

/-!
# Critical-orbit stability: the upper bound `Φ(G(v)) ≤ max_a qH a v`

For a unit `v` and `B` with `qH a v ≤ B` for the 32 representatives, `Φ(G(v)) ≤ B`
(`Phi_Gv_le`): every `χ ∈ 𝓜` is `U G(η)` with `η = η_p` (`exists_M4_conj`), the overlap is
`s ∑_{ik} conj(v_i) η_k O₁_{ik} O₂_{ik}` (`ip_Gv_localApply`), `sbirk` bounds it by the signed
permutation sums, and each of those is a representative overlap (`signed_perm`).
-/

set_option linter.unusedSimpArgs false

open scoped ComplexConjugate Matrix Kronecker

namespace FormalResearch.FourQubitEntropy.CO
open PaperECritical

/-- Every admissible sign pattern is `epsOf a` for some `a`. -/
theorem exists_a (i : Fin 4) (e : Fin 4 → ℝ) (h0 : e i = 0) (h1 : ∀ j, j ≠ i → e j ^ 2 = 1) :
    ∃ a : Fin 32, idxI a = i ∧ epsOf a = e := by
  fin_cases i
  · have h0' : e 0 = 0 := h0
    have s1 := eq_or_eq_neg_of_sq_eq_sq (e 1) 1 (by simpa using h1 1 (by decide))
    have s2 := eq_or_eq_neg_of_sq_eq_sq (e 2) 1 (by simpa using h1 2 (by decide))
    have s3 := eq_or_eq_neg_of_sq_eq_sq (e 3) 1 (by simpa using h1 3 (by decide))
    rcases s1 with s1 | s1 <;> rcases s2 with s2 | s2 <;> rcases s3 with s3 | s3
    · exact ⟨0, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨4, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨2, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨6, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨1, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨5, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨3, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨7, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
  · have h0' : e 1 = 0 := h0
    have s1 := eq_or_eq_neg_of_sq_eq_sq (e 0) 1 (by simpa using h1 0 (by decide))
    have s2 := eq_or_eq_neg_of_sq_eq_sq (e 2) 1 (by simpa using h1 2 (by decide))
    have s3 := eq_or_eq_neg_of_sq_eq_sq (e 3) 1 (by simpa using h1 3 (by decide))
    rcases s1 with s1 | s1 <;> rcases s2 with s2 | s2 <;> rcases s3 with s3 | s3
    · exact ⟨8, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨12, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨10, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨14, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨9, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨13, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨11, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨15, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
  · have h0' : e 2 = 0 := h0
    have s1 := eq_or_eq_neg_of_sq_eq_sq (e 0) 1 (by simpa using h1 0 (by decide))
    have s2 := eq_or_eq_neg_of_sq_eq_sq (e 1) 1 (by simpa using h1 1 (by decide))
    have s3 := eq_or_eq_neg_of_sq_eq_sq (e 3) 1 (by simpa using h1 3 (by decide))
    rcases s1 with s1 | s1 <;> rcases s2 with s2 | s2 <;> rcases s3 with s3 | s3
    · exact ⟨16, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨20, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨18, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨22, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨17, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨21, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨19, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨23, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
  · have h0' : e 3 = 0 := h0
    have s1 := eq_or_eq_neg_of_sq_eq_sq (e 0) 1 (by simpa using h1 0 (by decide))
    have s2 := eq_or_eq_neg_of_sq_eq_sq (e 1) 1 (by simpa using h1 1 (by decide))
    have s3 := eq_or_eq_neg_of_sq_eq_sq (e 2) 1 (by simpa using h1 2 (by decide))
    rcases s1 with s1 | s1 <;> rcases s2 with s2 | s2 <;> rcases s3 with s3 | s3
    · exact ⟨24, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨28, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨26, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨30, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨25, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨29, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨27, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩
    · exact ⟨31, by decide, funext fun j => by fin_cases j <;> simp [epsOf, h0', s1, s2, s3]⟩

/-- The inverse of `pairIdx`. -/
def pairOf (k : Fin 4) : Fin 2 × Fin 2 := (⟨k.val / 2, by omega⟩, ⟨k.val % 2, by omega⟩)

theorem pairIdx_pairOf (k : Fin 4) : pairIdx (pairOf k) = k := by
  fin_cases k <;> rfl

theorem pairOf_pairIdx (p : Fin 2 × Fin 2) : pairOf (pairIdx p) = p := by
  rcases p with ⟨a, b⟩; fin_cases a <;> fin_cases b <;> rfl

/-- Every signed permutation sum is a representative overlap: `|∑_i ε_i conj(v_i) η_{π i}|² = qH a v`
for some `a` (the large entry of `η_p` lands at `j₀ = π⁻¹ i₀`, and the global sign `ε_{j₀}` drops
out of the modulus). -/
theorem signed_perm (v : V) (p : Fin 32) (π : Equiv.Perm (Fin 2 × Fin 2))
    (ε : Fin 2 × Fin 2 → ℝ) (hε : ∀ i, ε i ^ 2 = 1) :
    ∃ a, Complex.normSq (∑ i, (ε i : ℂ) * ((starRingEnd ℂ) (v i) * etaV p (π i))) = qH a v := by
  set i₀ := pairOf (idxI p) with hi₀
  set j₀ := π.symm i₀ with hj₀
  have hπj₀ : π j₀ = i₀ := by simp [hj₀]
  have hpi₀ : pairIdx i₀ = idxI p := pairIdx_pairOf _
  set e : Fin 4 → ℝ := fun k => ε (pairOf k) * ε j₀ * epsOf p (pairIdx (π (pairOf k))) with he
  have h0 : e (pairIdx j₀) = 0 := by
    simp only [he, pairOf_pairIdx, hπj₀, hpi₀, eps_self, mul_zero]
  have h1 : ∀ k, k ≠ pairIdx j₀ → e k ^ 2 = 1 := by
    intro k hk
    have hne : pairIdx (π (pairOf k)) ≠ idxI p := by
      intro h
      apply hk
      have : π (pairOf k) = i₀ := by
        have := congrArg pairOf h
        rwa [pairOf_pairIdx] at this
      have h2 : pairOf k = j₀ := by rw [hj₀, ← this]; simp
      rw [← h2, pairIdx_pairOf]
    have := eps_sq p _ hne
    simp only [he]
    rw [mul_pow, mul_pow, hε, hε, this]; ring
  obtain ⟨a, ha1, ha2⟩ := exists_a (pairIdx j₀) e h0 h1
  refine ⟨a, ?_⟩
  have hpt : ∀ j, (ε j : ℂ) * etaV p (π j) = (ε j₀ : ℂ) * etaV a j := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [etaV, etaC, hπj₀, hpi₀, ← ha1, ite_true, eps_self]
    · have hne1 : pairIdx (π j) ≠ idxI p := by
        intro h
        apply hj
        have : π j = i₀ := by
          have := congrArg pairOf h
          rwa [pairOf_pairIdx] at this
        rw [hj₀, ← this]; simp
      have hne2 : pairIdx j ≠ idxI a := by
        rw [ha1]; intro h
        exact hj (by have := congrArg pairOf h; rwa [pairOf_pairIdx, pairOf_pairIdx] at this)
      have hea : epsOf a (pairIdx j) = ε j * ε j₀ * epsOf p (pairIdx (π j)) := by
        rw [ha2]; simp only [he, pairOf_pairIdx]
      simp only [etaV, etaC, hne1, hne2, ite_false, hea]
      have hε0 : (ε j₀ : ℂ) ^ 2 = 1 := by exact_mod_cast hε j₀
      push_cast
      linear_combination (-(Complex.I * (ε j : ℂ) * (epsOf p (pairIdx (π j)) : ℂ) /
        (Real.sqrt 6 : ℂ))) * hε0
  have hsum : ∑ i, (ε i : ℂ) * ((starRingEnd ℂ) (v i) * etaV p (π i)) =
      (ε j₀ : ℂ) * ∑ i, (starRingEnd ℂ) (v i) * etaV a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    calc (ε i : ℂ) * ((starRingEnd ℂ) (v i) * etaV p (π i))
        = (starRingEnd ℂ) (v i) * ((ε i : ℂ) * etaV p (π i)) := by ring
      _ = _ := by rw [hpt i]; ring
  rw [hsum, Complex.normSq_mul, Complex.normSq_ofReal, qH_eq_normSq_ip, ip_Gv]
  have := hε j₀
  have h' : ε j₀ * ε j₀ = 1 := by nlinarith
  rw [h', one_mul]

/-- Overlap bound against one local unitary orbit of `G(η_p)`. -/
theorem normSq_ip_le_of_orbit {v : V} {p : Fin 32} {χ : Psi} (hχ : LUEquiv (Gv (etaV p)) χ)
    {B : ℝ} (hB : ∀ a, qH a v ≤ B) : Complex.normSq (ip (Gv v) χ) ≤ B := by
  obtain ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩ := hχ
  obtain ⟨s, O1, O2, hs, hO1, hO2, hip⟩ := ip_Gv_localApply hx hy hz hw v (etaV p)
  have hB0 : 0 ≤ B := le_trans (by rw [qH_eq_normSq_ip]; exact Complex.normSq_nonneg _) (hB 0)
  have hbound := sbirk (fun i k => (starRingEnd ℂ) (v i) * etaV p k)
    (fun i k => O1 i k) (fun i k => O2 i k) hO1 hO2 (Real.sqrt B) (by
      intro π ε hε
      obtain ⟨a, ha⟩ := signed_perm v p π ε hε
      have h1 : Complex.normSq (∑ i, (ε i : ℂ) * ((starRingEnd ℂ) (v i) * etaV p (π i))) ≤ B := by
        rw [ha]; exact hB a
      rw [Complex.normSq_eq_norm_sq] at h1
      exact Real.le_sqrt_of_sq_le h1)
  rw [hip, Complex.normSq_mul, hs, one_mul, Complex.normSq_eq_norm_sq]
  have h0 := norm_nonneg (∑ i, ∑ k, (starRingEnd ℂ) (v i) * etaV p k * ((O1 i k * O2 i k : ℝ) : ℂ))
  calc _ ≤ Real.sqrt B ^ 2 := pow_le_pow_left₀ h0 hbound 2
    _ = B := Real.sq_sqrt hB0

/-- **The upper bound** `Φ(G(v)) ≤ B` whenever `qH a v ≤ B` for all 32 representatives. -/
theorem Phi_Gv_le {v : V} {B : ℝ} (hB : ∀ a, qH a v ≤ B) : Phi (Gv v) ≤ B := by
  obtain ⟨⟨pM, hpM⟩, ⟨pC, hpC⟩⟩ := exists_M4_conj
  refine csSup_le ⟨_, M4, InOrbit_M4, rfl⟩ ?_
  rintro _ ⟨χ, hχ, rfl⟩
  rcases hχ with h | h
  · exact normSq_ip_le_of_orbit (hpM.symm.trans h) hB
  · exact normSq_ip_le_of_orbit (hpC.symm.trans h) hB

/-- `Φ` is invariant under local unitaries. -/
theorem Phi_LUEquiv {φ ψ : Psi} (h : LUEquiv φ ψ) (hφ : normSqPsi φ = 1) : Phi ψ = Phi φ := by
  have hψ : normSqPsi ψ = 1 := (normSqPsi_LUEquiv h).trans hφ
  have key : ∀ {φ ψ : Psi}, LUEquiv φ ψ →
      ∀ χ, InOrbit χ → ∃ χ', InOrbit χ' ∧ Complex.normSq (ip ψ χ) = Complex.normSq (ip φ χ') := by
    intro φ ψ h χ hχ
    obtain ⟨x, y, z, w, hx, hy, hz, hw, hψ⟩ := LUEquiv.symm h
    refine ⟨localApply x y z w χ, ?_, ?_⟩
    · rcases hχ with h' | h'
      · exact Or.inl (h'.trans ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩)
      · exact Or.inr (h'.trans ⟨x, y, z, w, hx, hy, hz, hw, rfl⟩)
    · rw [← ip_localApply hx hy hz hw, hψ]
  refine le_antisymm (csSup_le ⟨_, M4, InOrbit_M4, rfl⟩ ?_) (csSup_le ⟨_, M4, InOrbit_M4, rfl⟩ ?_)
  · rintro _ ⟨χ, hχ, rfl⟩
    obtain ⟨χ', hχ', e⟩ := key h χ hχ
    rw [e]; exact le_Phi hφ hχ'
  · rintro _ ⟨χ, hχ, rfl⟩
    obtain ⟨χ', hχ', e⟩ := key (LUEquiv.symm h) χ hχ
    rw [e]; exact le_Phi hψ hχ'

/-- **`Φ` is the maximum of the 32 representative overlaps** (the signed-Birkhoff reduction): for a
critical unit state `ψ ≃ G(v)`, `Φ(ψ) = max_a qH a v`, attained at some representative. -/
theorem Phi_eq_max {ψ : Psi} (hψ : normSqPsi ψ = 1) (hW : blochSq ψ = 0) :
    ∃ v : V, LUEquiv (Gv v) ψ ∧ Nv v = 1 ∧ (∀ a, qH a v ≤ Phi ψ) ∧ ∃ a, Phi ψ = qH a v := by
  obtain ⟨v, hv⟩ := (critical_iff_LU_Gv ψ).mp hW
  have hN : Nv v = 1 := by
    have := normSqPsi_LUEquiv hv
    rw [Gv_n] at this
    simpa [Nv] using this.symm.trans hψ
  have hG : normSqPsi (Gv v) = 1 := by rw [Gv_n]; simpa [Nv] using hN
  have hlow := qH_le_Phi hv hψ
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin 32)) (fun a => qH a v)
  have hup : Phi ψ ≤ qH a v := by
    rw [Phi_LUEquiv hv hG]
    exact Phi_Gv_le fun b => ha ▸ Finset.le_sup' (fun a => qH a v) (Finset.mem_univ b)
  exact ⟨v, hv, hN, hlow, a, le_antisymm hup (hlow a)⟩

end FormalResearch.FourQubitEntropy.CO

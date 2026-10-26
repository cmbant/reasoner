import FormalResearch.FourQubitEntropy.Checks

/-!
# One-cut rigidity for every cut

`Checks.lean` proves one-cut rigidity for the cut `12|34`. The cuts `13|24` and `14|23` follow
by exchanging qubits `2 ↔ 3` (respectively `2 ↔ 4`), which maps the cut to `12|34`, together
with the fact that `M₄` itself satisfies the cut condition on every cut.

Paper: `prop:fqe-onecut` (entropy_maximum.tex).
-/

open scoped ComplexConjugate Matrix

namespace FormalResearch.FourQubitEntropy

/-! ### Local-unitary equivalence is an equivalence relation compatible with `conj` and swaps -/

theorem op1_unitary_map_star {a : Op1} (ha : aᴴ * a = 1) :
    (a.map (starRingEnd ℂ))ᴴ * a.map (starRingEnd ℂ) = 1 := by
  have hm := map_mul (starRingEnd ℂ).mapMatrix aᴴ a
  simp only [RingHom.mapMatrix_apply] at hm
  rw [ha] at hm
  have e : (a.map (starRingEnd ℂ))ᴴ = aᴴ.map (starRingEnd ℂ) := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [e, ← hm]
  simp

theorem conj_localApply (a b c d : Op1) (ψ : Psi) :
    (localApply a b c d ψ).conj =
      localApply (a.map (starRingEnd ℂ)) (b.map (starRingEnd ℂ)) (c.map (starRingEnd ℂ))
        (d.map (starRingEnd ℂ)) ψ.conj := by
  funext p q r s
  simp only [Psi.conj, localApply_apply, map_sum, map_mul, Matrix.map_apply]

theorem LUEquiv.conj {ψ φ : Psi} (h : LUEquiv ψ φ) : LUEquiv ψ.conj φ.conj := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨_, _, _, _, op1_unitary_map_star ha, op1_unitary_map_star hb, op1_unitary_map_star hc,
    op1_unitary_map_star hd, (conj_localApply a b c d ψ).symm⟩

theorem Psi.conj_conj (ψ : Psi) : ψ.conj.conj = ψ := by
  funext a b c d; simp [Psi.conj]

theorem swap23_swap23 (ψ : Psi) : swap23 (swap23 ψ) = ψ := rfl
theorem swap24_swap24 (ψ : Psi) : swap24 (swap24 ψ) = ψ := rfl

theorem swap23_conj (ψ : Psi) : swap23 ψ.conj = (swap23 ψ).conj := rfl
theorem swap24_conj (ψ : Psi) : swap24 ψ.conj = (swap24 ψ).conj := rfl

theorem LUEquiv.swap23 {ψ φ : Psi} (h : LUEquiv ψ φ) :
    LUEquiv (FormalResearch.FourQubitEntropy.swap23 ψ) (FormalResearch.FourQubitEntropy.swap23 φ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨a, c, b, d, ha, hc, hb, hd, (swap23_localApply a c b d ψ).symm⟩

theorem LUEquiv.swap24 {ψ φ : Psi} (h : LUEquiv ψ φ) :
    LUEquiv (FormalResearch.FourQubitEntropy.swap24 ψ) (FormalResearch.FourQubitEntropy.swap24 φ) := by
  obtain ⟨a, b, c, d, ha, hb, hc, hd, rfl⟩ := h
  exact ⟨a, d, c, b, ha, hd, hc, hb, (swap24_localApply a d c b ψ).symm⟩

theorem normSqPsi_swap23 (ψ : Psi) : normSqPsi (swap23 ψ) = normSqPsi ψ := by
  unfold normSqPsi swap23
  simp only [Fin.sum_univ_two]; ring

theorem normSqPsi_swap24 (ψ : Psi) : normSqPsi (swap24 ψ) = normSqPsi ψ := by
  unfold normSqPsi swap24
  simp only [Fin.sum_univ_two]; ring

theorem red12_swap23 (ψ : Psi) : red12 (swap23 ψ) = red13 ψ := (red13_eq_swap ψ).symm
theorem red13_swap23 (ψ : Psi) : red13 (swap23 ψ) = red12 ψ := by
  rw [red13_eq_swap, swap23_swap23]
theorem red14_swap23 (ψ : Psi) : red14 (swap23 ψ) = red14 ψ := by
  ext ⟨a, d⟩ ⟨a', d'⟩
  simp only [red14, swap23, Matrix.of_apply, Fin.sum_univ_two]
  ring

theorem red12_swap24 (ψ : Psi) : red12 (swap24 ψ) = red14 ψ := (red14_eq_swap ψ).symm
theorem red14_swap24 (ψ : Psi) : red14 (swap24 ψ) = red12 ψ := by
  rw [red14_eq_swap, swap24_swap24]
theorem red13_swap24 (ψ : Psi) : red13 (swap24 ψ) = red13 ψ := by
  ext ⟨a, c⟩ ⟨a', c'⟩
  simp only [red13, swap24, Matrix.of_apply, Fin.sum_univ_two]
  ring

theorem purity_swap23 (ψ : Psi) : purity (swap23 ψ) = purity ψ := by
  unfold purity
  rw [red12_swap23, red13_swap23, red14_swap23]; ring

theorem purity_swap24 (ψ : Psi) : purity (swap24 ψ) = purity ψ := by
  unfold purity
  rw [red12_swap24, red13_swap24, red14_swap24]; ring

/-- `P(M₄) = 1`, proved without the sextic inequality. -/
theorem purity_M4_eq_one : purity M4 = 1 := by
  have t12 : Matrix.trace (red12 M4) = 1 := by rw [trace_red12, M4_unit]; simp
  have t13 : Matrix.trace (red13 M4) = 1 := by rw [trace_red13, M4_unit]; simp
  have t14 : Matrix.trace (red14 M4) = 1 := by rw [trace_red14, M4_unit]; simp
  obtain ⟨a12, -⟩ := quad_traces M4_cutQuadratics.q12 t12
  obtain ⟨a13, -⟩ := quad_traces M4_cutQuadratics.q13 t13
  obtain ⟨a14, -⟩ := quad_traces M4_cutQuadratics.q14 t14
  unfold purity; rw [a12, a13, a14]; norm_num

/-- Transport of one-cut rigidity along a symmetry `σ` of the four qubits that carries the cut
`1j|..` to `12|34` and fixes `M₄` up to local unitaries and conjugation. -/
theorem rigidity_transport (σ : Psi → Psi) (red : Psi → Mat4)
    (hσσ : ∀ ψ, σ (σ ψ) = ψ) (hconj : ∀ ψ, σ ψ.conj = (σ ψ).conj)
    (hLU : ∀ ψ φ, LUEquiv ψ φ → LUEquiv (σ ψ) (σ φ))
    (hn : ∀ ψ, normSqPsi (σ ψ) = normSqPsi ψ) (hP : ∀ ψ, purity (σ ψ) = purity ψ)
    (hred : ∀ ψ, red12 (σ ψ) = red ψ)
    (hM : (red M4 - (1 / 6 : ℂ) • 1) * (red M4 - (1 / 2 : ℂ) • 1) = 0)
    (ψ : Psi) (hψ : normSqPsi ψ = 1) (hPψ : purity ψ = 1)
    (hq : (red ψ - (1 / 6 : ℂ) • 1) * (red ψ - (1 / 2 : ℂ) • 1) = 0) :
    LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ := by
  have hN : LUEquiv M4 (σ M4) ∨ LUEquiv (Psi.conj M4) (σ M4) :=
    one_cut_rigidity_12 (σ M4) (by rw [hn]; exact M4_unit)
      (by rw [hP]; exact purity_M4_eq_one) (by rw [hred]; exact hM)
  have hψ' := one_cut_rigidity_12 (σ ψ) (by rw [hn]; exact hψ) (by rw [hP]; exact hPψ)
    (by rw [hred]; exact hq)
  -- `σ` is an involution, so `LUEquiv A (σ B)` gives `LUEquiv (σ A) B`.
  have key : ∀ A B, LUEquiv A (σ B) → LUEquiv (σ A) B := fun A B h => by
    have := hLU _ _ h; rwa [hσσ] at this
  rcases hψ' with h | h
  · have h1 : LUEquiv (σ M4) ψ := key _ _ h
    rcases hN with h2 | h2
    · exact Or.inl (h2.trans h1)
    · exact Or.inr (h2.trans h1)
  · have h1 : LUEquiv (σ (Psi.conj M4)) ψ := key _ _ h
    rw [hconj] at h1
    rcases hN with h2 | h2
    · exact Or.inr (h2.conj.trans h1)
    · have h3 := h2.conj
      rw [Psi.conj_conj] at h3
      exact Or.inl (h3.trans h1)

/-- One-cut rigidity for the cut `13|24` (`prop:fqe-onecut`, entropy_maximum.tex). -/
theorem one_cut_rigidity_13 (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hq : (red13 ψ - (1 / 6 : ℂ) • 1) * (red13 ψ - (1 / 2 : ℂ) • 1) = 0) :
    LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  rigidity_transport swap23 red13 swap23_swap23 swap23_conj (fun _ _ => LUEquiv.swap23)
    normSqPsi_swap23 purity_swap23 red12_swap23 red13_M4 ψ hn hP hq

/-- One-cut rigidity for the cut `14|23` (`prop:fqe-onecut`, entropy_maximum.tex). -/
theorem one_cut_rigidity_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hq : (red14 ψ - (1 / 6 : ℂ) • 1) * (red14 ψ - (1 / 2 : ℂ) • 1) = 0) :
    LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  rigidity_transport swap24 red14 swap24_swap24 swap24_conj (fun _ _ => LUEquiv.swap24)
    normSqPsi_swap24 purity_swap24 red12_swap24 red14_M4 ψ hn hP hq

/-! ### The statement with the spectrum `(1/2, 1/6, 1/6, 1/6)` -/

/-- The spectrum of the Hermitian `R` is the multiset `{1/2, 1/6, 1/6, 1/6}`. -/
def HasM4Spectrum {R : Mat4} (hR : R.IsHermitian) : Prop :=
  Multiset.map hR.eigenvalues Finset.univ.val = {1 / 2, 1 / 6, 1 / 6, 1 / 6}

theorem HasM4Spectrum.quadratic {R : Mat4} {hR : R.IsHermitian} (h : HasM4Spectrum hR) :
    (R - (1 / 6 : ℂ) • 1) * (R - (1 / 2 : ℂ) • 1) = 0 := by
  apply quadratic_of_eigenvalues hR
  intro i
  have hi : hR.eigenvalues i ∈ Multiset.map hR.eigenvalues Finset.univ.val :=
    Multiset.mem_map_of_mem _ (Finset.mem_univ i)
  rw [h] at hi
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hi
  rcases hi with h1 | h1 | h1 | h1
  · exact Or.inr h1
  all_goals exact Or.inl h1

/-- **One-cut rigidity** (`prop:fqe-onecut`). If a unit vector has `P = 1` and the `2|2` cut
`1j|..` has spectrum `(1/2, 1/6, 1/6, 1/6)`, then `ψ` is local-unitarily equivalent to `M₄` or to
`conj M₄`. Stated for the three cuts `12|34`, `13|24`, `14|23`. -/
theorem one_cut_rigidity_spectrum_12 (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hs : HasM4Spectrum (red12_herm ψ)) : LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  one_cut_rigidity_12 ψ hn hP hs.quadratic

theorem one_cut_rigidity_spectrum_13 (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hs : HasM4Spectrum (red13_herm ψ)) : LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  one_cut_rigidity_13 ψ hn hP hs.quadratic

theorem one_cut_rigidity_spectrum_14 (ψ : Psi) (hn : normSqPsi ψ = 1) (hP : purity ψ = 1)
    (hs : HasM4Spectrum (red14_herm ψ)) : LUEquiv M4 ψ ∨ LUEquiv (Psi.conj M4) ψ :=
  one_cut_rigidity_14 ψ hn hP hs.quadratic

/-- info: 'FormalResearch.FourQubitEntropy.one_cut_rigidity_13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_cut_rigidity_13

/-- info: 'FormalResearch.FourQubitEntropy.one_cut_rigidity_14' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms one_cut_rigidity_14

/-- info: 'FormalResearch.FourQubitEntropy.one_cut_rigidity_spectrum_14' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_cut_rigidity_spectrum_14

/-- info: 'FormalResearch.FourQubitEntropy.one_cut_rigidity_spectrum_12' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_cut_rigidity_spectrum_12

/-- info: 'FormalResearch.FourQubitEntropy.one_cut_rigidity_spectrum_13' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms one_cut_rigidity_spectrum_13

end FormalResearch.FourQubitEntropy

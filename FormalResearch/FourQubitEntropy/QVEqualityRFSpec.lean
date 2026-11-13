module

public import FormalResearch.FourQubitEntropy.QVEqualityRFEq
public import FormalResearch.FourQubitEntropy.QVEqualityCritical

/-!
# Spectra `(RF-eq)` of `prop:fqe-critical-variance`: symmetries of `specG` and the extremal spectra

Paper E, `renyi_compatibility.tex`, `eq:fqe-variance-spectra`.  With `a = (1+2s)/3`, `b = (1-s)/3`:

`rfSpec1 = (1/2, a/2, b/2, b/2)`,  `rfSpec2 = ((1+b+2√(ab))/4, (1+b-2√(ab))/4, (1-b)/4, (1-b)/4)`.

This file proves the spectral bookkeeping: `specG` is symmetric under coordinate permutations and under flips of
two signs (`SpecEquiv`), so for `g₁g₂g₃ < 0` its spectrum is that of `(-|g₁|, -|g₂|, -|g₃|)`
(`specEquiv_canon`), and `(RF-eq)` spectra are the canonical spectra of `(a, b, b)` and `(√(ab), √(ab), b)`.
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.QVEquality

open FormalResearch.FourQubitEntropy FormalResearch.FourQubitEntropy.RenyiFull

theorem SpecEquiv.refl' (l : Fin 4 → ℝ) : SpecEquiv l l := ⟨1, fun _i => rfl⟩

theorem SpecEquiv.trans' {l l' l'' : Fin 4 → ℝ} (h : SpecEquiv l l') (h' : SpecEquiv l' l'') :
    SpecEquiv l l'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun i => by rw [he i, he' (e i)]; rfl⟩

theorem SpecEquiv.symm' {l l' : Fin 4 → ℝ} (h : SpecEquiv l l') : SpecEquiv l' l := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, fun i => by rw [he (e.symm i)]; simp⟩

/-! ### Symmetries of `specG` -/

theorem sp_bac (a b c : ℝ) : SpecEquiv (specG b a c) (specG a b c) :=
  ⟨Equiv.swap 1 2, fun i => by fin_cases i <;> simp [specG, Equiv.swap_apply_def] <;> ring⟩

theorem sp_acb (a b c : ℝ) : SpecEquiv (specG a c b) (specG a b c) :=
  ⟨Equiv.swap 0 1, fun i => by fin_cases i <;> simp [specG, Equiv.swap_apply_def] <;> ring⟩

theorem sp_flip_ab (a b c : ℝ) : SpecEquiv (specG (-a) (-b) c) (specG a b c) :=
  ⟨Equiv.swap 0 3 * Equiv.swap 1 2, fun i => by
    fin_cases i <;> simp [specG, Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;> ring⟩

theorem sp_flip_ac (a b c : ℝ) : SpecEquiv (specG (-a) b (-c)) (specG a b c) :=
  ⟨Equiv.swap 0 2 * Equiv.swap 1 3, fun i => by
    fin_cases i <;> simp [specG, Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;> ring⟩

theorem sp_flip_bc (a b c : ℝ) : SpecEquiv (specG a (-b) (-c)) (specG a b c) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 2 3, fun i => by
    fin_cases i <;> simp [specG, Equiv.swap_apply_def, Equiv.Perm.mul_apply] <;> ring⟩

theorem specEquiv_canon {g1 g2 g3 : ℝ} (h : g1 * g2 * g3 < 0) :
    SpecEquiv (specG g1 g2 g3) (specG (-|g1|) (-|g2|) (-|g3|)) := by
  have n1 : g1 ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  have n2 : g2 ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  have n3 : g3 ≠ 0 := fun h0 => by rw [h0] at h; simp at h
  rcases lt_or_gt_of_ne n1 with p1 | p1 <;> rcases lt_or_gt_of_ne n2 with p2 | p2 <;>
    rcases lt_or_gt_of_ne n3 with p3 | p3
  · rw [abs_of_neg p1, abs_of_neg p2, abs_of_neg p3]; simp only [neg_neg]; exact SpecEquiv.refl' _
  · exfalso; nlinarith [mul_pos_of_neg_of_neg p1 p2]
  · exfalso; nlinarith [mul_pos_of_neg_of_neg p1 p3, mul_pos_of_neg_of_neg p1 p3]
  · rw [abs_of_neg p1, abs_of_pos p2, abs_of_pos p3]; simp only [neg_neg]
    exact (sp_flip_bc g1 g2 g3).symm'
  · exfalso; nlinarith [mul_pos_of_neg_of_neg p2 p3]
  · rw [abs_of_pos p1, abs_of_neg p2, abs_of_pos p3]; simp only [neg_neg]
    exact (sp_flip_ac g1 g2 g3).symm'
  · rw [abs_of_pos p1, abs_of_pos p2, abs_of_neg p3]; simp only [neg_neg]
    exact (sp_flip_ab g1 g2 g3).symm'
  · exfalso; nlinarith [mul_pos p1 p2, mul_pos (mul_pos p1 p2) p3]

/-- The two spectra of `eq:fqe-variance-spectra`, as functions of `(a, b)` (resp. `(t, b)`, `t = √(ab)`). -/
noncomputable def rfSpec1' (a b : ℝ) : Fin 4 → ℝ := ![1 / 2, a / 2, b / 2, b / 2]
noncomputable def rfSpec2' (t b : ℝ) : Fin 4 → ℝ :=
  ![(1 + b + 2 * t) / 4, (1 + b - 2 * t) / 4, (1 - b) / 4, (1 - b) / 4]

theorem sp_aligned0 {a b : ℝ} (hab : a + 2 * b = 1) :
    SpecEquiv (specG (-a) (-b) (-b)) (rfSpec1' a b) :=
  ⟨⟨![2, 3, 1, 0], ![3, 2, 0, 1], by decide, by decide⟩, fun i => by
    fin_cases i <;> simp [specG, rfSpec1'] <;> linarith⟩

theorem sp_cross0 (t b : ℝ) :
    SpecEquiv (specG (-t) (-t) (-b)) (rfSpec2' t b) :=
  ⟨⟨![1, 2, 3, 0], ![3, 0, 1, 2], by decide, by decide⟩, fun i => by
    fin_cases i <;> simp [specG, rfSpec2'] <;> ring⟩

theorem sp_aligned {a b x y z : ℝ} (hab : a + 2 * b = 1)
    (h : (x = a ∧ y = b ∧ z = b) ∨ (x = b ∧ y = a ∧ z = b) ∨ (x = b ∧ y = b ∧ z = a)) :
    SpecEquiv (specG (-x) (-y) (-z)) (rfSpec1' a b) := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;> rw [hx, hy, hz]
  · exact sp_aligned0 hab
  · exact (sp_bac (-a) (-b) (-b)).trans' (sp_aligned0 hab)
  · exact ((sp_acb (-b) (-a) (-b)).trans' (sp_bac (-a) (-b) (-b))).trans' (sp_aligned0 hab)

theorem sp_cross {t b x y z : ℝ}
    (h : (x = t ∧ y = t ∧ z = b) ∨ (x = t ∧ y = b ∧ z = t) ∨ (x = b ∧ y = t ∧ z = t)) :
    SpecEquiv (specG (-x) (-y) (-z)) (rfSpec2' t b) := by
  rcases h with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;> rw [hx, hy, hz]
  · exact sp_cross0 t b
  · exact (sp_acb (-t) (-t) (-b)).trans' (sp_cross0 t b)
  · exact ((sp_bac (-t) (-b) (-t)).trans' (sp_acb (-t) (-t) (-b))).trans' (sp_cross0 t b)

/-- `(RF-eq)`: `a = (1+2s)/3`, `b = (1-s)/3`. -/
noncomputable def rfSpec1 (s : ℝ) : Fin 4 → ℝ := rfSpec1' ((1 + 2 * s) / 3) ((1 - s) / 3)
noncomputable def rfSpec2 (s : ℝ) : Fin 4 → ℝ :=
  rfSpec2' (Real.sqrt ((1 + 2 * s) / 3 * ((1 - s) / 3))) ((1 - s) / 3)

/-- The three cut spectra of `eq:fqe-variance-spectra`, up to ordering of the cuts and of each spectrum. -/
def IsRfTriple (l₂ l₃ l₄ : Fin 4 → ℝ) (s : ℝ) : Prop :=
  (SpecEquiv l₂ (rfSpec1 s) ∧ SpecEquiv l₃ (rfSpec2 s) ∧ SpecEquiv l₄ (rfSpec2 s)) ∨
  (SpecEquiv l₂ (rfSpec2 s) ∧ SpecEquiv l₃ (rfSpec1 s) ∧ SpecEquiv l₄ (rfSpec2 s)) ∨
  (SpecEquiv l₂ (rfSpec2 s) ∧ SpecEquiv l₃ (rfSpec2 s) ∧ SpecEquiv l₄ (rfSpec1 s))

theorem abs_mul_eq_sqrt {x y A B : ℝ} (hx : x ^ 2 = A) (hy : y ^ 2 = B) :
    |x * y| = Real.sqrt (A * B) := by
  rw [← Real.sqrt_sq_eq_abs, mul_pow, hx, hy]

/-- **The spectra of the equality case** for the `(m, n)` coordinates: with `A = (m_i²)`, `B = (n_i²)`
rearrangements of `((1+2s)/3, (1-s)/3, (1-s)/3)` and `κ > 0`, the cut spectra are the `(RF-eq)` triple. -/
theorem spc_rf_triple (m n : Fin 3 → ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hκ : 0 < kap m n)
    (hA : ((m 0 ^ 2 = (1 + 2 * s) / 3 ∧ m 1 ^ 2 = (1 - s) / 3 ∧ m 2 ^ 2 = (1 - s) / 3) ∨
        (m 0 ^ 2 = (1 - s) / 3 ∧ m 1 ^ 2 = (1 + 2 * s) / 3 ∧ m 2 ^ 2 = (1 - s) / 3) ∨
        (m 0 ^ 2 = (1 - s) / 3 ∧ m 1 ^ 2 = (1 - s) / 3 ∧ m 2 ^ 2 = (1 + 2 * s) / 3)))
    (hB : ((n 0 ^ 2 = (1 + 2 * s) / 3 ∧ n 1 ^ 2 = (1 - s) / 3 ∧ n 2 ^ 2 = (1 - s) / 3) ∨
        (n 0 ^ 2 = (1 - s) / 3 ∧ n 1 ^ 2 = (1 + 2 * s) / 3 ∧ n 2 ^ 2 = (1 - s) / 3) ∨
        (n 0 ^ 2 = (1 - s) / 3 ∧ n 1 ^ 2 = (1 - s) / 3 ∧ n 2 ^ 2 = (1 + 2 * s) / 3))) :
    IsRfTriple (spc0 m n) (spc1 m n) (spc2 m n) s := by
  have hab : (1 + 2 * s) / 3 + 2 * ((1 - s) / 3) = 1 := by ring
  have ha : 0 ≤ (1 + 2 * s) / 3 := by linarith
  have hb : 0 ≤ (1 - s) / 3 := by linarith
  have p0 : m 0 * n 0 * (m 1 * n 1) * -(m 2 * n 2) < 0 := by
    have : m 0 * n 0 * (m 1 * n 1) * -(m 2 * n 2) = -kap m n := by unfold kap; ring
    rw [this]; linarith
  have p1 : -(m 2 * n 1) * (m 0 * n 2) * (m 1 * n 0) < 0 := by
    have : -(m 2 * n 1) * (m 0 * n 2) * (m 1 * n 0) = -kap m n := by unfold kap; ring
    rw [this]; linarith
  have p2 : m 1 * n 2 * (m 2 * n 0) * -(m 0 * n 1) < 0 := by
    have : m 1 * n 2 * (m 2 * n 0) * -(m 0 * n 1) = -kap m n := by unfold kap; ring
    rw [this]; linarith
  have c0 : SpecEquiv (spc0 m n) (specG (-|m 0 * n 0|) (-|m 1 * n 1|) (-|-(m 2 * n 2)|)) :=
    specEquiv_canon p0
  have c1 : SpecEquiv (spc1 m n) (specG (-|-(m 2 * n 1)|) (-|m 0 * n 2|) (-|m 1 * n 0|)) :=
    specEquiv_canon p1
  have c2 : SpecEquiv (spc2 m n) (specG (-|m 1 * n 2|) (-|m 2 * n 0|) (-|-(m 0 * n 1)|)) :=
    specEquiv_canon p2
  simp only [abs_neg] at c0 c1 c2
  have hba : Real.sqrt ((1 - s) / 3 * ((1 + 2 * s) / 3)) = Real.sqrt ((1 + 2 * s) / 3 * ((1 - s) / 3)) := by
    rw [mul_comm]
  rcases hA with ⟨hm0, hm1, hm2⟩ | ⟨hm0, hm1, hm2⟩ | ⟨hm0, hm1, hm2⟩ <;>
  rcases hB with ⟨hn0, hn1, hn2⟩ | ⟨hn0, hn1, hn2⟩ | ⟨hn0, hn1, hn2⟩
  all_goals
    rw [abs_mul_eq_sqrt hm0 hn0, abs_mul_eq_sqrt hm1 hn1, abs_mul_eq_sqrt hm2 hn2] at c0
    rw [abs_mul_eq_sqrt hm2 hn1, abs_mul_eq_sqrt hm0 hn2, abs_mul_eq_sqrt hm1 hn0] at c1
    rw [abs_mul_eq_sqrt hm1 hn2, abs_mul_eq_sqrt hm2 hn0, abs_mul_eq_sqrt hm0 hn1] at c2
    simp only [Real.sqrt_mul_self ha, Real.sqrt_mul_self hb, hba] at c0 c1 c2
  -- aligned cut for the nine cases `(i, j)` in order: 0, 2, 1, 1, 0, 2, 2, 1, 0
  · exact Or.inl ⟨c0.trans' (sp_aligned hab (by simp)), c1.trans' (sp_cross (by simp)),
      c2.trans' (sp_cross (by simp))⟩
  · exact Or.inr (Or.inr ⟨c0.trans' (sp_cross (by simp)), c1.trans' (sp_cross (by simp)),
      c2.trans' (sp_aligned hab (by simp))⟩)
  · exact Or.inr (Or.inl ⟨c0.trans' (sp_cross (by simp)), c1.trans' (sp_aligned hab (by simp)),
      c2.trans' (sp_cross (by simp))⟩)
  · exact Or.inr (Or.inl ⟨c0.trans' (sp_cross (by simp)), c1.trans' (sp_aligned hab (by simp)),
      c2.trans' (sp_cross (by simp))⟩)
  · exact Or.inl ⟨c0.trans' (sp_aligned hab (by simp)), c1.trans' (sp_cross (by simp)),
      c2.trans' (sp_cross (by simp))⟩
  · exact Or.inr (Or.inr ⟨c0.trans' (sp_cross (by simp)), c1.trans' (sp_cross (by simp)),
      c2.trans' (sp_aligned hab (by simp))⟩)
  · exact Or.inr (Or.inr ⟨c0.trans' (sp_cross (by simp)), c1.trans' (sp_cross (by simp)),
      c2.trans' (sp_aligned hab (by simp))⟩)
  · exact Or.inr (Or.inl ⟨c0.trans' (sp_cross (by simp)), c1.trans' (sp_aligned hab (by simp)),
      c2.trans' (sp_cross (by simp))⟩)
  · exact Or.inl ⟨c0.trans' (sp_aligned hab (by simp)), c1.trans' (sp_cross (by simp)),
      c2.trans' (sp_cross (by simp))⟩

end FormalResearch.FourQubitEntropy.QVEquality

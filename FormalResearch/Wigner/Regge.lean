module

public import FormalResearch.Wigner.Symmetry

/-!
# Regge symmetries of the `6j` symbol (DLMF 34.5.9 and 34.5.10)

The Racah sum depends on the six spins only through the four triad sums
`a₁ = j₁+j₂+j₃`, `a₂ = j₁+l₂+l₃`, `a₃ = l₁+j₂+l₃`, `a₄ = l₁+l₂+j₃` and the three quad sums
`b₁ = j₁+j₂+l₁+l₂`, `b₂ = j₂+j₃+l₂+l₃`, `b₃ = j₃+j₁+l₃+l₁`, symmetrically in the `aᵢ` and in the
`bⱼ` (apart from the prefactor), and the product of the four `Δ²` factors equals
`∏ᵢⱼ (bⱼ - aᵢ)! / ∏ᵢ (aᵢ+1)!`, which is also symmetric.  Hence the whole group `S₄ × S₃` of order
`144` of permutations of the `aᵢ` and `bⱼ` leaves `sixJ` invariant, and a **termwise** permutation of
the seven inverse factorials proves each Regge move; no hypergeometric transformation
(Whipple's `₄F₃`) is needed once the sum is written in Racah's form.

* `sixJ_regge1` is DLMF 34.5.9 (permutation `a₃ ↔ a₄`, `b` fixed);
* `sixJ_regge2` is DLMF 34.5.10 (permutation `(a₂ a₄ a₃)`, `(b₁ b₂ b₃) ↦ (b₂ b₃ b₁)`).

Both hold for **all** rational spins, with no admissibility hypothesis: the zero extension of the
symbol is respected because the twelve numbers `bⱼ - aᵢ` are permuted.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma fq_nonneg (x : ℚ) : 0 ≤ fq x := by
  unfold fq; split_ifs <;> positivity

lemma ifa_nonneg (x : ℚ) : 0 ≤ ifa x := by
  unfold ifa invFact; split_ifs <;> positivity

lemma triSq_nonneg (a b c : ℚ) : 0 ≤ triSq a b c := by
  unfold triSq
  have := fq_nonneg (a + b - c); have := fq_nonneg (a - b + c)
  have := fq_nonneg (-a + b + c); have := ifa_nonneg (a + b + c + 1)
  positivity

lemma sqrt_mul4 {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Real.sqrt a * Real.sqrt b * Real.sqrt c * Real.sqrt d = Real.sqrt (a * b * c * d) := by
  rw [← Real.sqrt_mul ha, ← Real.sqrt_mul (mul_nonneg ha hb),
    ← Real.sqrt_mul (mul_nonneg (mul_nonneg ha hb) hc)]

/-- If the product of the four `Δ²` factors and the Racah sums agree, so do the symbols. -/
lemma sixJ_congr_of_prod {j₁ j₂ j₃ l₁ l₂ l₃ k₁ k₂ k₃ m₁ m₂ m₃ : ℚ}
    (hP : triSq k₁ k₂ k₃ * triSq k₁ m₂ m₃ * triSq m₁ k₂ m₃ * triSq m₁ m₂ k₃ =
      triSq j₁ j₂ j₃ * triSq j₁ l₂ l₃ * triSq l₁ j₂ l₃ * triSq l₁ l₂ j₃)
    (hR : racahSum6 k₁ k₂ k₃ m₁ m₂ m₃ = racahSum6 j₁ j₂ j₃ l₁ l₂ l₃) :
    sixJ k₁ k₂ k₃ m₁ m₂ m₃ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  unfold sixJ
  rw [sqrt_mul4 (triSq_nonneg _ _ _) (triSq_nonneg _ _ _) (triSq_nonneg _ _ _),
    sqrt_mul4 (triSq_nonneg _ _ _) (triSq_nonneg _ _ _) (triSq_nonneg _ _ _), hP, hR]

lemma term6_regge1 {j1 j2 j3 l1 l2 l3 J2 J3 L2 L3 : ℚ}
    (hJ2 : J2 = (j2 + l2 + j3 - l3) / 2) (hJ3 : J3 = (j2 - l2 + j3 + l3) / 2) (hL2 : L2 = (j2 + l2 - j3 + l3) / 2) (hL3 : L3 = (-j2 + l2 + j3 + l3) / 2) (σ : ℚ) (ε φ : ℝ) :
    term6 j1 J2 J3 l1 L2 L3 σ ε φ = term6 j1 j2 j3 l1 l2 l3 σ ε φ := by
  unfold term6
  rw [P7_vec, P7_vec]
  rw [show σ - j1 - J2 - J3 = σ - j1 - j2 - j3 by linarith,
    show σ - j1 - L2 - L3 = σ - j1 - l2 - l3 by linarith,
    show σ - l1 - J2 - L3 = σ - l1 - l2 - j3 by linarith,
    show σ - l1 - L2 - J3 = σ - l1 - j2 - l3 by linarith,
    show j1 + J2 + l1 + L2 - σ = j1 + j2 + l1 + l2 - σ by linarith,
    show J2 + J3 + L2 + L3 - σ = j2 + j3 + l2 + l3 - σ by linarith,
    show J3 + j1 + L3 + l1 - σ = j3 + j1 + l3 + l1 - σ by linarith]
  ring

lemma triSq_prod_regge1 {j1 j2 j3 l1 l2 l3 J2 J3 L2 L3 : ℚ}
    (hJ2 : J2 = (j2 + l2 + j3 - l3) / 2) (hJ3 : J3 = (j2 - l2 + j3 + l3) / 2) (hL2 : L2 = (j2 + l2 - j3 + l3) / 2) (hL3 : L3 = (-j2 + l2 + j3 + l3) / 2) :
    triSq j1 J2 J3 * triSq j1 L2 L3 *
      triSq l1 J2 L3 * triSq l1 L2 J3 =
    triSq j1 j2 j3 * triSq j1 l2 l3 * triSq l1 j2 l3 * triSq l1 l2 j3 := by
  unfold triSq
  rw [show j1 + J2 - J3 = j1 + l2 - l3 by linarith,
    show j1 - J2 + J3 = j1 - l2 + l3 by linarith,
    show -j1 + J2 + J3 = -j1 + j2 + j3 by linarith,
    show j1 + J2 + J3 + 1 = j1 + j2 + j3 + 1 by linarith,
    show j1 + L2 - L3 = j1 + j2 - j3 by linarith,
    show j1 - L2 + L3 = j1 - j2 + j3 by linarith,
    show -j1 + L2 + L3 = -j1 + l2 + l3 by linarith,
    show j1 + L2 + L3 + 1 = j1 + l2 + l3 + 1 by linarith,
    show l1 + J2 - L3 = l1 + j2 - l3 by linarith,
    show l1 - J2 + L3 = l1 - j2 + l3 by linarith,
    show -l1 + J2 + L3 = -l1 + l2 + j3 by linarith,
    show l1 + J2 + L3 + 1 = l1 + l2 + j3 + 1 by linarith,
    show l1 + L2 - J3 = l1 + l2 - j3 by linarith,
    show l1 - L2 + J3 = l1 - l2 + j3 by linarith,
    show -l1 + L2 + J3 = -l1 + j2 + l3 by linarith,
    show l1 + L2 + J3 + 1 = l1 + j2 + l3 + 1 by linarith]
  ring

lemma term6_regge2 {j1 j2 j3 l1 l2 l3 J1 J2 J3 L1 L2 L3 : ℚ}
    (hJ1 : J1 = (j2 + l2 + j3 - l3) / 2) (hJ2 : J2 = (j1 - l1 + j3 + l3) / 2) (hJ3 : J3 = (j1 + l1 + j2 - l2) / 2) (hL1 : L1 = (j2 + l2 - j3 + l3) / 2) (hL2 : L2 = (-j1 + l1 + j3 + l3) / 2) (hL3 : L3 = (j1 + l1 - j2 + l2) / 2) (σ : ℚ) (ε φ : ℝ) :
    term6 J1 J2 J3 L1 L2 L3 σ ε φ = term6 j1 j2 j3 l1 l2 l3 σ ε φ := by
  unfold term6
  rw [P7_vec, P7_vec]
  rw [show σ - J1 - J2 - J3 = σ - j1 - j2 - j3 by linarith,
    show σ - J1 - L2 - L3 = σ - l1 - l2 - j3 by linarith,
    show σ - L1 - J2 - L3 = σ - j1 - l2 - l3 by linarith,
    show σ - L1 - L2 - J3 = σ - l1 - j2 - l3 by linarith,
    show J1 + J2 + L1 + L2 - σ = j2 + j3 + l2 + l3 - σ by linarith,
    show J2 + J3 + L2 + L3 - σ = j3 + j1 + l3 + l1 - σ by linarith,
    show J3 + J1 + L3 + L1 - σ = j1 + j2 + l1 + l2 - σ by linarith]
  ring

lemma triSq_prod_regge2 {j1 j2 j3 l1 l2 l3 J1 J2 J3 L1 L2 L3 : ℚ}
    (hJ1 : J1 = (j2 + l2 + j3 - l3) / 2) (hJ2 : J2 = (j1 - l1 + j3 + l3) / 2) (hJ3 : J3 = (j1 + l1 + j2 - l2) / 2) (hL1 : L1 = (j2 + l2 - j3 + l3) / 2) (hL2 : L2 = (-j1 + l1 + j3 + l3) / 2) (hL3 : L3 = (j1 + l1 - j2 + l2) / 2) :
    triSq J1 J2 J3 * triSq J1 L2 L3 *
      triSq L1 J2 L3 * triSq L1 L2 J3 =
    triSq j1 j2 j3 * triSq j1 l2 l3 * triSq l1 j2 l3 * triSq l1 l2 j3 := by
  unfold triSq
  rw [show J1 + J2 - J3 = -l1 + l2 + j3 by linarith,
    show J1 - J2 + J3 = l1 + j2 - l3 by linarith,
    show -J1 + J2 + J3 = j1 - l2 + l3 by linarith,
    show J1 + J2 + J3 + 1 = j1 + j2 + j3 + 1 by linarith,
    show J1 + L2 - L3 = -j1 + j2 + j3 by linarith,
    show J1 - L2 + L3 = j1 + l2 - l3 by linarith,
    show -J1 + L2 + L3 = l1 - j2 + l3 by linarith,
    show J1 + L2 + L3 + 1 = l1 + l2 + j3 + 1 by linarith,
    show L1 + J2 - L3 = -l1 + j2 + l3 by linarith,
    show L1 - J2 + L3 = l1 + l2 - j3 by linarith,
    show -L1 + J2 + L3 = j1 - j2 + j3 by linarith,
    show L1 + J2 + L3 + 1 = j1 + l2 + l3 + 1 by linarith,
    show L1 + L2 - J3 = -j1 + l2 + l3 by linarith,
    show L1 - L2 + J3 = j1 + j2 - j3 by linarith,
    show -L1 + L2 + J3 = l1 - l2 + j3 by linarith,
    show L1 + L2 + J3 + 1 = l1 + j2 + l3 + 1 by linarith]
  ring

lemma racahSum6_regge1 {j1 j2 j3 l1 l2 l3 J2 J3 L2 L3 : ℚ}
    (hJ2 : J2 = (j2 + l2 + j3 - l3) / 2) (hJ3 : J3 = (j2 - l2 + j3 + l3) / 2)
    (hL2 : L2 = (j2 + l2 - j3 + l3) / 2) (hL3 : L3 = (-j2 + l2 + j3 + l3) / 2) :
    racahSum6 j1 J2 J3 l1 L2 L3 = racahSum6 j1 j2 j3 l1 l2 l3 := by
  unfold racahSum6
  exact finsum_congr fun t => term6_regge1 hJ2 hJ3 hL2 hL3 _ _ _

lemma racahSum6_regge2 {j1 j2 j3 l1 l2 l3 J1 J2 J3 L1 L2 L3 : ℚ}
    (hJ1 : J1 = (j2 + l2 + j3 - l3) / 2) (hJ2 : J2 = (j1 - l1 + j3 + l3) / 2)
    (hJ3 : J3 = (j1 + l1 + j2 - l2) / 2) (hL1 : L1 = (j2 + l2 - j3 + l3) / 2)
    (hL2 : L2 = (-j1 + l1 + j3 + l3) / 2) (hL3 : L3 = (j1 + l1 - j2 + l2) / 2) :
    racahSum6 J1 J2 J3 L1 L2 L3 = racahSum6 j1 j2 j3 l1 l2 l3 := by
  unfold racahSum6
  exact finsum_congr fun t => term6_regge2 hJ1 hJ2 hJ3 hL1 hL2 hL3 _ _ _

/-- **DLMF 34.5.9** (Regge symmetry).  Valid for all rational spins: both sides vanish together
outside the admissible domain. -/
theorem sixJ_regge1 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₁ j₂ j₃ l₁ l₂ l₃ =
      sixJ j₁ ((j₂ + l₂ + j₃ - l₃) / 2) ((j₂ - l₂ + j₃ + l₃) / 2) l₁
        ((j₂ + l₂ - j₃ + l₃) / 2) ((-j₂ + l₂ + j₃ + l₃) / 2) :=
  (sixJ_congr_of_prod (triSq_prod_regge1 rfl rfl rfl rfl) (racahSum6_regge1 rfl rfl rfl rfl)).symm

/-- **DLMF 34.5.10** (second Regge symmetry), for all rational spins. -/
theorem sixJ_regge2 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₁ j₂ j₃ l₁ l₂ l₃ =
      sixJ ((j₂ + l₂ + j₃ - l₃) / 2) ((j₁ - l₁ + j₃ + l₃) / 2) ((j₁ + l₁ + j₂ - l₂) / 2)
        ((j₂ + l₂ - j₃ + l₃) / 2) ((-j₁ + l₁ + j₃ + l₃) / 2) ((j₁ + l₁ - j₂ + l₂) / 2) :=
  (sixJ_congr_of_prod (triSq_prod_regge2 rfl rfl rfl rfl rfl rfl)
    (racahSum6_regge2 rfl rfl rfl rfl rfl rfl)).symm

/-- The form used in Weyl/P2 (`eq:6jRegge`): after a cyclic column permutation,
`{c a b; f b+m a+n} = {c, b+(m-n)/2, a+(n-m)/2; f, a+(m+n)/2, b+(m+n)/2}`. -/
theorem sixJ_regge1_shifted (a b c f m n : ℚ) :
    sixJ c a b f (b + m) (a + n) =
      sixJ c (b + (m - n) / 2) (a + (n - m) / 2) f (a + (m + n) / 2) (b + (m + n) / 2) := by
  rw [sixJ_regge1 c a b f (b + m) (a + n)]
  congr 1 <;> ring

/-- info: 'FormalResearch.Wigner.sixJ_regge1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_regge1

/-- info: 'FormalResearch.Wigner.sixJ_regge2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_regge2

/-- info: 'FormalResearch.Wigner.sixJ_regge1_shifted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_regge1_shifted

end FormalResearch.Wigner

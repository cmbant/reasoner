module

public import FormalResearch.Wigner.OrthogBase

/-!
# Racah orthogonality of the `6j` symbol (DLMF 34.5.14)

`sixJ_orthogonality`: for fixed `j₁ j₂ l₁ l₂` and admissible `l₃, l₃'` (the triads `(j₁,l₂,l₃)`,
`(l₁,j₂,l₃)` and the same for `l₃'` are triangles with integral sum),
`∑_{j₃} (2j₃+1)(2l₃+1) {j₁ j₂ j₃; l₁ l₂ l₃} {j₁ j₂ j₃; l₁ l₂ l₃'} = δ_{l₃ l₃'}`,
the sum over the lattice `j₃ = j₁ + j₂ - k`, `k ∈ ℕ`, which contains every `j₃` with
`(j₁,j₂,j₃)` a triangle; the symbol is zero-extended, so this is the finite sum over the
admissible range.
-/

@[expose] public section

namespace FormalResearch.Wigner

lemma IsTri.perm13 {a b c : ℚ} (h : IsTri a b c) : IsTri c b a := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · convert h3 using 1; ring
  · convert h2 using 1; ring
  · convert h1 using 1; ring

lemma IsTri.comm12 {a b c : ℚ} (h : IsTri a b c) : IsTri b a c := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · convert h1 using 1; ring
  · convert h3 using 1; ring
  · convert h2 using 1; ring

/-- Exchanging upper and lower entries in columns 2 and 3. -/
lemma sixJ_exch23 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₁ l₂ l₃ l₁ j₂ j₃ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  calc sixJ j₁ l₂ l₃ l₁ j₂ j₃ = sixJ l₂ j₁ l₃ j₂ l₁ j₃ := (sixJ_swap12 l₂ j₁ l₃ j₂ l₁ j₃)
    _ = sixJ l₂ l₃ j₁ j₂ j₃ l₁ := (sixJ_swap23 l₂ l₃ j₁ j₂ j₃ l₁)
    _ = sixJ j₂ j₃ j₁ l₂ l₃ l₁ := sixJ_exch12 j₂ j₃ j₁ l₂ l₃ l₁
    _ = sixJ j₂ j₁ j₃ l₂ l₁ l₃ := (sixJ_swap23 j₂ j₁ j₃ l₂ l₁ l₃)
    _ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := sixJ_swap12 j₁ j₂ j₃ l₁ l₂ l₃


lemma mem_lattice_image {x a b : ℚ} (h : IsTri x a b) {N : ℕ} (hN : a + b < N) :
    x ∈ (Finset.range N).image (fun k : ℕ => a + b - (k : ℚ)) := by
  have h0 := h.nonneg_first
  obtain ⟨-, -, ⟨n, hn⟩⟩ := h
  rw [Finset.mem_image]
  refine ⟨n, ?_, by linarith⟩
  rw [Finset.mem_range]
  have : (n : ℚ) < N := by linarith
  exact_mod_cast this

/-- The lattice sum depends only on the support of the summand. -/
lemma lsum_eq_of_support {a b c d : ℚ} {f : ℚ → ℝ}
    (hf : ∀ x, f x ≠ 0 → IsTri x a b ∧ IsTri x c d) : lsum a b f = lsum c d f := by
  have hneg : ∀ x : ℚ, x < 0 → f x = 0 := by
    intro x hx
    by_contra h
    have := (hf x h).1.nonneg_first
    linarith
  obtain ⟨N1, hN1⟩ := exists_nat_gt_lattice a b
  obtain ⟨N2, hN2⟩ := exists_nat_gt_lattice c d
  rw [lsum_eq_sum hneg N1 hN1, lsum_eq_sum hneg N2 hN2]
  have inj1 : Function.Injective (fun k : ℕ => a + b - (k : ℚ)) := by
    intro k l h; simp only [sub_right_inj] at h; exact_mod_cast h
  have inj2 : Function.Injective (fun k : ℕ => c + d - (k : ℚ)) := by
    intro k l h; simp only [sub_right_inj] at h; exact_mod_cast h
  rw [← Finset.sum_image (f := f) (g := fun k : ℕ => a + b - (k : ℚ))
      (fun k _ l _ h => inj1 h),
    ← Finset.sum_image (f := f) (g := fun k : ℕ => c + d - (k : ℚ))
      (fun k _ l _ h => inj2 h)]
  set S1 := (Finset.range N1).image (fun k : ℕ => a + b - (k : ℚ))
  set S2 := (Finset.range N2).image (fun k : ℕ => c + d - (k : ℚ))
  have e1 : ∑ x ∈ S1, f x = ∑ x ∈ S1 ∪ S2, f x := by
    apply Finset.sum_subset Finset.subset_union_left
    intro x hx hx1
    by_contra hne
    exact hx1 (mem_lattice_image (hf x hne).1 hN1)
  have e2 : ∑ x ∈ S2, f x = ∑ x ∈ S1 ∪ S2, f x := by
    apply Finset.sum_subset Finset.subset_union_right
    intro x hx hx1
    by_contra hne
    exact hx1 (mem_lattice_image (hf x hne).2 hN2)
  rw [e1, e2]


lemma OAdm.swap23 {a b c d μ : ℚ} (h : OAdm a b c d μ) : OAdm b a d c μ :=
  ⟨h.2.comm23, h.1.comm23⟩

lemma OAdm.exch23 {a b c d μ : ℚ} (h : OAdm a b c d μ) : OAdm c d a b μ := ⟨h.2, h.1⟩

lemma OA_swap23 (a b c d μ ν : ℚ) : OA a b c d μ ν = OA b a d c μ ν := by
  unfold OA lsum
  simp only [sixJ_swap23, add_comm b a]

lemma OA_exch23 (a b c d μ ν : ℚ) : OA a b c d μ ν = OA c d a b μ ν := by
  unfold OA
  have : ∀ x : ℚ, (2 * (x : ℝ) + 1) * (sixJ x c d μ a b * sixJ x c d ν a b) =
      (2 * (x : ℝ) + 1) * (sixJ x a b μ c d * sixJ x a b ν c d) := by
    intro x; rw [sixJ_exch23 x a b μ c d, sixJ_exch23 x a b ν c d]
  simp only [this]
  symm
  apply lsum_eq_of_support
  intro x hx
  have h1 : sixJ x a b μ c d ≠ 0 := by
    intro h0; apply hx; rw [h0]; ring
  by_contra hn
  exact h1 (sixJ_eq_zero_of_not_tri12 (fun h => hn ⟨h.2, h.1⟩))

lemma OAdm.minimal_cases {a b c d μ : ℚ} (h : OAdm a b c d μ) (h' : ¬ OAdm a b c d (μ - 1)) :
    μ = b - c ∨ μ = c - b ∨ μ = a - d ∨ μ = d - a := by
  unfold OAdm at h'
  rcases not_and_or.mp h' with h' | h'
  · rcases tri_prev_fail h.1 h' with e | e
    · right; right; right; exact e
    · right; right; left; exact e
  · rcases tri_prev_fail h.2 h' with e | e
    · left; exact e
    · right; left; exact e

lemma exists_minimal (a b c d : ℚ) : ∀ (n : ℕ) (μ : ℚ), OAdm a b c d μ → μ ≤ n →
    ∃ (μ₀ : ℚ) (k : ℕ), OAdm a b c d μ₀ ∧ ¬ OAdm a b c d (μ₀ - 1) ∧ μ = μ₀ + k := by
  intro n
  induction n with
  | zero =>
    intro μ h hμ
    refine ⟨μ, 0, h, fun hp => ?_, by simp⟩
    have := hp.1.nonneg_first
    push_cast at hμ
    linarith
  | succ n ih =>
    intro μ h hμ
    by_cases hp : OAdm a b c d (μ - 1)
    · obtain ⟨μ₀, k, h0, h1, h2⟩ := ih (μ - 1) hp (by push_cast at hμ; linarith)
      exact ⟨μ₀, k + 1, h0, h1, by push_cast; linarith⟩
    · exact ⟨μ, 0, h, hp, by simp⟩

/-- **Normalisation of the `6j` orthogonality relation**:
`(2μ+1) ∑ₓ (2x+1) {x a b; μ c d}² = 1` for admissible `μ`. -/
theorem orth_norm (a b c d μ : ℚ) (h : OAdm a b c d μ) :
    (2 * (μ : ℝ) + 1) * OA a b c d μ μ = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt_lattice μ 0
  obtain ⟨μ₀, k, h0, hmin, hμ⟩ := exists_minimal a b c d N μ h (by linarith)
  have hnn : 0 ≤ μ₀ := h0.1.nonneg_first
  have hchain := orth_norm_chain a b c d μ₀ hnn h0 k (by rw [← hμ]; exact h)
  rw [← hμ] at hchain
  rw [hchain]
  rcases h0.minimal_cases hmin with e | e | e | e
  · rw [e]; exact orth_norm_base a b c d (by rw [← e]; exact h0)
  · rw [OA_swap23, OA_exch23, e]
    exact orth_norm_base d c b a (by rw [← e]; exact h0.swap23.exch23)
  · rw [OA_swap23, e]
    exact orth_norm_base b a d c (by rw [← e]; exact h0.swap23)
  · rw [OA_exch23, e]
    exact orth_norm_base c d a b (by rw [← e]; exact h0.exch23)


/-- Exchanging the first and third columns. -/
lemma sixJ_swap13 (j₁ j₂ j₃ l₁ l₂ l₃ : ℚ) :
    sixJ j₃ j₂ j₁ l₃ l₂ l₁ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := by
  calc sixJ j₃ j₂ j₁ l₃ l₂ l₁ = sixJ j₃ j₁ j₂ l₃ l₁ l₂ := sixJ_swap23 j₃ j₁ j₂ l₃ l₁ l₂
    _ = sixJ j₁ j₃ j₂ l₁ l₃ l₂ := sixJ_swap12 j₁ j₃ j₂ l₁ l₃ l₂
    _ = sixJ j₁ j₂ j₃ l₁ l₂ l₃ := sixJ_swap23 j₁ j₂ j₃ l₁ l₂ l₃

/-- **DLMF 34.5.14 (Racah orthogonality of the `6j` symbol).**  For fixed `j₁ j₂ l₁ l₂` and
`l₃`, `l₃'` such that `(j₁,l₂,l₃)`, `(l₁,j₂,l₃)`, `(j₁,l₂,l₃')`, `(l₁,j₂,l₃')` are triangles with
integral sum,
`∑_{j₃} (2j₃+1)(2l₃+1) {j₁ j₂ j₃; l₁ l₂ l₃} {j₁ j₂ j₃; l₁ l₂ l₃'} = δ_{l₃ l₃'}`.
The sum is over the lattice `j₃ = j₁ + j₂ - k`, `k ∈ ℕ` (it contains every `j₃` with
`(j₁,j₂,j₃)` a triangle, and the symbol is zero outside the admissible range, so the `finsum` is
the finite sum over `max(|j₁-j₂|,|l₁-l₂|) ≤ j₃ ≤ min(j₁+j₂,l₁+l₂)`). -/
theorem sixJ_orthogonality (j₁ j₂ l₁ l₂ l₃ l₃' : ℚ)
    (h1 : IsTri j₁ l₂ l₃) (h2 : IsTri l₁ j₂ l₃) (h1' : IsTri j₁ l₂ l₃') (h2' : IsTri l₁ j₂ l₃') :
    ∑ᶠ k : ℕ, (2 * (((j₁ + j₂ - k : ℚ)) : ℝ) + 1) * (2 * (l₃ : ℝ) + 1) *
        sixJ j₁ j₂ (j₁ + j₂ - k) l₁ l₂ l₃ * sixJ j₁ j₂ (j₁ + j₂ - k) l₁ l₂ l₃' =
      if l₃ = l₃' then 1 else 0 := by
  have hOA : ∑ᶠ k : ℕ, (2 * (((j₁ + j₂ - k : ℚ)) : ℝ) + 1) * (2 * (l₃ : ℝ) + 1) *
        sixJ j₁ j₂ (j₁ + j₂ - k) l₁ l₂ l₃ * sixJ j₁ j₂ (j₁ + j₂ - k) l₁ l₂ l₃' =
      (2 * (l₃ : ℝ) + 1) * OA j₂ j₁ l₂ l₁ l₃ l₃' := by
    have hz : ∀ x : ℚ, x < 0 → (2 * (x : ℝ) + 1) *
        (sixJ x j₂ j₁ l₃ l₂ l₁ * sixJ x j₂ j₁ l₃' l₂ l₁) = 0 := by
      intro x hx; rw [sixJ_neg_x l₃ hx]; ring
    unfold OA
    rw [← lsum_smul hz]
    unfold lsum
    refine finsum_congr fun k => ?_
    rw [show j₂ + j₁ - (k : ℚ) = j₁ + j₂ - k by ring, ← sixJ_swap13 j₁ j₂ (j₁ + j₂ - k) l₁ l₂ l₃,
      ← sixJ_swap13 j₁ j₂ (j₁ + j₂ - k) l₁ l₂ l₃']
    ring
  rw [hOA]
  have hadm : OAdm j₂ j₁ l₂ l₁ l₃ := ⟨h2.perm13, h1.perm13⟩
  split_ifs with he
  · subst he
    exact orth_norm j₂ j₁ l₂ l₁ l₃ hadm
  · have hne : (l₃ : ℝ) * (l₃ + 1) ≠ l₃' * (l₃' + 1) := by
      intro h
      have n1 : (0 : ℝ) ≤ l₃ := by exact_mod_cast h2.perm13.nonneg_first
      have n2 : (0 : ℝ) ≤ l₃' := by exact_mod_cast h2'.perm13.nonneg_first
      have : (l₃ : ℝ) = l₃' := by nlinarith
      exact he (by exact_mod_cast this)
    have h0 : OA j₂ j₁ l₂ l₁ l₃ l₃' = 0 := sixJ_orth_offdiag j₂ j₁ l₂ l₁ l₃ l₃' hne
    rw [h0]; ring

/-- info: 'FormalResearch.Wigner.sixJ_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_orthogonality

/-- info: 'FormalResearch.Wigner.orth_norm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms orth_norm

end FormalResearch.Wigner

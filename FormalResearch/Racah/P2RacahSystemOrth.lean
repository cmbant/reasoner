module

public import FormalResearch.Racah.P2RacahSystemLattice
public import FormalResearch.Wigner.OrthogMain

/-!
# Discrete orthogonality of the normalised `6j` kernels on the physical `c`-lattice
(Weyl P2, `eq:RacahPhiOrthogonality` of `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, proof of `thm:6jfiniteRacah`: "DLMF 34.5.14, used
with `j_3 = c` and `l_3 = f`, gives `eq:RacahPhiOrthogonality` after inserting the normalisation
`eq:6jPhi`."

With `W_f(c) = {a b c; b+m a+n f}` (`W6 a b c f m n`), DLMF 34.5.14 (`sixJ_orthogonality`, `j₁ = a`,
`j₂ = b`, `l₁ = b+m`, `l₂ = a+n`, `l₃ = f`) is
`∑_c (2c+1)(2f+1) W_f(c) W_g(c) = δ_{fg}`.

## Results

* `sixJ_orth_physical`: the same sum written over the physical lattice `physC a b m n`.
* `weight_Phi_mul`: `ω_c Φ_f(c) Φ_g(c) = 2 (-1)^(f-g) (2c+1) W_f(c) W_g(c)` for physical `f, g`
  (the `c`-dependent phases `(-1)^ξ` cancel in the product).
* `Phi6_orthogonality`: **`eq:RacahPhiOrthogonality`**,
  `∑_{c ∈ 𝒞} ω_c Φ_f(c) Φ_g(c) = 2/(2f+1) δ_{fg}` for `f, g` in the physical `f`-range,
  `𝒞 = physC a b m n`, `ω_c = (2c+1)/(2AB)`, `A = wA a n`, `B = wB b m`.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

lemma isTri_cyc {x y z : ℚ} (h : IsTri x y z) : IsTri z x y := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · convert h2 using 1; ring
  · convert h3 using 1; ring
  · convert h1 using 1; ring

lemma isTri_cyc' {x y z : ℚ} (h : IsTri z x y) : IsTri x y z := isTri_cyc (isTri_cyc h)

/-- `Φ` and `W` vanish off the physical `c`-lattice. -/
lemma W6_eq_zero_of_not_physC {a b m n c : ℚ} (f : ℚ) (h : c ∉ physC a b m n) :
    W6 a b c f m n = 0 := by
  unfold W6
  by_cases h1 : IsTri c a b
  · have h2 : ¬ IsTri c (b + m) (a + n) := fun h2 => h ⟨h1, h2⟩
    exact sixJ_eq_zero_of_not_tri3 (fun h3 => h2 (isTri_cyc h3))
  · exact sixJ_eq_zero_of_not_tri12 (fun h' => h1 (isTri_cyc h'.1))

lemma Phi6_eq_zero_of_not_physC {a b m n c : ℚ} (f : ℚ) (h : c ∉ physC a b m n) :
    Phi6 a b c f m n = 0 := by
  unfold Phi6
  rw [W6_eq_zero_of_not_physC f h]; ring

lemma isTri_int_sum {c a b f n : ℚ} (h1 : IsTri c a b) (h3 : IsTri f a (a + n)) :
    ∃ z : ℤ, a + b + c + f + n = z := by
  obtain ⟨⟨N1, hN1⟩, ⟨N2, hN2⟩, ⟨N3, hN3⟩⟩ := h1
  obtain ⟨-, ⟨N4, hN4⟩, -⟩ := h3
  exact ⟨N1 + N2 + N3 + N4, by push_cast; linarith⟩

lemma sgn_xi_mul {a b c f g n : ℚ} (h1 : IsTri c a b) (hg : IsTri g a (a + n)) (k : ℤ)
    (hk : f - g = k) :
    sgn (a + b + c + f + n) * sgn (a + b + c + g + n) = (-1 : ℝ) ^ k := by
  rw [show a + b + c + f + n = (a + b + c + g + n) + k by linarith, sgn_add_int,
    mul_assoc, sgn_mul_self_of_int (isTri_int_sum h1 hg), mul_one]

lemma physF_diff_int {a b m n f g : ℚ} (hf : f ∈ physF a b m n) (hg : g ∈ physF a b m n) :
    ∃ k : ℤ, f - g = k := by
  obtain ⟨⟨-, ⟨N1, hN1⟩, -⟩, -⟩ := hf
  obtain ⟨⟨-, ⟨N2, hN2⟩, -⟩, -⟩ := hg
  exact ⟨N1 - N2, by push_cast; linarith⟩

/-- The `c`-dependent phases cancel: `ω_c Φ_f(c) Φ_g(c) = 2 (-1)^k (2c+1) W_f(c) W_g(c)`,
`k = f - g`. -/
theorem weight_Phi_mul {a b m n f g : ℚ} (hf : f ∈ physF a b m n) (hg : g ∈ physF a b m n)
    (k : ℤ) (hk : f - g = k) (c : ℚ) :
    omegaW (wA a n) (wB b m) c * (Phi6 a b c f m n * Phi6 a b c g m n) =
      2 * (-1 : ℝ) ^ k * ((2 * (c : ℝ) + 1) * W6 a b c f m n * W6 a b c g m n) := by
  by_cases hc : c ∈ physC a b m n
  · obtain ⟨hA, hB, -⟩ := admissible_facts hf.1 hf.2
    have hs := sgn_xi_mul hc.1 hg.2 k hk
    have hP : 0 < wA a n * wB b m := mul_pos hA hB
    have hT : (2 * Real.sqrt (wA a n * wB b m)) * (2 * Real.sqrt (wA a n * wB b m)) =
        4 * (wA a n * wB b m) := by
      have := Real.mul_self_sqrt hP.le
      nlinarith
    unfold omegaW Phi6
    have e : (2 * (c : ℝ) + 1) / (2 * wA a n * wB b m) *
        ((sgn (a + b + c + f + n) * (2 * Real.sqrt (wA a n * wB b m)) * W6 a b c f m n) *
          (sgn (a + b + c + g + n) * (2 * Real.sqrt (wA a n * wB b m)) * W6 a b c g m n)) =
        (2 * c + 1) / (2 * wA a n * wB b m) *
          (sgn (a + b + c + f + n) * sgn (a + b + c + g + n)) *
          ((2 * Real.sqrt (wA a n * wB b m)) * (2 * Real.sqrt (wA a n * wB b m))) *
          (W6 a b c f m n * W6 a b c g m n) := by ring
    rw [e, hs, hT]
    have : wA a n * wB b m ≠ 0 := hP.ne'
    field_simp
    ring
  · rw [Phi6_eq_zero_of_not_physC f hc, W6_eq_zero_of_not_physC f hc]
    ring

lemma finsum_mem_eq_of_support {α : Type*} {s t : Set α} (H : α → ℝ)
    (h : ∀ x, H x ≠ 0 → (x ∈ s ↔ x ∈ t)) : ∑ᶠ x ∈ s, H x = ∑ᶠ x ∈ t, H x :=
  finsum_mem_inter_support_eq' H s t h

/-- **DLMF 34.5.14 on the physical lattice**:
`∑_{c ∈ 𝒞} (2c+1)(2f+1) W_f(c) W_g(c) = δ_{fg}` for `f, g` in the physical `f`-range. -/
theorem sixJ_orth_physical {a b m n f g : ℚ} (hf : f ∈ physF a b m n) (hg : g ∈ physF a b m n) :
    ∑ᶠ c ∈ physC a b m n,
        (2 * (c : ℝ) + 1) * (2 * (f : ℝ) + 1) * W6 a b c f m n * W6 a b c g m n =
      if f = g then 1 else 0 := by
  have horth := sixJ_orthogonality a b (b + m) (a + n) f g (isTri_cyc' hf.2) (isTri_cyc' hf.1)
    (isTri_cyc' hg.2) (isTri_cyc' hg.1)
  set X : ℚ → ℝ := fun c =>
    (2 * (c : ℝ) + 1) * (2 * (f : ℝ) + 1) * W6 a b c f m n * W6 a b c g m n with hX
  have hinj : Function.Injective (fun k : ℕ => ((a + b : ℚ) - k)) := by
    intro i j hij
    have : (i : ℚ) = j := by simpa using hij
    exact_mod_cast this
  have hX0 : ∀ c, c ∉ physC a b m n → X c = 0 := by
    intro c hc
    simp only [hX, W6_eq_zero_of_not_physC f hc]; ring
  have hsub : physC a b m n ⊆ Set.range (fun k : ℕ => ((a + b : ℚ) - k)) := by
    intro c hc
    obtain ⟨N, hN⟩ := hc.1.2.2
    exact ⟨N, by simp only; linarith⟩
  have key : ∑ᶠ c ∈ physC a b m n, X c = ∑ᶠ k : ℕ, X ((a + b : ℚ) - k) := by
    rw [← finsum_mem_range hinj]
    apply finsum_mem_eq_of_support
    intro x hx
    have hxc : x ∈ physC a b m n := by
      by_contra h'; exact hx (hX0 x h')
    exact ⟨fun _ => hsub hxc, fun _ => hxc⟩
  rw [key]
  convert horth using 1
  apply finsum_congr
  intro k
  simp only [hX, W6]

/-- **`eq:RacahPhiOrthogonality`**:
`∑_{c ∈ 𝒞} ω_c Φ_f(c) Φ_g(c) = 2/(2f+1) δ_{fg}` for `f, g` in the physical `f`-range, where
`𝒞` is the physical `c`-lattice, `ω_c = (2c+1)/(2AB)`, `A = a+(n+1)/2`, `B = b+(m+1)/2`. -/
theorem Phi6_orthogonality {a b m n f g : ℚ} (hf : f ∈ physF a b m n) (hg : g ∈ physF a b m n) :
    ∑ᶠ c ∈ physC a b m n,
        omegaW (wA a n) (wB b m) c * (Phi6 a b c f m n * Phi6 a b c g m n) =
      if f = g then 2 / (2 * (f : ℝ) + 1) else 0 := by
  obtain ⟨k, hk⟩ := physF_diff_int hf hg
  obtain ⟨-, -, -, -, hf0⟩ := admissible_facts hf.1 hf.2
  have hf1 : (2 * (f : ℝ) + 1) ≠ 0 := by positivity
  have hpt : ∀ c : ℚ, omegaW (wA a n) (wB b m) c * (Phi6 a b c f m n * Phi6 a b c g m n) =
      (2 * (-1 : ℝ) ^ k / (2 * (f : ℝ) + 1)) *
        ((2 * (c : ℝ) + 1) * (2 * (f : ℝ) + 1) * W6 a b c f m n * W6 a b c g m n) := by
    intro c
    rw [weight_Phi_mul hf hg k hk c]
    field_simp
  rw [finsum_mem_congr rfl (fun c _ => hpt c), ← mul_finsum_mem, sixJ_orth_physical hf hg]
  by_cases hfg : f = g
  · have : k = 0 := by
      have : ((k : ℤ) : ℚ) = 0 := by rw [← hk, hfg, sub_self]
      exact_mod_cast this
    subst this
    simp [hfg]
  · simp [hfg]

/-- info: 'FormalResearch.Racah.SixJ.sixJ_orth_physical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sixJ_orth_physical

/-- info: 'FormalResearch.Racah.SixJ.Phi6_orthogonality' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Phi6_orthogonality

end FormalResearch.Racah.SixJ

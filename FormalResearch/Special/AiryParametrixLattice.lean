module

public import FormalResearch.Special.AiryParametrixDefect
public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# The Airy parametrix defect on a lattice (corollaries of `airyParametrix_defect`)

Two corollaries of the window-form defect lemma `airyParametrix_defect`
(`AiryParametrixDefect`), for the consumer (M5/M6):

* `airyParametrix_defect_bounded`: on `|X| ≤ R`, `X = h^{-2/3} ζ(q)`, the defect is `≤ K_R h² airyWt X`
  (stage (ii) of the plan: the `h²` defect, which contains the `h^{5/3}` stage (i) since `h² ≤ h^{5/3}`
  for `h ≤ 1`);
* `airyParametrix_defect_lattice`: for a lattice `q_k = q₀ + k h` and sequences with
  `a (k+1) = A(q_k + h/2)`, `a k = A(q_k - h/2)`, `c k = 2 A(q_k) Ch(ζ ζ'²)(q_k)`,
  `ψ k = g(q_k) Ai(h^{-2/3} ζ(q_k))`, the discrete Jacobi operator `FormalResearch.DiscreteAiry.jac a c ψ k` of
  `DiscreteJacobiCalculus` is the defect, so `|FormalResearch.DiscreteAiry.jac a c ψ k| ≤ K h² (1+|X_k|)³ airyWt X_k` whenever `q_k ∈ J`.

Proved.  Not formalised here: the uniform `O(h²) ψ` bound on the whole turn neighbourhood
(`AiryParametrixUniformLattice`: `airyParametrix_defect_uniform_lattice`, `airyParametrix_defect_uniform_rel`) and the
construction of `(ζ, g)` from `(a, c)` (`AiryParametrixLanger`: `langer_hrel` gives `ζ, g` from the data `u, A`, with
`c = 2 A u`; the identification `E - b = 2 a u` for a concrete chain remains the caller's input).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **Defect on a bounded window `|X| ≤ R`:** `≤ K_R h² airyWt X`. -/
theorem airyParametrix_defect_bounded {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    {R : ℝ} :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ q ∈ J,
      |h ^ (-(2 / 3 : ℝ)) * ζ q| ≤ R →
      |A (q + h / 2) * (g (q + h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q + h))) +
          A (q - h / 2) * (g (q - h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q - h))) -
          2 * A q * langerCosh (ζ q * deriv ζ q ^ 2) * (g q * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ q))| ≤
        K * (1 + R) ^ 3 * h ^ 2 * airyWt (h ^ (-(2 / 3 : ℝ)) * ζ q) := by
  obtain ⟨K, h0, hK, hh0, H⟩ := airyParametrix_defect hU hJ hJU hζ hA hg hrel
  refine ⟨K, h0, hK, hh0, fun h hh hh' q hq hX => ?_⟩
  refine (H h hh hh' q hq).trans ?_
  have hw := airyWt_pos (h ^ (-(2 / 3 : ℝ)) * ζ q)
  have h1 : (1 + |h ^ (-(2 / 3 : ℝ)) * ζ q|) ^ 3 ≤ (1 + R) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have : K * h ^ 2 * (1 + |h ^ (-(2 / 3 : ℝ)) * ζ q|) ^ 3 ≤ K * h ^ 2 * (1 + R) ^ 3 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc K * h ^ 2 * (1 + |h ^ (-(2 / 3 : ℝ)) * ζ q|) ^ 3 * airyWt (h ^ (-(2 / 3 : ℝ)) * ζ q)
      ≤ K * h ^ 2 * (1 + R) ^ 3 * airyWt (h ^ (-(2 / 3 : ℝ)) * ζ q) :=
        mul_le_mul_of_nonneg_right this hw.le
    _ = _ := by ring

/-- **The defect on a lattice.**  With `q_k = q₀ + k h`, coefficients `a (k+1) = A(q_k + h/2)`,
`a k = A(q_k - h/2)`, diagonal `c k = 2 A(q_k) Ch(ζ ζ'²)(q_k)` and `ψ k = g(q_k) Ai(h^{-2/3} ζ(q_k))`, the
Jacobi row `FormalResearch.DiscreteAiry.jac a c ψ k` is `O(h²)(1+|X_k|)³ airyWt(X_k)` at every lattice point `q_k ∈ J`, `X_k = h^{-2/3}ζ(q_k)`.
The constants are those of `airyParametrix_defect`, independent of `q₀`, `k`. -/
theorem airyParametrix_defect_lattice {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ (h q₀ : ℝ) (a c ψ : ℤ → ℝ), 0 < h → h ≤ h0 →
      (∀ k : ℤ, a k = A (q₀ + k * h - h / 2)) →
      (∀ k : ℤ, c k = 2 * A (q₀ + k * h) * langerCosh (ζ (q₀ + k * h) * deriv ζ (q₀ + k * h) ^ 2)) →
      (∀ k : ℤ, ψ k = g (q₀ + k * h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h))) →
      ∀ k : ℤ, q₀ + k * h ∈ J →
        |FormalResearch.DiscreteAiry.jac a c ψ k| ≤ K * h ^ 2 * (1 + |h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h)|) ^ 3 *
          airyWt (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h)) := by
  obtain ⟨K, h0, hK, hh0, H⟩ := airyParametrix_defect hU hJ hJU hζ hA hg hrel
  refine ⟨K, h0, hK, hh0, fun h q₀ a c ψ hh hh' ha hc hψ k hk => ?_⟩
  have := H h hh hh' (q₀ + k * h) hk
  have q1 : q₀ + ((k + 1 : ℤ) : ℝ) * h = q₀ + k * h + h := by push_cast; ring
  have q2 : q₀ + ((k - 1 : ℤ) : ℝ) * h = q₀ + k * h - h := by push_cast; ring
  have e1 : a (k + 1) = A (q₀ + k * h + h / 2) := by
    rw [ha]; congr 1; push_cast; ring
  have e2 : a k = A (q₀ + k * h - h / 2) := ha k
  have e3 : ψ (k + 1) = g (q₀ + k * h + h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h + h)) := by
    rw [hψ, q1]
  have e4 : ψ (k - 1) = g (q₀ + k * h - h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h - h)) := by
    rw [hψ, q2]
  unfold FormalResearch.DiscreteAiry.jac
  rw [e1, e2, e3, e4, hc, hψ]
  convert this using 2


/-- info: 'FormalResearch.Special.airyParametrix_defect_bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_bounded

/-- info: 'FormalResearch.Special.airyParametrix_defect_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_lattice

end FormalResearch.Special

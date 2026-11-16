module

public import FormalResearch.Special.AiryParametrixUniformDefect
public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# The uniform Airy parametrix defect on a lattice (corollaries of `airyParametrix_defect_uniform`)

Corollaries of the uniform defect lemma `airyParametrix_defect_uniform` (`AiryParametrixUniformDefect`) for the
consumers (M5/M6), with the *same* hypotheses as `airyParametrix_defect_lattice` but the weight
`h² airyWt(X_k)` in place of `h² (1+|X_k|)³ airyWt(X_k)`:

* `airyParametrix_defect_uniform_lattice`: lattice `q_k = q₀ + k h`, `a (k+1) = A(q_k + h/2)`,
  `a k = A(q_k - h/2)`, `c k = 2 A(q_k) Ch(ζζ'²)(q_k)`, `ψ k = g(q_k) Ai(h^{-2/3} ζ(q_k))`:
  `|jac a c ψ k| ≤ K h² airyWt(X_k)` whenever `q_k ∈ J` (all `X_k`, the oscillatory side included);
* `airyParametrix_defect_uniform_rel`: the relative form `|jac a c ψ k| ≤ K' h² |ψ k|` when moreover
  `X_k ≥ -1` (`Ai ≥ airyWt/20` there, and `g² ≥ 1/(1 + sup|A ζ' Sh|)` from the amplitude relation).

Proved.  On the oscillatory side `X < -1` `ψ` has zeros, so only the weight form is stated there.

Not formalised: explicit constants (`K`, `h₀` are existential, as in `airyParametrix_defect_lattice`), the amplitude
relation `hrel` is a hypothesis here (`langer_hrel` in `AiryParametrixLanger` supplies it for M3's `g`), and a relative form on `X_k < -1` (impossible: `ψ` has zeros).
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- **Uniform defect on a lattice**: `|jac a c ψ k| ≤ K h² airyWt(X_k)`. -/
theorem airyParametrix_defect_uniform_lattice {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ (h q₀ : ℝ) (a c ψ : ℤ → ℝ), 0 < h → h ≤ h0 →
      (∀ k : ℤ, a k = A (q₀ + k * h - h / 2)) →
      (∀ k : ℤ, c k = 2 * A (q₀ + k * h) * langerCosh (ζ (q₀ + k * h) * deriv ζ (q₀ + k * h) ^ 2)) →
      (∀ k : ℤ, ψ k = g (q₀ + k * h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h))) →
      ∀ k : ℤ, q₀ + k * h ∈ J →
        |FormalResearch.DiscreteAiry.jac a c ψ k| ≤
          K * h ^ 2 * airyWt (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h)) := by
  obtain ⟨K, h0, hK, hh0, H⟩ := airyParametrix_defect_uniform hU hJ hJU hζ hA hg hrel
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

/-- **Relative uniform defect**: on `X_k ≥ -1` (where `ψ ≍ airyWt`), `|jac a c ψ k| ≤ K h² |ψ k|`. -/
theorem airyParametrix_defect_uniform_rel {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ (h q₀ : ℝ) (a c ψ : ℤ → ℝ), 0 < h → h ≤ h0 →
      (∀ k : ℤ, a k = A (q₀ + k * h - h / 2)) →
      (∀ k : ℤ, c k = 2 * A (q₀ + k * h) * langerCosh (ζ (q₀ + k * h) * deriv ζ (q₀ + k * h) ^ 2)) →
      (∀ k : ℤ, ψ k = g (q₀ + k * h) * airyAi (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h))) →
      ∀ k : ℤ, q₀ + k * h ∈ J → -1 ≤ h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h) →
        |FormalResearch.DiscreteAiry.jac a c ψ k| ≤ K * h ^ 2 * |ψ k| := by
  obtain ⟨K0, h0, hK0, hh0, H⟩ := airyParametrix_defect_uniform_lattice hU hJ hJU hζ hA hg hrel
  obtain ⟨Z0, Z1, Z2, Z3, δζ, hZ0, hZ1, hZ2, hZ3, hδζ, hζj⟩ := apx_jet3 hU hζ hJ hJU
  obtain ⟨A0, A1, A2, δA, hA0, hA1, hA2, hδA, hAj⟩ := apx_jet2 hU hA hJ hJU
  obtain ⟨Mc, hMc0, hMc⟩ := apuc_bound (Z0 * Z1 ^ 2)
  set P : ℝ := A0 * Z1 * (2 * Mc) + 1 with hP
  have hP1 : 1 ≤ P := by rw [hP]; have : 0 ≤ A0 * Z1 * (2 * Mc) := by positivity
                         linarith
  refine ⟨20 * K0 * (1 + P), h0, by positivity, hh0, fun h q₀ a c ψ hh hh' ha hc hψ k hk hX => ?_⟩
  have hjac := H h q₀ a c ψ hh hh' ha hc hψ k hk
  set q : ℝ := q₀ + k * h with hq
  set X : ℝ := h ^ (-(2 / 3 : ℝ)) * ζ q with hXdef
  have hAi : airyWt X / 20 ≤ airyAi X := airyWt_div_twenty_le_airyAi hX
  have hw := airyWt_pos X
  have hAi0 : 0 < airyAi X := by linarith
  -- lower bound for `|g|` from the amplitude relation
  obtain ⟨hζ0, hζ1, -, -⟩ := hζj q hk
  obtain ⟨hA0q, -, -⟩ := hAj q hk
  have hF : |ζ q * deriv ζ q ^ 2| ≤ Z0 * Z1 ^ 2 := by
    rw [abs_mul, abs_pow]
    exact mul_le_mul hζ0 (pow_le_pow_left₀ (abs_nonneg _) hζ1 2) (by positivity) hZ0
  have hSh : |2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)| ≤ 2 * Mc := by
    have := (hMc _ hF).2.1
    rw [abs_mul, abs_two]
    have : |deriv langerCosh (ζ q * deriv ζ q ^ 2)| ≤ Mc := this
    linarith
  have hprod : |A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2))| ≤ A0 * Z1 * (2 * Mc) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul hA0q hζ1 (abs_nonneg _) hA0) hSh (abs_nonneg _) (by positivity)
  have hr := hrel q (hJU hk)
  have hg2 : 1 ≤ g q ^ 2 * P := by
    have e : g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) =
        g q ^ 2 * (A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2))) := by ring
    rw [e] at hr
    have h1 : g q ^ 2 * (A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2))) ≤
        g q ^ 2 * P := by
      calc _ ≤ g q ^ 2 * |A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2))| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ g q ^ 2 * P := mul_le_mul_of_nonneg_left (hprod.trans (by rw [hP]; linarith)) (sq_nonneg _)
    linarith
  have hu : 1 ≤ |g q| * (1 + P) := by
    by_contra hcon
    rw [not_le] at hcon
    have hu0 := abs_nonneg (g q)
    have hsq : g q ^ 2 = |g q| ^ 2 := (sq_abs _).symm
    rw [hsq] at hg2
    nlinarith [mul_nonneg hu0 hu0]
  -- assemble
  have hψk : |ψ k| = |g q| * airyAi X := by
    rw [hψ, abs_mul, abs_of_pos hAi0]
  rw [hψk]
  have hle : airyAi X ≤ |g q| * (1 + P) * airyAi X := le_mul_of_one_le_left hAi0.le hu
  calc |FormalResearch.DiscreteAiry.jac a c ψ k| ≤ K0 * h ^ 2 * airyWt X := hjac
    _ ≤ K0 * h ^ 2 * (20 * airyAi X) := by gcongr; linarith
    _ ≤ K0 * h ^ 2 * (20 * (|g q| * (1 + P) * airyAi X)) := by gcongr
    _ = 20 * K0 * (1 + P) * h ^ 2 * (|g q| * airyAi X) := by ring

/-- info: 'FormalResearch.Special.airyParametrix_defect_uniform_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_uniform_lattice

/-- info: 'FormalResearch.Special.airyParametrix_defect_uniform_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyParametrix_defect_uniform_rel

end FormalResearch.Special

module

public import FormalResearch.Special.AiryParametrixTaylor
public import FormalResearch.Special.AiryParametrixSkeleton

/-!
# Parametrix defect, part 6: jets of the coefficient functions on a compact set

For `f ∈ C^n(U)` (`U` open) and a compact `J ⊆ U` there are uniform bounds of `f, f', ..., f^{(n)}` on `J` and
a uniform Taylor remainder for increments `|s| ≤ δ` (`δ` with `cthickening δ J ⊆ U`):
`apx_jet2` (`n = 2`: `|f(q+s) - f(q) - f'(q) s| ≤ M₂ s²`) and `apx_jet3` (`n = 3`:
`|f(q+s) - f(q) - f'(q) s - f''(q) s²/2| ≤ M₃ |s|³`), with the derivatives written as `deriv f`,
`deriv (deriv f)`.  Also the differentiated relation `apx_transport` (the `q`-derivative of
`g² A ζ' Sh(ζ ζ'²) = 1`).  Proved; existential constants.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- Taylor remainders for increments of either sign, uniformly for `q` in a compact `J`. -/
lemma apx_taylor_J {f : ℝ → ℝ} {U J : Set ℝ} {n : ℕ} {δ : ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hJ : IsCompact J) (hδ : Metric.cthickening δ J ⊆ U) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ q ∈ J, ∀ s : ℝ, |s| ≤ δ →
      |f (q + s) - ∑ k ∈ Finset.range n, deriv^[k] f q * s ^ k / (k.factorial : ℝ)| ≤ B * |s| ^ n := by
  obtain ⟨B, hB0, hB⟩ := apx_taylor_local hU hf hJ.cthickening hδ
  refine ⟨B, hB0, fun q hq s hs => hB q s (fun t ht => ?_)⟩
  apply Metric.mem_cthickening_of_dist_le (q + t) q δ J hq
  rw [dist_eq_norm, add_sub_cancel_left, Real.norm_eq_abs]
  have : |t| ≤ |s| := by
    rcases le_total 0 s with h0 | h0
    · rw [uIcc_of_le h0] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg h0]; exact ht.2
    · rw [uIcc_of_ge h0] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos h0]; linarith [ht.1]
  linarith

/-- **Second-order jet** of a `C²` function on a compact `J ⊆ U`. -/
theorem apx_jet2 {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ M0 M1 M2 δ : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧ 0 < δ ∧ ∀ q ∈ J, |f q| ≤ M0 ∧ |deriv f q| ≤ M1 ∧
      ∀ s : ℝ, |s| ≤ δ → |f (q + s) - (f q + deriv f q * s)| ≤ M2 * s ^ 2 := by
  obtain ⟨δ, hδ, hcth⟩ := hJ.exists_cthickening_subset_open hU hJU
  obtain ⟨B, hB0, hB⟩ := apx_taylor_J (n := 2) hU hf hJ hcth
  obtain ⟨M0, hM0, h0⟩ := apx_bound_iterate hU hf hJ hJU 0 (by norm_num)
  obtain ⟨M1, hM1, h1⟩ := apx_bound_iterate hU hf hJ hJU 1 (by norm_num)
  refine ⟨M0, M1, B, δ, hM0, hM1, hB0, hδ, fun q hq => ⟨by simpa using h0 q hq, by simpa using h1 q hq,
    fun s hs => ?_⟩⟩
  have := hB q hq s hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero, id_eq,
    Function.iterate_one, Nat.factorial, pow_zero, pow_one] at this
  rw [sq_abs] at this
  convert this using 3; norm_num

/-- **Third-order jet** of a `C³` function on a compact `J ⊆ U`. -/
theorem apx_jet3 {f : ℝ → ℝ} {U J : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (hJ : IsCompact J) (hJU : J ⊆ U) :
    ∃ M0 M1 M2 M3 δ : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ 0 ≤ M2 ∧ 0 ≤ M3 ∧ 0 < δ ∧ ∀ q ∈ J, |f q| ≤ M0 ∧
      |deriv f q| ≤ M1 ∧ |deriv (deriv f) q| ≤ M2 ∧
      ∀ s : ℝ, |s| ≤ δ → |f (q + s) - (f q + deriv f q * s + deriv (deriv f) q * s ^ 2 / 2)| ≤
        M3 * |s| ^ 3 := by
  obtain ⟨δ, hδ, hcth⟩ := hJ.exists_cthickening_subset_open hU hJU
  obtain ⟨B, hB0, hB⟩ := apx_taylor_J (n := 3) hU hf hJ hcth
  obtain ⟨M0, hM0, h0⟩ := apx_bound_iterate hU hf hJ hJU 0 (by norm_num)
  obtain ⟨M1, hM1, h1⟩ := apx_bound_iterate hU hf hJ hJU 1 (by norm_num)
  obtain ⟨M2, hM2, h2⟩ := apx_bound_iterate hU hf hJ hJU 2 (by norm_num)
  have it2 : ∀ x, deriv^[2] f x = deriv (deriv f) x := by
    intro x; simp [Function.iterate_succ_apply']
  refine ⟨M0, M1, M2, B, δ, hM0, hM1, hM2, hB0, hδ, fun q hq => ⟨by simpa using h0 q hq,
    by simpa using h1 q hq, by simpa [it2] using h2 q hq, fun s hs => ?_⟩⟩
  have := hB q hq s hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Function.iterate_zero, id_eq,
    Function.iterate_one, it2, Nat.factorial, pow_zero, pow_one] at this
  convert this using 3; norm_num

/-- **Transport identity.**  If `g² A ζ' Sh(ζ ζ'²) ≡ 1` on the open set `U`, `Sh = 2 Ch'`, then at every
`q ∈ U`, with `G₀ = A g`, `G₁ = A' g/2 + A g'`, `ζ₁ = ζ'`, `ζ₂ = ζ''`, `F = ζ ζ₁²`:
`2 G₁ ζ₁ Sh(F) + G₀ ζ₂ (Sh(F) + 2F Sh'(F)) + G₀ ζ₁⁴ Sh'(F) = 0` (the `q`-derivative of the relation, divided
by `g`; `Sh' = 2 Ch''`). -/
theorem apx_transport {ζ A g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hζ : ContDiffOn ℝ 3 ζ U)
    (hA : ContDiffOn ℝ 2 A U) (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1)
    {q : ℝ} (hq : q ∈ U) :
    2 * (deriv A q * g q / 2 + A q * deriv g q) * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) +
      (A q * g q) * deriv (deriv ζ) q *
        (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2) +
          2 * (ζ q * deriv ζ q ^ 2) * (2 * deriv (deriv langerCosh) (ζ q * deriv ζ q ^ 2))) +
      (A q * g q) * deriv ζ q ^ 4 * (2 * deriv (deriv langerCosh) (ζ q * deriv ζ q ^ 2)) = 0 := by
  have hz0 : HasDerivAt ζ (deriv ζ q) q := by
    have := apx_hasDerivAt_iterate hU hζ 0 (by norm_num) q hq
    simpa using this
  have hz1 : HasDerivAt (deriv ζ) (deriv (deriv ζ) q) q := by
    have := apx_hasDerivAt_iterate hU hζ 1 (by norm_num) q hq
    simpa [Function.iterate_succ_apply'] using this
  have hA0 : HasDerivAt A (deriv A q) q := by
    have := apx_hasDerivAt_iterate hU hA 0 (by norm_num) q hq
    simpa using this
  have hg0 : HasDerivAt g (deriv g q) q := by
    have := apx_hasDerivAt_iterate hU hg 0 (by norm_num) q hq
    simpa using this
  have hF : HasDerivAt (fun x => ζ x * deriv ζ x ^ 2)
      (deriv ζ q * deriv ζ q ^ 2 + ζ q * (2 * deriv ζ q * deriv (deriv ζ) q)) q := by
    have := hz0.mul (hz1.pow 2)
    convert this using 1
    simp
  have hSh : HasDerivAt (fun x => 2 * deriv langerCosh (ζ x * deriv ζ x ^ 2))
      (2 * (deriv (deriv langerCosh) (ζ q * deriv ζ q ^ 2) *
        (deriv ζ q * deriv ζ q ^ 2 + ζ q * (2 * deriv ζ q * deriv (deriv ζ) q)))) q := by
    have := ((hasDerivAt_langerCosh' (ζ q * deriv ζ q ^ 2)).comp q hF).const_mul 2
    simpa using this
  have hΛ := ((((hg0.pow 2).mul hA0).mul hz1).mul hSh)
  have hΛ' : HasDerivAt (fun x => g x ^ 2 * A x * deriv ζ x * (2 * deriv langerCosh (ζ x * deriv ζ x ^ 2)))
      0 q := by
    have hev : (fun x => g x ^ 2 * A x * deriv ζ x * (2 * deriv langerCosh (ζ x * deriv ζ x ^ 2)))
        =ᶠ[nhds q] fun _ => (1 : ℝ) :=
      Filter.eventuallyEq_of_mem (hU.mem_nhds hq) (fun x hx => hrel x hx)
    exact (hasDerivAt_const q (1 : ℝ)).congr_of_eventuallyEq hev
  have hzero := hΛ.unique hΛ'
  have hgq : g q ≠ 0 := by
    intro h0
    have := hrel q hq
    rw [h0] at this; simp at this
  have : g q * (2 * (deriv A q * g q / 2 + A q * deriv g q) * deriv ζ q *
        (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) +
      (A q * g q) * deriv (deriv ζ) q *
        (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2) +
          2 * (ζ q * deriv ζ q ^ 2) * (2 * deriv (deriv langerCosh) (ζ q * deriv ζ q ^ 2))) +
      (A q * g q) * deriv ζ q ^ 4 * (2 * deriv (deriv langerCosh) (ζ q * deriv ζ q ^ 2))) = 0 := by
    simp only [Pi.mul_apply, Pi.pow_apply] at hzero
    linear_combination hzero
  exact (mul_eq_zero.1 this).resolve_left hgq

end FormalResearch.Special

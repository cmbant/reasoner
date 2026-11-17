module

public import FormalResearch.Special.AiryChebyshevApprox
public import FormalResearch.Special.AiryRankDecayTail

/-!
# The separated kernel `B_{R,m}(s, ζ) = Σ_{k<m} φ_k(s) ψ_k(ζ)` approximating `Ai(s + ζ)`

**Proved.**  For `R > 0` set

* `φ_k(s) = Re a_k(s)` on `|s| ≤ R` and `0` elsewhere (`airyRankPhi`; `a_k` the Chebyshev coefficients of
  `ζ ↦ Ai(s+ζ)` on `[0,R]`, `AiryChebyshevApprox`);
* `ψ_k(ζ) = T_k(2ζ/R - 1)` on `0 ≤ ζ ≤ R` and `0` elsewhere (`airyRankPsi`);
* `B_{R,m} = Σ_{k<m} φ_k ⊗ ψ_k` (`airyRankKer`), a kernel of rank `≤ m`.

Facts: all `φ_k`, `ψ_k` are measurable (`measurable_airyRankPhi`, `measurable_airyRankPsi`), bounded
(`abs_airyRankPhi_le`: `|φ_k| ≤ 2 M(R)`; `abs_airyRankPsi_le`: `|ψ_k| ≤ 1`) and vanish outside `[-R,R]`
(resp. `[0,R]`), hence lie in every `L^p`.  Off the box `{s ≤ R, ζ ≤ R}` the kernel vanishes
(`airyRankKer_eq_zero_of_*`), and on `{|s| ≤ R, 0 ≤ ζ ≤ R}` it approximates `Ai(s+ζ)` to `2M(R)/2^{m-1}`
(`abs_airy_sub_airyRankKer_le`).
-/

@[expose] public section

open Set Polynomial.Chebyshev

namespace FormalResearch.Special

/-- `φ_k(s)`: the Chebyshev coefficient of `Ai(s + ·)` on `[0,R]`, cut off to `|s| ≤ R`. -/
noncomputable def airyRankPhi (R : ℝ) (k : ℕ) (s : ℝ) : ℝ :=
  if s ∈ Icc (-R) R then airyChebCoeff R s k else 0

/-- `ψ_k(ζ) = T_k(2ζ/R - 1)` on `[0,R]`, zero elsewhere. -/
noncomputable def airyRankPsi (R : ℝ) (k : ℕ) (ζ : ℝ) : ℝ :=
  if ζ ∈ Icc 0 R then (T ℝ (k : ℤ)).eval (2 * ζ / R - 1) else 0

/-- The rank-`≤ m` separated kernel. -/
noncomputable def airyRankKer (R : ℝ) (m : ℕ) (s ζ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range m, airyRankPhi R k s * airyRankPsi R k ζ

lemma measurable_airyRankPhi (R : ℝ) (k : ℕ) : Measurable (airyRankPhi R k) :=
  Measurable.ite measurableSet_Icc (continuous_airyChebCoeff R k).measurable measurable_const

lemma measurable_airyRankPsi (R : ℝ) (k : ℕ) : Measurable (airyRankPsi R k) := by
  refine Measurable.ite measurableSet_Icc ?_ measurable_const
  exact ((Polynomial.continuous _).comp (by fun_prop)).measurable

lemma airyRankPhi_eq_zero {R s : ℝ} (k : ℕ) (hs : R < s) : airyRankPhi R k s = 0 := by
  unfold airyRankPhi
  split_ifs with h
  · linarith [h.2]
  · rfl

lemma airyRankPsi_eq_zero {R ζ : ℝ} (k : ℕ) (hζ : R < ζ) : airyRankPsi R k ζ = 0 := by
  unfold airyRankPsi
  split_ifs with h
  · linarith [h.2]
  · rfl

lemma airyRankKer_eq_zero_of_s {R s : ℝ} (m : ℕ) (ζ : ℝ) (hs : R < s) : airyRankKer R m s ζ = 0 := by
  unfold airyRankKer
  exact Finset.sum_eq_zero fun k _ => by rw [airyRankPhi_eq_zero k hs, zero_mul]

lemma airyRankKer_eq_zero_of_ζ {R ζ : ℝ} (m : ℕ) (s : ℝ) (hζ : R < ζ) : airyRankKer R m s ζ = 0 := by
  unfold airyRankKer
  exact Finset.sum_eq_zero fun k _ => by rw [airyRankPsi_eq_zero k hζ, mul_zero]

lemma abs_airyRankPsi_le (R : ℝ) (k : ℕ) (ζ : ℝ) (hR : 0 < R) : |airyRankPsi R k ζ| ≤ 1 := by
  unfold airyRankPsi
  split_ifs with h
  · refine abs_eval_T_real_le_one _ ?_
    rw [abs_le]; constructor
    · have : 0 ≤ 2 * ζ / R := by have := h.1; positivity
      linarith
    · have : 2 * ζ / R ≤ 2 := by rw [div_le_iff₀ hR]; linarith [h.2]
      linarith
  · simp

lemma abs_airyRankPhi_le {R : ℝ} (hR : 0 < R) (k : ℕ) (s : ℝ) :
    |airyRankPhi R k s| ≤ 2 * airyChebM R := by
  unfold airyRankPhi
  split_ifs with h
  · have hs : |s| ≤ R := abs_le.2 ⟨h.1, h.2⟩
    have h1 := (bernsteinHyp_airy hR hs).norm_chebCoeff_le k
    have h2 := Complex.abs_re_le_norm (FormalResearch.Chebyshev.chebCoeff (fun w =>
      airyShiftScale (s + R / 2) (R / 2) (FormalResearch.Chebyshev.joukowski w)) 2 k)
    unfold airyChebCoeff
    have hM : 0 ≤ airyChebM R := airyChebM_nonneg R
    have h3 : 2 * airyChebM R / 2 ^ k ≤ 2 * airyChebM R := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    linarith
  · simp only [abs_zero]; exact mul_nonneg (by norm_num) (airyChebM_nonneg R)

/-- On the box `|s| ≤ R`, `0 ≤ ζ ≤ R` the separated kernel approximates `Ai(s+ζ)`. -/
theorem abs_airy_sub_airyRankKer_le {R s ζ : ℝ} (hR : 0 < R) (hs : |s| ≤ R) (hζ0 : 0 ≤ ζ)
    (hζ : ζ ≤ R) (n : ℕ) :
    |airyAi (s + ζ) - airyRankKer R (n + 1) s ζ| ≤ 2 * airyChebM R / 2 ^ n := by
  have h := airy_cheb_pointwise hR hs hζ0 hζ n
  have e : airyRankKer R (n + 1) s ζ = ∑ k ∈ Finset.range (n + 1), airyChebCoeff R s k *
      (T ℝ (k : ℤ)).eval (2 * ζ / R - 1) := by
    unfold airyRankKer
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : s ∈ Icc (-R) R := ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
    have h2 : ζ ∈ Icc 0 R := ⟨hζ0, hζ⟩
    simp only [airyRankPhi, airyRankPsi, h1, h2, ite_true]
  rw [e]
  exact h

end FormalResearch.Special

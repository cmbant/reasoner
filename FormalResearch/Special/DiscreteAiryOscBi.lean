module

public import FormalResearch.Special.DiscreteAiryOscDefect
public import FormalResearch.Special.AiryBiEnvelope
public import FormalResearch.Special.AiryOlverBounds
public import FormalResearch.Special.AiryWt
public import FormalResearch.Special.AiryShift

/-!
# The growing Airy weight `airyBiWt` and the `Bi` parametrix defect

`airyBiWt X = (2+|X|)^{-1/4} exp(ξ(X))`, `ξ(X) = airyXi X = (2/3)(X₊)^{3/2}`, is the growing partner of
`airyWt X = (2+|X|)^{-1/4} exp(-ξ(X))`: `airyBiWt = airyWt · exp(2ξ)` and `airyWt · airyBiWt = (2+|X|)^{-1/2}`.
It is the weight of `Bi` on all of `ℝ` (the envelope `(2+|X|)^{-1/4}` on the oscillatory side, `e^{ξ}` growth beyond the turn).

* `airyBiWt_pos`, `airyBiWt_eq_mul`, `airyWt_mul_airyBiWt`;
* `apx_airyBi_global`: `|Bi x| ≤ 450 airyBiWt x`, `|Bi' x| ≤ 2385000 √(2+|x|) airyBiWt x` for all real `x` (Olver's `M E`,
  `N E` of `AiryOlver*` combined with `E² ≤ 320 e^{2ξ}`, `M² ≤ 600/√(2+|x|)`); `airyBi_ge_airyBiWt`: `Bi ≥ airyBiWt/800` on `x ≥ -1`;
* `airyBiWt_le_of_close`: local constancy of `airyBiWt` (`|ξ - X| ≤ 1`, `|ξ - X| √(1+|X|) ≤ Λ ⟹ airyBiWt ξ ≤ (6/5) e^Λ airyBiWt X`);
* `dao_bi_defect_lattice`: **the parametrix defect for `Bi`**: for `ψ_B(q) = g(q) Bi(h^{-2/3} ζ(q))` with the same data as the `Ai` lemma
  `airyParametrix_defect_uniform_lattice` (the amplitude relation `hrel`), `|jac a c ψ_B k| ≤ K h² airyBiWt(X_k)` for `q_k ∈ J`.

**Claim class: proved.**  The `Bi` defect is the answer to "is the machinery of the uniform defect `Ai`-specific?": it is not,
since the exact shift identity holds for every solution of `y'' = x y`; only the envelope input changes
(`DiscreteAiryOscDefect`).  Constants are those of the cited lemmas (existential for the defect), non-optimal.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- The growing Airy weight `(2+|X|)^{-1/4} exp(ξ(X))`. -/
noncomputable def airyBiWt (X : ℝ) : ℝ := (2 + |X|) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi X)

lemma airyBiWt_pos (X : ℝ) : 0 < airyBiWt X := by
  unfold airyBiWt
  have : 0 < 2 + |X| := by positivity
  positivity

lemma airyBiWt_eq_mul (X : ℝ) : airyBiWt X = airyWt X * Real.exp (2 * airyXi X) := by
  unfold airyBiWt airyWt
  have : Real.exp (2 * airyXi X) = Real.exp (airyXi X) * Real.exp (airyXi X) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-airyXi X) * Real.exp (airyXi X) = 1 := by rw [← Real.exp_add]; simp
  rw [this]
  calc (2 + |X|) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi X) =
      (2 + |X|) ^ (-(1 / 4) : ℝ) * (Real.exp (-airyXi X) * Real.exp (airyXi X)) * Real.exp (airyXi X) := by
        rw [h2]; ring
    _ = _ := by ring

/-- `airyWt · airyBiWt = 1/√(2+|X|)`. -/
lemma airyWt_mul_airyBiWt (X : ℝ) : airyWt X * airyBiWt X = (√(2 + |X|))⁻¹ := by
  have ht : 0 < 2 + |X| := by positivity
  rw [← rpow_neg_quarter_sq ht]
  unfold airyWt airyBiWt
  have h2 : Real.exp (-airyXi X) * Real.exp (airyXi X) = 1 := by rw [← Real.exp_add]; simp
  calc (2 + |X|) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi X) * ((2 + |X|) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi X))
      = ((2 + |X|) ^ (-(1 / 4) : ℝ)) ^ 2 * (Real.exp (-airyXi X) * Real.exp (airyXi X)) := by ring
    _ = _ := by rw [h2, mul_one]

lemma airyWt_le_airyBiWt (X : ℝ) : airyWt X ≤ airyBiWt X := by
  rw [airyBiWt_eq_mul]
  have h1 : 1 ≤ Real.exp (2 * airyXi X) := Real.one_le_exp (by linarith [airyXi_nonneg X])
  have := airyWt_pos X
  nlinarith

/-- **`Bi`, `Bi'` against `airyBiWt` on all of `ℝ`.** -/
theorem apx_airyBi_global (x : ℝ) :
    |airyBi x| ≤ 450 * airyBiWt x ∧ |airyBiDeriv x| ≤ 2385000 * √(2 + |x|) * airyBiWt x := by
  have ht : 0 < 2 + |x| := by positivity
  have hs : 0 < √(2 + |x|) := Real.sqrt_pos.mpr ht
  have hq : 0 < (2 + |x|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos ht _
  have hex : 0 < Real.exp (airyXi x) := Real.exp_pos _
  -- `M ≤ 25 (2+|x|)^{-1/4}`
  have hM0 := airyOlverM_nonneg x
  have hMsq := (airyOlverM_sq_two_sided x).2
  have hMw : airyOlverM x ≤ 25 * (2 + |x|) ^ (-(1 / 4) : ℝ) := by
    apply abs_le_of_sq_le_sq' (b := 25 * (2 + |x|) ^ (-(1 / 4) : ℝ)) _ (by positivity) |>.2
    rw [mul_pow, rpow_neg_quarter_sq ht]
    have : 1 / √(2 + |x|) = (√(2 + |x|))⁻¹ := one_div _
    rw [this] at hMsq
    nlinarith [inv_pos.2 hs]
  -- `E ≤ 18 e^{ξ}`
  have hE0 := airyOlverE_pos x
  have hEw : airyOlverE x ≤ 18 * Real.exp (airyXi x) := by
    by_cases hx : x ≤ airyCross
    · rw [airyOlverE_of_le hx]
      have : 1 ≤ Real.exp (airyXi x) := Real.one_le_exp (airyXi_nonneg x)
      linarith
    · rw [not_le] at hx
      have h := (airyOlverE_sq_two_sided hx).2
      apply abs_le_of_sq_le_sq' (b := 18 * Real.exp (airyXi x)) _ (by positivity) |>.2
      rw [mul_pow, ← Real.exp_nat_mul]
      have : Real.exp (2 * airyXi x) = Real.exp (((2 : ℕ) : ℝ) * airyXi x) := by norm_num
      rw [this] at h
      have hh : 0 < Real.exp (((2 : ℕ) : ℝ) * airyXi x) := Real.exp_pos _
      nlinarith
  have hBi := abs_airyBi_le_airyOlverM_mul_E x
  have hME : airyOlverM x * airyOlverE x ≤ 450 * airyBiWt x := by
    unfold airyBiWt
    calc airyOlverM x * airyOlverE x ≤ (25 * (2 + |x|) ^ (-(1 / 4) : ℝ)) * (18 * Real.exp (airyXi x)) :=
          mul_le_mul hMw hEw hE0.le (by positivity)
      _ = _ := by ring
  refine ⟨hBi.trans hME, ?_⟩
  have hB' := abs_airyBiDeriv_le_airyDerivWeightN_mul_E x
  have hN := airyDerivWeightN_le x
  have hN0 : 0 ≤ airyDerivWeightN x := by
    have h0 := (abs_nonneg _).trans (abs_airyAi'_le_airyDerivWeightN_div_E x)
    have hE := airyOlverE_pos x
    exact (div_nonneg_iff.1 h0).elim (fun h => h.1) (fun h => by linarith [h.2])
  calc |airyBiDeriv x| ≤ airyDerivWeightN x * airyOlverE x := hB'
    _ ≤ (5300 * √(2 + |x|) * airyOlverM x) * airyOlverE x := mul_le_mul_of_nonneg_right hN hE0.le
    _ = 5300 * √(2 + |x|) * (airyOlverM x * airyOlverE x) := by ring
    _ ≤ 5300 * √(2 + |x|) * (450 * airyBiWt x) := mul_le_mul_of_nonneg_left hME (by positivity)
    _ = 2385000 * √(2 + |x|) * airyBiWt x := by ring

/-- `Bi ≥ airyBiWt / 800` on `[-1, ∞)`. -/
theorem airyBi_ge_airyBiWt {x : ℝ} (hx : -1 ≤ x) : airyBiWt x / 800 ≤ airyBi x := by
  have h2 : 0 < 2 + x := by linarith
  have hle : 2 + x ≤ 2 + |x| := by linarith [le_abs_self x]
  have hr : (2 + |x|) ^ (-(1 / 4) : ℝ) ≤ (2 + x) ^ (-(1 / 4) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos h2 hle (by norm_num)
  refine le_trans ?_ (airyBi_envelope_real hx).1
  unfold airyBiWt
  have := Real.exp_pos (airyXi x)
  nlinarith

/-- **Local constancy of `airyBiWt`.** -/
theorem airyBiWt_le_of_close {X ξ Λ : ℝ} (h1 : |ξ - X| ≤ 1) (hΛ : |ξ - X| * √(1 + |X|) ≤ Λ) :
    airyBiWt ξ ≤ 6 / 5 * Real.exp Λ * airyBiWt X := by
  have hX2 : 0 < 2 + |X| := by positivity
  have hξ2 : 0 < 2 + |ξ| := by positivity
  have hpoly : (2 + |ξ|) ^ (-(1 / 4) : ℝ) ≤ 6 / 5 * (2 + |X|) ^ (-(1 / 4) : ℝ) := by
    have hle : (2 + |X|) / 2 ≤ 2 + |ξ| := by
      have : |X| ≤ |ξ| + 1 := by
        have := abs_sub_abs_le_abs_sub X ξ
        rw [abs_sub_comm] at this
        linarith
      linarith [abs_nonneg ξ]
    have hle' : 2⁻¹ * (2 + |X|) ≤ 2 + |ξ| := by linarith
    have h := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2⁻¹ * (2 + |X|)) hle'
      (by norm_num : -(1 / 4 : ℝ) ≤ 0)
    rw [Real.mul_rpow (by norm_num) hX2.le, Real.inv_rpow (by norm_num),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), inv_inv] at h
    refine h.trans ?_
    have := two_rpow_quarter_le
    have hp : 0 ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) := by positivity
    nlinarith
  have hΛ0 : 0 ≤ Λ := le_trans (by positivity) hΛ
  -- exponential factor: `ξ(ξ) - ξ(X) ≤ Λ`
  have hexp : airyXi ξ - airyXi X ≤ Λ := by
    unfold airyXi
    set a := max X 0 with ha
    set b := max ξ 0 with hb
    have ha0 : 0 ≤ a := le_max_right _ _
    rcases le_total b a with hba | hab
    · have : (2 / 3) * b ^ (3 / 2 : ℝ) ≤ (2 / 3) * a ^ (3 / 2 : ℝ) := by
        gcongr
      linarith
    · have hb0 : 0 ≤ b := le_max_right _ _
      have hdiff : b - a ≤ |ξ - X| := by
        have := abs_max_sub_max_le_abs ξ X 0
        exact (le_abs_self _).trans this
      have hbX : b ≤ 1 + |X| := by
        have : b - a ≤ 1 := hdiff.trans h1
        have : a ≤ |X| := by
          rw [ha]; exact max_le (le_abs_self X) (abs_nonneg X)
        linarith
      have key := rpow_three_halves_sub_le ha0 hab
      have hsq : √b ≤ √(1 + |X|) := Real.sqrt_le_sqrt hbX
      have h3 : 2 / 3 * b ^ (3 / 2 : ℝ) - 2 / 3 * a ^ (3 / 2 : ℝ) ≤ √b * (b - a) := by
        nlinarith [key]
      calc 2 / 3 * b ^ (3 / 2 : ℝ) - 2 / 3 * a ^ (3 / 2 : ℝ) ≤ √b * (b - a) := h3
        _ ≤ √(1 + |X|) * |ξ - X| := mul_le_mul hsq hdiff (by linarith) (Real.sqrt_nonneg _)
        _ ≤ Λ := by linarith
  unfold airyBiWt
  have hE : Real.exp (airyXi ξ) ≤ Real.exp Λ * Real.exp (airyXi X) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
  have hp : 0 ≤ (2 + |X|) ^ (-(1 / 4) : ℝ) := by positivity
  have hp1 : 0 < (2 + |ξ|) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hξ2 _
  calc (2 + |ξ|) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi ξ) ≤
      (6 / 5 * (2 + |X|) ^ (-(1 / 4) : ℝ)) * (Real.exp Λ * Real.exp (airyXi X)) :=
        mul_le_mul hpoly hE (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- **Uniform parametrix defect for `Bi`**: the lattice form `|jac a c ψ_B k| ≤ K h² airyBiWt(X_k)` for
`ψ_B(q) = g(q) Bi(h^{-2/3} ζ(q))` (same hypotheses as `airyParametrix_defect_uniform_lattice`). -/
theorem dao_bi_defect_lattice {U J : Set ℝ} {ζ A g : ℝ → ℝ} (hU : IsOpen U)
    (hJ : IsCompact J) (hJU : J ⊆ U) (hζ : ContDiffOn ℝ 3 ζ U) (hA : ContDiffOn ℝ 2 A U)
    (hg : ContDiffOn ℝ 2 g U)
    (hrel : ∀ q ∈ U, g q ^ 2 * A q * deriv ζ q * (2 * deriv langerCosh (ζ q * deriv ζ q ^ 2)) = 1) :
    ∃ K h0 : ℝ, 0 < K ∧ 0 < h0 ∧ ∀ (h q₀ : ℝ) (a c ψ : ℤ → ℝ), 0 < h → h ≤ h0 →
      (∀ k : ℤ, a k = A (q₀ + k * h - h / 2)) →
      (∀ k : ℤ, c k = 2 * A (q₀ + k * h) * langerCosh (ζ (q₀ + k * h) * deriv ζ (q₀ + k * h) ^ 2)) →
      (∀ k : ℤ, ψ k = g (q₀ + k * h) * airyBi (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h))) →
      ∀ k : ℤ, q₀ + k * h ∈ J →
        |FormalResearch.DiscreteAiry.jac a c ψ k| ≤
          K * h ^ 2 * airyBiWt (h ^ (-(2 / 3 : ℝ)) * ζ (q₀ + k * h)) :=
  dao_defect_lattice isAirySol_airyBi_shift 450 2385000 (by norm_num) (by norm_num)
    (fun x => (airyBiWt_pos x).le) (fun x => (apx_airyBi_global x).1) (fun x => (apx_airyBi_global x).2)
    hU hJ hJU hζ hA hg hrel

/-- info: 'FormalResearch.Special.apx_airyBi_global' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apx_airyBi_global

/-- info: 'FormalResearch.Special.airyBi_ge_airyBiWt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_ge_airyBiWt

/-- info: 'FormalResearch.Special.airyBiWt_le_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiWt_le_of_close

/-- info: 'FormalResearch.Special.dao_bi_defect_lattice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dao_bi_defect_lattice

end FormalResearch.Special

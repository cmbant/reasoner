module

public import FormalResearch.Special.AiryGammaBounds
public import FormalResearch.Special.AiryTaylor

/-!
# Rigorous Taylor evaluation of `Ai` at `-2.33` and `-2.35`: the sign change at the first zero

With `Ai = Ai(0) F + Ai'(0) G` (`AiryTaylor`) and the rational enclosures of `Ai(0), Ai'(0)`
(`AiryGammaBounds`), `Ai` is evaluated at two points by exact partial sums and a geometric tail bound:

* `airyAi_eq_series`: for real `x`, `Ai(x) = Ai(0) F(x) + Ai'(0) G(x)` with `F, G` the sums of the real series
  `Σ A_j x^{3j}/(3j)!` and `Σ B_j x^{3j+1}/(3j+1)!` (`airyFterm`, `airyGterm`);
* `abs_sub_partial_le`: if `|t_{k+1}| ≤ ρ |t_k|` for `k ≥ K` (`ρ < 1`) then
  `|Σ t - Σ_{k<K} t_k| ≤ |t_K|/(1 - ρ)`;
* `airyFterm_ratio`, `airyGterm_ratio`: `|F_{k+1}| = |F_k| |x|³/((3k+2)(3k+3))`,
  `|G_{k+1}| = |G_k| |x|³/((3k+3)(3k+4))`;
* `airyAi_neg_233_pos`, `airyAi_neg_235_neg`: **`Ai(-2.33) > 0` and `Ai(-2.35) < 0`**, hence (IVT) a zero of `Ai` in
  `(-2.35, -2.33)` (the first zero `a_1 = -2.3381074…`; `airy_exists_zero_first` in `AiryFirstZeros`).

Numerically checked with mpmath (30 digits): `F(-2.33) = -0.36137212…`, `G(-2.33) = -0.51766637…`,
`F(-2.35) = -0.38034159…`, `G(-2.35) = -0.48950419…`, `Ai(-2.33) = 0.0056848…`, `Ai(-2.35) = -0.0083387…`; the
partial sums used have six terms and the proved enclosures are `±3·10⁻⁴` wide.  The sign change is robust: it
holds for every `Ai(0)/|Ai'(0)| ∈ (1.287, 1.4325)` (true value `1.3717…`).

Not formalised: a Taylor evaluation at other points (the zeros `a_n`, `n ≥ 2` are located by the
asymptotics of `AiryAsymZeros`).
-/

@[expose] public section

open Filter Topology
open scoped Real Nat

namespace FormalResearch.Special

/-- The terms of `F(x) = Σ A_k x^{3k}/(3k)!`. -/
noncomputable def airyFterm (x : ℝ) (k : ℕ) : ℝ := airyCoefA k / ((3 * k)! : ℝ) * x ^ (3 * k)

/-- The terms of `G(x) = Σ B_k x^{3k+1}/(3k+1)!`. -/
noncomputable def airyGterm (x : ℝ) (k : ℕ) : ℝ := airyCoefB k / ((3 * k + 1)! : ℝ) * x ^ (3 * k + 1)

/-- **Real form of the Taylor decomposition**: `Ai(x) = Ai(0) F(x) + Ai'(0) G(x)`. -/
theorem airyAi_eq_series (x : ℝ) :
    ∃ F G : ℝ, HasSum (airyFterm x) F ∧ HasSum (airyGterm x) G ∧
      airyAi x = airyAi 0 * F + airyAi' 0 * G := by
  have hF := hasSum_airyTaylorF (x : ℂ)
  have hG := hasSum_airyTaylorG (x : ℂ)
  have hF' : HasSum (airyFterm x) (airyTaylorF (x : ℂ)).re := by
    have := Complex.hasSum_re hF
    convert this using 1
    funext k
    simp [airyFterm, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
  have hG' : HasSum (airyGterm x) (airyTaylorG (x : ℂ)).re := by
    have := Complex.hasSum_re hG
    convert this using 1
    funext k
    simp [airyGterm, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
  refine ⟨_, _, hF', hG', ?_⟩
  have h := airyAiC_eq_taylor (x : ℂ)
  have e0 : airyAiC 0 = (airyAi 0 : ℂ) := by simpa using airyAiC_ofReal 0
  have e1 : deriv airyAiC 0 = (airyAi' 0 : ℂ) := by simpa using deriv_airyAiC_ofReal 0
  rw [airyAiC_ofReal, e0, e1] at h
  have := congrArg Complex.re h
  simpa using this

/-- Tail bound for a series with eventually geometric decay of the terms. -/
lemma abs_sub_partial_le {t : ℕ → ℝ} {s : ℝ} (h : HasSum t s) (K : ℕ) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (hr : ∀ k, K ≤ k → |t (k + 1)| ≤ ρ * |t k|) :
    |s - ∑ k ∈ Finset.range K, t k| ≤ |t K| / (1 - ρ) := by
  have hs := h.summable
  have h1 : ∑ k ∈ Finset.range K, t k + ∑' k, t (k + K) = s := by
    rw [hs.sum_add_tsum_nat_add, h.tsum_eq]
  have hb : ∀ k, |t (k + K)| ≤ |t K| * ρ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc |t (k + 1 + K)| = |t ((k + K) + 1)| := by rw [show k + 1 + K = (k + K) + 1 by ring]
        _ ≤ ρ * |t (k + K)| := hr _ (by lia)
        _ ≤ ρ * (|t K| * ρ ^ k) := by gcongr
        _ = |t K| * ρ ^ (k + 1) := by ring
  have hgeo : HasSum (fun k : ℕ => |t K| * ρ ^ k) (|t K| * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 hρ1).mul_left _
  have hsum2 : Summable (fun k => t (k + K)) := (summable_nat_add_iff K).mpr hs
  have hnorm : ‖∑' k, t (k + K)‖ ≤ |t K| * (1 - ρ)⁻¹ := by
    refine tsum_of_norm_bounded hgeo (fun k => ?_)
    simpa [Real.norm_eq_abs] using hb k
  rw [Real.norm_eq_abs] at hnorm
  have : s - ∑ k ∈ Finset.range K, t k = ∑' k, t (k + K) := by linarith
  rw [this]
  calc _ ≤ |t K| * (1 - ρ)⁻¹ := hnorm
    _ = |t K| / (1 - ρ) := by rw [div_eq_mul_inv]

lemma airyFterm_succ (x : ℝ) (k : ℕ) :
    airyFterm x (k + 1) = airyFterm x k * (x ^ 3 / ((3 * k + 2) * (3 * k + 3))) := by
  have hA : airyCoefA (k + 1) = airyCoefA k * (3 * (k : ℝ) + 1) := by
    simp [airyCoefA, Finset.prod_range_succ]
  have hf : ((3 * (k + 1))! : ℝ) = ((3 * k)! : ℝ) * ((3 * k + 1) * (3 * k + 2) * (3 * k + 3)) := by
    rw [show 3 * (k + 1) = 3 * k + 1 + 1 + 1 by ring]
    simp only [Nat.factorial_succ]; push_cast; ring
  have hfp : (0 : ℝ) < ((3 * k)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold airyFterm
  rw [hA, hf, show 3 * (k + 1) = 3 * k + 3 by ring, pow_add]
  have h1 : (0 : ℝ) < 3 * k + 1 := by positivity
  have h2 : (0 : ℝ) < 3 * k + 2 := by positivity
  have h3 : (0 : ℝ) < 3 * k + 3 := by positivity
  field_simp

lemma airyGterm_succ (x : ℝ) (k : ℕ) :
    airyGterm x (k + 1) = airyGterm x k * (x ^ 3 / ((3 * k + 3) * (3 * k + 4))) := by
  have hB : airyCoefB (k + 1) = airyCoefB k * (3 * (k : ℝ) + 2) := by
    simp [airyCoefB, Finset.prod_range_succ]
  have hf : ((3 * (k + 1) + 1)! : ℝ) =
      ((3 * k + 1)! : ℝ) * ((3 * k + 2) * (3 * k + 3) * (3 * k + 4)) := by
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 1 + 1 + 1 by ring]
    simp only [Nat.factorial_succ]; push_cast; ring
  have hfp : (0 : ℝ) < ((3 * k + 1)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  unfold airyGterm
  rw [hB, hf, show 3 * (k + 1) + 1 = (3 * k + 1) + 3 by ring, pow_add]
  have h1 : (0 : ℝ) < 3 * k + 2 := by positivity
  have h2 : (0 : ℝ) < 3 * k + 3 := by positivity
  have h3 : (0 : ℝ) < 3 * k + 4 := by positivity
  field_simp

lemma airyFterm_ratio (x : ℝ) (k : ℕ) :
    |airyFterm x (k + 1)| = |airyFterm x k| * (|x| ^ 3 / ((3 * k + 2) * (3 * k + 3))) := by
  rw [airyFterm_succ, abs_mul, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (3 * k + 2) * (3 * k + 3))]

lemma airyGterm_ratio (x : ℝ) (k : ℕ) :
    |airyGterm x (k + 1)| = |airyGterm x k| * (|x| ^ 3 / ((3 * k + 3) * (3 * k + 4))) := by
  rw [airyGterm_succ, abs_mul, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (3 * k + 3) * (3 * k + 4))]

/-- Six-term enclosure of `F(x)` for `|x| ≤ 2.35`: `|F - Σ_{k<6} F_k| ≤ (420/407) |F_6|`. -/
lemma airyF_enclosure {x F : ℝ} (hx : |x| ≤ 47 / 20) (h : HasSum (airyFterm x) F) :
    |F - ∑ k ∈ Finset.range 6, airyFterm x k| ≤ |airyFterm x 6| * (420 / 407) := by
  have hx3 : |x| ^ 3 ≤ 13 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 3
    norm_num at this ⊢; linarith
  have := abs_sub_partial_le h 6 (ρ := 13 / 420) (by norm_num) (by norm_num) (fun k hk => by
    rw [airyFterm_ratio, mul_comm]
    have hk' : (6 : ℝ) ≤ k := by exact_mod_cast hk
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3])
  refine this.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]; norm_num

/-- Six-term enclosure of `G(x)` for `|x| ≤ 2.35`: `|G - Σ_{k<6} G_k| ≤ (462/449) |G_6|`. -/
lemma airyG_enclosure {x G : ℝ} (hx : |x| ≤ 47 / 20) (h : HasSum (airyGterm x) G) :
    |G - ∑ k ∈ Finset.range 6, airyGterm x k| ≤ |airyGterm x 6| * (462 / 449) := by
  have hx3 : |x| ^ 3 ≤ 13 := by
    have := pow_le_pow_left₀ (abs_nonneg x) hx 3
    norm_num at this ⊢; linarith
  have := abs_sub_partial_le h 6 (ρ := 13 / 462) (by norm_num) (by norm_num) (fun k hk => by
    rw [airyGterm_ratio, mul_comm]
    have hk' : (6 : ℝ) ≤ k := by exact_mod_cast hk
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg x, pow_nonneg (abs_nonneg x) 3])
  refine this.trans (le_of_eq ?_)
  rw [div_eq_mul_inv]; norm_num

/-- `F(-2.33) ∈ (-0.3620, -0.3607)`, `G(-2.33) ∈ (-0.5180, -0.5173)`. -/
lemma airyFG_neg233 {F G : ℝ} (hF : HasSum (airyFterm (-2.33)) F) (hG : HasSum (airyGterm (-2.33)) G) :
    -0.3620 < F ∧ F < -0.3607 ∧ -0.5180 < G ∧ G < -0.5173 := by
  have h1 := airyF_enclosure (by norm_num [abs_of_neg]) hF
  have h2 := airyG_enclosure (by norm_num [abs_of_neg]) hG
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, airyFterm, airyGterm, airyCoefA,
    airyCoefB, Finset.prod_range_succ, Finset.prod_range_zero] at h1 h2
  norm_num [Nat.factorial, abs_le] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- `F(-2.35) ∈ (-0.3810, -0.3796)`, `G(-2.35) ∈ (-0.4900, -0.4890)`. -/
lemma airyFG_neg235 {F G : ℝ} (hF : HasSum (airyFterm (-2.35)) F) (hG : HasSum (airyGterm (-2.35)) G) :
    -0.3810 < F ∧ F < -0.3796 ∧ -0.4900 < G ∧ G < -0.4890 := by
  have h1 := airyF_enclosure (by norm_num [abs_of_neg]) hF
  have h2 := airyG_enclosure (by norm_num [abs_of_neg]) hG
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, airyFterm, airyGterm, airyCoefA,
    airyCoefB, Finset.prod_range_succ, Finset.prod_range_zero] at h1 h2
  norm_num [Nat.factorial, abs_le] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **`Ai(-2.33) > 0`.** -/
theorem airyAi_neg_233_pos : 0 < airyAi (-2.33) := by
  obtain ⟨F, G, hF, hG, h⟩ := airyAi_eq_series (-2.33)
  obtain ⟨f1, f2, g1, g2⟩ := airyFG_neg233 hF hG
  obtain ⟨a1, a2⟩ := airyAi_zero_bounds
  obtain ⟨b1, b2⟩ := airyAi'_zero_bounds
  rw [h]
  nlinarith

/-- **`Ai(-2.35) < 0`.** -/
theorem airyAi_neg_235_neg : airyAi (-2.35) < 0 := by
  obtain ⟨F, G, hF, hG, h⟩ := airyAi_eq_series (-2.35)
  obtain ⟨f1, f2, g1, g2⟩ := airyFG_neg235 hF hG
  obtain ⟨a1, a2⟩ := airyAi_zero_bounds
  obtain ⟨b1, b2⟩ := airyAi'_zero_bounds
  rw [h]
  nlinarith

/-- info: 'FormalResearch.Special.airyAi_neg_233_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_neg_233_pos

/-- info: 'FormalResearch.Special.airyAi_neg_235_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_neg_235_neg

end FormalResearch.Special

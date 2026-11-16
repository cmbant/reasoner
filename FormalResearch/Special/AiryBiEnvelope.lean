module

public import FormalResearch.Special.AiryBiNeg
public import FormalResearch.Special.AiryAsymBiPos
public import FormalResearch.Special.AiryEnvelopeReal
public import FormalResearch.Special.AiryEnvelopeRot

/-!
# Two-sided real-axis envelope of `Bi` on `[-1, ∞)`

For `x ≥ -1`, with `ξ(x) = airyXi x = (2/3)(x₊)^{3/2}`:
`(1/800) (2+x)^{-1/4} e^{ξ(x)} ≤ Bi(x) ≤ 16 (2+x)^{-1/4} e^{ξ(x)}` (`airyBi_envelope_real`), the companion of
`airyAi_envelope_real` (`(1/20) (2+x)^{-1/4} e^{-ξ} ≤ Ai ≤ 4 (2+x)^{-1/4} e^{-ξ}`).  For `x ≥ 2` it follows from
`airyBi_pos_asymptotic`; on `[-1, 2]` from `1/100 ≤ Bi ≤ Bi(2)` (`airyBi_ge_one_hundredth`, monotonicity).
Consequences: `Ai Bi ≍ (2+x)^{-1/2}` on `[-1, ∞)` (`airyAi_mul_airyBi_envelope`) and `Bi' ≤ C (2+x)^{1/2} Bi`
(`airyBiDeriv_le_mul_airyBi`, from the Wronskian).  Constants are those of the proof (numerically the optimal ones
are `≈ 0.28` and `≈ 0.9` for large `x`).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.Special

lemma quarter_compare_two {x : ℝ} (hx : 2 ≤ x) :
    5 / 6 * x ^ (-(1 / 4) : ℝ) ≤ (2 + x) ^ (-(1 / 4) : ℝ) ∧ (2 + x) ^ (-(1 / 4) : ℝ) ≤ x ^ (-(1 / 4) : ℝ) := by
  have hx0 : 0 < x := by linarith
  have h2 : 0 < 2 + x := by linarith
  constructor
  · have h := Real.rpow_le_rpow_of_nonpos (show 0 < 2 + x by linarith) (show 2 + x ≤ 2 * x by linarith)
      (show (-(1 / 4) : ℝ) ≤ 0 by norm_num)
    rw [Real.mul_rpow (by norm_num) hx0.le] at h
    have h2q : (5 / 6 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4) : ℝ) := by
      rw [Real.rpow_neg (by norm_num)]
      rw [le_inv_comm₀ (by norm_num) (by positivity)]
      have := two_rpow_quarter_le
      linarith
    calc 5 / 6 * x ^ (-(1 / 4) : ℝ) ≤ (2 : ℝ) ^ (-(1 / 4) : ℝ) * x ^ (-(1 / 4) : ℝ) := by
          gcongr
      _ ≤ _ := h
  · exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) (by norm_num)

/-- For `x ≥ 2`: `0.27 x^{-1/4} e^{ξ} ≤ Bi(x) ≤ 0.86 x^{-1/4} e^{ξ}`, `ξ = (2/3) x^{3/2}`. -/
lemma airyBi_large_bounds {x : ℝ} (hx : 2 ≤ x) :
    0.27 * (x ^ (-(1 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ))) ≤ airyBi x ∧
      airyBi x ≤ 0.86 * (x ^ (-(1 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ))) := by
  have hx0 : 0 < x := by linarith
  have h := airyBi_pos_asymptotic hx0
  set E := x ^ (-(1 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ)) with hE
  have hEp : 0 < E := by positivity
  -- `x^{-7/4} = x^{-1/4} x^{-3/2}`, `x^{-3/2} ≤ 0.36`
  have h74 : x ^ (-(7 / 4) : ℝ) = x ^ (-(1 / 4) : ℝ) * x ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have h32 : x ^ (-(3 / 2) : ℝ) ≤ 0.36 := by
    rw [Real.rpow_neg hx0.le]
    have hs : 1.41 ≤ √x := by
      rw [Real.le_sqrt' (by norm_num)]; nlinarith
    have : x ^ (3 / 2 : ℝ) ≥ 2.8 := by
      rw [← sqrt_cube_eq_rpow hx0]
      nlinarith [Real.sqrt_nonneg x, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg x)]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hr : 4 / 5 * x ^ (-(7 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ)) ≤ 0.29 * E := by
    rw [h74, hE]
    have := Real.exp_pos (2 / 3 * x ^ (3 / 2 : ℝ))
    have hq : 0 < x ^ (-(1 / 4) : ℝ) := by positivity
    nlinarith [mul_pos hq this]
  have hT := sqrt_pi_bounds
  have hinv1 : 1 / √π ≤ 0.57 := by
    rw [div_le_iff₀ (by linarith [hT.1])]; nlinarith [hT.1]
  have hinv2 : 0.56 ≤ 1 / √π := by
    rw [le_div_iff₀ (by linarith [hT.1])]; nlinarith [sqrt_pi_le]
  have e : 1 / √π * x ^ (-(1 / 4) : ℝ) * Real.exp (2 / 3 * x ^ (3 / 2 : ℝ)) = 1 / √π * E := by
    rw [hE]; ring
  rw [e] at h
  rw [abs_le] at h
  constructor <;> nlinarith [h.1, h.2]


lemma rpow_three_halves_le_three {y : ℝ} (h0 : 0 ≤ y) (h2 : y ≤ 2) : y ^ (3 / 2 : ℝ) ≤ 3 := by
  rcases h0.eq_or_lt with h | h
  · rw [← h]; norm_num
  · rw [← sqrt_cube_eq_rpow h]
    have hs : √y ≤ 1.42 := by
      rw [Real.sqrt_le_left (by norm_num)]; nlinarith
    have hs0 := Real.sqrt_nonneg y
    nlinarith [mul_nonneg hs0 hs0]

lemma four_pow_neg_quarter_ge : (0.7 : ℝ) ≤ (4 : ℝ) ^ (-(1 / 4) : ℝ) := by
  rw [Real.rpow_neg (by norm_num), le_inv_comm₀ (by norm_num) (by positivity)]
  have h4 : ((4 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
  have hq : 0 ≤ (4 : ℝ) ^ (1 / 4 : ℝ) := by positivity
  by_contra hlt
  rw [not_le] at hlt
  have := pow_lt_pow_left₀ hlt (by norm_num) (by norm_num : (4 : ℕ) ≠ 0)
  rw [h4] at this
  norm_num at this

/-- **Two-sided real-axis envelope of `Bi`**: for `x ≥ -1`,
`(1/800) (2+x)^{-1/4} e^{ξ(x)} ≤ Bi(x) ≤ 16 (2+x)^{-1/4} e^{ξ(x)}`, `ξ(x) = (2/3)(x₊)^{3/2}`. -/
theorem airyBi_envelope_real {x : ℝ} (hx : -1 ≤ x) :
    1 / 800 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x)) ≤ airyBi x ∧
      airyBi x ≤ 16 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x)) := by
  have h2 : 0 < 2 + x := by linarith
  have hq : 0 < (2 + x) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
  rcases le_total 2 x with hx2 | hx2
  · -- large `x`
    have hx0 : 0 < x := by linarith
    have hξ : airyXi x = 2 / 3 * x ^ (3 / 2 : ℝ) := by
      unfold airyXi; rw [max_eq_left hx0.le]
    rw [hξ]
    obtain ⟨hl, hu⟩ := airyBi_large_bounds hx2
    obtain ⟨c1, c2⟩ := quarter_compare_two hx2
    have hE := Real.exp_pos (2 / 3 * x ^ (3 / 2 : ℝ))
    have hxq : 0 < x ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos hx0 _
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right c2 hE.le, mul_pos hq hE]
    · nlinarith [mul_le_mul_of_nonneg_right c1 hE.le, mul_pos hq hE, mul_pos hxq hE]
  · -- `x ∈ [-1, 2]`
    have hξ0 : 0 ≤ airyXi x := airyXi_nonneg x
    have hξ2 : airyXi x ≤ 2 := by
      unfold airyXi
      have := rpow_three_halves_le_three (y := max x 0) (le_max_right _ _) (max_le hx2 (by norm_num))
      linarith
    have hexp1 : 1 ≤ Real.exp (airyXi x) := Real.one_le_exp hξ0
    have hexp2 : Real.exp (airyXi x) ≤ 7.39 :=
      (Real.exp_le_exp.mpr hξ2).trans exp_two_le
    have hq1 : (2 + x) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    have hq4 : (4 : ℝ) ^ (-(1 / 4) : ℝ) ≤ (2 + x) ^ (-(1 / 4) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos h2 (by linarith) (by norm_num)
    have h4 := four_pow_neg_quarter_ge
    have hlow := airyBi_ge_one_hundredth (show -(11 / 10 : ℝ) ≤ x by linarith)
    have hmono := strictMonoOn_airyBi_Ici_neg.monotoneOn (show x ∈ Ici (-(11 / 10 : ℝ)) from
      by simp only [mem_Ici]; linarith) (show (2 : ℝ) ∈ Ici (-(11 / 10 : ℝ)) from
      by simp only [mem_Ici]; norm_num) hx2
    obtain ⟨-, hB2⟩ := airyBi_large_bounds (show (2 : ℝ) ≤ 2 from le_rfl)
    have hq2 : (2 : ℝ) ^ (-(1 / 4) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    have hξ2' : 2 / 3 * (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 2 := by
      have := rpow_three_halves_le_three (y := 2) (by norm_num) le_rfl
      linarith
    have he2 : Real.exp (2 / 3 * (2 : ℝ) ^ (3 / 2 : ℝ)) ≤ 7.39 :=
      (Real.exp_le_exp.mpr hξ2').trans exp_two_le
    have hep := Real.exp_pos (2 / 3 * (2 : ℝ) ^ (3 / 2 : ℝ))
    have hqp : 0 < (2 : ℝ) ^ (-(1 / 4) : ℝ) := by positivity
    have hB2' : airyBi 2 ≤ 0.86 * 7.39 := by
      refine hB2.trans ?_
      have := mul_le_mul hq2 he2 hep.le zero_le_one
      nlinarith
    constructor
    · nlinarith [mul_le_mul hq1 hexp2 (Real.exp_pos _).le zero_le_one]
    · nlinarith [mul_le_mul hq4 hexp1 zero_le_one hq.le]

/-- `Ai Bi ≍ (2+x)^{-1/2}`: for `x ≥ -1`, `(1/16000) (2+x)^{-1/2} ≤ Ai(x) Bi(x) ≤ 64 (2+x)^{-1/2}`. -/
theorem airyAi_mul_airyBi_envelope {x : ℝ} (hx : -1 ≤ x) :
    1 / 16000 * (2 + x) ^ (-(1 / 2) : ℝ) ≤ airyAi x * airyBi x ∧
      airyAi x * airyBi x ≤ 64 * (2 + x) ^ (-(1 / 2) : ℝ) := by
  have h2 : 0 < 2 + x := by linarith
  obtain ⟨a1, a2⟩ := airyAi_envelope_real hx
  obtain ⟨b1, b2⟩ := airyBi_envelope_real hx
  replace a1 : 1 / 20 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) ≤ airyAi x := by
    simpa [mul_assoc] using a1
  replace a2 : airyAi x ≤ 4 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x)) := by
    simpa [mul_assoc] using a2
  have hh : (2 + x) ^ (-(1 / 4) : ℝ) * (2 + x) ^ (-(1 / 4) : ℝ) = (2 + x) ^ (-(1 / 2) : ℝ) := by
    rw [← Real.rpow_add h2]; norm_num
  have hq : 0 < (2 + x) ^ (-(1 / 4) : ℝ) := Real.rpow_pos_of_pos h2 _
  have hexp : Real.exp (-airyXi x) * Real.exp (airyXi x) = 1 := by
    rw [← Real.exp_add]; simp
  have e1 := Real.exp_pos (-airyXi x)
  have e2 := Real.exp_pos (airyXi x)
  constructor
  · calc 1 / 16000 * (2 + x) ^ (-(1 / 2) : ℝ)
        = (1 / 20 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x))) *
          (1 / 800 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x))) := by
          rw [← hh]; nlinarith [hexp]
      _ ≤ _ := mul_le_mul a1 b1 (by positivity) (by linarith [a1, mul_pos hq e1])
  · calc airyAi x * airyBi x ≤ (4 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (-airyXi x))) *
          (16 * ((2 + x) ^ (-(1 / 4) : ℝ) * Real.exp (airyXi x))) :=
          mul_le_mul a2 b2 (by linarith [b1, mul_pos hq e2]) (by positivity)
      _ = 64 * (2 + x) ^ (-(1 / 2) : ℝ) := by rw [← hh]; nlinarith [hexp]


/-- `Bi'(x) ≤ 5300 (2+x)^{1/2} Bi(x)` for `x ≥ -1` (from the Wronskian and the envelopes). -/
theorem airyBiDeriv_le_mul_airyBi {x : ℝ} (hx : -1 ≤ x) :
    airyBiDeriv x ≤ 5300 * (2 + x) ^ (1 / 2 : ℝ) * airyBi x := by
  have h2 : 0 < 2 + x := by linarith
  have hA := airyAi_pos_of_neg_one_le hx
  have hB := airyBi_pos_of_neg_eleven_tenth_le (show -(11 / 10 : ℝ) ≤ x by linarith)
  have hW := airyWronskian_real x
  have hD := abs_airyAi'_le_mul_airyAi hx
  obtain ⟨hm, -⟩ := airyAi_mul_airyBi_envelope hx
  have hs : 0 < (2 + x) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos h2 _
  have hss : (2 + x) ^ (-(1 / 2) : ℝ) * (2 + x) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add h2]; norm_num
  set s := (2 + x) ^ (1 / 2 : ℝ) with hsdef
  set t := (2 + x) ^ (-(1 / 2) : ℝ) with htdef
  have ht : 0 < t := Real.rpow_pos_of_pos h2 _
  -- `1 ≤ 16000 s Ai Bi`
  have h1 : 1 ≤ 16000 * s * (airyAi x * airyBi x) := by
    have := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 16000 * s)
    nlinarith
  have hpi : 3.14 ≤ π := Real.pi_gt_d2.le
  have hpi0 := Real.pi_pos
  -- `Ai Bi' = 1/π + Ai' Bi ≤ 1/π + 120 s Ai Bi`
  have h3 : airyAi x * airyBiDeriv x ≤ 1 / π + 120 * s * (airyAi x * airyBi x) := by
    have e : airyAi x * airyBiDeriv x = 1 / π + airyAi' x * airyBi x := by linarith [hW]
    rw [e]
    have : airyAi' x * airyBi x ≤ |airyAi' x| * airyBi x := mul_le_mul_of_nonneg_right (le_abs_self _) hB.le
    nlinarith [mul_le_mul_of_nonneg_right hD hB.le]
  have h4 : 1 / π ≤ 1 / 3.14 := by
    rw [div_le_div_iff₀ hpi0 (by norm_num)]; linarith
  -- `Ai Bi' ≤ (1/3) · 16000 s Ai Bi + 120 s Ai Bi ≤ 5300 s Ai Bi`
  have h5 : airyAi x * airyBiDeriv x ≤ 5300 * s * (airyAi x * airyBi x) := by
    have hp : 0 ≤ airyAi x * airyBi x := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 (by norm_num : (0 : ℝ) ≤ 1 / 3.14)]
  have : airyAi x * airyBiDeriv x ≤ airyAi x * (5300 * s * airyBi x) := by nlinarith
  exact le_of_mul_le_mul_left this hA

/-- info: 'FormalResearch.Special.airyBi_envelope_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBi_envelope_real

/-- info: 'FormalResearch.Special.airyAi_mul_airyBi_envelope' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi_mul_airyBi_envelope

/-- info: 'FormalResearch.Special.airyBiDeriv_le_mul_airyBi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyBiDeriv_le_mul_airyBi

end FormalResearch.Special

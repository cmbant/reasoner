module

public import FormalResearch.Special.AiryZeroSpacing
public import FormalResearch.Complex.SeparatedKernelSum

/-!
# Zero data of `Ai` for the sampling bound of Theorem Q (3)

Inputs for `AiryCftQSample`, all **proved** from `AiryZeroSpacing` and `AiryFirstZeros` (no new numerics): with
`c_n := √(-a_{n+1})` (`n ≥ 0`),

* `airyZero_cube_ge12`: `12 ℓ² ≤ (-a_ℓ)³` for every `ℓ ≥ 1` (`16 ℓ²` for `ℓ ≥ 2`; `a_1 < -2.33` for `ℓ = 1`);
* `airyRoot_one_le`: `1 ≤ c_n`;
* `airyRoot_sep`: `|n - m| ≤ |c_n - c_m| max(c_n, c_m)²` for `n ≠ m` (from `|a_n - a_k| ≥ 1.8 |n-k| max(n,k)^{-1/3}`,
  `|a_n - a_k| = |c_n - c_k|(c_n + c_k)`, and `max(n,k)^{1/3} ≤ c_max/1.5`);
* `airyRoot_kernel_sum`: the Cauchy-kernel sum `Σ_n r_n²/((t - c_n)² + r_n²)`, `r_n = 1/(4c_n²)`, is bounded uniformly in `t` and the
  number of terms (`separated_kernel_sum`).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- `12 ℓ² ≤ (-a_ℓ)³` for all `ℓ ≥ 1`. -/
lemma airyZero_cube_ge12 {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 12 * (ℓ : ℝ) ^ 2 ≤ (-airyZero ℓ) ^ 3 := by
  rcases Nat.lt_or_ge 1 ℓ with h | h
  · have := (airyZero_abs_cube_bounds (n := ℓ) h).1
    have hl : (0 : ℝ) ≤ (ℓ : ℝ) ^ 2 := by positivity
    linarith
  · have : ℓ = 1 := by omega
    subst this
    have h1 := airyZero_one.2
    have : (2.33 : ℝ) ^ 3 ≤ (-airyZero 1) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
    norm_num at this ⊢
    linarith

/-- `12 ℓ² ≤ c_ℓ⁶` for `c_ℓ = √(-a_ℓ)`. -/
lemma airyZeroRoot_sixth_ge {ℓ : ℕ} (hℓ : 1 ≤ ℓ) : 12 * (ℓ : ℝ) ^ 2 ≤ airyZeroRoot ℓ ^ 6 := by
  have h := airyZero_cube_ge12 hℓ
  have e : airyZeroRoot ℓ ^ 6 = (-airyZero ℓ) ^ 3 := by
    rw [airyZero_eq_neg_root_sq ℓ]; ring
  rw [e]; exact h

lemma airyRoot_one_le (ℓ : ℕ) : 1 ≤ airyZeroRoot (ℓ + 1) := by
  have h := airyZeroRoot_sixth_ge (ℓ := ℓ + 1) (by omega)
  have hl : (1 : ℝ) ≤ ((ℓ + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ ℓ + 1)
  by_contra hc
  push Not at hc
  have h0 := (airyZeroRoot_pos (ℓ + 1)).le
  have : airyZeroRoot (ℓ + 1) ^ 6 < 1 := pow_lt_one₀ h0 hc (by norm_num)
  nlinarith

/-- `M ≤ c_M³ / 1.5³`-type bound in the form needed: `1.5 · M^{1/3} ≤ c_M`. -/
lemma airyRoot_label_rpow_le {M : ℕ} (hM : 1 ≤ M) : (3 / 2 : ℝ) * (M : ℝ) ^ (1 / 3 : ℝ) ≤ airyZeroRoot M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have h := airyZeroRoot_sixth_ge hM
  set q : ℝ := (M : ℝ) ^ (1 / 3 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hM0 _
  have hq3 : q ^ 3 = M := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]; norm_num
  have hq6 : q ^ 6 = (M : ℝ) ^ 2 := by rw [show q ^ 6 = (q ^ 3) ^ 2 by ring, hq3]
  have hc0 := (airyZeroRoot_pos M).le
  refine le_of_pow_le_pow_left₀ (by norm_num : 6 ≠ 0) hc0 ?_
  rw [mul_pow, hq6]
  have : (3 / 2 : ℝ) ^ 6 * (M : ℝ) ^ 2 ≤ 12 * (M : ℝ) ^ 2 := by
    have : (3 / 2 : ℝ) ^ 6 ≤ 12 := by norm_num
    nlinarith [sq_nonneg (M : ℝ)]
  linarith

/-- Separation for `n < m`: `m - n ≤ (c_m - c_n) c_m²`. -/
lemma airyRoot_sep_lt {n m : ℕ} (h : n < m) :
    ((m : ℝ) - n) ≤ (airyZeroRoot (m + 1) - airyZeroRoot (n + 1)) * airyZeroRoot (m + 1) ^ 2 := by
  have hs := airyZero_separation_lower (k := n + 1) (n := m + 1) (by omega) (by omega)
  have hb := airyRoot_label_rpow_le (M := m + 1) (by omega)
  set cn := airyZeroRoot (n + 1)
  set cm := airyZeroRoot (m + 1)
  have hcn0 : 0 < cn := airyZeroRoot_pos _
  have hcm0 : 0 < cm := airyZeroRoot_pos _
  have hlt : cn < cm := airyZeroRoot_lt (by omega) (by omega)
  have hM0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  set q : ℝ := ((m + 1 : ℕ) : ℝ) ^ (1 / 3 : ℝ) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hM0 _
  have hneg : ((m + 1 : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) = 1 / q := by
    rw [Real.rpow_neg hM0.le, hq, inv_eq_one_div]
  rw [hneg] at hs
  have hmn : (0 : ℝ) ≤ (m : ℝ) - n := by
    have : (n : ℝ) ≤ m := by exact_mod_cast h.le
    linarith
  have hdiff : airyZero (n + 1) - airyZero (m + 1) = (cm - cn) * (cm + cn) := by
    rw [airyZero_eq_neg_root_sq (n + 1), airyZero_eq_neg_root_sq (m + 1)]
    simp only [cn, cm]; ring
  rw [hdiff] at hs
  have e1 : ((m + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ) = (m : ℝ) - n := by push_cast; ring
  rw [e1] at hs
  -- 1/q ≥ 1.5 / cm
  have hq2 : 3 / 2 / cm ≤ 1 / q := by
    rw [div_le_div_iff₀ hcm0 hq0]; linarith
  have h1 : 1.8 * ((m : ℝ) - n) * (3 / 2 / cm) ≤ (cm - cn) * (cm + cn) := by
    refine le_trans ?_ hs
    gcongr
  have h2 : (cm - cn) * (cm + cn) ≤ (cm - cn) * (2 * cm) := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : 1.8 * ((m : ℝ) - n) * (3 / 2 / cm) ≤ (cm - cn) * (2 * cm) := h1.trans h2
  have h4 : 1.8 * ((m : ℝ) - n) * (3 / 2 / cm) * cm = 2.7 * ((m : ℝ) - n) := by
    field_simp; ring
  have h5 : 2.7 * ((m : ℝ) - n) ≤ (cm - cn) * (2 * cm) * cm := by
    rw [← h4]; exact mul_le_mul_of_nonneg_right h3 hcm0.le
  nlinarith

/-- **Separation of the roots `c_n = √(-a_{n+1})`**: `|n - m| ≤ |c_n - c_m| max(c_n, c_m)²` for `n ≠ m`. -/
lemma airyRoot_sep {n m : ℕ} (hnm : n ≠ m) :
    |(n : ℝ) - m| ≤ |airyZeroRoot (n + 1) - airyZeroRoot (m + 1)| *
      (max (airyZeroRoot (n + 1)) (airyZeroRoot (m + 1))) ^ 2 := by
  rcases lt_or_gt_of_ne hnm with h | h
  · have h1 := airyRoot_sep_lt h
    have hlt : airyZeroRoot (n + 1) < airyZeroRoot (m + 1) := airyZeroRoot_lt (by omega) (by omega)
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast h.le
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - n),
      abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ airyZeroRoot (m + 1) - airyZeroRoot (n + 1)),
      max_eq_right hlt.le]
    exact h1
  · have h1 := airyRoot_sep_lt h
    have hlt : airyZeroRoot (m + 1) < airyZeroRoot (n + 1) := airyZeroRoot_lt (by omega) (by omega)
    have hnm' : (m : ℝ) ≤ n := by exact_mod_cast h.le
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - m),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ airyZeroRoot (n + 1) - airyZeroRoot (m + 1)),
      max_eq_left hlt.le]
    exact h1

/-- **Uniform kernel sum over the zeros of `Ai`.**  There is `K` with
`Σ_{n<N} r_n²/((t - c_n)² + r_n²) ≤ K` for all real `t`, `N`, where `c_n = √(-a_{n+1})`, `r_n = 1/(4c_n²)`. -/
theorem airyRoot_kernel_sum : ∃ K : ℝ, ∀ (t : ℝ) (N : ℕ),
    ∑ n ∈ Finset.range N, (1 / (4 * airyZeroRoot (n + 1) ^ 2)) ^ 2 /
      ((t - airyZeroRoot (n + 1)) ^ 2 + (1 / (4 * airyZeroRoot (n + 1) ^ 2)) ^ 2) ≤ K := by
  obtain ⟨K, hK⟩ := FormalResearch.Hardy.separated_kernel_sum (ι := ℕ) (c := fun n => airyZeroRoot (n + 1))
    (d := id) (s := 1) (κ := 12) (by norm_num) (by norm_num)
  refine ⟨K, fun t N => hK (Finset.range N) (fun n _ => airyZeroRoot_pos _) (fun n _ => ?_)
    Function.injective_id.injOn (fun n _ m _ hnm => ?_) t⟩
  · have := airyZeroRoot_sixth_ge (ℓ := n + 1) (by omega)
    push_cast at this
    simpa using this
  · have := airyRoot_sep hnm
    have h0 : (0 : ℝ) ≤ |(n : ℝ) - m| := abs_nonneg _
    simp only [id]
    linarith

/-- info: 'FormalResearch.Special.airyRoot_kernel_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyRoot_kernel_sum

end FormalResearch.Special

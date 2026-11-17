module

public import FormalResearch.Special.AiryPruferAsym

/-!
# One zero of `Ai'` in each gap, and it is asymptotically the midpoint (the Clark node `α = π/2`)

The Clark nodes of `cos α·Ai - sin α·Ai'` for `α = π/2` are the zeros of `Ai'`.  Two facts (`n ≥ 1` resp. `n ≥ 2`):

* `airyAi'_existsUnique_zero_gap`: **exactly one zero `b_n` of `Ai'` in `(a_{n+1}, a_n)`** (Sturm separation in the Prüfer
  form: `Ai' = 0 ⇔ θ ∈ π/2 + πℤ`, and `θ` runs through `(-nπ, -(n-1)π)` there);
* `airyAi'_zero_midpoint`: **`|(a_n - b_n)/(a_n - a_{n+1}) - 1/2| ≤ 0.4/n`** for `n ≥ 2`.  Proof: the phases of `a_n, a_{n+1}`
  (`airyZero_phase_r`) and of `b_n` (`airyAi'_zero_phase_of_gap`, label `n + 1/4`) give, in the cubes `u = r³`,
  `u_b - u_n = 3π/4 + O(ε)`, `u_{n+1} - u_n = 3π/2 + O(ε)`, `ε = ρ_n^{-3} ≤ 1/(4.08 n)`; and for `0 < ρ < t`
  `(2/3)(t³ - ρ³)/t ≤ t² - ρ² ≤ (2/3)(t³ - ρ³)/ρ` with `ρ_{n+1}/ρ_n ≤ 1 + 1.63 ε`.

Numerically (mpmath, 30 digits): `(a_n - b_n)/(a_n - a_{n+1}) - 1/2 = 0.0249…/n` (`n = 2…100`: `0.0221, 0.0229, …, 0.02472`),
inside the proved `0.4/n`.  General Clark nodes `α ≢ 0, π/2`: the labelling by gaps is `AiryClarkLabel` and the half-way location, the fraction `1/2 + O(n^{-1/3})`, is
`AiryClarkLabelAsym`.  Not formalised: the node phase `kπ + π/4 + O(y^{-1/2})` itself.
-/

@[expose] public section

open Set
open scoped Real

namespace FormalResearch.Special

open SturmAiry

/-- **Exactly one zero of `Ai'` in `(a_{n+1}, a_n)`** (`n ≥ 1`). -/
theorem airyAi'_existsUnique_zero_gap {n : ℕ} (hn : 1 ≤ n) :
    ∃! b : ℝ, airyZero (n + 1) < b ∧ b < airyZero n ∧ airyAi' b = 0 := by
  obtain ⟨θ, hθ, hlo, hhi, -⟩ := airy_exists_prufer
  have h0 : 0 < θ 0 := by linarith [Real.pi_pos]
  obtain ⟨b, hb1, hb2, hb3, hbθ⟩ := airy_exists_airyAi'_zero hθ h0 hhi hlo hn
  refine ⟨b, ⟨hb1, hb2, hb3⟩, ?_⟩
  rintro b' ⟨h1, h2, h3⟩
  have hmono := airyPrufer_mono hθ
  have hb'le : b' ∈ Iic (0 : ℝ) := (h2.le.trans (airyZero_nonpos n))
  have hble : b ∈ Iic (0 : ℝ) := (hb2.le.trans (airyZero_nonpos n))
  have hcombo : combo (π / 2) airyAi airyAi' b' = 0 := by simp [combo, h3]
  obtain ⟨m, hm⟩ := (hθ.combo_eq_zero_iff (π / 2) b').1 hcombo
  have hθa := airy_prufer_airyZero hθ h0 hhi hn
  have hθa' := airy_prufer_airyZero hθ h0 hhi (by omega : 1 ≤ n + 1)
  have hl : θ (airyZero (n + 1)) < θ b' := hmono (airyZero_nonpos _) hb'le h1
  have hu : θ b' < θ (airyZero n) := hmono hb'le (airyZero_nonpos n) h2
  rw [hθa'] at hl; rw [hθa] at hu
  push_cast at hl
  have hm1 : (-(n : ℝ)) - 1 / 2 < m := by
    by_contra hc; push Not at hc
    nlinarith [Real.pi_pos]
  have hm2 : (m : ℝ) < -(n : ℝ) + 1 / 2 := by
    by_contra hc; push Not at hc
    nlinarith [Real.pi_pos]
  have hmn : m = -(n : ℤ) := by
    have h1' : (-(n : ℤ)) - 1 < m := by
      have : (-(n : ℝ)) - 1 < m := by linarith
      exact_mod_cast this
    have h2' : m < -(n : ℤ) + 1 := by
      have : (m : ℝ) < -(n : ℝ) + 1 := by linarith
      exact_mod_cast this
    omega
  have : θ b' = θ b := by rw [hbθ, hm, hmn]; push_cast; ring
  exact hmono.injOn hb'le hble this

/-- `0 < ρ < t`: `(2/3)(t³ - ρ³) ≤ t (t² - ρ²)` and `ρ (t² - ρ²) ≤ (2/3)(t³ - ρ³)`. -/
lemma airyClark_sq_cube {ρ t : ℝ} (hρ : 0 < ρ) (hρt : ρ < t) :
    2 / 3 * (t ^ 3 - ρ ^ 3) ≤ t * (t ^ 2 - ρ ^ 2) ∧ ρ * (t ^ 2 - ρ ^ 2) ≤ 2 / 3 * (t ^ 3 - ρ ^ 3) := by
  have hd : 0 ≤ t - ρ := by linarith
  constructor
  · nlinarith [mul_nonneg (sq_nonneg (t - ρ)) (by linarith : 0 ≤ t + 2 * ρ)]
  · nlinarith [mul_nonneg (sq_nonneg (t - ρ)) (by linarith : 0 ≤ 2 * t + ρ)]

lemma airyMid_key_lower {P ε A Q : ℝ} (hP : 3.14 < P) (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8)
    (hA : 0.75 * P - 2.28 * ε ≤ A) (hQ : Q ≤ 1.5 * P + 1.2 * ε) :
    (1 / 2 - 1.6 * ε) * Q * (1 + 1.63 * ε) ≤ A := by
  have hc : 0 ≤ (1 / 2 - 1.6 * ε) * (1 + 1.63 * ε) := by
    apply mul_nonneg <;> linarith
  have h1 : (1 / 2 - 1.6 * ε) * Q * (1 + 1.63 * ε) ≤
      (1 / 2 - 1.6 * ε) * (1.5 * P + 1.2 * ε) * (1 + 1.63 * ε) := by
    have := mul_le_mul_of_nonneg_left hQ hc
    nlinarith
  have h2 : (1 / 2 - 1.6 * ε) * (1.5 * P + 1.2 * ε) * (1 + 1.63 * ε) ≤ 0.75 * P - 2.28 * ε := by
    nlinarith [mul_pos hε0 hε0, mul_pos hε0 (mul_pos hε0 hε0), mul_pos hε0 (by linarith : 0 < P - 3.14),
      mul_pos (mul_pos hε0 hε0) (by linarith : 0 < P - 3.14)]
  linarith

lemma airyMid_key_upper {P ε A Q : ℝ} (hP : 3.14 < P) (hε0 : 0 < ε) (hε8 : ε ≤ 1 / 8)
    (hA : A ≤ 0.75 * P + 2.28 * ε) (hQ : 1.5 * P - 1.2 * ε ≤ Q) :
    A * (1 + 1.63 * ε) ≤ (1 / 2 + 1.6 * ε) * Q := by
  have h1 : A * (1 + 1.63 * ε) ≤ (0.75 * P + 2.28 * ε) * (1 + 1.63 * ε) :=
    mul_le_mul_of_nonneg_right hA (by linarith)
  have h2 : (1 / 2 + 1.6 * ε) * (1.5 * P - 1.2 * ε) ≤ (1 / 2 + 1.6 * ε) * Q :=
    mul_le_mul_of_nonneg_left hQ (by linarith)
  have h3 : (0.75 * P + 2.28 * ε) * (1 + 1.63 * ε) ≤ (1 / 2 + 1.6 * ε) * (1.5 * P - 1.2 * ε) := by
    nlinarith [mul_pos hε0 hε0, mul_pos hε0 (by linarith : 0 < P - 3.14),
      mul_nonneg hε0.le (by linarith : 0 ≤ 1 / 8 - ε)]
  linarith

lemma airyMid_sigma_le {ρ σ ε : ℝ} (hρ : 0 < ρ) (hε0 : 0 < ε) (hρε : ρ ^ 3 * ε = 1)
    (h : σ ^ 3 ≤ ρ ^ 3 + 4.87) : σ ≤ ρ * (1 + 1.63 * ε) := by
  by_contra hcon
  push Not at hcon
  have h3 : (ρ * (1 + 1.63 * ε)) ^ 3 < σ ^ 3 := pow_lt_pow_left₀ hcon (by positivity) (by norm_num : 3 ≠ 0)
  have e : (ρ * (1 + 1.63 * ε)) ^ 3 = ρ ^ 3 + 4.89 * (ρ ^ 3 * ε) + 3 * 1.63 ^ 2 * ε * (ρ ^ 3 * ε) +
      1.63 ^ 3 * ε ^ 2 * (ρ ^ 3 * ε) := by ring
  rw [e, hρε] at h3
  nlinarith [mul_pos hε0 hε0, pow_pos hε0 2]

lemma airyMid_lower_ratio {ρ τ κ c A Q x y : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hc : 0 ≤ c) (hx : 0 ≤ x)
    (s1 : 2 / 3 * A ≤ τ * x) (s4 : ρ * y ≤ 2 / 3 * Q) (hτ : τ ≤ ρ * κ) (key : c * Q * κ ≤ A) :
    c * y ≤ x := by
  have h1 : 2 * A ≤ 3 * (ρ * κ) * x := by
    have := mul_le_mul_of_nonneg_right hτ hx
    linarith
  have h2 : (c * κ) * (3 * (ρ * y)) ≤ (c * κ) * (3 * (2 / 3 * Q)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have : 3 * (ρ * κ) * (c * y) ≤ 3 * (ρ * κ) * x := by
    calc 3 * (ρ * κ) * (c * y) = (c * κ) * (3 * (ρ * y)) := by ring
      _ ≤ (c * κ) * (3 * (2 / 3 * Q)) := h2
      _ = 2 * (c * Q * κ) := by ring
      _ ≤ 2 * A := by linarith
      _ ≤ 3 * (ρ * κ) * x := h1
  exact le_of_mul_le_mul_left this (by positivity)

lemma airyMid_upper_ratio {ρ σ κ c A Q x y : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ) (hc : 0 ≤ c) (hy : 0 ≤ y)
    (s2 : ρ * x ≤ 2 / 3 * A) (s3 : 2 / 3 * Q ≤ σ * y) (hσ : σ ≤ ρ * κ) (key : A * κ ≤ c * Q) :
    x ≤ c * y := by
  have h2 : 2 * Q ≤ 3 * (ρ * κ) * y := by
    have := mul_le_mul_of_nonneg_right hσ hy
    linarith
  have h3 : κ * (3 * (ρ * x)) ≤ κ * (3 * (2 / 3 * A)) :=
    mul_le_mul_of_nonneg_left (by linarith) hκ.le
  have : 3 * (ρ * κ) * x ≤ 3 * (ρ * κ) * (c * y) := by
    calc 3 * (ρ * κ) * x = κ * (3 * (ρ * x)) := by ring
      _ ≤ κ * (3 * (2 / 3 * A)) := h3
      _ = 2 * (A * κ) := by ring
      _ ≤ 2 * (c * Q) := by linarith
      _ = c * (2 * Q) := by ring
      _ ≤ c * (3 * (ρ * κ) * y) := mul_le_mul_of_nonneg_left h2 hc
      _ = 3 * (ρ * κ) * (c * y) := by ring
  exact le_of_mul_le_mul_left this (by positivity)

/-- Pure-real core of the midpoint estimate. -/
lemma airyMid_core {ρ τ σ ε P N : ℝ} (hρ : 2 < ρ) (hρτ : ρ < τ) (hτσ : τ < σ) (hP : 3.14 < P)
    (hε : ε = 1 / ρ ^ 3) (hN : 4.08 * N ≤ ρ ^ 3) (hN0 : 0 < N)
    (hA1 : τ ^ 3 - ρ ^ 3 ≤ 0.75 * P + 2.28 * ε) (hA2 : 0.75 * P - 2.28 * ε ≤ τ ^ 3 - ρ ^ 3)
    (hQ1 : 1.5 * P - 1.2 * ε ≤ σ ^ 3 - ρ ^ 3) (hQ2 : σ ^ 3 - ρ ^ 3 ≤ 1.5 * P + 1.2 * ε)
    (hQd : σ ^ 3 - ρ ^ 3 ≤ 4.87) :
    |(τ ^ 2 - ρ ^ 2) / (σ ^ 2 - ρ ^ 2) - 1 / 2| ≤ 0.4 / N := by
  have hρ0 : 0 < ρ := by linarith
  have hσ0 : 0 < σ := by linarith
  have hρ3 : 8 < ρ ^ 3 := by nlinarith [pow_lt_pow_left₀ hρ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : 3 ≠ 0)]
  have hρ3pos : 0 < ρ ^ 3 := by positivity
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε8 : ε ≤ 1 / 8 := by rw [hε]; exact one_div_le_one_div_of_le (by norm_num) hρ3.le
  have hρε : ρ ^ 3 * ε = 1 := by rw [hε]; field_simp
  have hεN : 1.6 * ε ≤ 0.4 / N := by
    rw [le_div_iff₀ hN0, hε, mul_one_div, div_mul_eq_mul_div, div_le_iff₀ hρ3pos]
    linarith
  have hκ : σ ≤ ρ * (1 + 1.63 * ε) := airyMid_sigma_le hρ0 hε0 hρε (by linarith)
  have hτκ : τ ≤ ρ * (1 + 1.63 * ε) := hτσ.le.trans hκ
  obtain ⟨s1, s2⟩ := airyClark_sq_cube hρ0 hρτ
  obtain ⟨s3, s4⟩ := airyClark_sq_cube hρ0 (hρτ.trans hτσ)
  have hy0 : 0 < σ ^ 2 - ρ ^ 2 := by
    have : ρ ^ 2 < σ ^ 2 := pow_lt_pow_left₀ (hρτ.trans hτσ) hρ0.le (by norm_num : 2 ≠ 0)
    linarith
  have hx0 : 0 ≤ τ ^ 2 - ρ ^ 2 := by
    have : ρ ^ 2 < τ ^ 2 := pow_lt_pow_left₀ hρτ hρ0.le (by norm_num : 2 ≠ 0)
    linarith
  have hκ0 : 0 < 1 + 1.63 * ε := by positivity
  rw [abs_le]
  constructor
  · have key := airyMid_key_lower hP hε0 hε8 hA2 hQ2
    have h3 := airyMid_lower_ratio hρ0 hκ0 (by linarith : 0 ≤ 1 / 2 - 1.6 * ε) hx0 s1 s4 hτκ key
    have : -(0.4 / N) + 1 / 2 ≤ (τ ^ 2 - ρ ^ 2) / (σ ^ 2 - ρ ^ 2) := by
      rw [le_div_iff₀ hy0]
      have := mul_le_mul_of_nonneg_right (by linarith : -(0.4 / N) + 1 / 2 ≤ 1 / 2 - 1.6 * ε) hy0.le
      linarith
    linarith
  · have key := airyMid_key_upper hP hε0 hε8 hA1 hQ1
    have h3 := airyMid_upper_ratio hρ0 hκ0 (by linarith : 0 ≤ 1 / 2 + 1.6 * ε) hy0.le s2 s3 hκ key
    have : (τ ^ 2 - ρ ^ 2) / (σ ^ 2 - ρ ^ 2) ≤ 1 / 2 + 0.4 / N := by
      rw [div_le_iff₀ hy0]
      have := mul_le_mul_of_nonneg_right (by linarith : 1 / 2 + 1.6 * ε ≤ 1 / 2 + 0.4 / N) hy0.le
      linarith
    linarith

/-- **The zero of `Ai'` in the gap is asymptotically the midpoint**: for `n ≥ 2` and any zero `b ∈ (a_{n+1}, a_n)` of `Ai'`,
`|(a_n - b)/(a_n - a_{n+1}) - 1/2| ≤ 0.4/n`. -/
theorem airyAi'_zero_midpoint {n : ℕ} (hn : 2 ≤ n) {b : ℝ} (hb1 : airyZero (n + 1) < b)
    (hb2 : b < airyZero n) (hz : airyAi' b = 0) :
    |(airyZero n - b) / (airyZero n - airyZero (n + 1)) - 1 / 2| ≤ 0.4 / n := by
  obtain ⟨hρτ, hτσ, hτ1, -⟩ := airyAi'_zero_phase_of_gap hn hb1 hb2 hz
  have hbneg : b < 0 := hb2.trans (airyZero_neg n)
  obtain ⟨hp1, hp2⟩ := airyFZ_pi_bounds
  have hxa : airyZero n - b = (√(-b)) ^ 2 - airyZeroRoot n ^ 2 := by
    rw [Real.sq_sqrt (neg_nonneg.mpr hbneg.le), airyZero_eq_neg_root_sq n]; ring
  have hya : airyZero n - airyZero (n + 1) = airyZeroRoot (n + 1) ^ 2 - airyZeroRoot n ^ 2 := by
    rw [airyZero_eq_neg_root_sq n, airyZero_eq_neg_root_sq (n + 1)]; ring
  rw [hxa, hya]
  have pρ := abs_le.mp (airyZero_phase_r hn)
  have pσ := abs_le.mp (airyZero_phase_r (by omega : 2 ≤ n + 1))
  have pτ := abs_le.mp hτ1
  have hρ2 : 2 < airyZeroRoot n := two_lt_airyZeroRoot hn
  have hdel := airyZero_delta_bounds hn
  obtain ⟨hc1, -⟩ := airyZero_cube_bounds hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  generalize √(-b) = τ at *
  generalize airyZeroRoot n = ρ at *
  generalize airyZeroRoot (n + 1) = σ at *
  have hρ0 : 0 < ρ := by linarith
  have hτ0 : 0 < τ := by linarith
  have hρ3pos : 0 < ρ ^ 3 := by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = 1 / ρ ^ 3 := ⟨_, rfl⟩
  have hτ3 : ρ ^ 3 < τ ^ 3 := pow_lt_pow_left₀ hρτ hρ0.le (by norm_num : 3 ≠ 0)
  have hσ3 : τ ^ 3 < σ ^ 3 := pow_lt_pow_left₀ hτσ hτ0.le (by norm_num : 3 ≠ 0)
  have hτε : 1 / τ ^ 3 ≤ ε := by rw [hεdef]; exact one_div_le_one_div_of_le hρ3pos hτ3.le
  have hσε : 1 / σ ^ 3 ≤ ε := by rw [hεdef]; exact one_div_le_one_div_of_le hρ3pos (hτ3.trans hσ3).le
  have e1 : 2 / 5 / ρ ^ 3 = 2 / 5 * ε := by rw [hεdef]; ring
  have e2 : 2 / 5 / σ ^ 3 ≤ 2 / 5 * ε := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hσε (by norm_num)
  have e3 : 1.12 / τ ^ 3 ≤ 1.12 * ε := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hτε (by norm_num)
  rw [e1] at pρ
  push_cast at pσ
  exact airyMid_core (P := π) (ε := ε) (N := n) hρ2 hρτ hτσ (by linarith) hεdef hc1 hn' (by linarith [pρ.1, pρ.2, pτ.1, pτ.2])
    (by linarith [pρ.1, pρ.2, pτ.1, pτ.2]) (by linarith [pρ.1, pρ.2, pσ.1, pσ.2])
    (by linarith [pρ.1, pρ.2, pσ.1, pσ.2]) hdel.2

/-- info: 'FormalResearch.Special.airyAi'_existsUnique_zero_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_existsUnique_zero_gap

/-- info: 'FormalResearch.Special.airyAi'_zero_midpoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyAi'_zero_midpoint

end FormalResearch.Special

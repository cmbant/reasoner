module

public import FormalResearch.Special.AiryCftCircle
public import FormalResearch.Special.AiryRatioBounds
public import FormalResearch.Special.AiryZeroSpacing
public import FormalResearch.Special.AiryBiReal

/-!
# Good circles as `CftCircleData` for `Ai`: zero bookkeeping and the bound `|Ai'/Ai| ≤ 45 √(1+r)`

Inputs of `AiryCftMittagLeffler` (CFT/PR240 notes, Mittag-Leffler / Hadamard expansion of `Ai'/Ai`).

* `airyAiC_eq_zero_iff`: the zeros of `Ai` in `ℂ` are exactly `a_n = airyZero n`, `n ≥ 1`;
* `airyZero_deriv_ne_zero`: `Ai'(a_n) ≠ 0` (simple zeros; the Wronskian `Ai Bi' - Ai' Bi = 1/π`);
* `airyZero_split`: every radius `R` splits the zero list at some `N` (`n ≤ N ↔ |a_n| < R`);
* `airy_logDeriv_norm_le`: on a good circle `|u| = r`: `‖Ai'(u)/Ai(u)‖ ≤ 45 √(1+r)`
  (from the squared envelope (E1') and the good-circle lower bound; `625π ≤ 45²`; the constant is not sharp, the
  classical size is `|Ai'/Ai| ~ |u|^{1/2}`);
* `airy_circleData_exists`: for each `k ≥ 10` a good radius `r ∈ [k, k+1]` and `N` with
  `CftCircleData Ai a (Icc 1 N) r` and the splitting property.

All proved.  Numerical check of the constant (mpmath, 20 digits, `k ∈ {10, …, 40}`, good radii `(2/3) r^{3/2} ∈ π/4 + πℕ`,
73 angles on the upper half circle, the lower half by conjugation): the maximum of `‖Ai'/Ai‖ / √(1+r)` is `0.989`
(`|Ai'/Ai| ≈ √|u|`), far inside the proved `45`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real

namespace FormalResearch.Special

/-- The zeros of `Ai` in `ℂ` are exactly the `a_n`, `n ≥ 1` (real, negative, and listed by `airyZero`). -/
theorem airyAiC_eq_zero_iff (w : ℂ) : airyAiC w = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ w = (airyZero n : ℂ) := by
  constructor
  · intro h
    obtain ⟨him, hre⟩ := airyAiC_zero_real_neg h
    have hw : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hw, airyAiC_ofReal] at h
    have h' : airyAi w.re = 0 := by exact_mod_cast h
    obtain ⟨n, hn, hwn⟩ := exists_airyZero_eq h' hre.le
    exact ⟨n, hn, by rw [hw, hwn]⟩
  · rintro ⟨n, -, rfl⟩
    rw [airyAiC_ofReal, airyAi_airyZero]; simp

/-- Simple zeros: `Ai'(a_n) ≠ 0`. -/
theorem airyZero_deriv_ne_zero (n : ℕ) : deriv airyAiC (airyZero n : ℂ) ≠ 0 := by
  intro h
  have hW := airyAiC_wronskian_airyBiC_eq (airyZero n : ℂ)
  rw [airyAiC_ofReal, airyAi_airyZero, h] at hW
  simp at hW
  exact Real.pi_ne_zero (by exact_mod_cast hW.symm)

/-- `Ai'` has no zero in common with `Ai` (real axis form). -/
theorem airyAi_ne_zero_of_deriv_zero {x : ℝ} (h : airyAi' x = 0) : airyAi x ≠ 0 := by
  intro h0
  have := airyWronskian_real x
  rw [h, h0] at this
  simp at this
  exact Real.pi_ne_zero this.symm

lemma airyZero_injOn : Set.InjOn airyZero (Set.Ici 1) := by
  intro m hm n hn h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := airyZero_lt_of_lt (Set.mem_Ici.mp hm) hlt; linarith
  · have := airyZero_lt_of_lt (Set.mem_Ici.mp hn) hlt; linarith

lemma airyZero_anti {m n : ℕ} (hm : 1 ≤ m) (h : m ≤ n) : airyZero n ≤ airyZero m := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (airyZero_lt_of_lt hm h).le

/-- `|a_n|` is unbounded: for every `R` some `a_n` (`n ≥ 2`) has `R ≤ -a_n`. -/
lemma airyZero_exists_abs_ge (R : ℝ) : ∃ n : ℕ, 2 ≤ n ∧ R ≤ -airyZero n := by
  obtain ⟨n, hn⟩ := exists_nat_ge (max R 1 ^ 3)
  refine ⟨n + 2, by omega, ?_⟩
  have h2 : 2 ≤ n + 2 := by omega
  have hb := (airyZero_abs_cube_bounds h2).1
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hR1 : 1 ≤ max R 1 := le_max_right _ _
  have hm : max R 1 ^ 3 ≤ (n : ℝ) := hn
  have hcube : max R 1 ^ 3 ≤ (-airyZero (n + 2)) ^ 3 := by
    push_cast at hb
    nlinarith [sq_nonneg ((n : ℝ) + 2)]
  have hy : 0 ≤ -airyZero (n + 2) := (neg_pos.mpr (airyZero_neg _)).le
  have := le_of_pow_le_pow_left₀ (by norm_num : (3 : ℕ) ≠ 0) hy hcube
  exact (le_max_left R 1).trans this

/-- Every radius `R` splits the zero list: `n ≤ N ↔ |a_n| < R` for `n ≥ 1`. -/
theorem airyZero_split (R : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R) := by
  classical
  have hex : ∃ k : ℕ, R ≤ -airyZero (k + 1) := by
    obtain ⟨n, hn, h⟩ := airyZero_exists_abs_ge R
    exact ⟨n - 1, by rwa [Nat.sub_add_cancel (by omega)]⟩
  refine ⟨Nat.find hex, fun n hn => ?_⟩
  constructor
  · intro hnN
    have := Nat.find_min hex (show n - 1 < Nat.find hex by omega)
    rw [Nat.sub_add_cancel hn] at this
    exact not_le.mp this
  · intro hlt
    by_contra hnN
    have h1 : Nat.find hex + 1 ≤ n := by omega
    have h2 := airyZero_anti (by omega) h1
    have h3 := Nat.find_spec hex
    linarith

/-- **`CftCircleData` for `Ai`** on a zero-free circle. -/
theorem airy_circleData {R : ℝ} (hR : 0 < R) (hgood : ∀ u : ℂ, ‖u‖ = R → airyAiC u ≠ 0) :
    ∃ N : ℕ, (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < R)) ∧
      CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) R := by
  have hne : ∀ n : ℕ, 1 ≤ n → R ≠ -airyZero n := by
    intro n hn h
    apply hgood (airyZero n : ℂ)
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg n)]; linarith
    · rw [airyAiC_ofReal, airyAi_airyZero]; simp
  obtain ⟨N, hN⟩ := airyZero_split R
  refine ⟨N, hN, ?_⟩
  refine ⟨differentiable_airyAiC, hR, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi j hj h
    exact airyZero_injOn (Set.mem_Ici.mpr (Finset.mem_Icc.mp hi).1) (Set.mem_Ici.mpr (Finset.mem_Icc.mp hj).1)
      (by simpa using h)
  · intro i hi
    have hi' := Finset.mem_Icc.mp hi
    have := (hN i hi'.1).mp hi'.2
    rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg i)]
  · intro i _
    rw [airyAiC_ofReal, airyAi_airyZero]; simp
  · intro i _; exact airyZero_deriv_ne_zero i
  · intro w hw h0
    obtain ⟨n, hn, rfl⟩ := (airyAiC_eq_zero_iff w).mp h0
    refine ⟨n, Finset.mem_Icc.mpr ⟨hn, ?_⟩, rfl⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (airyZero_neg n)] at hw
    by_contra hnN
    have h1 : ¬ (-airyZero n < R) := fun h => hnN ((hN n hn).mpr h)
    exact hne n hn (le_antisymm (not_lt.mp h1) hw)

/-- Squared derivative envelope: `‖Ai'(z)‖² ≤ 25 (1 + |z|)^{1/2} e(z)`. -/
lemma airyCft_deriv_norm_sq_le (z : ℂ) :
    ‖deriv airyAiC z‖ ^ 2 ≤ 25 * (1 + ‖z‖) ^ (1 / 2 : ℝ) * airyEnv z := by
  have h := airyAiC_deriv_envelope z
  have h0 := norm_nonneg (deriv airyAiC z)
  have h1 := pow_le_pow_left₀ h0 h 2
  refine h1.trans (le_of_eq ?_)
  have e1 : ((1 + ‖z‖) ^ (1 / 4 : ℝ)) ^ 2 = (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  have e2 : (Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2 = airyEnv z := by
    rw [airyEnv, ← Real.exp_nat_mul]; norm_num; ring_nf
  calc (5 * (1 + ‖z‖) ^ (1 / 4 : ℝ) * Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2
      = 25 * ((1 + ‖z‖) ^ (1 / 4 : ℝ)) ^ 2 * (Real.exp (-(2 / 3) * (z ^ (3 / 2 : ℂ)).re)) ^ 2 := by
        ring
    _ = _ := by rw [e1, e2]

/-- **`‖Ai'/Ai‖ ≤ 45 √(1+r)` on a good circle** (`‖u‖ = r`, with the good-circle lower bound for `‖Ai‖²`). -/
theorem airy_logDeriv_norm_le {u : ℂ} {r : ℝ} (hu : ‖u‖ = r) (hr : 0 ≤ r)
    (hlb : 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u ≤ ‖airyAiC u‖ ^ 2) :
    ‖logDeriv airyAiC u‖ ≤ 45 * √(1 + r) := by
  have hpos : 0 < 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u := by
    have := airyEnv_pos u
    have : 0 < (1 + r) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    positivity
  have hAi : 0 < ‖airyAiC u‖ := by
    refine norm_pos_iff.mpr fun h => ?_
    rw [h, norm_zero] at hlb
    linarith
  have hd := airyCft_deriv_norm_sq_le u
  rw [hu] at hd
  set a : ℝ := √(1 + r) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have haa : a * a = 1 + r := Real.mul_self_sqrt (by linarith)
  have e1 : (1 + r) ^ (1 / 2 : ℝ) = a := by rw [ha, Real.sqrt_eq_rpow]
  have e2 : (1 + r) ^ (-(1 / 2) : ℝ) = a⁻¹ := by rw [Real.rpow_neg (by linarith), ← e1]
  rw [e1] at hd
  rw [e2] at hlb
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  rw [logDeriv_apply, norm_div, div_le_iff₀ hAi]
  have hen := airyEnv_pos u
  -- squares
  refine le_of_sq_le_sq ?_ (by positivity)
  have h2 : (45 * a * ‖airyAiC u‖) ^ 2 ≥ 25 * a * airyEnv u := by
    have h3 : 2025 * a ^ 2 * (1 / (25 * π) * a⁻¹ * airyEnv u) ≤ 2025 * a ^ 2 * ‖airyAiC u‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hlb (by positivity)
    have h4 : 2025 * a ^ 2 * (1 / (25 * π) * a⁻¹ * airyEnv u) = 81 / π * a * airyEnv u := by
      field_simp
      norm_num
    have h5 : 25 ≤ 81 / π := by rw [le_div_iff₀ hpi0]; nlinarith
    calc 25 * a * airyEnv u ≤ 81 / π * a * airyEnv u := by gcongr
      _ = _ := h4.symm
      _ ≤ _ := h3
      _ = _ := by ring
  calc ‖deriv airyAiC u‖ ^ 2 ≤ 25 * a * airyEnv u := hd
    _ ≤ _ := h2
    _ = _ := by ring

/-- **Good circles as `CftCircleData`.** For each `k ≥ 10` there are `r ∈ [k, k+1]` and `N` such that the zeros of `Ai`
in `|w| ≤ r` are `a_1, …, a_N` (`n ≤ N ↔ |a_n| < r`), `CftCircleData Ai a (Icc 1 N) r`, and `‖Ai'/Ai‖ ≤ 45 √(1+r)`
on `|u| = r`. -/
theorem airy_circleData_exists (k : ℕ) (hk : 10 ≤ k) :
    ∃ r : ℝ, (k : ℝ) ≤ r ∧ r ≤ k + 1 ∧ ∃ N : ℕ,
      (∀ n : ℕ, 1 ≤ n → (n ≤ N ↔ -airyZero n < r)) ∧
      CftCircleData airyAiC (fun n => (airyZero n : ℂ)) (Finset.Icc 1 N) r ∧
      ∀ u : ℂ, ‖u‖ = r → ‖logDeriv airyAiC u‖ ≤ 45 * √(1 + r) := by
  obtain ⟨r, h1, h2, h⟩ := good_circle_exists k hk
  have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hr : 0 < r := by linarith
  have hgood : ∀ u : ℂ, ‖u‖ = r → airyAiC u ≠ 0 := by
    intro u hu h0
    have := h u hu
    rw [h0, norm_zero] at this
    have : 0 < 1 / (25 * π) * (1 + r) ^ (-(1 / 2) : ℝ) * airyEnv u := by
      have := airyEnv_pos u
      have : 0 < (1 + r) ^ (-(1 / 2) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    linarith
  obtain ⟨N, hN, hD⟩ := airy_circleData hr hgood
  exact ⟨r, h1, h2, N, hN, hD, fun u hu => airy_logDeriv_norm_le hu hr.le (h u hu)⟩

/-- info: 'FormalResearch.Special.airy_circleData_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_circleData_exists

end FormalResearch.Special

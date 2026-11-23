module

public import FormalResearch.ModularBootstrap.Upper.Ramped.CombToAiryDef
public import FormalResearch.ModularBootstrap.Upper.Comb.Factors
public import FormalResearch.ModularBootstrap.Upper.Ramped.LangerKernelAux
public import FormalResearch.ModularBootstrap.Upper.Window.LemmaR

/-!
# One pair of the comb against its Airy model: Step 3 of Proposition 1.2(2) (`rem:P1.2`)

For a pair `χ' ± iε'` and a real point `x` the detuning `δ = log(q'/(tanh tanh)²)` splits exactly as
`δ = log(1 + B) + R`, `B = S²/sinh² z_-`, `S = sin(πε'/2)`, `z_- = π(x - χ')/2`, with a remainder
`0 ≤ R ≤ C ε'² e^{-π|x - χ'|}` (`detuneRem_bounds`).  The model weight is `A = ε̃²/(τ(x) - τ(χ'))²`,
`ε̃ = ε' τ'(ζ)` for a point `ζ` within `s` of `χ'`; for a near pair `|x - χ'| ≤ 1/10` one has
`|log(1+B) - log(1+A)| ≤ C (ε'² + |x - χ'| + s) T`, `T = A/(1+A)` (`near_log_bound`, `tau_sub_formula`).
-/

@[expose] public section

open Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Ramped

open FormalResearch.ModularBootstrap.Upper.Comb

/-- `B = sin²(πε/2)/sinh²(π(x - y)/2)`. -/
noncomputable def pairB (y ε x : ℝ) : ℝ :=
  Real.sin (π * ε / 2) ^ 2 / Real.sinh (π * (x - y) / 2) ^ 2

/-- The remainder `R` of the exact split `δ = log(1 + B) + R`. -/
noncomputable def detuneRem (y ε x : ℝ) : ℝ :=
  Real.log (1 + Real.sin (π * ε / 2) ^ 2 / Real.sinh (π * (x + y) / 2) ^ 2) -
    Real.log (1 - Real.sin (π * ε / 2) ^ 2 / Real.cosh (π * (x - y) / 2) ^ 2) -
    Real.log (1 - Real.sin (π * ε / 2) ^ 2 / Real.cosh (π * (x + y) / 2) ^ 2)

lemma sin_sq_le_small {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 8) :
    Real.sin (π * ε / 2) ^ 2 ≤ (π * ε / 2) ^ 2 ∧ Real.sin (π * ε / 2) ^ 2 ≤ 0.04 := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ Real.sin (π * ε / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith [Real.pi_lt_d4])
  have h1 : Real.sin (π * ε / 2) ≤ π * ε / 2 := Real.sin_le (by positivity)
  refine ⟨by nlinarith, ?_⟩
  have hpi4 : π ≤ 3.15 := by linarith [Real.pi_lt_d4]
  have hpe : 0 ≤ π * ε / 2 := by positivity
  have hpe_le : π * ε / 2 ≤ 3.15 / 16 := by nlinarith
  nlinarith

/-- The exact split of the detuning. -/
lemma deltaDetune_eq_add {y ε x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) (hd : x ≠ y) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 8) :
    deltaDetune y ε x = Real.log (1 + pairB y ε x) + detuneRem y ε x := by
  have hpi := Real.pi_pos
  set z₁ := π * (x - y) / 2
  set z₂ := π * (x + y) / 2
  set S := Real.sin (π * ε / 2)
  have hxy : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (fun h0 => hd (by linarith))
  have hz₁ : z₁ ≠ 0 := by
    dsimp [z₁]; exact div_ne_zero (mul_ne_zero hpi.ne' (sub_ne_zero.mpr hd)) two_ne_zero
  have hz₂ : 0 < z₂ := by dsimp [z₂]; positivity
  have hs1 : Real.sinh z₁ ≠ 0 := Real.sinh_ne_zero.mpr hz₁
  have hs2 : Real.sinh z₂ ≠ 0 := (Real.sinh_pos_iff.mpr hz₂).ne'
  have hc1 := Real.cosh_pos z₁
  have hc2 := Real.cosh_pos z₂
  have hS := (sin_sq_le_small hε0 hε).2
  have hu1 : 0 < 1 - S ^ 2 / Real.cosh z₁ ^ 2 := by
    have : S ^ 2 / Real.cosh z₁ ^ 2 ≤ S ^ 2 :=
      div_le_self (sq_nonneg _) (by have := Real.one_le_cosh z₁; nlinarith)
    linarith
  have hu2 : 0 < 1 - S ^ 2 / Real.cosh z₂ ^ 2 := by
    have : S ^ 2 / Real.cosh z₂ ^ 2 ≤ S ^ 2 :=
      div_le_self (sq_nonneg _) (by have := Real.one_le_cosh z₂; nlinarith)
    linarith
  have hv1 : 0 < 1 + S ^ 2 / Real.sinh z₁ ^ 2 := by positivity
  have hv2 : 0 < 1 + S ^ 2 / Real.sinh z₂ ^ 2 := by positivity
  have hq : blaschkePairQ y ε x / (Real.tanh z₁ * Real.tanh z₂) ^ 2 =
      ((1 + S ^ 2 / Real.sinh z₁ ^ 2) / (1 - S ^ 2 / Real.cosh z₁ ^ 2)) *
        ((1 + S ^ 2 / Real.sinh z₂ ^ 2) / (1 - S ^ 2 / Real.cosh z₂ ^ 2)) := by
    rw [blaschkePairQ_eq, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh]
    field_simp [hs1, hs2, hc1.ne', hc2.ne']
    ring
  unfold deltaDetune detuneRem pairB
  rw [hq, Real.log_mul (by positivity) (by positivity),
    Real.log_div hv1.ne' hu1.ne', Real.log_div hv2.ne' hu2.ne']
  ring

lemma neg_log_one_sub_le' {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 0.04) : -Real.log (1 - u) ≤ 1.05 * u := by
  have h1 : 0 < 1 - u := by linarith
  have h2 : -Real.log (1 - u) = Real.log (1 - u)⁻¹ := by rw [Real.log_inv]
  rw [h2]
  refine (Real.log_le_sub_one_of_pos (inv_pos.mpr h1)).trans ?_
  have : (1 - u)⁻¹ - 1 = u / (1 - u) := by field_simp; ring
  rw [this, div_le_iff₀ h1]
  nlinarith

lemma cosh_sq_ge (z : ℝ) : Real.exp (2 * |z|) / 4 ≤ Real.cosh z ^ 2 := by
  have h1 : Real.exp |z| / 2 ≤ Real.cosh z := by
    have hc : Real.cosh |z| = Real.cosh z := by
      rcases le_or_gt 0 z with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, Real.cosh_neg]
    rw [← hc, Real.cosh_eq]
    linarith [Real.exp_pos (-|z|)]
  have h2 : (Real.exp |z| / 2) ^ 2 ≤ Real.cosh z ^ 2 := by nlinarith [Real.exp_pos |z|]
  rwa [div_pow, ← Real.exp_nat_mul, show (2 : ℕ) * |z| = 2 * |z| by ring,
    show (2 : ℝ) ^ 2 = 4 by norm_num] at h2

/-- `0 ≤ R ≤ C ε² e^{-π d}` for `x ≥ ξ_*/2`, `y ≥ ξ_*`. -/
theorem detuneRem_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ {y ε x : ℝ}, xiStar / 2 ≤ x → xiStar ≤ y → 0 ≤ ε → ε ≤ 1 / 8 →
      0 ≤ detuneRem y ε x ∧ detuneRem y ε x ≤ C * ε ^ 2 * Real.exp (-π * |x - y|) := by
  have hpi := Real.pi_pos
  have hxs := xiStar_pos
  set s0 := π * xiStar / 2 with hs0
  have hs0p : 0 < s0 := by positivity
  set c0 := (1 - Real.exp (-(2 * s0))) / 2 with hc0
  have hc0p : 0 < c0 := by
    have : Real.exp (-(2 * s0)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    rw [hc0]; linarith
  have hsh : ∀ z : ℝ, s0 ≤ z → c0 ^ 2 * Real.exp (2 * z) ≤ Real.sinh z ^ 2 := by
    intro z hz
    have e1 : Real.sinh z = Real.exp z * ((1 - Real.exp (-(2 * z))) / 2) := by
      rw [Real.sinh_eq]
      have : Real.exp (-z) = Real.exp z * Real.exp (-(2 * z)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    have e2 : c0 ≤ (1 - Real.exp (-(2 * z))) / 2 := by
      have : Real.exp (-(2 * z)) ≤ Real.exp (-(2 * s0)) := Real.exp_le_exp.mpr (by linarith)
      rw [hc0]; linarith
    have e3 : Real.exp (2 * z) = Real.exp z ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1
    rw [e1, mul_pow, e3]
    have := Real.exp_pos z
    have e4 : c0 ^ 2 ≤ ((1 - Real.exp (-(2 * z))) / 2) ^ 2 := by gcongr
    nlinarith [sq_nonneg (Real.exp z)]
  refine ⟨π ^ 2 / 4 * (1 / c0 ^ 2 + 1.05 * 4 * 2), by positivity, ?_⟩
  intro y ε x hx hy hε0 hε
  have hS := sin_sq_le_small hε0 hε
  set S := Real.sin (π * ε / 2)
  set z₁ := π * (x - y) / 2
  set z₂ := π * (x + y) / 2
  have hz₂ : s0 ≤ z₂ := by dsimp [z₂, s0]; nlinarith
  have hd1 : π * |x - y| ≤ 2 * |z₁| := by
    dsimp [z₁]; rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]; linarith
  have hd2 : π * |x - y| ≤ 2 * z₂ := by
    have h1 : |x - y| ≤ x + y := by rw [abs_le]; constructor <;> linarith
    dsimp [z₂]; nlinarith
  have hS0 : 0 ≤ S ^ 2 := sq_nonneg _
  have hu : ∀ z : ℝ, π * |x - y| ≤ 2 * |z| →
      0 ≤ S ^ 2 / Real.cosh z ^ 2 ∧ S ^ 2 / Real.cosh z ^ 2 ≤ 0.04 ∧
        1.05 * (S ^ 2 / Real.cosh z ^ 2) ≤ 1.05 * 4 * (π ^ 2 / 4) * ε ^ 2 * Real.exp (-π * |x - y|) := by
    intro z hz
    refine ⟨by positivity, (div_le_self hS0 (by have := Real.one_le_cosh z; nlinarith)).trans hS.2, ?_⟩
    have hc := cosh_sq_ge z
    have hcp : 0 < Real.exp (2 * |z|) / 4 := by positivity
    calc 1.05 * (S ^ 2 / Real.cosh z ^ 2)
        ≤ 1.05 * ((π * ε / 2) ^ 2 / (Real.exp (2 * |z|) / 4)) := by
          have := div_le_div₀ (sq_nonneg (π * ε / 2)) hS.1 hcp hc
          linarith
      _ = 1.05 * 4 * (π ^ 2 / 4) * ε ^ 2 * Real.exp (-(2 * |z|)) := by
          rw [Real.exp_neg]; field_simp; ring
      _ ≤ 1.05 * 4 * (π ^ 2 / 4) * ε ^ 2 * Real.exp (-π * |x - y|) := by
          gcongr
          linarith
  have hz1pos : (0 : ℝ) < z₂ := lt_of_lt_of_le hs0p hz₂
  obtain ⟨u10, u1le, u1b⟩ := hu z₁ hd1
  obtain ⟨u20, u2le, u2b⟩ := hu z₂ (by rw [abs_of_pos hz1pos]; exact hd2)
  have hv : S ^ 2 / Real.sinh z₂ ^ 2 ≤ (π ^ 2 / 4) / c0 ^ 2 * ε ^ 2 * Real.exp (-π * |x - y|) := by
    have hsh2 := hsh z₂ hz₂
    have hp : 0 < c0 ^ 2 * Real.exp (2 * z₂) := by positivity
    calc S ^ 2 / Real.sinh z₂ ^ 2 ≤ (π * ε / 2) ^ 2 / (c0 ^ 2 * Real.exp (2 * z₂)) := by
          exact div_le_div₀ (sq_nonneg _) hS.1 hp hsh2
      _ = (π ^ 2 / 4) / c0 ^ 2 * ε ^ 2 * Real.exp (-(2 * z₂)) := by
          rw [Real.exp_neg]; field_simp; ring
      _ ≤ _ := by gcongr; linarith
  have hv0 : 0 ≤ S ^ 2 / Real.sinh z₂ ^ 2 := by positivity
  have l1 : 0 ≤ Real.log (1 + S ^ 2 / Real.sinh z₂ ^ 2) := Real.log_nonneg (by linarith)
  have l1' : Real.log (1 + S ^ 2 / Real.sinh z₂ ^ 2) ≤ S ^ 2 / Real.sinh z₂ ^ 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + S ^ 2 / Real.sinh z₂ ^ 2 by positivity)
    linarith
  have m1 := neg_log_one_sub_le' u10 u1le
  have m2 := neg_log_one_sub_le' u20 u2le
  have n1 : 0 ≤ -Real.log (1 - S ^ 2 / Real.cosh z₁ ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  have n2 : 0 ≤ -Real.log (1 - S ^ 2 / Real.cosh z₂ ^ 2) :=
    neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  unfold detuneRem
  constructor
  · linarith
  · have e : π ^ 2 / 4 * (1 / c0 ^ 2 + 1.05 * 4 * 2) * ε ^ 2 * Real.exp (-π * |x - y|) =
        (π ^ 2 / 4) / c0 ^ 2 * ε ^ 2 * Real.exp (-π * |x - y|) +
          1.05 * 4 * (π ^ 2 / 4) * ε ^ 2 * Real.exp (-π * |x - y|) +
          1.05 * 4 * (π ^ 2 / 4) * ε ^ 2 * Real.exp (-π * |x - y|) := by ring
    rw [e]
    linarith

/-! ### Near pairs: comparison of `B` with the Airy-model weight `A` -/

lemma sq_le_sinh_sq (u : ℝ) : u ^ 2 ≤ Real.sinh u ^ 2 := by
  rcases le_total 0 u with h | h
  · have := Real.self_le_sinh_iff.mpr h
    nlinarith
  · have h1 := Real.sinh_le_self_iff.mpr h
    nlinarith

lemma sinh_sq_le (u : ℝ) : Real.sinh u ^ 2 ≤ u ^ 2 * Real.exp (u ^ 2) := by
  have h1 : Real.sinh |u| ≤ |u| * Real.cosh |u| := Window.sinh_le_mul_cosh (abs_nonneg u)
  have h2 : Real.cosh |u| ≤ Real.exp (|u| ^ 2 / 2) := Real.cosh_le_exp_half_sq |u|
  have h3 : Real.sinh |u| ^ 2 = Real.sinh u ^ 2 := by
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, Real.sinh_neg, neg_sq]
  have hs0 : 0 ≤ Real.sinh |u| := Real.sinh_nonneg_iff.mpr (abs_nonneg u)
  have h4 : Real.sinh |u| ≤ |u| * Real.exp (|u| ^ 2 / 2) := h1.trans (by gcongr)
  rw [← h3]
  calc Real.sinh |u| ^ 2 ≤ (|u| * Real.exp (|u| ^ 2 / 2)) ^ 2 := by gcongr
    _ = u ^ 2 * Real.exp (u ^ 2) := by
        rw [mul_pow, sq_abs, ← Real.exp_nat_mul]; congr 2; push_cast; ring

lemma div_sinh_bounds {u : ℝ} (hu : u ≠ 0) :
    1 - u ^ 2 ≤ u ^ 2 / Real.sinh u ^ 2 ∧ u ^ 2 / Real.sinh u ^ 2 ≤ 1 := by
  have hu2 : 0 < u ^ 2 := by positivity
  have hs : 0 < Real.sinh u ^ 2 := lt_of_lt_of_le hu2 (sq_le_sinh_sq u)
  refine ⟨?_, (div_le_one hs).mpr (sq_le_sinh_sq u)⟩
  rw [le_div_iff₀ hs]
  rcases le_or_gt (1 - u ^ 2) 0 with h | h
  · nlinarith
  · have h1 := sinh_sq_le u
    have h2 : (1 - u ^ 2) * Real.exp (u ^ 2) ≤ 1 := by
      have := Real.add_one_le_exp (-(u ^ 2))
      have h3 : Real.exp (-(u ^ 2)) * Real.exp (u ^ 2) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (u ^ 2)]
    calc (1 - u ^ 2) * Real.sinh u ^ 2 ≤ (1 - u ^ 2) * (u ^ 2 * Real.exp (u ^ 2)) := by gcongr
      _ = ((1 - u ^ 2) * Real.exp (u ^ 2)) * u ^ 2 := by ring
      _ ≤ 1 * u ^ 2 := by gcongr
      _ = u ^ 2 := one_mul _

lemma sin_div_bounds {e : ℝ} (he0 : 0 < e) (he : e ≤ 1) :
    1 - e ^ 2 / 3 ≤ Real.sin e ^ 2 / e ^ 2 ∧ Real.sin e ^ 2 / e ^ 2 ≤ 1 := by
  have hpi := Real.pi_gt_three
  have h1 : e - e ^ 3 / 6 < Real.sin e := Real.sin_gt_sub_cube he0
  have h2 : Real.sin e ≤ e := Real.sin_le he0.le
  have h3 : 0 ≤ Real.sin e := Real.sin_nonneg_of_nonneg_of_le_pi he0.le (by linarith)
  have he2 : 0 < e ^ 2 := by positivity
  refine ⟨?_, (div_le_one he2).mpr (by nlinarith)⟩
  rw [le_div_iff₀ he2]
  have h4 : 0 ≤ e - e ^ 3 / 6 := by nlinarith
  have h5 : (e - e ^ 3 / 6) ^ 2 ≤ Real.sin e ^ 2 := by nlinarith
  nlinarith [sq_nonneg (e ^ 2), sq_nonneg e]

lemma rho_bounds {e u : ℝ} (he0 : 0 < e) (he : e ≤ 1) (hu : u ≠ 0) (hu1 : |u| ≤ 1) :
    1 - e ^ 2 / 3 - u ^ 2 ≤ Real.sin e ^ 2 / e ^ 2 * (u ^ 2 / Real.sinh u ^ 2) ∧
      Real.sin e ^ 2 / e ^ 2 * (u ^ 2 / Real.sinh u ^ 2) ≤ 1 := by
  obtain ⟨a1, a2⟩ := sin_div_bounds he0 he
  obtain ⟨b1, b2⟩ := div_sinh_bounds hu
  have hu2 : u ^ 2 ≤ 1 := by
    have : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
    rw [this]; nlinarith [abs_nonneg u]
  have he2 : e ^ 2 ≤ 1 := by nlinarith
  have hb0 : 0 ≤ u ^ 2 / Real.sinh u ^ 2 := by positivity
  have ha0 : 0 ≤ Real.sin e ^ 2 / e ^ 2 := by positivity
  constructor
  · have : (1 - e ^ 2 / 3) * (1 - u ^ 2) ≤ Real.sin e ^ 2 / e ^ 2 * (u ^ 2 / Real.sinh u ^ 2) :=
      mul_le_mul a1 b1 (by linarith) ha0
    nlinarith [mul_nonneg (sq_nonneg e) (sq_nonneg u)]
  · calc Real.sin e ^ 2 / e ^ 2 * (u ^ 2 / Real.sinh u ^ 2) ≤ 1 * 1 := mul_le_mul a2 b2 hb0 zero_le_one
      _ = 1 := one_mul _

lemma abs_log_one_add_sub_le {A B μ : ℝ} (hA : 0 ≤ A) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 1 / 2)
    (hBA : |B - A| ≤ μ * A) :
    |Real.log (1 + B) - Real.log (1 + A)| ≤ 2 * μ * (A / (1 + A)) := by
  have hA1 : 0 < 1 + A := by linarith
  have hTle : A / (1 + A) ≤ 1 := by rw [div_le_one hA1]; linarith
  have hT0 : 0 ≤ A / (1 + A) := by positivity
  set w := (B - A) / (1 + A) with hw
  have hwb : |w| ≤ μ * (A / (1 + A)) := by
    rw [hw, abs_div, abs_of_pos hA1, div_le_iff₀ hA1]
    calc |B - A| ≤ μ * A := hBA
      _ = μ * (A / (1 + A)) * (1 + A) := by field_simp
  have hw12 : |w| ≤ 1 / 2 := hwb.trans (by nlinarith)
  have h1 : 1 + B = (1 + A) * (1 + w) := by rw [hw]; field_simp; ring
  have hw1 : 0 < 1 + w := by have := neg_abs_le w; linarith
  have h2 : Real.log (1 + B) - Real.log (1 + A) = Real.log (1 + w) := by
    rw [h1, Real.log_mul hA1.ne' hw1.ne']; ring
  rw [h2]
  have u1 : Real.log (1 + w) ≤ |w| := by
    have := Real.log_le_sub_one_of_pos hw1
    linarith [le_abs_self w]
  have u2 : -(2 * |w|) ≤ Real.log (1 + w) := by
    have h3 := Real.one_sub_inv_le_log_of_pos hw1
    have h4 : 1 - (1 + w)⁻¹ = w / (1 + w) := by field_simp; ring
    rw [h4] at h3
    have h5 : -(2 * |w|) ≤ w / (1 + w) := by
      rw [le_div_iff₀ hw1]
      have := neg_abs_le w
      have := abs_nonneg w
      nlinarith [le_abs_self w, abs_nonneg w]
    linarith
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

lemma rho_correction {ρ ϑ g : ℝ} (hρ1 : ρ ≤ 1) (hlo : 1 - g ≤ ρ) (hg0 : 0 ≤ g)
    (hϑ : |ϑ| ≤ 1 / 10) : |ρ * (1 + ϑ) ^ 2 - 1| ≤ 3 * |ϑ| + 2 * g := by
  have hϑ2 := abs_le.mp hϑ
  have hq0 : 0 ≤ (1 + ϑ) ^ 2 := sq_nonneg _
  have hq1 : (1 + ϑ) ^ 2 ≤ 1.21 := by nlinarith
  have hup := mul_le_mul_of_nonneg_right hρ1 hq0
  have hlo' := mul_le_mul_of_nonneg_right hlo hq0
  have hgq : g * (1 + ϑ) ^ 2 ≤ g * 1.21 := mul_le_mul_of_nonneg_left hq1 hg0
  have hsq : ϑ ^ 2 ≤ |ϑ| * (1 / 10) := by
    have : ϑ ^ 2 = |ϑ| * |ϑ| := by rw [← sq, sq_abs]
    rw [this]; exact mul_le_mul_of_nonneg_left hϑ (abs_nonneg ϑ)
  have hl := neg_abs_le ϑ
  have hr := le_abs_self ϑ
  have e1 : (1 - g) * (1 + ϑ) ^ 2 = (1 + ϑ) ^ 2 - g * (1 + ϑ) ^ 2 := by ring
  have e2 : (1 + ϑ) ^ 2 = 1 + 2 * ϑ + ϑ ^ 2 := by ring
  rw [abs_le]
  constructor <;> nlinarith

lemma pairB_eq {x y ε : ℝ} (hxy : x ≠ y) (hε0 : 0 < ε) :
    pairB y ε x = ε ^ 2 / (x - y) ^ 2 *
      (Real.sin (π * ε / 2) ^ 2 / (π * ε / 2) ^ 2 *
        ((π * (x - y) / 2) ^ 2 / Real.sinh (π * (x - y) / 2) ^ 2)) := by
  have hpi := Real.pi_pos
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hsu : Real.sinh (π * (x - y) / 2) ^ 2 ≠ 0 :=
    (lt_of_lt_of_le (by positivity) (sq_le_sinh_sq _)).ne'
  unfold pairB
  field_simp

/-- **Near pair, abstract form.**  With `D = (x - y) m (1 + ϑ)`, `|ϑ| ≤ 1/10`, `|x - y| ≤ 1/10`, `0 < ε ≤ 1/8`:
`|log(1 + B) - log(1 + A)| ≤ 2 (3|ϑ| + 2ε² + |x - y|) T`, `A = (ε m)²/D²`, `T = A/(1 + A)`. -/
lemma near_log_bound {x y m ϑ ε : ℝ} (hm : 0 < m) (hxy : x ≠ y) (hd : |x - y| ≤ 1 / 10)
    (hε0 : 0 < ε) (hε : ε ≤ 1 / 8) (hϑ : |ϑ| ≤ 1 / 10) :
    |Real.log (1 + pairB y ε x) - Real.log (1 + (ε * m) ^ 2 / ((x - y) * m * (1 + ϑ)) ^ 2)| ≤
      2 * (3 * |ϑ| + 2 * ε ^ 2 + |x - y|) * nearT (ε * m) ((x - y) * m * (1 + ϑ)) := by
  have hpi := Real.pi_pos
  have hpi4 : π < 3.15 := by linarith [Real.pi_lt_d2]
  have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hϑ1 : 0 < 1 + ϑ := by have := neg_abs_le ϑ; linarith
  have hu0 : π * (x - y) / 2 ≠ 0 := by positivity
  have he0 : 0 < π * ε / 2 := by positivity
  have he1 : π * ε / 2 ≤ 1 := by nlinarith
  have hu1 : |π * (x - y) / 2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]; nlinarith
  obtain ⟨r1, r2⟩ := rho_bounds he0 he1 hu0 hu1
  have hB := pairB_eq hxy hε0
  have hw0 : 0 < ε ^ 2 / (x - y) ^ 2 := by positivity
  have hρ0 : 0 ≤ Real.sin (π * ε / 2) ^ 2 / (π * ε / 2) ^ 2 *
      ((π * (x - y) / 2) ^ 2 / Real.sinh (π * (x - y) / 2) ^ 2) := by positivity
  generalize Real.sin (π * ε / 2) ^ 2 / (π * ε / 2) ^ 2 *
      ((π * (x - y) / 2) ^ 2 / Real.sinh (π * (x - y) / 2) ^ 2) = ρ at hB hρ0 r1 r2
  have hg2 : 2 * ((π * ε / 2) ^ 2 / 3 + (π * (x - y) / 2) ^ 2) ≤ 2 * ε ^ 2 + |x - y| := by
    have hpi2 : π ^ 2 ≤ 10 := by nlinarith
    have h1 : 2 * ((π * ε / 2) ^ 2 / 3) ≤ 2 * ε ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hpi2) (sq_nonneg ε)]
    have h2 : 2 * (π * (x - y) / 2) ^ 2 ≤ |x - y| := by
      have : (π * (x - y) / 2) ^ 2 = π ^ 2 / 4 * |x - y| ^ 2 := by
        rw [div_pow, mul_pow, sq_abs]; ring
      rw [this]
      have h0 := abs_nonneg (x - y)
      have h3 : |x - y| ^ 2 ≤ |x - y| / 10 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 hpi2) (sq_nonneg |x - y|)]
    linarith
  have hk := rho_correction (g := (π * ε / 2) ^ 2 / 3 + (π * (x - y) / 2) ^ 2) r2
    (by linarith) (by positivity) hϑ
  have hA : (ε * m) ^ 2 / ((x - y) * m * (1 + ϑ)) ^ 2 = ε ^ 2 / (x - y) ^ 2 / (1 + ϑ) ^ 2 := by
    field_simp
  generalize hwdef : ε ^ 2 / (x - y) ^ 2 = w at hB hw0 hA
  rw [hA]
  have hA0 : 0 ≤ w / (1 + ϑ) ^ 2 := by positivity
  have hBA : |pairB y ε x - w / (1 + ϑ) ^ 2| ≤ (3 * |ϑ| + 2 * ε ^ 2 + |x - y|) * (w / (1 + ϑ) ^ 2) := by
    have e1 : pairB y ε x - w / (1 + ϑ) ^ 2 = w / (1 + ϑ) ^ 2 * (ρ * (1 + ϑ) ^ 2 - 1) := by
      rw [hB]; field_simp
    rw [e1, abs_mul, abs_of_nonneg hA0, mul_comm]
    exact mul_le_mul_of_nonneg_right (hk.trans (by linarith)) hA0
  have hμ0 : 0 ≤ 3 * |ϑ| + 2 * ε ^ 2 + |x - y| := by positivity
  have hμ : 3 * |ϑ| + 2 * ε ^ 2 + |x - y| ≤ 1 / 2 := by nlinarith
  have key := abs_log_one_add_sub_le hA0 hμ0 hμ hBA
  refine key.trans (le_of_eq ?_)
  congr 1
  unfold nearT
  have hD : (x - y) * m * (1 + ϑ) ≠ 0 := by positivity
  rw [← hwdef]
  field_simp

/-! ### The divided difference of `τ` -/

lemma deriv_tau_lipschitz {a b M : ℝ} (ha : 0 < a)
    (hM : ∀ z ∈ Icc a b, |deriv (deriv langerTau) z| ≤ M) {u v : ℝ} (hu : u ∈ Icc a b)
    (hv : v ∈ Icc a b) : |deriv langerTau u - deriv langerTau v| ≤ M * |u - v| := by
  have hsub : Icc a b ⊆ Ioi 0 := fun z hz => lt_of_lt_of_le ha hz.1
  have hdiff : ∀ z ∈ Icc a b, DifferentiableAt ℝ (deriv langerTau) z := fun z hz =>
    (contDiffOn_deriv_langerTau.differentiableOn one_ne_zero z (hsub hz)).differentiableAt
      (Ioi_mem_nhds (hsub hz))
  have := (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hdiff
    (fun z hz => by simpa using hM z hz) hv hu
  simpa [Real.norm_eq_abs] using this

lemma tau_mid {a b : ℝ} (ha : 0 < a) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≠ y) :
    ∃ ξ ∈ Icc a b, |ξ - y| ≤ |x - y| ∧ langerTau x - langerTau y = deriv langerTau ξ * (x - y) := by
  have hpos : ∀ z ∈ Icc a b, 0 < z := fun z hz => lt_of_lt_of_le ha hz.1
  have hcont : ∀ p q : ℝ, p ∈ Icc a b → q ∈ Icc a b → ContinuousOn langerTau (Icc p q) := by
    intro p q hp hq
    refine (contDiffOn_langerTau 0).continuousOn.mono fun z hz => ?_
    exact lt_of_lt_of_le ha (hp.1.trans hz.1)
  rcases lt_or_gt_of_ne hxy with h | h
  · have hder : ∀ z ∈ Ioo x y, HasDerivAt langerTau (deriv langerTau z) z := fun z hz =>
      hasDerivAt_langerTau_pos (lt_of_lt_of_le ha (hx.1.trans hz.1.le))
    obtain ⟨c, hc, hc2⟩ := exists_hasDerivAt_eq_slope langerTau (deriv langerTau) h
      (hcont x y hx hy) hder
    refine ⟨c, ⟨hx.1.trans hc.1.le, hc.2.le.trans hy.2⟩, ?_, ?_⟩
    · rw [abs_of_neg (by linarith [hc.2]), abs_of_neg (by linarith)]; linarith [hc.1]
    · rw [hc2]; field_simp; ring
  · have hder : ∀ z ∈ Ioo y x, HasDerivAt langerTau (deriv langerTau z) z := fun z hz =>
      hasDerivAt_langerTau_pos (lt_of_lt_of_le ha (hy.1.trans hz.1.le))
    obtain ⟨c, hc, hc2⟩ := exists_hasDerivAt_eq_slope langerTau (deriv langerTau) h
      (hcont y x hy hx) hder
    refine ⟨c, ⟨hy.1.trans hc.1.le, hc.2.le.trans hx.2⟩, ?_, ?_⟩
    · rw [abs_of_pos (by linarith [hc.1]), abs_of_pos (by linarith)]; linarith [hc.2]
    · rw [hc2]; field_simp

/-- `τ(x) - τ(y) = (x - y) τ'(ζ) (1 + ϑ)` with `|ϑ| ≤ M (|x - y| + |y - ζ|)/c_τ`. -/
lemma tau_sub_formula {a b cτ M : ℝ} (ha : 0 < a) (hc : 0 < cτ)
    (hcτ : ∀ z : ℝ, a ≤ z → cτ ≤ deriv langerTau z)
    (hM : ∀ z ∈ Icc a b, |deriv (deriv langerTau) z| ≤ M) {x y ζ : ℝ} (hx : x ∈ Icc a b)
    (hy : y ∈ Icc a b) (hζ : ζ ∈ Icc a b) (hxy : x ≠ y) :
    ∃ ϑ : ℝ, |ϑ| ≤ M * (|x - y| + |y - ζ|) / cτ ∧
      langerTau x - langerTau y = (x - y) * deriv langerTau ζ * (1 + ϑ) := by
  obtain ⟨ξ, hξ, hξy, hξe⟩ := tau_mid ha hx hy hxy
  have hm : 0 < deriv langerTau ζ := lt_of_lt_of_le hc (hcτ ζ hζ.1)
  have hL := deriv_tau_lipschitz ha hM hξ hζ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hx)
  refine ⟨(deriv langerTau ξ - deriv langerTau ζ) / deriv langerTau ζ, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hm, div_le_div_iff₀ hm hc]
    have h1 : |ξ - ζ| ≤ |x - y| + |y - ζ| := by
      calc |ξ - ζ| = |(ξ - y) + (y - ζ)| := by ring_nf
        _ ≤ |ξ - y| + |y - ζ| := abs_add_le _ _
        _ ≤ |x - y| + |y - ζ| := by linarith
    have h2 : |deriv langerTau ξ - deriv langerTau ζ| ≤ M * (|x - y| + |y - ζ|) :=
      hL.trans (mul_le_mul_of_nonneg_left h1 hM0)
    have h3 := hcτ ζ hζ.1
    calc |deriv langerTau ξ - deriv langerTau ζ| * cτ ≤ M * (|x - y| + |y - ζ|) * cτ := by gcongr
      _ ≤ M * (|x - y| + |y - ζ|) * deriv langerTau ζ := by gcongr
  · rw [hξe]; field_simp; ring

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.detuneRem_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms detuneRem_bounds

/-- info: 'FormalResearch.ModularBootstrap.Upper.Ramped.near_log_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms near_log_bound

end FormalResearch.ModularBootstrap.Upper.Ramped

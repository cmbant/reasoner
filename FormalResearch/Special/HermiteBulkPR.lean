module

public import Mathlib
public import FormalResearch.Special.HermitePRPhase
public import FormalResearch.Special.HermiteBulkOrigin

/-!
# The Liouville-Green march for `φ_n` from the origin to a bulk point

`hbk_S_eq`: the primitive `S` of `w = √(2n+1-x²)` equals `nπ/2 - Φ_n(x)` (the phase `hpr_phase` of
`HermitePRPhase`); `hbk_march`: the rotation comparison `hbk_rot`, applied to the Weber solution
`φ_n` with the initial data of `hbk_origin`, gives `|E φ_n(b) - c cos Φ_n(b)| ≤ 2 μ e^{μ/2} c`,
`μ = 5/(4 ε⁵ (2n+1))`, for `0 ≤ b ≤ (1-ε)√(2n+1)`.  Exact calculus plus the rotation estimate; no Airy
matching is used (the phase is fixed at `x = 0` by parity).
-/

@[expose] public section

open Real

namespace FormalResearch.Special

/-- The primitive `S` of `w` is `nπ/2 - Φ_n` (the Plancherel-Rotach phase `hpr_phase`). -/
lemma hbk_S_eq (n : ℕ) (b : ℝ) (hb : b ^ 2 < 2 * (n : ℝ) + 1) :
    hbk_S (2 * (n : ℝ) + 1) b = n * π / 2 - hpr_phase b n := by
  have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
  generalize hLdef : 2 * (n : ℝ) + 1 = L at *
  have hsL : 0 < √L := Real.sqrt_pos.2 hL
  have hsL2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  have hlt : |b / √L| < 1 := by
    rw [abs_div, abs_of_pos hsL, div_lt_one hsL]
    exact abs_lt_of_sq_lt_sq (by rw [hsL2]; exact hb) hsL.le
  have hab := abs_lt.1 hlt
  have hcos : cos (hpr_angle b n) = b / √L := by
    unfold hpr_angle; rw [hLdef]; exact Real.cos_arccos hab.1.le hab.2.le
  have hsin : sin (hpr_angle b n) = √(1 - (b / √L) ^ 2) := by
    unfold hpr_angle; rw [hLdef, Real.sin_arccos]
  have hasin : Real.arcsin (b / √L) = π / 2 - hpr_angle b n := by
    unfold hpr_angle; rw [hLdef, Real.arccos_eq_pi_div_two_sub_arcsin]; ring
  have hw : hbk_w L b = √L * sin (hpr_angle b n) := by
    rw [hsin, hbk_w, ← Real.sqrt_mul hL.le]
    congr 1
    field_simp
    rw [hsL2]; ring
  have hb' : b = √L * cos (hpr_angle b n) := by rw [hcos]; field_simp
  have hbw : b * hbk_w L b = L * (cos (hpr_angle b n) * sin (hpr_angle b n)) := by
    rw [hw]; nth_rewrite 1 [hb']; linear_combination (cos (hpr_angle b n) * sin (hpr_angle b n)) * hsL2
  unfold hbk_S hpr_phase
  rw [hLdef, hasin, hbw, sin_two_mul]
  linear_combination (-(π / 4)) * hLdef

/-- Lower bound of `w` on the bulk window. -/
lemma hbk_w_ge {L b x ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hL : 0 < L) (hb0 : 0 ≤ x) (hxb : x ≤ b)
    (hbε : b ≤ (1 - ε) * √L) : ε * √L ≤ hbk_w L x := by
  have hs2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  have hs0 : 0 < √L := Real.sqrt_pos.2 hL
  have h1 : x ^ 2 ≤ ((1 - ε) * √L) ^ 2 :=
    pow_le_pow_left₀ hb0 (hxb.trans hbε) 2
  have h2 : (ε * √L) ^ 2 ≤ L - x ^ 2 := by
    rw [mul_pow, hs2] at h1
    rw [mul_pow, hs2]
    nlinarith [mul_pos hε0 hL, mul_nonneg hε0.le (sub_nonneg.2 hε1)]
  exact Real.le_sqrt_of_sq_le h2

/-- **Liouville-Green march from the origin to a bulk point** `0 ≤ b ≤ (1-ε)√(2n+1)`:
with `μ = 5/(4 ε⁵ (2n+1))`, there is `c ≥ 0`, `|c² - 2/π| ≤ 1/(n+1)`, such that
`|E φ_n(b) - c cos Φ_n(b)| ≤ 2 μ e^{μ/2} c` (`E = (2n+1-b²)^{1/4}`). -/
theorem hbk_march (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (n : ℕ) (b : ℝ) (hb0 : 0 ≤ b)
    (hbε : b ≤ (1 - ε) * √(2 * (n : ℝ) + 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ |c ^ 2 - 2 / π| ≤ 1 / ((n : ℝ) + 1) ∧
      |hbk_U (2 * (n : ℝ) + 1) (hermitePhi n) b - c * cos (hpr_phase b n)| ≤
        2 * (5 / (4 * ε ^ 5 * (2 * (n : ℝ) + 1))) *
          exp (5 / (4 * ε ^ 5 * (2 * (n : ℝ) + 1)) / 2) * c := by
  have hL : 0 < 2 * (n : ℝ) + 1 := by positivity
  obtain ⟨c, hc0, hcN, hcn, hcΦ⟩ := hbk_origin n
  refine ⟨c, hc0, hcn, ?_⟩
  generalize hLdef : 2 * (n : ℝ) + 1 = L at *
  have hs0 : 0 < √L := Real.sqrt_pos.2 hL
  have hs2 : √L ^ 2 = L := Real.sq_sqrt hL.le
  have hbs : b < √L := lt_of_le_of_lt hbε (by nlinarith)
  have hx2 : ∀ x ∈ Set.Icc 0 b, x ^ 2 < L := by
    intro x hx
    have : x < √L := lt_of_le_of_lt hx.2 hbs
    nlinarith [hx.1]
  set κ : ℝ := 5 / (4 * ε ^ 5 * √L ^ 3) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have key := hbk_rot (hbk_U L (hermitePhi n)) (hbk_V L (hermitePhi n) (hkDer n)) (hbk_w L)
    (hbk_psi L) (hbk_S L) b κ hb0 hκ0
    (fun x hx => hbk_hasDerivAt_U (hx2 x hx) _ _ (hasDerivAt_hermitePhi' n x))
    (fun x hx => by
      have := hbk_hasDerivAt_V (hx2 x hx) (hermitePhi n) (hkDer n) (hasDerivAt_hermitePhi' n x)
        (by rw [← hLdef]; exact hasDerivAt_hkDer n x)
      exact this)
    (fun x hx => hbk_hasDerivAt_S (hx2 x hx))
    (by simp [hbk_S])
    (by
      intro x hx
      have hwp := hbk_w_pos (hx2 x hx)
      have hwge := hbk_w_ge hε0 hε1 hL hx.1 hx.2 hbε
      have hpsi : 0 ≤ hbk_psi L x := by unfold hbk_psi; positivity
      refine ⟨mul_nonneg hwp.le hpsi, ?_⟩
      have h1 : hbk_w L x * hbk_psi L x = (3 * x ^ 2 + 2 * L) / (4 * hbk_w L x ^ 5) := by
        unfold hbk_psi; field_simp
      rw [h1, div_le_iff₀ (by positivity)]
      have h5 : (ε * √L) ^ 5 ≤ hbk_w L x ^ 5 := pow_le_pow_left₀ (by positivity) hwge 5
      have hx3 : 3 * x ^ 2 + 2 * L ≤ 5 * L := by linarith [hx2 x hx]
      have e : κ * (4 * (ε * √L) ^ 5) = 5 * L := by
        have h3 : √L ^ 5 = √L ^ 3 * √L ^ 2 := by ring
        rw [hκ, mul_pow, h3, hs2]; field_simp
      nlinarith [mul_le_mul_of_nonneg_left h5 (mul_nonneg hκ0 (by norm_num : (0:ℝ) ≤ 4))])
  have hmem : b ∈ Set.Icc 0 b := ⟨hb0, le_rfl⟩
  have hk := key b hmem
  have hS := hbk_S_eq n b (by rw [hLdef]; exact hx2 b hmem)
  rw [hLdef] at hS
  rw [hS] at hk
  have hΦ := hcΦ (hpr_phase b n)
  have hsq : √(hbk_U L (hermitePhi n) 0 ^ 2 + hbk_V L (hermitePhi n) (hkDer n) 0 ^ 2) = c := by
    rw [← hcN]; exact Real.sqrt_sq hc0
  rw [hΦ, hsq] at hk
  refine hk.trans ?_
  have hκb : κ * b ≤ 5 / (4 * ε ^ 5 * L) := by
    have : κ * b ≤ κ * √L := mul_le_mul_of_nonneg_left hbs.le hκ0
    refine this.trans (le_of_eq ?_)
    have h3 : √L ^ 3 = √L * √L ^ 2 := by ring
    rw [hκ, h3, hs2]; field_simp
  have h2 : 2 * κ * b * exp (κ * b / 2) * c ≤
      2 * (5 / (4 * ε ^ 5 * L)) * exp (5 / (4 * ε ^ 5 * L) / 2) * c := by
    have e1 : exp (κ * b / 2) ≤ exp (5 / (4 * ε ^ 5 * L) / 2) :=
      exp_le_exp.2 (by linarith)
    have e2 : 2 * κ * b = 2 * (κ * b) := by ring
    rw [e2]
    apply mul_le_mul_of_nonneg_right _ hc0
    exact mul_le_mul (by linarith) e1 (exp_pos _).le (by positivity)
  exact h2

end FormalResearch.Special

/-- info: 'FormalResearch.Special.hbk_march' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hbk_march

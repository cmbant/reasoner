module

public import FormalResearch.Special.AiryRankDecayHS

/-!
# Geometric decay of the Hilbert–Schmidt tail of the Airy kernel `Ai(s + ζ)`

**Proved** (HS-tail form of `lem:airydecay`, `Weyl/free_fermion/paper/parts/edge.tex`).  For every `a ∈ ℝ` there are
constants `C, c > 0` (explicit: `c = 1/36`; `C` depends on `a` only) such that for every `m ∈ ℕ` there is `R > 0`
with

`∬_{s > a, ζ > 0} (Ai(s+ζ) - Σ_{k<m} φ_k(s) ψ_k(ζ))² ds dζ ≤ C e^{-c m}`

(`airy_hs_rank_decay`), where `φ_k = airyRankPhi R k`, `ψ_k = airyRankPsi R k` are bounded, measurable, compactly
supported (so square integrable) functions: a kernel of **rank `≤ m`** in separated form.  The integral is a
Lebesgue integral in `[0, ∞]`.  `R` is chosen with `R^{3/2} = max(t₀, m/8)`, `t₀ = max(8, 2|a|)^{3/2}`, balancing the
Chebyshev decay `4^{-m}` against the growth `exp(O(R^{3/2}))` of `Ai` on the Bernstein ellipse and the tail
`exp(-(2/3)(R/2)^{3/2})` beyond the box (`airy_hs_bound`).  The case `m = 0` is the finiteness of `∬ Ai(s+ζ)²`
(`airy_hs_zero_bound`).

In operator language (`𝒜_a : L²(0,∞) → L²(a,∞)` with kernel `Ai(s+ζ)`): the Hilbert–Schmidt distance from `𝒜_a`
to the set of operators of rank `≤ m` is at most `√C e^{-m/72}`.

Numerical checks (mpmath, 30 digits): the majorants `Ai(x)² ≤ 9e⁴e^{-x}` (all `x ∈ [-30,60]`, step `0.01`) and
`Ai(x)² ≤ 9e^{-x}exp(-(2/3)y^{3/2})` (`4 ≤ y ≤ x`) have no violation; the pointwise Chebyshev error for `R = 8`,
`s ∈ {-1,0,3,8}`, `n ≤ 20` is below `10⁻⁹` against the (very pessimistic) proved bound `2M/2^n` with
`M = 3exp((2/3)(17R/8)^{3/2}) ≈ 10¹⁹`: the proved constants are far from sharp, only the geometric rate in `m` matters.

**Not formalised** (no such theory in Mathlib / this repository): (i) the passage from this HS-tail statement to the
singular values `s_{m+1}(𝒜_a) ≤ C' e^{-c' m}` of the paper's `lem:airydecay` (that `s_{m+1}` is the operator-norm
distance to rank-`≤ m` operators and is dominated by the HS norm: Schmidt–Mirsky/Allakhverdiev, needs the
singular-value decomposition of compact operators on a Hilbert space); (ii) `λ_{m+1}(K_u) = s_{m+1}(𝒜_u)²` for
`K_u = 𝒜_u 𝒜_u^*` (spectral theorem for compact self-adjoint operators); (iii) the operator-level compression `𝒜_u` of `𝒜_{u_*}` (its HS-tail form, uniformity in `u ≥ a` with the same kernel, *is* formalised: `airy_hs_rank_decay_of_ge`); (iv) the constants are not optimised.

Note on the paper: `edge.tex` cites Trefethen Thm 8.2 for the Chebyshev *interpolation* error; Thm 8.2 is the truncation
statement (formalised in `FormalResearch.Complex.ChebyshevBernstein`), the interpolation bound being Thm 8.3
(`4Mρ^{-n}/(ρ-1)`); the rank count is identical.  The paper's `s ≤ 3R`/`s > 3R` split and the sector bound
`|Ai(w)| ≤ C e^{-(2/3)Re w^{3/2}}` on `|arg w| ≤ π/4` are replaced here by the cut at `s ≤ R` and the real-axis tail
(`AiryRankDecayTail`); only the order-`3/2` growth bound is needed in the complex domain.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace FormalResearch.Special

lemma airyRank_rpow_three_halves_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (3 / 2 : ℝ) = x * √x := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hx (by norm_num), Real.rpow_one,
    Real.sqrt_eq_rpow]

lemma rpow_seventeen_eighths : (17 / 8 : ℝ) ^ (3 / 2 : ℝ) ≤ 63 / 20 := by
  rw [airyRank_rpow_three_halves_eq (by norm_num)]
  have : √(17 / 8 : ℝ) ≤ 146 / 100 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  nlinarith

lemma airyChebM_le {R : ℝ} (hR : 0 ≤ R) :
    airyChebM R ≤ 3 * Real.exp ((21 / 10) * R ^ (3 / 2 : ℝ)) := by
  unfold airyChebM
  have h := Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 17 / 8) hR (z := 3 / 2)
  have hy : 0 ≤ R ^ (3 / 2 : ℝ) := Real.rpow_nonneg hR _
  have : (2 / 3 : ℝ) * ((17 / 8) * R) ^ (3 / 2 : ℝ) ≤ (21 / 10) * R ^ (3 / 2 : ℝ) := by
    rw [h]; nlinarith [rpow_seventeen_eighths]
  have := Real.exp_le_exp.2 this
  linarith

lemma half_rpow_ge {R : ℝ} (hR : 0 ≤ R) : R ^ (3 / 2 : ℝ) / 3 ≤ (R / 2) ^ (3 / 2 : ℝ) := by
  rw [airyRank_rpow_three_halves_eq hR, airyRank_rpow_three_halves_eq (by positivity)]
  have h2 : √(R / 2) = √R / √2 := Real.sqrt_div hR 2
  have : √2 ≤ 3 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  have hs2 : 0 < √2 := Real.sqrt_pos.2 (by norm_num)
  rw [h2]
  have hsR : 0 ≤ √R := Real.sqrt_nonneg R
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have : R / 2 * (√R / √2) * 3 = R * √R * (3 / (2 * √2)) := by
    field_simp
  rw [this]
  have h4 : 1 ≤ 3 / (2 * √2) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have : 0 ≤ R * √R := by positivity
  nlinarith

lemma sq_le_two_mul_exp {y : ℝ} (hy : 0 ≤ y) : y ^ 2 ≤ 2 * Real.exp y := by
  have := Real.quadratic_le_exp_of_nonneg hy
  nlinarith [sq_nonneg y]


lemma term1_le {a R : ℝ} (hR : 8 ≤ R) (haR : 2 * |a| ≤ R) (n : ℕ) :
    (2 * airyChebM R / 2 ^ n) ^ 2 * ((R - a) * R) ≤
      144 * Real.exp ((26 / 5) * R ^ (3 / 2 : ℝ)) * (1 / 4) ^ n := by
  have hR0 : 0 ≤ R := by linarith
  set y : ℝ := R ^ (3 / 2 : ℝ) with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg hR0 _
  have hM0 := airyChebM_nonneg R
  have hM := airyChebM_le hR0
  have hM2 : airyChebM R ^ 2 ≤ 9 * Real.exp ((21 / 5) * y) := by
    have h1 : airyChebM R ^ 2 ≤ (3 * Real.exp ((21 / 10) * y)) ^ 2 :=
      pow_le_pow_left₀ hM0 hM 2
    have h2 : (3 * Real.exp ((21 / 10) * y)) ^ 2 = 9 * Real.exp ((21 / 5) * y) := by
      rw [mul_pow, ← Real.exp_nat_mul]; norm_num; ring_nf
    linarith
  have hsq : (2 * airyChebM R / 2 ^ n) ^ 2 = 4 * airyChebM R ^ 2 * (1 / 4) ^ n := by
    have : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [div_pow, mul_pow, this, one_div, inv_pow]
    field_simp
    ring
  have hRa : (R - a) * R ≤ 4 * Real.exp y := by
    have h1 : R - a ≤ 2 * R := by linarith [neg_abs_le a]
    have h2 : R ^ 2 ≤ y ^ 2 := by
      have : y ^ 2 = R ^ 3 := by
        rw [hy, airyRank_rpow_three_halves_eq hR0, mul_pow, Real.sq_sqrt hR0]; ring
      rw [this]; nlinarith
    have h3 := sq_le_two_mul_exp hy0
    have : (R - a) * R ≤ 2 * R * R := by gcongr
    nlinarith
  have hq : 0 ≤ (1 / 4 : ℝ) ^ n := by positivity
  calc (2 * airyChebM R / 2 ^ n) ^ 2 * ((R - a) * R)
      = 4 * airyChebM R ^ 2 * (1 / 4) ^ n * ((R - a) * R) := by rw [hsq]
    _ ≤ 4 * (9 * Real.exp ((21 / 5) * y)) * (1 / 4) ^ n * (4 * Real.exp y) := by
        have : 0 ≤ (R - a) * R := by
          have : 0 ≤ R - a := by linarith [le_abs_self a, abs_nonneg a]
          positivity
        gcongr
    _ = 144 * Real.exp ((26 / 5) * y) * (1 / 4) ^ n := by
        have : Real.exp ((21 / 5) * y) * Real.exp y = Real.exp ((26 / 5) * y) := by
          rw [← Real.exp_add]; ring_nf
        calc 4 * (9 * Real.exp ((21 / 5) * y)) * (1 / 4) ^ n * (4 * Real.exp y)
            = 144 * (Real.exp ((21 / 5) * y) * Real.exp y) * (1 / 4) ^ n := by ring
          _ = _ := by rw [this]


/-- The `m = 0` case: `∬_{s > a, ζ > 0} Ai(s+ζ)² ≤ 9 e⁴ e^{-a}`. -/
theorem airy_hs_zero_bound (a : ℝ) :
    ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ), ENNReal.ofReal (airyAi (p.1 + p.2) ^ 2) ≤
      ENNReal.ofReal (9 * Real.exp 4 * Real.exp (-a)) := by
  set e : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-x)) with he
  have hem : Measurable e :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp measurable_neg)
  have hK : 0 ≤ 9 * Real.exp 4 := by positivity
  calc ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ), ENNReal.ofReal (airyAi (p.1 + p.2) ^ 2)
      ≤ ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ), ENNReal.ofReal (9 * Real.exp 4) * (e p.1 * e p.2) := by
        refine setLIntegral_mono' (measurableSet_Ioi.prod measurableSet_Ioi) fun p _ => ?_
        obtain ⟨s, ζ⟩ := p
        refine (ENNReal.ofReal_le_ofReal (airyAi_sq_le_exp (s + ζ))).trans (le_of_eq ?_)
        simp only [he]
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hK]
        congr 1
        rw [show -(s + ζ) = -s + -ζ by ring, Real.exp_add]
    _ = ENNReal.ofReal (9 * Real.exp 4 * Real.exp (-a)) := by
        rw [lintegral_const_mul (f := fun p : ℝ × ℝ => e p.1 * e p.2) _
          ((hem.comp measurable_fst).mul (hem.comp measurable_snd)),
          lintegral_prod_mul_set hem hem]
        simp only [he]
        rw [lintegral_exp_neg_Ioi, lintegral_exp_neg_Ioi, neg_zero, Real.exp_zero,
          ENNReal.ofReal_one, mul_one, ← ENNReal.ofReal_mul hK]

lemma exp_neg_log_four_le_quarter_aux : (1 / 4 : ℝ) ≤ Real.exp (-(138 / 100)) := by
  have h2 := Real.log_two_gt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have : (138 / 100 : ℝ) ≤ Real.log 4 := by rw [h4]; linarith
  have h5 : Real.exp (138 / 100) ≤ 4 := by
    calc Real.exp (138 / 100) ≤ Real.exp (Real.log 4) := Real.exp_le_exp.2 this
      _ = 4 := Real.exp_log (by norm_num)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (Real.exp_pos _) h5

lemma quarter_pow_le (n : ℕ) : (1 / 4 : ℝ) ^ n ≤ Real.exp (-(138 / 100) * n) := by
  have := pow_le_pow_left₀ (by norm_num) exp_neg_log_four_le_quarter_aux n
  rw [← Real.exp_nat_mul] at this
  convert this using 2
  ring


/-- **Geometric decay of the Hilbert–Schmidt tail of `Ai(s + ζ)`** (HS-tail form of `lem:airydecay`). -/
theorem airy_hs_rank_decay (a : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, ∃ R : ℝ, 0 < R ∧
      ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal ((airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2) ≤
        ENNReal.ofReal (C * Real.exp (-c * m)) := by
  set R₀ : ℝ := max 8 (2 * |a|) with hR₀
  have hR₀8 : 8 ≤ R₀ := le_max_left _ _
  have hR₀a : 2 * |a| ≤ R₀ := le_max_right _ _
  set t₀ : ℝ := R₀ ^ (3 / 2 : ℝ) with ht₀
  have ht₀pos : 0 < t₀ := Real.rpow_pos_of_pos (by linarith) _
  refine ⟨144 * Real.exp ((26 / 5) * t₀ + 7 / 10) + 9 * Real.exp (-a) +
    9 * Real.exp 4 * Real.exp (-a), 1 / 36, by positivity, by norm_num, ?_⟩
  intro m
  cases m with
  | zero =>
    refine ⟨1, one_pos, ?_⟩
    have : ∀ p : ℝ × ℝ, airyRankKer 1 0 p.1 p.2 = 0 := fun p => by
      simp [airyRankKer]
    simp only [this, sub_zero]
    refine (airy_hs_zero_bound a).trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
    have := Real.exp_pos (-a)
    have := Real.exp_pos 4
    have := Real.exp_pos ((26 / 5) * t₀ + 7 / 10)
    nlinarith [mul_pos this this]
  | succ n =>
    set y : ℝ := max t₀ ((n + 1) / 8) with hy
    have hyt : t₀ ≤ y := le_max_left _ _
    have hym : ((n : ℝ) + 1) / 8 ≤ y := le_max_right _ _
    have hyup : y ≤ t₀ + ((n : ℝ) + 1) / 8 := by
      refine max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) ?_
      linarith
    have hypos : 0 < y := lt_of_lt_of_le ht₀pos hyt
    set R : ℝ := y ^ (2 / 3 : ℝ) with hR
    have hR3 : R ^ (3 / 2 : ℝ) = y := by
      rw [hR, ← Real.rpow_mul hypos.le]; norm_num
    have hRR₀ : R₀ ≤ R := by
      have h1 : t₀ ^ (2 / 3 : ℝ) ≤ y ^ (2 / 3 : ℝ) := Real.rpow_le_rpow ht₀pos.le hyt (by norm_num)
      have h2 : t₀ ^ (2 / 3 : ℝ) = R₀ := by
        rw [ht₀, ← Real.rpow_mul (by linarith)]; norm_num
      rw [← h2]; exact h1
    have hR8 : 8 ≤ R := hR₀8.trans hRR₀
    have hRa : 2 * |a| ≤ R := hR₀a.trans hRR₀
    have hR0 : 0 < R := by linarith
    refine ⟨R, hR0, ?_⟩
    refine (airy_hs_bound hR8 hRa n).trans ?_
    have hT1 := term1_le hR8 hRa n
    rw [hR3] at hT1
    have hN : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    set E : ℝ := Real.exp (-(1 / 36) * ((n + 1 : ℕ) : ℝ)) with hE
    have hEpos : 0 < E := Real.exp_pos _
    -- first term
    have hT1' : (2 * airyChebM R / 2 ^ n) ^ 2 * ((R - a) * R) ≤
        144 * Real.exp ((26 / 5) * t₀ + 7 / 10) * E := by
      refine hT1.trans ?_
      have hq := quarter_pow_le n
      have h1 : 144 * Real.exp ((26 / 5) * y) * (1 / 4) ^ n ≤
          144 * Real.exp ((26 / 5) * y) * Real.exp (-(138 / 100) * n) := by gcongr
      refine h1.trans ?_
      have key : Real.exp ((26 / 5) * y) * Real.exp (-(138 / 100) * n) ≤
          Real.exp ((26 / 5) * t₀ + 7 / 10) * E := by
        rw [hE, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        rw [hN]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      calc 144 * Real.exp ((26 / 5) * y) * Real.exp (-(138 / 100) * n)
          = 144 * (Real.exp ((26 / 5) * y) * Real.exp (-(138 / 100) * n)) := by ring
        _ ≤ 144 * (Real.exp ((26 / 5) * t₀ + 7 / 10) * E) := by gcongr
        _ = _ := by ring
    -- second term
    have hT2' : 9 * Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) * Real.exp (-a) ≤
        9 * Real.exp (-a) * E := by
      have h1 := half_rpow_ge hR0.le
      rw [hR3] at h1
      have h2 : Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) ≤ E := by
        rw [hE]
        apply Real.exp_le_exp.2
        rw [hN]
        nlinarith
      have h3 := Real.exp_pos (-a)
      calc 9 * Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) * Real.exp (-a)
          = 9 * Real.exp (-a) * Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) := by ring
        _ ≤ 9 * Real.exp (-a) * E := by gcongr
    have hX1 : 0 ≤ (2 * airyChebM R / 2 ^ n) ^ 2 * ((R - a) * R) := by
      have : 0 ≤ R - a := by linarith [le_abs_self a, abs_nonneg a, neg_abs_le a]
      have := airyChebM_nonneg R
      positivity
    have hX2 : 0 ≤ 9 * Real.exp (-(2 / 3) * (R / 2) ^ (3 / 2 : ℝ)) * Real.exp (-a) := by positivity
    rw [← ENNReal.ofReal_add hX1 hX2]
    refine ENNReal.ofReal_le_ofReal ?_
    have h4 : 0 ≤ 9 * Real.exp 4 * Real.exp (-a) * E := by positivity
    nlinarith


lemma continuous_airyAi_aux : Continuous airyAi :=
  Complex.continuous_re.comp (differentiable_airyAiC.continuous.comp Complex.continuous_ofReal)

/-- **Separated form** of `airy_hs_rank_decay`: for every `m` there are `m` pairs of bounded, measurable functions
`φ_k, ψ_k` vanishing outside `[-R,R]` (so square integrable) with `∬_{s>a, ζ>0} (Ai(s+ζ) - Σ_{k<m} φ_k(s)ψ_k(ζ))² ≤
C e^{-c m}`. -/
theorem airy_rank_decay_separated (a : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, ∃ (φ ψ : ℕ → ℝ → ℝ) (K T : ℝ),
      (∀ k, Measurable (φ k)) ∧ (∀ k, Measurable (ψ k)) ∧
      (∀ k x, |φ k x| ≤ K ∧ |ψ k x| ≤ K) ∧ (∀ k x, T < |x| → φ k x = 0 ∧ ψ k x = 0) ∧
      ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ), ENNReal.ofReal
          ((airyAi (p.1 + p.2) - ∑ k ∈ Finset.range m, φ k p.1 * ψ k p.2) ^ 2) ≤
        ENNReal.ofReal (C * Real.exp (-c * m)) := by
  obtain ⟨C, c, hC, hc, h⟩ := airy_hs_rank_decay a
  refine ⟨C, c, hC, hc, fun m => ?_⟩
  obtain ⟨R, hR, hbound⟩ := h m
  refine ⟨airyRankPhi R, airyRankPsi R, max (2 * airyChebM R) 1, R, measurable_airyRankPhi R,
    measurable_airyRankPsi R, fun k x => ⟨(abs_airyRankPhi_le hR k x).trans (le_max_left _ _),
    (abs_airyRankPsi_le R k x hR).trans (le_max_right _ _)⟩, fun k x hx => ⟨?_, ?_⟩, hbound⟩
  · unfold airyRankPhi
    split_ifs with hm
    · have := abs_le.2 ⟨hm.1, hm.2⟩
      linarith
    · rfl
  · unfold airyRankPsi
    split_ifs with hm
    · have := abs_of_nonneg hm.1
      have := hm.2
      linarith
    · rfl

/-- **Real-integral form**: the squared error is integrable on `(a,∞) × (0,∞)` and its integral is at most
`C e^{-c m}`. -/
theorem airy_rank_decay_integral (a : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, ∃ R : ℝ, 0 < R ∧
      Integrable (fun p : ℝ × ℝ => (airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2)
        (volume.restrict (Ioi a ×ˢ Ioi (0 : ℝ))) ∧
      ∫ p in Ioi a ×ˢ Ioi (0 : ℝ), (airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2 ≤
        C * Real.exp (-c * m) := by
  obtain ⟨C, c, hC, hc, h⟩ := airy_hs_rank_decay a
  refine ⟨C, c, hC, hc, fun m => ?_⟩
  obtain ⟨R, hR, hbound⟩ := h m
  have hmeas : Measurable (fun p : ℝ × ℝ => (airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2) := by
    refine Measurable.pow_const (Measurable.sub ?_ ?_) 2
    · exact continuous_airyAi_aux.measurable.comp (measurable_fst.add measurable_snd)
    · unfold airyRankKer
      refine Finset.measurable_sum _ fun k _ => ?_
      exact ((measurable_airyRankPhi R k).comp measurable_fst).mul
        ((measurable_airyRankPsi R k).comp measurable_snd)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi a ×ˢ Ioi (0 : ℝ))]
      (fun p : ℝ × ℝ => (airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2) :=
    Filter.Eventually.of_forall fun p => sq_nonneg _
  have hfin : ∫⁻ p in Ioi a ×ˢ Ioi (0 : ℝ),
      ENNReal.ofReal ((airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2) < ⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨R, hR, ⟨hmeas.aestronglyMeasurable, ?_⟩, ?_⟩
  · exact (hasFiniteIntegral_iff_ofReal hnn).2 hfin
  · rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas.aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hbound

/-- **Uniformity in `u ≥ a`**: the same kernel `airyRankKer R m` works on every smaller domain `(u,∞) × (0,∞)`,
`u ≥ a` (the integrand is nonnegative), which is the HS-tail form of the paper's "for all `u ≥ u_*`". -/
theorem airy_hs_rank_decay_of_ge (a : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ m : ℕ, ∃ R : ℝ, 0 < R ∧ ∀ u : ℝ, a ≤ u →
      ∫⁻ p in Ioi u ×ˢ Ioi (0 : ℝ),
          ENNReal.ofReal ((airyAi (p.1 + p.2) - airyRankKer R m p.1 p.2) ^ 2) ≤
        ENNReal.ofReal (C * Real.exp (-c * m)) := by
  obtain ⟨C, c, hC, hc, h⟩ := airy_hs_rank_decay a
  refine ⟨C, c, hC, hc, fun m => ?_⟩
  obtain ⟨R, hR, hbound⟩ := h m
  refine ⟨R, hR, fun u hu => le_trans (lintegral_mono_set ?_) hbound⟩
  exact prod_mono (Ioi_subset_Ioi hu) subset_rfl

/-- info: 'FormalResearch.Special.airy_hs_rank_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_hs_rank_decay

/-- info: 'FormalResearch.Special.airy_hs_rank_decay_of_ge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_hs_rank_decay_of_ge

/-- info: 'FormalResearch.Special.airy_rank_decay_separated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_rank_decay_separated

/-- info: 'FormalResearch.Special.airy_rank_decay_integral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_rank_decay_integral

end FormalResearch.Special

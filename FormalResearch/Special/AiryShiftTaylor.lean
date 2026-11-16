module

public import FormalResearch.Special.AiryShift
public import FormalResearch.Special.AiryWt

/-!
# Taylor remainders of `Ai` against the weight `airyWt`

Jets of a solution of `y'' = x y`: `y⁽⁰⁾ = y`, `y⁽¹⁾ = y'`, `y⁽²⁾ = x y`, `y⁽³⁾ = y + x y'`,
`y⁽⁴⁾ = x² y + 2 y'`, `y⁽⁵⁾ = 4 x y + x² y'`, `y⁽⁶⁾ = (x³+4) y + 6 x y'` (`airyJetOf`).  A chain of
`k`-fold mean-value bounds (`airyTaylor_chain`: if `|y⁽ⁿ⁾| ≤ B` on the segment `[X, X+s]` then the order-`n`
Taylor polynomial of `y⁽⁰⁾` at `X` has remainder `≤ B |s|ⁿ`; no factorial gain) gives, for every solution:

* `airy_sol_taylor4`: `|y(X+s) − T₄| ≤ B |s|⁵` and `|y'(X+s) − T₃'| ≤ B |s|⁴`, with `B ≥ |4ξy + ξ²y'|` on the
  segment, where
  `T₄ = y + s y' + (s²/2) X y + (s³/6)(y + X y') + (s⁴/24)(X² y + 2 y')` and
  `T₃' = y' + s X y + (s²/2)(y + X y') + (s³/6)(X² y + 2 y')`;
* `airy_sol_taylor5`: the next order, `|y(X+s) − T₅| ≤ B |s|⁶`, `|y'(X+s) − T₄'| ≤ B |s|⁵` with
  `B ≥ |(ξ³+4)y + 6ξy'|` and `T₅ = T₄ + (s⁵/120)(4X y + X² y')`, `T₄' = T₃' + (s⁴/24)(4X y + X² y')`.

For `Ai`, with `u = 1 + |X|` and `Λ ≥ |s| √u`, `|s| ≤ 1`, `X ≥ -1` (`airy_taylor4`, `airy_taylor5`):

`|Ai(X+s) − T₄| ≤ K e^Λ |s|⁵ u² √u · airyWt X`, `|Ai'(X+s) − T₃'| ≤ K e^Λ |s|⁴ u² √u · airyWt X`,
`|Ai(X+s) − T₅| ≤ K e^Λ |s|⁶ u³ · airyWt X`, `|Ai'(X+s) − T₄'| ≤ K e^Λ |s|⁵ u³ · airyWt X`

(`u² √u = (1+|X|)^{5/2}`).  This is the Taylor lemma used in `lem:ec-defect` of
`Weyl/free_fermion/notes/edge_crossover.tex` (`EC:78-86`, with `airyWt` in place of the envelope `𝓔`) and
in the order-`h^{5/3}`, `h²` expansions of `lem:airy2-shift-parity` (P3 appendices `A:1068-1104`).

**The hypothesis `|s| √(1+|X|) ≤ Λ` is necessary and cannot be dropped.**  Numerically (`mpmath`, 30
digits) the best constant `K` in the first bound, over `X ∈ [-1, 30]`, `|s| ≤ 1`, is `0.0077`
(`0.0044` for `|s|√(1+|X|) ≤ 1/2`, `0.0051` for `≤ 1`, `0.0054` for `≤ 2`, `0.0523` for the `Ai'` bound
unrestricted; for the order-5 statement `0.0029` (`Ai`) and `0.018` (`Ai'`) with `Λ ≤ 2`), whereas at `s = -1` the ratio of the remainder to `|s|⁵ u^{5/2} airyWt` is `0.058, 5.9,
4.8·10⁵` at `X = 100, 300, 1000` (it grows like `e^{√X}`: `Ai(X-1)/Ai(X) ≈ e^{√X}`).  In the discrete
application `|s| = O(h^{1/3})` and `X = O(h^{-2/3})`, so `Λ = O(1)`.  The constants of the Lean statement are
non-optimal (the mean-value chain loses `1/n!`), and `K` is existential: on `[-2, -1]`, where `Ai` is not
covered by `airyAi_envelope_real`, `K` comes from the compactness of `[-2, -1]`.

Also here: the first terms of `C(X,s)`, `S(X,s)` of `AiryShift` (`airyShiftC_taylor`, `airyShiftS_taylor`):
`C = 1 + X s²/2 + s³/6 + X² s⁴/24 + X s⁵/30 + O(s⁶)`, `S = s + X s³/6 + s⁴/12 + X² s⁵/120 + O(s⁶)`
(remainder bounded by the sup of the sixth jet on the segment, as hypothesis).

Not formalised: Lagrange constants with `1/n!`; the sharp constant; orders above the fifth/sixth jet.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-! ### The mean-value chain -/

/-- `t ∈ [0, s]` (in either orientation) implies `|t| ≤ |s|`. -/
lemma abs_le_abs_of_mem_uIcc {s t : ℝ} (ht : t ∈ uIcc 0 s) : |t| ≤ |s| := by
  rcases le_total 0 s with hs | hs
  · rw [uIcc_of_le hs] at ht
    rw [abs_of_nonneg ht.1, abs_of_nonneg hs]; exact ht.2
  · rw [uIcc_of_ge hs] at ht
    rw [abs_of_nonpos ht.2, abs_of_nonpos hs]; linarith [ht.1]

/-- One step: if `|g'| ≤ B` on the segment `[0, s]` then `|g(t) - g(0)| ≤ B |s|` there. -/
lemma airyTaylor_step {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t) {s B : ℝ}
    (hB : ∀ t ∈ uIcc 0 s, |g' t| ≤ B) : ∀ t ∈ uIcc 0 s, |g t - g 0| ≤ B * |s| := by
  intro t ht
  have h0 : (0 : ℝ) ∈ uIcc 0 s := left_mem_uIcc
  have hsub : uIcc 0 t ⊆ uIcc 0 s := uIcc_subset_uIcc h0 ht
  have := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := g) (f' := g') (C := B) (x := 0) (y := t)
    (fun x _ => (hg x).hasDerivWithinAt) (fun x hx => by simpa using hB x (hsub hx))
    left_mem_uIcc right_mem_uIcc
  simp only [Real.norm_eq_abs, sub_zero] at this
  have hts : |t| ≤ |s| := abs_le_abs_of_mem_uIcc ht
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0 h0)
  calc |g t - g 0| ≤ B * |t| := this
    _ ≤ B * |s| := mul_le_mul_of_nonneg_left hts hB0

/-- **Taylor chain.**  If `F k` has derivative `F (k+1)` for `k < n` and `|F n (X + t)| ≤ B` on the segment
`t ∈ [0, s]`, then `|F 0 (X+t) - Σ_{k<n} F k X t^k/k!| ≤ B |s|^n` there. -/
lemma airyTaylor_chain : ∀ (n : ℕ) (F : ℕ → ℝ → ℝ),
    (∀ k < n, ∀ x, HasDerivAt (F k) (F (k + 1) x) x) → ∀ (X s B : ℝ),
    (∀ t ∈ uIcc 0 s, |F n (X + t)| ≤ B) →
    ∀ t ∈ uIcc 0 s, |F 0 (X + t) - ∑ k ∈ Finset.range n, F k X * t ^ k / (k.factorial : ℝ)| ≤
      B * |s| ^ n := by
  intro n
  induction n with
  | zero =>
    intro F _ X s B hB t ht
    simpa using hB t ht
  | succ n ih =>
    intro F hF X s B hB t ht
    have hIH := ih (fun k => F (k + 1)) (fun k hk x => hF (k + 1) (by omega) x) X s B hB
    -- the primitive
    set g : ℝ → ℝ := fun t => F 0 (X + t) -
      ∑ k ∈ Finset.range (n + 1), F k X * t ^ k / (k.factorial : ℝ) with hgdef
    set g' : ℝ → ℝ := fun t => F 1 (X + t) -
      ∑ k ∈ Finset.range n, F (k + 1) X * t ^ k / (k.factorial : ℝ) with hg'def
    have hg : ∀ t, HasDerivAt g (g' t) t := by
      intro t
      have h1 : HasDerivAt (fun t => F 0 (X + t)) (F 1 (X + t)) t :=
        (hF 0 (by omega) (X + t)).comp_const_add X t
      have hterm : ∀ k ∈ Finset.range n, HasDerivAt
          (fun t : ℝ => F (k + 1) X * t ^ (k + 1) / ((k + 1).factorial : ℝ))
          (F (k + 1) X * t ^ k / (k.factorial : ℝ)) t := by
        intro k _
        have := (((hasDerivAt_pow (k + 1) t).const_mul (F (k + 1) X)).div_const
          ((k + 1).factorial : ℝ))
        refine this.congr_deriv ?_
        rw [Nat.factorial_succ]
        push_cast
        have : (k.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have h2 := (HasDerivAt.fun_sum hterm).add_const (F 0 X)
      have hP : (fun t : ℝ => ∑ k ∈ Finset.range (n + 1), F k X * t ^ k / (k.factorial : ℝ)) =
          fun t => ∑ k ∈ Finset.range n, F (k + 1) X * t ^ (k + 1) / ((k + 1).factorial : ℝ)
            + F 0 X := by
        funext t
        rw [Finset.sum_range_succ']
        simp
      have h3 := h1.sub h2
      rw [← hP] at h3
      exact h3
    have h0 : g 0 = 0 := by
      simp only [hgdef, add_zero]
      rw [Finset.sum_range_succ']
      simp
    have hstep := airyTaylor_step hg (s := s) (B := B * |s| ^ n) (fun t ht => by
      simpa [hg'def] using hIH t ht) t ht
    rw [h0, sub_zero] at hstep
    simpa [hgdef, pow_succ, mul_assoc] using hstep

/-! ### Jets of a solution of `y'' = x y` -/

/-- The jets `y⁽ᵏ⁾` (`k ≤ 6`) of a solution `(y, y')` of `y'' = x y`, as polynomial combinations of `y, y'`. -/
def airyJetOf (y y' : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => y
  | 1 => y'
  | 2 => fun x => x * y x
  | 3 => fun x => y x + x * y' x
  | 4 => fun x => x ^ 2 * y x + 2 * y' x
  | 5 => fun x => 4 * x * y x + x ^ 2 * y' x
  | 6 => fun x => (x ^ 3 + 4) * y x + 6 * x * y' x
  | _ => fun _ => 0

lemma hasDerivAt_airyJetOf {y y' : ℝ → ℝ} (hy : IsAirySol y y') {k : ℕ} (hk : k < 6) (x : ℝ) :
    HasDerivAt (airyJetOf y y' k) (airyJetOf y y' (k + 1) x) x := by
  have h1 := (hy x).1
  have h2 := (hy x).2
  interval_cases k
  · simpa [airyJetOf] using h1
  · simpa [airyJetOf] using h2
  · have := (hasDerivAt_id x).mul h1
    simp only [airyJetOf]
    convert this using 1
    all_goals first | rfl | simp
  · have := h1.add ((hasDerivAt_id x).mul h2)
    simp only [airyJetOf]
    convert this using 1
    all_goals first | rfl | (simp; ring1)
  · have := (((hasDerivAt_id x).pow 2).mul h1).add (h2.const_mul 2)
    simp only [airyJetOf]
    convert this using 1
    all_goals first | rfl | (simp; ring1)
  · have := ((((hasDerivAt_id x).const_mul 4).mul h1)).add (((hasDerivAt_id x).pow 2).mul h2)
    simp only [airyJetOf]
    convert this using 1
    all_goals first | rfl | (simp; ring1)

/-- Core Taylor bound for the jets `y⁽ʲ⁾`, order `n`, `j + n ≤ 6`. -/
lemma airyTaylor_core {y y' : ℝ → ℝ} (hy : IsAirySol y y') {j n : ℕ} (hjn : j + n ≤ 6)
    (X s B : ℝ) (hB : ∀ t ∈ uIcc 0 s, |airyJetOf y y' (j + n) (X + t)| ≤ B) :
    |airyJetOf y y' j (X + s) -
        ∑ k ∈ Finset.range n, airyJetOf y y' (j + k) X * s ^ k / (k.factorial : ℝ)| ≤ B * |s| ^ n := by
  have := airyTaylor_chain n (fun k => airyJetOf y y' (j + k))
    (fun k hk x => hasDerivAt_airyJetOf hy (by omega) x) X s B (by simpa using hB) s right_mem_uIcc
  simpa using this

/-- **Taylor expansion of a solution to order 4 (and of its derivative to order 3).** -/
theorem airy_sol_taylor4 {y y' : ℝ → ℝ} (hy : IsAirySol y y') (X s B : ℝ)
    (hB : ∀ t ∈ uIcc 0 s, |4 * (X + t) * y (X + t) + (X + t) ^ 2 * y' (X + t)| ≤ B) :
    |y (X + s) - (y X + s * y' X + s ^ 2 / 2 * (X * y X) + s ^ 3 / 6 * (y X + X * y' X) +
        s ^ 4 / 24 * (X ^ 2 * y X + 2 * y' X))| ≤ B * |s| ^ 5 ∧
    |y' (X + s) - (y' X + s * (X * y X) + s ^ 2 / 2 * (y X + X * y' X) +
        s ^ 3 / 6 * (X ^ 2 * y X + 2 * y' X))| ≤ B * |s| ^ 4 := by
  constructor
  · have := airyTaylor_core hy (j := 0) (n := 5) (by norm_num) X s B (by simpa [airyJetOf] using hB)
    simp [Finset.sum_range_succ, Nat.factorial, airyJetOf] at this
    convert this using 2
    ring
  · have := airyTaylor_core hy (j := 1) (n := 4) (by norm_num) X s B (by simpa [airyJetOf] using hB)
    simp [Finset.sum_range_succ, Nat.factorial, airyJetOf] at this
    convert this using 2
    ring

/-- **Taylor expansion to order 5 (and of the derivative to order 4).** -/
theorem airy_sol_taylor5 {y y' : ℝ → ℝ} (hy : IsAirySol y y') (X s B : ℝ)
    (hB : ∀ t ∈ uIcc 0 s, |((X + t) ^ 3 + 4) * y (X + t) + 6 * (X + t) * y' (X + t)| ≤ B) :
    |y (X + s) - (y X + s * y' X + s ^ 2 / 2 * (X * y X) + s ^ 3 / 6 * (y X + X * y' X) +
        s ^ 4 / 24 * (X ^ 2 * y X + 2 * y' X) + s ^ 5 / 120 * (4 * X * y X + X ^ 2 * y' X))|
        ≤ B * |s| ^ 6 ∧
    |y' (X + s) - (y' X + s * (X * y X) + s ^ 2 / 2 * (y X + X * y' X) +
        s ^ 3 / 6 * (X ^ 2 * y X + 2 * y' X) + s ^ 4 / 24 * (4 * X * y X + X ^ 2 * y' X))|
        ≤ B * |s| ^ 5 := by
  constructor
  · have := airyTaylor_core hy (j := 0) (n := 6) (by norm_num) X s B (by simpa [airyJetOf] using hB)
    simp [Finset.sum_range_succ, Nat.factorial, airyJetOf] at this
    convert this using 2
    ring
  · have := airyTaylor_core hy (j := 1) (n := 5) (by norm_num) X s B (by simpa [airyJetOf] using hB)
    simp [Finset.sum_range_succ, Nat.factorial, airyJetOf] at this
    convert this using 2
    ring

/-! ### Application to `Ai` -/

/-- `|Ai| ≤ K₀ airyWt`, `|Ai'| ≤ K₀ √(1+|ξ|) airyWt` for all `ξ ≥ -2` (the range `[-1, ∞)` is
`airyAi_le_six_airyWt`, `abs_airyAi'_le_airyWt`; on the compact `[-2, -1]` the bound is by continuity,
so `K₀` is existential). -/
lemma airy_envelope_ge_neg_two :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ ξ : ℝ, -2 ≤ ξ →
      |airyAi ξ| ≤ K₀ * airyWt ξ ∧ |airyAi' ξ| ≤ K₀ * √(1 + |ξ|) * airyWt ξ := by
  have hc1 : ContinuousOn airyAi (Set.Icc (-2 : ℝ) (-1)) := differentiable_airyAi.continuous.continuousOn
  have hc2 : ContinuousOn airyAi' (Set.Icc (-2 : ℝ) (-1)) :=
    (continuous_iff_continuousAt.2 fun x => (hasDerivAt_airyAi' x).continuousAt).continuousOn
  obtain ⟨M1, hM1⟩ := isCompact_Icc.exists_bound_of_continuousOn hc1
  obtain ⟨M2, hM2⟩ := isCompact_Icc.exists_bound_of_continuousOn hc2
  have hM1' : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 (-2) ⟨le_rfl, by norm_num⟩)
  have hM2' : 0 ≤ M2 := le_trans (norm_nonneg _) (hM2 (-2) ⟨le_rfl, by norm_num⟩)
  refine ⟨1080 + 2 * M1 + 2 * M2, by positivity, ?_⟩
  intro ξ hξ
  rcases le_or_gt (-1) ξ with h1 | h1
  · have hw := airyWt_pos ξ
    have hAi := airyAi_le_six_airyWt h1
    have hApos : 0 < airyAi ξ := lt_of_lt_of_le (by positivity) (airyWt_div_twenty_le_airyAi h1)
    have hd := abs_airyAi'_le_airyWt h1
    have hs : √(2 + |ξ|) ≤ 3 / 2 * √(1 + |ξ|) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      nlinarith [abs_nonneg ξ]
    have hr := Real.sqrt_nonneg (1 + |ξ|)
    refine ⟨?_, ?_⟩
    · rw [abs_of_pos hApos]; nlinarith
    · calc |airyAi' ξ| ≤ 720 * √(2 + |ξ|) * airyWt ξ := hd
        _ ≤ 720 * (3 / 2 * √(1 + |ξ|)) * airyWt ξ := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hr hw.le]
  · -- `ξ ∈ [-2, -1)`: `airyWt ξ ≥ 1/2`
    have hmem : ξ ∈ Set.Icc (-2 : ℝ) (-1) := ⟨hξ, h1.le⟩
    have hneg : ξ < 0 := by linarith
    have hX0 : airyXi ξ = 0 := by
      unfold airyXi; rw [max_eq_right hneg.le, Real.zero_rpow (by norm_num)]; ring
    have habs : |ξ| ≤ 2 := by rw [abs_of_neg hneg]; linarith
    have hw : 1 / 2 ≤ airyWt ξ := by
      unfold airyWt
      rw [hX0, neg_zero, Real.exp_zero, mul_one]
      have hle : 2 + |ξ| ≤ 16 := by linarith
      have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 2 + |ξ|) hle
        (by norm_num : -(1 / 4 : ℝ) ≤ 0)
      refine le_trans ?_ this
      have e : (16 : ℝ) ^ (-(1 / 4) : ℝ) = 1 / 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
      rw [e]
    have hs1 : 1 ≤ √(1 + |ξ|) := by
      calc (1 : ℝ) = √1 := by simp
        _ ≤ √(1 + |ξ|) := Real.sqrt_le_sqrt (by linarith [abs_nonneg ξ])
    have a1 := hM1 ξ hmem
    have a2 := hM2 ξ hmem
    rw [Real.norm_eq_abs] at a1 a2
    refine ⟨?_, ?_⟩
    · nlinarith
    · nlinarith [mul_nonneg hM2' (sub_nonneg.2 hs1), mul_nonneg (sub_nonneg.2 hs1) (sub_nonneg.2 hw)]

/-- The fifth jet: `|4ξ Ai + ξ² Ai'| ≤ 5 K₀ u² √u airyWt` for `ξ ≥ -2`, `u = 1 + |ξ|`. -/
lemma airyJet5_bound {K₀ : ℝ} (hK : ∀ ξ : ℝ, -2 ≤ ξ →
      |airyAi ξ| ≤ K₀ * airyWt ξ ∧ |airyAi' ξ| ≤ K₀ * √(1 + |ξ|) * airyWt ξ)
    {ξ : ℝ} (hξ : -2 ≤ ξ) :
    |4 * ξ * airyAi ξ + ξ ^ 2 * airyAi' ξ| ≤
      5 * K₀ * ((1 + |ξ|) ^ 2 * √(1 + |ξ|)) * airyWt ξ := by
  obtain ⟨h1, h2⟩ := hK ξ hξ
  have hK0 : 0 ≤ K₀ := by
    have := le_trans (abs_nonneg _) h1
    have hw := airyWt_pos ξ
    by_contra h; have h' := not_le.1 h; nlinarith
  have hw := airyWt_pos ξ
  set u := 1 + |ξ| with hu
  have hu1 : 1 ≤ u := by linarith [abs_nonneg ξ]
  have hr1 : 1 ≤ √u := by
    calc (1 : ℝ) = √1 := by simp
      _ ≤ √u := Real.sqrt_le_sqrt hu1
  have hξu : |ξ| ≤ u := by linarith
  have hkey : u ≤ u ^ 2 * √u := by nlinarith
  calc |4 * ξ * airyAi ξ + ξ ^ 2 * airyAi' ξ|
      ≤ |4 * ξ * airyAi ξ| + |ξ ^ 2 * airyAi' ξ| := abs_add_le _ _
    _ = 4 * |ξ| * |airyAi ξ| + |ξ| ^ 2 * |airyAi' ξ| := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow]; norm_num
    _ ≤ 4 * u * (K₀ * airyWt ξ) + u ^ 2 * (K₀ * √u * airyWt ξ) := by
        gcongr
    _ ≤ 4 * (u ^ 2 * √u) * (K₀ * airyWt ξ) + u ^ 2 * (K₀ * √u * airyWt ξ) := by
        have := mul_nonneg hK0 hw.le
        nlinarith
    _ = 4 * K₀ * (u ^ 2 * √u) * airyWt ξ + K₀ * (u ^ 2 * √u) * airyWt ξ := by ring
    _ = _ := by ring

/-- The sixth jet: `|(ξ³+4) Ai + 6ξ Ai'| ≤ 11 K₀ u³ airyWt` for `ξ ≥ -2`, `u = 1 + |ξ|`. -/
lemma airyJet6_bound {K₀ : ℝ} (hK : ∀ ξ : ℝ, -2 ≤ ξ →
      |airyAi ξ| ≤ K₀ * airyWt ξ ∧ |airyAi' ξ| ≤ K₀ * √(1 + |ξ|) * airyWt ξ)
    {ξ : ℝ} (hξ : -2 ≤ ξ) :
    |(ξ ^ 3 + 4) * airyAi ξ + 6 * ξ * airyAi' ξ| ≤ 11 * K₀ * (1 + |ξ|) ^ 3 * airyWt ξ := by
  obtain ⟨h1, h2⟩ := hK ξ hξ
  have hK0 : 0 ≤ K₀ := by
    have := le_trans (abs_nonneg _) h1
    have hw := airyWt_pos ξ
    by_contra h; have h' := not_le.1 h; nlinarith
  have hw := airyWt_pos ξ
  set u := 1 + |ξ| with hu
  have hu1 : 1 ≤ u := by linarith [abs_nonneg ξ]
  have hr1 : 1 ≤ √u := by
    calc (1 : ℝ) = √1 := by simp
      _ ≤ √u := Real.sqrt_le_sqrt hu1
  have hru : √u ≤ u := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hξu : |ξ| ≤ u := by linarith
  have hA3 : |ξ ^ 3 + 4| ≤ u ^ 3 + 4 := by
    calc |ξ ^ 3 + 4| ≤ |ξ ^ 3| + |(4 : ℝ)| := abs_add_le _ _
      _ = |ξ| ^ 3 + 4 := by rw [abs_pow]; norm_num
      _ ≤ u ^ 3 + 4 := by gcongr
  calc |(ξ ^ 3 + 4) * airyAi ξ + 6 * ξ * airyAi' ξ|
      ≤ |(ξ ^ 3 + 4) * airyAi ξ| + |6 * ξ * airyAi' ξ| := abs_add_le _ _
    _ = |ξ ^ 3 + 4| * |airyAi ξ| + 6 * |ξ| * |airyAi' ξ| := by
        rw [abs_mul, abs_mul, abs_mul]; norm_num
    _ ≤ (u ^ 3 + 4) * (K₀ * airyWt ξ) + 6 * u * (K₀ * √u * airyWt ξ) := by
        gcongr
    _ ≤ (u ^ 3 + 4 * u ^ 3) * (K₀ * airyWt ξ) + 6 * u ^ 3 * (K₀ * airyWt ξ) := by
        have h0 : 0 ≤ K₀ * airyWt ξ := mul_nonneg hK0 hw.le
        have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
        have e : 6 * u * (K₀ * √u * airyWt ξ) = 6 * (u * √u) * (K₀ * airyWt ξ) := by ring
        have hur : u * √u ≤ u ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hru (by linarith : (0 : ℝ) ≤ u)]
        rw [e]
        nlinarith [mul_le_mul_of_nonneg_right hur h0]
    _ = _ := by ring

/-- Geometry of a segment `[X, X+s]`: for `t ∈ [0, s]`, `X + t ≥ -2`, `1 + |X + t| ≤ 2 (1 + |X|)` and
`airyWt (X + t) ≤ (6/5) e^Λ airyWt X`, provided `X ≥ -1`, `|s| ≤ 1`, `|s| √(1+|X|) ≤ Λ`. -/
lemma airy_segment_geometry {X s Λ : ℝ} (hX : -1 ≤ X) (hs1 : |s| ≤ 1)
    (hΛ : |s| * √(1 + |X|) ≤ Λ) {t : ℝ} (ht : t ∈ uIcc 0 s) :
    -2 ≤ X + t ∧ 1 + |X + t| ≤ 2 * (1 + |X|) ∧
      airyWt (X + t) ≤ 6 / 5 * Real.exp Λ * airyWt X := by
  have hts := abs_le_abs_of_mem_uIcc ht
  have ht1 : |t| ≤ 1 := hts.trans hs1
  refine ⟨?_, ?_, ?_⟩
  · have := neg_abs_le t; linarith
  · have := abs_add_le X t; linarith [abs_nonneg X]
  · refine airyWt_le_of_close (X := X) (ξ := X + t) (Λ := Λ) (by simpa using ht1) ?_
    simp only [add_sub_cancel_left]
    exact le_trans (mul_le_mul_of_nonneg_right hts (Real.sqrt_nonneg _)) hΛ

/-- **Taylor remainder for `Ai`, orders 4 / 3.**  There is `K > 0` such that for all `X ≥ -1`, `|s| ≤ 1`,
`Λ ≥ |s| √(1+|X|)`, with `u = 1 + |X|`,
`|Ai(X+s) - T₄| ≤ K e^Λ |s|⁵ u² √u airyWt X` and `|Ai'(X+s) - T₃'| ≤ K e^Λ |s|⁴ u² √u airyWt X`
(`T₄`, `T₃'` as in `airy_sol_taylor4`).  `K` is existential (not explicit); the hypothesis on `Λ` is necessary
(module docstring).  This is the Taylor step of `EC:78-86` (`lem:ec-defect`). -/
theorem airy_taylor4 : ∃ K : ℝ, 0 < K ∧ ∀ (X s Λ : ℝ), -1 ≤ X → |s| ≤ 1 → |s| * √(1 + |X|) ≤ Λ →
    |airyAi (X + s) - (airyAi X + s * airyAi' X + s ^ 2 / 2 * (X * airyAi X) +
        s ^ 3 / 6 * (airyAi X + X * airyAi' X) + s ^ 4 / 24 * (X ^ 2 * airyAi X + 2 * airyAi' X))|
      ≤ K * Real.exp Λ * |s| ^ 5 * ((1 + |X|) ^ 2 * √(1 + |X|)) * airyWt X ∧
    |airyAi' (X + s) - (airyAi' X + s * (X * airyAi X) + s ^ 2 / 2 * (airyAi X + X * airyAi' X) +
        s ^ 3 / 6 * (X ^ 2 * airyAi X + 2 * airyAi' X))|
      ≤ K * Real.exp Λ * |s| ^ 4 * ((1 + |X|) ^ 2 * √(1 + |X|)) * airyWt X := by
  obtain ⟨K₀, hK₀, hK⟩ := airy_envelope_ge_neg_two
  refine ⟨36 * K₀, by positivity, ?_⟩
  intro X s Λ hX hs1 hΛ
  have hB : ∀ t ∈ uIcc 0 s, |4 * (X + t) * airyAi (X + t) + (X + t) ^ 2 * airyAi' (X + t)| ≤
      36 * K₀ * Real.exp Λ * ((1 + |X|) ^ 2 * √(1 + |X|)) * airyWt X := by
    intro t ht
    obtain ⟨g1, g2, g3⟩ := airy_segment_geometry hX hs1 hΛ ht
    refine (airyJet5_bound hK g1).trans ?_
    set u := 1 + |X|
    set v := 1 + |X + t|
    have hv1 : 1 ≤ v := by linarith [abs_nonneg (X + t)]
    have hu1 : 1 ≤ u := by linarith [abs_nonneg X]
    have hpoly : v ^ 2 * √v ≤ 6 * (u ^ 2 * √u) := by
      have h1 : v ^ 2 ≤ 4 * u ^ 2 := by nlinarith
      have h2 : √v ≤ 3 / 2 * √u := by
        rw [Real.sqrt_le_iff]
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt (by linarith)]; nlinarith
      have := mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
      nlinarith
    have hwpos := airyWt_pos X
    have hE := Real.exp_pos Λ
    calc 5 * K₀ * (v ^ 2 * √v) * airyWt (X + t)
        ≤ 5 * K₀ * (6 * (u ^ 2 * √u)) * (6 / 5 * Real.exp Λ * airyWt X) := by
          have h0 : 0 ≤ 5 * K₀ := by positivity
          have := mul_le_mul_of_nonneg_left hpoly h0
          exact mul_le_mul this g3 (airyWt_pos _).le (by positivity)
      _ = _ := by ring
  obtain ⟨c1, c2⟩ := airy_sol_taylor4 isAirySol_airyAi X s _ hB
  exact ⟨by convert c1 using 1; ring, by convert c2 using 1; ring⟩

/-- **Taylor remainder for `Ai`, orders 5 / 4.**  There is `K > 0` such that for all `X ≥ -1`, `|s| ≤ 1`,
`Λ ≥ |s| √(1+|X|)`, `u = 1 + |X|`:
`|Ai(X+s) - T₅| ≤ K e^Λ |s|⁶ u³ airyWt X`, `|Ai'(X+s) - T₄'| ≤ K e^Λ |s|⁵ u³ airyWt X`
(`T₅`, `T₄'` as in `airy_sol_taylor5`). -/
theorem airy_taylor5 : ∃ K : ℝ, 0 < K ∧ ∀ (X s Λ : ℝ), -1 ≤ X → |s| ≤ 1 → |s| * √(1 + |X|) ≤ Λ →
    |airyAi (X + s) - (airyAi X + s * airyAi' X + s ^ 2 / 2 * (X * airyAi X) +
        s ^ 3 / 6 * (airyAi X + X * airyAi' X) + s ^ 4 / 24 * (X ^ 2 * airyAi X + 2 * airyAi' X) +
        s ^ 5 / 120 * (4 * X * airyAi X + X ^ 2 * airyAi' X))|
      ≤ K * Real.exp Λ * |s| ^ 6 * (1 + |X|) ^ 3 * airyWt X ∧
    |airyAi' (X + s) - (airyAi' X + s * (X * airyAi X) + s ^ 2 / 2 * (airyAi X + X * airyAi' X) +
        s ^ 3 / 6 * (X ^ 2 * airyAi X + 2 * airyAi' X) +
        s ^ 4 / 24 * (4 * X * airyAi X + X ^ 2 * airyAi' X))|
      ≤ K * Real.exp Λ * |s| ^ 5 * (1 + |X|) ^ 3 * airyWt X := by
  obtain ⟨K₀, hK₀, hK⟩ := airy_envelope_ge_neg_two
  refine ⟨106 * K₀, by positivity, ?_⟩
  intro X s Λ hX hs1 hΛ
  have hB : ∀ t ∈ uIcc 0 s, |((X + t) ^ 3 + 4) * airyAi (X + t) + 6 * (X + t) * airyAi' (X + t)| ≤
      106 * K₀ * Real.exp Λ * (1 + |X|) ^ 3 * airyWt X := by
    intro t ht
    obtain ⟨g1, g2, g3⟩ := airy_segment_geometry hX hs1 hΛ ht
    refine (airyJet6_bound hK g1).trans ?_
    set u := 1 + |X|
    set v := 1 + |X + t|
    have hv1 : 1 ≤ v := by linarith [abs_nonneg (X + t)]
    have hu1 : 1 ≤ u := by linarith [abs_nonneg X]
    have hpoly : v ^ 3 ≤ 8 * u ^ 3 := by
      calc v ^ 3 ≤ (2 * u) ^ 3 := by gcongr
        _ = 8 * u ^ 3 := by ring
    have hwpos := airyWt_pos X
    have hE := Real.exp_pos Λ
    calc 11 * K₀ * v ^ 3 * airyWt (X + t)
        ≤ 11 * K₀ * (8 * u ^ 3) * (6 / 5 * Real.exp Λ * airyWt X) := by
          have h0 : 0 ≤ 11 * K₀ := by positivity
          have := mul_le_mul_of_nonneg_left hpoly h0
          exact mul_le_mul this g3 (airyWt_pos _).le (by positivity)
      _ ≤ _ := by
          have hP : 0 ≤ K₀ * Real.exp Λ * u ^ 3 * airyWt X := by positivity
          have e1 : 11 * K₀ * (8 * u ^ 3) * (6 / 5 * Real.exp Λ * airyWt X) =
              (528 / 5) * (K₀ * Real.exp Λ * u ^ 3 * airyWt X) := by ring
          have e2 : 106 * K₀ * Real.exp Λ * u ^ 3 * airyWt X =
              106 * (K₀ * Real.exp Λ * u ^ 3 * airyWt X) := by ring
          rw [e1, e2]; linarith
  obtain ⟨c1, c2⟩ := airy_sol_taylor5 isAirySol_airyAi X s _ hB
  exact ⟨by convert c1 using 1; ring, by convert c2 using 1; ring⟩

/-! ### First terms of `C(X,s)`, `S(X,s)` -/

/-- `ξ ↦ C(X, ξ - X)` solves `y'' = ξ y`. -/
theorem isAirySol_airyShiftC_shifted (X : ℝ) :
    IsAirySol (fun ξ => airyShiftC X (ξ - X)) (fun ξ => airyShiftCd X (ξ - X)) := by
  intro ξ
  refine ⟨(hasDerivAt_airyShiftC X (ξ - X)).comp_sub_const ξ X, ?_⟩
  exact ((hasDerivAt_airyShiftCd X (ξ - X)).comp_sub_const ξ X).congr_deriv (by ring)

/-- `ξ ↦ S(X, ξ - X)` solves `y'' = ξ y`. -/
theorem isAirySol_airyShiftS_shifted (X : ℝ) :
    IsAirySol (fun ξ => airyShiftS X (ξ - X)) (fun ξ => airyShiftSd X (ξ - X)) := by
  intro ξ
  refine ⟨(hasDerivAt_airyShiftS X (ξ - X)).comp_sub_const ξ X, ?_⟩
  exact ((hasDerivAt_airyShiftSd X (ξ - X)).comp_sub_const ξ X).congr_deriv (by ring)

/-- `C(X,s) = 1 + X s²/2 + s³/6 + X² s⁴/24 + X s⁵/30 + O(s⁶)`; the remainder is `≤ B |s|⁶` if
`|(ξ³+4) C + 6ξ C_s| ≤ B` on the segment (`ξ = X + t`, `C = C(X,t)`, `C_s = C_s(X,t)`). -/
theorem airyShiftC_taylor (X s B : ℝ)
    (hB : ∀ t ∈ uIcc 0 s,
      |((X + t) ^ 3 + 4) * airyShiftC X t + 6 * (X + t) * airyShiftCd X t| ≤ B) :
    |airyShiftC X s - (1 + X * s ^ 2 / 2 + s ^ 3 / 6 + X ^ 2 * s ^ 4 / 24 + X * s ^ 5 / 30)|
      ≤ B * |s| ^ 6 := by
  obtain ⟨h1, -, h3, -⟩ := airyShift_initial X
  obtain ⟨h2, -⟩ := airy_sol_taylor5 (isAirySol_airyShiftC_shifted X) X s B
    (by simpa using hB)
  simp only [sub_self, add_sub_cancel_left, h1, airyShift_initial] at h2
  convert h2 using 2
  ring

/-- `S(X,s) = s + X s³/6 + s⁴/12 + X² s⁵/120 + O(s⁶)`; remainder `≤ B |s|⁶` if
`|(ξ³+4) S + 6ξ S_s| ≤ B` on the segment. -/
theorem airyShiftS_taylor (X s B : ℝ)
    (hB : ∀ t ∈ uIcc 0 s,
      |((X + t) ^ 3 + 4) * airyShiftS X t + 6 * (X + t) * airyShiftSd X t| ≤ B) :
    |airyShiftS X s - (s + X * s ^ 3 / 6 + s ^ 4 / 12 + X ^ 2 * s ^ 5 / 120)| ≤ B * |s| ^ 6 := by
  obtain ⟨-, -, h3, h4⟩ := airyShift_initial X
  obtain ⟨h2, -⟩ := airy_sol_taylor5 (isAirySol_airyShiftS_shifted X) X s B
    (by simpa using hB)
  simp only [sub_self, add_sub_cancel_left, h3, h4] at h2
  convert h2 using 2
  ring

/-- info: 'FormalResearch.Special.airy_taylor4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_taylor4

/-- info: 'FormalResearch.Special.airy_taylor5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_taylor5

/-- info: 'FormalResearch.Special.airy_sol_taylor4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sol_taylor4

/-- info: 'FormalResearch.Special.airy_sol_taylor5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airy_sol_taylor5

/-- info: 'FormalResearch.Special.airyShiftC_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyShiftC_taylor

/-- info: 'FormalResearch.Special.airyShiftS_taylor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyShiftS_taylor

end FormalResearch.Special

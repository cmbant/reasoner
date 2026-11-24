module

public import Mathlib

/-!
# Uniform `O(h^n)` bounds from pointwise ones

If each member `f θ` of a family of real functions is `C^n` near `0` and `O(h^n)` there, and the
`n`-th derivative is jointly continuous in `(θ, h)` on a compact parameter set, then the bound is
uniform in `θ` (`uniform_bigO_of_pointwise`).  The two steps are elementary:
* `iteratedDeriv_eq_zero_of_bigO`: a `C^n` function that is `O(h^n)` at `0` has vanishing
  derivatives of order `< n` at `0` (by the lower bound `lower_bound_of_iteratedDeriv`);
* `abs_le_of_iteratedDeriv`: with those derivatives zero, `|g h| ≤ M |h|^n` whenever `M` bounds the
  `n`-th derivative on `[-|h|, |h|]` (iterated mean value theorem).

Used for the defect bounds of the corrector theorem, whose constants must be uniform in the
spectral parameter and the symbol parameter (Paper J, `LadderData.Valid`).
-/

@[expose] public section

open Set

namespace FormalResearch.Analysis

/-- **Iterated mean value bound.** If `g` is `C^n` on `(-δ₀, δ₀)` with vanishing derivatives of order
`< n` at `0`, and `|g^{(n)}| ≤ M` on `[-|h|, |h|]`, then `|g h| ≤ M |h|^n`. -/
theorem abs_le_of_iteratedDeriv {δ₀ : ℝ} :
    ∀ (n : ℕ) (g : ℝ → ℝ), ContDiffOn ℝ n g (Ioo (-δ₀) δ₀) →
      (∀ k < n, iteratedDeriv k g 0 = 0) →
      ∀ h, |h| < δ₀ → ∀ M, (∀ t, |t| ≤ |h| → |iteratedDeriv n g t| ≤ M) → |g h| ≤ M * |h| ^ n
  | 0, g, _, _, h, _, M, hM => by simpa using hM h le_rfl
  | n + 1, g, hg, h0, h, hh, M, hM => by
    have hU : IsOpen (Ioo (-δ₀) δ₀) := isOpen_Ioo
    have hg1 := hg
    push_cast at hg1
    have hg' := (contDiffOn_succ_iff_deriv_of_isOpen hU).1 hg1
    have hmem : ∀ t, |t| ≤ |h| → t ∈ Ioo (-δ₀) δ₀ := fun t ht => by
      rw [mem_Ioo]; constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
    -- the derivative satisfies the hypotheses at order `n`
    have hd0 : ∀ k < n, iteratedDeriv k (deriv g) 0 = 0 := fun k hk => by
      rw [← iteratedDeriv_succ']; exact h0 (k + 1) (by omega)
    have hdb : ∀ t, |t| ≤ |h| → |deriv g t| ≤ M * |h| ^ n := fun t ht => by
      have hMt : ∀ s, |s| ≤ |t| → |iteratedDeriv n (deriv g) s| ≤ M := fun s hs => by
        rw [← iteratedDeriv_succ']; exact hM s (hs.trans ht)
      have := abs_le_of_iteratedDeriv n (deriv g) (by exact_mod_cast hg'.2.2) hd0 t
        (lt_of_le_of_lt ht hh) M hMt
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by simp))
      calc |deriv g t| ≤ M * |t| ^ n := this
        _ ≤ M * |h| ^ n := by gcongr
    -- mean value theorem on `[-|h|, |h|]`
    have hconv : Convex ℝ (Icc (-|h|) |h|) := convex_Icc _ _
    have hdiff : ∀ x ∈ Icc (-|h|) |h|, DifferentiableAt ℝ g x := fun x hx =>
      (hg'.1 x (hmem x (abs_le.2 hx))).differentiableAt (hU.mem_nhds (hmem x (abs_le.2 hx)))
    have hbound : ∀ x ∈ Icc (-|h|) |h|, ‖deriv g x‖ ≤ M * |h| ^ n := fun x hx => hdb x (abs_le.2 hx)
    have hmvt := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound
      (show (0 : ℝ) ∈ Icc (-|h|) |h| by simp) (show h ∈ Icc (-|h|) |h| from abs_le.1 le_rfl)
    have hg00 : g 0 = 0 := by simpa using h0 0 (by omega)
    simp only [hg00, sub_zero, Real.norm_eq_abs] at hmvt
    calc |g h| ≤ M * |h| ^ n * |h| := hmvt
      _ = M * |h| ^ (n + 1) := by ring

/-- **Iterated lower bound.** If `g` is `C^n` on `(-δ₀, δ₀)` with vanishing derivatives of order `< n`
at `0`, `0 ≤ h < δ₀`, and `m ≤ g^{(n)}` on `[0, h]`, then `m h^n / n! ≤ g h`. -/
theorem lower_bound_of_iteratedDeriv {δ₀ : ℝ} :
    ∀ (n : ℕ) (g : ℝ → ℝ), ContDiffOn ℝ n g (Ioo (-δ₀) δ₀) →
      (∀ k < n, iteratedDeriv k g 0 = 0) →
      ∀ h, 0 ≤ h → h < δ₀ → ∀ m, (∀ t ∈ Icc 0 h, m ≤ iteratedDeriv n g t) →
        m * h ^ n / n.factorial ≤ g h
  | 0, g, _, _, h, h0, _, m, hm => by simpa using hm h ⟨h0, le_rfl⟩
  | n + 1, g, hg, h0, h, hh0, hh, m, hm => by
    have hU : IsOpen (Ioo (-δ₀) δ₀) := isOpen_Ioo
    have hg1 := hg
    push_cast at hg1
    have hg' := (contDiffOn_succ_iff_deriv_of_isOpen hU).1 hg1
    have hδ : 0 < δ₀ := lt_of_le_of_lt hh0 hh
    have hmem : ∀ t ∈ Icc 0 h, t ∈ Ioo (-δ₀) δ₀ := fun t ht =>
      ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 hh⟩
    have hd0 : ∀ k < n, iteratedDeriv k (deriv g) 0 = 0 := fun k hk => by
      rw [← iteratedDeriv_succ']; exact h0 (k + 1) (by omega)
    -- lower bound for the derivative on `[0, h]`
    have hdl : ∀ t ∈ Icc 0 h, m * t ^ n / n.factorial ≤ deriv g t := fun t ht =>
      lower_bound_of_iteratedDeriv n (deriv g) (by exact_mod_cast hg'.2.2) hd0 t ht.1
        (lt_of_le_of_lt ht.2 hh) m fun s hs => by
          rw [← iteratedDeriv_succ']; exact hm s ⟨hs.1, hs.2.trans ht.2⟩
    -- `φ = g - m t^{n+1}/(n+1)!` is monotone on `[0, h]`
    let φ : ℝ → ℝ := fun t => g t - m * t ^ (n + 1) / (n + 1).factorial
    have hφd : ∀ t ∈ Icc 0 h, HasDerivAt φ (deriv g t - m * t ^ n / n.factorial) t := fun t ht => by
      have h1 : HasDerivAt g (deriv g t) t :=
        ((hg'.1 t (hmem t ht)).differentiableAt (hU.mem_nhds (hmem t ht))).hasDerivAt
      have h2 := ((hasDerivAt_pow (n + 1) t).const_mul m).div_const ((n + 1).factorial : ℝ)
      refine (h1.sub h2).congr_deriv ?_
      rw [Nat.factorial_succ]; push_cast
      field_simp
    have hmono : MonotoneOn φ (Icc 0 h) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc 0 h) ?_ ?_ ?_
      · exact fun t ht => (hφd t ht).continuousAt.continuousWithinAt
      · exact fun t ht => (hφd t (interior_subset ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        have ht' := interior_subset ht
        rw [(hφd t ht').deriv]; linarith [hdl t ht']
    have hφ := hmono ⟨le_rfl, hh0⟩ ⟨hh0, le_rfl⟩ hh0
    have hg00 : g 0 = 0 := by simpa using h0 0 (by omega)
    simp only [φ, hg00, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      zero_pow, mul_zero, zero_div, sub_zero] at hφ
    linarith

/-- **Vanishing derivatives.** A function `C^n` on `(-δ₀, δ₀)`, `δ₀ > 0`, that is `O(h^n)` at `0` has
vanishing derivatives of every order `< n` at `0`. -/
theorem iteratedDeriv_eq_zero_of_bigO {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {n : ℕ} {g : ℝ → ℝ}
    (hg : ContDiffOn ℝ n g (Ioo (-δ₀) δ₀)) {C δ : ℝ} (hδ : 0 < δ)
    (hC : ∀ h, |h| < δ → |g h| ≤ C * |h| ^ n) :
    ∀ k < n, iteratedDeriv k g 0 = 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  have hU : IsOpen (Ioo (-δ₀) δ₀) := isOpen_Ioo
  have h0U : (0 : ℝ) ∈ Ioo (-δ₀) δ₀ := ⟨by linarith, hδ₀⟩
  by_contra hc
  set c := iteratedDeriv k g 0 with hc_def
  -- normalise the sign
  set σ : ℝ := if 0 < c then 1 else -1 with hσ
  have hσc : 0 < σ * c := by
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · simp only [hσ, not_lt.mpr hneg.le, ↓reduceIte]; linarith
    · simp only [hσ, hpos, ↓reduceIte]; linarith
  have hσabs : |σ| = 1 := by by_cases h : 0 < c <;> simp [hσ, h]
  let G : ℝ → ℝ := fun t => σ * g t
  have hGd : ∀ j, iteratedDeriv j G = fun t => σ * iteratedDeriv j g t := fun j =>
    funext fun _ => iteratedDeriv_const_mul_field σ g
  have hGk : ContDiffOn ℝ k G (Ioo (-δ₀) δ₀) :=
    (hg.of_le (by exact_mod_cast hk.le)).const_smul σ
  have hG0 : ∀ j < k, iteratedDeriv j G 0 = 0 := fun j hj => by
    rw [hGd j]; simp [ih j hj (by omega)]
  -- continuity of the `k`-th derivative at `0`
  have hcont : ContinuousAt (iteratedDeriv k G) 0 := by
    have h1 := hGk.continuousOn_iteratedDerivWithin le_rfl hU.uniqueDiffOn
    have h2 : ContinuousOn (iteratedDeriv k G) (Ioo (-δ₀) δ₀) :=
      h1.congr fun x hx => (iteratedDerivWithin_of_isOpen hU hx).symm
    exact h2.continuousAt (hU.mem_nhds h0U)
  set a := σ * c with ha
  have hGk0 : iteratedDeriv k G 0 = a := by rw [hGd k]
  obtain ⟨η, hη, hηb⟩ := Metric.continuousAt_iff.1 hcont (a / 2) (by linarith)
  have hlow : ∀ t, |t| < η → a / 2 ≤ iteratedDeriv k G t := fun t ht => by
    have := hηb (by simpa [Real.dist_eq] using ht)
    rw [Real.dist_eq, hGk0] at this
    linarith [(abs_lt.1 this).1]
  -- a small positive step
  have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  set h := min (min (η / 2) (δ / 2)) (min (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1)))))
    with hh_def
  have hpos : 0 < h := by
    simp only [hh_def, lt_min_iff]
    refine ⟨⟨by linarith, by linarith⟩, by linarith, by norm_num, by positivity⟩
  have hη' : h < η := by
    have := min_le_left (min (η / 2) (δ / 2)) (min (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1)))))
    linarith [min_le_left (η / 2) (δ / 2)]
  have hδ' : h < δ := by
    have := min_le_left (min (η / 2) (δ / 2)) (min (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1)))))
    linarith [min_le_right (η / 2) (δ / 2)]
  have hR := min_le_right (min (η / 2) (δ / 2)) (min (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1)))))
  have hδ₀' : h < δ₀ := by linarith [min_le_left (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1))))]
  have h1 : h ≤ 1 / 2 := by
    linarith [min_le_right (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1)))),
      min_le_left (1 / 2 : ℝ) (a / (4 * k.factorial * (|C| + 1)))]
  have hsmall : h ≤ a / (4 * k.factorial * (|C| + 1)) := by
    linarith [min_le_right (δ₀ / 2) (min (1 / 2) (a / (4 * k.factorial * (|C| + 1)))),
      min_le_right (1 / 2 : ℝ) (a / (4 * k.factorial * (|C| + 1)))]
  -- lower bound against the `O(h^n)` bound
  have hL := lower_bound_of_iteratedDeriv k G hGk hG0 h hpos.le hδ₀' (a / 2) fun t ht =>
    hlow t (by rw [abs_of_nonneg ht.1]; linarith [ht.2])
  have hU' : G h ≤ |C| * h ^ (k + 1) := by
    have hb := hC h (by rw [abs_of_pos hpos]; exact hδ')
    rw [abs_of_pos hpos] at hb
    have hpow : h ^ n ≤ h ^ (k + 1) := pow_le_pow_of_le_one hpos.le (by linarith) (by omega)
    calc G h ≤ |G h| := le_abs_self _
      _ = |g h| := by simp [G, abs_mul, hσabs]
      _ ≤ C * h ^ n := hb
      _ ≤ |C| * h ^ n := by gcongr; exact le_abs_self C
      _ ≤ |C| * h ^ (k + 1) := by gcongr
  have hhk : 0 < h ^ k := pow_pos hpos k
  have key : a / 2 / k.factorial ≤ |C| * h := by
    have e : a / 2 * h ^ k / k.factorial = (a / 2 / k.factorial) * h ^ k := by ring
    have e2 : |C| * h ^ (k + 1) = (|C| * h) * h ^ k := by ring
    have := hL.trans hU'
    rw [e, e2] at this
    exact le_of_mul_le_mul_right this hhk
  have hCh : |C| * h ≤ |C| * (a / (4 * k.factorial * (|C| + 1))) := by gcongr
  have ha0 : 0 < a := hσc
  have hq : |C| / (|C| + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  have hfin : |C| * (a / (4 * k.factorial * (|C| + 1))) < a / 2 / k.factorial := by
    calc |C| * (a / (4 * k.factorial * (|C| + 1))) = (a / (4 * k.factorial)) * (|C| / (|C| + 1)) := by
          field_simp
      _ < (a / (4 * k.factorial)) * 1 := by gcongr
      _ ≤ a / 2 / k.factorial := by
          rw [mul_one, div_div]; gcongr; linarith
  linarith

/-- **Uniform `O(h^n)` from pointwise `O(h^n)`.** Let `S` be a compact parameter set, `δ₀ > 0`, and
`f θ` be `C^n` on `(-δ₀, δ₀)` for `θ ∈ S`, with `(θ, h) ↦ (f θ)^{(n)}(h)` continuous on
`S × [-δ₀/2, δ₀/2]`.  If each `f θ` is `O(h^n)` at `0`, then the bound is uniform on `S`. -/
theorem uniform_bigO_of_pointwise {Θ : Type*} [TopologicalSpace Θ] {S : Set Θ} (hS : IsCompact S)
    {n : ℕ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) {f : Θ → ℝ → ℝ}
    (hdiff : ∀ θ ∈ S, ContDiffOn ℝ n (f θ) (Ioo (-δ₀) δ₀))
    (hcont : ContinuousOn (fun p : Θ × ℝ => iteratedDeriv n (f p.1) p.2) (S ×ˢ Icc (-(δ₀ / 2)) (δ₀ / 2)))
    (hpt : ∀ θ ∈ S, ∃ C δ : ℝ, 0 < δ ∧ ∀ h, |h| < δ → |f θ h| ≤ C * |h| ^ n) :
    ∃ C δ : ℝ, 0 < δ ∧ ∀ θ ∈ S, ∀ h, |h| < δ → |f θ h| ≤ C * |h| ^ n := by
  obtain ⟨M, hM⟩ := (hS.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨M, δ₀ / 2, by linarith, fun θ hθ h hh => ?_⟩
  obtain ⟨C, δ, hδ, hC⟩ := hpt θ hθ
  have hvan := iteratedDeriv_eq_zero_of_bigO hδ₀ (hdiff θ hθ) hδ hC
  refine abs_le_of_iteratedDeriv n (f θ) (hdiff θ hθ) hvan h (by linarith) M fun t ht => ?_
  have := hM (θ, t) ⟨hθ, abs_le.1 (ht.trans hh.le)⟩
  simpa [Real.norm_eq_abs] using this

/-- info: 'FormalResearch.Analysis.uniform_bigO_of_pointwise' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Analysis.uniform_bigO_of_pointwise

end FormalResearch.Analysis

module

public import FormalResearch.Special.AiryClarkMid
public import FormalResearch.Special.AiryKernelOpFormula
public import FormalResearch.Special.SturmAiryInterlace
public import FormalResearch.Special.AiryZeroSpacing

/-!
# Labelling of the Clark nodes of the Airy space: the zeros of `Ai' - c Ai`

Put `ψ_α = cos α · Ai - sin α · Ai'`; for `sin α ≠ 0`, `ψ_α = -sin α (Ai' - c Ai)` with `c = cot α`, so the zeros of `ψ_α` are the zeros
of `clark_c := Ai' - c Ai`.  This module proves (CFT `GENERAL_THEOREMS.md` §1, `STRUCTURAL_LINKS.md` §2.2, survey item T3), **all proved**:

* the *gaps*: `G_1 = (a_1, ∞)`, `G_n = (a_n, a_{n-1})` for `n ≥ 2` (`airyClarkGap`), on which `Ai ≠ 0`;
* **`m = Ai'/Ai` is strictly decreasing on every gap** (`strictAntiOn_airyRatio`), because `m' = -K(x,x)/Ai²` with
  `K(x,x) = Ai'² - x Ai² > 0` (`airyKer_diag_pos`);
* **existence and uniqueness of one zero of `Ai' - c Ai` in each gap** (`airyClark_existsUnique`), for every real `c`:
  for `n ≥ 2` this is the interlacing theorem `SturmAiry.IsSol.exists_unique_zero_combo_between` (with `α` such that `cot α = c`), for `n = 1`
  an intermediate-value argument on `[a_1, c²]` (`Ai'(a_1) > 0`; `Ai'(c²) < -|c| Ai(c²)` from `K > 0`);
* the nodes `z_n(c) := airyClarkNode c n` (`n ≥ 1`; the note's `z_n(α)` with `c = cot α`): **every real zero of `Ai' - c Ai` is exactly one
  `z_n(c)`** (`airyClark_zero_classification`; zeros of `Ai` are never zeros of `Ai' - c Ai`), **all zeros are simple**
  (`airyClark_simple`: derivative `Ai(x)(x - c²) ≠ 0`);
* **strict monotonicity in `c`**: `c₁ < c₂ → z_n(c₂) < z_n(c₁)` (`airyClarkNode_strictAnti`), the nodes **fill each gap** (`airyClarkNode_surjOn`,
  `z_n(Ai'(x)/Ai(x)) = x`), and the limits `z_n(c) → a_n` as `c → +∞`, `z_n(c) → a_{n-1}` as `c → -∞` (`n ≥ 2`), `z_1(c) → +∞` as `c → -∞`
  (`tendsto_airyClarkNode_atTop`, `tendsto_airyClarkNode_atBot`);
* in the angle parametrisation (`airyClarkAngleNode α n := z_n(cos α / sin α)`, `0 < α < π`; `α ↦ α + π` is the same function):
  `α ↦ z_n(α)` is **strictly increasing** on `(0, π)` and `z_1` is a **bijection of `(0, π)` onto `(a_1, ∞)`** (`airyClarkAngleNode_strictMonoOn`,
  `airyClarkAngleNode_bijOn`), as in the note: `z_1(α)` increases from `a_1` through `a'_1` (`α = π/2`) to `+∞`, and `z_n(α) → a_n` as
  `α → 0⁺`, `→ a_{n-1}` as `α → 0⁻ ≡ π⁻`.

Asymptotic location (the nodes lie half-way between consecutive zeros) is `AiryClarkLabelAsym`.  Not formalised: the node phase
`ψ_α(-v) ≍ v^{1/4} cos(ζ + π/4 + O(v^{-1/2}))` itself (only its consequence for the node location is proved), `α = 0` (where the zeros are `a_n`,
`airyZero`), and the identification with the Clark/de Branges measure of the space (the labelling of its atoms `K(z,z)^{-1}`).
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special

open SturmAiry

/-- `K(x,x) = Ai'² - x Ai² > 0`. -/
lemma airyKer_pos' (x : ℝ) : 0 < airyAi' x ^ 2 - x * airyAi x ^ 2 := by
  have := airyKer_diag_pos x
  rwa [airyKer_self] at this

/-- The gaps of the zeros of `Ai`: `G_1 = (a_1, ∞)` and `G_n = (a_n, a_{n-1})` for `n ≥ 2`. -/
noncomputable def airyClarkGap (n : ℕ) : Set ℝ :=
  if n = 1 then Ioi (airyZero 1) else Ioo (airyZero n) (airyZero (n - 1))

lemma airyClarkGap_one : airyClarkGap 1 = Ioi (airyZero 1) := by simp [airyClarkGap]

lemma airyClarkGap_of_ne {n : ℕ} (h : n ≠ 1) : airyClarkGap n = Ioo (airyZero n) (airyZero (n - 1)) := by
  simp [airyClarkGap, h]

lemma mem_airyClarkGap {n : ℕ} {x : ℝ} :
    x ∈ airyClarkGap n ↔ airyZero n < x ∧ (n = 1 ∨ x < airyZero (n - 1)) := by
  unfold airyClarkGap
  split_ifs with h
  · subst h; simp
  · simp [h]

lemma isOpen_airyClarkGap (n : ℕ) : IsOpen (airyClarkGap n) := by
  unfold airyClarkGap; split_ifs
  · exact isOpen_Ioi
  · exact isOpen_Ioo

lemma convex_airyClarkGap (n : ℕ) : Convex ℝ (airyClarkGap n) := by
  unfold airyClarkGap; split_ifs
  · exact convex_Ioi _
  · exact convex_Ioo _ _

/-- `a_m ≤ a_n` for `1 ≤ n ≤ m`. -/
lemma airyZero_le_of_le {n m : ℕ} (hn : 1 ≤ n) (h : n ≤ m) : airyZero m ≤ airyZero n := by
  rcases h.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (airyZero_lt_of_lt hn h).le

/-- `Ai` has no zero in a gap. -/
lemma airyAi_ne_zero_of_mem_gap {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ airyClarkGap n) : airyAi x ≠ 0 := by
  intro h0
  rw [mem_airyClarkGap] at hx
  obtain ⟨h1, h2⟩ := hx
  have hx0 : x ≤ 0 := by
    by_contra hpos
    push Not at hpos
    exact (airyAi_pos hpos.le).ne' h0
  by_cases hn1 : n = 1
  · subst hn1
    obtain ⟨m, hm, rfl⟩ := exists_airyZero_eq h0 hx0
    have := airyZero_le_of_le (le_refl 1) hm
    linarith
  · have h2' : x < airyZero (n - 1) := h2.resolve_left hn1
    have := airyZero_next (n := n - 1) (by omega) h0 h2'
    have e : n - 1 + 1 = n := by omega
    rw [e] at this
    linarith

/-- The ratio `m = Ai'/Ai`. -/
noncomputable def airyRatio (x : ℝ) : ℝ := airyAi' x / airyAi x

lemma hasDerivAt_airyRatio {x : ℝ} (hx : airyAi x ≠ 0) :
    HasDerivAt airyRatio (-(airyAi' x ^ 2 - x * airyAi x ^ 2) / airyAi x ^ 2) x := by
  have h1 := isSol_airyAi.hasDerivAt x
  have h2 := isSol_airyAi.hasDerivAt' x
  have := h2.div h1 hx
  show HasDerivAt (fun y => airyAi' y / airyAi y) _ x
  refine this.congr_deriv ?_
  ring

lemma continuousOn_airyRatio {n : ℕ} (hn : 1 ≤ n) : ContinuousOn airyRatio (airyClarkGap n) := fun _ hx =>
  (hasDerivAt_airyRatio (airyAi_ne_zero_of_mem_gap hn hx)).continuousAt.continuousWithinAt

/-- **`m = Ai'/Ai` is strictly decreasing on every gap** (`m' = -K(x,x)/Ai² < 0`). -/
theorem strictAntiOn_airyRatio {n : ℕ} (hn : 1 ≤ n) : StrictAntiOn airyRatio (airyClarkGap n) := by
  refine strictAntiOn_of_deriv_neg (convex_airyClarkGap n) (continuousOn_airyRatio hn) ?_
  intro x hx
  rw [(isOpen_airyClarkGap n).interior_eq] at hx
  have hAi := airyAi_ne_zero_of_mem_gap hn hx
  rw [(hasDerivAt_airyRatio hAi).deriv]
  have := airyKer_pos' x
  have h2 : 0 < airyAi x ^ 2 := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos this) h2

/-- `Ai > 0` on `(a_1, ∞)`. -/
lemma airyAi_pos_of_gt_first {x : ℝ} (hx : airyZero 1 < x) : 0 < airyAi x := by
  by_contra hle
  push Not at hle
  have h0 : (0 : ℝ) ∈ Ioi (airyZero 1) := by simpa using airyZero_neg 1
  have hsub : uIcc x 0 ⊆ Ioi (airyZero 1) := (ordConnected_Ioi).uIcc_subset hx h0
  have hmem : 0 ∈ uIcc (airyAi x) (airyAi 0) := by
    rw [mem_uIcc]; left; exact ⟨hle, (airyAi_pos le_rfl).le⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc continuous_airyAi.continuousOn hmem
  have hzg : z ∈ airyClarkGap 1 := by
    rw [mem_airyClarkGap]; exact ⟨hsub hz, Or.inl rfl⟩
  exact airyAi_ne_zero_of_mem_gap le_rfl hzg hz0

/-- `Ai'(a_1) > 0` (the first zero is crossed upwards). -/
lemma airyAi'_first_pos : 0 < airyAi' (airyZero 1) := by
  have hne : airyAi' (airyZero 1) ≠ 0 := by
    intro h
    have := airyKer_pos' (airyZero 1)
    rw [h, airyAi_airyZero] at this
    simp at this
  have hge : 0 ≤ airyAi' (airyZero 1) := by
    have hs := (isSol_airyAi.hasDerivAt (airyZero 1)).tendsto_slope_zero_right
    refine ge_of_tendsto hs ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    rw [airyAi_airyZero, sub_zero, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 ht'.le) (airyAi_pos_of_gt_first (by linarith)).le
  exact lt_of_le_of_ne hge (Ne.symm hne)

/-- Existence of a zero of `Ai' - c Ai` in the first gap `(a_1, ∞)`. -/
lemma airyClark_exists_first (c : ℝ) : ∃ x ∈ airyClarkGap 1, airyAi' x = c * airyAi x := by
  have hlt : airyZero 1 < c ^ 2 := lt_of_lt_of_le (airyZero_neg 1) (sq_nonneg c)
  have hcont : ContinuousOn (fun x => airyAi' x - c * airyAi x) (Icc (airyZero 1) (c ^ 2)) :=
    (continuous_airyAi'.sub (continuous_const.mul continuous_airyAi)).continuousOn
  have ha : 0 < airyAi' (airyZero 1) - c * airyAi (airyZero 1) := by
    rw [airyAi_airyZero]; simpa using airyAi'_first_pos
  have hb : airyAi' (c ^ 2) - c * airyAi (c ^ 2) < 0 := by
    have hAi := airyAi_pos (sq_nonneg c)
    have hK := airyKer_pos' (c ^ 2)
    have hneg := airyAi'_neg (sq_nonneg c)
    -- `Ai' < -|c| Ai`
    have h1 : airyAi' (c ^ 2) < -|c| * airyAi (c ^ 2) := by
      have hsq : (c ^ 2) * airyAi (c ^ 2) ^ 2 = (|c| * airyAi (c ^ 2)) ^ 2 := by
        rw [mul_pow, sq_abs]
      rw [hsq] at hK
      have h2 : (|c| * airyAi (c ^ 2)) ^ 2 < (-airyAi' (c ^ 2)) ^ 2 := by nlinarith
      have h3 : |c| * airyAi (c ^ 2) < -airyAi' (c ^ 2) := by
        refine lt_of_pow_lt_pow_left₀ 2 (by linarith) h2
      linarith
    have h4 : -|c| * airyAi (c ^ 2) ≤ c * airyAi (c ^ 2) := by
      have := neg_abs_le c
      exact mul_le_mul_of_nonneg_right this hAi.le
    linarith
  have hmem : (0 : ℝ) ∈ Icc (airyAi' (c ^ 2) - c * airyAi (c ^ 2)) (airyAi' (airyZero 1) - c * airyAi (airyZero 1)) :=
    ⟨hb.le, ha.le⟩
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc' hlt.le hcont hmem
  have hxne : x ≠ airyZero 1 := by
    rintro rfl
    exact ha.ne' hx0
  refine ⟨x, ?_, by linarith⟩
  rw [mem_airyClarkGap]
  exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxne), Or.inl rfl⟩

/-- For `sin α ≠ 0`, `ψ_α(x) = 0 ⇔ Ai'(x) = cot α · Ai(x)`. -/
lemma combo_airy_eq_zero_iff {α : ℝ} (hα : Real.sin α ≠ 0) (x : ℝ) :
    combo α airyAi airyAi' x = 0 ↔ airyAi' x = (Real.cos α / Real.sin α) * airyAi x := by
  unfold combo
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- An angle `α ∈ (0, π)` with `cot α = c`: `α = π/2 - arctan c`. -/
lemma airyClark_exists_angle_cot (c : ℝ) :
    ∃ α : ℝ, 0 < α ∧ α < Real.pi ∧ Real.cos α / Real.sin α = c := by
  refine ⟨Real.pi / 2 - Real.arctan c, ?_, ?_, ?_⟩
  · have := Real.arctan_lt_pi_div_two c; linarith
  · have := Real.neg_pi_div_two_lt_arctan c; linarith
  · rw [Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, Real.sin_arctan, Real.cos_arctan]
    have : 0 < √(1 + c ^ 2) := Real.sqrt_pos.2 (by positivity)
    field_simp

/-- Existence of a zero of `Ai' - c Ai` in a gap `G_n`, `n ≥ 2` (interlacing theorem with `α`, `cot α = c`). -/
lemma airyClark_exists_gap {n : ℕ} (hn : 2 ≤ n) (c : ℝ) :
    ∃ x ∈ airyClarkGap n, airyAi' x = c * airyAi x := by
  obtain ⟨α, hα0, hαpi, hαc⟩ := airyClark_exists_angle_cot c
  have hsin : Real.sin α ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hα0 hαpi).ne'
  have hab : airyZero n < airyZero (n - 1) := by
    have := airyZero_strictAnti (n := n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rwa [e] at this
  have hne : ∀ x ∈ Ioo (airyZero n) (airyZero (n - 1)), airyAi x ≠ 0 := fun x hx =>
    airyAi_ne_zero_of_mem_gap (n := n) (by omega) (by
      rw [mem_airyClarkGap]; exact ⟨hx.1, Or.inr hx.2⟩)
  have hneg : ∀ x ∈ Icc (airyZero n) (airyZero (n - 1)), (fun x : ℝ => x) x < 0 := fun x hx =>
    lt_of_le_of_lt hx.2 (airyZero_neg _)
  obtain ⟨x, ⟨hx, hcomb⟩, -⟩ := isSol_airyAi.exists_unique_zero_combo_between continuous_id
    ⟨0, (airyAi_pos le_rfl).ne'⟩ hsin hab (airyAi_airyZero n) (airyAi_airyZero (n - 1)) hne hneg
  refine ⟨x, ?_, ?_⟩
  · rw [mem_airyClarkGap]; exact ⟨hx.1, Or.inr hx.2⟩
  · rw [← hαc]; exact (combo_airy_eq_zero_iff hsin x).1 hcomb

/-- **One zero of `Ai' - c Ai` in each gap.** -/
theorem airyClark_existsUnique {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    ∃! x, x ∈ airyClarkGap n ∧ airyAi' x = c * airyAi x := by
  obtain ⟨x, hx, hxe⟩ : ∃ x ∈ airyClarkGap n, airyAi' x = c * airyAi x := by
    rcases hn.eq_or_lt with rfl | h2
    · exact airyClark_exists_first c
    · exact airyClark_exists_gap h2 c
  refine ⟨x, ⟨hx, hxe⟩, ?_⟩
  rintro y ⟨hy, hye⟩
  have hmx : airyRatio x = c := by
    unfold airyRatio; rw [hxe]; field_simp [airyAi_ne_zero_of_mem_gap hn hx]
  have hmy : airyRatio y = c := by
    unfold airyRatio; rw [hye]; field_simp [airyAi_ne_zero_of_mem_gap hn hy]
  exact (strictAntiOn_airyRatio hn).injOn hy hx (hmy.trans hmx.symm)

/-- The `n`-th Clark node: the zero of `Ai' - c Ai` in the gap `G_n` (`n ≥ 1`; junk value `0` for `n = 0`).
In the note's notation `z_n(α) = airyClarkNode (cot α) n`. -/
noncomputable def airyClarkNode (c : ℝ) (n : ℕ) : ℝ :=
  if h : 1 ≤ n then Classical.choose (airyClark_existsUnique h c).exists else 0

lemma airyClarkNode_spec {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    airyClarkNode c n ∈ airyClarkGap n ∧ airyAi' (airyClarkNode c n) = c * airyAi (airyClarkNode c n) := by
  unfold airyClarkNode
  split_ifs
  exact Classical.choose_spec (airyClark_existsUnique hn c).exists

lemma airyClarkNode_mem_gap {n : ℕ} (hn : 1 ≤ n) (c : ℝ) : airyClarkNode c n ∈ airyClarkGap n :=
  (airyClarkNode_spec hn c).1

lemma airyClarkNode_eq {n : ℕ} (hn : 1 ≤ n) (c : ℝ) {x : ℝ} (hx : x ∈ airyClarkGap n)
    (hxe : airyAi' x = c * airyAi x) : x = airyClarkNode c n :=
  (airyClark_existsUnique hn c).unique ⟨hx, hxe⟩ (airyClarkNode_spec hn c)

/-- The node lies above `a_n`. -/
lemma airyZero_lt_airyClarkNode {n : ℕ} (hn : 1 ≤ n) (c : ℝ) : airyZero n < airyClarkNode c n :=
  (mem_airyClarkGap.1 (airyClarkNode_mem_gap hn c)).1

/-- The node lies below `a_{n-1}` for `n ≥ 2`. -/
lemma airyClarkNode_lt_airyZero {n : ℕ} (hn : 2 ≤ n) (c : ℝ) : airyClarkNode c n < airyZero (n - 1) := by
  rcases (mem_airyClarkGap.1 (airyClarkNode_mem_gap (n := n) (by omega) c)).2 with h | h
  · omega
  · exact h

/-- **The nodes are labelled in order**: `z_{n+1}(c) < a_n < z_n(c)`. -/
theorem airyClarkNode_succ_lt {n : ℕ} (hn : 1 ≤ n) (c : ℝ) :
    airyClarkNode c (n + 1) < airyZero n ∧ airyZero n < airyClarkNode c n := by
  refine ⟨?_, airyZero_lt_airyClarkNode hn c⟩
  have := airyClarkNode_lt_airyZero (n := n + 1) (by omega) c
  simpa using this

/-- Zeros of `Ai` are never zeros of `Ai' - c Ai` (the nodes are not zeros of `Ai`). -/
lemma airyAi_ne_zero_of_clark {c x : ℝ} (hx : airyAi' x = c * airyAi x) : airyAi x ≠ 0 := by
  intro h0
  have := airyKer_pos' x
  rw [hx, h0] at this
  simp at this

/-- Every `x` is in some gap or is a zero of `Ai` or ... : zeros of `Ai` unbounded below. -/
lemma exists_airyZero_lt (x : ℝ) : ∃ n : ℕ, 2 ≤ n ∧ airyZero n < x := by
  obtain ⟨n, hn⟩ := exists_nat_gt (|x| ^ 3)
  refine ⟨max n 2 + 1, by omega, ?_⟩
  set m := max n 2 + 1 with hm
  have hm2 : 2 ≤ m := by omega
  have h1 := (airyZero_abs_cube_bounds hm2).1
  have hmn : (n : ℝ) < m := by
    have : n < m := by omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (by omega : 1 ≤ m)
  have h2 : |x| ^ 3 < (-airyZero m) ^ 3 := by nlinarith [sq_nonneg (m : ℝ)]
  have h3 : |x| < -airyZero m := by
    refine lt_of_pow_lt_pow_left₀ 3 (neg_nonneg.2 (airyZero_nonpos m)) h2
  have := neg_abs_le x
  linarith

/-- **Classification: every real zero of `Ai' - c Ai` is exactly one node `z_n(c)`**. -/
theorem airyClark_zero_classification {c x : ℝ} (hx : airyAi' x = c * airyAi x) :
    ∃ n : ℕ, 1 ≤ n ∧ x = airyClarkNode c n := by
  by_cases h1 : airyZero 1 < x
  · refine ⟨1, le_rfl, airyClarkNode_eq le_rfl c ?_ hx⟩
    rw [mem_airyClarkGap]; exact ⟨h1, Or.inl rfl⟩
  · push Not at h1
    have hAi := airyAi_ne_zero_of_clark hx
    -- the least `m ≥ 2` with `a_m < x`
    have hex : ∃ k : ℕ, airyZero (k + 2) < x := by
      obtain ⟨n, hn2, hn⟩ := exists_airyZero_lt x
      exact ⟨n - 2, by simpa [Nat.sub_add_cancel hn2] using hn⟩
    classical
    set k := Nat.find hex with hk
    have hkp : airyZero (k + 2) < x := Nat.find_spec hex
    have hprev : x ≤ airyZero (k + 1) := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]; simpa using h1
      · have := Nat.find_min hex (show k - 1 < k by omega)
        push Not at this
        have e : k - 1 + 2 = k + 1 := by omega
        rwa [e] at this
    have hne : x ≠ airyZero (k + 1) := by
      intro h
      apply hAi
      rw [h]
      exact airyAi_airyZero _
    refine ⟨k + 2, by omega, airyClarkNode_eq (by omega) c ?_ hx⟩
    rw [mem_airyClarkGap]
    refine ⟨hkp, Or.inr ?_⟩
    have e : k + 2 - 1 = k + 1 := by omega
    rw [e]
    exact lt_of_le_of_ne hprev hne

/-- **The zeros of `Ai' - c Ai` are simple**: the derivative `x Ai(x) - c Ai'(x)` at a zero equals `Ai(x)(x - c²) ≠ 0`. -/
theorem airyClark_simple {c x : ℝ} (hx : airyAi' x = c * airyAi x) :
    HasDerivAt (fun y => airyAi' y - c * airyAi y) (x * airyAi x - c * airyAi' x) x ∧
      x * airyAi x - c * airyAi' x ≠ 0 := by
  refine ⟨((isSol_airyAi.hasDerivAt' x).sub ((isSol_airyAi.hasDerivAt x).const_mul c)), ?_⟩
  have hAi := airyAi_ne_zero_of_clark hx
  have hK := airyKer_pos' x
  rw [hx] at hK
  have e : x * airyAi x - c * (c * airyAi x) = airyAi x * (x - c ^ 2) := by ring
  rw [hx, e]
  refine mul_ne_zero hAi ?_
  intro h
  have : x = c ^ 2 := by linarith
  rw [this] at hK
  nlinarith [sq_nonneg (c * airyAi (c ^ 2))]

lemma airyRatio_airyClarkNode {n : ℕ} (hn : 1 ≤ n) (c : ℝ) : airyRatio (airyClarkNode c n) = c := by
  obtain ⟨hg, he⟩ := airyClarkNode_spec hn c
  unfold airyRatio
  rw [he]
  field_simp [airyAi_ne_zero_of_mem_gap hn hg]

/-- **The nodes fill the gap**: `z_n(Ai'(x)/Ai(x)) = x` for `x ∈ G_n`. -/
theorem airyClarkNode_ratio {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x ∈ airyClarkGap n) :
    airyClarkNode (airyRatio x) n = x := by
  symm
  refine airyClarkNode_eq hn _ hx ?_
  unfold airyRatio
  field_simp [airyAi_ne_zero_of_mem_gap hn hx]

/-- **Strict monotonicity in `c`**: `c₁ < c₂ → z_n(c₂) < z_n(c₁)`. -/
theorem airyClarkNode_strictAnti {n : ℕ} (hn : 1 ≤ n) : StrictAnti (fun c : ℝ => airyClarkNode c n) := by
  intro c₁ c₂ h
  by_contra hcon
  push Not at hcon
  have := (strictAntiOn_airyRatio hn).antitoneOn (airyClarkNode_mem_gap hn c₁) (airyClarkNode_mem_gap hn c₂) hcon
  rw [airyRatio_airyClarkNode hn, airyRatio_airyClarkNode hn] at this
  linarith

/-- The range of `c ↦ z_n(c)` is the whole gap `G_n`. -/
theorem range_airyClarkNode {n : ℕ} (hn : 1 ≤ n) : range (fun c : ℝ => airyClarkNode c n) = airyClarkGap n := by
  ext x
  constructor
  · rintro ⟨c, rfl⟩; exact airyClarkNode_mem_gap hn c
  · intro hx; exact ⟨airyRatio x, airyClarkNode_ratio hn hx⟩

/-- **`z_n(c) → a_n` as `c → +∞`** (`α → 0⁺`). -/
theorem tendsto_airyClarkNode_atTop {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun c : ℝ => airyClarkNode c n) atTop (𝓝 (airyZero n)) := by
  refine tendsto_atTop_isGLB (airyClarkNode_strictAnti hn).antitone ?_
  rw [range_airyClarkNode hn]
  by_cases h : n = 1
  · subst h
    rw [airyClarkGap_one]
    exact isGLB_Ioi
  · have : airyZero n < airyZero (n - 1) := by
      have := airyZero_strictAnti (n := n - 1) (by omega)
      have e : n - 1 + 1 = n := by omega
      rwa [e] at this
    rw [airyClarkGap_of_ne h]
    exact isGLB_Ioo this

/-- **`z_n(c) → a_{n-1}` as `c → -∞`** (`α → π⁻ ≡ 0⁻`), `n ≥ 2`. -/
theorem tendsto_airyClarkNode_atBot {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun c : ℝ => airyClarkNode c n) atBot (𝓝 (airyZero (n - 1))) := by
  refine tendsto_atBot_isLUB (airyClarkNode_strictAnti (by omega)).antitone ?_
  rw [range_airyClarkNode (by omega)]
  have hn1 : n ≠ 1 := by omega
  rw [airyClarkGap_of_ne hn1]
  have : airyZero n < airyZero (n - 1) := by
    have := airyZero_strictAnti (n := n - 1) (by omega)
    have e : n - 1 + 1 = n := by omega
    rwa [e] at this
  exact isLUB_Ioo this

/-- **`z_1(c) → +∞` as `c → -∞`** (the first node runs off to infinity as `α → π⁻`). -/
theorem tendsto_airyClarkNode_one_atBot : Tendsto (fun c : ℝ => airyClarkNode c 1) atBot atTop := by
  refine tendsto_atBot_atTop_of_antitone (airyClarkNode_strictAnti le_rfl).antitone ?_
  intro b
  refine ⟨airyRatio (max b 0 + 1), ?_⟩
  have hx : max b 0 + 1 ∈ airyClarkGap 1 := by
    rw [mem_airyClarkGap]
    exact ⟨by linarith [le_max_right b 0, airyZero_neg 1], Or.inl rfl⟩
  rw [airyClarkNode_ratio le_rfl hx]
  linarith [le_max_left b 0]

/-! ### The angle parametrisation: `ψ_α = cos α Ai - sin α Ai'` -/

/-- The Clark node `z_n(α)` of `ψ_α = cos α · Ai - sin α · Ai'` (`sin α ≠ 0`): `z_n(cot α)`. -/
noncomputable def airyClarkAngleNode (α : ℝ) (n : ℕ) : ℝ := airyClarkNode (Real.cos α / Real.sin α) n

lemma airyClark_cot_strictAntiOn : StrictAntiOn (fun α : ℝ => Real.cos α / Real.sin α) (Ioo 0 Real.pi) := by
  intro a ha b hb hab
  have hsa := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have hsb := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  show Real.cos b / Real.sin b < Real.cos a / Real.sin a
  rw [div_lt_div_iff₀ hsb hsa]
  have : Real.cos a * Real.sin b - Real.cos b * Real.sin a = Real.sin (b - a) := by
    rw [Real.sin_sub]; ring
  have hba : 0 < Real.sin (b - a) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [hb.2, ha.1])
  nlinarith

/-- **`z_n(α)` is strictly increasing in `α ∈ (0, π)`.** -/
theorem airyClarkAngleNode_strictMonoOn {n : ℕ} (hn : 1 ≤ n) :
    StrictMonoOn (fun α : ℝ => airyClarkAngleNode α n) (Ioo 0 Real.pi) := by
  intro a ha b hb hab
  exact airyClarkNode_strictAnti hn (airyClark_cot_strictAntiOn ha hb hab)

/-- `z_n(α + π) = z_n(α)` (the nodes of `ψ_α` depend on `α` modulo `π`; this is how the note's `α ∈ (-π/2, 0)` enters). -/
theorem airyClarkAngleNode_add_pi (α : ℝ) (n : ℕ) : airyClarkAngleNode (α + Real.pi) n = airyClarkAngleNode α n := by
  unfold airyClarkAngleNode
  rw [Real.cos_add_pi, Real.sin_add_pi, neg_div_neg_eq]

/-- **`α ↦ z_n(α)` is a bijection of `(0, π)` onto the gap `G_n`** (`G_1 = (a_1, ∞)`, `G_n = (a_n, a_{n-1})`). -/
theorem airyClarkAngleNode_bijOn {n : ℕ} (hn : 1 ≤ n) :
    BijOn (fun α : ℝ => airyClarkAngleNode α n) (Ioo 0 Real.pi) (airyClarkGap n) := by
  refine ⟨fun α _ => airyClarkNode_mem_gap hn _, (airyClarkAngleNode_strictMonoOn hn).injOn, fun x hx => ?_⟩
  obtain ⟨α, hα0, hαpi, hαc⟩ := airyClark_exists_angle_cot (airyRatio x)
  exact ⟨α, ⟨hα0, hαpi⟩, by
    show airyClarkNode (Real.cos α / Real.sin α) n = x
    rw [hαc]; exact airyClarkNode_ratio hn hx⟩

/-- **Zeros of `ψ_α`**: for `sin α ≠ 0`, `ψ_α(x) = 0` iff `x = z_n(α)` for some `n ≥ 1` (and every `z_n(α)` is a zero). -/
theorem airyClarkAngle_zero_iff {α : ℝ} (hα : Real.sin α ≠ 0) (x : ℝ) :
    combo α airyAi airyAi' x = 0 ↔ ∃ n : ℕ, 1 ≤ n ∧ x = airyClarkAngleNode α n := by
  rw [combo_airy_eq_zero_iff hα]
  constructor
  · exact airyClark_zero_classification
  · rintro ⟨n, hn, rfl⟩
    exact (airyClarkNode_spec hn _).2

lemma airyClark_tendsto_cot_nhdsGT_zero : Tendsto (fun α : ℝ => Real.cos α / Real.sin α) (𝓝[>] 0) atTop := by
  have h1 : Tendsto Real.sin (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(Real.continuous_sin.tendsto' 0 0 Real.sin_zero).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT Real.pi_pos] with a ha
    exact Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  have h2 : Tendsto Real.cos (𝓝[>] 0) (𝓝 1) := by
    have := (Real.continuous_cos.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have h3 : Tendsto (fun α : ℝ => (Real.sin α)⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero.comp h1
  simpa [div_eq_mul_inv] using h2.pos_mul_atTop one_pos h3

lemma airyClark_tendsto_cot_nhdsLT_pi : Tendsto (fun α : ℝ => Real.cos α / Real.sin α) (𝓝[<] Real.pi) atBot := by
  have h : Tendsto (fun α : ℝ => Real.pi - α) (𝓝[<] Real.pi) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun α : ℝ => Real.pi - α) (𝓝 Real.pi) (𝓝 (Real.pi - Real.pi)) :=
        (continuous_const.sub continuous_id).tendsto Real.pi
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with a ha
      simp only [mem_Ioi]; exact sub_pos.2 ha
  have h2 := tendsto_neg_atTop_atBot.comp (airyClark_tendsto_cot_nhdsGT_zero.comp h)
  refine h2.congr fun α => ?_
  simp [Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

/-- **`z_n(α) → a_n` as `α → 0⁺`** (note: `z_n(α) → a_n`). -/
theorem tendsto_airyClarkAngleNode_zero {n : ℕ} (hn : 1 ≤ n) :
    Tendsto (fun α : ℝ => airyClarkAngleNode α n) (𝓝[>] 0) (𝓝 (airyZero n)) :=
  (tendsto_airyClarkNode_atTop hn).comp airyClark_tendsto_cot_nhdsGT_zero

/-- **`z_n(α) → a_{n-1}` as `α → π⁻ ≡ 0⁻`** (`n ≥ 2`). -/
theorem tendsto_airyClarkAngleNode_pi {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun α : ℝ => airyClarkAngleNode α n) (𝓝[<] Real.pi) (𝓝 (airyZero (n - 1))) :=
  (tendsto_airyClarkNode_atBot hn).comp airyClark_tendsto_cot_nhdsLT_pi

/-- **`z_1(α) → +∞` as `α → π⁻`.** -/
theorem tendsto_airyClarkAngleNode_one_pi :
    Tendsto (fun α : ℝ => airyClarkAngleNode α 1) (𝓝[<] Real.pi) atTop :=
  tendsto_airyClarkNode_one_atBot.comp airyClark_tendsto_cot_nhdsLT_pi

/-- info: 'FormalResearch.Special.airyClark_existsUnique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClark_existsUnique

/-- info: 'FormalResearch.Special.strictAntiOn_airyRatio' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.strictAntiOn_airyRatio

/-- info: 'FormalResearch.Special.airyClark_zero_classification' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClark_zero_classification

/-- info: 'FormalResearch.Special.airyClark_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClark_simple

/-- info: 'FormalResearch.Special.airyClarkNode_strictAnti' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClarkNode_strictAnti

/-- info: 'FormalResearch.Special.tendsto_airyClarkNode_atTop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_airyClarkNode_atTop

/-- info: 'FormalResearch.Special.tendsto_airyClarkNode_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_airyClarkNode_atBot

/-- info: 'FormalResearch.Special.tendsto_airyClarkNode_one_atBot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_airyClarkNode_one_atBot

/-- info: 'FormalResearch.Special.airyClarkAngleNode_bijOn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClarkAngleNode_bijOn

/-- info: 'FormalResearch.Special.airyClarkAngle_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClarkAngle_zero_iff

/-- info: 'FormalResearch.Special.tendsto_airyClarkAngleNode_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_airyClarkAngleNode_zero

/-- info: 'FormalResearch.Special.tendsto_airyClarkAngleNode_pi' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.tendsto_airyClarkAngleNode_pi

end FormalResearch.Special

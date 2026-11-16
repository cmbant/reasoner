module

public import FormalResearch.Special.AiryPruferLift

/-!
# Counting zeros with the Prüfer angle

Let `θ` be a Prüfer angle of a nontrivial solution `(y, y')` of `y'' = q y`
(`IsPruferLift`, `AiryPruferLift`).  Zeros of `y` are the points where `θ ∈ π ℤ`, and `θ' = 1` there.

* `crossing_forward`, `crossing_backward`, `eq_of_zero_of_zero`: for a function `f` with `f' > 0`
  at each of its zeros, `f ≥ 0` is preserved forward in time, `f ≤ 0` backward, and `f` has at most
  one zero (it is crossed upward, once).
* `IsPruferLift.level_unique`: each level `θ = kπ` is attained at most once; hence **each zero of `y`
  is crossed exactly once** (`IsPruferLift.lt_of_zero`, `IsPruferLift.gt_of_zero`).
* `IsPruferLift.floor_mono`: `x ↦ ⌊θ x / π⌋` is nondecreasing.
* `IsPruferLift.zeros_ncard`: **zero count by floors**: for `a ≤ b`,
  `#{x ∈ (a, b] : y x = 0} = ⌊θ b / π⌋ - ⌊θ a / π⌋` (and the set is finite,
  `IsPruferLift.zeros_finite`).
* `IsPruferLift.sub_ge_of_le_neg_one` and `IsPruferLift.zeros_ncard_gt`: if `q ≤ -1` on `[a, b]` then
  `θ b - θ a ≥ b - a` and the number of zeros in `(a, b]` exceeds `(b - a)/π - 1`.  For
  `q x = x`: on `[-T, -1]` there are more than `(T - 1)/π - 1` zeros of every solution.

All results are proved (no numerical input).  Not formalised: asymptotics `θ(-v) ~ (2/3) v^{3/2}`.
-/

@[expose] public section

open Set Filter Topology

namespace FormalResearch.Special.SturmAiry

/-! ### Functions crossing zero only upward -/

section Crossing

variable {f f' : ℝ → ℝ}

/-- If `f' > 0` at every zero of `f`, then `f ≥ 0` is preserved forward in time. -/
theorem crossing_forward (hf : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, f x = 0 → 0 < f' x)
    {a x : ℝ} (hax : a ≤ x) (ha : 0 ≤ f a) : 0 ≤ f x := by
  have := image_le_of_deriv_right_lt_deriv_boundary (f := fun x => -f x) (f' := fun x => -f' x)
    (a := a) (b := x) (B := fun _ => (0 : ℝ)) (B' := fun _ => (0 : ℝ))
    (fun t _ => (hf t).neg.continuousAt.continuousWithinAt)
    (fun t _ => (hf t).neg.hasDerivWithinAt) (by simpa using ha)
    (fun t => hasDerivAt_const t (0 : ℝ))
    (by
      intro t _ ht
      have := hpos t (by linarith)
      linarith) (x := x) ⟨hax, le_rfl⟩
  simpa using this

/-- Backward in time, `f ≤ 0` is preserved. -/
theorem crossing_backward (hf : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, f x = 0 → 0 < f' x)
    {x b : ℝ} (hxb : x ≤ b) (hb : f b ≤ 0) : f x ≤ 0 := by
  have hg : ∀ t, HasDerivAt (fun t => -f (-t)) (f' (-t)) t := by
    intro t
    have hd : HasDerivAt f (f' (-t)) (-t) := hf (-t)
    exact ((hd.scomp t (hasDerivAt_neg t)).neg).congr_deriv (by simp)
  have := crossing_forward (f := fun t => -f (-t)) (f' := fun t => f' (-t)) hg
    (by
      intro t ht
      exact hpos (-t) (by simpa using ht)) (a := -b) (x := -x) (by linarith) (by simpa using hb)
  simpa using this

/-- `f` with `f' > 0` at its zeros has at most one zero. -/
theorem eq_of_zero_of_zero (hf : ∀ x, HasDerivAt f (f' x) x) (hpos : ∀ x, f x = 0 → 0 < f' x)
    {a b : ℝ} (ha : f a = 0) (hb : f b = 0) : a = b := by
  have key : ∀ a b, a < b → f a = 0 → f b = 0 → False := by
    intro a b hab ha hb
    have h1 : ∀ x ∈ Icc a b, 0 ≤ f x := fun x hx => crossing_forward hf hpos hx.1 ha.ge
    have h2 : ∀ x ∈ Icc a b, f x ≤ 0 := fun x hx => crossing_backward hf hpos hx.2 hb.le
    set m := (a + b) / 2
    have hmI : m ∈ Ioo a b := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
    have hev : f =ᶠ[𝓝 m] fun _ => (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhds hmI.1 hmI.2] with z hz using
        le_antisymm (h2 z (Ioo_subset_Icc_self hz)) (h1 z (Ioo_subset_Icc_self hz))
    have hd0 := (hasDerivAt_const m (0 : ℝ)).congr_of_eventuallyEq hev
    have h3 := (hf m).unique hd0
    have h4 := hpos m (hev.eq_of_nhds)
    linarith
  rcases lt_trichotomy a b with h | h | h
  · exact (key a b h ha hb).elim
  · exact h
  · exact (key b a h hb ha).elim

end Crossing

/-! ### The Prüfer angle crosses each level `kπ` exactly once, upward -/

namespace IsPruferLift

variable {q y y' θ : ℝ → ℝ}

private theorem level_hasDerivAt (hθ : IsPruferLift q y y' θ) (k : ℤ) (x : ℝ) :
    HasDerivAt (fun x => θ x - k * Real.pi)
      (Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2) x :=
  (hθ.hasDerivAt x).sub_const _

private theorem level_pos (_hθ : IsPruferLift q y y' θ) (k : ℤ) (x : ℝ) (hx : θ x - k * Real.pi = 0) :
    0 < Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2 := by
  have h : θ x = k * Real.pi := by linarith
  have hs : Real.sin (θ x) = 0 := by rw [h]; exact Real.sin_int_mul_pi k
  have := Real.sin_sq_add_cos_sq (θ x)
  rw [hs] at this ⊢
  nlinarith

/-- Each level `θ = kπ` is attained at most once. -/
theorem level_unique (hθ : IsPruferLift q y y' θ) (k : ℤ) {a b : ℝ} (ha : θ a = k * Real.pi)
    (hb : θ b = k * Real.pi) : a = b :=
  eq_of_zero_of_zero (level_hasDerivAt hθ k) (level_pos hθ k) (by simp [ha]) (by simp [hb])

/-- After a zero of `y` at `c` (`θ c = kπ`), `θ > kπ`. -/
theorem gt_of_zero (hθ : IsPruferLift q y y' θ) (k : ℤ) {c b : ℝ} (hc : θ c = k * Real.pi)
    (hcb : c < b) : k * Real.pi < θ b := by
  have h0 : 0 ≤ θ b - k * Real.pi := crossing_forward (level_hasDerivAt hθ k) (level_pos hθ k)
    hcb.le (by simp [hc])
  rcases h0.eq_or_lt with h | h
  · exact absurd (hθ.level_unique k hc (by linarith)) hcb.ne
  · linarith

/-- Before a zero of `y` at `c` (`θ c = kπ`), `θ < kπ`. -/
theorem lt_of_zero (hθ : IsPruferLift q y y' θ) (k : ℤ) {a c : ℝ} (hc : θ c = k * Real.pi)
    (hac : a < c) : θ a < k * Real.pi := by
  have h0 : θ a - k * Real.pi ≤ 0 := crossing_backward (level_hasDerivAt hθ k) (level_pos hθ k)
    hac.le (by simp [hc])
  rcases h0.eq_or_lt with h | h
  · exact absurd (hθ.level_unique k (by linarith) hc) hac.ne
  · linarith

/-- The integer part `⌊θ / π⌋` is nondecreasing: the zeros are crossed only upward. -/
theorem floor_mono (hθ : IsPruferLift q y y' θ) {a b : ℝ} (hab : a ≤ b) :
    ⌊θ a / Real.pi⌋ ≤ ⌊θ b / Real.pi⌋ := by
  have hk : ((⌊θ a / Real.pi⌋ : ℤ) : ℝ) * Real.pi ≤ θ a :=
    (le_div_iff₀ Real.pi_pos).1 (Int.floor_le _)
  have h0 := crossing_forward (level_hasDerivAt hθ ⌊θ a / Real.pi⌋) (level_pos hθ _) hab
    (by linarith)
  exact Int.le_floor.2 ((le_div_iff₀ Real.pi_pos).2 (by linarith))

private theorem floor_of_zero (hθ : IsPruferLift q y y' θ) {x : ℝ} (hx : y x = 0) :
    ∃ k : ℤ, θ x = k * Real.pi ∧ ⌊θ x / Real.pi⌋ = k := by
  obtain ⟨k, hk⟩ := (hθ.zero_iff_exists_int x).1 hx
  refine ⟨k, hk, ?_⟩
  have : θ x / Real.pi = k := by rw [hk]; field_simp
  rw [this, Int.floor_intCast]

private theorem zeros_mapsTo (hθ : IsPruferLift q y y' θ) {a b : ℝ} :
    MapsTo (fun x => ⌊θ x / Real.pi⌋) {x | x ∈ Ioc a b ∧ y x = 0}
      (Ioc ⌊θ a / Real.pi⌋ ⌊θ b / Real.pi⌋) := by
  rintro x ⟨hx, hy⟩
  obtain ⟨k, hk, hfl⟩ := floor_of_zero hθ hy
  simp only [mem_Ioc, hfl]
  constructor
  · exact Int.floor_lt.2 ((div_lt_iff₀ Real.pi_pos).2 (hθ.lt_of_zero k hk hx.1))
  · refine Int.le_floor.2 ((le_div_iff₀ Real.pi_pos).2 ?_)
    rcases hx.2.eq_or_lt with h | h
    · rw [← hk, h]
    · exact (hθ.gt_of_zero k hk h).le

private theorem zeros_injOn (hθ : IsPruferLift q y y' θ) {a b : ℝ} :
    InjOn (fun x => ⌊θ x / Real.pi⌋) {x | x ∈ Ioc a b ∧ y x = 0} := by
  rintro x ⟨-, hx⟩ x' ⟨-, hx'⟩ h
  obtain ⟨k, hk, hfl⟩ := floor_of_zero hθ hx
  obtain ⟨k', hk', hfl'⟩ := floor_of_zero hθ hx'
  simp only at h
  have : k = k' := by rw [← hfl, ← hfl', h]
  subst this
  exact hθ.level_unique k hk hk'

/-- **Zeros counted by floors.**  For `a ≤ b`, the number of zeros of `y` in `(a, b]` is
`⌊θ b / π⌋ - ⌊θ a / π⌋`. -/
theorem zeros_ncard (hθ : IsPruferLift q y y' θ) {a b : ℝ} (hab : a ≤ b) :
    (({x | x ∈ Ioc a b ∧ y x = 0}).ncard : ℤ) = ⌊θ b / Real.pi⌋ - ⌊θ a / Real.pi⌋ := by
  have h1 : ({x | x ∈ Ioc a b ∧ y x = 0}).ncard = (Ioc ⌊θ a / Real.pi⌋ ⌊θ b / Real.pi⌋).ncard := by
    refine Set.ncard_congr (fun x _ => ⌊θ x / Real.pi⌋) (fun x hx => zeros_mapsTo hθ hx)
      (fun x x' hx hx' h => zeros_injOn hθ hx hx' h) ?_
    intro k hk
    have hlo : θ a < k * Real.pi := by
      have := (Int.floor_lt.1 (show ⌊θ a / Real.pi⌋ < k from hk.1))
      exact (div_lt_iff₀ Real.pi_pos).1 this
    have hhi : k * Real.pi ≤ θ b :=
      (le_div_iff₀ Real.pi_pos).1 (Int.le_floor.1 hk.2)
    obtain ⟨c, hc, hcθ⟩ := intermediate_value_Icc hab hθ.continuous.continuousOn
      (show (k : ℝ) * Real.pi ∈ Icc (θ a) (θ b) from ⟨hlo.le, hhi⟩)
    have hca : a < c := lt_of_le_of_ne hc.1 (by rintro rfl; linarith)
    have hcy : y c = 0 := (hθ.zero_iff_exists_int c).2 ⟨k, hcθ⟩
    refine ⟨c, ⟨⟨hca, hc.2⟩, hcy⟩, ?_⟩
    show ⌊θ c / Real.pi⌋ = k
    rw [hcθ]
    have : (k : ℝ) * Real.pi / Real.pi = k := by field_simp
    rw [this, Int.floor_intCast]
  rw [h1, ← Finset.coe_Ioc, Set.ncard_coe_finset, Int.card_Ioc]
  exact Int.toNat_of_nonneg (sub_nonneg.2 (hθ.floor_mono hab))

/-- The zero set in `(a, b]` is finite. -/
theorem zeros_finite (hθ : IsPruferLift q y y' θ) (a b : ℝ) :
    {x | x ∈ Ioc a b ∧ y x = 0}.Finite :=
  Set.Finite.of_injOn (zeros_mapsTo hθ) (zeros_injOn hθ) (Set.finite_Ioc _ _)

/-- Where `q ≤ -1` the Prüfer angle increases at least linearly: `θ b - θ a ≥ b - a`. -/
theorem sub_ge_of_le_neg_one (hθ : IsPruferLift q y y' θ) {a b : ℝ} (hab : a ≤ b)
    (hq : ∀ x ∈ Icc a b, q x ≤ -1) : b - a ≤ θ b - θ a := by
  have hg : ∀ x, HasDerivAt (fun x => θ x - x)
      (Real.cos (θ x) ^ 2 - q x * Real.sin (θ x) ^ 2 - 1) x := fun x =>
    (hθ.hasDerivAt x).sub (hasDerivAt_id x)
  have hmono : MonotoneOn (fun x => θ x - x) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [(hg x).deriv]
    have h1 := hq x (Ioo_subset_Icc_self hx)
    nlinarith [Real.sin_sq_add_cos_sq (θ x),
      mul_nonneg (by linarith : 0 ≤ -1 - q x) (sq_nonneg (Real.sin (θ x)))]
  have := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  dsimp only at this
  linarith

/-- If `q ≤ -1` on `[a, b]`, more than `(b - a)/π - 1` zeros of `y` lie in `(a, b]`. -/
theorem zeros_ncard_gt (hθ : IsPruferLift q y y' θ) {a b : ℝ} (hab : a ≤ b)
    (hq : ∀ x ∈ Icc a b, q x ≤ -1) :
    (b - a) / Real.pi - 1 < ({x | x ∈ Ioc a b ∧ y x = 0}).ncard := by
  have hN := hθ.zeros_ncard hab
  have hN' : (({x | x ∈ Ioc a b ∧ y x = 0}).ncard : ℝ) =
      (⌊θ b / Real.pi⌋ : ℝ) - (⌊θ a / Real.pi⌋ : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hN
  rw [hN']
  have h1 := Int.lt_floor_add_one (θ b / Real.pi)
  have h2 := Int.floor_le (θ a / Real.pi)
  have h3 := hθ.sub_ge_of_le_neg_one hab hq
  have h4 : (b - a) / Real.pi ≤ θ b / Real.pi - θ a / Real.pi := by
    rw [← sub_div]
    exact div_le_div_of_nonneg_right h3 Real.pi_pos.le
  linarith

end IsPruferLift

/-- **Zero count for the Airy equation on the negative axis.**  Every nontrivial solution of
`y'' = x y` has, in `(-T, -1]` (`T ≥ 1`), more than `(T - 1)/π - 1` zeros. -/
theorem airy_zeros_ncard_gt {y y' : ℝ → ℝ} (h : IsSol (fun x => x) y y') (hy : ∃ x, y x ≠ 0)
    {T : ℝ} (hT : 1 ≤ T) :
    (T - 1) / Real.pi - 1 < ({x | x ∈ Ioc (-T) (-1) ∧ y x = 0}).ncard := by
  obtain ⟨θ, hθ, -⟩ := h.exists_isPruferLift continuous_id hy 0
  have := hθ.zeros_ncard_gt (a := -T) (b := -1) (by linarith) (fun x hx => hx.2)
  have e : (-1 - -T) = T - 1 := by ring
  rwa [e] at this

/-- info: 'FormalResearch.Special.SturmAiry.crossing_forward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.crossing_forward

/-- info: 'FormalResearch.Special.SturmAiry.eq_of_zero_of_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.eq_of_zero_of_zero

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.level_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.level_unique

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.zeros_ncard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.zeros_ncard

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.zeros_finite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.zeros_finite

/-- info: 'FormalResearch.Special.SturmAiry.IsPruferLift.zeros_ncard_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.IsPruferLift.zeros_ncard_gt

/-- info: 'FormalResearch.Special.SturmAiry.airy_zeros_ncard_gt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.SturmAiry.airy_zeros_ncard_gt

end FormalResearch.Special.SturmAiry

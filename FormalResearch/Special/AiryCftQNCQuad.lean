module

public import FormalResearch.Special.AiryCftQNCDefect
public import FormalResearch.Special.AiryCftQQuad
public import FormalResearch.Special.AiryCft2Clark

/-!
# Theorem Q (1), (4) for `N = P·Ai + Q·Ai'` and the Clark functions, in limit form

Statement formalised (CFT `GENERAL_THEOREMS.md` Theorem 1.1 and `AIRY_POISSON.md` Theorem Q, limit form): for real `P`,
`Q ≠ 0`, `N = P Ai + Q Ai'`, `D = P² - z Q²`, and `f` entire with `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` for an **arbitrary real** `ν`
and `f ∈ L¹(ℝ)`:

* (`airyNC_tendsto`) there are finite sets `T_k` of zeros of `N` exhausting all zeros with
  `Σ_{z ∈ T_k} f(z) D(z)/N'(z)² → ∫_ℝ f`;
* (`airyNC_hasSum`) if `Σ_{N(z)=0} f(z) D(z)/N'(z)²` is summable (over the subtype of zeros) its sum is `∫_ℝ f`;
* (`airyClark_hasSum`) the same for the Clark functions `cos α Ai - sin α Ai'` (`sin α ≠ 0`) with the weights `1/K(z,z)`.

Proof: the integral form `cft2_defect_bound_int` of the residue-defect bound (`AiryCftQNCDefect`) for `(N, M)`,
`M = P Bi + Q Bi'`, and the weights `-π M/N' = D/N'²` give, on the good circles `|u| = r_k = a_k²` of `airyNC_good_circle`
(ratio bounds `‖M/N ∓ i‖ e ≤ C₀`), the defect bound `C₀ a_k ∫_0^π |G(a_k e^{iφ})| dφ` (`airyQ_arc_reduce`), which the Hardy
Fejér–Riesz bound sends to `0` (`HardyArcDecay`).  All **proved**.  Not formalised: summability for `ν ≥ -1` (Theorem Q (3)).
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- **Theorem D for `N = P Ai + Q Ai'`, integral form.** -/
theorem airyNC_defect_bound_int (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hN : ∀ u : ℂ, ‖u‖ = r → airyNC P Q u ≠ 0)
    (S : Finset ℂ) (hS : ∀ z : ℂ, z ∈ S ↔ airyNC P Q z = 0 ∧ ‖z‖ ≤ r) :
    ‖(∑ t ∈ S, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) - ∫ x in (-r)..r, f (x : ℂ)‖ ≤
      (r / 2) * ((∫ θ in (0 : ℝ)..π, ‖f (circleMap 0 r θ) *
          (airyMC P Q (circleMap 0 r θ) / airyNC P Q (circleMap 0 r θ) - I)‖) +
        ∫ θ in π..(2 * π), ‖f (circleMap 0 r θ) *
          (airyMC P Q (circleMap 0 r θ) / airyNC P Q (circleMap 0 r θ) + I)‖) := by
  have hin : ∀ t ∈ S, ‖t‖ < r := by
    intro t ht
    obtain ⟨h0, h1⟩ := (hS t).mp ht
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd h0 (hN t h)
  have hder : ∀ t ∈ S, deriv (airyNC P Q) t ≠ 0 := by
    intro t ht
    obtain ⟨h0, -⟩ := (hS t).mp ht
    have him := airyNC_zero_im P Q hQ h0
    have e : t = (t.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [e] at h0
    rw [deriv_airyNC, e]
    exact (airyNC_zero_weight_pos P Q hQ h0).2
  have h := cft2_defect_bound_int (differentiable_airyNC P Q) (differentiable_airyMC P Q) hf hr S hin
    (fun t ht => ((hS t).mp ht).1) hder (fun w hw h0 => (hS w).mpr ⟨h0, hw⟩)
  have hsum : (-(π : ℂ)) * (∑ t ∈ S, f t * airyMC P Q t / deriv (airyNC P Q) t) =
      ∑ t ∈ S, f t * (airyDC P Q t / airyNC' P Q t ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨h0, -⟩ := (hS t).mp ht
    have hd := hder t ht
    rw [deriv_airyNC] at hd ⊢
    have hw := airyNC_weight_eq P Q h0 hd
    rw [← hw]
    ring
  rw [hsum] at h
  exact h

/-- **Theorem Q (1) + (4) for `N = P Ai + Q Ai'`, limit form.** -/
theorem airyNC_tendsto (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ T : ℕ → Finset {z : ℂ // airyNC P Q z = 0}, Tendsto T atTop atTop ∧
      Tendsto (fun k => ∑ z ∈ T k, f z * (airyDC P Q z / airyNC' P Q z ^ 2)) atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) := by
  classical
  obtain ⟨C₀, hC₀, k₀, hgc⟩ := airyNC_good_circle P Q hQ
  obtain ⟨hG1, hG2, hG3⟩ := airyQ_hardy_hyp hf hfi hC hb
  choose r hr using fun k : ℕ => hgc (k + k₀ + 1) (by omega)
  have hr1' : ∀ k : ℕ, ((k : ℝ) + k₀ + 1) ≤ r k := fun k => by
    have := (hr k).1
    push_cast at this
    exact this
  have hr1 : ∀ k : ℕ, ((k : ℝ) + 1) ≤ r k := fun k => by
    have := hr1' k
    have h0 : (0 : ℝ) ≤ k₀ := Nat.cast_nonneg _
    linarith
  have hr2 : ∀ k : ℕ, r k ≤ (k : ℝ) + k₀ + 2 := fun k => by
    have := (hr k).2.1
    push_cast at this
    linarith
  have hr0 : ∀ k, 0 < r k := fun k => by linarith [hr1 k, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hrmono : ∀ k : ℕ, r k ≤ r (k + 1) := fun k => by
    have h1 := hr1' (k + 1)
    push_cast at h1
    have := hr2 k
    linarith
  have hrt : Tendsto r atTop atTop :=
    tendsto_atTop_mono (f := fun k : ℕ => (k : ℝ) + 1) (fun k => hr1 k)
      (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hNne : ∀ k (u : ℂ), ‖u‖ = r k → airyNC P Q u ≠ 0 := by
    intro k u hu h0
    have h := ((hr k).2.2 u hu).1
    rw [h0, norm_zero] at h
    have hen := airyEnv_pos u
    have : 0 < Q ^ 2 / (256 * π) * √(r k) * airyEnv u := by
      have : 0 < √(r k) := Real.sqrt_pos.mpr (hr0 k)
      have : 0 < Q ^ 2 := by positivity
      positivity
    linarith
  set S : ℕ → Finset ℂ := fun k => (airyNC_zeros_finite P Q hQ (r k)).toFinset with hS
  have hSmem : ∀ k z, z ∈ S k ↔ airyNC P Q z = 0 ∧ ‖z‖ ≤ r k := fun k z => by
    simp [hS]
  set ι := {z : ℂ // airyNC P Q z = 0} with hι
  set g : ι → ℂ := fun z => f z * (airyDC P Q z / airyNC' P Q z ^ 2) with hg
  set T : ℕ → Finset ι := fun k => (S k).subtype (fun z => airyNC P Q z = 0) with hT
  have hTsum : ∀ k, ∑ z ∈ T k, g z = ∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2) := fun k =>
    Finset.sum_subtype_of_mem (fun t : ℂ => f t * (airyDC P Q t / airyNC' P Q t ^ 2))
      (fun t ht => ((hSmem k t).mp ht).1)
  have hTmono : Monotone T := by
    refine monotone_nat_of_le_succ fun k => ?_
    intro z hz
    have hz' := (hSmem k z).mp (Finset.mem_subtype.mp hz)
    exact Finset.mem_subtype.mpr ((hSmem (k + 1) z).mpr ⟨hz'.1, hz'.2.trans (hrmono k)⟩)
  have hTex : ∀ z : ι, ∃ k, z ∈ T k := by
    intro z
    obtain ⟨k, hk⟩ := exists_nat_ge ‖z.1‖
    refine ⟨k, ?_⟩
    exact Finset.mem_subtype.mpr ((hSmem k z.1).mpr ⟨z.2, hk.trans (by linarith [hr1 k])⟩)
  refine ⟨T, tendsto_atTop_finset_of_monotone hTmono hTex, ?_⟩
  have hrt' : Tendsto (fun k => -r k) atTop atBot := tendsto_neg_atTop_atBot.comp hrt
  have hI : Tendsto (fun k => ∫ x in (-(r k))..(r k), f (x : ℂ)) atTop (𝓝 (∫ x : ℝ, f (x : ℂ))) :=
    intervalIntegral_tendsto_integral hfi hrt' hrt
  have hsq : Tendsto (fun k => √(r k)) atTop atTop := Real.tendsto_sqrt_atTop.comp hrt
  have hA := (FormalResearch.Hardy.hardy_arc_tendsto_zero hG1 hG2 hG3).comp hsq
  have hdef : ∀ k, ‖(∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ ≤
      C₀ * (√(r k) * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 (√(r k)) φ)‖) := by
    intro k
    have hpos : 0 < √(r k) := Real.sqrt_pos.mpr (hr0 k)
    have e2 : √(r k) ^ 2 = r k := Real.sq_sqrt (hr0 k).le
    refine (airyNC_defect_bound_int P Q hQ hf (hr0 k) (hNne k) (S k) (hSmem k)).trans ?_
    have := airyQ_arc_reduce (Rp := fun u => airyMC P Q u / airyNC P Q u - I)
      (Rm := fun u => airyMC P Q u / airyNC P Q u + I) (K := C₀) hpos
      (fun u hu hi => ((hr k).2.2 u (by rw [hu, e2])).2.1 hi)
      (fun u hu hi => ((hr k).2.2 u (by rw [hu, e2])).2.2 hi) hf
    rwa [e2] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hI' : Tendsto (fun k => ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖) atTop (𝓝 0) := by
    have := hI.sub_const (∫ x : ℝ, f (x : ℂ))
    rw [sub_self] at this
    simpa using this.norm
  have hE : Tendsto (fun k => ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖ +
      C₀ * (√(r k) * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 (√(r k)) φ)‖)) atTop (𝓝 0) := by
    simpa using hI'.add (hA.const_mul C₀)
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hE
  rw [hTsum k]
  calc _ ≤ ‖(∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ + ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖ := by
        have := norm_add_le ((∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) -
          ∫ x in (-(r k))..(r k), f (x : ℂ)) ((∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ))
        rwa [sub_add_sub_cancel] at this
    _ ≤ _ := by rw [add_comm]; gcongr; exact hdef k

/-- **Theorem Q (4) for `N = P Ai + Q Ai'`, `HasSum` form.** -/
theorem airyNC_hasSum (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hs : Summable (fun z : {z : ℂ // airyNC P Q z = 0} => f z * (airyDC P Q z / airyNC' P Q z ^ 2))) :
    HasSum (fun z : {z : ℂ // airyNC P Q z = 0} => f z * (airyDC P Q z / airyNC' P Q z ^ 2))
      (∫ x : ℝ, f (x : ℂ)) := by
  obtain ⟨T, hT, ht⟩ := airyNC_tendsto P Q hQ hf hfi hC hb
  have h1 := hs.hasSum.comp hT
  rw [← tendsto_nhds_unique h1 ht]
  exact hs.hasSum

/-- **Theorem Q (4) for the Clark functions, `HasSum` form.** -/
theorem airyClark_hasSum (α : ℝ) (hα : Real.sin α ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hs : Summable (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
        f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2))) :
    HasSum (fun z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} =>
        f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2)) (∫ x : ℝ, f (x : ℂ)) := by
  have hQ : -Real.sin α ≠ 0 := neg_ne_zero.mpr hα
  have hz : ∀ z : ℂ, airyNC (Real.cos α) (-Real.sin α) z = 0 ↔
      (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0 := by
    intro z
    unfold airyNC
    push_cast
    constructor <;> intro h <;> linear_combination h
  let e : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0} ≃
      {z : ℂ // airyNC (Real.cos α) (-Real.sin α) z = 0} :=
    Equiv.subtypeEquivRight (fun z => (hz z).symm)
  have hw : ∀ z : {z : ℂ // (Real.cos α : ℂ) * airyAiC z - (Real.sin α : ℂ) * deriv airyAiC z = 0},
      f z / (deriv airyAiC z ^ 2 - z * airyAiC z ^ 2) =
        (fun w : {z : ℂ // airyNC (Real.cos α) (-Real.sin α) z = 0} =>
          f w * (airyDC (Real.cos α) (-Real.sin α) w / airyNC' (Real.cos α) (-Real.sin α) w ^ 2)) (e z) := by
    intro z
    have hz0 := (hz z.1).mpr z.2
    simp only [e, Equiv.subtypeEquivRight_apply_coe]
    rw [airyNC_weight_eq_inv_K _ _ hQ hz0]
    field_simp
  have hs' : Summable (fun w : {z : ℂ // airyNC (Real.cos α) (-Real.sin α) z = 0} =>
      f w * (airyDC (Real.cos α) (-Real.sin α) w / airyNC' (Real.cos α) (-Real.sin α) w ^ 2)) := by
    rw [← e.summable_iff]
    refine hs.congr fun z => ?_
    exact hw z
  have h := airyNC_hasSum (Real.cos α) (-Real.sin α) hQ hf hfi hC hb hs'
  rw [← e.hasSum_iff] at h
  convert h using 2 with z
  exact hw z

/-- info: 'FormalResearch.Special.airyNC_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_tendsto

/-- info: 'FormalResearch.Special.airyNC_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_hasSum

/-- info: 'FormalResearch.Special.airyClark_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyClark_hasSum

end FormalResearch.Special

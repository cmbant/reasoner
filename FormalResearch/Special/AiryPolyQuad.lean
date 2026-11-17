module

public import FormalResearch.Special.AiryPolyZeros
public import FormalResearch.Special.AiryCftQNCQuad

/-!
# Theorem Q (1), (4) for `N = P·Ai + Q·Ai'`, real polynomial `P`, `Q`: the limit form of the Airy quadrature

Formalises the quadrature of `SOFT_EDGE_THEOREMS.md` Lemmas 4.4/4.6 (the Blaschke-extension Airy summation) in the limit form of
Theorem Q (`AiryCftQNCQuad` for constant `P`, `Q`): for `f` entire, `‖f(u)‖ ≤ C (1+|u|)^ν e(u)` for an **arbitrary real** `ν` and
`f ∈ L¹(ℝ)`,

`Σ_{N(z)=0, |z| ≤ r_k} f(z) D(z)/N'(z)² → ∫_ℝ f`,    `D = P (P+Q') - Q (P'+zQ)`,

along the good circles `|u| = r_k` of `airyPQ_good_circle` (`AiryPolyCircle`).

* `airyPQ_defect_bound_int` (residue-defect formula for `(N, M)`, `M = P Bi + Q Bi'`, weights `-πM/N' = D/N'²` from the Wronskian
  `N M' - N' M = D/π`) and `airyPQ_tendsto_of_simple` hold for **every** pair of real polynomials, not both zero, **whose zeros of `N` are
  simple** (hypothesis `hsimple`; the zeros may be complex, the weights `D/N'²` are then complex).  (Numerical check, mpmath:
  `P = 1 + 0.3u`, `Q = u² - 2`, which is *not* Hermite-Biehler and has the two non-real zeros `-1.3494 ± 0.3687i`, and
  `f = Ai(u)Ai(u+1)/Π_{j≤3}(u-a_j)(u+1-a_j)`: the sum over the 600 real zeros is `0.20149`, adding the complex pair gives
  `0.2019584191 = ∫ f`.)
* `airyPQ_tendsto`: for a Hermite-Biehler pair, `Q ≠ 0`, the zeros are real, simple, and `D > 0` at them (`AiryPolyZeros`), so the finite sets
  `T_k` exhaust the real zeros.
* `airyPQ_hasSum`: `HasSum` to `∫ f` under summability (the unconditional `airyPQ_hasSum_unc` is in `AiryPolySample`).

Numerical check of the Hermite-Biehler case (mpmath, 22 digits): for `Q + iP ∈ {i(u - b̄), (u - w₁)(u - w₂), (u - w₁)(u - w₂)(u - w₃)}` and the
constant pair, the sum over 600 real zeros equals `∫ f = 0.2019584191` to 10 digits, and `D(t) > 0` at every zero.

Proof: `cft2_defect_bound_int` (generic) with `M = P Bi + Q Bi'`, then `airyQ_arc_reduce` and the Hardy arc bound exactly as in
`AiryCftQNCQuad`, with the good circles of `AiryPolyCircle` (ratio constant `168 √π`).  All **proved**.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric Polynomial
open scoped Real

namespace FormalResearch.Special

/-- **Theorem D for `N = P Ai + Q Ai'` (polynomial `P`, `Q`), integral form**, for simple zeros. -/
theorem airyPQ_defect_bound_int (P Q : ℝ[X]) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hN : ∀ u : ℂ, ‖u‖ = r → airyPQN P Q u ≠ 0)
    (hsimple : ∀ z : ℂ, airyPQN P Q z = 0 → airyPQN' P Q z ≠ 0)
    (S : Finset ℂ) (hS : ∀ z : ℂ, z ∈ S ↔ airyPQN P Q z = 0 ∧ ‖z‖ ≤ r) :
    ‖(∑ t ∈ S, f t * (airyPQD P Q t / airyPQN' P Q t ^ 2)) - ∫ x in (-r)..r, f (x : ℂ)‖ ≤
      (r / 2) * ((∫ θ in (0 : ℝ)..π, ‖f (circleMap 0 r θ) *
          (airyPQM P Q (circleMap 0 r θ) / airyPQN P Q (circleMap 0 r θ) - I)‖) +
        ∫ θ in π..(2 * π), ‖f (circleMap 0 r θ) *
          (airyPQM P Q (circleMap 0 r θ) / airyPQN P Q (circleMap 0 r θ) + I)‖) := by
  have hin : ∀ t ∈ S, ‖t‖ < r := by
    intro t ht
    obtain ⟨h0, h1⟩ := (hS t).mp ht
    rcases h1.lt_or_eq with h | h
    · exact h
    · exact absurd h0 (hN t h)
  have hder : ∀ t ∈ S, deriv (airyPQN P Q) t ≠ 0 := by
    intro t ht
    obtain ⟨h0, -⟩ := (hS t).mp ht
    rw [deriv_airyPQN]
    exact hsimple t h0
  have h := cft2_defect_bound_int (differentiable_airyPQN P Q) (differentiable_airyPQM P Q) hf hr S hin
    (fun t ht => ((hS t).mp ht).1) hder (fun w hw h0 => (hS w).mpr ⟨h0, hw⟩)
  have hsum : (-(π : ℂ)) * (∑ t ∈ S, f t * airyPQM P Q t / deriv (airyPQN P Q) t) =
      ∑ t ∈ S, f t * (airyPQD P Q t / airyPQN' P Q t ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    obtain ⟨h0, -⟩ := (hS t).mp ht
    have hd := hder t ht
    rw [deriv_airyPQN] at hd ⊢
    have hw := airyPQ_weight_eq P Q h0 hd
    rw [← hw]
    ring
  rw [hsum] at h
  exact h

/-- **Theorem Q (1) + (4) for `N = P Ai + Q Ai'` (real polynomials, simple zeros), limit form.** -/
theorem airyPQ_tendsto_of_simple (P Q : ℝ[X]) (hPQ : P ≠ 0 ∨ Q ≠ 0)
    (hsimple : ∀ z : ℂ, airyPQN P Q z = 0 → airyPQN' P Q z ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ T : ℕ → Finset {z : ℂ // airyPQN P Q z = 0}, Tendsto T atTop atTop ∧
      Tendsto (fun k => ∑ z ∈ T k, f z * (airyPQD P Q z / airyPQN' P Q z ^ 2)) atTop
        (𝓝 (∫ x : ℝ, f (x : ℂ))) := by
  classical
  obtain ⟨k₀, hgc⟩ := airyPQ_good_circle P Q hPQ
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
  have hNne : ∀ k (u : ℂ), ‖u‖ = r k → airyPQN P Q u ≠ 0 := by
    intro k u hu h0
    obtain ⟨hW, h, -⟩ := (hr k).2.2 u hu
    rw [h0, norm_zero] at h
    have hen := airyEnv_pos u
    have : 0 < airyPQW P Q u ^ 2 * airyEnv u / (64 * π * √(r k)) := by
      have : 0 < √(r k) := Real.sqrt_pos.mpr (hr0 k)
      positivity
    linarith
  have hnonzero : ∃ z, airyPQN P Q z ≠ 0 := ⟨((r 0 : ℝ) : ℂ), hNne 0 _ (by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0 0)])⟩
  set S : ℕ → Finset ℂ := fun k =>
    (airy_entire_zeros_finite (differentiable_airyPQN P Q) hnonzero (r k)).toFinset with hS
  have hSmem : ∀ k z, z ∈ S k ↔ airyPQN P Q z = 0 ∧ ‖z‖ ≤ r k := fun k z => by
    simp [hS]
  set ι := {z : ℂ // airyPQN P Q z = 0} with hι
  set g : ι → ℂ := fun z => f z * (airyPQD P Q z / airyPQN' P Q z ^ 2) with hg
  set T : ℕ → Finset ι := fun k => (S k).subtype (fun z => airyPQN P Q z = 0) with hT
  have hTsum : ∀ k, ∑ z ∈ T k, g z = ∑ t ∈ S k, f t * (airyPQD P Q t / airyPQN' P Q t ^ 2) := fun k =>
    Finset.sum_subtype_of_mem (fun t : ℂ => f t * (airyPQD P Q t / airyPQN' P Q t ^ 2))
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
  have hdef : ∀ k, ‖(∑ t ∈ S k, f t * (airyPQD P Q t / airyPQN' P Q t ^ 2)) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ ≤
      (168 * √π) * (√(r k) * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 (√(r k)) φ)‖) := by
    intro k
    have hpos : 0 < √(r k) := Real.sqrt_pos.mpr (hr0 k)
    have e2 : √(r k) ^ 2 = r k := Real.sq_sqrt (hr0 k).le
    refine (airyPQ_defect_bound_int P Q hf (hr0 k) (hNne k) hsimple (S k) (hSmem k)).trans ?_
    have := airyQ_arc_reduce (Rp := fun u => airyPQM P Q u / airyPQN P Q u - I)
      (Rm := fun u => airyPQM P Q u / airyPQN P Q u + I) (K := 168 * √π) hpos
      (fun u hu hi => ((hr k).2.2 u (by rw [hu, e2])).2.2.1 hi)
      (fun u hu hi => ((hr k).2.2 u (by rw [hu, e2])).2.2.2 hi) hf
    rwa [e2] at this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hI' : Tendsto (fun k => ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖) atTop (𝓝 0) := by
    have := hI.sub_const (∫ x : ℝ, f (x : ℂ))
    rw [sub_self] at this
    simpa using this.norm
  have hE : Tendsto (fun k => ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖ +
      (168 * √π) * (√(r k) * ∫ φ in (0 : ℝ)..π, ‖airyQG f (circleMap 0 (√(r k)) φ)‖)) atTop (𝓝 0) := by
    simpa using hI'.add (hA.const_mul (168 * √π))
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hE
  rw [hTsum k]
  calc _ ≤ ‖(∑ t ∈ S k, f t * (airyPQD P Q t / airyPQN' P Q t ^ 2)) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ + ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ)‖ := by
        have := norm_add_le ((∑ t ∈ S k, f t * (airyPQD P Q t / airyPQN' P Q t ^ 2)) -
          ∫ x in (-(r k))..(r k), f (x : ℂ)) ((∫ x in (-(r k))..(r k), f (x : ℂ)) - ∫ x : ℝ, f (x : ℂ))
        rwa [sub_add_sub_cancel] at this
    _ ≤ _ := by rw [add_comm]; gcongr; exact hdef k

/-- Simplicity of the zeros of a Hermite-Biehler combination (`AiryPolyZeros`). -/
lemma airyPQ_simple_of_HB {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) :
    ∀ z : ℂ, airyPQN P Q z = 0 → airyPQN' P Q z ≠ 0 := by
  intro z hz
  have e := airyPQ_zero_eq_ofReal hHB hz
  rw [e] at hz ⊢
  exact (airyPQ_zero_weight_pos hHB hQ hz).2

/-- **Theorem Q (1) + (4) for a Hermite-Biehler pair, limit form** (`SOFT_EDGE_THEOREMS.md` Lemma 4.6, quadrature). -/
theorem airyPQ_tendsto {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    ∃ T : ℕ → Finset {z : ℂ // airyPQN P Q z = 0}, Tendsto T atTop atTop ∧
      Tendsto (fun k => ∑ z ∈ T k, f z * (airyPQD P Q z / airyPQN' P Q z ^ 2)) atTop
        (𝓝 (∫ x : ℝ, f (x : ℂ))) :=
  airyPQ_tendsto_of_simple P Q (Or.inr hQ) (airyPQ_simple_of_HB hHB hQ) hf hfi hC hb

/-- **Theorem Q (4) for a Hermite-Biehler pair, `HasSum` form under summability.** -/
theorem airyPQ_hasSum {P Q : ℝ[X]} (hHB : AiryPQHB P Q) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hfi : Integrable (fun x : ℝ => f (x : ℂ))) {C ν : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u)
    (hs : Summable (fun z : {z : ℂ // airyPQN P Q z = 0} => f z * (airyPQD P Q z / airyPQN' P Q z ^ 2))) :
    HasSum (fun z : {z : ℂ // airyPQN P Q z = 0} => f z * (airyPQD P Q z / airyPQN' P Q z ^ 2))
      (∫ x : ℝ, f (x : ℂ)) := by
  obtain ⟨T, hT, ht⟩ := airyPQ_tendsto hHB hQ hf hfi hC hb
  have h1 := hs.hasSum.comp hT
  rw [← tendsto_nhds_unique h1 ht]
  exact hs.hasSum

/-- info: 'FormalResearch.Special.airyPQ_tendsto_of_simple' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_tendsto_of_simple

/-- info: 'FormalResearch.Special.airyPQ_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_tendsto

/-- info: 'FormalResearch.Special.airyPQ_hasSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyPQ_hasSum

end FormalResearch.Special

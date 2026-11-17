module

public import FormalResearch.Special.AiryCft2ComboWeights
public import FormalResearch.Special.AiryCft2ComboBounds
public import FormalResearch.Special.AiryCft2Generic
public import FormalResearch.Special.AiryCftQuadrature

/-!
# Theorem D and the Clark-Airy summation for `N = P·Ai + Q·Ai'` (`ν < -1`)

Statement formalised (CFT/PR240 `GENERAL_THEOREMS.md` Theorem 1.1 (Clark-Airy summation) for `ψ_α = cos α Ai - sin α Ai'`,
`sin α ≠ 0` (`P = cos α`, `Q = -sin α`), and `SOFT_EDGE_THEOREMS.md` Lemma 4.4 for constant `P, Q`; `AIRY_POISSON.md` Corollary D1
for `N = Ai`, already in `AiryCftQuadrature`): for real `P`, `Q ≠ 0` put `N = P Ai + Q Ai'`, `D = P² - z Q²`.  For `f` entire with
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)`, `ν < -1`, `e(u) = exp(-(4/3) Re u^{3/2})`:

`∫_ℝ f = Σ_{N(z)=0} f(z) D(z)/N'(z)²`   (`airyNC_quadrature`; HasSum over the subtype of zeros, absolutely convergent).

The zeros of `N` are real and simple and the weights are positive (`AiryCft2ComboZeros`); for `P = cos α`, `Q = -sin α`,
`D(z)/N'(z)² = 1/K(z,z)` with `K(z,z) = Ai'(z)² - z Ai(z)²` at a node (`airyNC_weight_eq_inv_K`, `AiryCft2Clark`, which also gives the
Clark form `airyClark_quadrature`); here the weights are stated in the form `D/N'²` of `SOFT_EDGE_THEOREMS.md` Lemma 4.4).

* `airyNC_defect_bound` (Theorem D for `N`, entire `f`): on a good circle `|u| = r` of `airyNC_good_circle`,
  `‖Σ_{N(t)=0, |t|<r} f(t) D(t)/N'(t)² - ∫_{-r}^{r} f‖ ≤ π r C₀ sup_{|u|=r} ‖f(u)‖/e(u)`.
* `airyNC_quadrature`: the `ν < -1` summation formula above.

Proof: the generic residue-defect bound `cft2_defect_bound` for the pair `(N, M)`, `M = P Bi + Q Bi'`, with residues
`-π M(t)/N'(t) = D(t)/N'(t)²` (`airyNC_weight_eq`, from the Wronskian `N M' - N' M = D/π`), the ratio bounds
`‖M/N ∓ i‖ e ≤ C₀` on the good circles (`airyNC_good_circle`), `e ≤ 1` on `ℝ`, and the absolute convergence of
`AiryCft2ComboWeights`; the partial sums over `|t| < r_k` converge to the full (absolutely convergent) series.

The case `f` holomorphic only near the closed disc is `airyNC_defect_ball` (`AiryCft2ComboBall`).
For `ν ≥ -1` see `AiryCftQNCQuad` and `AiryCftQNonneg` (limit form over good circles for any real `ν` with `f ∈ L¹(ℝ)`; `HasSum` under summability or for
nonnegative terms; this file's absolutely convergent `ν < -1` theorem is not superseded).  The sampling bound of Theorem Q (3) for `N` is `airyNC_sampling_sum` (`AiryCftQNCSample`), giving unconditional absolute convergence and
`HasSum` for every real `ν` with `f ∈ L¹(ℝ)` (`airyNC_hasSum_unc`, `AiryCftQNCUnc`).  Not formalised here: polynomial `P, Q` (see `airyPQ_hasSum_unc`, `AiryPolySample`, umbrella `AiryPoly`, for Hermite-Biehler pairs), and the `α → 0`
limit identifications.
-/

@[expose] public section

open Complex MeasureTheory Filter Topology Set Metric
open scoped Real

namespace FormalResearch.Special

/-- **Theorem D for `N = P Ai + Q Ai'`** (entire `f`) on a circle `|u| = r` with `N ≠ 0` on it and `‖f (M/N ∓ i)‖ ≤ B` on the
upper/lower half circle: `‖Σ_{N(t)=0, |t| ≤ r} f(t) D(t)/N'(t)² - ∫_{-r}^{r} f‖ ≤ π r B`. -/
theorem airyNC_defect_bound (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hN : ∀ u : ℂ, ‖u‖ = r → airyNC P Q u ≠ 0) {B : ℝ}
    (hp : ∀ w : ℂ, ‖w‖ = r → 0 ≤ w.im → ‖f w * (airyMC P Q w / airyNC P Q w - I)‖ ≤ B)
    (hm : ∀ w : ℂ, ‖w‖ = r → w.im ≤ 0 → ‖f w * (airyMC P Q w / airyNC P Q w + I)‖ ≤ B)
    (S : Finset ℂ) (hS : ∀ z : ℂ, z ∈ S ↔ airyNC P Q z = 0 ∧ ‖z‖ ≤ r) :
    ‖(∑ t ∈ S, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) - ∫ x in (-r)..r, f (x : ℂ)‖ ≤ π * r * B := by
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
  have h := cft2_defect_bound (differentiable_airyNC P Q) (differentiable_airyMC P Q) hf hr S hin
    (fun t ht => ((hS t).mp ht).1) hder (fun w hw h0 => (hS w).mpr ⟨h0, hw⟩) hp hm
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

/-- **Clark-Airy summation / Corollary D1 for `N = P Ai + Q Ai'`.** For `Q ≠ 0`, `f` entire with
`‖f(u)‖ ≤ C (1+|u|)^ν e(u)`, `ν < -1`: `∫_ℝ f = Σ_{N(z)=0} f(z) D(z)/N'(z)²` (absolutely convergent), `D = P² - z Q²`. -/
theorem airyNC_quadrature (P Q : ℝ) (hQ : Q ≠ 0) {f : ℂ → ℂ} (hf : Differentiable ℂ f) {C ν : ℝ} (hC : 0 ≤ C)
    (hν : ν < -1) (hb : ∀ u : ℂ, ‖f u‖ ≤ C * (1 + ‖u‖) ^ ν * airyEnv u) :
    HasSum (fun z : {z : ℂ // airyNC P Q z = 0} => f z * (airyDC P Q z / airyNC' P Q z ^ 2))
      (∫ x : ℝ, f (x : ℂ)) := by
  classical
  obtain ⟨C₀, hC₀, k₀, hgc⟩ := airyNC_good_circle P Q hQ
  have hfi := airy_integrable_real hf hC hν hb
  have hsum := airyNC_summable_weighted P Q hQ hC hν hb
  set L : ℂ := ∫ x : ℝ, f (x : ℂ) with hL
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
  -- nonvanishing on the circles
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
  -- the finite sets of zeros in the discs
  set S : ℕ → Finset ℂ := fun k => (airyNC_zeros_finite P Q hQ (r k)).toFinset with hS
  have hSmem : ∀ k z, z ∈ S k ↔ airyNC P Q z = 0 ∧ ‖z‖ ≤ r k := fun k z => by
    simp [hS]
  -- the defect bound on each circle
  have hdef : ∀ k, ‖(∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) -
      ∫ x in (-(r k))..(r k), f (x : ℂ)‖ ≤ π * r k * (C * (1 + r k) ^ ν * C₀) := by
    intro k
    have hpos : 0 ≤ C * (1 + r k) ^ ν := by
      have : 0 < (1 + r k) ^ ν := Real.rpow_pos_of_pos (by linarith [hr0 k]) _
      positivity
    refine airyNC_defect_bound P Q hQ hf (hr0 k) (hNne k) ?_ ?_ (S k) (hSmem k)
    · intro w hw him
      have hfw := hb w
      rw [hw] at hfw
      rw [norm_mul]
      have h7 := ((hr k).2.2 w hw).2.1 him
      have he := airyEnv_pos w
      calc ‖f w‖ * ‖airyMC P Q w / airyNC P Q w - I‖
          ≤ (C * (1 + r k) ^ ν * airyEnv w) * ‖airyMC P Q w / airyNC P Q w - I‖ := by gcongr
        _ = C * (1 + r k) ^ ν * (‖airyMC P Q w / airyNC P Q w - I‖ * airyEnv w) := by ring
        _ ≤ C * (1 + r k) ^ ν * C₀ := by gcongr
    · intro w hw him
      have hfw := hb w
      rw [hw] at hfw
      rw [norm_mul]
      have h7 := ((hr k).2.2 w hw).2.2 him
      have he := airyEnv_pos w
      calc ‖f w‖ * ‖airyMC P Q w / airyNC P Q w + I‖
          ≤ (C * (1 + r k) ^ ν * airyEnv w) * ‖airyMC P Q w / airyNC P Q w + I‖ := by gcongr
        _ = C * (1 + r k) ^ ν * (‖airyMC P Q w / airyNC P Q w + I‖ * airyEnv w) := by ring
        _ ≤ C * (1 + r k) ^ ν * C₀ := by gcongr
  -- the error sequence
  have hrt' : Tendsto (fun k => -r k) atTop atBot := tendsto_neg_atTop_atBot.comp hrt
  have hI : Tendsto (fun k => ∫ x in (-(r k))..(r k), f (x : ℂ)) atTop (𝓝 L) :=
    intervalIntegral_tendsto_integral hfi hrt' hrt
  have hI' : Tendsto (fun k => ‖L - ∫ x in (-(r k))..(r k), f (x : ℂ)‖) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := L)).sub hI
    rw [sub_self] at this
    simpa using this.norm
  have hB : Tendsto (fun k : ℕ => π * C * C₀ * (((k : ℝ) + 1) ^ (ν + 1))) atTop (𝓝 0) := by
    have h0 := tendsto_rpow_neg_atTop (show 0 < -(ν + 1) by linarith)
    simp only [neg_neg] at h0
    have h2 : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa using (h0.comp h2).const_mul (π * C * C₀)
  have hE : Tendsto (fun k => ‖L - ∫ x in (-(r k))..(r k), f (x : ℂ)‖ +
      π * C * C₀ * (((k : ℝ) + 1) ^ (ν + 1))) atTop (𝓝 0) := by
    simpa using hI'.add hB
  -- subtype partial sums
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
  have hTt : Tendsto T atTop atTop := tendsto_atTop_finset_of_monotone hTmono hTex
  have h1 : Tendsto (fun k => ∑ z ∈ T k, g z) atTop (𝓝 (∑' z, g z)) := hsum.hasSum.comp hTt
  have h2 : Tendsto (fun k => ∑ z ∈ T k, g z) atTop (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hE
    rw [hTsum k]
    have hk := hdef k
    have hrk : r k * (1 + r k) ^ ν ≤ ((k : ℝ) + 1) ^ (ν + 1) := by
      have hp1 : (0 : ℝ) < 1 + r k := by linarith [hr0 k]
      have e1 : (1 + r k) ^ (ν + 1) = (1 + r k) ^ ν * (1 + r k) := Real.rpow_add_one hp1.ne' ν
      have h2 : (1 + r k) ^ (ν + 1) ≤ ((k : ℝ) + 1) ^ (ν + 1) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith [hr1 k]) (by linarith)
      have h3 : 0 < (1 + r k) ^ ν := Real.rpow_pos_of_pos hp1 _
      nlinarith
    calc ‖(∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) - L‖
        ≤ ‖(∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) - ∫ x in (-(r k))..(r k), f (x : ℂ)‖ +
          ‖(∫ x in (-(r k))..(r k), f (x : ℂ)) - L‖ := by
          have := norm_add_le ((∑ t ∈ S k, f t * (airyDC P Q t / airyNC' P Q t ^ 2)) -
            ∫ x in (-(r k))..(r k), f (x : ℂ)) ((∫ x in (-(r k))..(r k), f (x : ℂ)) - L)
          rwa [sub_add_sub_cancel] at this
      _ ≤ _ := by
          rw [add_comm]
          refine add_le_add ?_ ?_
          · rw [norm_sub_rev]
          · refine hk.trans ?_
            have : π * r k * (C * (1 + r k) ^ ν * C₀) = π * C * C₀ * (r k * (1 + r k) ^ ν) := by ring
            rw [this]
            gcongr
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  exact hsum.hasSum

/-- info: 'FormalResearch.Special.airyNC_defect_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_defect_bound

/-- info: 'FormalResearch.Special.airyNC_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.airyNC_quadrature

end FormalResearch.Special

module

public import FormalResearch.Asymptotics.UniformExpansion

/-!
# Expansions from convergent power series with geometric coefficient bounds

If `f z t = ∑_r a r z t^r` as a convergent series for `t` small, with coefficients bounded
geometrically, `|a r z| ≤ C q^r` uniformly for `z ∈ K`, then the series is a uniform asymptotic
expansion in `t` in the sense of `HasUniformExpansion` (`hasUniformExpansion_of_hasSum_geom`).
The remainder after `R` terms is the tail of a geometric series, bounded by `2 C q^R t^R` once
`q t ≤ 1/2`.
-/

@[expose] public section

open Filter Topology Finset

namespace FormalResearch.Asymptotics

variable {E : Type*}

/-- **Convergent series with geometric bounds are uniform expansions.**  Suppose that for all
`z ∈ K` the coefficients satisfy `|a r z| ≤ C q^r`, and that for `t` in a set of `l` (with
`0 ≤ t` and `q t ≤ 1/2`) the series `∑ t^r a r z` converges to `f z t`.  Then `f` has the uniform
expansion `∑ t^r a r z` along `l`, uniformly for `z ∈ K`, with `ε = id`. -/
theorem hasUniformExpansion_of_hasSum_geom {f : E → ℝ → ℝ} {a : ℕ → E → ℝ} {K : Set E}
    {l : Filter ℝ} {C q : ℝ} (hq : 0 ≤ q)
    (hbound : ∀ z ∈ K, ∀ r, |a r z| ≤ C * q ^ r)
    (hl : ∀ᶠ t in l, 0 ≤ t ∧ q * t ≤ 1 / 2)
    (hsum : ∀ z ∈ K, ∀ t : ℝ, 0 ≤ t → q * t ≤ 1 / 2 →
      HasSum (fun r : ℕ => t ^ r * a r z) (f z t)) :
    HasUniformExpansion f a (fun t : ℝ => t) l K := by
  rw [hasUniformExpansion_iff]
  intro R
  refine ⟨2 * C * q ^ R, ?_⟩
  filter_upwards [hl] with t ⟨ht0, hqt⟩ z hz
  have hC : 0 ≤ C := by
    have := (abs_nonneg (a 0 z)).trans (hbound z hz 0)
    simpa using this
  have hs := hsum z hz t ht0 hqt
  have htail : HasSum (fun r : ℕ => t ^ (r + R) * a (r + R) z)
      (f z t - ∑ i ∈ range R, t ^ i * a i z) :=
    (hasSum_nat_add_iff' R).2 hs
  have hqt0 : 0 ≤ q * t := mul_nonneg hq ht0
  have hgeo : HasSum (fun r : ℕ => C * (q * t) ^ R * (q * t) ^ r)
      (C * (q * t) ^ R * (1 - q * t)⁻¹) :=
    (hasSum_geometric_of_lt_one hqt0 (by linarith)).mul_left _
  have hb : ‖f z t - ∑ i ∈ range R, t ^ i * a i z‖ ≤ C * (q * t) ^ R * (1 - q * t)⁻¹ := by
    refine htail.norm_le_of_bounded hgeo fun r => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht0 _)]
    calc t ^ (r + R) * |a (r + R) z| ≤ t ^ (r + R) * (C * q ^ (r + R)) :=
          mul_le_mul_of_nonneg_left (hbound z hz _) (pow_nonneg ht0 _)
      _ = C * (q * t) ^ R * (q * t) ^ r := by rw [mul_pow, mul_pow]; ring
  have hinv : (1 - q * t)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have h0 : 0 ≤ C * (q * t) ^ R := mul_nonneg hC (pow_nonneg hqt0 _)
  simp only [smul_eq_mul, Real.norm_eq_abs]
  calc _ ≤ C * (q * t) ^ R * (1 - q * t)⁻¹ := hb
    _ ≤ C * (q * t) ^ R * 2 := mul_le_mul_of_nonneg_left hinv h0
    _ = 2 * C * q ^ R * |t| ^ R := by rw [abs_of_nonneg ht0, mul_pow]; ring

/-- info: 'FormalResearch.Asymptotics.hasUniformExpansion_of_hasSum_geom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hasUniformExpansion_of_hasSum_geom

end FormalResearch.Asymptotics

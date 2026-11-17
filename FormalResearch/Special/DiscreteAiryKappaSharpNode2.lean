module

public import FormalResearch.Special.DiscreteAiryKappaSharpNode1
public import FormalResearch.Special.DiscreteAiryKappaSharpGeom
public import FormalResearch.Special.DiscreteAiryKappaSharpAssemble
public import FormalResearch.Special.DiscreteAiryKappaOrderLow

/-!
# Sharp `κ`: node-level bookkeeping lemmas (plan K1, sharp constant, step 11)

* `ksf_ico_range`: `Σ_{k ∈ [a, a+n)} f k = Σ_{i < n} f (a + i)` over `ℤ`;
* `ksf_cover`: the three-way split `N ≤ L + B + Z` of the Gauss weight (`L = Σ_{[0,k₀)}`, `B = Σ_{[k₀,b)}`, `Z = Σ_{[b, e)}`);
* `ksf_geo`: the position of the band end `q_b`: `A²/(2q_*) ≤ q_* - q_b ≤ A²/q_* + h` from `q_b ≤ q_A < q_b + h`, `q_A = √(q_*² - A²)`;
* `ksf_zone_hyps`: the two lower/upper bounds of `X_b = ζ(q_b)/δ²` used by the zone mass bound;
* `ksf_ye`: `y^{-3/2} ≤ K_Y δ³` for `y ≥ c₁ A²/(2 q_* δ²)`;
* `ksf_zeta_alg`: the zone mass bound in the form `Z ≤ 2 t N ζ` with `t = κ²δ/2`.

**Claim class: proved.**
-/

@[expose] public section

open Finset Set

namespace FormalResearch.Special

/-- `Σ_{[a, a+n)} f = Σ_{i<n} f(a+i)` over `ℤ`. -/
lemma ksf_ico_range (f : ℤ → ℝ) (a : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.Ico a (a + (n : ℤ)), f k = ∑ i ∈ range n, f (a + (i : ℤ)) := by
  have : Finset.Ico a (a + (n : ℤ)) = (range n).image (fun i : ℕ => a + (i : ℤ)) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨h1, h2⟩
      exact ⟨(k - a).toNat, by omega, by omega⟩
    · rintro ⟨i, hi, rfl⟩
      omega
  rw [this, Finset.sum_image (by intro i _ j _ hij; simpa using hij)]

/-- **The three-way split of the Gauss weight**. -/
lemma ksf_cover {Y : ℤ → ℝ} {Nz k0 b e : ℤ} {δ : ℝ} (hk0 : 0 ≤ k0) (hkb : k0 ≤ b) (hbe : b ≤ e) (hNe : Nz ≤ e)
    (hcover : ∀ S : Finset ℤ, (∀ k : ℤ, 0 ≤ k → k < Nz → k ∈ S) → 1 / δ ^ 3 ≤ ∑ k ∈ S, Y k ^ 2) :
    1 / δ ^ 3 ≤ ∑ k ∈ Finset.Ico (0 : ℤ) k0, Y k ^ 2 + ∑ k ∈ Finset.Ico k0 b, Y k ^ 2 + ∑ k ∈ Finset.Ico b e, Y k ^ 2 := by
  have h := hcover (Finset.Ico (0 : ℤ) e) (fun k hk0 hkN => Finset.mem_Ico.2 ⟨hk0, by omega⟩)
  rw [kk_ico_split (fun k => Y k ^ 2) (b := b) (by omega) hbe, kk_ico_split (fun k => Y k ^ 2) (b := k0) hk0 hkb] at h
  linarith

/-- **The band end**: `q_b ≤ q_A < q_b + h`, `q_A = √(q_*² - A²)`, `0 < A`, `0 < q_b` give
`A²/(2 q_*) ≤ q_* - q_b ≤ A²/q_* + h`. -/
lemma ksf_geo {qs A h qb : ℝ} (hqs : 0 < qs) (hA : 0 < A) (hAq : A < qs) (_hh : 0 < h) (hqb0 : 0 < qb)
    (h1 : qb ≤ √(qs ^ 2 - A ^ 2)) (h2 : √(qs ^ 2 - A ^ 2) < qb + h) :
    A ^ 2 / (2 * qs) ≤ qs - qb ∧ qs - qb ≤ A ^ 2 / qs + h := by
  have hq2 : 0 < qs ^ 2 - A ^ 2 := by nlinarith
  have hsq : √(qs ^ 2 - A ^ 2) ^ 2 = qs ^ 2 - A ^ 2 := Real.sq_sqrt hq2.le
  have hqA0 : 0 ≤ √(qs ^ 2 - A ^ 2) := Real.sqrt_nonneg _
  have hqAq : √(qs ^ 2 - A ^ 2) < qs := by
    rw [Real.sqrt_lt' hqs]; nlinarith
  constructor
  · have h3 : qb ^ 2 ≤ qs ^ 2 - A ^ 2 := by rw [← hsq]; exact pow_le_pow_left₀ hqb0.le h1 2
    have hqbq : qb < qs := by linarith
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have h3 : qs - √(qs ^ 2 - A ^ 2) ≤ A ^ 2 / qs := by
      rw [le_div_iff₀ hqs]
      have : (qs - √(qs ^ 2 - A ^ 2)) * (qs + √(qs ^ 2 - A ^ 2)) = A ^ 2 := by nlinarith
      nlinarith
    linarith

/-- `X_b = ζ(q_b)/δ²` on the zone boundary: `X_b ≤ -1` once `δ² ≤ c₁ A²/(2 q_*)`, and `-X_b ≤ R₀/δ²` with `R₀ = c₂ (A²/q_* + h)`. -/
lemma ksf_zone_hyps {x r c1 c2 δ A h qb : ℝ} (C : KshChart x r c1 c2) (hδ : 0 < δ) (hqs : 0 < √(1 - x ^ 2))
    (hqb : qb ∈ Icc (√(1 - x ^ 2) - r) (√(1 - x ^ 2)))
    (hg : A ^ 2 / (2 * √(1 - x ^ 2)) ≤ √(1 - x ^ 2) - qb) (hg2 : √(1 - x ^ 2) - qb ≤ A ^ 2 / √(1 - x ^ 2) + h)
    (hδ2 : 2 * √(1 - x ^ 2) * δ ^ 2 ≤ c1 * A ^ 2) :
    kshZ x qb / δ ^ 2 ≤ -1 ∧ -(kshZ x qb / δ ^ 2) ≤ c2 * (A ^ 2 / √(1 - x ^ 2) + h) / δ ^ 2 := by
  obtain ⟨hz1, hz2⟩ := C.zeta_bounds hqb
  have hδ2' : 0 < δ ^ 2 := by positivity
  constructor
  · rw [div_le_iff₀ hδ2']
    have h3 : c1 * (A ^ 2 / (2 * √(1 - x ^ 2))) ≤ c1 * (√(1 - x ^ 2) - qb) := mul_le_mul_of_nonneg_left hg C.hc1.le
    have h4 : 2 * √(1 - x ^ 2) * δ ^ 2 / (2 * √(1 - x ^ 2)) ≤ c1 * A ^ 2 / (2 * √(1 - x ^ 2)) :=
      div_le_div_of_nonneg_right hδ2 (by positivity)
    have e1 : 2 * √(1 - x ^ 2) * δ ^ 2 / (2 * √(1 - x ^ 2)) = δ ^ 2 := by field_simp
    have e2 : c1 * A ^ 2 / (2 * √(1 - x ^ 2)) = c1 * (A ^ 2 / (2 * √(1 - x ^ 2))) := by ring
    nlinarith
  · rw [← neg_div, div_le_div_iff_of_pos_right hδ2']
    have : c2 * (√(1 - x ^ 2) - qb) ≤ c2 * (A ^ 2 / √(1 - x ^ 2) + h) :=
      mul_le_mul_of_nonneg_left hg2 (by linarith [C.hc1, C.hc12])
    linarith

/-- `y^{-3/2} ≤ K_Y δ³` for `y ≥ y₀ = c₁ A²/(2 q_* δ²) > 0`, `K_Y = (2 q_*/(c₁ A²))^{3/2}`. -/
lemma ksf_ye {c1 A qs δ y : ℝ} (hc1 : 0 < c1) (hA : 0 < A) (hqs : 0 < qs) (hδ : 0 < δ) (hy : c1 * A ^ 2 / (2 * qs * δ ^ 2) ≤ y) :
    y ^ (-(3 / 2) : ℝ) ≤ (2 * qs / (c1 * A ^ 2)) ^ (3 / 2 : ℝ) * δ ^ 3 := by
  have hy0 : 0 < c1 * A ^ 2 / (2 * qs * δ ^ 2) := by positivity
  have h1 : y ^ (-(3 / 2) : ℝ) ≤ (c1 * A ^ 2 / (2 * qs * δ ^ 2)) ^ (-(3 / 2) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hy0 hy (by norm_num)
  refine h1.trans (le_of_eq ?_)
  have e : c1 * A ^ 2 / (2 * qs * δ ^ 2) = (2 * qs / (c1 * A ^ 2) * δ ^ 2)⁻¹ := by field_simp
  rw [e, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), neg_neg,
    Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le]
  norm_num

/-- The zone mass in the form `Z ≤ 2 t N ζ`, `t = κ²δ/2`, `N = 1/δ³`: from
`Z ≤ 2G²κ²(s/(c₁δ²)) + K₃κ²/δ` (`s = √R₀/π + 2c₂R₀`). -/
lemma ksf_zeta_alg {Z G κ s c1 K3 δ : ℝ} (hδ : 0 < δ) (hc1 : 0 < c1)
    (h : Z ≤ 2 * G ^ 2 * κ ^ 2 * (s / (c1 * δ ^ 2)) + K3 * κ ^ 2 / δ) :
    Z ≤ 2 * (κ ^ 2 * δ / 2) * (1 / δ ^ 3) * (2 * G ^ 2 * s / c1 + K3 * δ) := by
  refine h.trans (le_of_eq ?_)
  field_simp

/-- info: 'FormalResearch.Special.ksf_ye' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.ksf_ye

end FormalResearch.Special

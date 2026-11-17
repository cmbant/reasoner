module

public import FormalResearch.Special.HermiteNorm
public import FormalResearch.Special.DiscreteAiryUnifTheorem
public import FormalResearch.Special.DiscreteAiryUnifHahnData

/-!
# The Hermite chain as a simple-turn datum of the discrete-to-Airy theorem

The Hermite recurrence `√((n+1)/2) φ_{n+1} + √(n/2) φ_{n-1} = x φ_n` is a Jacobi chain `jac a c Y = 0`
(`jac a c y k = a(k+1) y(k+1) + a k y(k-1) - c k y k`) once the index is *reflected*, `Y_k = φ_{-k}(x)`, so that the
exponentially decaying (forbidden) side `n < x²/2` is the side of large `k` (the orientation of `DunDatum`: oscillatory for
`q < c`, forbidden for `q > c`).  With `S = x²/2`, `h = δ³ = 1/S` and the lattice `q_k = (k - ½) δ³`, the coefficients are
*exactly* (no `O(h²)` perturbation, `E = 0`)

* `a_k = A(q_k - δ³/2)` with `A(q) = √(-q/2)`  (`a_k = √(1-k)/x`),
* `c_k = 2 A(q_k) u(q_k) = √2` with `u(q) = (√(-q))⁻¹`,

and the turning point of `u(c) = 1` is `c = -1` (`n + ½ = S`, i.e. `2n+1 = x²`, the classical turning point).  Here
`u' = ½ (-q)^{-3/2} > 0` at `c`, so the datum is a simple turn.

* `hermite_datum`: `DunDatum hmU hmA (-1) (1/2) Ku m aLo aHi KA` for explicit-by-compactness constants (absolute, no `x`);
* `hermite_row`: `jac hmCoefA hmCoefC Y k = 0` for `Y_k = φ_{-k}(x)` and every `k ≤ 0` (so every row with `n = -k ≥ 0`).

**Claim class: proved.**  Numerical sanity check (mpmath, 30 digits, scratch, not committed): for `S = 200, 800, 3200`
the ratio `φ_n(x) / (g Ai(X))` with the explicit Langer data is constant to `~10⁻⁴` on `X ∈ [-40, 120]`, equal to
`0.6431, 0.5729, 0.5104 = S^{-1/12}(1 + O(1/S))`.
-/

@[expose] public section

open Set Metric FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- `u(q) = (√(-q))⁻¹`: the Hermite chain's `c/(2a)`, normalised so that the turn is at `q = -1`. -/
noncomputable def hmU (q : ℝ) : ℝ := (Real.sqrt (-q))⁻¹

/-- `A(q) = √(-q/2)`: the Hermite off-diagonal coefficient `√(k/2)` in the chart `q = -k/S`. -/
noncomputable def hmA (q : ℝ) : ℝ := Real.sqrt (-q / 2)

lemma hmU_cd : ContDiffOn ℝ 3 hmU (Iio 0) := by
  unfold hmU
  refine ContDiffOn.inv (ContDiffOn.sqrt (by fun_prop) (fun q hq => ?_)) (fun q hq => ?_)
  · have : q < 0 := hq
    linarith
  · have : q < 0 := hq
    exact (Real.sqrt_pos.2 (by linarith)).ne'

lemma hmA_cd : ContDiffOn ℝ 3 hmA (Iio 0) := by
  unfold hmA
  refine ContDiffOn.sqrt (by fun_prop) (fun q hq => ?_)
  have : q < 0 := hq
  linarith

lemma hasDerivAt_hmU_neg_one : HasDerivAt hmU (1 / 2) (-1) := by
  have h1 : HasDerivAt (fun q : ℝ => -q) (-1) (-1) := (hasDerivAt_id (-1 : ℝ)).neg
  have h2 := h1.sqrt (by norm_num : (-(-1 : ℝ)) ≠ 0)
  have h3 := h2.inv (by simp : Real.sqrt (-(-1 : ℝ)) ≠ 0)
  refine h3.congr_deriv ?_
  norm_num

lemma hmU_neg_one : hmU (-1) = 1 := by simp [hmU]

/-- **The Hermite datum** is in the class `DunDatum` on `ball (-1) (1/2)`, with absolute constants. -/
theorem hermite_datum : ∃ Ku m aLo aHi KA : ℝ, 0 < Ku ∧ 0 < m ∧ 0 < aLo ∧ aLo ≤ aHi ∧ 0 ≤ KA ∧
    DunDatum hmU hmA (-1) (1 / 2) Ku m aLo aHi KA := by
  have hS : IsCompact (Icc (-3 / 2 : ℝ) (-1 / 2)) := isCompact_Icc
  have hSU : Icc (-3 / 2 : ℝ) (-1 / 2) ⊆ Iio 0 := fun q hq => by
    have := hq.2
    show q < 0
    linarith
  obtain ⟨K1, hK1n, hK1⟩ := dun_fam_bound isOpen_Iio hmU_cd hS hSU
  obtain ⟨K2, hK2n, hK2⟩ := dun_fam_bound isOpen_Iio hmA_cd hS hSU
  have hball : ball (-1 : ℝ) (1 / 2) ⊆ Icc (-3 / 2 : ℝ) (-1 / 2) := fun q hq => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hq
    constructor <;> linarith [hq.1, hq.2]
  have hballU : ball (-1 : ℝ) (1 / 2) ⊆ Iio 0 := hball.trans hSU
  refine ⟨K1 + 1, 1 / 2, 1 / 2, 1, K2, by linarith, by norm_num, by norm_num, by norm_num, hK2n, ?_⟩
  refine
    { u3 := hmU_cd.mono hballU
      u0 := hmU_neg_one
      um := by rw [hasDerivAt_hmU_neg_one.deriv]
      ub := fun z hz => ?_
      A2 := (hmA_cd.mono hballU).of_le (by norm_num)
      Ab := fun z hz => ?_
      Aj := fun z hz => ?_ }
  · obtain ⟨b1, b2, b3⟩ := hK1 z (hball hz)
    exact ⟨by linarith, by linarith, by linarith⟩
  · have hz' := hball hz
    have h1 : (1 / 4 : ℝ) ≤ -z / 2 := by linarith [hz'.2]
    have h2 : -z / 2 ≤ 1 := by linarith [hz'.1]
    constructor
    · calc (1 / 2 : ℝ) = Real.sqrt (1 / 4) := by
            rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        _ ≤ hmA z := Real.sqrt_le_sqrt h1
    · calc hmA z ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h2
        _ = 1 := Real.sqrt_one
  · obtain ⟨b1, b2, b3⟩ := hK2 z (hball hz)
    exact ⟨b1, b2⟩

/-- The Hermite chain's off-diagonal coefficients `a_k = A(q_k - δ³/2)` on the lattice `q_k = -δ³/2 + k δ³`. -/
noncomputable def hmCoefA (δ : ℝ) (k : ℤ) : ℝ := hmA (dalQ (-δ ^ 3 / 2) δ k - δ ^ 3 / 2)

/-- The Hermite chain's diagonal `c_k = 2 A(q_k) u(q_k)`. -/
noncomputable def hmCoefC (δ : ℝ) (k : ℤ) : ℝ := 2 * hmA (dalQ (-δ ^ 3 / 2) δ k) * hmU (dalQ (-δ ^ 3 / 2) δ k)

/-- The reflected Hermite chain `Y_k = φ_{-k}(x)`. -/
noncomputable def hmY (x : ℝ) (k : ℤ) : ℝ := hermitePsi (-k) x

lemma sqrt_div_sq_eq {m x : ℝ} (hm : 0 ≤ m) (hx : 0 < x) : √(m / x ^ 2) = √2 / x * √(m / 2) := by
  have h2 : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  rw [Real.sqrt_div hm, Real.sqrt_sq hx.le, Real.sqrt_div hm]
  field_simp

lemma hmCoefA_eq' {x δ : ℝ} (hx : 0 < x) (hδ : δ ^ 3 = 2 / x ^ 2) (j : ℤ) (hj : j ≤ 1) :
    hmCoefA δ j = √2 / x * √((1 - (j : ℝ)) / 2) := by
  have h : -(dalQ (-δ ^ 3 / 2) δ j - δ ^ 3 / 2) / 2 = (1 - (j : ℝ)) / x ^ 2 := by
    simp only [dalQ]; rw [hδ]; field_simp; ring
  unfold hmCoefA hmA
  rw [h]
  exact sqrt_div_sq_eq (by have : (j : ℝ) ≤ 1 := by exact_mod_cast hj
                           linarith) hx

lemma two_sqrt_half_inv {t : ℝ} (ht : 0 < t) : 2 * √(t / 2) * (√t)⁻¹ = √2 := by
  have h2 : 0 < √(2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs : 0 < √t := Real.sqrt_pos.2 ht
  have h22 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [Real.sqrt_div ht.le]
  field_simp
  nlinarith

lemma hmCoefC_eq {x δ : ℝ} (hx : 0 < x) (hδ : δ ^ 3 = 2 / x ^ 2) (k : ℤ) (hk : k ≤ 0) :
    hmCoefC δ k = √2 := by
  have hk' : (k : ℝ) ≤ 0 := by exact_mod_cast hk
  have ht : -(dalQ (-δ ^ 3 / 2) δ k) = (1 - 2 * (k : ℝ)) / x ^ 2 := by
    simp only [dalQ]; rw [hδ]; field_simp; ring
  have hpos : 0 < (1 - 2 * (k : ℝ)) / x ^ 2 := div_pos (by linarith) (by positivity)
  unfold hmCoefC hmA hmU
  rw [ht]
  exact two_sqrt_half_inv hpos

/-- **The Hermite rows**: `Y_k = φ_{-k}(x)` solves `jac (hmCoefA δ) (hmCoefC δ) Y k = 0` for all `k ≤ 0`, when `x > 0`
and `δ³ = 2/x²` (`S = x²/2 = δ⁻³`). -/
theorem hermite_row {x δ : ℝ} (hx : 0 < x) (hδ : δ ^ 3 = 2 / x ^ 2) (k : ℤ) (hk : k ≤ 0) :
    jac (hmCoefA δ) (hmCoefC δ) (hmY x) k = 0 := by
  have hn : (0 : ℤ) ≤ -k := by omega
  have hrec := hermitePsi_rec (-k) hn x
  have e1 : hmCoefA δ (k + 1) = √2 / x * √(((-k : ℤ) : ℝ) / 2) := by
    rw [hmCoefA_eq' hx hδ (k + 1) (by omega)]; push_cast; ring_nf
  have e2 : hmCoefA δ k = √2 / x * √((((-k : ℤ) : ℝ) + 1) / 2) := by
    rw [hmCoefA_eq' hx hδ k (by omega)]; push_cast; ring_nf
  have e3 : hmY x (k + 1) = hermitePsi (-k - 1) x := by
    unfold hmY; congr 1; ring
  have e4 : hmY x (k - 1) = hermitePsi (-k + 1) x := by
    unfold hmY; congr 1; ring
  simp only [jac]
  rw [e1, e2, e3, e4, hmCoefC_eq hx hδ k hk]
  have : hmY x k = hermitePsi (-k) x := rfl
  rw [this]
  have hx0 : x ≠ 0 := hx.ne'
  have : √2 / x * √(((-k : ℤ) : ℝ) / 2) * hermitePsi (-k - 1) x +
      √2 / x * √((((-k : ℤ) : ℝ) + 1) / 2) * hermitePsi (-k + 1) x =
      √2 / x * (x * hermitePsi (-k) x) := by
    rw [← hrec]; ring
  rw [this]; field_simp; ring

/-- info: 'FormalResearch.Special.hermite_datum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_datum

/-- info: 'FormalResearch.Special.hermite_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.hermite_row

end FormalResearch.Special

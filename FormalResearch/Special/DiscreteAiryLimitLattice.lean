module

public import FormalResearch.Special.DiscreteAiryLimitData

/-!
# Discrete-to-Airy limit, step 2: the lattice `q_k = q₀ + kδ³` and its window indices

Part of the wiring module `DiscreteAiryLimit*`.  Let `ζ` be `C¹` on the window `[c₀ - r, c₀ + r]` with
`ζ(c₀) = 0` and `0 < c₁ ≤ ζ' ≤ c₂` there, and let `h = δ³`, `q_k = q₀ + k h`, `X_k = h^{-2/3} ζ(q_k) = ζ(q_k)/δ²`.

`dal_lattice_window`: there is `δ₀ > 0` such that for `δ ≤ δ₀` and every `q₀` there are indices `J ≤ m ≤ N` with

* the sites `q_k, k ∈ [J, N+1]`, lie in the window; `q_J ≥ c₀ - A₀δ²/c₂`, `q_m ∈ [c₀, c₀ + h)`, `q_{N+1} ≤ c₀ + r/2`,
  `q_N ≥ c₀ + r/4`;
* `X_k ≥ 0` for `k ≥ m`, `X_m ≤ c₂ δ`, `X_k ≥ -A₀` on `[J, m]`, `X_m - X_J ≤ A₀ + c₂`, `X_k ≤ (c₂ r/2)/δ²` on `[m, N+1]`;
* spacings `c₁ δ ≤ X_{k+1} - X_k ≤ c₂ δ` for `k ∈ [J, N]` (mean value inequality: `X_{k+1}-X_k = δ⁻² (ζ(q_k+δ³)-ζ(q_k))`);
* `|q_k - c₀| ≤ (A₀/c₂ + 1) δ²` on `[J, m]` (used for the near-hyperbolic constants of the oscillatory window).

Proved (ceilings/floors and the mean value inequality).  The same `m`, `J`, `N` are used by the main theorem
`discrete_airy_limit`: `J..m` is the bounded oscillatory window `X ∈ [-A₀, 0]`, `m..N+1` the forbidden side up to the
fixed point `c₀ + r/2`.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-- `(δ³)^{-2/3} = (δ²)⁻¹` for `δ > 0`. -/
lemma dal_rpow_cube {δ : ℝ} (hδ : 0 < δ) : (δ ^ 3) ^ (-(2 / 3 : ℝ)) = (δ ^ 2)⁻¹ := by
  rw [← Real.rpow_natCast δ 3, ← Real.rpow_mul hδ.le]
  have : ((3 : ℕ) : ℝ) * (-(2 / 3 : ℝ)) = -(2 : ℕ) := by push_cast; ring
  rw [this, Real.rpow_neg hδ.le, Real.rpow_natCast]

/-- Mean value inequalities for `ζ` on the window. -/
lemma dal_zeta_bounds {ζ : ℝ → ℝ} {c0 r c1 c2 : ℝ}
    (hd : ∀ q ∈ Icc (c0 - r) (c0 + r), HasDerivAt ζ (deriv ζ q) q ∧ c1 ≤ deriv ζ q ∧ deriv ζ q ≤ c2)
    {x y : ℝ} (hx : x ∈ Icc (c0 - r) (c0 + r)) (hy : y ∈ Icc (c0 - r) (c0 + r)) (hxy : x ≤ y) :
    c1 * (y - x) ≤ ζ y - ζ x ∧ ζ y - ζ x ≤ c2 * (y - x) := by
  have hcont : ContinuousOn ζ (Icc (c0 - r) (c0 + r)) := fun q hq => (hd q hq).1.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ ζ (interior (Icc (c0 - r) (c0 + r))) := fun q hq =>
    (hd q (interior_subset hq)).1.differentiableAt.differentiableWithinAt
  constructor
  · exact Convex.mul_sub_le_image_sub_of_le_deriv (convex_Icc _ _) hcont hdiff
      (fun q hq => (hd q (interior_subset hq)).2.1) x hx y hy hxy
  · exact Convex.image_sub_le_mul_sub_of_deriv_le (convex_Icc _ _) hcont hdiff
      (fun q hq => (hd q (interior_subset hq)).2.2) x hx y hy hxy

/-- The window indices: ceilings and floors on the lattice `q₀ + kδ³` (pure real inequalities). -/
lemma dal_idx {δ q₀ c0 r e : ℝ} (hδ : 0 < δ) (h38 : δ ^ 3 ≤ r / 8) (he3 : δ ^ 3 ≤ e) :
    ∃ J m N : ℤ, J ≤ m ∧ m ≤ N ∧ c0 - e ≤ q₀ + (J : ℝ) * δ ^ 3 ∧ q₀ + (J : ℝ) * δ ^ 3 < c0 - e + δ ^ 3 ∧
      c0 ≤ q₀ + (m : ℝ) * δ ^ 3 ∧ q₀ + (m : ℝ) * δ ^ 3 < c0 + δ ^ 3 ∧
      q₀ + ((N : ℝ) + 1) * δ ^ 3 ≤ c0 + r / 2 ∧ c0 + r / 4 ≤ q₀ + (N : ℝ) * δ ^ 3 := by
  have h3 : 0 < δ ^ 3 := by positivity
  set J : ℤ := ⌈(c0 - e - q₀) / δ ^ 3⌉ with hJdef
  set m : ℤ := ⌈(c0 - q₀) / δ ^ 3⌉ with hmdef
  set F : ℤ := ⌊(c0 + r / 2 - q₀) / δ ^ 3⌋ with hFdef
  set N : ℤ := F - 1 with hNdef
  have hJ1 : c0 - e ≤ q₀ + (J : ℝ) * δ ^ 3 := by
    have := Int.le_ceil ((c0 - e - q₀) / δ ^ 3)
    rw [div_le_iff₀ h3] at this; linarith
  have hJ2 : q₀ + (J : ℝ) * δ ^ 3 < c0 - e + δ ^ 3 := by
    have := Int.ceil_lt_add_one ((c0 - e - q₀) / δ ^ 3)
    rw [← hJdef, ← sub_lt_iff_lt_add, lt_div_iff₀ h3] at this
    nlinarith
  have hm1 : c0 ≤ q₀ + (m : ℝ) * δ ^ 3 := by
    have := Int.le_ceil ((c0 - q₀) / δ ^ 3)
    rw [div_le_iff₀ h3] at this; linarith
  have hm2 : q₀ + (m : ℝ) * δ ^ 3 < c0 + δ ^ 3 := by
    have := Int.ceil_lt_add_one ((c0 - q₀) / δ ^ 3)
    rw [← hmdef, ← sub_lt_iff_lt_add, lt_div_iff₀ h3] at this
    nlinarith
  have hF1 : q₀ + (F : ℝ) * δ ^ 3 ≤ c0 + r / 2 := by
    have := Int.floor_le ((c0 + r / 2 - q₀) / δ ^ 3)
    rw [le_div_iff₀ h3] at this; linarith
  have hF2 : c0 + r / 2 < q₀ + ((F : ℝ) + 1) * δ ^ 3 := by
    have := Int.lt_floor_add_one ((c0 + r / 2 - q₀) / δ ^ 3)
    rw [← hFdef, div_lt_iff₀ h3] at this
    nlinarith
  have hNc : (N : ℝ) = (F : ℝ) - 1 := by rw [hNdef]; push_cast; ring
  have hqN1 : q₀ + ((N : ℝ) + 1) * δ ^ 3 ≤ c0 + r / 2 := by rw [hNc]; linarith
  have hqN : c0 + r / 4 ≤ q₀ + (N : ℝ) * δ ^ 3 := by rw [hNc]; nlinarith
  have hJm : J ≤ m := by
    apply Int.ceil_mono
    exact div_le_div_of_nonneg_right (by linarith) h3.le
  have hmN : m ≤ N := by
    have : m + 1 ≤ F := by
      rw [hFdef]; apply Int.le_floor.2
      rw [le_div_iff₀ h3]; push_cast; nlinarith
    omega
  exact ⟨J, m, N, hJm, hmN, hJ1, hJ2, hm1, hm2, hqN1, hqN⟩

/-- **Lattice window indices.**  See the module docstring. -/
theorem dal_lattice_window {ζ : ℝ → ℝ} {c0 r c1 c2 A0 : ℝ} (hr : 0 < r) (hc1 : 0 < c1) (hc12 : c1 ≤ c2)
    (hA0 : 0 < A0) (hz0 : ζ c0 = 0)
    (hd : ∀ q ∈ Icc (c0 - r) (c0 + r), HasDerivAt ζ (deriv ζ q) q ∧ c1 ≤ deriv ζ q ∧ deriv ζ q ≤ c2) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 ∧ ∀ δ q₀ : ℝ, 0 < δ → δ ≤ δ0 → ∃ J m N : ℤ, J ≤ m ∧ m ≤ N ∧
      (∀ k ∈ Finset.Icc J (N + 1), q₀ + (k : ℝ) * δ ^ 3 ∈ Icc (c0 - r) (c0 + r)) ∧
      c0 - A0 * δ ^ 2 / c2 ≤ q₀ + (J : ℝ) * δ ^ 3 ∧ q₀ + (J : ℝ) * δ ^ 3 ≤ c0 ∧
      c0 ≤ q₀ + (m : ℝ) * δ ^ 3 ∧ q₀ + (m : ℝ) * δ ^ 3 < c0 + δ ^ 3 ∧
      q₀ + ((N : ℝ) + 1) * δ ^ 3 ≤ c0 + r / 2 ∧ c0 + r / 4 ≤ q₀ + (N : ℝ) * δ ^ 3 ∧
      (∀ k ∈ Finset.Icc J m, |q₀ + (k : ℝ) * δ ^ 3 - c0| ≤ (A0 / c2 + 1) * δ ^ 2) ∧
      (∀ k ∈ Finset.Icc m (N + 1), 0 ≤ (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (k : ℝ) * δ ^ 3)) ∧
      (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (m : ℝ) * δ ^ 3) ≤ c2 * δ ∧
      (∀ k ∈ Finset.Icc J m, -A0 ≤ (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (k : ℝ) * δ ^ 3)) ∧
      (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (m : ℝ) * δ ^ 3) -
          (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (J : ℝ) * δ ^ 3) ≤ A0 + c2 ∧
      (∀ k ∈ Finset.Icc m (N + 1),
        (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (k : ℝ) * δ ^ 3) ≤ (c2 * (r / 2)) / δ ^ 2) ∧
      c1 * (r / 4) / δ ^ 2 ≤ (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (N : ℝ) * δ ^ 3) ∧
      (∀ k ∈ Finset.Icc J N, c1 * δ ≤ (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3) -
          (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (k : ℝ) * δ ^ 3) ∧
        (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3) -
          (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ (q₀ + (k : ℝ) * δ ^ 3) ≤ c2 * δ) := by
  have hc2 : 0 < c2 := lt_of_lt_of_le hc1 hc12
  have hA0c : 0 < A0 / c2 := by positivity
  set δ0 : ℝ := min (min 1 (A0 / c2)) (min (r * c2 / A0) (r / 8)) with hδ0
  have hδ0pos : 0 < δ0 :=
    lt_min (lt_min one_pos hA0c) (lt_min (by positivity) (by positivity))
  refine ⟨δ0, hδ0pos, (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  intro δ q₀ hδ hδδ0
  have hδ1 : δ ≤ 1 := hδδ0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδA : δ ≤ A0 / c2 := hδδ0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδr : δ ≤ r * c2 / A0 := hδδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ8 : δ ≤ r / 8 := hδδ0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h3 : 0 < δ ^ 3 := by positivity
  have h2 : 0 < δ ^ 2 := by positivity
  have h2δ : δ ^ 2 ≤ δ := by nlinarith
  have h3δ : δ ^ 3 ≤ δ ^ 2 := by nlinarith
  have h38 : δ ^ 3 ≤ r / 8 := by linarith
  set e : ℝ := A0 * δ ^ 2 / c2 with he
  have he0 : 0 ≤ e := by positivity
  have he3 : δ ^ 3 ≤ e := by
    rw [he, le_div_iff₀ hc2]
    have : δ ^ 3 * c2 ≤ δ ^ 2 * A0 := by
      have := mul_le_mul_of_nonneg_left (le_div_iff₀ hc2 |>.1 hδA) h2.le
      nlinarith
    nlinarith
  have her : e ≤ r := by
    rw [he, div_le_iff₀ hc2]
    have h5 : δ * A0 ≤ r * c2 := by rw [le_div_iff₀ hA0] at hδr; exact hδr
    nlinarith
  obtain ⟨J, m, N, hJm, hmN, hJ1, hJ2, hm1, hm2, hqN1, hqN⟩ :=
    dal_idx (q₀ := q₀) (c0 := c0) (e := e) hδ h38 he3
  have qmono : ∀ k k' : ℤ, k ≤ k' → q₀ + (k : ℝ) * δ ^ 3 ≤ q₀ + (k' : ℝ) * δ ^ 3 := by
    intro k k' hk
    have : (k : ℝ) ≤ k' := by exact_mod_cast hk
    nlinarith
  have hc0w : c0 ∈ Icc (c0 - r) (c0 + r) := ⟨by linarith, by linarith⟩
  have hwin : ∀ k ∈ Finset.Icc J (N + 1), q₀ + (k : ℝ) * δ ^ 3 ∈ Icc (c0 - r) (c0 + r) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have a1 := qmono J k hk.1
    have a2 := qmono k (N + 1) hk.2
    push_cast at a2
    constructor <;> linarith
  have hqJc : q₀ + (J : ℝ) * δ ^ 3 ≤ c0 := by linarith
  -- ζ bounds against the turn
  have zlow : ∀ x ∈ Icc (c0 - r) (c0 + r), c0 ≤ x → c1 * (x - c0) ≤ ζ x ∧ ζ x ≤ c2 * (x - c0) := by
    intro x hx hcx
    have := dal_zeta_bounds hd hc0w hx hcx
    rw [hz0] at this; simpa using this
  have zneg : ∀ x ∈ Icc (c0 - r) (c0 + r), x ≤ c0 → -(c2 * (c0 - x)) ≤ ζ x := by
    intro x hx hxc
    have := (dal_zeta_bounds hd hx hc0w hxc).2
    rw [hz0] at this; nlinarith
  have hXdef : ∀ x : ℝ, (δ ^ 3) ^ (-(2 / 3 : ℝ)) * ζ x = ζ x / δ ^ 2 := by
    intro x; rw [dal_rpow_cube hδ]; ring
  simp only [hXdef]
  have he' : e = A0 / c2 * δ ^ 2 := by rw [he]; ring
  have hce : c2 * e = A0 * δ ^ 2 := by rw [he]; field_simp
  have hX0 : ∀ x ∈ Icc (c0 - r) (c0 + r), c0 ≤ x → 0 ≤ ζ x := fun x hx hcx => by
    have := (zlow x hx hcx).1
    have := mul_nonneg hc1.le (sub_nonneg.2 hcx)
    linarith
  refine ⟨J, m, N, hJm, hmN, hwin, hJ1, hqJc, hm1, hm2, hqN1, hqN, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have a1 := qmono J k hk.1
    have a2 := qmono k m hk.2
    have hb : A0 / c2 * δ ^ 2 + δ ^ 3 ≤ (A0 / c2 + 1) * δ ^ 2 := by
      have : (A0 / c2 + 1) * δ ^ 2 = A0 / c2 * δ ^ 2 + δ ^ 2 := by ring
      linarith
    have hpos : 0 ≤ A0 / c2 * δ ^ 2 := by positivity
    rw [abs_le]; constructor <;> linarith
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have a1 := qmono m k hk.1
    have hkw := hwin k (by rw [Finset.mem_Icc]; omega)
    exact div_nonneg (hX0 _ hkw (by linarith)) h2.le
  · have hmw := hwin m (by rw [Finset.mem_Icc]; omega)
    have := (zlow _ hmw hm1).2
    have h6 : c2 * (q₀ + (m : ℝ) * δ ^ 3 - c0) ≤ c2 * δ ^ 3 :=
      mul_le_mul_of_nonneg_left (by linarith) hc2.le
    rw [div_le_iff₀ h2]
    have : c2 * δ ^ 3 = c2 * δ * δ ^ 2 := by ring
    linarith
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have a1 := qmono J k hk.1
    have hkw := hwin k (by rw [Finset.mem_Icc]; omega)
    have : -(A0 * δ ^ 2) ≤ ζ (q₀ + (k : ℝ) * δ ^ 3) := by
      by_cases hk0 : q₀ + (k : ℝ) * δ ^ 3 ≤ c0
      · have := zneg _ hkw hk0
        have h6 : c2 * (c0 - (q₀ + (k : ℝ) * δ ^ 3)) ≤ c2 * e :=
          mul_le_mul_of_nonneg_left (by linarith) hc2.le
        linarith
      · have := hX0 _ hkw (by linarith)
        have := mul_pos hA0 h2
        linarith
    rw [le_div_iff₀ h2]; linarith
  · have hmw := hwin m (by rw [Finset.mem_Icc]; omega)
    have hJw := hwin J (by rw [Finset.mem_Icc]; omega)
    have h1 := (zlow _ hmw hm1).2
    have h2' : -(c2 * (c0 - (q₀ + (J : ℝ) * δ ^ 3))) ≤ ζ (q₀ + (J : ℝ) * δ ^ 3) := zneg _ hJw hqJc
    have h6 : c2 * (c0 - (q₀ + (J : ℝ) * δ ^ 3)) ≤ c2 * e :=
      mul_le_mul_of_nonneg_left (by linarith) hc2.le
    have h7 : c2 * (q₀ + (m : ℝ) * δ ^ 3 - c0) ≤ c2 * δ ^ 3 :=
      mul_le_mul_of_nonneg_left (by linarith) hc2.le
    have h8 : c2 * δ ^ 3 ≤ c2 * δ ^ 2 := mul_le_mul_of_nonneg_left h3δ hc2.le
    rw [← sub_div, div_le_iff₀ h2]
    have : (A0 + c2) * δ ^ 2 = A0 * δ ^ 2 + c2 * δ ^ 2 := by ring
    linarith
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have a1 := qmono m k hk.1
    have a2 := qmono k (N + 1) hk.2
    push_cast at a2
    have hkw := hwin k (by rw [Finset.mem_Icc]; omega)
    have h1 := (zlow _ hkw (by linarith)).2
    have h6 : c2 * (q₀ + (k : ℝ) * δ ^ 3 - c0) ≤ c2 * (r / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hc2.le
    exact div_le_div_of_nonneg_right (h1.trans h6) h2.le
  · have hNw := hwin N (by rw [Finset.mem_Icc]; omega)
    have a1 := qmono m N hmN
    have h1 := (zlow _ hNw (by linarith)).1
    have h6 : c1 * (r / 4) ≤ c1 * (q₀ + (N : ℝ) * δ ^ 3 - c0) :=
      mul_le_mul_of_nonneg_left (by linarith) hc1.le
    exact div_le_div_of_nonneg_right (h6.trans h1) h2.le
  · intro k hk
    rw [Finset.mem_Icc] at hk
    have hkw := hwin k (by rw [Finset.mem_Icc]; omega)
    have hk1w := hwin (k + 1) (by rw [Finset.mem_Icc]; omega)
    have hle : q₀ + (k : ℝ) * δ ^ 3 ≤ q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3 := qmono k (k + 1) (by omega)
    have := dal_zeta_bounds hd hkw hk1w hle
    have hdiff : q₀ + ((k + 1 : ℤ) : ℝ) * δ ^ 3 - (q₀ + (k : ℝ) * δ ^ 3) = δ ^ 3 := by push_cast; ring
    rw [hdiff] at this
    rw [← sub_div]
    have e3 : δ ^ 3 = δ * δ ^ 2 := by ring
    constructor
    · rw [le_div_iff₀ h2]; have := this.1; rw [e3] at this; linarith
    · rw [div_le_iff₀ h2]; have := this.2; rw [e3] at this; linarith

/-- info: 'FormalResearch.Special.dal_lattice_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.dal_lattice_window

end FormalResearch.Special

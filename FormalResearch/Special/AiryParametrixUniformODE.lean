module

public import FormalResearch.Special.AiryParametrixUniformCh
public import FormalResearch.Special.AiryShift

/-!
# Uniform parametrix defect, part 2: the shift functions at fixed `ζ` (Grönwall in `h`)

In the scaled variables `h = t³`, `ζ = t² X`, `Δ = t s` the exact shift functions of the Airy shift identity
(`AiryShift`, `C(X,Δ)`, `S(X,Δ)` solving `Y'' = (X+Δ) Y`) become the paper's `C(s; ζ, h)`, `S(s; ζ, h)`
(`A:1068-1104`):
`Cs(s) = C(ζ/t², t s)`, `Ss(s) = S(ζ/t², t s)/t` solve `Y_ss = (ζ + h s) Y` with data `(1, 0)`, `(0, 1)`.
Everything is polynomial in `(ζ, h s)`: no `|X|` enters, so the expansion in `h` at *fixed* `ζ` is uniform in
`X = ζ/t²` however large.

* `apu_gron`: Grönwall for `R'' = q R + f`, `R(0) = R'(0) = 0` on `|x| ≤ S`
  (`|R| ≤ φ (S+1) e^{(2+L)S}` for `|q| ≤ L`, `|f| ≤ φ`; energy `R² + R'²`);
* `apu_C_remainder`: `|Cs - (E + h O)| ≤ K h²` and `apu_S_remainder`: `|Ss - (A + h B)| ≤ K h²`,
  uniformly for `|ζ| ≤ Z₀`, `|s| ≤ S`, `0 < t ≤ 1` (the closed forms `E, O, A, B` of
  `AiryParametrixUniformCh` satisfy `E'' = ζE`, `O'' = ζO + sE`, `A'' = ζA`, `B'' = ζB + sA`, so
  the remainder solves `R'' = (ζ + hs) R + h² s O` (resp. `h² s B`)).

Proved; the constants are explicit up to those of `apu_bounds`.
-/

@[expose] public section

open Set

namespace FormalResearch.Special

/-! ### One-sided energy Grönwall -/

lemma apu_gron_pos {V V1 : ℝ → ℝ} {c φ2 S : ℝ} (hV : ∀ x, HasDerivAt V (V1 x) x)
    (hb : ∀ x ∈ Icc 0 S, V1 x ≤ c * V x + φ2) (hc : 0 ≤ c) (hφ : 0 ≤ φ2) (hV0 : V 0 = 0) :
    ∀ x ∈ Icc 0 S, V x ≤ φ2 * x * Real.exp (c * x) := by
  set W : ℝ → ℝ := fun x => V x * Real.exp (-(c * x)) - φ2 * x with hW
  have hWd : ∀ x, HasDerivAt W (V1 x * Real.exp (-(c * x)) + V x * (Real.exp (-(c * x)) * (-c)) - φ2) x := by
    intro x
    have hE : HasDerivAt (fun x => Real.exp (-(c * x))) (Real.exp (-(c * x)) * (-c)) x := by
      simpa using (((hasDerivAt_id x).const_mul c).neg.exp)
    have := (hV x).mul hE
    have h2 := (hasDerivAt_id x).const_mul φ2
    have := this.sub h2
    refine this.congr_deriv ?_
    simp
  intro x hx
  have hanti : AntitoneOn W (Icc 0 S) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 S)
    · exact fun y _ => (hWd y).continuousAt.continuousWithinAt
    · exact fun y _ => (hWd y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hWd y).deriv]
      have hE := Real.exp_pos (-(c * y))
      have hE1 : Real.exp (-(c * y)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hy.1]
      have := hb y ⟨hy.1.le, hy.2.le⟩
      nlinarith [mul_nonneg hE.le (sub_nonneg.2 this), mul_le_mul_of_nonneg_left hE1 hφ]
  have h1 : W x ≤ W 0 := hanti ⟨le_refl _, (hx.1).trans hx.2⟩ hx hx.1
  simp only [hW, hV0, zero_mul, mul_zero, neg_zero, Real.exp_zero, sub_zero] at h1
  have h2 : V x * Real.exp (-(c * x)) ≤ φ2 * x := by linarith
  have h3 : V x ≤ φ2 * x * Real.exp (c * x) := by
    have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (c * x)).le
    calc V x = V x * Real.exp (-(c * x)) * Real.exp (c * x) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := this
  exact h3

/-- **Two-sided energy Grönwall.**  `R' = R1`, `R1' = q R + f` with `R(0) = R1(0) = 0`, `|q| ≤ L`,
`|f| ≤ φ` on `|x| ≤ S`: then `|R| ≤ φ (S+1) e^{(2+L)S}` there. -/
lemma apu_gron {R R1 q f : ℝ → ℝ} {L φ S : ℝ} (hR : ∀ x, HasDerivAt R (R1 x) x)
    (hR1 : ∀ x, HasDerivAt R1 (q x * R x + f x) x) (hq : ∀ x, |x| ≤ S → |q x| ≤ L)
    (hf : ∀ x, |x| ≤ S → |f x| ≤ φ) (hR0 : R 0 = 0) (hR10 : R1 0 = 0) (hL : 0 ≤ L)
    (hS : 0 ≤ S) :
    ∀ x, |x| ≤ S → |R x| ≤ φ * (S + 1) * Real.exp ((2 + L) * S) := by
  have hφ : 0 ≤ φ := by
    have := (abs_nonneg (f 0)).trans (hf 0 (by simpa using hS))
    exact this
  set V : ℝ → ℝ := fun x => R x ^ 2 + R1 x ^ 2 with hV
  set V1 : ℝ → ℝ := fun x => 2 * R x * R1 x + 2 * R1 x * (q x * R x + f x) with hV1
  have hVd : ∀ x, HasDerivAt V (V1 x) x := by
    intro x
    have := ((hR x).pow 2).add ((hR1 x).pow 2)
    refine this.congr_deriv ?_
    simp only [hV1]; push_cast; ring
  have hV0 : V 0 = 0 := by simp [hV, hR0, hR10]
  -- the differential inequality `|V1| ≤ (2+L) V + φ²` on `|x| ≤ S`
  have hbd : ∀ x, |x| ≤ S → |V1 x| ≤ (2 + L) * V x + φ ^ 2 := by
    intro x hx
    have hqx := hq x hx
    have hfx := hf x hx
    have a1 : 2 * |R x| * |R1 x| ≤ R x ^ 2 + R1 x ^ 2 := by
      nlinarith [sq_nonneg (|R x| - |R1 x|), sq_abs (R x), sq_abs (R1 x)]
    have a2 : 2 * |R1 x| * |f x| ≤ R1 x ^ 2 + φ ^ 2 := by
      have : |f x| ≤ φ := hfx
      nlinarith [sq_nonneg (|R1 x| - φ), sq_abs (R1 x), mul_nonneg (abs_nonneg (R1 x)) (sub_nonneg.2 this)]
    have a3 : 2 * |q x| * |R x| * |R1 x| ≤ L * (R x ^ 2 + R1 x ^ 2) := by
      have := mul_le_mul_of_nonneg_right hqx (by positivity : 0 ≤ 2 * |R x| * |R1 x|)
      nlinarith [this, mul_le_mul_of_nonneg_left a1 hL]
    have e : V1 x = 2 * R x * R1 x + 2 * q x * R x * R1 x + 2 * R1 x * f x := by simp only [hV1]; ring
    rw [e]
    calc |2 * R x * R1 x + 2 * q x * R x * R1 x + 2 * R1 x * f x|
        ≤ |2 * R x * R1 x| + |2 * q x * R x * R1 x| + |2 * R1 x * f x| := abs_add_three _ _ _
      _ = 2 * |R x| * |R1 x| + 2 * |q x| * |R x| * |R1 x| + 2 * |R1 x| * |f x| := by
          simp only [abs_mul, abs_two]
      _ ≤ (2 + L) * V x + φ ^ 2 := by simp only [hV]; nlinarith [a1, a2, a3, sq_nonneg (R1 x)]
  have hc : 0 ≤ 2 + L := by linarith
  have hφ2 : 0 ≤ φ ^ 2 := sq_nonneg φ
  -- forward and backward bounds
  have hfwd : ∀ x ∈ Icc 0 S, V x ≤ φ ^ 2 * x * Real.exp ((2 + L) * x) :=
    apu_gron_pos hVd (fun x hx => (abs_le.1 (hbd x (by rw [abs_of_nonneg hx.1]; exact hx.2))).2) hc hφ2 hV0
  have hbwd : ∀ x ∈ Icc 0 S, V (-x) ≤ φ ^ 2 * x * Real.exp ((2 + L) * x) := by
    have hd : ∀ x, HasDerivAt (fun x => V (-x)) (-V1 (-x)) x := by
      intro x
      have := (hVd (-x)).comp x (hasDerivAt_neg x)
      refine this.congr_deriv ?_
      ring
    refine apu_gron_pos (V := fun x => V (-x)) (V1 := fun x => -V1 (-x)) hd ?_ hc hφ2 (by simpa using hV0)
    intro x hx
    have := hbd (-x) (by rw [abs_neg, abs_of_nonneg hx.1]; exact hx.2)
    have := (abs_le.1 this).1
    linarith
  intro x hx
  have hVx : V x ≤ φ ^ 2 * S * Real.exp ((2 + L) * S) := by
    rcases le_total 0 x with h0 | h0
    · have := hfwd x ⟨h0, by rwa [abs_of_nonneg h0] at hx⟩
      refine this.trans ?_
      have hxS : x ≤ S := by rwa [abs_of_nonneg h0] at hx
      gcongr
    · have hx' : 0 ≤ -x := by linarith
      have := hbwd (-x) ⟨hx', by rw [abs_of_nonpos h0] at hx; exact hx⟩
      simp only [neg_neg] at this
      refine this.trans ?_
      have hxS : -x ≤ S := by rw [abs_of_nonpos h0] at hx; exact hx
      gcongr
  have hR2 : R x ^ 2 ≤ V x := by simp only [hV]; nlinarith [sq_nonneg (R1 x)]
  have hbig : φ ^ 2 * S * Real.exp ((2 + L) * S) ≤ (φ * (S + 1) * Real.exp ((2 + L) * S)) ^ 2 := by
    have e1 : Real.exp ((2 + L) * S) ≤ Real.exp ((2 + L) * S) ^ 2 := by
      have : 1 ≤ Real.exp ((2 + L) * S) := Real.one_le_exp (by positivity)
      nlinarith
    have e2 : S ≤ (S + 1) ^ 2 := by nlinarith
    rw [mul_pow, mul_pow]
    have := mul_le_mul e2 e1 (Real.exp_pos _).le (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hφ2]
  exact abs_le_of_sq_le_sq (hR2.trans (hVx.trans hbig)) (by positivity)

/-! ### The scaled shift functions -/

/-- `C(s; ζ, h)` with `h = t³`: `C(ζ/t², t s)`. -/
noncomputable def apuCs (z t s : ℝ) : ℝ := airyShiftC (z / t ^ 2) (t * s)
/-- `∂_s C(s; ζ, h) = t C_Δ`. -/
noncomputable def apuCs1 (z t s : ℝ) : ℝ := t * airyShiftCd (z / t ^ 2) (t * s)
/-- `S(s; ζ, h) = S(ζ/t², t s)/t`. -/
noncomputable def apuSs (z t s : ℝ) : ℝ := airyShiftS (z / t ^ 2) (t * s) / t
/-- `∂_s S(s; ζ, h) = S_Δ`. -/
noncomputable def apuSs1 (z t s : ℝ) : ℝ := airyShiftSd (z / t ^ 2) (t * s)

lemma apu_hasDerivAt_Cs (z t s : ℝ) : HasDerivAt (apuCs z t) (apuCs1 z t s) s := by
  have := (hasDerivAt_airyShiftC (z / t ^ 2) (t * s)).comp s ((hasDerivAt_id s).const_mul t)
  unfold apuCs apuCs1
  refine this.congr_deriv ?_
  simp; ring

lemma apu_hasDerivAt_Cs1 {t : ℝ} (ht : t ≠ 0) (z s : ℝ) :
    HasDerivAt (apuCs1 z t) ((z + t ^ 3 * s) * apuCs z t s) s := by
  have := ((hasDerivAt_airyShiftCd (z / t ^ 2) (t * s)).comp s ((hasDerivAt_id s).const_mul t)).const_mul t
  unfold apuCs1 apuCs
  refine this.congr_deriv ?_
  field_simp

lemma apu_hasDerivAt_Ss {t : ℝ} (ht : t ≠ 0) (z s : ℝ) : HasDerivAt (apuSs z t) (apuSs1 z t s) s := by
  have := ((hasDerivAt_airyShiftS (z / t ^ 2) (t * s)).comp s ((hasDerivAt_id s).const_mul t)).div_const t
  unfold apuSs apuSs1
  refine this.congr_deriv ?_
  field_simp

lemma apu_hasDerivAt_Ss1 {t : ℝ} (ht : t ≠ 0) (z s : ℝ) :
    HasDerivAt (apuSs1 z t) ((z + t ^ 3 * s) * apuSs z t s) s := by
  have := (hasDerivAt_airyShiftSd (z / t ^ 2) (t * s)).comp s ((hasDerivAt_id s).const_mul t)
  unfold apuSs1 apuSs
  refine this.congr_deriv ?_
  field_simp

lemma apuCs_zero (z t : ℝ) : apuCs z t 0 = 1 := by
  simp [apuCs, (airyShift_initial _).1]
lemma apuCs1_zero (z t : ℝ) : apuCs1 z t 0 = 0 := by
  simp [apuCs1, (airyShift_initial _).2.1]
lemma apuSs_zero (z t : ℝ) : apuSs z t 0 = 0 := by
  simp [apuSs, (airyShift_initial _).2.2.1]
lemma apuSs1_zero {t : ℝ} (z : ℝ) : apuSs1 z t 0 = 1 := by
  simp [apuSs1, (airyShift_initial _).2.2.2]

lemma apuE1_eq (z s : ℝ) : apuE1 z s = z * apuA z s := by unfold apuE1 apuA; ring

/-! ### The remainders -/

/-- **`C` at fixed `ζ`**: `|C(s;ζ,h) - (E + h O)| ≤ K h²` uniformly for `|ζ| ≤ Z₀`, `|s| ≤ S`, `0 < t ≤ 1`,
`h = t³`. -/
theorem apu_C_remainder (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z t s : ℝ, |z| ≤ Z0 → |s| ≤ S → 0 < t → t ≤ 1 →
      |apuCs z t s - (apuE z s + t ^ 3 * apuO z s)| ≤ K * (t ^ 3) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := apu_bounds Z0 S hZ0 hS
  refine ⟨S * M * (S + 1) * Real.exp ((2 + (Z0 + S)) * S), by positivity, ?_⟩
  intro z t s hz hs ht0 ht1
  have ht : t ≠ 0 := ht0.ne'
  have hh0 : 0 < t ^ 3 := by positivity
  have hh1 : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
  set R : ℝ → ℝ := fun x => apuCs z t x - (apuE z x + t ^ 3 * apuO z x) with hRdef
  set R1 : ℝ → ℝ := fun x => apuCs1 z t x - (apuE1 z x + t ^ 3 * apuO1 z x) with hR1def
  have hRd : ∀ x, HasDerivAt R (R1 x) x := fun x =>
    (apu_hasDerivAt_Cs z t x).sub ((apu_hasDerivAt_E z x).add ((apu_hasDerivAt_O z x).const_mul _))
  have hR1d : ∀ x, HasDerivAt R1 ((z + t ^ 3 * x) * R x + (t ^ 3) ^ 2 * (x * apuO z x)) x := by
    intro x
    have := (apu_hasDerivAt_Cs1 ht z x).sub
      ((apu_hasDerivAt_E1 z x).add ((apu_hasDerivAt_O1 z x).const_mul (t ^ 3)))
    refine this.congr_deriv ?_
    simp only [hRdef]; ring
  have hq : ∀ x, |x| ≤ S → |z + t ^ 3 * x| ≤ Z0 + S := by
    intro x hx
    calc |z + t ^ 3 * x| ≤ |z| + |t ^ 3 * x| := abs_add_le _ _
      _ ≤ Z0 + S := by
          rw [abs_mul, abs_of_pos hh0]
          have : t ^ 3 * |x| ≤ 1 * S := mul_le_mul hh1 hx (abs_nonneg _) zero_le_one
          linarith
  have hf : ∀ x, |x| ≤ S → |(t ^ 3) ^ 2 * (x * apuO z x)| ≤ (t ^ 3) ^ 2 * (S * M) := by
    intro x hx
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (t ^ 3) ^ 2)]
    gcongr
    exact (hM z x hz hx).2.2.1
  have := apu_gron hRd hR1d hq hf (by simp [hRdef, apuCs_zero, apuE_zero, apuO_zero])
    (by simp [hR1def, apuCs1_zero, apuE1_zero, apuO1_zero]) (by positivity) hS s hs
  simp only [hRdef] at this
  refine this.trans (le_of_eq ?_)
  ring

/-- **`S` at fixed `ζ`**: `|S(s;ζ,h) - (A + h B)| ≤ K h²`. -/
theorem apu_S_remainder (Z0 S : ℝ) (hZ0 : 0 ≤ Z0) (hS : 0 ≤ S) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z t s : ℝ, |z| ≤ Z0 → |s| ≤ S → 0 < t → t ≤ 1 →
      |apuSs z t s - (apuA z s + t ^ 3 * apuB z s)| ≤ K * (t ^ 3) ^ 2 := by
  obtain ⟨M, hM0, hM⟩ := apu_bounds Z0 S hZ0 hS
  refine ⟨S * M * (S + 1) * Real.exp ((2 + (Z0 + S)) * S), by positivity, ?_⟩
  intro z t s hz hs ht0 ht1
  have ht : t ≠ 0 := ht0.ne'
  have hh0 : 0 < t ^ 3 := by positivity
  have hh1 : t ^ 3 ≤ 1 := pow_le_one₀ ht0.le ht1
  set R : ℝ → ℝ := fun x => apuSs z t x - (apuA z x + t ^ 3 * apuB z x) with hRdef
  set R1 : ℝ → ℝ := fun x => apuSs1 z t x - (apuE z x + t ^ 3 * apuB1 z x) with hR1def
  have hRd : ∀ x, HasDerivAt R (R1 x) x := fun x =>
    (apu_hasDerivAt_Ss ht z x).sub ((apu_hasDerivAt_A z x).add ((apu_hasDerivAt_B z x).const_mul _))
  have hR1d : ∀ x, HasDerivAt R1 ((z + t ^ 3 * x) * R x + (t ^ 3) ^ 2 * (x * apuB z x)) x := by
    intro x
    have := (apu_hasDerivAt_Ss1 ht z x).sub
      ((apu_hasDerivAt_E z x).add ((apu_hasDerivAt_B1 z x).const_mul (t ^ 3)))
    refine this.congr_deriv ?_
    simp only [hRdef, apuE1_eq]; ring
  have hq : ∀ x, |x| ≤ S → |z + t ^ 3 * x| ≤ Z0 + S := by
    intro x hx
    calc |z + t ^ 3 * x| ≤ |z| + |t ^ 3 * x| := abs_add_le _ _
      _ ≤ Z0 + S := by
          rw [abs_mul, abs_of_pos hh0]
          have : t ^ 3 * |x| ≤ 1 * S := mul_le_mul hh1 hx (abs_nonneg _) zero_le_one
          linarith
  have hf : ∀ x, |x| ≤ S → |(t ^ 3) ^ 2 * (x * apuB z x)| ≤ (t ^ 3) ^ 2 * (S * M) := by
    intro x hx
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (t ^ 3) ^ 2)]
    gcongr
    exact (hM z x hz hx).2.2.2.2.2.1
  have := apu_gron hRd hR1d hq hf (by simp [hRdef, apuSs_zero, apuA_zero, apuB_zero])
    (by simp [hR1def, apuSs1_zero, apuE_zero, apuB1_zero]) (by positivity) hS s hs
  simp only [hRdef] at this
  refine this.trans (le_of_eq ?_)
  ring

/-- info: 'FormalResearch.Special.apu_gron' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_gron

/-- info: 'FormalResearch.Special.apu_C_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_C_remainder

/-- info: 'FormalResearch.Special.apu_S_remainder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Special.apu_S_remainder

end FormalResearch.Special

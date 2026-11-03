module

public import Mathlib

/-!
# Null-critical states: the scalar inequalities (`eq:fqe-null-critical-sharp`)

Elementary real inequalities of the proof of the null-critical refinement in
`critical_orbit_stability.tex`, for two unit vectors `r, s ∈ ℝ³` (the Bloch vectors of the auxiliary
qubits).  With `c = √3`, `B = 1 + 1/√3`, `f₀ = B²/4 = (2+√3)/6`:

* `cubic_l1`: `x + y + z ≥ 1 + (9 - 3√3) x y z` for a nonnegative unit triple;
* `fg_ge`: `(1 + L/√3)(1 + (L - 2m)/√3) ≥ B²` for `m` the smallest of a nonnegative unit triple;
* `null_exists_pair` : there is a cube pair `(ε, η)` of opposite parity with
  `F(ε,η) = (1 + ε·r/√3)(1 + η·s/√3)/4 ≥ f₀` and `3/(4-√3) (1 - F) ≤ 1/2 + (27/2) r₁r₂r₃ s₁s₂s₃`.
-/

@[expose] public section


set_option linter.unusedSimpArgs false

namespace FormalResearch.FourQubitEntropy.CO

/-- `±1` from a Boolean. -/
def sg (b : Bool) : ℝ := if b then 1 else -1

theorem sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

/-- Parity of the pair: an odd number of the six signs differ. -/
def Parity (b b' : Fin 3 → Bool) : Bool :=
  xor (xor (xor (b 0) (b' 0)) (xor (b 1) (b' 1))) (xor (b 2) (b' 2))

/-- `Σ_j ε_j r_j` for `ε = sg ∘ b`. -/
def dotS (b : Fin 3 → Bool) (r : Fin 3 → ℝ) : ℝ := sg (b 0) * r 0 + sg (b 1) * r 1 + sg (b 2) * r 2

/-- The overlap `(1 + ε·r/√3)(1 + η·s/√3)/4`. -/
noncomputable def Fpair (b b' : Fin 3 → Bool) (r s : Fin 3 → ℝ) : ℝ :=
  (1 + dotS b r / Real.sqrt 3) * (1 + dotS b' s / Real.sqrt 3) / 4

theorem par_false (b b' : Fin 3 → Bool) (h : Parity b b' = false) :
    sg (b 0) * sg (b 1) * sg (b 2) * (sg (b' 0) * sg (b' 1) * sg (b' 2)) = 1 := by
  unfold Parity at h
  revert h
  generalize b 0 = x0
  generalize b 1 = x1
  generalize b 2 = x2
  generalize b' 0 = y0
  generalize b' 1 = y1
  generalize b' 2 = y2
  cases x0 <;> cases x1 <;> cases x2 <;> cases y0 <;> cases y1 <;> cases y2 <;> simp [sg]

/-- Flipping one sign. -/
def flipB (b : Fin 3 → Bool) (j : Fin 3) : Fin 3 → Bool := Function.update b j (!b j)

theorem parity_flip (b b' : Fin 3 → Bool) (j : Fin 3) :
    Parity (flipB b j) b' = !(Parity b b') := by
  unfold Parity flipB
  fin_cases j <;> simp [Function.update]

theorem dotS_flip (b : Fin 3 → Bool) (j : Fin 3) (r : Fin 3 → ℝ) :
    dotS (flipB b j) r = dotS b r - 2 * (sg (b j) * r j) := by
  unfold dotS flipB
  fin_cases j <;> simp [Function.update] <;> (cases b 0 <;> cases b 1 <;> cases b 2 <;> simp [sg] <;> ring)

theorem amgm3 {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) :
    27 * (a * b * d) ≤ (a + b + d) ^ 3 := by
  nlinarith [mul_nonneg ha (sq_nonneg (b - d)), mul_nonneg hb (sq_nonneg (d - a)),
    mul_nonneg hd (sq_nonneg (a - b)),
    mul_nonneg (add_nonneg (add_nonneg ha hb) hd)
      (add_nonneg (add_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - d))) (sq_nonneg (d - a)))]

theorem e2_facts {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    x * y + y * z + z * x ≤ 1 ∧ 27 * (x * y * z) ^ 2 ≤ (x * y + y * z + z * x) ^ 2 ∧
      27 * (x * y * z) ^ 2 ≤ 1 := by
  have e1 : x * y + y * z + z * x ≤ 1 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]
  have e0 : 0 ≤ x * y + y * z + z * x := by positivity
  have am := amgm3 (mul_nonneg hx hy) (mul_nonneg hy hz) (mul_nonneg hz hx)
  have : (x * y) * (y * z) * (z * x) = (x * y * z) ^ 2 := by ring
  rw [this] at am
  have e3 : (x * y + y * z + z * x) ^ 3 ≤ (x * y + y * z + z * x) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg (x * y + y * z + z * x)) (sub_nonneg.2 e1)]
  refine ⟨e1, by nlinarith, by nlinarith⟩

theorem sqrt3_facts : Real.sqrt 3 * Real.sqrt 3 = 3 ∧ 0 < Real.sqrt 3 ∧ Real.sqrt 3 < 2 := by
  refine ⟨Real.mul_self_sqrt (by norm_num), Real.sqrt_pos.mpr (by norm_num), ?_⟩
  have h : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 3]

/-- **`x + y + z ≥ 1 + (9 - 3√3) x y z`** for a nonnegative unit triple. -/
theorem cubic_l1 {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    1 + (9 - 3 * Real.sqrt 3) * (x * y * z) ≤ x + y + z := by
  obtain ⟨e1, e2, -⟩ := e2_facts hx hy hz h
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  set c := Real.sqrt 3 with hc'
  have hp : 0 ≤ x * y * z := by positivity
  have hL0 : 0 ≤ x + y + z := by positivity
  have hL2 : (x + y + z) ^ 2 = 1 + 2 * (x * y + y * z + z * x) := by nlinarith
  have hLc : x + y + z ≤ c := by nlinarith
  have he2 : 3 * c * (x * y * z) ≤ x * y + y * z + z * x := by
    by_contra hcon
    rw [not_le] at hcon
    have h0 : 0 ≤ x * y + y * z + z * x := by positivity
    have : (x * y + y * z + z * x) ^ 2 < (3 * c * (x * y * z)) ^ 2 := by
      apply pow_lt_pow_left₀ hcon h0 (by norm_num)
    nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have hK : 0 < 9 - 3 * c := by linarith
  have h1 : (x + y + z - 1) * (x + y + z + 1) = 2 * (x * y + y * z + z * x) := by nlinarith
  have h2 : (9 - 3 * c) * (x + y + z + 1) * (x * y * z) ≤ 6 * c * (x * y * z) := by
    have : (9 - 3 * c) * (x + y + z + 1) ≤ 6 * c := by nlinarith
    exact mul_le_mul_of_nonneg_right this hp
  have h3 : (x + y + z - 1) * (x + y + z + 1) < (9 - 3 * c) * (x * y * z) * (x + y + z + 1) := by
    apply mul_lt_mul_of_pos_right (by linarith) (by linarith)
  nlinarith

/-- `3√3 |xyz| ≤ 1` for a unit triple. -/
theorem null_prod_le {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    3 * Real.sqrt 3 * (x * y * z) ≤ 1 := by
  obtain ⟨-, -, e3⟩ := e2_facts hx hy hz h
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  by_contra hcon
  rw [not_le] at hcon
  have hp : 0 ≤ x * y * z := by positivity
  have : 1 < (3 * Real.sqrt 3 * (x * y * z)) ^ 2 := by nlinarith
  nlinarith

/-- `(1 + L/√3)(1 + (L - 2m)/√3) ≥ B²` for `m` the smallest of a nonnegative unit triple. -/
theorem fg_ge {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hzx : z ≤ x) (hzy : z ≤ y)
    (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    (1 + Real.sqrt 3 / 3) ^ 2 ≤
      (1 + (x + y + z) * Real.sqrt 3 / 3) * (1 + (x + y - z) * Real.sqrt 3 / 3) := by
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  set c := Real.sqrt 3
  have hxy : z * z ≤ x * y := mul_le_mul hzx hzy hz hx
  have hs : 1 ≤ x + y := by nlinarith
  nlinarith [mul_nonneg hc0.le (sub_nonneg.2 hs), hc]

theorem parity_flip' (b b' : Fin 3 → Bool) (j : Fin 3) :
    Parity b (flipB b' j) = !(Parity b b') := by
  unfold Parity flipB
  fin_cases j <;> simp [Function.update]

theorem div_s3 (t : ℝ) : t / Real.sqrt 3 = t * Real.sqrt 3 / 3 := by
  obtain ⟨hc, hc0, -⟩ := sqrt3_facts
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

theorem sg_decide_mul (x : ℝ) : sg (decide (0 ≤ x)) * x = |x| := by
  by_cases h : 0 ≤ x
  · simp [sg, h, abs_of_nonneg h]
  · have : x < 0 := lt_of_not_ge h
    simp [sg, h, abs_of_neg this]

theorem dotS_align (r : Fin 3 → ℝ) :
    dotS (fun j => decide (0 ≤ r j)) r = |r 0| + |r 1| + |r 2| := by
  simp only [dotS, sg_decide_mul]

theorem L_ge {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x ^ 2 + y ^ 2 + z ^ 2 = 1) :
    1 ≤ x + y + z := by
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx]

theorem abs_unit (r : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1) :
    |r 0| ^ 2 + |r 1| ^ 2 + |r 2| ^ 2 = 1 := by
  simpa only [sq_abs] using hr

theorem fg_vec (r : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1) (j0 : Fin 3)
    (hmin : ∀ j, |r j0| ≤ |r j|) :
    (1 + Real.sqrt 3 / 3) ^ 2 ≤ (1 + (|r 0| + |r 1| + |r 2|) * Real.sqrt 3 / 3) *
      (1 + ((|r 0| + |r 1| + |r 2|) - 2 * |r j0|) * Real.sqrt 3 / 3) := by
  have hu := abs_unit r hr
  have a0 := abs_nonneg (r 0)
  have a1 := abs_nonneg (r 1)
  have a2 := abs_nonneg (r 2)
  fin_cases j0
  · have := fg_ge a1 a2 a0 (hmin 1) (hmin 2) (by linarith)
    have e : (1 + (|r 0| + |r 1| + |r 2|) * Real.sqrt 3 / 3) *
      (1 + ((|r 0| + |r 1| + |r 2|) - 2 * |r 0|) * Real.sqrt 3 / 3) =
      (1 + (|r 1| + |r 2| + |r 0|) * Real.sqrt 3 / 3) * (1 + (|r 1| + |r 2| - |r 0|) * Real.sqrt 3 / 3) := by ring
    simp only [Fin.zero_eta, Fin.isValue]
    rw [e]; exact this
  · have := fg_ge a0 a2 a1 (hmin 0) (hmin 2) (by linarith)
    have e : (1 + (|r 0| + |r 1| + |r 2|) * Real.sqrt 3 / 3) *
      (1 + ((|r 0| + |r 1| + |r 2|) - 2 * |r 1|) * Real.sqrt 3 / 3) =
      (1 + (|r 0| + |r 2| + |r 1|) * Real.sqrt 3 / 3) * (1 + (|r 0| + |r 2| - |r 1|) * Real.sqrt 3 / 3) := by ring
    simp only [Fin.mk_one, Fin.isValue]
    rw [e]; exact this
  · have := fg_ge a0 a1 a2 (hmin 0) (hmin 1) (by linarith)
    have e : (1 + (|r 0| + |r 1| + |r 2|) * Real.sqrt 3 / 3) *
      (1 + ((|r 0| + |r 1| + |r 2|) - 2 * |r 2|) * Real.sqrt 3 / 3) =
      (1 + (|r 0| + |r 1| + |r 2|) * Real.sqrt 3 / 3) * (1 + (|r 0| + |r 1| - |r 2|) * Real.sqrt 3 / 3) := by ring
    simp only [Fin.reduceFinMk, Fin.isValue]
    rw [e]; exact this

/-- The two-variable algebra of the case `Q < 1/2`: `4F ≥ (B + A u)(B + A v) ≥ B² + (4 - B²) u v`. -/
theorem final_alg {c u v : ℝ} (hc : c * c = 3) (hc0 : 0 < c) (hc2 : c < 2) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (1 + c / 3) ^ 2 / 4 ≤ ((1 + c / 3) + (1 - c / 3) * u) * ((1 + c / 3) + (1 - c / 3) * v) / 4 ∧
    3 / (4 - c) * (1 - ((1 + c / 3) + (1 - c / 3) * u) * ((1 + c / 3) + (1 - c / 3) * v) / 4)
      ≤ (1 - u * v) / 2 := by
  have e1 : c * c * u = 3 * u := by rw [hc]
  have e2 : c * c * v = 3 * v := by rw [hc]
  have e3 : c * c * (u * v) = 3 * (u * v) := by rw [hc]
  have p1 := mul_nonneg hu0 (sub_nonneg.2 hv1)
  have p2 := mul_nonneg hv0 (sub_nonneg.2 hu1)
  have p3 := mul_nonneg hu0 hv0
  have hA : 0 ≤ 1 - c / 3 := by linarith
  constructor
  · nlinarith [mul_nonneg hA hu0, mul_nonneg hA hv0, mul_nonneg (mul_nonneg hA hA) p3, mul_nonneg hc0.le hu0,
      mul_nonneg hc0.le hv0, mul_nonneg (mul_nonneg hc0.le hc0.le) p3, mul_nonneg hc0.le p3]
  · rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [e1, e2, e3, hc, p1, p2, p3, mul_nonneg hc0.le p1, mul_nonneg hc0.le p2]

theorem Fpair_eq (b b' : Fin 3 → Bool) (r s : Fin 3 → ℝ) :
    Fpair b b' r s = (1 + dotS b r * Real.sqrt 3 / 3) * (1 + dotS b' s * Real.sqrt 3 / 3) / 4 := by
  unfold Fpair; rw [div_s3, div_s3]

/-- **A cube pair of opposite parity with `F ≥ f₀ = B²/4`**: aligned signs, or the sign at the smallest
coordinate flipped. -/
theorem null_key1 (r s : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1) :
    ∃ b b' : Fin 3 → Bool, Parity b b' = true ∧ (1 + Real.sqrt 3 / 3) ^ 2 / 4 ≤ Fpair b b' r s := by
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  set c := Real.sqrt 3 with hcdef
  set ba : Fin 3 → Bool := fun j => decide (0 ≤ r j) with hba
  set bb : Fin 3 → Bool := fun j => decide (0 ≤ s j) with hbb
  have hLr := L_ge (abs_nonneg (r 0)) (abs_nonneg (r 1)) (abs_nonneg (r 2)) (abs_unit r hr)
  have hLs := L_ge (abs_nonneg (s 0)) (abs_nonneg (s 1)) (abs_nonneg (s 2)) (abs_unit s hs)
  have hdr : dotS ba r = |r 0| + |r 1| + |r 2| := dotS_align r
  have hds : dotS bb s = |s 0| + |s 1| + |s 2| := dotS_align s
  by_cases hpar : Parity ba bb = true
  · refine ⟨ba, bb, hpar, ?_⟩
    rw [Fpair_eq, hdr, hds]
    have h1 : 0 ≤ (|r 0| + |r 1| + |r 2| - 1) * c := mul_nonneg (by linarith) hc0.le
    have h2 : 0 ≤ (|s 0| + |s 1| + |s 2| - 1) * c := mul_nonneg (by linarith) hc0.le
    nlinarith [mul_nonneg h1 h2, mul_nonneg h1 hc0.le, mul_nonneg h2 hc0.le]
  · have hpf : Parity ba bb = false := by simpa using hpar
    obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ (fun j => |r j|) Finset.univ_nonempty
    obtain ⟨j1, -, hj1⟩ := Finset.exists_min_image Finset.univ (fun j => |s j|) Finset.univ_nonempty
    have m0 : ∀ j, |r j0| ≤ |r j| := fun j => hj0 j (Finset.mem_univ j)
    have m1 : ∀ j, |s j1| ≤ |s j| := fun j => hj1 j (Finset.mem_univ j)
    have h0 := fg_vec r hr j0 m0
    have h1 := fg_vec s hs j1 m1
    set fr := 1 + (|r 0| + |r 1| + |r 2|) * c / 3 with hfr
    set fs := 1 + (|s 0| + |s 1| + |s 2|) * c / 3 with hfs
    set gr := 1 + ((|r 0| + |r 1| + |r 2|) - 2 * |r j0|) * c / 3 with hgr
    set gs := 1 + ((|s 0| + |s 1| + |s 2|) - 2 * |s j1|) * c / 3 with hgs
    have hgr0 : 0 < gr := by
      have := m0 0; have := m0 1; have := m0 2
      have : 0 ≤ ((|r 0| + |r 1| + |r 2|) - 2 * |r j0|) * c :=
        mul_nonneg (by linarith [abs_nonneg (r j0)]) hc0.le
      rw [hgr]; linarith
    have hgs0 : 0 < gs := by
      have := m1 0; have := m1 1; have := m1 2
      have : 0 ≤ ((|s 0| + |s 1| + |s 2|) - 2 * |s j1|) * c :=
        mul_nonneg (by linarith [abs_nonneg (s j1)]) hc0.le
      rw [hgs]; linarith
    have hfr0 : 0 < fr := by
      have : 0 ≤ (|r 0| + |r 1| + |r 2|) * c := mul_nonneg (by positivity) hc0.le
      rw [hfr]; linarith
    have hfs0 : 0 < fs := by
      have : 0 ≤ (|s 0| + |s 1| + |s 2|) * c := mul_nonneg (by positivity) hc0.le
      rw [hfs]; linarith
    have hB : 0 < (1 + c / 3) ^ 2 := by positivity
    by_cases hX : (1 + c / 3) ^ 2 ≤ gr * fs
    · refine ⟨flipB ba j0, bb, by rw [parity_flip, hpf]; rfl, ?_⟩
      rw [Fpair_eq, dotS_flip, hdr, hds, sg_decide_mul]
      show (1 + c / 3) ^ 2 / 4 ≤ gr * fs / 4
      linarith
    · have hX' : gr * fs < (1 + c / 3) ^ 2 := lt_of_not_ge hX
      refine ⟨ba, flipB bb j1, by rw [parity_flip', hpf]; rfl, ?_⟩
      rw [Fpair_eq, dotS_flip, hdr, hds, sg_decide_mul]
      show (1 + c / 3) ^ 2 / 4 ≤ fr * gs / 4
      by_contra hcon
      have hY : fr * gs < (1 + c / 3) ^ 2 := by linarith
      have hprod : (1 + c / 3) ^ 2 * (1 + c / 3) ^ 2 ≤ (gr * fs) * (fr * gs) := by
        calc (1 + c / 3) ^ 2 * (1 + c / 3) ^ 2 ≤ (fr * gr) * (fs * gs) :=
              mul_le_mul h0 h1 hB.le (by positivity)
          _ = (gr * fs) * (fr * gs) := by ring
      have := mul_lt_mul'' hX' hY (by positivity) (by positivity)
      linarith

theorem f0_eq : (1 + Real.sqrt 3 / 3) ^ 2 / 4 = (2 + Real.sqrt 3) / 6 := by
  obtain ⟨hc, -, -⟩ := sqrt3_facts
  nlinarith

theorem r_eq_sg (x : ℝ) : x = sg (decide (0 ≤ x)) * |x| := by
  have h := sg_decide_mul x
  have h2 := sg_sq (decide (0 ≤ x))
  calc x = (sg (decide (0 ≤ x)) * sg (decide (0 ≤ x))) * x := by rw [h2]; ring
    _ = sg (decide (0 ≤ x)) * (sg (decide (0 ≤ x)) * x) := by ring
    _ = _ := by rw [h]

set_option maxHeartbeats 1000000 in
/-- **The scalar core of the null-critical refinement.**  For unit `r, s ∈ ℝ³` there is a cube pair of
opposite parity with `F ≥ (2+√3)/6` and `3/(4-√3) (1 - F) ≤ 1/2 + (27/2) r₁r₂r₃ s₁s₂s₃`. -/
theorem null_exists_pair (r s : Fin 3 → ℝ) (hr : r 0 ^ 2 + r 1 ^ 2 + r 2 ^ 2 = 1)
    (hs : s 0 ^ 2 + s 1 ^ 2 + s 2 ^ 2 = 1) :
    ∃ b b' : Fin 3 → Bool, Parity b b' = true ∧ (2 + Real.sqrt 3) / 6 ≤ Fpair b b' r s ∧
      3 / (4 - Real.sqrt 3) * (1 - Fpair b b' r s) ≤
        1 / 2 + 27 / 2 * (r 0 * r 1 * r 2) * (s 0 * s 1 * s 2) := by
  obtain ⟨hc, hc0, hc2⟩ := sqrt3_facts
  set c := Real.sqrt 3 with hcdef
  by_cases hP : r 0 * r 1 * r 2 * (s 0 * s 1 * s 2) < 0
  · -- case `Q < 1/2`: align all signs
    set ba : Fin 3 → Bool := fun j => decide (0 ≤ r j) with hba
    set bb : Fin 3 → Bool := fun j => decide (0 ≤ s j) with hbb
    have hpar : Parity ba bb = true := by
      by_contra hcon
      have hpf : Parity ba bb = false := by simpa using hcon
      have h1 := par_false ba bb hpf
      have e : r 0 * r 1 * r 2 * (s 0 * s 1 * s 2) =
          (sg (ba 0) * sg (ba 1) * sg (ba 2) * (sg (bb 0) * sg (bb 1) * sg (bb 2))) *
            (|r 0| * |r 1| * |r 2| * (|s 0| * |s 1| * |s 2|)) := by
        have := r_eq_sg (r 0); have := r_eq_sg (r 1); have := r_eq_sg (r 2)
        have := r_eq_sg (s 0); have := r_eq_sg (s 1); have := r_eq_sg (s 2)
        calc r 0 * r 1 * r 2 * (s 0 * s 1 * s 2)
            = (sg (ba 0) * |r 0|) * (sg (ba 1) * |r 1|) * (sg (ba 2) * |r 2|) *
              ((sg (bb 0) * |s 0|) * (sg (bb 1) * |s 1|) * (sg (bb 2) * |s 2|)) := by
              rw [← r_eq_sg (r 0), ← r_eq_sg (r 1), ← r_eq_sg (r 2), ← r_eq_sg (s 0), ← r_eq_sg (s 1),
                ← r_eq_sg (s 2)]
          _ = _ := by ring
      rw [e, h1, one_mul] at hP
      have : 0 ≤ |r 0| * |r 1| * |r 2| * (|s 0| * |s 1| * |s 2|) := by positivity
      linarith
    have hPe : r 0 * r 1 * r 2 * (s 0 * s 1 * s 2) = -(|r 0| * |r 1| * |r 2| * (|s 0| * |s 1| * |s 2|)) := by
      have h := abs_of_neg hP
      have h2 : |r 0 * r 1 * r 2 * (s 0 * s 1 * s 2)| =
          |r 0| * |r 1| * |r 2| * (|s 0| * |s 1| * |s 2|) := by simp only [abs_mul]
      linarith
    have hLr : 1 + (9 - 3 * c) * (|r 0| * |r 1| * |r 2|) ≤ |r 0| + |r 1| + |r 2| :=
      cubic_l1 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_unit r hr)
    have hLs : 1 + (9 - 3 * c) * (|s 0| * |s 1| * |s 2|) ≤ |s 0| + |s 1| + |s 2| :=
      cubic_l1 (abs_nonneg _) (abs_nonneg _) (abs_nonneg _) (abs_unit s hs)
    have hu1 := null_prod_le (abs_nonneg (r 0)) (abs_nonneg (r 1)) (abs_nonneg (r 2)) (abs_unit r hr)
    have hv1 := null_prod_le (abs_nonneg (s 0)) (abs_nonneg (s 1)) (abs_nonneg (s 2)) (abs_unit s hs)
    set u : ℝ := 3 * c * (|r 0| * |r 1| * |r 2|) with hu
    set v : ℝ := 3 * c * (|s 0| * |s 1| * |s 2|) with hv
    have hu0 : 0 ≤ u := by positivity
    have hv0 : 0 ≤ v := by positivity
    obtain ⟨hA1, hA2⟩ := final_alg hc hc0 hc2 hu0 hu1 hv0 hv1
    have hUr : 1 + (c - 1) * u ≤ |r 0| + |r 1| + |r 2| := by
      have : (9 - 3 * c) * (|r 0| * |r 1| * |r 2|) = (c - 1) * u := by
        rw [hu]; linear_combination (-3 * (|r 0| * |r 1| * |r 2|)) * hc
      linarith
    have hUs : 1 + (c - 1) * v ≤ |s 0| + |s 1| + |s 2| := by
      have : (9 - 3 * c) * (|s 0| * |s 1| * |s 2|) = (c - 1) * v := by
        rw [hv]; linear_combination (-3 * (|s 0| * |s 1| * |s 2|)) * hc
      linarith
    have hFge : ((1 + c / 3) + (1 - c / 3) * u) * ((1 + c / 3) + (1 - c / 3) * v) / 4 ≤ Fpair ba bb r s := by
      rw [Fpair_eq, dotS_align, dotS_align]
      have k1 : (1 + c / 3) + (1 - c / 3) * u = 1 + (1 + (c - 1) * u) * c / 3 := by
        linear_combination (-u / 3) * hc
      have k2 : (1 + c / 3) + (1 - c / 3) * v = 1 + (1 + (c - 1) * v) * c / 3 := by
        linear_combination (-v / 3) * hc
      have hA : 0 ≤ (1 + c / 3) + (1 - c / 3) * u := by
        have : 0 ≤ (1 - c / 3) * u := mul_nonneg (by linarith) hu0
        linarith
      have l1 : 1 + (1 + (c - 1) * u) * c / 3 ≤ 1 + (|r 0| + |r 1| + |r 2|) * c / 3 := by
        have := mul_le_mul_of_nonneg_right hUr hc0.le
        linarith
      have l2 : 1 + (1 + (c - 1) * v) * c / 3 ≤ 1 + (|s 0| + |s 1| + |s 2|) * c / 3 := by
        have := mul_le_mul_of_nonneg_right hUs hc0.le
        linarith
      rw [k1, k2]
      rw [k1] at hA
      have hB : 0 ≤ 1 + (1 + (c - 1) * v) * c / 3 := by
        rw [← k2]; have : 0 ≤ (1 - c / 3) * v := mul_nonneg (by linarith) hv0
        linarith
      have := mul_le_mul l1 l2 hB (le_trans hA l1)
      linarith
    refine ⟨ba, bb, hpar, ?_, ?_⟩
    · rw [← f0_eq]; linarith
    · have hQ : 1 / 2 + 27 / 2 * (r 0 * r 1 * r 2) * (s 0 * s 1 * s 2) = (1 - u * v) / 2 := by
        have e : 27 / 2 * (r 0 * r 1 * r 2) * (s 0 * s 1 * s 2) =
            27 / 2 * (r 0 * r 1 * r 2 * (s 0 * s 1 * s 2)) := by ring
        rw [e, hPe, hu, hv]
        linear_combination (9 / 2 * (|r 0| * |r 1| * |r 2| * (|s 0| * |s 1| * |s 2|))) * hc
      rw [hQ]
      have hpos : 0 < 3 / (4 - c) := by apply div_pos (by norm_num) (by linarith)
      have := mul_le_mul_of_nonneg_left (by linarith : 1 - Fpair ba bb r s ≤
        1 - ((1 + c / 3) + (1 - c / 3) * u) * ((1 + c / 3) + (1 - c / 3) * v) / 4) hpos.le
      linarith
  · -- case `Q ≥ 1/2`
    rw [not_lt] at hP
    obtain ⟨b, b', hpar, hF⟩ := null_key1 r s hr hs
    refine ⟨b, b', hpar, by rw [← f0_eq]; exact hF, ?_⟩
    rw [f0_eq] at hF
    have h4 : 0 < 4 - c := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ h4]
    have : 1 / 2 ≤ 1 / 2 + 27 / 2 * (r 0 * r 1 * r 2) * (s 0 * s 1 * s 2) := by
      have e : 27 / 2 * (r 0 * r 1 * r 2) * (s 0 * s 1 * s 2) =
          27 / 2 * (r 0 * r 1 * r 2 * (s 0 * s 1 * s 2)) := by ring
      rw [e]; linarith
    nlinarith

end FormalResearch.FourQubitEntropy.CO

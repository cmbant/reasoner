module

public import FormalResearch.Racah.P2RacahLattice

/-!
# The physical `c`- and `f`-lattices of the Racah system (Weyl P2, `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, section *Exact finite Racah spectral system on
the physical `c`-lattice*, equations `eq:cminRacah`-`eq:Racahdimension`.

The paper's integrality conventions are packaged in `RacahLabels a b m n`: `2a`, `2b`, `2m` are
integers and `m - n` is an integer (so `a, b` are integers or half-integers, `m, n` are integers or
half-integers of the same class).

## Results

* `physC a b m n = {c | (c,a,b) and (c,b+m,a+n) triangles}` and
  `physF a b m n = {f | (f,b+m,b) and (f,a,a+n) triangles}`.
* `mem_physC_iff`: `c` is physical iff `c = c_min + i` with `i ∈ ℕ`, `i ≤ c_max - c_min`
  (`eq:cminRacah`, `eq:cmaxRacah`: the physical `c`-lattice is exactly `{c_min, ..., c_max}`).
* `mem_physF_iff`: likewise for `f_0 = max(|m|,|n|)` and `f_1 = min(2a+n, 2b+m)` (`eq:frangeRacah`).
* `physC_eq_image`, `physF_eq_image`, `ncard_physC_eq_ncard_physF` (with `cMax_sub_cMin`,
  `eq:Racahdimension`): the physical `f`-range has the same cardinality as the physical `c`-lattice;
  `ncard_physC` gives the value `c_max - c_min + 1` (or `0` if `c_max < c_min`).
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

open FormalResearch.Wigner

/-- The paper's integrality conventions: `2a`, `2b`, `2m` and `m - n` are integers. -/
structure RacahLabels (a b m n : ℚ) : Prop where
  two_a : ∃ p : ℤ, 2 * a = p
  two_b : ∃ q : ℤ, 2 * b = q
  two_m : ∃ r : ℤ, 2 * m = r
  m_sub_n : ∃ s : ℤ, m - n = s

/-- The physical `c`-lattice: the `c` for which `(c,a,b)` and `(c,b+m,a+n)` are triangles. -/
def physC (a b m n : ℚ) : Set ℚ := {c | IsTri c a b ∧ IsTri c (b + m) (a + n)}

/-- The physical `f`-range: the `f` for which `(f,b+m,b)` and `(f,a,a+n)` are triangles. -/
def physF (a b m n : ℚ) : Set ℚ := {f | IsTri f (b + m) b ∧ IsTri f a (a + n)}

lemma isNat_iff_int {t : ℚ} {T : ℤ} (h : 2 * t = T) : IsNat t ↔ 0 ≤ T ∧ 2 ∣ T := by
  constructor
  · rintro ⟨k, rfl⟩
    have : T = 2 * (k : ℤ) := by
      have h' : ((T : ℤ) : ℚ) = ((2 * (k : ℤ) : ℤ) : ℚ) := by push_cast; linarith
      exact_mod_cast h'
    exact ⟨by omega, ⟨k, this⟩⟩
  · rintro ⟨h0, k, rfl⟩
    refine ⟨k.toNat, ?_⟩
    have : ((k.toNat : ℤ) : ℚ) = (k : ℚ) := by exact_mod_cast Int.toNat_of_nonneg (by omega)
    push_cast at h this ⊢
    linarith

lemma isTri_iff_int {x y z : ℚ} {X Y Z : ℤ} (hx : 2 * x = X) (hy : 2 * y = Y) (hz : 2 * z = Z) :
    IsTri x y z ↔ (0 ≤ X + Y - Z ∧ 2 ∣ X + Y - Z) ∧ (0 ≤ X - Y + Z ∧ 2 ∣ X - Y + Z) ∧
      (0 ≤ -X + Y + Z ∧ 2 ∣ -X + Y + Z) := by
  unfold IsTri
  rw [isNat_iff_int (T := X + Y - Z) (by push_cast; linarith),
    isNat_iff_int (T := X - Y + Z) (by push_cast; linarith),
    isNat_iff_int (T := -X + Y + Z) (by push_cast; linarith)]

/-- Integer form of the `c`-lattice condition (`2c = κ`). -/
lemma physC_int (p q r s κ : ℤ) :
    (((0 ≤ κ + p - q ∧ 2 ∣ κ + p - q) ∧ (0 ≤ κ - p + q ∧ 2 ∣ κ - p + q) ∧
        (0 ≤ -κ + p + q ∧ 2 ∣ -κ + p + q)) ∧
      ((0 ≤ κ + (q + r) - (p + r - 2 * s) ∧ 2 ∣ κ + (q + r) - (p + r - 2 * s)) ∧
        (0 ≤ κ - (q + r) + (p + r - 2 * s) ∧ 2 ∣ κ - (q + r) + (p + r - 2 * s)) ∧
        (0 ≤ -κ + (q + r) + (p + r - 2 * s) ∧ 2 ∣ -κ + (q + r) + (p + r - 2 * s)))) ↔
    ∃ i : ℕ, 2 * (i : ℤ) ≤ min (p + q) (p + q + 2 * r - 2 * s) - max |p - q| |q - p + 2 * s| ∧
      κ = max |p - q| |q - p + 2 * s| + 2 * i := by
  simp only [abs_eq_max_neg]
  constructor
  · intro h
    refine ⟨((κ - max (max (p - q) (-(p - q))) (max (q - p + 2 * s) (-(q - p + 2 * s)))) / 2).toNat,
      ?_, ?_⟩ <;> omega
  · rintro ⟨i, h1, h2⟩
    omega

/-- Integer form of the `f`-range condition (`2f = φ`). -/
lemma physF_int (p q r s φ : ℤ) :
    (((0 ≤ φ + (q + r) - q ∧ 2 ∣ φ + (q + r) - q) ∧ (0 ≤ φ - (q + r) + q ∧ 2 ∣ φ - (q + r) + q) ∧
        (0 ≤ -φ + (q + r) + q ∧ 2 ∣ -φ + (q + r) + q)) ∧
      ((0 ≤ φ + p - (p + r - 2 * s) ∧ 2 ∣ φ + p - (p + r - 2 * s)) ∧
        (0 ≤ φ - p + (p + r - 2 * s) ∧ 2 ∣ φ - p + (p + r - 2 * s)) ∧
        (0 ≤ -φ + p + (p + r - 2 * s) ∧ 2 ∣ -φ + p + (p + r - 2 * s)))) ↔
    ∃ i : ℕ, 2 * (i : ℤ) ≤ min (2 * p + r - 2 * s) (2 * q + r) - max |r| |r - 2 * s| ∧
      φ = max |r| |r - 2 * s| + 2 * i := by
  simp only [abs_eq_max_neg]
  constructor
  · intro h
    refine ⟨((φ - max (max r (-r)) (max (r - 2 * s) (-(r - 2 * s)))) / 2).toNat, ?_, ?_⟩ <;> omega
  · rintro ⟨i, h1, h2⟩
    omega

lemma two_mul_abs (x : ℚ) : 2 * |x| = |2 * x| := by
  rw [abs_mul]; norm_num

lemma two_mul_max (x y : ℚ) : 2 * max x y = max (2 * x) (2 * y) :=
  mul_max_of_nonneg _ _ (by norm_num)

lemma two_mul_min (x y : ℚ) : 2 * min x y = min (2 * x) (2 * y) :=
  mul_min_of_nonneg _ _ (by norm_num)

/-- `2 c_min` as an integer. -/
lemma two_cMin {a b m n : ℚ} {p q s : ℤ} (hp : 2 * a = p) (hq : 2 * b = q)
    (hs : m - n = s) :
    2 * cMin a b m n = (((max |p - q| |q - p + 2 * s| : ℤ)) : ℚ) := by
  unfold cMin
  rw [two_mul_max, two_mul_abs, two_mul_abs]
  push_cast
  rw [show 2 * (a - b) = (p : ℚ) - q by linarith,
    show 2 * (b + m - a - n) = (q : ℚ) - p + 2 * s by linarith]

lemma two_cMax {a b m n : ℚ} {p q r s : ℤ} (hp : 2 * a = p) (hq : 2 * b = q) (hr : 2 * m = r)
    (hs : m - n = s) :
    2 * cMax a b m n = (((min (p + q) (p + q + 2 * r - 2 * s) : ℤ)) : ℚ) := by
  unfold cMax
  rw [two_mul_min]
  push_cast
  rw [show 2 * (a + b) = (p : ℚ) + q by linarith,
    show 2 * (a + b + m + n) = (p : ℚ) + q + 2 * r - 2 * s by linarith]

lemma two_fMin {m n : ℚ} {r s : ℤ} (hr : 2 * m = r)
    (hs : m - n = s) :
    2 * fMin m n = (((max |r| |r - 2 * s| : ℤ)) : ℚ) := by
  unfold fMin
  rw [two_mul_max, two_mul_abs, two_mul_abs]
  push_cast
  rw [show 2 * m = (r : ℚ) by linarith, show 2 * n = (r : ℚ) - 2 * s by linarith]

lemma two_fMax {a b m n : ℚ} {p q r s : ℤ} (hp : 2 * a = p) (hq : 2 * b = q) (hr : 2 * m = r)
    (hs : m - n = s) :
    2 * fMax a b m n = (((min (2 * p + r - 2 * s) (2 * q + r) : ℤ)) : ℚ) := by
  unfold fMax
  rw [two_mul_min]
  push_cast
  rw [show 2 * (2 * a + n) = 2 * (p : ℚ) + r - 2 * s by linarith,
    show 2 * (2 * b + m) = 2 * (q : ℚ) + r by linarith]

/-- **`eq:cminRacah`, `eq:cmaxRacah`**: the physical `c`-lattice is exactly
`{c_min, c_min+1, ..., c_max}` (with `c_min = max{|a-b|, |b+m-a-n|}` and
`c_max = min{a+b, a+b+m+n}`; empty exactly when `c_max < c_min`). -/
theorem mem_physC_iff {a b m n : ℚ} (h : RacahLabels a b m n) (c : ℚ) :
    c ∈ physC a b m n ↔
      ∃ i : ℕ, (i : ℚ) ≤ cMax a b m n - cMin a b m n ∧ c = cMin a b m n + i := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩ := h
  have hn : 2 * n = (r : ℚ) - 2 * s := by linarith
  have e1 := two_cMin hp hq hs
  have e2 := two_cMax hp hq hr hs
  have key := physC_int p q r s
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨N, hN⟩ := h1.1
    obtain ⟨κ, hκ⟩ : ∃ κ : ℤ, 2 * c = κ := ⟨2 * N - p + q, by push_cast; linarith⟩
    have hb : 2 * (b + m) = ((q + r : ℤ) : ℚ) := by push_cast; linarith
    have ha : 2 * (a + n) = ((p + r - 2 * s : ℤ) : ℚ) := by push_cast; linarith
    have t1 := (isTri_iff_int hκ hp hq).1 h1
    have t2 := (isTri_iff_int hκ hb ha).1 h2
    obtain ⟨i, hi1, hi2⟩ := (key κ).1 ⟨t1, t2⟩
    refine ⟨i, ?_, ?_⟩
    · have : 2 * (i : ℚ) ≤ 2 * (cMax a b m n - cMin a b m n) := by
        rw [mul_sub, e1, e2]; exact_mod_cast hi1
      linarith
    · have : 2 * c = 2 * (cMin a b m n + i) := by
        rw [mul_add, e1, hκ, hi2, Int.cast_add, Int.cast_mul, Int.cast_natCast]; norm_num
      linarith
  · rintro ⟨i, hi, rfl⟩
    have hi' : 2 * (i : ℤ) ≤ min (p + q) (p + q + 2 * r - 2 * s) - max |p - q| |q - p + 2 * s| := by
      have : 2 * (i : ℚ) ≤ 2 * (cMax a b m n - cMin a b m n) := by linarith
      rw [mul_sub, e1, e2] at this
      exact_mod_cast this
    have hκ : 2 * (cMin a b m n + i) = (((max |p - q| |q - p + 2 * s| + 2 * i : ℤ)) : ℚ) := by
      rw [mul_add, e1, Int.cast_add, Int.cast_mul, Int.cast_natCast]; norm_num
    have hb : 2 * (b + m) = ((q + r : ℤ) : ℚ) := by push_cast; linarith
    have ha : 2 * (a + n) = ((p + r - 2 * s : ℤ) : ℚ) := by push_cast; linarith
    obtain ⟨k1, k2⟩ := (key _).2 ⟨i, hi', rfl⟩
    exact ⟨(isTri_iff_int hκ hp hq).2 k1, (isTri_iff_int hκ hb ha).2 k2⟩

/-- **`eq:frangeRacah`**: the physical `f`-range is exactly `{f_0, f_0+1, ..., f_1}`, with
`f_0 = max(|m|,|n|)` and `f_1 = min(2a+n, 2b+m)`. -/
theorem mem_physF_iff {a b m n : ℚ} (h : RacahLabels a b m n) (f : ℚ) :
    f ∈ physF a b m n ↔
      ∃ i : ℕ, (i : ℚ) ≤ fMax a b m n - fMin m n ∧ f = fMin m n + i := by
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩ := h
  have hn : 2 * n = (r : ℚ) - 2 * s := by linarith
  have e1 := two_fMin hr hs
  have e2 := two_fMax hp hq hr hs
  have key := physF_int p q r s
  have hb : 2 * (b + m) = ((q + r : ℤ) : ℚ) := by push_cast; linarith
  have ha : 2 * (a + n) = ((p + r - 2 * s : ℤ) : ℚ) := by push_cast; linarith
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨N, hN⟩ := h1.1
    obtain ⟨φ, hφ⟩ : ∃ φ : ℤ, 2 * f = φ := ⟨2 * N - r, by push_cast; linarith⟩
    have t1 := (isTri_iff_int hφ hb hq).1 h1
    have t2 := (isTri_iff_int hφ hp ha).1 h2
    obtain ⟨i, hi1, hi2⟩ := (key φ).1 ⟨t1, t2⟩
    refine ⟨i, ?_, ?_⟩
    · have : 2 * (i : ℚ) ≤ 2 * (fMax a b m n - fMin m n) := by
        rw [mul_sub, e1, e2]; exact_mod_cast hi1
      linarith
    · have : 2 * f = 2 * (fMin m n + i) := by
        rw [mul_add, e1, hφ, hi2, Int.cast_add, Int.cast_mul, Int.cast_natCast]; norm_num
      linarith
  · rintro ⟨i, hi, rfl⟩
    have hi' : 2 * (i : ℤ) ≤ min (2 * p + r - 2 * s) (2 * q + r) - max |r| |r - 2 * s| := by
      have : 2 * (i : ℚ) ≤ 2 * (fMax a b m n - fMin m n) := by linarith
      rw [mul_sub, e1, e2] at this
      exact_mod_cast this
    have hφ : 2 * (fMin m n + i) = (((max |r| |r - 2 * s| + 2 * i : ℤ)) : ℚ) := by
      rw [mul_add, e1, Int.cast_add, Int.cast_mul, Int.cast_natCast]; norm_num
    obtain ⟨k1, k2⟩ := (key _).2 ⟨i, hi', rfl⟩
    exact ⟨(isTri_iff_int hφ hb hq).2 k1, (isTri_iff_int hφ hp ha).2 k2⟩

/-- The physical `c`-lattice as the image of `{i ∈ ℕ : i ≤ c_max - c_min}` under `i ↦ c_min + i`. -/
theorem physC_eq_image {a b m n : ℚ} (h : RacahLabels a b m n) :
    physC a b m n =
      (fun i : ℕ => cMin a b m n + i) '' {i : ℕ | (i : ℚ) ≤ cMax a b m n - cMin a b m n} := by
  ext c
  rw [mem_physC_iff h]
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- The physical `f`-range as the image of `{i ∈ ℕ : i ≤ f_1 - f_0}` under `i ↦ f_0 + i`. -/
theorem physF_eq_image {a b m n : ℚ} (h : RacahLabels a b m n) :
    physF a b m n =
      (fun i : ℕ => fMin m n + i) '' {i : ℕ | (i : ℚ) ≤ fMax a b m n - fMin m n} := by
  ext f
  rw [mem_physF_iff h]
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

lemma ncard_natLE (d : ℚ) :
    {i : ℕ | (i : ℚ) ≤ d}.ncard = if 0 ≤ d then ⌊d⌋₊ + 1 else 0 := by
  split_ifs with hd
  · have : {i : ℕ | (i : ℚ) ≤ d} = ↑(Finset.range (⌊d⌋₊ + 1)) := by
      ext i
      simp only [Set.mem_ofPred_eq, Finset.coe_range, Set.mem_Iio]
      rw [Nat.lt_succ_iff, Nat.le_floor_iff hd]
    rw [this, Set.ncard_coe_finset, Finset.card_range]
  · have : {i : ℕ | (i : ℚ) ≤ d} = ∅ := by
      ext i
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have : (0 : ℚ) ≤ i := by positivity
      linarith
    rw [this, Set.ncard_empty]

/-- The number of physical `c` is `c_max - c_min + 1` (`0` if the lattice is empty). -/
theorem ncard_physC {a b m n : ℚ} (h : RacahLabels a b m n) :
    (physC a b m n).ncard =
      if 0 ≤ cMax a b m n - cMin a b m n then ⌊cMax a b m n - cMin a b m n⌋₊ + 1 else 0 := by
  rw [physC_eq_image h, Set.ncard_image_of_injective _ (fun i j hij => by
    simpa using hij), ncard_natLE]

/-- **`eq:Racahdimension`** (cardinality form): the physical `f`-range and the physical
`c`-lattice have the same finite cardinality. -/
theorem ncard_physC_eq_ncard_physF {a b m n : ℚ} (h : RacahLabels a b m n) :
    (physC a b m n).ncard = (physF a b m n).ncard := by
  rw [physC_eq_image h, physF_eq_image h, Set.ncard_image_of_injective _ (fun i j hij => by
    simpa using hij), Set.ncard_image_of_injective _ (fun i j hij => by simpa using hij),
    cMax_sub_cMin]

/-- info: 'FormalResearch.Racah.SixJ.mem_physC_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_physC_iff

/-- info: 'FormalResearch.Racah.SixJ.mem_physF_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mem_physF_iff

/-- info: 'FormalResearch.Racah.SixJ.ncard_physC_eq_ncard_physF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ncard_physC_eq_ncard_physF

/-- info: 'FormalResearch.Racah.SixJ.ncard_physC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ncard_physC

end FormalResearch.Racah.SixJ

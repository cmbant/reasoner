module

public import FormalResearch.Racah.P2RacahSystemOp

/-!
# Non-emptiness of the finite Racah system (Weyl P2, `sec:6jcspectral`, `thm:6jfiniteRacah`)

Source: `Weyl/P2/paper/weyl_midpoint_recoupling.tex`, the paragraph opening `sec:6jcspectral`: "for fixed
`a, b, m, n` (with `b+m, a+n ≥ 0` and `f_1 ≥ f_0` below, so that the lattices are non-empty), the same `6j`
symbol is a finite orthogonal eigenfunction on the physical `c`-lattice", with `eq:cminRacah`,
`eq:cmaxRacah`, `eq:frangeRacah`, `eq:Racahdimension`.

Under the paper's integrality conventions (`RacahLabels`), `racah_nonempty_tfae` shows that the following
are equivalent:

1. the physical `c`-lattice `physC` is non-empty;
2. the physical `f`-range `physF` is non-empty;
3. `c_min ≤ c_max`;
4. `f_0 ≤ f_1`;
5. the paper's hypothesis `b+m ≥ 0`, `a+n ≥ 0` and `f_0 ≤ f_1`;
6. `RacahSystem a b m n D` holds for some `D`, i.e. the hypothesis of `thm_6jfiniteRacah` is satisfiable.

So the conditions `b+m ≥ 0`, `a+n ≥ 0` in the paper's parenthesis are consequences of `f_1 ≥ f_0`
(`nonneg_of_fMin_le_fMax`), and `thm_6jfiniteRacah` (hypothesis `RacahSystem a b m n D`) applies exactly under the
paper's non-emptiness hypothesis.  Finite exact statements only; all proved.
-/

@[expose] public section

namespace FormalResearch.Racah.SixJ

/-- `f_0 ≤ f_1` forces `b+m ≥ 0` and `a+n ≥ 0` (the conditions the paper lists beside `f_1 ≥ f_0`):
`2(a+n) = (2a+n) + n ≥ |n| + n ≥ 0` and `2(b+m) = (2b+m) + m ≥ |m| + m ≥ 0`. -/
theorem nonneg_of_fMin_le_fMax {a b m n : ℚ} (h : fMin m n ≤ fMax a b m n) :
    0 ≤ b + m ∧ 0 ≤ a + n := by
  unfold fMin fMax at h
  have h1 : |n| ≤ 2 * a + n := le_trans (le_trans (le_max_right _ _) h) (min_le_left _ _)
  have h2 : |m| ≤ 2 * b + m := le_trans (le_trans (le_max_left _ _) h) (min_le_right _ _)
  have h3 := neg_abs_le n
  have h4 := neg_abs_le m
  constructor <;> linarith

/-- **Non-emptiness of the finite Racah system.**  Under `RacahLabels`, the physical `c`-lattice and
`f`-range are non-empty iff `c_min ≤ c_max` iff `f_0 ≤ f_1` iff the paper's hypothesis (`b+m, a+n ≥ 0` and
`f_1 ≥ f_0`) holds iff the hypothesis `RacahSystem a b m n D` of `thm_6jfiniteRacah` is satisfiable. -/
theorem racah_nonempty_tfae {a b m n : ℚ} (h : RacahLabels a b m n) :
    List.TFAE
      [ (physC a b m n).Nonempty,
        (physF a b m n).Nonempty,
        cMin a b m n ≤ cMax a b m n,
        fMin m n ≤ fMax a b m n,
        0 ≤ b + m ∧ 0 ≤ a + n ∧ fMin m n ≤ fMax a b m n,
        ∃ D : ℕ, RacahSystem a b m n D ] := by
  have hd := cMax_sub_cMin a b m n
  have e34 : cMin a b m n ≤ cMax a b m n ↔ fMin m n ≤ fMax a b m n := by
    constructor <;> intro h' <;> linarith
  tfae_have 1 → 3 := by
    rintro ⟨c, hc⟩
    obtain ⟨i, hi, -⟩ := (mem_physC_iff h c).1 hc
    have : (0 : ℚ) ≤ i := by positivity
    linarith
  tfae_have 3 → 1 := by
    intro h3
    exact ⟨cMin a b m n, (mem_physC_iff h _).2 ⟨0, by simpa using h3, by simp⟩⟩
  tfae_have 2 → 4 := by
    rintro ⟨f, hf⟩
    obtain ⟨i, hi, -⟩ := (mem_physF_iff h f).1 hf
    have : (0 : ℚ) ≤ i := by positivity
    linarith
  tfae_have 4 → 2 := by
    intro h4
    exact ⟨fMin m n, (mem_physF_iff h _).2 ⟨0, by simpa using h4, by simp⟩⟩
  tfae_have 3 ↔ 4 := e34
  tfae_have 4 → 5 := fun h4 => ⟨(nonneg_of_fMin_le_fMax h4).1, (nonneg_of_fMin_le_fMax h4).2, h4⟩
  tfae_have 5 → 4 := fun h5 => h5.2.2
  tfae_have 3 → 6 := fun h3 => RacahSystem.exists h h3
  tfae_have 6 → 3 := by
    rintro ⟨D, hD⟩
    have h1 := hD.dim
    have : (0 : ℚ) ≤ D := by positivity
    linarith
  tfae_finish

/-- info: 'FormalResearch.Racah.SixJ.racah_nonempty_tfae' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms racah_nonempty_tfae

/-- info: 'FormalResearch.Racah.SixJ.nonneg_of_fMin_le_fMax' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonneg_of_fMin_le_fMax

/-- Negative instance: `a = b = 0`, `m = 2`, `n = 0` (integral labels) has an empty `c`-lattice
(`f_0 = 2 > f_1 = 0`). -/
theorem racah_empty_example : ¬ (physC (0 : ℚ) 0 2 0).Nonempty := by
  have h : RacahLabels (0 : ℚ) 0 2 0 :=
    ⟨⟨0, by norm_num⟩, ⟨0, by norm_num⟩, ⟨4, by norm_num⟩, ⟨2, by norm_num⟩⟩
  intro hne
  have h4 : fMin (2 : ℚ) 0 ≤ fMax 0 0 2 0 := ((racah_nonempty_tfae h).out 1 4).1 hne
  unfold fMin fMax at h4
  norm_num at h4

end FormalResearch.Racah.SixJ

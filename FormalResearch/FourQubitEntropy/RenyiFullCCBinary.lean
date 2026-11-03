module

public import FormalResearch.FourQubitEntropy.RenyiFullBQBinary
public import FormalResearch.FourQubitEntropy.RenyiFullRpow
public import FormalResearch.FourQubitEntropy.RenyiFullSliverEnt
public import FormalResearch.FourQubitEntropy.PaperECriticalRenyiGrouping

/-!
# Capped cubic lemma: the two binary quartic bounds and the binary cubic bound

Paper E, `lem:fqe-capped-cubic`, paragraph *Two binary bounds from endpoint values*:
with `h(u) = H_{q_s}(u, 1-u)` (`binH qBQ u`), `d₀ = u(1-u)`,

* `bin_quartic1`: `h(u) ≤ 4 d₀ - (11/40) d₀ (1-2u)²` for `3/100 ≤ u ≤ 1/2`,
* `bin_quartic2`: `h(u) ≤ 4 d₀ - (3/8) d₀ (1-2u)²` for `1/12 ≤ u ≤ 1/2`,

both from `A_q(u₀) ≥ a` at the endpoint (`binary_quartic_bound`, `A_q` increasing).  The endpoint values are
explicit rational power bounds (`b ≤ x^{1587/1000}` from `b^{1000} ≤ x^{1587}`) and the logarithm estimate
`-ln(1-z) ≤ z + z²/2 + z³/(3(1-z))`.  (The numerical constants differ slightly from the table of the paper: they are
chosen with more room, `S ≥ 4783/5000` and `S ≥ 8903/10000`.)
-/

@[expose] public section


namespace FormalResearch.FourQubitEntropy.RenyiFull

open Filter Topology

/-- `-ln(1-z) ≤ z + z²/2 + z³/(3(1-z))` for `0 ≤ z < 1`. -/
theorem neg_log_one_sub_le3 {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z < 1) :
    -Real.log (1 - z) ≤ z + z ^ 2 / 2 + z ^ 3 / (3 * (1 - z)) := by
  set f : ℝ → ℝ := fun z => z + z ^ 2 / 2 + z ^ 3 / (3 * (1 - z)) + Real.log (1 - z) with hf
  have hder : ∀ s : ℝ, s < 1 → HasDerivAt f (s ^ 3 / (3 * (1 - s) ^ 2)) s := by
    intro s hs
    have h1s : (1 - s) ≠ 0 := by linarith
    have a1 : HasDerivAt (fun s : ℝ => s + s ^ 2 / 2) (1 + s) s := by
      have := (hasDerivAt_id s).add ((hasDerivAt_pow 2 s).div_const 2)
      refine this.congr_deriv ?_
      simp
    have a2 : HasDerivAt (fun s : ℝ => s ^ 3 / (3 * (1 - s)))
        ((3 * s ^ 2 * (3 * (1 - s)) - s ^ 3 * (-3)) / (3 * (1 - s)) ^ 2) s := by
      have n1 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * s ^ 2) s := by
        simpa using hasDerivAt_pow 3 s
      have n2 : HasDerivAt (fun s : ℝ => 3 * (1 - s)) (-3) s := by
        have := ((hasDerivAt_id s).const_sub 1).const_mul 3
        simpa using this
      exact n1.div n2 (mul_ne_zero three_ne_zero h1s)
    have a3 : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - s)) s := by
      have := ((hasDerivAt_id s).const_sub 1).log (by simpa using h1s)
      simpa using this
    have := (a1.add a2).add a3
    convert this using 1
    field_simp
    ring
  have hmono : MonotoneOn f (Set.Ico 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1) (f' := fun s => s ^ 3 / (3 * (1 - s) ^ 2))
    · intro s hs
      exact (hder s hs.2).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      exact (hder s hs.2).hasDerivWithinAt
    · intro s hs
      rw [interior_Ico] at hs
      have : 0 < 1 - s := by linarith [hs.2]
      have : 0 < s := hs.1
      positivity
  have := hmono (⟨le_rfl, by norm_num⟩ : (0 : ℝ) ∈ Set.Ico 0 1) (⟨hz0, hz1⟩ : z ∈ Set.Ico 0 1) hz0
  simp [hf] at this
  linarith

/-- `H = -ln S/((q-1) ln 2)`. -/
theorem binH_eq_neg_log (u : ℝ) :
    binH qBQ u = -Real.log (u ^ qBQ + (1 - u) ^ qBQ) / ((qBQ - 1) * Real.log 2) := by
  rw [← renyiSpec_binary, renyiSpec_eq_neg (by unfold qBQ; norm_num)]
  simp [Fin.sum_univ_two]

theorem binH_le_of_S {u Sl cap : ℝ} (hSl0 : 0 < Sl) (hSl1 : Sl < 1)
    (hS : Sl ≤ u ^ qBQ + (1 - u) ^ qBQ)
    (hnum : (1 - Sl) + (1 - Sl) ^ 2 / 2 + (1 - Sl) ^ 3 / (3 * Sl) ≤ cap * (qBQ - 1) * (693147 / 1000000)) :
    binH qBQ u ≤ cap := by
  have hL := (log2_bounds).1
  have hr := qBQ_sub_one_pos
  rw [binH_eq_neg_log, div_le_iff₀ (mul_pos hr log_two_pos')]
  have h1 : Real.log Sl ≤ Real.log (u ^ qBQ + (1 - u) ^ qBQ) := Real.log_le_log hSl0 hS
  have h2 := neg_log_one_sub_le3 (z := 1 - Sl) (by linarith) (by linarith)
  have e : (1 - (1 - Sl)) = Sl := by ring
  rw [e] at h2
  have e2 : 1 - Sl = 1 - Sl := rfl
  have hcap : 0 ≤ cap * (qBQ - 1) := by
    by_contra hneg
    push Not at hneg
    have : cap * (qBQ - 1) * (693147 / 1000000) < 0 := mul_neg_of_neg_of_pos hneg (by norm_num)
    have : 0 ≤ (1 - Sl) + (1 - Sl) ^ 2 / 2 + (1 - Sl) ^ 3 / (3 * Sl) := by
      have : 0 ≤ 1 - Sl := by linarith
      positivity
    linarith
  have h3 : cap * (qBQ - 1) * (693147 / 1000000) ≤ cap * ((qBQ - 1) * Real.log 2) := by
    have := mul_le_mul_of_nonneg_left hL.le hcap
    linarith
  linarith

/-! ### Power bounds at the endpoints -/

theorem frac_pow_le {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : a ^ 1000 * d ^ 1587 ≤ c ^ 1587 * b ^ 1000) :
    ((a : ℝ) / b) ^ 1000 ≤ ((c : ℝ) / d) ^ 1587 := by
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  exact_mod_cast h

theorem rpow_qBQ_ge {x b : ℝ} (hb : 0 < b) (hx : 0 < x)
    (h : b ^ 1000 ≤ x ^ 1587) : b ≤ x ^ qBQ := by
  have := le_rpow_of_pow_le hb hx (m := 1587) (n := 1000) (by norm_num) h
  have e : ((1587 : ℕ) : ℝ) / ((1000 : ℕ) : ℝ) = qBQ := by unfold qBQ; push_cast; norm_num
  rwa [e] at this

theorem pow_lo_a : (1191 / 1250 : ℝ) ≤ (97 / 100 : ℝ) ^ qBQ := by
  have key : 1191 ^ 1000 * 100 ^ 1587 ≤ 97 ^ 1587 * 1250 ^ 1000 := by decide +kernel
  have h := frac_pow_le (a := 1191) (b := 1250) (c := 97) (d := 100) (by norm_num) (by norm_num) key
  refine rpow_qBQ_ge (by norm_num) (by norm_num) ?_
  simpa using h

theorem pow_lo_b : (19 / 5000 : ℝ) ≤ (3 / 100 : ℝ) ^ qBQ := by
  have key : 19 ^ 1000 * 100 ^ 1587 ≤ 3 ^ 1587 * 5000 ^ 1000 := by decide +kernel
  have h := frac_pow_le (a := 19) (b := 5000) (c := 3) (d := 100) (by norm_num) (by norm_num) key
  refine rpow_qBQ_ge (by norm_num) (by norm_num) ?_
  simpa using h

theorem pow_lo_c : (871 / 1000 : ℝ) ≤ (11 / 12 : ℝ) ^ qBQ := by
  have key : 871 ^ 1000 * 12 ^ 1587 ≤ 11 ^ 1587 * 1000 ^ 1000 := by decide +kernel
  have h := frac_pow_le (a := 871) (b := 1000) (c := 11) (d := 12) (by norm_num) (by norm_num) key
  refine rpow_qBQ_ge (by norm_num) (by norm_num) ?_
  simpa using h

theorem pow_lo_d : (193 / 10000 : ℝ) ≤ (1 / 12 : ℝ) ^ qBQ := by
  have key : 193 ^ 1000 * 12 ^ 1587 ≤ 1 ^ 1587 * 10000 ^ 1000 := by decide +kernel
  have h := frac_pow_le (a := 193) (b := 10000) (c := 1) (d := 12) (by norm_num) (by norm_num) key
  refine rpow_qBQ_ge (by norm_num) (by norm_num) ?_
  simpa using h

theorem binH_at_003 : binH qBQ (3 / 100) ≤ 1093 / 10000 := by
  have h := add_le_add pow_lo_b pow_lo_a
  refine binH_le_of_S (Sl := 4783 / 5000) (by norm_num) (by norm_num) ?_ ?_
  · have e : (1 : ℝ) - 3 / 100 = 97 / 100 := by norm_num
    rw [e]; linarith
  · unfold qBQ; norm_num

theorem binH_at_112 : binH qBQ (1 / 12) ≤ 5713 / 20000 := by
  have h := add_le_add pow_lo_d pow_lo_c
  refine binH_le_of_S (Sl := 8903 / 10000) (by norm_num) (by norm_num) ?_ ?_
  · have e : (1 : ℝ) - 1 / 12 = 11 / 12 := by norm_num
    rw [e]; linarith
  · unfold qBQ; norm_num

theorem bqA_ge_003 : 11 / 40 ≤ bqA (3 / 100) := by
  unfold bqA
  rw [le_div_iff₀ (by norm_num)]
  have := binH_at_003
  norm_num at this ⊢
  linarith

theorem bqA_ge_112 : 3 / 8 ≤ bqA (1 / 12) := by
  unfold bqA
  rw [le_div_iff₀ (by norm_num)]
  have := binH_at_112
  norm_num at this ⊢
  linarith

/-- **First binary quartic bound**: `h(u) ≤ 4u(1-u) - (11/40) u(1-u)(1-2u)²` on `[3/100, 1/2]`. -/
theorem bin_quartic1 {u : ℝ} (h1 : 3 / 100 ≤ u) (h2 : u ≤ 1 / 2) :
    binH qBQ u ≤ 4 * u * (1 - u) - 11 / 40 * (u * (1 - u) * (1 - 2 * u) ^ 2) :=
  binary_quartic_bound (by norm_num) (by norm_num) bqA_ge_003 h1 h2

/-- **Second binary quartic bound**: `h(u) ≤ 4u(1-u) - (3/8) u(1-u)(1-2u)²` on `[1/12, 1/2]`. -/
theorem bin_quartic2 {u : ℝ} (h1 : 1 / 12 ≤ u) (h2 : u ≤ 1 / 2) :
    binH qBQ u ≤ 4 * u * (1 - u) - 3 / 8 * (u * (1 - u) * (1 - 2 * u) ^ 2) :=
  binary_quartic_bound (by norm_num) (by norm_num) bqA_ge_112 h1 h2

/-- The binary cubic bound `h(u) ≤ 4u(1-u)`. -/
theorem bin_cubic {u : ℝ} (h1 : 0 ≤ u) (h2 : u ≤ 1) : binH qBQ u ≤ 4 * u * (1 - u) := by
  have hq := PaperECritical.qb_bounds
  have h := PaperECritical.renyi_binary_bound h1 h2
  have hanti := renyiSpec_anti (l := ![u, 1 - u]) (q := PaperECritical.qb) (q' := qBQ)
    (by linarith [hq.1]) (by unfold qBQ; linarith [hq.2.1, hq.2.2]) (by
      intro i; fin_cases i <;> simp <;> linarith) (by simp [Fin.sum_univ_two])
  rw [renyiSpec_binary] at hanti
  linarith

end FormalResearch.FourQubitEntropy.RenyiFull

module

public import FormalResearch.Asymptotics.UniformExpansion

/-!
# The exponential of an asymptotic expansion

If `f` has the expansion `∑ ε^r a_r` with `a_0 = 0` (so `f → 0`), then `exp f` has the expansion
`∑ ε^r κ_r`, where `∑ κ_r X^r = exp (∑ a_r X^r)` is the formal exponential
(`HasExpansionAlong.exp`, `HasUniformExpansion.exp`).  The formal exponential is
`expSeries A = ∑_n A^n / n!`, with coefficients
`[X^r] expSeries A = ∑_{n ≤ r} (n!)⁻¹ [X^r] A^n` (`coeff_expSeries`: only `n ≤ r` contribute when
`A` has no constant term).

Proof: `f^n` has the expansion with coefficients `[X^r] A^n` (Cauchy products,
`HasExpansionAlong.mul`), hence so does `∑_{n<R} f^n/n!`; and `exp f - ∑_{n<R} f^n/n! = O(f^R)`
(`Real.exp_bound`) with `f = O(ε)`.

Not covered: the converse (an expansion of `exp f` does not give one of `f` here), and complex or
vector-valued `f`.
-/

@[expose] public section

open Filter Topology Finset Asymptotics

namespace FormalResearch.Asymptotics

variable {E ι : Type*}

/-- The formal exponential `∑_n A^n / n!` of a power series without constant term, written
coefficientwise: `[X^r] = ∑_{n ≤ r} (n!)⁻¹ [X^r] A^n`. -/
noncomputable def expSeries (A : PowerSeries ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun r => ∑ n ∈ range (r + 1), ((n.factorial : ℝ))⁻¹ * PowerSeries.coeff r (A ^ n)

/-- The coefficient sequence `a · z` of `a : ℕ → E → ℝ` at the point `z`, as a power series. -/
noncomputable def coeffSeries (a : ℕ → E → ℝ) (z : E) : PowerSeries ℝ :=
  PowerSeries.mk fun r => a r z

/-- The exponential coefficients `κ_r(z) = [X^r] exp (∑ a_s(z) X^s)`. -/
noncomputable def expCoeff (a : ℕ → E → ℝ) (r : ℕ) (z : E) : ℝ :=
  PowerSeries.coeff r (expSeries (coeffSeries a z))

theorem coeff_pow_eq_zero_of_lt {A : PowerSeries ℝ} (hA : PowerSeries.constantCoeff A = 0)
    {r n : ℕ} (h : r < n) : PowerSeries.coeff r (A ^ n) = 0 := by
  obtain ⟨B, rfl⟩ := PowerSeries.X_dvd_iff.2 hA
  rw [mul_pow, PowerSeries.coeff_X_pow_mul']
  simp [not_le.2 h]

/-- Only `n ≤ r` contribute to `[X^r]` of the formal exponential: any `N > r` terms suffice. -/
theorem coeff_expSeries_eq_sum {A : PowerSeries ℝ} (hA : PowerSeries.constantCoeff A = 0)
    (r N : ℕ) (hN : r < N) :
    PowerSeries.coeff r (expSeries A) =
      ∑ n ∈ range N, ((n.factorial : ℝ))⁻¹ * PowerSeries.coeff r (A ^ n) := by
  rw [expSeries, PowerSeries.coeff_mk]
  refine sum_subset (range_subset_range.2 (Nat.succ_le_of_lt hN)) fun n _ hn => ?_
  rw [coeff_pow_eq_zero_of_lt hA (by simpa using hn), mul_zero]

theorem coeff_expSeries_zero (A : PowerSeries ℝ) : PowerSeries.coeff 0 (expSeries A) = 1 := by
  simp [expSeries]

theorem coeff_expSeries_one {A : PowerSeries ℝ} (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.coeff 1 (expSeries A) = PowerSeries.coeff 1 A := by
  rw [coeff_expSeries_eq_sum hA 1 2 (by norm_num)]
  simp [sum_range_succ, PowerSeries.coeff_one]

theorem coeff_expSeries_two {A : PowerSeries ℝ} (hA : PowerSeries.constantCoeff A = 0) :
    PowerSeries.coeff 2 (expSeries A) =
      PowerSeries.coeff 2 A + PowerSeries.coeff 1 A ^ 2 / 2 := by
  rw [coeff_expSeries_eq_sum hA 2 3 (by norm_num)]
  have h0 : PowerSeries.coeff 0 A = 0 := by simpa using hA
  simp [sum_range_succ, PowerSeries.coeff_one, pow_two, PowerSeries.coeff_mul,
    ]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [sum_range_succ, h0]
  ring

theorem expCoeff_zero (a : ℕ → E → ℝ) (z : E) : expCoeff a 0 z = 1 :=
  coeff_expSeries_zero _

theorem expCoeff_one (a : ℕ → E → ℝ) (h0 : ∀ z, a 0 z = 0) (z : E) :
    expCoeff a 1 z = a 1 z := by
  rw [expCoeff, coeff_expSeries_one (by simpa [coeffSeries] using h0 z)]
  simp [coeffSeries]

theorem expCoeff_two (a : ℕ → E → ℝ) (h0 : ∀ z, a 0 z = 0) (z : E) :
    expCoeff a 2 z = a 2 z + a 1 z ^ 2 / 2 := by
  rw [expCoeff, coeff_expSeries_two (by simpa [coeffSeries] using h0 z)]
  simp [coeffSeries]

section Exp

variable {L : Filter (E × ι)} {f : E → ι → ℝ} {a : ℕ → E → ℝ} {ε : ι → ℝ}

theorem HasExpansionAlong.congr_coeff {b : ℕ → E → ℝ} (h : HasExpansionAlong L f a ε)
    (hab : ∀ r z, a r z = b r z) : HasExpansionAlong L f b ε := by
  obtain rfl : a = b := funext fun r => funext fun z => hab r z
  exact h

theorem hasExpansionAlong_one :
    HasExpansionAlong L (fun (_ : E) (_ : ι) => (1 : ℝ))
      (fun r (_ : E) => PowerSeries.coeff r (1 : PowerSeries ℝ)) ε := by
  intro R
  cases R with
  | zero => simpa using isBigO_refl (fun _ : E × ι => (1 : ℝ)) L
  | succ R =>
    simp [PowerSeries.coeff_one]
    exact isBigO_zero _ L

theorem HasExpansionAlong.pow_coeff (hf : HasExpansionAlong L f a ε)
    (hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ)) (n : ℕ) :
    HasExpansionAlong L (fun z i => f z i ^ n)
      (fun r z => PowerSeries.coeff r (coeffSeries a z ^ n)) ε := by
  induction n with
  | zero => simpa using hasExpansionAlong_one (L := L) (ε := ε)
  | succ n ih =>
    have h := ih.mul hf hε
    have hc : cauchyCoeff (fun r z => PowerSeries.coeff r (coeffSeries a z ^ n)) a =
        fun r z => PowerSeries.coeff r (coeffSeries a z ^ (n + 1)) := by
      funext r z
      simp only [cauchyCoeff, pow_succ, PowerSeries.coeff_mul]
      refine sum_congr rfl fun p _ => ?_
      simp [coeffSeries]
    rw [hc] at h
    exact h.congr_left (Eventually.of_forall fun p => by simp [pow_succ])

theorem HasExpansionAlong.sum_pow_div (hf : HasExpansionAlong L f a ε)
    (hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ)) (N : ℕ) :
    HasExpansionAlong L (fun z i => ∑ n ∈ range N, ((n.factorial : ℝ))⁻¹ * f z i ^ n)
      (fun r z => ∑ n ∈ range N, ((n.factorial : ℝ))⁻¹ *
        PowerSeries.coeff r (coeffSeries a z ^ n)) ε := by
  induction N with
  | zero => intro R; simpa using isBigO_zero _ L
  | succ N ih =>
    have h2 := (hf.pow_coeff hε N).smul ((N.factorial : ℝ)⁻¹)
    have h := ih.add h2
    refine (h.congr_coeff fun r z => ?_).congr_left (Eventually.of_forall fun p => ?_)
    · simp [sum_range_succ]
    · simp [sum_range_succ]

/-- **The exponential of an expansion.**  If `f` has the expansion `∑ ε^r a_r` with `a_0 = 0` and
`ε → 0` along `L`, then `exp f` has the expansion `∑ ε^r κ_r` with `κ_r = [X^r] exp(∑ a_s X^s)`
(`expCoeff`). -/
theorem HasExpansionAlong.exp (hf : HasExpansionAlong L f a ε) (h0 : ∀ z, a 0 z = 0)
    (hε0 : Tendsto (fun p : E × ι => ε p.2) L (𝓝 0)) :
    HasExpansionAlong L (fun z i => Real.exp (f z i)) (expCoeff a) ε := by
  have hε : (fun p : E × ι => ε p.2) =O[L] fun _ => (1 : ℝ) := hε0.isBigO_one ℝ
  have hfO : (fun p : E × ι => f p.1 p.2) =O[L] fun p => ε p.2 := by
    simpa [h0] using hf 1
  have hf0 : Tendsto (fun p : E × ι => f p.1 p.2) L (𝓝 0) := hfO.trans_tendsto hε0
  have hfle : ∀ᶠ p in L, |f p.1 p.2| ≤ 1 := by
    have := hf0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with p hp
    simpa using hp
  have hA0 : ∀ z, PowerSeries.constantCoeff (coeffSeries a z) = 0 := fun z => by
    simpa [coeffSeries] using h0 z
  intro R
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp only [range_zero, sum_empty, sub_zero, pow_zero]
    refine IsBigO.of_bound (Real.exp 1) ?_
    filter_upwards [hfle] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_one, mul_one]
    exact Real.exp_le_exp.2 ((le_abs_self _).trans hp)
  · have e1 : (fun p : E × ι => Real.exp (f p.1 p.2) -
        ∑ n ∈ range R, ((n.factorial : ℝ))⁻¹ * f p.1 p.2 ^ n) =O[L] fun p => ε p.2 ^ R := by
      have hb : (fun p : E × ι => Real.exp (f p.1 p.2) -
          ∑ n ∈ range R, ((n.factorial : ℝ))⁻¹ * f p.1 p.2 ^ n) =O[L]
          fun p => f p.1 p.2 ^ R := by
        refine IsBigO.of_bound (R.succ / ((R.factorial : ℝ) * R)) ?_
        filter_upwards [hfle] with p hp
        have := Real.exp_bound hp hR
        simp only [div_eq_inv_mul] at this
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
        calc _ ≤ _ := this
          _ = _ := by ring
      exact hb.trans (hfO.pow R)
    have e2 := hf.sum_pow_div hε R
    have e2' : (fun p : E × ι => ∑ n ∈ range R, ((n.factorial : ℝ))⁻¹ * f p.1 p.2 ^ n -
        ∑ r ∈ range R, ε p.2 ^ r • expCoeff a r p.1) =O[L] fun p => ε p.2 ^ R := by
      refine (e2 R).congr_left fun p => ?_
      congr 1
      refine sum_congr rfl fun r hr => ?_
      rw [expCoeff, coeff_expSeries_eq_sum (hA0 _) r R (mem_range.1 hr)]
    refine (e1.add e2').congr_left fun p => ?_
    ring

/-- **The exponential of a uniform expansion** (`ε → 0` along `l`). -/
theorem HasUniformExpansion.exp {l : Filter ι} {K : Set E}
    (hf : HasUniformExpansion f a ε l K) (h0 : ∀ z, a 0 z = 0) (hε : Tendsto ε l (𝓝 0)) :
    HasUniformExpansion (fun z i => Real.exp (f z i)) (expCoeff a) ε l K :=
  HasExpansionAlong.exp hf h0 (hε.comp tendsto_snd)

end Exp


/-- info: 'FormalResearch.Asymptotics.HasExpansionAlong.exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasExpansionAlong.exp

/-- info: 'FormalResearch.Asymptotics.HasUniformExpansion.exp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms HasUniformExpansion.exp

/-- info: 'FormalResearch.Asymptotics.expCoeff_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms expCoeff_two

end FormalResearch.Asymptotics

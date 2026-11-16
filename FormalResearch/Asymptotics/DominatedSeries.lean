module

public import Mathlib

/-!
# Uniform Tannery theorem for finite partial sums

A generic "termwise limit of a finite sum with a dominated tail" lemma.  Let `Fn i ℓ z` be the
`ℓ`-th term of a finite sum `∑ ℓ ∈ s i, Fn i ℓ z`, where the index sets `s i` eventually contain
every initial segment `range L`.  If every term converges uniformly on `K` along `l`,
`Fn i ℓ ⟶ G ℓ`, and the terms of index `≥ L₀` are dominated by a summable sequence `M ℓ`,
uniformly in `z ∈ K` and eventually in `i`, then the finite sums converge uniformly on `K` to the
infinite series `∑' ℓ, G ℓ z`.

* `tendstoUniformlyOn_sum_of_dominated`: the statement above (uniform in `z`; the argument is the
  usual `ε/4` splitting into a finite head, a tail of the finite sum and a tail of the limit);
* `tendsto_sum_of_dominated`: the pointwise case `K = {z}`, i.e. the classical Tannery theorem for a
  varying finite index set (Mathlib's `tendsto_tsum_of_dominated_convergence` has a fixed index set);
* `norm_sum_sub_tsum_le_of_rate`: the rate version for `s n = range (n+1)`: if the terms differ from
  the limit terms by `≤ D ℓ / n` and the limit terms are dominated by `M ℓ` with `ℓ M ℓ` summable, the
  partial sum differs from the series by `≤ (∑ D + ∑ ℓ M ℓ)/n`;
* `tendstoUniformlyOn_of_norm_le`, `norm_pow_sub_pow_le'`: small helpers.

Nothing here is specific to Jacobi polynomials; the Jacobi instance is
`FormalResearch/Special/JacobiMehlerHeine.lean`.
-/

@[expose] public section

open Filter Topology Finset

namespace FormalResearch.Asymptotics

variable {ι E F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

/-- A finite sum of nonnegative terms of index `≥ L` is at most the tail of the series. -/
lemma sum_le_tsum_nat_add {M : ℕ → ℝ} (hM : Summable M) (hM0 : ∀ ℓ, 0 ≤ M ℓ) (L : ℕ)
    (T : Finset ℕ) (hT : ∀ ℓ ∈ T, L ≤ ℓ) : ∑ ℓ ∈ T, M ℓ ≤ ∑' k, M (k + L) := by
  set g : ℕ → ℝ := fun ℓ => if L ≤ ℓ then M ℓ else 0 with hg
  have hg0 : ∀ ℓ, 0 ≤ g ℓ := fun ℓ => by
    simp only [hg]; split_ifs
    · exact hM0 ℓ
    · exact le_rfl
  have hgs : Summable g := hM.of_nonneg_of_le hg0 fun ℓ => by
    simp only [hg]; split_ifs
    · exact le_rfl
    · exact hM0 ℓ
  have h1 : ∑ ℓ ∈ T, M ℓ = ∑ ℓ ∈ T, g ℓ :=
    Finset.sum_congr rfl fun ℓ hℓ => by simp [hg, hT ℓ hℓ]
  have h2 : ∑' k, g (k + L) = ∑' k, M (k + L) :=
    tsum_congr fun k => by simp [hg]
  have h3 := hgs.sum_add_tsum_nat_add L
  have h4 : ∑ i ∈ range L, g i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.1 hi
      simp [hg, not_le.2 this]
  rw [h1, ← h2]
  calc ∑ ℓ ∈ T, g ℓ ≤ ∑' ℓ, g ℓ := hgs.sum_le_tsum T fun ℓ _ => hg0 ℓ
    _ = ∑' k, g (k + L) := by rw [← h3, h4, zero_add]

/-- **Uniform Tannery theorem** for finite partial sums with varying index sets. -/
theorem tendstoUniformlyOn_sum_of_dominated {l : Filter ι} [l.NeBot] {s : ι → Finset ℕ}
    (hs : ∀ L, ∀ᶠ i in l, range L ⊆ s i) {Fn : ι → ℕ → E → F} {G : ℕ → E → F} {K : Set E}
    {M : ℕ → ℝ} (hM : Summable M) (hM0 : ∀ ℓ, 0 ≤ M ℓ) (L0 : ℕ)
    (hlim : ∀ ℓ, TendstoUniformlyOn (fun i => Fn i ℓ) (G ℓ) l K)
    (hdom : ∀ᶠ i in l, ∀ ℓ ∈ s i, L0 ≤ ℓ → ∀ z ∈ K, ‖Fn i ℓ z‖ ≤ M ℓ) :
    TendstoUniformlyOn (fun i z => ∑ ℓ ∈ s i, Fn i ℓ z) (fun z => ∑' ℓ, G ℓ z) l K := by
  -- the limit terms obey the same bound
  have hG : ∀ ℓ, L0 ≤ ℓ → ∀ z ∈ K, ‖G ℓ z‖ ≤ M ℓ := by
    intro ℓ hℓ z hz
    have hz' : Tendsto (fun i => Fn i ℓ z) l (𝓝 (G ℓ z)) :=
      ((hlim ℓ).tendsto_at hz)
    have : ∀ᶠ i in l, ‖Fn i ℓ z‖ ≤ M ℓ := by
      filter_upwards [hdom, hs (ℓ + 1)] with i hi hsi
      exact hi ℓ (hsi (Finset.mem_range.2 (Nat.lt_succ_self ℓ))) hℓ z hz
    exact le_of_tendsto hz'.norm this
  have hGs : ∀ z ∈ K, Summable fun ℓ => G ℓ z := by
    intro z hz
    rw [← summable_nat_add_iff L0]
    exact Summable.of_norm_bounded ((summable_nat_add_iff L0).2 hM)
      fun k => hG (k + L0) (Nat.le_add_left _ _) z hz
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- choose the head length
  have htail := tendsto_sum_nat_add M
  obtain ⟨L1, hL1⟩ := (htail.eventually (gt_mem_nhds (show (0:ℝ) < ε / 4 by positivity))).exists_forall_of_atTop
  set L := max L0 L1 with hLdef
  have hL0 : L0 ≤ L := le_max_left _ _
  have hLtail : ∑' k, M (k + L) < ε / 4 := hL1 L (le_max_right _ _)
  have hhead : ∀ᶠ i in l, ∀ ℓ ∈ range L, ∀ z ∈ K,
      dist (G ℓ z) (Fn i ℓ z) < ε / (4 * (L + 1)) := by
    refine (Finset.eventually_all _).2 fun ℓ _ => ?_
    exact Metric.tendstoUniformlyOn_iff.1 (hlim ℓ) _ (by positivity)
  filter_upwards [hhead, hdom, hs L] with i hi1 hi2 hi3 z hz
  have hsplit : ∑ ℓ ∈ s i, Fn i ℓ z =
      ∑ ℓ ∈ range L, Fn i ℓ z + ∑ ℓ ∈ s i \ range L, Fn i ℓ z := by
    rw [add_comm, Finset.sum_sdiff hi3]
  have hGsplit : ∑' ℓ, G ℓ z = ∑ ℓ ∈ range L, G ℓ z + ∑' k, G (k + L) z :=
    ((hGs z hz).sum_add_tsum_nat_add L).symm
  have hT1 : ‖∑ ℓ ∈ s i \ range L, Fn i ℓ z‖ ≤ ∑' k, M (k + L) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun ℓ hℓ => ?_).trans
      (sum_le_tsum_nat_add hM hM0 L (s i \ range L) fun ℓ hℓ => ?_)
    · have := Finset.mem_sdiff.1 hℓ
      exact hi2 ℓ this.1 (hL0.trans (not_lt.1 (by simpa using this.2))) z hz
    · have := Finset.mem_sdiff.1 hℓ
      exact not_lt.1 (by simpa using this.2)
  have hT2 : ‖∑' k, G (k + L) z‖ ≤ ∑' k, M (k + L) :=
    tsum_of_norm_bounded ((summable_nat_add_iff L).2 hM).hasSum
      fun k => hG (k + L) (hL0.trans (Nat.le_add_left _ _)) z hz
  have hH : ‖∑ ℓ ∈ range L, (G ℓ z - Fn i ℓ z)‖ ≤ ε / 4 := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ℓ ∈ range L, ‖G ℓ z - Fn i ℓ z‖ ≤ ∑ ℓ ∈ range L, ε / (4 * (L + 1)) :=
          Finset.sum_le_sum fun ℓ hℓ => by
            have := hi1 ℓ hℓ z hz
            rw [dist_eq_norm] at this
            exact this.le
      _ = L * (ε / (4 * (L + 1))) := by simp
      _ ≤ ε / 4 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hε]
  rw [dist_eq_norm, hsplit, hGsplit]
  have : ∑ ℓ ∈ range L, G ℓ z + ∑' k, G (k + L) z -
      (∑ ℓ ∈ range L, Fn i ℓ z + ∑ ℓ ∈ s i \ range L, Fn i ℓ z) =
      ∑ ℓ ∈ range L, (G ℓ z - Fn i ℓ z) + ∑' k, G (k + L) z -
        ∑ ℓ ∈ s i \ range L, Fn i ℓ z := by
    rw [Finset.sum_sub_distrib]; abel
  rw [this]
  calc ‖∑ ℓ ∈ range L, (G ℓ z - Fn i ℓ z) + ∑' k, G (k + L) z -
        ∑ ℓ ∈ s i \ range L, Fn i ℓ z‖
      ≤ ‖∑ ℓ ∈ range L, (G ℓ z - Fn i ℓ z)‖ + ‖∑' k, G (k + L) z‖ +
        ‖∑ ℓ ∈ s i \ range L, Fn i ℓ z‖ :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ < ε := by linarith

/-- The pointwise (classical Tannery) case. -/
theorem tendsto_sum_of_dominated {l : Filter ι} [l.NeBot] {s : ι → Finset ℕ}
    (hs : ∀ L, ∀ᶠ i in l, range L ⊆ s i) {Fn : ι → ℕ → F} {G : ℕ → F}
    {M : ℕ → ℝ} (hM : Summable M) (hM0 : ∀ ℓ, 0 ≤ M ℓ) (L0 : ℕ)
    (hlim : ∀ ℓ, Tendsto (fun i => Fn i ℓ) l (𝓝 (G ℓ)))
    (hdom : ∀ᶠ i in l, ∀ ℓ ∈ s i, L0 ≤ ℓ → ‖Fn i ℓ‖ ≤ M ℓ) :
    Tendsto (fun i => ∑ ℓ ∈ s i, Fn i ℓ) l (𝓝 (∑' ℓ, G ℓ)) := by
  have := tendstoUniformlyOn_sum_of_dominated (E := Unit) (K := Set.univ) hs hM hM0 L0
    (Fn := fun i ℓ _ => Fn i ℓ) (G := fun ℓ _ => G ℓ)
    (fun ℓ => by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [Metric.tendsto_nhds.1 (hlim ℓ) ε hε] with i hi _ _
      rwa [dist_comm])
    (by filter_upwards [hdom] with i hi ℓ h1 h2 _ _ using hi ℓ h1 h2)
  exact this.tendsto_at (Set.mem_univ ())

omit [CompleteSpace F] in
/-- Uniform convergence from a norm bound by a null sequence. -/
theorem tendstoUniformlyOn_of_norm_le {l : Filter ι} {K : Set E} {Fn : ι → E → F} {f : E → F}
    {c : ι → ℝ} (hc : Tendsto c l (𝓝 0)) (h : ∀ᶠ i in l, ∀ z ∈ K, ‖Fn i z - f z‖ ≤ c i) :
    TendstoUniformlyOn Fn f l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h, (Metric.tendsto_nhds.1 hc) ε hε] with i hi hc' z hz
  rw [dist_comm, dist_eq_norm]
  refine (hi z hz).trans_lt ?_
  simpa using (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hc')

/-- Lipschitz bound for powers in a normed field: `‖a^k - b^k‖ ≤ k S^k ‖a - b‖` when
`‖a‖, ‖b‖ ≤ S` and `1 ≤ S`. -/
theorem norm_pow_sub_pow_le' {R : Type*} [NormedField R] {a b : R} {S : ℝ} (ha : ‖a‖ ≤ S)
    (hb : ‖b‖ ≤ S) (hS : 1 ≤ S) (k : ℕ) : ‖a ^ k - b ^ k‖ ≤ k * S ^ k * ‖a - b‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a ^ (k + 1) - b ^ (k + 1) = a * (a ^ k - b ^ k) + (a - b) * b ^ k := by
      ring
    rw [e]
    have h1 : ‖a * (a ^ k - b ^ k)‖ ≤ S * (k * S ^ k * ‖a - b‖) :=
      (norm_mul_le _ _).trans (mul_le_mul ha ih (norm_nonneg _) (by linarith [norm_nonneg a]))
    have h2 : ‖(a - b) * b ^ k‖ ≤ ‖a - b‖ * S ^ k :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        ((norm_pow_le b k).trans (pow_le_pow_left₀ (norm_nonneg _) hb k)) (norm_nonneg _))
    refine (norm_add_le _ _).trans ((add_le_add h1 h2).trans ?_)
    have h3 : S ^ k ≤ S ^ (k + 1) := pow_le_pow_right₀ hS (Nat.le_succ k)
    have hn := norm_nonneg (a - b)
    push_cast
    rw [pow_succ] at h3 ⊢
    nlinarith [mul_nonneg hn (pow_nonneg (by linarith : (0:ℝ) ≤ S) k), mul_nonneg hn (by linarith : (0:ℝ) ≤ S - 1)]

/-- **Rate version of the Tannery theorem** for the partial sums `∑_{ℓ ≤ n} Fn n ℓ z`.  If the
terms differ from the limit terms by at most `D ℓ / n` (`D` summable), and the limit terms of index
`≥ L0` are dominated by `M ℓ` with `ℓ ↦ ℓ M ℓ` summable, then
`‖∑_{ℓ ≤ n} Fn n ℓ z - ∑' ℓ, G ℓ z‖ ≤ (∑' D + ∑' ℓ M ℓ) / n` for `n ≥ max N L0`, `n ≥ 1`. -/
theorem norm_sum_sub_tsum_le_of_rate {Fn : ℕ → ℕ → E → F} {G : ℕ → E → F} {K : Set E}
    {M D : ℕ → ℝ} (hM : Summable M) (hM0 : ∀ ℓ, 0 ≤ M ℓ)
    (hMl : Summable fun ℓ : ℕ => (ℓ : ℝ) * M ℓ) (hD : Summable D) (hD0 : ∀ ℓ, 0 ≤ D ℓ)
    (L0 N : ℕ) (hG : ∀ ℓ, L0 ≤ ℓ → ∀ z ∈ K, ‖G ℓ z‖ ≤ M ℓ)
    (hF : ∀ n, N ≤ n → ∀ ℓ ∈ range (n + 1), ∀ z ∈ K, ‖Fn n ℓ z - G ℓ z‖ ≤ D ℓ / n)
    {n : ℕ} (hn1 : 1 ≤ n) (hnN : N ≤ n) (hnL : L0 ≤ n) {z : E} (hz : z ∈ K) :
    ‖∑ ℓ ∈ range (n + 1), Fn n ℓ z - ∑' ℓ, G ℓ z‖ ≤
      ((∑' ℓ, D ℓ) + ∑' ℓ : ℕ, (ℓ : ℝ) * M ℓ) / n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hGs : Summable fun ℓ => G ℓ z := by
    rw [← summable_nat_add_iff L0]
    exact Summable.of_norm_bounded ((summable_nat_add_iff L0).2 hM)
      fun k => hG (k + L0) (Nat.le_add_left _ _) z hz
  have hGsplit : ∑' ℓ, G ℓ z = ∑ ℓ ∈ range (n + 1), G ℓ z + ∑' k, G (k + (n + 1)) z :=
    (hGs.sum_add_tsum_nat_add (n + 1)).symm
  have hhead : ‖∑ ℓ ∈ range (n + 1), (Fn n ℓ z - G ℓ z)‖ ≤ (∑' ℓ, D ℓ) / n := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ ℓ ∈ range (n + 1), ‖Fn n ℓ z - G ℓ z‖ ≤ ∑ ℓ ∈ range (n + 1), D ℓ / n :=
          Finset.sum_le_sum fun ℓ hℓ => hF n hnN ℓ hℓ z hz
      _ = (∑ ℓ ∈ range (n + 1), D ℓ) / n := by rw [Finset.sum_div]
      _ ≤ (∑' ℓ, D ℓ) / n := by
          gcongr
          exact hD.sum_le_tsum _ fun ℓ _ => hD0 ℓ
  have htail1 : ‖∑' k, G (k + (n + 1)) z‖ ≤ ∑' k, M (k + (n + 1)) :=
    tsum_of_norm_bounded ((summable_nat_add_iff (n + 1)).2 hM).hasSum
      fun k => hG (k + (n + 1)) (by omega) z hz
  have htail2 : ∑' k, M (k + (n + 1)) ≤ (∑' ℓ : ℕ, (ℓ : ℝ) * M ℓ) / n := by
    have h1 : ∀ k, M (k + (n + 1)) ≤ ((k + (n + 1) : ℕ) : ℝ) * M (k + (n + 1)) / n := by
      intro k
      rw [le_div_iff₀ hnpos]
      have : (n : ℝ) ≤ ((k + (n + 1) : ℕ) : ℝ) := by
        push_cast; have : (0 : ℝ) ≤ k := Nat.cast_nonneg _; linarith
      nlinarith [hM0 (k + (n + 1))]
    have hs : Summable fun k => ((k + (n + 1) : ℕ) : ℝ) * M (k + (n + 1)) / n :=
      (((summable_nat_add_iff (n + 1)).2 hMl).div_const _)
    calc ∑' k, M (k + (n + 1)) ≤ ∑' k, ((k + (n + 1) : ℕ) : ℝ) * M (k + (n + 1)) / n :=
          Summable.tsum_le_tsum h1 ((summable_nat_add_iff (n + 1)).2 hM) hs
      _ = (∑' k, ((k + (n + 1) : ℕ) : ℝ) * M (k + (n + 1))) / n := tsum_div_const
      _ ≤ (∑' ℓ : ℕ, (ℓ : ℝ) * M ℓ) / n := by
          refine div_le_div_of_nonneg_right ?_ hnpos.le
          have h2 := hMl.sum_add_tsum_nat_add (n + 1)
          have h3 : 0 ≤ ∑ i ∈ range (n + 1), (i : ℝ) * M i :=
            Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (hM0 i)
          linarith
  have e : ∑ ℓ ∈ range (n + 1), Fn n ℓ z - ∑' ℓ, G ℓ z =
      ∑ ℓ ∈ range (n + 1), (Fn n ℓ z - G ℓ z) - ∑' k, G (k + (n + 1)) z := by
    rw [hGsplit, Finset.sum_sub_distrib]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have := add_le_add hhead (htail1.trans htail2)
  rw [← add_div] at this
  exact this

/-! ### Axiom check -/

/-- info: 'FormalResearch.Asymptotics.tendstoUniformlyOn_sum_of_dominated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.tendstoUniformlyOn_sum_of_dominated

/-- info: 'FormalResearch.Asymptotics.tendsto_sum_of_dominated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.tendsto_sum_of_dominated

/-- info: 'FormalResearch.Asymptotics.norm_sum_sub_tsum_le_of_rate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms FormalResearch.Asymptotics.norm_sum_sub_tsum_le_of_rate

end FormalResearch.Asymptotics

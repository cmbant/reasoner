module

public import FormalResearch.FourQubitEntropy.SevenQubitConseqMajorant

/-!
# `lem:seven-fixed-purity-envelope`: the entropy envelope at fixed purity, every dimension `d ≥ 2`

Source: `ResearchNotes/QI/seven_qubit_entanglement/seven_qubit_entropy_global_upper.tex`,
`lem:seven-fixed-purity-envelope` (all dimensions) and the dimension-independent quadratic majorant
before it.

For a probability vector `λ` on `d` points with `∑ λ² = p` put
`t_d(p) = (1 + √((d-1)(dp-1)))/d` (`spikeWt`) and let `g_d(p)` (`gEnv`, nats) be the entropy of the
one-spike spectrum `(t_d(p), ((1-t_d(p))/(d-1))^{d-1})` (`spikeEnt`).  Then

* `entropy_le_gEnv`: `∑ -λ ln λ ≤ g_d(∑ λ²)`;
* `entropy_eq_gEnv_iff`: equality holds exactly when `λ` is that one-spike spectrum (one entry
  `t_d(p)`, all others `(1-t_d(p))/(d-1)`), including the uniform (`p = 1/d`) and pure (`p = 1`) ends.

Proof (as in the paper): `λ_max ≤ t_d(p)` by Cauchy–Schwarz on the other `d-1` entries; the Hermite
quadratic majorant `Q` of `-x ln x` with double contact at `b = (1-a)/(d-1)` and contact at `a = t_d(p)`
(`SevenQubitConseq.majorant`) is valid on `[0,a]`, and `∑ Q(λ_i)` depends only on `∑ λ` and `∑ λ²`, so it
equals its value `g_d(p)` on the spike.  For the equality case the majorant is strict off `{a, b}`
(`majorant_strict`, proved here), so every `λ_i ∈ {a,b}`, and the trace forces exactly one `a`.

Everything is proved (no hypotheses).  The `d = 8` instance is `SevenQubitConseq.entropy_le_g8`.
-/

@[expose] public section


open Real Finset

namespace FormalResearch.FourQubitEntropy.EntropyPurity

open FormalResearch.FourQubitEntropy.SevenQubitConseq

/-! ### Strict version of the Hermite majorant -/

theorem hc_mul {a b : ℝ} : hc a b * (a - b) ^ 2 = rem b a := by
  unfold hc
  rcases eq_or_ne a b with h | h
  · subst h; simp [rem_at]
  · have : (a - b) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.2 h)
    field_simp

theorem uf_strictMonoOn {b : ℝ} (hb : 0 < b) : StrictMonoOn (uf b) (Set.Ici b) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici b)
  · apply Continuous.continuousOn
    unfold uf rem tang
    fun_prop
  · intro y hy
    rw [interior_Ici] at hy
    have hy0 : (0 : ℝ) < y := hb.trans hy
    rw [(hasDerivAt_uf hb hy0.ne').deriv]
    have hne : y / b ≠ 1 := by
      rw [Ne, div_eq_one_iff_eq hb.ne']; exact ne_of_gt hy
    have := Real.log_lt_sub_one_of_pos (div_pos hy0 hb) hne
    rw [Real.log_div hy0.ne' hb.ne'] at this
    linarith

/-- `c > -1/(2b)` when `a > b`. -/
theorem hc_gt {a b : ℝ} (hb : 0 < b) (hba : b < a) : -(1 / (2 * b)) < hc a b := by
  have h := uf_strictMonoOn hb (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hba.le) hba
  have h0 : rem b b = 0 := rem_at b
  simp only [uf, h0, sub_self] at h
  have hp : 0 < (a - b) ^ 2 := by have := sub_pos.2 hba; positivity
  unfold hc
  rw [lt_div_iff₀ hp]
  have : -(1 / (2 * b)) * (a - b) ^ 2 = -((a - b) ^ 2 / (2 * b)) := by field_simp
  simp at h
  linarith

theorem Nn_pos {b y : ℝ} (hb : 0 < b) (hy : b < y) : 0 < Nn b y := by
  have hmono : StrictMonoOn (Nn b) (Set.Ici b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici b)
    · apply ContinuousOn.sub
      · apply ContinuousOn.mul (by fun_prop)
        apply ContinuousOn.sub
        · exact Real.continuousOn_log.mono (fun y hy => ne_of_gt (lt_of_lt_of_le hb hy))
        · exact continuousOn_const
      · fun_prop
    · intro y hy
      rw [interior_Ici] at hy
      have hy0 : (0 : ℝ) < y := hb.trans hy
      have hd := (((hasDerivAt_id y).add_const b).mul
        (((Real.hasDerivAt_log hy0.ne').sub_const (log b)))).sub
        (((hasDerivAt_id y).sub_const b).const_mul 2)
      have hd' : HasDerivAt (Nn b) (1 * (log y - log b) + (id y + b) * y⁻¹ - 2 * 1) y := by
        unfold Nn; exact hd
      rw [hd'.deriv]
      have hne : b / y ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq hy0.ne']; exact ne_of_lt hy
      have h4 := Real.log_lt_sub_one_of_pos (div_pos hb hy0) hne
      rw [Real.log_div hb.ne' hy0.ne'] at h4
      have e : (1 * (log y - log b) + (id y + b) * (y⁻¹)) - 2 * (1) = (log y - log b) + b / y - 1 := by
        simp only [id]; field_simp; ring
      rw [e]
      linarith
  have h0 : Nn b b = 0 := by simp [Nn]
  have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hy.le) hy
  rwa [h0] at this

theorem rho_strictMonoOn {b : ℝ} (hb : 0 < b) :
    StrictMonoOn (fun y => rem b y / (y - b) ^ 2) (Set.Ioi b) := by
  have hd : ∀ y ∈ Set.Ioi b, HasDerivAt (fun y => rem b y / (y - b) ^ 2)
      (((log b - log y) * (y - b) ^ 2 - rem b y * (2 * (y - b))) / ((y - b) ^ 2) ^ 2) y := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hb.trans hy
    have hyb : y - b ≠ 0 := sub_ne_zero.2 (ne_of_gt hy)
    have h2 : HasDerivAt (fun y => (y - b) ^ 2) (2 * (y - b)) y := by
      have := ((hasDerivAt_id y).sub_const b).pow 2
      refine this.congr_deriv ?_
      simp
    exact (hasDerivAt_rem hy0.ne').div h2 (pow_ne_zero 2 hyb)
  apply strictMonoOn_of_deriv_pos (convex_Ioi b)
  · intro y hy
    exact (hd y hy).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ioi] at hy
    rw [(hd y hy).deriv]
    have hyb : 0 < y - b := sub_pos.2 hy
    have hN := Nn_pos hb hy
    apply div_pos _ (by positivity)
    have e : (log b - log y) * (y - b) ^ 2 - rem b y * (2 * (y - b)) = (y - b) * Nn b y := by
      simp only [rem, tang, Nn, negMulLog]
      ring
    rw [e]
    exact mul_pos hyb hN

/-- **Strict Hermite majorant**: for `0 < b < a` and `x ∈ [0,a] \ {a, b}`,
`-x ln x < T_b(x) + c (x-b)²` (the paper's strictness remark before
`lem:seven-fixed-purity-envelope`). -/
theorem majorant_strict {a b x : ℝ} (hb : 0 < b) (hba : b < a) (hx0 : 0 ≤ x) (hxa : x < a)
    (hxb : x ≠ b) : negMulLog x < tang b x + hc a b * (x - b) ^ 2 := by
  have key : rem b x < hc a b * (x - b) ^ 2 := by
    rcases lt_or_gt_of_ne hxb with hxb | hxb
    · have h1 := rem_le_of_le hb hx0 hxb.le
      have h2 := hc_gt hb hba
      have hp : 0 < (x - b) ^ 2 := by have := sub_neg.2 hxb; positivity
      have : -(1 / (2 * b)) * (x - b) ^ 2 < hc a b * (x - b) ^ 2 :=
        mul_lt_mul_of_pos_right h2 hp
      have e : -(1 / (2 * b)) * (x - b) ^ 2 = -((x - b) ^ 2 / (2 * b)) := by field_simp
      linarith
    · have hmono := rho_strictMonoOn hb (Set.mem_Ioi.2 hxb) (Set.mem_Ioi.2 (hxb.trans hxa)) hxa
      have hp : 0 < (x - b) ^ 2 := by have := sub_pos.2 hxb; positivity
      have : rem b x / (x - b) ^ 2 < hc a b := hmono
      rw [div_lt_iff₀ hp] at this
      exact this
  unfold rem at key
  linarith

/-! ### Definitions -/

/-- Entropy (nats) of the one-spike spectrum `(a, ((1-a)/(d-1))^{d-1})` on `d` points. -/
noncomputable def spikeEnt (d a : ℝ) : ℝ := negMulLog a + (d - 1) * negMulLog ((1 - a) / (d - 1))

/-- The spike weight `t_d(p) = (1 + √((d-1)(dp-1)))/d`. -/
noncomputable def spikeWt (d p : ℝ) : ℝ := (1 + Real.sqrt ((d - 1) * (d * p - 1))) / d

/-- The envelope `g_d(p)` (nats): the entropy of the spike spectrum of purity `p`. -/
noncomputable def gEnv (d p : ℝ) : ℝ := spikeEnt d (spikeWt d p)

/-! ### Elementary facts about probability vectors -/

theorem sum_sq_ge_inv {ι : Type*} [Fintype ι] {d : ℕ} (hcard : Fintype.card ι = d) (hd : 0 < d)
    (lam : ι → ℝ) (h1 : ∑ i, lam i = 1) : 1 / (d : ℝ) ≤ ∑ i, lam i ^ 2 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have : 0 ≤ ∑ i, (lam i - 1 / d) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have e : ∑ i, (lam i - 1 / (d : ℝ)) ^ 2 = ∑ i, lam i ^ 2 - 1 / d := by
    have : ∀ i, (lam i - 1 / (d : ℝ)) ^ 2 = lam i ^ 2 - (2 / d) * lam i + 1 / d ^ 2 := fun i => by
      ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, h1,
      Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    field_simp
    ring
  linarith

theorem le_one_of_prob {ι : Type*} [Fintype ι] (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∑ i, lam i = 1) (i : ι) : lam i ≤ 1 := by
  rw [← h1]; exact Finset.single_le_sum (f := lam) (fun j _ => h0 j) (mem_univ i)

theorem sum_sq_le_one {ι : Type*} [Fintype ι] (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i)
    (h1 : ∑ i, lam i = 1) : ∑ i, lam i ^ 2 ≤ 1 := by
  calc ∑ i, lam i ^ 2 ≤ ∑ i, lam i := Finset.sum_le_sum fun i _ => by
        nlinarith [h0 i, le_one_of_prob lam h0 h1 i]
    _ = 1 := h1

/-- Sum of `f` over a one-spike vector. -/
theorem sum_spike {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} (hcard : Fintype.card ι = d)
    (lam : ι → ℝ) (f : ℝ → ℝ) {i0 : ι} {a b : ℝ} (ha : lam i0 = a)
    (hb : ∀ i, i ≠ i0 → lam i = b) : ∑ i, f (lam i) = f a + ((d : ℝ) - 1) * f b := by
  rw [← Finset.add_sum_erase univ _ (mem_univ i0), ha]
  rw [Finset.sum_congr rfl fun i hi => by rw [hb i (Finset.ne_of_mem_erase hi)]]
  rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i0), Finset.card_univ, hcard,
    nsmul_eq_mul]
  have : 1 ≤ d := by
    rw [← hcard]; exact Fintype.card_pos_iff.2 ⟨i0⟩
  push_cast [this]
  ring

/-! ### The envelope with prescribed contact points -/

/-- Cauchy–Schwarz on the other `d - 1` entries: every entry is at most `a`. -/
theorem le_spike {ι : Type*} [Fintype ι] {d : ℕ} (hcard : Fintype.card ι = d) (lam : ι → ℝ)
    (h1 : ∑ i, lam i = 1) {a b : ℝ} (hab : a + ((d : ℝ) - 1) * b = 1)
    (hba : b ≤ a) (hp : ∑ i, lam i ^ 2 = a ^ 2 + ((d : ℝ) - 1) * b ^ 2) (j : ι) : lam j ≤ a := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := univ.erase j) (f := lam)
  have hd1 : 1 ≤ d := by rw [← hcard]; exact Fintype.card_pos_iff.2 ⟨j⟩
  have hcm : ((univ.erase j).card : ℝ) = (d : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (mem_univ j), Finset.card_univ, hcard]; push_cast [hd1]; ring
  rw [hcm] at hcs
  have e1 : ∑ i ∈ univ.erase j, lam i = 1 - lam j := by
    have := Finset.add_sum_erase univ lam (mem_univ j)
    linarith
  have e2 : ∑ i ∈ univ.erase j, lam i ^ 2 = a ^ 2 + ((d : ℝ) - 1) * b ^ 2 - lam j ^ 2 := by
    have := Finset.add_sum_erase univ (fun i => lam i ^ 2) (mem_univ j)
    linarith
  rw [e1, e2] at hcs
  -- `(1-x)² ≤ (d-1)(p - x²)` is `d (x - a)(x - 2/d + a) ≤ 0`
  by_contra hlt
  rw [not_le] at hlt
  set m : ℝ := (d : ℝ) - 1
  have hm : 0 ≤ m := by simp only [m]; have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
                        linarith
  have hb1 : 1 - a = m * b := by linarith
  -- a ≥ b and a + m b = 1 give (m+1) a ≥ 1
  have hda : 1 ≤ (m + 1) * a := by nlinarith
  have key : (m + 1) * (lam j - a) * (lam j + a) - 2 * (lam j - a) ≤ 0 := by
    have e : (1 - lam j) ^ 2 - m * (a ^ 2 + m * b ^ 2 - lam j ^ 2) =
        (m + 1) * (lam j - a) * (lam j + a) - 2 * (lam j - a) := by
      have : m * b = 1 - a := hb1.symm
      have hmb2 : m * (m * b ^ 2) = (1 - a) ^ 2 := by rw [← this]; ring
      nlinarith [hmb2]
    linarith
  have hpos : 0 < lam j - a := by linarith
  have : (m + 1) * (lam j + a) - 2 > 0 := by nlinarith
  nlinarith [mul_pos hpos this]

/-- The quadratic majorant summed over `λ`: `∑ -λ ln λ ≤ -a ln a - (d-1) b ln b` when
`a + (d-1) b = 1`, `0 < b ≤ a` and `∑ λ² = a² + (d-1) b²`; strict unless every `λ_i ∈ {a, b}`. -/
theorem envelope_core {ι : Type*} [Fintype ι] {d : ℕ} (hcard : Fintype.card ι = d) (lam : ι → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) {a b : ℝ} (hab : a + ((d : ℝ) - 1) * b = 1)
    (hb : 0 < b) (hba : b ≤ a) (hp : ∑ i, lam i ^ 2 = a ^ 2 + ((d : ℝ) - 1) * b ^ 2) :
    ∑ i, negMulLog (lam i) ≤ negMulLog a + ((d : ℝ) - 1) * negMulLog b ∧
    (b < a → ∑ i, negMulLog (lam i) = negMulLog a + ((d : ℝ) - 1) * negMulLog b →
      ∀ i, lam i = a ∨ lam i = b) := by
  have hle := le_spike hcard lam h1 hab hba hp
  set c := hc a b with hcdef
  set α : ℝ := negMulLog b + (-log b - 1) * (-b) + c * b ^ 2 with hα
  set β : ℝ := (-log b - 1) - 2 * c * b with hβ
  set Q : ℝ → ℝ := fun x => α + β * x + c * x ^ 2 with hQ
  have hQe : ∀ x, tang b x + c * (x - b) ^ 2 = Q x := by
    intro x; simp only [tang, hQ, hα, hβ]; ring
  have hmaj : ∀ i, negMulLog (lam i) ≤ Q (lam i) := fun i => by
    rw [← hQe]; exact majorant hb hba (h0 i) (hle i)
  have hQa : negMulLog a = Q a := by
    have := hc_mul (a := a) (b := b)
    have e : rem b a = negMulLog a - tang b a := rfl
    rw [← hQe]; rw [← hcdef] at this; linarith
  have hQb : negMulLog b = Q b := by
    rw [← hQe]; simp [tang]
  have hsumQ : ∑ i, Q (lam i) = negMulLog a + ((d : ℝ) - 1) * negMulLog b := by
    calc ∑ i, Q (lam i) = (d : ℝ) * α + β * 1 + c * (a ^ 2 + ((d : ℝ) - 1) * b ^ 2) := by
          simp only [hQ]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            h1, hp]
          simp [Finset.sum_const, Finset.card_univ, hcard]
      _ = Q a + ((d : ℝ) - 1) * Q b := by
          simp only [hQ]
          have : a = 1 - ((d : ℝ) - 1) * b := by linarith
          subst this
          ring
      _ = _ := by rw [← hQa, ← hQb]
  refine ⟨hsumQ ▸ Finset.sum_le_sum fun i _ => hmaj i, fun hlt heq i => ?_⟩
  by_contra hne
  push Not at hne
  have hstrict : negMulLog (lam i) < Q (lam i) := by
    rw [← hQe]
    exact majorant_strict hb hlt (h0 i) (lt_of_le_of_ne (hle i) hne.1) hne.2
  have : ∑ j, negMulLog (lam j) < ∑ j, Q (lam j) :=
    Finset.sum_lt_sum (fun j _ => hmaj j) ⟨i, mem_univ i, hstrict⟩
  linarith

/-- Counting: if every entry is `a` or `b` with `a ≠ b` and `a + (d-1) b = 1 = ∑ λ`, then exactly one
entry equals `a`. -/
theorem spike_of_two_values {ι : Type*} [Fintype ι] {d : ℕ} (hcard : Fintype.card ι = d)
    (lam : ι → ℝ) (h1 : ∑ i, lam i = 1) {a b : ℝ} (hab : a + ((d : ℝ) - 1) * b = 1) (hne : a ≠ b)
    (h2 : ∀ i, lam i = a ∨ lam i = b) : ∃ i0, lam i0 = a ∧ ∀ i, i ≠ i0 → lam i = b := by
  classical
  set A := univ.filter fun i => lam i = a with hA
  have hs := Finset.sum_filter_add_sum_filter_not univ (fun i => lam i = a) lam
  have hsA : ∑ i ∈ A, lam i = A.card * a := by
    rw [Finset.sum_congr rfl fun i hi => (Finset.mem_filter.1 hi).2, Finset.sum_const,
      nsmul_eq_mul]
  have hsB : ∑ i ∈ univ.filter (fun i => ¬ lam i = a), lam i =
      (univ.filter (fun i => ¬ lam i = a)).card * b := by
    rw [Finset.sum_congr rfl fun i hi => ((h2 i).resolve_left (Finset.mem_filter.1 hi).2),
      Finset.sum_const, nsmul_eq_mul]
  have hc := Finset.card_filter_add_card_filter_not (s := univ) (fun i => lam i = a)
  rw [Finset.card_univ, hcard] at hc
  have hc' : ((univ.filter (fun i => ¬ lam i = a)).card : ℝ) = d - A.card := by
    rw [← hc]; push_cast; ring
  rw [← hA, hsA, hsB, hc', h1] at hs
  have hk : ((A.card : ℝ) - 1) * (a - b) = 0 := by linarith
  have hk1 : (A.card : ℝ) = 1 := by
    rcases mul_eq_zero.1 hk with h | h
    · linarith
    · exact absurd (sub_eq_zero.1 h) hne
  have : A.card = 1 := by exact_mod_cast hk1
  obtain ⟨i0, hi0⟩ := Finset.card_eq_one.1 this
  have hmem : i0 ∈ A := by rw [hi0]; exact mem_singleton_self i0
  refine ⟨i0, (Finset.mem_filter.1 hmem).2, fun i hi => (h2 i).resolve_left fun h => hi ?_⟩
  have : i ∈ A := Finset.mem_filter.2 ⟨mem_univ i, h⟩
  rw [hi0] at this
  exact Finset.mem_singleton.1 this

/-! ### The envelope -/

/-- The data of the spike of purity `p`: `s = √((d-1)(dp-1)) ∈ [0, d-1]`, `a = (1+s)/d`,
`b = (1-a)/(d-1) = (d-1-s)/(d(d-1))`, `a + (d-1)b = 1`, `a² + (d-1) b² = p`. -/
theorem spike_data {d p : ℝ} (hd : 1 < d) (hp1 : 1 / d ≤ p) (hp2 : p ≤ 1) :
    let s := Real.sqrt ((d - 1) * (d * p - 1))
    0 ≤ s ∧ s ≤ d - 1 ∧ s ^ 2 = (d - 1) * (d * p - 1) ∧
    spikeWt d p + (d - 1) * ((1 - spikeWt d p) / (d - 1)) = 1 ∧
    spikeWt d p ^ 2 + (d - 1) * ((1 - spikeWt d p) / (d - 1)) ^ 2 = p ∧
    (1 - spikeWt d p) / (d - 1) = (d - 1 - s) / (d * (d - 1)) ∧ spikeWt d p = (1 + s) / d := by
  intro s
  have hd0 : 0 < d := by linarith
  have hm : 0 < d - 1 := by linarith
  have hdp : 0 ≤ d * p - 1 := by
    rw [div_le_iff₀ hd0] at hp1; linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = (d - 1) * (d * p - 1) := Real.sq_sqrt (mul_nonneg hm.le hdp)
  have hsm : s ≤ d - 1 := by
    have : s ^ 2 ≤ (d - 1) ^ 2 := by rw [hs2]; nlinarith
    nlinarith
  have ht : spikeWt d p = (1 + s) / d := rfl
  refine ⟨hs0, hsm, hs2, ?_, ?_, ?_, ht⟩
  · rw [ht]; field_simp; ring
  · rw [ht]; field_simp
    linear_combination d * hs2
  · rw [ht]; field_simp; ring

/-- **`lem:seven-fixed-purity-envelope` (entropy bound, every `d ≥ 2`).**  For every probability vector
`λ` on a `d`-point set: `∑ -λ ln λ ≤ g_d(∑ λ²)`. -/
theorem entropy_le_gEnv {ι : Type*} [Fintype ι] {d : ℕ} (hd : 2 ≤ d)
    (hcard : Fintype.card ι = d) (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∑ i, negMulLog (lam i) ≤ gEnv d (∑ i, lam i ^ 2) := by
  set p := ∑ i, lam i ^ 2 with hpdef
  have hd' : (1 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 / (d : ℝ) ≤ p := sum_sq_ge_inv hcard (by omega) lam h1
  have hp2 : p ≤ 1 := sum_sq_le_one lam h0 h1
  obtain ⟨hs0, hsm, hs2, hab, hpq, hb, ht⟩ := spike_data hd' hp1 hp2
  set s := Real.sqrt (((d : ℝ) - 1) * ((d : ℝ) * p - 1))
  unfold gEnv spikeEnt
  rcases lt_or_ge s ((d : ℝ) - 1) with hlt | hge
  · have hbpos : 0 < (1 - spikeWt d p) / ((d : ℝ) - 1) := by
      rw [hb]; apply div_pos (by linarith) (by nlinarith)
    have hba : (1 - spikeWt d p) / ((d : ℝ) - 1) ≤ spikeWt d p := by
      rw [hb, ht, div_le_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith [mul_nonneg hs0 (sq_nonneg (d : ℝ))]
    exact (envelope_core hcard lam h0 h1 hab hbpos hba hpq.symm).1
  · -- `p = 1`: a point mass
    have hsm' : s = (d : ℝ) - 1 := le_antisymm hsm hge
    have hv : ∀ i, negMulLog (lam i) = 0 := by
      have hp : p = 1 := by
        have : ((d : ℝ) - 1) * ((d : ℝ) - 1) = ((d : ℝ) - 1) * ((d : ℝ) * p - 1) := by
          rw [← hs2, hsm']; ring
        have := mul_left_cancel₀ (by linarith : (d : ℝ) - 1 ≠ 0) this
        field_simp at this ⊢; nlinarith
      have hle := le_one_of_prob lam h0 h1
      have hsum : ∑ i, (lam i - lam i ^ 2) = 0 := by
        rw [Finset.sum_sub_distrib, h1, ← hpdef, hp]; ring
      have hnn : ∀ i ∈ (univ : Finset ι), 0 ≤ lam i - lam i ^ 2 := fun i _ => by
        nlinarith [h0 i, hle i]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
      intro i
      have : lam i * (lam i - 1) = 0 := by have := hz i (mem_univ i); nlinarith
      rcases mul_eq_zero.1 this with h | h
      · simp [h]
      · simp [show lam i = 1 by linarith]
    simp only [hv, Finset.sum_const_zero]
    rw [ht, hsm']
    have : (1 + ((d : ℝ) - 1)) / d = 1 := by field_simp; ring
    rw [this]; simp

/-- **`lem:seven-fixed-purity-envelope`, equality case.**  For a probability vector `λ` on a `d`-point
set (`d ≥ 2`) with `p = ∑ λ²`, `∑ -λ ln λ = g_d(p)` if and only if `λ` is the one-spike spectrum:
one entry `t_d(p)` and all others `(1 - t_d(p))/(d-1)`. -/
theorem entropy_eq_gEnv_iff {ι : Type*} [Fintype ι] {d : ℕ} (hd : 2 ≤ d)
    (hcard : Fintype.card ι = d) (lam : ι → ℝ) (h0 : ∀ i, 0 ≤ lam i) (h1 : ∑ i, lam i = 1) :
    ∑ i, negMulLog (lam i) = gEnv d (∑ i, lam i ^ 2) ↔
      ∃ i0, lam i0 = spikeWt d (∑ i, lam i ^ 2) ∧
        ∀ i, i ≠ i0 → lam i = (1 - spikeWt d (∑ i, lam i ^ 2)) / ((d : ℝ) - 1) := by
  classical
  set p := ∑ i, lam i ^ 2 with hpdef
  constructor
  swap
  · rintro ⟨i0, ha, hb⟩
    rw [sum_spike hcard lam negMulLog ha hb]; rfl
  intro heq
  have hd' : (1 : ℝ) < d := by exact_mod_cast hd
  have hp1 : 1 / (d : ℝ) ≤ p := sum_sq_ge_inv hcard (by omega) lam h1
  have hp2 : p ≤ 1 := sum_sq_le_one lam h0 h1
  obtain ⟨hs0, hsm, hs2, hab, hpq, hb, ht⟩ := spike_data hd' hp1 hp2
  set s := Real.sqrt (((d : ℝ) - 1) * ((d : ℝ) * p - 1))
  set a := spikeWt d p
  set b := (1 - a) / ((d : ℝ) - 1)
  have hba0 : b ≤ a := by
    rw [hb, ht, div_le_div_iff₀ (by nlinarith) (by linarith)]
    nlinarith [mul_nonneg hs0 (sq_nonneg (d : ℝ))]
  have hle := le_spike hcard lam h1 hab hba0 hpq.symm
  rcases hs0.eq_or_lt with hs | hs
  · -- uniform: every entry is at most `a = 1/d` and they sum to `1 = d a`
    have hab' : a = b := by
      have : a = 1 / d := by rw [ht, ← hs]; ring
      have hm0 : (d : ℝ) - 1 ≠ 0 := by linarith
      have hb' : b = 1 / d := by rw [hb, ← hs, sub_zero]; field_simp
      rw [this, hb']
    have hall : ∀ i, lam i = a := by
      have hsum : ∑ i, (a - lam i) = 0 := by
        rw [Finset.sum_sub_distrib, h1]; simp [hcard]; rw [hab'] at hab ⊢; linarith
      have hnn : ∀ i ∈ (univ : Finset ι), 0 ≤ a - lam i := fun i _ => by linarith [hle i]
      have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
      intro i; have := hz i (mem_univ i); linarith
    have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨i0⟩ := this
    exact ⟨i0, hall i0, fun i _ => by rw [hall i, hab']⟩
  rcases lt_or_ge s ((d : ℝ) - 1) with hlt | hge
  · have hbpos : 0 < b := by rw [hb]; apply div_pos (by linarith) (by nlinarith)
    have hba : b < a := by
      rw [hb, ht, div_lt_div_iff₀ (by nlinarith) (by linarith)]
      nlinarith [mul_pos hs (by positivity : (0 : ℝ) < (d : ℝ) ^ 2)]
    have h2 := (envelope_core hcard lam h0 h1 hab hbpos hba.le hpq.symm).2 hba heq
    exact spike_of_two_values hcard lam h1 hab hba.ne' h2
  · -- point mass
    have hsm' : s = (d : ℝ) - 1 := le_antisymm hsm hge
    have ha1 : a = 1 := by rw [ht, hsm']; field_simp; ring
    have hb0 : b = 0 := by simp only [b, ha1, sub_self, zero_div]
    have hp : p = 1 := by
      have : ((d : ℝ) - 1) * ((d : ℝ) - 1) = ((d : ℝ) - 1) * ((d : ℝ) * p - 1) := by
        rw [← hs2, hsm']; ring
      have := mul_left_cancel₀ (by linarith : (d : ℝ) - 1 ≠ 0) this
      field_simp at this ⊢; nlinarith
    have hle1 := le_one_of_prob lam h0 h1
    have hsum : ∑ i, (lam i - lam i ^ 2) = 0 := by
      rw [Finset.sum_sub_distrib, h1, ← hpdef, hp]; ring
    have hnn : ∀ i ∈ (univ : Finset ι), 0 ≤ lam i - lam i ^ 2 := fun i _ => by
      nlinarith [h0 i, hle1 i]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum
    have h2 : ∀ i, lam i = a ∨ lam i = b := by
      intro i
      have : lam i * (lam i - 1) = 0 := by have := hz i (mem_univ i); nlinarith
      rcases mul_eq_zero.1 this with h | h
      · right; rw [hb0, h]
      · left; rw [ha1]; linarith
    exact spike_of_two_values hcard lam h1 hab (by rw [ha1, hb0]; norm_num) h2

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.entropy_le_gEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_le_gEnv

/-- info: 'FormalResearch.FourQubitEntropy.EntropyPurity.entropy_eq_gEnv_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms entropy_eq_gEnv_iff

end FormalResearch.FourQubitEntropy.EntropyPurity

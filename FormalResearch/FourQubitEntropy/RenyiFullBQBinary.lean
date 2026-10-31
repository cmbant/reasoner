import FormalResearch.FourQubitEntropy.RenyiFullBQConv
import FormalResearch.FourQubitEntropy.RenyiFullBQRolle
import FormalResearch.FourQubitEntropy.RenyiSpec

/-!
# The binary quartic lemma at `q_s = 1587/1000`

Paper E, `lem:fqe-binary-quartic` (`renyi_binary_quartic.tex`), with `q = q_s = 1587/1000`.
With `v = (1-2u)²`, `m(v) = ((1+√v)^q + (1-√v)^q)/2`, `f = ln m` and `D = f/((q-1) ln 2)`:

* `bqD_third_pos`: `D''' > 0` on `(0,1)`;
* `bqA_strictMonoOn`: `A(u) = (4u(1-u) - H_q(u,1-u))/(u(1-u)(1-2u)²)` is strictly increasing on `(0,1/2)`;
* `binary_quartic_bound`: a quartic bound `H_q(u,1-u) ≤ 4u(1-u) - a u(1-u)(1-2u)²` at `u = u₀`
  holds on `u₀ ≤ u ≤ 1/2`.

The proof is the paper's real-variable proof (Riccati equation for `x = tanh(qφ)`, the rational bound `x ≤ U`,
two exact Bernstein sign certificates at `q_s`, `G'' > 0` hence `G' > 0`), with a Rolle argument
(`RenyiFullBQRolle.lean`) in place of the Hermite--Genocchi formula for monotonicity.
-/

namespace FormalResearch.FourQubitEntropy.RenyiFull

open Filter Topology

/-- `q_s` as a literal (the exponent of this file). -/
noncomputable def qBQ : ℝ := 1587 / 1000

/-- `F(s) = ln((1+s)^q + (1-s)^q)`. -/
noncomputable def bqFs (q s : ℝ) : ℝ := Real.log ((1 + s) ^ q + (1 - s) ^ q)

theorem hasDerivAt_bqFs {q s : ℝ} (hs : |s| < 1) :
    HasDerivAt (bqFs q) (q * (bqx q s - s) / (1 - s ^ 2)) s := by
  have h1 := abs_lt.1 hs
  have hp : (0 : ℝ) < 1 + s := by linarith
  have hm : (0 : ℝ) < 1 - s := by linarith
  have ha : HasDerivAt (fun s : ℝ => (1 + s) ^ q) (q * (1 + s) ^ q / (1 + s)) s := by
    have := ((hasDerivAt_id s).const_add 1).rpow_const (p := q) (Or.inl hp.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one hp.ne']
    ring
  have hb : HasDerivAt (fun s : ℝ => (1 - s) ^ q) (-(q * (1 - s) ^ q / (1 - s))) s := by
    have := ((hasDerivAt_id s).const_sub 1).rpow_const (p := q) (Or.inl hm.ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one hm.ne']
    ring
  have hden := bq_denom_pos hs q
  have := (ha.add hb).log hden.ne'
  refine this.congr_deriv ?_
  simp only [Pi.add_apply]
  unfold bqx
  have ha0 : 0 < (1 + s) ^ q := Real.rpow_pos_of_pos hp q
  have hb0 : 0 < (1 - s) ^ q := Real.rpow_pos_of_pos hm q
  have h2 : (1 : ℝ) - s ^ 2 = (1 + s) * (1 - s) := by ring
  rw [h2]
  field_simp
  ring

/-- `f(v) = ln m_q(v)`, `m_q(v) = ((1+√v)^q + (1-√v)^q)/2`. -/
noncomputable def bqf (q v : ℝ) : ℝ := bqFs q (Real.sqrt v) - Real.log 2

/-- `D(v) = f(v)/((q-1) ln 2)`. -/
noncomputable def bqD (q v : ℝ) : ℝ := bqf q v / ((q - 1) * Real.log 2)

theorem hasDerivAt_bqf {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (bqf q) (bqF1 q (Real.sqrt v)) v := by
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hs1 : Real.sqrt v < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hv0.le hv1
  have hs : |Real.sqrt v| < 1 := by rw [abs_lt]; constructor <;> linarith
  have h := (hasDerivAt_bqFs (q := q) hs).comp v (Real.hasDerivAt_sqrt hv0.ne')
  have := h.sub_const (Real.log 2)
  refine this.congr_deriv ?_
  unfold bqF1
  have : 1 - Real.sqrt v ^ 2 ≠ 0 := by nlinarith
  field_simp

theorem hasDerivAt_bqF1_sqrt {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun w => bqF1 q (Real.sqrt w)) (bqG q (Real.sqrt v)) v := by
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hs1 : Real.sqrt v < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hv0.le hv1
  have h := (hasDerivAt_bqF1 (q := q) hs0 hs1).comp v (Real.hasDerivAt_sqrt hv0.ne')
  refine h.congr_deriv ?_
  field_simp

theorem hasDerivAt_bqG_sqrt {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun w => bqG q (Real.sqrt w)) (bqG1 q (Real.sqrt v) / (2 * Real.sqrt v)) v := by
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hs1 : Real.sqrt v < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt hv0.le hv1
  have h := (hasDerivAt_bqG (q := q) hs0 hs1).comp v (Real.hasDerivAt_sqrt hv0.ne')
  refine h.congr_deriv ?_
  simp only [one_div]
  ring

/-! ### `D`, its derivatives, and the third derivative -/

theorem hasDerivAt_bqD {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (bqD q) (bqF1 q (Real.sqrt v) / ((q - 1) * Real.log 2)) v :=
  (hasDerivAt_bqf hv0 hv1).div_const _

theorem hasDerivAt_bqD1 {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun w => bqF1 q (Real.sqrt w) / ((q - 1) * Real.log 2))
      (bqG q (Real.sqrt v) / ((q - 1) * Real.log 2)) v :=
  (hasDerivAt_bqF1_sqrt hv0 hv1).div_const _

theorem hasDerivAt_bqD2 {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt (fun w => bqG q (Real.sqrt w) / ((q - 1) * Real.log 2))
      (bqG1 q (Real.sqrt v) / (2 * Real.sqrt v) / ((q - 1) * Real.log 2)) v :=
  (hasDerivAt_bqG_sqrt hv0 hv1).div_const _

theorem deriv_bqD {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    deriv (bqD q) v = bqF1 q (Real.sqrt v) / ((q - 1) * Real.log 2) :=
  (hasDerivAt_bqD hv0 hv1).deriv

theorem deriv_bqD_eventually {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    deriv (bqD q) =ᶠ[𝓝 v] fun w => bqF1 q (Real.sqrt w) / ((q - 1) * Real.log 2) := by
  filter_upwards [Ioo_mem_nhds hv0 hv1] with w hw
  exact deriv_bqD hw.1 hw.2

theorem deriv2_bqD {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    deriv (deriv (bqD q)) v = bqG q (Real.sqrt v) / ((q - 1) * Real.log 2) := by
  rw [(deriv_bqD_eventually hv0 hv1).deriv_eq]
  exact (hasDerivAt_bqD1 hv0 hv1).deriv

theorem deriv2_bqD_eventually {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    deriv (deriv (bqD q)) =ᶠ[𝓝 v] fun w => bqG q (Real.sqrt w) / ((q - 1) * Real.log 2) := by
  filter_upwards [Ioo_mem_nhds hv0 hv1] with w hw
  exact deriv2_bqD hw.1 hw.2

theorem deriv3_bqD {q v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    deriv (deriv (deriv (bqD q))) v =
      bqG1 q (Real.sqrt v) / (2 * Real.sqrt v) / ((q - 1) * Real.log 2) := by
  rw [(deriv2_bqD_eventually hv0 hv1).deriv_eq]
  exact (hasDerivAt_bqD2 hv0 hv1).deriv

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem qBQ_sub_one_pos : 0 < qBQ - 1 := by unfold qBQ; norm_num

theorem sqrt_lt_one_of {v : ℝ} (hv : v < 1) (hv0 : 0 ≤ v) : Real.sqrt v < 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  exact Real.sqrt_lt_sqrt hv0 hv

/-- **`D_q''' > 0` on `(0,1)`** at `q = q_s` (`lem:fqe-binary-quartic`). -/
theorem bqD_third_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    0 < deriv (deriv (deriv (bqD qBQ))) v := by
  rw [deriv3_bqD hv0 hv1]
  have hs0 : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hs1 : Real.sqrt v < 1 := sqrt_lt_one_of hv1 hv0.le
  have := bqG1_pos hs0 hs1
  have hc : 0 < (qBQ - 1) * Real.log 2 := mul_pos qBQ_sub_one_pos log_two_pos'
  have e : qBQ = 1587 / 1000 := rfl
  rw [e] at hc ⊢
  positivity

theorem bqG_strictMonoOn : StrictMonoOn (bqG (1587 / 1000)) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro s hs
    exact (hasDerivAt_bqG hs.1 hs.2).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    rw [(hasDerivAt_bqG hs.1 hs.2).deriv]
    exact bqG1_pos hs.1 hs.2

/-- `D''` is strictly increasing on `(0,1)`. -/
theorem bqD_second_strictMonoOn :
    StrictMonoOn (deriv (deriv (bqD qBQ))) (Set.Ioo 0 1) := by
  intro a ha b hb hab
  rw [deriv2_bqD ha.1 ha.2, deriv2_bqD hb.1 hb.2]
  have hc : 0 < (qBQ - 1) * Real.log 2 := mul_pos qBQ_sub_one_pos log_two_pos'
  have sa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha.1
  have sb1 : Real.sqrt b < 1 := sqrt_lt_one_of hb.2 hb.1.le
  have hsab : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha.1.le hab
  have : bqG qBQ (Real.sqrt a) < bqG qBQ (Real.sqrt b) :=
    bqG_strictMonoOn ⟨sa, hsab.trans sb1⟩ ⟨sa.trans hsab, sb1⟩ hsab
  exact div_lt_div_of_pos_right this hc

/-! ### The binary Rényi entropy and `A_q` -/

/-- The binary Rényi entropy `H_q(u, 1-u)`. -/
noncomputable def binH (q u : ℝ) : ℝ := Real.logb 2 (u ^ q + (1 - u) ^ q) / (1 - q)

theorem renyiSpec_binary (q u : ℝ) : renyiSpec q ![u, 1 - u] = binH q u := by
  unfold renyiSpec binH
  simp [Fin.sum_univ_two]

/-- `D_q(v) = 1 - H_q(u,1-u)` at `v = (1-2u)²`. -/
theorem bqD_binary {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) :
    bqD qBQ ((1 - 2 * u) ^ 2) = 1 - binH qBQ u := by
  have hq : 0 < qBQ := by unfold qBQ; norm_num
  have hs : Real.sqrt ((1 - 2 * u) ^ 2) = 1 - 2 * u := Real.sqrt_sq (by linarith)
  have hS : 0 < (1 - u) ^ qBQ + u ^ qBQ := by
    have := Real.rpow_pos_of_pos hu0 qBQ
    have := Real.rpow_pos_of_pos (show 0 < 1 - u by linarith) qBQ
    linarith
  have e1 : (1 + (1 - 2 * u)) ^ qBQ + (1 - (1 - 2 * u)) ^ qBQ =
      2 ^ qBQ * ((1 - u) ^ qBQ + u ^ qBQ) := by
    have a : (1 + (1 - 2 * u)) = 2 * (1 - u) := by ring
    have b : (1 - (1 - 2 * u)) = 2 * u := by ring
    rw [a, b, Real.mul_rpow (by norm_num) (by linarith), Real.mul_rpow (by norm_num) hu0.le]
    ring
  have hl : Real.log ((1 + (1 - 2 * u)) ^ qBQ + (1 - (1 - 2 * u)) ^ qBQ) =
      qBQ * Real.log 2 + Real.log ((1 - u) ^ qBQ + u ^ qBQ) := by
    rw [e1, Real.log_mul (Real.rpow_pos_of_pos (by norm_num) _).ne' hS.ne', Real.log_rpow (by norm_num)]
  unfold bqD bqf bqFs binH Real.logb
  rw [hs, hl]
  have hlog2 := log_two_pos'
  have hq1 : qBQ - 1 ≠ 0 := (qBQ_sub_one_pos).ne'
  have e2 : u ^ qBQ + (1 - u) ^ qBQ = (1 - u) ^ qBQ + u ^ qBQ := by ring
  rw [e2]
  have h1q : 1 - qBQ ≠ 0 := by intro h; apply hq1; linarith
  field_simp
  ring

/-- `A_q(u) = (4u(1-u) - H_q(u,1-u)) / (u(1-u)(1-2u)²)` at `q = q_s`. -/
noncomputable def bqA (u : ℝ) : ℝ :=
  (4 * u * (1 - u) - binH qBQ u) / (u * (1 - u) * (1 - 2 * u) ^ 2)

theorem bqA_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1 / 2) :
    bqA u = 4 * ((fun v => bqD qBQ v - v) ((1 - 2 * u) ^ 2) /
      ((1 - 2 * u) ^ 2 * (1 - (1 - 2 * u) ^ 2))) := by
  simp only
  rw [bqD_binary hu0 hu1.le]
  unfold bqA
  have h1 : (1 - 2 * u) ≠ 0 := by intro h; linarith
  have h2 : u ≠ 0 := hu0.ne'
  have h3 : 1 - u ≠ 0 := by intro h; linarith
  have e : 1 - (1 - 2 * u) ^ 2 = 4 * u * (1 - u) := by ring
  rw [e]
  field_simp
  ring

theorem bqD_continuousOn : ContinuousOn (bqD qBQ) (Set.Icc 0 1) := by
  have hq : 0 ≤ qBQ := by unfold qBQ; norm_num
  have hc : Continuous (fun v : ℝ => (1 + Real.sqrt v) ^ qBQ + (1 - Real.sqrt v) ^ qBQ) := by
    apply Continuous.add
    · exact (continuous_const.add Real.continuous_sqrt).rpow_const (fun _ => Or.inr hq)
    · exact (continuous_const.sub Real.continuous_sqrt).rpow_const (fun _ => Or.inr hq)
  have hlog : ContinuousOn (fun v : ℝ => Real.log ((1 + Real.sqrt v) ^ qBQ + (1 - Real.sqrt v) ^ qBQ))
      (Set.Icc 0 1) := by
    apply ContinuousOn.log hc.continuousOn
    intro v hv
    have a : 0 < (1 + Real.sqrt v) ^ qBQ := Real.rpow_pos_of_pos (by positivity) _
    have b : 0 ≤ (1 - Real.sqrt v) ^ qBQ := by
      apply Real.rpow_nonneg
      have := Real.sqrt_le_one.2 hv.2
      linarith
    linarith
  unfold bqD bqf bqFs
  exact (hlog.sub continuousOn_const).div_const _

theorem bqD_zero : bqD qBQ 0 = 0 := by
  unfold bqD bqf bqFs
  norm_num

theorem bqD_one : bqD qBQ 1 = 1 := by
  have hq : qBQ ≠ 0 := by unfold qBQ; norm_num
  unfold bqD bqf bqFs
  have h2 : Real.log ((2 : ℝ) ^ qBQ) = qBQ * Real.log 2 := Real.log_rpow (by norm_num) _
  simp only [Real.sqrt_one, sub_self, Real.zero_rpow hq, add_zero, one_add_one_eq_two]
  rw [h2]
  have := qBQ_sub_one_pos.ne'
  have := log_two_pos'.ne'
  field_simp

/-- **`A_q` is strictly increasing on `(0, 1/2)`** at `q = q_s` (`lem:fqe-binary-quartic`). -/
theorem bqA_strictMonoOn : StrictMonoOn bqA (Set.Ioo 0 (1 / 2)) := by
  have hanti := divdiff_strictAntiOn (g := fun v => bqD qBQ v - v)
    (g1 := fun v => bqF1 qBQ (Real.sqrt v) / ((qBQ - 1) * Real.log 2) - 1)
    (g2 := fun v => bqG qBQ (Real.sqrt v) / ((qBQ - 1) * Real.log 2))
    (bqD_continuousOn.sub continuousOn_id) (by simp [bqD_zero]) (by simp [bqD_one])
    (fun v hv => (hasDerivAt_bqD hv.1 hv.2).sub (hasDerivAt_id v))
    (fun v hv => ((hasDerivAt_bqD1 hv.1 hv.2).sub_const 1))
    (by
      intro a ha b hb hab
      have hc : 0 < (qBQ - 1) * Real.log 2 := mul_pos qBQ_sub_one_pos log_two_pos'
      have sa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha.1
      have sb1 : Real.sqrt b < 1 := sqrt_lt_one_of hb.2 hb.1.le
      have hsab : Real.sqrt a < Real.sqrt b := Real.sqrt_lt_sqrt ha.1.le hab
      exact div_lt_div_of_pos_right (bqG_strictMonoOn ⟨sa, hsab.trans sb1⟩ ⟨sa.trans hsab, sb1⟩ hsab) hc)
  intro u hu u' hu' huu'
  have hv : ∀ w : ℝ, w ∈ Set.Ioo (0 : ℝ) (1 / 2) → (1 - 2 * w) ^ 2 ∈ Set.Ioo (0 : ℝ) 1 := by
    intro w hw
    constructor
    · have : 0 < 1 - 2 * w := by linarith [hw.2]
      positivity
    · nlinarith [hw.1, hw.2]
  have := hanti (hv u' hu') (hv u hu) (by nlinarith [hu.1, hu.2, hu'.1, hu'.2])
  rw [bqA_eq hu.1 hu.2, bqA_eq hu'.1 hu'.2]
  simp only at this ⊢
  linarith

theorem binH_half : binH qBQ (1 / 2) = 1 := by
  have h1 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  unfold binH
  rw [h1]
  have e : (1 / 2 : ℝ) ^ qBQ + (1 / 2) ^ qBQ = (2 : ℝ) ^ (1 - qBQ) := by
    rw [Real.rpow_sub (by norm_num), one_div, Real.inv_rpow (by norm_num)]
    simp only [Real.rpow_one]
    field_simp
    ring
  rw [e, Real.logb_rpow (by norm_num) (by norm_num)]
  have : (1 - qBQ) ≠ 0 := by have := qBQ_sub_one_pos; intro h; linarith
  field_simp

/-- **The quartic bound from an endpoint value.** If `a ≤ A_q(u₀)` then
`H_q(u,1-u) ≤ 4u(1-u) - a u(1-u)(1-2u)²` for all `u₀ ≤ u ≤ 1/2` (`q = q_s`). -/
theorem binary_quartic_bound {u₀ u a : ℝ} (hu0 : 0 < u₀) (hu0h : u₀ < 1 / 2) (ha : a ≤ bqA u₀)
    (h1 : u₀ ≤ u) (h2 : u ≤ 1 / 2) :
    binH qBQ u ≤ 4 * u * (1 - u) - a * (u * (1 - u) * (1 - 2 * u) ^ 2) := by
  rcases h2.eq_or_lt with h | h
  · subst h
    rw [binH_half]
    norm_num
  · have hA : bqA u₀ ≤ bqA u := by
      rcases h1.eq_or_lt with e | e
      · rw [e]
      · exact (bqA_strictMonoOn ⟨hu0, hu0h⟩ ⟨hu0.trans_le h1, h⟩ e).le
    have hd : 0 < u * (1 - u) * (1 - 2 * u) ^ 2 := by
      have : 0 < 1 - 2 * u := by linarith
      have : 0 < u := hu0.trans_le h1
      have : 0 < 1 - u := by linarith
      positivity
    have hAu : bqA u * (u * (1 - u) * (1 - 2 * u) ^ 2) = 4 * u * (1 - u) - binH qBQ u := by
      unfold bqA; exact div_mul_cancel₀ _ hd.ne'
    nlinarith [mul_le_mul_of_nonneg_right (ha.trans hA) hd.le]

/-- The same in terms of `renyiSpec` of the two-point spectrum, at `q = 1587/1000`. -/
theorem binary_quartic_bound_spec {u₀ u a : ℝ} (hu0 : 0 < u₀) (hu0h : u₀ < 1 / 2) (ha : a ≤ bqA u₀)
    (h1 : u₀ ≤ u) (h2 : u ≤ 1 / 2) :
    renyiSpec (1587 / 1000 : ℝ) ![u, 1 - u] ≤ 4 * u * (1 - u) - a * (u * (1 - u) * (1 - 2 * u) ^ 2) := by
  have := binary_quartic_bound hu0 hu0h ha h1 h2
  rw [renyiSpec_binary]
  exact this

end FormalResearch.FourQubitEntropy.RenyiFull

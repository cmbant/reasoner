module

public import FormalResearch.Special.DiscreteLgSite
public import FormalResearch.Special.DiscreteJacobiCalculus

/-!
# Discrete Liouville-Green, M2b: the bulk datum, the pair `w cos P`, `w sin P`, its row defect and Casoratian

**Datum.**  `DlgData A θ w Θ U lo hi M`: on an open interval `U`, `A, θ, w ∈ C²`, `Θ' = θ`, `lo ≤ A, w ≤ hi` with `lo > 0`, the first two derivatives of
`A, θ, w` bounded by `M`, and the **amplitude relation** `A w² sin θ = 1`.  (For a Jacobi chain with `c = 2A cos θ`, `θ = arccos u` is the local phase
advance per step, `Θ = ∫θ` the Liouville-Green phase and `w = (A sin θ)^{-1/2}` the amplitude; `DlgData.transport` is the transport
equation `(A w² sin θ)' = 0`.)

**Lattice.**  `q_k = q₀ + k h`, `P_k = Θ(q_k)/h`, pair `φ_k = w(q_k) cos P_k`, `ψ_k = w(q_k) sin P_k` (`dlgPhi`, `dlgPsi`).

**Results.**  For coefficients with `|a_k - A(q_k - h/2)| ≤ E h²`, `|c_k - 2A(q_k) cos θ(q_k)| ≤ E h²` and `0 < h ≤ 1`, with `R = dlgR lo hi M E`:
* `dlg_row_defect`: `|jac a c φ|, |jac a c ψ| ≤ 70 hi R⁴ h²` on every row whose three sites lie in `U`;
* `dlg_cas_bound`: `|cas a φ ψ - 1| ≤ 3 R⁴ h` on every bond whose two sites lie in `U`.

Only first-order jets are used: the `O(h)` terms of the defect cancel by `transport` and `Re`, `Im` of the one complex defect are the second difference
and the odd difference `X₂`.  **Claim class: proved** (explicit constants).  **Not formalised:** the phase `Θ` to second order, i.e. the `h²` correction
`ϖ` of the Liouville-Green phase.
-/

@[expose] public section

open Set Finset FormalResearch.DiscreteAiry

namespace FormalResearch.Special

/-- The bulk Liouville-Green datum (see the module docstring). -/
structure DlgData (A θ w Θ : ℝ → ℝ) (U : Set ℝ) (lo hi M : ℝ) : Prop where
  isOpen : IsOpen U
  convex : Convex ℝ U
  lo_pos : 0 < lo
  M_nonneg : 0 ≤ M
  A2 : ContDiffOn ℝ 2 A U
  θ2 : ContDiffOn ℝ 2 θ U
  w2 : ContDiffOn ℝ 2 w U
  Θd : ∀ t ∈ U, HasDerivAt Θ (θ t) t
  Ab : ∀ t ∈ U, lo ≤ A t ∧ A t ≤ hi
  wb : ∀ t ∈ U, lo ≤ w t ∧ w t ≤ hi
  jb : ∀ t ∈ U, |deriv A t| ≤ M ∧ |deriv (deriv A) t| ≤ M ∧ |deriv θ t| ≤ M ∧ |deriv (deriv θ) t| ≤ M ∧
    |deriv w t| ≤ M ∧ |deriv (deriv w) t| ≤ M
  rel : ∀ t ∈ U, A t * w t ^ 2 * Real.sin (θ t) = 1

/-- **Transport equation** `2 (A'/2 + A w'/w) sin θ + A θ' cos θ = 0`, i.e. `(A w² sin θ)' = 0`. -/
lemma DlgData.transport {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M : ℝ} (D : DlgData A θ w Θ U lo hi M) {t : ℝ}
    (ht : t ∈ U) :
    2 * (deriv A t / 2 + A t * (deriv w t / w t)) * Real.sin (θ t) + A t * deriv θ t * Real.cos (θ t) = 0 := by
  have hA := (dlg_hasDeriv2 D.isOpen D.A2).1 t ht
  have hθ := (dlg_hasDeriv2 D.isOpen D.θ2).1 t ht
  have hw := (dlg_hasDeriv2 D.isOpen D.w2).1 t ht
  have hF := (hA.mul (hw.pow 2)).mul hθ.sin
  have hF0 : HasDerivAt (fun s => A s * w s ^ 2 * Real.sin (θ s)) 0 t :=
    (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq
      (by filter_upwards [D.isOpen.mem_nhds ht] with s hs using D.rel s hs)
  have h0 := hF.unique hF0
  have hw0 : w t ≠ 0 := (D.wb t ht).1.trans_lt' D.lo_pos |>.ne'
  have hw0' : 0 < w t := lt_of_lt_of_le D.lo_pos (D.wb t ht).1
  have key : (deriv A t * w t ^ 2 + A t * (2 * w t * deriv w t)) * Real.sin (θ t) +
      A t * w t ^ 2 * (Real.cos (θ t) * deriv θ t) = 0 := by
    simp only [Pi.mul_apply, Pi.pow_apply] at h0
    norm_num at h0
    linear_combination h0
  have e : 2 * (deriv A t / 2 + A t * (deriv w t / w t)) * Real.sin (θ t) + A t * deriv θ t * Real.cos (θ t) =
      (w t)⁻¹ ^ 2 * ((deriv A t * w t ^ 2 + A t * (2 * w t * deriv w t)) * Real.sin (θ t) +
        A t * w t ^ 2 * (Real.cos (θ t) * deriv θ t)) := by
    field_simp
  rw [e, key, mul_zero]

/-- The lattice `q_k = q₀ + k h`. -/
def dlgQ (q0 h : ℝ) (k : ℤ) : ℝ := q0 + (k : ℝ) * h

/-- The phase `P_k = Θ(q_k)/h`. -/
noncomputable def dlgP (Θ : ℝ → ℝ) (q0 h : ℝ) (k : ℤ) : ℝ := Θ (dlgQ q0 h k) / h

/-- `φ_k = w(q_k) cos P_k`. -/
noncomputable def dlgPhi (w Θ : ℝ → ℝ) (q0 h : ℝ) (k : ℤ) : ℝ := w (dlgQ q0 h k) * Real.cos (dlgP Θ q0 h k)

/-- `ψ_k = w(q_k) sin P_k`. -/
noncomputable def dlgPsi (w Θ : ℝ → ℝ) (q0 h : ℝ) (k : ℤ) : ℝ := w (dlgQ q0 h k) * Real.sin (dlgP Θ q0 h k)

lemma dlgQ_succ (q0 h : ℝ) (k : ℤ) : dlgQ q0 h (k + 1) = dlgQ q0 h k + h := by unfold dlgQ; push_cast; ring

lemma dlgQ_pred (q0 h : ℝ) (k : ℤ) : dlgQ q0 h (k - 1) = dlgQ q0 h k - h := by unfold dlgQ; push_cast; ring

/-- The constant `S = M/lo`, `m' = 1 + hi + M + S`, `cB = m'² + (E + M/4)(2m' + S) + 2 m' S`, `R = 1 + hi + 2M + E + cB + hi S`. -/
noncomputable def dlgR (lo hi M E : ℝ) : ℝ :=
  1 + hi + 2 * M + E + ((1 + hi + M + M / lo) ^ 2 + (E + M / 4) * (2 * (1 + hi + M + M / lo) + M / lo) +
    2 * (1 + hi + M + M / lo) * (M / lo)) + hi * (M / lo)

lemma dlgR_ge_one {lo hi M E : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hM : 0 ≤ M) (hE : 0 ≤ E) : 1 ≤ dlgR lo hi M E := by
  unfold dlgR
  have h1 : 0 ≤ M / lo := by positivity
  have : 0 ≤ (1 + hi + M + M / lo) ^ 2 + (E + M / 4) * (2 * (1 + hi + M + M / lo) + M / lo) +
    2 * (1 + hi + M + M / lo) * (M / lo) := by positivity
  have : 0 ≤ hi * (M / lo) := by positivity
  linarith

lemma dlgR_bounds {lo hi M E : ℝ} (hlo : 0 < lo) (hhi : 0 ≤ hi) (hM : 0 ≤ M) (hE : 0 ≤ E) :
    hi ≤ dlgR lo hi M E ∧ M ≤ dlgR lo hi M E ∧ E ≤ dlgR lo hi M E ∧ 2 * M + hi * (M / lo) ≤ dlgR lo hi M E := by
  unfold dlgR
  have p1 : 0 ≤ (1 + hi + M + M / lo) ^ 2 + (E + M / 4) * (2 * (1 + hi + M + M / lo) + M / lo) +
    2 * (1 + hi + M + M / lo) * (M / lo) := by positivity
  have p2 : 0 ≤ hi * (M / lo) := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The midpoint of `q` and `q + d` lies in the convex set `U`. -/
lemma dlg_mid_mem {U : Set ℝ} (hU : Convex ℝ U) {q d : ℝ} (hq : q ∈ U) (hqd : q + d ∈ U) : q + d / 2 ∈ U := by
  have := hU hq hqd (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  convert this using 1
  simp only [smul_eq_mul]; ring

/-- **Signed one-step jets** (`ε = ±1`, step `ε h`): the coefficient-weighted amplitude ratio and the phase increment. -/
lemma dlg_jets {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M E : ℝ} (D : DlgData A θ w Θ U lo hi M) (hE : 0 ≤ E)
    {q h ε ad : ℝ} (hε : ε = 1 ∨ ε = -1) (hq : q ∈ U) (hqd : q + ε * h ∈ U) (hh : 0 < h) (h1 : h ≤ 1)
    (had : |ad - A (q + ε * h / 2)| ≤ E * h ^ 2) :
    |ad * w (q + ε * h) / w q - A q - h * (ε * (deriv A q / 2 + A q * (deriv w q / w q)))| ≤ dlgR lo hi M E * h ^ 2 ∧
    |ε * (Θ (q + ε * h) - Θ q) / h - θ q - h * (ε * deriv θ q) / 2| ≤ dlgR lo hi M E * h ^ 2 := by
  have hε2 : ε ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hεa : |ε| = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hlo := D.lo_pos
  have hM := D.M_nonneg
  have hhi : 0 ≤ hi := (hlo.le.trans (D.Ab q hq).1).trans (D.Ab q hq).2
  have hRge := dlgR_ge_one hlo hhi hM hE
  obtain ⟨jA, jA2, jθ, jθ2, jw, jw2⟩ := D.jb q hq
  have hmid := dlg_mid_mem D.convex hq (by simpa [mul_comm] using hqd : q + (ε * h) ∈ U)
  have hA1 := (dlg_hasDeriv2 D.isOpen D.A2)
  have hθ1 := (dlg_hasDeriv2 D.isOpen D.θ2)
  have hw1 := (dlg_hasDeriv2 D.isOpen D.w2)
  have hεh : |ε * h| = h := by rw [abs_mul, hεa, one_mul, abs_of_pos hh]
  have hεh2 : (ε * h) ^ 2 = h ^ 2 := by rw [mul_pow, hε2, one_mul]
  have hw0 : 0 < w q := lt_of_lt_of_le hlo (D.wb q hq).1
  -- jets of A at the midpoint
  have tA : |A (q + ε * h / 2) - A q - (ε * h / 2) * deriv A q| ≤ M * h ^ 2 / 4 := by
    have := dlg_taylor2 D.convex hA1.1 hA1.2 (fun t ht => (D.jb t ht).2.1) hq hmid
    have e : q + ε * h / 2 - q = ε * h / 2 := by ring
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [div_pow, mul_pow, hε2]; ring
  -- jets of w
  have tw : |w (q + ε * h) - w q - (ε * h) * deriv w q| ≤ M * h ^ 2 := by
    have := dlg_taylor2 D.convex hw1.1 hw1.2 (fun t ht => (D.jb t ht).2.2.2.2.2) hq hqd
    have e : q + ε * h - q = ε * h := by ring
    rw [e] at this
    exact this.trans (le_of_eq (by rw [hεh2]))
  -- coefficient jet
  have jx : |ad - A q - h * (ε * deriv A q / 2)| ≤ (E + M / 4) * h ^ 2 := by
    have e : ad - A q - h * (ε * deriv A q / 2) = (ad - A (q + ε * h / 2)) + (A (q + ε * h / 2) - A q - (ε * h / 2) * deriv A q) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    linarith
  -- ratio jet
  have jy : |w (q + ε * h) / w q - 1 - h * (ε * (deriv w q / w q))| ≤ (M / lo) * h ^ 2 := by
    have e : w (q + ε * h) / w q - 1 - h * (ε * (deriv w q / w q)) =
        (w (q + ε * h) - w q - (ε * h) * deriv w q) / w q := by field_simp
    rw [e, abs_div, abs_of_pos hw0, div_le_iff₀ hw0]
    calc |w (q + ε * h) - w q - ε * h * deriv w q| ≤ M * h ^ 2 := tw
      _ = (M / lo) * h ^ 2 * lo := by field_simp
      _ ≤ (M / lo) * h ^ 2 * w q := by
          gcongr
          exact (D.wb q hq).1
  have hS : 0 ≤ M / lo := by positivity
  have hAq := D.Ab q hq
  have hσ : |deriv w q / w q| ≤ M / lo := by
    rw [abs_div, abs_of_pos hw0]
    calc |deriv w q| / w q ≤ M / w q := by gcongr
      _ ≤ M / lo := by gcongr; exact (D.wb q hq).1
  have hjm := dlg_jet_mul (x := ad) (y := w (q + ε * h) / w q) (x0 := A q) (x1 := ε * deriv A q / 2) (y0 := 1)
    (y1 := ε * (deriv w q / w q)) (h := h) (m := 1 + hi + M + M / lo) (cx := E + M / 4) (cy := M / lo) hh h1
    (by rw [abs_of_pos (hlo.trans_le hAq.1)]; linarith [hAq.2])
    (by
      rw [abs_div, abs_mul, hεa, one_mul, abs_two]; linarith)
    (by rw [abs_one]; linarith)
    (by rw [abs_mul, hεa, one_mul]; linarith)
    jx jy
  have hR1 : (1 + hi + M + M / lo) ^ 2 + (E + M / 4) * (2 * (1 + hi + M + M / lo) + M / lo) +
      2 * (1 + hi + M + M / lo) * (M / lo) ≤ dlgR lo hi M E := by
    unfold dlgR
    have : 0 ≤ hi * (M / lo) := by positivity
    linarith
  have hbd : |ad * w (q + ε * h) / w q - A q - h * (ε * (deriv A q / 2 + A q * (deriv w q / w q)))| ≤
      dlgR lo hi M E * h ^ 2 := by
    have e : ad * w (q + ε * h) / w q - A q - h * (ε * (deriv A q / 2 + A q * (deriv w q / w q))) =
        ad * (w (q + ε * h) / w q) - A q * 1 - h * (A q * (ε * (deriv w q / w q)) + ε * deriv A q / 2 * 1) := by ring
    rw [e]
    refine hjm.trans ?_
    exact mul_le_mul_of_nonneg_right hR1 (sq_nonneg h)
  refine ⟨hbd, ?_⟩
  have t3 := dlg_taylor3 D.convex D.Θd hθ1.1 hθ1.2 (fun t ht => (D.jb t ht).2.2.2.1) hq hqd
  have e3 : q + ε * h - q = ε * h := by ring
  rw [e3, hεh] at t3
  have e4 : ε * (Θ (q + ε * h) - Θ q) / h - θ q - h * (ε * deriv θ q) / 2 =
      ε * (Θ (q + ε * h) - Θ q - (ε * h) * θ q - (ε * h) ^ 2 * deriv θ q / 2) / h := by
    rcases hε with rfl | rfl
    · field_simp
    · field_simp; ring
  rw [e4, abs_div, abs_mul, hεa, one_mul, abs_of_pos hh, div_le_iff₀ hh]
  have hRM : M ≤ dlgR lo hi M E := by
    unfold dlgR
    have : 0 ≤ (1 + hi + M + M / lo) ^ 2 + (E + M / 4) * (2 * (1 + hi + M + M / lo) + M / lo) +
      2 * (1 + hi + M + M / lo) * (M / lo) := by positivity
    have : 0 ≤ hi * (M / lo) := by positivity
    linarith
  calc _ ≤ M * h ^ 3 := t3
    _ ≤ dlgR lo hi M E * h ^ 2 * h := by
        have : M * h ^ 3 = M * h ^ 2 * h := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hRM (sq_nonneg h)) hh.le

lemma dlg_row_id_cos (ap am ck wq wp wm P mp mm : ℝ) (hwq : wq ≠ 0) :
    ap * (wp * Real.cos (P + mp)) + am * (wm * Real.cos (P - mm)) - ck * (wq * Real.cos P) =
      wq * (Real.cos P * ((ap * wp / wq) * Real.cos mp + (am * wm / wq) * Real.cos mm - ck) -
        Real.sin P * ((ap * wp / wq) * Real.sin mp - (am * wm / wq) * Real.sin mm)) := by
  rw [Real.cos_add, Real.cos_sub]
  field_simp
  ring

lemma dlg_row_id_sin (ap am ck wq wp wm P mp mm : ℝ) (hwq : wq ≠ 0) :
    ap * (wp * Real.sin (P + mp)) + am * (wm * Real.sin (P - mm)) - ck * (wq * Real.sin P) =
      wq * (Real.sin P * ((ap * wp / wq) * Real.cos mp + (am * wm / wq) * Real.cos mm - ck) +
        Real.cos P * ((ap * wp / wq) * Real.sin mp - (am * wm / wq) * Real.sin mm)) := by
  rw [Real.sin_add, Real.sin_sub]
  field_simp
  ring

/-- **Row defect of the bulk pair.**  For `0 < h ≤ 1`, a row `k` whose three sites `q_{k-1}, q_k, q_{k+1}` lie in `U`, and coefficients with
`|a_{k+1} - A(q_{k+1} - h/2)|, |a_k - A(q_k - h/2)|, |c_k - 2A(q_k) cos θ(q_k)| ≤ E h²`: both `φ = w cos P` and `ψ = w sin P` have
`|jac a c ·| ≤ 70 hi R⁴ h²` at `k`, `R = dlgR lo hi M E`. -/
theorem dlg_row_defect {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M E : ℝ} (D : DlgData A θ w Θ U lo hi M) (hE : 0 ≤ E)
    {q0 h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) {a c : ℤ → ℝ} {k : ℤ}
    (hk0 : dlgQ q0 h k ∈ U) (hkp : dlgQ q0 h (k + 1) ∈ U) (hkm : dlgQ q0 h (k - 1) ∈ U)
    (hap : |a (k + 1) - A (dlgQ q0 h (k + 1) - h / 2)| ≤ E * h ^ 2)
    (ham : |a k - A (dlgQ q0 h k - h / 2)| ≤ E * h ^ 2)
    (hck : |c k - 2 * A (dlgQ q0 h k) * Real.cos (θ (dlgQ q0 h k))| ≤ E * h ^ 2) :
    |jac a c (dlgPhi w Θ q0 h) k| ≤ 70 * hi * dlgR lo hi M E ^ 4 * h ^ 2 ∧
      |jac a c (dlgPsi w Θ q0 h) k| ≤ 70 * hi * dlgR lo hi M E ^ 4 * h ^ 2 := by
  have hlo := D.lo_pos
  have hM := D.M_nonneg
  set q := dlgQ q0 h k with hqdef
  have hqp : dlgQ q0 h (k + 1) = q + h := dlgQ_succ q0 h k
  have hqm : dlgQ q0 h (k - 1) = q - h := dlgQ_pred q0 h k
  rw [hqp] at hkp hap
  rw [hqm] at hkm
  have hhi : 0 ≤ hi := (hlo.le.trans (D.Ab q hk0).1).trans (D.Ab q hk0).2
  have hRb : hi ≤ dlgR lo hi M E ∧ M ≤ dlgR lo hi M E ∧ E ≤ dlgR lo hi M E ∧ 2 * M + hi * (M / lo) ≤ dlgR lo hi M E :=
    dlgR_bounds hlo hhi hM hE
  set R := dlgR lo hi M E with hRdef
  have hR1 : 1 ≤ R := dlgR_ge_one hlo hhi hM hE
  have hw0 : 0 < w q := lt_of_lt_of_le hlo (D.wb q hk0).1
  have hAq := D.Ab q hk0
  have hwq := D.wb q hk0
  obtain ⟨jA, -, jθ, -, jw, -⟩ := D.jb q hk0
  -- jets (plus side, ε = 1; minus side, ε = -1)
  have hap' : |a (k + 1) - A (q + 1 * h / 2)| ≤ E * h ^ 2 := by
    have e : q + 1 * h / 2 = q + h - h / 2 := by ring
    rw [e]; exact hap
  have ham' : |a k - A (q + -1 * h / 2)| ≤ E * h ^ 2 := by
    have e : q + -1 * h / 2 = q - h / 2 := by ring
    rw [e]; exact ham
  obtain ⟨jBp, jmp⟩ := dlg_jets D hE (ε := 1) (ad := a (k + 1)) (Or.inl rfl) hk0 (by simpa using hkp) hh h1 hap'
  obtain ⟨jBm, jmm⟩ := dlg_jets D hE (ε := -1) (ad := a k) (Or.inr rfl) hk0 (by simpa [sub_eq_add_neg] using hkm) hh h1 ham'
  set B1 := deriv A q / 2 + A q * (deriv w q / w q) with hB1
  have hσ : |deriv w q / w q| ≤ M / lo := by
    rw [abs_div, abs_of_pos hw0]
    calc |deriv w q| / w q ≤ M / w q := by gcongr
      _ ≤ M / lo := by gcongr; exact hwq.1
  have hB1b : |B1| ≤ R := by
    have : |B1| ≤ M / 2 + hi * (M / lo) := by
      refine (abs_add_le _ _).trans ?_
      refine add_le_add ?_ ?_
      · rw [abs_div, abs_two]; linarith
      · rw [abs_mul, abs_of_pos (hlo.trans_le hAq.1)]
        exact mul_le_mul hAq.2 hσ (abs_nonneg _) hhi
    linarith [hRb.2.2.2]
  have hA0 : |A q| ≤ R := by rw [abs_of_pos (hlo.trans_le hAq.1)]; linarith [hAq.2, hRb.1]
  have ht1 : |deriv θ q| ≤ R := jθ.trans hRb.2.1
  have htr := D.transport hk0
  simp only [one_mul, neg_mul, ← sub_eq_add_neg] at jBp jBm jmp jmm
  have hmp : |(Θ (q + h) - Θ q) / h - θ q - h * deriv θ q / 2| ≤ R * h ^ 2 := by
    convert jmp using 2
  have hmm : |(Θ q - Θ (q - h)) / h - θ q + h * deriv θ q / 2| ≤ R * h ^ 2 := by
    convert jmm using 2
    ring
  have hBp : |a (k + 1) * w (q + h) / w q - A q - h * B1| ≤ R * h ^ 2 := jBp
  have hBm : |a k * w (q - h) / w q - A q + h * B1| ≤ R * h ^ 2 := by
    convert jBm using 2
    ring
  have hck' : |c k - 2 * A q * Real.cos (θ q)| ≤ R * h ^ 2 :=
    hck.trans (mul_le_mul_of_nonneg_right hRb.2.2.1 (sq_nonneg h))
  have hX1 := dlg_X1 hR1 hh h1 hA0 hB1b ht1 hBp hBm hmp hmm hck'
  have hX2 := dlg_X2 hR1 hh h1 hA0 hB1b ht1 hBp hBm hmp hmm htr
  -- the lattice phases
  have hP1 : dlgP Θ q0 h (k + 1) = dlgP Θ q0 h k + (Θ (q + h) - Θ q) / h := by
    unfold dlgP; rw [hqp]; ring
  have hP2 : dlgP Θ q0 h (k - 1) = dlgP Θ q0 h k - (Θ q - Θ (q - h)) / h := by
    unfold dlgP; rw [hqm]; ring
  set P := dlgP Θ q0 h k
  have hφ : jac a c (dlgPhi w Θ q0 h) k = w q * (Real.cos P * ((a (k + 1) * w (q + h) / w q) *
      Real.cos ((Θ (q + h) - Θ q) / h) + (a k * w (q - h) / w q) * Real.cos ((Θ q - Θ (q - h)) / h) - c k) -
      Real.sin P * ((a (k + 1) * w (q + h) / w q) * Real.sin ((Θ (q + h) - Θ q) / h) -
        (a k * w (q - h) / w q) * Real.sin ((Θ q - Θ (q - h)) / h))) := by
    unfold jac dlgPhi
    rw [hP1, hP2, hqp, hqm, ← hqdef]
    exact dlg_row_id_cos _ _ _ _ _ _ _ _ _ hw0.ne'
  have hψ : jac a c (dlgPsi w Θ q0 h) k = w q * (Real.sin P * ((a (k + 1) * w (q + h) / w q) *
      Real.cos ((Θ (q + h) - Θ q) / h) + (a k * w (q - h) / w q) * Real.cos ((Θ q - Θ (q - h)) / h) - c k) +
      Real.cos P * ((a (k + 1) * w (q + h) / w q) * Real.sin ((Θ (q + h) - Θ q) / h) -
        (a k * w (q - h) / w q) * Real.sin ((Θ q - Θ (q - h)) / h))) := by
    unfold jac dlgPsi
    rw [hP1, hP2, hqp, hqm, ← hqdef]
    exact dlg_row_id_sin _ _ _ _ _ _ _ _ _ hw0.ne'
  have hcP := Real.abs_cos_le_one P
  have hsP := Real.abs_sin_le_one P
  have hfin : ∀ T : ℝ, |T| ≤ 1 → ∀ T' : ℝ, |T'| ≤ 1 → ∀ X1 X2 : ℝ, |X1| ≤ 35 * R ^ 4 * h ^ 2 →
      |X2| ≤ 35 * R ^ 4 * h ^ 2 → |w q * (T * X1 + T' * X2)| ≤ 70 * hi * R ^ 4 * h ^ 2 := by
    intro T hT T' hT' X1 X2 hX1 hX2
    rw [abs_mul, abs_of_pos hw0]
    have b1 := dlg_mul_le hT hX1
    have b2 := dlg_mul_le hT' hX2
    have : |T * X1 + T' * X2| ≤ 70 * R ^ 4 * h ^ 2 := by
      refine (abs_add_le _ _).trans ?_
      linarith
    calc w q * |T * X1 + T' * X2| ≤ hi * (70 * R ^ 4 * h ^ 2) :=
          mul_le_mul hwq.2 this (abs_nonneg _) hhi
      _ = 70 * hi * R ^ 4 * h ^ 2 := by ring
  constructor
  · rw [hφ]
    have := hfin _ hcP (-Real.sin P) (by rwa [abs_neg]) _ _ hX1 hX2
    convert this using 2; ring
  · rw [hψ]
    exact hfin _ hsP _ hcP _ _ hX1 hX2

/-- **Casoratian of the bulk pair at one bond**: `|cas(φ, ψ)_k - 1| ≤ 48 R⁴ h` whenever `q_k, q_{k+1} ∈ U` and
`|a_{k+1} - A(q_{k+1} - h/2)| ≤ E h²`. -/
theorem dlg_cas_bound {A θ w Θ : ℝ → ℝ} {U : Set ℝ} {lo hi M E : ℝ} (D : DlgData A θ w Θ U lo hi M) (hE : 0 ≤ E)
    {q0 h : ℝ} (hh : 0 < h) (h1 : h ≤ 1) {a : ℤ → ℝ} {k : ℤ}
    (hk0 : dlgQ q0 h k ∈ U) (hkp : dlgQ q0 h (k + 1) ∈ U)
    (hap : |a (k + 1) - A (dlgQ q0 h (k + 1) - h / 2)| ≤ E * h ^ 2) :
    |cas a (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) k - 1| ≤ 48 * dlgR lo hi M E ^ 4 * h := by
  have hlo := D.lo_pos
  have hM := D.M_nonneg
  set q := dlgQ q0 h k with hqdef
  have hqp : dlgQ q0 h (k + 1) = q + h := dlgQ_succ q0 h k
  rw [hqp] at hkp hap
  have hhi : 0 ≤ hi := (hlo.le.trans (D.Ab q hk0).1).trans (D.Ab q hk0).2
  have hRb := dlgR_bounds hlo hhi hM hE
  have hR1 : 1 ≤ dlgR lo hi M E := dlgR_ge_one hlo hhi hM hE
  set R := dlgR lo hi M E with hRdef
  have hAq := D.Ab q hk0
  have hwq := D.wb q hk0
  have hwp := D.wb (q + h) hkp
  have hap' : |a (k + 1) - A (q + 1 * h / 2)| ≤ E * h ^ 2 := by
    have e : q + 1 * h / 2 = q + h - h / 2 := by ring
    rw [e]; exact hap
  obtain ⟨-, jmp⟩ := dlg_jets D hE (ε := 1) (ad := a (k + 1)) (Or.inl rfl) hk0 (by simpa using hkp) hh h1 hap'
  simp only [one_mul] at jmp
  have hmid := dlg_mid_mem D.convex hk0 hkp
  have hA1 := dlg_hasDeriv2 D.isOpen D.A2
  have hw1 := dlg_hasDeriv2 D.isOpen D.w2
  have lA := dlg_lip D.convex hA1.1 (fun t ht => (D.jb t ht).1) hk0 hmid
  have lw := dlg_lip D.convex hw1.1 (fun t ht => (D.jb t ht).2.2.2.2.1) hk0 hkp
  have hqh : |q + h / 2 - q| = h / 2 := by rw [add_sub_cancel_left, abs_of_pos (by positivity)]
  have hqh' : |q + h - q| = h := by rw [add_sub_cancel_left, abs_of_pos hh]
  rw [hqh] at lA
  rw [hqh'] at lw
  obtain ⟨-, -, jθ, -, -, -⟩ := D.jb q hk0
  have hMR : M ≤ R := hRb.2.1
  have hER : E ≤ R := hRb.2.2.1
  have hR2 : 0 ≤ R * h := by positivity
  have hh2 : h ^ 2 ≤ h := by
    have : h ^ 2 = h * h := by ring
    rw [this]; exact mul_le_of_le_one_right hh.le h1
  have b1 : |a (k + 1) - A q| ≤ 2 * R * h := by
    have e : a (k + 1) - A q = (a (k + 1) - A (q + h / 2)) + (A (q + h / 2) - A q) := by ring
    have hap'' : |a (k + 1) - A (q + h / 2)| ≤ E * h := by
      have : A (q + 1 * h / 2) = A (q + h / 2) := by rw [one_mul]
      rw [this] at hap'
      exact hap'.trans (mul_le_mul_of_nonneg_left hh2 hE)
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : E * h ≤ R * h := mul_le_mul_of_nonneg_right hER hh.le
    have : M * (h / 2) ≤ R * h := by
      have := mul_le_mul_of_nonneg_right hMR hh.le
      nlinarith
    linarith
  have b2 : |w (q + h) - w q| ≤ 2 * R * h := by
    have : M * h ≤ R * h := mul_le_mul_of_nonneg_right hMR hh.le
    linarith
  have b3 : |(Θ (q + h) - Θ q) / h - θ q| ≤ 2 * R * h := by
    have e : (Θ (q + h) - Θ q) / h - θ q = ((Θ (q + h) - Θ q) / h - θ q - h * deriv θ q / 2) + h * deriv θ q / 2 := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have : |h * deriv θ q / 2| ≤ R * h / 2 := by
      rw [abs_div, abs_mul, abs_of_pos hh, abs_two]
      have : h * |deriv θ q| ≤ h * R := mul_le_mul_of_nonneg_left (jθ.trans hMR) hh.le
      linarith
    have : R * h ^ 2 ≤ R * h := mul_le_mul_of_nonneg_left hh2 (by linarith)
    linarith [jmp]
  have hR1' : 1 ≤ 2 * R := by linarith
  have hrel := D.rel q hk0
  have hc := dlg_cas_real (R := 2 * R) (h := h) (A0 := A q) (w0 := w q) (wp := w (q + h)) (ap := a (k + 1)) (t0 := θ q)
    (mp := (Θ (q + h) - Θ q) / h) hR1'
    (by rw [abs_of_pos (hlo.trans_le hAq.1)]; linarith [hAq.2, hRb.1])
    (by rw [abs_of_pos (hlo.trans_le hwq.1)]; linarith [hwq.2, hRb.1])
    (by rw [abs_of_pos (hlo.trans_le hwp.1)]; linarith [hwp.2, hRb.1])
    b1 b2 b3 hrel
  have hid : cas a (dlgPhi w Θ q0 h) (dlgPsi w Θ q0 h) k =
      a (k + 1) * w q * w (q + h) * Real.sin ((Θ (q + h) - Θ q) / h) := by
    have hP1 : dlgP Θ q0 h (k + 1) = dlgP Θ q0 h k + (Θ (q + h) - Θ q) / h := by
      unfold dlgP; rw [hqp]; ring
    unfold cas dlgPhi dlgPsi
    rw [hP1, hqp, ← hqdef, Real.sin_add, Real.cos_add]
    have := Real.sin_sq_add_cos_sq (dlgP Θ q0 h k)
    linear_combination (a (k + 1) * w q * w (q + h) * Real.sin ((Θ (q + h) - Θ q) / h)) * this
  rw [hid]
  have e48 : 3 * (2 * R) ^ 4 * h = 48 * R ^ 4 * h := by ring
  rw [e48] at hc
  exact hc

end FormalResearch.Special

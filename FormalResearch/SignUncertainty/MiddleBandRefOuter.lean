module

public import FormalResearch.SignUncertainty.MiddleBandTauCut
public import FormalResearch.SignUncertainty.MiddleBandGeneralTail
public import FormalResearch.SignUncertainty.MiddleBandMainOuter

/-!
# GT.2a: the reference outer piece

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Outer pieces", second bullet.

The reference integral `(2π)⁻¹ ∫ e^{iψ(u)} e^{iεu/2} W(u) du` is split with the inner cutoff `ζ = tauCut ϑ τ ε` of the inner difference; the outer part
`∫ (1 - ζ(u)) W(u) e^{i((a₀ + ε/2)u - π²u³/36)} du` lives on `ε|u| ≥ 0.075`, where `|ψ'| ≥ 0.44 u²` (here `ψ' = a₀ + ε/2 - π²u²/12`, `a₀ = π²u₀²/12`, `εu₀ ≤ 0.05`).
The factor `e^{iεu/2}` is absorbed into the phase (shifted linear coefficient `a₀ + ε/2`).

* `cubic_tail_line`: two integrations by parts against the cubic phase on the whole line for an amplitude vanishing on `|x| < α` with the scale-invariant bounds
  `|a^{(r)}| ≤ B|x|^{-5/2-r}` (the half-line tails of `MiddleBandTail`, glued by the positive/negative split);
* `ref_outer_bound`: `‖∫ (1 - ζ) W e^{iψ̃}‖ ≤ C ε^{15/2}` for symbols with `|W^{(j)}| ≤ A_W|s|^{-5/2-j}`.

Status: proved, conditional on `O4NormalForm L τ` only through `tauCut_isCut` (such a `τ` exists for every `0 < L ≤ 0.002`, `o4_normal_form`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Complex

namespace FormalResearch.SignUncertainty

open FormalResearch.CohnElkies

/-- Splitting of an amplitude vanishing near `0` into its parts on `x > 0` and `x < 0`, both `C²`, with the local identifications. -/
lemma half_split {a : ℝ → ℂ} {α : ℝ} (hα : 0 < α) (ha : ContDiff ℝ 2 a) (hsupp : ∀ x, |x| < α → a x = 0) :
    ∃ ap an : ℝ → ℂ, ContDiff ℝ 2 ap ∧ ContDiff ℝ 2 an ∧ (∀ x, a x = ap x + an x) ∧
      (∀ x, x < α → ap x = 0) ∧ (∀ x, -α < x → an x = 0) ∧
      (∀ x, 0 < x → ap x = a x ∧ deriv ap x = deriv a x ∧ deriv (deriv ap) x = deriv (deriv a) x) ∧
      (∀ x, x < 0 → an x = a x ∧ deriv an x = deriv a x ∧ deriv (deriv an) x = deriv (deriv a) x) := by
  refine ⟨posPart a, fun x => a x - posPart a x, posPart_contDiff hα hsupp ha, ha.sub (posPart_contDiff hα hsupp ha),
    fun x => by ring, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases h : 0 < x
    · simp [posPart, h, hsupp x (by rw [abs_of_pos h]; exact hx)]
    · simp [posPart, h]
  · intro x hx
    by_cases h : 0 < x
    · simp [posPart, h]
    · simp [posPart, h, hsupp x (by rw [abs_of_nonpos (not_lt.1 h)]; linarith)]
  · intro x hx
    have hev : posPart a =ᶠ[nhds x] a := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using by simp [posPart, show 0 < y from hy]
    have h1 : deriv (posPart a) =ᶠ[nhds x] deriv a := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
      have : posPart a =ᶠ[nhds y] a := by
        filter_upwards [isOpen_Ioi.mem_nhds hy] with r hr using by simp [posPart, show 0 < r from hr]
      exact this.deriv_eq
    exact ⟨hev.eq_of_nhds, hev.deriv_eq, h1.deriv_eq⟩
  · intro x hx
    have hev : (fun y => a y - posPart a y) =ᶠ[nhds x] a := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      have : ¬ (0 < y) := not_lt.2 (le_of_lt (show y < 0 from hy))
      simp [posPart, this]
    have h1 : deriv (fun y => a y - posPart a y) =ᶠ[nhds x] deriv a := by
      filter_upwards [isOpen_Iio.mem_nhds hx] with y hy
      have : (fun y => a y - posPart a y) =ᶠ[nhds y] a := by
        filter_upwards [isOpen_Iio.mem_nhds hy] with r hr
        have : ¬ (0 < r) := not_lt.2 (le_of_lt (show r < 0 from hr))
        simp [posPart, this]
      exact this.deriv_eq
    exact ⟨hev.eq_of_nhds, hev.deriv_eq, h1.deriv_eq⟩

/-- **Cubic phase, whole line, amplitude vanishing on `|x| < α`.** -/
theorem cubic_tail_line : ∃ K : ℝ, 0 ≤ K ∧
    ∀ {a : ℝ → ℂ} {a0 α B q : ℝ}, 0 < α → 0 ≤ B → 0 < q → ContDiff ℝ 2 a → (∀ x, |x| < α → a x = 0) →
    (∀ x, α ≤ |x| → ‖a x‖ ≤ B * |x| ^ (-(5 / 2 : ℝ))) →
    (∀ x, α ≤ |x| → ‖deriv a x‖ ≤ B * |x| ^ (-(7 / 2 : ℝ))) →
    (∀ x, α ≤ |x| → ‖deriv (deriv a) x‖ ≤ B * |x| ^ (-(9 / 2 : ℝ))) →
    (∀ x, α ≤ |x| → q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12|) →
    ‖∫ x, a x * Complex.exp (Complex.I * ((a0 * x - Real.pi ^ 2 / 36 * x ^ 3 : ℝ) : ℂ))‖ ≤
      2 * ((1 + K) * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)))) := by
  obtain ⟨K, hK0, hK⟩ := cubic_two_ibp_power_tail
  obtain ⟨K', hK0', hK'⟩ := cubic_two_ibp_power_tail_neg
  refine ⟨max K K', le_max_of_le_left hK0, ?_⟩
  intro a a0 α B q hα hB hq ha hsupp hb0 hb1 hb2 hp
  obtain ⟨ap, an, hapC, hanC, hsum, hsp, hsn, hpos, hneg⟩ := half_split hα ha hsupp
  set ψ : ℝ → ℝ := fun x => a0 * x - Real.pi ^ 2 / 36 * x ^ 3 with hψ
  have hψc : Continuous ψ := by rw [hψ]; fun_prop
  have hpos' : ∀ x, α ≤ x → 0 < x := fun x hx => lt_of_lt_of_le hα hx
  have hap0 : ∀ x, α ≤ x → ‖ap x‖ ≤ B * x ^ (-(5 / 2 : ℝ)) := fun x hx => by
    have := hb0 x (by rw [abs_of_pos (hpos' x hx)]; exact hx)
    rw [abs_of_pos (hpos' x hx)] at this
    rwa [(hpos x (hpos' x hx)).1]
  have han0 : ∀ x, x ≤ -α → ‖an x‖ ≤ B * (-x) ^ (-(5 / 2 : ℝ)) := fun x hx => by
    have hxn : x < 0 := by linarith
    have := hb0 x (by rw [abs_of_neg hxn]; linarith)
    rw [abs_of_neg hxn] at this
    rwa [(hneg x hxn).1]
  have hint1 := tail_integrable (a := ap) (ψ := ψ) (α := α) (B := B) (s := 5 / 2) hα (by norm_num) hapC.continuous hψc hsp hap0
  have hint2 := tail_integrable_neg (a := an) (ψ := ψ) (α := α) (B := B) (s := 5 / 2) hα (by norm_num) hanC.continuous hψc hsn han0
  have hsplit : ∫ x, a x * Complex.exp (Complex.I * ψ x) =
      (∫ x, ap x * Complex.exp (Complex.I * ψ x)) + ∫ x, an x * Complex.exp (Complex.I * ψ x) := by
    rw [← integral_add hint1 hint2]
    congr 1; funext x; rw [hsum x]; ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have hpl := hK ap a0 α B q hα hB hq hapC hsp hap0
    (fun x hx => by
      have := hb1 x (by rw [abs_of_pos (hpos' x hx)]; exact hx)
      rw [abs_of_pos (hpos' x hx)] at this
      rwa [(hpos x (hpos' x hx)).2.1])
    (fun x hx => by
      have := hb2 x (by rw [abs_of_pos (hpos' x hx)]; exact hx)
      rw [abs_of_pos (hpos' x hx)] at this
      rwa [(hpos x (hpos' x hx)).2.2])
    (fun x hx => hp x (by rw [abs_of_pos (hpos' x hx)]; exact hx))
  have hng := hK' an a0 α B q hα hB hq hanC hsn han0
    (fun x hx => by
      have hxn : x < 0 := by linarith
      have := hb1 x (by rw [abs_of_neg hxn]; linarith)
      rw [abs_of_neg hxn] at this
      rwa [(hneg x hxn).2.1])
    (fun x hx => by
      have hxn : x < 0 := by linarith
      have := hb2 x (by rw [abs_of_neg hxn]; linarith)
      rw [abs_of_neg hxn] at this
      rwa [(hneg x hxn).2.2])
    (fun x hx => hp x (by rw [abs_of_neg (by linarith : x < 0)]; linarith))
  have hP : 0 ≤ (2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) := by positivity
  have hm1 : (1 + K) * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4))) ≤ (1 + max K K') * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4))) :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_left K K']) hP
  have hm2 : (1 + K') * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4))) ≤ (1 + max K K') * ((2 / 15) * α ^ (-(15 / 2 : ℝ)) * B * (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3)
        + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4))) :=
    mul_le_mul_of_nonneg_right (by linarith [le_max_right K K']) hP
  linarith

/-- info: 'FormalResearch.SignUncertainty.cubic_tail_line' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cubic_tail_line

lemma isCut_one : IsCut (fun _ : ℝ => (1 : ℝ)) 1 0 0 :=
  ⟨contDiff_const, fun _ => by simp, fun u _ => by simp, fun u _ => by simp⟩

lemma deriv_chain {W W1 W2 W3 : ℝ → ℂ}
    (hWd : ∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) {v : ℝ} (hv : v ≠ 0) :
    deriv W v = W1 v ∧ deriv (deriv W) v = W2 v := by
  have h1 : deriv W =ᶠ[nhds v] W1 := by
    filter_upwards [isOpen_ne.mem_nhds hv] with y hy using (hWd y hy).1.deriv
  exact ⟨(hWd v hv).1.deriv, by rw [h1.deriv_eq]; exact (hWd v hv).2.1.deriv⟩

/-- **The reference outer piece.**  For the inner cutoff `ζ = tauCut ϑ τ ε` and a symbol `W` with the `GT.1` bounds,
`‖∫ (1 - ζ) W e^{i(a₀ u - π²u³/36)}‖ ≤ C ε^{15/2}` whenever `a₀ ε² ≤ 0.0045` and `ε ≤ 0.15`. -/
theorem ref_outer_bound {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) (AW : ℝ) (hAW : 0 ≤ AW) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L ε a0 : ℝ} {τ : ℂ → ℂ} {W W1 W2 W3 : ℝ → ℂ}, O4NormalForm L τ → 0 < L → L ≤ 0.002 →
      0 < ε → ε ≤ 0.15 → a0 * ε ^ 2 ≤ 0.0045 →
      (∀ s, s ≠ 0 → HasDerivAt W (W1 s) s ∧ HasDerivAt W1 (W2 s) s ∧ HasDerivAt W2 (W3 s) s) →
      (∀ s, 1 / 2 ≤ |s| → ‖W s‖ ≤ AW * |s| ^ (-(5 / 2 : ℝ)) ∧ ‖W1 s‖ ≤ AW * |s| ^ (-(7 / 2 : ℝ)) ∧
        ‖W2 s‖ ≤ AW * |s| ^ (-(9 / 2 : ℝ))) →
      ‖∫ u : ℝ, (((1 - tauCut ϑ τ ε u : ℝ) : ℂ) * W u) *
          Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))‖ ≤ C * ε ^ (15 / 2 : ℝ) := by
  obtain ⟨Z1, Z2, hZ1, hZ2, hZ⟩ := tauCut_isCut hϑ
  obtain ⟨K, hK0, hK⟩ := cubic_tail_line
  set B : ℝ := (Z2 + 3 * Z1 + 6) * AW with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  set q : ℝ := 0.02 with hq
  set P : ℝ := (1 / q ^ 2 + Real.pi ^ 2 / (2 * q ^ 3) + Real.pi ^ 2 / (6 * q ^ 3) + Real.pi ^ 4 / (12 * q ^ 4)) with hP
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  refine ⟨2 * ((1 + K) * ((2 / 15) * ((0.075 : ℝ) ^ (-(15 / 2 : ℝ))) * B * P)), by positivity, ?_⟩
  intro L ε a0 τ W W1 W2 W3 h hL0 hL2 hε hε15 ha0 hWd hWb
  obtain ⟨hcut, hone, hzero⟩ := hZ h hL0 hL2 hε
  have hη : IsCut (fun u => (1 : ℝ) - tauCut ϑ τ ε u) (1 + 1) (0 + Z1) (0 + Z2) := isCut_one.sub hcut
  set α : ℝ := 0.075 / ε with hα
  have hα0 : 0 < α := by rw [hα]; positivity
  have hαhalf : 1 / 2 ≤ α := by
    rw [hα, le_div_iff₀ hε]; linarith
  have hεα : ∀ x : ℝ, α ≤ |x| ↔ 0.075 ≤ ε * |x| := fun x => by
    rw [hα, div_le_iff₀ hε]; constructor <;> intro hh <;> linarith
  set a : ℝ → ℂ := fun y => (((1 : ℝ) - tauCut ϑ τ ε y : ℝ) : ℂ) * W y with ha
  have hsupp : ∀ x, |x| < α → a x = 0 := by
    intro x hx
    have : ε * |x| ≤ 0.075 := by
      have := (hεα x).not.1 (not_le.2 hx)
      linarith
    simp [ha, hone x this]
  have haC : ContDiff ℝ 2 a := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v = 0
    · subst hv
      have : a =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℂ) := by
        filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hα0 : |(0 : ℝ)| < α)] with y hy
        exact hsupp y hy
      exact contDiffAt_const.congr_of_eventuallyEq this
    · exact (Complex.ofRealCLM.contDiff.comp (hη.contDiff)).contDiffAt.mul (contDiffAt_two_of_chain hv hWd)
  have hbd : ∀ x, α ≤ |x| → ‖a x‖ ≤ B * |x| ^ (-(5 / 2 : ℝ)) ∧ ‖deriv a x‖ ≤ B * |x| ^ (-(7 / 2 : ℝ)) ∧
      ‖deriv (deriv a) x‖ ≤ B * |x| ^ (-(9 / 2 : ℝ)) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h0; rw [h0] at hx; simp at hx; linarith
    have hxh : 1 / 2 ≤ |x| := hαhalf.trans hx
    obtain ⟨b0, b1, b2⟩ := hWb x hxh
    obtain ⟨d1, d2⟩ := deriv_chain hWd hx0
    have := leibniz_cut hη (g := W) (G := AW) (s := 5 / 2) (x := x) (contDiffAt_two_of_chain hx0 hWd) hAW hx0 b0
      (by rw [d1]; convert b1 using 2; norm_num) (by rw [d2]; convert b2 using 2; norm_num)
    obtain ⟨r0, r1, r2⟩ := this
    have e1 : (-(5 / 2 : ℝ) - 1) = -(7 / 2) := by norm_num
    have e2 : (-(5 / 2 : ℝ) - 2) = -(9 / 2) := by norm_num
    rw [e1] at r1; rw [e2] at r2
    have q0 : 0 ≤ |x| ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    have q1 : 0 ≤ |x| ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    have q2 : 0 ≤ |x| ^ (-(9 / 2 : ℝ)) := Real.rpow_nonneg (abs_nonneg _) _
    refine ⟨r0.trans ?_, r1.trans ?_, r2.trans ?_⟩
    · rw [hB]; nlinarith [mul_nonneg hAW q0, mul_nonneg hZ1 (mul_nonneg hAW q0), mul_nonneg hZ2 (mul_nonneg hAW q0)]
    · rw [hB]; nlinarith [mul_nonneg hAW q1, mul_nonneg hZ1 (mul_nonneg hAW q1), mul_nonneg hZ2 (mul_nonneg hAW q1)]
    · rw [hB]; nlinarith [mul_nonneg hAW q2, mul_nonneg hZ1 (mul_nonneg hAW q2), mul_nonneg hZ2 (mul_nonneg hAW q2)]
  have hphase : ∀ x, α ≤ |x| → q * x ^ 2 ≤ |a0 - Real.pi ^ 2 * x ^ 2 / 12| := by
    intro x hx
    have hx2 : 0.075 ^ 2 ≤ (ε * |x|) ^ 2 := by
      have := (hεα x).1 hx
      exact pow_le_pow_left₀ (by norm_num) this 2
    have hxx : (ε * |x|) ^ 2 = ε ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
    have hpi : (3.14 : ℝ) ≤ Real.pi := Real.pi_gt_d2.le
    have hpi2 : (9.85 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
    have hε2 : 0 < ε ^ 2 := by positivity
    have : 0 < x ^ 2 := by
      have : x ≠ 0 := by intro h0; rw [h0] at hx; simp at hx; linarith
      positivity
    have hxx2 : (0.075 : ℝ) ^ 2 ≤ ε ^ 2 * x ^ 2 := by rw [← hxx]; exact hx2
    have h1' : a0 * ε ^ 2 ≤ (0.8 * x ^ 2) * ε ^ 2 := by
      have e : (0.8 * x ^ 2) * ε ^ 2 = 0.8 * (ε ^ 2 * x ^ 2) := by ring
      rw [e]
      have : (0.005625 : ℝ) ≤ ε ^ 2 * x ^ 2 := by norm_num at hxx2; linarith
      linarith
    have h1 : a0 ≤ 0.8 * x ^ 2 := le_of_mul_le_mul_right h1' hε2
    have h3 : 9.85 * x ^ 2 ≤ Real.pi ^ 2 * x ^ 2 := mul_le_mul_of_nonneg_right hpi2 this.le
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hq]; linarith
  have hmain := hK (a := a) (a0 := a0) (α := α) (B := B) (q := q) hα0 hB0 (by norm_num [hq]) haC hsupp
    (fun x hx => (hbd x hx).1) (fun x hx => (hbd x hx).2.1) (fun x hx => (hbd x hx).2.2) hphase
  refine hmain.trans (le_of_eq ?_)
  have hαp : α ^ (-(15 / 2 : ℝ)) = (0.075 : ℝ) ^ (-(15 / 2 : ℝ)) * ε ^ (15 / 2 : ℝ) := by
    rw [hα]; exact div_rpow_neg_aux (by norm_num) hε _
  rw [hαp]; ring

/-- info: 'FormalResearch.SignUncertainty.ref_outer_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ref_outer_bound

end FormalResearch.SignUncertainty

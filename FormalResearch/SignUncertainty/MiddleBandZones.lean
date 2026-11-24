module

public import FormalResearch.SignUncertainty.MiddleBandNearZero

/-!
# GT.2a: shoulders, stationary and far zones for the inner difference

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Shoulders", "Stationary", "Far".

Setting: `ψ(u) = a₀ u - π² u³/36` with `a₀ = π² u₀²/12` (`u₀` the positive zero of `ψ'`), `u₀ ≥ 34`, and an amplitude `g` satisfying the
bounds `(e8)` (`LargeZone g G L ε`): for `1 ≤ |u|`, `ε|u| ≤ 0.18`, `g ∈ C²` at `u` and `|g^{(r)}(u)| ≤ G (L + ε²u²) |u|^{-5/2-r}`.
With the fixed cutoff profile `ϑ` (`Prof`), the cutoff differences supported in the three zones contribute at most
`C G (L + ε² u₀²) u₀^{-3}`:

* `zone_shoulder`: `1 ≤ |u| ≤ u₀/2`, two integrations by parts with `|ψ'| ≥ 3a₀/4`;
* `zone_stationary`: `u₀/4 ≤ |u| ≤ 3u₀`, van der Corput (second derivative `π²|u|/6`);
* `zone_far`: `3u₀/2 ≤ |u| ≤ 0.18/ε`, two integrations by parts with `|ψ'| ≥ 5π²u²/108` and `L ≤ ε²u₀²`.

Status: proved, unconditional (hypotheses are the pointwise bounds `(e8)`).
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.SignUncertainty

/-- The bounds `(e8)` for the inner difference in the zone `1 ≤ |u|`, `ε|u| ≤ 0.18`. -/
structure LargeZone (g : ℝ → ℂ) (G L ε : ℝ) : Prop where
  cd : ∀ u, 1 ≤ |u| → ε * |u| ≤ 0.18 → ContDiffAt ℝ 2 g u
  b0 : ∀ u, 1 ≤ |u| → ε * |u| ≤ 0.18 → ‖g u‖ ≤ G * (L + ε ^ 2 * u ^ 2) * |u| ^ (-(5 / 2 : ℝ))
  b1 : ∀ u, 1 ≤ |u| → ε * |u| ≤ 0.18 → ‖deriv g u‖ ≤ G * (L + ε ^ 2 * u ^ 2) * |u| ^ (-(7 / 2 : ℝ))
  b2 : ∀ u, 1 ≤ |u| → ε * |u| ≤ 0.18 → ‖deriv (deriv g) u‖ ≤ G * (L + ε ^ 2 * u ^ 2) * |u| ^ (-(9 / 2 : ℝ))

/-- `η g` is globally `C²` if `η` is `C²`, vanishes for `|u| ≤ α` and `|u| ≥ β`, and `g` is `C²` at all `u` with `α ≤ |u| ≤ β`. -/
lemma cut_mul_contDiff {η : ℝ → ℝ} (hη : ContDiff ℝ 2 η) {g : ℝ → ℂ} {α β : ℝ}
    (h0 : ∀ u, |u| ≤ α → η u = 0) (h1 : ∀ u, β ≤ |u| → η u = 0)
    (hg : ∀ u, α ≤ |u| → |u| ≤ β → ContDiffAt ℝ 2 g u) : ContDiff ℝ 2 (fun u => (η u : ℂ) * g u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hin : α ≤ |u| ∧ |u| ≤ β
  · exact ((Complex.ofRealCLM.contDiff.comp hη).contDiffAt).mul (hg u hin.1 hin.2)
  · have : (fun u => (η u : ℂ) * g u) =ᶠ[nhds u] fun _ => (0 : ℂ) := by
      rcases not_and_or.1 hin with h | h
      · have h' : |u| < α := not_le.1 h
        filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds h')] with v hv
        simp [h0 v hv.le]
      · have h' : β < |u| := not_le.1 h
        filter_upwards [continuous_abs.continuousAt.eventually (lt_mem_nhds h')] with v hv
        simp [h1 v hv.le]
    exact (contDiffAt_const).congr_of_eventuallyEq this


lemma integrable_osc_R {f : ℝ → ℂ} {R : ℝ} (hR : 0 ≤ R) (hf : Continuous f) (hz : ∀ u, R ≤ |u| → f u = 0) (a0 : ℝ) :
    Integrable (fun u => f u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) := by
  refine Continuous.integrable_of_hasCompactSupport (hf.mul (by fun_prop)) ?_
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) (fun x hx => ?_)
  have : R ≤ |x| := by
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [hz x this]

lemma pi4_ge : (96 : ℝ) ≤ Real.pi ^ 4 := by
  have h := Real.pi_gt_d2
  have h2 : (9.8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  nlinarith

lemma shoulder_sum {u0 : ℝ} (hu : 34 ≤ u0) :
    1 / (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 2 + Real.pi ^ 2 * (u0 / 2) / (2 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 3)
      + Real.pi ^ 2 / (6 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 3)
      + Real.pi ^ 4 * (u0 / 2) ^ 2 / (12 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 4) ≤ 6 / u0 ^ 4 := by
  have hu0 : 0 < u0 := by linarith
  have hπ := pi4_ge
  have hπ0 : 0 < Real.pi ^ 4 := by positivity
  have e1 : 1 / (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 2 = 256 / (Real.pi ^ 4 * u0 ^ 4) := by field_simp; ring
  have e2 : Real.pi ^ 2 * (u0 / 2) / (2 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 3) = 1024 / (Real.pi ^ 4 * u0 ^ 5) := by
    field_simp; ring
  have e3 : Real.pi ^ 2 / (6 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 3) = 2048 / (3 * Real.pi ^ 4 * u0 ^ 6) := by
    field_simp; ring
  have e4 : Real.pi ^ 4 * (u0 / 2) ^ 2 / (12 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 4) = 4096 / (3 * Real.pi ^ 4 * u0 ^ 6) := by
    field_simp; ring
  rw [e1, e2, e3, e4]
  have b1 : 256 / (Real.pi ^ 4 * u0 ^ 4) ≤ 3 / u0 ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < u0 ^ 4 := by positivity
    nlinarith
  have b2 : 1024 / (Real.pi ^ 4 * u0 ^ 5) ≤ 1 / u0 ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 0 < u0 ^ 4 := by positivity
    nlinarith [mul_le_mul hπ hu (by norm_num) hπ0.le]
  have b3 : 2048 / (3 * Real.pi ^ 4 * u0 ^ 6) ≤ 1 / u0 ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 0 < u0 ^ 4 := by positivity
    have h2 : 1156 ≤ u0 ^ 2 := by nlinarith
    nlinarith [mul_le_mul hπ h2 (by norm_num) hπ0.le]
  have b4 : 4096 / (3 * Real.pi ^ 4 * u0 ^ 6) ≤ 1 / u0 ^ 4 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h4 : 0 < u0 ^ 4 := by positivity
    have h2 : 1156 ≤ u0 ^ 2 := by nlinarith
    nlinarith [mul_le_mul hπ h2 (by norm_num) hπ0.le]
  have : (6 : ℝ) / u0 ^ 4 = 3 / u0 ^ 4 + 1 / u0 ^ 4 + 1 / u0 ^ 4 + 1 / u0 ^ 4 := by ring
  linarith


lemma rpow_nonpos_le_one {x t : ℝ} (hx : 1 ≤ |x|) (ht : t ≤ 0) : |x| ^ t ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx ht

/-- **Shoulders** `1 ≤ |u| ≤ u₀/2`. -/
theorem zone_shoulder {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u0 ε L G : ℝ} {g : ℝ → ℂ}, 34 ≤ u0 → 0 < ε → 0 ≤ L → 0 ≤ G → ε * u0 ≤ 0.36 →
      LargeZone g G L ε →
      Integrable (fun u => ((ϑ (u / (u0 / 4)) - ϑ u : ℝ) : ℂ) * g u * Complex.exp (Complex.I * ((Real.pi ^ 2 * u0 ^ 2 / 12 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) ∧
      ‖oscInt (Real.pi ^ 2 * u0 ^ 2 / 12) (fun u => ((ϑ (u / (u0 / 4)) - ϑ u : ℝ) : ℂ) * g u)‖ ≤
        C * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) := by
  set Kc : ℝ := 8 * K2 + 8 * K1 + 2 with hKc
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨24 * Kc, by positivity, ?_⟩
  intro u0 ε L G g hu0 hε hL hG hεu hz
  have hu0p : 0 < u0 := by linarith
  have hR : 0 < u0 / 4 := by positivity
  have hν : IsCut ϑ 1 (2 * K1) (4 * K2) := by simpa using hϑ.cut one_pos
  have hη0 := (hϑ.cut hR).sub hν
  set η : ℝ → ℝ := fun u => ϑ (u / (u0 / 4)) - ϑ u with hηdef
  have hηsmall : ∀ u, |u| ≤ 1 → η u = 0 := by
    intro u hu
    have h1 : ϑ u = 1 := hϑ.one u hu
    have h2 : ϑ (u / (u0 / 4)) = 1 := by
      apply hϑ.one
      rw [abs_div, abs_of_pos hR, div_le_one hR]
      linarith
    have e : η u = ϑ (u / (u0 / 4)) - ϑ u := rfl
    rw [e, h1, h2]; ring
  have hηbig : ∀ u, u0 / 2 ≤ |u| → η u = 0 := by
    intro u hu
    have h1 : ϑ u = 0 := hϑ.zero u (by linarith)
    have h2 : ϑ (u / (u0 / 4)) = 0 := by
      apply hϑ.zero
      rw [abs_div, abs_of_pos hR, le_div_iff₀ hR]
      linarith
    have e : η u = ϑ (u / (u0 / 4)) - ϑ u := rfl
    rw [e, h1, h2]; ring
  have hcd : ∀ u, 1 ≤ |u| → |u| ≤ u0 / 2 → ContDiffAt ℝ 2 g u := fun u h1 h2 =>
    hz.cd u h1 (by
      have : ε * |u| ≤ ε * (u0 / 2) := by gcongr
      linarith)
  have hAC := cut_mul_contDiff hη0.contDiff hηsmall hηbig hcd
  refine ⟨integrable_osc_R (f := fun u => (η u : ℂ) * g u) (R := u0 / 2) (by positivity) hAC.continuous (fun u hu => by simp [hηbig u hu]) _, ?_⟩
  set B : ℝ := Kc * G * (L + ε ^ 2 * u0 ^ 2) with hB
  have hB0 : 0 ≤ B := by positivity
  have hleib : ∀ x, 1 ≤ |x| → |x| ≤ u0 / 2 →
      ‖(η x : ℂ) * g x‖ ≤ B ∧ ‖deriv (fun y => (η y : ℂ) * g y) x‖ ≤ B ∧
        ‖deriv (deriv (fun y => (η y : ℂ) * g y)) x‖ ≤ B := by
    intro x h1 h2
    have hx0 : x ≠ 0 := abs_ne_zero.mp (by linarith)
    have hεx : ε * |x| ≤ 0.18 := by
      have : ε * |x| ≤ ε * (u0 / 2) := by gcongr
      linarith
    have hL' := leibniz_cut hη0 (hz.cd x h1 hεx) (G := G * (L + ε ^ 2 * x ^ 2)) (s := 5 / 2) (x := x)
      (by positivity) hx0 (hz.b0 x h1 hεx)
      (by have := hz.b1 x h1 hεx; rwa [show (-(7 / 2) : ℝ) = -(5 / 2) - 1 by norm_num] at this)
      (by have := hz.b2 x h1 hεx; rwa [show (-(9 / 2) : ℝ) = -(5 / 2) - 2 by norm_num] at this)
    obtain ⟨h0', h1', h2'⟩ := hL'
    have hx2 : x ^ 2 ≤ u0 ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) 2
    have hG1 : G * (L + ε ^ 2 * x ^ 2) ≤ G * (L + ε ^ 2 * u0 ^ 2) := by gcongr
    have hGp : 0 ≤ G * (L + ε ^ 2 * x ^ 2) := by positivity
    have r0 := rpow_nonpos_le_one (x := x) h1 (t := -(5 / 2)) (by norm_num)
    have r1 := rpow_nonpos_le_one (x := x) h1 (t := -(5 / 2) - 1) (by norm_num)
    have r2 := rpow_nonpos_le_one (x := x) h1 (t := -(5 / 2) - 2) (by norm_num)
    have q0 : 0 ≤ |x| ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have q1 : 0 ≤ |x| ^ (-(5 / 2) - 1 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have q2 : 0 ≤ |x| ^ (-(5 / 2) - 2 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have key : ∀ c r : ℝ, 0 ≤ c → c ≤ Kc → 0 ≤ r → r ≤ 1 → c * (G * (L + ε ^ 2 * x ^ 2)) * r ≤ B := by
      intro c r hc hcK hr0 hr1
      calc c * (G * (L + ε ^ 2 * x ^ 2)) * r ≤ c * (G * (L + ε ^ 2 * x ^ 2)) * 1 :=
            mul_le_mul_of_nonneg_left hr1 (mul_nonneg hc hGp)
        _ ≤ Kc * (G * (L + ε ^ 2 * x ^ 2)) := by rw [mul_one]; exact mul_le_mul_of_nonneg_right hcK hGp
        _ ≤ Kc * (G * (L + ε ^ 2 * u0 ^ 2)) := mul_le_mul_of_nonneg_left hG1 hKc0
        _ = B := by rw [hB]; ring
    refine ⟨h0'.trans (key _ _ (by norm_num) (by linarith) q0 r0),
      h1'.trans (key _ _ (by positivity) (by linarith) q1 r1),
      h2'.trans (key _ _ (by positivity) (by linarith) q2 r2)⟩
  have hp0 : (0 : ℝ) < Real.pi ^ 2 * u0 ^ 2 / 16 := by positivity
  have hmain := ibp_const_sym (a := fun u => (η u : ℂ) * g u) (a0 := Real.pi ^ 2 * u0 ^ 2 / 12) (α := 1) (β := u0 / 2)
    (B := B) (p0 := Real.pi ^ 2 * u0 ^ 2 / 16) one_pos (by linarith) hB0 hp0 hAC
    (fun x hx => by simp [hηsmall x (by linarith)])
    (fun x hx => by simp [hηbig x (by linarith)])
    (fun x h1 h2 => (hleib x h1 h2).1) (fun x h1 h2 => (hleib x h1 h2).2.1) (fun x h1 h2 => (hleib x h1 h2).2.2)
    (fun x h1 h2 => by
      have hx2 : x ^ 2 ≤ (u0 / 2) ^ 2 := by
        rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      have : 0 < Real.pi ^ 2 * u0 ^ 2 / 12 - Real.pi ^ 2 * x ^ 2 / 12 := by nlinarith [Real.pi_pos]
      have hpi : 0 < Real.pi ^ 2 := by positivity
      rw [abs_of_pos this]
      nlinarith [mul_le_mul_of_nonneg_left hx2 hpi.le])
  have hsum := shoulder_sum hu0
  have hmain' := hmain
  have hβ : (u0 / 2 - 1) ≤ u0 / 2 := by linarith
  calc ‖oscInt (Real.pi ^ 2 * u0 ^ 2 / 12) (fun u => (η u : ℂ) * g u)‖
      ≤ 2 * ((u0 / 2 - 1) * B * (1 / (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 2
        + Real.pi ^ 2 * (u0 / 2) / (2 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 3) + Real.pi ^ 2 / (6 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 3)
        + Real.pi ^ 4 * (u0 / 2) ^ 2 / (12 * (Real.pi ^ 2 * u0 ^ 2 / 16) ^ 4))) := hmain
    _ ≤ 2 * ((u0 / 2) * B * (6 / u0 ^ 4)) := by
        gcongr
    _ = 6 * B * (1 / u0 ^ 3) := by field_simp
    _ ≤ _ := by
        rw [hB]
        have hu3 : 0 ≤ 1 / u0 ^ 3 := by positivity
        have hP : 0 ≤ Kc * G * (L + ε ^ 2 * u0 ^ 2) := by positivity
        nlinarith [mul_nonneg hP hu3]


lemma int_rpow_tail_le {α β t : ℝ} (hα : 0 < α) (ht : 1 < t) :
    ∫ x in Set.Icc α β, x ^ (-t) ≤ α ^ (1 - t) / (t - 1) := by
  have hfi : IntegrableOn (fun x : ℝ => x ^ (-t)) (Set.Ici α) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) hα
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ici α)] (fun x : ℝ => x ^ (-t)) :=
    (ae_restrict_iff' measurableSet_Ici).2 (ae_of_all _ fun x hx =>
      Real.rpow_nonneg (by have := Set.mem_Ici.1 hx; linarith) _)
  calc ∫ x in Set.Icc α β, x ^ (-t) ≤ ∫ x in Set.Ici α, x ^ (-t) :=
        setIntegral_mono_set hfi hnn (ae_of_all _ fun x (hx : x ∈ Set.Icc α β) => Set.Icc_subset_Ici_self hx)
    _ = ∫ x in Set.Ioi α, x ^ (-t) := by rw [integral_Ici_eq_integral_Ioi]
    _ = α ^ (1 - t) / (t - 1) := mb_tail_pow hα ht

/-- `(u₀/4)^{-t} = 4^t u₀^{-t}`. -/
lemma quarter_rpow {u0 : ℝ} (hu : 0 < u0) (t : ℝ) : (u0 / 4) ^ (-t) = (4 : ℝ) ^ t * u0 ^ (-t) := by
  rw [Real.div_rpow hu.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), div_eq_mul_inv, inv_inv, mul_comm]

lemma four_rpow_le {t : ℝ} (h0 : 0 ≤ t) (h3 : t ≤ 3) : (4 : ℝ) ^ t ≤ 64 := by
  calc (4 : ℝ) ^ t ≤ (4 : ℝ) ^ (3 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h3
    _ = 64 := by norm_num


lemma rpow_neg_half_sqrt {u0 : ℝ} (hu : 0 < u0) (n : ℕ) (t : ℝ) (ht : t = n / 2) :
    u0 ^ (-t) = 1 / (Real.sqrt u0) ^ n := by
  rw [Real.rpow_neg hu.le, one_div, ht, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hu.le]
  congr 2
  ring

lemma sqrt_pow6 {u0 : ℝ} (hu : 0 < u0) : (Real.sqrt u0) ^ 6 = u0 ^ 3 := by
  have : (Real.sqrt u0) ^ 2 = u0 := Real.sq_sqrt hu.le
  calc (Real.sqrt u0) ^ 6 = ((Real.sqrt u0) ^ 2) ^ 3 := by ring
    _ = u0 ^ 3 := by rw [this]

lemma stat_arith (A L e2 u2 q : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L) (hq : 0 ≤ q) :
    A * (L * (26 * q) + e2 * (128 * (u2 * q))) ≤ 128 * A * (L + e2 * u2) * q := by
  nlinarith [mul_nonneg (mul_nonneg hA hL) hq]

set_option maxHeartbeats 1600000 in
/-- **Stationary zone** `u₀/4 ≤ |u| ≤ 3u₀`: van der Corput. -/
theorem zone_stationary {ϑ : ℝ → ℝ} {K1 K2 : ℝ} (hϑ : Prof ϑ K1 K2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u0 ε L G : ℝ} {g : ℝ → ℂ}, 34 ≤ u0 → 0 < ε → 0 ≤ L → 0 ≤ G → ε * u0 ≤ 0.05 →
      LargeZone g G L ε →
      Integrable (fun u => ((ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) : ℝ) : ℂ) * g u * Complex.exp (Complex.I * ((Real.pi ^ 2 * u0 ^ 2 / 12 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) ∧
      ‖oscInt (Real.pi ^ 2 * u0 ^ 2 / 12) (fun u => ((ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) : ℝ) : ℂ) * g u)‖ ≤
        C * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) := by
  set Kc : ℝ := 8 * K2 + 8 * K1 + 2 with hKc
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  have hKc0 : 0 ≤ Kc := by positivity
  refine ⟨22600 * Kc, by positivity, ?_⟩
  intro u0 ε L G g hu0 hε hL hG hεu hz
  have hu0p : 0 < u0 := by linarith
  have hR1 : 0 < 3 * u0 / 2 := by positivity
  have hR2 : 0 < u0 / 4 := by positivity
  have hη0 := (hϑ.cut hR1).sub (hϑ.cut hR2)
  set η : ℝ → ℝ := fun u => ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) with hηdef
  have hηsmall : ∀ u, |u| ≤ u0 / 4 → η u = 0 := by
    intro u hu
    have h2 : ϑ (u / (u0 / 4)) = 1 := by
      apply hϑ.one
      rw [abs_div, abs_of_pos hR2, div_le_one hR2]; exact hu
    have h1 : ϑ (u / (3 * u0 / 2)) = 1 := by
      apply hϑ.one
      rw [abs_div, abs_of_pos hR1, div_le_one hR1]; linarith
    have e : η u = ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) := rfl
    rw [e, h1, h2]; ring
  have hηbig : ∀ u, 3 * u0 ≤ |u| → η u = 0 := by
    intro u hu
    have h1 : ϑ (u / (3 * u0 / 2)) = 0 := by
      apply hϑ.zero
      rw [abs_div, abs_of_pos hR1, le_div_iff₀ hR1]; linarith
    have h2 : ϑ (u / (u0 / 4)) = 0 := by
      apply hϑ.zero
      rw [abs_div, abs_of_pos hR2, le_div_iff₀ hR2]; linarith
    have e : η u = ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) := rfl
    rw [e, h1, h2]; ring
  have hεx : ∀ x, |x| ≤ 3 * u0 → ε * |x| ≤ 0.18 := by
    intro x hx
    have : ε * |x| ≤ ε * (3 * u0) := by gcongr
    linarith
  have hcd : ∀ u, u0 / 4 ≤ |u| → |u| ≤ 3 * u0 → ContDiffAt ℝ 2 g u := fun u h1 h2 =>
    hz.cd u (by linarith) (hεx u h2)
  have hAC := cut_mul_contDiff hη0.contDiff hηsmall hηbig hcd
  refine ⟨integrable_osc_R (f := fun u => (η u : ℂ) * g u) (R := 3 * u0) (by positivity) hAC.continuous (fun u hu => by simp [hηbig u hu]) _, ?_⟩
  set E : ℝ := L + ε ^ 2 * u0 ^ 2 with hE
  have hE0 : 0 ≤ E := by positivity
  have hleib : ∀ x, u0 / 4 ≤ |x| → |x| ≤ 3 * u0 →
      ‖(η x : ℂ) * g x‖ ≤ Kc * (G * (L + ε ^ 2 * x ^ 2)) * |x| ^ (-(5 / 2 : ℝ)) ∧
      ‖deriv (fun y => (η y : ℂ) * g y) x‖ ≤ Kc * (G * (L + ε ^ 2 * x ^ 2)) * |x| ^ (-(7 / 2 : ℝ)) := by
    intro x h1 h2
    have hx1 : 1 ≤ |x| := by linarith
    have hx0 : x ≠ 0 := abs_ne_zero.mp (by linarith)
    have hL' := leibniz_cut hη0 (hz.cd x hx1 (hεx x h2)) (G := G * (L + ε ^ 2 * x ^ 2)) (s := 5 / 2) (x := x)
      (by positivity) hx0 (hz.b0 x hx1 (hεx x h2))
      (by have := hz.b1 x hx1 (hεx x h2); rwa [show (-(7 / 2) : ℝ) = -(5 / 2) - 1 by norm_num] at this)
      (by have := hz.b2 x hx1 (hεx x h2); rwa [show (-(9 / 2) : ℝ) = -(5 / 2) - 2 by norm_num] at this)
    obtain ⟨h0', h1', -⟩ := hL'
    have hGp : 0 ≤ G * (L + ε ^ 2 * x ^ 2) := by positivity
    have e1 : (-(5 / 2) - 1 : ℝ) = -(7 / 2) := by norm_num
    rw [e1] at h1'
    have q0 : 0 ≤ |x| ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    have q1 : 0 ≤ |x| ^ (-(7 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    refine ⟨h0'.trans ?_, h1'.trans ?_⟩
    · nlinarith [mul_nonneg (by rw [hKc]; linarith : (0 : ℝ) ≤ Kc - (1 + 1)) (mul_nonneg hGp q0)]
    · nlinarith [mul_nonneg (by rw [hKc]; linarith : (0 : ℝ) ≤ Kc - (2 * K1 + 2 * K1 + (1 + 1))) (mul_nonneg hGp q1)]
  set M : ℝ := 576 * Kc * G * E * u0 ^ (-(5 / 2 : ℝ)) with hM
  set V : ℝ := 128 * Kc * G * E * u0 ^ (-(5 / 2 : ℝ)) with hV
  have hu52 : 0 ≤ u0 ^ (-(5 / 2 : ℝ)) := Real.rpow_nonneg hu0p.le _
  have hKG : 0 ≤ Kc * G := mul_nonneg hKc0 hG
  have hzoneA : ∀ x, u0 / 4 ≤ |x| → |x| ^ (-(5 / 2 : ℝ)) ≤ 64 * u0 ^ (-(5 / 2 : ℝ)) := by
    intro x hx
    calc |x| ^ (-(5 / 2 : ℝ)) ≤ (u0 / 4) ^ (-(5 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hR2 hx (by norm_num)
      _ = (4 : ℝ) ^ (5 / 2 : ℝ) * u0 ^ (-(5 / 2 : ℝ)) := quarter_rpow hu0p _
      _ ≤ 64 * u0 ^ (-(5 / 2 : ℝ)) := by
          gcongr
          exact four_rpow_le (by norm_num) (by norm_num)
  have hMb : ∀ x, ‖(η x : ℂ) * g x‖ ≤ M := by
    intro x
    by_cases hin : u0 / 4 ≤ |x| ∧ |x| ≤ 3 * u0
    · refine (hleib x hin.1 hin.2).1.trans ?_
      have hx2 : x ^ 2 ≤ (3 * u0) ^ 2 := by
        rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) hin.2 2
      have hLx : L + ε ^ 2 * x ^ 2 ≤ 9 * E := by
        have : ε ^ 2 * x ^ 2 ≤ ε ^ 2 * (3 * u0) ^ 2 := by gcongr
        rw [hE]; nlinarith [sq_nonneg ε, sq_nonneg u0, mul_nonneg (sq_nonneg ε) (sq_nonneg u0)]
      have hA := hzoneA x hin.1
      have q0 : 0 ≤ |x| ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
      calc Kc * (G * (L + ε ^ 2 * x ^ 2)) * |x| ^ (-(5 / 2 : ℝ)) ≤ Kc * (G * (9 * E)) * (64 * u0 ^ (-(5 / 2 : ℝ))) := by
            gcongr
        _ = M := by rw [hM]; ring
    · have h0 : η x = 0 := by
        rcases not_and_or.1 hin with h | h
        · exact hηsmall x (not_le.1 h).le
        · exact hηbig x (not_le.1 h).le
      rw [h0]; simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      rw [hM]; positivity
  set d : ℝ → ℝ := fun y => Kc * G * (L * y ^ (-(7 / 2 : ℝ)) + ε ^ 2 * y ^ (-(3 / 2 : ℝ))) with hd
  have hdb : ∀ x, u0 / 4 ≤ |x| → |x| ≤ 3 * u0 → ‖deriv (fun y => (η y : ℂ) * g y) x‖ ≤ d |x| := by
    intro x h1 h2
    refine (hleib x h1 h2).2.trans (le_of_eq ?_)
    have hax : 0 < |x| := by linarith
    have e : |x| ^ (-(7 / 2 : ℝ)) * |x| ^ 2 = |x| ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hax]; norm_num
    have e2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    simp only [hd]
    rw [e2, ← e]; ring
  have hdi : IntegrableOn d (Set.Icc (u0 / 4) (3 * u0)) := by
    have h1 := contOn_rpow_Icc (β := 3 * u0) hR2 (-(7 / 2 : ℝ))
    have h2 := contOn_rpow_Icc (β := 3 * u0) hR2 (-(3 / 2 : ℝ))
    refine ContinuousOn.integrableOn_Icc ?_
    simp only [hd]
    fun_prop
  have hVb : ∫ x in Set.Icc (u0 / 4) (3 * u0), d x ≤ V := by
    have i1 : IntegrableOn (fun x : ℝ => x ^ (-(7 / 2 : ℝ))) (Set.Icc (u0 / 4) (3 * u0)) :=
      (contOn_rpow_Icc hR2 _).integrableOn_Icc
    have i2 : IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Set.Icc (u0 / 4) (3 * u0)) :=
      (contOn_rpow_Icc hR2 _).integrableOn_Icc
    obtain ⟨I1, hI1⟩ : ∃ I, I = ∫ x in Set.Icc (u0 / 4) (3 * u0), x ^ (-(7 / 2 : ℝ)) := ⟨_, rfl⟩
    obtain ⟨I2, hI2⟩ : ∃ I, I = ∫ x in Set.Icc (u0 / 4) (3 * u0), x ^ (-(3 / 2 : ℝ)) := ⟨_, rfl⟩
    have hsplit : ∫ x in Set.Icc (u0 / 4) (3 * u0), d x = Kc * G * (L * I1 + ε ^ 2 * I2) := by
      have h : ∫ x in Set.Icc (u0 / 4) (3 * u0), d x =
          ∫ x in Set.Icc (u0 / 4) (3 * u0), ((Kc * G * L) * x ^ (-(7 / 2 : ℝ)) + (Kc * G * ε ^ 2) * x ^ (-(3 / 2 : ℝ))) := by
        refine setIntegral_congr_fun measurableSet_Icc (fun x _ => ?_)
        simp only [hd]; ring
      rw [h, integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul, ← hI1, ← hI2]
      ring
    have t1 := int_rpow_tail_le (β := 3 * u0) hR2 (t := 7 / 2) (by norm_num)
    have t2 := int_rpow_tail_le (β := 3 * u0) hR2 (t := 3 / 2) (by norm_num)
    have a1 : (u0 / 4) ^ (1 - 7 / 2 : ℝ) = (4 : ℝ) ^ (5 / 2 : ℝ) * u0 ^ (-(5 / 2 : ℝ)) := by
      rw [← quarter_rpow hu0p]; norm_num
    have a2 : (u0 / 4) ^ (1 - 3 / 2 : ℝ) = (4 : ℝ) ^ (1 / 2 : ℝ) * u0 ^ (-(1 / 2 : ℝ)) := by
      rw [← quarter_rpow hu0p]; norm_num
    rw [a1, ← hI1] at t1; rw [a2, ← hI2] at t2
    have f1 : (4 : ℝ) ^ (5 / 2 : ℝ) ≤ 64 := four_rpow_le (by norm_num) (by norm_num)
    have f2 : (4 : ℝ) ^ (1 / 2 : ℝ) ≤ 64 := four_rpow_le (by norm_num) (by norm_num)
    have e1 : u0 ^ (-(1 / 2 : ℝ)) = u0 ^ 2 * u0 ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hu0p]; norm_num
    have b1 : I1 ≤ 26 * u0 ^ (-(5 / 2 : ℝ)) := by
      refine t1.trans ?_
      have h64 : (4 : ℝ) ^ (5 / 2 : ℝ) * u0 ^ (-(5 / 2 : ℝ)) ≤ 64 * u0 ^ (-(5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right f1 hu52
      have : (4 : ℝ) ^ (5 / 2 : ℝ) * u0 ^ (-(5 / 2 : ℝ)) / (7 / 2 - 1) ≤ 64 * u0 ^ (-(5 / 2 : ℝ)) / (7 / 2 - 1) :=
        div_le_div_of_nonneg_right h64 (by norm_num)
      refine this.trans ?_
      have : 64 * u0 ^ (-(5 / 2 : ℝ)) / (7 / 2 - 1) = 25.6 * u0 ^ (-(5 / 2 : ℝ)) := by ring
      rw [this]; linarith
    have b2 : I2 ≤ 128 * (u0 ^ 2 * u0 ^ (-(5 / 2 : ℝ))) := by
      refine t2.trans ?_
      have hu12 : 0 ≤ u0 ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hu0p.le _
      have h64 : (4 : ℝ) ^ (1 / 2 : ℝ) * u0 ^ (-(1 / 2 : ℝ)) ≤ 64 * u0 ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right f2 hu12
      have : (4 : ℝ) ^ (1 / 2 : ℝ) * u0 ^ (-(1 / 2 : ℝ)) / (3 / 2 - 1) ≤ 64 * u0 ^ (-(1 / 2 : ℝ)) / (3 / 2 - 1) :=
        div_le_div_of_nonneg_right h64 (by norm_num)
      refine this.trans ?_
      have h2 : 64 * u0 ^ (-(1 / 2 : ℝ)) / (3 / 2 - 1) = 128 * u0 ^ (-(1 / 2 : ℝ)) := by ring
      rw [h2, e1]
    rw [hsplit, hV, hE]
    have h1 : L * I1 ≤ L * (26 * u0 ^ (-(5 / 2 : ℝ))) := mul_le_mul_of_nonneg_left b1 hL
    have h2 : ε ^ 2 * I2 ≤ ε ^ 2 * (128 * (u0 ^ 2 * u0 ^ (-(5 / 2 : ℝ)))) := mul_le_mul_of_nonneg_left b2 (sq_nonneg ε)
    have h3 : Kc * G * (L * I1 + ε ^ 2 * I2) ≤
        Kc * G * (L * (26 * u0 ^ (-(5 / 2 : ℝ))) + ε ^ 2 * (128 * (u0 ^ 2 * u0 ^ (-(5 / 2 : ℝ))))) :=
      mul_le_mul_of_nonneg_left (add_le_add h1 h2) hKG
    refine h3.trans ?_
    have := stat_arith (Kc * G) L (ε ^ 2) (u0 ^ 2) (u0 ^ (-(5 / 2 : ℝ))) hKG hL hu52
    calc _ ≤ 128 * (Kc * G) * (L + ε ^ 2 * u0 ^ 2) * u0 ^ (-(5 / 2 : ℝ)) := this
      _ = _ := by ring
  have hmain := vdc_sym (a := fun u => (η u : ℂ) * g u) (a0 := Real.pi ^ 2 * u0 ^ 2 / 12) (α := u0 / 4) (β := 3 * u0)
    (M := M) (V := V) (d := d) hR2 (by linarith) hAC
    (fun x hx => by simp [hηsmall x (by linarith)])
    (fun x hx => by simp [hηbig x (by linarith)])
    hMb hdb hdi hVb
  -- final arithmetic
  set r : ℝ := Real.sqrt u0 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hu0p
  have hq5 : u0 ^ (-(5 / 2 : ℝ)) = 1 / r ^ 5 := rpow_neg_half_sqrt hu0p 5 (5 / 2) (by norm_num)
  have hw : r / 2 ≤ Real.sqrt (Real.pi ^ 2 * (u0 / 4) / 6) := by
    calc r / 2 = Real.sqrt ((r / 2) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Real.pi ^ 2 * (u0 / 4) / 6) := by
          apply Real.sqrt_le_sqrt
          have h1 : r ^ 2 = u0 := Real.sq_sqrt hu0p.le
          have h2 : (6 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
          have : (r / 2) ^ 2 = u0 / 4 := by rw [div_pow, h1]; norm_num
          rw [this]
          nlinarith
  have hMV : M + V = 704 * Kc * G * E * (1 / r ^ 5) := by rw [hM, hV, hq5]; ring
  have hMV0 : 0 ≤ M + V := by rw [hMV]; positivity
  have hdiv : 8 * (M + V) / Real.sqrt (Real.pi ^ 2 * (u0 / 4) / 6) ≤ 8 * (M + V) / (r / 2) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hw
  have h6 : r ^ 6 = u0 ^ 3 := sqrt_pow6 hu0p
  have hfin : 2 * (8 * (M + V) / (r / 2)) = 22528 * Kc * G * E * (1 / u0 ^ 3) := by
    rw [hMV, ← h6]; field_simp; ring
  have hE0' : 0 ≤ Kc * G * E * (1 / u0 ^ 3) := by positivity
  calc _ ≤ 2 * (8 * (M + V) / Real.sqrt (Real.pi ^ 2 * (u0 / 4) / 6)) := hmain
    _ ≤ 2 * (8 * (M + V) / (r / 2)) := by gcongr
    _ = 22528 * Kc * G * E * (1 / u0 ^ 3) := hfin
    _ ≤ _ := by
        rw [hE]
        nlinarith [hE0']


set_option maxHeartbeats 1600000 in
/-- **Far zone** `3u₀/2 ≤ |u| ≤ 0.18/ε`: two integrations by parts with `|ψ'| ≥ 5π²u²/108`, using `L ≤ ε²u₀²`. -/
theorem zone_far {ϑ : ℝ → ℝ} {K1 K2 Z0 Z1 Z2 : ℝ} (hϑ : Prof ϑ K1 K2) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1) (hZ2 : 0 ≤ Z2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ζ : ℝ → ℝ} {u0 ε L G : ℝ} {g : ℝ → ℂ}, IsCut ζ Z0 Z1 Z2 → (∀ u, ε * |u| ≤ 0.075 → ζ u = 1) →
      (∀ u, 0.18 ≤ ε * |u| → ζ u = 0) → 34 ≤ u0 → 0 < ε → 0 ≤ L → 0 ≤ G → ε * u0 ≤ 0.05 →
      L ≤ ε ^ 2 * u0 ^ 2 → LargeZone g G L ε →
      Integrable (fun u => ((ζ u - ϑ (u / (3 * u0 / 2)) : ℝ) : ℂ) * g u * Complex.exp (Complex.I * ((Real.pi ^ 2 * u0 ^ 2 / 12 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))) ∧
      ‖oscInt (Real.pi ^ 2 * u0 ^ 2 / 12) (fun u => ((ζ u - ϑ (u / (3 * u0 / 2)) : ℝ) : ℂ) * g u)‖ ≤
        C * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) := by
  set Kc : ℝ := (Z2 + 4 * K2) + 2 * (Z1 + 2 * K1) + (Z0 + 1) with hKc
  have hk1 := hϑ.hK1
  have hk2 := hϑ.hK2
  have hKc0 : 0 ≤ Kc := by positivity
  set q0 : ℝ := 5 * Real.pi ^ 2 / 108 with hq0
  have hq0p : 0 < q0 := by positivity
  have hcC := cubicC_nonneg hq0p
  refine ⟨8 * Kc * cubicC q0, by positivity, ?_⟩
  intro ζ u0 ε L G g hζ hζ1 hζ0 hu0 hε hL hG hεu hLe hz
  have hu0p : 0 < u0 := by linarith
  have hR1 : 0 < 3 * u0 / 2 := by positivity
  have hη0 := hζ.sub (hϑ.cut hR1)
  set η : ℝ → ℝ := fun u => ζ u - ϑ (u / (3 * u0 / 2)) with hηdef
  have hεR : ε * (3 * u0 / 2) ≤ 0.075 := by nlinarith
  have hηsmall : ∀ u, |u| ≤ 3 * u0 / 2 → η u = 0 := by
    intro u hu
    have h2 : ϑ (u / (3 * u0 / 2)) = 1 := by
      apply hϑ.one
      rw [abs_div, abs_of_pos hR1, div_le_one hR1]; exact hu
    have h1 : ζ u = 1 := hζ1 u (by nlinarith [abs_nonneg u])
    have e : η u = ζ u - ϑ (u / (3 * u0 / 2)) := rfl
    rw [e, h1, h2]; ring
  have hηbig : ∀ u, 0.18 / ε ≤ |u| → η u = 0 := by
    intro u hu
    have hu' : 0.18 ≤ ε * |u| := by rwa [div_le_iff₀ hε, mul_comm] at hu
    have h1 : ζ u = 0 := hζ0 u hu'
    have h2 : ϑ (u / (3 * u0 / 2)) = 0 := by
      apply hϑ.zero
      rw [abs_div, abs_of_pos hR1, le_div_iff₀ hR1]
      nlinarith
    have e : η u = ζ u - ϑ (u / (3 * u0 / 2)) := rfl
    rw [e, h1, h2]; ring
  have hcd : ∀ u, 3 * u0 / 2 ≤ |u| → |u| ≤ 0.18 / ε → ContDiffAt ℝ 2 g u := fun u h1 h2 =>
    hz.cd u (by linarith) (by rwa [le_div_iff₀ hε, mul_comm] at h2)
  have hAC := cut_mul_contDiff hη0.contDiff hηsmall hηbig hcd
  refine ⟨integrable_osc_R (f := fun u => (η u : ℂ) * g u) (R := 0.18 / ε) (by positivity) hAC.continuous (fun u hu => by simp [hηbig u hu]) _, ?_⟩
  set B : ℝ := 2 * Kc * G * ε ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hleib : ∀ x, 3 * u0 / 2 ≤ |x| → |x| ≤ 0.18 / ε →
      ‖(η x : ℂ) * g x‖ ≤ B * |x| ^ (-(1 / 2 : ℝ)) ∧
      ‖deriv (fun y => (η y : ℂ) * g y) x‖ ≤ B * |x| ^ (-(1 / 2 : ℝ) - 1) ∧
      ‖deriv (deriv (fun y => (η y : ℂ) * g y)) x‖ ≤ B * |x| ^ (-(1 / 2 : ℝ) - 2) := by
    intro x h1 h2
    have hx1 : 1 ≤ |x| := by linarith
    have hax : 0 < |x| := by linarith
    have hx0 : x ≠ 0 := abs_ne_zero.mp hax.ne'
    have hεx : ε * |x| ≤ 0.18 := by rwa [le_div_iff₀ hε, mul_comm] at h2
    have hL' := leibniz_cut hη0 (hz.cd x hx1 hεx) (G := G * (L + ε ^ 2 * x ^ 2)) (s := 5 / 2) (x := x)
      (by positivity) hx0 (hz.b0 x hx1 hεx)
      (by have := hz.b1 x hx1 hεx; rwa [show (-(7 / 2) : ℝ) = -(5 / 2) - 1 by norm_num] at this)
      (by have := hz.b2 x hx1 hεx; rwa [show (-(9 / 2) : ℝ) = -(5 / 2) - 2 by norm_num] at this)
    obtain ⟨h0', h1', h2'⟩ := hL'
    have hx2 : (9 / 4) * u0 ^ 2 ≤ x ^ 2 := by
      rw [← sq_abs x]
      nlinarith
    have hLx : L + ε ^ 2 * x ^ 2 ≤ 2 * (ε ^ 2 * x ^ 2) := by
      have : L ≤ ε ^ 2 * x ^ 2 := by
        calc L ≤ ε ^ 2 * u0 ^ 2 := hLe
          _ ≤ ε ^ 2 * x ^ 2 := by
              have : u0 ^ 2 ≤ x ^ 2 := by nlinarith [hx2, sq_nonneg u0]
              exact mul_le_mul_of_nonneg_left this (sq_nonneg ε)
      linarith
    have hGx : G * (L + ε ^ 2 * x ^ 2) ≤ G * (2 * (ε ^ 2 * x ^ 2)) := by gcongr
    have hpw : ∀ t : ℝ, |x| ^ 2 * |x| ^ t = |x| ^ (t + 2) := by
      intro t
      rw [← Real.rpow_natCast, ← Real.rpow_add hax]; norm_num; ring_nf
    have hx2' : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    have key : ∀ (c t t' : ℝ), 0 ≤ c → c ≤ Kc → t' = t + 2 →
        c * (G * (L + ε ^ 2 * x ^ 2)) * |x| ^ t ≤ B * |x| ^ t' := by
      intro c t t' hc hcK ht
      have hq : 0 ≤ |x| ^ t := Real.rpow_nonneg hax.le _
      have hGp : 0 ≤ G * (L + ε ^ 2 * x ^ 2) := by positivity
      calc c * (G * (L + ε ^ 2 * x ^ 2)) * |x| ^ t ≤ Kc * (G * (2 * (ε ^ 2 * x ^ 2))) * |x| ^ t := by
            gcongr
        _ = 2 * Kc * G * ε ^ 2 * (|x| ^ 2 * |x| ^ t) := by rw [hx2']; ring
        _ = B * |x| ^ t' := by rw [hpw, ht, hB]
    refine ⟨h0'.trans (key _ _ _ (by positivity) (by linarith) (by norm_num)),
      h1'.trans (key _ _ _ (by positivity) (by linarith) (by norm_num)),
      h2'.trans (key _ _ _ (by positivity) (by linarith) (by norm_num))⟩
  have hmain := ibp_gen_sym (a := fun u => (η u : ℂ) * g u) (a0 := Real.pi ^ 2 * u0 ^ 2 / 12) (α := 3 * u0 / 2)
    (β := 0.18 / ε) (B := B) (q := q0) (s := 1 / 2) hR1 (by
      rw [le_div_iff₀ hε]; nlinarith) hB0 hq0p (by norm_num) hAC
    (fun x hx => by simp [hηsmall x hx.le])
    (fun x hx => by simp [hηbig x hx.le])
    (fun x h1 h2 => (hleib x h1 h2).1) (fun x h1 h2 => (hleib x h1 h2).2.1) (fun x h1 h2 => (hleib x h1 h2).2.2)
    (fun x h1 h2 => by
      have hx2 : (9 / 4) * u0 ^ 2 ≤ x ^ 2 := by
        rw [← sq_abs x]; nlinarith
      have hneg : Real.pi ^ 2 * u0 ^ 2 / 12 - Real.pi ^ 2 * x ^ 2 / 12 ≤ 0 := by nlinarith [Real.pi_pos]
      rw [abs_of_nonpos hneg, hq0]
      have hp2 : 0 < Real.pi ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hx2 hp2.le])
  -- final arithmetic
  have hα : (3 * u0 / 2) ^ (-(1 / 2 + 5 : ℝ)) ≤ 1 / u0 ^ 3 := by
    calc (3 * u0 / 2) ^ (-(1 / 2 + 5 : ℝ)) ≤ u0 ^ (-(1 / 2 + 5 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hu0p (by linarith) (by norm_num)
      _ ≤ u0 ^ (-(3 : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 1 / u0 ^ 3 := by rw [Real.rpow_neg hu0p.le, one_div]; norm_cast
  have hαn : 0 ≤ (3 * u0 / 2) ^ (-(1 / 2 + 5 : ℝ)) := Real.rpow_nonneg hR1.le _
  have hE : ε ^ 2 ≤ L + ε ^ 2 * u0 ^ 2 := by
    have h1 : (1 : ℝ) ≤ u0 ^ 2 := by nlinarith
    have : ε ^ 2 ≤ ε ^ 2 * u0 ^ 2 := by
      calc ε ^ 2 = ε ^ 2 * 1 := (mul_one _).symm
        _ ≤ ε ^ 2 * u0 ^ 2 := mul_le_mul_of_nonneg_left h1 (sq_nonneg ε)
    linarith
  have h2 : (3 * u0 / 2) ^ (-(1 / 2 + 5 : ℝ)) / (1 / 2 + 5) ≤ 1 / u0 ^ 3 := by
    calc _ ≤ (3 * u0 / 2) ^ (-(1 / 2 + 5 : ℝ)) := div_le_self hαn (by norm_num)
      _ ≤ _ := hα
  have hBC : 0 ≤ B * cubicC q0 := mul_nonneg hB0 hcC
  calc _ ≤ 2 * (B * cubicC q0 * ((3 * u0 / 2) ^ (-(1 / 2 + 5 : ℝ)) / (1 / 2 + 5))) := hmain
    _ ≤ 2 * (B * cubicC q0 * (1 / u0 ^ 3)) := by gcongr
    _ = 4 * Kc * cubicC q0 * G * ε ^ 2 * (1 / u0 ^ 3) := by rw [hB]; ring
    _ ≤ 8 * Kc * cubicC q0 * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) := by
        have hu3 : 0 ≤ 1 / u0 ^ 3 := by positivity
        have hP : 0 ≤ Kc * cubicC q0 * G * (1 / u0 ^ 3) := by positivity
        have := mul_le_mul_of_nonneg_left hE hP
        nlinarith [this, mul_nonneg hP (by positivity : (0 : ℝ) ≤ L + ε ^ 2 * u0 ^ 2)]

/-- info: 'FormalResearch.SignUncertainty.zone_shoulder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zone_shoulder

/-- info: 'FormalResearch.SignUncertainty.zone_stationary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zone_stationary

/-- info: 'FormalResearch.SignUncertainty.zone_far' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zone_far

end FormalResearch.SignUncertainty

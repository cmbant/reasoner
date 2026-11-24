module

public import FormalResearch.SignUncertainty.MiddleBandZones

/-!
# GT.2a: the inner difference integral

Source: `CFT/sign_uncertainty/paper/u1c_estimate_proofs.tex`, proof of `cegt:GT2a`, "Inner difference" (the decomposition
`χ = χ_z + χ_st + χ_far` and the four regional estimates).  The outer cutoff `ζ` is any `IsCut` function equal to `1` for `ε|u| ≤ 0.075` and `0` for `ε|u| ≥ 0.18` (so both `ϑ(εu/0.09)` and `ϑ(t(εu)/ρ)` qualify).

* `inner_integral_bound`: for an amplitude `g` with the large-zone bounds `(e8)` (`LargeZone g G L ε`) and the near-zero bounds
  (`g(0) = g₀`, `|g(u) - g₀| ≤ G₀|u|^{1/2}`, `|g'| ≤ G₀|u|^{-1/2}`, `|g''| ≤ G₀|u|^{-3/2}` on `0 < |u| < 3`),
  `‖∫ ζ(u) g(u) e^{iψ(u)} du‖ ≤ C (G (L + ε²u₀²) + G₀) u₀^{-3}`, `ψ(u) = (π²u₀²/12) u - π²u³/36`.

Status: proved, unconditional (pointwise hypotheses on `g`).
-/

@[expose] public section

open MeasureTheory Set

namespace FormalResearch.SignUncertainty

lemma oscInt_add4 {f1 f2 f3 f4 : ℝ → ℂ} (a0 : ℝ)
    (h1 : Integrable (fun u => f1 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))))
    (h2 : Integrable (fun u => f2 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))))
    (h3 : Integrable (fun u => f3 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ))))
    (h4 : Integrable (fun u => f4 u * Complex.exp (Complex.I * ((a0 * u - Real.pi ^ 2 / 36 * u ^ 3 : ℝ) : ℂ)))) :
    oscInt a0 (fun u => f1 u + f2 u + f3 u + f4 u) = oscInt a0 f1 + oscInt a0 f2 + oscInt a0 f3 + oscInt a0 f4 := by
  unfold oscInt
  rw [← integral_add h1 h2, ← integral_add (by exact h1.add h2) h3, ← integral_add (by exact (h1.add h2).add h3) h4]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  show (f1 u + f2 u + f3 u + f4 u) * _ = f1 u * _ + f2 u * _ + f3 u * _ + f4 u * _
  ring

lemma p0_rpow_le {u0 : ℝ} (hu : 34 ≤ u0) : (Real.pi ^ 2 * u0 ^ 2 / 24) ^ (-(3 / 2 : ℝ)) ≤ 9 * (1 / u0 ^ 3) := by
  have hu0 : 0 < u0 := by linarith
  have hπ : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hle : u0 ^ 2 / 3 ≤ Real.pi ^ 2 * u0 ^ 2 / 24 := by nlinarith [sq_nonneg u0]
  have h3 : (3 : ℝ) ^ (3 / 2 : ℝ) ≤ 9 := by
    calc (3 : ℝ) ^ (3 / 2 : ℝ) ≤ (3 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 9 := by norm_num
  calc (Real.pi ^ 2 * u0 ^ 2 / 24) ^ (-(3 / 2 : ℝ)) ≤ (u0 ^ 2 / 3) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
    _ = (u0 ^ 2) ^ (-(3 / 2 : ℝ)) * (3 : ℝ) ^ (3 / 2 : ℝ) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), div_inv_eq_mul]
    _ = 1 / u0 ^ 3 * (3 : ℝ) ^ (3 / 2 : ℝ) := by
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul hu0.le, show ((2 : ℕ) : ℝ) * -(3 / 2) = -(3 : ℝ) by norm_num,
          Real.rpow_neg hu0.le, one_div]
        norm_cast
    _ ≤ 1 / u0 ^ 3 * 9 := by gcongr
    _ = 9 * (1 / u0 ^ 3) := by ring


/-- **The inner difference integral.** -/
theorem inner_integral_bound {ϑ : ℝ → ℝ} {K1 K2 Z0 Z1 Z2 : ℝ} (hϑ : Prof ϑ K1 K2) (hZ0 : 0 ≤ Z0) (hZ1 : 0 ≤ Z1)
    (hZ2 : 0 ≤ Z2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ζ : ℝ → ℝ} {u0 ε L G G0 : ℝ} {g : ℝ → ℂ} {g0 : ℂ}, IsCut ζ Z0 Z1 Z2 →
      (∀ u, ε * |u| ≤ 0.075 → ζ u = 1) → (∀ u, 0.18 ≤ ε * |u| → ζ u = 0) →
      34 ≤ u0 → 0 < ε → 0 ≤ L → 0 ≤ G → 0 ≤ G0 →
      ε * u0 ≤ 0.05 → L ≤ ε ^ 2 * u0 ^ 2 → LargeZone g G L ε →
      g 0 = g0 → ‖g0‖ ≤ G0 →
      (∀ u, 0 < |u| → |u| < 3 → ContDiffAt ℝ 2 g u) →
      (∀ u, 0 < |u| → |u| < 3 → ‖g u - g0‖ ≤ G0 * |u| ^ (1 / 2 : ℝ)) →
      (∀ u, 0 < |u| → |u| < 3 → ‖deriv g u‖ ≤ G0 * |u| ^ (-(1 / 2 : ℝ))) →
      (∀ u, 0 < |u| → |u| < 3 → ‖deriv (deriv g) u‖ ≤ G0 * |u| ^ (-(3 / 2 : ℝ))) →
      ‖oscInt (Real.pi ^ 2 * u0 ^ 2 / 12) (fun u => (ζ u : ℂ) * g u)‖ ≤
        C * (G * (L + ε ^ 2 * u0 ^ 2) + G0) * (1 / u0 ^ 3) := by
  obtain ⟨Cn, hCn0, hn⟩ := near_zero_bound hϑ
  obtain ⟨Cs, hCs0, hs⟩ := zone_shoulder hϑ
  obtain ⟨Ct, hCt0, ht⟩ := zone_stationary hϑ
  obtain ⟨Cf, hCf0, hf⟩ := zone_far hϑ hZ0 hZ1 hZ2
  refine ⟨9 * Cn + Cs + Ct + Cf, by positivity, ?_⟩
  intro ζ u0 ε L G G0 g g0 hζ hζ1 hζ0 hu0 hε hL hG hG0 hεu hLe hz hg0 hgG0 hc hH hd1 hd2
  have hu0p : 0 < u0 := by linarith
  set a0 : ℝ := Real.pi ^ 2 * u0 ^ 2 / 12 with ha0
  set p0 : ℝ := Real.pi ^ 2 * u0 ^ 2 / 24 with hp0
  have hπ : (8 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_d2]
  have hu2 : (1156 : ℝ) ≤ u0 ^ 2 := by nlinarith
  have hp2 : 2 ≤ p0 := by
    rw [hp0]
    nlinarith [mul_le_mul hπ hu2 (by norm_num) (by positivity : (0 : ℝ) ≤ Real.pi ^ 2)]
  have hgrad : ∀ x, |x| ≤ 2 → p0 ≤ a0 - Real.pi ^ 2 * x ^ 2 / 12 := by
    intro x hx
    have hx2 : x ^ 2 ≤ 4 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
    rw [hp0, ha0]
    nlinarith [mul_le_mul_of_nonneg_left hx2 (by positivity : (0 : ℝ) ≤ Real.pi ^ 2), sq_nonneg u0]
  have hεu' : ε * u0 ≤ 0.36 := by linarith
  obtain ⟨I1, B1⟩ := hn (a0 := a0) (p0 := p0) (G := G0) hp2 hG0 hg0 hgG0 hgrad hc hH hd1 hd2
  obtain ⟨I2, B2⟩ := hs hu0 hε hL hG hεu' hz
  obtain ⟨I3, B3⟩ := ht hu0 hε hL hG hεu hz
  obtain ⟨I4, B4⟩ := hf hζ hζ1 hζ0 hu0 hε hL hG hεu hLe hz
  have hsum : oscInt a0 (fun u => (ζ u : ℂ) * g u) =
      oscInt a0 (fun u => (ϑ u : ℂ) * g u) + oscInt a0 (fun u => ((ϑ (u / (u0 / 4)) - ϑ u : ℝ) : ℂ) * g u) +
      oscInt a0 (fun u => ((ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) : ℝ) : ℂ) * g u) +
      oscInt a0 (fun u => ((ζ u - ϑ (u / (3 * u0 / 2)) : ℝ) : ℂ) * g u) := by
    rw [← oscInt_add4 a0 I1 I2 I3 I4]
    congr 1
    funext u
    push_cast
    ring
  rw [hsum]
  have hn' : ‖oscInt a0 (fun u => (ϑ u : ℂ) * g u)‖ ≤ Cn * G0 * (9 * (1 / u0 ^ 3)) :=
    B1.trans (by
      have := p0_rpow_le hu0
      have hCG : 0 ≤ Cn * G0 := by positivity
      exact mul_le_mul_of_nonneg_left this hCG)
  have hu3 : 0 ≤ 1 / u0 ^ 3 := by positivity
  have hE : 0 ≤ G * (L + ε ^ 2 * u0 ^ 2) := by positivity
  calc _ ≤ ‖oscInt a0 (fun u => (ϑ u : ℂ) * g u)‖ + ‖oscInt a0 (fun u => ((ϑ (u / (u0 / 4)) - ϑ u : ℝ) : ℂ) * g u)‖ +
        ‖oscInt a0 (fun u => ((ϑ (u / (3 * u0 / 2)) - ϑ (u / (u0 / 4)) : ℝ) : ℂ) * g u)‖ +
        ‖oscInt a0 (fun u => ((ζ u - ϑ (u / (3 * u0 / 2)) : ℝ) : ℂ) * g u)‖ := by
        refine (norm_add_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ Cn * G0 * (9 * (1 / u0 ^ 3)) + Cs * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) +
        Ct * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) + Cf * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) := by
        gcongr
    _ ≤ _ := by
        have e : (9 * Cn + Cs + Ct + Cf) * (G * (L + ε ^ 2 * u0 ^ 2) + G0) * (1 / u0 ^ 3) -
            (Cn * G0 * (9 * (1 / u0 ^ 3)) + Cs * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) +
              Ct * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3) + Cf * G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3)) =
            9 * Cn * (G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3)) + (Cs + Ct + Cf) * (G0 * (1 / u0 ^ 3)) := by ring
        have : 0 ≤ 9 * Cn * (G * (L + ε ^ 2 * u0 ^ 2) * (1 / u0 ^ 3)) + (Cs + Ct + Cf) * (G0 * (1 / u0 ^ 3)) := by positivity
        linarith

/-- info: 'FormalResearch.SignUncertainty.inner_integral_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms inner_integral_bound

end FormalResearch.SignUncertainty

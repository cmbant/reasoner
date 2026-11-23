module

public import FormalResearch.ModularBootstrap.Upper.Assembly.Feasible
public import FormalResearch.ModularBootstrap.Upper.Rigidity.CrossingDictionary

/-!
# The Airy chart of the crossing dictionary against the tip chart of the combs

Source: `CFT/modular_bootstrap/paper/spectral_rigidity.tex` (§1, the variable `u(t)`),
`upper_transfer.tex` (`ut:ID`, `σ ↦ u = -κ σ`).

With `λ = (k_tip c)^{-2/3}`, `κ = (3π/2)^{2/3}`, `β = κ k_tip^{2/3}` (`betaTip_eq`), the tip chart
`x = ξ_* + λ σ` and the Airy chart `u = -β (x - ξ_*) c^{2/3}` are related by `u = -κ σ`:

* `slopeAiry_eq`: `ε/β = λ/κ`;
* `tAiry_eq`: `t(u) = c x²/3` for `x = ξ_* + λ (-u/κ) ≥ 0`;
* `jAiry_eq`: `J = (dt/dσ)/κ`, `dt/dσ = (2 c x/3) λ`;
* `uAiry_designTf`: `u(t_f + 1) → a_1 - d` as `c → ∞` (the first site `u_f`).

All results are proved unconditionally.
-/

@[expose] public section

open Real Filter Topology Set
open scoped Real

namespace FormalResearch.ModularBootstrap.Upper.Assembly

open FormalResearch.Special FormalResearch.ModularBootstrap FormalResearch.ModularBootstrap.Upper.Rigidity
  FormalResearch.ModularBootstrap.Upper.Comb FormalResearch.ModularBootstrap.Upper.Design
  FormalResearch.ModularBootstrap.Upper.Window FormalResearch.ModularBootstrap.Upper.Window.Cardy

lemma rpow_neg_two_thirds {c : ℝ} (hc : 0 < c) :
    c ^ (-((2 : ℝ) / 3)) = 1 / (c ^ ((1 : ℝ) / 3)) ^ 2 := by
  rw [Real.rpow_neg hc.le, one_div]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  norm_num

lemma slopeAiry_eq {c : ℝ} (hc : 0 < c) : slopeAiry c = lambdaComb c / kappaAiry := by
  have hκ := kappaAiry_pos
  have hk := kTip_pos
  have ha : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hkk : 0 < kTip ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  unfold slopeAiry epsAiry
  rw [betaTip_eq, lambdaComb_eq hc, rpow_neg_two_thirds hc, Real.rpow_neg hk.le]
  field_simp

lemma bAiry_eq {c : ℝ} (hc : 0 < c) {u : ℝ}
    (hx : 0 ≤ xiStar + lambdaComb c * (-u / kappaAiry)) :
    bAiry c u = xiStar + lambdaComb c * (-u / kappaAiry) := by
  unfold bAiry
  rw [slopeAiry_eq hc]
  have : xiStar - u * (lambdaComb c / kappaAiry) = xiStar + lambdaComb c * (-u / kappaAiry) := by ring
  rw [this]
  exact max_eq_left hx

lemma tAiry_eq {c : ℝ} (hc : 0 < c) {u : ℝ}
    (hx : 0 ≤ xiStar + lambdaComb c * (-u / kappaAiry)) :
    tAiry c u = c * (xiStar + lambdaComb c * (-u / kappaAiry)) ^ 2 / 3 := by
  unfold tAiry
  rw [bAiry_eq hc hx]
  ring

lemma jAiry_eq {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    jAiry c (c * x ^ 2 / 3) = ((2 * c * x / 3) * lambdaComb c) / kappaAiry := by
  have hκ := kappaAiry_pos
  have hk := kTip_pos
  have ha : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
  have hkk : 0 < kTip ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hk _
  unfold jAiry
  have hs : √(3 * (c * x ^ 2 / 3) / c) = x := by
    rw [show 3 * (c * x ^ 2 / 3) / c = x ^ 2 by field_simp]
    exact Real.sqrt_sq hx
  rw [hs, betaTip_eq, lambdaComb_eq hc, Real.rpow_neg hk.le]
  generalize hA : c ^ ((1 : ℝ) / 3) = a at *
  have hc3 : c = a ^ 3 := by rw [← hA]; exact (rpow_third_cube hc).symm
  clear hA
  subst hc3
  field_simp

/-- The Jacobian identity in the form used for `Ψ_g`: `J · κ = dt/dσ`. -/
lemma jAiry_mul_kappa {c x : ℝ} (hc : 0 < c) (hx : 0 ≤ x) :
    jAiry c (c * x ^ 2 / 3) * kappaAiry = (2 * c * x / 3) * lambdaComb c := by
  rw [jAiry_eq hc hx]
  field_simp [kappaAiry_pos.ne']

/-- `u(t_f + 1) → -κ σ_1` (`θ_j → u_f`) for the first site `σ_1` of any modification. -/
theorem uAiry_sigTf (σs : ℕ → ℝ) :
    Tendsto (fun c => uAiry c (sigTf σs c + 1)) atTop (𝓝 (-(kappaAiry * σs 1))) := by
  have hβ := betaTip_pos
  have hxi := xiStar_pos
  set σ1 : ℝ := σs 1 with hσ1
  have hκ := kappaAiry_pos
  -- the error `u(t_f+1) - (a_1 - d) = -β c^{2/3} (√(χ² + 3/c) - χ)`
  have hmain : ∀ᶠ c : ℝ in atTop, |uAiry c (sigTf σs c + 1) - (-(kappaAiry * σ1))| ≤
      (3 * betaTip / xiStar) * c ^ (-((1 : ℝ) / 3)) := by
    have hl : ∀ᶠ c : ℝ in atTop, lambdaComb c * |σ1| ≤ xiStar / 2 := by
      have h := tendsto_lambdaComb_atTop.mul_const |σ1|
      rw [zero_mul] at h
      exact h.eventually_le_const (by positivity)
    filter_upwards [hl, eventually_gt_atTop (0 : ℝ)] with c hlc hc
    set χ : ℝ := xiStar + lambdaComb c * σ1 with hχ
    have hlam := lambdaComb_pos' hc
    have hχlo : xiStar / 2 ≤ χ := by
      have := neg_abs_le σ1
      nlinarith
    have hχpos : 0 < χ := by linarith
    have hT : sigTf σs c = c * χ ^ 2 / 3 := rfl
    have hsq : √(3 * (sigTf σs c + 1) / c) = √(χ ^ 2 + 3 / c) := by
      rw [hT]; congr 1; field_simp
    have hu : uAiry c (sigTf σs c + 1) = -betaTip * (√(χ ^ 2 + 3 / c) - χ) * c ^ ((2 : ℝ) / 3) -
        kappaAiry * σ1 := by
      unfold uAiry
      rw [hsq]
      have hlamc : betaTip * lambdaComb c * c ^ ((2 : ℝ) / 3) = kappaAiry := by
        rw [lambdaComb_eq hc, betaTip_eq, Real.rpow_neg (kTip_pos.le)]
        have ha : 0 < c ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
        have hkk : 0 < kTip ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos kTip_pos _
        have h23 : c ^ ((2 : ℝ) / 3) = (c ^ ((1 : ℝ) / 3)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; norm_num
        rw [h23]
        field_simp
      have : -betaTip * (√(χ ^ 2 + 3 / c) - xiStar) * c ^ ((2 : ℝ) / 3) =
          -betaTip * (√(χ ^ 2 + 3 / c) - χ) * c ^ ((2 : ℝ) / 3) -
            betaTip * lambdaComb c * c ^ ((2 : ℝ) / 3) * σ1 := by
        rw [hχ]; ring
      rw [this, hlamc]
    have hsqrt_ge : χ ≤ √(χ ^ 2 + 3 / c) := by
      calc χ = √(χ ^ 2) := (Real.sqrt_sq hχpos.le).symm
        _ ≤ _ := Real.sqrt_le_sqrt (by have : 0 < 3 / c := by positivity
                                       linarith)
    have hsqrt_le : √(χ ^ 2 + 3 / c) ≤ χ + 3 / (2 * c * χ) := by
      have h0 : 0 ≤ χ + 3 / (2 * c * χ) := by positivity
      rw [Real.sqrt_le_left h0]
      have : (χ + 3 / (2 * c * χ)) ^ 2 = χ ^ 2 + 3 / c + (3 / (2 * c * χ)) ^ 2 := by
        field_simp; ring
      rw [this]
      nlinarith [sq_nonneg (3 / (2 * c * χ))]
    rw [hu]
    have hc23 : c ^ ((2 : ℝ) / 3) * (3 / (2 * c * χ)) ≤ (3 / xiStar) * c ^ (-((1 : ℝ) / 3)) := by
      have e : c ^ ((2 : ℝ) / 3) * (3 / (2 * c * χ)) = (3 / (2 * χ)) * c ^ (-((1 : ℝ) / 3)) := by
        have : c ^ ((2 : ℝ) / 3) / c = c ^ (-((1 : ℝ) / 3)) := by
          have h2 : c ^ ((2 : ℝ) / 3) = c ^ (-((1 : ℝ) / 3)) * c := by
            conv_lhs => rw [show (2 : ℝ) / 3 = -((1 : ℝ) / 3) + 1 by norm_num]
            rw [Real.rpow_add hc, Real.rpow_one]
          rw [h2]; field_simp
        calc c ^ ((2 : ℝ) / 3) * (3 / (2 * c * χ)) = (3 / (2 * χ)) * (c ^ ((2 : ℝ) / 3) / c) := by
              field_simp
          _ = _ := by rw [this]
      rw [e]
      have hp : 0 < c ^ (-((1 : ℝ) / 3)) := Real.rpow_pos_of_pos hc _
      gcongr
      linarith
    have hpos : 0 ≤ √(χ ^ 2 + 3 / c) - χ := by linarith
    have hc2 : 0 < c ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hc _
    rw [show -betaTip * (√(χ ^ 2 + 3 / c) - χ) * c ^ ((2 : ℝ) / 3) - kappaAiry * σ1 -
        -(kappaAiry * σ1) = -(betaTip * (√(χ ^ 2 + 3 / c) - χ) * c ^ ((2 : ℝ) / 3)) by ring,
      abs_neg, abs_of_nonneg (by positivity)]
    calc betaTip * (√(χ ^ 2 + 3 / c) - χ) * c ^ ((2 : ℝ) / 3)
        ≤ betaTip * (3 / (2 * c * χ)) * c ^ ((2 : ℝ) / 3) := by gcongr; linarith
      _ = betaTip * (c ^ ((2 : ℝ) / 3) * (3 / (2 * c * χ))) := by ring
      _ ≤ betaTip * ((3 / xiStar) * c ^ (-((1 : ℝ) / 3))) := by gcongr
      _ = (3 * betaTip / xiStar) * c ^ (-((1 : ℝ) / 3)) := by ring
  have hlim : Tendsto (fun c : ℝ => (3 * betaTip / xiStar) * c ^ (-((1 : ℝ) / 3))) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).const_mul (3 * betaTip / xiStar)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hmain.mono fun c hc => by simpa [Real.norm_eq_abs] using hc) hlim

/-- `u(t_f + 1) → a_1 - d` (`θ_j → u_f`). -/
theorem uAiry_designTf (d : ℝ) :
    Tendsto (fun c => uAiry c (designTf d c + 1)) atTop (𝓝 (airyZero 1 - d)) := by
  have hκ := kappaAiry_pos
  have hσ1def : kappaAiry * designSigma1 d 1 = |airyZero 1| + d := by
    rw [designSigma1_one]; field_simp
  have hneg : airyZero 1 - d = -(kappaAiry * designSigma1 d 1) := by
    rw [hσ1def, abs_of_neg (airyZero_neg 1)]; ring
  rw [hneg]
  exact uAiry_sigTf (designSigma1 d)

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.uAiry_sigTf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uAiry_sigTf

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.uAiry_designTf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms uAiry_designTf

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.jAiry_mul_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms jAiry_mul_kappa

/-- info: 'FormalResearch.ModularBootstrap.Upper.Assembly.tAiry_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms tAiry_eq

end FormalResearch.ModularBootstrap.Upper.Assembly

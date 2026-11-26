module

public import FormalResearch.SignUncertainty.CtSdJoin
public import FormalResearch.SignUncertainty.CtSdCauchy
public import FormalResearch.SignUncertainty.CtSdAiry
public import FormalResearch.SignUncertainty.CtOuterBandTail

/-!
# Assembly of `(ct:K-airy)`: head + deformation + tail with cancelling join (`ct:cfu` Step 3, abstract form)

Source: `CFT/sign_uncertainty/paper/constant_terms_lower.tex`, Lemma `ct:cfu`, Step 3.  **Proved** (abstract form: hypotheses are the
pulled-back real identities `B(T s)T'(s) = N_c s^{1/2} g_s(s)`, `ϕ(T s) = a s + s³/3` and the holomorphic amplitude data).
-/

@[expose] public section

open Set Filter Topology MeasureTheory Metric Complex
open scoped Real Interval

namespace FormalResearch.SignUncertainty.CtSd

open FormalResearch.SignUncertainty.CtOsc FormalResearch.Special

/-- Real tail data for `piece3_gen`. -/
structure TailBd (C0 KB γ L τ1 : ℝ) (m m1 m2 m3 : ℝ → ℝ) (B B1 B2 : ℝ → ℂ) (ϕ : ℝ → ℝ) : Prop where
  hM : MData C0 m m1 m2 m3
  hKB : 0 ≤ KB
  hγ : 0 < γ
  hϕ : ∀ τ : ℝ, 0 < τ → HasDerivAt ϕ (m τ - L) τ
  hB : ∀ τ : ℝ, 0 < τ → HasDerivAt B (B1 τ) τ
  hB1 : ∀ τ : ℝ, 0 < τ → HasDerivAt B1 (B2 τ) τ
  hc2 : ContinuousOn B2 (Ioi 0)
  hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ)
  hbB1 : ∀ τ : ℝ, 0 < τ → ‖B1 τ‖ ≤ KB * τ ^ (-1 / 2 : ℝ) / (1 + τ)
  hbB2 : ∀ τ : ℝ, 0 < τ → ‖B2 τ‖ ≤ KB * τ ^ (-3 / 2 : ℝ) / (1 + τ)
  hp : ∀ τ : ℝ, τ1 ≤ τ → γ * sg τ ≤ |m τ - L|

/-- The pull-back of the real amplitude and phase under `T`. -/
structure PullBack (s1' a : ℝ) (Nc : ℂ) (gs : ℂ → ℂ) (T T1 : ℝ → ℝ) (B : ℝ → ℂ) (ϕ : ℝ → ℝ) : Prop where
  hT : ∀ s ∈ Icc (0 : ℝ) s1', HasDerivAt T (T1 s) s
  hT1 : ∀ s ∈ Icc (0 : ℝ) s1', 0 < T1 s
  hT0 : T 0 = 0
  hBT : ∀ s ∈ Ioc (0 : ℝ) s1', B (T s) * ((T1 s : ℝ) : ℂ) = Nc * csr (s : ℂ) * gs (s : ℂ)
  hϕT : ∀ s ∈ Icc (0 : ℝ) s1', ϕ (T s) = a * s + s ^ 3 / 3

/-- The holomorphic amplitude `g_s = [1 + (s²+a)Q] E e^{iψ s}`. -/
noncomputable def gAmp (a psi : ℝ) (Q E : ℂ → ℂ) (s : ℂ) : ℂ :=
  (1 + (s ^ 2 + (a : ℂ)) * Q s) * E s * Complex.exp (Complex.I * (psi : ℂ) * s)

lemma norm_exp_I_mul_le (psi : ℝ) (z : ℂ) : ‖Complex.exp (Complex.I * (psi : ℂ) * z)‖ ≤ Real.exp (|psi| * ‖z‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have : (Complex.I * (psi : ℂ) * z).re = -(psi * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this]
  have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  calc -(psi * z.im) ≤ |psi * z.im| := neg_le_abs _
    _ = |psi| * |z.im| := abs_mul _ _
    _ ≤ |psi| * ‖z‖ := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)

lemma gAmp_diff {lam ρ0 a psi : ℝ} {Q Q' E : ℂ → ℂ} {a' : ℂ} {Q0 Q1 : ℂ} {CQ CE CB : ℝ}
    (amp : SdAmp lam ρ0 a' Q0 Q1 Q Q' E CQ CE CB) (hEd : DifferentiableOn ℂ E (ball 0 ρ0)) :
    DifferentiableOn ℂ (gAmp a psi Q E) (ball 0 ρ0) := by
  intro z hz
  have hQ : DifferentiableAt ℂ Q z := (amp.hQd z hz).differentiableAt
  have hE : DifferentiableAt ℂ E z := (hEd z hz).differentiableAt (isOpen_ball.mem_nhds hz)
  unfold gAmp
  refine DifferentiableAt.differentiableWithinAt ?_
  fun_prop

lemma gAmp_bd {lam ρ0 a psi : ℝ} {Q Q' E : ℂ → ℂ} {a' : ℂ} {Q0 Q1 : ℂ} {CQ CE CB : ℝ}
    (amp : SdAmp lam ρ0 a' Q0 Q1 Q Q' E CQ CE CB) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hρ0 : 0 ≤ ρ0)
    (hbr : ∀ s ∈ ball (0 : ℂ) ρ0, ‖1 + (s ^ 2 + (a : ℂ)) * Q s‖ ≤ CB) :
    ∀ z ∈ ball (0 : ℂ) ρ0, ‖gAmp a psi Q E z‖ ≤ CB * (1 + CE * ρ0) * Real.exp (|psi| * ρ0) := by
  intro z hz
  have hzn : ‖z‖ < ρ0 := by simpa using hz
  have hCB := amp.hCB
  have hCE := amp.hCE
  have hE : ‖E z‖ ≤ 1 + CE * ρ0 := by
    have h1 := amp.hE z hz
    have h2 : ‖E z‖ ≤ ‖E z - 1‖ + 1 := by
      calc ‖E z‖ = ‖(E z - 1) + 1‖ := by ring_nf
        _ ≤ ‖E z - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖E z - 1‖ + 1 := by simp
    have h3 : CE * lam ^ 3 * ‖z‖ ≤ CE * ρ0 := by
      have : lam ^ 3 ≤ 1 := pow_le_one₀ hlam.le hlam1
      calc CE * lam ^ 3 * ‖z‖ ≤ CE * 1 * ρ0 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_left this hCE) hzn.le (norm_nonneg _) (by positivity)
        _ = CE * ρ0 := by ring
    linarith
  have hex := norm_exp_I_mul_le psi z
  have hex' : ‖Complex.exp (Complex.I * (psi : ℂ) * z)‖ ≤ Real.exp (|psi| * ρ0) :=
    hex.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hzn.le (abs_nonneg _)))
  unfold gAmp
  rw [norm_mul, norm_mul]
  have hb := hbr z hz
  have hn1 := norm_nonneg (1 + (z ^ 2 + (a : ℂ)) * Q z)
  have hn2 := norm_nonneg (E z)
  calc ‖1 + (z ^ 2 + (a : ℂ)) * Q z‖ * ‖E z‖ * ‖Complex.exp (Complex.I * (psi : ℂ) * z)‖
      ≤ CB * (1 + CE * ρ0) * Real.exp (|psi| * ρ0) :=
        mul_le_mul (mul_le_mul hb hE hn2 hCB) hex' (norm_nonneg _) (by positivity)

lemma T_pos_of_deriv {s1' : ℝ} {T T1 : ℝ → ℝ} (hT : ∀ s ∈ Icc (0 : ℝ) s1', HasDerivAt T (T1 s) s)
    (hT1 : ∀ s ∈ Icc (0 : ℝ) s1', 0 < T1 s) (hT0 : T 0 = 0) : ∀ s ∈ Ioc (0 : ℝ) s1', 0 < T s := by
  intro s hs
  have hs1 : 0 < s1' := lt_of_lt_of_le hs.1 hs.2
  have hmono : StrictMonoOn T (Icc 0 s1') := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 s1')
      (fun s hs => (hT s hs).continuousAt.continuousWithinAt) ?_
    intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Icc 0 s1' := ⟨hx.1.le, hx.2.le⟩
    rw [(hT x hx').deriv]; exact hT1 x hx'
  have := hmono ⟨le_rfl, hs1.le⟩ ⟨hs.1.le, hs.2⟩ hs.1
  rwa [hT0] at this

/-- Interval integrability of the real integrand from the amplitude bound. -/
lemma intInt_B {c KB M : ℝ} {B : ℝ → ℂ} {ϕ : ℝ → ℝ} (hM : 0 < M) (hBc : ContinuousOn B (Ioi 0))
    (hϕc : ContinuousOn ϕ (Ioi 0)) (hKB : 0 ≤ KB)
    (hbB : ∀ τ : ℝ, 0 < τ → ‖B τ‖ ≤ KB * τ ^ (1 / 2 : ℝ) / (1 + τ)) :
    IntervalIntegrable (fun τ => B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) volume 0 M := by
  set g : ℝ → ℂ := fun τ => B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ)) with hg
  have hgc : ContinuousOn g (Ioi 0) := by
    refine hBc.mul ?_
    refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
    exact Complex.continuous_ofReal.comp_continuousOn hϕc
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le]
  have hdom : IntegrableOn (fun τ : ℝ => KB * τ ^ (-1 / 2 : ℝ)) (Ioc 0 M) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M) (r := -1 / 2) (by norm_num))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le] at this
    exact this.const_mul KB
  refine Integrable.mono' hdom ((hgc.mono (fun x (hx : x ∈ Ioc 0 M) => hx.1)).aestronglyMeasurable measurableSet_Ioc) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun τ hτ => ?_)
  simp only [hg, norm_mul]
  have hn : ‖Complex.exp (Complex.I * c * (ϕ τ : ℂ))‖ = 1 := by
    have : Complex.I * (c : ℂ) * (ϕ τ : ℂ) = Complex.I * ((c * ϕ τ : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact Complex.norm_exp_I_mul_ofReal _
  rw [hn, mul_one]
  refine (hbB τ hτ.1).trans ?_
  have h1 : τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (-1 / 2 : ℝ) := by
    calc τ ^ (1 / 2 : ℝ) / (1 + τ) ≤ τ ^ (1 / 2 : ℝ) / τ :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hτ.1.le _) hτ.1 (by linarith)
      _ = τ ^ (-1 / 2 : ℝ) := by
          rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub_one hτ.1.ne']
  calc KB * τ ^ (1 / 2 : ℝ) / (1 + τ) = KB * (τ ^ (1 / 2 : ℝ) / (1 + τ)) := by ring
    _ ≤ KB * τ ^ (-1 / 2 : ℝ) := mul_le_mul_of_nonneg_left h1 hKB

set_option maxHeartbeats 4000000 in
/-- **Assembly (abstract form of `(ct:K-airy)`).**  The improper integral `∫₀^∞ B e^{icϕ}` exists and
`-Re` of it is the Airy expression up to an explicit error. -/
theorem outer_assembly {c lam s1 s1' rr a Ua Uh psi q0 hh L R₀ : ℝ} {Nc N1 : ℂ} {Q Q' E : ℂ → ℂ}
    {CQ CE CB Cm CU Cend : ℝ} {T T1 : ℝ → ℝ} {B B1 B2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {C0 KB γ : ℝ} {m m1 m2 m3 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hlc : c * lam ^ 3 = 1)
    (hs1 : 0 < s1) (hs1s : s1 < s1') (hrr : 0 < rr) (hR1 : 1 ≤ rr ^ 2) (hsR : s1 = lam * rr ^ 2)
    (hUa : a = kap * Ua * lam ^ 2) (hUh : kap * Uh * lam ^ 2 = a + lam ^ 3 * psi)
    (hseg : kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16)
    (hN1 : N1 = (((1 / √π : ℝ)) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)))
    (hNc : Nc * ((lam * Real.sqrt lam : ℝ) : ℂ) = N1)
    (hRR : rr ^ 2 < R₀) (hR₀ : lam * R₀ ≤ 3 * s1) (ch : Chain3 R₀ ((((rr ^ 2 : ℝ)) : ℂ) * d6))
    (amp : SdAmp lam (3 * s1) (a : ℂ) (q0 : ℂ) (Complex.I * (hh : ℂ)) Q Q' E CQ CE CB)
    (hEd : DifferentiableOn ℂ E (ball 0 (3 * s1)))
    (hm : MomOK Cm Uh ch) (hCm : 0 ≤ Cm) (hCU : 0 ≤ CU) (hU : lam * Real.sqrt |Uh| ≤ CU) (hCend : 0 ≤ Cend)
    (hend : lam ^ 2 * (‖csr ((((rr ^ 2 : ℝ)) : ℂ) * d6)‖ * ‖Q ((lam : ℂ) * ((((rr ^ 2 : ℝ)) : ℂ) * d6)) - (q0 : ℂ)‖ *
      Real.exp (-(PhU Uh ((((rr ^ 2 : ℝ)) : ℂ) * d6)).im)) ≤ Cend * lam ^ 4)
    (htail : ∀ t, rr ^ 2 < t → -(t ^ 3 / 6) ≤ nu * Uh * t) (hkU : kap * |Uh| ≤ (rr ^ 2) ^ 2)
    (pb : PullBack s1' a Nc (gAmp a psi Q E) T T1 B ϕ)
    (tb : TailBd C0 KB γ L (T s1) m m1 m2 m3 B B1 B2 ϕ)
    (hne : ∀ s ∈ Ioo (s1 / 2) s1', a + s ^ 2 ≠ 0) :
    ∃ Itot : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 Itot) ∧
      |(-Itot.re) -
        ((1 + lam ^ 3 * (-psi * q0 - 3 / 2 * hh)) * (-π * (airyAi' Uh * airyBi Uh + airyAi Uh * airyBiDeriv Uh)) +
          lam ^ 2 * q0 * ((2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi Uh * airyBi Uh)))| ≤
      (1 / √π) * (sdC CQ CE CB Cm CU Cend (3 * s1) ‖Complex.I * (hh : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * (1 + |Uh|) ^ (1 / 2 : ℝ) +
        |1 + lam ^ 3 * (-psi * q0 - 3 / 2 * hh)| * (144 * Real.exp (-((rr ^ 2) ^ 3 / 12))) +
        lam ^ 2 * |q0| * (288 * Real.exp (-((rr ^ 2) ^ 3 / 12)))) +
      (1 / √π) * ((16 * (2 * (CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1)))) / rr ^ 3 +
          1024 * (2 * (CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1)))) / rr ^ 9) *
          Real.exp (-((rr ^ 2) ^ 3 / 4)) +
        320000 * (2 * (CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1)))) / rr ^ 9) +
      (1 / c ^ 2) * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * (T s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (T s1) ^ (-3 / 2 : ℝ))) := by
  classical
  have hR0 : 0 < rr ^ 2 := by positivity
  have hs1I : s1 ∈ Ioc (0 : ℝ) s1' := ⟨hs1, hs1s.le⟩
  have hTpos := T_pos_of_deriv pb.hT pb.hT1 pb.hT0
  have hτ1 : 0 < T s1 := hTpos s1 hs1I
  set gs : ℂ → ℂ := gAmp a psi Q E with hgs
  set Cb : ℝ := CB * (1 + CE * (3 * s1)) * Real.exp (|psi| * (3 * s1)) with hCbdef
  have hgd : DifferentiableOn ℂ gs (ball 0 (3 * s1)) := gAmp_diff amp hEd
  have hCb : ∀ z ∈ ball (0 : ℂ) (3 * s1), ‖gs z‖ ≤ Cb :=
    gAmp_bd amp hlam hlam1 (by positivity) amp.hB
  have hCb0 : 0 ≤ Cb := by
    have := amp.hCB; have := amp.hCE
    rw [hCbdef]; positivity
  -- tail
  obtain ⟨J, hJt, hJb⟩ := piece3_gen tb.hM tb.hγ tb.hKB hc hτ1 tb.hϕ tb.hB tb.hB1 tb.hc2 tb.hbB tb.hbB1 tb.hbB2 tb.hp
  -- head
  have hBc : ContinuousOn B (Ioi 0) := fun τ hτ => (tb.hB τ hτ).continuousAt.continuousWithinAt
  have hϕc : ContinuousOn ϕ (Ioi 0) := fun τ hτ => (tb.hϕ τ hτ).continuousAt.continuousWithinAt
  have hgsc : ContinuousOn (fun s : ℝ => gs (s : ℂ)) (Icc 0 s1) := by
    intro s hs
    have hmem : (s : ℂ) ∈ ball (0 : ℂ) (3 * s1) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    exact ((hgd.continuousOn.continuousAt (isOpen_ball.mem_nhds hmem)).comp (f := fun s : ℝ => (s : ℂ))
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hhead := head_eq (c := c) (lam := lam) (s1 := s1) (R := rr ^ 2) (a := a) (U := Ua) (KB := KB) (T := T) (T1 := T1)
    (B := B) (ϕ := ϕ) (gs := gs) (Nc := Nc) (N1 := N1) hc hlam hlc hs1 hsR hUa hNc
    (fun s hs => pb.hT s ⟨hs.1, hs.2.trans hs1s.le⟩) (fun s hs => pb.hT1 s ⟨hs.1, hs.2.trans hs1s.le⟩) pb.hT0 hBc hϕc
    tb.hKB tb.hbB (fun s hs => pb.hBT s ⟨hs.1, hs.2.trans hs1s.le⟩)
    (fun s hs => pb.hϕT s ⟨hs.1, hs.2.trans hs1s.le⟩) hgsc
  -- deformation
  have hR₀pos : 0 < R₀ := lt_trans hR0 hRR
  have hdiffG : DifferentiableOn ℂ (fun w => gs ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU Ua w)) (ball 0 R₀) := by
    intro w hw
    have hwn : ‖w‖ < R₀ := by simpa using hw
    have hmem : (lam : ℂ) * w ∈ ball (0 : ℂ) (3 * s1) := by
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
      nlinarith [mul_lt_mul_of_pos_left hwn hlam]
    have h1 : DifferentiableAt ℂ gs ((lam : ℂ) * w) := (hgd _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => gs ((lam : ℂ) * w)) w := h1.comp w (by fun_prop)
    have h3 : DifferentiableAt ℂ (fun w => Complex.exp (Complex.I * PhU Ua w)) w := by
      unfold PhU; fun_prop
    exact (h2.mul h3).differentiableWithinAt
  have hdef := deform_real hR₀pos hRR hR0 hdiffG ch
  -- segment
  have hsegt : ∀ t ∈ Icc (0 : ℝ) 1, ‖segPt (rr ^ 2) t‖ ≤ rr ^ 2 := fun t ht => norm_segPt_le hR0.le ht.1 ht.2
  have hgdat := fun t (ht : t ∈ Icc (0 : ℝ) 1) => gW_data hs1 hlam hsR hgd hCb (hsegt t ht)
  have hdd2 : ContinuousOn (deriv (deriv gs)) (ball 0 (3 * s1)) :=
    ((hgd.deriv isOpen_ball).deriv isOpen_ball).continuousOn
  have hc2seg : ContinuousOn (fun t : ℝ => (lam : ℂ) ^ 2 * deriv (deriv gs) ((lam : ℂ) * segPt (rr ^ 2) t)) (Icc 0 1) := by
    have hpt : Continuous fun t : ℝ => (lam : ℂ) * segPt (rr ^ 2) t := by
      simp only [segPt_eq]; fun_prop
    refine continuousOn_const.mul (hdd2.comp hpt.continuousOn ?_)
    intro t ht
    have := norm_segPt_le hR0.le ht.1 ht.2
    rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
    nlinarith
  set gW : ℂ → ℂ := fun w => gs ((lam : ℂ) * w) with hgW
  set gW1 : ℂ → ℂ := fun w => (lam : ℂ) * deriv gs ((lam : ℂ) * w) with hgW1
  set gW2 : ℂ → ℂ := fun w => (lam : ℂ) ^ 2 * deriv (deriv gs) ((lam : ℂ) * w) with hgW2
  have hsegR := seg_rem (U := Ua) (ρ := rr) (Cg := 2 * Cb) (gW := gW) (gW1 := gW1) (gW2 := gW2) hrr
    (by positivity) hseg
    (fun t ht => (hgdat t ht).1) (fun t ht => (hgdat t ht).2.1) hc2seg
    (fun t ht => ((hgdat t ht).2.2.1).trans (by linarith))
    (fun t ht => (hgdat t ht).2.2.2.1)
    (fun t ht => by
      have := (hgdat t ht).2.2.2.2
      rwa [show (rr ^ 2) ^ 2 = rr ^ 4 by ring] at this)
  -- the chain integral and the Airy evaluation
  have hdiffU : (kap : ℝ) * (Uh - Ua) = lam * psi := by
    have h1 : lam ^ 2 * (kap * (Uh - Ua) - lam * psi) = 0 := by
      linear_combination hUh + hUa
    have h2 : lam ^ 2 ≠ 0 := by positivity
    have := (mul_eq_zero.1 h1).resolve_left h2
    linarith
  have hexpU : ∀ w : ℂ, Complex.exp (Complex.I * (psi : ℂ) * ((lam : ℂ) * w)) * Complex.exp (Complex.I * PhU Ua w) =
      Complex.exp (Complex.I * PhU Uh w) := by
    intro w
    rw [← Complex.exp_add]
    congr 1
    unfold PhU
    have : ((kap : ℝ) : ℂ) * ((Uh : ℝ) : ℂ) - ((kap : ℝ) : ℂ) * ((Ua : ℝ) : ℂ) = (lam : ℂ) * (psi : ℂ) := by
      exact_mod_cast (by linarith : (kap : ℝ) * Uh - kap * Ua = lam * psi)
    linear_combination (Complex.I * w) * (-this)
  have hch : ch.int (fun z => csr z * (gs ((lam : ℂ) * z) * Complex.exp (Complex.I * PhU Ua z))) =
      ch.intE Uh (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) * E ((lam : ℂ) * w))) := by
    unfold Chain3.intE
    congr 1
    funext z
    simp only [hgs, gAmp]
    rw [← hexpU z]
    ring
  have haC : (a : ℂ) = (kap : ℂ) * (lam : ℂ) ^ 2 * (Uh : ℂ) - (lam : ℂ) ^ 3 * (psi : ℂ) := by
    have : a = kap * lam ^ 2 * Uh - lam ^ 3 * psi := by linarith [hUh]
    exact_mod_cast this
  have hsa := sd_airy (R := rr ^ 2) (R₀ := R₀) (ρ0 := 3 * s1) (lam := lam) (U := Uh) (psi := psi) (q0 := q0) (h := hh)
    ch hR₀pos hR1 hRR hlam hlam1 hR₀ haC amp hm hCm hCU hU hCend hend htail hkU
  -- the join
  have hlcC : (c : ℂ) * (lam : ℂ) ^ 3 = 1 := by exact_mod_cast hlc
  have hϕs1 : ϕ (T s1) = a * s1 + s1 ^ 3 / 3 := pb.hϕT s1 ⟨hs1.le, hs1s.le⟩
  have hexp : Complex.exp (Complex.I * PhU Ua (((rr ^ 2 : ℝ)) : ℂ)) = Complex.exp (Complex.I * c * (ϕ (T s1) : ℂ)) := by
    congr 1
    rw [hϕs1]; unfold PhU; rw [hUa, hsR]; push_cast
    linear_combination (-(Complex.I * ((kap : ℂ) * (Ua : ℂ) * (rr : ℂ) ^ 2 + ((rr : ℂ) ^ 2) ^ 3 / 3))) * hlcC
  have hs1Ioo : s1 ∈ Ioo (s1 / 2) s1' := ⟨by linarith, hs1s⟩
  have hgdiff1 : HasDerivAt gs (deriv gs (s1 : ℂ)) (s1 : ℂ) := by
    have hmem : (s1 : ℂ) ∈ ball (0 : ℂ) (3 * s1) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs1]; linarith
    exact ((hgd _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
  have hbdry := head_bdry (c := c) (lam := lam) (R := rr ^ 2) (s1 := s1) (a := a) (U := Ua) (Nc := Nc) (N1 := N1)
    (g' := deriv gs (s1 : ℂ)) (gs := gs) (gW := gW)
    (gW1 := gW1) hc hlam hlc hR0 hsR hUa hNc (hne s1 hs1Ioo)
    (by
      show gs ((lam : ℂ) * (((rr ^ 2 : ℝ)) : ℂ)) = gs (s1 : ℂ)
      congr 1; rw [hsR]; push_cast; ring)
    (by
      show (lam : ℂ) * deriv gs ((lam : ℂ) * (((rr ^ 2 : ℝ)) : ℂ)) = (lam : ℂ) * deriv gs (s1 : ℂ)
      congr 3; rw [hsR]; push_cast; ring)
  have hrho := hasDerivAt_rhoS (Nc := Nc) hs1 (hne s1 hs1Ioo) hgdiff1
  have hneC : ∀ s ∈ Ioo (s1 / 2) s1', ((a + s ^ 2 : ℝ) : ℂ) ≠ 0 := fun s hs => by exact_mod_cast hne s hs
  have htb := tail_bdry (a := a) (sl := s1 / 2) (s1 := s1) (s1' := s1') (T := T) (T1 := T1) (B := B) (B1 := B1)
    (Φ := fun s : ℝ => Nc * csr (s : ℂ) * gs (s : ℂ)) (ρ := rhoS Nc gs a) (ϕ := ϕ) (ϕ1 := fun τ => m τ - L)
    (ϕ2 := m1) (ρ' := rhoS' Nc gs (deriv gs (s1 : ℂ)) a s1) hs1Ioo
    (fun s hs => pb.hT s ⟨by linarith [hs.1], hs.2.le⟩) (fun s hs => pb.hT1 s ⟨by linarith [hs.1], hs.2.le⟩)
    (fun s hs => hTpos s ⟨by linarith [hs.1], hs.2.le⟩) tb.hϕ tb.hB
    (fun τ hτ => (tb.hM.d0 τ hτ).sub_const L)
    (fun s hs => pb.hBT s ⟨by linarith [hs.1], hs.2.le⟩) (fun s hs => pb.hϕT s ⟨by linarith [hs.1], hs.2.le⟩) hne
    (fun s hs => by
      show Nc * csr (s : ℂ) * gs (s : ℂ) = rhoS Nc gs a s * ((a + s ^ 2 : ℝ) : ℂ)
      unfold rhoS
      have := hneC s hs
      field_simp) hrho
  obtain ⟨htb1, htb2⟩ := htb
  obtain ⟨hba, hbb⟩ := hbdry
  obtain ⟨hsegEq, hsegNorm⟩ := hsegR
  rw [segZ0_add_segD] at hsegEq
  have hdef' : lineInt 0 1 0 (rr ^ 2) (fun w => csr w * gW w * Complex.exp (Complex.I * PhU Ua w)) =
      ch.int (fun z => csr z * gW z * Complex.exp (Complex.I * PhU Ua z)) +
      lineInt (segZ0 (rr ^ 2)) (segD (rr ^ 2)) 0 1 (fun z => csr z * gW z * Complex.exp (Complex.I * PhU Ua z)) := by
    simp only [hgW, mul_assoc]
    convert hdef using 2
    rfl
  have hhead' : ∫ τ in (0 : ℝ)..T s1, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ)) =
      N1 * (ch.int (fun z => csr z * gW z * Complex.exp (Complex.I * PhU Ua z)) +
      lineInt (segZ0 (rr ^ 2)) (segD (rr ^ 2)) 0 1 (fun z => csr z * gW z * Complex.exp (Complex.I * PhU Ua z))) := by
    rw [hhead, ← hdef']
  -- limit
  have hlim : Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop
      (𝓝 ((∫ τ in (0 : ℝ)..T s1, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) +
        (-((1 / (Complex.I * c)) * (B (T s1) / ((m (T s1) - L : ℝ) : ℂ) * Complex.exp (Complex.I * c * (ϕ (T s1) : ℂ)))) +
          (1 / (Complex.I * c)) ^ 2 * (ibpH B B1 (fun τ => m τ - L) m1 (T s1) / ((m (T s1) - L : ℝ) : ℂ) *
            Complex.exp (Complex.I * c * (ϕ (T s1) : ℂ))) + (1 / (Complex.I * c)) ^ 2 * J))) := by
    have h1 := hJt.const_add (∫ τ in (0 : ℝ)..T s1, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ)))
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop (T s1)] with b hb
    refine intervalIntegral.integral_add_adjacent_intervals (intInt_B hτ1 hBc hϕc tb.hKB tb.hbB) ?_
    have hcon : ContinuousOn (fun τ => B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) (Icc (T s1) b) := by
      have hsub : Icc (T s1) b ⊆ Ioi 0 := fun τ hτ => lt_of_lt_of_le hτ1 hτ.1
      refine (hBc.mono hsub).mul ?_
      refine Complex.continuous_exp.comp_continuousOn (continuousOn_const.mul ?_)
      exact Complex.continuous_ofReal.comp_continuousOn (hϕc.mono hsub)
    exact hcon.intervalIntegrable_of_Icc hb
  refine ⟨_, hlim, ?_⟩
  beta_reduce at htb1 htb2
  have hch' : ch.int (fun z => csr z * gW z * Complex.exp (Complex.I * PhU Ua z)) =
      ch.intE Uh (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) *
        E ((lam : ℂ) * w))) := by
    rw [← hch]; congr 1; funext z; simp only [hgW]; ring
  rw [hexp.symm.trans rfl, hhead', hsegEq, hch']
  set chint := ch.intE Uh (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) *
    E ((lam : ℂ) * w))) with hchint
  set e1 := Complex.exp (Complex.I * PhU Ua (((rr ^ 2 : ℝ)) : ℂ)) with he1
  set P1 := csrF gW (((rr ^ 2 : ℝ)) : ℂ) / (Complex.I * GG Ua (((rr ^ 2 : ℝ)) : ℂ)) with hP1
  set Hq1 := segH (csrF gW) (csrF1 gW gW1) (GG Ua) GG1 (((rr ^ 2 : ℝ)) : ℂ) /
    (Complex.I * GG Ua (((rr ^ 2 : ℝ)) : ℂ)) with hHq1
  set z0 : ℂ := segZ0 (rr ^ 2) + ((0 : ℝ) : ℂ) * segD (rr ^ 2) with hz0
  set P0 := csrF gW z0 / (Complex.I * GG Ua z0) with hP0
  set Hq0 := segH (csrF gW) (csrF1 gW gW1) (GG Ua) GG1 z0 / (Complex.I * GG Ua z0) with hHq0
  set e0 := Complex.exp (Complex.I * PhU Ua z0) with he0
  set Qint := lineInt (segZ0 (rr ^ 2)) (segD (rr ^ 2)) 0 1 (fun z => segQ (csrF gW) (csrF1 gW gW1)
    (csrF2 gW gW1 gW2) (GG Ua) GG1 GG2 z * Complex.exp (Complex.I * PhU Ua z)) with hQint
  set Bq := B (T s1) / (((m (T s1) - L : ℝ)) : ℂ) with hBq
  set Hi := ibpH B B1 (fun τ => m τ - L) m1 (T s1) / (((m (T s1) - L : ℝ)) : ℂ) with hHi
  have hkey : N1 * (chint + ((P1 * e1 - P0 * e0) - 1 / Complex.I * (Hq1 * e1 - Hq0 * e0) +
        (1 / Complex.I) ^ 2 * Qint)) +
      (-(1 / (Complex.I * c) * (Bq * e1)) + (1 / (Complex.I * c)) ^ 2 * (Hi * e1) + (1 / (Complex.I * c)) ^ 2 * J) =
      N1 * chint + (-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
        (1 / (Complex.I * c)) ^ 2 * J) := by
    linear_combination e1 * hba - e1 * hbb - (1 / (Complex.I * c)) * e1 * htb1 + (1 / (Complex.I * c)) ^ 2 * e1 * htb2
  rw [hkey]
  -- estimates
  have hsqπ : 0 < √π := Real.sqrt_pos.2 Real.pi_pos
  have hN1n : ‖N1‖ = 1 / √π := by
    rw [hN1, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_I_mul_ofReal, mul_one,
      abs_of_pos (by positivity)]
  have hre : (N1 * chint).re = (1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) * chint).re := by
    rw [hN1, mul_assoc, Complex.re_ofReal_mul]
  have hsa' : |-(N1 * chint).re -
        ((1 + lam ^ 3 * (-psi * q0 - 3 / 2 * hh)) * (-π * (airyAi' Uh * airyBi Uh + airyAi Uh * airyBiDeriv Uh)) +
          lam ^ 2 * q0 * ((2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi Uh * airyBi Uh)))| ≤
      (1 / √π) * (sdC CQ CE CB Cm CU Cend (3 * s1) ‖Complex.I * (hh : ℂ)‖ ‖(psi : ℂ)‖ * lam ^ 4 * (1 + |Uh|) ^ (1 / 2 : ℝ) +
        |1 + lam ^ 3 * (-psi * q0 - 3 / 2 * hh)| * (144 * Real.exp (-((rr ^ 2) ^ 3 / 12))) +
        lam ^ 2 * |q0| * (288 * Real.exp (-((rr ^ 2) ^ 3 / 12)))) := by
    rw [hre]
    have : -(1 / √π * (Complex.exp (Complex.I * (π / 4 : ℝ)) * chint).re) =
        -(1 / √π) * (Complex.exp (Complex.I * (π / 4 : ℝ)) * chint).re := by ring
    rw [this]
    exact hsa
  -- the remainder
  have hCg : 0 ≤ 2 * Cb := by positivity
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  obtain ⟨hdat1, hdat2, hdat3, hdat4, hdat5⟩ := hgdat 0 h00
  have hbd0 := norm_seg_bdry_le (U := Ua) (ρ := rr) (t := 0) (gW := gW) (gW1 := gW1) hrr le_rfl zero_le_one hCg hseg
    (hdat3.trans (by linarith)) hdat4
  have hIm := im_PhU_segPt (U := Ua) (R := rr ^ 2) (t := 0) hR0.le le_rfl zero_le_one hseg
  have he0n : ‖e0‖ ≤ Real.exp (-((rr ^ 2) ^ 3 / 4)) := by
    rw [he0, norm_exp_I_mul]
    apply Real.exp_le_exp.2
    have : (rr ^ 2) ^ 3 / 4 ≤ (PhU Ua z0).im := by
      have h1 : (rr ^ 2) ^ 3 / 4 ≤ rr ^ 2 / 2 * (29 * (rr ^ 2) ^ 2 / 48) * (1 - 0) := by
        have : 0 ≤ (rr ^ 2) ^ 3 := by positivity
        nlinarith
      exact h1.trans hIm
    linarith
  have hRest : ‖-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
      (1 / (Complex.I * c)) ^ 2 * J‖ ≤
      (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
        320000 * (2 * Cb) / rr ^ 9) +
      (1 / c ^ 2) * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * (T s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (T s1) ^ (-3 / 2 : ℝ))) := by
    have hP0n : ‖P0‖ ≤ 16 * (2 * Cb) / rr ^ 3 := hbd0.1
    have hHq0n : ‖Hq0‖ ≤ 1024 * (2 * Cb) / rr ^ 9 := hbd0.2
    have hQn : ‖Qint‖ ≤ 320000 * (2 * Cb) / rr ^ 9 := hsegNorm
    have hJn := hJb
    have hI1 : ‖(1 : ℂ) / Complex.I‖ = 1 := by simp
    have hc2 : ‖(1 / (Complex.I * (c : ℂ))) ^ 2‖ = 1 / c ^ 2 := by
      rw [norm_pow, norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc, div_pow, one_pow]
    have hA : 0 ≤ 16 * (2 * Cb) / rr ^ 3 := by positivity
    have hBc' : 0 ≤ 1024 * (2 * Cb) / rr ^ 9 := by positivity
    have hEe : 0 ≤ Real.exp (-((rr ^ 2) ^ 3 / 4)) := (Real.exp_pos _).le
    have t1 : ‖N1 * (P0 * e0)‖ ≤ (1 / √π) * (16 * (2 * Cb) / rr ^ 3 * Real.exp (-((rr ^ 2) ^ 3 / 4))) := by
      rw [norm_mul, norm_mul, hN1n]
      gcongr
    have t2 : ‖N1 * (1 / Complex.I * (Hq0 * e0))‖ ≤
        (1 / √π) * (1024 * (2 * Cb) / rr ^ 9 * Real.exp (-((rr ^ 2) ^ 3 / 4))) := by
      rw [norm_mul, norm_mul, norm_mul, hN1n, hI1, one_mul]
      gcongr
    have t3 : ‖N1 * ((1 / Complex.I) ^ 2 * Qint)‖ ≤ (1 / √π) * (320000 * (2 * Cb) / rr ^ 9) := by
      rw [norm_mul, norm_mul, norm_pow, hN1n, hI1, one_pow, one_mul]
      gcongr
    have t4 : ‖(1 / (Complex.I * (c : ℂ))) ^ 2 * J‖ ≤ (1 / c ^ 2) * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * (T s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (T s1) ^ (-3 / 2 : ℝ))) := by
      rw [norm_mul, hc2]
      gcongr
    calc ‖-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
          (1 / (Complex.I * c)) ^ 2 * J‖
        ≤ ‖-(N1 * (P0 * e0))‖ + ‖N1 * (1 / Complex.I * (Hq0 * e0))‖ + ‖N1 * ((1 / Complex.I) ^ 2 * Qint)‖ +
            ‖(1 / (Complex.I * c)) ^ 2 * J‖ := by
          refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by
          rw [norm_neg]
          have e : (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
              320000 * (2 * Cb) / rr ^ 9) =
              (1 / √π) * (16 * (2 * Cb) / rr ^ 3 * Real.exp (-((rr ^ 2) ^ 3 / 4))) +
              (1 / √π) * (1024 * (2 * Cb) / rr ^ 9 * Real.exp (-((rr ^ 2) ^ 3 / 4))) +
              (1 / √π) * (320000 * (2 * Cb) / rr ^ 9) := by ring
          rw [e]
          linarith
  -- conclusion
  have hre2 : -((N1 * chint + (-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
        (1 / (Complex.I * c)) ^ 2 * J)).re) = -(N1 * chint).re -
      (-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
        (1 / (Complex.I * c)) ^ 2 * J).re := by
    simp only [Complex.neg_re, Complex.add_re]; ring
  rw [hre2]
  set Rest := (-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
        (1 / (Complex.I * c)) ^ 2 * J) with hRestdef
  have hRe : |Rest.re| ≤ ‖Rest‖ := Complex.abs_re_le_norm _
  set Main : ℝ := (1 + lam ^ 3 * (-psi * q0 - 3 / 2 * hh)) * (-π * (airyAi' Uh * airyBi Uh + airyAi Uh * airyBiDeriv Uh)) +
          lam ^ 2 * q0 * ((2 : ℝ) ^ (-(1 / 3) : ℝ) * π * (airyAi Uh * airyBi Uh)) with hMain
  have : -(N1 * chint).re - Rest.re - Main = (-(N1 * chint).re - Main) - Rest.re := by ring
  rw [this]
  calc |(-(N1 * chint).re - Main) - Rest.re| ≤ |-(N1 * chint).re - Main| + |Rest.re| := abs_sub _ _
    _ ≤ _ := by linarith

/-- info: 'FormalResearch.SignUncertainty.CtSd.outer_assembly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms outer_assembly

end FormalResearch.SignUncertainty.CtSd

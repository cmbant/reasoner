module

public import FormalResearch.SignUncertainty.CtWindowSignedSplit
public import FormalResearch.SignUncertainty.CtWindowCfu

/-!
# Concrete Hankel `HalfCubicData` and pre-Airy steepest-descent assembly (`(ct:K-signed)`)

1. `outer_assembly_fs`: pre-Airy version of `CtSd.outer_assembly` returning the `fsOpCh ch Uh (...)` term plus
   the explicit `O(c^{-3/2})` segment+tail error `Rest` when `rr^2 = s₁ / lam` (`c * lam^3 = 1`).
2. `hankelHalfCubic`: builds a `FineOrderSigned.HalfCubicData` instance from the concrete Hankel amplitude
   `B_c(s, a) = (1 + (s^2 + a) Q_ε(s; z_A(a))) E_c(s; z_A(a))` via `mkHalfCubicOfCauchy`.
-/

@[expose] public section

open Complex MeasureTheory Metric Set Filter Topology
open scoped Real Interval

namespace FormalResearch.SignUncertainty

open FormalResearch.SignUncertainty.CtSd FormalResearch.SignUncertainty.CtChart
open FormalResearch.SignUncertainty.CtOsc FormalResearch.SignUncertainty.FineOrderSigned

/-! ### Part 1: Pre-Airy steepest-descent assembly (`O(c^{-3/2})` external remainder) -/

set_option maxHeartbeats 4000000 in
/-- Pre-Airy steepest-descent identity: expresses `-Itot.re` as `fsOpCh ch Uh B_lam` plus the segment
and tail remainder bounded by `O(c^{-3/2})` when `rr^2 = s1 / lam` and `lam = c^{-1/3}`. -/
theorem outer_assembly_fs {c lam s1 s1' rr a Ua Uh psi L R₀ : ℝ} {Nc N1 : ℂ} {Q E : ℂ → ℂ}
    {Cb : ℝ} {T T1 : ℝ → ℝ} {B B1 B2 : ℝ → ℂ} {ϕ : ℝ → ℝ} {C0 KB γ : ℝ} {m m1 m2 m3 : ℝ → ℝ}
    (hc : 0 < c) (hlam : 0 < lam) (_hlam1 : lam ≤ 1) (hlc : c * lam ^ 3 = 1)
    (hs1 : 0 < s1) (hs1s : s1 < s1') (hrr : 0 < rr) (_hR1 : 1 ≤ rr ^ 2) (hsR : s1 = lam * rr ^ 2)
    (hUa : a = kap * Ua * lam ^ 2) (hUh : kap * Uh * lam ^ 2 = a + lam ^ 3 * psi)
    (hseg : kap * |Ua| ≤ (rr ^ 2) ^ 2 / 16)
    (hN1 : N1 = (((1 / √π : ℝ)) : ℂ) * Complex.exp (Complex.I * (π / 4 : ℝ)))
    (hNc : Nc * ((lam * Real.sqrt lam : ℝ) : ℂ) = N1)
    (hRR : rr ^ 2 < R₀) (hR₀ : lam * R₀ ≤ 3 * s1) (ch : Chain3 R₀ ((((rr ^ 2 : ℝ)) : ℂ) * d6))
    (hCb0 : 0 ≤ Cb) (hgs_diff : DifferentiableOn ℂ (gAmp a psi Q E) (ball 0 (3 * s1)))
    (hgs_bd : ∀ z ∈ ball (0 : ℂ) (3 * s1), ‖gAmp a psi Q E z‖ ≤ Cb)
    (pb : PullBack s1' a Nc (gAmp a psi Q E) T T1 B ϕ)
    (tb : TailBd C0 KB γ L (T s1) m m1 m2 m3 B B1 B2 ϕ)
    (hne : ∀ s ∈ Ioo (s1 / 2) s1', a + s ^ 2 ≠ 0) :
    ∃ Itot : ℂ, Tendsto (fun b : ℝ => ∫ τ in (0 : ℝ)..b, B τ * Complex.exp (Complex.I * c * (ϕ τ : ℂ))) atTop (𝓝 Itot) ∧
      |(-Itot.re) - fsOpCh ch Uh (fun w => (1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) *
          E ((lam : ℂ) * w))| ≤
      (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
        320000 * (2 * Cb) / rr ^ 9) +
      (1 / c ^ 2) * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * (T s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (T s1) ^ (-3 / 2 : ℝ))) := by
  classical
  have hR0 : 0 < rr ^ 2 := by positivity
  have hs1I : s1 ∈ Ioc (0 : ℝ) s1' := ⟨hs1, hs1s.le⟩
  have hTpos := T_pos_of_deriv pb.hT pb.hT1 pb.hT0
  have hτ1 : 0 < T s1 := hTpos s1 hs1I
  set gs : ℂ → ℂ := gAmp a psi Q E with hgs
  obtain ⟨J, hJt, hJb⟩ := piece3_gen tb.hM tb.hγ tb.hKB hc hτ1 tb.hϕ tb.hB tb.hB1 tb.hc2 tb.hbB tb.hbB1 tb.hbB2 tb.hp
  have hBc : ContinuousOn B (Ioi 0) := fun τ hτ => (tb.hB τ hτ).continuousAt.continuousWithinAt
  have hϕc : ContinuousOn ϕ (Ioi 0) := fun τ hτ => (tb.hϕ τ hτ).continuousAt.continuousWithinAt
  have hgsc : ContinuousOn (fun s : ℝ => gs (s : ℂ)) (Icc 0 s1) := by
    intro s hs
    have hmem : (s : ℂ) ∈ ball (0 : ℂ) (3 * s1) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
    exact ((hgs_diff.continuousOn.continuousAt (isOpen_ball.mem_nhds hmem)).comp (f := fun s : ℝ => (s : ℂ))
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hhead := head_eq (c := c) (lam := lam) (s1 := s1) (R := rr ^ 2) (a := a) (U := Ua) (KB := KB) (T := T) (T1 := T1)
    (B := B) (ϕ := ϕ) (gs := gs) (Nc := Nc) (N1 := N1) hc hlam hlc hs1 hsR hUa hNc
    (fun s hs => pb.hT s ⟨hs.1, hs.2.trans hs1s.le⟩) (fun s hs => pb.hT1 s ⟨hs.1, hs.2.trans hs1s.le⟩) pb.hT0 hBc hϕc
    tb.hKB tb.hbB (fun s hs => pb.hBT s ⟨hs.1, hs.2.trans hs1s.le⟩)
    (fun s hs => pb.hϕT s ⟨hs.1, hs.2.trans hs1s.le⟩) hgsc
  have hR₀pos : 0 < R₀ := lt_trans hR0 hRR
  have hdiffG : DifferentiableOn ℂ (fun w => gs ((lam : ℂ) * w) * Complex.exp (Complex.I * PhU Ua w)) (ball 0 R₀) := by
    intro w hw
    have hwn : ‖w‖ < R₀ := by simpa using hw
    have hmem : (lam : ℂ) * w ∈ ball (0 : ℂ) (3 * s1) := by
      rw [mem_ball, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
      nlinarith [mul_lt_mul_of_pos_left hwn hlam]
    have h1 : DifferentiableAt ℂ gs ((lam : ℂ) * w) := (hgs_diff _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)
    have h2 : DifferentiableAt ℂ (fun w : ℂ => gs ((lam : ℂ) * w)) w := h1.comp w (by fun_prop)
    have h3 : DifferentiableAt ℂ (fun w => Complex.exp (Complex.I * PhU Ua w)) w := by
      unfold PhU; fun_prop
    exact (h2.mul h3).differentiableWithinAt
  have hdef := deform_real hR₀pos hRR hR0 hdiffG ch
  have hsegt : ∀ t ∈ Icc (0 : ℝ) 1, ‖segPt (rr ^ 2) t‖ ≤ rr ^ 2 := fun t ht => norm_segPt_le hR0.le ht.1 ht.2
  have hgdat := fun t (ht : t ∈ Icc (0 : ℝ) 1) => gW_data hs1 hlam hsR hgs_diff hgs_bd (hsegt t ht)
  have hdd2 : ContinuousOn (deriv (deriv gs)) (ball 0 (3 * s1)) :=
    ((hgs_diff.deriv isOpen_ball).deriv isOpen_ball).continuousOn
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
  have hexpU : ∀ w : ℂ, Complex.exp (Complex.I * (psi : ℂ) * ((lam : ℂ) * w)) * Complex.exp (Complex.I * PhU Ua w) =
      Complex.exp (Complex.I * PhU Uh w) := by
    intro w
    rw [← Complex.exp_add]
    congr 1
    unfold PhU
    have : ((kap : ℝ) : ℂ) * ((Uh : ℝ) : ℂ) - ((kap : ℝ) : ℂ) * ((Ua : ℝ) : ℂ) = (lam : ℂ) * (psi : ℂ) := by
      have hl2 : lam ^ 2 * (kap * (Uh - Ua) - lam * psi) = 0 := by linear_combination hUh + hUa
      have hl2n : lam ^ 2 ≠ 0 := by positivity
      have := (mul_eq_zero.1 hl2).resolve_left hl2n
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
    exact ((hgs_diff _ hmem).differentiableAt (isOpen_ball.mem_nhds hmem)).hasDerivAt
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
  have hch' : ch.int (fun z => csr z * gW z * Complex.exp (Complex.I * PhU Ua z)) =
      ch.intE Uh (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) *
        E ((lam : ℂ) * w))) := by
    rw [← hch]; congr 1; funext z; simp only [hgW]; ring
  rw [hexp.symm.trans rfl, hhead', hsegEq, hch']
  set chint := ch.intE Uh (fun w => csr w * ((1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) *
    E ((lam : ℂ) * w))) with hchint
  set e1 := Complex.exp (Complex.I * PhU Ua (((rr ^ 2 : ℝ)) : ℂ))
  set P1 := csrF gW (((rr ^ 2 : ℝ)) : ℂ) / (Complex.I * GG Ua (((rr ^ 2 : ℝ)) : ℂ))
  set Hq1 := segH (csrF gW) (csrF1 gW gW1) (GG Ua) GG1 (((rr ^ 2 : ℝ)) : ℂ) /
    (Complex.I * GG Ua (((rr ^ 2 : ℝ)) : ℂ))
  set z0 : ℂ := segZ0 (rr ^ 2) + ((0 : ℝ) : ℂ) * segD (rr ^ 2)
  set P0 := csrF gW z0 / (Complex.I * GG Ua z0)
  set Hq0 := segH (csrF gW) (csrF1 gW gW1) (GG Ua) GG1 z0 / (Complex.I * GG Ua z0)
  set e0 := Complex.exp (Complex.I * PhU Ua z0)
  set Qint := lineInt (segZ0 (rr ^ 2)) (segD (rr ^ 2)) 0 1 (fun z => segQ (csrF gW) (csrF1 gW gW1)
    (csrF2 gW gW1 gW2) (GG Ua) GG1 GG2 z * Complex.exp (Complex.I * PhU Ua z))
  set Bq := B (T s1) / (((m (T s1) - L : ℝ)) : ℂ)
  set Hi := ibpH B B1 (fun τ => m τ - L) m1 (T s1) / (((m (T s1) - L : ℝ)) : ℂ)
  have hkey : N1 * (chint + ((P1 * e1 - P0 * e0) - 1 / Complex.I * (Hq1 * e1 - Hq0 * e0) +
        (1 / Complex.I) ^ 2 * Qint)) +
      (-(1 / (Complex.I * c) * (Bq * e1)) + (1 / (Complex.I * c)) ^ 2 * (Hi * e1) + (1 / (Complex.I * c)) ^ 2 * J) =
      N1 * chint + (-(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
        (1 / (Complex.I * c)) ^ 2 * J) := by
    linear_combination e1 * hba - e1 * hbb - (1 / (Complex.I * c)) * e1 * htb1 + (1 / (Complex.I * c)) ^ 2 * e1 * htb2
  rw [hkey]
  have hN1n : ‖N1‖ = 1 / √π := by
    rw [hN1, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_I_mul_ofReal, mul_one,
      abs_of_pos (by positivity)]
  have hfsOp : -(N1 * chint).re = fsOpCh ch Uh (fun w => (1 + (((lam : ℂ) * w) ^ 2 + (a : ℂ)) * Q ((lam : ℂ) * w)) *
      E ((lam : ℂ) * w)) := by
    unfold fsOpCh
    rw [hN1, mul_assoc, Complex.re_ofReal_mul]
    rw [hchint]; ring
  have hCg : 0 ≤ 2 * Cb := by positivity
  obtain ⟨hdat1, hdat2, hdat3, hdat4, _⟩ := hgdat 0 ⟨le_rfl, zero_le_one⟩
  have hbd0 := norm_seg_bdry_le (U := Ua) (ρ := rr) (t := 0) (gW := gW) (gW1 := gW1) hrr le_rfl zero_le_one hCg hseg
    (hdat3.trans (by linarith)) hdat4
  have hIm := im_PhU_segPt (U := Ua) (R := rr ^ 2) (t := 0) hR0.le le_rfl zero_le_one hseg
  have he0n : ‖e0‖ ≤ Real.exp (-((rr ^ 2) ^ 3 / 4)) := by
    have he : ‖Complex.exp (Complex.I * PhU Ua z0)‖ = Real.exp (-(PhU Ua z0).im) := norm_exp_I_mul _
    have hseg0 : segPt (rr ^ 2) 0 = z0 := by rfl
    rw [hseg0] at hIm
    dsimp [e0]
    rw [he]
    apply Real.exp_le_exp.2
    have h1 : (rr ^ 2) ^ 3 / 4 ≤ rr ^ 2 / 2 * (29 * (rr ^ 2) ^ 2 / 48) * (1 - 0) := by
      have : 0 ≤ (rr ^ 2) ^ 3 := by positivity
      nlinarith
    linarith only [h1, hIm]
  set Rest := -(N1 * (P0 * e0)) + N1 * (1 / Complex.I * (Hq0 * e0)) + N1 * ((1 / Complex.I) ^ 2 * Qint) +
    (1 / (Complex.I * c)) ^ 2 * J
  have hRest : ‖Rest‖ ≤
      (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
        320000 * (2 * Cb) / rr ^ 9) +
      (1 / c ^ 2) * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * (T s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (T s1) ^ (-3 / 2 : ℝ))) := by
    have hP0n : ‖P0‖ ≤ 16 * (2 * Cb) / rr ^ 3 := hbd0.1
    have hHq0n : ‖Hq0‖ ≤ 1024 * (2 * Cb) / rr ^ 9 := hbd0.2
    have hI1 : ‖(1 : ℂ) / Complex.I‖ = 1 := by simp
    have hc2 : ‖(1 / (Complex.I * (c : ℂ))) ^ 2‖ = 1 / c ^ 2 := by
      rw [norm_pow, norm_div, norm_one, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hc, div_pow, one_pow]
    have hEe : 0 ≤ Real.exp (-((rr ^ 2) ^ 3 / 4)) := (Real.exp_pos _).le
    have t1 : ‖N1 * (P0 * e0)‖ ≤ (1 / √π) * (16 * (2 * Cb) / rr ^ 3 * Real.exp (-((rr ^ 2) ^ 3 / 4))) := by
      rw [norm_mul, norm_mul, hN1n]; gcongr
    have t2 : ‖N1 * (1 / Complex.I * (Hq0 * e0))‖ ≤
        (1 / √π) * (1024 * (2 * Cb) / rr ^ 9 * Real.exp (-((rr ^ 2) ^ 3 / 4))) := by
      rw [norm_mul, norm_mul, norm_mul, hN1n, hI1, one_mul]; gcongr
    have t3 : ‖N1 * ((1 / Complex.I) ^ 2 * Qint)‖ ≤ (1 / √π) * (320000 * (2 * Cb) / rr ^ 9) := by
      rw [norm_mul, norm_mul, norm_pow, hN1n, hI1, one_pow, one_mul]; gcongr
    have t4 : ‖(1 / (Complex.I * (c : ℂ))) ^ 2 * J‖ ≤ (1 / c ^ 2) * ((4 * KB * (1 + 4 * C0 / γ + 3 * C0 ^ 2 / γ ^ 2) / γ ^ 2) *
        ((2 / 9) * (T s1) ^ (-9 / 2 : ℝ) + (2 / 3) * (T s1) ^ (-3 / 2 : ℝ))) := by
      rw [norm_mul, hc2]; gcongr
    calc ‖Rest‖ ≤ ‖-(N1 * (P0 * e0))‖ + ‖N1 * (1 / Complex.I * (Hq0 * e0))‖ + ‖N1 * ((1 / Complex.I) ^ 2 * Qint)‖ +
          ‖(1 / (Complex.I * c)) ^ 2 * J‖ :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
      _ ≤ _ := by
          rw [norm_neg]
          have e : (1 / √π) * ((16 * (2 * Cb) / rr ^ 3 + 1024 * (2 * Cb) / rr ^ 9) * Real.exp (-((rr ^ 2) ^ 3 / 4)) +
              320000 * (2 * Cb) / rr ^ 9) =
              (1 / √π) * (16 * (2 * Cb) / rr ^ 3 * Real.exp (-((rr ^ 2) ^ 3 / 4))) +
              (1 / √π) * (1024 * (2 * Cb) / rr ^ 9 * Real.exp (-((rr ^ 2) ^ 3 / 4))) +
              (1 / √π) * (320000 * (2 * Cb) / rr ^ 9) := by ring
          rw [e]; linarith
  have hre : -(N1 * chint + Rest).re - (-(N1 * chint).re) = -Rest.re := by
    simp only [Complex.add_re]; ring
  rw [← hfsOp, hre, abs_neg]
  exact (Complex.abs_re_le_norm Rest).trans hRest

/-! ### Part 2: Concrete Hankel `HalfCubicData` -/

private lemma binetRem_conj (w : ℂ) :
    FormalResearch.Asymptotics.binetRem (starRingEnd ℂ w) =
      starRingEnd ℂ (FormalResearch.Asymptotics.binetRem w) := by
  unfold FormalResearch.Asymptotics.binetRem
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]

private lemma binetDiff_conj {c : ℝ} {w : ℂ} :
    FormalResearch.Asymptotics.binetDiff c (starRingEnd ℂ w) =
      starRingEnd ℂ (FormalResearch.Asymptotics.binetDiff c w) := by
  unfold FormalResearch.Asymptotics.binetDiff
  have h1 : (c : ℂ) * (1 - starRingEnd ℂ w) = starRingEnd ℂ ((c : ℂ) * (1 - w)) := by simp
  have h2 : FormalResearch.Asymptotics.binetRem (c : ℂ) =
      starRingEnd ℂ (FormalResearch.Asymptotics.binetRem (c : ℂ)) := by
    nth_rw 1 [← Complex.conj_ofReal c]
    exact binetRem_conj (c : ℂ)
  rw [h1, binetRem_conj]
  conv_lhs => rw [h2]
  rw [← map_sub]

/-- Real symmetry of `Tsd` near `0`. -/
private lemma tsd_im_zero_near {ε : ℝ} {ϑ : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hreg : ChartReg ε ϑ ρ) :
    ∃ r_y > (0 : ℝ), ∃ r_β > (0 : ℝ),
      ∀ y β : ℝ, |y| < r_y → |β| < r_β → (Tsd ((y : ℂ), (β : ℂ))).im = 0 := by
  have hc : ContinuousAt Tsd (0, 0) := contDiffAt_Tsd.continuousAt
  obtain ⟨rT, hrT, hdT⟩ := Metric.eventually_nhds_iff_ball.mp (ev_diff contDiffAt_Tsd)
  have hballT : ∃ r0 > (0 : ℝ), ∀ y β : ℂ, ‖y‖ < r0 → ‖β‖ < r0 → DifferentiableAt ℂ Tsd (y, β) := by
    refine ⟨rT, hrT, fun y β hy hβ => hdT _ (by rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hy hβ)⟩
  obtain ⟨r0, hr0, hTdiff⟩ := hballT
  let r_y : ℝ := min r0 (ρ ^ 2 / 2)
  let r_β : ℝ := min r0 ρ
  refine ⟨r_y, lt_min hr0 (by positivity), r_β, lt_min hr0 hρ, fun y β hy hβ => ?_⟩
  have hβ' : ‖(β : ℂ)‖ < r0 := by simpa [Real.norm_eq_abs] using lt_of_lt_of_le hβ (min_le_left _ _)
  have hdiff_y : DifferentiableOn ℂ (fun z : ℂ => Tsd (z, (β : ℂ))) (ball 0 r_y) := fun z hz => by
    have hz' : ‖z‖ < r0 := (mem_ball_zero_iff.1 hz).trans_le (min_le_left _ _)
    have hcd : DifferentiableAt ℂ (fun w : ℂ => Tsd (w, (β : ℂ))) z :=
      DifferentiableAt.comp (g := Tsd) z (hTdiff z (β : ℂ) hz' hβ')
        ((differentiableAt_id : DifferentiableAt ℂ (fun w : ℂ => w) z).prodMk
          (differentiableAt_const (β : ℂ)))
    exact hcd.differentiableWithinAt
  refine im_zero_on_ball_of_pos_real (lt_min hr0 (by positivity)) hdiff_y (fun q hq0 hq_lt => ?_) y hy
  have hs_lt : |Real.sqrt q| < ρ := by
    rw [abs_of_nonneg (Real.sqrt_nonneg q)]
    have h1 : Real.sqrt q < Real.sqrt (ρ ^ 2) := Real.sqrt_lt_sqrt hq0.le (by linarith [lt_of_lt_of_le hq_lt (min_le_right _ _), sq_pos_of_pos hρ])
    simpa [Real.sqrt_sq hρ.le] using h1
  have hβ_lt : |β| < ρ := lt_of_lt_of_le hβ (min_le_right _ _)
  have hdt := Treal_deriv (fun s hs => (hreg s (β : ℂ) hs (by simpa using hβ_lt)).2.1)
    (fun s hs => (hreg s (β : ℂ) hs (by simpa using hβ_lt)).2.2.1) hs_lt
  have hsq : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hq0.le]
  have heq := hdt.2
  rw [hsq] at heq
  rw [heq, Complex.ofReal_im]

/-- Concrete Hankel `HalfCubicData` together with all chart & remainder data. -/
theorem hankelHalfCubic (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    ∃ (d : HalfCubicData) (ϑ : ℂ → ℂ) (th : ℝ → ℝ) (zA_C : ℂ → ℂ) (r_s r_a ρ_reg M_Q K_b K_T r_T : ℝ),
      0 < r_s ∧ 0 < r_a ∧ 0 < ρ_reg ∧ 0 ≤ M_Q ∧ 0 ≤ K_b ∧ 0 ≤ K_T ∧ 0 < r_T ∧
      r_s < ρ_reg ∧ r_s < r_T / 2 ∧ d.r_a ≤ r_a ∧ d.s₁ ≤ 1 / (8 * K_T + 8) ∧ 3 * d.s₁ < r_s ∧
      d.r_q < (r_s / 2) ^ 2 ∧ d.r_q < (3 * d.s₁) ^ 2 ∧
      (∀ s β : ℂ, ‖s‖ < r_T → ‖β‖ < r_T → ‖Tf (s, β)‖ ≤ K_T * ‖s‖) ∧
      AnalyticAt ℝ th 0 ∧ (∀ᶠ τ in 𝓝 (0 : ℝ), CtOuter.outerTheta ε τ = τ * th (τ ^ 2)) ∧
      ChartReg ε ϑ ρ_reg ∧
      DifferentiableOn ℂ zA_C (ball 0 r_a) ∧ (∀ a ∈ ball (0 : ℂ) r_a, ‖zA_C a‖ < ρ_reg ∧ ‖zA_C a‖ < r_T) ∧
      (∀ (a : ℝ), |a| < r_a → zA_C (a : ℂ) = (CtCfu.zA a : ℂ) ∧ CtCfu.AF (CtCfu.zA a) = a ∧
        aC (zA_C (a : ℂ)) = (a : ℂ) ∧ ysF (zA_C (a : ℂ)) = -(a : ℂ) ∧
        psiHat ϑ (zA_C (a : ℂ)) = (CtCfu.psiOf th a : ℂ) ∧ CtCfu.Xi a = hankelXiUnit a ∧
        CtCfu.NF (CtCfu.zA a) = Real.log (π ^ 2 * hankelXiUnit a)) ∧
      (∀ z ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖Qeps ϑ (z, zA_C a)‖ ≤ M_Q) ∧
      (∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun z => Qeps ϑ (z, zA_C a)) (ball 0 r_s)) ∧
      (∀ n z a, 2 ≤ n → z ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a →
        ‖Efun n (zA_C a) z - 1‖ ≤ K_b * n⁻¹) ∧
      (∀ n a, 2 ≤ n → a ∈ ball (0 : ℂ) r_a → DifferentiableOn ℂ (fun z => Efun n (zA_C a) z) (ball 0 r_s)) ∧
      (∀ n a s, 2 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖s‖ < r_s / 2 →
        d.B n a s = (1 + (s ^ 2 + a) * Qeps ϑ (s, zA_C a)) * Efun n (zA_C a) s) ∧
      (∀ n (a : ℝ), 1 ≤ n → |a| < d.r_a → d.ψ n (a : ℂ) = (CtCfu.psiOf th a : ℂ)) ∧
      (∃ K_E K_O : ℝ, 0 ≤ K_E ∧ 0 ≤ K_O ∧
        (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.E n (-a) a - 1‖ ≤ K_E * n⁻¹) ∧
        (∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) d.r_a → ‖d.O n (-a) a‖ ≤ K_O * n⁻¹)) := by
  obtain ⟨ϑ, hϑA, hϑ⟩ := exists_vartheta ε
  obtain ⟨th, hthA, hth, -, -⟩ := CtCfu.theta_hat hε
  have hϑconj := vartheta_conj hϑA hϑ hth
  obtain ⟨ρ_reg, hρ_reg, hreg⟩ := chart_region hϑA hϑ
  obtain ⟨K_T, r_T, hK_T, hr_T, hTf_lip⟩ := exists_Tf_lip
  obtain ⟨r_z, zA_C, hr_z, hzA_diff, hzA_conj, hzA_real⟩ := exists_complex_extension CtCfu.analyticAt_zA
  obtain ⟨r_ψ, Ψ_a, hr_ψ, hΨ_diff, _, hΨ_real⟩ := exists_complex_extension (CtCfu.analyticAt_psiOf hthA)
  -- Local bounds and reality of `Tf`, `Qeps`, `muf`, `ysF`, `htil`, `dC`, `kC`, `Uf`
  have hQ_norm : ContinuousAt (Qeps ϑ) (0, 0) := (contDiffAt_Qeps hϑA).continuousAt
  obtain ⟨rQ1, hrQ1, hQ_bd0⟩ := Metric.eventually_nhds_iff_ball.mp
    (hQ_norm.eventually (Metric.ball_mem_nhds (Qeps ϑ (0, 0)) zero_lt_one))
  obtain ⟨rQ_d, hrQ_d, hQd⟩ := Metric.eventually_nhds_iff_ball.mp (ev_diff (contDiffAt_Qeps hϑA))
  obtain ⟨rTf_d, hrTf_d, hTfd⟩ := Metric.eventually_nhds_iff_ball.mp (ev_diff contDiffAt_Tf)
  have hTf_small : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), ‖Tf p‖ < 1 / 4 := by
    have := contDiffAt_Tf.continuousAt.eventually
      (Metric.ball_mem_nhds (Tf (0, 0)) (by norm_num : (0 : ℝ) < 1 / 4))
    refine this.mono fun p hp => ?_
    simpa [Tf_zero, dist_zero_right] using hp
  obtain ⟨rTf_b, hrTf_b, hTfb⟩ := Metric.eventually_nhds_iff_ball.mp hTf_small
  have hmuf_pos : ∀ᶠ q : ℂ × ℂ in 𝓝 (0, 0), 0 < (Uf q * kC (Zf q) / 2).re := by
    have hct : ContinuousAt (fun q : ℂ × ℂ => (Uf q * kC (Zf q) / 2).re) (0, 0) :=
      Complex.continuous_re.continuousAt.comp ((contDiffAt_Uf.mul contDiffAt_kZ).div_const 2).continuousAt
    have h0 : 0 < (Uf (0, 0) * kC (Zf (0, 0)) / 2).re := by
      rw [Sigma_zero, ← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_pos_of_pos CtCfu.d0_pos
    exact hct.eventually (lt_mem_nhds h0)
  obtain ⟨rSig, hrSig, hSig⟩ := Metric.eventually_nhds_iff_ball.mp hmuf_pos
  obtain ⟨rU_c, hrU_c, hU_c⟩ := Metric.eventually_nhds_iff_ball.mp Uf_conj
  obtain ⟨rZ_c, hrZ_c, hZ_c⟩ := Metric.eventually_nhds_iff_ball.mp Zf_conj
  obtain ⟨rH_c, hrH_c, hH_c⟩ := Metric.eventually_nhds_iff_ball.mp (CtChart.hF_conj hϑconj)
  obtain ⟨rHad, hrHad, hHad⟩ := Metric.eventually_nhds_iff_ball.mp (hadY_identity (contDiffAt_hF hϑA))
  obtain ⟨rTsd_y, hrTsd_y, rTsd_β, hrTsd_β, hTsd_im⟩ := tsd_im_zero_near hρ_reg hreg
  obtain ⟨rdC, hrdC, hdC_conj⟩ := Metric.eventually_nhds_iff.mp dC_conj
  obtain ⟨rhtil_c, hrhtil_c, hhtil_c⟩ := Metric.eventually_nhds_iff_ball.mp
    (ev_diff (contDiffAt_htil hϑA))
  obtain ⟨rAmp, hrAmp, hAmp⟩ := Metric.eventually_nhds_iff_ball.mp (amp_decomp ϑ)
  obtain ⟨δ_X, hδ_X, hXi_eq⟩ := ctCfu_Xi_eq_hankelXiUnit
  obtain ⟨r_link, hr_link, hLink⟩ := Metric.eventually_nhds_iff.mp
    (CtChart.psiHat_link hϑA hthA hϑ hth)
  -- Common polydisc radius `r_p` in `(y, β)` and `r_β` in `(s, β)`
  let r_p : ℝ := min (min rSig (min rU_c rZ_c))
    (min (min rH_c rHad) (min (min rTsd_y rTsd_β) (min rdC rhtil_c)))
  have hr_p : 0 < r_p := lt_min (lt_min hrSig (lt_min hrU_c hrZ_c))
    (lt_min (lt_min hrH_c hrHad) (lt_min (lt_min hrTsd_y hrTsd_β) (lt_min hrdC hrhtil_c)))
  have hrp_Sig : r_p ≤ rSig := (min_le_left _ _).trans (min_le_left _ _)
  have hrp_Uc : r_p ≤ rU_c := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrp_Zc : r_p ≤ rZ_c := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrp_Hc : r_p ≤ rH_c := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrp_Had : r_p ≤ rHad := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrp_TsdY : r_p ≤ rTsd_y :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hrp_TsdB : r_p ≤ rTsd_β :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hrp_htil : r_p ≤ rhtil_c :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let r_β : ℝ := min (min (min ρ_reg r_p) (min rQ1 rQ_d)) (min (min rTf_d rTf_b) (min rAmp r_T))
  have hr_β : 0 < r_β := lt_min (lt_min (lt_min hρ_reg hr_p) (lt_min hrQ1 hrQ_d))
    (lt_min (lt_min hrTf_d hrTf_b) (lt_min hrAmp hr_T))
  have hrβ_ρ : r_β ≤ ρ_reg := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hrβ_p : r_β ≤ r_p := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hrβ_Q1 : r_β ≤ rQ1 := ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrβ_Qd : r_β ≤ rQ_d := ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hrβ_Tfd : r_β ≤ rTf_d := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hrβ_Tfb : r_β ≤ rTf_b := ((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hrβ_Amp : r_β ≤ rAmp := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hrβ_rT : r_β ≤ r_T := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  -- Shrink `r_s < min (r_β / 2) (min (√r_p) (1 / (2 * K_T + 2)))`
  let r_s : ℝ := (min (min r_β (1 / (K_T + 1))) (Real.sqrt r_p)) / 3
  have hr_s : 0 < r_s :=
    div_pos (lt_min (lt_min hr_β (by positivity)) (Real.sqrt_pos.2 hr_p)) (by norm_num)
  have hrs_β : r_s < r_β := by
    have h1 : r_s ≤ r_β / 3 :=
      div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
    linarith only [h1, hr_β]
  have hrs_KT : r_s ≤ 1 / (3 * K_T + 3) := by
    have h1 : r_s ≤ (1 / (K_T + 1)) / 3 :=
      div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_right _ _)) (by norm_num)
    have h2 : (1 / (K_T + 1)) / 3 = 1 / (3 * K_T + 3) := by field_simp
    exact h1.trans_eq h2
  have hrs_ρ : r_s < ρ_reg := hrs_β.trans_le hrβ_ρ
  have hrs_rT : r_s < r_T / 2 := by
    have h1 : r_s ≤ r_β / 3 :=
      div_le_div_of_nonneg_right ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
    have h2 : r_β / 3 ≤ r_T / 3 := div_le_div_of_nonneg_right hrβ_rT (by norm_num)
    linarith only [h1, h2, hr_T]
  have hrs_sq : r_s ^ 2 < r_p := by
    have h1 : r_s ≤ Real.sqrt r_p / 3 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have h2 : r_s ^ 2 ≤ r_p / 9 := calc
      r_s ^ 2 ≤ (Real.sqrt r_p / 3) ^ 2 := pow_le_pow_left₀ hr_s.le h1 2
      _ = r_p / 9 := by rw [div_pow, Real.sq_sqrt hr_p.le]; norm_num
    linarith only [h2, hr_p]
  -- Choose `r_a` so `zA_C` is holomorphic on `ball 0 r_a` with image in `ball 0 r_β` and `a ∈ ball 0 (min (r_ψ/2) r_p)`
  have hzA0 : zA_C 0 = 0 := by simpa [CtCfu.zA_zero] using hzA_real 0 (by simpa using hr_z)
  have hzA_cont : ContinuousAt zA_C 0 :=
    ((hzA_diff 0 (mem_ball_self hr_z)).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr_z))).continuousAt
  obtain ⟨r_zβ, hr_zβ, hzA_β⟩ := Metric.eventually_nhds_iff.mp
    (hzA_cont.eventually (by rw [hzA0]; exact Metric.ball_mem_nhds 0 hr_β))
  let r_a : ℝ := min (min r_z r_zβ) (min (r_ψ / 2) (min δ_X (min r_link r_p)))
  have hr_a : 0 < r_a :=
    lt_min (lt_min hr_z hr_zβ) (lt_min (half_pos hr_ψ) (lt_min hδ_X (lt_min hr_link hr_p)))
  have hzA_ball_z : ∀ a ∈ ball (0 : ℂ) r_a, a ∈ ball (0 : ℂ) r_z := fun a ha =>
    ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)) ha
  have hzA_diff_a : DifferentiableOn ℂ zA_C (ball 0 r_a) := fun a ha =>
    (hzA_diff a (hzA_ball_z a ha)).mono (ball_subset_ball ((min_le_left _ _).trans (min_le_left _ _)))
  have hzA_in_β : ∀ a ∈ ball (0 : ℂ) r_a, ‖zA_C a‖ < r_β := fun a ha => by
    have hda : dist a 0 < r_zβ := by
      simpa [dist_zero_right] using (mem_ball_zero_iff.1 ha).trans_le ((min_le_left _ _).trans (min_le_right _ _))
    simpa [dist_zero_right] using hzA_β hda
  have hzA_in_ρ : ∀ a ∈ ball (0 : ℂ) r_a, ‖zA_C a‖ < ρ_reg := fun a ha =>
    (hzA_in_β a ha).trans_le hrβ_ρ
  have hzA_in_rT : ∀ a ∈ ball (0 : ℂ) r_a, ‖zA_C a‖ < r_T := fun a ha =>
    (hzA_in_β a ha).trans_le hrβ_rT
  -- Bound on `Ψ_a` over `closedBall 0 (r_ψ / 2)`
  have hΨ_cont_cb : ContinuousOn Ψ_a (closedBall 0 (r_ψ / 2)) :=
    hΨ_diff.continuousOn.mono (closedBall_subset_ball (half_lt_self hr_ψ))
  obtain ⟨a_m, _, hΨ_max⟩ := (isCompact_closedBall (0 : ℂ) (r_ψ / 2)).exists_isMaxOn
    ⟨0, mem_closedBall_self (half_pos hr_ψ).le⟩ hΨ_cont_cb.norm
  let M_ψ : ℝ := ‖Ψ_a a_m‖
  have hM_ψ : 0 ≤ M_ψ := norm_nonneg _
  have hΨ_bd : ∀ a ∈ ball (0 : ℂ) r_a, ‖Ψ_a a‖ ≤ M_ψ := fun a ha => by
    apply hΨ_max
    rw [mem_closedBall_zero_iff]
    exact ((mem_ball_zero_iff.1 ha).trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  -- Bound and holomorphy on `Q(z, a) := Qeps ϑ (z, zA_C a)`
  let Q : ℂ → ℂ → ℂ := fun z a => Qeps ϑ (z, zA_C a)
  let M_Q : ℝ := ‖Qeps ϑ (0, 0)‖ + 1
  have hM_Q : 0 ≤ M_Q := by positivity
  have hQ_bd : ∀ z ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖Q z a‖ ≤ M_Q := fun z hz a ha => by
    have hzβ : ‖z‖ < rQ1 := (mem_ball_zero_iff.1 hz).trans (hrs_β.trans_le hrβ_Q1)
    have haβ : ‖zA_C a‖ < rQ1 := (hzA_in_β a ha).trans_le hrβ_Q1
    have hp : (z, zA_C a) ∈ ball ((0 : ℂ), (0 : ℂ)) rQ1 := by
      rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hzβ haβ
    have h1 := hQ_bd0 _ hp
    rw [dist_eq_norm] at h1
    calc ‖Qeps ϑ (z, zA_C a)‖ = ‖Qeps ϑ (0, 0) + (Qeps ϑ (z, zA_C a) - Qeps ϑ (0, 0))‖ := by ring_nf
      _ ≤ ‖Qeps ϑ (0, 0)‖ + ‖Qeps ϑ (z, zA_C a) - Qeps ϑ (0, 0)‖ := norm_add_le _ _
      _ ≤ ‖Qeps ϑ (0, 0)‖ + 1 := by linarith
  have hQ_s : ∀ a ∈ ball (0 : ℂ) r_a, DifferentiableOn ℂ (fun ζ => Q ζ a) (ball 0 r_s) := fun a ha z hz => by
    have hz1 : ‖z‖ < rQ_d := (mem_ball_zero_iff.1 hz).trans (hrs_β.trans_le hrβ_Qd)
    have ha1 : ‖zA_C a‖ < rQ_d := (hzA_in_β a ha).trans_le hrβ_Qd
    have hd := hQd (z, zA_C a) (by rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hz1 ha1)
    exact (DifferentiableAt.comp (g := Qeps ϑ) z hd
      ((differentiableAt_id : DifferentiableAt ℂ (fun ζ : ℂ => ζ) z).prodMk
        (differentiableAt_const (zA_C a)))).differentiableWithinAt
  have hQ_a : ∀ ζ ∈ ball (0 : ℂ) r_s, DifferentiableOn ℂ (Q ζ) (ball 0 r_a) := fun ζ hζ a ha => by
    have hz1 : ‖ζ‖ < rQ_d := (mem_ball_zero_iff.1 hζ).trans (hrs_β.trans_le hrβ_Qd)
    have ha1 : ‖zA_C a‖ < rQ_d := (hzA_in_β a ha).trans_le hrβ_Qd
    have hd := hQd (ζ, zA_C a) (by rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hz1 ha1)
    have hzd := (hzA_diff_a a ha).differentiableAt (isOpen_ball.mem_nhds ha)
    exact (DifferentiableAt.comp (g := Qeps ϑ) a hd ((differentiableAt_const ζ).prodMk hzd)).differentiableWithinAt
  -- Holomorphy & bound for `Eb n z a := Efun (max n 2) (zA_C a) z`
  let Eb : ℝ → ℂ → ℂ → ℂ := fun n z a => Efun (max n 2) (zA_C a) z
  have hTf_bd : ∀ z ∈ ball (0 : ℂ) r_s, ∀ a ∈ ball (0 : ℂ) r_a, ‖Tf (z, zA_C a)‖ < 1 / 4 := fun z hz a ha => by
    have hz1 : ‖z‖ < rTf_b := (mem_ball_zero_iff.1 hz).trans (hrs_β.trans_le hrβ_Tfb)
    have ha1 : ‖zA_C a‖ < rTf_b := (hzA_in_β a ha).trans_le hrβ_Tfb
    exact hTfb _ (by rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hz1 ha1)
  have hEb_s : ∀ n a, 1 ≤ n → a ∈ ball (0 : ℂ) r_a → DifferentiableOn ℂ (fun ζ => Eb n ζ a) (ball 0 r_s) := by
    intro n a _ ha z hz
    have hz1 : ‖z‖ < rTf_d := (mem_ball_zero_iff.1 hz).trans (hrs_β.trans_le hrβ_Tfd)
    have ha1 : ‖zA_C a‖ < rTf_d := (hzA_in_β a ha).trans_le hrβ_Tfd
    have hTd : DifferentiableAt ℂ (fun ζ : ℂ => Tf (ζ, zA_C a)) z :=
      DifferentiableAt.comp (g := Tf) z
        (hTfd (z, zA_C a) (by rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hz1 ha1))
        ((differentiableAt_id : DifferentiableAt ℂ (fun ζ : ℂ => ζ) z).prodMk (differentiableAt_const (zA_C a)))
    have hIm : Tf (z, zA_C a) ∈ {τ : ℂ | -1 < τ.im} := by
      have h1 := (Complex.abs_im_le_norm (Tf (z, zA_C a))).trans (hTf_bd z hz a ha).le
      show -1 < (Tf (z, zA_C a)).im
      linarith [(abs_le.1 h1).1]
    have hB : DifferentiableAt ℂ (fun τ : ℂ => FormalResearch.Asymptotics.binetDiff (max n 2) (Complex.I * τ))
        (Tf (z, zA_C a)) :=
      (BinetDecay.differentiableOn_binetDiff_vertical (by linarith [le_max_right n 2] : 0 < max n 2) _ hIm).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hIm)
    have hE_at : DifferentiableAt ℂ
        (fun τ : ℂ => Complex.exp (-FormalResearch.Asymptotics.binetDiff (max n 2) (Complex.I * τ)))
        (Tf (z, zA_C a)) := hB.neg.cexp
    exact (hE_at.comp z hTd).differentiableWithinAt
  have hEb_a : ∀ n ζ, 1 ≤ n → ζ ∈ ball (0 : ℂ) r_s → DifferentiableOn ℂ (Eb n ζ) (ball 0 r_a) := by
    intro n ζ _ hζ a ha
    have hz1 : ‖ζ‖ < rTf_d := (mem_ball_zero_iff.1 hζ).trans (hrs_β.trans_le hrβ_Tfd)
    have ha1 : ‖zA_C a‖ < rTf_d := (hzA_in_β a ha).trans_le hrβ_Tfd
    have hzd := (hzA_diff_a a ha).differentiableAt (isOpen_ball.mem_nhds ha)
    have hTd : DifferentiableAt ℂ (fun x : ℂ => Tf (ζ, zA_C x)) a :=
      DifferentiableAt.comp (g := Tf) a
        (hTfd (ζ, zA_C a) (by rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right]; exact max_lt hz1 ha1))
        ((differentiableAt_const ζ).prodMk hzd)
    have hIm : Tf (ζ, zA_C a) ∈ {τ : ℂ | -1 < τ.im} := by
      have h1 := (Complex.abs_im_le_norm (Tf (ζ, zA_C a))).trans (hTf_bd ζ hζ a ha).le
      show -1 < (Tf (ζ, zA_C a)).im
      linarith [(abs_le.1 h1).1]
    have hB : DifferentiableAt ℂ (fun τ : ℂ => FormalResearch.Asymptotics.binetDiff (max n 2) (Complex.I * τ))
        (Tf (ζ, zA_C a)) :=
      (BinetDecay.differentiableOn_binetDiff_vertical (by linarith [le_max_right n 2] : 0 < max n 2) _ hIm).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hIm)
    have hE_at : DifferentiableAt ℂ
        (fun τ : ℂ => Complex.exp (-FormalResearch.Asymptotics.binetDiff (max n 2) (Complex.I * τ)))
        (Tf (ζ, zA_C a)) := hB.neg.cexp
    exact (hE_at.comp a hTd).differentiableWithinAt
  have hEb_bd_2 : ∀ n z a, 2 ≤ n → z ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a →
      ‖Efun n (zA_C a) z - 1‖ ≤ 2 * n⁻¹ := fun n z a hn hz ha => by
    have hζ : ‖Complex.I * Tf (z, zA_C a)‖ ≤ 1 / 2 := by
      rw [norm_mul, Complex.norm_I, one_mul]; linarith [hTf_bd z hz a ha]
    have hb := BinetDecay.norm_exp_neg_binetDiff_sub_one hn hζ
    have hnorm : 8 * ‖Complex.I * Tf (z, zA_C a)‖ / n ≤ 2 * n⁻¹ := by
      rw [norm_mul, Complex.norm_I, one_mul, div_eq_mul_inv]
      gcongr
      linarith [hTf_bd z hz a ha]
    exact hb.trans hnorm
  have hEb_bd : ∀ n z a, 1 ≤ n → z ∈ ball (0 : ℂ) r_s → a ∈ ball (0 : ℂ) r_a →
      ‖Eb n z a - 1‖ ≤ 2 * n⁻¹ := fun n z a hn hz ha => by
    refine (hEb_bd_2 (max n 2) z a (le_max_right _ _) hz ha).trans ?_
    have hn0 : 0 < n := by linarith
    gcongr
    exact le_max_left _ _
  -- Real link identities on `|a| < r_a`
  have hReal_link : ∀ a : ℝ, |a| < r_a →
      zA_C (a : ℂ) = (CtCfu.zA a : ℂ) ∧ CtCfu.AF (CtCfu.zA a) = a ∧
      aC (zA_C (a : ℂ)) = (a : ℂ) ∧ ysF (zA_C (a : ℂ)) = -(a : ℂ) ∧
      psiHat ϑ (zA_C (a : ℂ)) = (CtCfu.psiOf th a : ℂ) ∧ CtCfu.Xi a = hankelXiUnit a ∧
      CtCfu.NF (CtCfu.zA a) = Real.log (π ^ 2 * hankelXiUnit a) := by
    intro a ha
    have ha_z : |a| < r_z := ha.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have ha_X : |a| < δ_X := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have ha_l : dist a 0 < r_link := by
      rw [Real.dist_eq, sub_zero]
      exact ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
    have hz_eq := hzA_real a ha_z
    have hXi := hXi_eq a ha_X
    obtain ⟨haC, hpsi, -⟩ := hLink ha_l
    refine ⟨hz_eq, hXi.2.2, ?_, ?_, ?_, hXi.1, hXi.2.1⟩
    · rwa [hz_eq]
    · rw [ysF_eq_neg_aC, hz_eq, haC]
    · rwa [hz_eq]
  -- Reality/conjugation symmetry for `B_n(±x, a)` on `|x| < r_s, |a| < r_a`
  have hsym : ∀ n (x a : ℝ), 1 ≤ n → |x| < r_s → |a| < r_a →
      (1 + ((-(x : ℂ)) ^ 2 + (a : ℂ)) * Q (-(x : ℂ)) (a : ℂ)) * Eb n (-(x : ℂ)) (a : ℂ) =
        starRingEnd ℂ ((1 + ((x : ℂ) ^ 2 + (a : ℂ)) * Q (x : ℂ) (a : ℂ)) * Eb n (x : ℂ) (a : ℂ)) := by
    intro n x a hn hx ha
    have haC : (a : ℂ) ∈ ball (0 : ℂ) r_a := by simpa [mem_ball_zero_iff, Real.norm_eq_abs] using ha
    have hβ_lt : ‖zA_C (a : ℂ)‖ < r_β := hzA_in_β (a : ℂ) haC
    obtain ⟨hz_eq, _, _, hys_eq, _, _⟩ := hReal_link a ha
    set β : ℝ := CtCfu.zA a
    have hβ_eq : zA_C (a : ℂ) = (β : ℂ) := hz_eq
    have hβ_abs : |β| < r_β := by simpa [hβ_eq, Complex.norm_real, Real.norm_eq_abs] using hβ_lt
    have hx_β : |x| < r_β := hx.trans hrs_β
    have hx2_p : |x ^ 2| < r_p := by
      have : |x| ^ 2 < r_s ^ 2 := pow_lt_pow_left₀ hx (abs_nonneg x) (by norm_num)
      rw [abs_pow]; exact this.trans hrs_sq
    have hβ_p : |β| < r_p := hβ_abs.trans_le hrβ_p
    have ha_p : |a| < r_p := ha.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
    have hmem_p : ∀ y : ℝ, |y| < r_p → (((y : ℂ), (β : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) r_p) := fun y hy => by
      rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs]
      exact max_lt hy hβ_p
    -- 1. `Efun` conjugation symmetry
    have hTf_conj : Tf (conj2 ((x : ℂ), (β : ℂ))) = starRingEnd ℂ (Tf ((x : ℂ), (β : ℂ))) :=
      (hreg (x : ℂ) (β : ℂ) (by simpa [Complex.norm_real, Real.norm_eq_abs] using hx.trans hrs_ρ)
        (by simpa [Complex.norm_real, Real.norm_eq_abs] using hβ_abs.trans_le hrβ_ρ)).2.2.1
    have hTf_im : (Tf ((x : ℂ), (β : ℂ))).im = 0 := by
      have := congrArg Complex.im hTf_conj
      simp only [conj2, Complex.conj_ofReal, Complex.conj_im] at this
      linarith
    have hTf_odd : Tf (-(x : ℂ), (β : ℂ)) = -Tf ((x : ℂ), (β : ℂ)) := by
      unfold Tf; simp
    have hEfun_sym : Eb n (-(x : ℂ)) (a : ℂ) = starRingEnd ℂ (Eb n (x : ℂ) (a : ℂ)) := by
      dsimp [Eb, Efun]
      rw [hβ_eq, hTf_odd, ← Complex.exp_conj, map_neg, ← binetDiff_conj]
      congr 2
      have hconj_T : starRingEnd ℂ (Tf ((x : ℂ), (β : ℂ))) = Tf ((x : ℂ), (β : ℂ)) :=
        Complex.conj_eq_iff_im.2 hTf_im
      rw [map_mul, Complex.conj_I, hconj_T]; ring
    -- 2. `(muf (x^2, β)).im = 0`
    have hmuf_im : (muf ((x : ℂ) ^ 2, (β : ℂ))).im = 0 := by
      have hp_mem := hmem_p (x ^ 2) hx2_p
      have hZ_c1 := hZ_c _ (ball_subset_ball hrp_Zc hp_mem)
      have hU_c1 := hU_c _ (ball_subset_ball hrp_Uc hp_mem)
      have hSig1 := hSig _ (ball_subset_ball hrp_Sig hp_mem)
      have hZ_im : (Zf ((x : ℂ) ^ 2, (β : ℂ))).im = 0 := by
        have h1 : Zf (((x ^ 2 : ℝ) : ℂ), (β : ℂ)) = starRingEnd ℂ (Zf (((x ^ 2 : ℝ) : ℂ), (β : ℂ))) := by
          simpa [conj2] using hZ_c1
        rw [Complex.ofReal_pow] at h1; exact Complex.conj_eq_iff_im.1 h1.symm
      have hU_im : (Uf ((x : ℂ) ^ 2, (β : ℂ))).im = 0 := by
        have h1 : Uf (((x ^ 2 : ℝ) : ℂ), (β : ℂ)) = starRingEnd ℂ (Uf (((x ^ 2 : ℝ) : ℂ), (β : ℂ))) := by
          simpa [conj2] using hU_c1
        rw [Complex.ofReal_pow] at h1; exact Complex.conj_eq_iff_im.1 h1.symm
      have hk_im : (kC (Zf ((x : ℂ) ^ 2, (β : ℂ)))).im = 0 := by
        have hcZ : starRingEnd ℂ (Zf ((x : ℂ) ^ 2, (β : ℂ))) = Zf ((x : ℂ) ^ 2, (β : ℂ)) :=
          Complex.conj_eq_iff_im.2 hZ_im
        have hk1 : kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) = starRingEnd ℂ (kC (Zf ((x : ℂ) ^ 2, (β : ℂ)))) := by
          calc kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) = kC (starRingEnd ℂ (Zf ((x : ℂ) ^ 2, (β : ℂ)))) := by rw [hcZ]
            _ = starRingEnd ℂ (kC (Zf ((x : ℂ) ^ 2, (β : ℂ)))) := kC_conj _
        exact Complex.conj_eq_iff_im.1 hk1.symm
      have harg_im : (Uf ((x : ℂ) ^ 2, (β : ℂ)) * kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) / 2).im = 0 := by
        simp [Complex.mul_im, hU_im, hk_im]
      have harg_pos : 0 < (Uf ((x : ℂ) ^ 2, (β : ℂ)) * kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) / 2).re := by
        simpa [← Complex.ofReal_pow] using hSig1
      set r_arg := (Uf ((x : ℂ) ^ 2, (β : ℂ)) * kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) / 2).re
      have harg_eq : Uf ((x : ℂ) ^ 2, (β : ℂ)) * kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) / 2 = (r_arg : ℂ) :=
        Complex.ext rfl harg_im
      have hcsq_im : (csq (Uf ((x : ℂ) ^ 2, (β : ℂ)) * kC (Zf ((x : ℂ) ^ 2, (β : ℂ))) / 2)).im = 0 := by
        rw [harg_eq]; unfold csq
        rw [← Complex.ofReal_log harg_pos.le]
        have he : ((Real.log r_arg : ℝ) : ℂ) / 2 = ((Real.log r_arg / 2 : ℝ) : ℂ) := by push_cast; ring
        rw [he, ← Complex.ofReal_exp, Complex.ofReal_im]
      have htsd_im : (Tsd ((x : ℂ) ^ 2, (β : ℂ))).im = 0 := by
        rw [← Complex.ofReal_pow]
        exact hTsd_im (x ^ 2) β (hx2_p.trans_le hrp_TsdY) (hβ_p.trans_le hrp_TsdB)
      unfold muf
      simp only [Complex.mul_im, hcsq_im, htsd_im, mul_zero, zero_mul, add_zero]
    -- 3. `(htil ϑ (x^2, β)).im = 0` via `hadY_identity` + continuity
    have hhtil_im : (htil ϑ ((x : ℂ) ^ 2, (β : ℂ))).im = 0 := by
      have hF_im_fn : ∀ y : ℝ, |y| < r_p → (hF ϑ ((y : ℂ), (β : ℂ))).im = 0 := fun y hy => by
        have h1 := hH_c _ (ball_subset_ball hrp_Hc (hmem_p y hy))
        have h2 : hF ϑ ((y : ℂ), (β : ℂ)) = starRingEnd ℂ (hF ϑ ((y : ℂ), (β : ℂ))) := by simpa [conj2] using h1
        exact Complex.conj_eq_iff_im.1 h2.symm
      have h_ne_ys : ∀ y : ℝ, |y| < r_p → y ≠ -a → (htil ϑ ((y : ℂ), (β : ℂ))).im = 0 := fun y hy hne => by
        have hyd := hHad _ (ball_subset_ball hrp_Had (hmem_p y hy))
        dsimp only at hyd
        have hys_r : ysF (β : ℂ) = ((-a : ℝ) : ℂ) := by rw [← hβ_eq, hys_eq]; simp
        rw [hys_r] at hyd
        have him0 := congrArg Complex.im hyd
        have h1 := hF_im_fn y hy
        have h2 := hF_im_fn (-a) (by simpa [abs_neg] using ha_p)
        have hhad : hadY (hF ϑ) ((y : ℂ), (β : ℂ)) = htil ϑ ((y : ℂ), (β : ℂ)) := rfl
        have hsub_eq : (((y : ℂ) - ((-a : ℝ) : ℂ)) * hadY (hF ϑ) ((y : ℂ), (β : ℂ))) =
            (((y - (-a) : ℝ) : ℂ) * htil ϑ ((y : ℂ), (β : ℂ))) := by rw [hhad]; push_cast; ring
        rw [hsub_eq, Complex.sub_im, h1, h2, sub_zero] at him0
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at him0
        exact (mul_eq_zero.1 him0.symm).resolve_left (sub_ne_zero.2 hne)
      rw [← Complex.ofReal_pow]
      by_cases hne : x ^ 2 ≠ -a
      · exact h_ne_ys (x ^ 2) hx2_p hne
      · push Not at hne
        have hcont_y : ContinuousOn (fun y : ℝ => htil ϑ ((y : ℂ), (β : ℂ))) (Ioo (-r_p) r_p) := fun y hy => by
          have hp_mem : ((y : ℂ), (β : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rhtil_c :=
            ball_subset_ball hrp_htil (hmem_p y (abs_lt.2 hy))
          have hca : ContinuousAt (fun t : ℝ => htil ϑ ((t : ℂ), (β : ℂ))) y :=
            ContinuousAt.comp (g := htil ϑ) (f := fun t : ℝ => ((t : ℂ), (β : ℂ)))
              (hhtil_c _ hp_mem).continuousAt
              (Complex.continuous_ofReal.continuousAt.prodMk continuousAt_const)
          exact hca.continuousWithinAt
        have hpos_d : 0 < (r_p - |a|) / 2 := by linarith [abs_lt.1 ha_p]
        have hseq : Tendsto (fun k : ℕ => -a + 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2)) atTop (𝓝 (-a)) := by
          have h1 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2)) atTop (𝓝 (0 * ((r_p - |a|) / 2))) :=
            tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
          simpa using tendsto_const_nhds.add h1
        have him_t : Tendsto (fun k : ℕ => (htil ϑ (((-a + 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2) : ℝ) : ℂ), (β : ℂ))).im)
            atTop (𝓝 (htil ϑ (((-a : ℝ) : ℂ), (β : ℂ))).im) := by
          have hca : ContinuousAt (fun y : ℝ => (htil ϑ ((y : ℂ), (β : ℂ))).im) (-a) :=
            Complex.continuous_im.continuousAt.comp (hcont_y.continuousAt (isOpen_Ioo.mem_nhds (abs_lt.1 (by simpa [abs_neg] using ha_p))))
          exact hca.tendsto.comp hseq
        have hev : (fun k : ℕ => (htil ϑ (((-a + 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2) : ℝ) : ℂ), (β : ℂ))).im) =ᶠ[atTop]
            fun _ => 0 := by
          filter_upwards [Filter.eventually_ge_atTop 1] with k _
          have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
          have hpos_k : 0 < 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2) := by positivity
          have hle_k : 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2) ≤ (r_p - |a|) / 2 :=
            mul_le_of_le_one_left hpos_d.le (div_le_one_of_le₀ hk1 (by positivity))
          have hy_abs : |-a + 1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2)| < r_p := by
            have := abs_add_le (-a) (1 / ((k : ℝ) + 1) * ((r_p - |a|) / 2))
            rw [abs_neg, abs_of_pos hpos_k] at this
            linarith [abs_lt.1 ha_p]
          exact h_ne_ys _ hy_abs (by linarith)
        rw [hne]
        exact tendsto_nhds_unique him_t (tendsto_const_nhds.congr' hev.symm)
    -- 4. Combine via `amp_decomp ϑ`
    have hX_im : (Xph ϑ ((x : ℂ), (β : ℂ))).im = 0 := by
      unfold Xph
      dsimp only
      have hy_r : ysF (β : ℂ) = -(a : ℂ) := by rw [← hβ_eq, hys_eq]
      rw [hy_r]
      have h1 : ((x : ℂ) * ((x : ℂ) ^ 2 - -(a : ℂ))) = (((x * (x ^ 2 + a) : ℝ)) : ℂ) := by push_cast; ring
      rw [h1, Complex.mul_im, Complex.ofReal_im, hhtil_im, zero_mul, mul_zero, add_zero]
    have hX_odd : Xph ϑ (-(x : ℂ), (β : ℂ)) = -Xph ϑ ((x : ℂ), (β : ℂ)) := by
      unfold Xph; simp
    have hAmp_p : (1 + ((x : ℂ) ^ 2 + (a : ℂ)) * Q (x : ℂ) (a : ℂ)) =
        muf ((x : ℂ) ^ 2, (β : ℂ)) * Complex.exp (Complex.I * Xph ϑ ((x : ℂ), (β : ℂ))) := by
      have hp_mem : ((x : ℂ), (β : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rAmp := by
        rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        exact max_lt (hx_β.trans_le hrβ_Amp) (hβ_abs.trans_le hrβ_Amp)
      have hA := hAmp _ hp_mem
      have hys_r : ysF (β : ℂ) = -(a : ℂ) := by rw [← hβ_eq, hys_eq]
      dsimp only at hA
      rw [hys_r, sub_neg_eq_add] at hA
      dsimp [Q]; rw [hβ_eq]; exact hA.symm
    have hAmp_m : (1 + ((-(x : ℂ)) ^ 2 + (a : ℂ)) * Q (-(x : ℂ)) (a : ℂ)) =
        muf ((x : ℂ) ^ 2, (β : ℂ)) * Complex.exp (Complex.I * (-Xph ϑ ((x : ℂ), (β : ℂ)))) := by
      have hp_mem : (-(x : ℂ), (β : ℂ)) ∈ ball ((0 : ℂ), (0 : ℂ)) rAmp := by
        rw [mem_ball, Prod.dist_eq, dist_zero_right, dist_zero_right, norm_neg, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
        exact max_lt (hx_β.trans_le hrβ_Amp) (hβ_abs.trans_le hrβ_Amp)
      have hA := hAmp _ hp_mem
      have hys_r : ysF (β : ℂ) = -(a : ℂ) := by rw [← hβ_eq, hys_eq]
      dsimp only at hA
      rw [hys_r, sub_neg_eq_add, neg_sq, hX_odd] at hA
      dsimp [Q]; rw [hβ_eq, neg_sq]; exact hA.symm
    have hBr_sym : (1 + ((-(x : ℂ)) ^ 2 + (a : ℂ)) * Q (-(x : ℂ)) (a : ℂ)) =
        starRingEnd ℂ (1 + ((x : ℂ) ^ 2 + (a : ℂ)) * Q (x : ℂ) (a : ℂ)) := by
      rw [hAmp_m, hAmp_p, map_mul, Complex.conj_eq_iff_im.2 hmuf_im, ← Complex.exp_conj, map_mul, Complex.conj_I,
        Complex.conj_eq_iff_im.2 hX_im]
      congr 2; ring
    rw [hBr_sym, hEfun_sym, map_mul]
  -- Apply `mkHalfCubicOfCauchy`
  let ψ_hc : ℝ → ℂ → ℂ := fun _ a => Ψ_a a
  have hra_rψ : r_a ≤ r_ψ := by
    have h1 : r_a ≤ r_ψ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith only [h1, hr_ψ]
  obtain ⟨d, hd_ra, hd_s1, hd_rq, hd_ψ, hd_B, hd_E, hd_O⟩ := mkHalfCubicOfCauchy
    hr_s hr_a hM_Q hM_ψ (by norm_num : (0 : ℝ) ≤ 2) Q Eb ψ_hc
    hQ_s hQ_a hQ_bd hEb_s hEb_a hEb_bd
    (fun _ _ => hΨ_diff.mono (ball_subset_ball hra_rψ))
    (fun _ a _ ha => hΨ_bd a ha)
    (fun _ a _ ha => by
      have haψ : |a| < r_ψ := lt_of_lt_of_le ha hra_rψ
      dsimp [ψ_hc]; rw [hΨ_real a haψ, Complex.ofReal_im])
    hsym
  have h3s1 : 3 * d.s₁ < r_s := by rw [hd_s1]; linarith
  have hrq_lt_half : d.r_q < (r_s / 2) ^ 2 := by
    rw [hd_rq]
    exact half_lt_self (pow_pos (half_pos hr_s) 2)
  have hrq_lt_3s1 : d.r_q < (3 * d.s₁) ^ 2 := by
    rw [hd_rq, hd_s1]
    have h1 : (r_s / 2) ^ 2 / 2 = r_s ^ 2 / 8 := by ring
    have h2 : (3 * (r_s / 4)) ^ 2 = 9 * r_s ^ 2 / 16 := by ring
    rw [h1, h2]
    linarith only [pow_pos hr_s 2]
  have hds1_KT : d.s₁ ≤ 1 / (8 * K_T + 8) := by
    rw [hd_s1]
    have h4 : 0 ≤ 1 / (3 * K_T + 3) := by positivity
    calc r_s / 4 ≤ (1 / (3 * K_T + 3)) / 4 := div_le_div_of_nonneg_right hrs_KT (by norm_num)
      _ = 1 / (12 * K_T + 12) := by field_simp; ring
      _ ≤ 1 / (8 * K_T + 8) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        linarith
  have hd_ra_le : d.r_a ≤ r_a := by rw [hd_ra]; exact min_le_left _ _
  refine ⟨d, ϑ, th, zA_C, r_s, r_a, ρ_reg, M_Q, 2, K_T, r_T,
    hr_s, hr_a, hρ_reg, hM_Q, by norm_num, hK_T, hr_T, hrs_ρ, hrs_rT, hd_ra_le, hds1_KT, h3s1,
    hrq_lt_half, hrq_lt_3s1, hTf_lip, hthA, hth, hreg,
    hzA_diff_a, fun a ha => ⟨hzA_in_ρ a ha, hzA_in_rT a ha⟩,
    hReal_link, hQ_bd, hQ_s, hEb_bd_2, ?_, ?_, ?_, ?_⟩
  · intro n a hn ha
    have h2 : max n 2 = n := max_eq_left hn
    have hn1 : 1 ≤ n := by linarith
    simpa [Eb, h2] using hEb_s n a hn1 ha
  · intro n a s hn ha hs
    have h2 : max n 2 = n := max_eq_left hn
    have hn1 : 1 ≤ n := by linarith
    simpa [Eb, h2] using hd_B n a s hn1 ha hs
  · intro n a hn ha
    have ha_ra : |a| < r_a := lt_of_lt_of_le ha (by rw [hd_ra]; exact min_le_left _ _)
    have ha_ψ : |a| < r_ψ := lt_of_lt_of_le ha_ra hra_rψ
    rw [hd_ψ]
    dsimp [ψ_hc]
    exact hΨ_real a ha_ψ
  · exact ⟨2, (4 / (3 * (r_s / 2))) * 2, by norm_num, by positivity, hd_E, hd_O⟩

end FormalResearch.SignUncertainty

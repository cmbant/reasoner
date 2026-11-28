module

public import FormalResearch.SignUncertainty.HankelBessel
public import FormalResearch.SignUncertainty.HankelThresholds
public import FormalResearch.SignUncertainty.RadialRigidity
public import FormalResearch.SignUncertainty.HbMultilevelDefs
public import FormalResearch.Special.BesselDecay
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-!
# Finite-Constraint Hankel Compactness and Attainment (`lem:finite-hankel-compactness`, `gt:7.9a` (3))

Proves:
* `hankelPhi_decay`: for every real `c > 1/2`, `|φ_c(w)| ≤ C w^{-(c/2 - 1/4)}` for `w ≥ 1`,
  from `bessel_energy_bound` at order `ν = c - 1`.
* `finite_hankel_compactness` (`lem:finite-hankel-compactness`): every sequence of `IsHankelEigenfn c ε`
  with uniformly bounded `hankelMass` has a subsequence converging locally uniformly on `(0, ∞)` to an
  `IsHankelEigenfn c ε g` with `hankelMass c g ≤ M₀`.
* `hankelAttainment_proved : HankelAttainment` (`gt:7.9a` (3)): for every real `c > 1/2`, `ε ∈ {1, -1}`,
  and finite set `sites` of positive points, if the prescribed-site Hankel problem is feasible then it
  attains its infimum at some `IsHankelSiteMinimizer c ε sites T_* g_*`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real ENNReal

namespace FormalResearch.SignUncertainty

open FormalResearch.Special

/-! ### Bessel decay at order `ν = c - 1` for all `c > 1/2` -/

private lemma besselNorm_decay_self {ν : ℝ} (hν : -1 / 2 < ν) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ≥ (1 : ℝ), |besselNorm ν x| * x ^ (ν + 1 / 2) ≤ C := by
  obtain ⟨K, hK⟩ := bessel_energy_bound (ν := ν) hν.le (a := besselJPairA ν) (b := besselJPairB ν)
    (x₀ := 1) one_pos (fun x hx => hasDerivAt_besselJPairA (by linarith) (by linarith))
    (fun x hx => hasDerivAt_besselJPairB (by linarith) (by linarith))
  set x₁ : ℝ := max 1 (2 * ν + 1)
  have hx₁1 : 1 ≤ x₁ := le_max_left _ _
  have hG : 0 < Real.Gamma (ν + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hbig : ∀ x ≥ x₁, (|besselNorm ν x| * x ^ (ν + 1 / 2)) ^ 2 ≤
      4 ^ ν * Real.Gamma (ν + 1) ^ 2 * K := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have h1 := hK x hx
    have ha2 : besselJPairA ν x ^ 2 * x ≤ K := by
      have : 0 ≤ besselJPairB ν x ^ 2 := sq_nonneg _
      nlinarith
    have e1 : (|besselNorm ν x| * x ^ (ν + 1 / 2)) ^ 2 =
        besselNorm ν x ^ 2 * x ^ (2 * ν + 1) := by
      rw [mul_pow, sq_abs, ← Real.rpow_natCast (x ^ (ν + 1 / 2)) 2, ← Real.rpow_mul hx0.le]
      congr 2; push_cast; ring
    have e2 : besselJPairA ν x ^ 2 = (x / 2) ^ (2 * ν) * besselNorm ν x ^ 2 /
        Real.Gamma (ν + 1) ^ 2 := by
      unfold besselJPairA
      rw [div_pow, mul_pow, ← Real.rpow_natCast ((x / 2) ^ ν) 2, ← Real.rpow_mul (by positivity)]
      congr 3; push_cast; ring
    have e3 : (x / 2) ^ (2 * ν) = x ^ (2 * ν) / 4 ^ ν := by
      rw [Real.div_rpow hx0.le (by norm_num), show (2 : ℝ) ^ (2 * ν) = 4 ^ ν by
        rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]]
    have e4 : x ^ (2 * ν + 1) = x ^ (2 * ν) * x := Real.rpow_add_one hx0.ne' _
    have h4 : (0 : ℝ) < 4 ^ ν := Real.rpow_pos_of_pos (by norm_num) _
    rw [e1, e4]
    rw [e2, e3] at ha2
    have hA : (x ^ (2 * ν) * besselNorm ν x ^ 2 * x) /
        (4 ^ ν * Real.Gamma (ν + 1) ^ 2) ≤ K := by
      refine le_trans (le_of_eq ?_) ha2
      field_simp
    rw [div_le_iff₀ (by positivity)] at hA
    linarith [hA]
  refine ⟨max 1 (max (Real.sqrt (4 ^ ν * Real.Gamma (ν + 1) ^ 2 * K)) (x₁ ^ (ν + 1 / 2))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx => ?_⟩
  rcases le_or_gt x₁ x with hxx | hxx
  · exact le_trans (Real.le_sqrt_of_sq_le (hbig x hxx))
      ((le_max_left _ _).trans (le_max_right _ _))
  · have hx0 : 0 < x := by linarith
    have hy := abs_besselNorm_le_one hν x
    calc |besselNorm ν x| * x ^ (ν + 1 / 2) ≤ 1 * x ^ (ν + 1 / 2) :=
          mul_le_mul_of_nonneg_right hy (Real.rpow_nonneg hx0.le _)
      _ = x ^ (ν + 1 / 2) := one_mul _
      _ ≤ x₁ ^ (ν + 1 / 2) := Real.rpow_le_rpow hx0.le hxx.le (by linarith)
      _ ≤ _ := (le_max_right _ _).trans (le_max_right _ _)

/-- **Hankel kernel decay** for every real `c > 1/2`: `|φ_c(w)| ≤ C w^{-(c/2 - 1/4)}` for `w ≥ 1`. -/
theorem hankelPhi_decay {c : ℝ} (hc : 1 / 2 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : ℝ, 1 ≤ w → |hankelPhi c w| ≤ C * w ^ (-(c / 2 - 1 / 4)) := by
  obtain ⟨C, hCpos, hC⟩ := besselNorm_decay_self (ν := c - 1) (by linarith)
  have hpi : 1 ≤ 4 * π := by linarith [Real.pi_gt_three]
  have h4pi_pos : 0 < (4 * π) ^ (c - 1 / 2) := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨C / (4 * π) ^ (c - 1 / 2), div_pos hCpos h4pi_pos, fun w hw => ?_⟩
  have hw0 : 0 < w := by linarith
  have hsq : 1 ≤ √w := Real.one_le_sqrt.mpr hw
  set x : ℝ := 4 * π * √w
  have hx1 : 1 ≤ x := by
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (4 * π) * √w := mul_le_mul hpi hsq zero_le_one (by positivity)
  have hbx := hC x hx1
  have hpow : x ^ (c - 1 / 2) = (4 * π) ^ (c - 1 / 2) * w ^ (c / 2 - 1 / 4) := by
    dsimp [x]
    rw [Real.mul_rpow (by positivity) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
      ← Real.rpow_mul hw0.le]
    congr 2; ring
  have e1 : c - 1 + 1 / 2 = c - 1 / 2 := by ring
  rw [e1, hpow] at hbx
  unfold hankelPhi
  calc |besselNorm (c - 1) (4 * π * √w)|
      = (|besselNorm (c - 1) (4 * π * √w)| * ((4 * π) ^ (c - 1 / 2) * w ^ (c / 2 - 1 / 4))) /
          ((4 * π) ^ (c - 1 / 2) * w ^ (c / 2 - 1 / 4)) := by field_simp
    _ ≤ C / ((4 * π) ^ (c - 1 / 2) * w ^ (c / 2 - 1 / 4)) :=
        div_le_div_of_nonneg_right hbx (by positivity)
    _ = C / (4 * π) ^ (c - 1 / 2) * w ^ (-(c / 2 - 1 / 4)) := by
        rw [Real.rpow_neg hw0.le]; ring

/-! ### Equicontinuity and Arzelà–Ascoli compactness on `(0, ∞)` (`lem:finite-hankel-compactness`) -/

private lemma hankelRho0_integrableOn_Ioc {c R : ℝ} (hc : 0 < c) (hR : 0 ≤ R) :
    IntegrableOn (hankelRho0 c) (Ioc 0 R) := by
  have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mp
    (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := R) (by linarith : -1 < c - 1))
  exact hint.const_mul ((2 * π) ^ c / Real.Gamma c)

private lemma hankelEigenfn_equicontinuousOn {c ε M₀ a b : ℝ} (hc : 1 / 2 < c)
    (hε : ε = 1 ∨ ε = -1) (hM₀ : 0 ≤ M₀) {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, IsHankelEigenfn c ε (f n)) (hM : ∀ n, hankelMass c (f n) ≤ M₀)
    (ha : 0 < a) (hab : a ≤ b) :
    Equicontinuous (fun n (x : Icc a b) => f n x.1) := by
  have hc0 : 0 < c := by linarith
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  obtain ⟨C, _, hCdec⟩ := hankelPhi_decay hc
  intro x₀
  rw [Metric.equicontinuousAt_iff_pair]
  intro η hη
  let ηu : ℝ := η / (4 * (M₀ + 1))
  have hηu : 0 < ηu := div_pos hη (by positivity)
  have htend : Tendsto (fun w : ℝ => C * w ^ (-(c / 2 - 1 / 4))) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_rpow_neg_atTop (by linarith : 0 < c / 2 - 1 / 4)).const_mul C
  obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp (htend.eventually (gt_mem_nhds hηu))
  let W : ℝ := max 1 W₀
  have hW1 : 1 ≤ W := le_max_left _ _
  have hW_bd : ∀ w : ℝ, W ≤ w → |hankelPhi c w| ≤ ηu := fun w hw =>
    (hCdec w (hW1.trans hw)).trans (hW₀ w ((le_max_right _ _).trans hw)).le
  let R : ℝ := W / a
  have hR_pos : 0 < R := div_pos (by linarith) ha
  have huc := (isCompact_Icc (a := (0 : ℝ)) (b := b * R)).uniformContinuousOn_of_continuous
    (hankelPhi_continuous c).continuousOn
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := Metric.uniformContinuousOn_iff.mp huc ηu hηu
  let δ : ℝ := δ₀ / (R + 1)
  have hδ_pos : 0 < δ := div_pos hδ₀_pos (by linarith)
  refine ⟨Metric.ball x₀ (δ / 2), Metric.ball_mem_nhds x₀ (by positivity), fun y hy z hz n => ?_⟩
  have hdist_yz : |y.1 - z.1| < δ := by
    have hy' : dist y.1 x₀.1 < δ / 2 := by simpa [Metric.mem_ball, Subtype.dist_eq] using hy
    have hz' : dist z.1 x₀.1 < δ / 2 := by simpa [Metric.mem_ball, Subtype.dist_eq] using hz
    rw [← Real.dist_eq]
    calc dist y.1 z.1 ≤ dist y.1 x₀.1 + dist x₀.1 z.1 := dist_triangle _ _ _
      _ = dist y.1 x₀.1 + dist z.1 x₀.1 := by rw [dist_comm x₀.1 z.1]
      _ < δ / 2 + δ / 2 := add_lt_add hy' hz'
      _ = δ := by ring
  have hker_diff : ∀ s : ℝ, 0 < s →
      |hankelKernel c y.1 s - hankelKernel c z.1 s| ≤ 2 * ηu := fun s hs => by
    unfold hankelKernel
    rcases le_or_gt s R with hsR | hsR
    · have hb_nn : 0 ≤ b := le_trans ha.le hab
      have hy_mem : y.1 * s ∈ Icc 0 (b * R) :=
        ⟨mul_nonneg (by linarith [y.2.1]) hs.le, mul_le_mul y.2.2 hsR hs.le hb_nn⟩
      have hz_mem : z.1 * s ∈ Icc 0 (b * R) :=
        ⟨mul_nonneg (by linarith [z.2.1]) hs.le, mul_le_mul z.2.2 hsR hs.le hb_nn⟩
      have hd : dist (y.1 * s) (z.1 * s) < δ₀ := by
        rw [Real.dist_eq, show y.1 * s - z.1 * s = (y.1 - z.1) * s by ring, abs_mul, abs_of_pos hs]
        calc |y.1 - z.1| * s ≤ δ * R := mul_le_mul hdist_yz.le hsR hs.le hδ_pos.le
          _ = δ₀ * (R / (R + 1)) := by dsimp [δ]; ring
          _ < δ₀ * 1 := mul_lt_mul_of_pos_left ((div_lt_one (by linarith)).mpr (by linarith)) hδ₀_pos
          _ = δ₀ := mul_one _
      have hphi := hδ₀ (y.1 * s) hy_mem (z.1 * s) hz_mem hd
      rw [Real.dist_eq] at hphi
      linarith
    · have hyW : W ≤ y.1 * s := by
        calc W = a * R := by dsimp [R]; field_simp [ha.ne']
          _ ≤ y.1 * s := mul_le_mul y.2.1 hsR.le hR_pos.le (by linarith [y.2.1])
      have hzW : W ≤ z.1 * s := by
        calc W = a * R := by dsimp [R]; field_simp [ha.ne']
          _ ≤ z.1 * s := mul_le_mul z.2.1 hsR.le hR_pos.le (by linarith [z.2.1])
      exact (abs_sub _ _).trans ((add_le_add (hW_bd _ hyW) (hW_bd _ hzW)).trans_eq (by ring))
  have hy_nonneg : 0 ≤ y.1 := by linarith [y.2.1]
  have hz_nonneg : 0 ≤ z.1 := by linarith [z.2.1]
  have hT_sub : besselHankelTransform c (f n) y.1 - besselHankelTransform c (f n) z.1 =
      ∫ s in Ioi (0 : ℝ), f n s * hankelRho0 c s * (hankelKernel c y.1 s - hankelKernel c z.1 s) := by
    unfold besselHankelTransform
    rw [← integral_sub (integrableOn_mul_hankelKernel hc (hf n).int y.1)
      (integrableOn_mul_hankelKernel hc (hf n).int z.1)]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    ring
  change dist (f n y.1) (f n z.1) < η
  rw [Real.dist_eq]
  calc |f n y.1 - f n z.1|
      = |ε * (f n y.1 - f n z.1)| := by rw [abs_mul, hεabs, one_mul]
    _ = |besselHankelTransform c (f n) y.1 - besselHankelTransform c (f n) z.1| := by
        rw [mul_sub, ← (hf n).eigen y.1 hy_nonneg, ← (hf n).eigen z.1 hz_nonneg]
    _ = ‖∫ s in Ioi (0 : ℝ), f n s * hankelRho0 c s *
          (hankelKernel c y.1 s - hankelKernel c z.1 s)‖ := by rw [hT_sub, Real.norm_eq_abs]
    _ ≤ ∫ s in Ioi (0 : ℝ), ‖f n s * hankelRho0 c s *
          (hankelKernel c y.1 s - hankelKernel c z.1 s)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi (0 : ℝ), (2 * ηu) * (|f n s| * hankelRho0 c s) := by
        refine setIntegral_mono_on ?_ ((abs_mul_rho0_integrableOn hc0 (hf n).int).const_mul (2 * ηu))
          measurableSet_Ioi fun s (hs : 0 < s) => ?_
        · exact (((integrableOn_mul_hankelKernel hc (hf n).int y.1).sub
            (integrableOn_mul_hankelKernel hc (hf n).int z.1)).congr_fun
              (fun s _ => by dsimp; ring) measurableSet_Ioi).norm
        · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs.le)]
          calc |f n s| * hankelRho0 c s * |hankelKernel c y.1 s - hankelKernel c z.1 s|
              ≤ |f n s| * hankelRho0 c s * (2 * ηu) :=
                mul_le_mul_of_nonneg_left (hker_diff s hs)
                  (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hs.le))
            _ = (2 * ηu) * (|f n s| * hankelRho0 c s) := by ring
    _ = (2 * ηu) * hankelMass c (f n) := by
        rw [integral_const_mul]; rfl
    _ ≤ (2 * ηu) * M₀ := mul_le_mul_of_nonneg_left (hM n) (by positivity)
    _ = (M₀ / (2 * (M₀ + 1))) * η := by dsimp [ηu]; field_simp; ring
    _ < 1 * η := mul_lt_mul_of_pos_right (by
        rw [div_lt_one (by positivity)]; linarith) hη
    _ = η := one_mul _

private lemma hankelEigenfn_arzela_ascoli_single {c ε M₀ a b : ℝ} (hc : 1 / 2 < c)
    (hε : ε = 1 ∨ ε = -1) (hM₀ : 0 ≤ M₀) {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, IsHankelEigenfn c ε (f n)) (hM : ∀ n, hankelMass c (f n) ≤ M₀)
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ (ψ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono ψ ∧
      TendstoUniformlyOn (fun k => f (ψ k)) g atTop (Icc a b) := by
  classical
  let X := Icc a b
  have : CompactSpace X := isCompact_iff_compactSpace.mp isCompact_Icc
  let bcf : ℕ → BoundedContinuousFunction X ℝ := fun n =>
    BoundedContinuousFunction.mkOfCompact
      ⟨fun x => f n x.1,
        ((hf n).cont.comp_continuous continuous_subtype_val (fun x : X => le_trans ha.le x.2.1))⟩
  have hin_s : ∀ (g : BoundedContinuousFunction X ℝ) (x : X),
      g ∈ Set.range bcf → g x ∈ Metric.closedBall (0 : ℝ) M₀ := by
    rintro g x ⟨n, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
    dsimp [bcf]
    have hx_nn : 0 ≤ x.1 := le_trans ha.le x.2.1
    have h1 := (hf n).eigen x.1 hx_nn
    have h2 : |ε * f n x.1| = |f n x.1| := by rcases hε with rfl | rfl <;> simp
    rw [← h2, ← h1]
    exact (abs_besselHankelTransform_le hc (hf n).int x.1).trans (hM n)
  have heq : Equicontinuous (fun g : Set.range bcf => (g.1 : X → ℝ)) := by
    have he := hankelEigenfn_equicontinuousOn hc hε hM₀ hf hM ha hab
    intro x₀
    rw [Metric.equicontinuousAt_iff_pair]
    intro η hη
    obtain ⟨U, hU, hpair⟩ := Metric.equicontinuousAt_iff_pair.mp (he x₀) η hη
    refine ⟨U, hU, fun y hy z hz ⟨g, hg⟩ => ?_⟩
    obtain ⟨n, rfl⟩ := hg
    exact hpair y hy z hz n
  have hcomp : IsCompact (closure (Set.range bcf)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) M₀)
      (isCompact_closedBall 0 M₀) (Set.range bcf) hin_s heq
  obtain ⟨g₀, -, ψ, hψ_mono, hψ_tend⟩ := hcomp.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  let g : ℝ → ℝ := fun x => if hx : x ∈ X then g₀ ⟨x, hx⟩ else 0
  refine ⟨ψ, g, hψ_mono, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  rw [Metric.tendsto_atTop] at hψ_tend
  obtain ⟨K, hK⟩ := hψ_tend η hη
  filter_upwards [Filter.eventually_ge_atTop K] with k hk x hx
  have hg_eq : g x = g₀ ⟨x, hx⟩ := by dsimp only [g]; split_ifs with h; rfl; exact absurd hx h
  have hbcf_eq : bcf (ψ k) ⟨x, hx⟩ = f (ψ k) x := rfl
  calc dist (g x) (f (ψ k) x)
      = dist (bcf (ψ k) ⟨x, hx⟩) (g₀ ⟨x, hx⟩) := by rw [hg_eq, hbcf_eq, dist_comm]
    _ ≤ dist (bcf (ψ k)) g₀ := BoundedContinuousFunction.dist_coe_le_dist (x := (⟨x, hx⟩ : X))
    _ < η := hK k hk

private lemma hankelEigenfn_arzela_ascoli_diagonal {c ε M₀ : ℝ} (hc : 1 / 2 < c)
    (hε : ε = 1 ∨ ε = -1) (hM₀ : 0 ≤ M₀) {f : ℕ → ℝ → ℝ}
    (hf : ∀ n, IsHankelEigenfn c ε (f n)) (hM : ∀ n, hankelMass c (f n) ≤ M₀) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧
      ∀ m : ℕ, TendstoUniformlyOn (fun k => f (φ k)) g atTop
        (Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)) := by
  classical
  let K : ℕ → Set ℝ := fun m => Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)
  have hK_mono : ∀ m : ℕ, K m ⊆ K (m + 1) := fun m x hx => by
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hle1 : (m : ℝ) + 1 ≤ ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
    refine ⟨le_trans ?_ hx.1, hx.2.trans hle1⟩
    exact div_le_div_of_nonneg_left zero_le_one hm1 hle1
  let PSub (m : ℕ) (ψ : ℕ → ℕ) : Prop :=
    StrictMono ψ ∧ ∃ g : ℝ → ℝ, TendstoUniformlyOn (fun k => f (ψ k)) g atTop (K m)
  let step : ∀ (m : ℕ) (p : { ψ : ℕ → ℕ // PSub m ψ }),
      { ψ' : ℕ → ℕ // PSub (m + 1) ψ' ∧ ∃ α : ℕ → ℕ, StrictMono α ∧ ψ' = p.1 ∘ α } :=
    fun m p => by
      obtain ⟨ψ, hψ_mono, _⟩ := p
      have ha : (0 : ℝ) < 1 / (((m + 1 : ℕ) : ℝ) + 1) := by positivity
      have hab : (1 : ℝ) / (((m + 1 : ℕ) : ℝ) + 1) ≤ ((m + 1 : ℕ) : ℝ) + 1 := by
        have h1 : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith
        exact le_trans (div_le_one (by positivity) |>.mpr h1) h1
      have hex := hankelEigenfn_arzela_ascoli_single hc hε hM₀ (fun n => hf (ψ n))
        (fun n => hM (ψ n)) ha hab
      exact ⟨ψ ∘ Classical.choose hex,
        ⟨hψ_mono.comp (Classical.choose_spec (Classical.choose_spec hex)).1,
          Classical.choose (Classical.choose_spec hex),
          (Classical.choose_spec (Classical.choose_spec hex)).2⟩,
        Classical.choose hex, (Classical.choose_spec (Classical.choose_spec hex)).1, rfl⟩
  let ψ0_ex := hankelEigenfn_arzela_ascoli_single hc hε hM₀ hf hM (a := 1) (b := 1) zero_lt_one le_rfl
  let base : { ψ : ℕ → ℕ // PSub 0 ψ } :=
    ⟨Classical.choose ψ0_ex,
      (Classical.choose_spec (Classical.choose_spec ψ0_ex)).1,
      Classical.choose (Classical.choose_spec ψ0_ex), by
        simpa [K] using (Classical.choose_spec (Classical.choose_spec ψ0_ex)).2⟩
  let chain : ∀ m : ℕ, { ψ : ℕ → ℕ // PSub m ψ } :=
    Nat.rec base (fun m prev => ⟨(step m prev).1, (step m prev).2.1⟩)
  let φ : ℕ → ℕ := fun k => (chain k).1 k
  have hstep_sub : ∀ (m : ℕ), ∃ α : ℕ → ℕ, StrictMono α ∧ (chain (m + 1)).1 = (chain m).1 ∘ α :=
    fun m => by
      obtain ⟨α, hα, heq⟩ := (step m (chain m)).2.2
      exact ⟨α, hα, by change (step m (chain m)).1 = _; exact heq⟩
  have hchain_trans : ∀ (m k : ℕ), m ≤ k → ∃ α : ℕ → ℕ, StrictMono α ∧ (chain k).1 = (chain m).1 ∘ α := by
    intro m k hmk
    induction k with
    | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp hmk
      exact ⟨id, strictMono_id, rfl⟩
    | succ k ih =>
      rcases Nat.eq_or_lt_of_le hmk with rfl | hlt
      · exact ⟨id, strictMono_id, rfl⟩
      · obtain ⟨α₁, hα₁, h1⟩ := ih (Nat.lt_succ_iff.mp hlt)
        obtain ⟨α₂, hα₂, h2⟩ := hstep_sub k
        refine ⟨α₁ ∘ α₂, hα₁.comp hα₂, ?_⟩
        rw [h2, h1]; rfl
  have hφ_mono : StrictMono φ := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    obtain ⟨α, hα, hcomp⟩ := hstep_sub k
    have hlt1 : (chain k).1 k < (chain k).1 (α (k + 1)) :=
      (chain k).2.1 (lt_of_le_of_lt (hα.id_le k) (hα (Nat.lt_succ_self k)))
    simpa [φ, hcomp, Function.comp_apply] using hlt1
  let g_m : ∀ m : ℕ, ℝ → ℝ := fun m => Classical.choose (chain m).2.2
  have hg_tend : ∀ m : ℕ, TendstoUniformlyOn (fun k => f ((chain m).1 k)) (g_m m) atTop (K m) :=
    fun m => Classical.choose_spec (chain m).2.2
  have hg_agree : ∀ m₁ m₂ : ℕ, m₁ ≤ m₂ → ∀ x ∈ K m₁, g_m m₁ x = g_m m₂ x := by
    intro m₁ m₂ hm x hx
    obtain ⟨α, hα, hcomp⟩ := hchain_trans m₁ m₂ hm
    have hx₂ : x ∈ K m₂ := by
      clear α hα hcomp
      induction hm with
      | refl => exact hx
      | step _ ih => exact hK_mono _ ih
    have h1 : Tendsto (fun k => f ((chain m₁).1 (α k)) x) atTop (𝓝 (g_m m₁ x)) :=
      ((hg_tend m₁).tendsto_at hx).comp hα.tendsto_atTop
    have h2 : Tendsto (fun k => f ((chain m₂).1 k) x) atTop (𝓝 (g_m m₂ x)) :=
      (hg_tend m₂).tendsto_at hx₂
    rw [hcomp] at h2
    exact tendsto_nhds_unique h1 h2
  have hKm_ex : ∀ x : ℝ, 0 < x → ∃ m : ℕ, x ∈ K m := fun x hx => by
    obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / x) x)
    have hx1 : 1 / x < (m : ℝ) := (le_max_left _ _).trans_lt hm
    have hx2 : x < (m : ℝ) := (le_max_right _ _).trans_lt hm
    refine ⟨m, ?_, by linarith⟩
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
    have h1x : 1 / x ≤ (m : ℝ) + 1 := by linarith
    calc (1 : ℝ) = x * (1 / x) := by field_simp [hx.ne']
      _ ≤ x * ((m : ℝ) + 1) := mul_le_mul_of_nonneg_left h1x hx.le
  let G : ℝ → ℝ := fun x => if hx : 0 < x then g_m (Nat.find (hKm_ex x hx)) x else 0
  have hG_eq : ∀ m : ℕ, ∀ x ∈ K m, G x = g_m m x := fun m x hx => by
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    dsimp only [G]
    split_ifs
    set m₀ := Nat.find (hKm_ex x hx0)
    have hm₀ : x ∈ K m₀ := Nat.find_spec (hKm_ex x hx0)
    exact (hg_agree m₀ (max m₀ m) (le_max_left _ _) x hm₀).trans
      (hg_agree m (max m₀ m) (le_max_right _ _) x hx).symm
  refine ⟨φ, G, hφ_mono, fun m => ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp (hg_tend m) η hη)
  filter_upwards [Filter.eventually_ge_atTop (max m N)] with k hk x hx
  obtain ⟨α, hα, hcomp⟩ := hchain_trans m k ((le_max_left _ _).trans hk)
  have hNk : N ≤ α k := ((le_max_right _ _).trans hk).trans (hα.id_le k)
  rw [hG_eq m x hx]
  have hf_eq : f (φ k) x = f ((chain m).1 (α k)) x := by dsimp [φ]; rw [hcomp]; rfl
  rw [hf_eq]
  exact hN (α k) hNk x hx

/-- **`lem:finite-hankel-compactness`**: any sequence of `IsHankelEigenfn c ε` (`c > 1/2`, `ε = ±1`)
with `hankelMass c (f n) ≤ M₀` has a subsequence converging locally uniformly on `(0, ∞)` to an
`IsHankelEigenfn c ε g` with `hankelMass c g ≤ M₀`. -/
theorem finite_hankel_compactness {c ε M₀ : ℝ} (hc : 1 / 2 < c) (hε : ε = 1 ∨ ε = -1)
    (hM₀ : 0 ≤ M₀) {f : ℕ → ℝ → ℝ} (hf : ∀ n, IsHankelEigenfn c ε (f n))
    (hM : ∀ n, hankelMass c (f n) ≤ M₀) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ IsHankelEigenfn c ε g ∧ hankelMass c g ≤ M₀ ∧
      ∀ a b : ℝ, 0 < a → a ≤ b → TendstoUniformlyOn (fun k => f (φ k)) g atTop (Icc a b) := by
  have hc0 : 0 < c := by linarith
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  obtain ⟨φ, g₀, hφ_mono, hg₀_diag⟩ := hankelEigenfn_arzela_ascoli_diagonal hc hε hM₀ hf hM
  have hg₀_unif : ∀ a b : ℝ, 0 < a → a ≤ b →
      TendstoUniformlyOn (fun k => f (φ k)) g₀ atTop (Icc a b) := fun a b ha hab => by
    obtain ⟨m, hm⟩ := exists_nat_gt (max (1 / a) b)
    have ha1 : 1 / a < (m : ℝ) := (le_max_left _ _).trans_lt hm
    have hb1 : b < (m : ℝ) := (le_max_right _ _).trans_lt hm
    have hsub : Icc a b ⊆ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) := fun x hx => by
      refine ⟨?_, hx.2.trans (by linarith)⟩
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)]
      calc (1 : ℝ) = a * (1 / a) := by field_simp [ha.ne']
        _ ≤ x * ((m : ℝ) + 1) := mul_le_mul hx.1 (by linarith) (by positivity) (ha.le.trans hx.1)
    exact (hg₀_diag m).mono hsub
  have hg₀_pt : ∀ s : ℝ, 0 < s → Tendsto (fun k => f (φ k) s) atTop (𝓝 (g₀ s)) := fun s hs =>
    (hg₀_unif s s hs le_rfl).tendsto_at ⟨le_rfl, le_rfl⟩
  have hg₀_cont : ContinuousOn g₀ (Ioi 0) := fun s (hs : 0 < s) => by
    have hsub : Icc (s / 2) (2 * s) ⊆ Ici (0 : ℝ) := fun x hx => le_trans (by linarith) hx.1
    have hcont_cc : ContinuousOn g₀ (Icc (s / 2) (2 * s)) :=
      (hg₀_unif (s / 2) (2 * s) (by linarith) (by linarith)).continuousOn
        ((Eventually.of_forall fun k => (hf (φ k)).cont.mono hsub).frequently)
    have hnhds : Icc (s / 2) (2 * s) ∈ 𝓝[Ioi 0] s :=
      nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) (by linarith))
    exact (hcont_cc.continuousWithinAt ⟨by linarith, by linarith⟩).mono_of_mem_nhdsWithin hnhds
  -- Integrability and mass bound for `g₀` via Fatou
  have hg₀_aesm : AEStronglyMeasurable (fun s => g₀ s * hankelRho0 c s) (volume.restrict (Ioi 0)) :=
    (hg₀_cont.mul (continuousOn_hankelRho0 c)).aestronglyMeasurable measurableSet_Ioi
  have hFatou : ∫⁻ s in Ioi (0 : ℝ), ‖g₀ s * hankelRho0 c s‖ₑ ∂volume ≤ ENNReal.ofReal M₀ := by
    have hmeas : ∀ k, AEMeasurable (fun s => ‖f (φ k) s * hankelRho0 c s‖ₑ) (volume.restrict (Ioi 0)) :=
      fun k => (((hf (φ k)).cont.mono Ioi_subset_Ici_self).mul (continuousOn_hankelRho0 c)).aestronglyMeasurable
        measurableSet_Ioi |>.eNorm
    have hlim_ae : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
        Filter.liminf (fun k => ‖f (φ k) s * hankelRho0 c s‖ₑ) atTop = ‖g₀ s * hankelRho0 c s‖ₑ :=
      (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) =>
        ((continuous_eNorm.tendsto _).comp ((hg₀_pt s hs).mul_const _)).liminf_eq
    calc ∫⁻ s in Ioi (0 : ℝ), ‖g₀ s * hankelRho0 c s‖ₑ ∂volume
        = ∫⁻ s in Ioi (0 : ℝ),
            Filter.liminf (fun k => ‖f (φ k) s * hankelRho0 c s‖ₑ) atTop ∂volume :=
          (lintegral_congr_ae hlim_ae).symm
      _ ≤ Filter.liminf (fun k => ∫⁻ s in Ioi (0 : ℝ), ‖f (φ k) s * hankelRho0 c s‖ₑ ∂volume) atTop :=
          lintegral_liminf_le' (μ := volume.restrict (Ioi (0 : ℝ))) (u := (atTop : Filter ℕ)) hmeas
      _ ≤ ENNReal.ofReal M₀ := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
          have hint_k := (hf (φ k)).int
          rw [← ofReal_integral_norm_eq_lintegral_eNorm hint_k]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ∫ s in Ioi (0 : ℝ), ‖f (φ k) s * hankelRho0 c s‖ ∂volume
              = hankelMass c (f (φ k)) := by
                refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs.le)]
            _ ≤ M₀ := hM (φ k)
  have hg₀_int : IntegrableOn (fun s => g₀ s * hankelRho0 c s) (Ioi 0) :=
    ⟨hg₀_aesm, hFatou.trans_lt ENNReal.ofReal_lt_top⟩
  have hg₀_mass : hankelMass c g₀ ≤ M₀ := by
    have heq : ∫ s in Ioi (0 : ℝ), ‖g₀ s * hankelRho0 c s‖ ∂volume = hankelMass c g₀ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs.le)]
    rw [← heq]
    have hof : ENNReal.ofReal (∫ s in Ioi (0 : ℝ), ‖g₀ s * hankelRho0 c s‖ ∂volume) ≤ ENNReal.ofReal M₀ := by
      rwa [ofReal_integral_norm_eq_lintegral_eNorm hg₀_int]
    exact (ENNReal.ofReal_le_ofReal_iff hM₀).mp hof
  -- Eigenidentity of `g₀` at every `Δ > 0`
  have hg₀_eigen : ∀ Δ : ℝ, 0 < Δ → besselHankelTransform c g₀ Δ = ε * g₀ Δ := fun Δ hΔ => by
    have htend_H : Tendsto (fun k => besselHankelTransform c (f (φ k)) Δ) atTop
        (𝓝 (besselHankelTransform c g₀ Δ)) := by
      rw [Metric.tendsto_atTop]
      intro η hη
      obtain ⟨C, _, hCdec⟩ := hankelPhi_decay hc
      let ηu : ℝ := η / (8 * (M₀ + 1))
      have hηu : 0 < ηu := div_pos hη (by positivity)
      have hdec : Tendsto (fun w : ℝ => C * w ^ (-(c / 2 - 1 / 4))) atTop (𝓝 0) := by
        simpa [mul_zero] using (tendsto_rpow_neg_atTop (by linarith : 0 < c / 2 - 1 / 4)).const_mul C
      obtain ⟨W₀, hW₀⟩ := Filter.eventually_atTop.mp (hdec.eventually (gt_mem_nhds hηu))
      let W : ℝ := max 1 W₀
      let R : ℝ := max 1 (W / Δ)
      have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
      have htail_ker : ∀ s : ℝ, R < s → |hankelKernel c Δ s| ≤ ηu := fun s hs => by
        have hW1 : 1 ≤ W := le_max_left _ _
        have hsW : W ≤ Δ * s := by
          have : W / Δ ≤ R := le_max_right _ _
          calc W = Δ * (W / Δ) := by field_simp [hΔ.ne']
            _ ≤ Δ * s := mul_le_mul_of_nonneg_left (this.trans hs.le) hΔ.le
        exact (hCdec (Δ * s) (hW1.trans hsW)).trans (hW₀ (Δ * s) ((le_max_right _ _).trans hsW)).le
      have hsplit : ∀ h : ℝ → ℝ, IntegrableOn (fun s => h s * hankelRho0 c s) (Ioi 0) →
          besselHankelTransform c h Δ =
            (∫ s in Ioc 0 R, h s * hankelRho0 c s * hankelKernel c Δ s) +
            (∫ s in Ioi R, h s * hankelRho0 c s * hankelKernel c Δ s) := fun h hh => by
        have hI := integrableOn_mul_hankelKernel hc hh Δ
        unfold besselHankelTransform
        rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hR_pos.le)),
          Ioc_union_Ioi_eq_Ioi hR_pos.le]
      have htail_bd : ∀ h : ℝ → ℝ, IntegrableOn (fun s => h s * hankelRho0 c s) (Ioi 0) →
          hankelMass c h ≤ M₀ →
          |∫ s in Ioi R, h s * hankelRho0 c s * hankelKernel c Δ s| ≤ ηu * M₀ := fun h hh hMh => by
        have hI := (integrableOn_mul_hankelKernel hc hh Δ).mono_set (Ioi_subset_Ioi hR_pos.le)
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans ?_
        have h1 : ∫ s in Ioi R, ‖h s * hankelRho0 c s * hankelKernel c Δ s‖ ≤
            ∫ s in Ioi R, ηu * (|h s| * hankelRho0 c s) := by
          refine setIntegral_mono_on hI.norm
            (((abs_mul_rho0_integrableOn hc0 hh).mono_set (Ioi_subset_Ioi hR_pos.le)).const_mul ηu)
            measurableSet_Ioi fun s (hs : R < s) => ?_
          have hs0 : 0 < s := hR_pos.trans hs
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs0.le)]
          calc |h s| * hankelRho0 c s * |hankelKernel c Δ s|
              ≤ |h s| * hankelRho0 c s * ηu :=
                mul_le_mul_of_nonneg_left (htail_ker s hs)
                  (mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hs0.le))
            _ = ηu * (|h s| * hankelRho0 c s) := by ring
        have h2 : ∫ s in Ioi R, |h s| * hankelRho0 c s ≤ hankelMass c h := by
          refine setIntegral_mono_set (abs_mul_rho0_integrableOn hc0 hh)
            ((ae_restrict_mem measurableSet_Ioi).mono fun s (hs : 0 < s) =>
              mul_nonneg (abs_nonneg _) (hankelRho0_nonneg hc0 hs.le))
            (Eventually.of_forall (Ioi_subset_Ioi hR_pos.le))
        calc _ ≤ ∫ s in Ioi R, ηu * (|h s| * hankelRho0 c s) := h1
          _ = ηu * ∫ s in Ioi R, |h s| * hankelRho0 c s := integral_const_mul _ _
          _ ≤ ηu * hankelMass c h := mul_le_mul_of_nonneg_left h2 hηu.le
          _ ≤ ηu * M₀ := mul_le_mul_of_nonneg_left hMh hηu.le
      have hcore_tend : Tendsto
          (fun k => ∫ s in Ioc 0 R, f (φ k) s * hankelRho0 c s * hankelKernel c Δ s) atTop
          (𝓝 (∫ s in Ioc 0 R, g₀ s * hankelRho0 c s * hankelKernel c Δ s)) := by
        refine tendsto_integral_of_dominated_convergence (bound := fun s => M₀ * hankelRho0 c s)
          (fun k => ((integrableOn_mul_hankelKernel hc (hf (φ k)).int Δ).mono_set
            Ioc_subset_Ioi_self).aestronglyMeasurable)
          ((hankelRho0_integrableOn_Ioc hc0 hR_pos.le).const_mul M₀) (fun k => ?_) ?_
        · refine (ae_restrict_mem measurableSet_Ioc).mono fun s ⟨hs0, _⟩ => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs0.le)]
          have hf_bd : |f (φ k) s| ≤ M₀ := by
            have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
            calc |f (φ k) s| = |ε * f (φ k) s| := by rw [abs_mul, hεabs, one_mul]
              _ = |besselHankelTransform c (f (φ k)) s| := by rw [(hf (φ k)).eigen s hs0.le]
              _ ≤ hankelMass c (f (φ k)) := abs_besselHankelTransform_le hc (hf (φ k)).int s
              _ ≤ M₀ := hM (φ k)
          calc |f (φ k) s| * hankelRho0 c s * |hankelKernel c Δ s|
              ≤ (M₀ * hankelRho0 c s) * 1 :=
                mul_le_mul (mul_le_mul_of_nonneg_right hf_bd (hankelRho0_nonneg hc0 hs0.le))
                  (abs_hankelKernel_le_one hc _ _) (abs_nonneg _)
                  (mul_nonneg hM₀ (hankelRho0_nonneg hc0 hs0.le))
            _ = M₀ * hankelRho0 c s := mul_one _
        · refine (ae_restrict_mem measurableSet_Ioc).mono fun s ⟨hs0, _⟩ => ?_
          exact ((hg₀_pt s hs0).mul_const _).mul_const _
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hcore_tend (η / 2) (by linarith)
      refine ⟨N, fun k hk => ?_⟩
      rw [hsplit (f (φ k)) (hf (φ k)).int, hsplit g₀ hg₀_int, Real.dist_eq]
      have hcore_d : |(∫ s in Ioc 0 R, f (φ k) s * hankelRho0 c s * hankelKernel c Δ s) -
          (∫ s in Ioc 0 R, g₀ s * hankelRho0 c s * hankelKernel c Δ s)| < η / 2 := by
        have h := hN k hk; rwa [Real.dist_eq] at h
      have h1 := htail_bd (f (φ k)) (hf (φ k)).int (hM (φ k))
      have h2 := htail_bd g₀ hg₀_int hg₀_mass
      have hηM : ηu * M₀ ≤ η / 8 := by
        dsimp [ηu]
        calc η / (8 * (M₀ + 1)) * M₀ = (η / 8) * (M₀ / (M₀ + 1)) := by field_simp
          _ ≤ (η / 8) * 1 := mul_le_mul_of_nonneg_left ((div_le_one (by positivity)).mpr (by linarith))
              (by positivity)
          _ = η / 8 := mul_one _
      have hsplit_sub : ∀ a₁ b₁ a₂ b₂ : ℝ, |(a₁ + b₁) - (a₂ + b₂)| ≤ |a₁ - a₂| + (|b₁| + |b₂|) :=
        fun a₁ b₁ a₂ b₂ => by
          rw [show (a₁ + b₁) - (a₂ + b₂) = (a₁ - a₂) + (b₁ - b₂) by ring]
          exact (abs_add_le (a₁ - a₂) (b₁ - b₂)).trans (add_le_add le_rfl (abs_sub b₁ b₂))
      have htri := hsplit_sub (∫ s in Ioc 0 R, f (φ k) s * hankelRho0 c s * hankelKernel c Δ s)
        (∫ s in Ioi R, f (φ k) s * hankelRho0 c s * hankelKernel c Δ s)
        (∫ s in Ioc 0 R, g₀ s * hankelRho0 c s * hankelKernel c Δ s)
        (∫ s in Ioi R, g₀ s * hankelRho0 c s * hankelKernel c Δ s)
      linarith
    have htend_rhs : Tendsto (fun k => ε * f (φ k) Δ) atTop (𝓝 (ε * g₀ Δ)) :=
      (hg₀_pt Δ hΔ).const_mul ε
    have h_eq : (fun k => besselHankelTransform c (f (φ k)) Δ) = fun k => ε * f (φ k) Δ := by
      ext k; exact (hf (φ k)).eigen Δ hΔ.le
    rw [h_eq] at htend_H
    exact tendsto_nhds_unique htend_H htend_rhs
  -- Extend continuously to `0` by setting `g Δ := ε * besselHankelTransform c g₀ Δ`
  let g : ℝ → ℝ := fun Δ => ε * besselHankelTransform c g₀ Δ
  have hg_eq_pos : ∀ s : ℝ, 0 < s → g s = g₀ s := fun s hs => by
    dsimp [g]; rw [hg₀_eigen s hs, ← mul_assoc, hε2, one_mul]
  have hg_int : IntegrableOn (fun s => g s * hankelRho0 c s) (Ioi 0) :=
    hg₀_int.congr_fun (fun s (hs : 0 < s) => by rw [hg_eq_pos s hs]) measurableSet_Ioi
  have hg_mass : hankelMass c g ≤ M₀ := by
    have hm : hankelMass c g = hankelMass c g₀ := by
      refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
      rw [hg_eq_pos s hs]
    rwa [hm]
  have hg_eig : IsHankelEigenfn c ε g :=
    { cont := ((besselHankelTransform_continuous hc hg₀_int).const_mul ε).continuousOn
      int := hg_int
      eigen := fun Δ _ => by
        have htr : besselHankelTransform c g Δ = besselHankelTransform c g₀ Δ := by
          refine setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
          rw [hg_eq_pos s hs]
        rw [htr]; dsimp [g]; rw [← mul_assoc, hε2, one_mul] }
  refine ⟨φ, g, hφ_mono, hg_eig, hg_mass, fun a b ha hab => ?_⟩
  refine (hg₀_unif a b ha hab).congr_right fun x hx => ?_
  exact (hg_eq_pos x (ha.trans_le hx.1)).symm

/-! ### Infimum attainment (`gt:7.9a` (3)) -/

private lemma hankel_feasible_pos {c ε T : ℝ} (hc : 1 / 2 < c) (hε : ε = 1 ∨ ε = -1)
    {f : ℝ → ℝ} (hf : IsHankelFeasible c ε T f) : 0 < T := by
  have hc0 : 0 < c := by linarith
  by_contra hT
  push Not at hT
  have hnonneg : ∀ s : ℝ, 0 < s → 0 ≤ f s := fun s hs => hf.tail_nonneg s (by linarith)
  have hint0 : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s ≤ 0 := by
    have h0 := hf.eigen 0 self_mem_Ici
    rw [besselHankelTransform_zero hc0] at h0
    linarith [hf.origin_sign]
  have hint_nn : 0 ≤ ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s :=
    setIntegral_nonneg measurableSet_Ioi fun s hs =>
      mul_nonneg (hnonneg s hs) (hankelRho0_nonneg hc0 hs.le)
  have hint_eq : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = 0 := le_antisymm hint0 hint_nn
  have hcont_on : ContinuousOn (fun s => f s * hankelRho0 c s) (Ioi 0) :=
    (hf.cont.mono Ioi_subset_Ici_self).mul (continuousOn_hankelRho0 c)
  have h_ae : (fun s => f s * hankelRho0 c s) =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_mem measurableSet_Ioi).mono fun s hs =>
        mul_nonneg (hnonneg s hs) (hankelRho0_nonneg hc0 hs.le)) hf.int).mp hint_eq
  have hf_pos_zero : ∀ s : ℝ, 0 < s → f s = 0 := fun s hs => by
    have hmul0 : f s * hankelRho0 c s = 0 := by
      by_contra hnz
      have hpos : 0 < f s * hankelRho0 c s :=
        lt_of_le_of_ne (mul_nonneg (hnonneg s hs) (hankelRho0_nonneg hc0 hs.le)) (Ne.symm hnz)
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp (hcont_on s hs)
        (f s * hankelRho0 c s / 2) (by linarith)
      let a : ℝ := max (s / 2) (s - δ / 2)
      let b' : ℝ := s + δ / 2
      have ha_pos : 0 < a := lt_max_of_lt_left (by linarith)
      have hab : a < b' := by dsimp [a, b']; exact max_lt (by linarith) (by linarith)
      have hsub : Ioo a b' ⊆ {x : ℝ | f x * hankelRho0 c x ≠ 0} := fun x hx => by
        have hx0 : 0 < x := lt_trans ha_pos hx.1
        dsimp [a, b'] at hx
        have hdist : dist x s < δ := by
          rw [Real.dist_eq, abs_lt]
          constructor <;> [linarith [le_max_right (s / 2) (s - δ / 2), hx.1]; linarith [hx.2]]
        have hb := (abs_lt.mp (by simpa [Real.dist_eq] using hball hx0 hdist)).1
        exact ne_of_gt (by linarith)
      have hsub_pos : Ioo a b' ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans ha_pos hx.1
      have hvol0 : (volume.restrict (Ioi (0 : ℝ))) (Ioo a b') = 0 :=
        measure_mono_null hsub (ae_iff.mp h_ae)
      rw [Measure.restrict_apply measurableSet_Ioo, Set.inter_eq_left.mpr hsub_pos, Real.volume_Ioo,
        ENNReal.ofReal_eq_zero] at hvol0
      linarith
    exact (mul_eq_zero.mp hmul0).resolve_right (hankelRho0_pos hc0 hs).ne'
  have hf_zero : ∀ Δ : ℝ, 0 ≤ Δ → f Δ = 0 := fun Δ hΔ => by
    rcases eq_or_lt_of_le hΔ with rfl | hpos
    · have h0 := hf.eigen 0 self_mem_Ici
      rw [besselHankelTransform_zero hc0] at h0
      have hi0 : ∫ s in Ioi (0 : ℝ), f s * hankelRho0 c s = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero fun s hs => by rw [hf_pos_zero s hs, zero_mul]
      rw [hi0] at h0
      have hεnz : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
      exact (mul_eq_zero.mp h0.symm).resolve_left hεnz
    · exact hf_pos_zero Δ hpos
  obtain ⟨Δ, hΔ, hne⟩ := hf.nonzero
  exact hne (hf_zero Δ hΔ)

/-- **Proposition 7.9a (3)** (`gt:7.9a`, unconditional): for every real `c > 1/2`, sign `ε = ±1`,
and finite set `sites` of positive points, if the prescribed-site Hankel problem is feasible then it
attains its infimum at some `IsHankelSiteMinimizer c ε sites Tstar gstar`. -/
theorem hankelAttainment_proved : HankelAttainment := by
  intro c hc ε hε sites hsites_pos hfeas_ex
  have hc0 : 0 < c := by linarith
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> ring
  have hεabs : |ε| = 1 := by rcases hε with rfl | rfl <;> simp
  let S_T : Set ℝ := {T : ℝ | ∃ f, IsHankelFeasible c ε T f ∧ ∀ s ∈ sites, 0 ≤ f s}
  have hne : S_T.Nonempty := by obtain ⟨T, f, hf, hs⟩ := hfeas_ex; exact ⟨T, f, hf, hs⟩
  have hbdd : BddBelow S_T := ⟨0, fun T ⟨f, hf, _⟩ => (hankel_feasible_pos hc hε hf).le⟩
  let Tstar : ℝ := sInf S_T
  have hT_nonneg : 0 ≤ Tstar := le_csInf hne fun T ⟨f, hf, _⟩ => (hankel_feasible_pos hc hε hf).le
  have hseq_ex : ∀ n : ℕ, ∃ (T : ℝ) (g : ℝ → ℝ),
      IsHankelFeasible c ε T g ∧ (∀ s ∈ sites, 0 ≤ g s) ∧ hankelMass c g = 1 ∧
        T ≤ Tstar + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨T, hTm, hTlt⟩ := Real.lt_sInf_add_pos hne (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))
    obtain ⟨f, hf, hsites⟩ := hTm
    obtain ⟨Δ0, hΔ0, hne0⟩ := hf.nonzero
    have hm : 0 < hankelMass c f :=
      hankelMass_pos_of_continuousOn hc0 hf.cont hf.int ⟨Δ0, hΔ0, hne0⟩
    set m := hankelMass c f
    have hmi : 0 < m⁻¹ := inv_pos.2 hm
    refine ⟨T, fun s => m⁻¹ * f s, ?_, fun s hs => mul_nonneg hmi.le (hsites s hs), ?_, hTlt.le⟩
    · refine ⟨hf.toIsHankelEigenfn.smul m⁻¹, ⟨Δ0, hΔ0, mul_ne_zero hmi.ne' hne0⟩, ?_, ?_⟩
      · have := hf.origin_sign
        show ε * (m⁻¹ * f 0) ≤ 0
        nlinarith [mul_nonneg hmi.le (neg_nonneg.2 this)]
      · intro Δ hΔ
        exact mul_nonneg hmi.le (hf.tail_nonneg Δ hΔ)
    · rw [hankelMass_smul, abs_of_pos hmi, inv_mul_cancel₀ hm.ne']
  choose Tseq gseq hseq using hseq_ex
  have hg_feas : ∀ n, IsHankelFeasible c ε (Tseq n) (gseq n) := fun n => (hseq n).1
  have hg_sites : ∀ n, ∀ s ∈ sites, 0 ≤ gseq n s := fun n => (hseq n).2.1
  have hg_mass : ∀ n, hankelMass c (gseq n) = 1 := fun n => (hseq n).2.2.1
  have hT_le : ∀ n, Tseq n ≤ Tstar + 1 / ((n : ℝ) + 1) := fun n => (hseq n).2.2.2
  obtain ⟨φ, gstar, hφ_mono, hgstar_eig, _, hgstar_unif⟩ := finite_hankel_compactness hc hε zero_le_one
    (fun n => (hg_feas n).toIsHankelEigenfn) (fun n => (hg_mass n).le)
  have hgstar_pt : ∀ s : ℝ, 0 < s → Tendsto (fun k => gseq (φ k) s) atTop (𝓝 (gstar s)) :=
    fun s hs => (hgstar_unif s s hs le_rfl).tendsto_at ⟨le_rfl, le_rfl⟩
  have hsites_lim : ∀ s ∈ sites, 0 ≤ gstar s := fun s hs =>
    ge_of_tendsto (hgstar_pt s (hsites_pos s hs)) (Eventually.of_forall fun k => hg_sites (φ k) s hs)
  have htail_strict : ∀ Δ : ℝ, Tstar < Δ → 0 ≤ gstar Δ := fun Δ hΔ => by
    have hΔ0 : 0 < Δ := lt_of_le_of_lt hT_nonneg hΔ
    have hinv : Tendsto (fun k : ℕ => (1 : ℝ) / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ_mono.tendsto_atTop
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hinv.eventually (Iic_mem_nhds (sub_pos.mpr hΔ)))
    refine ge_of_tendsto (hgstar_pt Δ hΔ0) (Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩)
    have hTk : Tseq (φ k) ≤ Δ := le_trans (hT_le (φ k)) (by linarith [hN k hk])
    exact (hg_feas (φ k)).tail_nonneg Δ hTk
  have htail_lim : ∀ Δ ≥ Tstar, 0 ≤ gstar Δ := fun Δ hΔ => by
    rcases eq_or_lt_of_le hΔ with rfl | hgt
    · have htend_pt : Tendsto (fun n : ℕ => Tstar + 1 / ((n : ℝ) + 1)) atTop (𝓝[Ici (0 : ℝ)] Tstar) :=
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (by simpa using tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
          (Eventually.of_forall fun n => add_nonneg hT_nonneg (by positivity))
      exact ge_of_tendsto ((hgstar_eig.cont Tstar hT_nonneg).tendsto.comp htend_pt)
        (Eventually.of_forall fun n => htail_strict _ (by linarith [(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1))]))
    · exact htail_strict Δ hgt
  -- Split `(0, ∞)` at `R := Tstar + 1`
  let R : ℝ := Tstar + 1
  have hR_pos : 0 < R := by dsimp [R]; linarith
  have hg_tail_nn : ∀ k s, R < s → 0 ≤ gseq (φ k) s := fun k s hs => by
    have hT1 : Tseq (φ k) ≤ R := (hT_le (φ k)).trans (by
      have h1 : (1 : ℝ) / ((φ k : ℝ) + 1) ≤ 1 := div_le_one (by positivity) |>.mpr (by linarith)
      dsimp [R]; linarith)
    exact (hg_feas (φ k)).tail_nonneg s (hT1.trans hs.le)
  have hg_abs_bd : ∀ k s, 0 < s → |gseq (φ k) s| ≤ 1 := fun k s hs => by
    calc |gseq (φ k) s| = |ε * gseq (φ k) s| := by rw [abs_mul, hεabs, one_mul]
      _ = |besselHankelTransform c (gseq (φ k)) s| := by rw [(hg_feas (φ k)).eigen s hs.le]
      _ ≤ hankelMass c (gseq (φ k)) := abs_besselHankelTransform_le hc (hg_feas (φ k)).int s
      _ = 1 := hg_mass (φ k)
  -- `Ioc 0 R` convergence of `∫ g_k ρ₀`
  let A : ℕ → ℝ := fun k => ∫ s in Ioc 0 R, gseq (φ k) s * hankelRho0 c s
  let Astar : ℝ := ∫ s in Ioc 0 R, gstar s * hankelRho0 c s
  have hA_tend : Tendsto A atTop (𝓝 Astar) := by
    refine tendsto_integral_of_dominated_convergence (bound := fun s => hankelRho0 c s)
      (fun k => ((hg_feas (φ k)).int.mono_set Ioc_subset_Ioi_self).aestronglyMeasurable)
      (hankelRho0_integrableOn_Ioc hc0 hR_pos.le) (fun k => ?_) ?_
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun s ⟨hs0, _⟩ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs0.le)]
      exact mul_le_of_le_one_left (hankelRho0_nonneg hc0 hs0.le) (hg_abs_bd k s hs0)
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun s ⟨hs0, _⟩ => ?_
      exact (hgstar_pt s hs0).mul_const _
  -- `origin_sign` via Fatou on `Ioi R` + DCT on `Ioc 0 R`
  let B : ℕ → ℝ := fun k => ∫ s in Ioi R, gseq (φ k) s * hankelRho0 c s
  let Bstar : ℝ := ∫ s in Ioi R, gstar s * hankelRho0 c s
  have hAB_k : ∀ k, A k + B k ≤ 0 := fun k => by
    have hI := (hg_feas (φ k)).int
    have heq : A k + B k = ∫ s in Ioi (0 : ℝ), gseq (φ k) s * hankelRho0 c s := by
      dsimp [A, B]
      rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
        (hI.mono_set Ioc_subset_Ioi_self) (hI.mono_set (Ioi_subset_Ioi hR_pos.le)),
        Ioc_union_Ioi_eq_Ioi hR_pos.le]
    rw [heq, ← besselHankelTransform_zero hc0, (hg_feas (φ k)).eigen 0 self_mem_Ici]
    exact (hg_feas (φ k)).origin_sign
  have hAB_star : Astar + Bstar = ε * gstar 0 := by
    dsimp [Astar, Bstar]
    rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hgstar_eig.int.mono_set Ioc_subset_Ioi_self)
      (hgstar_eig.int.mono_set (Ioi_subset_Ioi hR_pos.le)),
      Ioc_union_Ioi_eq_Ioi hR_pos.le, ← besselHankelTransform_zero hc0,
      hgstar_eig.eigen 0 self_mem_Ici]
  have hBstar_le : Bstar ≤ -Astar := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    have hFatou : ∫⁻ s in Ioi R, ENNReal.ofReal (gstar s * hankelRho0 c s) ∂volume ≤
        liminf (fun k => ∫⁻ s in Ioi R, ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s) ∂volume) atTop := by
      have hmeas : ∀ k, AEMeasurable (fun s => ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s))
          (volume.restrict (Ioi R)) := fun k =>
        ENNReal.continuous_ofReal.measurable.comp_aemeasurable
          (((hg_feas (φ k)).int.mono_set (Ioi_subset_Ioi hR_pos.le)).aestronglyMeasurable.aemeasurable)
      have hlim_ae : ∀ᵐ s ∂(volume.restrict (Ioi R)),
          Filter.liminf (fun k => ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s)) atTop =
            ENNReal.ofReal (gstar s * hankelRho0 c s) :=
        (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : R < s) =>
          ((ENNReal.continuous_ofReal.tendsto _).comp
            ((hgstar_pt s (hR_pos.trans hs)).mul_const _)).liminf_eq
      calc ∫⁻ s in Ioi R, ENNReal.ofReal (gstar s * hankelRho0 c s) ∂volume
          = ∫⁻ s in Ioi R,
              Filter.liminf (fun k => ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s)) atTop ∂volume :=
            (lintegral_congr_ae hlim_ae).symm
        _ ≤ Filter.liminf (fun k =>
              ∫⁻ s in Ioi R, ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s) ∂volume) atTop :=
            lintegral_liminf_le' (μ := volume.restrict (Ioi R)) (u := (atTop : Filter ℕ)) hmeas
    have hlhs : ∫⁻ s in Ioi R, ENNReal.ofReal (gstar s * hankelRho0 c s) ∂volume = ENNReal.ofReal Bstar := by
      refine (ofReal_integral_eq_lintegral_ofReal (hgstar_eig.int.mono_set (Ioi_subset_Ioi hR_pos.le)) ?_).symm
      refine (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : R < s) => ?_
      exact mul_nonneg (htail_lim s (by dsimp [R] at hs; linarith)) (hankelRho0_nonneg hc0 (hR_pos.trans hs).le)
    have hrhs_ev : ∀ᶠ k in atTop,
        ∫⁻ s in Ioi R, ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s) ∂volume ≤
          ENNReal.ofReal (-Astar + δ / 2) := by
      filter_upwards [hA_tend.neg.eventually (gt_mem_nhds (by linarith : -Astar < -Astar + δ / 2))] with k hk
      have heq_k : ∫⁻ s in Ioi R, ENNReal.ofReal (gseq (φ k) s * hankelRho0 c s) ∂volume =
          ENNReal.ofReal (B k) := by
        refine (ofReal_integral_eq_lintegral_ofReal
          ((hg_feas (φ k)).int.mono_set (Ioi_subset_Ioi hR_pos.le)) ?_).symm
        refine (ae_restrict_mem measurableSet_Ioi).mono fun s (hs : R < s) => ?_
        exact mul_nonneg (hg_tail_nn k s hs) (hankelRho0_nonneg hc0 (hR_pos.trans hs).le)
      rw [heq_k]
      exact ENNReal.ofReal_le_ofReal (by linarith [hAB_k k])
    have hlim_le : ENNReal.ofReal Bstar ≤ ENNReal.ofReal (-Astar + δ / 2) := by
      rw [← hlhs]
      exact hFatou.trans (liminf_le_of_frequently_le' hrhs_ev.frequently)
    have hAstar_le : Astar ≤ 0 := le_of_tendsto hA_tend (Eventually.of_forall fun k => by
      have hBk : 0 ≤ B k := setIntegral_nonneg measurableSet_Ioi fun s (hs : R < s) =>
        mul_nonneg (hg_tail_nn k s hs) (hankelRho0_nonneg hc0 (hR_pos.trans hs).le)
      linarith [hAB_k k])
    have h1 : Bstar ≤ -Astar + δ / 2 :=
      (ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ -Astar + δ / 2)).mp hlim_le
    linarith
  have horigin : ε * gstar 0 ≤ 0 := by linarith
  -- Nonvanishing: negative part mass on `Ioc 0 R` is `≥ 1`
  let D : ℕ → ℝ := fun k => ∫ s in Ioc 0 R, (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s
  let Dstar : ℝ := ∫ s in Ioc 0 R, (|gstar s| - gstar s) * hankelRho0 c s
  have hD_ge : ∀ k, 1 ≤ D k := fun k => by
    have hIabs := abs_mul_rho0_integrableOn hc0 (hg_feas (φ k)).int
    have hI := (hg_feas (φ k)).int
    have hIdiff : IntegrableOn (fun s => (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s) (Ioi 0) :=
      (hIabs.sub hI).congr_fun (fun s _ => by dsimp; ring) measurableSet_Ioi
    have hI0 : ∫ s in Ioi R, (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero fun s (hs : R < s) => by
        rw [abs_of_nonneg (hg_tail_nn k s hs), sub_self, zero_mul]
    have hD_full : D k = ∫ s in Ioi (0 : ℝ), (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s := by
      calc D k = D k + 0 := (add_zero _).symm
        _ = D k + ∫ s in Ioi R, (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s := by rw [hI0]
        _ = ∫ s in Ioi (0 : ℝ), (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s := by
            dsimp [D]
            rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
              (hIdiff.mono_set Ioc_subset_Ioi_self) (hIdiff.mono_set (Ioi_subset_Ioi hR_pos.le)),
              Ioc_union_Ioi_eq_Ioi hR_pos.le]
    have hsub : ∫ s in Ioi (0 : ℝ), (|gseq (φ k) s| - gseq (φ k) s) * hankelRho0 c s =
        hankelMass c (gseq (φ k)) - ∫ s in Ioi (0 : ℝ), gseq (φ k) s * hankelRho0 c s := by
      refine (setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_).trans (integral_sub hIabs hI)
      ring
    rw [hD_full, hsub, hg_mass (φ k), ← besselHankelTransform_zero hc0,
      (hg_feas (φ k)).eigen 0 self_mem_Ici]
    linarith [(hg_feas (φ k)).origin_sign]
  have hD_tend : Tendsto D atTop (𝓝 Dstar) := by
    have hIabs_star := abs_mul_rho0_integrableOn hc0 hgstar_eig.int
    refine tendsto_integral_of_dominated_convergence (bound := fun s => 2 * hankelRho0 c s)
      (fun k => (((abs_mul_rho0_integrableOn hc0 (hg_feas (φ k)).int).sub (hg_feas (φ k)).int).congr_fun
        (fun s _ => by dsimp; ring) measurableSet_Ioi |>.mono_set Ioc_subset_Ioi_self).aestronglyMeasurable)
      ((hankelRho0_integrableOn_Ioc hc0 hR_pos.le).const_mul 2) (fun k => ?_) ?_
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun s ⟨hs0, _⟩ => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hankelRho0_nonneg hc0 hs0.le)]
      have hdiff_bd : |(|gseq (φ k) s| - gseq (φ k) s)| ≤ 2 := by
        calc |(|gseq (φ k) s| - gseq (φ k) s)| ≤ |(|gseq (φ k) s|)| + |gseq (φ k) s| := abs_sub _ _
          _ = |gseq (φ k) s| + |gseq (φ k) s| := by rw [abs_abs]
          _ ≤ 1 + 1 := add_le_add (hg_abs_bd k s hs0) (hg_abs_bd k s hs0)
          _ = 2 := by norm_num
      exact mul_le_mul_of_nonneg_right hdiff_bd (hankelRho0_nonneg hc0 hs0.le)
    · refine (ae_restrict_mem measurableSet_Ioc).mono fun s ⟨hs0, _⟩ => ?_
      exact (((hgstar_pt s hs0).abs.sub (hgstar_pt s hs0)).mul_const _)
  have hDstar_ge : 1 ≤ Dstar := ge_of_tendsto hD_tend (Eventually.of_forall hD_ge)
  have hnz : ∃ Δ ∈ Ici (0 : ℝ), gstar Δ ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hD0 : Dstar = 0 := setIntegral_eq_zero_of_forall_eq_zero fun s ⟨hs0, _⟩ => by
      rw [hzero s hs0.le, abs_zero, sub_self, zero_mul]
    linarith
  exact ⟨Tstar, gstar, {
    feasible := { hgstar_eig with nonzero := hnz, origin_sign := horigin, tail_nonneg := htail_lim }
    sites_nonneg := hsites_lim
    least := fun T' f' hf' hs' => csInf_le hbdd ⟨f', hf', hs'⟩ }⟩

/-- info: 'FormalResearch.SignUncertainty.hankelPhi_decay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelPhi_decay

/-- info: 'FormalResearch.SignUncertainty.finite_hankel_compactness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_hankel_compactness

/-- info: 'FormalResearch.SignUncertainty.hankelAttainment_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms hankelAttainment_proved

end FormalResearch.SignUncertainty

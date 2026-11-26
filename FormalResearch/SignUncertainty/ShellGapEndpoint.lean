module

public import FormalResearch.SignUncertainty.ShellGapEndpointAux

/-!
# The `v = t_m` endpoint clause of `thm:ce-shell-gap` (Corollary H.14d)

Source: `CFT/sign_uncertainty/paper/ce_shells.tex`, `thm:ce-shell-gap` and its proof, with the zero-mass clause of
`thm:ce-physical-profile`.

* `endpoint_subseq`: normalise by `M[h_k]` (so that `M[p_k], M[q_k] ≤ 1` by the origin mass identity), extract
  limits `Ψ_p/M[h] → P_∞`, `Ψ_q/M[h] → Q_∞` (`extract_two`), pass the signs and the Laplace constraint to the limit
  `-Φ = P_∞ - Q_∞` of `-Ψ_h/M[h]`, identify `Φ = -b G_N` by the uniqueness `D.uniqueness` (`lem:hb-uniqueness`) at
  the cutoff `t_m`, and apply the equality case of `lem:qual-compact` (`Analysis.qual_compact_real`) to
  `F_j = -Ψ_{h_j}/M[h_j]`, whose limit `b G_N` has `∫ = 0`: this gives `‖b G_N‖₁ = 1` (so `b = 1/‖G_N‖₁`), the
  `L¹` convergence of the physical profile and, since `∫ Ψ_ĥ/M[h] = M[ĥ]/M[h] = -∫F_j → 0`, the vanishing of the
  Fourier profile.
* `shellGapEndpoint_proved : ShellGapEndpoint D`: the uniqueness of the limit upgrades subsequences to the whole
  sequence (`profileConv_of_subseq`); the profile of `f = ĥ - h` and `M[ĥ]/M[f] → 0` follow by subtraction and
  `M[f]/M[h] → ‖G_N/‖G_N‖₁‖₁ = 1`; `ℒ_y(-G_N) ≥ 0` is the already proved `hankelShellGapLimit_proved` at `u_* = t_m`.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Real

namespace FormalResearch.SignUncertainty

open FormalResearch.Analysis (qual_compact_real)

/-- **Subsequential form of the endpoint clause** (`thm:ce-shell-gap`, proof). Under the hypotheses of
`ShellGapEndpoint`, a subsequence of the normalised physical and Fourier profiles converges locally uniformly and in
`L¹` to `-G_N/‖G_N‖₁` and `0`. -/
theorem endpoint_subseq (D : ShellHBData) {r : ℝ → ℕ → ℝ} (hr : ShellOffsetsSmall r)
    {dk : ℕ → ℕ} (hdk : Tendsto dk atTop atTop) (h2 : ∀ k, 2 ≤ dk k)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {G : ℕ → ℝ → ℝ} {T : ℕ → ℝ}
    (hP : ∀ k, HankelShellProfile ((dk k : ℝ) / 2) (T k) (G k))
    (hshell : ∀ k, ∀ t ∈ D.S, t ≠ D.tm → 0 ≤ shellSite t (r t) (dk k) →
      G k (shellSite t (r t) (dk k)) ≤ 0)
    (hT : ∀ k, T k ≤ (dk k : ℝ) / (2 * π ^ 2) - (D.tm / hankelBeta1) * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)
      + ε k * ((dk k : ℝ) / 2) ^ (1 / 3 : ℝ)) :
    ∃ K : ℕ → ℕ, StrictMono K ∧
      ProfileConv (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2) (G (K n)) u /
        hankelMass ((dk (K n) : ℝ) / 2) (G (K n))) (fun u => -D.normG u) ∧
      ProfileConv (fun n u => hankelWindowProfile ((dk (K n) : ℝ) / 2)
        (besselHankelTransform ((dk (K n) : ℝ) / 2) (G (K n))) u /
        hankelMass ((dk (K n) : ℝ) / 2) (G (K n))) (fun _ => 0) := by
  have H := radial_compactness
  have hβ := hankelBeta1_pos
  set c : ℕ → ℝ := fun k => (dk k : ℝ) / 2 with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => by
    have : (2 : ℝ) ≤ dk k := by exact_mod_cast h2 k
    simp only [hcdef]; positivity
  have hc : Tendsto c atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hdk).atTop_div_const (by norm_num)
  set p : ℕ → ℝ → ℝ := fun k => hankelPlus (c k) (G k) with hpdef
  set q : ℕ → ℝ → ℝ := fun k => hankelMinus (c k) (G k) with hqdef
  have hp : ∀ k, IsHankelEigenfn (c k) 1 (p k) := fun k => (hP k).plus (h2 k)
  have hq : ∀ k, IsHankelEigenfn (c k) (-1) (q k) := fun k => (hP k).minus (h2 k)
  set μ : ℕ → ℝ := fun k => hankelMass (c k) (G k) with hμdef
  have hμpos : ∀ k, 0 < μ k := fun k =>
    lt_of_lt_of_le (hP k).origin_pos ((hP k).origin_le_hankelMass (h2 k))
  have hpB : ∀ k, hankelMass (c k) (p k) ≤ 1 * μ k := fun k => by
    rw [one_mul]; exact (hP k).hankelMass_plus_le (h2 k)
  have hqB : ∀ k, hankelMass (c k) (q k) ≤ 1 * μ k := fun k => by
    rw [one_mul]; exact (hP k).hankelMass_minus_le (h2 k)
  have hTc : ∀ k, T k ≤ c k / Real.pi ^ 2 - (D.tm / hankelBeta1) * c k ^ (1 / 3 : ℝ) +
      ε k * c k ^ (1 / 3 : ℝ) := fun k => by
    have := hT k
    rwa [show (dk k : ℝ) / (2 * Real.pi ^ 2) = ((dk k : ℝ) / 2) / Real.pi ^ 2 by rw [div_div]] at this
  have hdom : ∀ k Δ, T k ≤ Δ → |p k Δ| ≤ q k Δ := fun k Δ hΔ => (hP k).abs_plus_le_minus hΔ
  have hhat : ∀ k Δ, 0 ≤ Δ → 0 ≤ p k Δ + q k Δ := fun k Δ hΔ => by
    have := (hP k).nonneg_hat Δ hΔ
    simp only [hpdef, hqdef, hankelPlus, hankelMinus]; linarith
  have hGpq : ∀ k Δ, p k Δ - q k Δ = G k Δ := fun k Δ => by
    simp only [hpdef, hqdef, hankelPlus, hankelMinus]; ring
  have hĜpq : ∀ k Δ, p k Δ + q k Δ = besselHankelTransform (c k) (G k) Δ := fun k Δ => by
    simp only [hpdef, hqdef, hankelPlus, hankelMinus]; ring
  obtain ⟨K, Fp, Fq, hK, hFp, hFq, hlocp, hlocq⟩ := extract_two H hc hp hq hμpos hpB hqB
  have hKt : Tendsto K atTop atTop := hK.tendsto_atTop
  have hc' : Tendsto (fun n => c (K n)) atTop atTop := hc.comp hKt
  have hcpos' : ∀ n, 0 < c (K n) := fun n => hcpos _
  have hμpos' : ∀ n, 0 < μ (K n) := fun n => hμpos _
  have hε' : Tendsto (fun n => ε (K n)) atTop (𝓝 0) := hε.comp hKt
  set Pr : ℝ → ℝ := fun u => (Fp (u : ℂ)).re with hPr
  set Qr : ℝ → ℝ := fun u => (Fq (u : ℂ)).re with hQr
  have hPc : Continuous Pr :=
    Complex.continuous_re.comp (hFp.1.continuous.comp Complex.continuous_ofReal)
  have hQc : Continuous Qr :=
    Complex.continuous_re.comp (hFq.1.continuous.comp Complex.continuous_ofReal)
  have hnonneg : ∀ u, 0 ≤ Pr u + Qr u :=
    limit_nonneg (c := fun n => c (K n)) (μ := fun n => μ (K n)) (p := fun n => p (K n))
      (q := fun n => q (K n)) hcpos' hμpos' (fun n => hhat (K n)) hlocp hlocq
  have hleft : ∀ u ≤ D.tm, Pr u - Qr u ≤ 0 :=
    limit_left (c := fun n => c (K n)) (μ := fun n => μ (K n)) (p := fun n => p (K n))
      (q := fun n => q (K n)) (T := fun n => T (K n)) (ε := fun n => ε (K n)) hcpos' hμpos'
      hε' (fun n => hTc (K n)) (fun n => hdom (K n)) hlocp hlocq hPc hQc
  have hshellP : ∀ t ∈ D.S, t ≠ D.tm → Pr t - Qr t ≤ 0 := by
    intro t ht htm
    obtain ⟨u, hut, huw, hpos⟩ := shell_window_point (t := t) (r := r t) (hr t)
      (dk := fun n => dk (K n)) (hdk.comp hKt) (fun n => h2 _)
    refine limit_sub_nonpos hlocp hlocq hPc hQc hut ?_
    filter_upwards [hpos] with n hn
    have e : hankelWindowProfile (c (K n)) (p (K n)) (u n) / μ (K n) -
        hankelWindowProfile (c (K n)) (q (K n)) (u n) / μ (K n) =
        hankelWindowProfile (c (K n)) (fun Δ => p (K n) Δ - q (K n) Δ) (u n) / μ (K n) := by
      rw [hankelWindowProfile_sub]; ring
    show hankelWindowProfile (c (K n)) (p (K n)) (u n) / μ (K n) -
        hankelWindowProfile (c (K n)) (q (K n)) (u n) / μ (K n) ≤ 0
    rw [e]
    refine div_nonpos_of_nonpos_of_nonneg (hankelWindowProfile_nonpos_of (hcpos' n) ?_) (hμpos' n).le
    intro _
    show p (K n) (winDelta (c (K n)) (u n)) - q (K n) (winDelta (c (K n)) (u n)) ≤ 0
    rw [hGpq, show winDelta (c (K n)) (u n) = shellSite t (r t) (dk (K n)) from huw n]
    exact hshell (K n) t ht htm hn.le
  have hlap : ∀ y : ℝ, 0 ≤ y → 0 ≤ ∫ u, (Pr u - Qr u) * Real.exp (y * u) := by
    intro y hy0
    have hpos : ∀ y : ℝ, 0 < y → 0 ≤ ∫ u, (Pr u - Qr u) * Real.exp (y * u) := fun y hy =>
      limit_laplace (c := fun n => c (K n)) (μ := fun n => μ (K n)) (p := fun n => p (K n))
        (q := fun n => q (K n)) hc' (fun n => hp (K n)) (fun n => hq (K n)) hμpos'
        (B := 1) (fun n => hpB (K n)) (fun n => hqB (K n)) (fun n => hhat (K n)) hPc hQc hlocp
        hlocq hy (hFp.integrable_exp_nonneg hy.le) (hFq.integrable_exp_nonneg hy.le)
    rcases hy0.eq_or_lt with rfl | hy
    · have hF := hFp.sub hFq
      have hcont := hF.laplace_continuousOn_Ici 0 (mem_Ici.2 le_rfl)
      have hlim := (hcont.mono Ioi_subset_Ici_self).tendsto
      have key : 0 ≤ ∫ u : ℝ, ((Fp (u : ℂ) - Fq (u : ℂ)).re) * Real.exp (0 * u) := by
        refine ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
        have := hpos y hy
        simpa [Complex.sub_re] using this
      simpa [Complex.sub_re] using key
    · exact hpos y hy
  -- the limit `H = Fp - Fq` and its identification by uniqueness
  have hHin : InAiryClass (fun z => Fp z - Fq z) := hFp.sub hFq
  obtain ⟨C, ν, hC, hbd⟩ := hHin.2.2.1
  have hHre : ∀ x : ℝ, ((fun z => Fp z - Fq z) (x : ℂ)).re = Pr x - Qr x := fun x => by
    simp [hPr, hQr, Complex.sub_re]
  have hint0 : 0 ≤ (∫ x : ℝ, (fun z => Fp z - Fq z) (x : ℂ)).re := by
    have hre0 : ∫ x : ℝ, ((fun z => Fp z - Fq z) (x : ℂ)).re =
        (∫ x : ℝ, (fun z => Fp z - Fq z) (x : ℂ)).re := integral_re hHin.2.1
    rw [← hre0]
    have := hlap 0 le_rfl
    simpa [hHre] using this
  obtain ⟨b, hb0, hHeq, -⟩ := D.uniqueness hHin.1 hHin.2.1 hC hbd hHin.2.2.2 hint0
    (fun t ht htm => by rw [hHre]; exact hshellP t ht htm)
    (fun x hx => by rw [hHre]; exact hleft x hx)
  have hΦ : ∀ u : ℝ, Pr u - Qr u = -(b * (D.G (u : ℂ)).re) := fun u => by
    have := congrArg Complex.re (hHeq (u : ℂ))
    rw [Complex.neg_re, Complex.re_ofReal_mul, hHre u] at this
    exact this
  -- the normalised physical and Fourier profiles
  set Φn : ℕ → ℝ → ℝ := fun n u => hankelWindowProfile (c (K n)) (G (K n)) u / μ (K n) with hΦn
  set Bn : ℕ → ℝ → ℝ := fun n u =>
    hankelWindowProfile (c (K n)) (besselHankelTransform (c (K n)) (G (K n))) u / μ (K n) with hBn
  have hΦn_eq : ∀ n u, Φn n u = hankelWindowProfile (c (K n)) (p (K n)) u / μ (K n) -
      hankelWindowProfile (c (K n)) (q (K n)) u / μ (K n) := fun n u => by
    have e : hankelWindowProfile (c (K n)) (G (K n)) u =
        hankelWindowProfile (c (K n)) (fun Δ => p (K n) Δ - q (K n) Δ) u := by
      congr 1; funext Δ; exact (hGpq (K n) Δ).symm
    show hankelWindowProfile (c (K n)) (G (K n)) u / μ (K n) = _
    rw [e, hankelWindowProfile_sub]; ring
  have hBn_eq : ∀ n u, Bn n u = hankelWindowProfile (c (K n)) (p (K n)) u / μ (K n) +
      hankelWindowProfile (c (K n)) (q (K n)) u / μ (K n) := fun n u => by
    have e : hankelWindowProfile (c (K n)) (besselHankelTransform (c (K n)) (G (K n))) u =
        hankelWindowProfile (c (K n)) (fun Δ => p (K n) Δ + q (K n) Δ) u := by
      congr 1; funext Δ; exact (hĜpq (K n) Δ).symm
    show hankelWindowProfile (c (K n)) (besselHankelTransform (c (K n)) (G (K n))) u / μ (K n) = _
    rw [e, hankelWindowProfile_add]; ring
  have hΦlu : TendstoLocallyUniformlyOn Φn (fun u => Pr u - Qr u) atTop univ :=
    (hlocp.sub hlocq).congr (fun n u _ => (hΦn_eq n u).symm)
  have hBlu : TendstoLocallyUniformlyOn Bn (fun u => Pr u + Qr u) atTop univ :=
    (hlocp.add hlocq).congr (fun n u _ => (hBn_eq n u).symm)
  have hΦi : ∀ n, Integrable (Φn n) := fun n =>
    ((integrable_hankelWindowProfile_iff (hcpos' n) _).2 (hP (K n)).int).div_const _
  have hBi : ∀ n, Integrable (Bn n) := fun n =>
    ((integrable_hankelWindowProfile_iff (hcpos' n) _).2 (hP (K n)).int_hat).div_const _
  have hIntΦ : ∀ n, ∫ u, Φn n u = G (K n) 0 / μ (K n) := fun n => by
    show ∫ u, hankelWindowProfile (c (K n)) (G (K n)) u / μ (K n) = _
    rw [integral_div, integral_hankelWindowProfile (hcpos' n)]
    exact congrArg (· / μ (K n)) ((hP (K n)).integral_eq (h2 (K n)))
  have hIntB : ∀ n, ∫ u, Bn n u = G (K n) 0 / μ (K n) := fun n => by
    show ∫ u, hankelWindowProfile (c (K n)) (besselHankelTransform (c (K n)) (G (K n))) u / μ (K n) = _
    rw [integral_div, integral_hankelWindowProfile (hcpos' n)]
    exact congrArg (· / μ (K n)) ((hP (K n)).integral_hat_eq (h2 (K n)))
  have hnormΦ : ∀ n, ∫ u, |Φn n u| = 1 := fun n => by
    show ∫ u, |hankelWindowProfile (c (K n)) (G (K n)) u / μ (K n)| = 1
    simp_rw [abs_div, abs_of_pos (hμpos' n)]
    rw [integral_div, integral_abs_hankelWindowProfile (hcpos' n)]
    exact div_self (hμpos' n).ne'
  have hBnn : ∀ n u, 0 ≤ Bn n u := fun n u =>
    div_nonneg (hankelWindowProfile_nonneg_of (hcpos' n) fun hΔ =>
      (hP (K n)).nonneg_hat _ hΔ.le) (hμpos' n).le
  have hG0pos : ∀ n, 0 ≤ G (K n) 0 / μ (K n) := fun n =>
    div_nonneg (hP (K n)).origin_pos.le (hμpos' n).le
  -- the equality case of `lem:qual-compact`
  have hGt_int : Integrable (fun u : ℝ => b * (D.G (u : ℂ)).re) := D.G_int.re.const_mul b
  have hGt_eq : ∀ u : ℝ, b * (D.G (u : ℂ)).re = -(Pr u - Qr u) := fun u => by rw [hΦ u]; ring
  have hmain := qual_compact_real (F := fun n u => -Φn n u) (G := fun u => b * (D.G (u : ℂ)).re)
    (v := D.tm) (fun n => (hΦi n).neg) (fun N => hGt_int.integrableOn)
    (fun n => by simp_rw [abs_neg]; exact hnormΦ n)
    (fun ε hε => Eventually.of_forall fun n => by
      rw [integral_neg, hIntΦ]; linarith [hG0pos n])
    (fun N => by
      refine (setIntegral_Icc_abs_sub_tendsto hΦi (hPc.sub hQc) hΦlu (-(N : ℝ)) N).congr
        fun j => setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
      show |Φn j u - (Pr u - Qr u)| = |-Φn j u - b * (D.G (u : ℂ)).re|
      rw [hGt_eq u, ← abs_neg]
      congr 1; ring)
    (fun a ha => by
      have hpos : 0 < (D.tm - a) / hankelBeta1 := div_pos (sub_pos.2 ha) hβ
      filter_upwards [hε'.eventually (Iio_mem_nhds hpos)] with n hn u hu
      have hge := winDelta_ge (hcpos' n) (hTc (K n)) hn.le hu
      have h1 : hankelWindowProfile (c (K n)) (G (K n)) u ≤ 0 :=
        hankelWindowProfile_nonpos_of (hcpos' n) (fun _ => (hP (K n)).tail _ hge)
      show 0 ≤ -(hankelWindowProfile (c (K n)) (G (K n)) u / μ (K n))
      rw [neg_nonneg]
      exact div_nonpos_of_nonpos_of_nonneg h1 (hμpos' n).le)
    (fun δ hδ => by
      obtain ⟨b₁, h1⟩ := tail_small (Or.inl rfl) hc' hcpos' (fun n => hp (K n)) hμpos'
        (fun n => by simpa using hpB (K n)) (δ / 2) (by positivity)
      obtain ⟨b₂, h2'⟩ := tail_small (Or.inr rfl) hc' hcpos' (fun n => hq (K n)) hμpos'
        (fun n => by simpa using hqB (K n)) (δ / 2) (by positivity)
      refine ⟨max b₁ b₂, fun b' hb' => ?_⟩
      filter_upwards [h1 b' ((le_max_left _ _).trans hb'), h2' b' ((le_max_right _ _).trans hb')]
        with n hn1 hn2
      have iP : Integrable (fun u => |hankelWindowProfile (c (K n)) (p (K n)) u / μ (K n)|) :=
        (((integrable_hankelWindowProfile_iff (hcpos' n) _).2 (hp (K n)).int).div_const _).abs
      have iQ : Integrable (fun u => |hankelWindowProfile (c (K n)) (q (K n)) u / μ (K n)|) :=
        (((integrable_hankelWindowProfile_iff (hcpos' n) _).2 (hq (K n)).int).div_const _).abs
      calc ∫ u in Ioi b', |-Φn n u|
          ≤ ∫ u in Ioi b', (|hankelWindowProfile (c (K n)) (p (K n)) u / μ (K n)| +
              |hankelWindowProfile (c (K n)) (q (K n)) u / μ (K n)|) := by
            refine setIntegral_mono_on (hΦi n).neg.abs.integrableOn (iP.add iQ).integrableOn
              measurableSet_Ioi fun u _ => ?_
            rw [abs_neg, hΦn_eq n u]
            exact abs_sub _ _
        _ = (∫ u in Ioi b', |hankelWindowProfile (c (K n)) (p (K n)) u / μ (K n)|) +
              ∫ u in Ioi b', |hankelWindowProfile (c (K n)) (q (K n)) u / μ (K n)| :=
            integral_add iP.integrableOn iQ.integrableOn
        _ ≤ δ / 2 + δ / 2 := add_le_add hn1 hn2
        _ = δ := by ring)
  obtain ⟨-, -, -, -, hEq, -⟩ := hmain
  have hre : ∫ x : ℝ, (D.G (x : ℂ)).re = (∫ x : ℝ, D.G (x : ℂ)).re := integral_re D.G_int
  have hGt0 : ∫ u : ℝ, b * (D.G (u : ℂ)).re = 0 := by
    rw [integral_const_mul, hre, D.G_integral_zero]; simp
  obtain ⟨hGt1, hconv⟩ := hEq hGt0
  have hNpos := D.G_l1_pos
  have hbN : b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ = 1 := by
    have e : ∫ u : ℝ, |b * (D.G (u : ℂ)).re| = b * ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show |b * (D.G (u : ℂ)).re| = b * ‖D.G (u : ℂ)‖
      rw [abs_mul, abs_of_nonneg hb0, Complex.abs_re_eq_norm.mpr (D.G_real u)]
    rw [← e]; exact hGt1
  have hnormG : ∀ u : ℝ, D.normG u = b * (D.G (u : ℂ)).re := fun u => by
    unfold ShellHBData.normG
    have : b = (∫ x : ℝ, ‖D.G (x : ℂ)‖)⁻¹ := eq_inv_of_mul_eq_one_left hbN
    rw [this, div_eq_inv_mul]
  have hfun : (fun u => Pr u - Qr u) = fun u => -D.normG u := funext fun u => by
    rw [hnormG, hΦ]
  refine ⟨K, hK, ⟨by rw [← hfun]; exact hΦlu, ?_⟩, ?_⟩
  · refine hconv.congr fun j => integral_congr_ae (Eventually.of_forall fun u => ?_)
    show |-Φn j u - b * (D.G (u : ℂ)).re| = |Φn j u - -D.normG u|
    rw [hnormG, ← abs_neg]
    congr 1; ring
  · -- the Fourier profile: its mass `M[ĥ]/M[h] = -∫ F_j → 0`
    have hG0 : Tendsto (fun n => G (K n) 0 / μ (K n)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ∫ u, -Φn n u) atTop (𝓝 0) := by
        refine squeeze_zero_norm (fun n => ?_) hconv
        have hi : Integrable (fun u => -Φn n u - b * (D.G (u : ℂ)).re) := (hΦi n).neg.sub hGt_int
        have hs : ∫ u, (-Φn n u - b * (D.G (u : ℂ)).re) =
            (∫ u, -Φn n u) - ∫ u : ℝ, b * (D.G (u : ℂ)).re := integral_sub (hΦi n).neg hGt_int
        calc ‖∫ u, -Φn n u‖ = ‖∫ u, (-Φn n u - b * (D.G (u : ℂ)).re)‖ := by
              rw [hs, hGt0, sub_zero]
          _ ≤ ∫ u, ‖-Φn n u - b * (D.G (u : ℂ)).re‖ := norm_integral_le_integral_norm _
          _ = ∫ u, |-Φn n u - b * (D.G (u : ℂ)).re| := by simp only [Real.norm_eq_abs]
      have h2 := h1.neg
      simp only [neg_zero] at h2
      refine h2.congr fun n => ?_
      rw [integral_neg, hIntΦ]; ring
    have hPQ : ∀ u, Pr u + Qr u = 0 := by
      intro u
      obtain ⟨N, hN⟩ := exists_nat_ge (|u| + 1)
      have hN1 : (1 : ℝ) ≤ N := by linarith [abs_nonneg u]
      have hab : -(N : ℝ) ≤ N := by linarith
      have hcont : Continuous fun x => Pr x + Qr x := hPc.add hQc
      have hle : ∫ x in Icc (-(N : ℝ)) N, (Pr x + Qr x) ≤ 0 := by
        have hU : TendstoUniformlyOn Bn (fun x => Pr x + Qr x) atTop (Icc (-(N : ℝ)) N) :=
          (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
            (hBlu.mono (subset_univ _))
        have hlim := setIntegral_Icc_tendsto_unif hab hU
          (Eventually.of_forall fun n => (hBi n).integrableOn) hcont.continuousOn.integrableOn_Icc
        refine le_of_tendsto_of_tendsto hlim hG0 (Eventually.of_forall fun n => ?_)
        show ∫ x in Icc (-(N : ℝ)) N, Bn n x ≤ G (K n) 0 / μ (K n)
        rw [← hIntB n]
        exact setIntegral_le_integral (hBi n) (Eventually.of_forall fun x => hBnn n x)
      have hzero : ∫ x in Icc (-(N : ℝ)) N, (Pr x + Qr x) = 0 :=
        le_antisymm hle (setIntegral_nonneg measurableSet_Icc fun x _ => hnonneg x)
      have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hnonneg)
        hcont.continuousOn.integrableOn_Icc).1 hzero
      have heq := Measure.eqOn_Icc_of_ae_eq volume (by linarith : -(N : ℝ) ≠ N) hae
        hcont.continuousOn (continuous_const (y := (0 : ℝ))).continuousOn
        (show u ∈ Icc (-(N : ℝ)) N from ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩)
      exact heq
    refine ⟨?_, ?_⟩
    · have hfun2 : (fun u => Pr u + Qr u) = fun _ => (0 : ℝ) := funext hPQ
      rw [← hfun2]; exact hBlu
    · refine hG0.congr fun n => ?_
      rw [← hIntB n]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show Bn n u = |Bn n u - 0|
      rw [sub_zero, abs_of_nonneg (hBnn n u)]

/-- **`thm:ce-shell-gap`, the `v = t_m` endpoint clause** (Corollary H.14d; Hankel form), proved: for every
Hermite–Biehler configuration `D`, along any sequence of Hankel Cohn–Elkies profiles `h_k` (dimensions `d_k ≥ 2`,
offsets `o(c^{1/3})`, `h_k ≤ 0` at the prescribed shells, thresholds
`T_k ≤ c/π² - (t_m/β₁) c^{1/3} + o(c^{1/3})`), the profiles `Ψ_{h_k}/M[h_k] → -G_N/‖G_N‖₁` and `Ψ_{ĥ_k}/M[h_k] → 0`
locally uniformly and in `L¹`, `Ψ_{f_k}/M[f_k] → G_N/‖G_N‖₁` for `f_k = ĥ_k - h_k`, `M[ĥ_k]/M[f_k] → 0`, and
`ℒ_y(-G_N) ≥ 0` for all `y > 0`. The zero-mass clause of `thm:ce-physical-profile` is the equality case of
`lem:qual-compact` (`Analysis.qual_compact_real`), applied after identifying the limit as `-b G_N` by
`lem:hb-uniqueness` (`D.uniqueness`); the uniqueness of the limit upgrades subsequences to the whole sequence. -/
theorem shellGapEndpoint_proved (D : ShellHBData) : ShellGapEndpoint D := by
  intro r hr dk hdk h2 ε hε G T hP hshell hT
  -- the physical and Fourier profiles, along the whole sequence
  have hsub : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∃ K : ℕ → ℕ, StrictMono K ∧
      ProfileConv (fun n u => hankelWindowProfile ((dk (ns (K n)) : ℝ) / 2) (G (ns (K n))) u /
        hankelMass ((dk (ns (K n)) : ℝ) / 2) (G (ns (K n)))) (fun u => -D.normG u) ∧
      ProfileConv (fun n u => hankelWindowProfile ((dk (ns (K n)) : ℝ) / 2)
        (besselHankelTransform ((dk (ns (K n)) : ℝ) / 2) (G (ns (K n)))) u /
        hankelMass ((dk (ns (K n)) : ℝ) / 2) (G (ns (K n)))) (fun _ => 0) := fun ns hns =>
    endpoint_subseq D hr (dk := fun k => dk (ns k)) (hdk.comp hns) (fun k => h2 _)
      (ε := fun k => ε (ns k)) (hε.comp hns) (G := fun k => G (ns k)) (T := fun k => T (ns k))
      (fun k => hP _) (fun k => hshell _) (fun k => hT _)
  have hA : ProfileConv (fun k u => hankelWindowProfile ((dk k : ℝ) / 2) (G k) u /
      hankelMass ((dk k : ℝ) / 2) (G k)) (fun u => -D.normG u) :=
    profileConv_of_subseq fun ns hns => by
      obtain ⟨K, -, h1, -⟩ := hsub ns hns
      exact ⟨K, h1⟩
  have hB : ProfileConv (fun k u => hankelWindowProfile ((dk k : ℝ) / 2)
      (besselHankelTransform ((dk k : ℝ) / 2) (G k)) u / hankelMass ((dk k : ℝ) / 2) (G k))
      (fun _ => 0) :=
    profileConv_of_subseq fun ns hns => by
      obtain ⟨K, -, -, h2'⟩ := hsub ns hns
      exact ⟨K, h2'⟩
  -- notation
  set c : ℕ → ℝ := fun k => (dk k : ℝ) / 2 with hcdef
  have hcpos : ∀ k, 0 < c k := fun k => by
    have : (2 : ℝ) ≤ dk k := by exact_mod_cast h2 k
    simp only [hcdef]; positivity
  set μ : ℕ → ℝ := fun k => hankelMass (c k) (G k) with hμdef
  have hμpos : ∀ k, 0 < μ k := fun k =>
    lt_of_lt_of_le (hP k).origin_pos ((hP k).origin_le_hankelMass (h2 k))
  set A : ℕ → ℝ → ℝ := fun k u => hankelWindowProfile (c k) (G k) u / μ k with hAdef
  set B : ℕ → ℝ → ℝ := fun k u =>
    hankelWindowProfile (c k) (besselHankelTransform (c k) (G k)) u / μ k with hBdef
  have hAi : ∀ k, Integrable (A k) := fun k =>
    ((integrable_hankelWindowProfile_iff (hcpos k) _).2 (hP k).int).div_const _
  have hBi : ∀ k, Integrable (B k) := fun k =>
    ((integrable_hankelWindowProfile_iff (hcpos k) _).2 (hP k).int_hat).div_const _
  have hLAi : Integrable (fun u => -D.normG u) := D.normG_integrable.neg
  have hLBi : Integrable (fun _ : ℝ => (0 : ℝ)) := integrable_zero _ _ _
  -- `f = ĥ - h`
  have hC := ProfileConv.sub hA hB hAi hBi hLAi hLBi
  set f : ℕ → ℝ → ℝ := fun k Δ => besselHankelTransform (c k) (G k) Δ - G k Δ with hfdef
  have hCf : ∀ k u, B k u - A k u = hankelWindowProfile (c k) (f k) u / μ k := fun k u => by
    simp only [hAdef, hBdef, hfdef]
    rw [hankelWindowProfile_sub]; ring
  have hCi : ∀ k, Integrable (fun u => B k u - A k u) := fun k => (hBi k).sub (hAi k)
  have hnormG_abs : ∫ u, |D.normG u| = 1 := by
    have hN := D.G_l1_pos
    have : ∫ u, |D.normG u| = (∫ u : ℝ, ‖D.G (u : ℂ)‖) / ∫ x : ℝ, ‖D.G (x : ℂ)‖ := by
      rw [← integral_div]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      show |(D.G (u : ℂ)).re / ∫ x : ℝ, ‖D.G (x : ℂ)‖| = ‖D.G (u : ℂ)‖ / ∫ x : ℝ, ‖D.G (x : ℂ)‖
      rw [abs_div, abs_of_pos hN, Complex.abs_re_eq_norm.mpr (D.G_real u)]
    rw [this, div_self hN.ne']
  -- the mass ratio `m_k = M[f_k]/M[h_k] → 1`
  set m : ℕ → ℝ := fun k => hankelMass (c k) (f k) / μ k with hmdef
  have hm_int : ∀ k, ∫ u, |B k u - A k u| = m k := fun k => by
    simp_rw [hCf k, abs_div, abs_of_pos (hμpos k)]
    rw [integral_div, integral_abs_hankelWindowProfile (hcpos k)]
  have hm_lim : Tendsto m atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hC.2
    rw [← hm_int k, ← hnormG_abs]
    have e : (∫ u, |B k u - A k u|) - (∫ u, |D.normG u|) =
        ∫ u, (|B k u - A k u| - |D.normG u|) :=
      (integral_sub (hCi k).abs D.normG_integrable.abs).symm
    rw [Real.norm_eq_abs, e]
    refine (abs_integral_le_integral_abs).trans ?_
    refine integral_mono (((hCi k).abs.sub D.normG_integrable.abs).abs)
      (((hCi k).sub (hLBi.sub hLAi)).abs) fun u => ?_
    simp only [zero_sub, neg_neg]
    exact abs_abs_sub_abs_le_abs_sub _ _
  have hD := hC.div_const hCi (hLBi.sub hLAi) (by simpa using D.normG_continuous) hm_lim one_ne_zero
  refine ⟨hA, hB, ?_, ?_, ?_⟩
  · refine hD.congr (fun k u => ?_) (fun u => ?_)
    · show (B k u - A k u) / m k = hankelWindowProfile (c k) (f k) u / hankelMass (c k) (f k)
      rw [hCf]
      show hankelWindowProfile (c k) (f k) u / μ k / (hankelMass (c k) (f k) / μ k) = _
      exact div_div_div_cancel_right₀ (hμpos k).ne' _ _
    · simp
  · have hM : Tendsto (fun k => hankelMass (c k) (besselHankelTransform (c k) (G k)) / μ k) atTop (𝓝 0) := by
      refine hB.2.congr fun k => ?_
      show ∫ u, |hankelWindowProfile (c k) (besselHankelTransform (c k) (G k)) u / μ k - 0| =
        hankelMass (c k) (besselHankelTransform (c k) (G k)) / μ k
      simp_rw [sub_zero, abs_div, abs_of_pos (hμpos k)]
      rw [integral_div, integral_abs_hankelWindowProfile (hcpos k)]
    have := hM.div hm_lim one_ne_zero
    simp only [zero_div] at this
    refine this.congr fun k => ?_
    exact div_div_div_cancel_right₀ (hμpos k).ne' _ _
  · exact (one_profile_threshold_le_and_endpoint_iff D).2.1
      ((one_profile_feasible_iff D D.tm).1
        (hankelShellGapLimit_proved D r hr D.tm dk hdk h2 ε hε G T hP hshell hT))

/-- info: 'FormalResearch.SignUncertainty.endpoint_subseq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms endpoint_subseq

/-- info: 'FormalResearch.SignUncertainty.shellGapEndpoint_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shellGapEndpoint_proved

end FormalResearch.SignUncertainty
